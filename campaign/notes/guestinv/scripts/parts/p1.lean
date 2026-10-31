import InitECandidate.Solver.PanTerminatingBounded

/-! PROPOSED STATEMENTS ONLY (Wave 8, mission 9409f9a9, track `guestinv-opus55`), revision 3.

Replaces the presumed-false all-state `TerminatingFunBounded "main"` route by a guarded one.
Revision 2 answered the round-1 quorum (`campaign/reviews/guestinv-r1.md`):

* `GuestInv` (§2) is *metadata only* (code, memory domains, base address). Every Pancake
  evaluation preserves it (`guestInv_evaluate`, proved), so every call / decCall / handler / seq
  composition needs no preservation side condition.
* Every function on `main`'s call graph gets its own bound `K.«f»` (§6, generated mechanically
  from `Guest/SoftwareAst.lean` by `campaign/notes/guestinv/scripts/coverage.py`), equal to the
  sum over the body of `K(callee) + 1` per call and `(N + 1) * (body + 1)` per loop, where `N` is
  the loop's iteration bound, from a measure that holds for ARBITRARY memory and globals wherever
  one exists.
* Five loops have no arbitrary-memory measure: `run_frames` (EVM gas), `htab_truncate`
  (count in memory), `_decode_witness_node_body` (needs heap/scratch separation) and the two MPT
  update loops. They and their callers form the *guarded tier* (§7), whose leaves carry explicit
  memory contracts (`HtabWF`, `EvmInv` with a gas-value-free potential, `WorldOK`).

Revision 3 answers the round-2 quorum (`campaign/reviews/guestinv-r2.md`):

* `htab_new_spec` / `htab_new_scratch_spec` are guarded by `key_len ∈ htabKeyLens`
  (`HtabNewReady`, item 1).
* `EvmInv` requires stack room in every suspended frame (`FrameRoom`), so `finish_child`'s
  `stack_push` on the parent never allocates below the child's mark (item 2).
* The combinator set is closed and every combinator is PROVED (item 3): tail call
  (`tailCall_on`), handler call (`callHandle_guestInv`), the stationary `while` rule
  (`while_rank_stationary`, with `while_rank` as a corollary), `dec` for guards that read locals
  (`dec_onLocals` with `LocalsOnly`, instantiated for every guard), and the guarded `decCall_on`
  and condition-aware `ite_cond_on` that the guarded leaves need. `htab_del_progress_spec` gives
  `htab_truncate` its count decrement.
* The bridge (§4) is unchanged and proved; `K_pan_budget` (§8) is proved by `decide`; no `K.«f»`
  changed.

Rationale, the per-loop justification table, the list of `sorry`s and the list of statements
changed since revision 2 are in `campaign/notes/guestinv/DESIGN.md`. `sorry` appears only in leaf
theorem bodies, never in a definition or a combinator.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

/-! ## 1. Layout constants (all from `InitE.Parameters` / `Guest/SoftwareAst.lean`) -/

/-- Upper end of the bump heap: `alloc` traps unless the new `heap_ptr ≤ 0xb0000000`. -/
def heapLimit : Nat := scratchStart

/-- `journal_cap` is only ever assigned `0` (declaration) or `524288` (`state_init`,
`Guest/SoftwareAst.lean:12768`). -/
def journalCapMax : Nat := 524288

/-- Bytes of `ordinaryDomain = [sourceBase, heapEnd)` (aligned cells only). A loop that loads or
stores a strictly increasing address on every iteration errors within this many iterations. -/
def domainBytes : Nat := heapEnd - sourceBase

theorem domainBytes_eq : domainBytes = 31104957928 := by decide

/-- Maximum key length of every guest hash table. `htab_new`/`htab_new_scratch` are called with
the literal key lengths 20, 28, 32, 52 and 60 only (`bal_init` uses 28 and 60,
`Guest/SoftwareAst.lean:13873-13875`); round 1 wrongly had 52. -/
def maxKeyLen : Nat := 60

/-- Frame-chain length bound used by the EVM potential. Each active frame owns at least
280 (record) + 1024 (stack) + 104 (continuation) disjoint scratch bytes and the scratch arena has
`0xb0bee000 - 0xb0000000 = 12509184` bytes, so `EvmInv` forces at most 8884 frames. -/
def maxChain : Nat := 16384

/-- The 67 guest globals, in declaration order (all `Shape.one`, all initialised to `0`).
`astGlobalNames_eq` below checks this list against the AST. -/
def guestGlobalNames : List String :=
  ["heap_ptr", "journal_n", "scratch_ptr", "frame_mem_ptr", "u256_ws", "sha_st", "sha_pad",
   "keccak_rc", "keccak_st", "keccak_pad", "secp_accel_scratch", "zero_hashes", "ssz_len_chunk",
   "ssz_offs", "hdr_zero8", "empty_trie_root", "empty_code_hash", "mpt_nib_scratch",
   "mpt_hash_scratch", "mpt_key_scratch", "ws", "bs", "ts", "sk_buf", "journal", "journal_cap",
   "bal_accounts", "bal_index", "bal_idx_accts", "bal_idx_stor", "bal_key_buf", "ev",
   "evm_empty", "pre_hdr_buf", "evm_key_buf", "cur_cont", "transfer_topic", "vm_system_address",
   "null_address", "rmd_tab", "rmd_x", "rmd_h", "rmd_pad", "b2_sigma", "b2_iv", "b2_v",
   "bn_gamma", "bn_expw", "bls_c", "bls_discount", "be", "bo", "precompile_addrs", "zero32",
   "block_hashes", "block_hashes_n", "cur_si", "beacon_roots_address", "history_storage_address",
   "withdrawal_request_address", "consolidation_request_address", "builder_deposit_address",
   "builder_exit_address", "deposit_contract_address", "deposit_event_signature_hash",
   "wd_rlp_slices", "fail_code"]

/-- Global declarations read off the literal AST. -/
def astGlobalNames : List String :=
  Guest.Software.guestAst.filterMap fun d =>
    match d with
    | .decl _ name _ => some name
    | _ => none

theorem astGlobalNames_eq : astGlobalNames = guestGlobalNames := by decide

/-- The key lengths of all 32 `htab_new` / `htab_new_scratch` call sites in the AST: always a
literal, 15×20, 1×28, 8×32, 7×52, 1×60 (DESIGN.md §1, item 4). All are at most `maxKeyLen`. -/
def htabKeyLens : List Nat := [20, 28, 32, 52, 60]

theorem htabKeyLens_le : ∀ k ∈ htabKeyLens, k ≤ maxKeyLen := by decide

/-- The capacities of the same 32 call sites: always a literal, 1×4, 8×8, 6×16, 12×64, 4×256
(round-2 Astra item 3: an unbounded `cap` wraps `(ncap + 1) * stride`). -/
def htabCaps : List Nat := [4, 8, 16, 64, 256]

/-! ## 2. `GuestInv`: metadata only, preserved by every evaluation

Round 1 put four global-variable facts into `GuestInv` (`heap_ptr ≤ 0xb0000000`,
`ArenaOK frame_mem_ptr scratch_ptr`, `journal_n ≤ journal_cap ≤ 2^19`, all globals are words).
Each of them is broken by some call whose destination or argument comes from memory or from an
unrelated callee: `call heap_mark → journal_n` (round 1, item 1), `scratch_release(load(rec+48))`
and `frame_mem_release(load(rec+56))` in `finish_child`. In revision 2 every unguarded bound holds
for arbitrary memory AND arbitrary globals, so `GuestInv` keeps only the four fields that no
Pancake program can change. Preservation is a theorem about the semantics (`guestInv_evaluate`). -/

/-- The guest invariant: code and the three memory-domain/base fields of the covered entry. -/
structure GuestInvData {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop where
  code : s.code = originalRuntimeCode
  memaddrs : s.memaddrs = ordinaryDomain
  shMemaddrs : s.shMemaddrs = sharedDomain
  baseAddr : s.baseAddr = BitVec.ofNat 64 sourceBase

def GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInvData s

/-- `name` is a global bound to the word `w`. -/
def GlobalWord {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) (w : BitVec 64) :
    Prop :=
  s.globals.lookup (ofString name) = some (.val (.word w))

/-- The FFI state replays the oracle of an input whose declared gas limit is covered.
Only meaningful at `F = Guest.HostMemory`; false at every other carrier. -/
def CoveredFfi : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun {F} s => ∃ (h : F = Guest.HostMemory) (input : Guest.InputBlob),
    Guest.GasLimit.declaredGasLimit input ≤ maxCoveredGas ∧
    OracleConsistent sourceOracle (Guest.guestHostMemory input)
      (cast (congrArg HolFfiState h) s.ffi)

/-- `GuestInv` plus the covered input. -/
def GuestInvCovered : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ CoveredFfi s

/-! ### Preservation (proved) -/

/-- `baseAddr` is never changed by evaluation (Flapjack `evaluateInvariantsHOLFinite`). -/
theorem evaluate_baseAddr {F : Type} (state : PanSemStateFiniteExact 64 F)
    (program : ProgHOL 64) :
    (evaluateHOLFiniteState state program).2.baseAddr = state.baseAddr := by
  have invariant := evaluateInvariantsHOLFinite program
    (PanPropsEvalStateFiniteExact.ofPanSemFinite state)
    (evaluateHOLFiniteState state program).1
    (PanPropsEvalStateFiniteExact.ofPanSemFinite (evaluateHOLFiniteState state program).2) (by
      simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
        PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite])
  exact invariant.2.2.2.2.1

/-- Every evaluation of every program preserves `GuestInv` (whatever its result). -/
theorem guestInv_evaluate {F : Type} (s : PanSemStateFiniteExact 64 F) (prog : ProgHOL 64)
    (h : GuestInv s) : GuestInv (evaluateHOLFiniteState s prog).2 := by
  obtain ⟨c, m, sh, b⟩ := h
  have hm := PanRunBounded.evaluateHOLFiniteState_metadata s prog
  exact ⟨hm.1.trans c, hm.2.1.trans m, hm.2.2.2.1.trans sh, (evaluate_baseAddr s prog).trans b⟩

theorem guestInv_congr {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hcode : t.code = s.code) (hmem : t.memaddrs = s.memaddrs) (hsh : t.shMemaddrs = s.shMemaddrs)
    (hbase : t.baseAddr = s.baseAddr) (h : GuestInv s) : GuestInv t := by
  obtain ⟨c, m, sh, b⟩ := h
  exact ⟨hcode.trans c, hmem.trans m, hsh.trans sh, hbase.trans b⟩

theorem guestInv_callEntry {F : Type} (s : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (h : GuestInv s) :
    GuestInv (callEntryStateHOLFinite s callee) :=
  guestInv_congr (s := s) rfl rfl rfl rfl h

theorem guestInv_with_locals_clock {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (h : GuestInv s) :
    GuestInv { s with locals := locals, clock := k } :=
  guestInv_congr (s := s) rfl rfl rfl rfl h

theorem guestInv_setVar {F : Type} (name : MlS) (v : ValueHOL 64)
    (s : PanSemStateFiniteExact 64 F) (h : GuestInv s) : GuestInv (setVarHOLFinite name v s) :=
  guestInv_congr (s := s) rfl rfl rfl rfl h

/-! ## 3. Guarded function bounds, preservation and combinators -/

/-- `fname` is installed and its body is bounded by `K` from every `P` entry state. -/
def TerminatingFunBoundedOn (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) (K : Nat) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    TerminatingProgBoundedOn P body K

/-- Every non-timeout run of `prog` from a `P` state ends in a `Q` state. -/
def PreservesOn (P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (prog : ProgHOL 64) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
    state.code = originalRuntimeCode → P state →
    (evaluateHOLFiniteState state prog).1 ≠ some .timeOut →
    Q (evaluateHOLFiniteState state prog).2

def FunPreservesOn (P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    PreservesOn P Q body

/-- `GuestInv` is preserved by every program: no preservation side condition anywhere. -/
theorem preservesOn_guestInv (prog : ProgHOL 64) : PreservesOn GuestInv GuestInv prog :=
  fun state _ h _ => guestInv_evaluate state prog h

/-- Round-1 item 1, regression: `call heap_mark → journal_n` (a global destination fed by
`heap_ptr`) broke the old journal conjunct; it trivially preserves the new `GuestInv`. -/
example : PreservesOn GuestInv GuestInv
    (.call (some (some (.global, ofString "journal_n"), none)) (ofString "heap_mark") []) :=
  preservesOn_guestInv _

/-- Preservation through any handler-free call, whatever the destination (round-1 item 1). -/
theorem PreservesOn.call_guestInv (fname : MlS)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) :
    PreservesOn GuestInv GuestInv (.call (some (destination, none)) fname arguments) :=
  preservesOn_guestInv _

/-- Same definition as `PanTerminatingCallOn.CallEntryOn` (branch `wave8/step0-opus55`). -/
def CallEntryOn (P Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (fname : MlS)
    (arguments : List (ExpHOL 64)) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL),
    state.code = originalRuntimeCode → P state →
    evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values →
    lookupCodeHOLFinite state.code.lookup fname values = some (body, callee, returnShape) →
    Pc (callEntryStateHOLFinite state callee)

theorem callEntryOn_guestInv (fname : MlS) (arguments : List (ExpHOL 64)) :
    CallEntryOn GuestInv GuestInv fname arguments := by
  intro F state values body callee ret _ hP _ _
  exact guestInv_callEntry state callee hP

theorem TerminatingFunBoundedOn.weaken {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {K K' : Nat} (h : TerminatingFunBoundedOn P fname K) (hle : K ≤ K') :
    TerminatingFunBoundedOn P fname K' := by
  obtain ⟨params, body, ret, hlook, hb⟩ := h
  exact ⟨params, body, ret, hlook, fun state hcode hP => (hb state hcode hP).weaken hle⟩

theorem TerminatingFunBoundedOn.mono {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {K : Nat} (h : TerminatingFunBoundedOn P fname K)
    (hQP : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), Q s → P s) :
    TerminatingFunBoundedOn Q fname K := by
  obtain ⟨params, body, ret, hlook, hb⟩ := h
  exact ⟨params, body, ret, hlook, fun state hcode hQ => hb state hcode (hQP state hQ)⟩

theorem TerminatingFunBoundedOn.of_unconditional
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {fname : MlS} {K : Nat}
    (h : TerminatingFunBounded fname K) : TerminatingFunBoundedOn P fname K := by
  obtain ⟨params, body, ret, hlook, hb⟩ := h
  exact ⟨params, body, ret, hlook, fun state hcode _ => hb state hcode⟩

def LocalsFree (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (k : Nat), P s → P { s with locals := locals, clock := k }

theorem localsFree_guestInv : LocalsFree GuestInv :=
  fun s locals k h => guestInv_with_locals_clock s locals k h
