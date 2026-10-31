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

/-- Upper bound on the capacity argument of `htab_new` / `htab_new_scratch` (round-2 Astra item 3:
an unbounded `cap` wraps `(ncap + 1) * stride`; round-3 non-blocking: a bound, not a list of
literals, because `nodedb_build` (9948) passes a computed power of two `≥ 2n + 2`). With
`cap ≤ 2^32` and `stride ≤ 64`, `(max cap 2 + 1) * stride < 2^64`. -/
def htabCapMax : Nat := 2 ^ 32

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

/-- Shared prefix of `call`/`decCall` (from `PanTerminatingCallOn.callee_body_bound`). -/
theorem callee_body_bound {P Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64} {ret : ShapeHOL} {B : Nat}
    (hlook : originalRuntimeCode.lookup fname = some (params, body, ret))
    (hbody : TerminatingProgBoundedOn Pc body B) {arguments : List (ExpHOL 64)}
    (hentry : CallEntryOn P Pc fname arguments)
    {F : Type} (state : PanSemStateFiniteExact 64 F) (hcode : state.code = originalRuntimeCode)
    (hP : P state) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (hl : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    body' = body ∧ TerminatingRunBounded (callEntryStateHOLFinite state callee) body' B := by
  have hsame := lookupCodeHOLFinite_installed_body state.code.lookup fname params body body'
    ret ret' values callee (by rw [hcode]; exact hlook) hl
  subst hsame
  exact ⟨rfl, hbody (callEntryStateHOLFinite state callee) hcode
    (hentry state values body' callee ret' hcode hP hargs hl)⟩

/-- Call without handler, callee guarded by `Pc` and discharged by `CallEntryOn`.
Proof: `PanTerminatingCallOn.TerminatingProgBoundedOn.call` verbatim. -/
theorem TerminatingProgBoundedOn.call_on
    {P Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {fname : MlS} {B : Nat}
    (hf : TerminatingFunBoundedOn Pc fname B)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (hentry : CallEntryOn P Pc fname arguments) :
    TerminatingProgBoundedOn P (.call (some (destination, none)) fname arguments) (B + 1) := by
  obtain ⟨params, body, ret, hlook, hbody⟩ := hf
  intro F state hcode hP hnt
  rcases hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
    _ | values
  · have hout : evaluateHOLFiniteState state (.call (some (destination, none)) fname arguments) =
        (some .error, state) := by
      rw [evaluateHOLFiniteState_call, hargs]
    rw [hout]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · rcases hl : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · have hout : evaluateHOLFiniteState state (.call (some (destination, none)) fname arguments) =
          (some .error, state) := by
        rw [evaluateHOLFiniteState_call, hargs]
        simp only [hl]
      rw [hout]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · obtain ⟨_, hrunBound⟩ := callee_body_bound hlook hbody hentry state hcode hP values body'
        callee ret' hargs hl
      by_cases hz : state.clock = 0
      · exfalso; apply hnt
        rw [evaluateHOLFiniteState_call, hargs]
        simp [hl, hz]
      · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body' with
          ⟨res, post⟩
        have hntb : res ≠ some .timeOut := by
          intro h; subst h; apply hnt
          rw [evaluateHOLFiniteState_call, hargs]
          simp [hl, hz, hrun]
        have hb := hrunBound (by rw [hrun]; exact hntb)
        rw [hrun] at hb
        obtain ⟨hspent, hkept⟩ := hb
        change state.clock - 1 ≤ post.clock + B at hspent
        change post.clock ≤ state.clock - 1 at hkept
        have hpair := evaluate_call_body_clock_no_timeout state post fname destination arguments
          values body' callee ret' res hargs hl hz hrun hntb
        dsimp only at hpair
        rw [hpair.2]
        exact ⟨by omega, by omega⟩

/-- `GuestInv` instance of `call_on`: no call-site obligation at all. -/
theorem TerminatingProgBoundedOn.call_guestInv {fname : MlS} {B : Nat}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) :
    TerminatingProgBoundedOn GuestInv (.call (some (destination, none)) fname arguments)
      (B + 1) :=
  TerminatingProgBoundedOn.call_on hf destination arguments (callEntryOn_guestInv fname arguments)

/-- Tail call `.call none fname args` (round-2 item 3): the callee's result (return value,
exception, error) becomes the caller's result, its locals are discarded. Same clock accounting
as `call_on`: one tick for the call plus the callee's body. -/
theorem TerminatingProgBoundedOn.tailCall_on
    {P Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {fname : MlS} {B : Nat}
    (hf : TerminatingFunBoundedOn Pc fname B) (arguments : List (ExpHOL 64))
    (hentry : CallEntryOn P Pc fname arguments) :
    TerminatingProgBoundedOn P (.call none fname arguments) (B + 1) := by
  obtain ⟨params, body, ret, hlook, hbody⟩ := hf
  intro F state hcode hP hnt
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
    _ | values
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · simp only [hl] at hnt ⊢
      obtain ⟨_, hrunBound⟩ := callee_body_bound hlook hbody hentry state hcode hP values body'
        callee ret' hargs hl
      by_cases hz : state.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt ⊢
        have bodyClock (hsafe : res ≠ some .timeOut) :
            state.clock - 1 ≤ post.clock + B ∧ post.clock ≤ state.clock - 1 := by
          have hb := hrunBound (by rw [hrun]; exact hsafe)
          rw [hrun] at hb
          exact hb
        cases res with
        | none =>
          obtain ⟨hs, hk⟩ := bodyClock (by simp)
          exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
        | some r =>
          cases r with
          | timeOut => simp at hnt
          | returned value =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            dsimp only
            split
            · exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩
            · exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
          | _ =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩

/-- `GuestInv` instance of `tailCall_on`: no call-site obligation. -/
theorem TerminatingProgBoundedOn.tailCall_guestInv {fname : MlS} {B : Nat}
    (hf : TerminatingFunBoundedOn GuestInv fname B) (arguments : List (ExpHOL 64)) :
    TerminatingProgBoundedOn GuestInv (.call none fname arguments) (B + 1) :=
  TerminatingProgBoundedOn.tailCall_on hf arguments (callEntryOn_guestInv fname arguments)

/-- `decCall`: the continuation runs on `setVar name v {post with locals := caller locals}`;
`GuestInv` of that state follows from `guestInv_evaluate` (no callee preservation hypothesis). -/
theorem TerminatingProgBoundedOn.decCall_guestInv {fname : MlS} {B Bc : Nat}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {continuation : ProgHOL 64}
    (hcont : TerminatingProgBoundedOn GuestInv continuation Bc) :
    TerminatingProgBoundedOn GuestInv (.decCall name shape fname arguments continuation)
      (B + Bc + 1) := by
  obtain ⟨params, body, ret, hlook, hbody⟩ := hf
  have hentry : CallEntryOn GuestInv GuestInv fname arguments := callEntryOn_guestInv fname arguments
  intro F state hcode hP hnt
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
    _ | values
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · simp only [hl] at hnt ⊢
      obtain ⟨hbb, hrunBound⟩ := callee_body_bound hlook hbody hentry state hcode hP values body'
        callee ret' hargs hl
      subst hbb
      by_cases hz : state.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee)
          body').1
        have hpost := guestInv_evaluate (callEntryStateHOLFinite state callee) body'
          (guestInv_callEntry state callee hP)
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt hmeta hpost ⊢
        change post.code = state.code at hmeta
        have bodyClock (hsafe : res ≠ some .timeOut) :
            state.clock - 1 ≤ post.clock + B ∧ post.clock ≤ state.clock - 1 := by
          have hb := hrunBound (by rw [hrun]; exact hsafe)
          rw [hrun] at hb
          exact hb
        cases res with
        | none =>
          obtain ⟨hs, hk⟩ := bodyClock (by simp)
          exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
        | some r =>
          cases r with
          | returned value =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact value) shape &&
                shapeEqHOL (shapeOfHOLExact value) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt ⊢
              set resumed := setVarHOLFinite name value { post with locals := state.locals } with hres
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              have hresInv : GuestInv resumed :=
                guestInv_setVar name value _
                  (guestInv_with_locals_clock post state.locals post.clock hpost)
              have hcb := hcont resumed hresCode hresInv hnt
              obtain ⟨hsc, hkc⟩ := hcb
              change post.clock ≤ (evaluateHOLFiniteState resumed continuation).2.clock + Bc
                at hsc
              change (evaluateHOLFiniteState resumed continuation).2.clock ≤ post.clock at hkc
              exact ⟨by omega, by omega⟩
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
              exact ⟨by omega, by omega⟩
          | timeOut => simp at hnt
          | «break» =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
          | «continue» =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
          | error =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩
          | exception _ _ =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩
          | finalFfi _ =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩

/-- Guarded handler call (round-3 item 2): the callee is guarded by `Pc`, discharged at the call
site by `CallEntryOn P Pc` (e.g. `run_frames` → `op_dispatch` under `EvmInv ∧ ¬ EvmDone` with an
`EvmErr` handler; `finish_child` likewise). The handler runs on a `GuestInv` state
(`guestInv_evaluate` from the caller's `GuestInv`, which `hPG` extracts from `P`), so its bound is
needed only under `GuestInv`. `callHandle_guestInv` is the instance `P = Pc = GuestInv`. -/
theorem TerminatingProgBoundedOn.callHandle_on
    {P Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {fname : MlS} {B Bh : Nat}
    (hf : TerminatingFunBoundedOn Pc fname B)
    (hPG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    (destination : Option (VarKind × MlS)) (exn : MlS) (var : MlS) {handler : ProgHOL 64}
    (hh : TerminatingProgBoundedOn GuestInv handler Bh) (arguments : List (ExpHOL 64))
    (hentry : CallEntryOn P Pc fname arguments) :
    TerminatingProgBoundedOn P
      (.call (some (destination, some (exn, var, handler))) fname arguments) (B + Bh + 1) := by
  obtain ⟨params, body, ret, hlook, hbody⟩ := hf
  intro F state hcode hP hnt
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
    _ | values
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · simp only [hl] at hnt ⊢
      obtain ⟨hbb, hrunBound⟩ := callee_body_bound hlook hbody hentry state hcode hP values body'
        callee ret' hargs hl
      subst hbb
      by_cases hz : state.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee)
          body').1
        have hpost := guestInv_evaluate (callEntryStateHOLFinite state callee) body'
          (guestInv_callEntry state callee (hPG state hP))
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt hmeta hpost ⊢
        change post.code = state.code at hmeta
        have bodyClock (hsafe : res ≠ some .timeOut) :
            state.clock - 1 ≤ post.clock + B ∧ post.clock ≤ state.clock - 1 := by
          have hb := hrunBound (by rw [hrun]; exact hsafe)
          rw [hrun] at hb
          exact hb
        cases res with
        | none =>
          obtain ⟨hs, hk⟩ := bodyClock (by simp)
          exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
        | some r =>
          cases r with
          | timeOut => simp at hnt
          | returned value =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            dsimp only at hnt ⊢
            split
            · rcases destination with _ | ⟨kind, name⟩
              · exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
              · dsimp only
                split
                · cases kind <;>
                    exact ⟨by simp [setKvarHOLFinite, setVarHOLFinite, setGlobalHOLFinite]; omega,
                      by simp [setKvarHOLFinite, setVarHOLFinite, setGlobalHOLFinite]; omega⟩
                · exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
            · exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
          | exception eid v =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            dsimp only at hnt ⊢
            by_cases hid : eid = exn
            · simp only [hid, ↓reduceIte] at hnt ⊢
              rcases hsh : state.eshapes.lookup exn with _ | shape
              · dsimp only
                exact ⟨by omega, by omega⟩
              · simp only [hsh] at hnt ⊢
                by_cases hv : (shapeEqHOL (shapeOfHOLExact v) shape &&
                    isValidValueHOLExact state.toExact .local var v) = true
                · simp only [hv, ↓reduceIte] at hnt ⊢
                  set resumed := setVarHOLFinite var v { post with locals := state.locals }
                  have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
                  have hresInv : GuestInv resumed :=
                    guestInv_setVar var v _
                      (guestInv_with_locals_clock post state.locals post.clock hpost)
                  obtain ⟨hsc, hkc⟩ := hh resumed hresCode hresInv hnt
                  change post.clock ≤ (evaluateHOLFiniteState resumed handler).2.clock + Bh at hsc
                  change (evaluateHOLFiniteState resumed handler).2.clock ≤ post.clock at hkc
                  exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
                · simp only [hv, Bool.false_eq_true, ↓reduceIte]
                  exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
            · simp only [hid, ↓reduceIte]
              exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩
          | _ =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩


/-- Call with an exception handler (e.g. `run_frames` → `op_dispatch` with `EvmErr`):
the handler runs after the callee raised, on a `GuestInv` state (`guestInv_evaluate`). Instance
`P = Pc = GuestInv` of `callHandle_on`. -/
theorem TerminatingProgBoundedOn.callHandle_guestInv {fname : MlS} {B Bh : Nat}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (destination : Option (VarKind × MlS)) (exn : MlS) (var : MlS) {handler : ProgHOL 64}
    (hh : TerminatingProgBoundedOn GuestInv handler Bh) (arguments : List (ExpHOL 64)) :
    TerminatingProgBoundedOn GuestInv
      (.call (some (destination, some (exn, var, handler))) fname arguments) (B + Bh + 1) :=
  TerminatingProgBoundedOn.callHandle_on hf (fun _ h => h) destination exn var hh arguments
    (callEntryOn_guestInv fname arguments)

/-- Guarded `seq`: the second program starts where the first ended, so it needs preservation. -/
theorem TerminatingProgBoundedOn.seq_on
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn P first a) (hp : PreservesOn P P first)
    (h2 : TerminatingProgBoundedOn P second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  intro F state hcode hP
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  have hmid := hp state hcode hP
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt hmid ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simp [hr1]
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) (hmid (by simp)) hnt
    exact ⟨by omega, by omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    exact ⟨by omega, k1⟩

theorem TerminatingProgBoundedOn.ite_on
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {cond : ExpHOL 64}
    {yes no : ProgHOL 64} {a b : Nat}
    (hyes : TerminatingProgBoundedOn P yes a) (hno : TerminatingProgBoundedOn P no b) :
    TerminatingProgBoundedOn P (.ite cond yes no) (max a b) := by
  intro F state hcode hP
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split <;> intro hnt
  · revert hnt
    split <;> intro hnt
    · exact TerminatingRunBounded.weaken (hno state hcode hP) (Nat.le_max_right a b) hnt
    · exact TerminatingRunBounded.weaken (hyes state hcode hP) (Nat.le_max_left a b) hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem TerminatingProgBoundedOn.dec_on
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : LocalsFree P)
    (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} {K : Nat}
    (hbody : TerminatingProgBoundedOn P body K) :
    TerminatingProgBoundedOn P (.dec name shape init body) K := by
  intro F state hcode hPs
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · revert hnt
    split <;> intro hnt
    · rename_i val _ _
      have hb := hbody (setVarHOLFinite name val state) hcode
        (hP state (state.locals.update (name, val)) state.clock hPs) hnt
      simpa [setVarHOLFinite] using hb
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩


/-- Guarded `seq` for `GuestInv`: no preservation hypothesis (`preservesOn_guestInv`). -/
theorem TerminatingProgBoundedOn.seq_guestInv {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn GuestInv first a)
    (h2 : TerminatingProgBoundedOn GuestInv second b) :
    TerminatingProgBoundedOn GuestInv (.seq first second) (a + b) :=
  TerminatingProgBoundedOn.seq_on h1 (preservesOn_guestInv first) h2

/-- A `while` loop head is active: its condition evaluates to a nonzero word (same definition as
`PanTerminatingNoRepeat.LoopActive` on `wave8/step0`). -/
def LoopActive (condition : ExpHOL 64) {F : Type} (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ word : BitVec 64,
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      condition = some (.val (.word word)) ∧ word ≠ 0

/-! ### `while` rules (round-2 item 3)

`evaluate_clock_irrelevant`, `evaluate_ne_of_clock_lt` and `while_unfold_continue` are copied
verbatim from `PanTerminatingNoRepeat` (`wave8/step0`), which this file cannot import (it is not
on this branch's cone). -/

/-- Clock irrelevance for non-`.timeOut` runs (Flapjack `panPropsEvaluateAddClockEq`). -/
theorem evaluate_clock_irrelevant {F : Type} (prog : ProgHOL 64)
    (state post : PanSemStateFiniteExact 64 F) (res : Option (PanSemResultExact 64)) (d : Nat)
    (hrun : evaluateHOLFiniteState state prog = (res, post)) (hnt : res ≠ some .timeOut) :
    evaluateHOLFiniteState { state with clock := state.clock + d } prog =
      (res, { post with clock := post.clock + d }) :=
  panPropsEvaluateAddClockEq prog state res post d ⟨hrun, hnt⟩

/-- A non-`.timeOut` run from `state` cannot have the same outcome as the run from a state that
differs only by having strictly more clock. -/
theorem evaluate_ne_of_clock_lt {F : Type} (prog : ProgHOL 64)
    (state upper : PanSemStateFiniteExact 64 F)
    (hupper : upper = { state with clock := upper.clock }) (hlt : state.clock < upper.clock)
    (hsame : evaluateHOLFiniteState upper prog = evaluateHOLFiniteState state prog)
    (hnt : (evaluateHOLFiniteState state prog).1 ≠ some .timeOut) : False := by
  rcases hrun : evaluateHOLFiniteState state prog with ⟨res, post⟩
  rw [hrun] at hsame hnt
  have hadd := evaluate_clock_irrelevant prog state post res (upper.clock - state.clock) hrun hnt
  have hshift : ({ state with clock := state.clock + (upper.clock - state.clock) } :
      PanSemStateFiniteExact 64 F) = upper := by
    have hsum : state.clock + (upper.clock - state.clock) = upper.clock := by omega
    rw [hsum]
    exact hupper.symm
  rw [hshift, hsame] at hadd
  have hclk := congrArg (fun out => out.2.clock) hadd
  dsimp only at hclk
  omega

/-- One continuing iteration of `.while` hands the rest of the run to the body's post-state. -/
theorem while_unfold_continue {F : Type} (condition : ExpHOL 64) (body : ProgHOL 64)
    (state : PanSemStateFiniteExact 64 F) (word : BitVec 64)
    (hcond : evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      condition = some (.val (.word word)))
    (hword : word ≠ 0) (hclock : state.clock ≠ 0)
    (hflow : (evaluateHOLFiniteState (decClockHOLFinite state) body).1 = none ∨
      (evaluateHOLFiniteState (decClockHOLFinite state) body).1 = some .continue) :
    evaluateHOLFiniteState state (.while condition body) =
      evaluateHOLFiniteState (evaluateHOLFiniteState (decClockHOLFinite state) body).2
        (.while condition body) := by
  rw [evaluateHOLFiniteState_while_fixClockRewrite]
  simp only [hcond, if_pos hword, if_neg hclock]
  rcases hb : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨r, post⟩
  rw [hb] at hflow
  rcases hflow with h | h <;> (dsimp only at h; subst h; rfl)

/-- `t` is an exact repeat of the loop head `s`: every field but the clock agrees. -/
def SameHead {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  t = { s with clock := t.clock }

/-- The rest of the loop, run from `t`, times out (e.g. `modinv_bin`'s halving loop once `u = 0`:
the body is straight-line word arithmetic that always returns, and `u` stays `0`). -/
def WhileTimesOut (condition : ExpHOL 64) (body : ProgHOL 64) {F : Type}
    (t : PanSemStateFiniteExact 64 F) : Prop :=
  (evaluateHOLFiniteState t (.while condition body)).1 = some .timeOut

/-- The stationary alternatives of `while_rank_stationary`: an exact repeat of the loop head, or
a state from which the loop times out. -/
def Stationary (condition : ExpHOL 64) (body : ProgHOL 64) {F : Type}
    (s t : PanSemStateFiniteExact 64 F) : Prop :=
  SameHead s t ∨ WhileTimesOut condition body t

/-- Induction core of `while_rank_stationary`: `n` bounds `μ + 1` at the active loop head. The
body bound is needed only after an ACTIVE `P` loop head (revision 4, round-3 item 1). -/
theorem while_rank_stationary_aux
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {condition : ExpHOL 64}
    {body : ProgHOL 64} {B : Nat}
    (μ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat)
    (hbody : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s → TerminatingRunBounded (decClockHOLFinite s) body B)
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s →
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) →
      P (evaluateHOLFiniteState (decClockHOLFinite s) body).2 ∧
        (μ (evaluateHOLFiniteState (decClockHOLFinite s) body).2 < μ s ∨
          Stationary condition body s (evaluateHOLFiniteState (decClockHOLFinite s) body).2)) :
    ∀ (n : Nat) {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode → P state →
      (LoopActive condition state → μ state + 1 ≤ n) →
      TerminatingRunBounded state (.while condition body) (n * (B + 1)) := by
  intro n
  induction n with
  | zero =>
    intro F state hcode hP hle hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    split
    · rename_i word hword
      by_cases hzero : word = 0
      · rw [if_neg (by simp [hzero])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
      · have := hle ⟨word, hword, hzero⟩
        omega
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  | succ n ih =>
    intro F state hcode hP hle hnt
    have hnt0 := hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    split
    · rename_i word hword
      simp only [hword] at hnt
      by_cases hzero : word = 0
      · rw [if_neg (by simp [hzero])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
      · rw [if_pos hzero] at hnt ⊢
        by_cases hclock : state.clock = 0
        · rw [if_pos hclock] at hnt; exact absurd rfl hnt
        · rw [if_neg hclock] at hnt ⊢
          have hact : LoopActive condition state := ⟨word, hword, hzero⟩
          have hμ := hle hact
          have hb := hbody state hcode hP hact
          have hstep' := hstep state hcode hP hact
          have hunfold := while_unfold_continue condition body state word hword hzero hclock
          have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite state) body).1
          unfold TerminatingRunBounded at hb
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨result, post⟩
          simp only [hrun] at hnt hb hstep' hunfold hmeta
          dsimp only at hb hstep' hunfold hmeta hnt ⊢
          change post.code = state.code at hmeta
          have hcont (hflow : result = none ∨ result = some .continue) :
              state.clock ≤ (evaluateHOLFiniteState post (.while condition body)).2.clock +
                (n + 1) * (B + 1) ∧
              (evaluateHOLFiniteState post (.while condition body)).2.clock ≤ state.clock := by
            have hsafe : result ≠ some .timeOut := by
              rcases hflow with h | h <;> simp [h]
            obtain ⟨hspent, hkept⟩ := hb hsafe
            change state.clock - 1 ≤ post.clock + B at hspent
            change post.clock ≤ state.clock - 1 at hkept
            obtain ⟨hPpost, hdown⟩ := hstep' hflow
            have hsame := hunfold hflow
            have hntPost : (evaluateHOLFiniteState post (.while condition body)).1 ≠
                some .timeOut := by
              rw [← hsame]; exact hnt0
            rcases hdown with hlt | hrep
            · obtain ⟨htail, htailKept⟩ := ih post (hmeta.trans hcode) hPpost
                (fun _ => by omega) hntPost
              have hmul : n * (B + 1) + (B + 1) = (n + 1) * (B + 1) := by
                rw [Nat.succ_mul]
              exact ⟨by omega, by omega⟩
            · exfalso
              rcases hrep with hrep | hto
              · refine evaluate_ne_of_clock_lt (.while condition body) post state ?_
                  (by omega) hsame hntPost
                rw [hrep]
              · exact hntPost hto
          cases result with
          | none => exact hcont (Or.inl rfl)
          | some r =>
            cases r with
            | «continue» => exact hcont (Or.inr rfl)
            | timeOut => exact absurd rfl hnt
            | _ =>
              obtain ⟨hspent, hkept⟩ := hb (by simp)
              change state.clock - 1 ≤ post.clock + B at hspent
              change post.clock ≤ state.clock - 1 at hkept
              simp only
              have hone : B + 1 ≤ (n + 1) * (B + 1) := Nat.le_mul_of_pos_left _ (by omega)
              exact ⟨by omega, by omega⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

/-- Ranking rule with stationary iterations (round-2 item 3). Every continuing iteration from an
active `P` loop head `s` lands in a `P` state that either has a strictly smaller rank
`μ ≤ N`, or is stationary: an exact repeat of `s` (`SameHead`: all fields but the clock agree), or
a state from which the loop times out (`WhileTimesOut`). An exact repeat is a timeout (clock
irrelevance: the run from the repeat is the run from `s` with less clock), so neither needs a
decrease. This is `while_noRepeat` (`wave8/step0`) with the visited-key count replaced by `μ` and
the key collision replaced by `SameHead`. This covers `htab_truncate` (an `htab_del` that finds no matching key writes
nothing), both `fq12_inv` loops, `sort_elems` at width `0` and the `_mpt_insert_node` self-loop.
A loop that becomes stationary only after a warm-up iteration (writes that are idempotent from the
second iteration on) uses `μ = 2·r + [the next iteration is not an exact repeat]`. -/
theorem TerminatingProgBoundedOn.while_rank_stationary
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {condition : ExpHOL 64}
    {body : ProgHOL 64} {B N : Nat}
    (μ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat)
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s))
    (hbody : TerminatingProgBoundedOn P body B)
    (hle : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s → μ s ≤ N)
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s →
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) →
      P (evaluateHOLFiniteState (decClockHOLFinite s) body).2 ∧
        (μ (evaluateHOLFiniteState (decClockHOLFinite s) body).2 < μ s ∨
          Stationary condition body s (evaluateHOLFiniteState (decClockHOLFinite s) body).2)) :
    TerminatingProgBoundedOn P (.while condition body) ((N + 1) * (B + 1)) :=
  fun state hcode hP =>
    while_rank_stationary_aux μ (fun s hc hPs _ => hbody (decClockHOLFinite s) hc (hdec s hPs))
      hstep (N + 1) state hcode hP (fun hact => by have := hle state hcode hP hact; omega)

/-- Ranking rule for `while` (strict decrease on every continuing iteration): the special case of
`while_rank_stationary` without stationary iterations. It covers the loop classes of DESIGN.md §3:
* strict local counter `i < X`, `i := i + 1` (resp. `i ≠ 0`, `i := i - 1`): `μ = X - i` (resp.
  `μ = i`) read from the locals, `N = 2^64`, for ARBITRARY memory (errors inside the body
  terminate the run and are covered);
* fresh-address walk: `μ = heapEnd - address`, `N = W`;
* monotone measure (halving, degree, allocation potential, EVM potential): `N` = its range. -/
theorem TerminatingProgBoundedOn.while_rank
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {condition : ExpHOL 64}
    {body : ProgHOL 64} {B N : Nat}
    (μ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat)
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s))
    (hbody : TerminatingProgBoundedOn P body B)
    (hle : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s → μ s ≤ N)
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s →
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) →
      P (evaluateHOLFiniteState (decClockHOLFinite s) body).2 ∧
        μ (evaluateHOLFiniteState (decClockHOLFinite s) body).2 < μ s) :
    TerminatingProgBoundedOn P (.while condition body) ((N + 1) * (B + 1)) :=
  TerminatingProgBoundedOn.while_rank_stationary μ hdec hbody hle
    fun s hcode hP hact hflow =>
      let h := hstep s hcode hP hact hflow
      ⟨h.1, Or.inl h.2⟩

/-! ### `while` rules with the body needed only on active loop heads (round-3 item 1)

`gb_run_frames` uses `P = GuestInv ∧ (EvmInv ∨ go = 0)`: the last iteration restores `ev` and
`cur_cont` and sets `go := 0`, so `P` must admit exit states that are not `EvmInv`, and from those
the body's guarded callees (`op_dispatch`, `finish_child`, …) have no bound leaf. The body is only
ever run after an active head, so the rules below ask for its bound under
`P s ∧ LoopActive condition s` (for `run_frames`: `go ≠ 0`, hence `EvmInv`). Same proof as
`while_rank_stationary`; the condition is read without the clock, so it survives `decClock`. -/

/-- The loop condition does not read the clock: an active head stays active after `decClock`. -/
theorem loopActive_decClock {condition : ExpHOL 64} {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : LoopActive condition s) : LoopActive condition (decClockHOLFinite s) := by
  obtain ⟨w, hw, hne⟩ := h
  refine ⟨w, ?_, hne⟩
  rw [← hw]
  exact @evalHOLFinite_upd_clock_eq 64 F _ s
    (fun address => Classical.propDecidable (s.memaddrs address)) (s.clock - 1) condition

/-- `while_rank_stationary` with the body bound required only on active `P` heads. -/
theorem TerminatingProgBoundedOn.while_rank_stationary_active
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {condition : ExpHOL 64}
    {body : ProgHOL 64} {B N : Nat}
    (μ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat)
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s))
    (hbody : TerminatingProgBoundedOn (fun s => P s ∧ LoopActive condition s) body B)
    (hle : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s → μ s ≤ N)
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s →
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) →
      P (evaluateHOLFiniteState (decClockHOLFinite s) body).2 ∧
        (μ (evaluateHOLFiniteState (decClockHOLFinite s) body).2 < μ s ∨
          Stationary condition body s (evaluateHOLFiniteState (decClockHOLFinite s) body).2)) :
    TerminatingProgBoundedOn P (.while condition body) ((N + 1) * (B + 1)) :=
  fun state hcode hP =>
    while_rank_stationary_aux μ
      (fun s hc hPs hact => hbody (decClockHOLFinite s) hc ⟨hdec s hPs, loopActive_decClock hact⟩)
      hstep (N + 1) state hcode hP (fun hact => by have := hle state hcode hP hact; omega)

/-- `while_rank` with the body bound required only on active `P` heads (`gb_run_frames`). -/
theorem TerminatingProgBoundedOn.while_rank_active
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {condition : ExpHOL 64}
    {body : ProgHOL 64} {B N : Nat}
    (μ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat)
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s))
    (hbody : TerminatingProgBoundedOn (fun s => P s ∧ LoopActive condition s) body B)
    (hle : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s → μ s ≤ N)
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      P s → LoopActive condition s →
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) →
      P (evaluateHOLFiniteState (decClockHOLFinite s) body).2 ∧
        μ (evaluateHOLFiniteState (decClockHOLFinite s) body).2 < μ s) :
    TerminatingProgBoundedOn P (.while condition body) ((N + 1) * (B + 1)) :=
  TerminatingProgBoundedOn.while_rank_stationary_active μ hdec hbody hle
    fun s hcode hP hact hflow =>
      let h := hstep s hcode hP hact hflow
      ⟨h.1, Or.inl h.2⟩

/-! ### Guards that read locals (round-2 item 3) -/

/-- `P` reads the locals only through the names in `names`, and ignores the clock. Every guard of
the guarded tier has this form: `GuestInv`, `ArenaReady`, `WorldOK`, `EvmInv`, `FinishReady`
(`names = []`), `HtabArgWF` (`["t"]`), `UnionArgWF` (`["dst"]`), `MptReady` (`["node"]`),
`MptObjReady` (`["m"]`), `RollbackReady` (`["child"]`). -/
def LocalsOnly (names : List String) (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) :
    Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (k : Nat), (∀ n ∈ names, locals.lookup (ofString n) = s.locals.lookup (ofString n)) →
    P s → P { s with locals := locals, clock := k }

theorem LocalsOnly.of_localsFree {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (h : LocalsFree P) : LocalsOnly [] P :=
  fun s locals k _ hP => h s locals k hP

theorem localsOnly_guestInv : LocalsOnly [] GuestInv :=
  LocalsOnly.of_localsFree localsFree_guestInv

/-- The clock step of a loop head keeps such a guard (`hdec` of `while_rank`). -/
theorem LocalsOnly.decClock {names : List String}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (h : LocalsOnly names P)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (hP : P s) : P (decClockHOLFinite s) :=
  h s s.locals (s.clock - 1) (fun _ _ => rfl) hP

/-- Declaring a local that the guard does not read keeps the guard. -/
theorem LocalsOnly.setVar {names : List String}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (h : LocalsOnly names P)
    {name : MlS} (hname : ∀ n ∈ names, ofString n ≠ name) (v : ValueHOL 64)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (hP : P s) : P (setVarHOLFinite name v s) := by
  have := h s (s.locals.update (name, v)) s.clock (fun n hn => by
    have hne := hname n hn
    simp only [HolFiniteMapExact.update, FUPDATE]
    split
    · rename_i heq; exact absurd (by simpa using heq) hne.symm
    · rfl) hP
  simpa [setVarHOLFinite] using this

/-- `dec` for a guard that reads locals (round-2 item 3): the declared name must not be one the
guard reads. Every `dec` inside the guarded leaves declares a fresh name (`pos`, `leaf`, `k`, …)
distinct from the guard's parameter (`t`, `dst`, `node`, `m`, `child`). -/
theorem TerminatingProgBoundedOn.dec_onLocals
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {names : List String}
    (hP : LocalsOnly names P) (name : MlS) (hname : ∀ n ∈ names, ofString n ≠ name)
    (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} {K : Nat}
    (hbody : TerminatingProgBoundedOn P body K) :
    TerminatingProgBoundedOn P (.dec name shape init body) K := by
  intro F state hcode hPs
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · revert hnt
    split <;> intro hnt
    · rename_i val _ _
      have hb := hbody (setVarHOLFinite name val state) hcode (hP.setVar hname val state hPs) hnt
      simpa [setVarHOLFinite] using hb
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

/-- The condition of an `ite` evaluates to a nonzero word (resp. to the word `0`). -/
def CondTrue (cond : ExpHOL 64) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w : BitVec 64, @evalHOLExact 64 F _ s.toExact
    (fun address => Classical.propDecidable (s.memaddrs address)) cond = some (.val (.word w)) ∧
    w ≠ 0

def CondFalse (cond : ExpHOL 64) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  @evalHOLExact 64 F _ s.toExact
    (fun address => Classical.propDecidable (s.memaddrs address)) cond = some (.val (.word 0))

/-- `ite` whose branches may use the outcome of the test (a guarded call under a test such as
`kind ≠ 0` before `finish_child`). -/
theorem TerminatingProgBoundedOn.ite_cond_on
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {cond : ExpHOL 64}
    {yes no : ProgHOL 64} {a b : Nat}
    (hyes : TerminatingProgBoundedOn (fun s => P s ∧ CondTrue cond s) yes a)
    (hno : TerminatingProgBoundedOn (fun s => P s ∧ CondFalse cond s) no b) :
    TerminatingProgBoundedOn P (.ite cond yes no) (max a b) := by
  intro F state hcode hP
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split <;> intro hnt
  · rename_i w hw
    revert hnt
    split <;> intro hnt
    · rename_i hz
      subst hz
      exact TerminatingRunBounded.weaken (hno state hcode ⟨hP, hw⟩) (Nat.le_max_right a b) hnt
    · rename_i hz
      exact TerminatingRunBounded.weaken (hyes state hcode ⟨hP, w, hw, hz⟩) (Nat.le_max_left a b)
        hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

/-- What a `decCall`'s continuation may assume: from a `P` caller state whose callee returned
`value` normally, the resumed state (`name := value`, caller locals, callee memory and globals)
satisfies `Q`. Discharged by the callee's contract (`FunSpec`/`FunEnsures`, §7) and, for a guard
reading locals, `LocalsOnly`. -/
def DecCallResumeOn (P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (name : MlS)
    (fname : MlS) (arguments : List (ExpHOL 64)) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
    state.code = originalRuntimeCode → P state →
    evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values →
    lookupCodeHOLFinite state.code.lookup fname values = some (body, callee, returnShape) →
    evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.returned value), post) →
    Q (setVarHOLFinite name value { post with locals := state.locals })

/-- Guarded `decCall`: callee guard `Pc` from `CallEntryOn`, continuation guard `Q` from
`DecCallResumeOn`. `decCall_guestInv` is the instance `P = Pc = Q = GuestInv`. -/
theorem TerminatingProgBoundedOn.decCall_on
    {P Pc Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {fname : MlS} {B Bc : Nat}
    (hf : TerminatingFunBoundedOn Pc fname B)
    (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {continuation : ProgHOL 64}
    (hentry : CallEntryOn P Pc fname arguments)
    (hres : DecCallResumeOn P Q name fname arguments)
    (hcont : TerminatingProgBoundedOn Q continuation Bc) :
    TerminatingProgBoundedOn P (.decCall name shape fname arguments continuation)
      (B + Bc + 1) := by
  obtain ⟨params, body, ret, hlook, hbody⟩ := hf
  intro F state hcode hP hnt
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
    _ | values
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · simp only [hl] at hnt ⊢
      obtain ⟨hbb, hrunBound⟩ := callee_body_bound hlook hbody hentry state hcode hP values body'
        callee ret' hargs hl
      subst hbb
      by_cases hz : state.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee)
          body').1
        have hresQ := hres state values body' callee ret'
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt hmeta ⊢
        change post.code = state.code at hmeta
        have bodyClock (hsafe : res ≠ some .timeOut) :
            state.clock - 1 ≤ post.clock + B ∧ post.clock ≤ state.clock - 1 := by
          have hb := hrunBound (by rw [hrun]; exact hsafe)
          rw [hrun] at hb
          exact hb
        cases res with
        | none =>
          obtain ⟨hs, hk⟩ := bodyClock (by simp)
          exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
        | some r =>
          cases r with
          | returned value =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact value) shape &&
                shapeEqHOL (shapeOfHOLExact value) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt ⊢
              set resumed := setVarHOLFinite name value { post with locals := state.locals } with hres'
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              have hresInv : Q resumed := hresQ value post hcode hP hargs hl hrun
              have hcb := hcont resumed hresCode hresInv hnt
              obtain ⟨hsc, hkc⟩ := hcb
              change post.clock ≤ (evaluateHOLFiniteState resumed continuation).2.clock + Bc
                at hsc
              change (evaluateHOLFiniteState resumed continuation).2.clock ≤ post.clock at hkc
              exact ⟨by omega, by omega⟩
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
              exact ⟨by omega, by omega⟩
          | timeOut => simp at hnt
          | «break» =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
          | «continue» =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
          | _ =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩

/-! ## 4. Bridge: covered entry ⊨ `GuestInv`, and guarded `main` ⇒ covered clock bound -/

/-- A declaration is either not a global, or a global initialised to the constant `0`. -/
def zeroGlobalDecl : DeclHOL 64 → Bool
  | .decl _ _ (.const c) => c == 0
  | .decl _ _ _ => false
  | _ => true

def declGlobalNames : List (DeclHOL 64) → List MlS
  | [] => []
  | .decl _ n _ :: ds => n :: declGlobalNames ds
  | _ :: ds => declGlobalNames ds

theorem evaluateDecls_zero_globals {σ : Type} :
    ∀ (decls : List (DeclHOL 64)) (s s' : PanSemStateFiniteExact 64 σ)
      (h : DecidablePred s.memaddrs),
      @evaluateDeclsHOLFinite 64 σ _ s h decls = some s' →
      decls.all zeroGlobalDecl = true →
      ∀ name : MlS, (s.globals.lookup name = some (.val (.word 0)) ∨ name ∈ declGlobalNames decls) →
        s'.globals.lookup name = some (.val (.word 0)) := by
  intro decls
  induction decls with
  | nil =>
    intro s s' h run _ name hn
    simp only [evaluateDeclsHOLFinite, Option.some.injEq] at run
    subst run
    simpa [declGlobalNames] using hn
  | cons d rest ih =>
    intro s s' h run hall name hn
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨hd, hrest⟩ := hall
    cases d with
    | name _ _ =>
      simp only [evaluateDeclsHOLFinite] at run
      exact ih s s' h run hrest name (by simpa [declGlobalNames] using hn)
    | decl shape n e =>
      cases e with
      | const c =>
        simp only [zeroGlobalDecl, beq_iff_eq] at hd
        subst hd
        simp only [evaluateDeclsHOLFinite] at run
        split at run
        · rename_i v hv
          have hv' : some (ValueHOL.val (HolWordLab.word (0 : BitVec 64))) = some v := hv
          cases hv'
          split at run
          · refine ih _ s' _ run hrest name ?_
            by_cases hname : name = n
            · subst hname
              left
              simp [setGlobalHOLFinite, FUPDATE]
            · simp only [declGlobalNames, List.mem_cons, hname, false_or] at hn
              rcases hn with hn | hn
              · left
                simp [setGlobalHOLFinite, FUPDATE, Ne.symm hname, hn]
              · right; exact hn
          · cases run
        · cases run
      | _ => simp [zeroGlobalDecl] at hd
    | function fi =>
      simp only [evaluateDeclsHOLFinite] at run
      split at run
      · exact ih _ s' _ run hrest name (by simpa [declGlobalNames] using hn)
      · cases run
    | exnDecl en sh =>
      simp only [evaluateDeclsHOLFinite] at run
      split at run
      · exact ih _ s' _ run hrest name (by simpa [declGlobalNames] using hn)
      · cases run

/-- Decl-level counterpart of `zeroGlobalDecl` (cheap to `decide` on the literal AST). -/
def zeroDeclAst : Decl (BitVec 64) → Bool
  | .decl _ _ (.const c) => c == 0
  | .decl _ _ _ => false
  | _ => true

theorem zeroGlobalDecl_declToHOL (d : Decl (BitVec 64)) :
    zeroGlobalDecl (declToHOL d) = zeroDeclAst d := by
  cases d with
  | decl shape name e => cases e <;> simp [declToHOL, expToHOL, zeroGlobalDecl, zeroDeclAst]
  | _ => rfl

theorem guestAst_zero : Guest.Software.guestAst.all zeroDeclAst = true := by decide

theorem mem_guestAst_of_mem_sourceDeclarations {d : DeclHOL 64} (h : d ∈ sourceDeclarations) :
    d ∈ Guest.Software.guestAst.map declToHOL := by
  unfold sourceDeclarations at h
  obtain ⟨before, fi, rest, hsplit, _, hmoved⟩ :=
    Flapjack.Pancake.PanToTarget.mainFirstHOL_of_main
      (Guest.Software.guestAst.map declToHOL) sourceHasMain
  rw [hmoved] at h
  rw [hsplit]
  rcases List.mem_cons.mp h with rfl | h
  · exact List.mem_append_right _ List.mem_cons_self
  · rcases List.mem_append.mp h with hb | hr
    · exact List.mem_append_left _ hb
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)

theorem sourceDeclarations_zero : sourceDeclarations.all zeroGlobalDecl = true := by
  rw [List.all_eq_true]
  intro d hd
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (mem_guestAst_of_mem_sourceDeclarations hd)
  rw [zeroGlobalDecl_declToHOL]
  exact List.all_eq_true.mp guestAst_zero a ha

theorem mem_declGlobalNames {shape : ShapeHOL} {n : MlS} {e : ExpHOL 64} :
    ∀ {l : List (DeclHOL 64)}, DeclHOL.decl shape n e ∈ l → n ∈ declGlobalNames l
  | [], h => by cases h
  | d :: ds, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · have ih := mem_declGlobalNames h
      cases d <;> simp only [declGlobalNames] <;> first | exact ih | exact List.mem_cons_of_mem _ ih

theorem guestGlobalNames_declared :
    ∀ n ∈ guestGlobalNames, ofString n ∈ declGlobalNames sourceDeclarations := by
  intro n hn
  rw [← astGlobalNames_eq] at hn
  obtain ⟨d, hd, hdn⟩ := List.mem_filterMap.mp hn
  cases d with
  | decl shape name e =>
    simp only [Option.some.injEq] at hdn
    subst hdn
    exact mem_declGlobalNames
      (GuestCodeLookup.mem_sourceDeclarations_of_mem (List.mem_map.mpr ⟨_, hd, rfl⟩))
  | _ => simp at hdn

/-- The 67 global declarations evaluate to the word `0` (each is `Decl.decl Shape.one n (const 0)`). -/
theorem postDecls_globals (input : Guest.InputBlob) (stCtxt : StructContextExact)
    (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hdecls : @evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls) :
    ∀ name ∈ guestGlobalNames, GlobalWord s_decls name 0 := fun name hn =>
  evaluateDecls_zero_globals sourceDeclarations _ s_decls _ hdecls sourceDeclarations_zero
    (ofString name) (Or.inr (guestGlobalNames_declared name hn))

/-- The covered post-declarations state satisfies `GuestInv` (four metadata fields). -/
theorem guestInv_postDecls (input : Guest.InputBlob) (stCtxt : StructContextExact)
    (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hdecls : @evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls) :
    GuestInv s_decls := by
  have hmeta := B2PostDecls.evaluateDecls_meta sourceDeclarations
    { sourceInitialState input with structs := stCtxt } s_decls
    (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a)) hdecls
  refine ⟨?_, hmeta.memaddrs, hmeta.shMemaddrs, hmeta.baseAddr⟩
  rw [hmeta.code]
  exact B2PostDecls.map_ext rfl

theorem coveredFfi_postDecls (input : Guest.InputBlob) (stCtxt : StructContextExact)
    (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hgas : Guest.GasLimit.declaredGasLimit input ≤ maxCoveredGas)
    (hdecls : @evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls) :
    CoveredFfi s_decls := by
  have hmeta := B2PostDecls.evaluateDecls_meta sourceDeclarations
    { sourceInitialState input with structs := stCtxt } s_decls
    (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a)) hdecls
  refine ⟨rfl, input, hgas, ?_⟩
  change OracleConsistent sourceOracle (Guest.guestHostMemory input) s_decls.ffi
  rw [hmeta.ffi]
  exact initial_oracle_consistent sourceOracle (Guest.guestHostMemory input)

/-- Generic bridge: any guard `P` that holds at every covered `main` entry state.
Proof adapted from the repaired `coveredSourceTicksConsumedBounded_of_terminatingMain`. -/
theorem coveredSourceTicksConsumedBounded_of_terminatingMainOnP
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {K : Nat}
    (hmain : TerminatingFunBoundedOn P (ofString "main") K)
    (hentry : ∀ (input : Guest.InputBlob) (stCtxt : StructContextExact)
      (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory) (k : Nat)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)),
      Guest.GasLimit.declaredGasLimit input ≤ maxCoveredGas →
      @evaluateDeclsHOLFinite 64 Guest.HostMemory _
        { sourceInitialState input with structs := stCtxt }
        (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
        sourceDeclarations = some s_decls →
      P (callEntryStateHOLFinite { s_decls with clock := k } callee)) :
    CoveredSourceTicksConsumedBounded (K + 1) := by
  obtain ⟨params, body, retShape, hlook, hbody⟩ := hmain
  have hparams : params = [] := by
    rw [lookup_main] at hlook
    have h1 := congrArg Prod.fst (Option.some.inj hlook)
    exact h1.symm.trans rfl
  subst hparams
  intro input outcome events hgas _hsource _hcov stCtxt s_decls _hst hdecls k res s_post hrun hnt
  have hmeta := B2PostDecls.evaluateDecls_meta sourceDeclarations
    { sourceInitialState input with structs := stCtxt } s_decls
    (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a)) hdecls
  have hcode : s_decls.code = originalRuntimeCode := by
    rw [hmeta.code]
    exact B2PostDecls.map_ext rfl
  rw [evaluateHOLFiniteState_call] at hrun
  have hargs : evalListHOLFinite { s_decls with clock := k }
      (h := fun a => Classical.propDecidable (({ s_decls with clock := k } :
        PanSemStateFiniteExact 64 Guest.HostMemory).memaddrs a)) [] = some [] := rfl
  rw [hargs] at hrun
  dsimp only at hrun
  obtain ⟨callee, hlookup_call⟩ : ∃ callee,
      PanSemStateFiniteExact.lookupCodeHOLFinite s_decls.code.lookup (ofString "main") [] =
        some (body, callee, retShape) := by
    rw [hcode]
    rcases hx : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
        (ofString "main") [] with _ | ⟨b, c, r⟩
    · rw [PanSemStateFiniteExact.lookupCodeHOLFinite_eq_none_iff] at hx
      simp [lookupCodeHOLExact, hlook] at hx
    · have hx' := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hx
      simp [lookupCodeHOLExact, hlook] at hx'
      obtain ⟨rfl, -, rfl⟩ := hx'
      exact ⟨c, rfl⟩
  rw [hlookup_call] at hrun
  dsimp only at hrun
  by_cases hk0 : k = 0
  · subst hk0
    simp at hrun
    rcases hrun with ⟨rfl, _⟩
    exact absurd rfl hnt
  · simp only [hk0, ↓reduceIte] at hrun
    let entry := callEntryStateHOLFinite { s_decls with clock := k } callee
    have hentry_code : entry.code = originalRuntimeCode := hcode
    have hentry_P : P entry := hentry input stCtxt s_decls k callee hgas hdecls
    rcases hb_run : evaluateHOLFiniteState entry body with ⟨bres, bpost⟩
    rw [hb_run] at hrun
    have hb_nt : bres ≠ some .timeOut := by
      intro hbt
      subst hbt
      simp at hrun
      rcases hrun with ⟨rfl, _⟩
      exact hnt rfl
    have hb_bound := hbody entry hentry_code hentry_P (by rw [hb_run]; exact hb_nt)
    rw [hb_run] at hb_bound
    obtain ⟨hspent, _⟩ := hb_bound
    have hentry_clk : entry.clock = k - 1 := rfl
    dsimp only at hspent
    have hpost_clk : s_post.clock = bpost.clock := by
      cases bres with
      | none => simp at hrun; obtain ⟨_, rfl⟩ := hrun; rfl
      | some r =>
        cases r <;> simp [emptyLocalsHOLFinite] at hrun
        all_goals (try split at hrun) <;> obtain ⟨_, rfl⟩ := hrun <;> rfl
    omega

/-- Main bridge (the replacement of `coveredSourceTicksConsumedBounded_of_terminatingMain`). -/
theorem coveredSourceTicksConsumedBounded_of_terminatingMainOn {K : Nat}
    (hmain : TerminatingFunBoundedOn GuestInv (ofString "main") K) :
    CoveredSourceTicksConsumedBounded (K + 1) :=
  coveredSourceTicksConsumedBounded_of_terminatingMainOnP hmain
    fun input stCtxt s_decls k callee _ hdecls =>
      guestInv_callEntry _ callee
        (guestInv_with_locals_clock s_decls s_decls.locals k
          (guestInv_postDecls input stCtxt s_decls hdecls))

/-- Covered variant: the guarded main bound may also use the covered input (gas ≤ 2·10^8). -/
theorem coveredSourceTicksConsumedBounded_of_terminatingMainOnCovered {K : Nat}
    (hmain : TerminatingFunBoundedOn GuestInvCovered (ofString "main") K) :
    CoveredSourceTicksConsumedBounded (K + 1) :=
  coveredSourceTicksConsumedBounded_of_terminatingMainOnP hmain
    fun input stCtxt s_decls k callee hgas hdecls =>
      ⟨guestInv_callEntry _ callee
        (guestInv_with_locals_clock s_decls s_decls.locals k
          (guestInv_postDecls input stCtxt s_decls hdecls)),
       coveredFfi_postDecls input stCtxt s_decls hgas hdecls⟩

/-- `main`-only entry guard: the covered entry also fixes memory to the bootstrap image
(`sourceMemory`: 40-byte startup header, zero elsewhere). `alloc` never zeroes, so `main`
may rely on fresh heap cells being `0`; no leaf below `main` gets this conjunct. -/
def InitialMemory : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => s.memory = sourceMemory

/-- All 67 globals still hold their declaration value `0`. -/
def GlobalsZero : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∀ name ∈ guestGlobalNames, GlobalWord s name 0

/-- THE TOP OBLIGATION's guard. `main` is entered exactly once, from the covered
post-declarations state; this guard records everything that is true there: `GuestInv`, the
covered FFI (header gas ≤ 2·10^8), the bootstrap memory image and all globals = 0. It is
strictly stronger than `GuestInv`; only `main` gets it (every other leaf is guarded by
`GuestInv` or by a §7 contract). The campaign target `CoveredSourceTicksConsumedBounded K_pan`
follows from `TerminatingFunBoundedOn MainEntry "main" K.main` alone (bridge below). -/
def MainEntry : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInvCovered s ∧ InitialMemory s ∧ GlobalsZero s

theorem initialMemory_postDecls (input : Guest.InputBlob) (stCtxt : StructContextExact)
    (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory) (k : Nat)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hdecls : @evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls) :
    InitialMemory (callEntryStateHOLFinite { s_decls with clock := k } callee) :=
  (B2PostDecls.evaluateDecls_meta sourceDeclarations
    { sourceInitialState input with structs := stCtxt } s_decls
    (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a)) hdecls).memory

/-- Strongest bridge: guarded by the exact covered entry shape (used for `K_pan`). -/
theorem coveredSourceTicksConsumedBounded_of_terminatingMainOnEntry {K : Nat}
    (hmain : TerminatingFunBoundedOn MainEntry (ofString "main") K) :
    CoveredSourceTicksConsumedBounded (K + 1) :=
  coveredSourceTicksConsumedBounded_of_terminatingMainOnP hmain
    fun input stCtxt s_decls k callee hgas hdecls =>
      ⟨⟨guestInv_callEntry _ callee
          (guestInv_with_locals_clock s_decls s_decls.locals k
            (guestInv_postDecls input stCtxt s_decls hdecls)),
        coveredFfi_postDecls input stCtxt s_decls hgas hdecls⟩,
       initialMemory_postDecls input stCtxt s_decls k callee hdecls,
       fun name hn => postDecls_globals input stCtxt s_decls hdecls name hn⟩

/-- The adapter round 1 asked for: the campaign's target predicate, fully qualified (the name
`CoveredSourceTicksConsumedBounded` also occurs in other files). -/
theorem coveredTarget_of_terminatingMainOnEntry {K : Nat}
    (hmain : TerminatingFunBoundedOn MainEntry (ofString "main") K) :
    InitECandidate.Solver.UniformSourceClock.CoveredSourceTicksConsumedBounded (K + 1) :=
  coveredSourceTicksConsumedBounded_of_terminatingMainOnEntry hmain


/-! ## 5. Memory views and memory contracts (guarded tier only)

Everything in this section is used only by the guarded tier (§7). The unguarded tier (§6) never
looks at memory contents. -/

/-- The word stored at the (aligned) address `a` (`HolWordLab` has the single constructor
`.word`). -/
def memW {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) : Nat :=
  match s.memory (BitVec.ofNat 64 a) with
  | .word w => w.toNat

/-- `a` is an in-domain cell holding a word (what a successful `load` needs). -/
def WordAt {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) : Prop :=
  ∃ w : BitVec 64, s.memaddrs (BitVec.ofNat 64 a) ∧ s.memory (BitVec.ofNat 64 a) = .word w

/-- The global `name` as a natural number (`0` if it is not a word). -/
def globN {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) : Nat :=
  match s.globals.lookup (ofString name) with
  | some (.val (.word w)) => w.toNat
  | _ => 0

/-- The local `name` as a natural number (`0` if absent or not a word). -/
def locN {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) : Nat :=
  match s.locals.lookup (ofString name) with
  | some (.val (.word w)) => w.toNat
  | _ => 0

/-- A memory interval `(base, length)` in bytes. -/
abbrev Ivl := Nat × Nat

def Inside (i : Ivl) (lo hi : Nat) : Prop := lo ≤ i.1 ∧ i.1 + i.2 ≤ hi

def Disj (i j : Ivl) : Prop := i.1 + i.2 ≤ j.1 ∨ j.1 + j.2 ≤ i.1

def InIvl (a : Nat) (i : Ivl) : Prop := i.1 ≤ a ∧ a < i.1 + i.2

/-- Every aligned cell of `i` is an in-domain word. -/
def WordsOK {F : Type} (s : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  i.1 % 8 = 0 ∧ i.2 % 8 = 0 ∧ ∀ k, k < i.2 / 8 → WordAt s (i.1 + 8 * k)

/-! ### Allocator globals -/

/-- The four allocator globals describe separated arenas: the bump heap
`[sourceBase, heap_ptr) ⊆ [sourceBase, 0xb0000000)`, frame memory growing up from `0xb0000000` to
`frame_mem_ptr`, scratch growing down from `0xb0bee000` to `scratch_ptr`. Holds after `mem_init`
(`mem_init_arenaReady`); `alloc`/`scratch_alloc`/`frame_mem_alloc` preserve it by their own
checks; `heap_release`/`scratch_release`/`frame_mem_release` preserve it when their argument is a
mark taken by the same activation (the contract of every caller, §7).

Revision 6 (round-4 Astra item 7): the three pointers are 8-byte aligned. `mem_init` sets them to
`sourceBase`, `0xb0bee000`, `0xb0000000` (all aligned). `alloc` and `frame_mem_alloc` return the
OLD pointer `p` and set the new one to `(p + n + 7) & -8`; `scratch_alloc` sets and returns
`(p - n) & -8` (AST 66, 110, 154). So with aligned pointers every allocation returns an aligned
block and leaves the pointers aligned. The release marks are earlier pointer values (`heap_mark`,
`scratch_mark`, and the continuation marks, aligned by `MarksOK`). Without alignment,
`frame_mem_ptr = 0xb0000001` made `frame_open`'s `frame_mem_alloc(1024)` return an unaligned EVM
memory, which `WordsOK` (in `FrameWF`) rejects. Every contract that ends in `ArenaReady` (all of
§7) now also re-establishes alignment. -/
def ArenaOK {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  sourceBase ≤ globN s "heap_ptr" ∧ globN s "heap_ptr" ≤ heapLimit ∧
  scratchStart ≤ globN s "frame_mem_ptr" ∧ globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" ∧
  globN s "scratch_ptr" ≤ scratchEnd ∧
  globN s "heap_ptr" % 8 = 0 ∧ globN s "frame_mem_ptr" % 8 = 0 ∧ globN s "scratch_ptr" % 8 = 0

def ArenaReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ ArenaOK s

/-- `i` lies in currently allocated heap or scratch memory. -/
def Allocated {F : Type} (s : PanSemStateFiniteExact 64 F) (i : Ivl) : Prop :=
  Inside i sourceBase (globN s "heap_ptr") ∨ Inside i (globN s "scratch_ptr") scratchEnd

/-! ### Crit-bit tables (round-1 item 4)

Layout (`htab_new`, `Guest/SoftwareAst.lean:4867`): header words at `t + 8k`,
`k = 0..10` = key_len, stride, cap, count, keys, nodes, order, root, next, free, ncap.
Node `n` occupies `nodes + 32n .. +32`: `+0` parent (or next free node), `+8`/`+16` children of
an internal node, resp. value / order position of a leaf, `+24` crit bit (`8·key_len` marks a
leaf). Node `0` is the null node. -/

def hdr {F : Type} (s : PanSemStateFiniteExact 64 F) (t k : Nat) : Nat := memW s (t + 8 * k)

def nodeF {F : Type} (s : PanSemStateFiniteExact 64 F) (nodes n off : Nat) : Nat :=
  memW s (nodes + 32 * n + off)

/-- The four memory blocks of table `t`: header, keys, nodes, order. -/
def htabFootprint {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) : List Ivl :=
  [(t, 88), (hdr s t 4, (hdr s t 10 + 1) * hdr s t 1), (hdr s t 5, (hdr s t 10 + 1) * 32),
   (hdr s t 6, (hdr s t 10 + 1) * 8)]

/-- The free list starting at `head`, linked through node field `+0`, is exactly `Fr`. -/
def FreeChain {F : Type} (s : PanSemStateFiniteExact 64 F) (nodes : Nat) : Nat → List Nat → Prop
  | head, [] => head = 0
  | head, f :: rest => head = f ∧ FreeChain s nodes (nodeF s nodes f 0) rest

/-- Structural crit-bit invariant (replaces round 1's `HtabWF`):
* the four blocks are in-domain words, pairwise disjoint;
* `1 ≤ key_len ≤ 60`, `stride = round8 key_len`, `2 ≤ ncap`, `1 ≤ next ≤ ncap + 1`;
* the allocated node indices `[1, next)` split into live leaves `L` (listed by `order[0..count)`,
  so `count = |L|`), internal nodes `I` with `|I| + 1 = count` (or both empty) and the free list
  `Fr` (headed at `t+72`); hence `2·count - 1 ≤ ncap`, so `count ≤ ncap` and every index the code
  computes stays inside its block;
* a leaf has crit bit `8·key_len` and order position `+16` equal to its index in `L`; its value
  `+8` is UNCONSTRAINED (round 1 wrongly bounded it, and `htab_set` overwrites it);
* an internal node has crit bit `< 8·key_len`, two distinct children in `L ∪ I` whose parent
  field `+0` points back to it; the root `t+56` is `0` iff the table is empty, has parent `0`, and
  is nobody's child; every other live node's parent is an internal node that has it as a child;
* rooted and acyclic (round-2 Astra item 4): some depth `dep` strictly decreases from every
  non-root live node to its parent, so following parents from any live node reaches the root,
  and descending through children from the root reaches a leaf. Without it a disconnected cycle
  (`1=(0,7,0,8)`, `2=(3,9,1,8)`, `3=(3,2,3,0)`, root `1`, count `2`) satisfied `HtabWF`, and
  `htab_del` of leaf 1 broke it.
The fields `cap` (`+16`) and the values are free. -/
def HtabWF {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) : Prop :=
  let klen := hdr s t 0
  let cnt := hdr s t 3
  let nodes := hdr s t 5
  let order := hdr s t 6
  let root := hdr s t 7
  let next := hdr s t 8
  let ncap := hdr s t 10
  let nd := nodeF s nodes
  (∀ i ∈ htabFootprint s t, Inside i sourceBase heapEnd ∧ WordsOK s i) ∧
  (htabFootprint s t).Pairwise Disj ∧
  1 ≤ klen ∧ klen ≤ maxKeyLen ∧ hdr s t 1 = (klen + 7) / 8 * 8 ∧
  2 ≤ ncap ∧ 1 ≤ next ∧ next ≤ ncap + 1 ∧
  ∃ L I Fr : List Nat,
    L.length = cnt ∧ (L ++ I ++ Fr).Nodup ∧
    (∀ n, n ∈ L ++ I ++ Fr ↔ 1 ≤ n ∧ n < next) ∧
    ((cnt = 0 ∧ I = []) ∨ I.length + 1 = cnt) ∧
    (∀ (i : Nat) (h : i < L.length),
      memW s (order + 8 * i) = L[i] ∧ nd L[i] 24 = 8 * klen ∧ nd L[i] 16 = i) ∧
    (∀ n ∈ I, nd n 24 < 8 * klen ∧ nd n 8 ∈ L ++ I ∧ nd n 16 ∈ L ++ I ∧ nd n 8 ≠ nd n 16 ∧
      nd (nd n 8) 0 = n ∧ nd (nd n 16) 0 = n) ∧
    (cnt = 0 → root = 0) ∧ (0 < cnt → root ∈ L ++ I ∧ nd root 0 = 0) ∧
    (∀ n ∈ I, nd n 8 ≠ root ∧ nd n 16 ≠ root) ∧
    (∀ n ∈ L ++ I, n ≠ root → nd n 0 ∈ I) ∧
    (∃ dep : Nat → Nat, ∀ n ∈ L ++ I, n ≠ root →
      (nd (nd n 0) 8 = n ∨ nd (nd n 0) 16 = n) ∧ dep (nd n 0) < dep n) ∧
    FreeChain s nodes (hdr s t 9) Fr

/-- Regression (round-2 Astra item 4): no live non-root node is its own parent. Astra's
counterexample has node `3` with parent `3`, so it no longer satisfies `HtabWF`. -/
theorem htabWF_no_self_parent {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat)
    (h : HtabWF s t) : ∃ L I : List Nat, (L.length = hdr s t 3) ∧
      ∀ n ∈ L ++ I, n ≠ hdr s t 7 → nodeF s (hdr s t 5) n 0 ≠ n := by
  obtain ⟨-, -, -, -, -, -, -, -, L, I, -, hlen, -, -, -, -, -, -, -, -, -, ⟨dep, hdep⟩, -⟩ := h
  refine ⟨L, I, hlen, fun n hn hroot heq => ?_⟩
  have := (hdep n hn hroot).2
  rw [heq] at this
  exact Nat.lt_irrefl _ this

/-- Live values of table `t` (the `+8` field of every live leaf). -/
def HtabValuesIn {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) (S : List Nat) : Prop :=
  ∀ i, i < hdr s t 3 → nodeF s (hdr s t 5) (memW s (hdr s t 6 + 8 * i)) 8 ∈ S

/-- The 8-byte memory cell at address `a` meets the byte interval `i` (revision 6, round-4 Astra
item 4). Memory is a map from cell addresses to words; a byte store changes the whole aligned cell
holding the byte. For an aligned `a` and a word-aligned `i` (base and length multiples of 8) this is
exactly `InIvl a i`. -/
def CellHits (a : Nat) (i : Ivl) : Prop := i.1 < a + 8 ∧ a < i.1 + i.2

/-- Memory outside `keep ∪ fresh` is unchanged from `s` to `post`. Addresses are the 64-bit
words themselves, tested through `toNat` (round-2 Astra item 1: quantifying over `a : Nat` and
reading `BitVec.ofNat 64 a` made `x + 2^64` an outside alias of every changed `x`).

Revision 6 (round-4 Astra item 4): the frame is at cell granularity. A cell may change iff it
MEETS a kept region or the fresh region (`CellHits`), not only if its address lies inside one. So a
byte region `(a + 1, 1)` declares the whole cell `a`. Before, `memzero(a + 1, 1)` changed the word
at `a`, outside `[a + 1, a + 2)`, and every byte-writing contract (`ww_memcpy`, `ww_memzero`,
`ww_rlp_encode_bytes`, `ww_rlp_encode_word`, `ww_compute_contract_address`,
`ww_recover_sender_with_chain_id`, the `KeepsOn`/`NodeFn` contracts of byte writers, …) was false
for unaligned regions. The change is in this one definition, so every frame (`WritesWithin`,
`HtabExit`, `UnionExit`, `HtabNewExit`, `MptExit`, `NodeFnExit`) uses it. An owned object is
word-aligned (`WordsOK`); if it is byte-disjoint from every kept region, none of its cells is hit,
so the frame still protects it exactly as before. -/
def FrameOutside {F : Type} (s post : PanSemStateFiniteExact 64 F) (keep : List Ivl)
    (fresh : Ivl) : Prop :=
  ∀ a : BitVec 64, (∀ i ∈ keep, ¬ CellHits a.toNat i) → ¬ CellHits a.toNat fresh →
    post.memory a = s.memory a

/-- Regression (round-2 Astra item 1): a single store inside `fresh` respects the frame. -/
example {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64) (w : HolWordLab 64) :
    FrameOutside s { s with memory := fun b => if b = x then w else s.memory b } [] (x.toNat, 8) := by
  intro a _ hout
  have hne : a ≠ x := by
    rintro rfl
    exact hout ⟨by omega, by omega⟩
  simp [hne]

/-- Regression (revision 6, round-4 Astra item 4): writing the cell `x` for a byte store at
`x + 1` respects the frame of the one-byte region `(x + 1, 1)`. -/
example {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64) (w : HolWordLab 64) :
    FrameOutside s { s with memory := fun b => if b = x then w else s.memory b }
      [(x.toNat + 1, 1)] (0, 0) := by
  intro a hkeep _
  have hne : a ≠ x := by
    rintro rfl
    exact hkeep _ (List.mem_singleton.2 rfl) ⟨by omega, by omega⟩
  simp [hne]

/-- Regression (revision 6): an aligned cell outside an aligned region is not hit, so for
word-aligned objects the cell frame is the old address frame. -/
theorem cellHits_aligned {a : Nat} {i : Ivl} (ha : a % 8 = 0) (hi1 : i.1 % 8 = 0)
    (h : CellHits a i) : InIvl a i := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨by omega, h2⟩

/-- Normal return of a function body from an entry state (callee-entry formulation). -/
def FunEnsures (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      ∀ v, (evaluateHOLFiniteState s body).1 = some (.returned v) →
        Q s (evaluateHOLFiniteState s body).2

/-- Entry of an `htab_*` function: the table parameter `t` is well formed and allocated, the
arenas are separated. -/
def HtabArgWF : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ HtabWF s (locN s "t") ∧
    ∀ i ∈ htabFootprint s (locN s "t"), Allocated s i

/-- Exit contract of the table-mutating functions (`htab_set`, `htab_del`, `htab_truncate`):
the table stays well formed, the heap only grows, the new footprint is the old one plus freshly
allocated heap, and nothing else in memory changes (the write frame that keeps every OTHER table,
frame record and buffer intact). Globals other than `heap_ptr` are unchanged. -/
def HtabExit : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop :=
  fun s post =>
    let t := locN s "t"
    let fresh : Ivl := (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")
    ArenaReady post ∧ HtabWF post t ∧
    globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    (∀ i ∈ htabFootprint post t, Allocated post i ∧
      ((∃ j ∈ htabFootprint s t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
    FrameOutside s post (htabFootprint s t) fresh ∧
    (∀ name, name ≠ "heap_ptr" → s.globals.lookup (ofString name) = post.globals.lookup (ofString name))

/-- `htab_union_into(dst, src)`: the same contract for `dst` (whatever `src` is, even `src = dst`
or a table aliasing `dst`'s header: round-1 item 3). -/
def UnionArgWF : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ HtabWF s (locN s "dst") ∧
    ∀ i ∈ htabFootprint s (locN s "dst"), Allocated s i

def UnionExit : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop :=
  fun s post =>
    let t := locN s "dst"
    let fresh : Ivl := (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")
    ArenaReady post ∧ HtabWF post t ∧
    globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    (∀ i ∈ htabFootprint post t, Allocated post i) ∧
    FrameOutside s post (htabFootprint s t) fresh ∧
    (∀ name, name ≠ "heap_ptr" → s.globals.lookup (ofString name) = post.globals.lookup (ofString name))

/-! ### Global state typing: `WorldOK`

Roots (read off `state_init` 12716-12774, `state_fresh_tx` 12778, `bal_init` 13871): the record
`ws` (40 B; table at `+32`), `bs` (80 B; tables at `+8..+48`, `+72`), `ts` (72 B; tables at
`+8..+64`), the globals `bal_accounts`, `bal_idx_accts`, `bal_idx_stor`, and the journal. A root
slot holding `0` is allowed (every access through it errors: `0 + off ∉ ordinaryDomain`); before
`state_init` all of them are `0`, so `WorldOK` holds right after `mem_init`. `bs+32` and `ts+32`
are tables of tables (`set_storage` 13456, `merge_tx_into_block` 13748): their live values are
tables again. Values of every other table are never written through (accounts are updated
copy-on-write: `set_account_balance`, `increment_nonce`), so they are unconstrained. -/

/-- Record slots holding table pointers. -/
def wsTableSlots : List Nat := [32]
def bsTableSlots : List Nat := [8, 16, 24, 32, 40, 48, 72]
def tsTableSlots : List Nat := [8, 16, 24, 32, 40, 48, 56, 64]
def globalTableRoots : List String := ["bal_accounts", "bal_idx_accts", "bal_idx_stor"]

/-- Every global that holds a buffer allocated with a literal size (`alloc(n)` assigned to the
global in the `*_init` functions, `state_init`, `state_fresh_tx`, `bal_init`; generated by
`coverage.py`, `out/tiers.txt`; revision 4 also folds constant products such as `alloc(256 * 8)`,
adding `bls_discount`, `bn_gamma`, `bn_expw`, `precompile_addrs`, `zero_hashes`), including the records `ws` (40 B), `bs` (80 B), `ts` (72 B). -/
def globalBuffers : List (String × Nat) :=
  [("b2_iv", 64), ("b2_sigma", 80), ("b2_v", 128), ("bal_key_buf", 64), ("be", 120), ("beacon_roots_address", 24), ("bls_c", 7136), ("bls_discount", 2048), ("bn_expw", 352), ("bn_gamma", 384), ("bo", 88), ("bs", 80), ("builder_deposit_address", 24), ("builder_exit_address", 24), ("consolidation_request_address", 24), ("deposit_contract_address", 24), ("deposit_event_signature_hash", 32), ("empty_code_hash", 32), ("empty_trie_root", 32), ("evm_empty", 8), ("evm_key_buf", 32), ("hdr_zero8", 8), ("history_storage_address", 24), ("keccak_pad", 136), ("keccak_rc", 192), ("keccak_st", 200), ("mpt_hash_scratch", 40), ("mpt_key_scratch", 16), ("mpt_nib_scratch", 64), ("null_address", 24), ("pre_hdr_buf", 96), ("precompile_addrs", 360), ("rmd_h", 40), ("rmd_pad", 128), ("rmd_tab", 160), ("rmd_x", 128), ("sha_pad", 128), ("sha_st", 64), ("sk_buf", 64), ("ssz_len_chunk", 32), ("ssz_offs", 64), ("transfer_topic", 32), ("ts", 72), ("u256_ws", 640), ("vm_system_address", 24), ("withdrawal_request_address", 24), ("ws", 40), ("zero32", 32), ("zero_hashes", 2048)]

/-- The block-output objects hanging off the record `bo` (`execute_block` 33580-33609): the
transaction and receipt arrays `bo+24`, `bo+32` (`16·ntx + 16` bytes, `ntx = bo+80`), the request
array `bo+56` (8 slots of 16 bytes), and the two 8-byte-element lists `bo+40` (block logs) and
`bo+72` (`lst_new(8, 16)`: 24-byte header, backing array `8·capacity`). They are written through by
`process_transaction` (33368-33374, `lst_push` 33398/33418) and `requests_append` (33499-33501),
the only writes through a pointer field of a global record outside the frame tier and the typed
table slots (round-3 item 5, `coverage.py` write-root scan, DESIGN.md Q1), so `WorldOK` owns them.
An object whose pointer is still `0` (between `bo := alloc(88)`/`memzero` and the stores) is
empty. -/
def blockOutObjects {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  let bo := globN s "bo"
  let obj (p len : Nat) : Ivl := if bo = 0 ∨ p = 0 then (0, 0) else (p, len)
  let lst (k : Nat) : List Ivl :=
    [obj (memW s (bo + k)) 24, obj (memW s (memW s (bo + k))) (8 * memW s (memW s (bo + k) + 16))]
  [obj (memW s (bo + 24)) (16 * memW s (bo + 80) + 16), obj (memW s (bo + 32)) (16 * memW s (bo + 80) + 16),
   obj (memW s (bo + 56)) 128] ++ lst 40 ++ lst 72

/-- A list header `l` (`lst_new` 24-byte header: data `+0`, length `+8`, capacity `+16`) and its
backing array of `esz`-byte elements. -/
def lstObjects {F : Type} (s : PanSemStateFiniteExact 64 F) (l esz : Nat) : List Ivl :=
  [(l, 24), (memW s l, esz * memW s (l + 16))]

/-- A list can be pushed to and updated in place: `1 ≤` capacity (`lst_push` doubles it) and
length `≤` capacity (`lst_upsert_idx` writes elements below the length). -/
def LstOK {F : Type} (s : PanSemStateFiniteExact 64 F) (l : Nat) : Prop :=
  1 ≤ memW s (l + 16) ∧ memW s (l + 8) ≤ memW s (l + 16)

/-- The live account records of the block access list (round-3 Gemini item 4): the values of the
table `bal_accounts` (`bal_ensure_account` 13883-13917), 40-byte records with two tables (`+0`,
`+8`, `htab_new(32, 8)`) and three lists of 40-, 16- and 24-byte elements (`+16`, `+24`, `+32`),
written through by `add_*_change`, `bal_remove_change`, `lst_upsert_idx`, `lst_push`. -/
def balRecords {F : Type} (s : PanSemStateFiniteExact 64 F) : List Nat :=
  let t := globN s "bal_accounts"
  if t = 0 then [] else
    (List.range (hdr s t 3)).map fun i => nodeF s (hdr s t 5) (memW s (hdr s t 6 + 8 * i)) 8

def balObjects {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  (balRecords s).flatMap fun ad =>
    (ad, 40) :: lstObjects s (memW s (ad + 16)) 40 ++ lstObjects s (memW s (ad + 24)) 16 ++
      lstObjects s (memW s (ad + 32)) 24

/-- The fixed objects: every global buffer (empty while its global is still `0`), the journal
array, the block-output objects (round-3 item 5) and the block-access-list account records with
their lists (round-3 Gemini item 4). -/
def fixedObjects {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++
    [(globN s "journal", 32 * globN s "journal_cap")] ++ blockOutObjects s ++ balObjects s

def RootIn (S : List Nat) (v : Nat) : Prop := v = 0 ∨ v ∈ S

/-- `S` is a set of well-formed, allocated tables with pairwise disjoint footprints, disjoint
from the fixed objects; it contains every root and is closed under the two nested roots. -/
def TablesTyped {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  S.Nodup ∧
  (∀ t ∈ S, HtabWF s t ∧ ∀ i ∈ htabFootprint s t, Allocated s i ∧
    ∀ j ∈ fixedObjects s, Disj i j) ∧
  (∀ t ∈ S, ∀ u ∈ S, t ≠ u → ∀ i ∈ htabFootprint s t, ∀ j ∈ htabFootprint s u, Disj i j) ∧
  (∀ k ∈ wsTableSlots, globN s "ws" ≠ 0 → RootIn S (memW s (globN s "ws" + k))) ∧
  (∀ k ∈ bsTableSlots, globN s "bs" ≠ 0 → RootIn S (memW s (globN s "bs" + k))) ∧
  (∀ k ∈ tsTableSlots, globN s "ts" ≠ 0 → RootIn S (memW s (globN s "ts" + k))) ∧
  (∀ g ∈ globalTableRoots, RootIn S (globN s g)) ∧
  (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ∈ S → HtabValuesIn s (memW s (globN s "bs" + 32)) S) ∧
  (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ∈ S → HtabValuesIn s (memW s (globN s "ts" + 32)) S) ∧
  (∀ ad ∈ balRecords s, memW s ad ∈ S ∧ memW s (ad + 8) ∈ S ∧
    ∀ k ∈ [16, 24, 32], LstOK s (memW s (ad + k))) ∧
  (globN s "bo" ≠ 0 → ∀ k ∈ [40, 72], memW s (globN s "bo" + k) ≠ 0 → LstOK s (memW s (globN s "bo" + k)))

/-- The journal: `journal_n ≤ journal_cap ≤ 2^19`, the array is allocated, and every record's
table (`+0`) is a typed table (`state_restore` calls `htab_set`/`htab_del` on it). -/
def JournalTyped {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  globN s "journal_n" ≤ globN s "journal_cap" ∧ globN s "journal_cap" ≤ journalCapMax ∧
  (globN s "journal_cap" = 0 ∨ (Allocated s (globN s "journal", 32 * globN s "journal_cap") ∧
    WordsOK s (globN s "journal", 32 * globN s "journal_cap"))) ∧
  ∀ i, i < globN s "journal_n" → memW s (globN s "journal" + 32 * i) ∈ S

/-- The fixed objects are allocated words and pairwise disjoint. -/
def FixedTyped {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  (∀ i ∈ fixedObjects s, i.2 = 0 ∨ (Allocated s i ∧ WordsOK s i)) ∧ (fixedObjects s).Pairwise Disj

/-! ### MPT node heap -/

/-- Trie nodes are records of `nodeSize kind` bytes (`node_new_*`): kind at `+0` (`0` hashed, `1` leaf) (`2` extension with child `+48`,
`3` branch with children `+32 + 8i`, `i < 16`), cached encoding `+8/+16`, branch value
`+160/+168`. `NodeHeap s Nd`: the nodes `Nd` are allocated heap records, pairwise disjoint, and
closed under children. -/
def nodeSize (kind : Nat) : Nat :=
  if kind = 0 then 32 else if kind = 1 then 64 else if kind = 2 then 56 else 176

/-- The record of node `n`, sized by its kind (round-3 Gemini item 5: `node_new_hashed` 32 B,
`node_new_leaf` 64 B, `node_new_ext` 56 B, `node_new_branch` 176 B, AST 9975-10060). -/
def nodeIvl {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) : Ivl := (n, nodeSize (memW s n))

/-- The byte at address `a`, as `loadByte` reads it when its cell is in the domain: byte
`a % 8` (by the state's endianness) of the word in the aligned cell `a / 8 * 8` (Flapjack
`panMemLoadByteHOL`, without the domain test). -/
def memB {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) : Nat :=
  match s.memory (panByteAlignHOL (BitVec.ofNat 64 a)) with
  | .word v => (panGetByteHOL (BitVec.ofNat 64 a) v s.be).toNat

/-- The `len` bytes at `p` are nibbles (revision 6, round-4 Astra item 5): `key_to_nibbles` and
`compact_to_nibbles` (AST 9807, 9849) store `b >> 4` and `b & 15` only. -/
def NibblesOK {F : Type} (s : PanSemStateFiniteExact 64 F) (p len : Nat) : Prop :=
  ∀ k, k < len → memB s (p + k) < 16

/-- A nibble array `(p, len)` usable as an MPT key or node path next to the node set `Nd`
(revision 6, round-4 Astra item 5): empty, or nibbles in allocated heap, byte-disjoint from every
node record of `Nd`. The MPT functions write only node records, fresh heap and the free scratch
gap, so such an array survives them (with aligned allocator pointers, `ArenaOK`, no cell of it is
written). `_mpt_insert_node` indexes `node + 32 + 8·b` for a key byte `b` and stores a pointer
there; a byte `18` hit `node + 176`, past the 176-byte branch. -/
def KeyIn {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (p len : Nat) : Prop :=
  len = 0 ∨ (NibblesOK s p len ∧ Allocated s (p, len) ∧ Inside (p, len) sourceBase heapLimit ∧
    ∀ n ∈ Nd, Disj (p, len) (nodeIvl s n))

/-- The path of a leaf (`1`) or extension (`2`) node: pointer `+32`, length `+40`
(`node_new_leaf` 9994, `node_new_ext` 10021); `(0, 0)` for other kinds and empty paths. -/
def nodePath {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) : Ivl :=
  if (memW s n = 1 ∨ memW s n = 2) ∧ memW s (n + 40) ≠ 0 then (memW s (n + 32), memW s (n + 40))
  else (0, 0)

/-- Revision 6 (round-4 Astra item 5): a leaf's or extension's path is a nibble array in the
sense of `KeyIn`. `_split_extension` and `_create_branch_from_two_leaves` index a fresh branch by a
path byte, `_insert_into_leaf`/`_delete_ext_finish`/`_collapse_branch` copy paths into new nodes. -/
def NodeHeap {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) : Prop :=
  (∀ n ∈ Nd, memW s n ≤ 3 ∧ Allocated s (nodeIvl s n) ∧ Inside (nodeIvl s n) sourceBase heapLimit ∧
    WordsOK s (nodeIvl s n) ∧
    (memW s n = 2 → RootIn Nd (memW s (n + 48))) ∧
    (memW s n = 3 → ∀ i, i < 16 → RootIn Nd (memW s (n + 32 + 8 * i))) ∧
    ((memW s n = 1 ∨ memW s n = 2) → KeyIn s Nd (memW s (n + 32)) (memW s (n + 40)))) ∧
  (∀ n ∈ Nd, ∀ m ∈ Nd, n ≠ m → Disj (nodeIvl s n) (nodeIvl s m))

/-- Everything a typed node set occupies: the node records and their paths (revision 6). Writing
any of it can break `NodeHeap`, so owned objects and output regions avoid all of it. -/
def nodeExtents {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) : List Ivl :=
  Nd.flatMap fun n => [nodeIvl s n, nodePath s n]

/-- The persistent tries with their node set exposed (revision 6, round-4 Astra item 2): the
witness state trie `ws+24` and the cached storage tries (live values `v` of table `ws+32` are root
nodes tagged `+1`, `ws_storage_trie` 13042) are typed node heaps whose records and paths are
disjoint from every typed table and fixed object (`compute_state_root` mutates them through
`mpt_set`). -/
def TriesTypedWith {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) : Prop :=
  NodeHeap s Nd ∧
    (∀ o ∈ nodeExtents s Nd, (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj o i) ∧
      ∀ j ∈ fixedObjects s, Disj o j) ∧
    (globN s "ws" ≠ 0 → RootIn Nd (memW s (globN s "ws" + 24)) ∧
      (memW s (globN s "ws" + 32) ∈ S → ∀ i, i < hdr s (memW s (globN s "ws" + 32)) 3 →
        RootIn Nd (nodeF s (hdr s (memW s (globN s "ws" + 32)) 5)
          (memW s (hdr s (memW s (globN s "ws" + 32)) 6 + 8 * i)) 8 - 1)))

def TriesTyped {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  ∃ Nd : List Nat, TriesTypedWith s S Nd

/-- The regions `os` avoid the persistent tries (revision 6, round-4 Astra item 2): some typed
node set of the tries (`TriesTypedWith`, the same `S`) has records and paths disjoint from every
region. A frame object (return data in particular), the message record, or an output buffer over a
trie node made `set_retdata` (kind `4` into a hashed node), `depth0_prepare` or the output writer
break `NodeHeap`. -/
def AvoidsTries {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) (os : List Ivl) :
    Prop :=
  ∃ Nd : List Nat, TriesTypedWith s S Nd ∧ ∀ o ∈ os, ∀ j ∈ nodeExtents s Nd, Disj o j

/-- The global invariant of the guarded tier between EVM frames. -/
def WorldTyped {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  TablesTyped s S ∧ JournalTyped s S ∧ FixedTyped s ∧ TriesTyped s S

def WorldOK : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S : List Nat, WorldTyped s S

/-! ### EVM frames (round-1 item 5)

Frame record `e` (280 B, `frame_new` 15370): `+0` pc, `+8` stack base, `+16` stack height,
`+24/+32/+40` memory base/length/capacity, `+48/+56` code/length, `+64` gas, `+72` state gas,
`+80` jump-destination bitmap, `+88` logs list, `+104` running flag, `+112` message, `+120/+128`
output, `+136` deletion table, `+144/+152/+216` return-data buffer/length/capacity, `+160` error,
`+168/+176` access tables, `+192` spilled gas, `+208/+224` marks, `+232` stack capacity,
`+264/+272` access counts. Continuation record `c` (104 B, `frame_open` 18450, `start_child`
18705): `+0` parent frame, `+8` parent continuation, `+16` kind (`0` = outermost), `+24` journal
snapshot, `+32` done flag, `+40` message, `+48/+56` scratch / frame-memory marks released by
`finish_child`, `+64` new-account flag, `+72/+80` output window in the PARENT's memory, `+88`
contract address, `+96` create snapshot. DESIGN.md Q1 audits every pointer field. -/

/-- The active chain `(ev, cur_cont), (parent ev, parent cont), …`, following `c+0`/`c+8` while
the kind `c+16 ≠ 0` (exactly the `run_frames` / `finish_child` control flow). -/
def evmChainFrom {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat → Nat → Nat → List Ivl
  | 0, _, _ => []
  | fuel + 1, e, c =>
    (e, c) :: (if memW s (c + 16) = 0 then [] else evmChainFrom s fuel (memW s c) (memW s (c + 8)))

def evmChain {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  evmChainFrom s (maxChain + 1) (globN s "ev") (globN s "cur_cont")

/-- The current frame cannot run another instruction (`run_frames` 18675-18681). -/
abbrev EvmDone {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  memW s (globN s "cur_cont" + 32) ≠ 0 ∨ memW s (globN s "ev" + 104) = 0 ∨
    memW s (globN s "ev" + 56) ≤ memW s (globN s "ev")

/-- The logs backing array of frame `e`: header `h = e+88` holds data `+0`, length `+8`, capacity
`+16`; elements are 8-byte log pointers (`frame_new` 15407: `lst_new_scratch(8, 4)`). It starts in
scratch and `lst_push` (13842) regrows it on the HEAP (round-2 Astra item 5). -/
def frameLogs {F : Type} (s : PanSemStateFiniteExact 64 F) (ec : Ivl) : Ivl :=
  (memW s (memW s (ec.1 + 88)), 8 * memW s (memW s (ec.1 + 88) + 16))

/-- The return-data buffer of frame `e` (round-3 item 4): pointer `e+144`, capacity `e+216`.
`set_retdata` (19064) writes `n ≤ cap` bytes at the pointer, and when `cap < n` replaces it by
`alloc(n + 8)`, a heap block of `round8 (n + 8)` bytes. With capacity `0` nothing is ever written
through the pointer (`n = 0` returns early, `n > 0` reallocates); it is then `evm_empty`
(`frame_new` 15431, `set_retdata` 19074) and the block is empty, `(0, 0)`. -/
def frameRet {F : Type} (s : PanSemStateFiniteExact 64 F) (ec : Ivl) : Ivl :=
  if memW s (ec.1 + 216) = 0 then (0, 0)
  else (memW s (ec.1 + 144), (memW s (ec.1 + 216) + 15) / 8 * 8)

/-- The memory blocks a frame writes: record, continuation, stack, EVM memory, logs header, logs
backing array, return-data buffer. Index 3 (EVM memory) lives in the frame-memory arena, index 5
(logs array) in the heap or scratch, index 6 (return data, round-3 item 4) in the heap, the others
in scratch. -/
def frameObjects {F : Type} (s : PanSemStateFiniteExact 64 F) (ec : Ivl) : List Ivl :=
  [(ec.1, 280), (ec.2, 104), (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)),
   (memW s (ec.1 + 24), memW s (ec.1 + 40)), (memW s (ec.1 + 88), 24), frameLogs s ec,
   frameRet s ec]

/-- The scratch-resident blocks of a frame (`frameObjects` without EVM memory and logs array). -/
def frameScratch {F : Type} (s : PanSemStateFiniteExact 64 F) (ec : Ivl) : List Ivl :=
  [(ec.1, 280), (ec.2, 104), (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)),
   (memW s (ec.1 + 88), 24)]

/-- One frame: record, continuation, stack and logs header in allocated scratch; EVM memory in
the frame-memory arena below `frame_mem_ptr`; logs backing array in allocated heap or scratch;
return-data buffer in allocated heap, or capacity `0` with pointer `evm_empty`;
`1 ≤` stack capacity (round-3 item 3: `PUSH0` on capacity `0` made `stack_push` allocate a
0-word stack and store past it), stack height ≤ capacity ≤ 1024, memory length ≤ capacity,
`1 ≤` logs capacity (round-3 item 3: `lst_push` on capacity `0` regrows to `0` and sets length 1),
logs length ≤ capacity; its three tables are typed. `frame_new` gives capacities 32 and 4;
`stack_push` (15080) doubles up to 1024 and `lst_push` (13856) doubles, so both stay `≥ 1`. -/
def FrameWF {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) (ec : Ivl) : Prop :=
  let e := ec.1
  (∀ i ∈ [(e, 280), (ec.2, 104), (memW s (e + 8), 32 * memW s (e + 232)), (memW s (e + 88), 24)],
    Inside i (globN s "scratch_ptr") scratchEnd ∧ WordsOK s i) ∧
  Inside (memW s (e + 24), memW s (e + 40)) scratchStart (globN s "frame_mem_ptr") ∧
  WordsOK s (memW s (e + 24), memW s (e + 40)) ∧
  1 ≤ memW s (e + 232) ∧ memW s (e + 16) ≤ memW s (e + 232) ∧ memW s (e + 232) ≤ 1024 ∧
  memW s (e + 32) ≤ memW s (e + 40) ∧
  memW s (e + 136) ∈ S ∧ memW s (e + 168) ∈ S ∧ memW s (e + 176) ∈ S ∧
  1 ≤ memW s (memW s (e + 88) + 16) ∧
  memW s (memW s (e + 88) + 8) ≤ memW s (memW s (e + 88) + 16) ∧
  (Inside (frameLogs s ec) sourceBase (globN s "heap_ptr") ∨
    Inside (frameLogs s ec) (globN s "scratch_ptr") scratchEnd) ∧
  WordsOK s (frameLogs s ec) ∧
  ((memW s (e + 216) = 0 ∧ memW s (e + 144) = globN s "evm_empty") ∨
    (Inside (frameRet s ec) sourceBase (globN s "heap_ptr") ∧ WordsOK s (frameRet s ec)))

/-- A suspended frame has room for one more stack word (round-2 item 2). `finish_child`
(`Guest/SoftwareAst.lean:18572`) runs `stack_push` on the parent BEFORE
`scratch_release(child_mark)`; on a full parent `stack_push` would allocate a new 64-slot stack
below the child's mark, which the release then frees. Every frame below the current one was
suspended by one of the six frame-opening opcodes (`op_call`, `op_callcode`, `op_delegatecall`,
`op_staticcall` pop 6 or 7 words and push at most one; `op_create`, `op_create2` pop 3 or 4) after
those pops, so `op_dispatch_spec` re-establishes it for the new parent. -/
def FrameRoom {F : Type} (s : PanSemStateFiniteExact 64 F) (ec : Ivl) : Prop :=
  memW s (ec.1 + 16) + 1 ≤ memW s (ec.1 + 232)

/-- Output windows of the suspended frames (round-3 item 4). `finish_child` (18650-18652) copies
`min(c+80, child+128)` bytes to `parent_mem + c+72`, where `c` is the child's continuation and
`parent_mem`, `parent_mem + capacity` are the parent's `e+24`, `e+40`. So for every chain position
`i` with a parent, either the window is empty (`c_i+80 = 0`: `op_call` passes
`sat_word(out_start)`, which is arbitrary when the size is `0`, so the sum need not be in range)
or it lies inside the parent's EVM memory. `op_call`/`op_callcode`/`op_delegatecall`/
`op_staticcall` establish it by `extend_memory` on the output window BEFORE `generic_call` →
`start_child` stores the window (18746-18748); `op_create`/`op_create2` store size `0`. The parent
is suspended, so nothing changes its memory capacity until `finish_child`. -/
def RetWindowsOK {F : Type} (s : PanSemStateFiniteExact 64 F) (ch : List Ivl) : Prop :=
  ∀ (i : Nat) (hi : i + 1 < ch.length),
    memW s ((ch[i]'(by omega)).2 + 80) = 0 ∨
      memW s ((ch[i]'(by omega)).2 + 72) + memW s ((ch[i]'(by omega)).2 + 80) ≤
        memW s (ch[i + 1].1 + 40)

/-- The live values of table `t` (the `+8` field of every live leaf). -/
def htabValues {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) : List Nat :=
  (List.range (hdr s t 3)).map fun i => nodeF s (hdr s t 5) (memW s (hdr s t 6 + 8 * i)) 8

/-- The table slots `ks` of the global record `g` (none while `g = 0`). -/
def recordSlots {F : Type} (s : PanSemStateFiniteExact 64 F) (g : String) (ks : List Nat) :
    List Nat :=
  if globN s g = 0 then [] else ks.map fun k => memW s (globN s g + k)

/-- Every table pointer the world state holds outside the frames (revision 6, round-4 Astra item
1), read off `TablesTyped`/`JournalTyped`: the record slots of `ws`, `bs`, `ts`, the global roots,
the live values of the tables of tables `bs+32`, `ts+32` (when typed), the two tables of every BAL
account record, and the table of every journal record. -/
def worldTableRefs {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : List Nat :=
  let nest (g : String) : List Nat :=
    if globN s g ≠ 0 ∧ memW s (globN s g + 32) ∈ S then htabValues s (memW s (globN s g + 32))
    else []
  recordSlots s "ws" wsTableSlots ++ recordSlots s "bs" bsTableSlots ++
    recordSlots s "ts" tsTableSlots ++ globalTableRoots.map (globN s) ++ nest "bs" ++ nest "ts" ++
    (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) ++
    (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k))

/-- The table `t` released with the child at chain position `i` is referenced only as the deletion
table of frames `0..i` (the child and its descendants), all of which die with the child (revision
6, round-4 Astra item 1): no world reference (`worldTableRefs`), and every frame slot `+136`,
`+168`, `+176` of the chain holding `t` is a deletion slot `+136` at a position `j ≤ i`. -/
def DelExclusive {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) (ch : List Ivl)
    (i t : Nat) : Prop :=
  t ∉ worldTableRefs s S ∧
  ∀ (j : Nat) (hj : j < ch.length), ∀ k ∈ [136, 168, 176], memW s (ch[j].1 + k) = t → k = 136 ∧ j ≤ i

/-- Release marks of the child at chain position `i` (whose continuation is `c_i`): releasing
scratch to `c_i+48` and frame memory to `c_i+56` frees exactly the child's scratch blocks and keeps
every ancestor's blocks allocated (an ancestor's logs array is on the heap or above the mark).
Round-3 Astra item 3: the release must also keep every SURVIVING typed table and fixed object
allocated. The only table ever built in scratch is a frame's deletion table `e+136`
(`frame_new` → `htab_new_scratch`, its only caller; `htab_copy_scratch` is unreachable), so every
table of `S` other than the deletion tables of frames `0..i` lies in the heap or above the mark,
and so does every non-empty fixed object. Astra's witness (a shared `htab_new_scratch` table at
`0xb0bdffa8` below the child's mark `0xb0be8000`) violates this.

Revision 6 (round-4 Astra item 1): the exemption is EXCLUSIVE. A table of `S` may lie below the
mark only if it is the deletion table of a frame `j ≤ i` AND `DelExclusive`: no world root, nested
root or journal record names it, and no frame slot other than a deletion slot `e_j+136` with
`j ≤ i` does. Astra's witness (`parent+136 = bal_idx_accts = child+136 = 0xb0bed2f8`, mark
`0xb0bed8a8`) has the child's deletion table named by the parent and by a global root, so it must
lie in the heap or above the mark, and the child-error release no longer frees it. The marks are
8-byte aligned (revision 6, round-4 Astra item 7: `finish_child` releases to them, `ArenaOK`). -/
def MarksOK {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) (ch : List Ivl) : Prop :=
  ∀ (i : Nat) (hi : i + 1 < ch.length),
    let m := memW s ((ch[i]'(by omega)).2 + 48)
    let mm := memW s ((ch[i]'(by omega)).2 + 56)
    m ≤ scratchEnd ∧ scratchStart ≤ mm ∧ m % 8 = 0 ∧ mm % 8 = 0 ∧
    (∀ j (hj : j < ch.length), i < j →
      (∀ o ∈ frameScratch s ch[j], Inside o m scratchEnd) ∧
      Inside (frameObjects s ch[j])[3]! scratchStart mm ∧
      (Inside (frameLogs s ch[j]) sourceBase heapLimit ∨ Inside (frameLogs s ch[j]) m scratchEnd)) ∧
    (∀ o ∈ frameScratch s (ch[i]'(by omega)), o.1 + o.2 ≤ m) ∧
    mm ≤ memW s ((ch[i]'(by omega)).1 + 24) ∧
    (∀ t ∈ S, (t ∈ (ch.take (i + 1)).map (fun ec => memW s (ec.1 + 136)) ∧ DelExclusive s S ch i t) ∨
      ∀ o ∈ htabFootprint s t, Inside o sourceBase heapLimit ∨ Inside o m scratchEnd) ∧
    (∀ o ∈ fixedObjects s, o.2 = 0 ∨ Inside o sourceBase heapLimit ∨ Inside o m scratchEnd)

/-- The EVM invariant at every `run_frames` loop head (replaces round 1's `EvmFramesWF`): the
world is typed (one table set `S` covering global AND frame tables), the chain is closed (its
last continuation has kind `0`) and at most `maxChain` long, every frame is well formed, every
suspended frame (`ch.tail`) has stack room for the result `finish_child` pushes (`FrameRoom`), every
child's output window lies in its parent's EVM memory (`RetWindowsOK`, round-3 item 4), all
frame blocks (return-data buffers included) are pairwise disjoint and disjoint from every table
footprint and fixed object, disjoint from the persistent tries (revision 6, round-4 Astra item 2:
`AvoidsTries`; a parent return-data pointer `ws+24 = n` on a hashed node made `set_retdata` write
kind `4` into it), the release marks are valid, and the regular gas `R` (gas plus
spilled gas over the chain) is below `2^64 − 1` (round-3 Gemini items 1-2: with a frame's gas at
`2^64 − 1`, `charge_gas` accepts the saturated out-of-gas sentinel of `extend_memory_cost1/2`, and
`op_mstore`/`op_extcodecopy`/… then write outside EVM memory; `R` never grows along `run_frames`,
and starts as the message gas, `MsgReady`). This is the only gas conjunct: the potential `evmPot` is bounded for
arbitrary gas words. -/
def EvmInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S : List Nat, WorldTyped s S ∧
    let ch := evmChain s
    ch ≠ [] ∧ ch.length ≤ maxChain ∧ (∃ ec ∈ ch.getLast?, memW s (ec.2 + 16) = 0) ∧
    (∀ ec ∈ ch, FrameWF s S ec) ∧ (∀ ec ∈ ch.tail, FrameRoom s ec) ∧ RetWindowsOK s ch ∧
    ((ch.map (frameObjects s)).flatten).Pairwise Disj ∧
    (∀ ec ∈ ch, ∀ o ∈ frameObjects s ec,
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj o i) ∧ ∀ j ∈ fixedObjects s, Disj o j) ∧
    AvoidsTries s S (ch.map (frameObjects s)).flatten ∧
    MarksOK s S ch ∧
    (ch.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum + 1 < 2 ^ 64

/-! Round-1 item 5 regressions, by construction of `EvmInv`/`evmPot`:
* minting gas (`refill_frame_state_gas` with `spilled = 2^62`, `incorporate_child_on_error`) can
  only move gas between the `R` and `S` components of `evmPot`, whose ranges are bounded by the
  word size, not by any gas invariant;
* `ev+8 = ev` (stack over the record) violates the pairwise disjointness of `frameObjects`;
* a wild `cur_cont+48` violates `MarksOK`. -/

def evmPotS : Nat := maxChain * 2 ^ 64
def evmPotF : Nat := 2 * maxChain + 2

/-- Lexicographic EVM potential `(R, F, S)` as one number:
`R = Σ (gas + spilled)` over the chain, `F = 2·depth + [not done]`, `S = Σ state gas`.
Every word is `< 2^64` and `depth ≤ maxChain`, so `F < evmPotF`, `S < evmPotS` and
`evmPot < evmPotMax` for ARBITRARY gas contents. A continuing `run_frames` iteration
* charges regular gas (`R` drops; `CALL` moves gas to the child without changing `R`), or
* charges only state gas (`S` drops, `R`, `F` unchanged), or
* halts the frame (`F` drops by one; `refill_frame_state_gas` keeps `R` and may raise `S`), or
* pops a done frame (`finish_child`: `F` drops by at least one; `incorporate_child_on_*` adds
  the child's `gas (+ spilled)` to the parent, so `R` does not grow; state-gas refunds only
  raise `S`). -/
def evmPot {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  let ch := evmChain s
  let R := (ch.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum
  let Fp := 2 * ch.length + (if EvmDone s then 0 else 1)
  let S := (ch.map fun ec => memW s (ec.1 + 72)).sum
  R * (evmPotF * evmPotS) + Fp * evmPotS + S

def evmPotMax : Nat := (2 * maxChain * 2 ^ 64 + 1) * evmPotF * evmPotS

/-- The `run_frames` loop (`while go != 0 …`, `Guest/SoftwareAst.lean:18672`), read off the
installed code. -/
def runFramesLoop : Option (ExpHOL 64 × ProgHOL 64) :=
  match originalRuntimeCode.lookup (ofString "run_frames") with
  | some (_, .dec _ _ _ (.seq (.while c b) _), _) => some (c, b)
  | _ => none

/-! ## 6. Generated bounds and unguarded leaves

GENERATED by `campaign/notes/guestinv/scripts/coverage.py` from `Guest/SoftwareAst.lean`; do not
edit by hand. `K.«f»` is the tick bound of function `f`: the sum over its body of
`K.«g» + 1` per call (plus the handler), `(N + 1) * (body + 1)` per `while` (with `N` the loop's
iteration bound, DESIGN.md §3-§5), `Nat.max` over the two branches of an `ite`. There is no
recursion on `main`'s call graph, so the definitions are in dependency order. -/

namespace K

/-- `trap_with` (AST line 26), log2 ≈ 0. -/
def «trap_with» : Nat := 0

/-- `alloc` (AST line 66), log2 ≈ 2. -/
def «alloc» : Nat := Nat.max ((«trap_with» + 1)) (0) + Nat.max ((«trap_with» + 1)) (0)

/-- `mpt_fail` (AST line 9769), log2 ≈ 0. -/
def «mpt_fail» : Nat := 0

/-- `memcpy` (AST line 198), log2 ≈ 65. -/
def «memcpy» : Nat := Nat.max (((domainBytes + 1) + 1) * (0 + 1) + ((domainBytes + 1) + 1) * (0 + 1)) (0) + ((domainBytes + 1) + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1)

/-- `nibbles_concat` (AST line 9922), log2 ≈ 66. -/
def «nibbles_concat» : Nat := («alloc» + 1) + («memcpy» + 1) + («memcpy» + 1)

/-- `node_new_ext` (AST line 10021), log2 ≈ 2. -/
def «node_new_ext» : Nat := («alloc» + 1)

/-- `node_new_leaf` (AST line 9994), log2 ≈ 2. -/
def «node_new_leaf» : Nat := («alloc» + 1)

/-- `_collapse_branch` (AST line 10674), log2 ≈ 66. -/
def «_collapse_branch» : Nat := (2 ^ 64 + 1) * (0 + 1) + Nat.max (Nat.max ((«mpt_fail» + 1)) (0) + («node_new_leaf» + 1)) (0) + Nat.max (Nat.max ((«mpt_fail» + 1)) (0) + («alloc» + 1) + Nat.max ((«node_new_ext» + 1)) (0) + («nibbles_concat» + 1) + Nat.max ((«node_new_leaf» + 1)) (0) + («node_new_ext» + 1)) (0)

/-- `memzero` (AST line 251), log2 ≈ 65. -/
def «memzero» : Nat := Nat.max (((domainBytes + 1) + 1) * (0 + 1) + ((domainBytes + 1) + 1) * (0 + 1)) (0) + ((domainBytes + 1) + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1)

/-- `node_new_branch` (AST line 10046), log2 ≈ 65. -/
def «node_new_branch» : Nat := («alloc» + 1) + («memzero» + 1)

/-- `_create_branch_from_two_leaves` (AST line 10507), log2 ≈ 65. -/
def «_create_branch_from_two_leaves» : Nat := («node_new_branch» + 1) + Nat.max (0) ((«node_new_leaf» + 1)) + Nat.max (0) ((«node_new_leaf» + 1))

/-- `key_to_nibbles` (AST line 9807), log2 ≈ 65. -/
def «key_to_nibbles» : Nat := ((domainBytes + 1) + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1)

/-- `compact_to_nibbles` (AST line 9849), log2 ≈ 65. -/
def «compact_to_nibbles» : Nat := Nat.max ((«mpt_fail» + 1)) (0) + («alloc» + 1) + («key_to_nibbles» + 1)

/-- `rlp_fail` (AST line 4305), log2 ≈ 0. -/
def «rlp_fail» : Nat := 0

/-- `rlp_read_length` (AST line 4317), log2 ≈ 65. -/
def «rlp_read_length» : Nat := Nat.max ((«rlp_fail» + 1)) (0) + (2 ^ 64 + 1) * (0 + 1)

/-- `rlp_item_header` (AST line 4432), log2 ≈ 66. -/
def «rlp_item_header» : Nat := Nat.max ((«rlp_fail» + 1)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0)) (0)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0) + («rlp_read_length» + 1) + Nat.max ((«rlp_fail» + 1)) (0) + Nat.max ((«rlp_fail» + 1)) (0)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0)) (0) + Nat.max ((«rlp_fail» + 1)) (0) + («rlp_read_length» + 1) + Nat.max ((«rlp_fail» + 1)) (0) + Nat.max ((«rlp_fail» + 1)) (0)

/-- `scratch_alloc` (AST line 154), log2 ≈ 2. -/
def «scratch_alloc» : Nat := Nat.max ((«trap_with» + 1)) (0) + Nat.max ((«trap_with» + 1)) (0)

/-- `_rlp_validate_items_body` (AST line 4507), log2 ≈ 319. -/
def «_rlp_validate_items_body» : Nat := (((2 ^ 61 + 1) * 2 ^ 192) + 1) * (Nat.max (0) ((«rlp_item_header» + 1) + Nat.max ((«scratch_alloc» + 1)) (0)) + 1)

/-- `scratch_mark` (AST line 176), log2 ≈ 0. -/
def «scratch_mark» : Nat := 0

/-- `scratch_release` (AST line 186), log2 ≈ 0. -/
def «scratch_release» : Nat := 0

/-- `rlp_validate_items` (AST line 4548), log2 ≈ 319. -/
def «rlp_validate_items» : Nat := («scratch_mark» + 1) + («_rlp_validate_items_body» + 1) + («scratch_release» + 1) + («scratch_release» + 1)

/-- `rlp_item_total` (AST line 4567), log2 ≈ 319. -/
def «rlp_item_total» : Nat := («rlp_item_header» + 1) + Nat.max ((«rlp_validate_items» + 1)) (0)

/-- `rlp_list_count` (AST line 4582), log2 ≈ 447. -/
def «rlp_list_count» : Nat := (2 ^ 128 + 1) * ((«rlp_item_total» + 1) + 1)

/-- `rlp_item` (AST line 4338), log2 ≈ 448. -/
def «rlp_item» : Nat := Nat.max ((«rlp_fail» + 1)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0)) (0)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0) + («rlp_read_length» + 1) + Nat.max ((«rlp_fail» + 1)) (0) + Nat.max ((«rlp_fail» + 1)) (0)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0) + («rlp_list_count» + 1)) (0) + Nat.max ((«rlp_fail» + 1)) (0) + («rlp_read_length» + 1) + Nat.max ((«rlp_fail» + 1)) (0) + Nat.max ((«rlp_fail» + 1)) (0) + («rlp_list_count» + 1)

/-- `rlp_decode_fully` (AST line 4417), log2 ≈ 448. -/
def «rlp_decode_fully» : Nat := («rlp_item» + 1) + Nat.max ((«rlp_fail» + 1)) (0)

/-- `rlp_item_total_unchecked` (AST line 4600), log2 ≈ 66. -/
def «rlp_item_total_unchecked» : Nat := Nat.max ((«rlp_read_length» + 1)) (0) + («rlp_read_length» + 1)

/-- `rlp_list_to_slices` (AST line 4631), log2 ≈ 447. -/
def «rlp_list_to_slices» : Nat := («rlp_list_count» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«rlp_item_total_unchecked» + 1) + 1)

/-- `_decode_step` (AST line 10110), log2 ≈ 449. -/
def «_decode_step» : Nat := («rlp_decode_fully» + 1) + («mpt_fail» + 1) + Nat.max ((«mpt_fail» + 1)) (0) + («rlp_list_to_slices» + 1) + Nat.max ((«rlp_item» + 1) + Nat.max ((«mpt_fail» + 1)) (0) + («compact_to_nibbles» + 1) + Nat.max ((«rlp_item» + 1) + Nat.max ((«mpt_fail» + 1)) (0) + («node_new_leaf» + 1)) (0) + Nat.max ((«mpt_fail» + 1)) (0) + («scratch_alloc» + 1)) (0) + Nat.max ((«mpt_fail» + 1)) (0) + («node_new_branch» + 1) + («scratch_alloc» + 1)

/-- `node_new_hashed` (AST line 9975), log2 ≈ 2. -/
def «node_new_hashed» : Nat := («alloc» + 1)

/-- `htab_find_leaf` (AST line 4976), log2 ≈ 65. -/
def «htab_find_leaf» : Nat := (2 ^ 64 + 1) * (0 + 1)

/-- `memeq` (AST line 304), log2 ≈ 67. -/
def «memeq» : Nat := Nat.max ((2 ^ 64 + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1)) (0) + (2 ^ 64 + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1)

/-- `htab_get` (AST line 4999), log2 ≈ 67. -/
def «htab_get» : Nat := («htab_find_leaf» + 1) + («memeq» + 1)

/-- `nodedb_lookup` (AST line 9960), log2 ≈ 67. -/
def «nodedb_lookup» : Nat := («htab_get» + 1)

/-- `_resolve_step` (AST line 10077), log2 ≈ 448. -/
def «_resolve_step» : Nat := («rlp_item» + 1) + («mpt_fail» + 1) + Nat.max (Nat.max ((«mpt_fail» + 1)) (0) + («nodedb_lookup» + 1) + Nat.max ((«node_new_hashed» + 1)) (0)) (0)

/-- `_decode_witness_node_body` (AST line 10196), log2 ≈ 517. -/
def «_decode_witness_node_body» : Nat := (2 ^ 68 + 1) * (Nat.max ((«_decode_step» + 1)) (Nat.max ((«_resolve_step» + 1)) (Nat.max (0) (Nat.max (Nat.max ((«mpt_fail» + 1)) (0) + Nat.max ((«mpt_fail» + 1)) (0) + («node_new_ext» + 1)) (Nat.max (0) ((«rlp_item» + 1) + Nat.max ((«mpt_fail» + 1)) (0)))))) + 1)

/-- `_decode_witness_node_mpt` (AST line 10311), log2 ≈ 517. -/
def «_decode_witness_node_mpt» : Nat := («_decode_witness_node_body» + 1) + («scratch_release» + 1)

/-- `_decode_witness_node` (AST line 10328), log2 ≈ 517. -/
def «_decode_witness_node» : Nat := («scratch_mark» + 1) + («_decode_witness_node_mpt» + 1) + («scratch_release» + 1) + («scratch_release» + 1)

/-- `_delete_ext_finish` (AST line 10727), log2 ≈ 66. -/
def «_delete_ext_finish» : Nat := Nat.max ((«mpt_fail» + 1)) (0) + («nibbles_concat» + 1) + Nat.max ((«node_new_ext» + 1)) (0) + («node_new_leaf» + 1)

/-- `min` (AST line 667), log2 ≈ 0. -/
def «min» : Nat := 0

/-- `common_prefix_length` (AST line 9903), log2 ≈ 65. -/
def «common_prefix_length» : Nat := («min» + 1) + (2 ^ 64 + 1) * (0 + 1)

/-- `_insert_into_leaf` (AST line 10532), log2 ≈ 67. -/
def «_insert_into_leaf» : Nat := Nat.max ((«memeq» + 1)) (0) + («common_prefix_length» + 1) + («_create_branch_from_two_leaves» + 1) + Nat.max ((«node_new_ext» + 1)) (0)

/-- `node_invalidate` (AST line 10061), log2 ≈ 0. -/
def «node_invalidate» : Nat := 0

/-- `_mpt_delete_node_body` (AST line 10758), log2 ≈ 197. -/
def «_mpt_delete_node_body» : Nat := (2 ^ 130 + 1) * (Nat.max (0) (Nat.max ((«mpt_fail» + 1)) (0) + («node_invalidate» + 1) + Nat.max (Nat.max ((«memeq» + 1)) (0)) (Nat.max ((«common_prefix_length» + 1) + Nat.max (0) ((«scratch_alloc» + 1))) (Nat.max (Nat.max (0) ((«_collapse_branch» + 1))) ((«scratch_alloc» + 1))))) + 1) + (2 ^ 64 + 1) * (Nat.max ((«_delete_ext_finish» + 1)) ((«_collapse_branch» + 1)) + 1)

/-- `_mpt_delete_node` (AST line 10852), log2 ≈ 197. -/
def «_mpt_delete_node» : Nat := («scratch_mark» + 1) + («_mpt_delete_node_body» + 1) + («scratch_release» + 1) + («scratch_release» + 1)

/-- `_split_extension` (AST line 10561), log2 ≈ 65. -/
def «_split_extension» : Nat := («node_new_branch» + 1) + Nat.max ((«node_new_ext» + 1)) (0) + Nat.max (0) (Nat.max ((«mpt_fail» + 1)) (0) + («node_new_leaf» + 1))

/-- `_mpt_insert_node` (AST line 10598), log2 ≈ 197. -/
def «_mpt_insert_node» : Nat := (2 ^ 130 + 1) * (Nat.max ((«node_new_leaf» + 1)) (Nat.max ((«mpt_fail» + 1)) (0) + («node_invalidate» + 1) + Nat.max ((«_insert_into_leaf» + 1)) (Nat.max ((«common_prefix_length» + 1) + Nat.max (0) ((«_split_extension» + 1) + Nat.max ((«node_new_ext» + 1)) (0))) (0))) + 1)

/-- `_node_needs_rlp` (AST line 10989), log2 ≈ 0. -/
def «_node_needs_rlp» : Nat := 0

/-- `nibble_list_to_compact` (AST line 9877), log2 ≈ 35. -/
def «nibble_list_to_compact» : Nat := ((domainBytes + 1) + 1) * (0 + 1)

/-- `rlp_be_len` (AST line 4698), log2 ≈ 129. -/
def «rlp_be_len» : Nat := (2 ^ 128 + 1) * (0 + 1)

/-- `rlp_header_len` (AST line 4753), log2 ≈ 129. -/
def «rlp_header_len» : Nat := («rlp_be_len» + 1)

/-- `rlp_bytes_encoded_len` (AST line 4827), log2 ≈ 129. -/
def «rlp_bytes_encoded_len» : Nat := («rlp_header_len» + 1)

/-- `rlp_value_encoded_len` (AST line 11095), log2 ≈ 129. -/
def «rlp_value_encoded_len» : Nat := («rlp_bytes_encoded_len» + 1)

/-- `_node_rlp_begin` (AST line 10890), log2 ≈ 130. -/
def «_node_rlp_begin» : Nat := Nat.max ((«alloc» + 1) + («nibble_list_to_compact» + 1) + («rlp_bytes_encoded_len» + 1) + Nat.max ((«rlp_value_encoded_len» + 1)) (0)) (0)

/-- `node_ref_len` (AST line 11110), log2 ≈ 1. -/
def «node_ref_len» : Nat := Nat.max ((«mpt_fail» + 1)) (0)

/-- `keccak_f1600` (AST line 4038), log2 ≈ 65. -/
def «keccak_f1600» : Nat := (2 ^ 64 + 1) * (0 + 1)

/-- `keccak_absorb_block` (AST line 4239), log2 ≈ 66. -/
def «keccak_absorb_block» : Nat := (2 ^ 64 + 1) * (0 + 1) + («keccak_f1600» + 1)

/-- `keccak256` (AST line 4262), log2 ≈ 100. -/
def «keccak256» : Nat := («memzero» + 1) + ((domainBytes + 1) + 1) * ((«keccak_absorb_block» + 1) + 1) + («memzero» + 1) + («memcpy» + 1) + («keccak_absorb_block» + 1) + Nat.max (0) ((«memcpy» + 1))

/-- `node_hash_cached` (AST line 11137), log2 ≈ 100. -/
def «node_hash_cached» : Nat := Nat.max ((«mpt_fail» + 1)) (0) + («alloc» + 1) + («keccak256» + 1)

/-- `node_write_ref` (AST line 11161), log2 ≈ 100. -/
def «node_write_ref» : Nat := Nat.max ((«memcpy» + 1)) (0) + Nat.max ((«mpt_fail» + 1)) (0) + Nat.max ((«memcpy» + 1)) (0) + («node_hash_cached» + 1) + («memcpy» + 1)

/-- `rlp_put_be` (AST line 4714), log2 ≈ 65. -/
def «rlp_put_be» : Nat := (2 ^ 64 + 1) * (0 + 1)

/-- `rlp_write_header` (AST line 4732), log2 ≈ 129. -/
def «rlp_write_header» : Nat := («rlp_be_len» + 1) + («rlp_put_be» + 1)

/-- `rlp_encode_bytes` (AST line 4768), log2 ≈ 129. -/
def «rlp_encode_bytes» : Nat := («rlp_write_header» + 1) + («memcpy» + 1)

/-- `rlp_encode_list_header` (AST line 4817), log2 ≈ 129. -/
def «rlp_encode_list_header» : Nat := («rlp_write_header» + 1)

/-- `rlp_list_header_len` (AST line 4842), log2 ≈ 129. -/
def «rlp_list_header_len» : Nat := («rlp_header_len» + 1)

/-- `_node_rlp_finish` (AST line 10930), log2 ≈ 164. -/
def «_node_rlp_finish» : Nat := Nat.max ((«node_ref_len» + 1)) (0) + Nat.max ((2 ^ 64 + 1) * ((«node_ref_len» + 1) + 1) + («rlp_value_encoded_len» + 1)) (0) + («rlp_list_header_len» + 1) + («alloc» + 1) + («rlp_encode_list_header» + 1) + Nat.max ((«rlp_encode_bytes» + 1) + Nat.max ((«rlp_encode_bytes» + 1)) ((«node_write_ref» + 1))) ((2 ^ 64 + 1) * ((«node_write_ref» + 1) + 1) + («rlp_encode_bytes» + 1))

/-- `_node_rlp_fill` (AST line 11011), log2 ≈ 256. -/
def «_node_rlp_fill» : Nat := («scratch_mark» + 1) + («scratch_alloc» + 1) + («_node_rlp_begin» + 1) + (2 ^ 62 + 1) * (Nat.max (Nat.max ((«_node_needs_rlp» + 1)) (0)) (Nat.max ((2 ^ 192 + 1) * ((«_node_needs_rlp» + 1) + 1)) (0)) + Nat.max ((«scratch_alloc» + 1) + («_node_rlp_begin» + 1)) ((«_node_rlp_finish» + 1)) + 1) + («scratch_release» + 1)

/-- `htab_has` (AST line 5022), log2 ≈ 67. -/
def «htab_has» : Nat := («htab_find_leaf» + 1) + («memeq» + 1)

/-- `is_warm_address` (AST line 15473), log2 ≈ 67. -/
def «is_warm_address» : Nat := («htab_has» + 1)

/-- `access_gas_cost` (AST line 15496), log2 ≈ 67. -/
def «access_gas_cost» : Nat := («is_warm_address» + 1)

/-- `access_list_payload_len` (AST line 11977), log2 ≈ 194. -/
def «access_list_payload_len» : Nat := (2 ^ 64 + 1) * ((«rlp_list_header_len» + 1) + («rlp_list_header_len» + 1) + 1)

/-- `htab_first_diff` (AST line 4951), log2 ≈ 129. -/
def «htab_first_diff» : Nat := (2 ^ 64 + 1) * (Nat.max ((2 ^ 64 + 1) * (0 + 1)) (0) + 1)

/-- `htab_grow` (AST line 5117), log2 ≈ 66. -/
def «htab_grow» : Nat := («alloc» + 1) + («memcpy» + 1) + («alloc» + 1) + («memcpy» + 1) + («alloc» + 1) + («memcpy» + 1)

/-- `htab_new_node` (AST line 5041), log2 ≈ 66. -/
def «htab_new_node» : Nat := Nat.max ((«htab_grow» + 1)) (0)

/-- `htab_new_internal` (AST line 5097), log2 ≈ 66. -/
def «htab_new_internal» : Nat := («htab_new_node» + 1)

/-- `htab_new_leaf` (AST line 5068), log2 ≈ 67. -/
def «htab_new_leaf» : Nat := («htab_new_node» + 1) + («memcpy» + 1)

/-- `htab_set` (AST line 5149), log2 ≈ 130. -/
def «htab_set» : Nat := («htab_find_leaf» + 1) + Nat.max ((«htab_new_leaf» + 1)) (0) + («memeq» + 1) + («htab_first_diff» + 1) + (2 ^ 128 + 1) * (0 + 1) + («htab_new_leaf» + 1) + («htab_new_internal» + 1)

/-- `record_pre_state_read` (AST line 12980), log2 ≈ 130. -/
def «record_pre_state_read» : Nat := («htab_set» + 1)

/-- `decode_account_from_leaf` (AST line 11266), log2 ≈ 450. -/
def «decode_account_from_leaf» : Nat := («rlp_decode_fully» + 1) + («mpt_fail» + 1) + Nat.max ((«mpt_fail» + 1)) (0) + («rlp_list_to_slices» + 1) + Nat.max ((«mpt_fail» + 1)) (0) + («rlp_item» + 1) + («rlp_item» + 1) + («rlp_item» + 1) + («rlp_item» + 1) + Nat.max ((«mpt_fail» + 1)) (0) + Nat.max ((«mpt_fail» + 1)) (0) + (2 ^ 64 + 1) * (0 + 1) + Nat.max ((«mpt_fail» + 1)) (0) + («memzero» + 1) + (2 ^ 64 + 1) * (0 + 1) + Nat.max (0) (Nat.max ((«mpt_fail» + 1)) (0)) + Nat.max (0) (Nat.max ((«mpt_fail» + 1)) (0))

/-- `heap_mark` (AST line 88), log2 ≈ 0. -/
def «heap_mark» : Nat := 0

/-- `heap_release` (AST line 98), log2 ≈ 0. -/
def «heap_release» : Nat := 0

/-- `trie_walk` (AST line 10376), log2 ≈ 196. -/
def «trie_walk» : Nat := (2 ^ 128 + 1) * (Nat.max ((«mpt_fail» + 1)) (0) + Nat.max (Nat.max ((«memeq» + 1)) (0)) (0) + Nat.max ((«memeq» + 1)) (0) + 1)

/-- `trie_lookup` (AST line 10432), log2 ≈ 196. -/
def «trie_lookup» : Nat := («key_to_nibbles» + 1) + («trie_walk» + 1)

/-- `ws_account_leaf` (AST line 12992), log2 ≈ 196. -/
def «ws_account_leaf» : Nat := («heap_mark» + 1) + («alloc» + 1) + («keccak256» + 1) + («trie_lookup» + 1) + («heap_release» + 1)

/-- `ws_get_account_optional` (AST line 13009), log2 ≈ 450. -/
def «ws_get_account_optional» : Nat := («ws_account_leaf» + 1) + («alloc» + 1) + («decode_account_from_leaf» + 1)

/-- `ws_storage_root_of` (AST line 13027), log2 ≈ 450. -/
def «ws_storage_root_of» : Nat := («ws_get_account_optional» + 1)

/-- `ws_account_has_storage` (AST line 13119), log2 ≈ 450. -/
def «ws_account_has_storage» : Nat := («ws_storage_root_of» + 1) + («memeq» + 1)

/-- `account_has_storage` (AST line 13330), log2 ≈ 450. -/
def «account_has_storage» : Nat := («htab_get» + 1) + («htab_get» + 1) + («record_pre_state_read» + 1) + («ws_account_has_storage» + 1)

/-- `acct_new` (AST line 12937), log2 ≈ 2. -/
def «acct_new» : Nat := («alloc» + 1)

/-- `acct_empty` (AST line 12956), log2 ≈ 3. -/
def «acct_empty» : Nat := («acct_new» + 1)

/-- `get_pre_state_account_optional` (AST line 13135), log2 ≈ 450. -/
def «get_pre_state_account_optional» : Nat := («htab_set» + 1) + («htab_get» + 1) + («record_pre_state_read» + 1) + («ws_get_account_optional» + 1)

/-- `get_account_optional` (AST line 13170), log2 ≈ 450. -/
def «get_account_optional» : Nat := («htab_set» + 1) + («htab_get» + 1) + («get_pre_state_account_optional» + 1)

/-- `get_account` (AST line 13188), log2 ≈ 450. -/
def «get_account» : Nat := («get_account_optional» + 1) + Nat.max ((«acct_empty» + 1)) (0)

/-- `account_deployable` (AST line 13358), log2 ≈ 451. -/
def «account_deployable» : Nat := («get_account» + 1) + («memeq» + 1) + («account_has_storage» + 1)

/-- `account_exists` (AST line 13315), log2 ≈ 450. -/
def «account_exists» : Nat := («get_account_optional» + 1)

/-- `acct_copy` (AST line 12967), log2 ≈ 65. -/
def «acct_copy» : Nat := («alloc» + 1) + («memcpy» + 1)

/-- `u256_is_zero` (AST line 814), log2 ≈ 0. -/
def «u256_is_zero» : Nat := 0

/-- `acct_is_empty` (AST line 13383), log2 ≈ 67. -/
def «acct_is_empty» : Nat := («memeq» + 1) + («u256_is_zero» + 1)

/-- `htab_new` (AST line 4867), log2 ≈ 4. -/
def «htab_new» : Nat := («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1)

/-- `lst_new` (AST line 13804), log2 ≈ 3. -/
def «lst_new» : Nat := («alloc» + 1) + («alloc» + 1)

/-- `bal_ensure_account` (AST line 13883), log2 ≈ 130. -/
def «bal_ensure_account» : Nat := («htab_get» + 1) + («alloc» + 1) + («htab_new» + 1) + («htab_new» + 1) + («lst_new» + 1) + («lst_new» + 1) + («lst_new» + 1) + («htab_set» + 1)

/-- `lst_push` (AST line 13840), log2 ≈ 65. -/
def «lst_push» : Nat := Nat.max ((«alloc» + 1) + («memcpy» + 1)) (0)

/-- `lst_upsert_idx` (AST line 13919), log2 ≈ 66. -/
def «lst_upsert_idx» : Nat := (2 ^ 64 + 1) * (0 + 1) + («lst_push» + 1)

/-- `add_balance_change` (AST line 13978), log2 ≈ 130. -/
def «add_balance_change» : Nat := («bal_ensure_account» + 1) + («lst_upsert_idx» + 1)

/-- `add_code_change` (AST line 14023), log2 ≈ 130. -/
def «add_code_change» : Nat := («bal_ensure_account» + 1) + («lst_upsert_idx» + 1)

/-- `add_nonce_change` (AST line 13992), log2 ≈ 130. -/
def «add_nonce_change» : Nat := («bal_ensure_account» + 1) + (2 ^ 64 + 1) * (0 + 1) + («lst_push» + 1)

/-- `add_sat` (AST line 14847), log2 ≈ 0. -/
def «add_sat» : Nat := 0

/-- `add_storage_read` (AST line 13965), log2 ≈ 131. -/
def «add_storage_read» : Nat := («bal_ensure_account» + 1) + («htab_set» + 1)

/-- `add_storage_write` (AST line 13942), log2 ≈ 131. -/
def «add_storage_write» : Nat := («bal_ensure_account» + 1) + («htab_get» + 1) + Nat.max ((«lst_new» + 1) + («htab_set» + 1)) (0) + («lst_upsert_idx» + 1)

/-- `add_to_bloom` (AST line 31915), log2 ≈ 100. -/
def «add_to_bloom» : Nat := («heap_mark» + 1) + («alloc» + 1) + («keccak256» + 1) + (2 ^ 64 + 1) * (0 + 1) + («heap_release» + 1)

/-- `add_touched_account` (AST line 14039), log2 ≈ 130. -/
def «add_touched_account» : Nat := («bal_ensure_account» + 1)

/-- `st_be32` (AST line 585), log2 ≈ 0. -/
def «st_be32» : Nat := 0

/-- `bswap64` (AST line 525), log2 ≈ 0. -/
def «bswap64» : Nat := 0

/-- `st_be64` (AST line 603), log2 ≈ 2. -/
def «st_be64» : Nat := Nat.max ((«bswap64» + 1)) (0) + («st_be32» + 1) + («st_be32» + 1)

/-- `addr_from_words` (AST line 32506), log2 ≈ 4. -/
def «addr_from_words» : Nat := («st_be32» + 1) + («st_be64» + 1) + («st_be64» + 1)

/-- `u256_from_be` (AST line 2213), log2 ≈ 65. -/
def «u256_from_be» : Nat := Nat.max ((«bswap64» + 1) + («bswap64» + 1) + («bswap64» + 1) + («bswap64» + 1)) (0) + (2 ^ 64 + 1) * (0 + 1)

/-- `address_to_u256` (AST line 14906), log2 ≈ 65. -/
def «address_to_u256» : Nat := («u256_from_be» + 1)

/-- `udivmod` (AST line 695), log2 ≈ 65. -/
def «udivmod» : Nat := Nat.max ((«trap_with» + 1)) (0) + (2 ^ 64 + 1) * (0 + 1)

/-- `udiv` (AST line 727), log2 ≈ 65. -/
def «udiv» : Nat := («udivmod» + 1)

/-- `check_gas_limit` (AST line 9590), log2 ≈ 65. -/
def «check_gas_limit» : Nat := («udiv» + 1)

/-- `bal_init` (AST line 13863), log2 ≈ 6. -/
def «bal_init» : Nat := («htab_new» + 1) + («htab_new» + 1) + («htab_new» + 1) + («alloc» + 1)

/-- `htab_keys` (AST line 5332), log2 ≈ 129. -/
def «htab_keys» : Nat := («alloc» + 1) + (2 ^ 64 + 1) * ((«memcpy» + 1) + 1)

/-- `rlp_encode_word` (AST line 4790), log2 ≈ 129. -/
def «rlp_encode_word» : Nat := («rlp_be_len» + 1) + («rlp_put_be» + 1)

/-- `bit_length64` (AST line 1919), log2 ≈ 0. -/
def «bit_length64» : Nat := 0

/-- `u256_bit_length` (AST line 1966), log2 ≈ 3. -/
def «u256_bit_length» : Nat := Nat.max ((«bit_length64» + 1)) (0) + Nat.max ((«bit_length64» + 1)) (0) + Nat.max ((«bit_length64» + 1)) (0) + («bit_length64» + 1)

/-- `u256_byte_length` (AST line 1991), log2 ≈ 3. -/
def «u256_byte_length» : Nat := («u256_bit_length» + 1)

/-- `u256_limb` (AST line 828), log2 ≈ 0. -/
def «u256_limb» : Nat := 0

/-- `u256_to_be_min` (AST line 2302), log2 ≈ 66. -/
def «u256_to_be_min» : Nat := («u256_byte_length» + 1) + (2 ^ 64 + 1) * ((«u256_limb» + 1) + 1)

/-- `rlp_put_u256` (AST line 9334), log2 ≈ 129. -/
def «rlp_put_u256» : Nat := («heap_mark» + 1) + («alloc» + 1) + («u256_to_be_min» + 1) + («rlp_encode_bytes» + 1) + («heap_release» + 1)

/-- `bal_sort_gt` (AST line 14327), log2 ≈ 65. -/
def «bal_sort_gt» : Nat := (2 ^ 64 + 1) * (0 + 1)

/-- `sort_elems` (AST line 14364), log2 ≈ 201. -/
def «sort_elems» : Nat := («heap_mark» + 1) + («alloc» + 1) + (65 + 1) * ((2 ^ 64 + 1) * ((2 ^ 65 + 1) * ((«bal_sort_gt» + 1) + («memcpy» + 1) + 1) + (2 ^ 64 + 1) * ((«memcpy» + 1) + 1) + (2 ^ 64 + 1) * ((«memcpy» + 1) + 1) + 1) + 1) + Nat.max ((«memcpy» + 1)) (0) + («heap_release» + 1)

/-- `sorted_keys32` (AST line 14442), log2 ≈ 201. -/
def «sorted_keys32» : Nat := («htab_keys» + 1) + («sort_elems» + 1)

/-- `bal_encode_account` (AST line 14455), log2 ≈ 265. -/
def «bal_encode_account» : Nat := («rlp_encode_bytes» + 1) + («heap_mark» + 1) + («sorted_keys32» + 1) + (2 ^ 64 + 1) * ((«htab_get» + 1) + («sort_elems» + 1) + («u256_from_be» + 1) + («rlp_put_u256» + 1) + (2 ^ 64 + 1) * ((«rlp_encode_word» + 1) + («rlp_put_u256» + 1) + («rlp_list_header_len» + 1) + («memcpy» + 1) + («rlp_encode_list_header» + 1) + 1) + («rlp_list_header_len» + 1) + («memcpy» + 1) + («rlp_encode_list_header» + 1) + («rlp_list_header_len» + 1) + («memcpy» + 1) + («rlp_encode_list_header» + 1) + 1) + («rlp_list_header_len» + 1) + («memcpy» + 1) + («rlp_encode_list_header» + 1) + («htab_keys» + 1) + (2 ^ 64 + 1) * ((«htab_has» + 1) + 1) + («sort_elems» + 1) + (2 ^ 64 + 1) * ((«u256_from_be» + 1) + («rlp_put_u256» + 1) + 1) + («rlp_list_header_len» + 1) + («memcpy» + 1) + («rlp_encode_list_header» + 1) + («sort_elems» + 1) + (2 ^ 64 + 1) * ((«rlp_encode_word» + 1) + («rlp_put_u256» + 1) + («rlp_list_header_len» + 1) + («memcpy» + 1) + («rlp_encode_list_header» + 1) + 1) + («rlp_list_header_len» + 1) + («memcpy» + 1) + («rlp_encode_list_header» + 1) + («sort_elems» + 1) + (2 ^ 64 + 1) * ((«rlp_encode_word» + 1) + («rlp_encode_word» + 1) + («rlp_list_header_len» + 1) + («memcpy» + 1) + («rlp_encode_list_header» + 1) + 1) + («rlp_list_header_len» + 1) + («memcpy» + 1) + («rlp_encode_list_header» + 1) + («sort_elems» + 1) + (2 ^ 64 + 1) * ((«rlp_encode_word» + 1) + («rlp_encode_bytes» + 1) + («rlp_list_header_len» + 1) + («memcpy» + 1) + («rlp_encode_list_header» + 1) + 1) + («rlp_list_header_len» + 1) + («memcpy» + 1) + («rlp_encode_list_header» + 1) + («heap_release» + 1) + («rlp_list_header_len» + 1) + («memcpy» + 1) + («rlp_encode_list_header» + 1)

/-- `htab_item` (AST line 5314), log2 ≈ 0. -/
def «htab_item» : Nat := 0

/-- `build_block_access_list_rlp` (AST line 14685), log2 ≈ 329. -/
def «build_block_access_list_rlp» : Nat := (2 ^ 64 + 1) * ((«htab_item» + 1) + Nat.max ((«add_storage_read» + 1)) (0) + 1) + (2 ^ 64 + 1) * ((«htab_item» + 1) + Nat.max ((«add_touched_account» + 1)) (0) + 1) + («alloc» + 1) + («htab_keys» + 1) + («sort_elems» + 1) + (2 ^ 64 + 1) * ((«htab_get» + 1) + (2 ^ 64 + 1) * ((«htab_item» + 1) + 1) + (2 ^ 64 + 1) * (0 + 1) + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«htab_get» + 1) + («bal_encode_account» + 1) + 1) + («rlp_list_header_len» + 1) + («rlp_encode_list_header» + 1)

/-- `mpt_new` (AST line 10444), log2 ≈ 2. -/
def «mpt_new» : Nat := («alloc» + 1)

/-- `node_rlp` (AST line 11074), log2 ≈ 256. -/
def «node_rlp» : Nat := Nat.max ((«mpt_fail» + 1)) (0) + («_node_rlp_fill» + 1)

/-- `node_hash` (AST line 11202), log2 ≈ 256. -/
def «node_hash» : Nat := («node_rlp» + 1) + («alloc» + 1) + («keccak256» + 1)

/-- `mpt_root` (AST line 11223), log2 ≈ 256. -/
def «mpt_root» : Nat := Nat.max ((«memcpy» + 1)) (0) + («node_hash» + 1) + («memcpy» + 1)

/-- `mpt_nibble_key` (AST line 10470), log2 ≈ 100. -/
def «mpt_nibble_key» : Nat := Nat.max ((«keccak256» + 1) + («alloc» + 1) + («key_to_nibbles» + 1)) (0) + («alloc» + 1) + («key_to_nibbles» + 1)

/-- `mpt_set` (AST line 10872), log2 ≈ 197. -/
def «mpt_set» : Nat := («mpt_nibble_key» + 1) + Nat.max ((«_mpt_delete_node» + 1)) ((«_mpt_insert_node» + 1))

/-- `build_mpt_indexed` (AST line 11243), log2 ≈ 261. -/
def «build_mpt_indexed» : Nat := («heap_mark» + 1) + («mpt_new» + 1) + (2 ^ 64 + 1) * ((«rlp_encode_word» + 1) + («mpt_set» + 1) + 1) + («mpt_root» + 1) + («heap_release» + 1)

/-- `sha256_block` (AST line 2367), log2 ≈ 0. -/
def «sha256_block» : Nat := 0

/-- `sha256_finish` (AST line 2898), log2 ≈ 66. -/
def «sha256_finish» : Nat := (2 ^ 64 + 1) * ((«st_be32» + 1) + 1)

/-- `sha256_state_init` (AST line 2341), log2 ≈ 0. -/
def «sha256_state_init» : Nat := 0

/-- `sha256` (AST line 2914), log2 ≈ 67. -/
def «sha256» : Nat := («sha256_state_init» + 1) + ((domainBytes + 1) + 1) * ((«sha256_block» + 1) + 1) + («memzero» + 1) + («memcpy» + 1) + («st_be64» + 1) + («sha256_block» + 1) + Nat.max ((«sha256_block» + 1)) (0) + («sha256_finish» + 1)

/-- `compute_requests_hash` (AST line 32190), log2 ≈ 131. -/
def «compute_requests_hash» : Nat := («heap_mark» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«sha256» + 1) + 1) + («sha256» + 1) + («heap_release» + 1)

/-- `cache_get_root` (AST line 32325), log2 ≈ 450. -/
def «cache_get_root» : Nat := («htab_has» + 1) + («ws_storage_root_of» + 1)

/-- `encode_account` (AST line 11343), log2 ≈ 131. -/
def «encode_account» : Nat := («rlp_encode_word» + 1) + («st_be64» + 1) + («st_be64» + 1) + («st_be64» + 1) + («st_be64» + 1) + (32 + 1) * (0 + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_bytes» + 1)

/-- `htab_copy` (AST line 5354), log2 ≈ 67. -/
def «htab_copy» : Nat := («alloc» + 1) + («memcpy» + 1) + («alloc» + 1) + («memcpy» + 1) + («alloc» + 1) + («memcpy» + 1) + («alloc» + 1) + («memcpy» + 1)

/-- `decode_witness_to_mpt` (AST line 10348), log2 ≈ 517. -/
def «decode_witness_to_mpt» : Nat := («memeq» + 1) + («nodedb_lookup» + 1) + Nat.max ((«mpt_fail» + 1)) (0) + («_decode_witness_node» + 1) + Nat.max ((«alloc» + 1) + («memcpy» + 1)) (0)

/-- `mpt_from_witness` (AST line 10459), log2 ≈ 517. -/
def «mpt_from_witness» : Nat := («decode_witness_to_mpt» + 1) + («mpt_new» + 1)

/-- `compute_state_root` (AST line 32341), log2 ≈ 581. -/
def «compute_state_root» : Nat := («htab_copy» + 1) + («htab_new» + 1) + (2 ^ 64 + 1) * ((«htab_item» + 1) + Nat.max ((«htab_has» + 1) + Nat.max ((«htab_set» + 1)) (0) + («ws_storage_root_of» + 1) + («mpt_from_witness» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((2 ^ 64 + 1) * ((«htab_item» + 1) + Nat.max ((«u256_is_zero» + 1) + Nat.max ((«u256_to_be_min» + 1) + («rlp_encode_bytes» + 1) + («alloc» + 1) + («memcpy» + 1) + («mpt_set» + 1)) (0) + Nat.max ((«mpt_set» + 1)) (0)) (0) + 1) + 1) + («alloc» + 1) + («mpt_root» + 1) + («htab_set» + 1)) (0) + 1) + («mpt_from_witness» + 1) + (2 ^ 64 + 1) * ((«htab_item» + 1) + Nat.max ((«htab_has» + 1) + Nat.max ((«ws_get_account_optional» + 1) + («htab_set» + 1) + Nat.max ((«htab_get» + 1) + («alloc» + 1) + («encode_account» + 1) + («mpt_set» + 1)) (0)) (0)) (0) + 1) + (2 ^ 64 + 1) * ((«htab_item» + 1) + Nat.max (Nat.max ((«mpt_set» + 1)) ((«htab_get» + 1) + Nat.max (0) ((«cache_get_root» + 1)) + («alloc» + 1) + («encode_account» + 1) + («mpt_set» + 1))) (0) + 1) + («mpt_root» + 1)

/-- `tx_fixed_bytes` (AST line 11468), log2 ≈ 448. -/
def «tx_fixed_bytes» : Nat := («rlp_item» + 1)

/-- `tx_list_item` (AST line 11510), log2 ≈ 448. -/
def «tx_list_item» : Nat := («rlp_item» + 1)

/-- `decode_access_list` (AST line 11525), log2 ≈ 576. -/
def «decode_access_list» : Nat := («rlp_list_to_slices» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«rlp_item» + 1) + («rlp_list_to_slices» + 1) + («tx_fixed_bytes» + 1) + («tx_list_item» + 1) + («rlp_list_to_slices» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«tx_fixed_bytes» + 1) + («memcpy» + 1) + 1) + 1)

/-- `tx_scalar_item` (AST line 11389), log2 ≈ 448. -/
def «tx_scalar_item» : Nat := («rlp_item» + 1)

/-- `tx_scalar_u256` (AST line 11416), log2 ≈ 448. -/
def «tx_scalar_u256» : Nat := («tx_scalar_item» + 1) + («u256_from_be» + 1)

/-- `tx_scalar_word` (AST line 11431), log2 ≈ 448. -/
def «tx_scalar_word» : Nat := («tx_scalar_item» + 1) + (2 ^ 64 + 1) * (0 + 1)

/-- `decode_authorizations` (AST line 11588), log2 ≈ 514. -/
def «decode_authorizations» : Nat := («rlp_list_to_slices» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«rlp_item» + 1) + («rlp_list_to_slices» + 1) + («tx_scalar_u256» + 1) + («tx_fixed_bytes» + 1) + («tx_scalar_word» + 1) + («tx_scalar_word» + 1) + («tx_scalar_u256» + 1) + («tx_scalar_u256» + 1) + 1)

/-- `decode_blob_hashes` (AST line 11569), log2 ≈ 512. -/
def «decode_blob_hashes» : Nat := («rlp_list_to_slices» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«tx_fixed_bytes» + 1) + («memcpy» + 1) + 1)

/-- `tx_bytes_item` (AST line 11453), log2 ≈ 448. -/
def «tx_bytes_item» : Nat := («rlp_item» + 1)

/-- `tx_to_item` (AST line 11487), log2 ≈ 448. -/
def «tx_to_item» : Nat := («rlp_item» + 1)

/-- `decode_transaction_rlp` (AST line 11634), log2 ≈ 576. -/
def «decode_transaction_rlp» : Nat := («alloc» + 1) + («memzero» + 1) + Nat.max ((«rlp_decode_fully» + 1)) (Nat.max ((«rlp_decode_fully» + 1)) (0)) + («rlp_list_to_slices» + 1) + Nat.max ((«tx_scalar_word» + 1)) (0) + Nat.max ((«tx_scalar_word» + 1)) ((«tx_scalar_u256» + 1)) + Nat.max ((«tx_scalar_u256» + 1)) ((«tx_scalar_u256» + 1) + («tx_scalar_u256» + 1)) + («tx_scalar_word» + 1) + Nat.max ((«tx_fixed_bytes» + 1)) ((«tx_to_item» + 1)) + («tx_scalar_u256» + 1) + («tx_bytes_item» + 1) + Nat.max ((«tx_list_item» + 1) + («decode_access_list» + 1)) (0) + Nat.max ((«tx_scalar_u256» + 1) + («tx_list_item» + 1) + («decode_blob_hashes» + 1)) (0) + Nat.max ((«tx_list_item» + 1) + («decode_authorizations» + 1)) (0) + («tx_scalar_u256» + 1) + («tx_scalar_u256» + 1) + («tx_scalar_u256» + 1)

/-- `decode_transaction` (AST line 11805), log2 ≈ 576. -/
def «decode_transaction» : Nat := («decode_transaction_rlp» + 1)

/-- `logs_bloom` (AST line 31941), log2 ≈ 228. -/
def «logs_bloom» : Nat := («memzero» + 1) + (2 ^ 64 + 1) * ((«add_to_bloom» + 1) + (2 ^ 64 + 1) * ((«add_to_bloom» + 1) + 1) + 1)

/-- `max` (AST line 681), log2 ≈ 0. -/
def «max» : Nat := 0

/-- `is_zero_bytes` (AST line 477), log2 ≈ 65. -/
def «is_zero_bytes» : Nat := (2 ^ 64 + 1) * (0 + 1)

/-- `ld_be64` (AST line 539), log2 ≈ 1. -/
def «ld_be64» : Nat := Nat.max ((«bswap64» + 1)) (0)

/-- `extract_deposit_data` (AST line 32212), log2 ≈ 69. -/
def «extract_deposit_data» : Nat := («heap_mark» + 1) + («is_zero_bytes» + 1) + («ld_be64» + 1) + («is_zero_bytes» + 1) + («is_zero_bytes» + 1) + («ld_be64» + 1) + («is_zero_bytes» + 1) + («ld_be64» + 1) + («is_zero_bytes» + 1) + («ld_be64» + 1) + («is_zero_bytes» + 1) + («ld_be64» + 1) + («is_zero_bytes» + 1) + («ld_be64» + 1) + («is_zero_bytes» + 1) + («ld_be64» + 1) + («is_zero_bytes» + 1) + («ld_be64» + 1) + («is_zero_bytes» + 1) + («ld_be64» + 1) + («is_zero_bytes» + 1) + («ld_be64» + 1) + («heap_release» + 1) + («memcpy» + 1) + («memcpy» + 1) + («memcpy» + 1) + («memcpy» + 1) + («memcpy» + 1)

/-- `sk_make` (AST line 12923), log2 ≈ 66. -/
def «sk_make» : Nat := («memcpy» + 1) + («memcpy» + 1)

/-- `ws_get_code` (AST line 13099), log2 ≈ 68. -/
def «ws_get_code» : Nat := («memeq» + 1) + («nodedb_lookup» + 1)

/-- `get_code` (AST line 13203), log2 ≈ 130. -/
def «get_code» : Nat := («memeq» + 1) + («htab_get» + 1) + («htab_get» + 1) + («sk_make» + 1) + («htab_set» + 1) + («ws_get_code» + 1)

/-- `ext_code_of` (AST line 16953), log2 ≈ 450. -/
def «ext_code_of» : Nat := («get_account» + 1) + («get_code» + 1)

/-- `frame_mem_release` (AST line 142), log2 ≈ 0. -/
def «frame_mem_release» : Nat := 0

/-- `htab_union_into` (AST line 13711), log2 ≈ 194. -/
def «htab_union_into» : Nat := (2 ^ 64 + 1) * ((«htab_item» + 1) + Nat.max ((«htab_set» + 1)) (0) + 1)

/-- `merge_tx_into_block` (AST line 13731), log2 ≈ 258. -/
def «merge_tx_into_block» : Nat := («htab_union_into» + 1) + («htab_union_into» + 1) + («htab_union_into» + 1) + («htab_union_into» + 1) + («htab_union_into» + 1) + (2 ^ 64 + 1) * ((«htab_item» + 1) + Nat.max ((«htab_get» + 1) + Nat.max ((«htab_new» + 1) + («htab_set» + 1)) (0) + («htab_union_into» + 1)) (0) + 1)

/-- `bal_list_remove_idx` (AST line 14163), log2 ≈ 129. -/
def «bal_list_remove_idx» : Nat := (2 ^ 64 + 1) * (Nat.max (Nat.max ((«memcpy» + 1)) (0)) (0) + 1)

/-- `bal_remove_change` (AST line 14189), log2 ≈ 129. -/
def «bal_remove_change» : Nat := («htab_get» + 1) + («bal_list_remove_idx» + 1)

/-- `get_pre_tx_account` (AST line 14051), log2 ≈ 450. -/
def «get_pre_tx_account» : Nat := («htab_get» + 1) + («record_pre_state_read» + 1) + («ws_get_account_optional» + 1)

/-- `st_le32` (AST line 553), log2 ≈ 0. -/
def «st_le32» : Nat := 0

/-- `st_le64` (AST line 571), log2 ≈ 2. -/
def «st_le64» : Nat := («st_le32» + 1) + («st_le32» + 1)

/-- `idx_start_account` (AST line 14087), log2 ≈ 450. -/
def «idx_start_account» : Nat := («st_le64» + 1) + («memcpy» + 1) + («htab_get» + 1) + («get_pre_tx_account» + 1) + («alloc» + 1) + («memzero» + 1) + («memcpy» + 1) + Nat.max ((«memcpy» + 1)) (0) + («st_le64» + 1) + («memcpy» + 1) + («htab_set» + 1)

/-- `stor_lookup` (AST line 13233), log2 ≈ 68. -/
def «stor_lookup» : Nat := («htab_get» + 1) + («htab_get» + 1)

/-- `ws_storage_trie` (AST line 13042), log2 ≈ 517. -/
def «ws_storage_trie» : Nat := («htab_get» + 1) + («decode_witness_to_mpt» + 1) + («htab_set» + 1)

/-- `ws_get_storage` (AST line 13061), log2 ≈ 517. -/
def «ws_get_storage» : Nat := («ws_storage_root_of» + 1) + («memeq» + 1) + («ws_storage_trie» + 1) + («heap_mark» + 1) + («alloc» + 1) + («keccak256» + 1) + («trie_lookup» + 1) + («heap_release» + 1) + («rlp_decode_fully» + 1) + («u256_from_be» + 1)

/-- `get_pre_tx_storage` (AST line 14069), log2 ≈ 517. -/
def «get_pre_tx_storage» : Nat := («stor_lookup» + 1) + («record_pre_state_read» + 1) + («ws_get_storage» + 1)

/-- `idx_start_storage` (AST line 14129), log2 ≈ 517. -/
def «idx_start_storage» : Nat := («st_le64» + 1) + («memcpy» + 1) + («memcpy» + 1) + («htab_get» + 1) + («get_pre_tx_storage» + 1) + («alloc» + 1) + («st_le64» + 1) + («memcpy» + 1) + («memcpy» + 1) + («htab_set» + 1)

/-- `htab_del` (AST line 5217), log2 ≈ 67. -/
def «htab_del» : Nat := («htab_find_leaf» + 1) + («memeq» + 1)

/-- `remove_storage_write` (AST line 14206), log2 ≈ 129. -/
def «remove_storage_write» : Nat := («htab_get» + 1) + («htab_get» + 1) + («bal_list_remove_idx» + 1) + Nat.max ((«htab_del» + 1)) (0)

/-- `u256_eq` (AST line 869), log2 ≈ 0. -/
def «u256_eq» : Nat := 0

/-- `update_builder_from_tx` (AST line 14233), log2 ≈ 645. -/
def «update_builder_from_tx» : Nat := (2 ^ 64 + 1) * ((«htab_item» + 1) + Nat.max ((«idx_start_account» + 1) + («u256_eq» + 1) + Nat.max ((«add_balance_change» + 1)) ((«bal_remove_change» + 1)) + Nat.max ((«add_nonce_change» + 1)) ((«bal_remove_change» + 1)) + («memeq» + 1) + Nat.max ((«get_code» + 1) + («add_code_change» + 1)) ((«bal_remove_change» + 1))) (0) + 1) + (2 ^ 64 + 1) * ((«htab_item» + 1) + Nat.max ((2 ^ 64 + 1) * ((«htab_item» + 1) + Nat.max ((«idx_start_storage» + 1) + («u256_eq» + 1) + Nat.max ((«add_storage_write» + 1)) ((«remove_storage_write» + 1))) (0) + 1)) (0) + 1)

/-- `incorporate_tx_into_block` (AST line 14313), log2 ≈ 645. -/
def «incorporate_tx_into_block» : Nat := («update_builder_from_tx» + 1) + («merge_tx_into_block» + 1)

/-- `msg_new` (AST line 15344), log2 ≈ 65. -/
def «msg_new» : Nat := («alloc» + 1) + («memzero» + 1)

/-- `frame_state_gas_used` (AST line 15018), log2 ≈ 0. -/
def «frame_state_gas_used» : Nat := 0

/-- `charge_gas` (AST line 14949), log2 ≈ 0. -/
def «charge_gas» : Nat := 0

/-- `charge_state_gas` (AST line 14968), log2 ≈ 1. -/
def «charge_state_gas» : Nat := («add_sat» + 1)

/-- `jset` (AST line 12825), log2 ≈ 130. -/
def «jset» : Nat := («htab_get» + 1) + Nat.max ((«trap_with» + 1)) (0) + («alloc» + 1) + («memcpy» + 1) + («htab_set» + 1)

/-- `jdel` (AST line 12857), log2 ≈ 68. -/
def «jdel» : Nat := («htab_get» + 1) + Nat.max ((«trap_with» + 1)) (0) + («alloc» + 1) + («memcpy» + 1) + («htab_del» + 1)

/-- `destroy_storage` (AST line 13480), log2 ≈ 194. -/
def «destroy_storage» : Nat := («htab_get» + 1) + (2 ^ 64 + 1) * ((«htab_item» + 1) + Nat.max ((«sk_make» + 1) + («htab_set» + 1)) (0) + 1) + («jdel» + 1)

/-- `set_account` (AST line 13439), log2 ≈ 130. -/
def «set_account» : Nat := («jset» + 1)

/-- `destroy_account` (AST line 13510), log2 ≈ 194. -/
def «destroy_account» : Nat := («destroy_storage» + 1) + («set_account» + 1)

/-- `modify_state_commit` (AST line 13524), log2 ≈ 194. -/
def «modify_state_commit» : Nat := («set_account» + 1) + («acct_is_empty» + 1) + Nat.max ((«destroy_account» + 1)) (0)

/-- `set_code` (AST line 13681), log2 ≈ 450. -/
def «set_code» : Nat := («alloc» + 1) + («keccak256» + 1) + («memeq» + 1) + Nat.max ((«alloc» + 1) + («jset» + 1)) (0) + («get_account» + 1) + («acct_copy» + 1) + («modify_state_commit» + 1)

/-- `ceil32` (AST line 14862), log2 ≈ 1. -/
def «ceil32» : Nat := («add_sat» + 1)

/-- `words_of` (AST line 14878), log2 ≈ 2. -/
def «words_of» : Nat := («ceil32» + 1)

/-- `create_finish` (AST line 18867), log2 ≈ 450. -/
def «create_finish» : Nat := («words_of» + 1) + («charge_gas» + 1) + («charge_state_gas» + 1) + («alloc» + 1) + («memcpy» + 1) + («set_code» + 1)

/-- `frame_halt` (AST line 18756), log2 ≈ 0. -/
def «frame_halt» : Nat := 0

/-- `increment_nonce` (AST line 13664), log2 ≈ 450. -/
def «increment_nonce» : Nat := («get_account» + 1) + («acct_copy» + 1) + («modify_state_commit» + 1)

/-- `mark_account_created` (AST line 13562), log2 ≈ 130. -/
def «mark_account_created» : Nat := («htab_set» + 1)

/-- `compute_jumpdests` (AST line 15279), log2 ≈ 65. -/
def «compute_jumpdests» : Nat := («scratch_alloc» + 1) + («memzero» + 1) + (31104957928 + 1) * (0 + 1)

/-- `is_valid_delegation` (AST line 14917), log2 ≈ 0. -/
def «is_valid_delegation» : Nat := 0

/-- `get_delegated_code_address` (AST line 17610), log2 ≈ 1. -/
def «get_delegated_code_address» : Nat := («is_valid_delegation» + 1)

/-- `get_pre_state_account` (AST line 13155), log2 ≈ 450. -/
def «get_pre_state_account» : Nat := («get_pre_state_account_optional» + 1) + Nat.max ((«acct_empty» + 1)) (0)

/-- `is_account_alive` (AST line 13419), log2 ≈ 450. -/
def «is_account_alive» : Nat := («get_account_optional» + 1) + («acct_is_empty» + 1)

/-- `warm_address` (AST line 15484), log2 ≈ 130. -/
def «warm_address» : Nat := («htab_set» + 1)

/-- `prepare_dispatch` (AST line 17836), log2 ≈ 452. -/
def «prepare_dispatch» : Nat := Nat.max ((«get_pre_state_account» + 1) + («acct_is_empty» + 1) + Nat.max ((«charge_state_gas» + 1)) (0)) (0) + («u256_is_zero» + 1) + Nat.max ((«is_account_alive» + 1) + Nat.max ((«charge_state_gas» + 1)) (0)) (0) + («ext_code_of» + 1) + («get_delegated_code_address» + 1) + Nat.max ((«alloc» + 1) + («memcpy» + 1) + («is_warm_address» + 1) + Nat.max ((«charge_gas» + 1)) ((«charge_gas» + 1) + («warm_address» + 1)) + («ext_code_of» + 1)) (0) + («compute_jumpdests» + 1)

/-- `ec_set_infinity` (AST line 6984), log2 ≈ 0. -/
def «ec_set_infinity» : Nat := 0

/-- `u256_add_carry` (AST line 1039), log2 ≈ 0. -/
def «u256_add_carry» : Nat := 0

/-- `u256_lt` (AST line 883), log2 ≈ 0. -/
def «u256_lt» : Nat := 0

/-- `u256_sub` (AST line 1083), log2 ≈ 0. -/
def «u256_sub» : Nat := 0

/-- `fp_add` (AST line 5427), log2 ≈ 3. -/
def «fp_add» : Nat := («u256_add_carry» + 1) + Nat.max ((«u256_sub» + 1)) (0) + («u256_lt» + 1) + Nat.max ((«u256_sub» + 1)) (0)

/-- `fp_reduce` (AST line 5479), log2 ≈ 2. -/
def «fp_reduce» : Nat := («u256_lt» + 1) + Nat.max ((«u256_sub» + 1)) (0)

/-- `u256_add` (AST line 1061), log2 ≈ 0. -/
def «u256_add» : Nat := 0

/-- `fp_mul` (AST line 5494), log2 ≈ 3. -/
def «fp_mul» : Nat := Nat.max ((«u256_add» + 1)) (0) + («fp_reduce» + 1)

/-- `fp_sqr` (AST line 6163), log2 ≈ 3. -/
def «fp_sqr» : Nat := Nat.max ((«u256_add» + 1)) (0) + («fp_reduce» + 1)

/-- `fp_sub` (AST line 5448), log2 ≈ 2. -/
def «fp_sub» : Nat := («u256_lt» + 1) + («u256_sub» + 1) + Nat.max ((«u256_add» + 1)) (0)

/-- `ec_double` (AST line 7027), log2 ≈ 7. -/
def «ec_double» : Nat := («u256_is_zero» + 1) + («u256_is_zero» + 1) + Nat.max ((«ec_set_infinity» + 1)) (0) + («fp_sqr» + 1) + («fp_mul» + 1) + («fp_add» + 1) + («fp_add» + 1) + («fp_sqr» + 1) + («fp_add» + 1) + («fp_add» + 1) + («fp_sqr» + 1) + («fp_add» + 1) + («fp_sub» + 1) + («fp_sub» + 1) + («fp_mul» + 1) + («fp_sqr» + 1) + («fp_add» + 1) + («fp_add» + 1) + («fp_add» + 1) + («fp_sub» + 1) + («fp_mul» + 1) + («fp_add» + 1)

/-- `ec_set_affine` (AST line 7000), log2 ≈ 0. -/
def «ec_set_affine» : Nat := 0

/-- `ec_add_affine` (AST line 7086), log2 ≈ 8. -/
def «ec_add_affine» : Nat := («u256_is_zero» + 1) + Nat.max ((«ec_set_affine» + 1)) (0) + («fp_sqr» + 1) + («fp_mul» + 1) + («fp_mul» + 1) + («fp_mul» + 1) + («u256_eq» + 1) + Nat.max ((«fp_add» + 1) + («u256_is_zero» + 1) + Nat.max ((«ec_set_infinity» + 1)) (0) + («ec_double» + 1)) (0) + («fp_sub» + 1) + («fp_sub» + 1) + («fp_sqr» + 1) + («fp_mul» + 1) + («fp_mul» + 1) + («fp_sqr» + 1) + («fp_sub» + 1) + («fp_add» + 1) + («fp_sub» + 1) + («fp_sub» + 1) + («fp_mul» + 1) + («fp_mul» + 1) + («fp_sub» + 1) + («fp_mul» + 1)

/-- `ec_is_infinity` (AST line 7016), log2 ≈ 1. -/
def «ec_is_infinity» : Nat := («u256_is_zero» + 1)

/-- `mod_half` (AST line 6866), log2 ≈ 1. -/
def «mod_half» : Nat := («u256_add_carry» + 1)

/-- `mod_sub` (AST line 6881), log2 ≈ 2. -/
def «mod_sub» : Nat := («u256_lt» + 1) + («u256_sub» + 1) + Nat.max ((«u256_add» + 1)) (0)

/-- `modinv_bin` (AST line 6815), log2 ≈ 387. -/
def «modinv_bin» : Nat := («u256_is_zero» + 1) + (2 ^ 256 + 1) * ((2 ^ 128 + 1) * ((«mod_half» + 1) + 1) + (2 ^ 128 + 1) * ((«mod_half» + 1) + 1) + («u256_lt» + 1) + («u256_sub» + 1) + («mod_sub» + 1) + 1)

/-- `fp_inv` (AST line 6897), log2 ≈ 387. -/
def «fp_inv» : Nat := («modinv_bin» + 1)

/-- `ec_to_affine` (AST line 7308), log2 ≈ 387. -/
def «ec_to_affine» : Nat := («u256_is_zero» + 1) + («fp_inv» + 1) + («fp_sqr» + 1) + («fp_mul» + 1) + («fp_mul» + 1) + («fp_mul» + 1) + («ec_set_affine» + 1)

/-- `u256_bit` (AST line 854), log2 ≈ 1. -/
def «u256_bit» : Nat := («u256_limb» + 1)

/-- `ec_mul2` (AST line 7257), log2 ≈ 387. -/
def «ec_mul2» : Nat := («ec_set_infinity» + 1) + («u256_bit_length» + 1) + («u256_bit_length» + 1) + («max» + 1) + («heap_mark» + 1) + («alloc» + 1) + («ec_set_affine» + 1) + («ec_add_affine» + 1) + («ec_is_infinity» + 1) + Nat.max ((«ec_to_affine» + 1)) (0) + (2 ^ 64 + 1) * ((«ec_double» + 1) + («u256_bit» + 1) + («u256_bit» + 1) + Nat.max (Nat.max (Nat.max ((«ec_add_affine» + 1)) (0)) ((«ec_add_affine» + 1))) (Nat.max ((«ec_add_affine» + 1)) (0)) + 1) + («heap_release» + 1)

/-- `fn_inv` (AST line 6974), log2 ≈ 387. -/
def «fn_inv» : Nat := («modinv_bin» + 1)

/-- `digits_len` (AST line 1566), log2 ≈ 65. -/
def «digits_len» : Nat := (2 ^ 64 + 1) * (0 + 1)

/-- `digits_to_u256` (AST line 1556), log2 ≈ 0. -/
def «digits_to_u256» : Nat := 0

/-- `div64by32` (AST line 1506), log2 ≈ 65. -/
def «div64by32» : Nat := (2 ^ 64 + 1) * (0 + 1)

/-- `nlz32` (AST line 1467), log2 ≈ 0. -/
def «nlz32» : Nat := 0

/-- `divmnu` (AST line 1583), log2 ≈ 257. -/
def «divmnu» : Nat := Nat.max ((2 ^ 64 + 1) * ((«div64by32» + 1) + 1)) (0) + («nlz32» + 1) + (2 ^ 64 + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1) + (2 ^ 64 + 1) * (Nat.max (0) ((«div64by32» + 1)) + (2 ^ 192 + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1) + Nat.max ((2 ^ 64 + 1) * (0 + 1)) (0) + 1) + (2 ^ 64 + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1)

/-- `u256_to_digits` (AST line 1530), log2 ≈ 0. -/
def «u256_to_digits» : Nat := 0

/-- `digits_divmod` (AST line 1718), log2 ≈ 257. -/
def «digits_divmod» : Nat := («u256_to_digits» + 1) + («digits_len» + 1) + («digits_len» + 1) + (16 + 1) * (0 + 1) + Nat.max ((«digits_to_u256» + 1)) (0) + (8 + 1) * (0 + 1) + («divmnu» + 1) + («digits_to_u256» + 1)

/-- `mul64x64` (AST line 1127), log2 ≈ 0. -/
def «mul64x64» : Nat := 0

/-- `u256_divmod` (AST line 1754), log2 ≈ 257. -/
def «u256_divmod» : Nat := («u256_lt» + 1) + Nat.max ((«udivmod» + 1)) (0) + («u256_to_digits» + 1) + («digits_divmod» + 1) + («digits_to_u256» + 1)

/-- `u256_mod` (AST line 1794), log2 ≈ 257. -/
def «u256_mod» : Nat := («u256_divmod» + 1)

/-- `u256_mul_full` (AST line 1230), log2 ≈ 5. -/
def «u256_mul_full» : Nat := («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1)

/-- `u256_mulmod` (AST line 1888), log2 ≈ 258. -/
def «u256_mulmod» : Nat := Nat.max ((«mul64x64» + 1) + Nat.max ((«u256_mod» + 1)) (0) + («u256_to_digits» + 1) + («digits_divmod» + 1)) (0) + («u256_mul_full» + 1) + («u256_to_digits» + 1) + («u256_to_digits» + 1) + («digits_divmod» + 1)

/-- `fn_mul` (AST line 6917), log2 ≈ 258. -/
def «fn_mul» : Nat := («u256_mulmod» + 1)

/-- `fp_neg` (AST line 5464), log2 ≈ 2. -/
def «fp_neg» : Nat := («u256_is_zero» + 1) + («u256_sub» + 1)

/-- `fp_pow` (AST line 6778), log2 ≈ 68. -/
def «fp_pow» : Nat := (2 ^ 64 + 1) * (Nat.max ((«fp_sqr» + 1)) (0) + («u256_bit» + 1) + Nat.max ((«fp_mul» + 1)) (0) + 1)

/-- `fp_sqrt` (AST line 6907), log2 ≈ 68. -/
def «fp_sqrt» : Nat := («fp_pow» + 1)

/-- `secp256k1_decompress_r` (AST line 7351), log2 ≈ 68. -/
def «secp256k1_decompress_r» : Nat := Nat.max ((«u256_add_carry» + 1)) (0) + («u256_lt» + 1) + («fp_sqr» + 1) + («fp_mul» + 1) + («fp_add» + 1) + («fp_sqrt» + 1) + («fp_sqr» + 1) + («u256_eq» + 1) + Nat.max ((«fp_neg» + 1)) (0) + («ec_set_affine» + 1)

/-- `u256_to_be32` (AST line 2265), log2 ≈ 5. -/
def «u256_to_be32» : Nat := Nat.max ((«bswap64» + 1) + («bswap64» + 1) + («bswap64» + 1) + («bswap64» + 1)) (0) + («st_be64» + 1) + («st_be64» + 1) + («st_be64» + 1) + («st_be64» + 1)

/-- `secp256k1_recover` (AST line 7395), log2 ≈ 389. -/
def «secp256k1_recover» : Nat := («u256_is_zero» + 1) + («u256_lt» + 1) + («u256_is_zero» + 1) + («u256_lt» + 1) + («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («secp256k1_decompress_r» + 1) + Nat.max ((«heap_release» + 1)) (0) + («u256_from_be» + 1) + («u256_lt» + 1) + Nat.max ((«u256_sub» + 1)) (0) + («fn_inv» + 1) + («u256_is_zero» + 1) + Nat.max ((«u256_sub» + 1)) (0) + («fn_mul» + 1) + («fn_mul» + 1) + («ec_mul2» + 1) + («ec_to_affine» + 1) + Nat.max ((«u256_to_be32» + 1) + («u256_to_be32» + 1)) (0) + («heap_release» + 1)

/-- `u256_gt` (AST line 921), log2 ≈ 1. -/
def «u256_gt» : Nat := («u256_lt» + 1)

/-- `recover_authority` (AST line 17625), log2 ≈ 389. -/
def «recover_authority» : Nat := («u256_is_zero» + 1) + («u256_lt» + 1) + («u256_is_zero» + 1) + («u256_gt» + 1) + («heap_mark» + 1) + («alloc» + 1) + («rlp_put_u256» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_word» + 1) + («rlp_list_header_len» + 1) + («rlp_encode_list_header» + 1) + («alloc» + 1) + («keccak256» + 1) + («alloc» + 1) + («secp256k1_recover» + 1) + Nat.max ((«heap_release» + 1)) (0) + («keccak256» + 1) + («heap_release» + 1) + («alloc» + 1) + («memcpy» + 1)

/-- `u256_fits_word` (AST line 800), log2 ≈ 0. -/
def «u256_fits_word» : Nat := 0

/-- `validate_authorization_checks` (AST line 17717), log2 ≈ 450. -/
def «validate_authorization_checks» : Nat := («get_account» + 1) + («get_code» + 1) + Nat.max ((«is_valid_delegation» + 1)) (0)

/-- `set_delegation` (AST line 17740), log2 ≈ 516. -/
def «set_delegation» : Nat := («htab_new» + 1) + («htab_set» + 1) + («u256_is_zero» + 1) + Nat.max ((«htab_set» + 1)) (0) + («htab_new» + 1) + (2 ^ 64 + 1) * ((«u256_is_zero» + 1) + («u256_fits_word» + 1) + Nat.max (Nat.max ((«recover_authority» + 1) + Nat.max ((«warm_address» + 1) + («validate_authorization_checks» + 1)) (0)) (0)) (0) + Nat.max ((«account_exists» + 1) + Nat.max ((«charge_state_gas» + 1)) (0) + («htab_has» + 1) + Nat.max ((«charge_gas» + 1) + («htab_set» + 1)) (0) + («get_pre_state_account» + 1) + («get_code» + 1) + («is_valid_delegation» + 1) + («memeq» + 1) + Nat.max ((«set_code» + 1)) ((«htab_has» + 1) + Nat.max ((«charge_state_gas» + 1)) (0) + («htab_set» + 1) + («alloc» + 1) + («memcpy» + 1) + («set_code» + 1)) + («increment_nonce» + 1)) (0) + 1)

/-- `depth0_prepare` (AST line 18772), log2 ≈ 516. -/
def «depth0_prepare» : Nat := Nat.max ((«set_delegation» + 1) + («frame_state_gas_used» + 1)) (0) + («prepare_dispatch» + 1)

/-- `frame_mem_alloc` (AST line 110), log2 ≈ 2. -/
def «frame_mem_alloc» : Nat := Nat.max ((«trap_with» + 1)) (0) + Nat.max ((«trap_with» + 1)) (0)

/-- `frame_mem_mark` (AST line 132), log2 ≈ 0. -/
def «frame_mem_mark» : Nat := 0

/-- `htab_count` (AST line 5294), log2 ≈ 0. -/
def «htab_count» : Nat := 0

/-- `htab_new_scratch` (AST line 4909), log2 ≈ 4. -/
def «htab_new_scratch» : Nat := («scratch_alloc» + 1) + («scratch_alloc» + 1) + («scratch_alloc» + 1) + («scratch_alloc» + 1)

/-- `lst_new_scratch` (AST line 13822), log2 ≈ 3. -/
def «lst_new_scratch» : Nat := («scratch_alloc» + 1) + («scratch_alloc» + 1)

/-- `frame_new` (AST line 15370), log2 ≈ 66. -/
def «frame_new» : Nat := («scratch_mark» + 1) + («frame_mem_mark» + 1) + («scratch_alloc» + 1) + («memzero» + 1) + («scratch_alloc» + 1) + («frame_mem_alloc» + 1) + («compute_jumpdests» + 1) + («lst_new_scratch» + 1) + («htab_new_scratch» + 1) + («htab_count» + 1) + («htab_count» + 1)

/-- `frame_open` (AST line 18450), log2 ≈ 66. -/
def «frame_open» : Nat := («frame_new» + 1) + («scratch_alloc» + 1) + («memzero» + 1)

/-- `refill_frame_state_gas` (AST line 15029), log2 ≈ 0. -/
def «refill_frame_state_gas» : Nat := 0

/-- `frame_exception` (AST line 18477), log2 ≈ 2. -/
def «frame_exception» : Nat := («refill_frame_state_gas» + 1) + Nat.max ((«frame_halt» + 1)) (0)

/-- `log_append` (AST line 16486), log2 ≈ 65. -/
def «log_append» : Nat := («lst_push» + 1)

/-- `emit_transfer_log` (AST line 17459), log2 ≈ 67. -/
def «emit_transfer_log» : Nat := («u256_is_zero» + 1) + («alloc» + 1) + («alloc» + 1) + («memcpy» + 1) + («memzero» + 1) + («memcpy» + 1) + («memzero» + 1) + («memcpy» + 1) + («alloc» + 1) + («u256_to_be32» + 1) + («log_append» + 1)

/-- `move_ether` (AST line 13597), log2 ≈ 451. -/
def «move_ether» : Nat := («get_account» + 1) + («u256_lt» + 1) + («acct_copy» + 1) + («u256_sub» + 1) + («modify_state_commit» + 1) + («get_account» + 1) + («acct_copy» + 1) + («u256_add» + 1) + («modify_state_commit» + 1)

/-- `precompile_index` (AST line 31482), log2 ≈ 65. -/
def «precompile_index» : Nat := («is_zero_bytes» + 1)

/-- `fq_mul` (AST line 22338), log2 ≈ 2. -/
def «fq_mul» : Nat := («u256_lt» + 1) + Nat.max ((«u256_sub» + 1)) (0)

/-- `fq_from_mont` (AST line 23320), log2 ≈ 2. -/
def «fq_from_mont» : Nat := («fq_mul» + 1)

/-- `fq_inv` (AST line 23330), log2 ≈ 387. -/
def «fq_inv» : Nat := («modinv_bin» + 1) + («fq_mul» + 1)

/-- `bn254_g1_to_bytes` (AST line 24508), log2 ≈ 387. -/
def «bn254_g1_to_bytes» : Nat := («u256_is_zero» + 1) + Nat.max ((«memzero» + 1)) (0) + («fq_inv» + 1) + («fq_mul» + 1) + («fq_mul» + 1) + («fq_from_mont» + 1) + («fq_from_mont» + 1) + («u256_to_be32» + 1) + («u256_to_be32» + 1)

/-- `fe_set_one` (AST line 23653), log2 ≈ 65. -/
def «fe_set_one» : Nat := («memzero» + 1)

/-- `fe_set_zero` (AST line 23641), log2 ≈ 65. -/
def «fe_set_zero» : Nat := («memzero» + 1)

/-- `ecp_set_inf` (AST line 23667), log2 ≈ 66. -/
def «ecp_set_inf» : Nat := («fe_set_one» + 1) + («fe_set_one» + 1) + («fe_set_zero» + 1)

/-- `fq_add` (AST line 22291), log2 ≈ 2. -/
def «fq_add» : Nat := («u256_add» + 1) + («u256_lt» + 1) + Nat.max ((«u256_sub» + 1)) (0)

/-- `fq_to_mont` (AST line 23310), log2 ≈ 2. -/
def «fq_to_mont» : Nat := («fq_mul» + 1)

/-- `bn254_parse_g1` (AST line 24385), log2 ≈ 67. -/
def «bn254_parse_g1» : Nat := («u256_from_be» + 1) + («u256_from_be» + 1) + («u256_lt» + 1) + («u256_lt» + 1) + («u256_is_zero» + 1) + («u256_is_zero» + 1) + Nat.max ((«ecp_set_inf» + 1)) (0) + («fq_to_mont» + 1) + («fq_to_mont» + 1) + («fq_mul» + 1) + («fq_mul» + 1) + («fq_mul» + 1) + («fq_add» + 1) + («u256_eq» + 1)

/-- `fq_mul_small` (AST line 23341), log2 ≈ 68. -/
def «fq_mul_small» : Nat := («bit_length64» + 1) + (2 ^ 64 + 1) * ((«fq_add» + 1) + Nat.max ((«fq_add» + 1)) (0) + 1)

/-- `fq_sub` (AST line 22307), log2 ≈ 2. -/
def «fq_sub» : Nat := («u256_lt» + 1) + («u256_sub» + 1) + Nat.max ((«u256_add» + 1)) (0)

/-- `fq12_reduce` (AST line 23386), log2 ≈ 133. -/
def «fq12_reduce» : Nat := (2 ^ 64 + 1) * ((«fq_mul_small» + 1) + («fq_mul_small» + 1) + («fq_sub» + 1) + («fq_add» + 1) + 1)

/-- `fq12_mul` (AST line 23413), log2 ≈ 136. -/
def «fq12_mul» : Nat := («heap_mark» + 1) + («alloc» + 1) + (23 + 1) * ((2 ^ 128 + 1) * ((«fq_mul» + 1) + («fq_add» + 1) + 1) + 1) + («fq12_reduce» + 1) + («memcpy» + 1) + («heap_release» + 1)

/-- `fq2_mul` (AST line 23362), log2 ≈ 5. -/
def «fq2_mul» : Nat := («fq_mul» + 1) + («fq_mul» + 1) + («fq_mul» + 1) + («fq_mul» + 1) + («fq_sub» + 1) + («fq_add» + 1)

/-- `fe_mul` (AST line 23502), log2 ≈ 136. -/
def «fe_mul» : Nat := Nat.max ((«fq_mul» + 1)) (0) + Nat.max ((«fq2_mul» + 1)) (0) + («fq12_mul» + 1)

/-- `fe_mul_small` (AST line 23603), log2 ≈ 132. -/
def «fe_mul_small» : Nat := (2 ^ 64 + 1) * ((«fq_mul_small» + 1) + 1)

/-- `fq12_sqr` (AST line 23456), log2 ≈ 136. -/
def «fq12_sqr» : Nat := («heap_mark» + 1) + («alloc» + 1) + (23 + 1) * ((2 ^ 128 + 1) * ((«fq_mul» + 1) + («fq_add» + 1) + 1) + («fq_add» + 1) + Nat.max ((«fq_mul» + 1) + («fq_add» + 1)) (0) + 1) + («fq12_reduce» + 1) + («memcpy» + 1) + («heap_release» + 1)

/-- `fe_sqr` (AST line 23529), log2 ≈ 137. -/
def «fe_sqr» : Nat := Nat.max ((«fq12_sqr» + 1)) (0) + («fe_mul» + 1)

/-- `fe_sub` (AST line 23566), log2 ≈ 67. -/
def «fe_sub» : Nat := (2 ^ 64 + 1) * ((«fq_sub» + 1) + 1)

/-- `ecp_double` (AST line 23694), log2 ≈ 140. -/
def «ecp_double» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («fe_sqr» + 1) + («fe_mul_small» + 1) + («fe_mul» + 1) + («fe_mul» + 1) + («fe_mul» + 1) + («fe_sqr» + 1) + («fe_mul_small» + 1) + («fe_sub» + 1) + («fe_sqr» + 1) + («fe_mul» + 1) + («fe_mul_small» + 1) + («fe_mul_small» + 1) + («fe_sub» + 1) + («fe_mul» + 1) + («fe_sqr» + 1) + («fe_mul» + 1) + («fe_mul_small» + 1) + («fe_sub» + 1) + («fe_mul» + 1) + («fe_mul_small» + 1) + («memcpy» + 1) + («memcpy» + 1) + («memcpy» + 1) + («heap_release» + 1)

/-- `fe_eq` (AST line 23631), log2 ≈ 67. -/
def «fe_eq» : Nat := («memeq» + 1)

/-- `fe_is_zero` (AST line 23621), log2 ≈ 65. -/
def «fe_is_zero» : Nat := («is_zero_bytes» + 1)

/-- `ecp_add` (AST line 23764), log2 ≈ 141. -/
def «ecp_add» : Nat := («fe_is_zero» + 1) + Nat.max ((«memcpy» + 1)) (0) + («fe_is_zero» + 1) + Nat.max ((«memcpy» + 1)) (0) + («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («fe_mul» + 1) + («fe_mul» + 1) + («fe_mul» + 1) + («fe_mul» + 1) + («fe_eq» + 1) + Nat.max ((«fe_eq» + 1) + («heap_release» + 1) + Nat.max ((«ecp_double» + 1)) (0) + («ecp_set_inf» + 1)) (0) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («fe_sub» + 1) + («fe_sub» + 1) + («fe_sqr» + 1) + («fe_mul» + 1) + («fe_mul» + 1) + («fe_mul» + 1) + («fe_sqr» + 1) + («fe_mul» + 1) + («fe_sub» + 1) + («fe_mul_small» + 1) + («fe_sub» + 1) + («fe_mul» + 1) + («fe_sub» + 1) + («fe_mul» + 1) + («fe_mul» + 1) + («fe_sub» + 1) + («fe_mul» + 1) + («memcpy» + 1) + («memcpy» + 1) + («memcpy» + 1) + («heap_release» + 1)

/-- `bn254_g1_add` (AST line 24541), log2 ≈ 387. -/
def «bn254_g1_add» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («bn254_parse_g1» + 1) + Nat.max ((«heap_release» + 1)) (0) + («bn254_parse_g1» + 1) + Nat.max ((«heap_release» + 1)) (0) + («ecp_add» + 1) + («bn254_g1_to_bytes» + 1) + («heap_release» + 1)

/-- `buffer_read` (AST line 15256), log2 ≈ 66. -/
def «buffer_read» : Nat := Nat.max ((«memcpy» + 1)) (0) + («memzero» + 1)

/-- `pre_alt_bn128_add` (AST line 24699), log2 ≈ 387. -/
def «pre_alt_bn128_add» : Nat := («charge_gas» + 1) + («alloc» + 1) + («heap_mark» + 1) + («alloc» + 1) + («buffer_read» + 1) + («bn254_g1_add» + 1) + («heap_release» + 1)

/-- `ecp_mul` (AST line 23874), log2 ≈ 206. -/
def «ecp_mul» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («ecp_set_inf» + 1) + («memcpy» + 1) + («u256_bit_length» + 1) + (2 ^ 64 + 1) * ((«u256_bit» + 1) + Nat.max ((«ecp_add» + 1)) (0) + Nat.max ((«ecp_double» + 1)) (0) + 1) + («memcpy» + 1) + («heap_release» + 1)

/-- `bn254_g1_mul` (AST line 24574), log2 ≈ 387. -/
def «bn254_g1_mul» : Nat := («heap_mark» + 1) + («alloc» + 1) + («bn254_parse_g1» + 1) + Nat.max ((«heap_release» + 1)) (0) + («u256_from_be» + 1) + («ecp_mul» + 1) + («bn254_g1_to_bytes» + 1) + («heap_release» + 1)

/-- `pre_alt_bn128_mul` (AST line 24728), log2 ≈ 387. -/
def «pre_alt_bn128_mul» : Nat := («charge_gas» + 1) + («alloc» + 1) + («heap_mark» + 1) + («alloc» + 1) + («buffer_read» + 1) + («bn254_g1_mul» + 1) + («heap_release» + 1)

/-- `bn254_init` (AST line 22161), log2 ≈ 3. -/
def «bn254_init» : Nat := («alloc» + 1) + («alloc» + 1)

/-- `ecp_linefunc` (AST line 23910), log2 ≈ 140. -/
def «ecp_linefunc» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + Nat.max ((«fe_set_zero» + 1) + («fe_set_zero» + 1)) ((«fe_mul» + 1) + («fe_mul» + 1) + («fe_sub» + 1) + («fe_mul» + 1) + («fe_mul» + 1) + («fe_sub» + 1)) + («fe_is_zero» + 1) + Nat.max ((«fe_is_zero» + 1) + Nat.max ((«fe_sqr» + 1) + («fe_mul_small» + 1) + («fe_mul» + 1) + («fe_mul_small» + 1)) ((«fe_mul» + 1) + («fe_mul» + 1) + («fe_sub» + 1) + («fe_mul» + 1) + («heap_release» + 1))) (0) + («fe_mul» + 1) + («fe_mul» + 1) + («fe_sub» + 1) + («fe_mul» + 1) + («fe_mul» + 1) + («fe_mul» + 1) + («fe_sub» + 1) + («fe_mul» + 1) + («fe_sub» + 1) + («fe_mul» + 1) + («fe_mul» + 1) + («heap_release» + 1)

/-- `fq_neg` (AST line 22323), log2 ≈ 2. -/
def «fq_neg» : Nat := («u256_is_zero» + 1) + («u256_sub» + 1)

/-- `fe_neg` (AST line 23585), log2 ≈ 67. -/
def «fe_neg» : Nat := (2 ^ 64 + 1) * ((«fq_neg» + 1) + 1)

/-- `fq12_frob` (AST line 24051), log2 ≈ 71. -/
def «fq12_frob» : Nat := (6 + 1) * ((«fq_mul_small» + 1) + («fq_add» + 1) + («fq_neg» + 1) + («fq_mul» + 1) + («fq_mul» + 1) + («fq_mul» + 1) + («fq_mul» + 1) + («fq_sub» + 1) + («fq_add» + 1) + («fq_mul_small» + 1) + («fq_sub» + 1) + 1)

/-- `bn254_miller_raw` (AST line 24253), log2 ≈ 207. -/
def «bn254_miller_raw» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («memcpy» + 1) + («memcpy» + 1) + («fe_neg» + 1) + («fe_set_one» + 1) + («fe_set_one» + 1) + (2 ^ 64 + 1) * ((«ecp_linefunc» + 1) + («fq12_sqr» + 1) + («fq12_mul» + 1) + («fq12_sqr» + 1) + («fq12_mul» + 1) + («ecp_double» + 1) + Nat.max ((«ecp_linefunc» + 1) + («fq12_mul» + 1) + («fq12_mul» + 1) + («ecp_add» + 1)) (0) + Nat.max ((«ecp_linefunc» + 1) + («fq12_mul» + 1) + («fq12_mul» + 1) + («ecp_add» + 1)) (0) + 1) + («fq12_frob» + 1) + («fq12_frob» + 1) + («fq12_frob» + 1) + («fq12_frob» + 1) + («fq12_frob» + 1) + («fe_neg» + 1) + («fq12_frob» + 1) + («ecp_linefunc» + 1) + («fq12_mul» + 1) + («fq12_mul» + 1) + («ecp_add» + 1) + («ecp_linefunc» + 1) + («fq12_mul» + 1) + («fq12_mul» + 1) + («heap_release» + 1)

/-- `fe_add` (AST line 23547), log2 ≈ 67. -/
def «fe_add» : Nat := (2 ^ 64 + 1) * ((«fq_add» + 1) + 1)

/-- `bn254_parse_g2` (AST line 24436), log2 ≈ 69. -/
def «bn254_parse_g2» : Nat := («u256_from_be» + 1) + («u256_from_be» + 1) + («u256_from_be» + 1) + («u256_from_be» + 1) + («u256_lt» + 1) + («u256_lt» + 1) + («u256_lt» + 1) + («u256_lt» + 1) + («is_zero_bytes» + 1) + Nat.max ((«ecp_set_inf» + 1)) (0) + («fq_to_mont» + 1) + («fq_to_mont» + 1) + («fq_to_mont» + 1) + («fq_to_mont» + 1) + («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («fq2_mul» + 1) + («fq2_mul» + 1) + («fq2_mul» + 1) + («fe_add» + 1) + («memeq» + 1) + («heap_release» + 1)

/-- `ecp_is_inf` (AST line 23684), log2 ≈ 65. -/
def «ecp_is_inf» : Nat := («fe_is_zero» + 1)

/-- `fq12_cast` (AST line 24033), log2 ≈ 65. -/
def «fq12_cast» : Nat := («memzero» + 1)

/-- `fq_poly_deg` (AST line 24084), log2 ≈ 129. -/
def «fq_poly_deg» : Nat := (2 ^ 64 + 1) * ((«is_zero_bytes» + 1) + 1)

/-- `fq_poly_submul` (AST line 24103), log2 ≈ 38. -/
def «fq_poly_submul» : Nat := ((domainBytes + 1) + 1) * ((«fq_mul» + 1) + («fq_sub» + 1) + 1)

/-- `fq12_inv` (AST line 24124), log2 ≈ 391. -/
def «fq12_inv» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («memzero» + 1) + («memzero» + 1) + («memcpy» + 1) + («memzero» + 1) + («memzero» + 1) + (14 + 1) * ((«fq_poly_deg» + 1) + («fq_poly_deg» + 1) + («memzero» + 1) + («fq_inv» + 1) + (14 + 1) * ((«fq_mul» + 1) + («fq_poly_submul» + 1) + («fq_poly_deg» + 1) + 1) + («memcpy» + 1) + (13 + 1) * ((«u256_is_zero» + 1) + Nat.max ((«fq_poly_submul» + 1)) (0) + 1) + 1) + («fq_poly_deg» + 1) + Nat.max ((«memzero» + 1) + («heap_release» + 1)) (0) + («fq_inv» + 1) + (12 + 1) * ((«fq_mul» + 1) + 1) + («heap_release» + 1)

/-- `fq12_pow_words` (AST line 24225), log2 ≈ 201. -/
def «fq12_pow_words» : Nat := («fe_set_one» + 1) + (2 ^ 64 + 1) * (Nat.max ((«fq12_sqr» + 1)) (0) + Nat.max ((«fq12_mul» + 1)) (0) + 1)

/-- `fq12_twist` (AST line 23999), log2 ≈ 70. -/
def «fq12_twist» : Nat := («memzero» + 1) + (3 + 1) * ((«fq_mul_small» + 1) + («fq_sub» + 1) + 1)

/-- `bn254_pairing_check` (AST line 24600), log2 ≈ 391. -/
def «bn254_pairing_check» : Nat := («bn254_init» + 1) + («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («fe_set_one» + 1) + («fe_set_one» + 1) + (2 ^ 64 + 1) * ((«bn254_parse_g1» + 1) + Nat.max ((«heap_release» + 1)) (0) + («bn254_parse_g2» + 1) + Nat.max ((«heap_release» + 1)) (0) + («ecp_mul» + 1) + («ecp_is_inf» + 1) + Nat.max ((«heap_release» + 1)) (0) + («ecp_mul» + 1) + («ecp_is_inf» + 1) + Nat.max ((«heap_release» + 1)) (0) + («ecp_is_inf» + 1) + («ecp_is_inf» + 1) + Nat.max ((«fq12_twist» + 1) + («fq12_cast» + 1) + («bn254_miller_raw» + 1) + («fq12_mul» + 1) + («fq12_mul» + 1)) (0) + 1) + Nat.max ((«fq12_inv» + 1) + («fq12_mul» + 1) + («fq12_pow_words» + 1) + («memzero» + 1) + («memeq» + 1)) (0) + («heap_release» + 1)

/-- `pre_alt_bn128_pairing_check` (AST line 24757), log2 ≈ 391. -/
def «pre_alt_bn128_pairing_check» : Nat := («udivmod» + 1) + («charge_gas» + 1) + («bn254_pairing_check» + 1) + («alloc» + 1) + («memzero» + 1)

/-- `blake2_g` (AST line 20073), log2 ≈ 0. -/
def «blake2_g» : Nat := 0

/-- `blake2b_f` (AST line 20115), log2 ≈ 68. -/
def «blake2b_f» : Nat := («memcpy» + 1) + («memcpy» + 1) + (2 ^ 64 + 1) * ((«blake2_g» + 1) + («blake2_g» + 1) + («blake2_g» + 1) + («blake2_g» + 1) + («blake2_g» + 1) + («blake2_g» + 1) + («blake2_g» + 1) + («blake2_g» + 1) + 1) + (2 ^ 64 + 1) * (0 + 1)

/-- `pre_blake2f` (AST line 31632), log2 ≈ 69. -/
def «pre_blake2f» : Nat := («charge_gas» + 1) + («alloc» + 1) + («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1) + («blake2b_f» + 1) + (2 ^ 64 + 1) * ((«st_le64» + 1) + 1) + («heap_release» + 1)

/-- `bls_fp_add_raw` (AST line 26675), log2 ≈ 0. -/
def «bls_fp_add_raw» : Nat := 0

/-- `bls_fp_sub_raw` (AST line 26703), log2 ≈ 0. -/
def «bls_fp_sub_raw» : Nat := 0

/-- `bls_fp_add` (AST line 26731), log2 ≈ 2. -/
def «bls_fp_add» : Nat := («bls_fp_add_raw» + 1) + («bls_fp_sub_raw» + 1)

/-- `bls_fp_eq` (AST line 26607), log2 ≈ 0. -/
def «bls_fp_eq» : Nat := 0

/-- `bls_fp_is_zero` (AST line 26593), log2 ≈ 0. -/
def «bls_fp_is_zero» : Nat := 0

/-- `bls_fp_mul` (AST line 26791), log2 ≈ 7. -/
def «bls_fp_mul» : Nat := («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («bls_fp_sub_raw» + 1)

/-- `bls_fp_sqr` (AST line 27550), log2 ≈ 7. -/
def «bls_fp_sqr» : Nat := («bls_fp_mul» + 1)

/-- `bls_fp_sub` (AST line 26748), log2 ≈ 2. -/
def «bls_fp_sub» : Nat := («bls_fp_sub_raw» + 1) + («bls_fp_add_raw» + 1)

/-- `g1_copy` (AST line 28655), log2 ≈ 65. -/
def «g1_copy» : Nat := («memcpy» + 1)

/-- `g1_double` (AST line 28689), log2 ≈ 10. -/
def «g1_double» : Nat := («bls_fp_sqr» + 1) + («bls_fp_add» + 1) + («bls_fp_add» + 1) + («bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_add» + 1) + («bls_fp_add» + 1) + («bls_fp_add» + 1) + («bls_fp_sqr» + 1) + («bls_fp_sub» + 1) + («bls_fp_sqr» + 1) + («bls_fp_mul» + 1) + («bls_fp_add» + 1) + («bls_fp_sub» + 1) + («bls_fp_mul» + 1) + («bls_fp_sqr» + 1) + («bls_fp_mul» + 1) + («bls_fp_add» + 1) + («bls_fp_add» + 1) + («bls_fp_add» + 1) + («bls_fp_sub» + 1) + («bls_fp_mul» + 1) + («bls_fp_add» + 1) + («bls_fp_add» + 1) + («bls_fp_add» + 1)

/-- `g1_set_inf` (AST line 28628), log2 ≈ 0. -/
def «g1_set_inf» : Nat := 0

/-- `g1_add` (AST line 28747), log2 ≈ 66. -/
def «g1_add» : Nat := («bls_fp_is_zero» + 1) + Nat.max ((«g1_copy» + 1)) (0) + («bls_fp_is_zero» + 1) + Nat.max ((«g1_copy» + 1)) (0) + («bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_eq» + 1) + Nat.max ((«bls_fp_eq» + 1) + Nat.max ((«g1_double» + 1)) (0) + («g1_set_inf» + 1)) (0) + («bls_fp_sub» + 1) + («bls_fp_sub» + 1) + («bls_fp_sqr» + 1) + («bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_sqr» + 1) + («bls_fp_mul» + 1) + («bls_fp_sub» + 1) + («bls_fp_add» + 1) + («bls_fp_sub» + 1) + («bls_fp_mul» + 1) + («bls_fp_sub» + 1) + («bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_sub» + 1) + («bls_fp_mul» + 1)

/-- `bls_fp_from_be48` (AST line 27719), log2 ≈ 0. -/
def «bls_fp_from_be48» : Nat := 0

/-- `bls_fp_lt_raw` (AST line 26621), log2 ≈ 0. -/
def «bls_fp_lt_raw» : Nat := 0

/-- `bls_fp_to_mont` (AST line 27560), log2 ≈ 7. -/
def «bls_fp_to_mont» : Nat := («bls_fp_mul» + 1)

/-- `bls_fp_decode64` (AST line 27751), log2 ≈ 65. -/
def «bls_fp_decode64» : Nat := («is_zero_bytes» + 1) + («bls_fp_from_be48» + 1) + («bls_fp_lt_raw» + 1) + («bls_fp_to_mont» + 1)

/-- `g1_on_curve` (AST line 28884), log2 ≈ 8. -/
def «g1_on_curve» : Nat := («bls_fp_sqr» + 1) + («bls_fp_sqr» + 1) + («bls_fp_mul» + 1) + («bls_fp_add» + 1) + («bls_fp_eq» + 1)

/-- `g1_decode` (AST line 28901), log2 ≈ 66. -/
def «g1_decode» : Nat := («bls_fp_decode64» + 1) + («bls_fp_decode64» + 1) + («bls_fp_is_zero» + 1) + («bls_fp_is_zero» + 1) + («g1_on_curve» + 1)

/-- `bls_fp_from_mont` (AST line 27570), log2 ≈ 7. -/
def «bls_fp_from_mont» : Nat := («bls_fp_mul» + 1)

/-- `bls_fp_to_be48` (AST line 27729), log2 ≈ 5. -/
def «bls_fp_to_be48» : Nat := («st_be64» + 1) + («st_be64» + 1) + («st_be64» + 1) + («st_be64» + 1) + («st_be64» + 1) + («st_be64» + 1)

/-- `bls_fp_encode64` (AST line 27775), log2 ≈ 65. -/
def «bls_fp_encode64» : Nat := («bls_fp_from_mont» + 1) + («memzero» + 1) + («bls_fp_to_be48» + 1)

/-- `bls_fp_shr1` (AST line 27580), log2 ≈ 0. -/
def «bls_fp_shr1» : Nat := 0

/-- `bls_fp_half_can` (AST line 27590), log2 ≈ 2. -/
def «bls_fp_half_can» : Nat := Nat.max ((«bls_fp_shr1» + 1)) (0) + («bls_fp_add_raw» + 1)

/-- `bls_fp_inv_raw` (AST line 27605), log2 ≈ 388. -/
def «bls_fp_inv_raw» : Nat := («bls_fp_is_zero» + 1) + (2 ^ 256 + 1) * ((2 ^ 128 + 1) * ((«bls_fp_shr1» + 1) + («bls_fp_half_can» + 1) + 1) + (2 ^ 128 + 1) * ((«bls_fp_shr1» + 1) + («bls_fp_half_can» + 1) + 1) + («bls_fp_lt_raw» + 1) + («bls_fp_sub_raw» + 1) + («bls_fp_sub» + 1) + 1)

/-- `bls_fp_inv` (AST line 27658), log2 ≈ 388. -/
def «bls_fp_inv» : Nat := («bls_fp_inv_raw» + 1) + («bls_fp_mul» + 1)

/-- `g1_normalize` (AST line 28861), log2 ≈ 388. -/
def «g1_normalize» : Nat := («bls_fp_inv» + 1) + («bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_is_zero» + 1)

/-- `g1_encode` (AST line 28933), log2 ≈ 388. -/
def «g1_encode» : Nat := («heap_mark» + 1) + («alloc» + 1) + («g1_normalize» + 1) + («bls_fp_encode64» + 1) + («bls_fp_encode64» + 1) + («heap_release» + 1)

/-- `bls_g1_add_exec` (AST line 30340), log2 ≈ 388. -/
def «bls_g1_add_exec» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («g1_decode» + 1) + Nat.max ((«g1_decode» + 1)) (0) + Nat.max ((«heap_release» + 1)) (0) + («g1_add» + 1) + («g1_encode» + 1) + («heap_release» + 1)

/-- `pre_bls_g1_add` (AST line 31236), log2 ≈ 388. -/
def «pre_bls_g1_add» : Nat := («charge_gas» + 1) + («alloc» + 1) + («bls_g1_add_exec» + 1)

/-- `bls_g1_msm_discount` (AST line 31208), log2 ≈ 0. -/
def «bls_g1_msm_discount» : Nat := 0

/-- `g1_mul` (AST line 28824), log2 ≈ 130. -/
def «g1_mul» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («g1_copy» + 1) + («g1_set_inf» + 1) + (2 ^ 64 + 1) * (Nat.max ((«g1_double» + 1)) (0) + Nat.max ((«g1_add» + 1)) (0) + 1) + («g1_copy» + 1) + («heap_release» + 1)

/-- `g1_is_inf` (AST line 28644), log2 ≈ 1. -/
def «g1_is_inf» : Nat := («bls_fp_is_zero» + 1)

/-- `g1_subgroup_check` (AST line 28953), log2 ≈ 130. -/
def «g1_subgroup_check» : Nat := («heap_mark» + 1) + («alloc» + 1) + («g1_mul» + 1) + («g1_is_inf» + 1) + («heap_release» + 1)

/-- `bls_g1_msm_exec` (AST line 30370), log2 ≈ 388. -/
def «bls_g1_msm_exec» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«g1_decode» + 1) + Nat.max ((«heap_release» + 1)) (0) + («g1_subgroup_check» + 1) + Nat.max ((«heap_release» + 1)) (0) + («u256_from_be» + 1) + («g1_mul» + 1) + Nat.max ((«g1_copy» + 1)) ((«g1_add» + 1)) + 1) + («g1_encode» + 1) + («heap_release» + 1)

/-- `pre_bls_g1_msm` (AST line 31264), log2 ≈ 388. -/
def «pre_bls_g1_msm» : Nat := («udivmod» + 1) + («bls_g1_msm_discount» + 1) + («udivmod» + 1) + («charge_gas» + 1) + («alloc» + 1) + («bls_g1_msm_exec» + 1)

/-- `fp2_add` (AST line 27864), log2 ≈ 3. -/
def «fp2_add» : Nat := («bls_fp_add» + 1) + («bls_fp_add» + 1)

/-- `fp2_copy` (AST line 27791), log2 ≈ 65. -/
def «fp2_copy» : Nat := («memcpy» + 1)

/-- `fp2_eq` (AST line 27845), log2 ≈ 2. -/
def «fp2_eq» : Nat := («bls_fp_eq» + 1) + («bls_fp_eq» + 1)

/-- `fp2_mul` (AST line 27949), log2 ≈ 8. -/
def «fp2_mul» : Nat := («bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_add» + 1) + («bls_fp_add» + 1) + («bls_fp_mul» + 1) + («bls_fp_sub» + 1) + («bls_fp_sub» + 1) + («bls_fp_sub» + 1)

/-- `fp2_sqr` (AST line 27977), log2 ≈ 8. -/
def «fp2_sqr» : Nat := («bls_fp_add» + 1) + («bls_fp_sub» + 1) + («bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_add» + 1)

/-- `fp2_sub` (AST line 27884), log2 ≈ 3. -/
def «fp2_sub» : Nat := («bls_fp_sub» + 1) + («bls_fp_sub» + 1)

/-- `g2_copy` (AST line 28996), log2 ≈ 65. -/
def «g2_copy» : Nat := («memcpy» + 1)

/-- `g2_double` (AST line 29026), log2 ≈ 66. -/
def «g2_double» : Nat := («heap_mark» + 1) + («alloc» + 1) + («fp2_sqr» + 1) + («fp2_add» + 1) + («fp2_add» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_add» + 1) + («fp2_add» + 1) + («fp2_add» + 1) + («fp2_sqr» + 1) + («fp2_sub» + 1) + («fp2_sqr» + 1) + («fp2_mul» + 1) + («fp2_add» + 1) + («fp2_sub» + 1) + («fp2_mul» + 1) + («fp2_sqr» + 1) + («fp2_mul» + 1) + («fp2_add» + 1) + («fp2_add» + 1) + («fp2_add» + 1) + («fp2_sub» + 1) + («fp2_mul» + 1) + («fp2_add» + 1) + («fp2_add» + 1) + («fp2_add» + 1) + («fp2_copy» + 1) + («fp2_copy» + 1) + («fp2_copy» + 1) + («heap_release» + 1)

/-- `fp2_is_zero` (AST line 27829), log2 ≈ 0. -/
def «fp2_is_zero» : Nat := 0

/-- `g2_is_inf` (AST line 28986), log2 ≈ 1. -/
def «g2_is_inf» : Nat := («fp2_is_zero» + 1)

/-- `fp2_set_one` (AST line 27815), log2 ≈ 0. -/
def «fp2_set_one» : Nat := 0

/-- `fp2_set_zero` (AST line 27803), log2 ≈ 65. -/
def «fp2_set_zero» : Nat := («memzero» + 1)

/-- `g2_set_inf` (AST line 28970), log2 ≈ 65. -/
def «g2_set_inf» : Nat := («fp2_set_one» + 1) + («fp2_set_one» + 1) + («fp2_set_zero» + 1)

/-- `g2_add` (AST line 29109), log2 ≈ 68. -/
def «g2_add» : Nat := («g2_is_inf» + 1) + Nat.max ((«g2_copy» + 1)) (0) + («g2_is_inf» + 1) + Nat.max ((«g2_copy» + 1)) (0) + («heap_mark» + 1) + («alloc» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_eq» + 1) + Nat.max ((«fp2_eq» + 1) + («heap_release» + 1) + Nat.max ((«g2_double» + 1)) (0) + («g2_set_inf» + 1)) (0) + («fp2_sub» + 1) + («fp2_sub» + 1) + («fp2_sqr» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_sqr» + 1) + («fp2_mul» + 1) + («fp2_sub» + 1) + («fp2_add» + 1) + («fp2_sub» + 1) + («fp2_mul» + 1) + («fp2_sub» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_sub» + 1) + («fp2_mul» + 1) + («fp2_copy» + 1) + («fp2_copy» + 1) + («fp2_copy» + 1) + («heap_release» + 1)

/-- `g2_on_curve` (AST line 29276), log2 ≈ 10. -/
def «g2_on_curve» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («fp2_sqr» + 1) + («fp2_sqr» + 1) + («fp2_mul» + 1) + («fp2_add» + 1) + («fp2_eq» + 1) + («heap_release» + 1)

/-- `g2_decode` (AST line 29300), log2 ≈ 67. -/
def «g2_decode» : Nat := («bls_fp_decode64» + 1) + («bls_fp_decode64» + 1) + («bls_fp_decode64» + 1) + («bls_fp_decode64» + 1) + («fp2_is_zero» + 1) + («fp2_is_zero» + 1) + Nat.max ((«fp2_set_zero» + 1)) (0) + («fp2_set_one» + 1) + («g2_on_curve» + 1)

/-- `bls_fp_neg` (AST line 26765), log2 ≈ 2. -/
def «bls_fp_neg» : Nat := («bls_fp_is_zero» + 1) + («bls_fp_sub_raw» + 1)

/-- `fp2_inv` (AST line 28035), log2 ≈ 388. -/
def «fp2_inv» : Nat := («bls_fp_sqr» + 1) + («bls_fp_sqr» + 1) + («bls_fp_add» + 1) + («bls_fp_inv» + 1) + («bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_neg» + 1)

/-- `g2_normalize` (AST line 29247), log2 ≈ 388. -/
def «g2_normalize» : Nat := («heap_mark» + 1) + («alloc» + 1) + («g2_is_inf» + 1) + Nat.max ((«memzero» + 1) + («heap_release» + 1)) (0) + («fp2_inv» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («heap_release» + 1)

/-- `g2_encode` (AST line 29343), log2 ≈ 388. -/
def «g2_encode» : Nat := («heap_mark» + 1) + («alloc» + 1) + («g2_normalize» + 1) + («bls_fp_encode64» + 1) + («bls_fp_encode64» + 1) + («bls_fp_encode64» + 1) + («bls_fp_encode64» + 1) + («heap_release» + 1)

/-- `bls_g2_add_exec` (AST line 30416), log2 ≈ 388. -/
def «bls_g2_add_exec» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («g2_decode» + 1) + Nat.max ((«g2_decode» + 1)) (0) + Nat.max ((«heap_release» + 1)) (0) + («g2_add» + 1) + («g2_encode» + 1) + («heap_release» + 1)

/-- `pre_bls_g2_add` (AST line 31300), log2 ≈ 388. -/
def «pre_bls_g2_add» : Nat := («charge_gas» + 1) + («alloc» + 1) + («bls_g2_add_exec» + 1)

/-- `bls_g2_msm_discount` (AST line 31222), log2 ≈ 0. -/
def «bls_g2_msm_discount» : Nat := 0

/-- `g2_mul` (AST line 29213), log2 ≈ 132. -/
def «g2_mul» : Nat := («heap_mark» + 1) + («alloc» + 1) + («g2_set_inf» + 1) + (2 ^ 64 + 1) * (Nat.max ((«g2_double» + 1)) (0) + Nat.max ((«g2_add» + 1)) (0) + 1) + («g2_copy» + 1) + («heap_release» + 1)

/-- `g2_subgroup_check` (AST line 29367), log2 ≈ 132. -/
def «g2_subgroup_check» : Nat := («heap_mark» + 1) + («alloc» + 1) + («g2_mul» + 1) + («g2_is_inf» + 1) + («heap_release» + 1)

/-- `bls_g2_msm_exec` (AST line 30446), log2 ≈ 388. -/
def «bls_g2_msm_exec» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«g2_decode» + 1) + Nat.max ((«heap_release» + 1)) (0) + («g2_subgroup_check» + 1) + Nat.max ((«heap_release» + 1)) (0) + («u256_from_be» + 1) + («g2_mul» + 1) + Nat.max ((«g2_copy» + 1)) ((«g2_add» + 1)) + 1) + («g2_encode» + 1) + («heap_release» + 1)

/-- `pre_bls_g2_msm` (AST line 31328), log2 ≈ 388. -/
def «pre_bls_g2_msm» : Nat := («udivmod» + 1) + («bls_g2_msm_discount» + 1) + («udivmod» + 1) + («charge_gas» + 1) + («alloc» + 1) + («bls_g2_msm_exec» + 1)

/-- `iso_horner_fp2` (AST line 30055), log2 ≈ 73. -/
def «iso_horner_fp2» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («fp2_copy» + 1) + (2 ^ 64 + 1) * ((«fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_add» + 1) + 1) + («fp2_copy» + 1) + («heap_release» + 1)

/-- `iso_map_g2` (AST line 30084), log2 ≈ 75. -/
def «iso_map_g2» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («fp2_copy» + 1) + («fp2_sqr» + 1) + («fp2_mul» + 1) + («iso_horner_fp2» + 1) + («iso_horner_fp2» + 1) + («iso_horner_fp2» + 1) + («iso_horner_fp2» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («g2_copy» + 1) + («heap_release» + 1)

/-- `fp2_neg` (AST line 27904), log2 ≈ 3. -/
def «fp2_neg» : Nat := («bls_fp_neg» + 1) + («bls_fp_neg» + 1)

/-- `bls_fp_sgn0` (AST line 27696), log2 ≈ 7. -/
def «bls_fp_sgn0» : Nat := («bls_fp_from_mont» + 1)

/-- `fp2_sgn0` (AST line 28096), log2 ≈ 8. -/
def «fp2_sgn0» : Nat := («bls_fp_sgn0» + 1) + («bls_fp_is_zero» + 1) + («bls_fp_sgn0» + 1)

/-- `fp2_pow` (AST line 28059), log2 ≈ 73. -/
def «fp2_pow» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («fp2_copy» + 1) + («fp2_set_one» + 1) + (2 ^ 64 + 1) * (Nat.max ((«fp2_sqr» + 1)) (0) + Nat.max ((«fp2_mul» + 1)) (0) + 1) + («fp2_copy» + 1) + («heap_release» + 1)

/-- `swu_sqrt_division_fp2` (AST line 29879), log2 ≈ 73. -/
def «swu_sqrt_division_fp2» : Nat := («heap_mark» + 1) + («alloc» + 1) + («fp2_copy» + 1) + (6 + 1) * ((«fp2_mul» + 1) + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_pow» + 1) + («fp2_mul» + 1) + («fp2_copy» + 1) + (4 + 1) * ((«fp2_mul» + 1) + («fp2_sqr» + 1) + («fp2_mul» + 1) + («fp2_sub» + 1) + («fp2_is_zero» + 1) + Nat.max ((«fp2_copy» + 1)) (0) + 1) + («heap_release» + 1)

/-- `swu_g2` (AST line 29940), log2 ≈ 73. -/
def «swu_g2» : Nat := («heap_mark» + 1) + («alloc» + 1) + («fp2_sqr» + 1) + («fp2_mul» + 1) + («fp2_sqr» + 1) + («fp2_add» + 1) + («fp2_mul» + 1) + («fp2_neg» + 1) + («fp2_set_one» + 1) + («fp2_add» + 1) + («fp2_mul» + 1) + («fp2_is_zero» + 1) + Nat.max ((«fp2_mul» + 1)) (0) + («fp2_sqr» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_sqr» + 1) + («fp2_mul» + 1) + («fp2_add» + 1) + («fp2_mul» + 1) + («fp2_add» + 1) + («swu_sqrt_division_fp2» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_sqr» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + (4 + 1) * ((«fp2_mul» + 1) + («fp2_sqr» + 1) + («fp2_mul» + 1) + («fp2_sub» + 1) + («fp2_is_zero» + 1) + Nat.max ((«fp2_copy» + 1)) (0) + 1) + Nat.max ((«fp2_mul» + 1)) (0) + («fp2_sgn0» + 1) + («fp2_sgn0» + 1) + Nat.max ((«fp2_neg» + 1)) (0) + («fp2_mul» + 1) + («fp2_copy» + 1) + («fp2_copy» + 1) + («fp2_copy» + 1) + («heap_release» + 1)

/-- `map_fp2_to_g2` (AST line 30128), log2 ≈ 132. -/
def «map_fp2_to_g2» : Nat := («heap_mark» + 1) + («alloc» + 1) + («swu_g2» + 1) + («iso_map_g2» + 1) + («g2_mul» + 1) + («heap_release» + 1)

/-- `bls_map_fp2_to_g2_exec` (AST line 30581), log2 ≈ 388. -/
def «bls_map_fp2_to_g2_exec» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («bls_fp_decode64» + 1) + Nat.max ((«bls_fp_decode64» + 1)) (0) + Nat.max ((«heap_release» + 1)) (0) + («map_fp2_to_g2» + 1) + («g2_encode» + 1) + («heap_release» + 1)

/-- `pre_bls_map_fp2_to_g2` (AST line 31426), log2 ≈ 388. -/
def «pre_bls_map_fp2_to_g2» : Nat := («charge_gas» + 1) + («alloc» + 1) + («bls_map_fp2_to_g2_exec» + 1)

/-- `iso_horner_fp` (AST line 29789), log2 ≈ 72. -/
def «iso_horner_fp» : Nat := (2 ^ 64 + 1) * ((«bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_add» + 1) + 1)

/-- `iso_map_g1` (AST line 29812), log2 ≈ 74. -/
def «iso_map_g1» : Nat := («heap_mark» + 1) + («alloc» + 1) + (15 + 1) * ((«bls_fp_mul» + 1) + 1) + («iso_horner_fp» + 1) + («iso_horner_fp» + 1) + («iso_horner_fp» + 1) + («iso_horner_fp» + 1) + («bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («heap_release» + 1)

/-- `bls_fp_pow` (AST line 27669), log2 ≈ 72. -/
def «bls_fp_pow» : Nat := (2 ^ 64 + 1) * (Nat.max ((«bls_fp_mul» + 1)) (0) + Nat.max ((«bls_fp_mul» + 1)) (0) + 1)

/-- `swu_sqrt_division_fp` (AST line 29697), log2 ≈ 72. -/
def «swu_sqrt_division_fp» : Nat := («bls_fp_mul» + 1) + («bls_fp_sqr» + 1) + («bls_fp_mul» + 1) + («bls_fp_pow» + 1) + («bls_fp_mul» + 1) + («bls_fp_sqr» + 1) + («bls_fp_mul» + 1) + («bls_fp_sub» + 1) + («bls_fp_is_zero» + 1)

/-- `swu_g1` (AST line 29719), log2 ≈ 72. -/
def «swu_g1» : Nat := («bls_fp_sqr» + 1) + («bls_fp_mul» + 1) + («bls_fp_sqr» + 1) + («bls_fp_add» + 1) + («bls_fp_mul» + 1) + («bls_fp_neg» + 1) + («bls_fp_add» + 1) + («bls_fp_mul» + 1) + («bls_fp_is_zero» + 1) + Nat.max ((«bls_fp_mul» + 1)) (0) + («bls_fp_sqr» + 1) + («bls_fp_mul» + 1) + («bls_fp_sqr» + 1) + («bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_add» + 1) + («bls_fp_mul» + 1) + («bls_fp_add» + 1) + («swu_sqrt_division_fp» + 1) + Nat.max ((«bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_mul» + 1) + («bls_fp_mul» + 1)) (0) + («bls_fp_sgn0» + 1) + («bls_fp_sgn0» + 1) + Nat.max ((«bls_fp_neg» + 1)) (0) + («bls_fp_mul» + 1)

/-- `map_fp_to_g1` (AST line 29859), log2 ≈ 130. -/
def «map_fp_to_g1» : Nat := («heap_mark» + 1) + («alloc» + 1) + («swu_g1» + 1) + («iso_map_g1» + 1) + («g1_mul» + 1) + («heap_release» + 1)

/-- `bls_map_fp_to_g1_exec` (AST line 30554), log2 ≈ 388. -/
def «bls_map_fp_to_g1_exec» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («bls_fp_decode64» + 1) + Nat.max ((«heap_release» + 1)) (0) + («map_fp_to_g1» + 1) + («g1_encode» + 1) + («heap_release» + 1)

/-- `pre_bls_map_fp_to_g1` (AST line 31398), log2 ≈ 388. -/
def «pre_bls_map_fp_to_g1» : Nat := («charge_gas» + 1) + («alloc» + 1) + («bls_map_fp_to_g1_exec» + 1)

/-- `fp6_copy` (AST line 28118), log2 ≈ 65. -/
def «fp6_copy» : Nat := («memcpy» + 1)

/-- `fp6_neg` (AST line 28190), log2 ≈ 5. -/
def «fp6_neg» : Nat := («fp2_neg» + 1) + («fp2_neg» + 1) + («fp2_neg» + 1)

/-- `fp12_conj` (AST line 28429), log2 ≈ 65. -/
def «fp12_conj» : Nat := («fp6_copy» + 1) + («fp6_neg» + 1)

/-- `fp12_copy` (AST line 28339), log2 ≈ 65. -/
def «fp12_copy» : Nat := («memcpy» + 1)

/-- `fp6_add` (AST line 28158), log2 ≈ 5. -/
def «fp6_add» : Nat := («fp2_add» + 1) + («fp2_add» + 1) + («fp2_add» + 1)

/-- `fp2_mul_xi` (AST line 27999), log2 ≈ 3. -/
def «fp2_mul_xi» : Nat := («bls_fp_sub» + 1) + («bls_fp_add» + 1)

/-- `fp6_mul` (AST line 28206), log2 ≈ 12. -/
def «fp6_mul» : Nat := («heap_mark» + 1) + («alloc» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_add» + 1) + («fp2_mul_xi» + 1) + («fp2_add» + 1) + («fp2_mul_xi» + 1) + («fp2_add» + 1) + («fp2_add» + 1) + («fp2_add» + 1) + («fp2_add» + 1) + («heap_release» + 1)

/-- `fp6_mul_v` (AST line 28255), log2 ≈ 66. -/
def «fp6_mul_v» : Nat := («heap_mark» + 1) + («alloc» + 1) + («fp2_mul_xi» + 1) + («fp2_copy» + 1) + («fp2_copy» + 1) + («fp2_copy» + 1) + («heap_release» + 1)

/-- `fp6_sub` (AST line 28174), log2 ≈ 5. -/
def «fp6_sub» : Nat := («fp2_sub» + 1) + («fp2_sub» + 1) + («fp2_sub» + 1)

/-- `fp12_mul` (AST line 28382), log2 ≈ 66. -/
def «fp12_mul» : Nat := («heap_mark» + 1) + («alloc» + 1) + («fp6_mul» + 1) + («fp6_mul» + 1) + («fp6_add» + 1) + («fp6_add» + 1) + («fp6_mul» + 1) + («fp6_sub» + 1) + («fp6_sub» + 1) + («fp6_mul_v» + 1) + («fp6_add» + 1) + («heap_release» + 1)

/-- `fp6_set_one` (AST line 28142), log2 ≈ 66. -/
def «fp6_set_one» : Nat := («fp2_set_one» + 1) + («fp2_set_zero» + 1) + («fp2_set_zero» + 1)

/-- `fp6_set_zero` (AST line 28130), log2 ≈ 65. -/
def «fp6_set_zero» : Nat := («memzero» + 1)

/-- `fp12_set_one` (AST line 28351), log2 ≈ 66. -/
def «fp12_set_one» : Nat := («fp6_set_one» + 1) + («fp6_set_zero» + 1)

/-- `fp12_pow_absx` (AST line 28508), log2 ≈ 131. -/
def «fp12_pow_absx» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («fp12_copy» + 1) + («fp12_set_one» + 1) + (2 ^ 64 + 1) * (Nat.max ((«fp12_mul» + 1)) (0) + Nat.max ((«fp12_mul» + 1)) (0) + 1) + («fp12_copy» + 1) + («heap_release» + 1)

/-- `fp12_exp_x` (AST line 28545), log2 ≈ 131. -/
def «fp12_exp_x» : Nat := («fp12_pow_absx» + 1) + («fp12_conj» + 1)

/-- `fp2_conj` (AST line 27932), log2 ≈ 2. -/
def «fp2_conj» : Nat := («bls_fp_neg» + 1)

/-- `fp12_frob` (AST line 28476), log2 ≈ 11. -/
def «fp12_frob» : Nat := («fp2_conj» + 1) + («fp2_conj» + 1) + («fp2_mul» + 1) + («fp2_conj» + 1) + («fp2_mul» + 1) + («fp2_conj» + 1) + («fp2_mul» + 1) + («fp2_conj» + 1) + («fp2_mul» + 1) + («fp2_conj» + 1) + («fp2_mul» + 1)

/-- `fp6_inv` (AST line 28277), log2 ≈ 388. -/
def «fp6_inv» : Nat := («heap_mark» + 1) + («alloc» + 1) + («fp2_sqr» + 1) + («fp2_mul» + 1) + («fp2_mul_xi» + 1) + («fp2_sub» + 1) + («fp2_sqr» + 1) + («fp2_mul_xi» + 1) + («fp2_mul» + 1) + («fp2_sub» + 1) + («fp2_sqr» + 1) + («fp2_mul» + 1) + («fp2_sub» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_add» + 1) + («fp2_mul_xi» + 1) + («fp2_mul» + 1) + («fp2_add» + 1) + («fp2_inv» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («heap_release» + 1)

/-- `fp12_inv` (AST line 28443), log2 ≈ 388. -/
def «fp12_inv» : Nat := («heap_mark» + 1) + («alloc» + 1) + («fp6_mul» + 1) + («fp6_mul» + 1) + («fp6_mul_v» + 1) + («fp6_sub» + 1) + («fp6_inv» + 1) + («fp6_mul» + 1) + («fp6_mul» + 1) + («fp6_neg» + 1) + («heap_release» + 1)

/-- `fp12_final_exp` (AST line 28559), log2 ≈ 388. -/
def «fp12_final_exp» : Nat := («heap_mark» + 1) + («alloc» + 1) + («fp12_inv» + 1) + («fp12_conj» + 1) + («fp12_mul» + 1) + («fp12_frob» + 1) + («fp12_frob» + 1) + («fp12_mul» + 1) + («fp12_exp_x» + 1) + («fp12_conj» + 1) + («fp12_mul» + 1) + («fp12_exp_x» + 1) + («fp12_conj» + 1) + («fp12_mul» + 1) + («fp12_exp_x» + 1) + («fp12_frob» + 1) + («fp12_mul» + 1) + («fp12_exp_x» + 1) + («fp12_exp_x» + 1) + («fp12_frob» + 1) + («fp12_frob» + 1) + («fp12_mul» + 1) + («fp12_conj» + 1) + («fp12_mul» + 1) + («fp12_mul» + 1) + («fp12_mul» + 1) + («fp12_mul» + 1) + («heap_release» + 1)

/-- `fp12_is_one` (AST line 28365), log2 ≈ 67. -/
def «fp12_is_one» : Nat := («heap_mark» + 1) + («alloc» + 1) + («fp12_set_one» + 1) + («memeq» + 1) + («heap_release» + 1)

/-- `pair_addition_step` (AST line 29484), log2 ≈ 65. -/
def «pair_addition_step» : Nat := («heap_mark» + 1) + («alloc» + 1) + («fp2_sqr» + 1) + («fp2_sqr» + 1) + («fp2_mul» + 1) + («fp2_add» + 1) + («fp2_sqr» + 1) + («fp2_sub» + 1) + («fp2_sub» + 1) + («fp2_mul» + 1) + («fp2_sub» + 1) + («fp2_sqr» + 1) + («fp2_add» + 1) + («fp2_add» + 1) + («fp2_mul» + 1) + («fp2_sub» + 1) + («fp2_sub» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_sqr» + 1) + («fp2_sub» + 1) + («fp2_sub» + 1) + («fp2_sub» + 1) + («fp2_add» + 1) + («fp2_sqr» + 1) + («fp2_sub» + 1) + («fp2_sub» + 1) + («fp2_add» + 1) + («fp2_sub» + 1) + («fp2_mul» + 1) + («fp2_mul» + 1) + («fp2_add» + 1) + («fp2_sub» + 1) + («fp2_copy» + 1) + («fp2_sqr» + 1) + («fp2_sub» + 1) + («fp2_sqr» + 1) + («fp2_sub» + 1) + («fp2_add» + 1) + («fp2_sub» + 1) + («fp2_add» + 1) + («fp2_neg» + 1) + («fp2_add» + 1) + («heap_release» + 1)

/-- `pair_doubling_step` (AST line 29384), log2 ≈ 65. -/
def «pair_doubling_step» : Nat := («heap_mark» + 1) + («alloc» + 1) + («fp2_sqr» + 1) + («fp2_sqr» + 1) + («fp2_sqr» + 1) + («fp2_add» + 1) + («fp2_sqr» + 1) + («fp2_sub» + 1) + («fp2_sub» + 1) + («fp2_add» + 1) + («fp2_add» + 1) + («fp2_add» + 1) + («fp2_add» + 1) + («fp2_sqr» + 1) + («fp2_sqr» + 1) + («fp2_sub» + 1) + («fp2_sub» + 1) + («fp2_add» + 1) + («fp2_sqr» + 1) + («fp2_sub» + 1) + («fp2_sub» + 1) + («fp2_sub» + 1) + («fp2_mul» + 1) + («fp2_add» + 1) + («fp2_add» + 1) + («fp2_add» + 1) + («fp2_sub» + 1) + («fp2_copy» + 1) + («fp2_mul» + 1) + («fp2_add» + 1) + («fp2_neg» + 1) + («fp2_sqr» + 1) + («fp2_sub» + 1) + («fp2_sub» + 1) + («fp2_add» + 1) + («fp2_add» + 1) + («fp2_sub» + 1) + («fp2_mul» + 1) + («fp2_add» + 1) + («heap_release» + 1)

/-- `fp2_scale` (AST line 28017), log2 ≈ 8. -/
def «fp2_scale» : Nat := («bls_fp_mul» + 1) + («bls_fp_mul» + 1)

/-- `pair_ell` (AST line 29595), log2 ≈ 67. -/
def «pair_ell» : Nat := («heap_mark» + 1) + («alloc» + 1) + («memzero» + 1) + («fp2_copy» + 1) + («fp2_scale» + 1) + («fp2_scale» + 1) + («fp12_mul» + 1) + («heap_release» + 1)

/-- `pair_miller_loop` (AST line 29619), log2 ≈ 132. -/
def «pair_miller_loop» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («fp2_copy» + 1) + («fp2_copy» + 1) + («fp2_set_one» + 1) + («fp12_set_one» + 1) + (2 ^ 64 + 1) * ((«fp12_mul» + 1) + («pair_doubling_step» + 1) + («pair_ell» + 1) + Nat.max ((«pair_addition_step» + 1) + («pair_ell» + 1)) (0) + 1) + («fp12_conj» + 1) + («heap_release» + 1)

/-- `pair_accumulate` (AST line 29661), log2 ≈ 389. -/
def «pair_accumulate» : Nat := («g1_is_inf» + 1) + («g2_is_inf» + 1) + («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («g1_normalize» + 1) + («g2_normalize» + 1) + («pair_miller_loop» + 1) + («fp12_mul» + 1) + («heap_release» + 1)

/-- `bls_pairing_exec` (AST line 30492), log2 ≈ 453. -/
def «bls_pairing_exec» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («fp12_set_one» + 1) + (2 ^ 64 + 1) * ((«g1_decode» + 1) + Nat.max ((«heap_release» + 1)) (0) + («g1_subgroup_check» + 1) + Nat.max ((«heap_release» + 1)) (0) + («g2_decode» + 1) + Nat.max ((«heap_release» + 1)) (0) + («g2_subgroup_check» + 1) + Nat.max ((«heap_release» + 1)) (0) + («pair_accumulate» + 1) + 1) + («fp12_final_exp» + 1) + («fp12_is_one» + 1) + («memzero» + 1) + («heap_release» + 1)

/-- `pre_bls_pairing` (AST line 31364), log2 ≈ 453. -/
def «pre_bls_pairing» : Nat := («udivmod» + 1) + («charge_gas» + 1) + («alloc» + 1) + («bls_pairing_exec» + 1)

/-- `secp256k1_address_of_point` (AST line 7465), log2 ≈ 100. -/
def «secp256k1_address_of_point» : Nat := («heap_mark» + 1) + («alloc» + 1) + («keccak256» + 1) + («memcpy» + 1) + («heap_release» + 1)

/-- `secp256k1_ecrecover` (AST line 7483), log2 ≈ 389. -/
def «secp256k1_ecrecover» : Nat := («heap_mark» + 1) + («alloc» + 1) + («secp256k1_recover» + 1) + Nat.max ((«secp256k1_address_of_point» + 1)) (0) + («heap_release» + 1)

/-- `pre_ecrecover` (AST line 31556), log2 ≈ 389. -/
def «pre_ecrecover» : Nat := («charge_gas» + 1) + («alloc» + 1) + («alloc» + 1) + («heap_mark» + 1) + («alloc» + 1) + («buffer_read» + 1) + («u256_from_be» + 1) + («u256_from_be» + 1) + («u256_from_be» + 1) + («u256_fits_word» + 1) + Nat.max ((«heap_release» + 1)) (0) + («secp256k1_ecrecover» + 1) + Nat.max ((«heap_release» + 1)) (0) + («memzero» + 1) + («heap_release» + 1)

/-- `pre_identity` (AST line 31515), log2 ≈ 3. -/
def «pre_identity» : Nat := («words_of» + 1) + («charge_gas» + 1)

/-- `bls_fp_is_high` (AST line 27707), log2 ≈ 7. -/
def «bls_fp_is_high» : Nat := («bls_fp_from_mont» + 1) + («bls_fp_lt_raw» + 1)

/-- `kzg_decompress_g1` (AST line 30148), log2 ≈ 72. -/
def «kzg_decompress_g1» : Nat := («heap_mark» + 1) + («alloc» + 1) + («memcpy» + 1) + («bls_fp_from_be48» + 1) + («heap_release» + 1) + Nat.max ((«bls_fp_is_zero» + 1) + («g1_set_inf» + 1)) (0) + («bls_fp_lt_raw» + 1) + («bls_fp_to_mont» + 1) + («bls_fp_sqr» + 1) + («bls_fp_mul» + 1) + («bls_fp_add» + 1) + («bls_fp_pow» + 1) + («bls_fp_sqr» + 1) + («bls_fp_eq» + 1) + («bls_fp_is_high» + 1) + Nat.max ((«bls_fp_neg» + 1)) (0)

/-- `kzg_load_g1` (AST line 30216), log2 ≈ 130. -/
def «kzg_load_g1» : Nat := Nat.max ((«is_zero_bytes» + 1) + Nat.max ((«g1_set_inf» + 1)) (0)) (0) + («kzg_decompress_g1» + 1) + («g1_is_inf» + 1) + («g1_subgroup_check» + 1)

/-- `g2_neg` (AST line 29008), log2 ≈ 66. -/
def «g2_neg» : Nat := Nat.max ((«fp2_copy» + 1) + («fp2_copy» + 1)) (0) + («fp2_neg» + 1)

/-- `kzg_neg_scalar` (AST line 30245), log2 ≈ 65. -/
def «kzg_neg_scalar» : Nat := («u256_from_be» + 1) + («u256_is_zero» + 1) + («u256_sub» + 1)

/-- `kzg_verify` (AST line 30267), log2 ≈ 390. -/
def «kzg_verify» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («fp2_copy» + 1) + («fp2_copy» + 1) + («fp2_set_one» + 1) + («kzg_neg_scalar» + 1) + («g2_mul» + 1) + («fp2_copy» + 1) + («fp2_copy» + 1) + («fp2_set_one» + 1) + («g2_add» + 1) + («memcpy» + 1) + («memcpy» + 1) + («kzg_neg_scalar» + 1) + («g1_mul» + 1) + («g1_add» + 1) + («g2_neg» + 1) + («fp12_set_one» + 1) + («pair_accumulate» + 1) + («pair_accumulate» + 1) + («fp12_final_exp» + 1) + («fp12_is_one» + 1) + («heap_release» + 1)

/-- `kzg_point_evaluation_exec` (AST line 30611), log2 ≈ 390. -/
def «kzg_point_evaluation_exec» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («sha256» + 1) + («memeq» + 1) + Nat.max ((«heap_release» + 1)) (0) + («kzg_load_g1» + 1) + Nat.max ((«heap_release» + 1)) (0) + («kzg_load_g1» + 1) + Nat.max ((«heap_release» + 1)) (0) + («u256_from_be» + 1) + («u256_from_be» + 1) + («u256_lt» + 1) + («u256_lt» + 1) + Nat.max ((«heap_release» + 1)) (0) + («kzg_verify» + 1) + («heap_release» + 1) + («memzero» + 1) + («u256_to_be32» + 1)

/-- `pre_kzg_point_evaluation` (AST line 31454), log2 ≈ 390. -/
def «pre_kzg_point_evaluation» : Nat := («charge_gas» + 1) + («alloc» + 1) + («kzg_point_evaluation_exec» + 1)

/-- `be_top_bit` (AST line 20407), log2 ≈ 66. -/
def «be_top_bit» : Nat := (2 ^ 64 + 1) * (Nat.max ((«bit_length64» + 1)) (0) + 1)

/-- `bn_from_be` (AST line 20170), log2 ≈ 66. -/
def «bn_from_be» : Nat := (2 ^ 64 + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1)

/-- `bn_divmnu` (AST line 20253), log2 ≈ 257. -/
def «bn_divmnu» : Nat := Nat.max ((2 ^ 64 + 1) * ((«div64by32» + 1) + 1)) (0) + («nlz32» + 1) + (2 ^ 64 + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1) + (2 ^ 64 + 1) * (Nat.max (0) ((«div64by32» + 1)) + (2 ^ 192 + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1) + Nat.max ((2 ^ 64 + 1) * (0 + 1)) (0) + 1) + (2 ^ 64 + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1)

/-- `bn_mod` (AST line 20386), log2 ≈ 257. -/
def «bn_mod» : Nat := («digits_len» + 1) + Nat.max ((«memcpy» + 1) + («memzero» + 1)) (0) + («bn_divmnu» + 1)

/-- `bn_mul` (AST line 20218), log2 ≈ 129. -/
def «bn_mul» : Nat := (2 ^ 64 + 1) * (0 + 1) + (2 ^ 64 + 1) * ((2 ^ 64 + 1) * (0 + 1) + 1)

/-- `bn_to_be` (AST line 20196), log2 ≈ 65. -/
def «bn_to_be» : Nat := (2 ^ 64 + 1) * (0 + 1)

/-- `modexp` (AST line 20427), log2 ≈ 322. -/
def «modexp» : Nat := («heap_mark» + 1) + («alloc» + 1) + («bn_from_be» + 1) + («digits_len» + 1) + Nat.max ((«memzero» + 1) + («heap_release» + 1)) (0) + («max» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («bn_from_be» + 1) + («bn_mod» + 1) + («be_top_bit» + 1) + Nat.max ((«memzero» + 1)) ((«memcpy» + 1) + (2 ^ 64 + 1) * ((«bn_mul» + 1) + («bn_mod» + 1) + Nat.max ((«bn_mul» + 1) + («bn_mod» + 1)) (0) + 1)) + («bn_to_be» + 1) + («heap_release» + 1)

/-- `modexp_gas` (AST line 31689), log2 ≈ 3. -/
def «modexp_gas» : Nat := («max» + 1) + («u256_bit_length» + 1)

/-- `sat_word` (AST line 14833), log2 ≈ 0. -/
def «sat_word» : Nat := 0

/-- `pre_modexp` (AST line 31725), log2 ≈ 322. -/
def «pre_modexp» : Nat := («buffer_read» + 1) + («u256_from_be» + 1) + («sat_word» + 1) + («u256_from_be» + 1) + («sat_word» + 1) + («u256_from_be» + 1) + («sat_word» + 1) + («min» + 1) + («buffer_read» + 1) + («u256_from_be» + 1) + («modexp_gas» + 1) + («charge_gas» + 1) + Nat.max ((«alloc» + 1)) (0) + («alloc» + 1) + («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («buffer_read» + 1) + («buffer_read» + 1) + («buffer_read» + 1) + («modexp» + 1) + («heap_release» + 1)

/-- `p256_fp_add` (AST line 20490), log2 ≈ 3. -/
def «p256_fp_add» : Nat := («u256_add_carry» + 1) + Nat.max ((«u256_sub» + 1)) (0) + («u256_lt» + 1) + Nat.max ((«u256_sub» + 1)) (0)

/-- `p256_fp_reduce` (AST line 20527), log2 ≈ 2. -/
def «p256_fp_reduce» : Nat := («u256_lt» + 1) + Nat.max ((«u256_sub» + 1)) (0)

/-- `p256_fp_mul` (AST line 20542), log2 ≈ 131. -/
def «p256_fp_mul» : Nat := (2 ^ 128 + 1) * ((«u256_add_carry» + 1) + 1) + (2 ^ 128 + 1) * ((«u256_lt» + 1) + («u256_sub» + 1) + 1) + («p256_fp_reduce» + 1)

/-- `p256_fp_sqr` (AST line 21184), log2 ≈ 131. -/
def «p256_fp_sqr» : Nat := (2 ^ 128 + 1) * ((«u256_add_carry» + 1) + 1) + (2 ^ 128 + 1) * ((«u256_lt» + 1) + («u256_sub» + 1) + 1) + («p256_fp_reduce» + 1)

/-- `p256_fp_sub` (AST line 20511), log2 ≈ 2. -/
def «p256_fp_sub» : Nat := («u256_lt» + 1) + («u256_sub» + 1) + Nat.max ((«u256_add» + 1)) (0)

/-- `p256_set_infinity` (AST line 21782), log2 ≈ 0. -/
def «p256_set_infinity» : Nat := 0

/-- `p256_ec_double` (AST line 21814), log2 ≈ 134. -/
def «p256_ec_double» : Nat := («u256_is_zero» + 1) + («u256_is_zero» + 1) + Nat.max ((«p256_set_infinity» + 1)) (0) + («p256_fp_sqr» + 1) + («p256_fp_sqr» + 1) + («p256_fp_mul» + 1) + («p256_fp_sub» + 1) + («p256_fp_add» + 1) + («p256_fp_mul» + 1) + («p256_fp_add» + 1) + («p256_fp_add» + 1) + («p256_fp_sqr» + 1) + («p256_fp_add» + 1) + («p256_fp_add» + 1) + («p256_fp_add» + 1) + («p256_fp_sub» + 1) + («p256_fp_add» + 1) + («p256_fp_sqr» + 1) + («p256_fp_sub» + 1) + («p256_fp_sub» + 1) + («p256_fp_sub» + 1) + («p256_fp_mul» + 1) + («p256_fp_sqr» + 1) + («p256_fp_add» + 1) + («p256_fp_add» + 1) + («p256_fp_add» + 1) + («p256_fp_sub» + 1)

/-- `p256_set_affine` (AST line 21798), log2 ≈ 0. -/
def «p256_set_affine» : Nat := 0

/-- `p256_ec_add_affine` (AST line 21880), log2 ≈ 135. -/
def «p256_ec_add_affine» : Nat := («u256_is_zero» + 1) + Nat.max ((«p256_set_affine» + 1)) (0) + («p256_fp_sqr» + 1) + («p256_fp_mul» + 1) + («p256_fp_mul» + 1) + («p256_fp_mul» + 1) + («u256_eq» + 1) + Nat.max ((«p256_fp_add» + 1) + («u256_is_zero» + 1) + Nat.max ((«p256_set_infinity» + 1)) (0) + («p256_ec_double» + 1)) (0) + («p256_fp_sub» + 1) + («p256_fp_sub» + 1) + («p256_fp_sqr» + 1) + («p256_fp_mul» + 1) + («p256_fp_mul» + 1) + («p256_fp_sqr» + 1) + («p256_fp_sub» + 1) + («p256_fp_add» + 1) + («p256_fp_sub» + 1) + («p256_fp_sub» + 1) + («p256_fp_mul» + 1) + («p256_fp_mul» + 1) + («p256_fp_sub» + 1) + («p256_fp_mul» + 1)

/-- `p256_ec_mul2` (AST line 21944), log2 ≈ 200. -/
def «p256_ec_mul2» : Nat := («p256_set_infinity» + 1) + («u256_bit_length» + 1) + («u256_bit_length» + 1) + («max» + 1) + (2 ^ 64 + 1) * ((«p256_ec_double» + 1) + («u256_bit» + 1) + Nat.max ((«p256_ec_add_affine» + 1)) (0) + («u256_bit» + 1) + Nat.max ((«p256_ec_add_affine» + 1)) (0) + 1)

/-- `p256_on_curve` (AST line 22001), log2 ≈ 132. -/
def «p256_on_curve» : Nat := («p256_fp_sqr» + 1) + («p256_fp_sqr» + 1) + («p256_fp_mul» + 1) + («p256_fp_add» + 1) + («p256_fp_add» + 1) + («p256_fp_sub» + 1) + («p256_fp_add» + 1) + («u256_eq» + 1)

/-- `p256_verify` (AST line 22022), log2 ≈ 387. -/
def «p256_verify» : Nat := («u256_is_zero» + 1) + («u256_lt» + 1) + («u256_is_zero» + 1) + («u256_lt» + 1) + («u256_lt» + 1) + («u256_lt» + 1) + («p256_on_curve» + 1) + («u256_from_be» + 1) + («u256_lt» + 1) + Nat.max ((«u256_sub» + 1)) (0) + («modinv_bin» + 1) + («u256_mulmod» + 1) + («u256_mulmod» + 1) + («heap_mark» + 1) + («alloc» + 1) + («p256_ec_mul2» + 1) + («u256_is_zero» + 1) + Nat.max ((«heap_release» + 1)) (0) + («p256_fp_sqr» + 1) + («heap_release» + 1) + («p256_fp_mul» + 1) + («u256_eq» + 1) + («u256_add_carry» + 1) + («u256_lt» + 1) + («p256_fp_mul» + 1) + («u256_eq» + 1)

/-- `pre_p256verify` (AST line 22115), log2 ≈ 387. -/
def «pre_p256verify» : Nat := («charge_gas» + 1) + («alloc» + 1) + («u256_from_be» + 1) + («u256_from_be» + 1) + («u256_from_be» + 1) + («u256_from_be» + 1) + («p256_verify» + 1) + Nat.max ((«alloc» + 1) + («memzero» + 1)) (0)

/-- `rmd_f` (AST line 19800), log2 ≈ 0. -/
def «rmd_f» : Nat := 0

/-- `rmd_k` (AST line 19826), log2 ≈ 0. -/
def «rmd_k» : Nat := 0

/-- `rmd_kp` (AST line 19852), log2 ≈ 0. -/
def «rmd_kp» : Nat := 0

/-- `ripemd160_block` (AST line 19878), log2 ≈ 67. -/
def «ripemd160_block» : Nat := (2 ^ 64 + 1) * (0 + 1) + (2 ^ 64 + 1) * ((«rmd_f» + 1) + («rmd_k» + 1) + («rmd_f» + 1) + («rmd_kp» + 1) + 1)

/-- `ripemd160` (AST line 19955), log2 ≈ 102. -/
def «ripemd160» : Nat := ((domainBytes + 1) + 1) * ((«ripemd160_block» + 1) + 1) + («memzero» + 1) + («memcpy» + 1) + («st_le64» + 1) + («ripemd160_block» + 1) + Nat.max ((«ripemd160_block» + 1)) (0) + (2 ^ 64 + 1) * ((«st_le32» + 1) + 1)

/-- `pre_ripemd160` (AST line 31608), log2 ≈ 102. -/
def «pre_ripemd160» : Nat := («words_of» + 1) + («charge_gas» + 1) + («alloc» + 1) + («memzero» + 1) + («ripemd160» + 1)

/-- `pre_sha256` (AST line 31534), log2 ≈ 67. -/
def «pre_sha256» : Nat := («words_of» + 1) + («charge_gas» + 1) + («alloc» + 1) + («sha256» + 1)

/-- `run_precompile` (AST line 31795), log2 ≈ 453. -/
def «run_precompile» : Nat := Nat.max ((«pre_ecrecover» + 1)) (0) + Nat.max ((«pre_sha256» + 1)) (0) + Nat.max ((«pre_ripemd160» + 1)) (0) + Nat.max ((«pre_identity» + 1)) (0) + Nat.max ((«pre_alt_bn128_add» + 1)) (0) + Nat.max ((«pre_alt_bn128_mul» + 1)) (0) + Nat.max ((«pre_alt_bn128_pairing_check» + 1)) (0) + Nat.max ((«pre_modexp» + 1)) (0) + Nat.max ((«pre_blake2f» + 1)) (0) + Nat.max ((«pre_kzg_point_evaluation» + 1)) (0) + Nat.max ((«pre_bls_g1_add» + 1)) (0) + Nat.max ((«pre_bls_g1_msm» + 1)) (0) + Nat.max ((«pre_bls_g2_add» + 1)) (0) + Nat.max ((«pre_bls_g2_msm» + 1)) (0) + Nat.max ((«pre_bls_pairing» + 1)) (0) + Nat.max ((«pre_bls_map_fp_to_g1» + 1)) (0) + Nat.max ((«pre_bls_map_fp2_to_g2» + 1)) (0) + Nat.max ((«pre_p256verify» + 1)) (0)

/-- `frame_prologue` (AST line 18499), log2 ≈ 453. -/
def «frame_prologue» : Nat := Nat.max ((«u256_is_zero» + 1) + Nat.max ((«move_ether» + 1) + («memeq» + 1) + Nat.max ((«emit_transfer_log» + 1)) (0)) (0)) (0) + Nat.max ((«precompile_index» + 1) + Nat.max (Nat.max ((«run_precompile» + 1)) (0)) (0)) (0)

/-- `frame_start` (AST line 18539), log2 ≈ 453. -/
def «frame_start» : Nat := («frame_prologue» + 1) + («frame_exception» + 1)

/-- `credit_state_gas_refund` (AST line 15000), log2 ≈ 1. -/
def «credit_state_gas_refund» : Nat := («min» + 1)

/-- `incorporate_child_on_error` (AST line 18941), log2 ≈ 0. -/
def «incorporate_child_on_error» : Nat := 0

/-- `incorporate_child_on_success` (AST line 18957), log2 ≈ 194. -/
def «incorporate_child_on_success» : Nat := («incorporate_child_on_error» + 1) + (2 ^ 64 + 1) * ((«log_append» + 1) + 1) + («htab_union_into» + 1)

/-- `pc_add` (AST line 15437), log2 ≈ 0. -/
def «pc_add» : Nat := 0

/-- `htab_truncate` (AST line 5278), log2 ≈ 131. -/
def «htab_truncate» : Nat := (2 ^ 64 + 1) * ((«htab_del» + 1) + 1)

/-- `rollback_child_access` (AST line 18995), log2 ≈ 132. -/
def «rollback_child_access» : Nat := («htab_truncate» + 1) + («htab_truncate» + 1)

/-- `set_retdata` (AST line 19064), log2 ≈ 65. -/
def «set_retdata» : Nat := Nat.max ((«alloc» + 1)) (0) + («memcpy» + 1)

/-- `stack_push` (AST line 15065), log2 ≈ 65. -/
def «stack_push» : Nat := Nat.max ((«scratch_alloc» + 1) + («memcpy» + 1)) (0)

/-- `state_restore` (AST line 12903), log2 ≈ 194. -/
def «state_restore» : Nat := (2 ^ 64 + 1) * (Nat.max ((«htab_set» + 1)) ((«htab_del» + 1)) + 1)

/-- `finish_child` (AST line 18572), log2 ≈ 450. -/
def «finish_child» : Nat := Nat.max (Nat.max ((«create_finish» + 1) + («state_restore» + 1) + («refill_frame_state_gas» + 1) + («frame_halt» + 1)) ((«state_restore» + 1))) (0) + Nat.max (Nat.max ((«rollback_child_access» + 1) + («incorporate_child_on_error» + 1) + Nat.max ((«credit_state_gas_refund» + 1)) (0) + («set_retdata» + 1) + («stack_push» + 1)) ((«incorporate_child_on_success» + 1) + («set_retdata» + 1) + («address_to_u256» + 1) + («stack_push» + 1))) (Nat.max ((«rollback_child_access» + 1) + («incorporate_child_on_error» + 1) + Nat.max ((«credit_state_gas_refund» + 1)) (0) + («set_retdata» + 1) + («stack_push» + 1)) ((«incorporate_child_on_success» + 1) + («set_retdata» + 1) + («stack_push» + 1)) + («min» + 1) + Nat.max ((«memcpy» + 1)) (0)) + («scratch_release» + 1) + («frame_mem_release» + 1) + («pc_add» + 1)

/-- `frame_epilogue` (AST line 18558), log2 ≈ 194. -/
def «frame_epilogue» : Nat := Nat.max ((«state_restore» + 1)) (0)

/-- `stack_pop` (AST line 15046), log2 ≈ 0. -/
def «stack_pop» : Nat := 0

/-- `op_add` (AST line 15525), log2 ≈ 65. -/
def «op_add» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («u256_add» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `u256_addmod` (AST line 1861), log2 ≈ 258. -/
def «u256_addmod» : Nat := («u256_add_carry» + 1) + Nat.max ((«u256_mod» + 1)) (0) + («u256_to_digits» + 1) + («digits_divmod» + 1)

/-- `op_addmod` (AST line 15658), log2 ≈ 258. -/
def «op_addmod» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («u256_addmod» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_address` (AST line 16734), log2 ≈ 66. -/
def «op_address» : Nat := («charge_gas» + 1) + («address_to_u256» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_and` (AST line 15851), log2 ≈ 65. -/
def «op_and» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `to_address_masked` (AST line 14889), log2 ≈ 4. -/
def «to_address_masked» : Nat := («st_be32» + 1) + («st_be64» + 1) + («st_be64» + 1)

/-- `warm_after_charge` (AST line 15511), log2 ≈ 130. -/
def «warm_after_charge» : Nat := Nat.max ((«warm_address» + 1)) (0)

/-- `op_balance` (AST line 16751), log2 ≈ 450. -/
def «op_balance» : Nat := («stack_pop» + 1) + («to_address_masked» + 1) + («access_gas_cost» + 1) + («charge_gas» + 1) + («warm_after_charge» + 1) + («get_account» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `block_env` (AST line 17115), log2 ≈ 0. -/
def «block_env» : Nat := 0

/-- `op_basefee` (AST line 17125), log2 ≈ 65. -/
def «op_basefee» : Nat := («charge_gas» + 1) + («block_env» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `u256_div` (AST line 1783), log2 ≈ 257. -/
def «u256_div» : Nat := («u256_divmod» + 1)

/-- `u256_from_word` (AST line 780), log2 ≈ 0. -/
def «u256_from_word» : Nat := 0

/-- `u256_mul` (AST line 1150), log2 ≈ 3. -/
def «u256_mul» : Nat := Nat.max ((«mul64x64» + 1)) (0) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1)

/-- `taylor_exponential` (AST line 9511), log2 ≈ 321. -/
def «taylor_exponential» : Nat := («u256_from_word» + 1) + («u256_from_word» + 1) + («u256_from_word» + 1) + («u256_mul» + 1) + («u256_is_zero» + 1) + ((2 ^ 64 + 1) + 1) * ((«u256_add» + 1) + («u256_mul_full» + 1) + Nat.max ((«trap_with» + 1)) (0) + («u256_from_word» + 1) + («u256_mul» + 1) + («u256_div» + 1) + («u256_is_zero» + 1) + 1) + («u256_div» + 1)

/-- `calculate_blob_gas_price` (AST line 9550), log2 ≈ 321. -/
def «calculate_blob_gas_price» : Nat := («taylor_exponential» + 1)

/-- `op_blobbasefee` (AST line 17165), log2 ≈ 321. -/
def «op_blobbasefee» : Nat := («charge_gas» + 1) + («block_env» + 1) + («calculate_blob_gas_price» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_blobhash` (AST line 17142), log2 ≈ 66. -/
def «op_blobhash» : Nat := («stack_pop» + 1) + («charge_gas» + 1) + («sat_word» + 1) + Nat.max ((«u256_from_be» + 1) + («stack_push» + 1)) ((«stack_push» + 1)) + («pc_add» + 1)

/-- `track_ancestor_access` (AST line 13771), log2 ≈ 0. -/
def «track_ancestor_access» : Nat := 0

/-- `op_blockhash` (AST line 17183), log2 ≈ 66. -/
def «op_blockhash» : Nat := («stack_pop» + 1) + («charge_gas» + 1) + («block_env» + 1) + («sat_word» + 1) + Nat.max ((«stack_push» + 1) + («pc_add» + 1)) (0) + («u256_from_be» + 1) + («track_ancestor_access» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `stack_push_word` (AST line 15103), log2 ≈ 65. -/
def «stack_push_word» : Nat := («stack_push» + 1)

/-- `u256_byte` (AST line 2197), log2 ≈ 1. -/
def «u256_byte» : Nat := («u256_limb» + 1)

/-- `op_byte` (AST line 15922), log2 ≈ 65. -/
def «op_byte» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («sat_word» + 1) + («u256_byte» + 1) + («stack_push_word» + 1) + («pc_add» + 1)

/-- `calculate_delegation_cost` (AST line 17693), log2 ≈ 450. -/
def «calculate_delegation_cost» : Nat := («ext_code_of» + 1) + («is_valid_delegation» + 1) + («alloc» + 1) + («memcpy» + 1) + («is_warm_address» + 1)

/-- `calculate_message_call_gas` (AST line 19328), log2 ≈ 3. -/
def «calculate_message_call_gas» : Nat := («u256_is_zero» + 1) + («add_sat» + 1) + Nat.max ((«add_sat» + 1) + («add_sat» + 1)) (0)

/-- `extend_memory` (AST line 15206), log2 ≈ 66. -/
def «extend_memory» : Nat := Nat.max ((«frame_mem_alloc» + 1) + («memzero» + 1)) (0) + («memzero» + 1)

/-- `memory_gas_cost` (AST line 15129), log2 ≈ 3. -/
def «memory_gas_cost» : Nat := («words_of» + 1) + («mul64x64» + 1) + («add_sat» + 1)

/-- `extend_memory_cost1` (AST line 15146), log2 ≈ 5. -/
def «extend_memory_cost1» : Nat := («u256_is_zero» + 1) + («sat_word» + 1) + («sat_word» + 1) + («add_sat» + 1) + («ceil32» + 1) + («ceil32» + 1) + («memory_gas_cost» + 1) + («memory_gas_cost» + 1)

/-- `extend_memory_cost2` (AST line 15181), log2 ≈ 6. -/
def «extend_memory_cost2» : Nat := («extend_memory_cost1» + 1) + («extend_memory_cost1» + 1)

/-- `msg_new_scratch` (AST line 15357), log2 ≈ 65. -/
def «msg_new_scratch» : Nat := («scratch_alloc» + 1) + («memzero» + 1)

/-- `child_message` (AST line 19009), log2 ≈ 65. -/
def «child_message» : Nat := («msg_new_scratch» + 1)

/-- `state_snapshot` (AST line 12893), log2 ≈ 0. -/
def «state_snapshot» : Nat := 0

/-- `start_child` (AST line 18703), log2 ≈ 453. -/
def «start_child» : Nat := Nat.max ((«state_snapshot» + 1) + («destroy_storage» + 1) + («mark_account_created» + 1) + («increment_nonce» + 1)) (0) + («frame_open» + 1) + («state_snapshot» + 1) + («frame_start» + 1)

/-- `generic_call` (AST line 19294), log2 ≈ 453. -/
def «generic_call» : Nat := («set_retdata» + 1) + Nat.max (Nat.max ((«credit_state_gas_refund» + 1)) (0) + («stack_push» + 1)) (0) + («scratch_mark» + 1) + («frame_mem_mark» + 1) + («child_message» + 1) + («start_child» + 1)

/-- `op_call` (AST line 19358), log2 ≈ 454. -/
def «op_call» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («to_address_masked» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («u256_is_zero» + 1) + («extend_memory_cost2» + 1) + («is_warm_address» + 1) + («add_sat» + 1) + («charge_gas» + 1) + Nat.max ((«warm_address» + 1)) (0) + («calculate_delegation_cost» + 1) + Nat.max ((«charge_gas» + 1) + («warm_address» + 1)) (0) + («ext_code_of» + 1) + Nat.max ((«is_account_alive» + 1) + Nat.max ((«charge_state_gas» + 1)) (0)) (0) + («sat_word» + 1) + («calculate_message_call_gas» + 1) + («charge_gas» + 1) + («extend_memory» + 1) + («get_account» + 1) + («u256_lt» + 1) + Nat.max ((«stack_push» + 1) + («set_retdata» + 1) + Nat.max ((«credit_state_gas_refund» + 1)) (0)) ((«sat_word» + 1) + («sat_word» + 1) + («sat_word» + 1) + («sat_word» + 1) + («generic_call» + 1)) + Nat.max ((«pc_add» + 1)) (0)

/-- `op_callcode` (AST line 19457), log2 ≈ 454. -/
def «op_callcode» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («to_address_masked» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («extend_memory_cost2» + 1) + («is_warm_address» + 1) + («u256_is_zero» + 1) + («add_sat» + 1) + («charge_gas» + 1) + Nat.max ((«warm_address» + 1)) (0) + («calculate_delegation_cost» + 1) + Nat.max ((«charge_gas» + 1) + («warm_address» + 1)) (0) + («ext_code_of» + 1) + («sat_word» + 1) + («calculate_message_call_gas» + 1) + («charge_gas» + 1) + («extend_memory» + 1) + («get_account» + 1) + («u256_lt» + 1) + Nat.max ((«stack_push» + 1) + («set_retdata» + 1)) ((«sat_word» + 1) + («sat_word» + 1) + («sat_word» + 1) + («sat_word» + 1) + («generic_call» + 1)) + Nat.max ((«pc_add» + 1)) (0)

/-- `copy_from_buffer` (AST line 16866), log2 ≈ 67. -/
def «copy_from_buffer» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («sat_word» + 1) + («words_of» + 1) + («extend_memory_cost1» + 1) + («add_sat» + 1) + («charge_gas» + 1) + («extend_memory» + 1) + Nat.max ((«sat_word» + 1) + («sat_word» + 1) + («buffer_read» + 1)) (0) + («pc_add» + 1)

/-- `op_calldatacopy` (AST line 16895), log2 ≈ 67. -/
def «op_calldatacopy» : Nat := («copy_from_buffer» + 1)

/-- `op_calldataload` (AST line 16824), log2 ≈ 67. -/
def «op_calldataload» : Nat := («stack_pop» + 1) + («charge_gas» + 1) + («sat_word» + 1) + («heap_mark» + 1) + («alloc» + 1) + («buffer_read» + 1) + («u256_from_be» + 1) + («heap_release» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_calldatasize` (AST line 16850), log2 ≈ 65. -/
def «op_calldatasize» : Nat := («charge_gas» + 1) + («stack_push_word» + 1) + («pc_add» + 1)

/-- `op_caller` (AST line 16791), log2 ≈ 66. -/
def «op_caller» : Nat := («charge_gas» + 1) + («address_to_u256» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_callvalue` (AST line 16808), log2 ≈ 65. -/
def «op_callvalue» : Nat := («charge_gas» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_chainid` (AST line 17289), log2 ≈ 65. -/
def «op_chainid» : Nat := («charge_gas» + 1) + («block_env» + 1) + («stack_push_word» + 1) + («pc_add» + 1)

/-- `op_clz` (AST line 16002), log2 ≈ 65. -/
def «op_clz» : Nat := («stack_pop» + 1) + («charge_gas» + 1) + («u256_bit_length» + 1) + («stack_push_word» + 1) + («pc_add» + 1)

/-- `op_codecopy` (AST line 16924), log2 ≈ 67. -/
def «op_codecopy» : Nat := («copy_from_buffer» + 1)

/-- `op_codesize` (AST line 16908), log2 ≈ 65. -/
def «op_codesize» : Nat := («charge_gas» + 1) + («stack_push_word» + 1) + («pc_add» + 1)

/-- `op_coinbase` (AST line 17220), log2 ≈ 66. -/
def «op_coinbase» : Nat := («charge_gas» + 1) + («block_env» + 1) + («address_to_u256» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `compute_contract_address` (AST line 19098), log2 ≈ 131. -/
def «compute_contract_address» : Nat := («heap_mark» + 1) + («alloc» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_word» + 1) + («rlp_list_header_len» + 1) + («rlp_encode_list_header» + 1) + («alloc» + 1) + («keccak256» + 1) + («memcpy» + 1) + («heap_release» + 1)

/-- `generic_create` (AST line 19156), log2 ≈ 454. -/
def «generic_create» : Nat := («set_retdata» + 1) + («get_account» + 1) + («u256_lt» + 1) + Nat.max ((«stack_push» + 1)) (0) + («warm_address» + 1) + («is_account_alive» + 1) + Nat.max ((«charge_state_gas» + 1)) (0) + («account_deployable» + 1) + Nat.max ((«increment_nonce» + 1) + Nat.max ((«credit_state_gas_refund» + 1)) (0) + («stack_push» + 1)) (0) + («increment_nonce» + 1) + («scratch_mark» + 1) + («frame_mem_mark» + 1) + («child_message» + 1) + («start_child» + 1)

/-- `require_not_static` (AST line 15459), log2 ≈ 0. -/
def «require_not_static» : Nat := 0

/-- `op_create` (AST line 19223), log2 ≈ 454. -/
def «op_create» : Nat := («require_not_static» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («sat_word» + 1) + («extend_memory_cost1» + 1) + («words_of» + 1) + («add_sat» + 1) + («charge_gas» + 1) + («extend_memory» + 1) + («get_account» + 1) + («alloc» + 1) + («compute_contract_address» + 1) + («sat_word» + 1) + («generic_create» + 1) + Nat.max ((«pc_add» + 1)) (0)

/-- `compute_create2_contract_address` (AST line 19129), log2 ≈ 101. -/
def «compute_create2_contract_address» : Nat := («heap_mark» + 1) + («alloc» + 1) + («memcpy» + 1) + («memcpy» + 1) + («keccak256» + 1) + («alloc» + 1) + («keccak256» + 1) + («memcpy» + 1) + («heap_release» + 1)

/-- `op_create2` (AST line 19257), log2 ≈ 454. -/
def «op_create2» : Nat := («require_not_static» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («sat_word» + 1) + («extend_memory_cost1» + 1) + («words_of» + 1) + («add_sat» + 1) + («charge_gas» + 1) + («alloc» + 1) + («u256_to_be32» + 1) + («extend_memory» + 1) + («sat_word» + 1) + («alloc» + 1) + («compute_create2_contract_address» + 1) + («generic_create» + 1) + Nat.max ((«pc_add» + 1)) (0)

/-- `op_delegatecall` (AST line 19539), log2 ≈ 454. -/
def «op_delegatecall» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («to_address_masked» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («extend_memory_cost2» + 1) + («is_warm_address» + 1) + («add_sat» + 1) + («charge_gas» + 1) + Nat.max ((«warm_address» + 1)) (0) + («calculate_delegation_cost» + 1) + Nat.max ((«charge_gas» + 1) + («warm_address» + 1)) (0) + («ext_code_of» + 1) + («sat_word» + 1) + («calculate_message_call_gas» + 1) + («charge_gas» + 1) + («extend_memory» + 1) + («sat_word» + 1) + («sat_word» + 1) + («sat_word» + 1) + («sat_word» + 1) + («generic_call» + 1) + Nat.max ((«pc_add» + 1)) (0)

/-- `op_div` (AST line 15582), log2 ≈ 257. -/
def «op_div» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («u256_div» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_dup` (AST line 16308), log2 ≈ 65. -/
def «op_dup» : Nat := («charge_gas» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `code_imm` (AST line 16370), log2 ≈ 0. -/
def «code_imm» : Nat := 0

/-- `decode_single` (AST line 16385), log2 ≈ 0. -/
def «decode_single» : Nat := 0

/-- `op_dupn` (AST line 16401), log2 ≈ 65. -/
def «op_dupn» : Nat := («charge_gas» + 1) + («code_imm» + 1) + («decode_single» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `stack_push_bool` (AST line 15115), log2 ≈ 65. -/
def «stack_push_bool» : Nat := («stack_push» + 1)

/-- `op_eq` (AST line 15814), log2 ≈ 65. -/
def «op_eq» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («u256_eq» + 1) + («stack_push_bool» + 1) + («pc_add» + 1)

/-- `stack_swap_positions` (AST line 16330), log2 ≈ 0. -/
def «stack_swap_positions» : Nat := 0

/-- `op_exchange` (AST line 16447), log2 ≈ 3. -/
def «op_exchange» : Nat := («charge_gas» + 1) + («code_imm» + 1) + («max» + 1) + («stack_swap_positions» + 1) + («pc_add» + 1)

/-- `u256_exp` (AST line 2002), log2 ≈ 69. -/
def «u256_exp» : Nat := («u256_bit_length» + 1) + (2 ^ 64 + 1) * ((«u256_bit» + 1) + Nat.max ((«u256_mul» + 1)) (0) + Nat.max ((«u256_mul» + 1)) (0) + 1)

/-- `op_exp` (AST line 15698), log2 ≈ 69. -/
def «op_exp» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («u256_byte_length» + 1) + («charge_gas» + 1) + («u256_exp» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_extcodecopy` (AST line 16987), log2 ≈ 450. -/
def «op_extcodecopy» : Nat := («stack_pop» + 1) + («to_address_masked» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («sat_word» + 1) + («words_of» + 1) + («extend_memory_cost1» + 1) + («access_gas_cost» + 1) + («add_sat» + 1) + («charge_gas» + 1) + («warm_after_charge» + 1) + («extend_memory» + 1) + («ext_code_of» + 1) + Nat.max ((«sat_word» + 1) + («sat_word» + 1) + («buffer_read» + 1)) (0) + («pc_add» + 1)

/-- `op_extcodehash` (AST line 17072), log2 ≈ 450. -/
def «op_extcodehash» : Nat := («stack_pop» + 1) + («to_address_masked» + 1) + («access_gas_cost» + 1) + («charge_gas» + 1) + («warm_after_charge» + 1) + («get_account» + 1) + («acct_is_empty» + 1) + Nat.max ((«stack_push» + 1)) ((«u256_from_be» + 1) + («stack_push» + 1)) + («pc_add» + 1)

/-- `op_extcodesize` (AST line 16965), log2 ≈ 450. -/
def «op_extcodesize» : Nat := («stack_pop» + 1) + («to_address_masked» + 1) + («access_gas_cost» + 1) + («charge_gas» + 1) + («warm_after_charge» + 1) + («ext_code_of» + 1) + («stack_push_word» + 1) + («pc_add» + 1)

/-- `op_gas` (AST line 16130), log2 ≈ 65. -/
def «op_gas» : Nat := («charge_gas» + 1) + («stack_push_word» + 1) + («pc_add» + 1)

/-- `op_gaslimit` (AST line 17272), log2 ≈ 65. -/
def «op_gaslimit» : Nat := («charge_gas» + 1) + («block_env» + 1) + («stack_push_word» + 1) + («pc_add» + 1)

/-- `op_gasprice` (AST line 16936), log2 ≈ 65. -/
def «op_gasprice» : Nat := («charge_gas» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_gt` (AST line 15757), log2 ≈ 65. -/
def «op_gt» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («u256_gt» + 1) + («stack_push_bool» + 1) + («pc_add» + 1)

/-- `op_iszero` (AST line 15833), log2 ≈ 65. -/
def «op_iszero» : Nat := («stack_pop» + 1) + («charge_gas» + 1) + («u256_is_zero» + 1) + («stack_push_bool» + 1) + («pc_add» + 1)

/-- `is_valid_jumpdest` (AST line 15324), log2 ≈ 0. -/
def «is_valid_jumpdest» : Nat := 0

/-- `op_jump` (AST line 16066), log2 ≈ 2. -/
def «op_jump» : Nat := («stack_pop» + 1) + («charge_gas» + 1) + («is_valid_jumpdest» + 1)

/-- `op_jumpdest` (AST line 16146), log2 ≈ 2. -/
def «op_jumpdest» : Nat := («charge_gas» + 1) + («pc_add» + 1)

/-- `op_jumpi` (AST line 16086), log2 ≈ 3. -/
def «op_jumpi» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («u256_is_zero» + 1) + Nat.max ((«pc_add» + 1)) (0) + («is_valid_jumpdest» + 1)

/-- `op_keccak` (AST line 16020), log2 ≈ 100. -/
def «op_keccak» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («sat_word» + 1) + («words_of» + 1) + («extend_memory_cost1» + 1) + («add_sat» + 1) + («charge_gas» + 1) + («extend_memory» + 1) + («heap_mark» + 1) + («alloc» + 1) + («sat_word» + 1) + («keccak256» + 1) + («u256_from_be» + 1) + («heap_release» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_log` (AST line 16499), log2 ≈ 69. -/
def «op_log» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («sat_word» + 1) + («extend_memory_cost1» + 1) + («mul64x64» + 1) + («add_sat» + 1) + Nat.max (0) ((«add_sat» + 1)) + («charge_gas» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«stack_pop» + 1) + («u256_to_be32» + 1) + 1) + («extend_memory» + 1) + («require_not_static» + 1) + («alloc» + 1) + («alloc» + 1) + («memcpy» + 1) + («alloc» + 1) + («sat_word» + 1) + («memcpy» + 1) + («log_append» + 1) + («pc_add» + 1)

/-- `op_lt` (AST line 15738), log2 ≈ 65. -/
def «op_lt» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («u256_lt» + 1) + («stack_push_bool» + 1) + («pc_add» + 1)

/-- `op_mcopy` (AST line 16233), log2 ≈ 67. -/
def «op_mcopy» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («sat_word» + 1) + («words_of» + 1) + («extend_memory_cost2» + 1) + («add_sat» + 1) + («charge_gas» + 1) + («extend_memory» + 1) + Nat.max ((«sat_word» + 1) + («sat_word» + 1) + («heap_mark» + 1) + («alloc» + 1) + («memcpy» + 1) + («memcpy» + 1) + («heap_release» + 1)) (0) + («pc_add» + 1)

/-- `charge_with_memory` (AST line 15240), log2 ≈ 66. -/
def «charge_with_memory» : Nat := («extend_memory_cost1» + 1) + («add_sat» + 1) + («charge_gas» + 1) + («extend_memory» + 1)

/-- `op_mload` (AST line 16198), log2 ≈ 67. -/
def «op_mload» : Nat := («stack_pop» + 1) + («charge_with_memory» + 1) + («sat_word» + 1) + («u256_from_be» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_mod` (AST line 15620), log2 ≈ 257. -/
def «op_mod» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («u256_mod» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_msize` (AST line 16217), log2 ≈ 65. -/
def «op_msize» : Nat := («charge_gas» + 1) + («stack_push_word» + 1) + («pc_add» + 1)

/-- `op_mstore` (AST line 16160), log2 ≈ 66. -/
def «op_mstore» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_with_memory» + 1) + («sat_word» + 1) + («u256_to_be32» + 1) + («pc_add» + 1)

/-- `op_mstore8` (AST line 16179), log2 ≈ 66. -/
def «op_mstore8» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_with_memory» + 1) + («sat_word» + 1) + («pc_add» + 1)

/-- `op_mul` (AST line 15544), log2 ≈ 65. -/
def «op_mul» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («u256_mul» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_mulmod` (AST line 15678), log2 ≈ 258. -/
def «op_mulmod» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («u256_mulmod» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_not` (AST line 15905), log2 ≈ 65. -/
def «op_not» : Nat := («stack_pop» + 1) + («charge_gas» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_number` (AST line 17255), log2 ≈ 65. -/
def «op_number» : Nat := («charge_gas» + 1) + («block_env» + 1) + («stack_push_word» + 1) + («pc_add» + 1)

/-- `op_or` (AST line 15869), log2 ≈ 65. -/
def «op_or» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_origin` (AST line 16773), log2 ≈ 66. -/
def «op_origin» : Nat := («charge_gas» + 1) + («address_to_u256» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_pc` (AST line 16114), log2 ≈ 65. -/
def «op_pc» : Nat := («charge_gas» + 1) + («stack_push_word» + 1) + («pc_add» + 1)

/-- `op_pop` (AST line 16268), log2 ≈ 2. -/
def «op_pop» : Nat := («stack_pop» + 1) + («charge_gas» + 1) + («pc_add» + 1)

/-- `op_prevrandao` (AST line 17306), log2 ≈ 66. -/
def «op_prevrandao» : Nat := («charge_gas» + 1) + («block_env» + 1) + («u256_from_be» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_push` (AST line 16283), log2 ≈ 67. -/
def «op_push» : Nat := («charge_gas» + 1) + («heap_mark» + 1) + («alloc» + 1) + («buffer_read» + 1) + («u256_from_be» + 1) + («heap_release» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_return` (AST line 17501), log2 ≈ 66. -/
def «op_return» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («extend_memory_cost1» + 1) + («charge_gas» + 1) + («extend_memory» + 1) + («sat_word» + 1) + («sat_word» + 1)

/-- `op_returndatacopy` (AST line 17038), log2 ≈ 66. -/
def «op_returndatacopy» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («sat_word» + 1) + («words_of» + 1) + («extend_memory_cost1» + 1) + («add_sat» + 1) + («charge_gas» + 1) + («sat_word» + 1) + («add_sat» + 1) + («extend_memory» + 1) + Nat.max ((«sat_word» + 1) + («memcpy» + 1)) (0) + («pc_add» + 1)

/-- `op_returndatasize` (AST line 17022), log2 ≈ 65. -/
def «op_returndatasize» : Nat := («charge_gas» + 1) + («stack_push_word» + 1) + («pc_add» + 1)

/-- `op_revert` (AST line 17526), log2 ≈ 66. -/
def «op_revert» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («extend_memory_cost1» + 1) + («charge_gas» + 1) + («extend_memory» + 1) + («sat_word» + 1) + («sat_word» + 1)

/-- `u256_or` (AST line 1019), log2 ≈ 0. -/
def «u256_or» : Nat := 0

/-- `u256_shl` (AST line 2028), log2 ≈ 0. -/
def «u256_shl» : Nat := 0

/-- `u256_shr` (AST line 2088), log2 ≈ 0. -/
def «u256_shr» : Nat := 0

/-- `u256_sar` (AST line 2148), log2 ≈ 2. -/
def «u256_sar» : Nat := («u256_shr» + 1) + Nat.max (Nat.max ((«u256_shl» + 1) + («u256_or» + 1)) (0)) (0)

/-- `op_sar` (AST line 15982), log2 ≈ 65. -/
def «op_sar» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («sat_word» + 1) + («u256_sar» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `u256_neg` (AST line 1105), log2 ≈ 0. -/
def «u256_neg» : Nat := 0

/-- `u256_abs` (AST line 1805), log2 ≈ 1. -/
def «u256_abs» : Nat := Nat.max ((«u256_neg» + 1)) (0)

/-- `u256_sdiv` (AST line 1819), log2 ≈ 257. -/
def «u256_sdiv» : Nat := («u256_abs» + 1) + («u256_abs» + 1) + («u256_div» + 1) + Nat.max ((«u256_neg» + 1)) (0)

/-- `op_sdiv` (AST line 15601), log2 ≈ 257. -/
def «op_sdiv» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («u256_sdiv» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_selfbalance` (AST line 17098), log2 ≈ 450. -/
def «op_selfbalance» : Nat := («charge_gas» + 1) + («get_account» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_selfdestruct` (AST line 17551), log2 ≈ 452. -/
def «op_selfdestruct» : Nat := («require_not_static» + 1) + («stack_pop» + 1) + («to_address_masked» + 1) + («is_warm_address» + 1) + («charge_gas» + 1) + Nat.max ((«warm_address» + 1)) (0) + («is_account_alive» + 1) + («get_account» + 1) + («u256_is_zero» + 1) + («charge_gas» + 1) + («charge_state_gas» + 1) + («get_account» + 1) + («move_ether» + 1) + («memeq» + 1) + Nat.max ((«emit_transfer_log» + 1)) (0) + («htab_has» + 1) + Nat.max ((«htab_set» + 1)) (0)

/-- `u256_slt` (AST line 931), log2 ≈ 0. -/
def «u256_slt» : Nat := 0

/-- `u256_sgt` (AST line 969), log2 ≈ 1. -/
def «u256_sgt» : Nat := («u256_slt» + 1)

/-- `op_sgt` (AST line 15795), log2 ≈ 65. -/
def «op_sgt» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («u256_sgt» + 1) + («stack_push_bool» + 1) + («pc_add» + 1)

/-- `op_shl` (AST line 15942), log2 ≈ 65. -/
def «op_shl» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («sat_word» + 1) + («u256_shl» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_shr` (AST line 15962), log2 ≈ 65. -/
def «op_shr» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («sat_word» + 1) + («u256_shr» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `u256_and` (AST line 1009), log2 ≈ 0. -/
def «u256_and» : Nat := 0

/-- `u256_not` (AST line 999), log2 ≈ 0. -/
def «u256_not» : Nat := 0

/-- `u256_signextend` (AST line 2175), log2 ≈ 3. -/
def «u256_signextend» : Nat := («u256_bit» + 1) + («u256_shl» + 1) + Nat.max ((«u256_or» + 1)) (0) + («u256_not» + 1) + («u256_and» + 1)

/-- `op_signextend` (AST line 15718), log2 ≈ 65. -/
def «op_signextend» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («sat_word» + 1) + («u256_signextend» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `get_storage` (AST line 13249), log2 ≈ 517. -/
def «get_storage» : Nat := («sk_make» + 1) + («htab_set» + 1) + («stor_lookup» + 1) + («stor_lookup» + 1) + («record_pre_state_read» + 1) + («ws_get_storage» + 1)

/-- `is_warm_storage_key` (AST line 16559), log2 ≈ 67. -/
def «is_warm_storage_key» : Nat := («sk_make» + 1) + («htab_has» + 1)

/-- `warm_storage_key` (AST line 16571), log2 ≈ 130. -/
def «warm_storage_key» : Nat := («sk_make» + 1) + («htab_set» + 1)

/-- `op_sload` (AST line 16584), log2 ≈ 517. -/
def «op_sload» : Nat := («stack_pop» + 1) + («u256_to_be32» + 1) + («is_warm_storage_key» + 1) + Nat.max ((«charge_gas» + 1)) ((«charge_gas» + 1) + («warm_storage_key» + 1)) + («get_storage» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_slotnum` (AST line 17324), log2 ≈ 65. -/
def «op_slotnum» : Nat := («charge_gas» + 1) + («block_env» + 1) + («stack_push_word» + 1) + («pc_add» + 1)

/-- `op_slt` (AST line 15776), log2 ≈ 65. -/
def «op_slt» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («u256_slt» + 1) + («stack_push_bool» + 1) + («pc_add» + 1)

/-- `u256_smod` (AST line 1840), log2 ≈ 257. -/
def «u256_smod» : Nat := («u256_abs» + 1) + («u256_abs» + 1) + («u256_mod» + 1) + Nat.max ((«u256_neg» + 1)) (0)

/-- `op_smod` (AST line 15639), log2 ≈ 257. -/
def «op_smod» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («u256_smod» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `check_gas` (AST line 14935), log2 ≈ 0. -/
def «check_gas» : Nat := 0

/-- `get_storage_original` (AST line 13276), log2 ≈ 517. -/
def «get_storage_original» : Nat := («htab_has» + 1) + («stor_lookup» + 1) + («record_pre_state_read» + 1) + («ws_get_storage» + 1)

/-- `set_storage` (AST line 13451), log2 ≈ 450. -/
def «set_storage» : Nat := («get_account_optional» + 1) + («htab_get» + 1) + Nat.max ((«htab_new» + 1) + («jset» + 1)) (0) + («alloc» + 1) + («jset» + 1)

/-- `op_sstore` (AST line 16611), log2 ≈ 518. -/
def «op_sstore» : Nat := («require_not_static» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («u256_to_be32» + 1) + («is_warm_storage_key» + 1) + («max» + 1) + («check_gas» + 1) + («charge_gas» + 1) + Nat.max ((«warm_storage_key» + 1)) (0) + («get_storage_original» + 1) + («get_storage» + 1) + («u256_eq» + 1) + («u256_eq» + 1) + («u256_eq» + 1) + («u256_is_zero» + 1) + («u256_is_zero» + 1) + («u256_is_zero» + 1) + Nat.max ((«credit_state_gas_refund» + 1)) (0) + («charge_gas» + 1) + («charge_state_gas» + 1) + («set_storage» + 1) + («pc_add» + 1)

/-- `op_staticcall` (AST line 19600), log2 ≈ 454. -/
def «op_staticcall» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («to_address_masked» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («extend_memory_cost2» + 1) + («is_warm_address» + 1) + («add_sat» + 1) + («charge_gas» + 1) + Nat.max ((«warm_address» + 1)) (0) + («calculate_delegation_cost» + 1) + Nat.max ((«charge_gas» + 1) + («warm_address» + 1)) (0) + («ext_code_of» + 1) + («sat_word» + 1) + («calculate_message_call_gas» + 1) + («charge_gas» + 1) + («extend_memory» + 1) + («sat_word» + 1) + («sat_word» + 1) + («sat_word» + 1) + («sat_word» + 1) + («generic_call» + 1) + Nat.max ((«pc_add» + 1)) (0)

/-- `op_stop` (AST line 16052), log2 ≈ 1. -/
def «op_stop» : Nat := («pc_add» + 1)

/-- `op_sub` (AST line 15563), log2 ≈ 65. -/
def «op_sub» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («u256_sub» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_swap` (AST line 16350), log2 ≈ 2. -/
def «op_swap» : Nat := («charge_gas» + 1) + («stack_swap_positions» + 1) + («pc_add» + 1)

/-- `op_swapn` (AST line 16425), log2 ≈ 3. -/
def «op_swapn» : Nat := («charge_gas» + 1) + («code_imm» + 1) + («decode_single» + 1) + («stack_swap_positions» + 1) + («pc_add» + 1)

/-- `op_timestamp` (AST line 17238), log2 ≈ 65. -/
def «op_timestamp» : Nat := («charge_gas» + 1) + («block_env» + 1) + («stack_push_word» + 1) + («pc_add» + 1)

/-- `get_transient_storage` (AST line 13299), log2 ≈ 67. -/
def «get_transient_storage» : Nat := («sk_make» + 1) + («htab_get» + 1)

/-- `op_tload` (AST line 16688), log2 ≈ 68. -/
def «op_tload» : Nat := («stack_pop» + 1) + («charge_gas» + 1) + («u256_to_be32» + 1) + («get_transient_storage» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `set_transient_storage` (AST line 13574), log2 ≈ 130. -/
def «set_transient_storage» : Nat := («sk_make» + 1) + («u256_is_zero» + 1) + Nat.max ((«jdel» + 1)) (0) + («alloc» + 1) + («jset» + 1)

/-- `op_tstore` (AST line 16710), log2 ≈ 130. -/
def «op_tstore» : Nat := («require_not_static» + 1) + («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («u256_to_be32» + 1) + («set_transient_storage» + 1) + («pc_add» + 1)

/-- `op_xor` (AST line 15887), log2 ≈ 65. -/
def «op_xor» : Nat := («stack_pop» + 1) + («stack_pop» + 1) + («charge_gas» + 1) + («stack_push» + 1) + («pc_add» + 1)

/-- `op_dispatch` (AST line 17902), log2 ≈ 519. -/
def «op_dispatch» : Nat := Nat.max (Nat.max (Nat.max ((«op_stop» + 1)) (0) + Nat.max ((«op_add» + 1)) (0) + Nat.max ((«op_mul» + 1)) (0) + Nat.max ((«op_sub» + 1)) (0) + Nat.max ((«op_div» + 1)) (0) + Nat.max ((«op_sdiv» + 1)) (0) + Nat.max ((«op_mod» + 1)) (0) + Nat.max ((«op_smod» + 1)) (0) + Nat.max ((«op_addmod» + 1)) (0) + Nat.max ((«op_mulmod» + 1)) (0) + Nat.max ((«op_exp» + 1)) (0) + Nat.max ((«op_signextend» + 1)) (0)) (Nat.max ((«op_lt» + 1)) (0) + Nat.max ((«op_gt» + 1)) (0) + Nat.max ((«op_slt» + 1)) (0) + Nat.max ((«op_sgt» + 1)) (0) + Nat.max ((«op_eq» + 1)) (0) + Nat.max ((«op_iszero» + 1)) (0) + Nat.max ((«op_and» + 1)) (0) + Nat.max ((«op_or» + 1)) (0) + Nat.max ((«op_xor» + 1)) (0) + Nat.max ((«op_not» + 1)) (0) + Nat.max ((«op_byte» + 1)) (0) + Nat.max ((«op_shl» + 1)) (0) + Nat.max ((«op_shr» + 1)) (0) + Nat.max ((«op_sar» + 1)) (0) + Nat.max ((«op_clz» + 1)) (0))) (0) + Nat.max (Nat.max (Nat.max ((«op_keccak» + 1)) (0) + Nat.max ((«op_address» + 1)) (0) + Nat.max ((«op_balance» + 1)) (0) + Nat.max ((«op_origin» + 1)) (0) + Nat.max ((«op_caller» + 1)) (0) + Nat.max ((«op_callvalue» + 1)) (0) + Nat.max ((«op_calldataload» + 1)) (0) + Nat.max ((«op_calldatasize» + 1)) (0) + Nat.max ((«op_calldatacopy» + 1)) (0) + Nat.max ((«op_codesize» + 1)) (0) + Nat.max ((«op_codecopy» + 1)) (0) + Nat.max ((«op_gasprice» + 1)) (0) + Nat.max ((«op_extcodesize» + 1)) (0) + Nat.max ((«op_extcodecopy» + 1)) (0) + Nat.max ((«op_returndatasize» + 1)) (0) + Nat.max ((«op_returndatacopy» + 1)) (0) + Nat.max ((«op_extcodehash» + 1)) (0)) (Nat.max ((«op_blockhash» + 1)) (0) + Nat.max ((«op_coinbase» + 1)) (0) + Nat.max ((«op_timestamp» + 1)) (0) + Nat.max ((«op_number» + 1)) (0) + Nat.max ((«op_prevrandao» + 1)) (0) + Nat.max ((«op_gaslimit» + 1)) (0) + Nat.max ((«op_chainid» + 1)) (0) + Nat.max ((«op_selfbalance» + 1)) (0) + Nat.max ((«op_basefee» + 1)) (0) + Nat.max ((«op_blobhash» + 1)) (0) + Nat.max ((«op_blobbasefee» + 1)) (0) + Nat.max ((«op_slotnum» + 1)) (0) + Nat.max ((«op_pop» + 1)) (0) + Nat.max ((«op_mload» + 1)) (0) + Nat.max ((«op_mstore» + 1)) (0) + Nat.max ((«op_mstore8» + 1)) (0) + Nat.max ((«op_sload» + 1)) (0) + Nat.max ((«op_sstore» + 1)) (0) + Nat.max ((«op_jump» + 1)) (0) + Nat.max ((«op_jumpi» + 1)) (0) + Nat.max ((«op_pc» + 1)) (0) + Nat.max ((«op_msize» + 1)) (0) + Nat.max ((«op_gas» + 1)) (0) + Nat.max ((«op_jumpdest» + 1)) (0) + Nat.max ((«op_tload» + 1)) (0) + Nat.max ((«op_tstore» + 1)) (0) + Nat.max ((«op_mcopy» + 1)) (0) + Nat.max ((«op_push» + 1)) (0))) (0) + Nat.max (Nat.max ((«op_push» + 1)) (0) + Nat.max ((«op_dup» + 1)) (0) + («op_swap» + 1)) (0) + Nat.max ((«op_log» + 1)) (0) + Nat.max ((«op_dupn» + 1)) (0) + Nat.max ((«op_swapn» + 1)) (0) + Nat.max ((«op_exchange» + 1)) (0) + Nat.max ((«op_create» + 1)) (0) + Nat.max ((«op_call» + 1)) (0) + Nat.max ((«op_callcode» + 1)) (0) + Nat.max ((«op_return» + 1)) (0) + Nat.max ((«op_delegatecall» + 1)) (0) + Nat.max ((«op_create2» + 1)) (0) + Nat.max ((«op_staticcall» + 1)) (0) + Nat.max ((«op_revert» + 1)) (0) + Nat.max ((«op_selfdestruct» + 1)) (0)

/-- `run_frames` (AST line 18663), log2 ≈ 691. -/
def «run_frames» : Nat := (evmPotMax + 1) * (Nat.max (0) (Nat.max (0) (Nat.max (0) ((«op_dispatch» + 1) + («frame_exception» + 1)))) + Nat.max ((«frame_epilogue» + 1) + Nat.max (0) ((«finish_child» + 1) + («frame_exception» + 1))) (0) + 1)

/-- `process_message` (AST line 18803), log2 ≈ 691. -/
def «process_message» : Nat := («frame_open» + 1) + Nat.max ((«state_snapshot» + 1) + («depth0_prepare» + 1) + Nat.max ((«scratch_release» + 1) + («frame_mem_release» + 1)) (0) + («state_restore» + 1) + («refill_frame_state_gas» + 1) + («frame_halt» + 1)) (0) + («state_snapshot» + 1) + («frame_start» + 1) + («run_frames» + 1)

/-- `process_create_message` (AST line 18899), log2 ≈ 691. -/
def «process_create_message» : Nat := («state_snapshot» + 1) + («destroy_storage» + 1) + («mark_account_created» + 1) + («increment_nonce» + 1) + («process_message» + 1) + Nat.max ((«create_finish» + 1) + («state_restore» + 1) + («refill_frame_state_gas» + 1) + («frame_halt» + 1)) (0) + («state_restore» + 1)

/-- `process_message_call` (AST line 19661), log2 ≈ 691. -/
def «process_message_call» : Nat := («alloc» + 1) + («memzero» + 1) + Nat.max ((«account_deployable» + 1) + («process_create_message» + 1)) ((«process_message» + 1)) + («frame_state_gas_used» + 1)

/-- `state_fresh_tx` (AST line 12778), log2 ≈ 7. -/
def «state_fresh_tx» : Nat := («alloc» + 1) + («htab_new» + 1) + («htab_new» + 1) + («htab_new» + 1) + («htab_new» + 1) + («htab_new» + 1) + («htab_new» + 1) + («htab_new» + 1) + («htab_new» + 1)

/-- `te_new` (AST line 32838), log2 ≈ 65. -/
def «te_new» : Nat := («alloc» + 1) + («memzero» + 1)

/-- `process_unchecked_system_transaction` (AST line 32851), log2 ≈ 691. -/
def «process_unchecked_system_transaction» : Nat := («state_fresh_tx» + 1) + («ext_code_of» + 1) + («te_new» + 1) + («msg_new» + 1) + («htab_new» + 1) + («htab_new» + 1) + («process_message_call» + 1) + («incorporate_tx_into_block» + 1) + Nat.max (Nat.max ((«alloc» + 1) + («memcpy» + 1)) (0) + («scratch_release» + 1) + («frame_mem_release» + 1)) (0)

/-- `process_checked_system_transaction` (AST line 32928), log2 ≈ 691. -/
def «process_checked_system_transaction» : Nat := («state_fresh_tx» + 1) + («ext_code_of» + 1) + («alloc» + 1) + («process_unchecked_system_transaction» + 1)

/-- `requests_append` (AST line 33485), log2 ≈ 65. -/
def «requests_append» : Nat := («alloc» + 1) + («memcpy» + 1)

/-- `process_general_purpose_requests` (AST line 33507), log2 ≈ 693. -/
def «process_general_purpose_requests» : Nat := («alloc» + 1) + (2 ^ 64 + 1) * ((2 ^ 64 + 1) * ((«memeq» + 1) + Nat.max (Nat.max ((«memeq» + 1) + Nat.max (Nat.max ((«alloc» + 1) + («memcpy» + 1)) (0) + («extract_deposit_data» + 1)) (0)) (0)) (0) + 1) + 1) + Nat.max ((«requests_append» + 1)) (0) + («process_checked_system_transaction» + 1) + Nat.max ((«requests_append» + 1)) (0) + («process_checked_system_transaction» + 1) + Nat.max ((«requests_append» + 1)) (0) + («process_checked_system_transaction» + 1) + Nat.max ((«requests_append» + 1)) (0) + («process_checked_system_transaction» + 1) + Nat.max ((«requests_append» + 1)) (0)

/-- `calculate_total_blob_gas` (AST line 11914), log2 ≈ 0. -/
def «calculate_total_blob_gas» : Nat := 0

/-- `fee_mul` (AST line 32778), log2 ≈ 5. -/
def «fee_mul» : Nat := («u256_mul_full» + 1)

/-- `check_transaction` (AST line 32951), log2 ≈ 450. -/
def «check_transaction» : Nat := («min» + 1) + («calculate_total_blob_gas» + 1) + («get_account» + 1) + Nat.max ((«u256_lt» + 1)) ((«u256_lt» + 1) + («u256_lt» + 1) + («u256_sub» + 1) + («u256_lt» + 1) + («u256_add» + 1)) + («fee_mul» + 1) + Nat.max ((2 ^ 64 + 1) * (0 + 1) + («calculate_blob_gas_price» + 1) + («u256_lt» + 1) + («fee_mul» + 1) + («u256_add_carry» + 1)) (0) + («u256_fits_word» + 1) + («u256_add_carry» + 1) + («u256_lt» + 1) + («get_code» + 1) + («memeq» + 1) + Nat.max ((«is_valid_delegation» + 1)) (0)

/-- `clear_account_preserving_balance` (AST line 13541), log2 ≈ 450. -/
def «clear_account_preserving_balance» : Nat := («destroy_storage» + 1) + («get_account» + 1) + («acct_copy» + 1) + («modify_state_commit» + 1)

/-- `create_ether` (AST line 13629), log2 ≈ 450. -/
def «create_ether» : Nat := («get_account» + 1) + («acct_copy» + 1) + («u256_add» + 1) + («modify_state_commit» + 1)

/-- `rlp_finish_list` (AST line 31969), log2 ≈ 130. -/
def «rlp_finish_list» : Nat := («rlp_list_header_len» + 1) + («memcpy» + 1) + («rlp_encode_list_header» + 1)

/-- `encode_logs` (AST line 32005), log2 ≈ 257. -/
def «encode_logs» : Nat := (2 ^ 64 + 1) * ((«rlp_encode_bytes» + 1) + (2 ^ 64 + 1) * ((«rlp_encode_bytes» + 1) + 1) + («rlp_finish_list» + 1) + («rlp_encode_bytes» + 1) + («rlp_finish_list» + 1) + 1) + («rlp_finish_list» + 1)

/-- `logs_encoded_bound` (AST line 31985), log2 ≈ 65. -/
def «logs_encoded_bound» : Nat := (2 ^ 64 + 1) * (0 + 1)

/-- `encode_receipt` (AST line 32051), log2 ≈ 257. -/
def «encode_receipt» : Nat := («logs_encoded_bound» + 1) + («alloc» + 1) + («rlp_encode_word» + 1) + («alloc» + 1) + («logs_bloom» + 1) + («rlp_encode_bytes» + 1) + («encode_logs» + 1) + («rlp_finish_list» + 1)

/-- `rlp_word_encoded_len` (AST line 4852), log2 ≈ 129. -/
def «rlp_word_encoded_len» : Nat := («rlp_be_len» + 1)

/-- `tx_u256_encoded_len` (AST line 11940), log2 ≈ 3. -/
def «tx_u256_encoded_len» : Nat := («u256_byte_length» + 1)

/-- `auth_payload_len` (AST line 12060), log2 ≈ 130. -/
def «auth_payload_len» : Nat := («tx_u256_encoded_len» + 1) + («rlp_word_encoded_len» + 1) + («rlp_word_encoded_len» + 1) + («tx_u256_encoded_len» + 1) + («tx_u256_encoded_len» + 1)

/-- `auth_list_payload_len` (AST line 12075), log2 ≈ 194. -/
def «auth_list_payload_len» : Nat := (2 ^ 64 + 1) * ((«auth_payload_len» + 1) + («rlp_list_header_len» + 1) + 1)

/-- `tx_encode_bound` (AST line 12141), log2 ≈ 195. -/
def «tx_encode_bound» : Nat := («access_list_payload_len» + 1) + («auth_list_payload_len» + 1)

/-- `tx_put_access_list` (AST line 11998), log2 ≈ 257. -/
def «tx_put_access_list» : Nat := («access_list_payload_len» + 1) + («rlp_encode_list_header» + 1) + (2 ^ 64 + 1) * ((«rlp_list_header_len» + 1) + («rlp_encode_list_header» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_list_header» + 1) + (2 ^ 64 + 1) * ((«rlp_encode_bytes» + 1) + 1) + 1)

/-- `tx_put_u256` (AST line 11924), log2 ≈ 129. -/
def «tx_put_u256» : Nat := («heap_mark» + 1) + («alloc» + 1) + («u256_to_be_min» + 1) + («rlp_encode_bytes» + 1) + («heap_release» + 1)

/-- `tx_put_authorizations` (AST line 12094), log2 ≈ 196. -/
def «tx_put_authorizations» : Nat := («auth_list_payload_len» + 1) + («rlp_encode_list_header» + 1) + (2 ^ 64 + 1) * ((«auth_payload_len» + 1) + («rlp_encode_list_header» + 1) + («tx_put_u256» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_word» + 1) + («rlp_encode_word» + 1) + («tx_put_u256» + 1) + («tx_put_u256» + 1) + 1)

/-- `tx_put_blob_hashes` (AST line 12040), log2 ≈ 193. -/
def «tx_put_blob_hashes» : Nat := («rlp_encode_list_header» + 1) + (2 ^ 64 + 1) * ((«rlp_encode_bytes» + 1) + 1)

/-- `tx_put_to` (AST line 11961), log2 ≈ 129. -/
def «tx_put_to» : Nat := («rlp_encode_bytes» + 1)

/-- `tx_encode_generic` (AST line 12154), log2 ≈ 257. -/
def «tx_encode_generic» : Nat := («tx_encode_bound» + 1) + («alloc» + 1) + Nat.max ((«rlp_encode_word» + 1)) (0) + («tx_put_u256» + 1) + Nat.max ((«tx_put_u256» + 1)) ((«tx_put_u256» + 1) + («tx_put_u256» + 1)) + («rlp_encode_word» + 1) + («tx_put_to» + 1) + («tx_put_u256» + 1) + («rlp_encode_bytes» + 1) + Nat.max ((«tx_put_access_list» + 1)) (0) + Nat.max ((«tx_put_u256» + 1) + («tx_put_blob_hashes» + 1)) (0) + Nat.max ((«tx_put_authorizations» + 1)) (0) + Nat.max ((«tx_put_u256» + 1) + («tx_put_u256» + 1) + («tx_put_u256» + 1)) (0) + Nat.max ((«rlp_encode_word» + 1)) (0) + («rlp_list_header_len» + 1) + («rlp_encode_list_header» + 1)

/-- `encode_transaction` (AST line 12267), log2 ≈ 257. -/
def «encode_transaction» : Nat := («tx_encode_generic» + 1)

/-- `tx_signing_hash_mode` (AST line 12289), log2 ≈ 257. -/
def «tx_signing_hash_mode» : Nat := («heap_mark» + 1) + («tx_encode_generic» + 1) + («keccak256» + 1) + («heap_release» + 1)

/-- `signing_hash_155` (AST line 12315), log2 ≈ 257. -/
def «signing_hash_155» : Nat := («tx_signing_hash_mode» + 1)

/-- `signing_hash_1559` (AST line 12335), log2 ≈ 257. -/
def «signing_hash_1559» : Nat := («tx_signing_hash_mode» + 1)

/-- `signing_hash_2930` (AST line 12325), log2 ≈ 257. -/
def «signing_hash_2930» : Nat := («tx_signing_hash_mode» + 1)

/-- `signing_hash_4844` (AST line 12345), log2 ≈ 257. -/
def «signing_hash_4844» : Nat := («tx_signing_hash_mode» + 1)

/-- `signing_hash_7702` (AST line 12355), log2 ≈ 257. -/
def «signing_hash_7702» : Nat := («tx_signing_hash_mode» + 1)

/-- `signing_hash_pre155` (AST line 12305), log2 ≈ 257. -/
def «signing_hash_pre155» : Nat := («tx_signing_hash_mode» + 1)

/-- `signature_recovery_parameters` (AST line 12399), log2 ≈ 259. -/
def «signature_recovery_parameters» : Nat := («u256_is_zero» + 1) + («u256_lt» + 1) + («u256_is_zero» + 1) + («u256_gt» + 1) + («u256_fits_word» + 1) + Nat.max (Nat.max (Nat.max ((«signing_hash_pre155» + 1)) (0)) (0) + («u256_add» + 1) + («u256_add» + 1) + («u256_add» + 1) + («u256_eq» + 1) + («u256_eq» + 1) + («signing_hash_155» + 1)) (0) + Nat.max ((«signing_hash_2930» + 1)) (0) + Nat.max ((«signing_hash_1559» + 1)) (0) + Nat.max ((«signing_hash_4844» + 1)) (0) + Nat.max ((«signing_hash_7702» + 1)) (0)

/-- `recover_transaction_public_key` (AST line 12483), log2 ≈ 389. -/
def «recover_transaction_public_key» : Nat := («heap_mark» + 1) + («alloc» + 1) + («signature_recovery_parameters» + 1) + («secp256k1_recover» + 1) + («heap_release» + 1)

/-- `sender_address_from_public_key` (AST line 12503), log2 ≈ 100. -/
def «sender_address_from_public_key» : Nat := («heap_mark» + 1) + («alloc» + 1) + («keccak256» + 1) + («memcpy» + 1) + («heap_release» + 1)

/-- `recover_sender_with_chain_id` (AST line 12542), log2 ≈ 389. -/
def «recover_sender_with_chain_id» : Nat := («heap_mark» + 1) + («alloc» + 1) + («recover_transaction_public_key» + 1) + («sender_address_from_public_key» + 1) + («heap_release» + 1)

/-- `set_account_balance` (AST line 13647), log2 ≈ 450. -/
def «set_account_balance» : Nat := («get_account» + 1) + («acct_copy» + 1) + («modify_state_commit» + 1)

/-- `tx_chain_id` (AST line 12365), log2 ≈ 3. -/
def «tx_chain_id» : Nat := («u256_fits_word» + 1) + («u256_sub» + 1) + («u256_shr» + 1) + («u256_fits_word» + 1)

/-- `tx_has_access_list` (AST line 11890), log2 ≈ 0. -/
def «tx_has_access_list» : Nat := 0

/-- `tx_is_blob` (AST line 32750), log2 ≈ 0. -/
def «tx_is_blob» : Nat := 0

/-- `tx_is_setcode` (AST line 32764), log2 ≈ 0. -/
def «tx_is_setcode» : Nat := 0

/-- `udiv_small5` (AST line 33447), log2 ≈ 65. -/
def «udiv_small5» : Nat := («udiv» + 1)

/-- `count_tokens_in_data` (AST line 12562), log2 ≈ 65. -/
def «count_tokens_in_data» : Nat := (2 ^ 64 + 1) * (0 + 1)

/-- `calculate_intrinsic_cost` (AST line 12581), log2 ≈ 67. -/
def «calculate_intrinsic_cost» : Nat := («count_tokens_in_data» + 1) + («u256_is_zero» + 1) + Nat.max (0) ((«memeq» + 1)) + Nat.max ((2 ^ 64 + 1) * (0 + 1)) (0)

/-- `validate_transaction` (AST line 12639), log2 ≈ 67. -/
def «validate_transaction» : Nat := («calculate_intrinsic_cost» + 1) + («u256_fits_word» + 1)

/-- `process_transaction` (AST line 33103), log2 ≈ 691. -/
def «process_transaction» : Nat := («state_fresh_tx» + 1) + («encode_transaction» + 1) + («tx_chain_id» + 1) + («alloc» + 1) + («recover_sender_with_chain_id» + 1) + («validate_transaction» + 1) + («check_transaction» + 1) + («calculate_total_blob_gas» + 1) + («get_account» + 1) + Nat.max ((«calculate_blob_gas_price» + 1) + («fee_mul» + 1)) (0) + («fee_mul» + 1) + («min» + 1) + («increment_nonce» + 1) + («u256_sub» + 1) + («u256_sub» + 1) + («set_account_balance» + 1) + («te_new» + 1) + («tx_has_access_list» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * (0 + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((2 ^ 64 + 1) * ((«memcpy» + 1) + («memcpy» + 1) + 1) + 1) + («tx_is_blob» + 1) + («tx_is_setcode» + 1) + («alloc» + 1) + («keccak256» + 1) + («msg_new» + 1) + («htab_new» + 1) + («htab_set» + 1) + (2 ^ 64 + 1) * ((«htab_set» + 1) + 1) + (2 ^ 64 + 1) * ((«htab_set» + 1) + 1) + («htab_new» + 1) + (2 ^ 64 + 1) * ((«htab_set» + 1) + 1) + («alloc» + 1) + Nat.max ((«get_account» + 1) + («alloc» + 1) + («compute_contract_address» + 1)) (0) + («htab_set» + 1) + («process_message_call» + 1) + («udiv_small5» + 1) + («min» + 1) + («max» + 1) + («fee_mul» + 1) + («u256_sub» + 1) + («fee_mul» + 1) + («create_ether» + 1) + («create_ether» + 1) + («max» + 1) + Nat.max ((«lst_new» + 1)) (0) + («encode_receipt» + 1) + (2 ^ 64 + 1) * ((«lst_push» + 1) + 1) + («lst_new» + 1) + (2 ^ 64 + 1) * (0 + 1) + («lst_push» + 1) + Nat.max ((2 ^ 64 + 1) * ((«htab_item» + 1) + Nat.max ((«clear_account_preserving_balance» + 1)) (0) + 1)) (0) + («incorporate_tx_into_block» + 1) + Nat.max ((«scratch_release» + 1) + («frame_mem_release» + 1)) (0)

/-- `process_withdrawals` (AST line 33458), log2 ≈ 645. -/
def «process_withdrawals» : Nat := («state_fresh_tx» + 1) + (2 ^ 64 + 1) * ((«u256_mul» + 1) + («create_ether» + 1) + 1) + («incorporate_tx_into_block» + 1)

/-- `validate_block_access_list_gas_limit` (AST line 14776), log2 ≈ 195. -/
def «validate_block_access_list_gas_limit» : Nat := (2 ^ 64 + 1) * ((«htab_item» + 1) + Nat.max ((2 ^ 64 + 1) * ((«htab_item» + 1) + Nat.max ((«htab_has» + 1)) (0) + 1)) (0) + 1) + («udiv» + 1)

/-- `execute_block` (AST line 33580), log2 ≈ 755. -/
def «execute_block» : Nat := («alloc» + 1) + («memzero» + 1) + («alloc» + 1) + («alloc» + 1) + («lst_new» + 1) + («alloc» + 1) + («lst_new» + 1) + («bal_init» + 1) + («process_unchecked_system_transaction» + 1) + («process_unchecked_system_transaction» + 1) + («state_fresh_tx» + 1) + («track_ancestor_access» + 1) + (2 ^ 64 + 1) * ((«decode_transaction» + 1) + («process_transaction» + 1) + 1) + («process_withdrawals» + 1) + («process_general_purpose_requests» + 1) + («build_block_access_list_rlp» + 1) + («validate_block_access_list_gas_limit» + 1) + («alloc» + 1) + («compute_state_root» + 1) + («alloc» + 1) + («build_mpt_indexed» + 1) + («alloc» + 1) + («build_mpt_indexed» + 1) + («alloc» + 1) + («logs_bloom» + 1) + («alloc» + 1) + («build_mpt_indexed» + 1) + («alloc» + 1) + («compute_requests_hash» + 1) + («alloc» + 1) + («keccak256» + 1) + («max» + 1) + («memeq» + 1) + («memeq» + 1) + («memeq» + 1) + («memeq» + 1) + («memeq» + 1) + («memeq» + 1) + («memeq» + 1)

/-- `encode_header` (AST line 9350), log2 ≈ 133. -/
def «encode_header» : Nat := («alloc» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_bytes» + 1) + («rlp_put_u256» + 1) + («rlp_encode_word» + 1) + («rlp_encode_word» + 1) + («rlp_encode_word» + 1) + («rlp_encode_word» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_bytes» + 1) + («rlp_put_u256» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_word» + 1) + («rlp_encode_word» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_bytes» + 1) + Nat.max ((«rlp_encode_bytes» + 1) + («rlp_encode_word» + 1)) (0) + («rlp_list_header_len» + 1) + («rlp_encode_list_header» + 1)

/-- `header_hash` (AST line 9460), log2 ≈ 133. -/
def «header_hash» : Nat := («heap_mark» + 1) + («encode_header» + 1) + («keccak256» + 1) + («heap_release» + 1)

/-- `is_valid_versioned_hashes` (AST line 32794), log2 ≈ 640. -/
def «is_valid_versioned_hashes» : Nat := (2 ^ 64 + 1) * ((«decode_transaction» + 1) + («tx_is_blob» + 1) + Nat.max ((2 ^ 64 + 1) * ((«memeq» + 1) + 1)) (0) + 1)

/-- `nodedb_build` (AST line 9937), log2 ≈ 194. -/
def «nodedb_build» : Nat := (2 ^ 64 + 1) * (0 + 1) + («htab_new» + 1) + (2 ^ 64 + 1) * ((«keccak256» + 1) + («htab_set» + 1) + 1)

/-- `withdrawal_rlp_len` (AST line 32099), log2 ≈ 131. -/
def «withdrawal_rlp_len» : Nat := («rlp_word_encoded_len» + 1) + («rlp_word_encoded_len» + 1) + («rlp_word_encoded_len» + 1) + («rlp_list_header_len» + 1)

/-- `block_rlp_length` (AST line 32586), log2 ≈ 195. -/
def «block_rlp_length» : Nat := («heap_mark» + 1) + («encode_header» + 1) + («heap_release» + 1) + (2 ^ 64 + 1) * (Nat.max ((«rlp_bytes_encoded_len» + 1)) (0) + 1) + («rlp_list_header_len» + 1) + (2 ^ 64 + 1) * ((«withdrawal_rlp_len» + 1) + 1) + («rlp_list_header_len» + 1) + («rlp_list_header_len» + 1)

/-- `encode_execution_requests` (AST line 32142), log2 ≈ 129. -/
def «encode_execution_requests» : Nat := («alloc» + 1) + (2 ^ 64 + 1) * (Nat.max ((«alloc» + 1) + («memcpy» + 1)) (0) + 1)

/-- `encode_withdrawal_rlp` (AST line 32114), log2 ≈ 131. -/
def «encode_withdrawal_rlp» : Nat := («alloc» + 1) + («rlp_encode_word» + 1) + («rlp_encode_word» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_word» + 1) + («rlp_finish_list» + 1)

/-- `payload_header` (AST line 32645), log2 ≈ 262. -/
def «payload_header» : Nat := («alloc» + 1) + («memzero» + 1) + («alloc» + 1) + («alloc» + 1) + («keccak256» + 1) + («alloc» + 1) + («alloc» + 1) + («memzero» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («block_rlp_length» + 1) + («build_mpt_indexed» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«encode_withdrawal_rlp» + 1) + 1) + («build_mpt_indexed» + 1) + («encode_execution_requests» + 1) + («compute_requests_hash» + 1) + («keccak256» + 1)

/-- `state_init` (AST line 12708), log2 ≈ 517. -/
def «state_init» : Nat := («alloc» + 1) + («decode_witness_to_mpt» + 1) + («htab_new» + 1) + («alloc» + 1) + («htab_new» + 1) + («htab_new» + 1) + («htab_new» + 1) + («htab_new» + 1) + («htab_new» + 1) + («htab_new» + 1) + («htab_new» + 1) + («alloc» + 1) + («alloc» + 1)

/-- `calculate_base_fee_per_gas` (AST line 9613), log2 ≈ 259. -/
def «calculate_base_fee_per_gas» : Nat := («check_gas_limit» + 1) + («u256_from_word» + 1) + («u256_from_word» + 1) + Nat.max ((«u256_from_word» + 1) + («u256_mul» + 1) + («u256_div» + 1) + («u256_div» + 1) + («u256_is_zero» + 1) + Nat.max ((«u256_from_word» + 1)) (0) + («u256_add» + 1)) (0) + («u256_from_word» + 1) + («u256_mul» + 1) + («u256_div» + 1) + («u256_div» + 1) + («u256_sub» + 1)

/-- `calculate_excess_blob_gas` (AST line 9561), log2 ≈ 321. -/
def «calculate_excess_blob_gas» : Nat := («calculate_blob_gas_price» + 1) + («u256_from_word» + 1) + («u256_mul» + 1) + («u256_from_word» + 1) + («u256_mul» + 1) + («u256_gt» + 1) + Nat.max ((«udiv» + 1)) (0)

/-- `validate_header` (AST line 9675), log2 ≈ 321. -/
def «validate_header» : Nat := («calculate_excess_blob_gas» + 1) + («calculate_base_fee_per_gas» + 1) + («u256_eq» + 1) + («u256_is_zero» + 1) + («memeq» + 1) + («heap_mark» + 1) + («alloc» + 1) + («keccak256» + 1) + («memeq» + 1) + Nat.max ((«heap_release» + 1)) (0) + («header_hash» + 1) + («memeq» + 1) + («heap_release» + 1)

/-- `hdr_bytes_field` (AST line 9168), log2 ≈ 448. -/
def «hdr_bytes_field» : Nat := («rlp_item» + 1)

/-- `hdr_raw_field` (AST line 9187), log2 ≈ 448. -/
def «hdr_raw_field» : Nat := («rlp_item» + 1)

/-- `hdr_uint_field` (AST line 9103), log2 ≈ 448. -/
def «hdr_uint_field» : Nat := («rlp_item» + 1)

/-- `hdr_u256_field` (AST line 9152), log2 ≈ 448. -/
def «hdr_u256_field» : Nat := («hdr_uint_field» + 1) + («u256_from_be» + 1)

/-- `hdr_word_field` (AST line 9130), log2 ≈ 448. -/
def «hdr_word_field» : Nat := («hdr_uint_field» + 1) + (2 ^ 64 + 1) * (0 + 1)

/-- `decode_header` (AST line 9202), log2 ≈ 452. -/
def «decode_header» : Nat := («rlp_decode_fully» + 1) + («rlp_list_to_slices» + 1) + («alloc» + 1) + («hdr_bytes_field» + 1) + («hdr_bytes_field» + 1) + («hdr_bytes_field» + 1) + («hdr_bytes_field» + 1) + («hdr_bytes_field» + 1) + («hdr_bytes_field» + 1) + («hdr_bytes_field» + 1) + («hdr_u256_field» + 1) + («hdr_word_field» + 1) + («hdr_word_field» + 1) + («hdr_word_field» + 1) + («hdr_uint_field» + 1) + («hdr_word_field» + 1) + («hdr_raw_field» + 1) + («hdr_bytes_field» + 1) + («hdr_bytes_field» + 1) + («hdr_u256_field» + 1) + («hdr_bytes_field» + 1) + («hdr_uint_field» + 1) + («hdr_word_field» + 1) + («hdr_uint_field» + 1) + («hdr_word_field» + 1) + («hdr_bytes_field» + 1) + («hdr_bytes_field» + 1) + Nat.max ((«hdr_bytes_field» + 1) + («hdr_uint_field» + 1) + («hdr_word_field» + 1)) (0)

/-- `validate_headers` (AST line 9476), log2 ≈ 516. -/
def «validate_headers» : Nat := («alloc» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«decode_header» + 1) + («keccak256» + 1) + 1) + (2 ^ 64 + 1) * ((«memeq» + 1) + 1)

/-- `run_attempt` (AST line 33734), log2 ≈ 755. -/
def «run_attempt» : Nat := («validate_headers» + 1) + («check_gas_limit» + 1) + («nodedb_build» + 1) + («nodedb_build» + 1) + («state_init» + 1) + (2 ^ 64 + 1) * (0 + 1) + («payload_header» + 1) + («alloc» + 1) + («header_hash» + 1) + («memeq» + 1) + («is_valid_versioned_hashes» + 1) + («validate_header» + 1) + («alloc» + 1) + («memzero» + 1) + («execute_block» + 1)

/-- `attempt_l1` (AST line 33847), log2 ≈ 755. -/
def «attempt_l1» : Nat := («run_attempt» + 1)

/-- `attempt_l2` (AST line 33863), log2 ≈ 755. -/
def «attempt_l2» : Nat := («attempt_l1» + 1)

/-- `attempt_l3` (AST line 33879), log2 ≈ 755. -/
def «attempt_l3» : Nat := («attempt_l2» + 1)

/-- `attempt_l4` (AST line 33895), log2 ≈ 755. -/
def «attempt_l4» : Nat := («attempt_l3» + 1)

/-- `attempt_l5` (AST line 33911), log2 ≈ 755. -/
def «attempt_l5» : Nat := («attempt_l4» + 1)

/-- `attempt_l6` (AST line 33927), log2 ≈ 755. -/
def «attempt_l6» : Nat := («attempt_l5» + 1)

/-- `attempt_l7` (AST line 33943), log2 ≈ 755. -/
def «attempt_l7» : Nat := («attempt_l6» + 1)

/-- `blake2_init` (AST line 20017), log2 ≈ 4. -/
def «blake2_init» : Nat := («alloc» + 1) + («alloc» + 1) + («alloc» + 1)

/-- `bls_consts_init` (AST line 24793), log2 ≈ 2. -/
def «bls_consts_init» : Nat := («alloc» + 1)

/-- `bls_lib_init` (AST line 30328), log2 ≈ 3. -/
def «bls_lib_init» : Nat := («bls_consts_init» + 1)

/-- `bls_precompiles_init` (AST line 30678), log2 ≈ 4. -/
def «bls_precompiles_init» : Nat := («bls_lib_init» + 1) + («alloc» + 1)

/-- `ceil_log2` (AST line 749), log2 ≈ 65. -/
def «ceil_log2» : Nat := (2 ^ 64 + 1) * (0 + 1)

/-- `ssz_fail` (AST line 8285), log2 ≈ 0. -/
def «ssz_fail» : Nat := 0

/-- `ssz_split_var_list` (AST line 8447), log2 ≈ 66. -/
def «ssz_split_var_list» : Nat := Nat.max ((«ssz_fail» + 1)) (0) + Nat.max ((«ssz_fail» + 1)) (0) + Nat.max ((«ssz_fail» + 1)) (0) + («alloc» + 1) + (2 ^ 64 + 1) * (Nat.max ((«ssz_fail» + 1)) (0) + 1)

/-- `decode_bytes_list` (AST line 8637), log2 ≈ 67. -/
def «decode_bytes_list» : Nat := («ssz_split_var_list» + 1) + (2 ^ 64 + 1) * (Nat.max ((«ssz_fail» + 1)) (0) + 1)

/-- `ssz_check_offsets` (AST line 8414), log2 ≈ 66. -/
def «ssz_check_offsets» : Nat := (2 ^ 64 + 1) * (Nat.max ((«ssz_fail» + 1)) (0) + Nat.max (Nat.max ((«ssz_fail» + 1)) (0)) (0) + 1) + Nat.max ((«ssz_fail» + 1)) (0)

/-- `ssz_fixed_list_count` (AST line 8496), log2 ≈ 65. -/
def «ssz_fixed_list_count» : Nat := («udivmod» + 1) + Nat.max ((«ssz_fail» + 1)) (0) + Nat.max ((«ssz_fail» + 1)) (0)

/-- `decode_payload` (AST line 8515), log2 ≈ 67. -/
def «decode_payload» : Nat := Nat.max ((«ssz_fail» + 1)) (0) + («alloc» + 1) + («ssz_check_offsets» + 1) + Nat.max ((«ssz_fail» + 1)) (0) + («ssz_split_var_list» + 1) + («ssz_fixed_list_count» + 1)

/-- `decode_requests` (AST line 8584), log2 ≈ 68. -/
def «decode_requests» : Nat := Nat.max ((«ssz_fail» + 1)) (0) + (2 ^ 64 + 1) * (0 + 1) + («ssz_check_offsets» + 1) + («alloc» + 1) + («ssz_fixed_list_count» + 1) + («ssz_fixed_list_count» + 1) + («ssz_fixed_list_count» + 1) + («ssz_fixed_list_count» + 1) + («ssz_fixed_list_count» + 1)

/-- `decode_stateless_input` (AST line 8656), log2 ≈ 70. -/
def «decode_stateless_input» : Nat := Nat.max ((«ssz_fail» + 1)) (0) + Nat.max ((«ssz_fail» + 1)) (0) + Nat.max ((«ssz_fail» + 1)) (0) + («ssz_check_offsets» + 1) + («alloc» + 1) + Nat.max ((«ssz_fail» + 1)) (0) + («ssz_check_offsets» + 1) + («decode_payload» + 1) + («ssz_fixed_list_count» + 1) + («decode_requests» + 1) + Nat.max ((«ssz_fail» + 1)) (0) + (2 ^ 64 + 1) * (0 + 1) + («ssz_check_offsets» + 1) + («decode_bytes_list» + 1) + («decode_bytes_list» + 1) + («decode_bytes_list» + 1)

/-- `input_blob` (AST line 624), log2 ≈ 35. -/
def «input_blob» : Nat := Nat.max ((«trap_with» + 1)) (0) + («alloc» + 1) + ((domainBytes + 1) + 1) * (0 + 1)

/-- `host_input_byte` (AST line 8297), log2 ≈ 0. -/
def «host_input_byte» : Nat := 0

/-- `host_input_le32` (AST line 8310), log2 ≈ 3. -/
def «host_input_le32» : Nat := («host_input_byte» + 1) + («host_input_byte» + 1) + («host_input_byte» + 1) + («host_input_byte» + 1)

/-- `precheck_host_ssz_header` (AST line 8324), log2 ≈ 68. -/
def «precheck_host_ssz_header» : Nat := Nat.max ((«ssz_fail» + 1)) (0) + («host_input_byte» + 1) + («host_input_byte» + 1) + Nat.max ((«ssz_fail» + 1)) (0) + Nat.max ((«ssz_fail» + 1)) (0) + («host_input_le32» + 1) + («host_input_le32» + 1) + («ssz_check_offsets» + 1) + Nat.max ((«ssz_fail» + 1)) (0) + («host_input_le32» + 1) + («host_input_le32» + 1) + («host_input_le32» + 1) + («ssz_check_offsets» + 1) + Nat.max ((«ssz_fail» + 1)) (0) + («host_input_le32» + 1) + («host_input_le32» + 1) + («host_input_le32» + 1) + («host_input_le32» + 1) + («ssz_check_offsets» + 1)

/-- `decode_host_input` (AST line 8401), log2 ≈ 70. -/
def «decode_host_input» : Nat := («precheck_host_ssz_header» + 1) + («input_blob» + 1) + («decode_stateless_input» + 1)

/-- `evm_init` (AST line 17353), log2 ≈ 100. -/
def «evm_init» : Nat := («heap_mark» + 1) + («alloc» + 1) + («heap_release» + 1) + («alloc» + 1) + («keccak256» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * (0 + 1) + («alloc» + 1) + («memzero» + 1) + («alloc» + 1) + («memzero» + 1) + («alloc» + 1) + («alloc» + 1)

/-- `fork_init` (AST line 32522), log2 ≈ 66. -/
def «fork_init» : Nat := («alloc» + 1) + («memzero» + 1) + («alloc» + 1) + («memzero» + 1) + (2 ^ 64 + 1) * (0 + 1) + («alloc» + 1) + («addr_from_words» + 1) + («alloc» + 1) + («addr_from_words» + 1) + («alloc» + 1) + («addr_from_words» + 1) + («alloc» + 1) + («addr_from_words» + 1) + («alloc» + 1) + («addr_from_words» + 1) + («alloc» + 1) + («addr_from_words» + 1) + («alloc» + 1) + («addr_from_words» + 1) + («alloc» + 1) + («st_be64» + 1) + («st_be64» + 1) + («st_be64» + 1) + («st_be64» + 1)

/-- `header_init` (AST line 9657), log2 ≈ 65. -/
def «header_init» : Nat := («alloc» + 1) + («memzero» + 1)

/-- `sha256_pair` (AST line 2954), log2 ≈ 0. -/
def «sha256_pair» : Nat := 0

/-- `merkleize` (AST line 8052), log2 ≈ 72. -/
def «merkleize» : Nat := («ceil_log2» + 1) + («ceil_log2» + 1) + («max» + 1) + Nat.max ((«memcpy» + 1)) (0) + («heap_mark» + 1) + («alloc» + 1) + («memcpy» + 1) + («memzero» + 1) + (64 + 1) * ((2 ^ 64 + 1) * ((«sha256_pair» + 1) + 1) + 1) + (2 ^ 64 + 1) * ((«sha256_pair» + 1) + 1) + («memcpy» + 1) + («heap_release» + 1)

/-- `pack_bytes` (AST line 8213), log2 ≈ 66. -/
def «pack_bytes» : Nat := («alloc» + 1) + («memcpy» + 1) + («memzero» + 1)

/-- `htr_bytes_vector` (AST line 8229), log2 ≈ 72. -/
def «htr_bytes_vector» : Nat := Nat.max ((«memzero» + 1) + («memcpy» + 1)) (0) + («heap_mark» + 1) + («pack_bytes» + 1) + («merkleize» + 1) + («heap_release» + 1)

/-- `htr_u64_at` (AST line 8271), log2 ≈ 66. -/
def «htr_u64_at» : Nat := («memzero» + 1) + («memcpy» + 1)

/-- `htr_bdep` (AST line 8943), log2 ≈ 73. -/
def «htr_bdep» : Nat := («heap_mark» + 1) + («alloc» + 1) + («htr_bytes_vector» + 1) + («memcpy» + 1) + («htr_u64_at» + 1) + («htr_bytes_vector» + 1) + («merkleize» + 1) + («heap_release» + 1)

/-- `htr_bexit` (AST line 8967), log2 ≈ 73. -/
def «htr_bexit» : Nat := («heap_mark» + 1) + («alloc» + 1) + («htr_bytes_vector» + 1) + («htr_bytes_vector» + 1) + («merkleize» + 1) + («heap_release» + 1)

/-- `mix_in_length` (AST line 8099), log2 ≈ 65. -/
def «mix_in_length» : Nat := («memzero» + 1) + («st_le64» + 1) + («sha256_pair» + 1)

/-- `htr_bytes_list` (AST line 8253), log2 ≈ 72. -/
def «htr_bytes_list» : Nat := («heap_mark» + 1) + («pack_bytes» + 1) + («merkleize» + 1) + («heap_release» + 1) + («mix_in_length» + 1)

/-- `htr_cons` (AST line 8921), log2 ≈ 74. -/
def «htr_cons» : Nat := («heap_mark» + 1) + («alloc» + 1) + («htr_bytes_vector» + 1) + («htr_bytes_vector» + 1) + («htr_bytes_vector» + 1) + («merkleize» + 1) + («heap_release» + 1)

/-- `htr_deposit` (AST line 8873), log2 ≈ 73. -/
def «htr_deposit» : Nat := («heap_mark» + 1) + («alloc» + 1) + («htr_bytes_vector» + 1) + («memcpy» + 1) + («htr_u64_at» + 1) + («htr_bytes_vector» + 1) + («htr_u64_at» + 1) + («merkleize» + 1) + («heap_release» + 1)

/-- `merkleize_progressive` (AST line 8115), log2 ≈ 106. -/
def «merkleize_progressive» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + ((domainBytes + 64) + 1) * ((«merkleize» + 1) + 1) + («memzero» + 1) + (2 ^ 64 + 1) * ((«sha256_pair» + 1) + 1) + («memcpy» + 1) + («heap_release» + 1)

/-- `htr_plist_chunks` (AST line 8156), log2 ≈ 106. -/
def «htr_plist_chunks» : Nat := («merkleize_progressive» + 1) + («mix_in_length» + 1)

/-- `htr_pbytes` (AST line 8170), log2 ≈ 106. -/
def «htr_pbytes» : Nat := («heap_mark» + 1) + («pack_bytes» + 1) + («htr_plist_chunks» + 1) + («heap_release» + 1)

/-- `htr_pcontainer` (AST line 8186), log2 ≈ 106. -/
def «htr_pcontainer» : Nat := («heap_mark» + 1) + («alloc» + 1) + («merkleize_progressive» + 1) + («memzero» + 1) + (2 ^ 64 + 1) * (0 + 1) + («sha256_pair» + 1) + («heap_release» + 1)

/-- `htr_withdrawal` (AST line 8755), log2 ≈ 73. -/
def «htr_withdrawal» : Nat := («heap_mark» + 1) + («alloc» + 1) + («htr_u64_at» + 1) + («htr_u64_at» + 1) + («htr_bytes_vector» + 1) + («htr_u64_at» + 1) + («merkleize» + 1) + («heap_release» + 1)

/-- `htr_payload` (AST line 8793), log2 ≈ 170. -/
def «htr_payload» : Nat := («heap_mark» + 1) + («alloc» + 1) + («memcpy» + 1) + («htr_bytes_vector» + 1) + («memcpy» + 1) + («memcpy» + 1) + («htr_bytes_vector» + 1) + («memcpy» + 1) + («htr_u64_at» + 1) + («htr_u64_at» + 1) + («htr_u64_at» + 1) + («htr_u64_at» + 1) + («htr_bytes_list» + 1) + («memcpy» + 1) + («memcpy» + 1) + («heap_mark» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«htr_pbytes» + 1) + 1) + («htr_plist_chunks» + 1) + («heap_release» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«htr_withdrawal» + 1) + 1) + («htr_plist_chunks» + 1) + («heap_release» + 1) + («htr_u64_at» + 1) + («htr_u64_at» + 1) + («htr_pbytes» + 1) + («htr_u64_at» + 1) + («htr_pcontainer» + 1) + («heap_release» + 1)

/-- `htr_wdreq` (AST line 8899), log2 ≈ 73. -/
def «htr_wdreq» : Nat := («heap_mark» + 1) + («alloc» + 1) + («htr_bytes_vector» + 1) + («htr_bytes_vector» + 1) + («htr_u64_at» + 1) + («merkleize» + 1) + («heap_release» + 1)

/-- `htr_request_list` (AST line 8987), log2 ≈ 140. -/
def «htr_request_list» : Nat := («heap_mark» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * (Nat.max ((«htr_deposit» + 1)) (0) + Nat.max ((«htr_wdreq» + 1)) (0) + Nat.max ((«htr_cons» + 1)) (0) + Nat.max ((«htr_bdep» + 1)) (0) + Nat.max ((«htr_bexit» + 1)) (0) + 1) + («htr_plist_chunks» + 1) + («heap_release» + 1)

/-- `htr_requests` (AST line 9027), log2 ≈ 142. -/
def «htr_requests» : Nat := («heap_mark» + 1) + («alloc» + 1) + («htr_request_list» + 1) + («htr_request_list» + 1) + («htr_request_list» + 1) + («htr_request_list» + 1) + («htr_request_list» + 1) + («htr_pcontainer» + 1) + («heap_release» + 1)

/-- `htr_new_payload_request` (AST line 9053), log2 ≈ 170. -/
def «htr_new_payload_request» : Nat := («heap_mark» + 1) + («alloc» + 1) + («htr_payload» + 1) + («htr_plist_chunks» + 1) + («memcpy» + 1) + («htr_requests» + 1) + («merkleize» + 1) + («heap_release» + 1)

/-- `keccak_init` (AST line 3974), log2 ≈ 4. -/
def «keccak_init» : Nat := («alloc» + 1) + («alloc» + 1) + («alloc» + 1)

/-- `mem_init` (AST line 50), log2 ≈ 0. -/
def «mem_init» : Nat := 0

/-- `mpt_init` (AST line 9781), log2 ≈ 101. -/
def «mpt_init» : Nat := («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («keccak256» + 1) + («keccak256» + 1)

/-- `output_write` (AST line 651), log2 ≈ 65. -/
def «output_write» : Nat := (2 ^ 64 + 1) * (0 + 1)

/-- `ripemd160_init` (AST line 19738), log2 ≈ 4. -/
def «ripemd160_init» : Nat := («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1)

/-- `secp256k1_init` (AST line 5417), log2 ≈ 0. -/
def «secp256k1_init» : Nat := 0

/-- `serialize_result` (AST line 9077), log2 ≈ 65. -/
def «serialize_result» : Nat := («memcpy» + 1) + («st_le64» + 1)

/-- `sha256_init` (AST line 2327), log2 ≈ 3. -/
def «sha256_init» : Nat := («alloc» + 1) + («alloc» + 1)

/-- `ssz_init` (AST line 7520), log2 ≈ 4. -/
def «ssz_init» : Nat := («alloc» + 1) + («alloc» + 1) + («alloc» + 1)

/-- `u256_ws_init` (AST line 766), log2 ≈ 2. -/
def «u256_ws_init» : Nat := Nat.max ((«alloc» + 1)) (0)

/-- `verify_stateless_new_payload` (AST line 33959), log2 ≈ 755. -/
def «verify_stateless_new_payload» : Nat := («attempt_l7» + 1)

/-- `main` (AST line 33979), log2 ≈ 755. -/
def «main» : Nat := («mem_init» + 1) + («sha256_init» + 1) + («keccak_init» + 1) + («ssz_init» + 1) + («mpt_init» + 1) + («u256_ws_init» + 1) + («secp256k1_init» + 1) + («bn254_init» + 1) + («bls_precompiles_init» + 1) + («ripemd160_init» + 1) + («blake2_init» + 1) + («header_init» + 1) + («evm_init» + 1) + («fork_init» + 1) + («alloc» + 1) + («alloc» + 1) + («memzero» + 1) + («decode_host_input» + 1) + («serialize_result» + 1) + («output_write» + 1) + («alloc» + 1) + («htr_new_payload_request» + 1) + («verify_stateless_new_payload» + 1) + («serialize_result» + 1) + («output_write» + 1)

end K

/-! ### Unguarded leaves: every function on `main`'s call graph outside the guarded tier, bounded
for ARBITRARY memory and globals (guard `GuestInv`). The docstring lists each loop's class
(DESIGN.md §3). -/

/-- `trap_with` (AST line 26): loop-free. -/
theorem «fb_trap_with» : TerminatingFunBoundedOn GuestInv (ofString "trap_with") K.«trap_with» := by sorry
/-- `alloc` (AST line 66): loop-free. -/
theorem «fb_alloc» : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc» := by sorry
/-- `mpt_fail` (AST line 9769): loop-free. -/
theorem «fb_mpt_fail» : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail» := by sorry
/-- `memcpy` (AST line 198): #0 WALK; #1 WALK; #2 WALK; #3 CTR. -/
theorem «fb_memcpy» : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy» := by sorry
/-- `nibbles_concat` (AST line 9922): loop-free. -/
theorem «fb_nibbles_concat» : TerminatingFunBoundedOn GuestInv (ofString "nibbles_concat") K.«nibbles_concat» := by sorry
/-- `node_new_ext` (AST line 10021): loop-free. -/
theorem «fb_node_new_ext» : TerminatingFunBoundedOn GuestInv (ofString "node_new_ext") K.«node_new_ext» := by sorry
/-- `node_new_leaf` (AST line 9994): loop-free. -/
theorem «fb_node_new_leaf» : TerminatingFunBoundedOn GuestInv (ofString "node_new_leaf") K.«node_new_leaf» := by sorry
/-- `_collapse_branch` (AST line 10674): #0 CTR. -/
theorem «fb__collapse_branch» : TerminatingFunBoundedOn GuestInv (ofString "_collapse_branch") K.«_collapse_branch» := by sorry
/-- `memzero` (AST line 251): #0 WALK; #1 WALK; #2 WALK; #3 CTR. -/
theorem «fb_memzero» : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero» := by sorry
/-- `node_new_branch` (AST line 10046): loop-free. -/
theorem «fb_node_new_branch» : TerminatingFunBoundedOn GuestInv (ofString "node_new_branch") K.«node_new_branch» := by sorry
/-- `_create_branch_from_two_leaves` (AST line 10507): loop-free. -/
theorem «fb__create_branch_from_two_leaves» : TerminatingFunBoundedOn GuestInv (ofString "_create_branch_from_two_leaves") K.«_create_branch_from_two_leaves» := by sorry
/-- `key_to_nibbles` (AST line 9807): #0 WALK; #1 CTR. -/
theorem «fb_key_to_nibbles» : TerminatingFunBoundedOn GuestInv (ofString "key_to_nibbles") K.«key_to_nibbles» := by sorry
/-- `compact_to_nibbles` (AST line 9849): loop-free. -/
theorem «fb_compact_to_nibbles» : TerminatingFunBoundedOn GuestInv (ofString "compact_to_nibbles") K.«compact_to_nibbles» := by sorry
/-- `rlp_fail` (AST line 4305): loop-free. -/
theorem «fb_rlp_fail» : TerminatingFunBoundedOn GuestInv (ofString "rlp_fail") K.«rlp_fail» := by sorry
/-- `rlp_read_length` (AST line 4317): #0 CTR. -/
theorem «fb_rlp_read_length» : TerminatingFunBoundedOn GuestInv (ofString "rlp_read_length") K.«rlp_read_length» := by sorry
/-- `rlp_item_header` (AST line 4432): loop-free. -/
theorem «fb_rlp_item_header» : TerminatingFunBoundedOn GuestInv (ofString "rlp_item_header") K.«rlp_item_header» := by sorry
/-- `scratch_alloc` (AST line 154): loop-free. -/
theorem «fb_scratch_alloc» : TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc» := by sorry
/-- `_rlp_validate_items_body` (AST line 4507): #0 STACK. -/
theorem «fb__rlp_validate_items_body» : TerminatingFunBoundedOn GuestInv (ofString "_rlp_validate_items_body") K.«_rlp_validate_items_body» := by sorry
/-- `scratch_mark` (AST line 176): loop-free. -/
theorem «fb_scratch_mark» : TerminatingFunBoundedOn GuestInv (ofString "scratch_mark") K.«scratch_mark» := by sorry
/-- `scratch_release` (AST line 186): loop-free. -/
theorem «fb_scratch_release» : TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release» := by sorry
/-- `rlp_validate_items` (AST line 4548): loop-free. -/
theorem «fb_rlp_validate_items» : TerminatingFunBoundedOn GuestInv (ofString "rlp_validate_items") K.«rlp_validate_items» := by sorry
/-- `rlp_item_total` (AST line 4567): loop-free. -/
theorem «fb_rlp_item_total» : TerminatingFunBoundedOn GuestInv (ofString "rlp_item_total") K.«rlp_item_total» := by sorry
/-- `rlp_list_count` (AST line 4582): #0 MONO. -/
theorem «fb_rlp_list_count» : TerminatingFunBoundedOn GuestInv (ofString "rlp_list_count") K.«rlp_list_count» := by sorry
/-- `rlp_item` (AST line 4338): loop-free. -/
theorem «fb_rlp_item» : TerminatingFunBoundedOn GuestInv (ofString "rlp_item") K.«rlp_item» := by sorry
/-- `rlp_decode_fully` (AST line 4417): loop-free. -/
theorem «fb_rlp_decode_fully» : TerminatingFunBoundedOn GuestInv (ofString "rlp_decode_fully") K.«rlp_decode_fully» := by sorry
/-- `rlp_item_total_unchecked` (AST line 4600): loop-free. -/
theorem «fb_rlp_item_total_unchecked» : TerminatingFunBoundedOn GuestInv (ofString "rlp_item_total_unchecked") K.«rlp_item_total_unchecked» := by sorry
/-- `rlp_list_to_slices` (AST line 4631): #0 CTR. -/
theorem «fb_rlp_list_to_slices» : TerminatingFunBoundedOn GuestInv (ofString "rlp_list_to_slices") K.«rlp_list_to_slices» := by sorry
/-- `_decode_step` (AST line 10110): loop-free. -/
theorem «fb__decode_step» : TerminatingFunBoundedOn GuestInv (ofString "_decode_step") K.«_decode_step» := by sorry
/-- `node_new_hashed` (AST line 9975): loop-free. -/
theorem «fb_node_new_hashed» : TerminatingFunBoundedOn GuestInv (ofString "node_new_hashed") K.«node_new_hashed» := by sorry
/-- `htab_find_leaf` (AST line 4976): #0 RO(1). -/
theorem «fb_htab_find_leaf» : TerminatingFunBoundedOn GuestInv (ofString "htab_find_leaf") K.«htab_find_leaf» := by sorry
/-- `memeq` (AST line 304): #0 RO(1); #1 RO(1); #2 RO(1); #3 CTR. -/
theorem «fb_memeq» : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq» := by sorry
/-- `htab_get` (AST line 4999): loop-free. -/
theorem «fb_htab_get» : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get» := by sorry
/-- `nodedb_lookup` (AST line 9960): loop-free. -/
theorem «fb_nodedb_lookup» : TerminatingFunBoundedOn GuestInv (ofString "nodedb_lookup") K.«nodedb_lookup» := by sorry
/-- `_resolve_step` (AST line 10077): loop-free. -/
theorem «fb__resolve_step» : TerminatingFunBoundedOn GuestInv (ofString "_resolve_step") K.«_resolve_step» := by sorry
/-- `_delete_ext_finish` (AST line 10727): loop-free. -/
theorem «fb__delete_ext_finish» : TerminatingFunBoundedOn GuestInv (ofString "_delete_ext_finish") K.«_delete_ext_finish» := by sorry
/-- `min` (AST line 667): loop-free. -/
theorem «fb_min» : TerminatingFunBoundedOn GuestInv (ofString "min") K.«min» := by sorry
/-- `common_prefix_length` (AST line 9903): #0 CTR. -/
theorem «fb_common_prefix_length» : TerminatingFunBoundedOn GuestInv (ofString "common_prefix_length") K.«common_prefix_length» := by sorry
/-- `_insert_into_leaf` (AST line 10532): loop-free. -/
theorem «fb__insert_into_leaf» : TerminatingFunBoundedOn GuestInv (ofString "_insert_into_leaf") K.«_insert_into_leaf» := by sorry
/-- `node_invalidate` (AST line 10061): loop-free. -/
theorem «fb_node_invalidate» : TerminatingFunBoundedOn GuestInv (ofString "node_invalidate") K.«node_invalidate» := by sorry
/-- `_split_extension` (AST line 10561): loop-free. -/
theorem «fb__split_extension» : TerminatingFunBoundedOn GuestInv (ofString "_split_extension") K.«_split_extension» := by sorry
/-- `_node_needs_rlp` (AST line 10989): loop-free. -/
theorem «fb__node_needs_rlp» : TerminatingFunBoundedOn GuestInv (ofString "_node_needs_rlp") K.«_node_needs_rlp» := by sorry
/-- `nibble_list_to_compact` (AST line 9877): #0 WALK. -/
theorem «fb_nibble_list_to_compact» : TerminatingFunBoundedOn GuestInv (ofString "nibble_list_to_compact") K.«nibble_list_to_compact» := by sorry
/-- `rlp_be_len` (AST line 4698): #0 RO(2). -/
theorem «fb_rlp_be_len» : TerminatingFunBoundedOn GuestInv (ofString "rlp_be_len") K.«rlp_be_len» := by sorry
/-- `rlp_header_len` (AST line 4753): loop-free. -/
theorem «fb_rlp_header_len» : TerminatingFunBoundedOn GuestInv (ofString "rlp_header_len") K.«rlp_header_len» := by sorry
/-- `rlp_bytes_encoded_len` (AST line 4827): loop-free. -/
theorem «fb_rlp_bytes_encoded_len» : TerminatingFunBoundedOn GuestInv (ofString "rlp_bytes_encoded_len") K.«rlp_bytes_encoded_len» := by sorry
/-- `rlp_value_encoded_len` (AST line 11095): loop-free. -/
theorem «fb_rlp_value_encoded_len» : TerminatingFunBoundedOn GuestInv (ofString "rlp_value_encoded_len") K.«rlp_value_encoded_len» := by sorry
/-- `_node_rlp_begin` (AST line 10890): loop-free. -/
theorem «fb__node_rlp_begin» : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_begin") K.«_node_rlp_begin» := by sorry
/-- `node_ref_len` (AST line 11110): loop-free. -/
theorem «fb_node_ref_len» : TerminatingFunBoundedOn GuestInv (ofString "node_ref_len") K.«node_ref_len» := by sorry
/-- `keccak_f1600` (AST line 4038): #0 CTR. -/
theorem «fb_keccak_f1600» : TerminatingFunBoundedOn GuestInv (ofString "keccak_f1600") K.«keccak_f1600» := by sorry
/-- `keccak_absorb_block` (AST line 4239): #0 CTR; #1 CTR. -/
theorem «fb_keccak_absorb_block» : TerminatingFunBoundedOn GuestInv (ofString "keccak_absorb_block") K.«keccak_absorb_block» := by sorry
/-- `keccak256` (AST line 4262): #0 WALK. -/
theorem «fb_keccak256» : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256» := by sorry
/-- `node_hash_cached` (AST line 11137): loop-free. -/
theorem «fb_node_hash_cached» : TerminatingFunBoundedOn GuestInv (ofString "node_hash_cached") K.«node_hash_cached» := by sorry
/-- `node_write_ref` (AST line 11161): loop-free. -/
theorem «fb_node_write_ref» : TerminatingFunBoundedOn GuestInv (ofString "node_write_ref") K.«node_write_ref» := by sorry
/-- `rlp_put_be` (AST line 4714): #0 CTR. -/
theorem «fb_rlp_put_be» : TerminatingFunBoundedOn GuestInv (ofString "rlp_put_be") K.«rlp_put_be» := by sorry
/-- `rlp_write_header` (AST line 4732): loop-free. -/
theorem «fb_rlp_write_header» : TerminatingFunBoundedOn GuestInv (ofString "rlp_write_header") K.«rlp_write_header» := by sorry
/-- `rlp_encode_bytes` (AST line 4768): loop-free. -/
theorem «fb_rlp_encode_bytes» : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.«rlp_encode_bytes» := by sorry
/-- `rlp_encode_list_header` (AST line 4817): loop-free. -/
theorem «fb_rlp_encode_list_header» : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_list_header") K.«rlp_encode_list_header» := by sorry
/-- `rlp_list_header_len` (AST line 4842): loop-free. -/
theorem «fb_rlp_list_header_len» : TerminatingFunBoundedOn GuestInv (ofString "rlp_list_header_len") K.«rlp_list_header_len» := by sorry
/-- `_node_rlp_finish` (AST line 10930): #0 CTR; #1 CTR. -/
theorem «fb__node_rlp_finish» : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_finish") K.«_node_rlp_finish» := by sorry
/-- `_node_rlp_fill` (AST line 11011): #0 ALLOC; #1 RO(3). -/
theorem «fb__node_rlp_fill» : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_fill") K.«_node_rlp_fill» := by sorry
/-- `htab_has` (AST line 5022): loop-free. -/
theorem «fb_htab_has» : TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.«htab_has» := by sorry
/-- `is_warm_address` (AST line 15473): loop-free. -/
theorem «fb_is_warm_address» : TerminatingFunBoundedOn GuestInv (ofString "is_warm_address") K.«is_warm_address» := by sorry
/-- `access_gas_cost` (AST line 15496): loop-free. -/
theorem «fb_access_gas_cost» : TerminatingFunBoundedOn GuestInv (ofString "access_gas_cost") K.«access_gas_cost» := by sorry
/-- `access_list_payload_len` (AST line 11977): #0 CTR. -/
theorem «fb_access_list_payload_len» : TerminatingFunBoundedOn GuestInv (ofString "access_list_payload_len") K.«access_list_payload_len» := by sorry
/-- `htab_first_diff` (AST line 4951): #0 CTR; #1 CTR. -/
theorem «fb_htab_first_diff» : TerminatingFunBoundedOn GuestInv (ofString "htab_first_diff") K.«htab_first_diff» := by sorry
/-- `htab_grow` (AST line 5117): loop-free. -/
theorem «fb_htab_grow» : TerminatingFunBoundedOn GuestInv (ofString "htab_grow") K.«htab_grow» := by sorry
/-- `htab_new_node` (AST line 5041): loop-free. -/
theorem «fb_htab_new_node» : TerminatingFunBoundedOn GuestInv (ofString "htab_new_node") K.«htab_new_node» := by sorry
/-- `htab_new_internal` (AST line 5097): loop-free. -/
theorem «fb_htab_new_internal» : TerminatingFunBoundedOn GuestInv (ofString "htab_new_internal") K.«htab_new_internal» := by sorry
/-- `htab_new_leaf` (AST line 5068): loop-free. -/
theorem «fb_htab_new_leaf» : TerminatingFunBoundedOn GuestInv (ofString "htab_new_leaf") K.«htab_new_leaf» := by sorry
/-- `htab_set` (AST line 5149): #0 RO(2). -/
theorem «fb_htab_set» : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set» := by sorry
/-- `record_pre_state_read` (AST line 12980): loop-free. -/
theorem «fb_record_pre_state_read» : TerminatingFunBoundedOn GuestInv (ofString "record_pre_state_read") K.«record_pre_state_read» := by sorry
/-- `decode_account_from_leaf` (AST line 11266): #0 CTR; #1 CTR. -/
theorem «fb_decode_account_from_leaf» : TerminatingFunBoundedOn GuestInv (ofString "decode_account_from_leaf") K.«decode_account_from_leaf» := by sorry
/-- `heap_mark` (AST line 88): loop-free. -/
theorem «fb_heap_mark» : TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark» := by sorry
/-- `heap_release` (AST line 98): loop-free. -/
theorem «fb_heap_release» : TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release» := by sorry
/-- `trie_walk` (AST line 10376): #0 RO(2). -/
theorem «fb_trie_walk» : TerminatingFunBoundedOn GuestInv (ofString "trie_walk") K.«trie_walk» := by sorry
/-- `trie_lookup` (AST line 10432): loop-free. -/
theorem «fb_trie_lookup» : TerminatingFunBoundedOn GuestInv (ofString "trie_lookup") K.«trie_lookup» := by sorry
/-- `ws_account_leaf` (AST line 12992): loop-free. -/
theorem «fb_ws_account_leaf» : TerminatingFunBoundedOn GuestInv (ofString "ws_account_leaf") K.«ws_account_leaf» := by sorry
/-- `ws_get_account_optional` (AST line 13009): loop-free. -/
theorem «fb_ws_get_account_optional» : TerminatingFunBoundedOn GuestInv (ofString "ws_get_account_optional") K.«ws_get_account_optional» := by sorry
/-- `ws_storage_root_of` (AST line 13027): loop-free. -/
theorem «fb_ws_storage_root_of» : TerminatingFunBoundedOn GuestInv (ofString "ws_storage_root_of") K.«ws_storage_root_of» := by sorry
/-- `ws_account_has_storage` (AST line 13119): loop-free. -/
theorem «fb_ws_account_has_storage» : TerminatingFunBoundedOn GuestInv (ofString "ws_account_has_storage") K.«ws_account_has_storage» := by sorry
/-- `account_has_storage` (AST line 13330): loop-free. -/
theorem «fb_account_has_storage» : TerminatingFunBoundedOn GuestInv (ofString "account_has_storage") K.«account_has_storage» := by sorry
/-- `acct_new` (AST line 12937): loop-free. -/
theorem «fb_acct_new» : TerminatingFunBoundedOn GuestInv (ofString "acct_new") K.«acct_new» := by sorry
/-- `acct_empty` (AST line 12956): loop-free. -/
theorem «fb_acct_empty» : TerminatingFunBoundedOn GuestInv (ofString "acct_empty") K.«acct_empty» := by sorry
/-- `get_pre_state_account_optional` (AST line 13135): loop-free. -/
theorem «fb_get_pre_state_account_optional» : TerminatingFunBoundedOn GuestInv (ofString "get_pre_state_account_optional") K.«get_pre_state_account_optional» := by sorry
/-- `get_account_optional` (AST line 13170): loop-free. -/
theorem «fb_get_account_optional» : TerminatingFunBoundedOn GuestInv (ofString "get_account_optional") K.«get_account_optional» := by sorry
/-- `get_account` (AST line 13188): loop-free. -/
theorem «fb_get_account» : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account» := by sorry
/-- `account_deployable` (AST line 13358): loop-free. -/
theorem «fb_account_deployable» : TerminatingFunBoundedOn GuestInv (ofString "account_deployable") K.«account_deployable» := by sorry
/-- `account_exists` (AST line 13315): loop-free. -/
theorem «fb_account_exists» : TerminatingFunBoundedOn GuestInv (ofString "account_exists") K.«account_exists» := by sorry
/-- `acct_copy` (AST line 12967): loop-free. -/
theorem «fb_acct_copy» : TerminatingFunBoundedOn GuestInv (ofString "acct_copy") K.«acct_copy» := by sorry
/-- `u256_is_zero` (AST line 814): loop-free. -/
theorem «fb_u256_is_zero» : TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero» := by sorry
/-- `acct_is_empty` (AST line 13383): loop-free. -/
theorem «fb_acct_is_empty» : TerminatingFunBoundedOn GuestInv (ofString "acct_is_empty") K.«acct_is_empty» := by sorry
/-- `htab_new` (AST line 4867): loop-free. -/
theorem «fb_htab_new» : TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new» := by sorry
/-- `lst_new` (AST line 13804): loop-free. -/
theorem «fb_lst_new» : TerminatingFunBoundedOn GuestInv (ofString "lst_new") K.«lst_new» := by sorry
/-- `bal_ensure_account` (AST line 13883): loop-free. -/
theorem «fb_bal_ensure_account» : TerminatingFunBoundedOn GuestInv (ofString "bal_ensure_account") K.«bal_ensure_account» := by sorry
/-- `lst_push` (AST line 13840): loop-free. -/
theorem «fb_lst_push» : TerminatingFunBoundedOn GuestInv (ofString "lst_push") K.«lst_push» := by sorry
/-- `lst_upsert_idx` (AST line 13919): #0 CTR. -/
theorem «fb_lst_upsert_idx» : TerminatingFunBoundedOn GuestInv (ofString "lst_upsert_idx") K.«lst_upsert_idx» := by sorry
/-- `add_balance_change` (AST line 13978): loop-free. -/
theorem «fb_add_balance_change» : TerminatingFunBoundedOn GuestInv (ofString "add_balance_change") K.«add_balance_change» := by sorry
/-- `add_code_change` (AST line 14023): loop-free. -/
theorem «fb_add_code_change» : TerminatingFunBoundedOn GuestInv (ofString "add_code_change") K.«add_code_change» := by sorry
/-- `add_nonce_change` (AST line 13992): #0 CTR. -/
theorem «fb_add_nonce_change» : TerminatingFunBoundedOn GuestInv (ofString "add_nonce_change") K.«add_nonce_change» := by sorry
/-- `add_sat` (AST line 14847): loop-free. -/
theorem «fb_add_sat» : TerminatingFunBoundedOn GuestInv (ofString "add_sat") K.«add_sat» := by sorry
/-- `add_storage_read` (AST line 13965): loop-free. -/
theorem «fb_add_storage_read» : TerminatingFunBoundedOn GuestInv (ofString "add_storage_read") K.«add_storage_read» := by sorry
/-- `add_storage_write` (AST line 13942): loop-free. -/
theorem «fb_add_storage_write» : TerminatingFunBoundedOn GuestInv (ofString "add_storage_write") K.«add_storage_write» := by sorry
/-- `add_to_bloom` (AST line 31915): #0 CTR. -/
theorem «fb_add_to_bloom» : TerminatingFunBoundedOn GuestInv (ofString "add_to_bloom") K.«add_to_bloom» := by sorry
/-- `add_touched_account` (AST line 14039): loop-free. -/
theorem «fb_add_touched_account» : TerminatingFunBoundedOn GuestInv (ofString "add_touched_account") K.«add_touched_account» := by sorry
/-- `st_be32` (AST line 585): loop-free. -/
theorem «fb_st_be32» : TerminatingFunBoundedOn GuestInv (ofString "st_be32") K.«st_be32» := by sorry
/-- `bswap64` (AST line 525): loop-free. -/
theorem «fb_bswap64» : TerminatingFunBoundedOn GuestInv (ofString "bswap64") K.«bswap64» := by sorry
/-- `st_be64` (AST line 603): loop-free. -/
theorem «fb_st_be64» : TerminatingFunBoundedOn GuestInv (ofString "st_be64") K.«st_be64» := by sorry
/-- `addr_from_words` (AST line 32506): loop-free. -/
theorem «fb_addr_from_words» : TerminatingFunBoundedOn GuestInv (ofString "addr_from_words") K.«addr_from_words» := by sorry
/-- `u256_from_be` (AST line 2213): #0 CTR. -/
theorem «fb_u256_from_be» : TerminatingFunBoundedOn GuestInv (ofString "u256_from_be") K.«u256_from_be» := by sorry
/-- `address_to_u256` (AST line 14906): loop-free. -/
theorem «fb_address_to_u256» : TerminatingFunBoundedOn GuestInv (ofString "address_to_u256") K.«address_to_u256» := by sorry
/-- `udivmod` (AST line 695): #0 CTR. -/
theorem «fb_udivmod» : TerminatingFunBoundedOn GuestInv (ofString "udivmod") K.«udivmod» := by sorry
/-- `udiv` (AST line 727): loop-free. -/
theorem «fb_udiv» : TerminatingFunBoundedOn GuestInv (ofString "udiv") K.«udiv» := by sorry
/-- `check_gas_limit` (AST line 9590): loop-free. -/
theorem «fb_check_gas_limit» : TerminatingFunBoundedOn GuestInv (ofString "check_gas_limit") K.«check_gas_limit» := by sorry
/-- `bal_init` (AST line 13863): loop-free. -/
theorem «fb_bal_init» : TerminatingFunBoundedOn GuestInv (ofString "bal_init") K.«bal_init» := by sorry
/-- `htab_keys` (AST line 5332): #0 CTR. -/
theorem «fb_htab_keys» : TerminatingFunBoundedOn GuestInv (ofString "htab_keys") K.«htab_keys» := by sorry
/-- `rlp_encode_word` (AST line 4790): loop-free. -/
theorem «fb_rlp_encode_word» : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_word") K.«rlp_encode_word» := by sorry
/-- `bit_length64` (AST line 1919): loop-free. -/
theorem «fb_bit_length64» : TerminatingFunBoundedOn GuestInv (ofString "bit_length64") K.«bit_length64» := by sorry
/-- `u256_bit_length` (AST line 1966): loop-free. -/
theorem «fb_u256_bit_length» : TerminatingFunBoundedOn GuestInv (ofString "u256_bit_length") K.«u256_bit_length» := by sorry
/-- `u256_byte_length` (AST line 1991): loop-free. -/
theorem «fb_u256_byte_length» : TerminatingFunBoundedOn GuestInv (ofString "u256_byte_length") K.«u256_byte_length» := by sorry
/-- `u256_limb` (AST line 828): loop-free. -/
theorem «fb_u256_limb» : TerminatingFunBoundedOn GuestInv (ofString "u256_limb") K.«u256_limb» := by sorry
/-- `u256_to_be_min` (AST line 2302): #0 CTR. -/
theorem «fb_u256_to_be_min» : TerminatingFunBoundedOn GuestInv (ofString "u256_to_be_min") K.«u256_to_be_min» := by sorry
/-- `rlp_put_u256` (AST line 9334): loop-free. -/
theorem «fb_rlp_put_u256» : TerminatingFunBoundedOn GuestInv (ofString "rlp_put_u256") K.«rlp_put_u256» := by sorry
/-- `bal_sort_gt` (AST line 14327): #0 CTR. -/
theorem «fb_bal_sort_gt» : TerminatingFunBoundedOn GuestInv (ofString "bal_sort_gt") K.«bal_sort_gt» := by sorry
/-- `sort_elems` (AST line 14364): #0 MONO; #1 MONO; #2 MONO; #3 CTR; #4 CTR. -/
theorem «fb_sort_elems» : TerminatingFunBoundedOn GuestInv (ofString "sort_elems") K.«sort_elems» := by sorry
/-- `sorted_keys32` (AST line 14442): loop-free. -/
theorem «fb_sorted_keys32» : TerminatingFunBoundedOn GuestInv (ofString "sorted_keys32") K.«sorted_keys32» := by sorry
/-- `bal_encode_account` (AST line 14455): #0 CTR; #1 CTR; #2 CTR; #3 CTR; #4 CTR; #5 CTR; #6 CTR. -/
theorem «fb_bal_encode_account» : TerminatingFunBoundedOn GuestInv (ofString "bal_encode_account") K.«bal_encode_account» := by sorry
/-- `htab_item` (AST line 5314): loop-free. -/
theorem «fb_htab_item» : TerminatingFunBoundedOn GuestInv (ofString "htab_item") K.«htab_item» := by sorry
/-- `build_block_access_list_rlp` (AST line 14685): #0 CTR; #1 CTR; #2 CTR; #3 CTR; #4 CTR; #5 CTR. -/
theorem «fb_build_block_access_list_rlp» : TerminatingFunBoundedOn GuestInv (ofString "build_block_access_list_rlp") K.«build_block_access_list_rlp» := by sorry
/-- `mpt_new` (AST line 10444): loop-free. -/
theorem «fb_mpt_new» : TerminatingFunBoundedOn GuestInv (ofString "mpt_new") K.«mpt_new» := by sorry
/-- `node_rlp` (AST line 11074): loop-free. -/
theorem «fb_node_rlp» : TerminatingFunBoundedOn GuestInv (ofString "node_rlp") K.«node_rlp» := by sorry
/-- `node_hash` (AST line 11202): loop-free. -/
theorem «fb_node_hash» : TerminatingFunBoundedOn GuestInv (ofString "node_hash") K.«node_hash» := by sorry
/-- `mpt_root` (AST line 11223): loop-free. -/
theorem «fb_mpt_root» : TerminatingFunBoundedOn GuestInv (ofString "mpt_root") K.«mpt_root» := by sorry
/-- `mpt_nibble_key` (AST line 10470): loop-free. -/
theorem «fb_mpt_nibble_key» : TerminatingFunBoundedOn GuestInv (ofString "mpt_nibble_key") K.«mpt_nibble_key» := by sorry
/-- `sha256_block` (AST line 2367): loop-free. -/
theorem «fb_sha256_block» : TerminatingFunBoundedOn GuestInv (ofString "sha256_block") K.«sha256_block» := by sorry
/-- `sha256_finish` (AST line 2898): #0 CTR. -/
theorem «fb_sha256_finish» : TerminatingFunBoundedOn GuestInv (ofString "sha256_finish") K.«sha256_finish» := by sorry
/-- `sha256_state_init` (AST line 2341): loop-free. -/
theorem «fb_sha256_state_init» : TerminatingFunBoundedOn GuestInv (ofString "sha256_state_init") K.«sha256_state_init» := by sorry
/-- `sha256` (AST line 2914): #0 WALK. -/
theorem «fb_sha256» : TerminatingFunBoundedOn GuestInv (ofString "sha256") K.«sha256» := by sorry
/-- `compute_requests_hash` (AST line 32190): #0 CTR. -/
theorem «fb_compute_requests_hash» : TerminatingFunBoundedOn GuestInv (ofString "compute_requests_hash") K.«compute_requests_hash» := by sorry
/-- `cache_get_root` (AST line 32325): loop-free. -/
theorem «fb_cache_get_root» : TerminatingFunBoundedOn GuestInv (ofString "cache_get_root") K.«cache_get_root» := by sorry
/-- `encode_account` (AST line 11343): #0 CTR. -/
theorem «fb_encode_account» : TerminatingFunBoundedOn GuestInv (ofString "encode_account") K.«encode_account» := by sorry
/-- `htab_copy` (AST line 5354): loop-free. -/
theorem «fb_htab_copy» : TerminatingFunBoundedOn GuestInv (ofString "htab_copy") K.«htab_copy» := by sorry
/-- `tx_fixed_bytes` (AST line 11468): loop-free. -/
theorem «fb_tx_fixed_bytes» : TerminatingFunBoundedOn GuestInv (ofString "tx_fixed_bytes") K.«tx_fixed_bytes» := by sorry
/-- `tx_list_item` (AST line 11510): loop-free. -/
theorem «fb_tx_list_item» : TerminatingFunBoundedOn GuestInv (ofString "tx_list_item") K.«tx_list_item» := by sorry
/-- `decode_access_list` (AST line 11525): #0 CTR; #1 CTR. -/
theorem «fb_decode_access_list» : TerminatingFunBoundedOn GuestInv (ofString "decode_access_list") K.«decode_access_list» := by sorry
/-- `tx_scalar_item` (AST line 11389): loop-free. -/
theorem «fb_tx_scalar_item» : TerminatingFunBoundedOn GuestInv (ofString "tx_scalar_item") K.«tx_scalar_item» := by sorry
/-- `tx_scalar_u256` (AST line 11416): loop-free. -/
theorem «fb_tx_scalar_u256» : TerminatingFunBoundedOn GuestInv (ofString "tx_scalar_u256") K.«tx_scalar_u256» := by sorry
/-- `tx_scalar_word` (AST line 11431): #0 CTR. -/
theorem «fb_tx_scalar_word» : TerminatingFunBoundedOn GuestInv (ofString "tx_scalar_word") K.«tx_scalar_word» := by sorry
/-- `decode_authorizations` (AST line 11588): #0 CTR. -/
theorem «fb_decode_authorizations» : TerminatingFunBoundedOn GuestInv (ofString "decode_authorizations") K.«decode_authorizations» := by sorry
/-- `decode_blob_hashes` (AST line 11569): #0 CTR. -/
theorem «fb_decode_blob_hashes» : TerminatingFunBoundedOn GuestInv (ofString "decode_blob_hashes") K.«decode_blob_hashes» := by sorry
/-- `tx_bytes_item` (AST line 11453): loop-free. -/
theorem «fb_tx_bytes_item» : TerminatingFunBoundedOn GuestInv (ofString "tx_bytes_item") K.«tx_bytes_item» := by sorry
/-- `tx_to_item` (AST line 11487): loop-free. -/
theorem «fb_tx_to_item» : TerminatingFunBoundedOn GuestInv (ofString "tx_to_item") K.«tx_to_item» := by sorry
/-- `decode_transaction_rlp` (AST line 11634): loop-free. -/
theorem «fb_decode_transaction_rlp» : TerminatingFunBoundedOn GuestInv (ofString "decode_transaction_rlp") K.«decode_transaction_rlp» := by sorry
/-- `decode_transaction` (AST line 11805): loop-free. -/
theorem «fb_decode_transaction» : TerminatingFunBoundedOn GuestInv (ofString "decode_transaction") K.«decode_transaction» := by sorry
/-- `logs_bloom` (AST line 31941): #0 CTR; #1 CTR. -/
theorem «fb_logs_bloom» : TerminatingFunBoundedOn GuestInv (ofString "logs_bloom") K.«logs_bloom» := by sorry
/-- `max` (AST line 681): loop-free. -/
theorem «fb_max» : TerminatingFunBoundedOn GuestInv (ofString "max") K.«max» := by sorry
/-- `is_zero_bytes` (AST line 477): #0 CTR. -/
theorem «fb_is_zero_bytes» : TerminatingFunBoundedOn GuestInv (ofString "is_zero_bytes") K.«is_zero_bytes» := by sorry
/-- `ld_be64` (AST line 539): loop-free. -/
theorem «fb_ld_be64» : TerminatingFunBoundedOn GuestInv (ofString "ld_be64") K.«ld_be64» := by sorry
/-- `extract_deposit_data` (AST line 32212): loop-free. -/
theorem «fb_extract_deposit_data» : TerminatingFunBoundedOn GuestInv (ofString "extract_deposit_data") K.«extract_deposit_data» := by sorry
/-- `sk_make` (AST line 12923): loop-free. -/
theorem «fb_sk_make» : TerminatingFunBoundedOn GuestInv (ofString "sk_make") K.«sk_make» := by sorry
/-- `ws_get_code` (AST line 13099): loop-free. -/
theorem «fb_ws_get_code» : TerminatingFunBoundedOn GuestInv (ofString "ws_get_code") K.«ws_get_code» := by sorry
/-- `get_code` (AST line 13203): loop-free. -/
theorem «fb_get_code» : TerminatingFunBoundedOn GuestInv (ofString "get_code") K.«get_code» := by sorry
/-- `ext_code_of` (AST line 16953): loop-free. -/
theorem «fb_ext_code_of» : TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.«ext_code_of» := by sorry
/-- `frame_mem_release` (AST line 142): loop-free. -/
theorem «fb_frame_mem_release» : TerminatingFunBoundedOn GuestInv (ofString "frame_mem_release") K.«frame_mem_release» := by sorry
/-- `htab_union_into` (AST line 13711): #0 CTR. -/
theorem «fb_htab_union_into» : TerminatingFunBoundedOn GuestInv (ofString "htab_union_into") K.«htab_union_into» := by sorry
/-- `merge_tx_into_block` (AST line 13731): #0 CTR. -/
theorem «fb_merge_tx_into_block» : TerminatingFunBoundedOn GuestInv (ofString "merge_tx_into_block") K.«merge_tx_into_block» := by sorry
/-- `bal_list_remove_idx` (AST line 14163): #0 CTR. -/
theorem «fb_bal_list_remove_idx» : TerminatingFunBoundedOn GuestInv (ofString "bal_list_remove_idx") K.«bal_list_remove_idx» := by sorry
/-- `bal_remove_change` (AST line 14189): loop-free. -/
theorem «fb_bal_remove_change» : TerminatingFunBoundedOn GuestInv (ofString "bal_remove_change") K.«bal_remove_change» := by sorry
/-- `get_pre_tx_account` (AST line 14051): loop-free. -/
theorem «fb_get_pre_tx_account» : TerminatingFunBoundedOn GuestInv (ofString "get_pre_tx_account") K.«get_pre_tx_account» := by sorry
/-- `st_le32` (AST line 553): loop-free. -/
theorem «fb_st_le32» : TerminatingFunBoundedOn GuestInv (ofString "st_le32") K.«st_le32» := by sorry
/-- `st_le64` (AST line 571): loop-free. -/
theorem «fb_st_le64» : TerminatingFunBoundedOn GuestInv (ofString "st_le64") K.«st_le64» := by sorry
/-- `idx_start_account` (AST line 14087): loop-free. -/
theorem «fb_idx_start_account» : TerminatingFunBoundedOn GuestInv (ofString "idx_start_account") K.«idx_start_account» := by sorry
/-- `stor_lookup` (AST line 13233): loop-free. -/
theorem «fb_stor_lookup» : TerminatingFunBoundedOn GuestInv (ofString "stor_lookup") K.«stor_lookup» := by sorry
/-- `htab_del` (AST line 5217): loop-free. -/
theorem «fb_htab_del» : TerminatingFunBoundedOn GuestInv (ofString "htab_del") K.«htab_del» := by sorry
/-- `remove_storage_write` (AST line 14206): loop-free. -/
theorem «fb_remove_storage_write» : TerminatingFunBoundedOn GuestInv (ofString "remove_storage_write") K.«remove_storage_write» := by sorry
/-- `u256_eq` (AST line 869): loop-free. -/
theorem «fb_u256_eq» : TerminatingFunBoundedOn GuestInv (ofString "u256_eq") K.«u256_eq» := by sorry
/-- `msg_new` (AST line 15344): loop-free. -/
theorem «fb_msg_new» : TerminatingFunBoundedOn GuestInv (ofString "msg_new") K.«msg_new» := by sorry
/-- `frame_state_gas_used` (AST line 15018): loop-free. -/
theorem «fb_frame_state_gas_used» : TerminatingFunBoundedOn GuestInv (ofString "frame_state_gas_used") K.«frame_state_gas_used» := by sorry
/-- `charge_gas` (AST line 14949): loop-free. -/
theorem «fb_charge_gas» : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas» := by sorry
/-- `charge_state_gas` (AST line 14968): loop-free. -/
theorem «fb_charge_state_gas» : TerminatingFunBoundedOn GuestInv (ofString "charge_state_gas") K.«charge_state_gas» := by sorry
/-- `jset` (AST line 12825): loop-free. -/
theorem «fb_jset» : TerminatingFunBoundedOn GuestInv (ofString "jset") K.«jset» := by sorry
/-- `jdel` (AST line 12857): loop-free. -/
theorem «fb_jdel» : TerminatingFunBoundedOn GuestInv (ofString "jdel") K.«jdel» := by sorry
/-- `destroy_storage` (AST line 13480): #0 CTR. -/
theorem «fb_destroy_storage» : TerminatingFunBoundedOn GuestInv (ofString "destroy_storage") K.«destroy_storage» := by sorry
/-- `set_account` (AST line 13439): loop-free. -/
theorem «fb_set_account» : TerminatingFunBoundedOn GuestInv (ofString "set_account") K.«set_account» := by sorry
/-- `destroy_account` (AST line 13510): loop-free. -/
theorem «fb_destroy_account» : TerminatingFunBoundedOn GuestInv (ofString "destroy_account") K.«destroy_account» := by sorry
/-- `modify_state_commit` (AST line 13524): loop-free. -/
theorem «fb_modify_state_commit» : TerminatingFunBoundedOn GuestInv (ofString "modify_state_commit") K.«modify_state_commit» := by sorry
/-- `set_code` (AST line 13681): loop-free. -/
theorem «fb_set_code» : TerminatingFunBoundedOn GuestInv (ofString "set_code") K.«set_code» := by sorry
/-- `ceil32` (AST line 14862): loop-free. -/
theorem «fb_ceil32» : TerminatingFunBoundedOn GuestInv (ofString "ceil32") K.«ceil32» := by sorry
/-- `words_of` (AST line 14878): loop-free. -/
theorem «fb_words_of» : TerminatingFunBoundedOn GuestInv (ofString "words_of") K.«words_of» := by sorry
/-- `create_finish` (AST line 18867): loop-free. -/
theorem «fb_create_finish» : TerminatingFunBoundedOn GuestInv (ofString "create_finish") K.«create_finish» := by sorry
/-- `frame_halt` (AST line 18756): loop-free. -/
theorem «fb_frame_halt» : TerminatingFunBoundedOn GuestInv (ofString "frame_halt") K.«frame_halt» := by sorry
/-- `increment_nonce` (AST line 13664): loop-free. -/
theorem «fb_increment_nonce» : TerminatingFunBoundedOn GuestInv (ofString "increment_nonce") K.«increment_nonce» := by sorry
/-- `mark_account_created` (AST line 13562): loop-free. -/
theorem «fb_mark_account_created» : TerminatingFunBoundedOn GuestInv (ofString "mark_account_created") K.«mark_account_created» := by sorry
/-- `compute_jumpdests` (AST line 15279): #0 WALK. -/
theorem «fb_compute_jumpdests» : TerminatingFunBoundedOn GuestInv (ofString "compute_jumpdests") K.«compute_jumpdests» := by sorry
/-- `is_valid_delegation` (AST line 14917): loop-free. -/
theorem «fb_is_valid_delegation» : TerminatingFunBoundedOn GuestInv (ofString "is_valid_delegation") K.«is_valid_delegation» := by sorry
/-- `get_delegated_code_address` (AST line 17610): loop-free. -/
theorem «fb_get_delegated_code_address» : TerminatingFunBoundedOn GuestInv (ofString "get_delegated_code_address") K.«get_delegated_code_address» := by sorry
/-- `get_pre_state_account` (AST line 13155): loop-free. -/
theorem «fb_get_pre_state_account» : TerminatingFunBoundedOn GuestInv (ofString "get_pre_state_account") K.«get_pre_state_account» := by sorry
/-- `is_account_alive` (AST line 13419): loop-free. -/
theorem «fb_is_account_alive» : TerminatingFunBoundedOn GuestInv (ofString "is_account_alive") K.«is_account_alive» := by sorry
/-- `warm_address` (AST line 15484): loop-free. -/
theorem «fb_warm_address» : TerminatingFunBoundedOn GuestInv (ofString "warm_address") K.«warm_address» := by sorry
/-- `prepare_dispatch` (AST line 17836): loop-free. -/
theorem «fb_prepare_dispatch» : TerminatingFunBoundedOn GuestInv (ofString "prepare_dispatch") K.«prepare_dispatch» := by sorry
/-- `ec_set_infinity` (AST line 6984): loop-free. -/
theorem «fb_ec_set_infinity» : TerminatingFunBoundedOn GuestInv (ofString "ec_set_infinity") K.«ec_set_infinity» := by sorry
/-- `u256_add_carry` (AST line 1039): loop-free. -/
theorem «fb_u256_add_carry» : TerminatingFunBoundedOn GuestInv (ofString "u256_add_carry") K.«u256_add_carry» := by sorry
/-- `u256_lt` (AST line 883): loop-free. -/
theorem «fb_u256_lt» : TerminatingFunBoundedOn GuestInv (ofString "u256_lt") K.«u256_lt» := by sorry
/-- `u256_sub` (AST line 1083): loop-free. -/
theorem «fb_u256_sub» : TerminatingFunBoundedOn GuestInv (ofString "u256_sub") K.«u256_sub» := by sorry
/-- `fp_add` (AST line 5427): loop-free. -/
theorem «fb_fp_add» : TerminatingFunBoundedOn GuestInv (ofString "fp_add") K.«fp_add» := by sorry
/-- `fp_reduce` (AST line 5479): loop-free. -/
theorem «fb_fp_reduce» : TerminatingFunBoundedOn GuestInv (ofString "fp_reduce") K.«fp_reduce» := by sorry
/-- `u256_add` (AST line 1061): loop-free. -/
theorem «fb_u256_add» : TerminatingFunBoundedOn GuestInv (ofString "u256_add") K.«u256_add» := by sorry
/-- `fp_mul` (AST line 5494): loop-free. -/
theorem «fb_fp_mul» : TerminatingFunBoundedOn GuestInv (ofString "fp_mul") K.«fp_mul» := by sorry
/-- `fp_sqr` (AST line 6163): loop-free. -/
theorem «fb_fp_sqr» : TerminatingFunBoundedOn GuestInv (ofString "fp_sqr") K.«fp_sqr» := by sorry
/-- `fp_sub` (AST line 5448): loop-free. -/
theorem «fb_fp_sub» : TerminatingFunBoundedOn GuestInv (ofString "fp_sub") K.«fp_sub» := by sorry
/-- `ec_double` (AST line 7027): loop-free. -/
theorem «fb_ec_double» : TerminatingFunBoundedOn GuestInv (ofString "ec_double") K.«ec_double» := by sorry
/-- `ec_set_affine` (AST line 7000): loop-free. -/
theorem «fb_ec_set_affine» : TerminatingFunBoundedOn GuestInv (ofString "ec_set_affine") K.«ec_set_affine» := by sorry
/-- `ec_add_affine` (AST line 7086): loop-free. -/
theorem «fb_ec_add_affine» : TerminatingFunBoundedOn GuestInv (ofString "ec_add_affine") K.«ec_add_affine» := by sorry
/-- `ec_is_infinity` (AST line 7016): loop-free. -/
theorem «fb_ec_is_infinity» : TerminatingFunBoundedOn GuestInv (ofString "ec_is_infinity") K.«ec_is_infinity» := by sorry
/-- `mod_half` (AST line 6866): loop-free. -/
theorem «fb_mod_half» : TerminatingFunBoundedOn GuestInv (ofString "mod_half") K.«mod_half» := by sorry
/-- `mod_sub` (AST line 6881): loop-free. -/
theorem «fb_mod_sub» : TerminatingFunBoundedOn GuestInv (ofString "mod_sub") K.«mod_sub» := by sorry
/-- `modinv_bin` (AST line 6815): #0 MONO; #1 MONO; #2 MONO. -/
theorem «fb_modinv_bin» : TerminatingFunBoundedOn GuestInv (ofString "modinv_bin") K.«modinv_bin» := by sorry
/-- `fp_inv` (AST line 6897): loop-free. -/
theorem «fb_fp_inv» : TerminatingFunBoundedOn GuestInv (ofString "fp_inv") K.«fp_inv» := by sorry
/-- `ec_to_affine` (AST line 7308): loop-free. -/
theorem «fb_ec_to_affine» : TerminatingFunBoundedOn GuestInv (ofString "ec_to_affine") K.«ec_to_affine» := by sorry
/-- `u256_bit` (AST line 854): loop-free. -/
theorem «fb_u256_bit» : TerminatingFunBoundedOn GuestInv (ofString "u256_bit") K.«u256_bit» := by sorry
/-- `ec_mul2` (AST line 7257): #0 CTR. -/
theorem «fb_ec_mul2» : TerminatingFunBoundedOn GuestInv (ofString "ec_mul2") K.«ec_mul2» := by sorry
/-- `fn_inv` (AST line 6974): loop-free. -/
theorem «fb_fn_inv» : TerminatingFunBoundedOn GuestInv (ofString "fn_inv") K.«fn_inv» := by sorry
/-- `digits_len` (AST line 1566): #0 CTR. -/
theorem «fb_digits_len» : TerminatingFunBoundedOn GuestInv (ofString "digits_len") K.«digits_len» := by sorry
/-- `digits_to_u256` (AST line 1556): loop-free. -/
theorem «fb_digits_to_u256» : TerminatingFunBoundedOn GuestInv (ofString "digits_to_u256") K.«digits_to_u256» := by sorry
/-- `div64by32` (AST line 1506): #0 CTR. -/
theorem «fb_div64by32» : TerminatingFunBoundedOn GuestInv (ofString "div64by32") K.«div64by32» := by sorry
/-- `nlz32` (AST line 1467): loop-free. -/
theorem «fb_nlz32» : TerminatingFunBoundedOn GuestInv (ofString "nlz32") K.«nlz32» := by sorry
/-- `divmnu` (AST line 1583): #0 CTR; #1 CTR; #2 CTR; #3 CTR; #4 RO(3); #5 CTR; #6 CTR; #7 CTR; #8 CTR. -/
theorem «fb_divmnu» : TerminatingFunBoundedOn GuestInv (ofString "divmnu") K.«divmnu» := by sorry
/-- `u256_to_digits` (AST line 1530): loop-free. -/
theorem «fb_u256_to_digits» : TerminatingFunBoundedOn GuestInv (ofString "u256_to_digits") K.«u256_to_digits» := by sorry
/-- `digits_divmod` (AST line 1718): #0 CTR; #1 CTR. -/
theorem «fb_digits_divmod» : TerminatingFunBoundedOn GuestInv (ofString "digits_divmod") K.«digits_divmod» := by sorry
/-- `mul64x64` (AST line 1127): loop-free. -/
theorem «fb_mul64x64» : TerminatingFunBoundedOn GuestInv (ofString "mul64x64") K.«mul64x64» := by sorry
/-- `u256_divmod` (AST line 1754): loop-free. -/
theorem «fb_u256_divmod» : TerminatingFunBoundedOn GuestInv (ofString "u256_divmod") K.«u256_divmod» := by sorry
/-- `u256_mod` (AST line 1794): loop-free. -/
theorem «fb_u256_mod» : TerminatingFunBoundedOn GuestInv (ofString "u256_mod") K.«u256_mod» := by sorry
/-- `u256_mul_full` (AST line 1230): loop-free. -/
theorem «fb_u256_mul_full» : TerminatingFunBoundedOn GuestInv (ofString "u256_mul_full") K.«u256_mul_full» := by sorry
/-- `u256_mulmod` (AST line 1888): loop-free. -/
theorem «fb_u256_mulmod» : TerminatingFunBoundedOn GuestInv (ofString "u256_mulmod") K.«u256_mulmod» := by sorry
/-- `fn_mul` (AST line 6917): loop-free. -/
theorem «fb_fn_mul» : TerminatingFunBoundedOn GuestInv (ofString "fn_mul") K.«fn_mul» := by sorry
/-- `fp_neg` (AST line 5464): loop-free. -/
theorem «fb_fp_neg» : TerminatingFunBoundedOn GuestInv (ofString "fp_neg") K.«fp_neg» := by sorry
/-- `fp_pow` (AST line 6778): #0 CTR. -/
theorem «fb_fp_pow» : TerminatingFunBoundedOn GuestInv (ofString "fp_pow") K.«fp_pow» := by sorry
/-- `fp_sqrt` (AST line 6907): loop-free. -/
theorem «fb_fp_sqrt» : TerminatingFunBoundedOn GuestInv (ofString "fp_sqrt") K.«fp_sqrt» := by sorry
/-- `secp256k1_decompress_r` (AST line 7351): loop-free. -/
theorem «fb_secp256k1_decompress_r» : TerminatingFunBoundedOn GuestInv (ofString "secp256k1_decompress_r") K.«secp256k1_decompress_r» := by sorry
/-- `u256_to_be32` (AST line 2265): loop-free. -/
theorem «fb_u256_to_be32» : TerminatingFunBoundedOn GuestInv (ofString "u256_to_be32") K.«u256_to_be32» := by sorry
/-- `secp256k1_recover` (AST line 7395): loop-free. -/
theorem «fb_secp256k1_recover» : TerminatingFunBoundedOn GuestInv (ofString "secp256k1_recover") K.«secp256k1_recover» := by sorry
/-- `u256_gt` (AST line 921): loop-free. -/
theorem «fb_u256_gt» : TerminatingFunBoundedOn GuestInv (ofString "u256_gt") K.«u256_gt» := by sorry
/-- `recover_authority` (AST line 17625): loop-free. -/
theorem «fb_recover_authority» : TerminatingFunBoundedOn GuestInv (ofString "recover_authority") K.«recover_authority» := by sorry
/-- `u256_fits_word` (AST line 800): loop-free. -/
theorem «fb_u256_fits_word» : TerminatingFunBoundedOn GuestInv (ofString "u256_fits_word") K.«u256_fits_word» := by sorry
/-- `validate_authorization_checks` (AST line 17717): loop-free. -/
theorem «fb_validate_authorization_checks» : TerminatingFunBoundedOn GuestInv (ofString "validate_authorization_checks") K.«validate_authorization_checks» := by sorry
/-- `set_delegation` (AST line 17740): #0 CTR. -/
theorem «fb_set_delegation» : TerminatingFunBoundedOn GuestInv (ofString "set_delegation") K.«set_delegation» := by sorry
/-- `depth0_prepare` (AST line 18772): loop-free. -/
theorem «fb_depth0_prepare» : TerminatingFunBoundedOn GuestInv (ofString "depth0_prepare") K.«depth0_prepare» := by sorry
/-- `frame_mem_alloc` (AST line 110): loop-free. -/
theorem «fb_frame_mem_alloc» : TerminatingFunBoundedOn GuestInv (ofString "frame_mem_alloc") K.«frame_mem_alloc» := by sorry
/-- `frame_mem_mark` (AST line 132): loop-free. -/
theorem «fb_frame_mem_mark» : TerminatingFunBoundedOn GuestInv (ofString "frame_mem_mark") K.«frame_mem_mark» := by sorry
/-- `htab_count` (AST line 5294): loop-free. -/
theorem «fb_htab_count» : TerminatingFunBoundedOn GuestInv (ofString "htab_count") K.«htab_count» := by sorry
/-- `htab_new_scratch` (AST line 4909): loop-free. -/
theorem «fb_htab_new_scratch» : TerminatingFunBoundedOn GuestInv (ofString "htab_new_scratch") K.«htab_new_scratch» := by sorry
/-- `lst_new_scratch` (AST line 13822): loop-free. -/
theorem «fb_lst_new_scratch» : TerminatingFunBoundedOn GuestInv (ofString "lst_new_scratch") K.«lst_new_scratch» := by sorry
/-- `frame_new` (AST line 15370): loop-free. -/
theorem «fb_frame_new» : TerminatingFunBoundedOn GuestInv (ofString "frame_new") K.«frame_new» := by sorry
/-- `frame_open` (AST line 18450): loop-free. -/
theorem «fb_frame_open» : TerminatingFunBoundedOn GuestInv (ofString "frame_open") K.«frame_open» := by sorry
/-- `refill_frame_state_gas` (AST line 15029): loop-free. -/
theorem «fb_refill_frame_state_gas» : TerminatingFunBoundedOn GuestInv (ofString "refill_frame_state_gas") K.«refill_frame_state_gas» := by sorry
/-- `frame_exception` (AST line 18477): loop-free. -/
theorem «fb_frame_exception» : TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.«frame_exception» := by sorry
/-- `log_append` (AST line 16486): loop-free. -/
theorem «fb_log_append» : TerminatingFunBoundedOn GuestInv (ofString "log_append") K.«log_append» := by sorry
/-- `emit_transfer_log` (AST line 17459): loop-free. -/
theorem «fb_emit_transfer_log» : TerminatingFunBoundedOn GuestInv (ofString "emit_transfer_log") K.«emit_transfer_log» := by sorry
/-- `move_ether` (AST line 13597): loop-free. -/
theorem «fb_move_ether» : TerminatingFunBoundedOn GuestInv (ofString "move_ether") K.«move_ether» := by sorry
/-- `precompile_index` (AST line 31482): loop-free. -/
theorem «fb_precompile_index» : TerminatingFunBoundedOn GuestInv (ofString "precompile_index") K.«precompile_index» := by sorry
/-- `fq_mul` (AST line 22338): loop-free. -/
theorem «fb_fq_mul» : TerminatingFunBoundedOn GuestInv (ofString "fq_mul") K.«fq_mul» := by sorry
/-- `fq_from_mont` (AST line 23320): loop-free. -/
theorem «fb_fq_from_mont» : TerminatingFunBoundedOn GuestInv (ofString "fq_from_mont") K.«fq_from_mont» := by sorry
/-- `fq_inv` (AST line 23330): loop-free. -/
theorem «fb_fq_inv» : TerminatingFunBoundedOn GuestInv (ofString "fq_inv") K.«fq_inv» := by sorry
/-- `bn254_g1_to_bytes` (AST line 24508): loop-free. -/
theorem «fb_bn254_g1_to_bytes» : TerminatingFunBoundedOn GuestInv (ofString "bn254_g1_to_bytes") K.«bn254_g1_to_bytes» := by sorry
/-- `fe_set_one` (AST line 23653): loop-free. -/
theorem «fb_fe_set_one» : TerminatingFunBoundedOn GuestInv (ofString "fe_set_one") K.«fe_set_one» := by sorry
/-- `fe_set_zero` (AST line 23641): loop-free. -/
theorem «fb_fe_set_zero» : TerminatingFunBoundedOn GuestInv (ofString "fe_set_zero") K.«fe_set_zero» := by sorry
/-- `ecp_set_inf` (AST line 23667): loop-free. -/
theorem «fb_ecp_set_inf» : TerminatingFunBoundedOn GuestInv (ofString "ecp_set_inf") K.«ecp_set_inf» := by sorry
/-- `fq_add` (AST line 22291): loop-free. -/
theorem «fb_fq_add» : TerminatingFunBoundedOn GuestInv (ofString "fq_add") K.«fq_add» := by sorry
/-- `fq_to_mont` (AST line 23310): loop-free. -/
theorem «fb_fq_to_mont» : TerminatingFunBoundedOn GuestInv (ofString "fq_to_mont") K.«fq_to_mont» := by sorry
/-- `bn254_parse_g1` (AST line 24385): loop-free. -/
theorem «fb_bn254_parse_g1» : TerminatingFunBoundedOn GuestInv (ofString "bn254_parse_g1") K.«bn254_parse_g1» := by sorry
/-- `fq_mul_small` (AST line 23341): #0 CTR. -/
theorem «fb_fq_mul_small» : TerminatingFunBoundedOn GuestInv (ofString "fq_mul_small") K.«fq_mul_small» := by sorry
/-- `fq_sub` (AST line 22307): loop-free. -/
theorem «fb_fq_sub» : TerminatingFunBoundedOn GuestInv (ofString "fq_sub") K.«fq_sub» := by sorry
/-- `fq12_reduce` (AST line 23386): #0 CTR. -/
theorem «fb_fq12_reduce» : TerminatingFunBoundedOn GuestInv (ofString "fq12_reduce") K.«fq12_reduce» := by sorry
/-- `fq12_mul` (AST line 23413): #0 CTR; #1 CTR. -/
theorem «fb_fq12_mul» : TerminatingFunBoundedOn GuestInv (ofString "fq12_mul") K.«fq12_mul» := by sorry
/-- `fq2_mul` (AST line 23362): loop-free. -/
theorem «fb_fq2_mul» : TerminatingFunBoundedOn GuestInv (ofString "fq2_mul") K.«fq2_mul» := by sorry
/-- `fe_mul` (AST line 23502): loop-free. -/
theorem «fb_fe_mul» : TerminatingFunBoundedOn GuestInv (ofString "fe_mul") K.«fe_mul» := by sorry
/-- `fe_mul_small` (AST line 23603): #0 CTR. -/
theorem «fb_fe_mul_small» : TerminatingFunBoundedOn GuestInv (ofString "fe_mul_small") K.«fe_mul_small» := by sorry
/-- `fq12_sqr` (AST line 23456): #0 CTR; #1 CTR. -/
theorem «fb_fq12_sqr» : TerminatingFunBoundedOn GuestInv (ofString "fq12_sqr") K.«fq12_sqr» := by sorry
/-- `fe_sqr` (AST line 23529): loop-free. -/
theorem «fb_fe_sqr» : TerminatingFunBoundedOn GuestInv (ofString "fe_sqr") K.«fe_sqr» := by sorry
/-- `fe_sub` (AST line 23566): #0 CTR. -/
theorem «fb_fe_sub» : TerminatingFunBoundedOn GuestInv (ofString "fe_sub") K.«fe_sub» := by sorry
/-- `ecp_double` (AST line 23694): loop-free. -/
theorem «fb_ecp_double» : TerminatingFunBoundedOn GuestInv (ofString "ecp_double") K.«ecp_double» := by sorry
/-- `fe_eq` (AST line 23631): loop-free. -/
theorem «fb_fe_eq» : TerminatingFunBoundedOn GuestInv (ofString "fe_eq") K.«fe_eq» := by sorry
/-- `fe_is_zero` (AST line 23621): loop-free. -/
theorem «fb_fe_is_zero» : TerminatingFunBoundedOn GuestInv (ofString "fe_is_zero") K.«fe_is_zero» := by sorry
/-- `ecp_add` (AST line 23764): loop-free. -/
theorem «fb_ecp_add» : TerminatingFunBoundedOn GuestInv (ofString "ecp_add") K.«ecp_add» := by sorry
/-- `bn254_g1_add` (AST line 24541): loop-free. -/
theorem «fb_bn254_g1_add» : TerminatingFunBoundedOn GuestInv (ofString "bn254_g1_add") K.«bn254_g1_add» := by sorry
/-- `buffer_read` (AST line 15256): loop-free. -/
theorem «fb_buffer_read» : TerminatingFunBoundedOn GuestInv (ofString "buffer_read") K.«buffer_read» := by sorry
/-- `pre_alt_bn128_add` (AST line 24699): loop-free. -/
theorem «fb_pre_alt_bn128_add» : TerminatingFunBoundedOn GuestInv (ofString "pre_alt_bn128_add") K.«pre_alt_bn128_add» := by sorry
/-- `ecp_mul` (AST line 23874): #0 CTR. -/
theorem «fb_ecp_mul» : TerminatingFunBoundedOn GuestInv (ofString "ecp_mul") K.«ecp_mul» := by sorry
/-- `bn254_g1_mul` (AST line 24574): loop-free. -/
theorem «fb_bn254_g1_mul» : TerminatingFunBoundedOn GuestInv (ofString "bn254_g1_mul") K.«bn254_g1_mul» := by sorry
/-- `pre_alt_bn128_mul` (AST line 24728): loop-free. -/
theorem «fb_pre_alt_bn128_mul» : TerminatingFunBoundedOn GuestInv (ofString "pre_alt_bn128_mul") K.«pre_alt_bn128_mul» := by sorry
/-- `bn254_init` (AST line 22161): loop-free. -/
theorem «fb_bn254_init» : TerminatingFunBoundedOn GuestInv (ofString "bn254_init") K.«bn254_init» := by sorry
/-- `ecp_linefunc` (AST line 23910): loop-free. -/
theorem «fb_ecp_linefunc» : TerminatingFunBoundedOn GuestInv (ofString "ecp_linefunc") K.«ecp_linefunc» := by sorry
/-- `fq_neg` (AST line 22323): loop-free. -/
theorem «fb_fq_neg» : TerminatingFunBoundedOn GuestInv (ofString "fq_neg") K.«fq_neg» := by sorry
/-- `fe_neg` (AST line 23585): #0 CTR. -/
theorem «fb_fe_neg» : TerminatingFunBoundedOn GuestInv (ofString "fe_neg") K.«fe_neg» := by sorry
/-- `fq12_frob` (AST line 24051): #0 CTR. -/
theorem «fb_fq12_frob» : TerminatingFunBoundedOn GuestInv (ofString "fq12_frob") K.«fq12_frob» := by sorry
/-- `bn254_miller_raw` (AST line 24253): #0 CTR. -/
theorem «fb_bn254_miller_raw» : TerminatingFunBoundedOn GuestInv (ofString "bn254_miller_raw") K.«bn254_miller_raw» := by sorry
/-- `fe_add` (AST line 23547): #0 CTR. -/
theorem «fb_fe_add» : TerminatingFunBoundedOn GuestInv (ofString "fe_add") K.«fe_add» := by sorry
/-- `bn254_parse_g2` (AST line 24436): loop-free. -/
theorem «fb_bn254_parse_g2» : TerminatingFunBoundedOn GuestInv (ofString "bn254_parse_g2") K.«bn254_parse_g2» := by sorry
/-- `ecp_is_inf` (AST line 23684): loop-free. -/
theorem «fb_ecp_is_inf» : TerminatingFunBoundedOn GuestInv (ofString "ecp_is_inf") K.«ecp_is_inf» := by sorry
/-- `fq12_cast` (AST line 24033): loop-free. -/
theorem «fb_fq12_cast» : TerminatingFunBoundedOn GuestInv (ofString "fq12_cast") K.«fq12_cast» := by sorry
/-- `fq_poly_deg` (AST line 24084): #0 CTR. -/
theorem «fb_fq_poly_deg» : TerminatingFunBoundedOn GuestInv (ofString "fq_poly_deg") K.«fq_poly_deg» := by sorry
/-- `fq_poly_submul` (AST line 24103): #0 WALK. -/
theorem «fb_fq_poly_submul» : TerminatingFunBoundedOn GuestInv (ofString "fq_poly_submul") K.«fq_poly_submul» := by sorry
/-- `fq12_inv` (AST line 24124): #0 MONO; #1 MONO; #2 CTR; #3 CTR. -/
theorem «fb_fq12_inv» : TerminatingFunBoundedOn GuestInv (ofString "fq12_inv") K.«fq12_inv» := by sorry
/-- `fq12_pow_words` (AST line 24225): #0 CTR. -/
theorem «fb_fq12_pow_words» : TerminatingFunBoundedOn GuestInv (ofString "fq12_pow_words") K.«fq12_pow_words» := by sorry
/-- `fq12_twist` (AST line 23999): #0 CTR. -/
theorem «fb_fq12_twist» : TerminatingFunBoundedOn GuestInv (ofString "fq12_twist") K.«fq12_twist» := by sorry
/-- `bn254_pairing_check` (AST line 24600): #0 CTR. -/
theorem «fb_bn254_pairing_check» : TerminatingFunBoundedOn GuestInv (ofString "bn254_pairing_check") K.«bn254_pairing_check» := by sorry
/-- `pre_alt_bn128_pairing_check` (AST line 24757): loop-free. -/
theorem «fb_pre_alt_bn128_pairing_check» : TerminatingFunBoundedOn GuestInv (ofString "pre_alt_bn128_pairing_check") K.«pre_alt_bn128_pairing_check» := by sorry
/-- `blake2_g` (AST line 20073): loop-free. -/
theorem «fb_blake2_g» : TerminatingFunBoundedOn GuestInv (ofString "blake2_g") K.«blake2_g» := by sorry
/-- `blake2b_f` (AST line 20115): #0 CTR; #1 CTR. -/
theorem «fb_blake2b_f» : TerminatingFunBoundedOn GuestInv (ofString "blake2b_f") K.«blake2b_f» := by sorry
/-- `pre_blake2f` (AST line 31632): #0 CTR; #1 CTR; #2 CTR. -/
theorem «fb_pre_blake2f» : TerminatingFunBoundedOn GuestInv (ofString "pre_blake2f") K.«pre_blake2f» := by sorry
/-- `bls_fp_add_raw` (AST line 26675): loop-free. -/
theorem «fb_bls_fp_add_raw» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_add_raw") K.«bls_fp_add_raw» := by sorry
/-- `bls_fp_sub_raw` (AST line 26703): loop-free. -/
theorem «fb_bls_fp_sub_raw» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_sub_raw") K.«bls_fp_sub_raw» := by sorry
/-- `bls_fp_add` (AST line 26731): loop-free. -/
theorem «fb_bls_fp_add» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_add") K.«bls_fp_add» := by sorry
/-- `bls_fp_eq` (AST line 26607): loop-free. -/
theorem «fb_bls_fp_eq» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_eq") K.«bls_fp_eq» := by sorry
/-- `bls_fp_is_zero` (AST line 26593): loop-free. -/
theorem «fb_bls_fp_is_zero» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_is_zero") K.«bls_fp_is_zero» := by sorry
/-- `bls_fp_mul` (AST line 26791): loop-free. -/
theorem «fb_bls_fp_mul» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_mul") K.«bls_fp_mul» := by sorry
/-- `bls_fp_sqr` (AST line 27550): loop-free. -/
theorem «fb_bls_fp_sqr» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_sqr") K.«bls_fp_sqr» := by sorry
/-- `bls_fp_sub` (AST line 26748): loop-free. -/
theorem «fb_bls_fp_sub» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_sub") K.«bls_fp_sub» := by sorry
/-- `g1_copy` (AST line 28655): loop-free. -/
theorem «fb_g1_copy» : TerminatingFunBoundedOn GuestInv (ofString "g1_copy") K.«g1_copy» := by sorry
/-- `g1_double` (AST line 28689): loop-free. -/
theorem «fb_g1_double» : TerminatingFunBoundedOn GuestInv (ofString "g1_double") K.«g1_double» := by sorry
/-- `g1_set_inf` (AST line 28628): loop-free. -/
theorem «fb_g1_set_inf» : TerminatingFunBoundedOn GuestInv (ofString "g1_set_inf") K.«g1_set_inf» := by sorry
/-- `g1_add` (AST line 28747): loop-free. -/
theorem «fb_g1_add» : TerminatingFunBoundedOn GuestInv (ofString "g1_add") K.«g1_add» := by sorry
/-- `bls_fp_from_be48` (AST line 27719): loop-free. -/
theorem «fb_bls_fp_from_be48» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_from_be48") K.«bls_fp_from_be48» := by sorry
/-- `bls_fp_lt_raw` (AST line 26621): loop-free. -/
theorem «fb_bls_fp_lt_raw» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_lt_raw") K.«bls_fp_lt_raw» := by sorry
/-- `bls_fp_to_mont` (AST line 27560): loop-free. -/
theorem «fb_bls_fp_to_mont» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_to_mont") K.«bls_fp_to_mont» := by sorry
/-- `bls_fp_decode64` (AST line 27751): loop-free. -/
theorem «fb_bls_fp_decode64» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_decode64") K.«bls_fp_decode64» := by sorry
/-- `g1_on_curve` (AST line 28884): loop-free. -/
theorem «fb_g1_on_curve» : TerminatingFunBoundedOn GuestInv (ofString "g1_on_curve") K.«g1_on_curve» := by sorry
/-- `g1_decode` (AST line 28901): loop-free. -/
theorem «fb_g1_decode» : TerminatingFunBoundedOn GuestInv (ofString "g1_decode") K.«g1_decode» := by sorry
/-- `bls_fp_from_mont` (AST line 27570): loop-free. -/
theorem «fb_bls_fp_from_mont» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_from_mont") K.«bls_fp_from_mont» := by sorry
/-- `bls_fp_to_be48` (AST line 27729): loop-free. -/
theorem «fb_bls_fp_to_be48» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_to_be48") K.«bls_fp_to_be48» := by sorry
/-- `bls_fp_encode64` (AST line 27775): loop-free. -/
theorem «fb_bls_fp_encode64» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_encode64") K.«bls_fp_encode64» := by sorry
/-- `bls_fp_shr1` (AST line 27580): loop-free. -/
theorem «fb_bls_fp_shr1» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_shr1") K.«bls_fp_shr1» := by sorry
/-- `bls_fp_half_can` (AST line 27590): loop-free. -/
theorem «fb_bls_fp_half_can» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_half_can") K.«bls_fp_half_can» := by sorry
/-- `bls_fp_inv_raw` (AST line 27605): #0 MONO; #1 MONO; #2 MONO. -/
theorem «fb_bls_fp_inv_raw» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_inv_raw") K.«bls_fp_inv_raw» := by sorry
/-- `bls_fp_inv` (AST line 27658): loop-free. -/
theorem «fb_bls_fp_inv» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_inv") K.«bls_fp_inv» := by sorry
/-- `g1_normalize` (AST line 28861): loop-free. -/
theorem «fb_g1_normalize» : TerminatingFunBoundedOn GuestInv (ofString "g1_normalize") K.«g1_normalize» := by sorry
/-- `g1_encode` (AST line 28933): loop-free. -/
theorem «fb_g1_encode» : TerminatingFunBoundedOn GuestInv (ofString "g1_encode") K.«g1_encode» := by sorry
/-- `bls_g1_add_exec` (AST line 30340): loop-free. -/
theorem «fb_bls_g1_add_exec» : TerminatingFunBoundedOn GuestInv (ofString "bls_g1_add_exec") K.«bls_g1_add_exec» := by sorry
/-- `pre_bls_g1_add` (AST line 31236): loop-free. -/
theorem «fb_pre_bls_g1_add» : TerminatingFunBoundedOn GuestInv (ofString "pre_bls_g1_add") K.«pre_bls_g1_add» := by sorry
/-- `bls_g1_msm_discount` (AST line 31208): loop-free. -/
theorem «fb_bls_g1_msm_discount» : TerminatingFunBoundedOn GuestInv (ofString "bls_g1_msm_discount") K.«bls_g1_msm_discount» := by sorry
/-- `g1_mul` (AST line 28824): #0 CTR. -/
theorem «fb_g1_mul» : TerminatingFunBoundedOn GuestInv (ofString "g1_mul") K.«g1_mul» := by sorry
/-- `g1_is_inf` (AST line 28644): loop-free. -/
theorem «fb_g1_is_inf» : TerminatingFunBoundedOn GuestInv (ofString "g1_is_inf") K.«g1_is_inf» := by sorry
/-- `g1_subgroup_check` (AST line 28953): loop-free. -/
theorem «fb_g1_subgroup_check» : TerminatingFunBoundedOn GuestInv (ofString "g1_subgroup_check") K.«g1_subgroup_check» := by sorry
/-- `bls_g1_msm_exec` (AST line 30370): #0 CTR. -/
theorem «fb_bls_g1_msm_exec» : TerminatingFunBoundedOn GuestInv (ofString "bls_g1_msm_exec") K.«bls_g1_msm_exec» := by sorry
/-- `pre_bls_g1_msm` (AST line 31264): loop-free. -/
theorem «fb_pre_bls_g1_msm» : TerminatingFunBoundedOn GuestInv (ofString "pre_bls_g1_msm") K.«pre_bls_g1_msm» := by sorry
/-- `fp2_add` (AST line 27864): loop-free. -/
theorem «fb_fp2_add» : TerminatingFunBoundedOn GuestInv (ofString "fp2_add") K.«fp2_add» := by sorry
/-- `fp2_copy` (AST line 27791): loop-free. -/
theorem «fb_fp2_copy» : TerminatingFunBoundedOn GuestInv (ofString "fp2_copy") K.«fp2_copy» := by sorry
/-- `fp2_eq` (AST line 27845): loop-free. -/
theorem «fb_fp2_eq» : TerminatingFunBoundedOn GuestInv (ofString "fp2_eq") K.«fp2_eq» := by sorry
/-- `fp2_mul` (AST line 27949): loop-free. -/
theorem «fb_fp2_mul» : TerminatingFunBoundedOn GuestInv (ofString "fp2_mul") K.«fp2_mul» := by sorry
/-- `fp2_sqr` (AST line 27977): loop-free. -/
theorem «fb_fp2_sqr» : TerminatingFunBoundedOn GuestInv (ofString "fp2_sqr") K.«fp2_sqr» := by sorry
/-- `fp2_sub` (AST line 27884): loop-free. -/
theorem «fb_fp2_sub» : TerminatingFunBoundedOn GuestInv (ofString "fp2_sub") K.«fp2_sub» := by sorry
/-- `g2_copy` (AST line 28996): loop-free. -/
theorem «fb_g2_copy» : TerminatingFunBoundedOn GuestInv (ofString "g2_copy") K.«g2_copy» := by sorry
/-- `g2_double` (AST line 29026): loop-free. -/
theorem «fb_g2_double» : TerminatingFunBoundedOn GuestInv (ofString "g2_double") K.«g2_double» := by sorry
/-- `fp2_is_zero` (AST line 27829): loop-free. -/
theorem «fb_fp2_is_zero» : TerminatingFunBoundedOn GuestInv (ofString "fp2_is_zero") K.«fp2_is_zero» := by sorry
/-- `g2_is_inf` (AST line 28986): loop-free. -/
theorem «fb_g2_is_inf» : TerminatingFunBoundedOn GuestInv (ofString "g2_is_inf") K.«g2_is_inf» := by sorry
/-- `fp2_set_one` (AST line 27815): loop-free. -/
theorem «fb_fp2_set_one» : TerminatingFunBoundedOn GuestInv (ofString "fp2_set_one") K.«fp2_set_one» := by sorry
/-- `fp2_set_zero` (AST line 27803): loop-free. -/
theorem «fb_fp2_set_zero» : TerminatingFunBoundedOn GuestInv (ofString "fp2_set_zero") K.«fp2_set_zero» := by sorry
/-- `g2_set_inf` (AST line 28970): loop-free. -/
theorem «fb_g2_set_inf» : TerminatingFunBoundedOn GuestInv (ofString "g2_set_inf") K.«g2_set_inf» := by sorry
/-- `g2_add` (AST line 29109): loop-free. -/
theorem «fb_g2_add» : TerminatingFunBoundedOn GuestInv (ofString "g2_add") K.«g2_add» := by sorry
/-- `g2_on_curve` (AST line 29276): loop-free. -/
theorem «fb_g2_on_curve» : TerminatingFunBoundedOn GuestInv (ofString "g2_on_curve") K.«g2_on_curve» := by sorry
/-- `g2_decode` (AST line 29300): loop-free. -/
theorem «fb_g2_decode» : TerminatingFunBoundedOn GuestInv (ofString "g2_decode") K.«g2_decode» := by sorry
/-- `bls_fp_neg` (AST line 26765): loop-free. -/
theorem «fb_bls_fp_neg» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_neg") K.«bls_fp_neg» := by sorry
/-- `fp2_inv` (AST line 28035): loop-free. -/
theorem «fb_fp2_inv» : TerminatingFunBoundedOn GuestInv (ofString "fp2_inv") K.«fp2_inv» := by sorry
/-- `g2_normalize` (AST line 29247): loop-free. -/
theorem «fb_g2_normalize» : TerminatingFunBoundedOn GuestInv (ofString "g2_normalize") K.«g2_normalize» := by sorry
/-- `g2_encode` (AST line 29343): loop-free. -/
theorem «fb_g2_encode» : TerminatingFunBoundedOn GuestInv (ofString "g2_encode") K.«g2_encode» := by sorry
/-- `bls_g2_add_exec` (AST line 30416): loop-free. -/
theorem «fb_bls_g2_add_exec» : TerminatingFunBoundedOn GuestInv (ofString "bls_g2_add_exec") K.«bls_g2_add_exec» := by sorry
/-- `pre_bls_g2_add` (AST line 31300): loop-free. -/
theorem «fb_pre_bls_g2_add» : TerminatingFunBoundedOn GuestInv (ofString "pre_bls_g2_add") K.«pre_bls_g2_add» := by sorry
/-- `bls_g2_msm_discount` (AST line 31222): loop-free. -/
theorem «fb_bls_g2_msm_discount» : TerminatingFunBoundedOn GuestInv (ofString "bls_g2_msm_discount") K.«bls_g2_msm_discount» := by sorry
/-- `g2_mul` (AST line 29213): #0 CTR. -/
theorem «fb_g2_mul» : TerminatingFunBoundedOn GuestInv (ofString "g2_mul") K.«g2_mul» := by sorry
/-- `g2_subgroup_check` (AST line 29367): loop-free. -/
theorem «fb_g2_subgroup_check» : TerminatingFunBoundedOn GuestInv (ofString "g2_subgroup_check") K.«g2_subgroup_check» := by sorry
/-- `bls_g2_msm_exec` (AST line 30446): #0 CTR. -/
theorem «fb_bls_g2_msm_exec» : TerminatingFunBoundedOn GuestInv (ofString "bls_g2_msm_exec") K.«bls_g2_msm_exec» := by sorry
/-- `pre_bls_g2_msm` (AST line 31328): loop-free. -/
theorem «fb_pre_bls_g2_msm» : TerminatingFunBoundedOn GuestInv (ofString "pre_bls_g2_msm") K.«pre_bls_g2_msm» := by sorry
/-- `iso_horner_fp2` (AST line 30055): #0 CTR. -/
theorem «fb_iso_horner_fp2» : TerminatingFunBoundedOn GuestInv (ofString "iso_horner_fp2") K.«iso_horner_fp2» := by sorry
/-- `iso_map_g2` (AST line 30084): loop-free. -/
theorem «fb_iso_map_g2» : TerminatingFunBoundedOn GuestInv (ofString "iso_map_g2") K.«iso_map_g2» := by sorry
/-- `fp2_neg` (AST line 27904): loop-free. -/
theorem «fb_fp2_neg» : TerminatingFunBoundedOn GuestInv (ofString "fp2_neg") K.«fp2_neg» := by sorry
/-- `bls_fp_sgn0` (AST line 27696): loop-free. -/
theorem «fb_bls_fp_sgn0» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_sgn0") K.«bls_fp_sgn0» := by sorry
/-- `fp2_sgn0` (AST line 28096): loop-free. -/
theorem «fb_fp2_sgn0» : TerminatingFunBoundedOn GuestInv (ofString "fp2_sgn0") K.«fp2_sgn0» := by sorry
/-- `fp2_pow` (AST line 28059): #0 CTR. -/
theorem «fb_fp2_pow» : TerminatingFunBoundedOn GuestInv (ofString "fp2_pow") K.«fp2_pow» := by sorry
/-- `swu_sqrt_division_fp2` (AST line 29879): #0 CTR; #1 CTR. -/
theorem «fb_swu_sqrt_division_fp2» : TerminatingFunBoundedOn GuestInv (ofString "swu_sqrt_division_fp2") K.«swu_sqrt_division_fp2» := by sorry
/-- `swu_g2` (AST line 29940): #0 CTR. -/
theorem «fb_swu_g2» : TerminatingFunBoundedOn GuestInv (ofString "swu_g2") K.«swu_g2» := by sorry
/-- `map_fp2_to_g2` (AST line 30128): loop-free. -/
theorem «fb_map_fp2_to_g2» : TerminatingFunBoundedOn GuestInv (ofString "map_fp2_to_g2") K.«map_fp2_to_g2» := by sorry
/-- `bls_map_fp2_to_g2_exec` (AST line 30581): loop-free. -/
theorem «fb_bls_map_fp2_to_g2_exec» : TerminatingFunBoundedOn GuestInv (ofString "bls_map_fp2_to_g2_exec") K.«bls_map_fp2_to_g2_exec» := by sorry
/-- `pre_bls_map_fp2_to_g2` (AST line 31426): loop-free. -/
theorem «fb_pre_bls_map_fp2_to_g2» : TerminatingFunBoundedOn GuestInv (ofString "pre_bls_map_fp2_to_g2") K.«pre_bls_map_fp2_to_g2» := by sorry
/-- `iso_horner_fp` (AST line 29789): #0 CTR. -/
theorem «fb_iso_horner_fp» : TerminatingFunBoundedOn GuestInv (ofString "iso_horner_fp") K.«iso_horner_fp» := by sorry
/-- `iso_map_g1` (AST line 29812): #0 CTR. -/
theorem «fb_iso_map_g1» : TerminatingFunBoundedOn GuestInv (ofString "iso_map_g1") K.«iso_map_g1» := by sorry
/-- `bls_fp_pow` (AST line 27669): #0 CTR. -/
theorem «fb_bls_fp_pow» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_pow") K.«bls_fp_pow» := by sorry
/-- `swu_sqrt_division_fp` (AST line 29697): loop-free. -/
theorem «fb_swu_sqrt_division_fp» : TerminatingFunBoundedOn GuestInv (ofString "swu_sqrt_division_fp") K.«swu_sqrt_division_fp» := by sorry
/-- `swu_g1` (AST line 29719): loop-free. -/
theorem «fb_swu_g1» : TerminatingFunBoundedOn GuestInv (ofString "swu_g1") K.«swu_g1» := by sorry
/-- `map_fp_to_g1` (AST line 29859): loop-free. -/
theorem «fb_map_fp_to_g1» : TerminatingFunBoundedOn GuestInv (ofString "map_fp_to_g1") K.«map_fp_to_g1» := by sorry
/-- `bls_map_fp_to_g1_exec` (AST line 30554): loop-free. -/
theorem «fb_bls_map_fp_to_g1_exec» : TerminatingFunBoundedOn GuestInv (ofString "bls_map_fp_to_g1_exec") K.«bls_map_fp_to_g1_exec» := by sorry
/-- `pre_bls_map_fp_to_g1` (AST line 31398): loop-free. -/
theorem «fb_pre_bls_map_fp_to_g1» : TerminatingFunBoundedOn GuestInv (ofString "pre_bls_map_fp_to_g1") K.«pre_bls_map_fp_to_g1» := by sorry
/-- `fp6_copy` (AST line 28118): loop-free. -/
theorem «fb_fp6_copy» : TerminatingFunBoundedOn GuestInv (ofString "fp6_copy") K.«fp6_copy» := by sorry
/-- `fp6_neg` (AST line 28190): loop-free. -/
theorem «fb_fp6_neg» : TerminatingFunBoundedOn GuestInv (ofString "fp6_neg") K.«fp6_neg» := by sorry
/-- `fp12_conj` (AST line 28429): loop-free. -/
theorem «fb_fp12_conj» : TerminatingFunBoundedOn GuestInv (ofString "fp12_conj") K.«fp12_conj» := by sorry
/-- `fp12_copy` (AST line 28339): loop-free. -/
theorem «fb_fp12_copy» : TerminatingFunBoundedOn GuestInv (ofString "fp12_copy") K.«fp12_copy» := by sorry
/-- `fp6_add` (AST line 28158): loop-free. -/
theorem «fb_fp6_add» : TerminatingFunBoundedOn GuestInv (ofString "fp6_add") K.«fp6_add» := by sorry
/-- `fp2_mul_xi` (AST line 27999): loop-free. -/
theorem «fb_fp2_mul_xi» : TerminatingFunBoundedOn GuestInv (ofString "fp2_mul_xi") K.«fp2_mul_xi» := by sorry
/-- `fp6_mul` (AST line 28206): loop-free. -/
theorem «fb_fp6_mul» : TerminatingFunBoundedOn GuestInv (ofString "fp6_mul") K.«fp6_mul» := by sorry
/-- `fp6_mul_v` (AST line 28255): loop-free. -/
theorem «fb_fp6_mul_v» : TerminatingFunBoundedOn GuestInv (ofString "fp6_mul_v") K.«fp6_mul_v» := by sorry
/-- `fp6_sub` (AST line 28174): loop-free. -/
theorem «fb_fp6_sub» : TerminatingFunBoundedOn GuestInv (ofString "fp6_sub") K.«fp6_sub» := by sorry
/-- `fp12_mul` (AST line 28382): loop-free. -/
theorem «fb_fp12_mul» : TerminatingFunBoundedOn GuestInv (ofString "fp12_mul") K.«fp12_mul» := by sorry
/-- `fp6_set_one` (AST line 28142): loop-free. -/
theorem «fb_fp6_set_one» : TerminatingFunBoundedOn GuestInv (ofString "fp6_set_one") K.«fp6_set_one» := by sorry
/-- `fp6_set_zero` (AST line 28130): loop-free. -/
theorem «fb_fp6_set_zero» : TerminatingFunBoundedOn GuestInv (ofString "fp6_set_zero") K.«fp6_set_zero» := by sorry
/-- `fp12_set_one` (AST line 28351): loop-free. -/
theorem «fb_fp12_set_one» : TerminatingFunBoundedOn GuestInv (ofString "fp12_set_one") K.«fp12_set_one» := by sorry
/-- `fp12_pow_absx` (AST line 28508): #0 CTR. -/
theorem «fb_fp12_pow_absx» : TerminatingFunBoundedOn GuestInv (ofString "fp12_pow_absx") K.«fp12_pow_absx» := by sorry
/-- `fp12_exp_x` (AST line 28545): loop-free. -/
theorem «fb_fp12_exp_x» : TerminatingFunBoundedOn GuestInv (ofString "fp12_exp_x") K.«fp12_exp_x» := by sorry
/-- `fp2_conj` (AST line 27932): loop-free. -/
theorem «fb_fp2_conj» : TerminatingFunBoundedOn GuestInv (ofString "fp2_conj") K.«fp2_conj» := by sorry
/-- `fp12_frob` (AST line 28476): loop-free. -/
theorem «fb_fp12_frob» : TerminatingFunBoundedOn GuestInv (ofString "fp12_frob") K.«fp12_frob» := by sorry
/-- `fp6_inv` (AST line 28277): loop-free. -/
theorem «fb_fp6_inv» : TerminatingFunBoundedOn GuestInv (ofString "fp6_inv") K.«fp6_inv» := by sorry
/-- `fp12_inv` (AST line 28443): loop-free. -/
theorem «fb_fp12_inv» : TerminatingFunBoundedOn GuestInv (ofString "fp12_inv") K.«fp12_inv» := by sorry
/-- `fp12_final_exp` (AST line 28559): loop-free. -/
theorem «fb_fp12_final_exp» : TerminatingFunBoundedOn GuestInv (ofString "fp12_final_exp") K.«fp12_final_exp» := by sorry
/-- `fp12_is_one` (AST line 28365): loop-free. -/
theorem «fb_fp12_is_one» : TerminatingFunBoundedOn GuestInv (ofString "fp12_is_one") K.«fp12_is_one» := by sorry
/-- `pair_addition_step` (AST line 29484): loop-free. -/
theorem «fb_pair_addition_step» : TerminatingFunBoundedOn GuestInv (ofString "pair_addition_step") K.«pair_addition_step» := by sorry
/-- `pair_doubling_step` (AST line 29384): loop-free. -/
theorem «fb_pair_doubling_step» : TerminatingFunBoundedOn GuestInv (ofString "pair_doubling_step") K.«pair_doubling_step» := by sorry
/-- `fp2_scale` (AST line 28017): loop-free. -/
theorem «fb_fp2_scale» : TerminatingFunBoundedOn GuestInv (ofString "fp2_scale") K.«fp2_scale» := by sorry
/-- `pair_ell` (AST line 29595): loop-free. -/
theorem «fb_pair_ell» : TerminatingFunBoundedOn GuestInv (ofString "pair_ell") K.«pair_ell» := by sorry
/-- `pair_miller_loop` (AST line 29619): #0 CTR. -/
theorem «fb_pair_miller_loop» : TerminatingFunBoundedOn GuestInv (ofString "pair_miller_loop") K.«pair_miller_loop» := by sorry
/-- `pair_accumulate` (AST line 29661): loop-free. -/
theorem «fb_pair_accumulate» : TerminatingFunBoundedOn GuestInv (ofString "pair_accumulate") K.«pair_accumulate» := by sorry
/-- `bls_pairing_exec` (AST line 30492): #0 CTR. -/
theorem «fb_bls_pairing_exec» : TerminatingFunBoundedOn GuestInv (ofString "bls_pairing_exec") K.«bls_pairing_exec» := by sorry
/-- `pre_bls_pairing` (AST line 31364): loop-free. -/
theorem «fb_pre_bls_pairing» : TerminatingFunBoundedOn GuestInv (ofString "pre_bls_pairing") K.«pre_bls_pairing» := by sorry
/-- `secp256k1_address_of_point` (AST line 7465): loop-free. -/
theorem «fb_secp256k1_address_of_point» : TerminatingFunBoundedOn GuestInv (ofString "secp256k1_address_of_point") K.«secp256k1_address_of_point» := by sorry
/-- `secp256k1_ecrecover` (AST line 7483): loop-free. -/
theorem «fb_secp256k1_ecrecover» : TerminatingFunBoundedOn GuestInv (ofString "secp256k1_ecrecover") K.«secp256k1_ecrecover» := by sorry
/-- `pre_ecrecover` (AST line 31556): loop-free. -/
theorem «fb_pre_ecrecover» : TerminatingFunBoundedOn GuestInv (ofString "pre_ecrecover") K.«pre_ecrecover» := by sorry
/-- `pre_identity` (AST line 31515): loop-free. -/
theorem «fb_pre_identity» : TerminatingFunBoundedOn GuestInv (ofString "pre_identity") K.«pre_identity» := by sorry
/-- `bls_fp_is_high` (AST line 27707): loop-free. -/
theorem «fb_bls_fp_is_high» : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_is_high") K.«bls_fp_is_high» := by sorry
/-- `kzg_decompress_g1` (AST line 30148): loop-free. -/
theorem «fb_kzg_decompress_g1» : TerminatingFunBoundedOn GuestInv (ofString "kzg_decompress_g1") K.«kzg_decompress_g1» := by sorry
/-- `kzg_load_g1` (AST line 30216): loop-free. -/
theorem «fb_kzg_load_g1» : TerminatingFunBoundedOn GuestInv (ofString "kzg_load_g1") K.«kzg_load_g1» := by sorry
/-- `g2_neg` (AST line 29008): loop-free. -/
theorem «fb_g2_neg» : TerminatingFunBoundedOn GuestInv (ofString "g2_neg") K.«g2_neg» := by sorry
/-- `kzg_neg_scalar` (AST line 30245): loop-free. -/
theorem «fb_kzg_neg_scalar» : TerminatingFunBoundedOn GuestInv (ofString "kzg_neg_scalar") K.«kzg_neg_scalar» := by sorry
/-- `kzg_verify` (AST line 30267): loop-free. -/
theorem «fb_kzg_verify» : TerminatingFunBoundedOn GuestInv (ofString "kzg_verify") K.«kzg_verify» := by sorry
/-- `kzg_point_evaluation_exec` (AST line 30611): loop-free. -/
theorem «fb_kzg_point_evaluation_exec» : TerminatingFunBoundedOn GuestInv (ofString "kzg_point_evaluation_exec") K.«kzg_point_evaluation_exec» := by sorry
/-- `pre_kzg_point_evaluation` (AST line 31454): loop-free. -/
theorem «fb_pre_kzg_point_evaluation» : TerminatingFunBoundedOn GuestInv (ofString "pre_kzg_point_evaluation") K.«pre_kzg_point_evaluation» := by sorry
/-- `be_top_bit` (AST line 20407): #0 CTR. -/
theorem «fb_be_top_bit» : TerminatingFunBoundedOn GuestInv (ofString "be_top_bit") K.«be_top_bit» := by sorry
/-- `bn_from_be` (AST line 20170): #0 CTR; #1 CTR. -/
theorem «fb_bn_from_be» : TerminatingFunBoundedOn GuestInv (ofString "bn_from_be") K.«bn_from_be» := by sorry
/-- `bn_divmnu` (AST line 20253): #0 CTR; #1 CTR; #2 CTR; #3 CTR; #4 RO(3); #5 CTR; #6 CTR; #7 CTR; #8 CTR. -/
theorem «fb_bn_divmnu» : TerminatingFunBoundedOn GuestInv (ofString "bn_divmnu") K.«bn_divmnu» := by sorry
/-- `bn_mod` (AST line 20386): loop-free. -/
theorem «fb_bn_mod» : TerminatingFunBoundedOn GuestInv (ofString "bn_mod") K.«bn_mod» := by sorry
/-- `bn_mul` (AST line 20218): #0 CTR; #1 CTR; #2 CTR. -/
theorem «fb_bn_mul» : TerminatingFunBoundedOn GuestInv (ofString "bn_mul") K.«bn_mul» := by sorry
/-- `bn_to_be` (AST line 20196): #0 CTR. -/
theorem «fb_bn_to_be» : TerminatingFunBoundedOn GuestInv (ofString "bn_to_be") K.«bn_to_be» := by sorry
/-- `modexp` (AST line 20427): #0 CTR. -/
theorem «fb_modexp» : TerminatingFunBoundedOn GuestInv (ofString "modexp") K.«modexp» := by sorry
/-- `modexp_gas` (AST line 31689): loop-free. -/
theorem «fb_modexp_gas» : TerminatingFunBoundedOn GuestInv (ofString "modexp_gas") K.«modexp_gas» := by sorry
/-- `sat_word` (AST line 14833): loop-free. -/
theorem «fb_sat_word» : TerminatingFunBoundedOn GuestInv (ofString "sat_word") K.«sat_word» := by sorry
/-- `pre_modexp` (AST line 31725): loop-free. -/
theorem «fb_pre_modexp» : TerminatingFunBoundedOn GuestInv (ofString "pre_modexp") K.«pre_modexp» := by sorry
/-- `p256_fp_add` (AST line 20490): loop-free. -/
theorem «fb_p256_fp_add» : TerminatingFunBoundedOn GuestInv (ofString "p256_fp_add") K.«p256_fp_add» := by sorry
/-- `p256_fp_reduce` (AST line 20527): loop-free. -/
theorem «fb_p256_fp_reduce» : TerminatingFunBoundedOn GuestInv (ofString "p256_fp_reduce") K.«p256_fp_reduce» := by sorry
/-- `p256_fp_mul` (AST line 20542): #0 MONO; #1 MONO. -/
theorem «fb_p256_fp_mul» : TerminatingFunBoundedOn GuestInv (ofString "p256_fp_mul") K.«p256_fp_mul» := by sorry
/-- `p256_fp_sqr` (AST line 21184): #0 MONO; #1 MONO. -/
theorem «fb_p256_fp_sqr» : TerminatingFunBoundedOn GuestInv (ofString "p256_fp_sqr") K.«p256_fp_sqr» := by sorry
/-- `p256_fp_sub` (AST line 20511): loop-free. -/
theorem «fb_p256_fp_sub» : TerminatingFunBoundedOn GuestInv (ofString "p256_fp_sub") K.«p256_fp_sub» := by sorry
/-- `p256_set_infinity` (AST line 21782): loop-free. -/
theorem «fb_p256_set_infinity» : TerminatingFunBoundedOn GuestInv (ofString "p256_set_infinity") K.«p256_set_infinity» := by sorry
/-- `p256_ec_double` (AST line 21814): loop-free. -/
theorem «fb_p256_ec_double» : TerminatingFunBoundedOn GuestInv (ofString "p256_ec_double") K.«p256_ec_double» := by sorry
/-- `p256_set_affine` (AST line 21798): loop-free. -/
theorem «fb_p256_set_affine» : TerminatingFunBoundedOn GuestInv (ofString "p256_set_affine") K.«p256_set_affine» := by sorry
/-- `p256_ec_add_affine` (AST line 21880): loop-free. -/
theorem «fb_p256_ec_add_affine» : TerminatingFunBoundedOn GuestInv (ofString "p256_ec_add_affine") K.«p256_ec_add_affine» := by sorry
/-- `p256_ec_mul2` (AST line 21944): #0 CTR. -/
theorem «fb_p256_ec_mul2» : TerminatingFunBoundedOn GuestInv (ofString "p256_ec_mul2") K.«p256_ec_mul2» := by sorry
/-- `p256_on_curve` (AST line 22001): loop-free. -/
theorem «fb_p256_on_curve» : TerminatingFunBoundedOn GuestInv (ofString "p256_on_curve") K.«p256_on_curve» := by sorry
/-- `p256_verify` (AST line 22022): loop-free. -/
theorem «fb_p256_verify» : TerminatingFunBoundedOn GuestInv (ofString "p256_verify") K.«p256_verify» := by sorry
/-- `pre_p256verify` (AST line 22115): loop-free. -/
theorem «fb_pre_p256verify» : TerminatingFunBoundedOn GuestInv (ofString "pre_p256verify") K.«pre_p256verify» := by sorry
/-- `rmd_f` (AST line 19800): loop-free. -/
theorem «fb_rmd_f» : TerminatingFunBoundedOn GuestInv (ofString "rmd_f") K.«rmd_f» := by sorry
/-- `rmd_k` (AST line 19826): loop-free. -/
theorem «fb_rmd_k» : TerminatingFunBoundedOn GuestInv (ofString "rmd_k") K.«rmd_k» := by sorry
/-- `rmd_kp` (AST line 19852): loop-free. -/
theorem «fb_rmd_kp» : TerminatingFunBoundedOn GuestInv (ofString "rmd_kp") K.«rmd_kp» := by sorry
/-- `ripemd160_block` (AST line 19878): #0 CTR; #1 CTR. -/
theorem «fb_ripemd160_block» : TerminatingFunBoundedOn GuestInv (ofString "ripemd160_block") K.«ripemd160_block» := by sorry
/-- `ripemd160` (AST line 19955): #0 WALK; #1 CTR. -/
theorem «fb_ripemd160» : TerminatingFunBoundedOn GuestInv (ofString "ripemd160") K.«ripemd160» := by sorry
/-- `pre_ripemd160` (AST line 31608): loop-free. -/
theorem «fb_pre_ripemd160» : TerminatingFunBoundedOn GuestInv (ofString "pre_ripemd160") K.«pre_ripemd160» := by sorry
/-- `pre_sha256` (AST line 31534): loop-free. -/
theorem «fb_pre_sha256» : TerminatingFunBoundedOn GuestInv (ofString "pre_sha256") K.«pre_sha256» := by sorry
/-- `run_precompile` (AST line 31795): loop-free. -/
theorem «fb_run_precompile» : TerminatingFunBoundedOn GuestInv (ofString "run_precompile") K.«run_precompile» := by sorry
/-- `frame_prologue` (AST line 18499): loop-free. -/
theorem «fb_frame_prologue» : TerminatingFunBoundedOn GuestInv (ofString "frame_prologue") K.«frame_prologue» := by sorry
/-- `frame_start` (AST line 18539): loop-free. -/
theorem «fb_frame_start» : TerminatingFunBoundedOn GuestInv (ofString "frame_start") K.«frame_start» := by sorry
/-- `credit_state_gas_refund` (AST line 15000): loop-free. -/
theorem «fb_credit_state_gas_refund» : TerminatingFunBoundedOn GuestInv (ofString "credit_state_gas_refund") K.«credit_state_gas_refund» := by sorry
/-- `incorporate_child_on_error` (AST line 18941): loop-free. -/
theorem «fb_incorporate_child_on_error» : TerminatingFunBoundedOn GuestInv (ofString "incorporate_child_on_error") K.«incorporate_child_on_error» := by sorry
/-- `incorporate_child_on_success` (AST line 18957): #0 CTR. -/
theorem «fb_incorporate_child_on_success» : TerminatingFunBoundedOn GuestInv (ofString "incorporate_child_on_success") K.«incorporate_child_on_success» := by sorry
/-- `pc_add` (AST line 15437): loop-free. -/
theorem «fb_pc_add» : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add» := by sorry
/-- `set_retdata` (AST line 19064): loop-free. -/
theorem «fb_set_retdata» : TerminatingFunBoundedOn GuestInv (ofString "set_retdata") K.«set_retdata» := by sorry
/-- `stack_push` (AST line 15065): loop-free. -/
theorem «fb_stack_push» : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push» := by sorry
/-- `state_restore` (AST line 12903): #0 GCTR. -/
theorem «fb_state_restore» : TerminatingFunBoundedOn GuestInv (ofString "state_restore") K.«state_restore» := by sorry
/-- `frame_epilogue` (AST line 18558): loop-free. -/
theorem «fb_frame_epilogue» : TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.«frame_epilogue» := by sorry
/-- `stack_pop` (AST line 15046): loop-free. -/
theorem «fb_stack_pop» : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop» := by sorry
/-- `op_add` (AST line 15525): loop-free. -/
theorem «fb_op_add» : TerminatingFunBoundedOn GuestInv (ofString "op_add") K.«op_add» := by sorry
/-- `u256_addmod` (AST line 1861): loop-free. -/
theorem «fb_u256_addmod» : TerminatingFunBoundedOn GuestInv (ofString "u256_addmod") K.«u256_addmod» := by sorry
/-- `op_addmod` (AST line 15658): loop-free. -/
theorem «fb_op_addmod» : TerminatingFunBoundedOn GuestInv (ofString "op_addmod") K.«op_addmod» := by sorry
/-- `op_address` (AST line 16734): loop-free. -/
theorem «fb_op_address» : TerminatingFunBoundedOn GuestInv (ofString "op_address") K.«op_address» := by sorry
/-- `op_and` (AST line 15851): loop-free. -/
theorem «fb_op_and» : TerminatingFunBoundedOn GuestInv (ofString "op_and") K.«op_and» := by sorry
/-- `to_address_masked` (AST line 14889): loop-free. -/
theorem «fb_to_address_masked» : TerminatingFunBoundedOn GuestInv (ofString "to_address_masked") K.«to_address_masked» := by sorry
/-- `warm_after_charge` (AST line 15511): loop-free. -/
theorem «fb_warm_after_charge» : TerminatingFunBoundedOn GuestInv (ofString "warm_after_charge") K.«warm_after_charge» := by sorry
/-- `op_balance` (AST line 16751): loop-free. -/
theorem «fb_op_balance» : TerminatingFunBoundedOn GuestInv (ofString "op_balance") K.«op_balance» := by sorry
/-- `block_env` (AST line 17115): loop-free. -/
theorem «fb_block_env» : TerminatingFunBoundedOn GuestInv (ofString "block_env") K.«block_env» := by sorry
/-- `op_basefee` (AST line 17125): loop-free. -/
theorem «fb_op_basefee» : TerminatingFunBoundedOn GuestInv (ofString "op_basefee") K.«op_basefee» := by sorry
/-- `u256_div` (AST line 1783): loop-free. -/
theorem «fb_u256_div» : TerminatingFunBoundedOn GuestInv (ofString "u256_div") K.«u256_div» := by sorry
/-- `u256_from_word` (AST line 780): loop-free. -/
theorem «fb_u256_from_word» : TerminatingFunBoundedOn GuestInv (ofString "u256_from_word") K.«u256_from_word» := by sorry
/-- `u256_mul` (AST line 1150): loop-free. -/
theorem «fb_u256_mul» : TerminatingFunBoundedOn GuestInv (ofString "u256_mul") K.«u256_mul» := by sorry
/-- `taylor_exponential` (AST line 9511): #0 MONO. -/
theorem «fb_taylor_exponential» : TerminatingFunBoundedOn GuestInv (ofString "taylor_exponential") K.«taylor_exponential» := by sorry
/-- `calculate_blob_gas_price` (AST line 9550): loop-free. -/
theorem «fb_calculate_blob_gas_price» : TerminatingFunBoundedOn GuestInv (ofString "calculate_blob_gas_price") K.«calculate_blob_gas_price» := by sorry
/-- `op_blobbasefee` (AST line 17165): loop-free. -/
theorem «fb_op_blobbasefee» : TerminatingFunBoundedOn GuestInv (ofString "op_blobbasefee") K.«op_blobbasefee» := by sorry
/-- `op_blobhash` (AST line 17142): loop-free. -/
theorem «fb_op_blobhash» : TerminatingFunBoundedOn GuestInv (ofString "op_blobhash") K.«op_blobhash» := by sorry
/-- `track_ancestor_access` (AST line 13771): loop-free. -/
theorem «fb_track_ancestor_access» : TerminatingFunBoundedOn GuestInv (ofString "track_ancestor_access") K.«track_ancestor_access» := by sorry
/-- `op_blockhash` (AST line 17183): loop-free. -/
theorem «fb_op_blockhash» : TerminatingFunBoundedOn GuestInv (ofString "op_blockhash") K.«op_blockhash» := by sorry
/-- `stack_push_word` (AST line 15103): loop-free. -/
theorem «fb_stack_push_word» : TerminatingFunBoundedOn GuestInv (ofString "stack_push_word") K.«stack_push_word» := by sorry
/-- `u256_byte` (AST line 2197): loop-free. -/
theorem «fb_u256_byte» : TerminatingFunBoundedOn GuestInv (ofString "u256_byte") K.«u256_byte» := by sorry
/-- `op_byte` (AST line 15922): loop-free. -/
theorem «fb_op_byte» : TerminatingFunBoundedOn GuestInv (ofString "op_byte") K.«op_byte» := by sorry
/-- `calculate_delegation_cost` (AST line 17693): loop-free. -/
theorem «fb_calculate_delegation_cost» : TerminatingFunBoundedOn GuestInv (ofString "calculate_delegation_cost") K.«calculate_delegation_cost» := by sorry
/-- `calculate_message_call_gas` (AST line 19328): loop-free. -/
theorem «fb_calculate_message_call_gas» : TerminatingFunBoundedOn GuestInv (ofString "calculate_message_call_gas") K.«calculate_message_call_gas» := by sorry
/-- `extend_memory` (AST line 15206): loop-free. -/
theorem «fb_extend_memory» : TerminatingFunBoundedOn GuestInv (ofString "extend_memory") K.«extend_memory» := by sorry
/-- `memory_gas_cost` (AST line 15129): loop-free. -/
theorem «fb_memory_gas_cost» : TerminatingFunBoundedOn GuestInv (ofString "memory_gas_cost") K.«memory_gas_cost» := by sorry
/-- `extend_memory_cost1` (AST line 15146): loop-free. -/
theorem «fb_extend_memory_cost1» : TerminatingFunBoundedOn GuestInv (ofString "extend_memory_cost1") K.«extend_memory_cost1» := by sorry
/-- `extend_memory_cost2` (AST line 15181): loop-free. -/
theorem «fb_extend_memory_cost2» : TerminatingFunBoundedOn GuestInv (ofString "extend_memory_cost2") K.«extend_memory_cost2» := by sorry
/-- `msg_new_scratch` (AST line 15357): loop-free. -/
theorem «fb_msg_new_scratch» : TerminatingFunBoundedOn GuestInv (ofString "msg_new_scratch") K.«msg_new_scratch» := by sorry
/-- `child_message` (AST line 19009): loop-free. -/
theorem «fb_child_message» : TerminatingFunBoundedOn GuestInv (ofString "child_message") K.«child_message» := by sorry
/-- `state_snapshot` (AST line 12893): loop-free. -/
theorem «fb_state_snapshot» : TerminatingFunBoundedOn GuestInv (ofString "state_snapshot") K.«state_snapshot» := by sorry
/-- `start_child` (AST line 18703): loop-free. -/
theorem «fb_start_child» : TerminatingFunBoundedOn GuestInv (ofString "start_child") K.«start_child» := by sorry
/-- `generic_call` (AST line 19294): loop-free. -/
theorem «fb_generic_call» : TerminatingFunBoundedOn GuestInv (ofString "generic_call") K.«generic_call» := by sorry
/-- `op_call` (AST line 19358): loop-free. -/
theorem «fb_op_call» : TerminatingFunBoundedOn GuestInv (ofString "op_call") K.«op_call» := by sorry
/-- `op_callcode` (AST line 19457): loop-free. -/
theorem «fb_op_callcode» : TerminatingFunBoundedOn GuestInv (ofString "op_callcode") K.«op_callcode» := by sorry
/-- `copy_from_buffer` (AST line 16866): loop-free. -/
theorem «fb_copy_from_buffer» : TerminatingFunBoundedOn GuestInv (ofString "copy_from_buffer") K.«copy_from_buffer» := by sorry
/-- `op_calldatacopy` (AST line 16895): loop-free. -/
theorem «fb_op_calldatacopy» : TerminatingFunBoundedOn GuestInv (ofString "op_calldatacopy") K.«op_calldatacopy» := by sorry
/-- `op_calldataload` (AST line 16824): loop-free. -/
theorem «fb_op_calldataload» : TerminatingFunBoundedOn GuestInv (ofString "op_calldataload") K.«op_calldataload» := by sorry
/-- `op_calldatasize` (AST line 16850): loop-free. -/
theorem «fb_op_calldatasize» : TerminatingFunBoundedOn GuestInv (ofString "op_calldatasize") K.«op_calldatasize» := by sorry
/-- `op_caller` (AST line 16791): loop-free. -/
theorem «fb_op_caller» : TerminatingFunBoundedOn GuestInv (ofString "op_caller") K.«op_caller» := by sorry
/-- `op_callvalue` (AST line 16808): loop-free. -/
theorem «fb_op_callvalue» : TerminatingFunBoundedOn GuestInv (ofString "op_callvalue") K.«op_callvalue» := by sorry
/-- `op_chainid` (AST line 17289): loop-free. -/
theorem «fb_op_chainid» : TerminatingFunBoundedOn GuestInv (ofString "op_chainid") K.«op_chainid» := by sorry
/-- `op_clz` (AST line 16002): loop-free. -/
theorem «fb_op_clz» : TerminatingFunBoundedOn GuestInv (ofString "op_clz") K.«op_clz» := by sorry
/-- `op_codecopy` (AST line 16924): loop-free. -/
theorem «fb_op_codecopy» : TerminatingFunBoundedOn GuestInv (ofString "op_codecopy") K.«op_codecopy» := by sorry
/-- `op_codesize` (AST line 16908): loop-free. -/
theorem «fb_op_codesize» : TerminatingFunBoundedOn GuestInv (ofString "op_codesize") K.«op_codesize» := by sorry
/-- `op_coinbase` (AST line 17220): loop-free. -/
theorem «fb_op_coinbase» : TerminatingFunBoundedOn GuestInv (ofString "op_coinbase") K.«op_coinbase» := by sorry
/-- `compute_contract_address` (AST line 19098): loop-free. -/
theorem «fb_compute_contract_address» : TerminatingFunBoundedOn GuestInv (ofString "compute_contract_address") K.«compute_contract_address» := by sorry
/-- `generic_create` (AST line 19156): loop-free. -/
theorem «fb_generic_create» : TerminatingFunBoundedOn GuestInv (ofString "generic_create") K.«generic_create» := by sorry
/-- `require_not_static` (AST line 15459): loop-free. -/
theorem «fb_require_not_static» : TerminatingFunBoundedOn GuestInv (ofString "require_not_static") K.«require_not_static» := by sorry
/-- `op_create` (AST line 19223): loop-free. -/
theorem «fb_op_create» : TerminatingFunBoundedOn GuestInv (ofString "op_create") K.«op_create» := by sorry
/-- `compute_create2_contract_address` (AST line 19129): loop-free. -/
theorem «fb_compute_create2_contract_address» : TerminatingFunBoundedOn GuestInv (ofString "compute_create2_contract_address") K.«compute_create2_contract_address» := by sorry
/-- `op_create2` (AST line 19257): loop-free. -/
theorem «fb_op_create2» : TerminatingFunBoundedOn GuestInv (ofString "op_create2") K.«op_create2» := by sorry
/-- `op_delegatecall` (AST line 19539): loop-free. -/
theorem «fb_op_delegatecall» : TerminatingFunBoundedOn GuestInv (ofString "op_delegatecall") K.«op_delegatecall» := by sorry
/-- `op_div` (AST line 15582): loop-free. -/
theorem «fb_op_div» : TerminatingFunBoundedOn GuestInv (ofString "op_div") K.«op_div» := by sorry
/-- `op_dup` (AST line 16308): loop-free. -/
theorem «fb_op_dup» : TerminatingFunBoundedOn GuestInv (ofString "op_dup") K.«op_dup» := by sorry
/-- `code_imm` (AST line 16370): loop-free. -/
theorem «fb_code_imm» : TerminatingFunBoundedOn GuestInv (ofString "code_imm") K.«code_imm» := by sorry
/-- `decode_single` (AST line 16385): loop-free. -/
theorem «fb_decode_single» : TerminatingFunBoundedOn GuestInv (ofString "decode_single") K.«decode_single» := by sorry
/-- `op_dupn` (AST line 16401): loop-free. -/
theorem «fb_op_dupn» : TerminatingFunBoundedOn GuestInv (ofString "op_dupn") K.«op_dupn» := by sorry
/-- `stack_push_bool` (AST line 15115): loop-free. -/
theorem «fb_stack_push_bool» : TerminatingFunBoundedOn GuestInv (ofString "stack_push_bool") K.«stack_push_bool» := by sorry
/-- `op_eq` (AST line 15814): loop-free. -/
theorem «fb_op_eq» : TerminatingFunBoundedOn GuestInv (ofString "op_eq") K.«op_eq» := by sorry
/-- `stack_swap_positions` (AST line 16330): loop-free. -/
theorem «fb_stack_swap_positions» : TerminatingFunBoundedOn GuestInv (ofString "stack_swap_positions") K.«stack_swap_positions» := by sorry
/-- `op_exchange` (AST line 16447): loop-free. -/
theorem «fb_op_exchange» : TerminatingFunBoundedOn GuestInv (ofString "op_exchange") K.«op_exchange» := by sorry
/-- `u256_exp` (AST line 2002): #0 CTR. -/
theorem «fb_u256_exp» : TerminatingFunBoundedOn GuestInv (ofString "u256_exp") K.«u256_exp» := by sorry
/-- `op_exp` (AST line 15698): loop-free. -/
theorem «fb_op_exp» : TerminatingFunBoundedOn GuestInv (ofString "op_exp") K.«op_exp» := by sorry
/-- `op_extcodecopy` (AST line 16987): loop-free. -/
theorem «fb_op_extcodecopy» : TerminatingFunBoundedOn GuestInv (ofString "op_extcodecopy") K.«op_extcodecopy» := by sorry
/-- `op_extcodehash` (AST line 17072): loop-free. -/
theorem «fb_op_extcodehash» : TerminatingFunBoundedOn GuestInv (ofString "op_extcodehash") K.«op_extcodehash» := by sorry
/-- `op_extcodesize` (AST line 16965): loop-free. -/
theorem «fb_op_extcodesize» : TerminatingFunBoundedOn GuestInv (ofString "op_extcodesize") K.«op_extcodesize» := by sorry
/-- `op_gas` (AST line 16130): loop-free. -/
theorem «fb_op_gas» : TerminatingFunBoundedOn GuestInv (ofString "op_gas") K.«op_gas» := by sorry
/-- `op_gaslimit` (AST line 17272): loop-free. -/
theorem «fb_op_gaslimit» : TerminatingFunBoundedOn GuestInv (ofString "op_gaslimit") K.«op_gaslimit» := by sorry
/-- `op_gasprice` (AST line 16936): loop-free. -/
theorem «fb_op_gasprice» : TerminatingFunBoundedOn GuestInv (ofString "op_gasprice") K.«op_gasprice» := by sorry
/-- `op_gt` (AST line 15757): loop-free. -/
theorem «fb_op_gt» : TerminatingFunBoundedOn GuestInv (ofString "op_gt") K.«op_gt» := by sorry
/-- `op_iszero` (AST line 15833): loop-free. -/
theorem «fb_op_iszero» : TerminatingFunBoundedOn GuestInv (ofString "op_iszero") K.«op_iszero» := by sorry
/-- `is_valid_jumpdest` (AST line 15324): loop-free. -/
theorem «fb_is_valid_jumpdest» : TerminatingFunBoundedOn GuestInv (ofString "is_valid_jumpdest") K.«is_valid_jumpdest» := by sorry
/-- `op_jump` (AST line 16066): loop-free. -/
theorem «fb_op_jump» : TerminatingFunBoundedOn GuestInv (ofString "op_jump") K.«op_jump» := by sorry
/-- `op_jumpdest` (AST line 16146): loop-free. -/
theorem «fb_op_jumpdest» : TerminatingFunBoundedOn GuestInv (ofString "op_jumpdest") K.«op_jumpdest» := by sorry
/-- `op_jumpi` (AST line 16086): loop-free. -/
theorem «fb_op_jumpi» : TerminatingFunBoundedOn GuestInv (ofString "op_jumpi") K.«op_jumpi» := by sorry
/-- `op_keccak` (AST line 16020): loop-free. -/
theorem «fb_op_keccak» : TerminatingFunBoundedOn GuestInv (ofString "op_keccak") K.«op_keccak» := by sorry
/-- `op_log` (AST line 16499): #0 CTR. -/
theorem «fb_op_log» : TerminatingFunBoundedOn GuestInv (ofString "op_log") K.«op_log» := by sorry
/-- `op_lt` (AST line 15738): loop-free. -/
theorem «fb_op_lt» : TerminatingFunBoundedOn GuestInv (ofString "op_lt") K.«op_lt» := by sorry
/-- `op_mcopy` (AST line 16233): loop-free. -/
theorem «fb_op_mcopy» : TerminatingFunBoundedOn GuestInv (ofString "op_mcopy") K.«op_mcopy» := by sorry
/-- `charge_with_memory` (AST line 15240): loop-free. -/
theorem «fb_charge_with_memory» : TerminatingFunBoundedOn GuestInv (ofString "charge_with_memory") K.«charge_with_memory» := by sorry
/-- `op_mload` (AST line 16198): loop-free. -/
theorem «fb_op_mload» : TerminatingFunBoundedOn GuestInv (ofString "op_mload") K.«op_mload» := by sorry
/-- `op_mod` (AST line 15620): loop-free. -/
theorem «fb_op_mod» : TerminatingFunBoundedOn GuestInv (ofString "op_mod") K.«op_mod» := by sorry
/-- `op_msize` (AST line 16217): loop-free. -/
theorem «fb_op_msize» : TerminatingFunBoundedOn GuestInv (ofString "op_msize") K.«op_msize» := by sorry
/-- `op_mstore` (AST line 16160): loop-free. -/
theorem «fb_op_mstore» : TerminatingFunBoundedOn GuestInv (ofString "op_mstore") K.«op_mstore» := by sorry
/-- `op_mstore8` (AST line 16179): loop-free. -/
theorem «fb_op_mstore8» : TerminatingFunBoundedOn GuestInv (ofString "op_mstore8") K.«op_mstore8» := by sorry
/-- `op_mul` (AST line 15544): loop-free. -/
theorem «fb_op_mul» : TerminatingFunBoundedOn GuestInv (ofString "op_mul") K.«op_mul» := by sorry
/-- `op_mulmod` (AST line 15678): loop-free. -/
theorem «fb_op_mulmod» : TerminatingFunBoundedOn GuestInv (ofString "op_mulmod") K.«op_mulmod» := by sorry
/-- `op_not` (AST line 15905): loop-free. -/
theorem «fb_op_not» : TerminatingFunBoundedOn GuestInv (ofString "op_not") K.«op_not» := by sorry
/-- `op_number` (AST line 17255): loop-free. -/
theorem «fb_op_number» : TerminatingFunBoundedOn GuestInv (ofString "op_number") K.«op_number» := by sorry
/-- `op_or` (AST line 15869): loop-free. -/
theorem «fb_op_or» : TerminatingFunBoundedOn GuestInv (ofString "op_or") K.«op_or» := by sorry
/-- `op_origin` (AST line 16773): loop-free. -/
theorem «fb_op_origin» : TerminatingFunBoundedOn GuestInv (ofString "op_origin") K.«op_origin» := by sorry
/-- `op_pc` (AST line 16114): loop-free. -/
theorem «fb_op_pc» : TerminatingFunBoundedOn GuestInv (ofString "op_pc") K.«op_pc» := by sorry
/-- `op_pop` (AST line 16268): loop-free. -/
theorem «fb_op_pop» : TerminatingFunBoundedOn GuestInv (ofString "op_pop") K.«op_pop» := by sorry
/-- `op_prevrandao` (AST line 17306): loop-free. -/
theorem «fb_op_prevrandao» : TerminatingFunBoundedOn GuestInv (ofString "op_prevrandao") K.«op_prevrandao» := by sorry
/-- `op_push` (AST line 16283): loop-free. -/
theorem «fb_op_push» : TerminatingFunBoundedOn GuestInv (ofString "op_push") K.«op_push» := by sorry
/-- `op_return` (AST line 17501): loop-free. -/
theorem «fb_op_return» : TerminatingFunBoundedOn GuestInv (ofString "op_return") K.«op_return» := by sorry
/-- `op_returndatacopy` (AST line 17038): loop-free. -/
theorem «fb_op_returndatacopy» : TerminatingFunBoundedOn GuestInv (ofString "op_returndatacopy") K.«op_returndatacopy» := by sorry
/-- `op_returndatasize` (AST line 17022): loop-free. -/
theorem «fb_op_returndatasize» : TerminatingFunBoundedOn GuestInv (ofString "op_returndatasize") K.«op_returndatasize» := by sorry
/-- `op_revert` (AST line 17526): loop-free. -/
theorem «fb_op_revert» : TerminatingFunBoundedOn GuestInv (ofString "op_revert") K.«op_revert» := by sorry
/-- `u256_or` (AST line 1019): loop-free. -/
theorem «fb_u256_or» : TerminatingFunBoundedOn GuestInv (ofString "u256_or") K.«u256_or» := by sorry
/-- `u256_shl` (AST line 2028): loop-free. -/
theorem «fb_u256_shl» : TerminatingFunBoundedOn GuestInv (ofString "u256_shl") K.«u256_shl» := by sorry
/-- `u256_shr` (AST line 2088): loop-free. -/
theorem «fb_u256_shr» : TerminatingFunBoundedOn GuestInv (ofString "u256_shr") K.«u256_shr» := by sorry
/-- `u256_sar` (AST line 2148): loop-free. -/
theorem «fb_u256_sar» : TerminatingFunBoundedOn GuestInv (ofString "u256_sar") K.«u256_sar» := by sorry
/-- `op_sar` (AST line 15982): loop-free. -/
theorem «fb_op_sar» : TerminatingFunBoundedOn GuestInv (ofString "op_sar") K.«op_sar» := by sorry
/-- `u256_neg` (AST line 1105): loop-free. -/
theorem «fb_u256_neg» : TerminatingFunBoundedOn GuestInv (ofString "u256_neg") K.«u256_neg» := by sorry
/-- `u256_abs` (AST line 1805): loop-free. -/
theorem «fb_u256_abs» : TerminatingFunBoundedOn GuestInv (ofString "u256_abs") K.«u256_abs» := by sorry
/-- `u256_sdiv` (AST line 1819): loop-free. -/
theorem «fb_u256_sdiv» : TerminatingFunBoundedOn GuestInv (ofString "u256_sdiv") K.«u256_sdiv» := by sorry
/-- `op_sdiv` (AST line 15601): loop-free. -/
theorem «fb_op_sdiv» : TerminatingFunBoundedOn GuestInv (ofString "op_sdiv") K.«op_sdiv» := by sorry
/-- `op_selfbalance` (AST line 17098): loop-free. -/
theorem «fb_op_selfbalance» : TerminatingFunBoundedOn GuestInv (ofString "op_selfbalance") K.«op_selfbalance» := by sorry
/-- `op_selfdestruct` (AST line 17551): loop-free. -/
theorem «fb_op_selfdestruct» : TerminatingFunBoundedOn GuestInv (ofString "op_selfdestruct") K.«op_selfdestruct» := by sorry
/-- `u256_slt` (AST line 931): loop-free. -/
theorem «fb_u256_slt» : TerminatingFunBoundedOn GuestInv (ofString "u256_slt") K.«u256_slt» := by sorry
/-- `u256_sgt` (AST line 969): loop-free. -/
theorem «fb_u256_sgt» : TerminatingFunBoundedOn GuestInv (ofString "u256_sgt") K.«u256_sgt» := by sorry
/-- `op_sgt` (AST line 15795): loop-free. -/
theorem «fb_op_sgt» : TerminatingFunBoundedOn GuestInv (ofString "op_sgt") K.«op_sgt» := by sorry
/-- `op_shl` (AST line 15942): loop-free. -/
theorem «fb_op_shl» : TerminatingFunBoundedOn GuestInv (ofString "op_shl") K.«op_shl» := by sorry
/-- `op_shr` (AST line 15962): loop-free. -/
theorem «fb_op_shr» : TerminatingFunBoundedOn GuestInv (ofString "op_shr") K.«op_shr» := by sorry
/-- `u256_and` (AST line 1009): loop-free. -/
theorem «fb_u256_and» : TerminatingFunBoundedOn GuestInv (ofString "u256_and") K.«u256_and» := by sorry
/-- `u256_not` (AST line 999): loop-free. -/
theorem «fb_u256_not» : TerminatingFunBoundedOn GuestInv (ofString "u256_not") K.«u256_not» := by sorry
/-- `u256_signextend` (AST line 2175): loop-free. -/
theorem «fb_u256_signextend» : TerminatingFunBoundedOn GuestInv (ofString "u256_signextend") K.«u256_signextend» := by sorry
/-- `op_signextend` (AST line 15718): loop-free. -/
theorem «fb_op_signextend» : TerminatingFunBoundedOn GuestInv (ofString "op_signextend") K.«op_signextend» := by sorry
/-- `is_warm_storage_key` (AST line 16559): loop-free. -/
theorem «fb_is_warm_storage_key» : TerminatingFunBoundedOn GuestInv (ofString "is_warm_storage_key") K.«is_warm_storage_key» := by sorry
/-- `warm_storage_key` (AST line 16571): loop-free. -/
theorem «fb_warm_storage_key» : TerminatingFunBoundedOn GuestInv (ofString "warm_storage_key") K.«warm_storage_key» := by sorry
/-- `op_slotnum` (AST line 17324): loop-free. -/
theorem «fb_op_slotnum» : TerminatingFunBoundedOn GuestInv (ofString "op_slotnum") K.«op_slotnum» := by sorry
/-- `op_slt` (AST line 15776): loop-free. -/
theorem «fb_op_slt» : TerminatingFunBoundedOn GuestInv (ofString "op_slt") K.«op_slt» := by sorry
/-- `u256_smod` (AST line 1840): loop-free. -/
theorem «fb_u256_smod» : TerminatingFunBoundedOn GuestInv (ofString "u256_smod") K.«u256_smod» := by sorry
/-- `op_smod` (AST line 15639): loop-free. -/
theorem «fb_op_smod» : TerminatingFunBoundedOn GuestInv (ofString "op_smod") K.«op_smod» := by sorry
/-- `check_gas` (AST line 14935): loop-free. -/
theorem «fb_check_gas» : TerminatingFunBoundedOn GuestInv (ofString "check_gas") K.«check_gas» := by sorry
/-- `set_storage` (AST line 13451): loop-free. -/
theorem «fb_set_storage» : TerminatingFunBoundedOn GuestInv (ofString "set_storage") K.«set_storage» := by sorry
/-- `op_staticcall` (AST line 19600): loop-free. -/
theorem «fb_op_staticcall» : TerminatingFunBoundedOn GuestInv (ofString "op_staticcall") K.«op_staticcall» := by sorry
/-- `op_stop` (AST line 16052): loop-free. -/
theorem «fb_op_stop» : TerminatingFunBoundedOn GuestInv (ofString "op_stop") K.«op_stop» := by sorry
/-- `op_sub` (AST line 15563): loop-free. -/
theorem «fb_op_sub» : TerminatingFunBoundedOn GuestInv (ofString "op_sub") K.«op_sub» := by sorry
/-- `op_swap` (AST line 16350): loop-free. -/
theorem «fb_op_swap» : TerminatingFunBoundedOn GuestInv (ofString "op_swap") K.«op_swap» := by sorry
/-- `op_swapn` (AST line 16425): loop-free. -/
theorem «fb_op_swapn» : TerminatingFunBoundedOn GuestInv (ofString "op_swapn") K.«op_swapn» := by sorry
/-- `op_timestamp` (AST line 17238): loop-free. -/
theorem «fb_op_timestamp» : TerminatingFunBoundedOn GuestInv (ofString "op_timestamp") K.«op_timestamp» := by sorry
/-- `get_transient_storage` (AST line 13299): loop-free. -/
theorem «fb_get_transient_storage» : TerminatingFunBoundedOn GuestInv (ofString "get_transient_storage") K.«get_transient_storage» := by sorry
/-- `op_tload` (AST line 16688): loop-free. -/
theorem «fb_op_tload» : TerminatingFunBoundedOn GuestInv (ofString "op_tload") K.«op_tload» := by sorry
/-- `set_transient_storage` (AST line 13574): loop-free. -/
theorem «fb_set_transient_storage» : TerminatingFunBoundedOn GuestInv (ofString "set_transient_storage") K.«set_transient_storage» := by sorry
/-- `op_tstore` (AST line 16710): loop-free. -/
theorem «fb_op_tstore» : TerminatingFunBoundedOn GuestInv (ofString "op_tstore") K.«op_tstore» := by sorry
/-- `op_xor` (AST line 15887): loop-free. -/
theorem «fb_op_xor» : TerminatingFunBoundedOn GuestInv (ofString "op_xor") K.«op_xor» := by sorry
/-- `state_fresh_tx` (AST line 12778): loop-free. -/
theorem «fb_state_fresh_tx» : TerminatingFunBoundedOn GuestInv (ofString "state_fresh_tx") K.«state_fresh_tx» := by sorry
/-- `te_new` (AST line 32838): loop-free. -/
theorem «fb_te_new» : TerminatingFunBoundedOn GuestInv (ofString "te_new") K.«te_new» := by sorry
/-- `requests_append` (AST line 33485): loop-free. -/
theorem «fb_requests_append» : TerminatingFunBoundedOn GuestInv (ofString "requests_append") K.«requests_append» := by sorry
/-- `calculate_total_blob_gas` (AST line 11914): loop-free. -/
theorem «fb_calculate_total_blob_gas» : TerminatingFunBoundedOn GuestInv (ofString "calculate_total_blob_gas") K.«calculate_total_blob_gas» := by sorry
/-- `fee_mul` (AST line 32778): loop-free. -/
theorem «fb_fee_mul» : TerminatingFunBoundedOn GuestInv (ofString "fee_mul") K.«fee_mul» := by sorry
/-- `check_transaction` (AST line 32951): #0 CTR. -/
theorem «fb_check_transaction» : TerminatingFunBoundedOn GuestInv (ofString "check_transaction") K.«check_transaction» := by sorry
/-- `clear_account_preserving_balance` (AST line 13541): loop-free. -/
theorem «fb_clear_account_preserving_balance» : TerminatingFunBoundedOn GuestInv (ofString "clear_account_preserving_balance") K.«clear_account_preserving_balance» := by sorry
/-- `create_ether` (AST line 13629): loop-free. -/
theorem «fb_create_ether» : TerminatingFunBoundedOn GuestInv (ofString "create_ether") K.«create_ether» := by sorry
/-- `rlp_finish_list` (AST line 31969): loop-free. -/
theorem «fb_rlp_finish_list» : TerminatingFunBoundedOn GuestInv (ofString "rlp_finish_list") K.«rlp_finish_list» := by sorry
/-- `encode_logs` (AST line 32005): #0 CTR; #1 CTR. -/
theorem «fb_encode_logs» : TerminatingFunBoundedOn GuestInv (ofString "encode_logs") K.«encode_logs» := by sorry
/-- `logs_encoded_bound` (AST line 31985): #0 CTR. -/
theorem «fb_logs_encoded_bound» : TerminatingFunBoundedOn GuestInv (ofString "logs_encoded_bound") K.«logs_encoded_bound» := by sorry
/-- `encode_receipt` (AST line 32051): loop-free. -/
theorem «fb_encode_receipt» : TerminatingFunBoundedOn GuestInv (ofString "encode_receipt") K.«encode_receipt» := by sorry
/-- `rlp_word_encoded_len` (AST line 4852): loop-free. -/
theorem «fb_rlp_word_encoded_len» : TerminatingFunBoundedOn GuestInv (ofString "rlp_word_encoded_len") K.«rlp_word_encoded_len» := by sorry
/-- `tx_u256_encoded_len` (AST line 11940): loop-free. -/
theorem «fb_tx_u256_encoded_len» : TerminatingFunBoundedOn GuestInv (ofString "tx_u256_encoded_len") K.«tx_u256_encoded_len» := by sorry
/-- `auth_payload_len` (AST line 12060): loop-free. -/
theorem «fb_auth_payload_len» : TerminatingFunBoundedOn GuestInv (ofString "auth_payload_len") K.«auth_payload_len» := by sorry
/-- `auth_list_payload_len` (AST line 12075): #0 CTR. -/
theorem «fb_auth_list_payload_len» : TerminatingFunBoundedOn GuestInv (ofString "auth_list_payload_len") K.«auth_list_payload_len» := by sorry
/-- `tx_encode_bound` (AST line 12141): loop-free. -/
theorem «fb_tx_encode_bound» : TerminatingFunBoundedOn GuestInv (ofString "tx_encode_bound") K.«tx_encode_bound» := by sorry
/-- `tx_put_access_list` (AST line 11998): #0 CTR; #1 CTR. -/
theorem «fb_tx_put_access_list» : TerminatingFunBoundedOn GuestInv (ofString "tx_put_access_list") K.«tx_put_access_list» := by sorry
/-- `tx_put_u256` (AST line 11924): loop-free. -/
theorem «fb_tx_put_u256» : TerminatingFunBoundedOn GuestInv (ofString "tx_put_u256") K.«tx_put_u256» := by sorry
/-- `tx_put_authorizations` (AST line 12094): #0 CTR. -/
theorem «fb_tx_put_authorizations» : TerminatingFunBoundedOn GuestInv (ofString "tx_put_authorizations") K.«tx_put_authorizations» := by sorry
/-- `tx_put_blob_hashes` (AST line 12040): #0 CTR. -/
theorem «fb_tx_put_blob_hashes» : TerminatingFunBoundedOn GuestInv (ofString "tx_put_blob_hashes") K.«tx_put_blob_hashes» := by sorry
/-- `tx_put_to` (AST line 11961): loop-free. -/
theorem «fb_tx_put_to» : TerminatingFunBoundedOn GuestInv (ofString "tx_put_to") K.«tx_put_to» := by sorry
/-- `tx_encode_generic` (AST line 12154): loop-free. -/
theorem «fb_tx_encode_generic» : TerminatingFunBoundedOn GuestInv (ofString "tx_encode_generic") K.«tx_encode_generic» := by sorry
/-- `encode_transaction` (AST line 12267): loop-free. -/
theorem «fb_encode_transaction» : TerminatingFunBoundedOn GuestInv (ofString "encode_transaction") K.«encode_transaction» := by sorry
/-- `tx_signing_hash_mode` (AST line 12289): loop-free. -/
theorem «fb_tx_signing_hash_mode» : TerminatingFunBoundedOn GuestInv (ofString "tx_signing_hash_mode") K.«tx_signing_hash_mode» := by sorry
/-- `signing_hash_155` (AST line 12315): loop-free. -/
theorem «fb_signing_hash_155» : TerminatingFunBoundedOn GuestInv (ofString "signing_hash_155") K.«signing_hash_155» := by sorry
/-- `signing_hash_1559` (AST line 12335): loop-free. -/
theorem «fb_signing_hash_1559» : TerminatingFunBoundedOn GuestInv (ofString "signing_hash_1559") K.«signing_hash_1559» := by sorry
/-- `signing_hash_2930` (AST line 12325): loop-free. -/
theorem «fb_signing_hash_2930» : TerminatingFunBoundedOn GuestInv (ofString "signing_hash_2930") K.«signing_hash_2930» := by sorry
/-- `signing_hash_4844` (AST line 12345): loop-free. -/
theorem «fb_signing_hash_4844» : TerminatingFunBoundedOn GuestInv (ofString "signing_hash_4844") K.«signing_hash_4844» := by sorry
/-- `signing_hash_7702` (AST line 12355): loop-free. -/
theorem «fb_signing_hash_7702» : TerminatingFunBoundedOn GuestInv (ofString "signing_hash_7702") K.«signing_hash_7702» := by sorry
/-- `signing_hash_pre155` (AST line 12305): loop-free. -/
theorem «fb_signing_hash_pre155» : TerminatingFunBoundedOn GuestInv (ofString "signing_hash_pre155") K.«signing_hash_pre155» := by sorry
/-- `signature_recovery_parameters` (AST line 12399): loop-free. -/
theorem «fb_signature_recovery_parameters» : TerminatingFunBoundedOn GuestInv (ofString "signature_recovery_parameters") K.«signature_recovery_parameters» := by sorry
/-- `recover_transaction_public_key` (AST line 12483): loop-free. -/
theorem «fb_recover_transaction_public_key» : TerminatingFunBoundedOn GuestInv (ofString "recover_transaction_public_key") K.«recover_transaction_public_key» := by sorry
/-- `sender_address_from_public_key` (AST line 12503): loop-free. -/
theorem «fb_sender_address_from_public_key» : TerminatingFunBoundedOn GuestInv (ofString "sender_address_from_public_key") K.«sender_address_from_public_key» := by sorry
/-- `recover_sender_with_chain_id` (AST line 12542): loop-free. -/
theorem «fb_recover_sender_with_chain_id» : TerminatingFunBoundedOn GuestInv (ofString "recover_sender_with_chain_id") K.«recover_sender_with_chain_id» := by sorry
/-- `set_account_balance` (AST line 13647): loop-free. -/
theorem «fb_set_account_balance» : TerminatingFunBoundedOn GuestInv (ofString "set_account_balance") K.«set_account_balance» := by sorry
/-- `tx_chain_id` (AST line 12365): loop-free. -/
theorem «fb_tx_chain_id» : TerminatingFunBoundedOn GuestInv (ofString "tx_chain_id") K.«tx_chain_id» := by sorry
/-- `tx_has_access_list` (AST line 11890): loop-free. -/
theorem «fb_tx_has_access_list» : TerminatingFunBoundedOn GuestInv (ofString "tx_has_access_list") K.«tx_has_access_list» := by sorry
/-- `tx_is_blob` (AST line 32750): loop-free. -/
theorem «fb_tx_is_blob» : TerminatingFunBoundedOn GuestInv (ofString "tx_is_blob") K.«tx_is_blob» := by sorry
/-- `tx_is_setcode` (AST line 32764): loop-free. -/
theorem «fb_tx_is_setcode» : TerminatingFunBoundedOn GuestInv (ofString "tx_is_setcode") K.«tx_is_setcode» := by sorry
/-- `udiv_small5` (AST line 33447): loop-free. -/
theorem «fb_udiv_small5» : TerminatingFunBoundedOn GuestInv (ofString "udiv_small5") K.«udiv_small5» := by sorry
/-- `count_tokens_in_data` (AST line 12562): #0 CTR. -/
theorem «fb_count_tokens_in_data» : TerminatingFunBoundedOn GuestInv (ofString "count_tokens_in_data") K.«count_tokens_in_data» := by sorry
/-- `calculate_intrinsic_cost` (AST line 12581): #0 CTR. -/
theorem «fb_calculate_intrinsic_cost» : TerminatingFunBoundedOn GuestInv (ofString "calculate_intrinsic_cost") K.«calculate_intrinsic_cost» := by sorry
/-- `validate_transaction` (AST line 12639): loop-free. -/
theorem «fb_validate_transaction» : TerminatingFunBoundedOn GuestInv (ofString "validate_transaction") K.«validate_transaction» := by sorry
/-- `validate_block_access_list_gas_limit` (AST line 14776): #0 CTR; #1 CTR. -/
theorem «fb_validate_block_access_list_gas_limit» : TerminatingFunBoundedOn GuestInv (ofString "validate_block_access_list_gas_limit") K.«validate_block_access_list_gas_limit» := by sorry
/-- `encode_header` (AST line 9350): loop-free. -/
theorem «fb_encode_header» : TerminatingFunBoundedOn GuestInv (ofString "encode_header") K.«encode_header» := by sorry
/-- `header_hash` (AST line 9460): loop-free. -/
theorem «fb_header_hash» : TerminatingFunBoundedOn GuestInv (ofString "header_hash") K.«header_hash» := by sorry
/-- `is_valid_versioned_hashes` (AST line 32794): #0 CTR; #1 CTR. -/
theorem «fb_is_valid_versioned_hashes» : TerminatingFunBoundedOn GuestInv (ofString "is_valid_versioned_hashes") K.«is_valid_versioned_hashes» := by sorry
/-- `nodedb_build` (AST line 9937): #0 RO(1); #1 CTR. -/
theorem «fb_nodedb_build» : TerminatingFunBoundedOn GuestInv (ofString "nodedb_build") K.«nodedb_build» := by sorry
/-- `withdrawal_rlp_len` (AST line 32099): loop-free. -/
theorem «fb_withdrawal_rlp_len» : TerminatingFunBoundedOn GuestInv (ofString "withdrawal_rlp_len") K.«withdrawal_rlp_len» := by sorry
/-- `block_rlp_length` (AST line 32586): #0 CTR; #1 CTR. -/
theorem «fb_block_rlp_length» : TerminatingFunBoundedOn GuestInv (ofString "block_rlp_length") K.«block_rlp_length» := by sorry
/-- `encode_execution_requests` (AST line 32142): #0 CTR. -/
theorem «fb_encode_execution_requests» : TerminatingFunBoundedOn GuestInv (ofString "encode_execution_requests") K.«encode_execution_requests» := by sorry
/-- `encode_withdrawal_rlp` (AST line 32114): loop-free. -/
theorem «fb_encode_withdrawal_rlp» : TerminatingFunBoundedOn GuestInv (ofString "encode_withdrawal_rlp") K.«encode_withdrawal_rlp» := by sorry
/-- `calculate_base_fee_per_gas` (AST line 9613): loop-free. -/
theorem «fb_calculate_base_fee_per_gas» : TerminatingFunBoundedOn GuestInv (ofString "calculate_base_fee_per_gas") K.«calculate_base_fee_per_gas» := by sorry
/-- `calculate_excess_blob_gas` (AST line 9561): loop-free. -/
theorem «fb_calculate_excess_blob_gas» : TerminatingFunBoundedOn GuestInv (ofString "calculate_excess_blob_gas") K.«calculate_excess_blob_gas» := by sorry
/-- `validate_header` (AST line 9675): loop-free. -/
theorem «fb_validate_header» : TerminatingFunBoundedOn GuestInv (ofString "validate_header") K.«validate_header» := by sorry
/-- `hdr_bytes_field` (AST line 9168): loop-free. -/
theorem «fb_hdr_bytes_field» : TerminatingFunBoundedOn GuestInv (ofString "hdr_bytes_field") K.«hdr_bytes_field» := by sorry
/-- `hdr_raw_field` (AST line 9187): loop-free. -/
theorem «fb_hdr_raw_field» : TerminatingFunBoundedOn GuestInv (ofString "hdr_raw_field") K.«hdr_raw_field» := by sorry
/-- `hdr_uint_field` (AST line 9103): loop-free. -/
theorem «fb_hdr_uint_field» : TerminatingFunBoundedOn GuestInv (ofString "hdr_uint_field") K.«hdr_uint_field» := by sorry
/-- `hdr_u256_field` (AST line 9152): loop-free. -/
theorem «fb_hdr_u256_field» : TerminatingFunBoundedOn GuestInv (ofString "hdr_u256_field") K.«hdr_u256_field» := by sorry
/-- `hdr_word_field` (AST line 9130): #0 CTR. -/
theorem «fb_hdr_word_field» : TerminatingFunBoundedOn GuestInv (ofString "hdr_word_field") K.«hdr_word_field» := by sorry
/-- `decode_header` (AST line 9202): loop-free. -/
theorem «fb_decode_header» : TerminatingFunBoundedOn GuestInv (ofString "decode_header") K.«decode_header» := by sorry
/-- `validate_headers` (AST line 9476): #0 CTR; #1 CTR. -/
theorem «fb_validate_headers» : TerminatingFunBoundedOn GuestInv (ofString "validate_headers") K.«validate_headers» := by sorry
/-- `blake2_init` (AST line 20017): loop-free. -/
theorem «fb_blake2_init» : TerminatingFunBoundedOn GuestInv (ofString "blake2_init") K.«blake2_init» := by sorry
/-- `bls_consts_init` (AST line 24793): loop-free. -/
theorem «fb_bls_consts_init» : TerminatingFunBoundedOn GuestInv (ofString "bls_consts_init") K.«bls_consts_init» := by sorry
/-- `bls_lib_init` (AST line 30328): loop-free. -/
theorem «fb_bls_lib_init» : TerminatingFunBoundedOn GuestInv (ofString "bls_lib_init") K.«bls_lib_init» := by sorry
/-- `bls_precompiles_init` (AST line 30678): loop-free. -/
theorem «fb_bls_precompiles_init» : TerminatingFunBoundedOn GuestInv (ofString "bls_precompiles_init") K.«bls_precompiles_init» := by sorry
/-- `ceil_log2` (AST line 749): #0 RO(1). -/
theorem «fb_ceil_log2» : TerminatingFunBoundedOn GuestInv (ofString "ceil_log2") K.«ceil_log2» := by sorry
/-- `ssz_fail` (AST line 8285): loop-free. -/
theorem «fb_ssz_fail» : TerminatingFunBoundedOn GuestInv (ofString "ssz_fail") K.«ssz_fail» := by sorry
/-- `ssz_split_var_list` (AST line 8447): #0 CTR. -/
theorem «fb_ssz_split_var_list» : TerminatingFunBoundedOn GuestInv (ofString "ssz_split_var_list") K.«ssz_split_var_list» := by sorry
/-- `decode_bytes_list` (AST line 8637): #0 CTR. -/
theorem «fb_decode_bytes_list» : TerminatingFunBoundedOn GuestInv (ofString "decode_bytes_list") K.«decode_bytes_list» := by sorry
/-- `ssz_check_offsets` (AST line 8414): #0 CTR. -/
theorem «fb_ssz_check_offsets» : TerminatingFunBoundedOn GuestInv (ofString "ssz_check_offsets") K.«ssz_check_offsets» := by sorry
/-- `ssz_fixed_list_count` (AST line 8496): loop-free. -/
theorem «fb_ssz_fixed_list_count» : TerminatingFunBoundedOn GuestInv (ofString "ssz_fixed_list_count") K.«ssz_fixed_list_count» := by sorry
/-- `decode_payload` (AST line 8515): loop-free. -/
theorem «fb_decode_payload» : TerminatingFunBoundedOn GuestInv (ofString "decode_payload") K.«decode_payload» := by sorry
/-- `decode_requests` (AST line 8584): #0 CTR. -/
theorem «fb_decode_requests» : TerminatingFunBoundedOn GuestInv (ofString "decode_requests") K.«decode_requests» := by sorry
/-- `decode_stateless_input` (AST line 8656): #0 CTR. -/
theorem «fb_decode_stateless_input» : TerminatingFunBoundedOn GuestInv (ofString "decode_stateless_input") K.«decode_stateless_input» := by sorry
/-- `input_blob` (AST line 624): #0 WALK. -/
theorem «fb_input_blob» : TerminatingFunBoundedOn GuestInv (ofString "input_blob") K.«input_blob» := by sorry
/-- `host_input_byte` (AST line 8297): loop-free. -/
theorem «fb_host_input_byte» : TerminatingFunBoundedOn GuestInv (ofString "host_input_byte") K.«host_input_byte» := by sorry
/-- `host_input_le32` (AST line 8310): loop-free. -/
theorem «fb_host_input_le32» : TerminatingFunBoundedOn GuestInv (ofString "host_input_le32") K.«host_input_le32» := by sorry
/-- `precheck_host_ssz_header` (AST line 8324): loop-free. -/
theorem «fb_precheck_host_ssz_header» : TerminatingFunBoundedOn GuestInv (ofString "precheck_host_ssz_header") K.«precheck_host_ssz_header» := by sorry
/-- `decode_host_input` (AST line 8401): loop-free. -/
theorem «fb_decode_host_input» : TerminatingFunBoundedOn GuestInv (ofString "decode_host_input") K.«decode_host_input» := by sorry
/-- `evm_init` (AST line 17353): #0 CTR. -/
theorem «fb_evm_init» : TerminatingFunBoundedOn GuestInv (ofString "evm_init") K.«evm_init» := by sorry
/-- `fork_init` (AST line 32522): #0 CTR. -/
theorem «fb_fork_init» : TerminatingFunBoundedOn GuestInv (ofString "fork_init") K.«fork_init» := by sorry
/-- `header_init` (AST line 9657): loop-free. -/
theorem «fb_header_init» : TerminatingFunBoundedOn GuestInv (ofString "header_init") K.«header_init» := by sorry
/-- `sha256_pair` (AST line 2954): loop-free. -/
theorem «fb_sha256_pair» : TerminatingFunBoundedOn GuestInv (ofString "sha256_pair") K.«sha256_pair» := by sorry
/-- `merkleize` (AST line 8052): #0 MONO; #1 CTR; #2 CTR. -/
theorem «fb_merkleize» : TerminatingFunBoundedOn GuestInv (ofString "merkleize") K.«merkleize» := by sorry
/-- `pack_bytes` (AST line 8213): loop-free. -/
theorem «fb_pack_bytes» : TerminatingFunBoundedOn GuestInv (ofString "pack_bytes") K.«pack_bytes» := by sorry
/-- `htr_bytes_vector` (AST line 8229): loop-free. -/
theorem «fb_htr_bytes_vector» : TerminatingFunBoundedOn GuestInv (ofString "htr_bytes_vector") K.«htr_bytes_vector» := by sorry
/-- `htr_u64_at` (AST line 8271): loop-free. -/
theorem «fb_htr_u64_at» : TerminatingFunBoundedOn GuestInv (ofString "htr_u64_at") K.«htr_u64_at» := by sorry
/-- `htr_bdep` (AST line 8943): loop-free. -/
theorem «fb_htr_bdep» : TerminatingFunBoundedOn GuestInv (ofString "htr_bdep") K.«htr_bdep» := by sorry
/-- `htr_bexit` (AST line 8967): loop-free. -/
theorem «fb_htr_bexit» : TerminatingFunBoundedOn GuestInv (ofString "htr_bexit") K.«htr_bexit» := by sorry
/-- `mix_in_length` (AST line 8099): loop-free. -/
theorem «fb_mix_in_length» : TerminatingFunBoundedOn GuestInv (ofString "mix_in_length") K.«mix_in_length» := by sorry
/-- `htr_bytes_list` (AST line 8253): loop-free. -/
theorem «fb_htr_bytes_list» : TerminatingFunBoundedOn GuestInv (ofString "htr_bytes_list") K.«htr_bytes_list» := by sorry
/-- `htr_cons` (AST line 8921): loop-free. -/
theorem «fb_htr_cons» : TerminatingFunBoundedOn GuestInv (ofString "htr_cons") K.«htr_cons» := by sorry
/-- `htr_deposit` (AST line 8873): loop-free. -/
theorem «fb_htr_deposit» : TerminatingFunBoundedOn GuestInv (ofString "htr_deposit") K.«htr_deposit» := by sorry
/-- `merkleize_progressive` (AST line 8115): #0 WALK; #1 CTR. -/
theorem «fb_merkleize_progressive» : TerminatingFunBoundedOn GuestInv (ofString "merkleize_progressive") K.«merkleize_progressive» := by sorry
/-- `htr_plist_chunks` (AST line 8156): loop-free. -/
theorem «fb_htr_plist_chunks» : TerminatingFunBoundedOn GuestInv (ofString "htr_plist_chunks") K.«htr_plist_chunks» := by sorry
/-- `htr_pbytes` (AST line 8170): loop-free. -/
theorem «fb_htr_pbytes» : TerminatingFunBoundedOn GuestInv (ofString "htr_pbytes") K.«htr_pbytes» := by sorry
/-- `htr_pcontainer` (AST line 8186): #0 CTR. -/
theorem «fb_htr_pcontainer» : TerminatingFunBoundedOn GuestInv (ofString "htr_pcontainer") K.«htr_pcontainer» := by sorry
/-- `htr_withdrawal` (AST line 8755): loop-free. -/
theorem «fb_htr_withdrawal» : TerminatingFunBoundedOn GuestInv (ofString "htr_withdrawal") K.«htr_withdrawal» := by sorry
/-- `htr_payload` (AST line 8793): #0 CTR; #1 CTR. -/
theorem «fb_htr_payload» : TerminatingFunBoundedOn GuestInv (ofString "htr_payload") K.«htr_payload» := by sorry
/-- `htr_wdreq` (AST line 8899): loop-free. -/
theorem «fb_htr_wdreq» : TerminatingFunBoundedOn GuestInv (ofString "htr_wdreq") K.«htr_wdreq» := by sorry
/-- `htr_request_list` (AST line 8987): #0 CTR. -/
theorem «fb_htr_request_list» : TerminatingFunBoundedOn GuestInv (ofString "htr_request_list") K.«htr_request_list» := by sorry
/-- `htr_requests` (AST line 9027): loop-free. -/
theorem «fb_htr_requests» : TerminatingFunBoundedOn GuestInv (ofString "htr_requests") K.«htr_requests» := by sorry
/-- `htr_new_payload_request` (AST line 9053): loop-free. -/
theorem «fb_htr_new_payload_request» : TerminatingFunBoundedOn GuestInv (ofString "htr_new_payload_request") K.«htr_new_payload_request» := by sorry
/-- `keccak_init` (AST line 3974): loop-free. -/
theorem «fb_keccak_init» : TerminatingFunBoundedOn GuestInv (ofString "keccak_init") K.«keccak_init» := by sorry
/-- `mem_init` (AST line 50): loop-free. -/
theorem «fb_mem_init» : TerminatingFunBoundedOn GuestInv (ofString "mem_init") K.«mem_init» := by sorry
/-- `mpt_init` (AST line 9781): loop-free. -/
theorem «fb_mpt_init» : TerminatingFunBoundedOn GuestInv (ofString "mpt_init") K.«mpt_init» := by sorry
/-- `output_write` (AST line 651): #0 CTR. -/
theorem «fb_output_write» : TerminatingFunBoundedOn GuestInv (ofString "output_write") K.«output_write» := by sorry
/-- `ripemd160_init` (AST line 19738): loop-free. -/
theorem «fb_ripemd160_init» : TerminatingFunBoundedOn GuestInv (ofString "ripemd160_init") K.«ripemd160_init» := by sorry
/-- `secp256k1_init` (AST line 5417): loop-free. -/
theorem «fb_secp256k1_init» : TerminatingFunBoundedOn GuestInv (ofString "secp256k1_init") K.«secp256k1_init» := by sorry
/-- `serialize_result` (AST line 9077): loop-free. -/
theorem «fb_serialize_result» : TerminatingFunBoundedOn GuestInv (ofString "serialize_result") K.«serialize_result» := by sorry
/-- `sha256_init` (AST line 2327): loop-free. -/
theorem «fb_sha256_init» : TerminatingFunBoundedOn GuestInv (ofString "sha256_init") K.«sha256_init» := by sorry
/-- `ssz_init` (AST line 7520): loop-free. -/
theorem «fb_ssz_init» : TerminatingFunBoundedOn GuestInv (ofString "ssz_init") K.«ssz_init» := by sorry
/-- `u256_ws_init` (AST line 766): loop-free. -/
theorem «fb_u256_ws_init» : TerminatingFunBoundedOn GuestInv (ofString "u256_ws_init") K.«u256_ws_init» := by sorry

/-! ## 7. Guarded tier: contracts and leaves

The six loops without an arbitrary-memory measure (`run_frames`, `htab_truncate`,
`_decode_witness_node_body`, `_mpt_insert_node`, `_mpt_delete_node_body` ×2) and every function
that (transitively) calls one of them. Each such function has a bound leaf under an explicit
guard (the generated `gb_*` leaves below and DESIGN.md §6); the memory facts those leaves need at
their guarded call sites are the contracts of this section, each a separate leaf. Every guard is
`LocalsOnly` (end of this section), so `dec_onLocals`, `LocalsOnly.decClock` (`hdec` of the
`while` rules) and `decCall_on` apply to it. -/

/-- Outcome specification of a function body from its callee-entry state. -/
def FunSpec (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      Q s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2

/-- `Q` on normal return only. -/
def OnReturn (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → Q s post

/-! ### Table contracts (round-1 items 3 and 4) -/

theorem htab_set_spec : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_set") := by sorry
theorem htab_del_spec : FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_del") := by sorry

/-- Progress of `htab_del` (round-2 item 3, `htab_truncate`): a normal return either deleted a
leaf, so the count `t+24` dropped by one, or wrote nothing at all (`htab_find_leaf` found no leaf
or `memeq` rejected its key; `HtabWF` does not constrain key bytes, so the key of the last leaf
need not lead back to that leaf). In the second case memory, globals and the FFI state are those of
the entry state: the caller's loop head repeats exactly (`SameHead`). -/
def HtabDelProgress : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F →
    Prop :=
  fun s post => hdr post (locN s "t") 3 + 1 = hdr s (locN s "t") 3 ∨
    post = { s with locals := post.locals, clock := post.clock }

theorem htab_del_progress_spec :
    FunSpec HtabArgWF (OnReturn HtabDelProgress) (ofString "htab_del") := by sorry
theorem htab_truncate_spec :
    FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_truncate") := by sorry
theorem htab_union_into_spec :
    FunSpec UnionArgWF (OnReturn UnionExit) (ofString "htab_union_into") := by sorry

/-- `htab_new` / `htab_new_scratch` return a well-formed empty table whose footprint is freshly
allocated (heap resp. scratch); nothing outside the UNION of the fresh heap and the fresh scratch
changes (round-2 Astra item 2: revision 2 intersected the two frames), and no global but the two
allocator pointers changes (round-3 Gemini item 5: the globals frame was missing). -/
def HtabNewExit : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    ArenaReady post ∧ HtabWF post w.toNat ∧ hdr post w.toNat 3 = 0 ∧
    (∀ i ∈ htabFootprint post w.toNat, Allocated post i ∧
      (Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∨
        Inside i (globN post "scratch_ptr") (globN s "scratch_ptr"))) ∧
    FrameOutside s post
      [(globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr")]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") ∧
    ∀ name, name ∉ ["heap_ptr", "scratch_ptr"] →
      s.globals.lookup (ofString name) = post.globals.lookup (ofString name)

/-- Entry of `htab_new` / `htab_new_scratch` (round-2 Fable item 1, Astra item 3): separated
arenas, a key length from the literal call sites and a bounded capacity. `htab_new` checks
neither: `key_len = 0` breaks `1 ≤ klen`, `61` breaks `klen ≤ maxKeyLen`, `2^64 - 3` wraps the
stride; `cap = 2^64 - 1` wraps `(ncap + 1) * stride`. 31 call sites pass a literal capacity
(≤ 256); `nodedb_build` passes a power of two, which its caller bounds (round-3 non-blocking). -/
def HtabNewReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "key_len" ∈ htabKeyLens ∧ locN s "cap" ≤ htabCapMax

theorem htab_new_spec : FunSpec HtabNewReady HtabNewExit (ofString "htab_new") := by sorry
theorem htab_new_scratch_spec :
    FunSpec HtabNewReady HtabNewExit (ofString "htab_new_scratch") := by sorry

/-! ### MPT update contracts (`_mpt_insert_node`, `_mpt_delete_node_body`) -/

/-- Entry of the two MPT update functions `_mpt_insert_node`/`_mpt_delete_node(_body)(node, key,
klen, level, …)`: separated arenas and a typed trie below the `node` parameter. Revision 6
(round-4 Astra item 5): `level ≤ klen` and the unread key `(key + level, klen − level)` is a
nibble array next to the trie (`KeyIn`: nibbles, allocated heap, disjoint from every node record).
Both loops read `loadByte(key + level)` as a branch index and store through `node + 32 + 8·idx`
(insert) or push it into a scratch frame that later stores `fnode + 32 + 8·idx` (delete). A key
byte `18` indexed `n + 176`, past the 176-byte branch. `level` grows by `1` at a branch (only when
`level ≠ klen`) and by an extension's path length when `common_prefix_length` matched all of it
(`≤ klen − level`), so `level ≤ klen` and the key's suffix are loop invariants; the writes go to
node records, fresh heap and the free scratch gap, which `KeyIn` keeps away from the key. -/
def MptReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "level" ≤ locN s "klen" ∧ ∃ Nd, NodeHeap s Nd ∧
    RootIn Nd (locN s "node") ∧
    KeyIn s Nd (locN s "key" + locN s "level") (locN s "klen" - locN s "level")

/-- The trie object `m` (16 bytes, `mpt_new` 10446: `+0` root node) and its node set, placed
relative to the typed world `S` (revision 5, round-4 Fable item 3): `m` is allocated, and `m` and
every node of `Nd` are disjoint from every table footprint of `S` and every fixed object, as
`TriesTyped` requires of the world tries. `mpt_set` stores `m+0` (10886) and rewrites node records;
`mpt_root` stores hash pointers into the node caches (`+8/+16`). A node at `nodes + 8` of a table
in `S` made `mpt_root` overwrite that table's root. Revision 6: the node paths too
(`nodeExtents`, round-4 Astra item 5), and `m` avoids the persistent tries (`AvoidsTries`, item
2: `mpt_set`'s store `m+0` must not hit a world node). -/
def MptObjIn {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  Allocated s (locN s "m", 16) ∧ WordsOK s (locN s "m", 16) ∧
  (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (locN s "m", 16) i) ∧
  (∀ j ∈ fixedObjects s, Disj (locN s "m", 16) j) ∧
  ∃ Nd, NodeHeap s Nd ∧ RootIn Nd (memW s (locN s "m")) ∧
    ∀ o ∈ nodeExtents s Nd, Disj o (locN s "m", 16) ∧
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj o i) ∧
      ∀ j ∈ fixedObjects s, Disj o j

/-- A typed world `S` with a typed trie object `m` in it (`MptObjIn`, the same `S`), and regions
`R s` disjoint from every table footprint of `S` and every fixed object (`mpt_root`'s output
buffer, as in `WorldAvoids`). Revision 6 (round-4 Astra item 2): the object `m` and the regions
avoid the persistent tries (`AvoidsTries`, same `S`). -/
def MptObjAvoids (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, WorldTyped s S ∧ MptObjIn s S ∧ (∀ i ∈ R s,
    (∀ t ∈ S, ∀ j ∈ htabFootprint s t, Disj i j) ∧ ∀ j ∈ fixedObjects s, Disj i j) ∧
    AvoidsTries s S ((locN s "m", 16) :: R s)

/-- `mpt_set(m, …)`: a typed world with the trie object `m` in it (revision 5: `MptObjIn`; the
revision-4 guard did not relate `m` and its nodes to the typed tables and fixed objects). -/
def MptObjReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => MptObjAvoids (fun _ => []) s

/-- Exit: the returned root is typed in the new node heap, which extends the old one by fresh
heap records; old memory outside the old nodes (sized by kind), the heap free at entry and the
scratch free at entry is unchanged, and only `heap_ptr`/`scratch_ptr` among the globals change.
Round-3 Gemini item 5: nodes are sized by kind (`nodeIvl`), and `_mpt_delete_node_body` leaves
40-byte `scratch_alloc` frames below the entry `scratch_ptr` (its caller releases them), so the
free scratch gap `[frame_mem_ptr, scratch_ptr)` at entry is in the frame; the globals frame was
missing. -/
def MptExit : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    (∀ name, name ∉ ["heap_ptr", "scratch_ptr"] →
      s.globals.lookup (ofString name) = post.globals.lookup (ofString name)) ∧
    ∃ Nd Nd', NodeHeap s Nd ∧ RootIn Nd (locN s "node") ∧ NodeHeap post Nd' ∧
      RootIn Nd' w.toNat ∧
      FrameOutside s post
        ((Nd.map fun n => nodeIvl s n) ++
          [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
        (globN s "heap_ptr", heapLimit - globN s "heap_ptr")

theorem mpt_insert_node_spec : FunSpec MptReady MptExit (ofString "_mpt_insert_node") := by sorry
theorem mpt_delete_node_body_spec :
    FunSpec MptReady MptExit (ofString "_mpt_delete_node_body") := by sorry

/-! ### `WorldOK` from `mem_init` -/

/-- After `mem_init` the arenas are separated and every root is `0` (all globals were `0`). -/
theorem mem_init_world :
    FunSpec (fun s => GuestInv s ∧ GlobalsZero s) (OnReturn fun _ post => WorldOK post)
      (ofString "mem_init") := by sorry

/-! ### EVM frame contracts (round-1 item 5) -/

/-- `R` component of `evmPot`. -/
def evmR {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum

def IsEvmErr (r : Option (PanSemResultExact 64)) : Prop :=
  ∃ v, r = some (.exception (ofString "EvmErr") v)

/-- One instruction: from a running frame, a normal return strictly lowers `evmPot` (charged
regular or state gas, or halted the frame); an `EvmErr` leaves the chain length and `R` no larger
(the handler `frame_exception` then halts the frame). -/
theorem op_dispatch_spec :
    FunSpec (fun s => EvmInv s ∧ ¬ EvmDone s)
      (fun s r post =>
        ((∃ v, r = some (.returned v)) → EvmInv post ∧ evmPot post < evmPot s) ∧
        (IsEvmErr r → EvmInv post ∧ (evmChain post).length = (evmChain s).length ∧
          evmR post ≤ evmR s))
      (ofString "op_dispatch") := by sorry

/-- The `EvmErr` handler halts the current frame (`cur_cont+32 := 1`) without growing `R`. -/
theorem frame_exception_spec :
    FunSpec EvmInv
      (OnReturn fun s post => EvmInv post ∧ EvmDone post ∧
        (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "frame_exception") := by sorry

/-- The epilogue only rolls back the journal (tables in the typed set). -/
theorem frame_epilogue_spec :
    FunSpec (fun s => EvmInv s ∧ EvmDone s)
      (OnReturn fun s post => EvmInv post ∧ EvmDone post ∧
        (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "frame_epilogue") := by sorry

/-- Popping a done child: one frame shorter, `R` not larger, on return and on `EvmErr` (raised,
if at all, after the pop by `stack_push` in the parent). Includes the marks release
(`MarksOK`), `rollback_child_access` (truncation of the child's typed access tables) and
`incorporate_child_on_success` (`htab_union_into` into the parent's typed table). -/
theorem finish_child_spec :
    FunSpec (fun s => EvmInv s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0)
      (fun s r post => ((∃ v, r = some (.returned v)) ∨ IsEvmErr r) →
        EvmInv post ∧ (evmChain post).length + 1 = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "finish_child") := by sorry

/-! ### Guards of the guarded bound leaves -/

/-- `op_dispatch`, `op_sload`, `op_sstore` entry (revision 5, round-4 Fable item 1): a running
frame, the precondition of `op_dispatch_spec`, which `run_frames` provides at its `op_dispatch`
call. `charge_gas`, `stack_pop` and `warm_storage_key` write through the global `ev` (the frame's
gas, stack and access table), which `WorldOK` does not own; `EvmInv` does (`frameObjects`). -/
def EvmRun : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => EvmInv s ∧ ¬ EvmDone s

/-- `finish_child` entry (inside `run_frames`). -/
def FinishReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => EvmInv s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0

/-- `rollback_child_access(child)`: the child's two access tables are typed. Revision 6 (found
while auditing the `gbody_*` hypotheses, round-4 Astra item 8): the body truncates `child+168`,
then RELOADS `child+176` and `child+272` and truncates that table, so its composition needs the
child record outside both footprints, allocated words, and the two tables equal or with disjoint
footprints (`htab_truncate_spec` frames only the first table's footprint). `finish_child` calls it
after `ev := parent`, from facts it read off `EvmInv` while `child` was the current frame (record
and tables of a chain frame: `FrameWF`, frame objects disjoint from table footprints, tables of `S`
pairwise disjoint). -/
def RollbackReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ Allocated s (locN s "child", 280) ∧ WordsOK s (locN s "child", 280) ∧
    (∀ k ∈ [168, 176],
      HtabWF s (memW s (locN s "child" + k)) ∧
      ∀ i ∈ htabFootprint s (memW s (locN s "child" + k)), Allocated s i ∧
        Disj (locN s "child", 280) i) ∧
    (memW s (locN s "child" + 168) = memW s (locN s "child" + 176) ∨
      ∀ i ∈ htabFootprint s (memW s (locN s "child" + 168)),
        ∀ j ∈ htabFootprint s (memW s (locN s "child" + 176)), Disj i j)

/-! ### Every guard reads at most one local (`dec_onLocals`, round-2 item 3) -/

theorem freeChain_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k nodes : Nat) :
    ∀ (Fr : List Nat) (head : Nat),
      FreeChain { s with locals := locals, clock := k } nodes head Fr ↔ FreeChain s nodes head Fr
  | [], _ => Iff.rfl
  | f :: rest, head => by
    simp only [FreeChain]
    exact and_congr Iff.rfl (freeChain_with_locals s locals k nodes rest _)

theorem htabWF_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k t : Nat) :
    HtabWF { s with locals := locals, clock := k } t ↔ HtabWF s t := by
  simp only [HtabWF, freeChain_with_locals]
  exact Iff.rfl

theorem tablesTyped_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S : List Nat) :
    TablesTyped { s with locals := locals, clock := k } S ↔ TablesTyped s S := by
  simp only [TablesTyped, htabWF_with_locals]
  exact Iff.rfl

theorem worldTyped_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S : List Nat) :
    WorldTyped { s with locals := locals, clock := k } S ↔ WorldTyped s S := by
  simp only [WorldTyped, tablesTyped_with_locals]
  exact Iff.rfl

theorem locN_congr {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (n : String)
    (h : locals.lookup (ofString n) = s.locals.lookup (ofString n)) :
    locN { s with locals := locals, clock := k } n = locN s n := by
  simp only [locN, h]

theorem arenaReady_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ArenaReady { s with locals := locals, clock := k } ↔ ArenaReady s :=
  ⟨fun h => ⟨guestInv_congr (s := { s with locals := locals, clock := k }) rfl rfl rfl rfl h.1, h.2⟩,
   fun h => ⟨guestInv_with_locals_clock s locals k h.1, h.2⟩⟩

theorem evmChainFrom_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ∀ (fuel e c : Nat),
      evmChainFrom { s with locals := locals, clock := k } fuel e c = evmChainFrom s fuel e c
  | 0, _, _ => rfl
  | fuel + 1, e, c => by
    simp only [evmChainFrom, evmChainFrom_with_locals s locals k fuel]
    rfl

theorem evmChain_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    evmChain { s with locals := locals, clock := k } = evmChain s :=
  evmChainFrom_with_locals s locals k _ _ _

theorem localsFree_arenaReady : LocalsFree ArenaReady :=
  fun s locals k h => (arenaReady_with_locals s locals k).2 h

theorem localsFree_worldOK : LocalsFree WorldOK := by
  intro F s locals k h
  simp only [WorldOK, worldTyped_with_locals, arenaReady_with_locals] at h ⊢
  exact h

theorem localsFree_evmInv : LocalsFree EvmInv := by
  intro F s locals k h
  simp only [EvmInv, worldTyped_with_locals, arenaReady_with_locals, evmChain_with_locals] at h ⊢
  exact h

/-- Round-3 non-blocking: `main`'s guard reads neither locals nor the clock. -/
theorem localsFree_mainEntry : LocalsFree MainEntry := by
  intro F s locals k h
  obtain ⟨⟨hg, hc⟩, hm, hz⟩ := h
  exact ⟨⟨guestInv_with_locals_clock s locals k hg, hc⟩, hm, hz⟩

theorem localsOnly_mainEntry : LocalsOnly [] MainEntry :=
  LocalsOnly.of_localsFree localsFree_mainEntry

theorem localsFree_finishReady : LocalsFree FinishReady := by
  intro F s locals k h
  exact ⟨localsFree_evmInv s locals k h.1, h.2⟩

theorem localsFree_evmRun : LocalsFree EvmRun := by
  intro F s locals k h
  exact ⟨localsFree_evmInv s locals k h.1, h.2⟩

theorem localsOnly_htabArgWF : LocalsOnly ["t"] HtabArgWF := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "t" (hl "t" (by simp))
  simp only [HtabArgWF, htabWF_with_locals, arenaReady_with_locals] at hP ⊢
  rw [ht]
  exact hP

theorem localsOnly_unionArgWF : LocalsOnly ["dst"] UnionArgWF := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "dst" (hl "dst" (by simp))
  simp only [UnionArgWF, htabWF_with_locals, arenaReady_with_locals] at hP ⊢
  rw [ht]
  exact hP

theorem localsOnly_mptReady : LocalsOnly ["node", "key", "klen", "level"] MptReady := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "node" (hl "node" (by simp))
  have hk := locN_congr s locals k "key" (hl "key" (by simp))
  have hn := locN_congr s locals k "klen" (hl "klen" (by simp))
  have hv := locN_congr s locals k "level" (hl "level" (by simp))
  simp only [MptReady, arenaReady_with_locals] at hP ⊢
  rw [ht, hk, hn, hv]
  exact hP

theorem localsOnly_mptObjReady : LocalsOnly ["m"] MptObjReady := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "m" (hl "m" (by simp))
  simp only [MptObjReady, MptObjAvoids, MptObjIn, worldTyped_with_locals, arenaReady_with_locals]
    at hP ⊢
  rw [ht]
  exact hP

theorem localsOnly_rollbackReady : LocalsOnly ["child"] RollbackReady := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "child" (hl "child" (by simp))
  simp only [RollbackReady, htabWF_with_locals, arenaReady_with_locals] at hP ⊢
  rw [ht]
  exact hP

theorem localsOnly_htabNewReady : LocalsOnly ["key_len", "cap"] HtabNewReady := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "key_len" (hl "key_len" (by simp))
  have hc := locN_congr s locals k "cap" (hl "cap" (by simp))
  simp only [HtabNewReady, arenaReady_with_locals] at hP ⊢
  rw [ht, hc]
  exact hP

/-- Regression for `dec_onLocals`: `htab_truncate`'s body declares `stride`, `pos`, `leaf`, never
`t`, so `HtabArgWF` passes every `dec` of the body. -/
example : ∀ n ∈ ["t"], ofString n ≠ ofString "pos" := by decide

/-! ### Callee contracts for the guarded compositions (round-3 recommendation, item 5)

Each guarded body (`gbody_*`, below) is composed from its callees' bounds and, at every call site
that is followed by a guarded call or a guarded loop head (computed by `coverage.py`, DESIGN.md
§6), a contract that carries the caller's world guard across the call. A contract only speaks
about outcomes that resume the caller: a normal return, or an exception other than `TrapErr`
(`trap_with` is the only raiser of `TrapErr`, after its FFI call, and no handler in the program
catches it). Three uniform shapes, chosen mechanically:
* `ReadOnlyFn`: the callee (transitively) has no store, no global assignment and no FFI call
  (`trap_with` aside), so it changes nothing but its own locals and the clock;
* `WritesWithin R`: the callee writes only the region `R` (its pointer parameters' extents and the
  global scratch buffers it uses), memory that is free at entry (above `heap_ptr`, between
  `frame_mem_ptr` and `scratch_ptr`) and the allocator globals it lists; true for arbitrary
  states, the caller shows `R` is unowned;
* `KeepsOn P W`: from a `P` entry the callee ends in a `W` state (the reviewers'
  `PreservesOn WorldOK WorldOK`, restricted to resuming outcomes). -/

/-- The outcomes after which the caller resumes (return, or a catchable exception). -/
def Resumes (r : Option (PanSemResultExact 64)) : Prop :=
  (∃ v, r = some (.returned v)) ∨ ∃ e v, r = some (.exception e v) ∧ e ≠ ofString "TrapErr"

/-- `fname` changes nothing but locals and clock. -/
def ReadOnlyFn (fname : MlS) : Prop :=
  FunSpec GuestInv (fun s r post => Resumes r → post = { s with locals := post.locals, clock := post.clock })
    fname

/-- From a `P` entry, every resuming outcome is a `W` state. -/
def KeepsOn (P W : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (fname : MlS) : Prop :=
  FunSpec P (fun _ r post => Resumes r → W post) fname

/-- Write frame: on every resuming outcome the arenas stay separated and only grow, memory changes
only inside `R s` and the memory free at entry, and only the globals in `gw` change. -/
def WritesWithin (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) (gw : List String)
    (fname : MlS) : Prop :=
  FunSpec ArenaReady (fun s r post => Resumes r →
    ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    FrameOutside s post
      (R s ++ [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr") ∧
    ∀ name, name ∉ gw → s.globals.lookup (ofString name) = post.globals.lookup (ofString name))
    fname

/-- `WorldOK`, and the regions `R s` are disjoint from every typed table and fixed object and
(revision 6, round-4 Astra item 2) from the persistent tries (`AvoidsTries`, same `S`): the output
buffers of `compute_state_root`/`build_mpt_indexed` must not overwrite a trie node or path. -/
def WorldAvoids (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, WorldTyped s S ∧ (∀ i ∈ R s,
    (∀ t ∈ S, ∀ j ∈ htabFootprint s t, Disj i j) ∧ ∀ j ∈ fixedObjects s, Disj i j) ∧
    AvoidsTries s S (R s)

/-- `process_transaction(tx, index)` writes the receipt slots `bo+24`/`bo+32` at `16·index`
(33368-33374): the index is below the block's transaction count `bo+80` (`execute_block`'s loop). -/
def TxReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ locN s "index" < memW s (globN s "bo" + 80)

/-- `execute_block(si, hdr)` (revision 5, round-4 non-blocking): the transaction count
`ntx = (si+0)+40` (33588) sizes the arrays `alloc(16·ntx + 16)` (33593, 33596) without wrapping,
so `blockOutObjects` (unwrapped length `16·(bo+80) + 16`) is the block `alloc` returns. -/
def BlockReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ 16 * memW s (memW s (locN s "si") + 40) + 16 < 2 ^ 64

theorem localsOnly_blockReady : LocalsOnly ["si"] BlockReady := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "si" (hl "si" (by simp))
  refine ⟨localsFree_worldOK s locals k hP.1, ?_⟩
  show 16 * memW s (memW s (locN { s with locals := locals, clock := k } "si") + 40) + 16 < 2 ^ 64
  rw [ht]; exact hP.2

/-- `process_general_purpose_requests` runs once per block, right after `execute_block` zeroed
`bo` (so no request is recorded yet); it appends at most three requests (`requests_append` 33485
writes slot `bo+64` of the 8-slot array `bo+56`). -/
def ReqsFresh : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ memW s (globN s "bo" + 64) = 0

/-- Entry of `process_message_call`, `process_create_message` and `process_message`: the world is
typed by a set `S` that contains the message's two access tables `msg+152`, `msg+160` (copied into
the outermost frame's `e+168`/`e+176` by `frame_new` 15418-15420). Every caller builds them with
`htab_new` just before (`process_transaction` 33343-33346, `process_unchecked_system_transaction`
32899-32902). Round-3 Gemini item 3: the 176-byte message record (`msg_new`) is owned, so the stores
`depth0_prepare`/`prepare_dispatch` make through it (`msg+48`, `+104`, `+112`, `+120`, `+168`)
cannot reach a table or fixed object; its gas `msg+40` (`mgas ≤ 16777216` after
`validate_transaction`, `30000000` for system calls) bounds the initial `R` of `EvmInv`.
Revision 6 (round-4 Astra item 2): the record also avoids the persistent tries (`AvoidsTries`);
every caller passes a fresh `msg_new` block. -/
def MsgReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, WorldTyped s S ∧
    memW s (locN s "msg" + 152) ∈ S ∧ memW s (locN s "msg" + 160) ∈ S ∧
    Allocated s (locN s "msg", 176) ∧ WordsOK s (locN s "msg", 176) ∧
    (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (locN s "msg", 176) i) ∧
    (∀ j ∈ fixedObjects s, Disj (locN s "msg", 176) j) ∧
    AvoidsTries s S [(locN s "msg", 176)] ∧
    memW s (locN s "msg" + 40) < 2 ^ 63

/-- `frame_open(msg, 0)` in `process_message`: builds the outermost frame, after which `EvmInv`
holds (closed one-frame chain; its blocks are fresh scratch/frame memory; its tables are the
message's typed tables and a fresh `htab_new_scratch` table). -/
def FrameOpenReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => MsgReady s ∧ locN s "kind" = 0

theorem msgReady_worldOK {F : Type} (s : PanSemStateFiniteExact 64 F) (h : MsgReady s) :
    WorldOK s :=
  ⟨h.1, h.2.elim fun S hS => ⟨S, hS.1⟩⟩

theorem localsOnly_msgReady : LocalsOnly ["msg"] MsgReady := by
  intro F s locals k hl hP
  have hm := locN_congr s locals k "msg" (hl "msg" (by simp))
  simp only [MsgReady, worldTyped_with_locals, arenaReady_with_locals] at hP ⊢
  rw [hm]
  exact hP

theorem localsOnly_frameOpenReady : LocalsOnly ["msg", "kind"] FrameOpenReady := by
  intro F s locals k hl hP
  have hk := locN_congr s locals k "kind" (hl "kind" (by simp))
  refine ⟨localsOnly_msgReady s locals k (fun n hn => hl n (by simp at hn ⊢; exact Or.inl hn)) hP.1, ?_⟩
  show locN { s with locals := locals, clock := k } "kind" = 0
  rw [hk]; exact hP.2

/-- `EvmInv` with its table set `S` exposed (revision 5): the body of `EvmInv` after `∃ S`,
verbatim, so that a guard can state more facts about the same `S` (`evmInv_iff_at`, by `Iff.rfl`). -/
def EvmInvAt {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  WorldTyped s S ∧
    let ch := evmChain s
    ch ≠ [] ∧ ch.length ≤ maxChain ∧ (∃ ec ∈ ch.getLast?, memW s (ec.2 + 16) = 0) ∧
    (∀ ec ∈ ch, FrameWF s S ec) ∧ (∀ ec ∈ ch.tail, FrameRoom s ec) ∧ RetWindowsOK s ch ∧
    ((ch.map (frameObjects s)).flatten).Pairwise Disj ∧
    (∀ ec ∈ ch, ∀ o ∈ frameObjects s ec,
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj o i) ∧ ∀ j ∈ fixedObjects s, Disj o j) ∧
    AvoidsTries s S (ch.map (frameObjects s)).flatten ∧
    MarksOK s S ch ∧
    (ch.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum + 1 < 2 ^ 64

theorem evmInv_iff_at {F : Type} (s : PanSemStateFiniteExact 64 F) :
    EvmInv s ↔ ArenaReady s ∧ ∃ S, EvmInvAt s S := Iff.rfl

/-- The 176-byte message record at `m` is owned (as in `MsgReady`): allocated words, disjoint
from every table footprint of `S`, every fixed object, every frame block of the chain and
(revision 6, round-4 Astra item 2) the persistent tries. -/
def MsgOwned {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) (m : Nat) : Prop :=
  Allocated s (m, 176) ∧ WordsOK s (m, 176) ∧
  (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (m, 176) i) ∧
  (∀ j ∈ fixedObjects s, Disj (m, 176) j) ∧
  (∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj (m, 176) o) ∧
  AvoidsTries s S [(m, 176)]

/-- After `frame_open(msg, 0)` in `process_message` (revision 5, round-4 Fable item 2): `EvmInv`,
and the outermost frame's message `ev+112` (the `msg` of `MsgReady`, stored by `frame_new`) is
still owned, for the same table set. `depth0_prepare` stores `msg+48` (18772) and
`prepare_dispatch`, its only caller's callee, `msg+112`, `msg+120` (17836); `EvmInv` alone does not
own `ev+112` (a message at `t − 112` for a typed table `t` overwrote its key length). Only depth
`0` writes through the message, so `frameObjects` (all depths) is unchanged. -/
def EvmMsgReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, EvmInvAt s S ∧ MsgOwned s S (memW s (globN s "ev" + 112))

theorem evmInv_of_evmMsgReady {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmMsgReady s) :
    EvmInv s :=
  ⟨h.1, h.2.elim fun S hS => ⟨S, hS.1⟩⟩

theorem localsFree_evmMsgReady : LocalsFree EvmMsgReady := by
  intro F s locals k h
  simp only [EvmMsgReady, EvmInvAt, MsgOwned, worldTyped_with_locals, arenaReady_with_locals,
    evmChain_with_locals] at h ⊢
  exact h

/-- The node parameter `x` is a node of `Nd` of kind `k` (revision 6, round-4 Astra item 6). -/
def NodeKind {F : Type} (s : PanSemStateFiniteExact 64 F) (Nd : List Nat) (x : String) (k : Nat) :
    Prop :=
  locN s x ∈ Nd ∧ memW s (locN s x) = k

/-- MPT-tier callee entry (round-3 item 5, DESIGN.md Q9): separated arenas, the listed node
parameters are rooted in a typed node heap `Nd`, and the function's own requirement `req s Nd`
(revision 6, round-4 Astra items 5 and 6): the node kinds it reads and writes (`NodeKind`), and
the nibble arrays it indexes or copies into a node path (`KeyIn`). -/
def NodeArgs (names : List String)
    (req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd, NodeHeap s Nd ∧ (∀ n ∈ names, RootIn Nd (locN s n)) ∧ req s Nd

/-- MPT-tier callee exit, `MptExit`-shaped: every typed node set satisfying the entry extends to a
typed node set of the post-state; memory changes only inside those node records, the free scratch
gap and the heap free at entry; the returned word is a typed node or `0` (what `_mpt_insert_node` /
`_mpt_delete_node_body` need to re-establish `MptReady` at their loop heads). The node functions
write no global buffer (checked on their closures). Revision 6: the old nodes keep their kinds and
every new node of `Nd'` is a fresh heap record (all seven functions write node fields `+8` and
beyond, and build nodes only with `alloc`). The callers' loop invariants need both: a saved
extension stays an extension until `_delete_ext_finish`, and a key or saved path stays disjoint
from the grown node set. -/
def NodeFnExit (names : List String)
    (req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => Resumes r → ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
    ∀ Nd, NodeHeap s Nd → (∀ n ∈ names, RootIn Nd (locN s n)) → req s Nd →
      ∃ Nd', NodeHeap post Nd' ∧ (∀ n ∈ Nd, n ∈ Nd') ∧
        (∀ n ∈ Nd, memW post n = memW s n) ∧
        (∀ n ∈ Nd', n ∈ Nd ∨ Inside (nodeIvl post n) (globN s "heap_ptr") (globN post "heap_ptr")) ∧
        FrameOutside s post
          ((Nd.map fun n => nodeIvl s n) ++
            [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
          (globN s "heap_ptr", heapLimit - globN s "heap_ptr") ∧
        (∀ name, name ∉ ["heap_ptr", "scratch_ptr"] →
          s.globals.lookup (ofString name) = post.globals.lookup (ofString name)) ∧
        ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat

/-- `NodeFn names req g`: from a typed node heap rooting `names` and meeting `g`'s requirement
`req` (node kinds, key arrays; DESIGN.md §6 "NodeFn requirements"), `g` ends in a typed node heap. -/
def NodeFn (names : List String)
    (req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop) (fname : MlS) : Prop :=
  FunSpec (NodeArgs names req) (NodeFnExit names req) fname

/-- Value contract (revision 6): a normal return is a word at most `B` of the entry state.
`common_prefix_length(a, al, b, bl)` returns `i < min(al, bl)` or `min(al, bl)` (AST 10512); the
MPT loops need `pl ≤ sl` and `pl ≤ klen − level` to keep `level ≤ klen` and to meet
`_split_extension`'s requirement `pl < sl`. -/
def RetLe (B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat) (fname : MlS) : Prop :=
  FunSpec GuestInv (fun s r _ => ∀ v, r = some (.returned v) →
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ B s) fname

/-- Value contract (revision 6): a normal return is a pair `(p, l)` of a nibble array allocated
fresh on the heap during the call. `mpt_nibble_key` (AST 10470) returns `alloc(64)` filled by
`key_to_nibbles` from the 32-byte hash, or `alloc(2·klen)` filled from the key: the key
`_mpt_insert_node`/`_mpt_delete_node` receive from `mpt_set` (`MptReady`'s `KeyIn`). -/
def RetNibbles (fname : MlS) : Prop :=
  FunSpec ArenaReady (fun s r post => ∀ v, r = some (.returned v) →
    ∃ p l : BitVec 64, v = .rStruct [.val (.word p), .val (.word l)] ∧
      NibblesOK post p.toNat l.toNat ∧
      Inside (p.toNat, l.toNat) (globN s "heap_ptr") (globN post "heap_ptr")) fname

/-- `requests_append` entry: the next request slot exists. -/
def ReqRoom : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ memW s (globN s "bo" + 64) < 8

/-- A read-only callee keeps every guard that ignores locals and the clock (proved). -/
theorem ReadOnlyFn.keepsOn {W : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hW : LocalsFree W) (hG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), W s → GuestInv s)
    {fname : MlS} (h : ReadOnlyFn fname) : KeepsOn W W fname := by
  obtain ⟨params, body, ret, hlook, hb⟩ := h
  refine ⟨params, body, ret, hlook, fun s hc hWs hnt hr => ?_⟩
  rw [hb s hc (hG s hWs) hnt hr]
  exact hW s _ _ hWs

theorem worldOK_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F) (h : WorldOK s) :
    GuestInv s := h.1.1

theorem evmInv_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    GuestInv s := h.1.1

/-- `EvmInv` implies `WorldOK` (the frame-level guard is stronger). -/
theorem worldOK_of_evmInv {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    WorldOK s :=
  ⟨h.1, h.2.elim fun S hS => ⟨S, hS.1⟩⟩

theorem localsOnly_txReady : LocalsOnly ["index"] TxReady := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "index" (hl "index" (by simp))
  refine ⟨localsFree_worldOK s locals k hP.1, ?_⟩
  show locN { s with locals := locals, clock := k } "index" < memW s (globN s "bo" + 80)
  rw [ht]; exact hP.2

theorem localsFree_reqsFresh : LocalsFree ReqsFresh :=
  fun s locals k h => ⟨localsFree_worldOK s locals k h.1, h.2⟩

/-! ### Outcome triples (proved rules, used to prove the frame glue)

`Hoare P prog Q`: every non-timeout run of `prog` from a `P` state ends with result `r` in a state
`t` such that `Q r t`. Relational facts are carried by ghost numbers inside `P`/`Q`. -/

structure Hoare (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (prog : ProgHOL 64)
    (Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop) :
    Prop where
  run : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
    (evaluateHOLFiniteState s prog).1 ≠ some .timeOut →
    Q (evaluateHOLFiniteState s prog).1 (evaluateHOLFiniteState s prog).2

section HoareRules

variable {P P' R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
  {Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}

theorem Hoare.of_false {prog : ProgHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → False) : Hoare P prog Q :=
  ⟨fun s _ hP _ => (h s hP).elim⟩

theorem Hoare.mono {prog : ProgHOL 64} (h : Hoare P' prog Q)
    (hPP : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P' s) : Hoare P prog Q :=
  ⟨fun s hcode hP hnt => h.run s hcode (hPP s hP) hnt⟩

theorem Hoare.skip
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q none s) :
    Hoare P .skip Q := by
  refine ⟨fun {F} s _ hP _ => ?_⟩
  rw [evaluateHOLFiniteState_skip]
  exact h s hP

theorem Hoare.seq {first second : ProgHOL 64}
    (h1 : Hoare P first fun r t => (r = none → R t) ∧ (r ≠ none → Q r t))
    (h2 : Hoare R second Q) : Hoare P (.seq first second) Q := by
  refine ⟨fun {F} s hcode hP hnt => ?_⟩
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s first).1
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr : evaluateHOLFiniteState s first with ⟨r1, m⟩
  simp only [hr] at hnt hmeta ⊢
  change m.code = s.code at hmeta
  cases r1 with
  | none =>
    have h := h1.run s hcode hP (by rw [hr]; simp)
    rw [hr] at h
    exact h2.run m (hmeta.trans hcode) (h.1 rfl) hnt
  | some r =>
    have h := h1.run s hcode hP (by rw [hr]; exact hnt)
    rw [hr] at h
    exact h.2 (by simp)

theorem Hoare.ite {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hyes : Hoare (fun s => P s ∧ CondTrue cond s) yes Q)
    (hno : Hoare (fun s => P s ∧ CondFalse cond s) no Q)
    (herr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q (some .error) s) :
    Hoare P (.ite cond yes no) Q := by
  refine ⟨fun {F} s hcode hP hnt => ?_⟩
  rw [evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split <;> intro hnt
  · rename_i w hw
    revert hnt
    split <;> intro hnt
    · rename_i hz
      subst hz
      exact hno.run s hcode ⟨hP, hw⟩ hnt
    · rename_i hz
      exact hyes.run s hcode ⟨hP, w, hw, hz⟩ hnt
  · exact herr s hP

theorem resVarEq_lookup_ne (m : HolFiniteMapExact MlS (ValueHOL 64)) (name n : MlS)
    (o : Option (ValueHOL 64)) (h : n ≠ name) :
    (HolFiniteMapExact.resVarEq m (name, o)).lookup n = m.lookup n := by
  rcases o with _ | v
  · simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.eraseEq, FDOMSUB_HOL, h]
  · simp only [HolFiniteMapExact.resVarEq, HolFiniteMapExact.updateEq, FUPDATE_HOL]
    split
    · rename_i heq; exact absurd heq h
    · rfl

/-- `Q` does not read the locals outside `names`. -/
def PostLocalsOnly (names : List String)
    (Q : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop) :
    Prop :=
  ∀ {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)),
    (∀ n ∈ names, locals.lookup (ofString n) = t.locals.lookup (ofString n)) →
    Q r t → Q r { t with locals := locals }

theorem Hoare.dec {names : List String} {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64}
    {body : ProgHOL 64} (hname : ∀ n ∈ names, ofString n ≠ name)
    (hinit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init =
        some v → P' (setVarHOLFinite name v s))
    (hbody : Hoare P' body Q) (hQ : PostLocalsOnly names Q)
    (herr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q (some .error) s) :
    Hoare P (.dec name shape init body) Q := by
  refine ⟨fun {F} s hcode hP hnt => ?_⟩
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact herr s hP
  · rename_i v hv
    revert hnt
    split <;> intro hnt
    · have hb := hbody.run (setVarHOLFinite name v s) hcode (hinit s v hP hv) hnt
      exact hQ _ _ _ (fun n hn => resVarEq_lookup_ne _ _ _ _ (hname n hn)) hb
    · exact herr s hP

theorem Hoare.assign {kind : VarKind} {name : MlS} {source : ExpHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) source =
        some v → Q none (setKvarHOLFinite kind name v s))
    (herr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q (some .error) s) :
    Hoare P (.assign kind name source) Q := by
  refine ⟨fun {F} s hcode hP hnt => ?_⟩
  rw [evaluateHOLFiniteState_assign] at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact herr s hP
  · rename_i v hv
    revert hnt
    split <;> intro hnt
    · exact h s v hP hv
    · exact herr s hP

/-- The installed body of a `FunSpec` function, at a successful lookup. -/
theorem FunSpec.at_lookup {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop} {fname : MlS}
    (hf : FunSpec Pc Qc fname) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (hcode : state.code = originalRuntimeCode) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hl : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret'))
    (hPc : Pc (callEntryStateHOLFinite state callee))
    (hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body').1 ≠
      some .timeOut) :
    Qc (callEntryStateHOLFinite state callee)
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body').1
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body').2 := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  have hsame := lookupCodeHOLFinite_installed_body state.code.lookup fname params body body'
    ret ret' values callee (by rw [hcode]; exact hlook) hl
  subst hsame
  exact hspec _ hcode hPc hnt

/-- Handler-free call with no destination, callee described by a `FunSpec`. Results other than
a normal return are covered by `hother` (a call never yields `continue`). -/
theorem Hoare.call0 {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop} {fname : MlS} {arguments : List (ExpHOL 64)}
    (hf : FunSpec Pc Qc fname) (hentry : CallEntryOn P Pc fname arguments)
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (post : PanSemStateFiniteExact 64 F)
      (v : ValueHOL 64), s.code = originalRuntimeCode → P s →
      Qc (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      Q none { post with locals := s.locals })
    (hother : ∀ {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F),
      r ≠ none → r ≠ some .continue → Q r t) :
    Hoare P (.call (some (none, none)) fname arguments) Q := by
  refine ⟨fun {F} s hcode hP hnt => ?_⟩
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) arguments with
    _ | values
  · exact hother _ _ (by simp) (by simp)
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact hother _ _ (by simp) (by simp)
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hPc := hentry s values body' callee ret' hcode hP hargs hl
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt ⊢
        have hQc (hsafe : res ≠ some .timeOut) : Qc (callEntryStateHOLFinite s callee) res post := by
          have := FunSpec.at_lookup hf s hcode values body' callee ret' hl hPc (by rw [hrun]; exact hsafe)
          rw [hrun] at this
          exact this
        cases res with
        | none => exact hother _ _ (by simp) (by simp)
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            split
            · exact hret s callee post v hcode hP (hQc (by simp))
            · exact hother _ _ (by simp) (by simp)
          | timeOut => simp at hnt
          | _ => exact hother _ _ (by simp) (by simp)

/-- Call with an exception handler and no destination: the handler runs on
`setVar var v {post with locals := caller locals}` after the callee raised `exn`. -/
theorem Hoare.callH {Pc Ph : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop} {fname : MlS} {arguments : List (ExpHOL 64)}
    {exn var : MlS} {handler : ProgHOL 64}
    (hf : FunSpec Pc Qc fname) (hentry : CallEntryOn P Pc fname arguments)
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (post : PanSemStateFiniteExact 64 F)
      (v : ValueHOL 64), s.code = originalRuntimeCode → P s →
      Qc (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      Q none { post with locals := s.locals })
    (hexn : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (post : PanSemStateFiniteExact 64 F)
      (v : ValueHOL 64), s.code = originalRuntimeCode → P s →
      Qc (callEntryStateHOLFinite s callee) (some (.exception exn v)) post →
      Ph (setVarHOLFinite var v { post with locals := s.locals }))
    (hh : Hoare Ph handler Q)
    (hother : ∀ {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F),
      r ≠ none → r ≠ some .continue → Q r t) :
    Hoare P (.call (some (none, some (exn, var, handler))) fname arguments) Q := by
  refine ⟨fun {F} s hcode hP hnt => ?_⟩
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) arguments with
    _ | values
  · exact hother _ _ (by simp) (by simp)
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact hother _ _ (by simp) (by simp)
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hPc := hentry s values body' callee ret' hcode hP hargs hl
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite s callee) body').1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt hmeta ⊢
        change post.code = s.code at hmeta
        have hQc (hsafe : res ≠ some .timeOut) : Qc (callEntryStateHOLFinite s callee) res post := by
          have := FunSpec.at_lookup hf s hcode values body' callee ret' hl hPc (by rw [hrun]; exact hsafe)
          rw [hrun] at this
          exact this
        cases res with
        | none => exact hother _ _ (by simp) (by simp)
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            split
            · exact hret s callee post v hcode hP (hQc (by simp))
            · exact hother _ _ (by simp) (by simp)
          | timeOut => simp at hnt
          | exception eid v =>
            dsimp only at hnt ⊢
            by_cases hid : eid = exn
            · subst hid
              simp only [↓reduceIte] at hnt ⊢
              rcases hsh : s.eshapes.lookup eid with _ | shape
              · exact hother _ _ (by simp) (by simp)
              · simp only [hsh] at hnt ⊢
                by_cases hv : (shapeEqHOL (shapeOfHOLExact v) shape &&
                    isValidValueHOLExact s.toExact .local var v) = true
                · simp only [hv, ↓reduceIte] at hnt ⊢
                  exact hh.run _ (by simp [setVarHOLFinite]; exact hmeta.trans hcode)
                    (hexn s callee post v hcode hP (hQc (by simp))) hnt
                · simp only [hv, Bool.false_eq_true, ↓reduceIte]
                  exact hother _ _ (by simp) (by simp)
            · simp only [hid, ↓reduceIte]
              exact hother _ _ (by simp) (by simp)
          | _ => exact hother _ _ (by simp) (by simp)

end HoareRules

/-! ### Evaluating the `run_frames` loop tests -/

/-- Evaluation of an expression at a state (the decider every rewrite lemma uses). -/
noncomputable abbrev evalAt {F : Type} (t : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    Option (ValueHOL 64) :=
  @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e

theorem evalAt_cmp {F : Type} (t : PanSemStateFiniteExact 64 F) (op : Cmp) (l r : ExpHOL 64)
    (w : BitVec 64) (h : evalAt t (.cmp op l r) = some (.val (.word w))) :
    ∃ a b : BitVec 64, evalAt t l = some (.val (.word a)) ∧ evalAt t r = some (.val (.word b)) ∧
      w = if Flapjack.Compiler.Encoders.Asm.wordCmpHOL op a b then 1 else 0 := by
  simp only [evalAt, evalHOLExact] at h ⊢
  split at h
  · rename_i a b ha hb
    exact ⟨a, b, ha, hb, (by simpa using h.symm)⟩
  · cases h

theorem evalAt_const {F : Type} (t : PanSemStateFiniteExact 64 F) (k : BitVec 64)
    (v : ValueHOL 64) (h : evalAt t (.const k) = some v) : v = .val (.word k) := by
  simp only [evalAt, evalHOLExact] at h
  cases h; rfl

theorem evalAt_local {F : Type} (t : PanSemStateFiniteExact 64 F) (n : String) (a : BitVec 64)
    (h : evalAt t (.var .local (ofString n)) = some (.val (.word a))) : a.toNat = locN t n := by
  simp only [evalAt, evalHOLExact] at h
  simp [locN] at h ⊢
  rw [h]

theorem evalAt_loadG' {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k a : BitVec 64)
    (h : evalAt t (.load .one (.op .add [.var .global (ofString g), .const k])) =
      some (.val (.word a))) :
    a.toNat = memW t (globN t g + k.toNat) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hg : t.globals.lookup (ofString g) with _ | v
  · simp [hg] at h
  · rcases v with x | fs | ⟨nm, fs⟩
    · cases x with
      | word x =>
        simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
        have hadd : BitVec.ofNat 64 (x.toNat + k.toNat) = x + k := by
          rw [BitVec.add_def]
        simp only [globN, memW, hg, hadd, h.2]
    · simp [hg, valueIsWord] at h
    · simp [hg, valueIsWord] at h

/-- A one-word load from `global + k` that succeeds yields the word `memW t (globN t g + k)`. -/
theorem evalAt_loadG {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k : BitVec 64)
    (v : ValueHOL 64)
    (h : evalAt t (.load .one (.op .add [.var .global (ofString g), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW t (globN t g + k.toNat) := by
  have hv : ∃ a : BitVec 64, v = .val (.word a) := by
    simp [evalAt, evalHOLExact, evalListHOLExact] at h
    rcases hg : t.globals.lookup (ofString g) with _ | w
    · simp [hg] at h
    · rcases w with x | fs | ⟨nm, fs⟩
      · cases x with
        | word x =>
          simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
          rcases hm : t.memory (x + k) with ⟨y⟩
          exact ⟨y, by rw [← h.2, hm]⟩
      · simp [hg, valueIsWord] at h
      · simp [hg, valueIsWord] at h
  obtain ⟨a, rfl⟩ := hv
  exact ⟨a, rfl, evalAt_loadG' t g k a h⟩

theorem locN_setVar_same {F : Type} (t : PanSemStateFiniteExact 64 F) (n : String)
    (w : BitVec 64) : locN (setVarHOLFinite (ofString n) (.val (.word w)) t) n = w.toNat := by
  simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

theorem locN_setVar_ne {F : Type} (t : PanSemStateFiniteExact 64 F) (n : String) (m : MlS)
    (v : ValueHOL 64) (h : ofString n ≠ m) : locN (setVarHOLFinite m v t) n = locN t n := by
  have hl : (t.locals.update (m, v)).lookup (ofString n) = t.locals.lookup (ofString n) := by
    simp [HolFiniteMapExact.update, FUPDATE, Ne.symm h]
  simp only [locN, setVarHOLFinite, hl]

/-! ### The EVM potential reads only memory and globals -/

def evmFp {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  2 * (evmChain s).length + (if EvmDone s then 0 else 1)

def evmS {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  ((evmChain s).map fun ec => memW s (ec.1 + 72)).sum

theorem evmPot_eq {F : Type} (s : PanSemStateFiniteExact 64 F) :
    evmPot s = evmR s * (evmPotF * evmPotS) + evmFp s * evmPotS + evmS s := rfl

theorem memW_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : t.memory = s.memory) :
    memW t = memW s := by
  funext a; simp [memW, h]

theorem globN_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : t.globals = s.globals) :
    globN t = globN s := by
  funext a; simp [globN, h]

theorem evmChainFrom_congr {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : t.memory = s.memory) :
    ∀ (fuel e c : Nat), evmChainFrom t fuel e c = evmChainFrom s fuel e c
  | 0, _, _ => rfl
  | fuel + 1, e, c => by
    simp only [evmChainFrom, memW_congr h, evmChainFrom_congr h fuel]

theorem evmChain_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (hm : t.memory = s.memory)
    (hg : t.globals = s.globals) : evmChain t = evmChain s := by
  simp only [evmChain, evmChainFrom_congr hm, globN_congr hg]

theorem evmDone_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (hm : t.memory = s.memory)
    (hg : t.globals = s.globals) : EvmDone t ↔ EvmDone s := by
  simp only [EvmDone, memW_congr hm, globN_congr hg]

theorem evm_congr {F : Type} {s t : PanSemStateFiniteExact 64 F} (hm : t.memory = s.memory)
    (hg : t.globals = s.globals) :
    evmPot t = evmPot s ∧ evmR t = evmR s ∧ (evmChain t).length = (evmChain s).length ∧
      evmFp t = evmFp s := by
  have hc := evmChain_congr hm hg
  have hd := evmDone_congr hm hg
  refine ⟨?_, ?_, by rw [hc], ?_⟩
  · simp only [evmPot, hc, memW_congr hm, hd]
  · simp only [evmR, hc, memW_congr hm]
  · simp only [evmFp, hc, hd]

theorem memW_lt {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) : memW s a < 2 ^ 64 := by
  unfold memW
  split
  rename_i w _
  exact w.isLt

theorem sum_map_memW_le {F : Type} (s : PanSemStateFiniteExact 64 F) (off : Nat) :
    ∀ l : List Ivl, (l.map fun ec => memW s (ec.1 + off)).sum ≤ l.length * (2 ^ 64 - 1)
  | [] => by simp
  | x :: xs => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := memW_lt s (x.1 + off)
    have h2 := sum_map_memW_le s off xs
    omega

theorem evmInv_len {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    (evmChain s).length ≤ maxChain := by
  obtain ⟨_, S, hS⟩ := h
  exact hS.2.2.1

theorem evmS_lt {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) : evmS s < evmPotS := by
  have hlen := evmInv_len s h
  have hle := sum_map_memW_le s 72 (evmChain s)
  have hm : (evmChain s).length * (2 ^ 64 - 1) < maxChain * 2 ^ 64 := by
    have : (evmChain s).length * (2 ^ 64 - 1) ≤ maxChain * (2 ^ 64 - 1) :=
      Nat.mul_le_mul_right _ hlen
    simp only [maxChain] at this ⊢
    omega
  show ((evmChain s).map fun ec => memW s (ec.1 + 72)).sum < maxChain * 2 ^ 64
  omega

theorem evmFp_lt {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    evmFp s < evmPotF := by
  have hlen := evmInv_len s h
  unfold evmFp evmPotF
  simp only [maxChain] at hlen ⊢
  split <;> omega

/-- The decrease argument of `run_frames`: under `EvmInv`, `R` not larger and `F` strictly
smaller is below any potential with those `R`, `F` components. -/
theorem evmPot_lt_bound {F : Type} (t : PanSemStateFiniteExact 64 F) (h : EvmInv t) {R0 F0 : Nat}
    (hR : evmR t ≤ R0) (hF : evmFp t < F0) :
    evmPot t < R0 * (evmPotF * evmPotS) + F0 * evmPotS := by
  have hS := evmS_lt t h
  have hFp := evmFp_lt t h
  rw [evmPot_eq]
  rcases Nat.lt_or_ge (evmR t) R0 with hlt | hge
  · have h1 : evmFp t * evmPotS + evmS t < evmPotF * evmPotS := by
      have : (evmFp t + 1) * evmPotS ≤ evmPotF * evmPotS := Nat.mul_le_mul_right _ hFp
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    have h2 : (evmR t + 1) * (evmPotF * evmPotS) ≤ R0 * (evmPotF * evmPotS) :=
      Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul] at h2
    have h3 : 0 ≤ F0 * evmPotS := Nat.zero_le _
    omega
  · have hReq : evmR t = R0 := le_antisymm hR hge
    have h2 : (evmFp t + 1) * evmPotS ≤ F0 * evmPotS := Nat.mul_le_mul_right _ hF
    rw [Nat.add_mul, Nat.one_mul] at h2
    rw [hReq]
    omega

theorem evmPot_ge {F : Type} (s : PanSemStateFiniteExact 64 F) :
    evmR s * (evmPotF * evmPotS) + evmFp s * evmPotS ≤ evmPot s := by
  rw [evmPot_eq]; omega

/-! ### Loop tests of `run_frames` -/

theorem cond_loadG {F : Type} (t : PanSemStateFiniteExact 64 F) (op : Cmp) (g : String)
    (k w : BitVec 64)
    (h : evalAt t (.cmp op (.load .one (.op .add [.var .global (ofString g), .const k]))
      (.const 0)) = some (.val (.word w))) :
    ∃ a : BitVec 64, a.toNat = memW t (globN t g + k.toNat) ∧
      w = if Flapjack.Compiler.Encoders.Asm.wordCmpHOL op a 0 then 1 else 0 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := evalAt_cmp t op _ _ w h
  obtain ⟨a', ha', hm⟩ := evalAt_loadG t g k _ ha
  cases ha'
  have hb' := evalAt_const t 0 _ hb
  cases hb'
  exact ⟨a, hm, rfl⟩

theorem condTrue_ne0 {F : Type} {t : PanSemStateFiniteExact 64 F} {g : String} {k : BitVec 64}
    (h : CondTrue (.cmp .notEqual (.load .one (.op .add [.var .global (ofString g), .const k]))
      (.const 0)) t) : memW t (globN t g + k.toNat) ≠ 0 := by
  obtain ⟨w, hw, hne⟩ := h
  obtain ⟨a, ha, rfl⟩ := cond_loadG t _ g k w hw
  rw [← ha]
  intro h0
  apply hne
  have : a = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
  subst this
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem condFalse_ne0 {F : Type} {t : PanSemStateFiniteExact 64 F} {g : String} {k : BitVec 64}
    (h : CondFalse (.cmp .notEqual (.load .one (.op .add [.var .global (ofString g), .const k]))
      (.const 0)) t) : memW t (globN t g + k.toNat) = 0 := by
  obtain ⟨a, ha, h0⟩ := cond_loadG t _ g k 0 h
  rw [← ha]
  by_cases hz : a = 0
  · subst hz; rfl
  · exfalso
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at h0
    exact hz h0

theorem condTrue_eq0 {F : Type} {t : PanSemStateFiniteExact 64 F} {g : String} {k : BitVec 64}
    (h : CondTrue (.cmp .equal (.load .one (.op .add [.var .global (ofString g), .const k]))
      (.const 0)) t) : memW t (globN t g + k.toNat) = 0 := by
  obtain ⟨w, hw, hne⟩ := h
  obtain ⟨a, ha, rfl⟩ := cond_loadG t _ g k w hw
  rw [← ha]
  by_cases hz : a = 0
  · subst hz; rfl
  · exfalso; apply hne
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    exact hz

theorem condFalse_eq0 {F : Type} {t : PanSemStateFiniteExact 64 F} {g : String} {k : BitVec 64}
    (h : CondFalse (.cmp .equal (.load .one (.op .add [.var .global (ofString g), .const k]))
      (.const 0)) t) : memW t (globN t g + k.toNat) ≠ 0 := by
  obtain ⟨a, ha, h0⟩ := cond_loadG t _ g k 0 h
  rw [← ha]
  intro hz
  have : a = 0 := BitVec.eq_of_toNat_eq (by simpa using hz)
  subst this
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at h0

theorem cond_local {F : Type} (t : PanSemStateFiniteExact 64 F) (op : Cmp) (n : String)
    (r : ExpHOL 64) (w : BitVec 64)
    (h : evalAt t (.cmp op (.var .local (ofString n)) r) = some (.val (.word w))) :
    ∃ a b : BitVec 64, a.toNat = locN t n ∧ evalAt t r = some (.val (.word b)) ∧
      w = if Flapjack.Compiler.Encoders.Asm.wordCmpHOL op a b then 1 else 0 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := evalAt_cmp t op _ _ w h
  exact ⟨a, b, evalAt_local t n a ha, hb, rfl⟩

theorem condTrue_local_ne0 {F : Type} {t : PanSemStateFiniteExact 64 F} {n : String}
    (h : CondTrue (.cmp .notEqual (.var .local (ofString n)) (.const 0)) t) : locN t n ≠ 0 := by
  obtain ⟨w, hw, hne⟩ := h
  obtain ⟨a, b, ha, hb, rfl⟩ := cond_local t _ n _ w hw
  cases evalAt_const t 0 _ hb
  rw [← ha]
  intro h0
  apply hne
  have : a = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
  subst this
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem condFalse_local_ne0 {F : Type} {t : PanSemStateFiniteExact 64 F} {n : String}
    (h : CondFalse (.cmp .notEqual (.var .local (ofString n)) (.const 0)) t) : locN t n = 0 := by
  obtain ⟨a, b, ha, hb, h0⟩ := cond_local t _ n _ 0 h
  cases evalAt_const t 0 _ hb
  rw [← ha]
  by_cases hz : a = 0
  · subst hz; rfl
  · exfalso
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at h0
    exact hz h0

theorem cond_notLower {F : Type} {t : PanSemStateFiniteExact 64 F} {n g : String} {k w : BitVec 64}
    (h : evalAt t (.cmp .notLower (.var .local (ofString n))
      (.load .one (.op .add [.var .global (ofString g), .const k]))) = some (.val (.word w))) :
    (w ≠ 0 → memW t (globN t g + k.toNat) ≤ locN t n) ∧
      (w = 0 → locN t n < memW t (globN t g + k.toNat)) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := cond_local t _ n _ w h
  obtain ⟨b', hb', hm⟩ := evalAt_loadG t g k _ hb
  cases hb'
  rw [← ha, ← hm]
  constructor
  · intro hw
    by_cases hlt : a < b
    · exfalso; apply hw; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt]
    · exact Nat.le_of_not_lt (fun hc => hlt (BitVec.lt_def.mpr hc))
  · intro hw
    by_cases hlt : a < b
    · exact BitVec.lt_def.mp hlt
    · exfalso; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt] at hw

/-! ### The glue, proved -/

section RunFramesGlue

variable (p0 R0 L0 F0 : Nat)

/-- Loop-head facts carried through the body: the potential components of the head. -/
def GPre : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => EvmInv t ∧ evmPot t = p0 ∧ evmR t = R0 ∧ (evmChain t).length = L0 ∧ evmFp t = F0

def GQ : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun r t => (r = none ∨ r = some .continue) → (EvmInv t ∧ evmPot t < p0) ∨ locN t "go" = 0

def GMid : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => (GPre p0 R0 L0 F0 t ∧ EvmDone t ∧ locN t "done" ≠ 0) ∨
    (EvmInv t ∧ evmPot t < p0 ∧ locN t "done" = 0)

def GA : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun r t => (r = none → GMid p0 R0 L0 F0 t) ∧ (r ≠ none → GQ p0 r t)

theorem gq_other {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F)
    (h1 : r ≠ none) (h2 : r ≠ some .continue) : GQ p0 r t := by
  intro h; rcases h with h | h <;> contradiction

theorem ga_other {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F)
    (h1 : r ≠ none) (h2 : r ≠ some .continue) : GA p0 R0 L0 F0 r t :=
  ⟨fun h => absurd h h1, fun _ => gq_other p0 r t h1 h2⟩

theorem gpre_congr {F : Type} {t u : PanSemStateFiniteExact 64 F} (hm : u.memory = t.memory)
    (hg : u.globals = t.globals) (hinv : EvmInv u) (h : GPre p0 R0 L0 F0 t) :
    GPre p0 R0 L0 F0 u := by
  obtain ⟨_, h1, h2, h3, h4⟩ := h
  obtain ⟨e1, e2, e3, e4⟩ := evm_congr hm hg
  exact ⟨hinv, e1.trans h1, e2.trans h2, e3.trans h3, e4.trans h4⟩

theorem evmInv_locals {F : Type} {t : PanSemStateFiniteExact 64 F}
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (h : EvmInv t) :
    EvmInv { t with locals := locals } :=
  localsFree_evmInv t locals t.clock h

theorem evmInv_setVar {F : Type} {t : PanSemStateFiniteExact 64 F} (n : MlS) (v : ValueHOL 64)
    (h : EvmInv t) : EvmInv (setVarHOLFinite n v t) :=
  localsFree_evmInv t _ t.clock h

theorem evmInv_entry {F : Type} {t : PanSemStateFiniteExact 64 F}
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (h : EvmInv t) :
    EvmInv (callEntryStateHOLFinite t callee) :=
  localsFree_evmInv t _ _ h

theorem gq_postLocals : PostLocalsOnly ["go"] (GQ p0) := by
  intro F r t locals hl h hr
  rcases h hr with ⟨hi, hp⟩ | hgo
  · left
    exact ⟨evmInv_locals locals hi, by rw [(evm_congr (s := t) (t := { t with locals := locals }) rfl rfl).1]; exact hp⟩
  · right
    rw [locN_congr t locals t.clock "go" (hl "go" (by simp))]
    exact hgo

theorem ga_postLocals : PostLocalsOnly ["go", "done"] (GA p0 R0 L0 F0) := by
  intro F r t locals hl h
  have hgo := hl "go" (by simp)
  have hdone := locN_congr t locals t.clock "done" (hl "done" (by simp))
  refine ⟨fun hr => ?_, fun hr => gq_postLocals p0 r t locals (fun n hn => by
    simp at hn; subst hn; exact hgo) (h.2 hr)⟩
  rcases h.1 hr with ⟨hp, hd, hn⟩ | ⟨hi, hp, hn⟩
  · left
    refine ⟨gpre_congr p0 R0 L0 F0 (t := t) (u := { t with locals := locals }) rfl rfl
      (evmInv_locals locals hp.1) hp, ?_, ?_⟩
    · exact (evmDone_congr (s := t) (t := { t with locals := locals }) rfl rfl).2 hd
    · change locN { t with locals := locals, clock := t.clock } "done" ≠ 0
      rw [hdone]; exact hn
  · right
    refine ⟨evmInv_locals locals hi, ?_, ?_⟩
    · rw [(evm_congr (s := t) (t := { t with locals := locals }) rfl rfl).1]; exact hp
    · change locN { t with locals := locals, clock := t.clock } "done" = 0
      rw [hdone]; exact hn

end RunFramesGlue

/-- `run_frames` is the 585th declaration of the AST. -/
theorem lookup_run_frames :
    originalRuntimeCode.lookup (ofString "run_frames") =
      some ((sourceFunctionEntry Guest.Software.guestFn_run_frames).2) := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 584 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_run_frames) rfl

section RunFramesGlue2

variable (p0 R0 L0 F0 : Nat)

/-- After `dec done 0`. -/
def GP1 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPre p0 R0 L0 F0 t ∧ locN t "done" = 0

/-- After `dec pc (load ev)` on the not-yet-done path. -/
def GPpc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPre p0 R0 L0 F0 t ∧ locN t "done" = 0 ∧
    memW t (globN t "cur_cont" + 32) = 0 ∧ memW t (globN t "ev" + 104) ≠ 0 ∧
    locN t "pc" = memW t (globN t "ev")

/-- At the `op_dispatch` call: a running frame. -/
def GPdisp : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPre p0 R0 L0 F0 t ∧ locN t "done" = 0 ∧ ¬ EvmDone t ∧ F0 = 2 * L0 + 1

/-- In the `EvmErr` handler of `op_dispatch`. -/
def GPh : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => EvmInv t ∧ (evmChain t).length = L0 ∧ evmR t ≤ R0 ∧ locN t "done" = 0 ∧
    F0 = 2 * L0 + 1

/-- The done branch, before `frame_epilogue`. -/
def GPdone : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPre p0 R0 L0 F0 t ∧ EvmDone t

/-- After `frame_epilogue`. -/
def GPepi : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => EvmInv t ∧ EvmDone t ∧ (evmChain t).length = L0 ∧ evmR t ≤ R0 ∧ 2 * L0 ≤ F0

/-- At the `finish_child` call. -/
def GPfin : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => GPepi R0 L0 F0 t ∧ memW t (globN t "cur_cont" + 16) ≠ 0

/-- In the `EvmErr` handler of `finish_child`. -/
def GPh4 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => EvmInv t ∧ (evmChain t).length + 1 = L0 ∧ evmR t ≤ R0 ∧ 2 * L0 ≤ F0

end RunFramesGlue2

theorem evmFp_done {F : Type} {t : PanSemStateFiniteExact 64 F} (h : EvmDone t) :
    evmFp t = 2 * (evmChain t).length := by
  simp [evmFp, h]

theorem evmFp_notDone {F : Type} {t : PanSemStateFiniteExact 64 F} (h : ¬ EvmDone t) :
    evmFp t = 2 * (evmChain t).length + 1 := by
  simp [evmFp, h]

theorem evmFp_le {F : Type} (t : PanSemStateFiniteExact 64 F) :
    evmFp t ≤ 2 * (evmChain t).length + 1 := by
  unfold evmFp; split <;> omega


set_option maxHeartbeats 4000000 in
/-- Glue (round-2 Astra item 6: now PROVED): the four frame contracts compose to
`run_frames_step`. The loop body is evaluated symbolically with the `Hoare` rules: a running frame
dispatches one instruction (`evmPot` drops, or `EvmErr` → `frame_exception` halts the frame:
`F` drops by one); a done frame runs `frame_epilogue` and then either leaves the loop
(`go := 0`, outermost frame) or pops the child (`finish_child`, then possibly
`frame_exception`: the chain is one shorter, so `F` drops). -/
theorem run_frames_step_of_specs
    (h1 : FunSpec (fun s => EvmInv s ∧ ¬ EvmDone s)
      (fun s r post =>
        ((∃ v, r = some (.returned v)) → EvmInv post ∧ evmPot post < evmPot s) ∧
        (IsEvmErr r → EvmInv post ∧ (evmChain post).length = (evmChain s).length ∧
          evmR post ≤ evmR s))
      (ofString "op_dispatch"))
    (h2 : FunSpec EvmInv
      (OnReturn fun s post => EvmInv post ∧ EvmDone post ∧
        (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "frame_exception"))
    (h3 : FunSpec (fun s => EvmInv s ∧ EvmDone s)
      (OnReturn fun s post => EvmInv post ∧ EvmDone post ∧
        (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "frame_epilogue"))
    (h4 : FunSpec (fun s => EvmInv s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0)
      (fun s r post => ((∃ v, r = some (.returned v)) ∨ IsEvmErr r) →
        EvmInv post ∧ (evmChain post).length + 1 = (evmChain s).length ∧ evmR post ≤ evmR s)
      (ofString "finish_child")) :
    ∀ c b, runFramesLoop = some (c, b) →
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → EvmInv s →
      LoopActive c s →
      ((evaluateHOLFiniteState (decClockHOLFinite s) b).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) b).1 = some .continue) →
      (EvmInv (evaluateHOLFiniteState (decClockHOLFinite s) b).2 ∧
        evmPot (evaluateHOLFiniteState (decClockHOLFinite s) b).2 < evmPot s) ∨
      locN (evaluateHOLFiniteState (decClockHOLFinite s) b).2 "go" = 0 := by
  intro c b hcb F s hcode hinv _hact hflow
  unfold runFramesLoop at hcb
  rw [lookup_run_frames] at hcb
  simp only [sourceFunctionEntry, Guest.Software.guestFn_run_frames,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.some.injEq, Prod.mk.injEq] at hcb
  obtain ⟨-, hb⟩ := hcb
  -- ghost values of the loop head
  set p0 := evmPot s with hp0
  set R0 := evmR s with hR0
  set L0 := (evmChain s).length with hL0
  set F0 := evmFp s with hF0
  have hfin : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), EvmInv t → evmR t ≤ R0 →
      evmFp t < F0 → evmPot t < p0 := fun t ht hR hF =>
    lt_of_lt_of_le (evmPot_lt_bound t ht hR hF) (evmPot_ge s)
  have key : Hoare (GPre p0 R0 L0 F0) b (GQ p0) := by
    subst hb
    refine Hoare.dec (names := ["go"]) (P' := GP1 p0 R0 L0 F0) (by decide) ?_ ?_
      (gq_postLocals p0) (fun _ _ => gq_other p0 _ _ (by simp) (by simp))
    · intro F t v hP hv
      cases evalAt_const t 0 v hv
      refine ⟨gpre_congr p0 R0 L0 F0 (t := t) (u := setVarHOLFinite _ _ t) rfl rfl
        (evmInv_setVar _ _ hP.1) hP, ?_⟩
      rw [locN_setVar_same]; rfl
    · refine Hoare.seq (R := GMid p0 R0 L0 F0) ?_ ?_
      · -- the tests and the instruction
        refine Hoare.ite ?_ ?_ (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
        · -- `cur_cont+32 ≠ 0`: done
          refine Hoare.assign (fun t v hP hv => ?_)
            (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
          cases evalAt_const t 1 v hv
          refine ⟨fun _ => Or.inl ⟨?_, ?_, ?_⟩, fun h => absurd rfl h⟩
          · exact gpre_congr p0 R0 L0 F0 (t := t) (u := setKvarHOLFinite .local _ _ t) rfl rfl
              (evmInv_setVar _ _ hP.1.1.1) hP.1.1
          · refine (evmDone_congr (s := t) (t := setKvarHOLFinite .local _ _ t) rfl rfl).2 ?_
            have := condTrue_ne0 hP.2
            exact Or.inl (by simpa using this)
          · show locN (setVarHOLFinite (ofString "done") (.val (.word 1)) t) "done" ≠ 0
            rw [locN_setVar_same]; decide
        · refine Hoare.ite ?_ ?_ (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
          · -- `ev+104 = 0`: done
            refine Hoare.assign (fun t v hP hv => ?_)
              (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
            cases evalAt_const t 1 v hv
            refine ⟨fun _ => Or.inl ⟨?_, ?_, ?_⟩, fun h => absurd rfl h⟩
            · exact gpre_congr p0 R0 L0 F0 (t := t) (u := setKvarHOLFinite .local _ _ t) rfl rfl
                (evmInv_setVar _ _ hP.1.1.1.1) hP.1.1.1
            · refine (evmDone_congr (s := t) (t := setKvarHOLFinite .local _ _ t) rfl rfl).2 ?_
              have := condTrue_eq0 hP.2
              exact Or.inr (Or.inl (by simpa using this))
            · show locN (setVarHOLFinite (ofString "done") (.val (.word 1)) t) "done" ≠ 0
              rw [locN_setVar_same]; decide
          · refine Hoare.dec (names := ["go", "done"]) (P' := GPpc p0 R0 L0 F0) (by decide) ?_ ?_
              (ga_postLocals p0 R0 L0 F0)
              (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
            · intro F t v hP hv
              obtain ⟨⟨hP1, hc1⟩, hc2⟩ := hP
              obtain ⟨a, rfl, ha⟩ := evalAt_loadG t "ev" 0 v hv
              refine ⟨gpre_congr p0 R0 L0 F0 (t := t) (u := setVarHOLFinite _ _ t) rfl rfl
                (evmInv_setVar _ _ hP1.1.1) hP1.1, ?_, ?_, ?_, ?_⟩
              · rw [locN_setVar_ne t "done" (ofString "pc") _ (by decide)]; exact hP1.2
              · show memW t (globN t "cur_cont" + 32) = 0
                have := condFalse_ne0 hc1
                simpa using this
              · show memW t (globN t "ev" + 104) ≠ 0
                have := condFalse_eq0 hc2
                simpa using this
              · rw [locN_setVar_same]
                show a.toNat = memW t (globN t "ev")
                simpa using ha
            · refine Hoare.ite ?_ ?_ (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
              · -- `pc ≥ code length`: done
                refine Hoare.assign (fun t v hP hv => ?_)
                  (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
                cases evalAt_const t 1 v hv
                obtain ⟨⟨hpre, _, _, _, hpc⟩, w, hw, hne⟩ := hP
                refine ⟨fun _ => Or.inl ⟨?_, ?_, ?_⟩, fun h => absurd rfl h⟩
                · exact gpre_congr p0 R0 L0 F0 (t := t) (u := setKvarHOLFinite .local _ _ t)
                    rfl rfl (evmInv_setVar _ _ hpre.1) hpre
                · refine (evmDone_congr (s := t) (t := setKvarHOLFinite .local _ _ t) rfl rfl).2 ?_
                  have := (cond_notLower hw).1 hne
                  refine Or.inr (Or.inr ?_)
                  rw [← hpc]
                  simpa using this
                · show locN (setVarHOLFinite (ofString "done") (.val (.word 1)) t) "done" ≠ 0
                  rw [locN_setVar_same]; decide
              · -- running frame: dispatch one instruction
                refine Hoare.dec (names := ["go", "done"]) (P' := GPdisp p0 R0 L0 F0) (by decide)
                  ?_ ?_ (ga_postLocals p0 R0 L0 F0)
                  (fun _ _ => ga_other p0 R0 L0 F0 _ _ (by simp) (by simp))
                · intro F t v hP hv
                  cases evalAt_const t 0 v hv
                  obtain ⟨⟨hpre, hdone, hc1, hc2, hpc⟩, hc3⟩ := hP
                  have hlt := (cond_notLower hc3).2 rfl
                  have hnd : ¬ EvmDone t := by
                    rintro (h | h | h)
                    · exact h hc1
                    · exact hc2 h
                    · rw [← hpc] at h
                      simp at hlt
                      omega
                  refine ⟨gpre_congr p0 R0 L0 F0 (t := t) (u := setVarHOLFinite _ _ t) rfl rfl
                    (evmInv_setVar _ _ hpre.1) hpre, ?_, ?_, ?_⟩
                  · rw [locN_setVar_ne t "done" (ofString "err") _ (by decide)]; exact hdone
                  · exact fun h => hnd ((evmDone_congr (s := t) (t := setVarHOLFinite _ _ t)
                      rfl rfl).1 h)
                  · rw [← hpre.2.2.2.2, ← hpre.2.2.2.1, evmFp_notDone hnd]
                · refine Hoare.callH (Pc := fun s => EvmInv s ∧ ¬ EvmDone s) (Ph := GPh R0 L0 F0)
                    h1 ?_ ?_ ?_ ?_ (fun r t h h' => ga_other p0 R0 L0 F0 r t h h')
                  · intro F t values body callee ret _ hP _ _
                    exact ⟨evmInv_entry callee hP.1.1, fun hd => hP.2.2.1
                      ((evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).1 hd)⟩
                  · intro F t callee post v _ hP hq
                    obtain ⟨hi, hlt⟩ := hq.1 ⟨v, rfl⟩
                    refine ⟨fun _ => Or.inr ⟨evmInv_locals _ hi, ?_, hP.2.1⟩, fun h => absurd rfl h⟩
                    rw [(evm_congr (s := post) (t := { post with locals := t.locals }) rfl rfl).1]
                    rw [(evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).1,
                      hP.1.2.1] at hlt
                    exact hlt
                  · intro F t callee post v _ hP hq
                    obtain ⟨hi, hlen, hR⟩ := hq.2 ⟨v, rfl⟩
                    obtain ⟨-, eR, eL, -⟩ := evm_congr (s := t) (t := callEntryStateHOLFinite t callee)
                      rfl rfl
                    obtain ⟨-, fR, fL, -⟩ := evm_congr (s := post)
                      (t := setVarHOLFinite (ofString "err") v { post with locals := t.locals }) rfl rfl
                    refine ⟨evmInv_setVar _ _ (evmInv_locals _ hi), ?_, ?_, ?_, hP.2.2.2⟩
                    · rw [fL, hlen, eL]; exact hP.1.2.2.2.1
                    · rw [fR]; exact hR.trans (le_of_eq (eR.trans hP.1.2.2.1))
                    · rw [locN_setVar_ne _ "done" (ofString "err") _ (by decide)]; exact hP.2.1
                  · refine Hoare.call0 (Pc := EvmInv) h2 ?_ ?_
                      (fun r t h h' => ga_other p0 R0 L0 F0 r t h h')
                    · intro F t values body callee ret _ hP _ _
                      exact evmInv_entry callee hP.1
                    · intro F u callee post v _ hP hq
                      obtain ⟨hi, hd, hlen, hR⟩ := hq v rfl
                      obtain ⟨-, eR, eL, -⟩ := evm_congr (s := u)
                        (t := callEntryStateHOLFinite u callee) rfl rfl
                      obtain ⟨fp, fR, fL, fF⟩ := evm_congr (s := post)
                        (t := { post with locals := u.locals }) rfl rfl
                      refine ⟨fun _ => Or.inr ⟨evmInv_locals _ hi, ?_, hP.2.2.2.1⟩,
                        fun h => absurd rfl h⟩
                      apply hfin _ (evmInv_locals _ hi)
                      · rw [fR]; exact hR.trans ((le_of_eq eR).trans hP.2.2.1)
                      · rw [fF, evmFp_done hd, hlen, eL, hP.2.1, hP.2.2.2.2]; omega
      · -- the done branch
        refine Hoare.ite ?_ ?_ (fun _ _ => gq_other p0 _ _ (by simp) (by simp))
        · refine Hoare.seq (R := GPdone p0 R0 L0 F0)
            (Hoare.skip fun t hP => ⟨fun _ => ?_, fun h => absurd rfl h⟩) ?_
          · rcases hP.1 with ⟨hp, hd, _⟩ | ⟨_, _, hz⟩
            · exact ⟨hp, hd⟩
            · exact absurd hz (condTrue_local_ne0 hP.2)
          refine Hoare.seq (R := GPepi R0 L0 F0) ?_ ?_
          · refine Hoare.call0 (Pc := fun s => EvmInv s ∧ EvmDone s) h3 ?_ ?_
              (fun r t h h' => ⟨fun hr => absurd hr h, fun _ => gq_other p0 r t h h'⟩)
            · intro F t values body callee ret _ hP _ _
              exact ⟨evmInv_entry callee hP.1.1,
                (evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).2 hP.2⟩
            · intro F t callee post v _ hP hq
              obtain ⟨hi, hd, hlen, hR⟩ := hq v rfl
              obtain ⟨-, eR, eL, -⟩ := evm_congr (s := t) (t := callEntryStateHOLFinite t callee)
                rfl rfl
              obtain ⟨-, fR, fL, -⟩ := evm_congr (s := post) (t := { post with locals := t.locals })
                rfl rfl
              refine ⟨fun _ => ⟨evmInv_locals _ hi,
                (evmDone_congr (s := post) (t := { post with locals := t.locals }) rfl rfl).2 hd,
                ?_, ?_, ?_⟩, fun h => absurd rfl h⟩
              · rw [fL, hlen, eL]; exact hP.1.2.2.2.1
              · rw [fR]; exact hR.trans (le_of_eq (eR.trans hP.1.2.2.1))
              · rw [← hP.1.2.2.2.2, evmFp_done hP.2, hP.1.2.2.2.1]
          · refine Hoare.ite ?_ ?_ (fun _ _ => gq_other p0 _ _ (by simp) (by simp))
            · -- outermost frame: `ev`, `cur_cont` restored, `go := 0`
              refine Hoare.seq (R := fun _ => True)
                (Hoare.assign (fun _ _ _ _ => ⟨fun _ => trivial, fun h => absurd rfl h⟩)
                  (fun _ _ => ⟨fun h => absurd h (by simp), fun _ => gq_other p0 _ _ (by simp)
                    (by simp)⟩)) ?_
              refine Hoare.seq (R := fun _ => True)
                (Hoare.assign (fun _ _ _ _ => ⟨fun _ => trivial, fun h => absurd rfl h⟩)
                  (fun _ _ => ⟨fun h => absurd h (by simp), fun _ => gq_other p0 _ _ (by simp)
                    (by simp)⟩)) ?_
              refine Hoare.assign (fun t v _ hv => ?_) (fun _ _ => gq_other p0 _ _ (by simp) (by simp))
              cases evalAt_const t 0 v hv
              intro _
              right
              show locN (setVarHOLFinite (ofString "go") (.val (.word 0)) t) "go" = 0
              rw [locN_setVar_same]; rfl
            · -- pop the done child
              refine Hoare.dec (names := ["go"]) (P' := GPfin R0 L0 F0) (by decide) ?_ ?_
                (gq_postLocals p0) (fun _ _ => gq_other p0 _ _ (by simp) (by simp))
              · intro F t v hP hv
                cases evalAt_const t 0 v hv
                obtain ⟨⟨hi, hd, hlen, hR, hF⟩, hk⟩ := hP
                obtain ⟨-, fR, fL, -⟩ := evm_congr (s := t) (t := setVarHOLFinite _ _ t) rfl rfl
                refine ⟨⟨evmInv_setVar _ _ hi,
                  (evmDone_congr (s := t) (t := setVarHOLFinite _ _ t) rfl rfl).2 hd,
                  fL.trans hlen, (le_of_eq fR).trans hR, hF⟩, ?_⟩
                show memW t (globN t "cur_cont" + 16) ≠ 0
                have := condFalse_eq0 hk
                simpa using this
              · refine Hoare.callH
                  (Pc := fun s => EvmInv s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0)
                  (Ph := GPh4 R0 L0 F0) h4 ?_ ?_ ?_ ?_ (fun r t h h' => gq_other p0 r t h h')
                · intro F t values body callee ret _ hP _ _
                  exact ⟨evmInv_entry callee hP.1.1,
                    (evmDone_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).2
                      hP.1.2.1, hP.2⟩
                · intro F t callee post v _ hP hq
                  obtain ⟨hi, hlen, hR⟩ := hq (Or.inl ⟨v, rfl⟩)
                  obtain ⟨-, eR, eL, -⟩ := evm_congr (s := t) (t := callEntryStateHOLFinite t callee)
                    rfl rfl
                  obtain ⟨-, fR, fL, fF⟩ := evm_congr (s := post)
                    (t := { post with locals := t.locals }) rfl rfl
                  intro _
                  left
                  refine ⟨evmInv_locals _ hi, hfin _ (evmInv_locals _ hi) ?_ ?_⟩
                  · rw [fR]; exact hR.trans ((le_of_eq eR).trans hP.1.2.2.2.1)
                  · rw [fF]
                    have h1 := evmFp_le post
                    have h2 := hP.1.2.2.2.2
                    rw [eL, hP.1.2.2.1] at hlen
                    omega
                · intro F t callee post v _ hP hq
                  obtain ⟨hi, hlen, hR⟩ := hq (Or.inr ⟨v, rfl⟩)
                  obtain ⟨-, eR, eL, -⟩ := evm_congr (s := t) (t := callEntryStateHOLFinite t callee)
                    rfl rfl
                  obtain ⟨-, fR, fL, -⟩ := evm_congr (s := post)
                    (t := setVarHOLFinite (ofString "err2") v { post with locals := t.locals }) rfl rfl
                  refine ⟨evmInv_setVar _ _ (evmInv_locals _ hi), ?_, ?_, hP.1.2.2.2.2⟩
                  · rw [fL, hlen, eL]; exact hP.1.2.2.1
                  · rw [fR]; exact hR.trans ((le_of_eq eR).trans hP.1.2.2.2.1)
                · refine Hoare.call0 (Pc := EvmInv) h2 ?_ ?_ (fun r t h h' => gq_other p0 r t h h')
                  · intro F t values body callee ret _ hP _ _
                    exact evmInv_entry callee hP.1
                  · intro F u callee post v _ hP hq
                    obtain ⟨hi, hd, hlen, hR⟩ := hq v rfl
                    obtain ⟨-, eR, eL, -⟩ := evm_congr (s := u)
                      (t := callEntryStateHOLFinite u callee) rfl rfl
                    obtain ⟨-, fR, fL, fF⟩ := evm_congr (s := post)
                      (t := { post with locals := u.locals }) rfl rfl
                    intro _
                    left
                    refine ⟨evmInv_locals _ hi, hfin _ (evmInv_locals _ hi) ?_ ?_⟩
                    · rw [fR]; exact hR.trans ((le_of_eq eR).trans hP.2.2.1)
                    · rw [fF, evmFp_done hd, hlen, eL]
                      have := hP.2.1
                      have := hP.2.2.2
                      omega
        · refine Hoare.skip (fun t hP => fun _ => ?_)
          rcases hP.1 with ⟨_, _, hn⟩ | ⟨hi, hp, _⟩
          · exact absurd (condFalse_local_ne0 hP.2) hn
          · exact Or.inl ⟨hi, hp⟩
  have hnt : (evaluateHOLFiniteState (decClockHOLFinite s) b).1 ≠ some .timeOut := by
    rcases hflow with h | h <;> rw [h] <;> simp
  have hpre : GPre p0 R0 L0 F0 (decClockHOLFinite s) := by
    obtain ⟨e1, e2, e3, e4⟩ := evm_congr (s := s) (t := decClockHOLFinite s) rfl rfl
    exact ⟨localsFree_evmInv s s.locals (s.clock - 1) hinv, e1, e2, e3, e4⟩
  exact key.run (decClockHOLFinite s) hcode hpre hnt hflow

/-- One continuing iteration of the `run_frames` loop strictly lowers `evmPot` and keeps
`EvmInv`, or ends the loop (`go := 0` after the outermost frame). Proved from the four contract
leaves and the (proved) glue. -/
theorem run_frames_step : ∀ c b, runFramesLoop = some (c, b) →
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → EvmInv s →
      LoopActive c s →
      ((evaluateHOLFiniteState (decClockHOLFinite s) b).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) b).1 = some .continue) →
      (EvmInv (evaluateHOLFiniteState (decClockHOLFinite s) b).2 ∧
        evmPot (evaluateHOLFiniteState (decClockHOLFinite s) b).2 < evmPot s) ∨
      locN (evaluateHOLFiniteState (decClockHOLFinite s) b).2 "go" = 0 :=
  run_frames_step_of_specs op_dispatch_spec frame_exception_spec frame_epilogue_spec
    finish_child_spec

/-! ### Concrete compositions (revision 4: shrinking the primitive list) -/

theorem TerminatingProgBoundedOn.mono_bound {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64} {a b : Nat} (h : TerminatingProgBoundedOn P prog a) (hle : a ≤ b) :
    TerminatingProgBoundedOn P prog b :=
  fun s hc hP => (h s hc hP).weaken hle

/-- A program that never changes the clock costs nothing. -/
theorem TerminatingProgBoundedOn.of_clock {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState s prog).2.clock = s.clock) :
    TerminatingProgBoundedOn P prog 0 :=
  fun s _ _ _ => ⟨by have := h s; omega, by have := h s; omega⟩

theorem clock_return {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.return e)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_return]
  repeat' split
  all_goals (try dsimp only)
  all_goals (try split)
  all_goals (try rfl)

theorem clock_raise {F : Type} (s : PanSemStateFiniteExact 64 F) (n : MlS) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.raise n e)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_raise]
  repeat' split
  all_goals (try dsimp only)
  all_goals (try split)
  all_goals (try rfl)

theorem clock_shMemStore {F : Type} (s : PanSemStateFiniteExact 64 F) (op : OpSize) (a v : ExpHOL 64) :
    (evaluateHOLFiniteState s (.shMemStore op a v)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_shMemStore]
  show (shMemStoreClauseHOLFiniteExact s op a v).2.clock = s.clock
  simp only [shMemStoreClauseHOLFiniteExact, shMemStoreClauseHOLExact, shMemStoreHOLExact]
  repeat' split
  all_goals rfl

/-- A guard that ignores locals and clock holds at every callee entry. -/
theorem callEntryOn_of_localsFree {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (h : LocalsFree P) (fname : MlS) (arguments : List (ExpHOL 64)) :
    CallEntryOn P P fname arguments :=
  fun state _ _ _ _ _ hP _ _ => h state _ _ hP

/-- `seq` whose second part needs only `GuestInv` (which every evaluation keeps). -/
theorem TerminatingProgBoundedOn.seq_guestInv_after
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn P first a)
    (hPG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    (h2 : TerminatingProgBoundedOn GuestInv second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  intro F state hcode hP
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  have hmid := guestInv_evaluate state first (hPG state hP)
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt hmid ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simp [hr1]
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) hmid hnt
    exact ⟨by omega, by omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    exact ⟨by omega, k1⟩

theorem seq_clock {first second : ProgHOL 64}
    (h1 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState s first).2.clock = s.clock)
    (h2 : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState s second).2.clock = s.clock) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState s (.seq first second)).2.clock = s.clock := by
  intro F s
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s first with ⟨r, mid⟩
  have := h1 s
  rw [hr] at this
  cases r with
  | none => dsimp only; rw [h2 mid]; exact this
  | some _ => exact this

theorem clock_assign {F : Type} (s : PanSemStateFiniteExact 64 F) (k : VarKind) (n : MlS)
    (e : ExpHOL 64) : (evaluateHOLFiniteState s (.assign k n e)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_assign]
  repeat' split
  all_goals (try dsimp only)
  all_goals (try split)
  all_goals (try rfl)
  all_goals (cases k <;> rfl)

/-- A guard implied by the caller's guard holds at every callee entry, if it ignores locals. -/
theorem callEntryOn_of_imp {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hQ : LocalsFree Q) (himp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q s)
    (fname : MlS) (arguments : List (ExpHOL 64)) : CallEntryOn P Q fname arguments :=
  fun state _ _ _ _ _ hP _ _ => hQ state _ _ (himp state hP)

/-- The continuation of any `decCall` is a `GuestInv` state. -/
theorem decCallResumeOn_guestInv {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hPG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    (name fname : MlS) (arguments : List (ExpHOL 64)) :
    DecCallResumeOn P GuestInv name fname arguments := by
  intro F state values body callee ret value post _ hP _ _ hrun
  have hpost := guestInv_evaluate (callEntryStateHOLFinite state callee) body
    (guestInv_callEntry state callee (hPG state hP))
  rw [hrun] at hpost
  exact guestInv_setVar name value _ (guestInv_with_locals_clock post state.locals post.clock hpost)

/-- A read-only callee resumes its caller in the caller's guard (the declared name is not read by
the guard). -/
theorem ReadOnlyFn.resumeOn {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} (hP : LocalsOnly names P)
    (hPG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    {fname : MlS} (h : ReadOnlyFn fname) (name : MlS) (hname : ∀ n ∈ names, ofString n ≠ name)
    (arguments : List (ExpHOL 64)) : DecCallResumeOn P P name fname arguments := by
  obtain ⟨params, body', ret', hlook, hb⟩ := h
  intro F state values body callee ret value post hcode hPs _ hl hrun
  have hsame := lookupCodeHOLFinite_installed_body state.code.lookup fname params body' body
    ret' ret values callee (by rw [hcode]; exact hlook) hl
  subst hsame
  have hro := hb (callEntryStateHOLFinite state callee) hcode
    (guestInv_callEntry state callee (hPG state hPs)) (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨value, rfl⟩)
  rw [hrun] at hro
  dsimp only at hro
  have heq : ({ post with locals := state.locals } : PanSemStateFiniteExact 64 F) =
      { state with locals := state.locals, clock := post.clock } := by
    rw [hro]; rfl
  rw [heq]
  exact hP.setVar hname value _ (hP state state.locals post.clock (fun _ _ => rfl) hPs)

/-! ### Direct callees, read off the AST (revision 6, round-4 Astra item 8)

Each `GBody.«f»` below is an obligation about the body of the single function `f`. Its
hypotheses are the bound of each direct callee of `f` and the contract of each callee at a
guard-carrying call site; `«callees_f»` checks, by `decide` on the literal AST, that the direct
callees of `f` are exactly the functions whose bounds are listed. -/

/-- Every function named by a `call` or `decCall` in a body (exception handlers included). -/
def progCallees : Prog (BitVec 64) → List String
  | .dec _ _ _ b => progCallees b
  | .seq a b => progCallees a ++ progCallees b
  | .ite _ a b => progCallees a ++ progCallees b
  | .while _ b => progCallees b
  | .call (some (_, some (_, _, h))) g _ => g :: progCallees h
  | .call _ g _ => [g]
  | .decCall _ _ g _ b => g :: progCallees b
  | _ => []

def fnBody : Decl (BitVec 64) → Prog (BitVec 64)
  | .function fd => fd.body
  | _ => .skip

/-- The two lists name the same set of functions. -/
def sameNames (l m : List String) : Bool := l.all (· ∈ m) && m.all (· ∈ l)

/-! ### Guard-carrying `seq` from the Hoare layer (revision 6, round-4 Astra item 8) -/

/-- Guarded `seq` that needs the guard after the first part only when it falls through (a
normal `none` result), stated as a Hoare triple. `seq_on` asks for preservation on every outcome,
which fails for calls (a trapped callee leaves an arbitrary state). -/
theorem TerminatingProgBoundedOn.seq_hoare
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn P first a) (hp : Hoare P first (fun r t => r = none → P t))
    (h2 : TerminatingProgBoundedOn P second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  intro F state hcode hP
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  have hmid := hp.run state hcode hP
  simp only [hr1] at hmeta hnt hmid ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simp [hr1]
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) (hmid (by simp) rfl) hnt
    exact ⟨by omega, by omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1 state hcode hP hnt1
    rw [hr1] at s1 k1
    dsimp only at s1 k1
    exact ⟨by omega, k1⟩

theorem return_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.return e)).1 ≠ none := by
  rw [evaluateHOLFiniteState_return]
  split
  · simp
  · split <;> simp

theorem clock_skip {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s .skip).2.clock = s.clock := by simp

/-- An early-return guard clause `if c then return e` falls through only from the unchanged
state. -/
theorem Hoare.ite_return_skip {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (cond e : ExpHOL 64) : Hoare P (.ite cond (.return e) .skip) (fun r t => r = none → P t) :=
  Hoare.ite ⟨fun s _ _ _ h => absurd h (return_ne_none s e)⟩ (Hoare.skip fun _ h _ => h.1)
    (fun _ _ h => absurd h (by simp))

/-- A handler-free call without destination to a callee that keeps the locals-free guard `W`
falls through only into a `W` state. -/
theorem Hoare.call_keeps {W : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hW : LocalsFree W) {fname : MlS} (hk : KeepsOn W W fname) (arguments : List (ExpHOL 64)) :
    Hoare W (.call (some (none, none)) fname arguments) (fun r t => r = none → W t) :=
  Hoare.call0 hk (callEntryOn_of_localsFree hW _ _)
    (fun s _ post v _ _ hq _ => hW post s.locals post.clock (hq (Or.inl ⟨v, rfl⟩)))
    (fun _ _ hr _ h => absurd h hr)

/-- `if c then (call g) ` with `g` keeping `W`, as a fall-through triple. -/
theorem Hoare.ite_call_keeps {W : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hW : LocalsFree W) {fname : MlS} (hk : KeepsOn W W fname) (cond : ExpHOL 64)
    (arguments : List (ExpHOL 64)) :
    Hoare W (.ite cond (.call (some (none, none)) fname arguments) .skip)
      (fun r t => r = none → W t) :=
  Hoare.ite (Hoare.mono (Hoare.call_keeps hW hk arguments) (fun _ h => h.1))
    (Hoare.skip fun _ h _ => h.1) (fun _ _ h => absurd h (by simp))

theorem clock_store {F : Type} (s : PanSemStateFiniteExact 64 F) (a v : ExpHOL 64) :
    (evaluateHOLFiniteState s (.store a v)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_store]
  repeat' split
  all_goals (try dsimp only)

/-! ### Guarded bound leaves (generated) -/

/-! #### Callee contracts (generated; one leaf per callee and world guard) -/

/-- `_decode_step` (AST line 10110): keeps `ArenaReady`. -/
theorem «ak__decode_step» :
    KeepsOn ArenaReady ArenaReady (ofString "_decode_step") := by sorry
/-- `charge_gas` (AST line 14949): keeps `EvmInv`. -/
theorem «ek_charge_gas» :
    KeepsOn EvmInv EvmInv (ofString "charge_gas") := by sorry
/-- `create_finish` (AST line 18867): keeps `EvmInv`. -/
theorem «ek_create_finish» :
    KeepsOn EvmInv EvmInv (ofString "create_finish") := by sorry
/-- `depth0_prepare` (AST line 18772): keeps `EvmInv`. -/
theorem «ek_depth0_prepare» :
    KeepsOn EvmMsgReady EvmInv (ofString "depth0_prepare") := by sorry
/-- `frame_halt` (AST line 18756): keeps `EvmInv`. -/
theorem «ek_frame_halt» :
    KeepsOn EvmInv EvmInv (ofString "frame_halt") := by sorry
/-- `frame_start` (AST line 18539): keeps `EvmInv`. -/
theorem «ek_frame_start» :
    KeepsOn EvmInv EvmInv (ofString "frame_start") := by sorry
/-- `get_storage_original` (AST line 13276): keeps `EvmInv`. -/
theorem «ek_get_storage_original» :
    KeepsOn EvmInv EvmInv (ofString "get_storage_original") := by sorry
/-- `refill_frame_state_gas` (AST line 15029): keeps `EvmInv`. -/
theorem «ek_refill_frame_state_gas» :
    KeepsOn EvmInv EvmInv (ofString "refill_frame_state_gas") := by sorry
/-- `stack_pop` (AST line 15046): keeps `EvmInv`. -/
theorem «ek_stack_pop» :
    KeepsOn EvmInv EvmInv (ofString "stack_pop") := by sorry
/-- `state_restore` (AST line 12903): keeps `EvmInv`. -/
theorem «ek_state_restore» :
    KeepsOn EvmInv EvmInv (ofString "state_restore") := by sorry
/-- `warm_storage_key` (AST line 16571): keeps `EvmInv`. -/
theorem «ek_warm_storage_key» :
    KeepsOn EvmInv EvmInv (ofString "warm_storage_key") := by sorry
/-- `frame_open` (AST line 18450): carries the frame built by `frame_open` (hand-written). -/
theorem «fk_frame_open» :
    KeepsOn FrameOpenReady EvmMsgReady (ofString "frame_open") := by sorry
/-- `_collapse_branch` (AST line 10674): typed nodes in, typed nodes out (MPT tier); requirement: `NodeKind s Nd "node" 3`. -/
theorem «nf__collapse_branch» :
    NodeFn ["node"]
    (fun s Nd =>
      NodeKind s Nd "node" 3)
    (ofString "_collapse_branch") := by sorry
/-- `_delete_ext_finish` (AST line 10727): typed nodes in, typed nodes out (MPT tier); requirement: `NodeKind s Nd "node" 2 ∧ KeyIn s Nd (locN s "seg") (locN s "sl")`. -/
theorem «nf__delete_ext_finish» :
    NodeFn ["node", "nc"]
    (fun s Nd =>
      NodeKind s Nd "node" 2 ∧ KeyIn s Nd (locN s "seg") (locN s "sl"))
    (ofString "_delete_ext_finish") := by sorry
/-- `_insert_into_leaf` (AST line 10532): typed nodes in, typed nodes out (MPT tier); requirement: `NodeKind s Nd "node" 1 ∧ KeyIn s Nd (locN s "rk") (locN s "rl")`. -/
theorem «nf__insert_into_leaf» :
    NodeFn ["node"]
    (fun s Nd =>
      NodeKind s Nd "node" 1 ∧ KeyIn s Nd (locN s "rk") (locN s "rl"))
    (ofString "_insert_into_leaf") := by sorry
/-- `_split_extension` (AST line 10561): typed nodes in, typed nodes out (MPT tier); requirement: `NodeKind s Nd "node" 2 ∧ KeyIn s Nd (locN s "rk") (locN s "rl") ∧ locN s "pl" < memW s (locN s "node" + 40) ∧ locN s "pl" ≤ locN s "rl"`. -/
theorem «nf__split_extension» :
    NodeFn ["node"]
    (fun s Nd =>
      NodeKind s Nd "node" 2 ∧ KeyIn s Nd (locN s "rk") (locN s "rl") ∧
      locN s "pl" < memW s (locN s "node" + 40) ∧ locN s "pl" ≤ locN s "rl")
    (ofString "_split_extension") := by sorry
/-- `node_invalidate` (AST line 10061): typed nodes in, typed nodes out (MPT tier); requirement: none. -/
theorem «nf_node_invalidate» :
    NodeFn ["nd"]
    (fun _ _ => True)
    (ofString "node_invalidate") := by sorry
/-- `node_new_ext` (AST line 10021): typed nodes in, typed nodes out (MPT tier); requirement: `KeyIn s Nd (locN s "nib") (locN s "nlen")`. -/
theorem «nf_node_new_ext» :
    NodeFn ["child"]
    (fun s Nd =>
      KeyIn s Nd (locN s "nib") (locN s "nlen"))
    (ofString "node_new_ext") := by sorry
/-- `node_new_leaf` (AST line 9994): typed nodes in, typed nodes out (MPT tier); requirement: `KeyIn s Nd (locN s "nib") (locN s "nlen")`. -/
theorem «nf_node_new_leaf» :
    NodeFn []
    (fun s Nd =>
      KeyIn s Nd (locN s "nib") (locN s "nlen"))
    (ofString "node_new_leaf") := by sorry
/-- `mpt_nibble_key` (AST line 10470): returns a fresh heap nibble array (value contract). -/
theorem «nk_mpt_nibble_key» :
    RetNibbles (ofString "mpt_nibble_key") := by sorry
/-- `calculate_total_blob_gas` (AST line 11914): read-only. -/
theorem «ro_calculate_total_blob_gas» :
    ReadOnlyFn (ofString "calculate_total_blob_gas") := by sorry
/-- `check_gas` (AST line 14935): read-only. -/
theorem «ro_check_gas» :
    ReadOnlyFn (ofString "check_gas") := by sorry
/-- `check_gas_limit` (AST line 9590): read-only. -/
theorem «ro_check_gas_limit» :
    ReadOnlyFn (ofString "check_gas_limit") := by sorry
/-- `common_prefix_length` (AST line 9903): read-only. -/
theorem «ro_common_prefix_length» :
    ReadOnlyFn (ofString "common_prefix_length") := by sorry
/-- `fee_mul` (AST line 32778): read-only. -/
theorem «ro_fee_mul» :
    ReadOnlyFn (ofString "fee_mul") := by sorry
/-- `heap_mark` (AST line 88): read-only. -/
theorem «ro_heap_mark» :
    ReadOnlyFn (ofString "heap_mark") := by sorry
/-- `htab_get` (AST line 4999): read-only. -/
theorem «ro_htab_get» :
    ReadOnlyFn (ofString "htab_get") := by sorry
/-- `htab_has` (AST line 5022): read-only. -/
theorem «ro_htab_has» :
    ReadOnlyFn (ofString "htab_has") := by sorry
/-- `htab_item` (AST line 5314): read-only. -/
theorem «ro_htab_item» :
    ReadOnlyFn (ofString "htab_item") := by sorry
/-- `max` (AST line 681): read-only. -/
theorem «ro_max» :
    ReadOnlyFn (ofString "max") := by sorry
/-- `memeq` (AST line 304): read-only. -/
theorem «ro_memeq» :
    ReadOnlyFn (ofString "memeq") := by sorry
/-- `min` (AST line 667): read-only. -/
theorem «ro_min» :
    ReadOnlyFn (ofString "min") := by sorry
/-- `mpt_fail` (AST line 9769): read-only. -/
theorem «ro_mpt_fail» :
    ReadOnlyFn (ofString "mpt_fail") := by sorry
/-- `nodedb_lookup` (AST line 9960): read-only. -/
theorem «ro_nodedb_lookup» :
    ReadOnlyFn (ofString "nodedb_lookup") := by sorry
/-- `require_not_static` (AST line 15459): read-only. -/
theorem «ro_require_not_static» :
    ReadOnlyFn (ofString "require_not_static") := by sorry
/-- `scratch_mark` (AST line 176): read-only. -/
theorem «ro_scratch_mark» :
    ReadOnlyFn (ofString "scratch_mark") := by sorry
/-- `secp256k1_init` (AST line 5417): read-only. -/
theorem «ro_secp256k1_init» :
    ReadOnlyFn (ofString "secp256k1_init") := by sorry
/-- `state_snapshot` (AST line 12893): read-only. -/
theorem «ro_state_snapshot» :
    ReadOnlyFn (ofString "state_snapshot") := by sorry
/-- `stor_lookup` (AST line 13233): read-only. -/
theorem «ro_stor_lookup» :
    ReadOnlyFn (ofString "stor_lookup") := by sorry
/-- `tx_chain_id` (AST line 12365): read-only. -/
theorem «ro_tx_chain_id» :
    ReadOnlyFn (ofString "tx_chain_id") := by sorry
/-- `tx_has_access_list` (AST line 11890): read-only. -/
theorem «ro_tx_has_access_list» :
    ReadOnlyFn (ofString "tx_has_access_list") := by sorry
/-- `tx_is_blob` (AST line 32750): read-only. -/
theorem «ro_tx_is_blob» :
    ReadOnlyFn (ofString "tx_is_blob") := by sorry
/-- `tx_is_setcode` (AST line 32764): read-only. -/
theorem «ro_tx_is_setcode» :
    ReadOnlyFn (ofString "tx_is_setcode") := by sorry
/-- `u256_eq` (AST line 869): read-only. -/
theorem «ro_u256_eq» :
    ReadOnlyFn (ofString "u256_eq") := by sorry
/-- `u256_is_zero` (AST line 814): read-only. -/
theorem «ro_u256_is_zero» :
    ReadOnlyFn (ofString "u256_is_zero") := by sorry
/-- `u256_mul` (AST line 1150): read-only. -/
theorem «ro_u256_mul» :
    ReadOnlyFn (ofString "u256_mul") := by sorry
/-- `u256_sub` (AST line 1083): read-only. -/
theorem «ro_u256_sub» :
    ReadOnlyFn (ofString "u256_sub") := by sorry
/-- `udiv_small5` (AST line 33447): read-only. -/
theorem «ro_udiv_small5» :
    ReadOnlyFn (ofString "udiv_small5") := by sorry
/-- `validate_block_access_list_gas_limit` (AST line 14776): read-only. -/
theorem «ro_validate_block_access_list_gas_limit» :
    ReadOnlyFn (ofString "validate_block_access_list_gas_limit") := by sorry
/-- `validate_transaction` (AST line 12639): read-only. -/
theorem «ro_validate_transaction» :
    ReadOnlyFn (ofString "validate_transaction") := by sorry
/-- `common_prefix_length` (AST line 9903): returns at most `min(al, bl)` (value contract). -/
theorem «rv_common_prefix_length» :
    RetLe (fun s => min (locN s "al") (locN s "bl")) (ofString "common_prefix_length") := by sorry
/-- `account_deployable` (AST line 13358): keeps `WorldOK`. -/
theorem «wk_account_deployable» :
    KeepsOn WorldOK WorldOK (ofString "account_deployable") := by sorry
/-- `add_balance_change` (AST line 13978): keeps `WorldOK`. -/
theorem «wk_add_balance_change» :
    KeepsOn WorldOK WorldOK (ofString "add_balance_change") := by sorry
/-- `add_code_change` (AST line 14023): keeps `WorldOK`. -/
theorem «wk_add_code_change» :
    KeepsOn WorldOK WorldOK (ofString "add_code_change") := by sorry
/-- `add_nonce_change` (AST line 13992): keeps `WorldOK`. -/
theorem «wk_add_nonce_change» :
    KeepsOn WorldOK WorldOK (ofString "add_nonce_change") := by sorry
/-- `add_storage_write` (AST line 13942): keeps `WorldOK`. -/
theorem «wk_add_storage_write» :
    KeepsOn WorldOK WorldOK (ofString "add_storage_write") := by sorry
/-- `bal_remove_change` (AST line 14189): keeps `WorldOK`. -/
theorem «wk_bal_remove_change» :
    KeepsOn WorldOK WorldOK (ofString "bal_remove_change") := by sorry
/-- `block_rlp_length` (AST line 32586): keeps `WorldOK`. -/
theorem «wk_block_rlp_length» :
    KeepsOn WorldOK WorldOK (ofString "block_rlp_length") := by sorry
/-- `build_block_access_list_rlp` (AST line 14685): keeps `WorldOK`. -/
theorem «wk_build_block_access_list_rlp» :
    KeepsOn WorldOK WorldOK (ofString "build_block_access_list_rlp") := by sorry
/-- `build_mpt_indexed` (AST line 11243): keeps `WorldOK`. -/
theorem «wk_build_mpt_indexed» :
    KeepsOn (WorldAvoids (fun s => [(locN s "out", 32)])) WorldOK (ofString "build_mpt_indexed") := by sorry
/-- `calculate_blob_gas_price` (AST line 9550): keeps `WorldOK`. -/
theorem «wk_calculate_blob_gas_price» :
    KeepsOn WorldOK WorldOK (ofString "calculate_blob_gas_price") := by sorry
/-- `check_transaction` (AST line 32951): keeps `WorldOK`. -/
theorem «wk_check_transaction» :
    KeepsOn WorldOK WorldOK (ofString "check_transaction") := by sorry
/-- `clear_account_preserving_balance` (AST line 13541): keeps `WorldOK`. -/
theorem «wk_clear_account_preserving_balance» :
    KeepsOn WorldOK WorldOK (ofString "clear_account_preserving_balance") := by sorry
/-- `compute_state_root` (AST line 32341): keeps `WorldOK`. -/
theorem «wk_compute_state_root» :
    KeepsOn (WorldAvoids (fun s => [(locN s "out", 32)])) WorldOK (ofString "compute_state_root") := by sorry
/-- `create_ether` (AST line 13629): keeps `WorldOK`. -/
theorem «wk_create_ether» :
    KeepsOn WorldOK WorldOK (ofString "create_ether") := by sorry
/-- `decode_host_input` (AST line 8401): keeps `WorldOK`. -/
theorem «wk_decode_host_input» :
    KeepsOn WorldOK WorldOK (ofString "decode_host_input") := by sorry
/-- `destroy_storage` (AST line 13480): keeps `WorldOK`. -/
theorem «wk_destroy_storage» :
    KeepsOn WorldOK WorldOK (ofString "destroy_storage") := by sorry
/-- `encode_receipt` (AST line 32051): keeps `WorldOK`. -/
theorem «wk_encode_receipt» :
    KeepsOn WorldOK WorldOK (ofString "encode_receipt") := by sorry
/-- `encode_transaction` (AST line 12267): keeps `WorldOK`. -/
theorem «wk_encode_transaction» :
    KeepsOn WorldOK WorldOK (ofString "encode_transaction") := by sorry
/-- `encode_withdrawal_rlp` (AST line 32114): keeps `WorldOK`. -/
theorem «wk_encode_withdrawal_rlp» :
    KeepsOn WorldOK WorldOK (ofString "encode_withdrawal_rlp") := by sorry
/-- `ext_code_of` (AST line 16953): keeps `WorldOK`. -/
theorem «wk_ext_code_of» :
    KeepsOn WorldOK WorldOK (ofString "ext_code_of") := by sorry
/-- `get_account` (AST line 13188): keeps `WorldOK`. -/
theorem «wk_get_account» :
    KeepsOn WorldOK WorldOK (ofString "get_account") := by sorry
/-- `get_code` (AST line 13203): keeps `WorldOK`. -/
theorem «wk_get_code» :
    KeepsOn WorldOK WorldOK (ofString "get_code") := by sorry
/-- `idx_start_account` (AST line 14087): keeps `WorldOK`. -/
theorem «wk_idx_start_account» :
    KeepsOn WorldOK WorldOK (ofString "idx_start_account") := by sorry
/-- `idx_start_storage` (AST line 14129): keeps `WorldOK`. -/
theorem «wk_idx_start_storage» :
    KeepsOn WorldOK WorldOK (ofString "idx_start_storage") := by sorry
/-- `increment_nonce` (AST line 13664): keeps `WorldOK`. -/
theorem «wk_increment_nonce» :
    KeepsOn WorldOK WorldOK (ofString "increment_nonce") := by sorry
/-- `mark_account_created` (AST line 13562): keeps `WorldOK`. -/
theorem «wk_mark_account_created» :
    KeepsOn WorldOK WorldOK (ofString "mark_account_created") := by sorry
/-- `mpt_from_witness` (AST line 10459): keeps `WorldOK`. -/
theorem «wk_mpt_from_witness» :
    KeepsOn WorldOK WorldOK (ofString "mpt_from_witness") := by sorry
/-- `mpt_root` (AST line 11223): keeps `WorldOK`. -/
theorem «wk_mpt_root» :
    KeepsOn (MptObjAvoids (fun s => [(locN s "out", 32)])) WorldOK (ofString "mpt_root") := by sorry
/-- `mpt_set` (AST line 10872): keeps `WorldOK`. -/
theorem «wk_mpt_set» :
    KeepsOn MptObjReady WorldOK (ofString "mpt_set") := by sorry
/-- `nodedb_build` (AST line 9937): keeps `WorldOK`. -/
theorem «wk_nodedb_build» :
    KeepsOn WorldOK WorldOK (ofString "nodedb_build") := by sorry
/-- `payload_header` (AST line 32645): keeps `WorldOK`. -/
theorem «wk_payload_header» :
    KeepsOn WorldOK WorldOK (ofString "payload_header") := by sorry
/-- `process_checked_system_transaction` (AST line 32928): keeps `WorldOK`. -/
theorem «wk_process_checked_system_transaction» :
    KeepsOn WorldOK WorldOK (ofString "process_checked_system_transaction") := by sorry
/-- `process_general_purpose_requests` (AST line 33507): keeps `WorldOK`. -/
theorem «wk_process_general_purpose_requests» :
    KeepsOn ReqsFresh WorldOK (ofString "process_general_purpose_requests") := by sorry
/-- `process_message_call` (AST line 19661): keeps `WorldOK`. -/
theorem «wk_process_message_call» :
    KeepsOn MsgReady WorldOK (ofString "process_message_call") := by sorry
/-- `process_transaction` (AST line 33103): keeps `WorldOK`. -/
theorem «wk_process_transaction» :
    KeepsOn TxReady WorldOK (ofString "process_transaction") := by sorry
/-- `process_unchecked_system_transaction` (AST line 32851): keeps `WorldOK`. -/
theorem «wk_process_unchecked_system_transaction» :
    KeepsOn WorldOK WorldOK (ofString "process_unchecked_system_transaction") := by sorry
/-- `process_withdrawals` (AST line 33458): keeps `WorldOK`. -/
theorem «wk_process_withdrawals» :
    KeepsOn WorldOK WorldOK (ofString "process_withdrawals") := by sorry
/-- `record_pre_state_read` (AST line 12980): keeps `WorldOK`. -/
theorem «wk_record_pre_state_read» :
    KeepsOn WorldOK WorldOK (ofString "record_pre_state_read") := by sorry
/-- `remove_storage_write` (AST line 14206): keeps `WorldOK`. -/
theorem «wk_remove_storage_write» :
    KeepsOn WorldOK WorldOK (ofString "remove_storage_write") := by sorry
/-- `requests_append` (AST line 33485): keeps `WorldOK`. -/
theorem «wk_requests_append» :
    KeepsOn ReqRoom WorldOK (ofString "requests_append") := by sorry
/-- `set_account_balance` (AST line 13647): keeps `WorldOK`. -/
theorem «wk_set_account_balance» :
    KeepsOn WorldOK WorldOK (ofString "set_account_balance") := by sorry
/-- `state_init` (AST line 12708): keeps `WorldOK`. -/
theorem «wk_state_init» :
    KeepsOn WorldOK WorldOK (ofString "state_init") := by sorry
/-- `validate_header` (AST line 9675): keeps `WorldOK`. -/
theorem «wk_validate_header» :
    KeepsOn WorldOK WorldOK (ofString "validate_header") := by sorry
/-- `_resolve_step` (AST line 10077): writes only memory it allocates. -/
theorem «ww__resolve_step» :
    WritesWithin (fun s => [])
    ["heap_ptr", "scratch_ptr"] (ofString "_resolve_step") := by sorry
/-- `alloc` (AST line 66): writes only memory it allocates. -/
theorem «ww_alloc» :
    WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "alloc") := by sorry
/-- `bal_init` (AST line 13863): writes only memory it allocates. -/
theorem «ww_bal_init» :
    WritesWithin (fun s => [])
    ["bal_accounts", "bal_idx_accts", "bal_idx_stor", "bal_index", "bal_key_buf", "heap_ptr"] (ofString "bal_init") := by sorry
/-- `blake2_init` (AST line 20017): writes only memory it allocates and the buffers b2_iv, b2_sigma. -/
theorem «ww_blake2_init» :
    WritesWithin (fun s => [(globN s "b2_iv", 64), (globN s "b2_sigma", 80)])
    ["b2_iv", "b2_sigma", "b2_v", "heap_ptr"] (ofString "blake2_init") := by sorry
/-- `bls_precompiles_init` (AST line 30678): writes only memory it allocates and the buffers bls_c, bls_discount. -/
theorem «ww_bls_precompiles_init» :
    WritesWithin (fun s => [(globN s "bls_c", 7136), (globN s "bls_discount", 2048)])
    ["bls_c", "bls_discount", "heap_ptr"] (ofString "bls_precompiles_init") := by sorry
/-- `bn254_init` (AST line 22161): writes only memory it allocates and the buffers bn_expw, bn_gamma. -/
theorem «ww_bn254_init» :
    WritesWithin (fun s => [(globN s "bn_expw", 352), (globN s "bn_gamma", 384)])
    ["bn_expw", "bn_gamma", "heap_ptr"] (ofString "bn254_init") := by sorry
/-- `cache_get_root` (AST line 32325): writes only memory it allocates and the buffers keccak_pad, keccak_st, mpt_nib_scratch. -/
theorem «ww_cache_get_root» :
    WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_nib_scratch", 64)])
    ["heap_ptr", "scratch_ptr"] (ofString "cache_get_root") := by sorry
/-- `compute_contract_address` (AST line 19098): writes its parameter extents and the buffers keccak_pad, keccak_st. -/
theorem «ww_compute_contract_address» :
    WritesWithin (fun s => [(locN s "out", 20), (globN s "keccak_pad", 136), (globN s "keccak_st", 200)])
    ["heap_ptr"] (ofString "compute_contract_address") := by sorry
/-- `decode_transaction` (AST line 11805): writes only memory it allocates. -/
theorem «ww_decode_transaction» :
    WritesWithin (fun s => [])
    ["heap_ptr", "scratch_ptr"] (ofString "decode_transaction") := by sorry
/-- `encode_account` (AST line 11343): writes its parameter extents and the buffers mpt_hash_scratch. -/
theorem «ww_encode_account» :
    WritesWithin (fun s => [(locN s "out", 110), (globN s "mpt_hash_scratch", 40)])
    [] (ofString "encode_account") := by sorry
/-- `evm_init` (AST line 17353): writes only memory it allocates and the buffers evm_empty, keccak_pad, keccak_st, null_address, transfer_topic, vm_system_address. -/
theorem «ww_evm_init» :
    WritesWithin (fun s => [(globN s "evm_empty", 8), (globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "null_address", 24), (globN s "transfer_topic", 32), (globN s "vm_system_address", 24)])
    ["evm_empty", "evm_key_buf", "heap_ptr", "null_address", "pre_hdr_buf", "transfer_topic", "vm_system_address"] (ofString "evm_init") := by sorry
/-- `extract_deposit_data` (AST line 32212): writes its parameter extents. -/
theorem «ww_extract_deposit_data» :
    WritesWithin (fun s => [(locN s "out", 192)])
    ["heap_ptr"] (ofString "extract_deposit_data") := by sorry
/-- `fork_init` (AST line 32522): writes only memory it allocates and the buffers beacon_roots_address, builder_deposit_address, builder_exit_address, consolidation_request_address, deposit_contract_address, deposit_event_signature_hash, history_storage_address, precompile_addrs, withdrawal_request_address, zero32. -/
theorem «ww_fork_init» :
    WritesWithin (fun s => [(globN s "beacon_roots_address", 24), (globN s "builder_deposit_address", 24), (globN s "builder_exit_address", 24), (globN s "consolidation_request_address", 24), (globN s "deposit_contract_address", 24), (globN s "deposit_event_signature_hash", 32), (globN s "history_storage_address", 24), (globN s "precompile_addrs", 360), (globN s "withdrawal_request_address", 24), (globN s "zero32", 32)])
    ["beacon_roots_address", "builder_deposit_address", "builder_exit_address", "consolidation_request_address", "deposit_contract_address", "deposit_event_signature_hash", "heap_ptr", "history_storage_address", "precompile_addrs", "withdrawal_request_address", "zero32"] (ofString "fork_init") := by sorry
/-- `header_hash` (AST line 9460): writes its parameter extents and the buffers keccak_pad, keccak_st. -/
theorem «ww_header_hash» :
    WritesWithin (fun s => [(locN s "out", 32), (globN s "keccak_pad", 136), (globN s "keccak_st", 200)])
    ["heap_ptr"] (ofString "header_hash") := by sorry
/-- `header_init` (AST line 9657): writes only memory it allocates and the buffers hdr_zero8. -/
theorem «ww_header_init» :
    WritesWithin (fun s => [(globN s "hdr_zero8", 8)])
    ["hdr_zero8", "heap_ptr"] (ofString "header_init") := by sorry
/-- `htab_copy` (AST line 5354): writes only memory it allocates. -/
theorem «ww_htab_copy» :
    WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "htab_copy") := by sorry
/-- `htr_new_payload_request` (AST line 9053): writes its parameter extents and the buffers ssz_len_chunk. -/
theorem «ww_htr_new_payload_request» :
    WritesWithin (fun s => [(locN s "out", 32), (globN s "ssz_len_chunk", 32)])
    ["heap_ptr"] (ofString "htr_new_payload_request") := by sorry
/-- `is_valid_versioned_hashes` (AST line 32794): writes only memory it allocates. -/
theorem «ww_is_valid_versioned_hashes» :
    WritesWithin (fun s => [])
    ["heap_ptr", "scratch_ptr"] (ofString "is_valid_versioned_hashes") := by sorry
/-- `is_warm_storage_key` (AST line 16559): writes only memory it allocates and the buffers sk_buf. -/
theorem «ww_is_warm_storage_key» :
    WritesWithin (fun s => [(globN s "sk_buf", 64)])
    [] (ofString "is_warm_storage_key") := by sorry
/-- `keccak256` (AST line 4262): writes its parameter extents and the buffers keccak_pad, keccak_st. -/
theorem «ww_keccak256» :
    WritesWithin (fun s => [(locN s "out", 32), (globN s "keccak_pad", 136), (globN s "keccak_st", 200)])
    [] (ofString "keccak256") := by sorry
/-- `keccak_init` (AST line 3974): writes only memory it allocates and the buffers keccak_rc. -/
theorem «ww_keccak_init» :
    WritesWithin (fun s => [(globN s "keccak_rc", 192)])
    ["heap_ptr", "keccak_pad", "keccak_rc", "keccak_st"] (ofString "keccak_init") := by sorry
/-- `logs_bloom` (AST line 31941): writes its parameter extents and the buffers keccak_pad, keccak_st. -/
theorem «ww_logs_bloom» :
    WritesWithin (fun s => [(locN s "out", 256), (globN s "keccak_pad", 136), (globN s "keccak_st", 200)])
    ["heap_ptr"] (ofString "logs_bloom") := by sorry
/-- `lst_new` (AST line 13804): writes only memory it allocates. -/
theorem «ww_lst_new» :
    WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "lst_new") := by sorry
/-- `lst_push` (AST line 13840): writes its parameter extents. -/
theorem «ww_lst_push» :
    WritesWithin (fun s => [(locN s "l", 24), (memW s (locN s "l"), locN s "esz" * memW s (locN s "l" + 16))])
    ["heap_ptr"] (ofString "lst_push") := by sorry
/-- `memcpy` (AST line 198): writes its parameter extents. -/
theorem «ww_memcpy» :
    WritesWithin (fun s => [(locN s "dst", locN s "n")])
    [] (ofString "memcpy") := by sorry
/-- `memzero` (AST line 251): writes its parameter extents. -/
theorem «ww_memzero» :
    WritesWithin (fun s => [(locN s "dst", locN s "n")])
    [] (ofString "memzero") := by sorry
/-- `mpt_init` (AST line 9781): writes only memory it allocates and the buffers empty_code_hash, empty_trie_root, keccak_pad, keccak_st, mpt_hash_scratch. -/
theorem «ww_mpt_init» :
    WritesWithin (fun s => [(globN s "empty_code_hash", 32), (globN s "empty_trie_root", 32), (globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_hash_scratch", 40)])
    ["empty_code_hash", "empty_trie_root", "heap_ptr", "mpt_hash_scratch", "mpt_key_scratch", "mpt_nib_scratch"] (ofString "mpt_init") := by sorry
/-- `mpt_new` (AST line 10444): writes only memory it allocates. -/
theorem «ww_mpt_new» :
    WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "mpt_new") := by sorry
/-- `mpt_nibble_key` (AST line 10470): writes only memory it allocates and the buffers keccak_pad, keccak_st, mpt_hash_scratch. -/
theorem «ww_mpt_nibble_key» :
    WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_hash_scratch", 40)])
    ["heap_ptr"] (ofString "mpt_nibble_key") := by sorry
/-- `msg_new` (AST line 15344): writes only memory it allocates. -/
theorem «ww_msg_new» :
    WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "msg_new") := by sorry
/-- `node_new_ext` (AST line 10021): writes only memory it allocates. -/
theorem «ww_node_new_ext» :
    WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "node_new_ext") := by sorry
/-- `recover_sender_with_chain_id` (AST line 12542): writes its parameter extents and the buffers keccak_pad, keccak_st, u256_ws. -/
theorem «ww_recover_sender_with_chain_id» :
    WritesWithin (fun s => [(locN s "out20", 20), (globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "u256_ws", 640)])
    ["heap_ptr"] (ofString "recover_sender_with_chain_id") := by sorry
/-- `ripemd160_init` (AST line 19738): writes only memory it allocates and the buffers rmd_tab. -/
theorem «ww_ripemd160_init» :
    WritesWithin (fun s => [(globN s "rmd_tab", 160)])
    ["heap_ptr", "rmd_h", "rmd_pad", "rmd_tab", "rmd_x"] (ofString "ripemd160_init") := by sorry
/-- `rlp_encode_bytes` (AST line 4768): writes its parameter extents. -/
theorem «ww_rlp_encode_bytes» :
    WritesWithin (fun s => [(locN s "dst", locN s "n" + 9)])
    [] (ofString "rlp_encode_bytes") := by sorry
/-- `rlp_encode_word` (AST line 4790): writes its parameter extents. -/
theorem «ww_rlp_encode_word» :
    WritesWithin (fun s => [(locN s "dst", 33)])
    [] (ofString "rlp_encode_word") := by sorry
/-- `rlp_item` (AST line 4338): writes only memory it allocates. -/
theorem «ww_rlp_item» :
    WritesWithin (fun s => [])
    ["scratch_ptr"] (ofString "rlp_item") := by sorry
/-- `scratch_alloc` (AST line 154): writes only memory it allocates. -/
theorem «ww_scratch_alloc» :
    WritesWithin (fun s => [])
    ["scratch_ptr"] (ofString "scratch_alloc") := by sorry
/-- `sha256_init` (AST line 2327): writes only memory it allocates. -/
theorem «ww_sha256_init» :
    WritesWithin (fun s => [])
    ["heap_ptr", "sha_pad", "sha_st"] (ofString "sha256_init") := by sorry
/-- `sk_make` (AST line 12923): writes only memory it allocates and the buffers sk_buf. -/
theorem «ww_sk_make» :
    WritesWithin (fun s => [(globN s "sk_buf", 64)])
    [] (ofString "sk_make") := by sorry
/-- `ssz_init` (AST line 7520): writes only memory it allocates and the buffers zero_hashes. -/
theorem «ww_ssz_init» :
    WritesWithin (fun s => [(globN s "zero_hashes", 2048)])
    ["heap_ptr", "ssz_len_chunk", "ssz_offs", "zero_hashes"] (ofString "ssz_init") := by sorry
/-- `st_le64` (AST line 571): writes its parameter extents. -/
theorem «ww_st_le64» :
    WritesWithin (fun s => [(locN s "p", 8)])
    [] (ofString "st_le64") := by sorry
/-- `state_fresh_tx` (AST line 12778): writes only memory it allocates and the buffers ts. -/
theorem «ww_state_fresh_tx» :
    WritesWithin (fun s => [(globN s "ts", 72)])
    ["heap_ptr", "journal_n", "ts"] (ofString "state_fresh_tx") := by sorry
/-- `te_new` (AST line 32838): writes only memory it allocates. -/
theorem «ww_te_new» :
    WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "te_new") := by sorry
/-- `track_ancestor_access` (AST line 13771): writes only memory it allocates and the buffers bs. -/
theorem «ww_track_ancestor_access» :
    WritesWithin (fun s => [(globN s "bs", 80)])
    [] (ofString "track_ancestor_access") := by sorry
/-- `u256_to_be32` (AST line 2265): writes its parameter extents. -/
theorem «ww_u256_to_be32» :
    WritesWithin (fun s => [(locN s "out", 32)])
    [] (ofString "u256_to_be32") := by sorry
/-- `u256_to_be_min` (AST line 2302): writes its parameter extents. -/
theorem «ww_u256_to_be_min» :
    WritesWithin (fun s => [(locN s "out", 32)])
    [] (ofString "u256_to_be_min") := by sorry
/-- `u256_ws_init` (AST line 766): writes only memory it allocates. -/
theorem «ww_u256_ws_init» :
    WritesWithin (fun s => [])
    ["heap_ptr", "u256_ws"] (ofString "u256_ws_init") := by sorry
/-- `validate_headers` (AST line 9476): writes only memory it allocates and the buffers keccak_pad, keccak_st. -/
theorem «ww_validate_headers» :
    WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200)])
    ["heap_ptr", "scratch_ptr"] (ofString "validate_headers") := by sorry
/-- `ws_get_account_optional` (AST line 13009): writes only memory it allocates and the buffers keccak_pad, keccak_st, mpt_nib_scratch. -/
theorem «ww_ws_get_account_optional» :
    WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_nib_scratch", 64)])
    ["heap_ptr", "scratch_ptr"] (ofString "ws_get_account_optional") := by sorry
/-- `ws_storage_root_of` (AST line 13027): writes only memory it allocates and the buffers keccak_pad, keccak_st, mpt_nib_scratch. -/
theorem «ww_ws_storage_root_of» :
    WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_nib_scratch", 64)])
    ["heap_ptr", "scratch_ptr"] (ofString "ws_storage_root_of") := by sorry

/-! #### Composition obligations of the guarded bodies (generated)

`GBody.«f»`: from the bounds of `f`'s direct callees and the contracts of the callees at
its guard-carrying call sites, `f`'s body is bounded under its guard. `gbody_f` is the
primitive; `gb_f` is PROVED from it. -/

/-- The body of `_decode_witness_node_body` alone (AST line 10196, guard `ArenaReady`, #0 GUARD). Its direct callees are
exactly `_decode_step`, `_resolve_step`, `mpt_fail`, `node_new_ext`, `rlp_item` (`«callees__decode_witness_node_body»`, checked against the AST). Hypotheses: the bound
of each of these 5 callees, then the contract of each callee at a guard-carrying
call site (5: `ak__decode_step`, `ww__resolve_step`, `ro_mpt_fail`, `ww_node_new_ext`, `ww_rlp_item`). Nothing else is assumed. -/
def GBody.«_decode_witness_node_body» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "_decode_step") K.«_decode_step») →
  (TerminatingFunBoundedOn GuestInv (ofString "_resolve_step") K.«_resolve_step») →
  (TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail») →
  (TerminatingFunBoundedOn GuestInv (ofString "node_new_ext") K.«node_new_ext») →
  (TerminatingFunBoundedOn GuestInv (ofString "rlp_item") K.«rlp_item») →
  (KeepsOn ArenaReady ArenaReady (ofString "_decode_step")) →
  (WritesWithin (fun s => [])
    ["heap_ptr", "scratch_ptr"] (ofString "_resolve_step")) →
  (ReadOnlyFn (ofString "mpt_fail")) →
  (WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "node_new_ext")) →
  (WritesWithin (fun s => [])
    ["scratch_ptr"] (ofString "rlp_item")) →
  TerminatingFunBoundedOn ArenaReady (ofString "_decode_witness_node_body") K.«_decode_witness_node_body»

/-- The direct callees of `_decode_witness_node_body`, read off its AST body (revision 6). -/
theorem «callees__decode_witness_node_body» : sameNames (progCallees (fnBody Guest.Software.guestFn__decode_witness_node_body))
    ["_decode_step", "_resolve_step", "mpt_fail", "node_new_ext", "rlp_item"] = true := by decide

theorem «gbody__decode_witness_node_body» : GBody.«_decode_witness_node_body» := by sorry

theorem «gb__decode_witness_node_body» : TerminatingFunBoundedOn ArenaReady (ofString "_decode_witness_node_body") K.«_decode_witness_node_body» :=
  «gbody__decode_witness_node_body» «fb__decode_step» «fb__resolve_step» «fb_mpt_fail» «fb_node_new_ext» «fb_rlp_item» «ak__decode_step» «ww__resolve_step» «ro_mpt_fail» «ww_node_new_ext» «ww_rlp_item»

/-- The body of `_decode_witness_node_mpt` alone (AST line 10311, guard `WorldOK`, loop-free). Its direct callees are
exactly `_decode_witness_node_body`, `scratch_release` (`«callees__decode_witness_node_mpt»`, checked against the AST). Hypotheses: the bound
of each of these 2 callees, then the contract of each callee at a guard-carrying
call site (0: none). Nothing else is assumed. -/
def GBody.«_decode_witness_node_mpt» : Prop :=
  (TerminatingFunBoundedOn ArenaReady (ofString "_decode_witness_node_body") K.«_decode_witness_node_body») →
  (TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release») →
  TerminatingFunBoundedOn WorldOK (ofString "_decode_witness_node_mpt") K.«_decode_witness_node_mpt»

/-- The direct callees of `_decode_witness_node_mpt`, read off its AST body (revision 6). -/
theorem «callees__decode_witness_node_mpt» : sameNames (progCallees (fnBody Guest.Software.guestFn__decode_witness_node_mpt))
    ["_decode_witness_node_body", "scratch_release"] = true := by decide

theorem «lookup__decode_witness_node_mpt» : originalRuntimeCode.lookup (ofString "_decode_witness_node_mpt") =
    some ((sourceFunctionEntry Guest.Software.guestFn__decode_witness_node_mpt).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 263 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__decode_witness_node_mpt) rfl

/-- PROVED by concrete-body composition (no longer a primitive). -/
theorem «gbody__decode_witness_node_mpt» : GBody.«_decode_witness_node_mpt» := by
  intro hb hsr
  refine ⟨_, _, _, «lookup__decode_witness_node_mpt», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn__decode_witness_node_mpt, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (LocalsOnly.of_localsFree localsFree_worldOK) _ (by simp) _ _
      (TerminatingProgBoundedOn.dec_onLocals (LocalsOnly.of_localsFree localsFree_worldOK) _ (by simp) _ _
        (TerminatingProgBoundedOn.seq_guestInv_after
          (TerminatingProgBoundedOn.callHandle_on hb worldOK_guestInv _ _ _ (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hsr _ _) (TerminatingProgBoundedOn.of_clock (fun s => clock_raise s _ _))) _
            (callEntryOn_of_imp localsFree_arenaReady (fun s h => h.1) _ _))
          worldOK_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))))) ?_
  unfold K.«_decode_witness_node_mpt»; omega

theorem «gb__decode_witness_node_mpt» : TerminatingFunBoundedOn WorldOK (ofString "_decode_witness_node_mpt") K.«_decode_witness_node_mpt» :=
  «gbody__decode_witness_node_mpt» «gb__decode_witness_node_body» «fb_scratch_release»

/-- The body of `_decode_witness_node` alone (AST line 10328, guard `WorldOK`, loop-free). Its direct callees are
exactly `_decode_witness_node_mpt`, `scratch_mark`, `scratch_release` (`«callees__decode_witness_node»`, checked against the AST). Hypotheses: the bound
of each of these 3 callees, then the contract of each callee at a guard-carrying
call site (1: `ro_scratch_mark`). Nothing else is assumed. -/
def GBody.«_decode_witness_node» : Prop :=
  (TerminatingFunBoundedOn WorldOK (ofString "_decode_witness_node_mpt") K.«_decode_witness_node_mpt») →
  (TerminatingFunBoundedOn GuestInv (ofString "scratch_mark") K.«scratch_mark») →
  (TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release») →
  (ReadOnlyFn (ofString "scratch_mark")) →
  TerminatingFunBoundedOn WorldOK (ofString "_decode_witness_node") K.«_decode_witness_node»

/-- The direct callees of `_decode_witness_node`, read off its AST body (revision 6). -/
theorem «callees__decode_witness_node» : sameNames (progCallees (fnBody Guest.Software.guestFn__decode_witness_node))
    ["_decode_witness_node_mpt", "scratch_mark", "scratch_release"] = true := by decide

theorem «lookup__decode_witness_node» : originalRuntimeCode.lookup (ofString "_decode_witness_node") =
    some ((sourceFunctionEntry Guest.Software.guestFn__decode_witness_node).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 264 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__decode_witness_node) rfl

/-- PROVED by concrete-body composition (no longer a primitive). -/
theorem «gbody__decode_witness_node» : GBody.«_decode_witness_node» := by
  intro hmpt hmk hsr hro
  refine ⟨_, _, _, «lookup__decode_witness_node», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn__decode_witness_node, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.decCall_on hmk _ _ _
      (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _)
      (ReadOnlyFn.resumeOn (LocalsOnly.of_localsFree localsFree_worldOK) worldOK_guestInv hro _ (by simp) _)
      (TerminatingProgBoundedOn.dec_onLocals (LocalsOnly.of_localsFree localsFree_worldOK) _ (by simp) _ _
        (TerminatingProgBoundedOn.dec_onLocals (LocalsOnly.of_localsFree localsFree_worldOK) _ (by simp) _ _
          (TerminatingProgBoundedOn.seq_guestInv_after
            (TerminatingProgBoundedOn.callHandle_on hmpt worldOK_guestInv _ _ _ (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hsr _ _) (TerminatingProgBoundedOn.of_clock (fun s => clock_raise s _ _))) _ (callEntryOn_of_localsFree localsFree_worldOK _ _))
            worldOK_guestInv
            (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hsr _ _)
              (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))))))) ?_
  unfold K.«_decode_witness_node»; omega

theorem «gb__decode_witness_node» : TerminatingFunBoundedOn WorldOK (ofString "_decode_witness_node") K.«_decode_witness_node» :=
  «gbody__decode_witness_node» «gb__decode_witness_node_mpt» «fb_scratch_mark» «fb_scratch_release» «ro_scratch_mark»

/-- The body of `_mpt_delete_node_body` alone (AST line 10758, guard `MptReady`, #0 GUARD; #1 GUARD). Its direct callees are
exactly `_collapse_branch`, `_delete_ext_finish`, `common_prefix_length`, `memeq`, `mpt_fail`, `node_invalidate`, `scratch_alloc` (`«callees__mpt_delete_node_body»`, checked against the AST). Hypotheses: the bound
of each of these 7 callees, then the contract of each callee at a guard-carrying
call site (8: `nf__collapse_branch`, `nf__delete_ext_finish`, `ro_common_prefix_length`, `rv_common_prefix_length`, `ro_memeq`, `ro_mpt_fail`, `nf_node_invalidate`, `ww_scratch_alloc`). Nothing else is assumed. -/
def GBody.«_mpt_delete_node_body» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "_collapse_branch") K.«_collapse_branch») →
  (TerminatingFunBoundedOn GuestInv (ofString "_delete_ext_finish") K.«_delete_ext_finish») →
  (TerminatingFunBoundedOn GuestInv (ofString "common_prefix_length") K.«common_prefix_length») →
  (TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») →
  (TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail») →
  (TerminatingFunBoundedOn GuestInv (ofString "node_invalidate") K.«node_invalidate») →
  (TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc») →
  (NodeFn ["node"]
    (fun s Nd =>
      NodeKind s Nd "node" 3)
    (ofString "_collapse_branch")) →
  (NodeFn ["node", "nc"]
    (fun s Nd =>
      NodeKind s Nd "node" 2 ∧ KeyIn s Nd (locN s "seg") (locN s "sl"))
    (ofString "_delete_ext_finish")) →
  (ReadOnlyFn (ofString "common_prefix_length")) →
  (RetLe (fun s => min (locN s "al") (locN s "bl")) (ofString "common_prefix_length")) →
  (ReadOnlyFn (ofString "memeq")) →
  (ReadOnlyFn (ofString "mpt_fail")) →
  (NodeFn ["nd"]
    (fun _ _ => True)
    (ofString "node_invalidate")) →
  (WritesWithin (fun s => [])
    ["scratch_ptr"] (ofString "scratch_alloc")) →
  TerminatingFunBoundedOn MptReady (ofString "_mpt_delete_node_body") K.«_mpt_delete_node_body»

/-- The direct callees of `_mpt_delete_node_body`, read off its AST body (revision 6). -/
theorem «callees__mpt_delete_node_body» : sameNames (progCallees (fnBody Guest.Software.guestFn__mpt_delete_node_body))
    ["_collapse_branch", "_delete_ext_finish", "common_prefix_length", "memeq", "mpt_fail", "node_invalidate", "scratch_alloc"] = true := by decide

theorem «gbody__mpt_delete_node_body» : GBody.«_mpt_delete_node_body» := by sorry

theorem «gb__mpt_delete_node_body» : TerminatingFunBoundedOn MptReady (ofString "_mpt_delete_node_body") K.«_mpt_delete_node_body» :=
  «gbody__mpt_delete_node_body» «fb__collapse_branch» «fb__delete_ext_finish» «fb_common_prefix_length» «fb_memeq» «fb_mpt_fail» «fb_node_invalidate» «fb_scratch_alloc» «nf__collapse_branch» «nf__delete_ext_finish» «ro_common_prefix_length» «rv_common_prefix_length» «ro_memeq» «ro_mpt_fail» «nf_node_invalidate» «ww_scratch_alloc»

/-- The body of `_mpt_delete_node` alone (AST line 10852, guard `MptReady`, loop-free). Its direct callees are
exactly `_mpt_delete_node_body`, `scratch_mark`, `scratch_release` (`«callees__mpt_delete_node»`, checked against the AST). Hypotheses: the bound
of each of these 3 callees, then the contract of each callee at a guard-carrying
call site (1: `ro_scratch_mark`). Nothing else is assumed. -/
def GBody.«_mpt_delete_node» : Prop :=
  (TerminatingFunBoundedOn MptReady (ofString "_mpt_delete_node_body") K.«_mpt_delete_node_body») →
  (TerminatingFunBoundedOn GuestInv (ofString "scratch_mark") K.«scratch_mark») →
  (TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release») →
  (ReadOnlyFn (ofString "scratch_mark")) →
  TerminatingFunBoundedOn MptReady (ofString "_mpt_delete_node") K.«_mpt_delete_node»

/-- The direct callees of `_mpt_delete_node`, read off its AST body (revision 6). -/
theorem «callees__mpt_delete_node» : sameNames (progCallees (fnBody Guest.Software.guestFn__mpt_delete_node))
    ["_mpt_delete_node_body", "scratch_mark", "scratch_release"] = true := by decide

theorem «gbody__mpt_delete_node» : GBody.«_mpt_delete_node» := by sorry

theorem «gb__mpt_delete_node» : TerminatingFunBoundedOn MptReady (ofString "_mpt_delete_node") K.«_mpt_delete_node» :=
  «gbody__mpt_delete_node» «gb__mpt_delete_node_body» «fb_scratch_mark» «fb_scratch_release» «ro_scratch_mark»

/-- The body of `_mpt_insert_node` alone (AST line 10598, guard `MptReady`, #0 GUARD). Its direct callees are
exactly `_insert_into_leaf`, `_split_extension`, `common_prefix_length`, `mpt_fail`, `node_invalidate`, `node_new_ext`, `node_new_leaf` (`«callees__mpt_insert_node»`, checked against the AST). Hypotheses: the bound
of each of these 7 callees, then the contract of each callee at a guard-carrying
call site (8: `nf__insert_into_leaf`, `nf__split_extension`, `ro_common_prefix_length`, `rv_common_prefix_length`, `ro_mpt_fail`, `nf_node_invalidate`, `nf_node_new_ext`, `nf_node_new_leaf`). Nothing else is assumed. -/
def GBody.«_mpt_insert_node» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "_insert_into_leaf") K.«_insert_into_leaf») →
  (TerminatingFunBoundedOn GuestInv (ofString "_split_extension") K.«_split_extension») →
  (TerminatingFunBoundedOn GuestInv (ofString "common_prefix_length") K.«common_prefix_length») →
  (TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail») →
  (TerminatingFunBoundedOn GuestInv (ofString "node_invalidate") K.«node_invalidate») →
  (TerminatingFunBoundedOn GuestInv (ofString "node_new_ext") K.«node_new_ext») →
  (TerminatingFunBoundedOn GuestInv (ofString "node_new_leaf") K.«node_new_leaf») →
  (NodeFn ["node"]
    (fun s Nd =>
      NodeKind s Nd "node" 1 ∧ KeyIn s Nd (locN s "rk") (locN s "rl"))
    (ofString "_insert_into_leaf")) →
  (NodeFn ["node"]
    (fun s Nd =>
      NodeKind s Nd "node" 2 ∧ KeyIn s Nd (locN s "rk") (locN s "rl") ∧
      locN s "pl" < memW s (locN s "node" + 40) ∧ locN s "pl" ≤ locN s "rl")
    (ofString "_split_extension")) →
  (ReadOnlyFn (ofString "common_prefix_length")) →
  (RetLe (fun s => min (locN s "al") (locN s "bl")) (ofString "common_prefix_length")) →
  (ReadOnlyFn (ofString "mpt_fail")) →
  (NodeFn ["nd"]
    (fun _ _ => True)
    (ofString "node_invalidate")) →
  (NodeFn ["child"]
    (fun s Nd =>
      KeyIn s Nd (locN s "nib") (locN s "nlen"))
    (ofString "node_new_ext")) →
  (NodeFn []
    (fun s Nd =>
      KeyIn s Nd (locN s "nib") (locN s "nlen"))
    (ofString "node_new_leaf")) →
  TerminatingFunBoundedOn MptReady (ofString "_mpt_insert_node") K.«_mpt_insert_node»

/-- The direct callees of `_mpt_insert_node`, read off its AST body (revision 6). -/
theorem «callees__mpt_insert_node» : sameNames (progCallees (fnBody Guest.Software.guestFn__mpt_insert_node))
    ["_insert_into_leaf", "_split_extension", "common_prefix_length", "mpt_fail", "node_invalidate", "node_new_ext", "node_new_leaf"] = true := by decide

theorem «gbody__mpt_insert_node» : GBody.«_mpt_insert_node» := by sorry

theorem «gb__mpt_insert_node» : TerminatingFunBoundedOn MptReady (ofString "_mpt_insert_node") K.«_mpt_insert_node» :=
  «gbody__mpt_insert_node» «fb__insert_into_leaf» «fb__split_extension» «fb_common_prefix_length» «fb_mpt_fail» «fb_node_invalidate» «fb_node_new_ext» «fb_node_new_leaf» «nf__insert_into_leaf» «nf__split_extension» «ro_common_prefix_length» «rv_common_prefix_length» «ro_mpt_fail» «nf_node_invalidate» «nf_node_new_ext» «nf_node_new_leaf»

/-- The body of `mpt_set` alone (AST line 10872, guard `MptObjReady`, loop-free). Its direct callees are
exactly `_mpt_delete_node`, `_mpt_insert_node`, `mpt_nibble_key` (`«callees_mpt_set»`, checked against the AST). Hypotheses: the bound
of each of these 3 callees, then the contract of each callee at a guard-carrying
call site (2: `ww_mpt_nibble_key`, `nk_mpt_nibble_key`). Nothing else is assumed. -/
def GBody.«mpt_set» : Prop :=
  (TerminatingFunBoundedOn MptReady (ofString "_mpt_delete_node") K.«_mpt_delete_node») →
  (TerminatingFunBoundedOn MptReady (ofString "_mpt_insert_node") K.«_mpt_insert_node») →
  (TerminatingFunBoundedOn GuestInv (ofString "mpt_nibble_key") K.«mpt_nibble_key») →
  (WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_hash_scratch", 40)])
    ["heap_ptr"] (ofString "mpt_nibble_key")) →
  (RetNibbles (ofString "mpt_nibble_key")) →
  TerminatingFunBoundedOn MptObjReady (ofString "mpt_set") K.«mpt_set»

/-- The direct callees of `mpt_set`, read off its AST body (revision 6). -/
theorem «callees_mpt_set» : sameNames (progCallees (fnBody Guest.Software.guestFn_mpt_set))
    ["_mpt_delete_node", "_mpt_insert_node", "mpt_nibble_key"] = true := by decide

theorem «gbody_mpt_set» : GBody.«mpt_set» := by sorry

theorem «gb_mpt_set» : TerminatingFunBoundedOn MptObjReady (ofString "mpt_set") K.«mpt_set» :=
  «gbody_mpt_set» «gb__mpt_delete_node» «gb__mpt_insert_node» «fb_mpt_nibble_key» «ww_mpt_nibble_key» «nk_mpt_nibble_key»

/-- The body of `build_mpt_indexed` alone (AST line 11243, guard `WorldOK`, #0 CTR). Its direct callees are
exactly `heap_mark`, `heap_release`, `mpt_new`, `mpt_root`, `mpt_set`, `rlp_encode_word` (`«callees_build_mpt_indexed»`, checked against the AST). Hypotheses: the bound
of each of these 6 callees, then the contract of each callee at a guard-carrying
call site (4: `ro_heap_mark`, `ww_mpt_new`, `wk_mpt_set`, `ww_rlp_encode_word`). Nothing else is assumed. -/
def GBody.«build_mpt_indexed» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark») →
  (TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release») →
  (TerminatingFunBoundedOn GuestInv (ofString "mpt_new") K.«mpt_new») →
  (TerminatingFunBoundedOn GuestInv (ofString "mpt_root") K.«mpt_root») →
  (TerminatingFunBoundedOn MptObjReady (ofString "mpt_set") K.«mpt_set») →
  (TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_word") K.«rlp_encode_word») →
  (ReadOnlyFn (ofString "heap_mark")) →
  (WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "mpt_new")) →
  (KeepsOn MptObjReady WorldOK (ofString "mpt_set")) →
  (WritesWithin (fun s => [(locN s "dst", 33)])
    [] (ofString "rlp_encode_word")) →
  TerminatingFunBoundedOn WorldOK (ofString "build_mpt_indexed") K.«build_mpt_indexed»

/-- The direct callees of `build_mpt_indexed`, read off its AST body (revision 6). -/
theorem «callees_build_mpt_indexed» : sameNames (progCallees (fnBody Guest.Software.guestFn_build_mpt_indexed))
    ["heap_mark", "heap_release", "mpt_new", "mpt_root", "mpt_set", "rlp_encode_word"] = true := by decide

theorem «gbody_build_mpt_indexed» : GBody.«build_mpt_indexed» := by sorry

theorem «gb_build_mpt_indexed» : TerminatingFunBoundedOn WorldOK (ofString "build_mpt_indexed") K.«build_mpt_indexed» :=
  «gbody_build_mpt_indexed» «fb_heap_mark» «fb_heap_release» «fb_mpt_new» «fb_mpt_root» «gb_mpt_set» «fb_rlp_encode_word» «ro_heap_mark» «ww_mpt_new» «wk_mpt_set» «ww_rlp_encode_word»

/-- The body of `decode_witness_to_mpt` alone (AST line 10348, guard `WorldOK`, loop-free). Its direct callees are
exactly `_decode_witness_node`, `alloc`, `memcpy`, `memeq`, `mpt_fail`, `nodedb_lookup` (`«callees_decode_witness_to_mpt»`, checked against the AST). Hypotheses: the bound
of each of these 6 callees, then the contract of each callee at a guard-carrying
call site (3: `ro_memeq`, `ro_mpt_fail`, `ro_nodedb_lookup`). Nothing else is assumed. -/
def GBody.«decode_witness_to_mpt» : Prop :=
  (TerminatingFunBoundedOn WorldOK (ofString "_decode_witness_node") K.«_decode_witness_node») →
  (TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
  (TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy») →
  (TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») →
  (TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail») →
  (TerminatingFunBoundedOn GuestInv (ofString "nodedb_lookup") K.«nodedb_lookup») →
  (ReadOnlyFn (ofString "memeq")) →
  (ReadOnlyFn (ofString "mpt_fail")) →
  (ReadOnlyFn (ofString "nodedb_lookup")) →
  TerminatingFunBoundedOn WorldOK (ofString "decode_witness_to_mpt") K.«decode_witness_to_mpt»

/-- The direct callees of `decode_witness_to_mpt`, read off its AST body (revision 6). -/
theorem «callees_decode_witness_to_mpt» : sameNames (progCallees (fnBody Guest.Software.guestFn_decode_witness_to_mpt))
    ["_decode_witness_node", "alloc", "memcpy", "memeq", "mpt_fail", "nodedb_lookup"] = true := by decide

theorem «lookup_decode_witness_to_mpt» : originalRuntimeCode.lookup (ofString "decode_witness_to_mpt") =
    some ((sourceFunctionEntry Guest.Software.guestFn_decode_witness_to_mpt).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 265 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_witness_to_mpt) rfl

/-- PROVED by concrete-body composition (no longer a primitive). -/
theorem «gbody_decode_witness_to_mpt» : GBody.«decode_witness_to_mpt» := by
  intro hdw hal hmc hme hmf hnl hrme hrmf hrnl
  refine ⟨_, _, _, «lookup_decode_witness_to_mpt», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_decode_witness_to_mpt, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.decCall_on hme _ _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _) (ReadOnlyFn.resumeOn (LocalsOnly.of_localsFree localsFree_worldOK) worldOK_guestInv hrme _ (by simp) _)
      (TerminatingProgBoundedOn.seq_hoare (TerminatingProgBoundedOn.ite_on (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))
        (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s))) (Hoare.ite_return_skip _ _)
        (TerminatingProgBoundedOn.decCall_on hnl _ _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _) (ReadOnlyFn.resumeOn (LocalsOnly.of_localsFree localsFree_worldOK) worldOK_guestInv hrnl _ (by simp) _)
          (TerminatingProgBoundedOn.seq_hoare
            (TerminatingProgBoundedOn.ite_on (TerminatingProgBoundedOn.call_on hmf _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _)) (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
            (Hoare.ite_call_keeps localsFree_worldOK
              (ReadOnlyFn.keepsOn localsFree_worldOK worldOK_guestInv hrmf) _ _)
            (TerminatingProgBoundedOn.decCall_on hdw _ _ _ (callEntryOn_of_localsFree localsFree_worldOK _ _)
              (decCallResumeOn_guestInv worldOK_guestInv _ _ _)
              (TerminatingProgBoundedOn.seq_guestInv
                (TerminatingProgBoundedOn.ite_on
                  (TerminatingProgBoundedOn.decCall_guestInv hal _ _ _
                    (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hmc _ _)
                      (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _)))) (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))))) ?_
  unfold K.«decode_witness_to_mpt»
  simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl]
  omega

theorem «gb_decode_witness_to_mpt» : TerminatingFunBoundedOn WorldOK (ofString "decode_witness_to_mpt") K.«decode_witness_to_mpt» :=
  «gbody_decode_witness_to_mpt» «gb__decode_witness_node» «fb_alloc» «fb_memcpy» «fb_memeq» «fb_mpt_fail» «fb_nodedb_lookup» «ro_memeq» «ro_mpt_fail» «ro_nodedb_lookup»

/-- The body of `mpt_from_witness` alone (AST line 10459, guard `WorldOK`, loop-free). Its direct callees are
exactly `decode_witness_to_mpt`, `mpt_new` (`«callees_mpt_from_witness»`, checked against the AST). Hypotheses: the bound
of each of these 2 callees, then the contract of each callee at a guard-carrying
call site (0: none). Nothing else is assumed. -/
def GBody.«mpt_from_witness» : Prop :=
  (TerminatingFunBoundedOn WorldOK (ofString "decode_witness_to_mpt") K.«decode_witness_to_mpt») →
  (TerminatingFunBoundedOn GuestInv (ofString "mpt_new") K.«mpt_new») →
  TerminatingFunBoundedOn WorldOK (ofString "mpt_from_witness") K.«mpt_from_witness»

/-- The direct callees of `mpt_from_witness`, read off its AST body (revision 6). -/
theorem «callees_mpt_from_witness» : sameNames (progCallees (fnBody Guest.Software.guestFn_mpt_from_witness))
    ["decode_witness_to_mpt", "mpt_new"] = true := by decide

theorem «lookup_mpt_from_witness» : originalRuntimeCode.lookup (ofString "mpt_from_witness") =
    some ((sourceFunctionEntry Guest.Software.guestFn_mpt_from_witness).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 269 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_from_witness) rfl

/-- PROVED by concrete-body composition (no longer a primitive). -/
theorem «gbody_mpt_from_witness» : GBody.«mpt_from_witness» := by
  intro hd hn
  refine ⟨_, _, _, «lookup_mpt_from_witness», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_mpt_from_witness, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.decCall_on hd _ _ _ (callEntryOn_of_localsFree localsFree_worldOK _ _)
      (decCallResumeOn_guestInv worldOK_guestInv _ _ _)
      (TerminatingProgBoundedOn.tailCall_guestInv hn _)) ?_
  unfold K.«mpt_from_witness»; omega

theorem «gb_mpt_from_witness» : TerminatingFunBoundedOn WorldOK (ofString "mpt_from_witness") K.«mpt_from_witness» :=
  «gbody_mpt_from_witness» «gb_decode_witness_to_mpt» «fb_mpt_new»

/-- The body of `compute_state_root` alone (AST line 32341, guard `WorldOK`, #0 CTR; #1 CTR; #2 CTR; #3 CTR; #4 CTR). Its direct callees are
exactly `alloc`, `cache_get_root`, `encode_account`, `htab_copy`, `htab_get`, `htab_has`, `htab_item`, `htab_new`, `htab_set`, `memcpy`, `mpt_from_witness`, `mpt_root`, `mpt_set`, `rlp_encode_bytes`, `u256_is_zero`, `u256_to_be_min`, `ws_get_account_optional`, `ws_storage_root_of` (`«callees_compute_state_root»`, checked against the AST). Hypotheses: the bound
of each of these 18 callees, then the contract of each callee at a guard-carrying
call site (18: `ww_alloc`, `ww_cache_get_root`, `ww_encode_account`, `ww_htab_copy`, `ro_htab_get`, `ro_htab_has`, `ro_htab_item`, `htab_new_spec`, `htab_set_spec`, `ww_memcpy`, `wk_mpt_from_witness`, `wk_mpt_root`, `wk_mpt_set`, `ww_rlp_encode_bytes`, `ro_u256_is_zero`, `ww_u256_to_be_min`, `ww_ws_get_account_optional`, `ww_ws_storage_root_of`). Nothing else is assumed. -/
def GBody.«compute_state_root» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
  (TerminatingFunBoundedOn GuestInv (ofString "cache_get_root") K.«cache_get_root») →
  (TerminatingFunBoundedOn GuestInv (ofString "encode_account") K.«encode_account») →
  (TerminatingFunBoundedOn GuestInv (ofString "htab_copy") K.«htab_copy») →
  (TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get») →
  (TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.«htab_has») →
  (TerminatingFunBoundedOn GuestInv (ofString "htab_item") K.«htab_item») →
  (TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new») →
  (TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set») →
  (TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy») →
  (TerminatingFunBoundedOn WorldOK (ofString "mpt_from_witness") K.«mpt_from_witness») →
  (TerminatingFunBoundedOn GuestInv (ofString "mpt_root") K.«mpt_root») →
  (TerminatingFunBoundedOn MptObjReady (ofString "mpt_set") K.«mpt_set») →
  (TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.«rlp_encode_bytes») →
  (TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero») →
  (TerminatingFunBoundedOn GuestInv (ofString "u256_to_be_min") K.«u256_to_be_min») →
  (TerminatingFunBoundedOn GuestInv (ofString "ws_get_account_optional") K.«ws_get_account_optional») →
  (TerminatingFunBoundedOn GuestInv (ofString "ws_storage_root_of") K.«ws_storage_root_of») →
  (WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "alloc")) →
  (WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_nib_scratch", 64)])
    ["heap_ptr", "scratch_ptr"] (ofString "cache_get_root")) →
  (WritesWithin (fun s => [(locN s "out", 110), (globN s "mpt_hash_scratch", 40)])
    [] (ofString "encode_account")) →
  (WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "htab_copy")) →
  (ReadOnlyFn (ofString "htab_get")) →
  (ReadOnlyFn (ofString "htab_has")) →
  (ReadOnlyFn (ofString "htab_item")) →
  (type_of% @htab_new_spec) →
  (type_of% @htab_set_spec) →
  (WritesWithin (fun s => [(locN s "dst", locN s "n")])
    [] (ofString "memcpy")) →
  (KeepsOn WorldOK WorldOK (ofString "mpt_from_witness")) →
  (KeepsOn (MptObjAvoids (fun s => [(locN s "out", 32)])) WorldOK (ofString "mpt_root")) →
  (KeepsOn MptObjReady WorldOK (ofString "mpt_set")) →
  (WritesWithin (fun s => [(locN s "dst", locN s "n" + 9)])
    [] (ofString "rlp_encode_bytes")) →
  (ReadOnlyFn (ofString "u256_is_zero")) →
  (WritesWithin (fun s => [(locN s "out", 32)])
    [] (ofString "u256_to_be_min")) →
  (WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_nib_scratch", 64)])
    ["heap_ptr", "scratch_ptr"] (ofString "ws_get_account_optional")) →
  (WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_nib_scratch", 64)])
    ["heap_ptr", "scratch_ptr"] (ofString "ws_storage_root_of")) →
  TerminatingFunBoundedOn WorldOK (ofString "compute_state_root") K.«compute_state_root»

/-- The direct callees of `compute_state_root`, read off its AST body (revision 6). -/
theorem «callees_compute_state_root» : sameNames (progCallees (fnBody Guest.Software.guestFn_compute_state_root))
    ["alloc", "cache_get_root", "encode_account", "htab_copy", "htab_get", "htab_has", "htab_item", "htab_new", "htab_set", "memcpy", "mpt_from_witness", "mpt_root", "mpt_set", "rlp_encode_bytes", "u256_is_zero", "u256_to_be_min", "ws_get_account_optional", "ws_storage_root_of"] = true := by decide

theorem «gbody_compute_state_root» : GBody.«compute_state_root» := by sorry

theorem «gb_compute_state_root» : TerminatingFunBoundedOn WorldOK (ofString "compute_state_root") K.«compute_state_root» :=
  «gbody_compute_state_root» «fb_alloc» «fb_cache_get_root» «fb_encode_account» «fb_htab_copy» «fb_htab_get» «fb_htab_has» «fb_htab_item» «fb_htab_new» «fb_htab_set» «fb_memcpy» «gb_mpt_from_witness» «fb_mpt_root» «gb_mpt_set» «fb_rlp_encode_bytes» «fb_u256_is_zero» «fb_u256_to_be_min» «fb_ws_get_account_optional» «fb_ws_storage_root_of» «ww_alloc» «ww_cache_get_root» «ww_encode_account» «ww_htab_copy» «ro_htab_get» «ro_htab_has» «ro_htab_item» «htab_new_spec» «htab_set_spec» «ww_memcpy» «wk_mpt_from_witness» «wk_mpt_root» «wk_mpt_set» «ww_rlp_encode_bytes» «ro_u256_is_zero» «ww_u256_to_be_min» «ww_ws_get_account_optional» «ww_ws_storage_root_of»

/-- The body of `ws_storage_trie` alone (AST line 13042, guard `WorldOK`, loop-free). Its direct callees are
exactly `decode_witness_to_mpt`, `htab_get`, `htab_set` (`«callees_ws_storage_trie»`, checked against the AST). Hypotheses: the bound
of each of these 3 callees, then the contract of each callee at a guard-carrying
call site (1: `ro_htab_get`). Nothing else is assumed. -/
def GBody.«ws_storage_trie» : Prop :=
  (TerminatingFunBoundedOn WorldOK (ofString "decode_witness_to_mpt") K.«decode_witness_to_mpt») →
  (TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get») →
  (TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set») →
  (ReadOnlyFn (ofString "htab_get")) →
  TerminatingFunBoundedOn WorldOK (ofString "ws_storage_trie") K.«ws_storage_trie»

/-- The direct callees of `ws_storage_trie`, read off its AST body (revision 6). -/
theorem «callees_ws_storage_trie» : sameNames (progCallees (fnBody Guest.Software.guestFn_ws_storage_trie))
    ["decode_witness_to_mpt", "htab_get", "htab_set"] = true := by decide

theorem «lookup_ws_storage_trie» : originalRuntimeCode.lookup (ofString "ws_storage_trie") =
    some ((sourceFunctionEntry Guest.Software.guestFn_ws_storage_trie).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 368 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ws_storage_trie) rfl

/-- PROVED by concrete-body composition (no longer a primitive). -/
theorem «gbody_ws_storage_trie» : GBody.«ws_storage_trie» := by
  intro hdw hget hset hro
  refine ⟨_, _, _, «lookup_ws_storage_trie», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_ws_storage_trie, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (LocalsOnly.of_localsFree localsFree_worldOK) _ (by simp) _ _
      (TerminatingProgBoundedOn.decCall_on hget _ _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _) (ReadOnlyFn.resumeOn (LocalsOnly.of_localsFree localsFree_worldOK) worldOK_guestInv hro _ (by simp) _)
        (TerminatingProgBoundedOn.seq_hoare (TerminatingProgBoundedOn.ite_on (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))
        (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s))) (Hoare.ite_return_skip _ _)
          (TerminatingProgBoundedOn.decCall_on hdw _ _ _ (callEntryOn_of_localsFree localsFree_worldOK _ _)
            (decCallResumeOn_guestInv worldOK_guestInv _ _ _)
            (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hset _ _)
              (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))))))) ?_
  unfold K.«ws_storage_trie»; omega

theorem «gb_ws_storage_trie» : TerminatingFunBoundedOn WorldOK (ofString "ws_storage_trie") K.«ws_storage_trie» :=
  «gbody_ws_storage_trie» «gb_decode_witness_to_mpt» «fb_htab_get» «fb_htab_set» «ro_htab_get»

/-- The body of `ws_get_storage` alone (AST line 13061, guard `WorldOK`, loop-free). Its direct callees are
exactly `alloc`, `heap_mark`, `heap_release`, `keccak256`, `memeq`, `rlp_decode_fully`, `trie_lookup`, `u256_from_be`, `ws_storage_root_of`, `ws_storage_trie` (`«callees_ws_get_storage»`, checked against the AST). Hypotheses: the bound
of each of these 10 callees, then the contract of each callee at a guard-carrying
call site (2: `ro_memeq`, `ww_ws_storage_root_of`). Nothing else is assumed. -/
def GBody.«ws_get_storage» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
  (TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark») →
  (TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release») →
  (TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256») →
  (TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») →
  (TerminatingFunBoundedOn GuestInv (ofString "rlp_decode_fully") K.«rlp_decode_fully») →
  (TerminatingFunBoundedOn GuestInv (ofString "trie_lookup") K.«trie_lookup») →
  (TerminatingFunBoundedOn GuestInv (ofString "u256_from_be") K.«u256_from_be») →
  (TerminatingFunBoundedOn GuestInv (ofString "ws_storage_root_of") K.«ws_storage_root_of») →
  (TerminatingFunBoundedOn WorldOK (ofString "ws_storage_trie") K.«ws_storage_trie») →
  (ReadOnlyFn (ofString "memeq")) →
  (WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_nib_scratch", 64)])
    ["heap_ptr", "scratch_ptr"] (ofString "ws_storage_root_of")) →
  TerminatingFunBoundedOn WorldOK (ofString "ws_get_storage") K.«ws_get_storage»

/-- The direct callees of `ws_get_storage`, read off its AST body (revision 6). -/
theorem «callees_ws_get_storage» : sameNames (progCallees (fnBody Guest.Software.guestFn_ws_get_storage))
    ["alloc", "heap_mark", "heap_release", "keccak256", "memeq", "rlp_decode_fully", "trie_lookup", "u256_from_be", "ws_storage_root_of", "ws_storage_trie"] = true := by decide

theorem «gbody_ws_get_storage» : GBody.«ws_get_storage» := by sorry

theorem «gb_ws_get_storage» : TerminatingFunBoundedOn WorldOK (ofString "ws_get_storage") K.«ws_get_storage» :=
  «gbody_ws_get_storage» «fb_alloc» «fb_heap_mark» «fb_heap_release» «fb_keccak256» «fb_memeq» «fb_rlp_decode_fully» «fb_trie_lookup» «fb_u256_from_be» «fb_ws_storage_root_of» «gb_ws_storage_trie» «ro_memeq» «ww_ws_storage_root_of»

/-- The body of `get_pre_tx_storage` alone (AST line 14069, guard `WorldOK`, loop-free). Its direct callees are
exactly `record_pre_state_read`, `stor_lookup`, `ws_get_storage` (`«callees_get_pre_tx_storage»`, checked against the AST). Hypotheses: the bound
of each of these 3 callees, then the contract of each callee at a guard-carrying
call site (2: `wk_record_pre_state_read`, `ro_stor_lookup`). Nothing else is assumed. -/
def GBody.«get_pre_tx_storage» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "record_pre_state_read") K.«record_pre_state_read») →
  (TerminatingFunBoundedOn GuestInv (ofString "stor_lookup") K.«stor_lookup») →
  (TerminatingFunBoundedOn WorldOK (ofString "ws_get_storage") K.«ws_get_storage») →
  (KeepsOn WorldOK WorldOK (ofString "record_pre_state_read")) →
  (ReadOnlyFn (ofString "stor_lookup")) →
  TerminatingFunBoundedOn WorldOK (ofString "get_pre_tx_storage") K.«get_pre_tx_storage»

/-- The direct callees of `get_pre_tx_storage`, read off its AST body (revision 6). -/
theorem «callees_get_pre_tx_storage» : sameNames (progCallees (fnBody Guest.Software.guestFn_get_pre_tx_storage))
    ["record_pre_state_read", "stor_lookup", "ws_get_storage"] = true := by decide

theorem «lookup_get_pre_tx_storage» : originalRuntimeCode.lookup (ofString "get_pre_tx_storage") =
    some ((sourceFunctionEntry Guest.Software.guestFn_get_pre_tx_storage).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 421 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_get_pre_tx_storage) rfl

/-- PROVED by concrete-body composition (no longer a primitive). -/
theorem «gbody_get_pre_tx_storage» : GBody.«get_pre_tx_storage» := by
  intro hrec hsl hws hk hro
  refine ⟨_, _, _, «lookup_get_pre_tx_storage», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_get_pre_tx_storage, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.decCall_on hsl _ _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _) (ReadOnlyFn.resumeOn (LocalsOnly.of_localsFree localsFree_worldOK) worldOK_guestInv hro _ (by simp) _)
      (TerminatingProgBoundedOn.seq_hoare (TerminatingProgBoundedOn.ite_on (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))
        (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s))) (Hoare.ite_return_skip _ _)
        (TerminatingProgBoundedOn.seq_hoare (TerminatingProgBoundedOn.call_on hrec _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
          (Hoare.call_keeps localsFree_worldOK hk _)
          (TerminatingProgBoundedOn.decCall_on hws _ _ _ (callEntryOn_of_localsFree localsFree_worldOK _ _)
            (decCallResumeOn_guestInv worldOK_guestInv _ _ _) (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))) ?_
  unfold K.«get_pre_tx_storage»; omega

theorem «gb_get_pre_tx_storage» : TerminatingFunBoundedOn WorldOK (ofString "get_pre_tx_storage") K.«get_pre_tx_storage» :=
  «gbody_get_pre_tx_storage» «fb_record_pre_state_read» «fb_stor_lookup» «gb_ws_get_storage» «wk_record_pre_state_read» «ro_stor_lookup»

/-- The body of `idx_start_storage` alone (AST line 14129, guard `WorldOK`, loop-free). Its direct callees are
exactly `alloc`, `get_pre_tx_storage`, `htab_get`, `htab_set`, `memcpy`, `st_le64` (`«callees_idx_start_storage»`, checked against the AST). Hypotheses: the bound
of each of these 6 callees, then the contract of each callee at a guard-carrying
call site (3: `ro_htab_get`, `ww_memcpy`, `ww_st_le64`). Nothing else is assumed. -/
def GBody.«idx_start_storage» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
  (TerminatingFunBoundedOn WorldOK (ofString "get_pre_tx_storage") K.«get_pre_tx_storage») →
  (TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get») →
  (TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set») →
  (TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy») →
  (TerminatingFunBoundedOn GuestInv (ofString "st_le64") K.«st_le64») →
  (ReadOnlyFn (ofString "htab_get")) →
  (WritesWithin (fun s => [(locN s "dst", locN s "n")])
    [] (ofString "memcpy")) →
  (WritesWithin (fun s => [(locN s "p", 8)])
    [] (ofString "st_le64")) →
  TerminatingFunBoundedOn WorldOK (ofString "idx_start_storage") K.«idx_start_storage»

/-- The direct callees of `idx_start_storage`, read off its AST body (revision 6). -/
theorem «callees_idx_start_storage» : sameNames (progCallees (fnBody Guest.Software.guestFn_idx_start_storage))
    ["alloc", "get_pre_tx_storage", "htab_get", "htab_set", "memcpy", "st_le64"] = true := by decide

theorem «gbody_idx_start_storage» : GBody.«idx_start_storage» := by sorry

theorem «gb_idx_start_storage» : TerminatingFunBoundedOn WorldOK (ofString "idx_start_storage") K.«idx_start_storage» :=
  «gbody_idx_start_storage» «fb_alloc» «gb_get_pre_tx_storage» «fb_htab_get» «fb_htab_set» «fb_memcpy» «fb_st_le64» «ro_htab_get» «ww_memcpy» «ww_st_le64»

/-- The body of `update_builder_from_tx` alone (AST line 14233, guard `WorldOK`, #0 CTR; #1 CTR; #2 CTR). Its direct callees are
exactly `add_balance_change`, `add_code_change`, `add_nonce_change`, `add_storage_write`, `bal_remove_change`, `get_code`, `htab_item`, `idx_start_account`, `idx_start_storage`, `memeq`, `remove_storage_write`, `u256_eq` (`«callees_update_builder_from_tx»`, checked against the AST). Hypotheses: the bound
of each of these 12 callees, then the contract of each callee at a guard-carrying
call site (12: `wk_add_balance_change`, `wk_add_code_change`, `wk_add_nonce_change`, `wk_add_storage_write`, `wk_bal_remove_change`, `wk_get_code`, `ro_htab_item`, `wk_idx_start_account`, `wk_idx_start_storage`, `ro_memeq`, `wk_remove_storage_write`, `ro_u256_eq`). Nothing else is assumed. -/
def GBody.«update_builder_from_tx» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "add_balance_change") K.«add_balance_change») →
  (TerminatingFunBoundedOn GuestInv (ofString "add_code_change") K.«add_code_change») →
  (TerminatingFunBoundedOn GuestInv (ofString "add_nonce_change") K.«add_nonce_change») →
  (TerminatingFunBoundedOn GuestInv (ofString "add_storage_write") K.«add_storage_write») →
  (TerminatingFunBoundedOn GuestInv (ofString "bal_remove_change") K.«bal_remove_change») →
  (TerminatingFunBoundedOn GuestInv (ofString "get_code") K.«get_code») →
  (TerminatingFunBoundedOn GuestInv (ofString "htab_item") K.«htab_item») →
  (TerminatingFunBoundedOn GuestInv (ofString "idx_start_account") K.«idx_start_account») →
  (TerminatingFunBoundedOn WorldOK (ofString "idx_start_storage") K.«idx_start_storage») →
  (TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») →
  (TerminatingFunBoundedOn GuestInv (ofString "remove_storage_write") K.«remove_storage_write») →
  (TerminatingFunBoundedOn GuestInv (ofString "u256_eq") K.«u256_eq») →
  (KeepsOn WorldOK WorldOK (ofString "add_balance_change")) →
  (KeepsOn WorldOK WorldOK (ofString "add_code_change")) →
  (KeepsOn WorldOK WorldOK (ofString "add_nonce_change")) →
  (KeepsOn WorldOK WorldOK (ofString "add_storage_write")) →
  (KeepsOn WorldOK WorldOK (ofString "bal_remove_change")) →
  (KeepsOn WorldOK WorldOK (ofString "get_code")) →
  (ReadOnlyFn (ofString "htab_item")) →
  (KeepsOn WorldOK WorldOK (ofString "idx_start_account")) →
  (KeepsOn WorldOK WorldOK (ofString "idx_start_storage")) →
  (ReadOnlyFn (ofString "memeq")) →
  (KeepsOn WorldOK WorldOK (ofString "remove_storage_write")) →
  (ReadOnlyFn (ofString "u256_eq")) →
  TerminatingFunBoundedOn WorldOK (ofString "update_builder_from_tx") K.«update_builder_from_tx»

/-- The direct callees of `update_builder_from_tx`, read off its AST body (revision 6). -/
theorem «callees_update_builder_from_tx» : sameNames (progCallees (fnBody Guest.Software.guestFn_update_builder_from_tx))
    ["add_balance_change", "add_code_change", "add_nonce_change", "add_storage_write", "bal_remove_change", "get_code", "htab_item", "idx_start_account", "idx_start_storage", "memeq", "remove_storage_write", "u256_eq"] = true := by decide

theorem «gbody_update_builder_from_tx» : GBody.«update_builder_from_tx» := by sorry

theorem «gb_update_builder_from_tx» : TerminatingFunBoundedOn WorldOK (ofString "update_builder_from_tx") K.«update_builder_from_tx» :=
  «gbody_update_builder_from_tx» «fb_add_balance_change» «fb_add_code_change» «fb_add_nonce_change» «fb_add_storage_write» «fb_bal_remove_change» «fb_get_code» «fb_htab_item» «fb_idx_start_account» «gb_idx_start_storage» «fb_memeq» «fb_remove_storage_write» «fb_u256_eq» «wk_add_balance_change» «wk_add_code_change» «wk_add_nonce_change» «wk_add_storage_write» «wk_bal_remove_change» «wk_get_code» «ro_htab_item» «wk_idx_start_account» «wk_idx_start_storage» «ro_memeq» «wk_remove_storage_write» «ro_u256_eq»

/-- The body of `incorporate_tx_into_block` alone (AST line 14313, guard `WorldOK`, loop-free). Its direct callees are
exactly `merge_tx_into_block`, `update_builder_from_tx` (`«callees_incorporate_tx_into_block»`, checked against the AST). Hypotheses: the bound
of each of these 2 callees, then the contract of each callee at a guard-carrying
call site (0: none). Nothing else is assumed. -/
def GBody.«incorporate_tx_into_block» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "merge_tx_into_block") K.«merge_tx_into_block») →
  (TerminatingFunBoundedOn WorldOK (ofString "update_builder_from_tx") K.«update_builder_from_tx») →
  TerminatingFunBoundedOn WorldOK (ofString "incorporate_tx_into_block") K.«incorporate_tx_into_block»

/-- The direct callees of `incorporate_tx_into_block`, read off its AST body (revision 6). -/
theorem «callees_incorporate_tx_into_block» : sameNames (progCallees (fnBody Guest.Software.guestFn_incorporate_tx_into_block))
    ["merge_tx_into_block", "update_builder_from_tx"] = true := by decide

theorem «lookup_incorporate_tx_into_block» : originalRuntimeCode.lookup (ofString "incorporate_tx_into_block") =
    some ((sourceFunctionEntry Guest.Software.guestFn_incorporate_tx_into_block).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 428 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_incorporate_tx_into_block) rfl

/-- PROVED by concrete-body composition (no longer a primitive). -/
theorem «gbody_incorporate_tx_into_block» : GBody.«incorporate_tx_into_block» := by
  intro hm hu
  refine ⟨_, _, _, «lookup_incorporate_tx_into_block», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_incorporate_tx_into_block, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.seq_guestInv_after
      (TerminatingProgBoundedOn.call_on hu _ _ (callEntryOn_of_localsFree localsFree_worldOK _ _)) worldOK_guestInv
      (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hm _ _) (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«incorporate_tx_into_block»; omega

theorem «gb_incorporate_tx_into_block» : TerminatingFunBoundedOn WorldOK (ofString "incorporate_tx_into_block") K.«incorporate_tx_into_block» :=
  «gbody_incorporate_tx_into_block» «fb_merge_tx_into_block» «gb_update_builder_from_tx»

/-- The body of `htab_truncate` alone (AST line 5278, guard `HtabArgWF`, #0 WF). Its direct callees are
exactly `htab_del` (`«callees_htab_truncate»`, checked against the AST). Hypotheses: the bound
of each of these 1 callees, then the contract of each callee at a guard-carrying
call site (2: `htab_del_spec`, `htab_del_progress_spec`). Nothing else is assumed. -/
def GBody.«htab_truncate» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "htab_del") K.«htab_del») →
  (type_of% @htab_del_spec) →
  (type_of% @htab_del_progress_spec) →
  TerminatingFunBoundedOn HtabArgWF (ofString "htab_truncate") K.«htab_truncate»

/-- The direct callees of `htab_truncate`, read off its AST body (revision 6). -/
theorem «callees_htab_truncate» : sameNames (progCallees (fnBody Guest.Software.guestFn_htab_truncate))
    ["htab_del"] = true := by decide

theorem «gbody_htab_truncate» : GBody.«htab_truncate» := by sorry

theorem «gb_htab_truncate» : TerminatingFunBoundedOn HtabArgWF (ofString "htab_truncate") K.«htab_truncate» :=
  «gbody_htab_truncate» «fb_htab_del» «htab_del_spec» «htab_del_progress_spec»

/-- The body of `rollback_child_access` alone (AST line 18995, guard `RollbackReady`, loop-free). Its direct callees are
exactly `htab_truncate` (`«callees_rollback_child_access»`, checked against the AST). Hypotheses: the bound
of each of these 1 callees, then the contract of each callee at a guard-carrying
call site (1: `htab_truncate_spec`). Nothing else is assumed. -/
def GBody.«rollback_child_access» : Prop :=
  (TerminatingFunBoundedOn HtabArgWF (ofString "htab_truncate") K.«htab_truncate») →
  (type_of% @htab_truncate_spec) →
  TerminatingFunBoundedOn RollbackReady (ofString "rollback_child_access") K.«rollback_child_access»

/-- The direct callees of `rollback_child_access`, read off its AST body (revision 6). -/
theorem «callees_rollback_child_access» : sameNames (progCallees (fnBody Guest.Software.guestFn_rollback_child_access))
    ["htab_truncate"] = true := by decide

theorem «gbody_rollback_child_access» : GBody.«rollback_child_access» := by sorry

theorem «gb_rollback_child_access» : TerminatingFunBoundedOn RollbackReady (ofString "rollback_child_access") K.«rollback_child_access» :=
  «gbody_rollback_child_access» «gb_htab_truncate» «htab_truncate_spec»

/-- The body of `finish_child` alone (AST line 18572, guard `FinishReady`, loop-free). Its direct callees are
exactly `address_to_u256`, `create_finish`, `credit_state_gas_refund`, `frame_halt`, `frame_mem_release`, `incorporate_child_on_error`, `incorporate_child_on_success`, `memcpy`, `min`, `pc_add`, `refill_frame_state_gas`, `rollback_child_access`, `scratch_release`, `set_retdata`, `stack_push`, `state_restore` (`«callees_finish_child»`, checked against the AST). Hypotheses: the bound
of each of these 16 callees, then the contract of each callee at a guard-carrying
call site (4: `ek_create_finish`, `ek_frame_halt`, `ek_refill_frame_state_gas`, `ek_state_restore`). Nothing else is assumed. -/
def GBody.«finish_child» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "address_to_u256") K.«address_to_u256») →
  (TerminatingFunBoundedOn GuestInv (ofString "create_finish") K.«create_finish») →
  (TerminatingFunBoundedOn GuestInv (ofString "credit_state_gas_refund") K.«credit_state_gas_refund») →
  (TerminatingFunBoundedOn GuestInv (ofString "frame_halt") K.«frame_halt») →
  (TerminatingFunBoundedOn GuestInv (ofString "frame_mem_release") K.«frame_mem_release») →
  (TerminatingFunBoundedOn GuestInv (ofString "incorporate_child_on_error") K.«incorporate_child_on_error») →
  (TerminatingFunBoundedOn GuestInv (ofString "incorporate_child_on_success") K.«incorporate_child_on_success») →
  (TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy») →
  (TerminatingFunBoundedOn GuestInv (ofString "min") K.«min») →
  (TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») →
  (TerminatingFunBoundedOn GuestInv (ofString "refill_frame_state_gas") K.«refill_frame_state_gas») →
  (TerminatingFunBoundedOn RollbackReady (ofString "rollback_child_access") K.«rollback_child_access») →
  (TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release») →
  (TerminatingFunBoundedOn GuestInv (ofString "set_retdata") K.«set_retdata») →
  (TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push») →
  (TerminatingFunBoundedOn GuestInv (ofString "state_restore") K.«state_restore») →
  (KeepsOn EvmInv EvmInv (ofString "create_finish")) →
  (KeepsOn EvmInv EvmInv (ofString "frame_halt")) →
  (KeepsOn EvmInv EvmInv (ofString "refill_frame_state_gas")) →
  (KeepsOn EvmInv EvmInv (ofString "state_restore")) →
  TerminatingFunBoundedOn FinishReady (ofString "finish_child") K.«finish_child»

/-- The direct callees of `finish_child`, read off its AST body (revision 6). -/
theorem «callees_finish_child» : sameNames (progCallees (fnBody Guest.Software.guestFn_finish_child))
    ["address_to_u256", "create_finish", "credit_state_gas_refund", "frame_halt", "frame_mem_release", "incorporate_child_on_error", "incorporate_child_on_success", "memcpy", "min", "pc_add", "refill_frame_state_gas", "rollback_child_access", "scratch_release", "set_retdata", "stack_push", "state_restore"] = true := by decide

theorem «gbody_finish_child» : GBody.«finish_child» := by sorry

theorem «gb_finish_child» : TerminatingFunBoundedOn FinishReady (ofString "finish_child") K.«finish_child» :=
  «gbody_finish_child» «fb_address_to_u256» «fb_create_finish» «fb_credit_state_gas_refund» «fb_frame_halt» «fb_frame_mem_release» «fb_incorporate_child_on_error» «fb_incorporate_child_on_success» «fb_memcpy» «fb_min» «fb_pc_add» «fb_refill_frame_state_gas» «gb_rollback_child_access» «fb_scratch_release» «fb_set_retdata» «fb_stack_push» «fb_state_restore» «ek_create_finish» «ek_frame_halt» «ek_refill_frame_state_gas» «ek_state_restore»

/-- The body of `get_storage` alone (AST line 13249, guard `WorldOK`, loop-free). Its direct callees are
exactly `htab_set`, `record_pre_state_read`, `sk_make`, `stor_lookup`, `ws_get_storage` (`«callees_get_storage»`, checked against the AST). Hypotheses: the bound
of each of these 5 callees, then the contract of each callee at a guard-carrying
call site (4: `htab_set_spec`, `wk_record_pre_state_read`, `ww_sk_make`, `ro_stor_lookup`). Nothing else is assumed. -/
def GBody.«get_storage» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set») →
  (TerminatingFunBoundedOn GuestInv (ofString "record_pre_state_read") K.«record_pre_state_read») →
  (TerminatingFunBoundedOn GuestInv (ofString "sk_make") K.«sk_make») →
  (TerminatingFunBoundedOn GuestInv (ofString "stor_lookup") K.«stor_lookup») →
  (TerminatingFunBoundedOn WorldOK (ofString "ws_get_storage") K.«ws_get_storage») →
  (type_of% @htab_set_spec) →
  (KeepsOn WorldOK WorldOK (ofString "record_pre_state_read")) →
  (WritesWithin (fun s => [(globN s "sk_buf", 64)])
    [] (ofString "sk_make")) →
  (ReadOnlyFn (ofString "stor_lookup")) →
  TerminatingFunBoundedOn WorldOK (ofString "get_storage") K.«get_storage»

/-- The direct callees of `get_storage`, read off its AST body (revision 6). -/
theorem «callees_get_storage» : sameNames (progCallees (fnBody Guest.Software.guestFn_get_storage))
    ["htab_set", "record_pre_state_read", "sk_make", "stor_lookup", "ws_get_storage"] = true := by decide

theorem «gbody_get_storage» : GBody.«get_storage» := by sorry

theorem «gb_get_storage» : TerminatingFunBoundedOn WorldOK (ofString "get_storage") K.«get_storage» :=
  «gbody_get_storage» «fb_htab_set» «fb_record_pre_state_read» «fb_sk_make» «fb_stor_lookup» «gb_ws_get_storage» «htab_set_spec» «wk_record_pre_state_read» «ww_sk_make» «ro_stor_lookup»

/-- The body of `op_sload` alone (AST line 16584, guard `EvmRun`, loop-free). Its direct callees are
exactly `charge_gas`, `get_storage`, `is_warm_storage_key`, `pc_add`, `stack_pop`, `stack_push`, `u256_to_be32`, `warm_storage_key` (`«callees_op_sload»`, checked against the AST). Hypotheses: the bound
of each of these 8 callees, then the contract of each callee at a guard-carrying
call site (5: `ek_charge_gas`, `ww_is_warm_storage_key`, `ek_stack_pop`, `ww_u256_to_be32`, `ek_warm_storage_key`). Nothing else is assumed. -/
def GBody.«op_sload» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas») →
  (TerminatingFunBoundedOn WorldOK (ofString "get_storage") K.«get_storage») →
  (TerminatingFunBoundedOn GuestInv (ofString "is_warm_storage_key") K.«is_warm_storage_key») →
  (TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») →
  (TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop») →
  (TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push») →
  (TerminatingFunBoundedOn GuestInv (ofString "u256_to_be32") K.«u256_to_be32») →
  (TerminatingFunBoundedOn GuestInv (ofString "warm_storage_key") K.«warm_storage_key») →
  (KeepsOn EvmInv EvmInv (ofString "charge_gas")) →
  (WritesWithin (fun s => [(globN s "sk_buf", 64)])
    [] (ofString "is_warm_storage_key")) →
  (KeepsOn EvmInv EvmInv (ofString "stack_pop")) →
  (WritesWithin (fun s => [(locN s "out", 32)])
    [] (ofString "u256_to_be32")) →
  (KeepsOn EvmInv EvmInv (ofString "warm_storage_key")) →
  TerminatingFunBoundedOn EvmRun (ofString "op_sload") K.«op_sload»

/-- The direct callees of `op_sload`, read off its AST body (revision 6). -/
theorem «callees_op_sload» : sameNames (progCallees (fnBody Guest.Software.guestFn_op_sload))
    ["charge_gas", "get_storage", "is_warm_storage_key", "pc_add", "stack_pop", "stack_push", "u256_to_be32", "warm_storage_key"] = true := by decide

theorem «gbody_op_sload» : GBody.«op_sload» := by sorry

theorem «gb_op_sload» : TerminatingFunBoundedOn EvmRun (ofString "op_sload") K.«op_sload» :=
  «gbody_op_sload» «fb_charge_gas» «gb_get_storage» «fb_is_warm_storage_key» «fb_pc_add» «fb_stack_pop» «fb_stack_push» «fb_u256_to_be32» «fb_warm_storage_key» «ek_charge_gas» «ww_is_warm_storage_key» «ek_stack_pop» «ww_u256_to_be32» «ek_warm_storage_key»

/-- The body of `get_storage_original` alone (AST line 13276, guard `WorldOK`, loop-free). Its direct callees are
exactly `htab_has`, `record_pre_state_read`, `stor_lookup`, `ws_get_storage` (`«callees_get_storage_original»`, checked against the AST). Hypotheses: the bound
of each of these 4 callees, then the contract of each callee at a guard-carrying
call site (3: `ro_htab_has`, `wk_record_pre_state_read`, `ro_stor_lookup`). Nothing else is assumed. -/
def GBody.«get_storage_original» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.«htab_has») →
  (TerminatingFunBoundedOn GuestInv (ofString "record_pre_state_read") K.«record_pre_state_read») →
  (TerminatingFunBoundedOn GuestInv (ofString "stor_lookup") K.«stor_lookup») →
  (TerminatingFunBoundedOn WorldOK (ofString "ws_get_storage") K.«ws_get_storage») →
  (ReadOnlyFn (ofString "htab_has")) →
  (KeepsOn WorldOK WorldOK (ofString "record_pre_state_read")) →
  (ReadOnlyFn (ofString "stor_lookup")) →
  TerminatingFunBoundedOn WorldOK (ofString "get_storage_original") K.«get_storage_original»

/-- The direct callees of `get_storage_original`, read off its AST body (revision 6). -/
theorem «callees_get_storage_original» : sameNames (progCallees (fnBody Guest.Software.guestFn_get_storage_original))
    ["htab_has", "record_pre_state_read", "stor_lookup", "ws_get_storage"] = true := by decide

theorem «lookup_get_storage_original» : originalRuntimeCode.lookup (ofString "get_storage_original") =
    some ((sourceFunctionEntry Guest.Software.guestFn_get_storage_original).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 379 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_get_storage_original) rfl

/-- PROVED by concrete-body composition (no longer a primitive). -/
theorem «gbody_get_storage_original» : GBody.«get_storage_original» := by
  intro hhas hrec hsl hws hrh hk hrs
  refine ⟨_, _, _, «lookup_get_storage_original», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_get_storage_original, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.decCall_on hhas _ _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _) (ReadOnlyFn.resumeOn (LocalsOnly.of_localsFree localsFree_worldOK) worldOK_guestInv hrh _ (by simp) _)
      (TerminatingProgBoundedOn.seq_hoare (TerminatingProgBoundedOn.ite_on (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))
        (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s))) (Hoare.ite_return_skip _ _)
        (TerminatingProgBoundedOn.decCall_on hsl _ _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _) (ReadOnlyFn.resumeOn (LocalsOnly.of_localsFree localsFree_worldOK) worldOK_guestInv hrs _ (by simp) _)
          (TerminatingProgBoundedOn.seq_hoare (TerminatingProgBoundedOn.ite_on (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))
        (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s))) (Hoare.ite_return_skip _ _)
            (TerminatingProgBoundedOn.seq_hoare (TerminatingProgBoundedOn.call_on hrec _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
              (Hoare.call_keeps localsFree_worldOK hk _)
              (TerminatingProgBoundedOn.decCall_on hws _ _ _ (callEntryOn_of_localsFree localsFree_worldOK _ _)
                (decCallResumeOn_guestInv worldOK_guestInv _ _ _) (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))))) ?_
  unfold K.«get_storage_original»; omega

theorem «gb_get_storage_original» : TerminatingFunBoundedOn WorldOK (ofString "get_storage_original") K.«get_storage_original» :=
  «gbody_get_storage_original» «fb_htab_has» «fb_record_pre_state_read» «fb_stor_lookup» «gb_ws_get_storage» «ro_htab_has» «wk_record_pre_state_read» «ro_stor_lookup»

/-- The body of `op_sstore` alone (AST line 16611, guard `EvmRun`, loop-free). Its direct callees are
exactly `charge_gas`, `charge_state_gas`, `check_gas`, `credit_state_gas_refund`, `get_storage`, `get_storage_original`, `is_warm_storage_key`, `max`, `pc_add`, `require_not_static`, `set_storage`, `stack_pop`, `u256_eq`, `u256_is_zero`, `u256_to_be32`, `warm_storage_key` (`«callees_op_sstore»`, checked against the AST). Hypotheses: the bound
of each of these 16 callees, then the contract of each callee at a guard-carrying
call site (9: `ek_charge_gas`, `ro_check_gas`, `ek_get_storage_original`, `ww_is_warm_storage_key`, `ro_max`, `ro_require_not_static`, `ek_stack_pop`, `ww_u256_to_be32`, `ek_warm_storage_key`). Nothing else is assumed. -/
def GBody.«op_sstore» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas») →
  (TerminatingFunBoundedOn GuestInv (ofString "charge_state_gas") K.«charge_state_gas») →
  (TerminatingFunBoundedOn GuestInv (ofString "check_gas") K.«check_gas») →
  (TerminatingFunBoundedOn GuestInv (ofString "credit_state_gas_refund") K.«credit_state_gas_refund») →
  (TerminatingFunBoundedOn WorldOK (ofString "get_storage") K.«get_storage») →
  (TerminatingFunBoundedOn WorldOK (ofString "get_storage_original") K.«get_storage_original») →
  (TerminatingFunBoundedOn GuestInv (ofString "is_warm_storage_key") K.«is_warm_storage_key») →
  (TerminatingFunBoundedOn GuestInv (ofString "max") K.«max») →
  (TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») →
  (TerminatingFunBoundedOn GuestInv (ofString "require_not_static") K.«require_not_static») →
  (TerminatingFunBoundedOn GuestInv (ofString "set_storage") K.«set_storage») →
  (TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop») →
  (TerminatingFunBoundedOn GuestInv (ofString "u256_eq") K.«u256_eq») →
  (TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero») →
  (TerminatingFunBoundedOn GuestInv (ofString "u256_to_be32") K.«u256_to_be32») →
  (TerminatingFunBoundedOn GuestInv (ofString "warm_storage_key") K.«warm_storage_key») →
  (KeepsOn EvmInv EvmInv (ofString "charge_gas")) →
  (ReadOnlyFn (ofString "check_gas")) →
  (KeepsOn EvmInv EvmInv (ofString "get_storage_original")) →
  (WritesWithin (fun s => [(globN s "sk_buf", 64)])
    [] (ofString "is_warm_storage_key")) →
  (ReadOnlyFn (ofString "max")) →
  (ReadOnlyFn (ofString "require_not_static")) →
  (KeepsOn EvmInv EvmInv (ofString "stack_pop")) →
  (WritesWithin (fun s => [(locN s "out", 32)])
    [] (ofString "u256_to_be32")) →
  (KeepsOn EvmInv EvmInv (ofString "warm_storage_key")) →
  TerminatingFunBoundedOn EvmRun (ofString "op_sstore") K.«op_sstore»

/-- The direct callees of `op_sstore`, read off its AST body (revision 6). -/
theorem «callees_op_sstore» : sameNames (progCallees (fnBody Guest.Software.guestFn_op_sstore))
    ["charge_gas", "charge_state_gas", "check_gas", "credit_state_gas_refund", "get_storage", "get_storage_original", "is_warm_storage_key", "max", "pc_add", "require_not_static", "set_storage", "stack_pop", "u256_eq", "u256_is_zero", "u256_to_be32", "warm_storage_key"] = true := by decide

theorem «gbody_op_sstore» : GBody.«op_sstore» := by sorry

theorem «gb_op_sstore» : TerminatingFunBoundedOn EvmRun (ofString "op_sstore") K.«op_sstore» :=
  «gbody_op_sstore» «fb_charge_gas» «fb_charge_state_gas» «fb_check_gas» «fb_credit_state_gas_refund» «gb_get_storage» «gb_get_storage_original» «fb_is_warm_storage_key» «fb_max» «fb_pc_add» «fb_require_not_static» «fb_set_storage» «fb_stack_pop» «fb_u256_eq» «fb_u256_is_zero» «fb_u256_to_be32» «fb_warm_storage_key» «ek_charge_gas» «ro_check_gas» «ek_get_storage_original» «ww_is_warm_storage_key» «ro_max» «ro_require_not_static» «ek_stack_pop» «ww_u256_to_be32» «ek_warm_storage_key»

/-- The body of `op_dispatch` alone (AST line 17902, guard `EvmRun`, loop-free). Its direct callees are
exactly `op_add`, `op_addmod`, `op_address`, `op_and`, `op_balance`, `op_basefee`, `op_blobbasefee`, `op_blobhash`, `op_blockhash`, `op_byte`, `op_call`, `op_callcode`, `op_calldatacopy`, `op_calldataload`, `op_calldatasize`, `op_caller`, `op_callvalue`, `op_chainid`, `op_clz`, `op_codecopy`, `op_codesize`, `op_coinbase`, `op_create`, `op_create2`, `op_delegatecall`, `op_div`, `op_dup`, `op_dupn`, `op_eq`, `op_exchange`, `op_exp`, `op_extcodecopy`, `op_extcodehash`, `op_extcodesize`, `op_gas`, `op_gaslimit`, `op_gasprice`, `op_gt`, `op_iszero`, `op_jump`, `op_jumpdest`, `op_jumpi`, `op_keccak`, `op_log`, `op_lt`, `op_mcopy`, `op_mload`, `op_mod`, `op_msize`, `op_mstore`, `op_mstore8`, `op_mul`, `op_mulmod`, `op_not`, `op_number`, `op_or`, `op_origin`, `op_pc`, `op_pop`, `op_prevrandao`, `op_push`, `op_return`, `op_returndatacopy`, `op_returndatasize`, `op_revert`, `op_sar`, `op_sdiv`, `op_selfbalance`, `op_selfdestruct`, `op_sgt`, `op_shl`, `op_shr`, `op_signextend`, `op_sload`, `op_slotnum`, `op_slt`, `op_smod`, `op_sstore`, `op_staticcall`, `op_stop`, `op_sub`, `op_swap`, `op_swapn`, `op_timestamp`, `op_tload`, `op_tstore`, `op_xor` (`«callees_op_dispatch»`, checked against the AST). Hypotheses: the bound
of each of these 87 callees, then the contract of each callee at a guard-carrying
call site (0: none). Nothing else is assumed. -/
def GBody.«op_dispatch» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "op_add") K.«op_add») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_addmod") K.«op_addmod») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_address") K.«op_address») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_and") K.«op_and») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_balance") K.«op_balance») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_basefee") K.«op_basefee») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_blobbasefee") K.«op_blobbasefee») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_blobhash") K.«op_blobhash») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_blockhash") K.«op_blockhash») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_byte") K.«op_byte») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_call") K.«op_call») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_callcode") K.«op_callcode») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_calldatacopy") K.«op_calldatacopy») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_calldataload") K.«op_calldataload») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_calldatasize") K.«op_calldatasize») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_caller") K.«op_caller») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_callvalue") K.«op_callvalue») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_chainid") K.«op_chainid») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_clz") K.«op_clz») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_codecopy") K.«op_codecopy») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_codesize") K.«op_codesize») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_coinbase") K.«op_coinbase») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_create") K.«op_create») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_create2") K.«op_create2») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_delegatecall") K.«op_delegatecall») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_div") K.«op_div») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_dup") K.«op_dup») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_dupn") K.«op_dupn») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_eq") K.«op_eq») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_exchange") K.«op_exchange») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_exp") K.«op_exp») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_extcodecopy") K.«op_extcodecopy») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_extcodehash") K.«op_extcodehash») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_extcodesize") K.«op_extcodesize») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_gas") K.«op_gas») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_gaslimit") K.«op_gaslimit») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_gasprice") K.«op_gasprice») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_gt") K.«op_gt») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_iszero") K.«op_iszero») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_jump") K.«op_jump») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_jumpdest") K.«op_jumpdest») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_jumpi") K.«op_jumpi») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_keccak") K.«op_keccak») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_log") K.«op_log») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_lt") K.«op_lt») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mcopy") K.«op_mcopy») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mload") K.«op_mload») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mod") K.«op_mod») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_msize") K.«op_msize») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mstore") K.«op_mstore») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mstore8") K.«op_mstore8») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mul") K.«op_mul») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mulmod") K.«op_mulmod») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_not") K.«op_not») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_number") K.«op_number») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_or") K.«op_or») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_origin") K.«op_origin») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_pc") K.«op_pc») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_pop") K.«op_pop») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_prevrandao") K.«op_prevrandao») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_push") K.«op_push») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_return") K.«op_return») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_returndatacopy") K.«op_returndatacopy») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_returndatasize") K.«op_returndatasize») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_revert") K.«op_revert») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_sar") K.«op_sar») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_sdiv") K.«op_sdiv») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_selfbalance") K.«op_selfbalance») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_selfdestruct") K.«op_selfdestruct») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_sgt") K.«op_sgt») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_shl") K.«op_shl») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_shr") K.«op_shr») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_signextend") K.«op_signextend») →
  (TerminatingFunBoundedOn EvmRun (ofString "op_sload") K.«op_sload») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_slotnum") K.«op_slotnum») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_slt") K.«op_slt») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_smod") K.«op_smod») →
  (TerminatingFunBoundedOn EvmRun (ofString "op_sstore") K.«op_sstore») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_staticcall") K.«op_staticcall») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_stop") K.«op_stop») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_sub") K.«op_sub») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_swap") K.«op_swap») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_swapn") K.«op_swapn») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_timestamp") K.«op_timestamp») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_tload") K.«op_tload») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_tstore") K.«op_tstore») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_xor") K.«op_xor») →
  TerminatingFunBoundedOn EvmRun (ofString "op_dispatch") K.«op_dispatch»

/-- The direct callees of `op_dispatch`, read off its AST body (revision 6). -/
theorem «callees_op_dispatch» : sameNames (progCallees (fnBody Guest.Software.guestFn_op_dispatch))
    ["op_add", "op_addmod", "op_address", "op_and", "op_balance", "op_basefee", "op_blobbasefee", "op_blobhash", "op_blockhash", "op_byte", "op_call", "op_callcode", "op_calldatacopy", "op_calldataload", "op_calldatasize", "op_caller", "op_callvalue", "op_chainid", "op_clz", "op_codecopy", "op_codesize", "op_coinbase", "op_create", "op_create2", "op_delegatecall", "op_div", "op_dup", "op_dupn", "op_eq", "op_exchange", "op_exp", "op_extcodecopy", "op_extcodehash", "op_extcodesize", "op_gas", "op_gaslimit", "op_gasprice", "op_gt", "op_iszero", "op_jump", "op_jumpdest", "op_jumpi", "op_keccak", "op_log", "op_lt", "op_mcopy", "op_mload", "op_mod", "op_msize", "op_mstore", "op_mstore8", "op_mul", "op_mulmod", "op_not", "op_number", "op_or", "op_origin", "op_pc", "op_pop", "op_prevrandao", "op_push", "op_return", "op_returndatacopy", "op_returndatasize", "op_revert", "op_sar", "op_sdiv", "op_selfbalance", "op_selfdestruct", "op_sgt", "op_shl", "op_shr", "op_signextend", "op_sload", "op_slotnum", "op_slt", "op_smod", "op_sstore", "op_staticcall", "op_stop", "op_sub", "op_swap", "op_swapn", "op_timestamp", "op_tload", "op_tstore", "op_xor"] = true := by decide

theorem «gbody_op_dispatch» : GBody.«op_dispatch» := by sorry

theorem «gb_op_dispatch» : TerminatingFunBoundedOn EvmRun (ofString "op_dispatch") K.«op_dispatch» :=
  «gbody_op_dispatch» «fb_op_add» «fb_op_addmod» «fb_op_address» «fb_op_and» «fb_op_balance» «fb_op_basefee» «fb_op_blobbasefee» «fb_op_blobhash» «fb_op_blockhash» «fb_op_byte» «fb_op_call» «fb_op_callcode» «fb_op_calldatacopy» «fb_op_calldataload» «fb_op_calldatasize» «fb_op_caller» «fb_op_callvalue» «fb_op_chainid» «fb_op_clz» «fb_op_codecopy» «fb_op_codesize» «fb_op_coinbase» «fb_op_create» «fb_op_create2» «fb_op_delegatecall» «fb_op_div» «fb_op_dup» «fb_op_dupn» «fb_op_eq» «fb_op_exchange» «fb_op_exp» «fb_op_extcodecopy» «fb_op_extcodehash» «fb_op_extcodesize» «fb_op_gas» «fb_op_gaslimit» «fb_op_gasprice» «fb_op_gt» «fb_op_iszero» «fb_op_jump» «fb_op_jumpdest» «fb_op_jumpi» «fb_op_keccak» «fb_op_log» «fb_op_lt» «fb_op_mcopy» «fb_op_mload» «fb_op_mod» «fb_op_msize» «fb_op_mstore» «fb_op_mstore8» «fb_op_mul» «fb_op_mulmod» «fb_op_not» «fb_op_number» «fb_op_or» «fb_op_origin» «fb_op_pc» «fb_op_pop» «fb_op_prevrandao» «fb_op_push» «fb_op_return» «fb_op_returndatacopy» «fb_op_returndatasize» «fb_op_revert» «fb_op_sar» «fb_op_sdiv» «fb_op_selfbalance» «fb_op_selfdestruct» «fb_op_sgt» «fb_op_shl» «fb_op_shr» «fb_op_signextend» «gb_op_sload» «fb_op_slotnum» «fb_op_slt» «fb_op_smod» «gb_op_sstore» «fb_op_staticcall» «fb_op_stop» «fb_op_sub» «fb_op_swap» «fb_op_swapn» «fb_op_timestamp» «fb_op_tload» «fb_op_tstore» «fb_op_xor»

/-- The body of `run_frames` alone (AST line 18663, guard `EvmInv`, #0 POT). Its direct callees are
exactly `finish_child`, `frame_epilogue`, `frame_exception`, `op_dispatch` (`«callees_run_frames»`, checked against the AST). Hypotheses: the bound
of each of these 4 callees, then the contract of each callee at a guard-carrying
call site (4: `finish_child_spec`, `frame_epilogue_spec`, `frame_exception_spec`, `op_dispatch_spec`). Nothing else is assumed. -/
def GBody.«run_frames» : Prop :=
  (TerminatingFunBoundedOn FinishReady (ofString "finish_child") K.«finish_child») →
  (TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.«frame_epilogue») →
  (TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.«frame_exception») →
  (TerminatingFunBoundedOn EvmRun (ofString "op_dispatch") K.«op_dispatch») →
  (type_of% @finish_child_spec) →
  (type_of% @frame_epilogue_spec) →
  (type_of% @frame_exception_spec) →
  (type_of% @op_dispatch_spec) →
  TerminatingFunBoundedOn EvmInv (ofString "run_frames") K.«run_frames»

/-- The direct callees of `run_frames`, read off its AST body (revision 6). -/
theorem «callees_run_frames» : sameNames (progCallees (fnBody Guest.Software.guestFn_run_frames))
    ["finish_child", "frame_epilogue", "frame_exception", "op_dispatch"] = true := by decide

theorem «gbody_run_frames» : GBody.«run_frames» := by sorry

theorem «gb_run_frames» : TerminatingFunBoundedOn EvmInv (ofString "run_frames") K.«run_frames» :=
  «gbody_run_frames» «gb_finish_child» «fb_frame_epilogue» «fb_frame_exception» «gb_op_dispatch» «finish_child_spec» «frame_epilogue_spec» «frame_exception_spec» «op_dispatch_spec»

/-- The body of `process_message` alone (AST line 18803, guard `MsgReady`, loop-free). Its direct callees are
exactly `depth0_prepare`, `frame_halt`, `frame_mem_release`, `frame_open`, `frame_start`, `refill_frame_state_gas`, `run_frames`, `scratch_release`, `state_restore`, `state_snapshot` (`«callees_process_message»`, checked against the AST). Hypotheses: the bound
of each of these 10 callees, then the contract of each callee at a guard-carrying
call site (4: `ek_depth0_prepare`, `fk_frame_open`, `ek_frame_start`, `ro_state_snapshot`). Nothing else is assumed. -/
def GBody.«process_message» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "depth0_prepare") K.«depth0_prepare») →
  (TerminatingFunBoundedOn GuestInv (ofString "frame_halt") K.«frame_halt») →
  (TerminatingFunBoundedOn GuestInv (ofString "frame_mem_release") K.«frame_mem_release») →
  (TerminatingFunBoundedOn GuestInv (ofString "frame_open") K.«frame_open») →
  (TerminatingFunBoundedOn GuestInv (ofString "frame_start") K.«frame_start») →
  (TerminatingFunBoundedOn GuestInv (ofString "refill_frame_state_gas") K.«refill_frame_state_gas») →
  (TerminatingFunBoundedOn EvmInv (ofString "run_frames") K.«run_frames») →
  (TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release») →
  (TerminatingFunBoundedOn GuestInv (ofString "state_restore") K.«state_restore») →
  (TerminatingFunBoundedOn GuestInv (ofString "state_snapshot") K.«state_snapshot») →
  (KeepsOn EvmMsgReady EvmInv (ofString "depth0_prepare")) →
  (KeepsOn FrameOpenReady EvmMsgReady (ofString "frame_open")) →
  (KeepsOn EvmInv EvmInv (ofString "frame_start")) →
  (ReadOnlyFn (ofString "state_snapshot")) →
  TerminatingFunBoundedOn MsgReady (ofString "process_message") K.«process_message»

/-- The direct callees of `process_message`, read off its AST body (revision 6). -/
theorem «callees_process_message» : sameNames (progCallees (fnBody Guest.Software.guestFn_process_message))
    ["depth0_prepare", "frame_halt", "frame_mem_release", "frame_open", "frame_start", "refill_frame_state_gas", "run_frames", "scratch_release", "state_restore", "state_snapshot"] = true := by decide

theorem «gbody_process_message» : GBody.«process_message» := by sorry

theorem «gb_process_message» : TerminatingFunBoundedOn MsgReady (ofString "process_message") K.«process_message» :=
  «gbody_process_message» «fb_depth0_prepare» «fb_frame_halt» «fb_frame_mem_release» «fb_frame_open» «fb_frame_start» «fb_refill_frame_state_gas» «gb_run_frames» «fb_scratch_release» «fb_state_restore» «fb_state_snapshot» «ek_depth0_prepare» «fk_frame_open» «ek_frame_start» «ro_state_snapshot»

/-- The body of `process_create_message` alone (AST line 18899, guard `MsgReady`, loop-free). Its direct callees are
exactly `create_finish`, `destroy_storage`, `frame_halt`, `increment_nonce`, `mark_account_created`, `process_message`, `refill_frame_state_gas`, `state_restore`, `state_snapshot` (`«callees_process_create_message»`, checked against the AST). Hypotheses: the bound
of each of these 9 callees, then the contract of each callee at a guard-carrying
call site (4: `wk_destroy_storage`, `wk_increment_nonce`, `wk_mark_account_created`, `ro_state_snapshot`). Nothing else is assumed. -/
def GBody.«process_create_message» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "create_finish") K.«create_finish») →
  (TerminatingFunBoundedOn GuestInv (ofString "destroy_storage") K.«destroy_storage») →
  (TerminatingFunBoundedOn GuestInv (ofString "frame_halt") K.«frame_halt») →
  (TerminatingFunBoundedOn GuestInv (ofString "increment_nonce") K.«increment_nonce») →
  (TerminatingFunBoundedOn GuestInv (ofString "mark_account_created") K.«mark_account_created») →
  (TerminatingFunBoundedOn MsgReady (ofString "process_message") K.«process_message») →
  (TerminatingFunBoundedOn GuestInv (ofString "refill_frame_state_gas") K.«refill_frame_state_gas») →
  (TerminatingFunBoundedOn GuestInv (ofString "state_restore") K.«state_restore») →
  (TerminatingFunBoundedOn GuestInv (ofString "state_snapshot") K.«state_snapshot») →
  (KeepsOn WorldOK WorldOK (ofString "destroy_storage")) →
  (KeepsOn WorldOK WorldOK (ofString "increment_nonce")) →
  (KeepsOn WorldOK WorldOK (ofString "mark_account_created")) →
  (ReadOnlyFn (ofString "state_snapshot")) →
  TerminatingFunBoundedOn MsgReady (ofString "process_create_message") K.«process_create_message»

/-- The direct callees of `process_create_message`, read off its AST body (revision 6). -/
theorem «callees_process_create_message» : sameNames (progCallees (fnBody Guest.Software.guestFn_process_create_message))
    ["create_finish", "destroy_storage", "frame_halt", "increment_nonce", "mark_account_created", "process_message", "refill_frame_state_gas", "state_restore", "state_snapshot"] = true := by decide

theorem «gbody_process_create_message» : GBody.«process_create_message» := by sorry

theorem «gb_process_create_message» : TerminatingFunBoundedOn MsgReady (ofString "process_create_message") K.«process_create_message» :=
  «gbody_process_create_message» «fb_create_finish» «fb_destroy_storage» «fb_frame_halt» «fb_increment_nonce» «fb_mark_account_created» «gb_process_message» «fb_refill_frame_state_gas» «fb_state_restore» «fb_state_snapshot» «wk_destroy_storage» «wk_increment_nonce» «wk_mark_account_created» «ro_state_snapshot»

/-- The body of `process_message_call` alone (AST line 19661, guard `MsgReady`, loop-free). Its direct callees are
exactly `account_deployable`, `alloc`, `frame_state_gas_used`, `memzero`, `process_create_message`, `process_message` (`«callees_process_message_call»`, checked against the AST). Hypotheses: the bound
of each of these 6 callees, then the contract of each callee at a guard-carrying
call site (3: `wk_account_deployable`, `ww_alloc`, `ww_memzero`). Nothing else is assumed. -/
def GBody.«process_message_call» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "account_deployable") K.«account_deployable») →
  (TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
  (TerminatingFunBoundedOn GuestInv (ofString "frame_state_gas_used") K.«frame_state_gas_used») →
  (TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero») →
  (TerminatingFunBoundedOn MsgReady (ofString "process_create_message") K.«process_create_message») →
  (TerminatingFunBoundedOn MsgReady (ofString "process_message") K.«process_message») →
  (KeepsOn WorldOK WorldOK (ofString "account_deployable")) →
  (WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "alloc")) →
  (WritesWithin (fun s => [(locN s "dst", locN s "n")])
    [] (ofString "memzero")) →
  TerminatingFunBoundedOn MsgReady (ofString "process_message_call") K.«process_message_call»

/-- The direct callees of `process_message_call`, read off its AST body (revision 6). -/
theorem «callees_process_message_call» : sameNames (progCallees (fnBody Guest.Software.guestFn_process_message_call))
    ["account_deployable", "alloc", "frame_state_gas_used", "memzero", "process_create_message", "process_message"] = true := by decide

theorem «gbody_process_message_call» : GBody.«process_message_call» := by sorry

theorem «gb_process_message_call» : TerminatingFunBoundedOn MsgReady (ofString "process_message_call") K.«process_message_call» :=
  «gbody_process_message_call» «fb_account_deployable» «fb_alloc» «fb_frame_state_gas_used» «fb_memzero» «gb_process_create_message» «gb_process_message» «wk_account_deployable» «ww_alloc» «ww_memzero»

/-- The body of `process_unchecked_system_transaction` alone (AST line 32851, guard `WorldOK`, loop-free). Its direct callees are
exactly `alloc`, `ext_code_of`, `frame_mem_release`, `htab_new`, `incorporate_tx_into_block`, `memcpy`, `msg_new`, `process_message_call`, `scratch_release`, `state_fresh_tx`, `te_new` (`«callees_process_unchecked_system_transaction»`, checked against the AST). Hypotheses: the bound
of each of these 11 callees, then the contract of each callee at a guard-carrying
call site (6: `wk_ext_code_of`, `htab_new_spec`, `ww_msg_new`, `wk_process_message_call`, `ww_state_fresh_tx`, `ww_te_new`). Nothing else is assumed. -/
def GBody.«process_unchecked_system_transaction» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
  (TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.«ext_code_of») →
  (TerminatingFunBoundedOn GuestInv (ofString "frame_mem_release") K.«frame_mem_release») →
  (TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new») →
  (TerminatingFunBoundedOn WorldOK (ofString "incorporate_tx_into_block") K.«incorporate_tx_into_block») →
  (TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy») →
  (TerminatingFunBoundedOn GuestInv (ofString "msg_new") K.«msg_new») →
  (TerminatingFunBoundedOn MsgReady (ofString "process_message_call") K.«process_message_call») →
  (TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release») →
  (TerminatingFunBoundedOn GuestInv (ofString "state_fresh_tx") K.«state_fresh_tx») →
  (TerminatingFunBoundedOn GuestInv (ofString "te_new") K.«te_new») →
  (KeepsOn WorldOK WorldOK (ofString "ext_code_of")) →
  (type_of% @htab_new_spec) →
  (WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "msg_new")) →
  (KeepsOn MsgReady WorldOK (ofString "process_message_call")) →
  (WritesWithin (fun s => [(globN s "ts", 72)])
    ["heap_ptr", "journal_n", "ts"] (ofString "state_fresh_tx")) →
  (WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "te_new")) →
  TerminatingFunBoundedOn WorldOK (ofString "process_unchecked_system_transaction") K.«process_unchecked_system_transaction»

/-- The direct callees of `process_unchecked_system_transaction`, read off its AST body (revision 6). -/
theorem «callees_process_unchecked_system_transaction» : sameNames (progCallees (fnBody Guest.Software.guestFn_process_unchecked_system_transaction))
    ["alloc", "ext_code_of", "frame_mem_release", "htab_new", "incorporate_tx_into_block", "memcpy", "msg_new", "process_message_call", "scratch_release", "state_fresh_tx", "te_new"] = true := by decide

theorem «gbody_process_unchecked_system_transaction» : GBody.«process_unchecked_system_transaction» := by sorry

theorem «gb_process_unchecked_system_transaction» : TerminatingFunBoundedOn WorldOK (ofString "process_unchecked_system_transaction") K.«process_unchecked_system_transaction» :=
  «gbody_process_unchecked_system_transaction» «fb_alloc» «fb_ext_code_of» «fb_frame_mem_release» «fb_htab_new» «gb_incorporate_tx_into_block» «fb_memcpy» «fb_msg_new» «gb_process_message_call» «fb_scratch_release» «fb_state_fresh_tx» «fb_te_new» «wk_ext_code_of» «htab_new_spec» «ww_msg_new» «wk_process_message_call» «ww_state_fresh_tx» «ww_te_new»

/-- The body of `process_checked_system_transaction` alone (AST line 32928, guard `WorldOK`, loop-free). Its direct callees are
exactly `alloc`, `ext_code_of`, `process_unchecked_system_transaction`, `state_fresh_tx` (`«callees_process_checked_system_transaction»`, checked against the AST). Hypotheses: the bound
of each of these 4 callees, then the contract of each callee at a guard-carrying
call site (3: `ww_alloc`, `wk_ext_code_of`, `ww_state_fresh_tx`). Nothing else is assumed. -/
def GBody.«process_checked_system_transaction» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
  (TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.«ext_code_of») →
  (TerminatingFunBoundedOn WorldOK (ofString "process_unchecked_system_transaction") K.«process_unchecked_system_transaction») →
  (TerminatingFunBoundedOn GuestInv (ofString "state_fresh_tx") K.«state_fresh_tx») →
  (WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "alloc")) →
  (KeepsOn WorldOK WorldOK (ofString "ext_code_of")) →
  (WritesWithin (fun s => [(globN s "ts", 72)])
    ["heap_ptr", "journal_n", "ts"] (ofString "state_fresh_tx")) →
  TerminatingFunBoundedOn WorldOK (ofString "process_checked_system_transaction") K.«process_checked_system_transaction»

/-- The direct callees of `process_checked_system_transaction`, read off its AST body (revision 6). -/
theorem «callees_process_checked_system_transaction» : sameNames (progCallees (fnBody Guest.Software.guestFn_process_checked_system_transaction))
    ["alloc", "ext_code_of", "process_unchecked_system_transaction", "state_fresh_tx"] = true := by decide

theorem «gbody_process_checked_system_transaction» : GBody.«process_checked_system_transaction» := by sorry

theorem «gb_process_checked_system_transaction» : TerminatingFunBoundedOn WorldOK (ofString "process_checked_system_transaction") K.«process_checked_system_transaction» :=
  «gbody_process_checked_system_transaction» «fb_alloc» «fb_ext_code_of» «gb_process_unchecked_system_transaction» «fb_state_fresh_tx» «ww_alloc» «wk_ext_code_of» «ww_state_fresh_tx»

/-- The body of `process_general_purpose_requests` alone (AST line 33507, guard `ReqsFresh`, #0 CTR; #1 CTR). Its direct callees are
exactly `alloc`, `extract_deposit_data`, `memcpy`, `memeq`, `process_checked_system_transaction`, `requests_append` (`«callees_process_general_purpose_requests»`, checked against the AST). Hypotheses: the bound
of each of these 6 callees, then the contract of each callee at a guard-carrying
call site (6: `ww_alloc`, `ww_extract_deposit_data`, `ww_memcpy`, `ro_memeq`, `wk_process_checked_system_transaction`, `wk_requests_append`). Nothing else is assumed. -/
def GBody.«process_general_purpose_requests» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
  (TerminatingFunBoundedOn GuestInv (ofString "extract_deposit_data") K.«extract_deposit_data») →
  (TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy») →
  (TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») →
  (TerminatingFunBoundedOn WorldOK (ofString "process_checked_system_transaction") K.«process_checked_system_transaction») →
  (TerminatingFunBoundedOn GuestInv (ofString "requests_append") K.«requests_append») →
  (WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "alloc")) →
  (WritesWithin (fun s => [(locN s "out", 192)])
    ["heap_ptr"] (ofString "extract_deposit_data")) →
  (WritesWithin (fun s => [(locN s "dst", locN s "n")])
    [] (ofString "memcpy")) →
  (ReadOnlyFn (ofString "memeq")) →
  (KeepsOn WorldOK WorldOK (ofString "process_checked_system_transaction")) →
  (KeepsOn ReqRoom WorldOK (ofString "requests_append")) →
  TerminatingFunBoundedOn ReqsFresh (ofString "process_general_purpose_requests") K.«process_general_purpose_requests»

/-- The direct callees of `process_general_purpose_requests`, read off its AST body (revision 6). -/
theorem «callees_process_general_purpose_requests» : sameNames (progCallees (fnBody Guest.Software.guestFn_process_general_purpose_requests))
    ["alloc", "extract_deposit_data", "memcpy", "memeq", "process_checked_system_transaction", "requests_append"] = true := by decide

theorem «gbody_process_general_purpose_requests» : GBody.«process_general_purpose_requests» := by sorry

theorem «gb_process_general_purpose_requests» : TerminatingFunBoundedOn ReqsFresh (ofString "process_general_purpose_requests") K.«process_general_purpose_requests» :=
  «gbody_process_general_purpose_requests» «fb_alloc» «fb_extract_deposit_data» «fb_memcpy» «fb_memeq» «gb_process_checked_system_transaction» «fb_requests_append» «ww_alloc» «ww_extract_deposit_data» «ww_memcpy» «ro_memeq» «wk_process_checked_system_transaction» «wk_requests_append»

/-- The body of `process_transaction` alone (AST line 33103, guard `TxReady`, #0 CTR; #1 CTR; #2 CTR; #3 CTR; #4 CTR; #5 CTR; #6 CTR; #7 CTR; #8 CTR). Its direct callees are
exactly `alloc`, `calculate_blob_gas_price`, `calculate_total_blob_gas`, `check_transaction`, `clear_account_preserving_balance`, `compute_contract_address`, `create_ether`, `encode_receipt`, `encode_transaction`, `fee_mul`, `frame_mem_release`, `get_account`, `htab_item`, `htab_new`, `htab_set`, `incorporate_tx_into_block`, `increment_nonce`, `keccak256`, `lst_new`, `lst_push`, `max`, `memcpy`, `min`, `msg_new`, `process_message_call`, `recover_sender_with_chain_id`, `scratch_release`, `set_account_balance`, `state_fresh_tx`, `te_new`, `tx_chain_id`, `tx_has_access_list`, `tx_is_blob`, `tx_is_setcode`, `u256_sub`, `udiv_small5`, `validate_transaction` (`«callees_process_transaction»`, checked against the AST). Hypotheses: the bound
of each of these 37 callees, then the contract of each callee at a guard-carrying
call site (34: `ww_alloc`, `wk_calculate_blob_gas_price`, `ro_calculate_total_blob_gas`, `wk_check_transaction`, `wk_clear_account_preserving_balance`, `ww_compute_contract_address`, `wk_create_ether`, `wk_encode_receipt`, `wk_encode_transaction`, `ro_fee_mul`, `wk_get_account`, `ro_htab_item`, `htab_new_spec`, `htab_set_spec`, `wk_increment_nonce`, `ww_keccak256`, `ww_lst_new`, `ww_lst_push`, `ro_max`, `ww_memcpy`, `ro_min`, `ww_msg_new`, `wk_process_message_call`, `ww_recover_sender_with_chain_id`, `wk_set_account_balance`, `ww_state_fresh_tx`, `ww_te_new`, `ro_tx_chain_id`, `ro_tx_has_access_list`, `ro_tx_is_blob`, `ro_tx_is_setcode`, `ro_u256_sub`, `ro_udiv_small5`, `ro_validate_transaction`). Nothing else is assumed. -/
def GBody.«process_transaction» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
  (TerminatingFunBoundedOn GuestInv (ofString "calculate_blob_gas_price") K.«calculate_blob_gas_price») →
  (TerminatingFunBoundedOn GuestInv (ofString "calculate_total_blob_gas") K.«calculate_total_blob_gas») →
  (TerminatingFunBoundedOn GuestInv (ofString "check_transaction") K.«check_transaction») →
  (TerminatingFunBoundedOn GuestInv (ofString "clear_account_preserving_balance") K.«clear_account_preserving_balance») →
  (TerminatingFunBoundedOn GuestInv (ofString "compute_contract_address") K.«compute_contract_address») →
  (TerminatingFunBoundedOn GuestInv (ofString "create_ether") K.«create_ether») →
  (TerminatingFunBoundedOn GuestInv (ofString "encode_receipt") K.«encode_receipt») →
  (TerminatingFunBoundedOn GuestInv (ofString "encode_transaction") K.«encode_transaction») →
  (TerminatingFunBoundedOn GuestInv (ofString "fee_mul") K.«fee_mul») →
  (TerminatingFunBoundedOn GuestInv (ofString "frame_mem_release") K.«frame_mem_release») →
  (TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account») →
  (TerminatingFunBoundedOn GuestInv (ofString "htab_item") K.«htab_item») →
  (TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new») →
  (TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set») →
  (TerminatingFunBoundedOn WorldOK (ofString "incorporate_tx_into_block") K.«incorporate_tx_into_block») →
  (TerminatingFunBoundedOn GuestInv (ofString "increment_nonce") K.«increment_nonce») →
  (TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256») →
  (TerminatingFunBoundedOn GuestInv (ofString "lst_new") K.«lst_new») →
  (TerminatingFunBoundedOn GuestInv (ofString "lst_push") K.«lst_push») →
  (TerminatingFunBoundedOn GuestInv (ofString "max") K.«max») →
  (TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy») →
  (TerminatingFunBoundedOn GuestInv (ofString "min") K.«min») →
  (TerminatingFunBoundedOn GuestInv (ofString "msg_new") K.«msg_new») →
  (TerminatingFunBoundedOn MsgReady (ofString "process_message_call") K.«process_message_call») →
  (TerminatingFunBoundedOn GuestInv (ofString "recover_sender_with_chain_id") K.«recover_sender_with_chain_id») →
  (TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release») →
  (TerminatingFunBoundedOn GuestInv (ofString "set_account_balance") K.«set_account_balance») →
  (TerminatingFunBoundedOn GuestInv (ofString "state_fresh_tx") K.«state_fresh_tx») →
  (TerminatingFunBoundedOn GuestInv (ofString "te_new") K.«te_new») →
  (TerminatingFunBoundedOn GuestInv (ofString "tx_chain_id") K.«tx_chain_id») →
  (TerminatingFunBoundedOn GuestInv (ofString "tx_has_access_list") K.«tx_has_access_list») →
  (TerminatingFunBoundedOn GuestInv (ofString "tx_is_blob") K.«tx_is_blob») →
  (TerminatingFunBoundedOn GuestInv (ofString "tx_is_setcode") K.«tx_is_setcode») →
  (TerminatingFunBoundedOn GuestInv (ofString "u256_sub") K.«u256_sub») →
  (TerminatingFunBoundedOn GuestInv (ofString "udiv_small5") K.«udiv_small5») →
  (TerminatingFunBoundedOn GuestInv (ofString "validate_transaction") K.«validate_transaction») →
  (WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "alloc")) →
  (KeepsOn WorldOK WorldOK (ofString "calculate_blob_gas_price")) →
  (ReadOnlyFn (ofString "calculate_total_blob_gas")) →
  (KeepsOn WorldOK WorldOK (ofString "check_transaction")) →
  (KeepsOn WorldOK WorldOK (ofString "clear_account_preserving_balance")) →
  (WritesWithin (fun s => [(locN s "out", 20), (globN s "keccak_pad", 136), (globN s "keccak_st", 200)])
    ["heap_ptr"] (ofString "compute_contract_address")) →
  (KeepsOn WorldOK WorldOK (ofString "create_ether")) →
  (KeepsOn WorldOK WorldOK (ofString "encode_receipt")) →
  (KeepsOn WorldOK WorldOK (ofString "encode_transaction")) →
  (ReadOnlyFn (ofString "fee_mul")) →
  (KeepsOn WorldOK WorldOK (ofString "get_account")) →
  (ReadOnlyFn (ofString "htab_item")) →
  (type_of% @htab_new_spec) →
  (type_of% @htab_set_spec) →
  (KeepsOn WorldOK WorldOK (ofString "increment_nonce")) →
  (WritesWithin (fun s => [(locN s "out", 32), (globN s "keccak_pad", 136), (globN s "keccak_st", 200)])
    [] (ofString "keccak256")) →
  (WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "lst_new")) →
  (WritesWithin (fun s => [(locN s "l", 24), (memW s (locN s "l"), locN s "esz" * memW s (locN s "l" + 16))])
    ["heap_ptr"] (ofString "lst_push")) →
  (ReadOnlyFn (ofString "max")) →
  (WritesWithin (fun s => [(locN s "dst", locN s "n")])
    [] (ofString "memcpy")) →
  (ReadOnlyFn (ofString "min")) →
  (WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "msg_new")) →
  (KeepsOn MsgReady WorldOK (ofString "process_message_call")) →
  (WritesWithin (fun s => [(locN s "out20", 20), (globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "u256_ws", 640)])
    ["heap_ptr"] (ofString "recover_sender_with_chain_id")) →
  (KeepsOn WorldOK WorldOK (ofString "set_account_balance")) →
  (WritesWithin (fun s => [(globN s "ts", 72)])
    ["heap_ptr", "journal_n", "ts"] (ofString "state_fresh_tx")) →
  (WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "te_new")) →
  (ReadOnlyFn (ofString "tx_chain_id")) →
  (ReadOnlyFn (ofString "tx_has_access_list")) →
  (ReadOnlyFn (ofString "tx_is_blob")) →
  (ReadOnlyFn (ofString "tx_is_setcode")) →
  (ReadOnlyFn (ofString "u256_sub")) →
  (ReadOnlyFn (ofString "udiv_small5")) →
  (ReadOnlyFn (ofString "validate_transaction")) →
  TerminatingFunBoundedOn TxReady (ofString "process_transaction") K.«process_transaction»

/-- The direct callees of `process_transaction`, read off its AST body (revision 6). -/
theorem «callees_process_transaction» : sameNames (progCallees (fnBody Guest.Software.guestFn_process_transaction))
    ["alloc", "calculate_blob_gas_price", "calculate_total_blob_gas", "check_transaction", "clear_account_preserving_balance", "compute_contract_address", "create_ether", "encode_receipt", "encode_transaction", "fee_mul", "frame_mem_release", "get_account", "htab_item", "htab_new", "htab_set", "incorporate_tx_into_block", "increment_nonce", "keccak256", "lst_new", "lst_push", "max", "memcpy", "min", "msg_new", "process_message_call", "recover_sender_with_chain_id", "scratch_release", "set_account_balance", "state_fresh_tx", "te_new", "tx_chain_id", "tx_has_access_list", "tx_is_blob", "tx_is_setcode", "u256_sub", "udiv_small5", "validate_transaction"] = true := by decide

theorem «gbody_process_transaction» : GBody.«process_transaction» := by sorry

theorem «gb_process_transaction» : TerminatingFunBoundedOn TxReady (ofString "process_transaction") K.«process_transaction» :=
  «gbody_process_transaction» «fb_alloc» «fb_calculate_blob_gas_price» «fb_calculate_total_blob_gas» «fb_check_transaction» «fb_clear_account_preserving_balance» «fb_compute_contract_address» «fb_create_ether» «fb_encode_receipt» «fb_encode_transaction» «fb_fee_mul» «fb_frame_mem_release» «fb_get_account» «fb_htab_item» «fb_htab_new» «fb_htab_set» «gb_incorporate_tx_into_block» «fb_increment_nonce» «fb_keccak256» «fb_lst_new» «fb_lst_push» «fb_max» «fb_memcpy» «fb_min» «fb_msg_new» «gb_process_message_call» «fb_recover_sender_with_chain_id» «fb_scratch_release» «fb_set_account_balance» «fb_state_fresh_tx» «fb_te_new» «fb_tx_chain_id» «fb_tx_has_access_list» «fb_tx_is_blob» «fb_tx_is_setcode» «fb_u256_sub» «fb_udiv_small5» «fb_validate_transaction» «ww_alloc» «wk_calculate_blob_gas_price» «ro_calculate_total_blob_gas» «wk_check_transaction» «wk_clear_account_preserving_balance» «ww_compute_contract_address» «wk_create_ether» «wk_encode_receipt» «wk_encode_transaction» «ro_fee_mul» «wk_get_account» «ro_htab_item» «htab_new_spec» «htab_set_spec» «wk_increment_nonce» «ww_keccak256» «ww_lst_new» «ww_lst_push» «ro_max» «ww_memcpy» «ro_min» «ww_msg_new» «wk_process_message_call» «ww_recover_sender_with_chain_id» «wk_set_account_balance» «ww_state_fresh_tx» «ww_te_new» «ro_tx_chain_id» «ro_tx_has_access_list» «ro_tx_is_blob» «ro_tx_is_setcode» «ro_u256_sub» «ro_udiv_small5» «ro_validate_transaction»

/-- The body of `process_withdrawals` alone (AST line 33458, guard `WorldOK`, #0 CTR). Its direct callees are
exactly `create_ether`, `incorporate_tx_into_block`, `state_fresh_tx`, `u256_mul` (`«callees_process_withdrawals»`, checked against the AST). Hypotheses: the bound
of each of these 4 callees, then the contract of each callee at a guard-carrying
call site (3: `wk_create_ether`, `ww_state_fresh_tx`, `ro_u256_mul`). Nothing else is assumed. -/
def GBody.«process_withdrawals» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "create_ether") K.«create_ether») →
  (TerminatingFunBoundedOn WorldOK (ofString "incorporate_tx_into_block") K.«incorporate_tx_into_block») →
  (TerminatingFunBoundedOn GuestInv (ofString "state_fresh_tx") K.«state_fresh_tx») →
  (TerminatingFunBoundedOn GuestInv (ofString "u256_mul") K.«u256_mul») →
  (KeepsOn WorldOK WorldOK (ofString "create_ether")) →
  (WritesWithin (fun s => [(globN s "ts", 72)])
    ["heap_ptr", "journal_n", "ts"] (ofString "state_fresh_tx")) →
  (ReadOnlyFn (ofString "u256_mul")) →
  TerminatingFunBoundedOn WorldOK (ofString "process_withdrawals") K.«process_withdrawals»

/-- The direct callees of `process_withdrawals`, read off its AST body (revision 6). -/
theorem «callees_process_withdrawals» : sameNames (progCallees (fnBody Guest.Software.guestFn_process_withdrawals))
    ["create_ether", "incorporate_tx_into_block", "state_fresh_tx", "u256_mul"] = true := by decide

theorem «gbody_process_withdrawals» : GBody.«process_withdrawals» := by sorry

theorem «gb_process_withdrawals» : TerminatingFunBoundedOn WorldOK (ofString "process_withdrawals") K.«process_withdrawals» :=
  «gbody_process_withdrawals» «fb_create_ether» «gb_incorporate_tx_into_block» «fb_state_fresh_tx» «fb_u256_mul» «wk_create_ether» «ww_state_fresh_tx» «ro_u256_mul»

/-- The body of `execute_block` alone (AST line 33580, guard `BlockReady`, #0 CTR). Its direct callees are
exactly `alloc`, `bal_init`, `build_block_access_list_rlp`, `build_mpt_indexed`, `compute_requests_hash`, `compute_state_root`, `decode_transaction`, `keccak256`, `logs_bloom`, `lst_new`, `max`, `memeq`, `memzero`, `process_general_purpose_requests`, `process_transaction`, `process_unchecked_system_transaction`, `process_withdrawals`, `state_fresh_tx`, `track_ancestor_access`, `validate_block_access_list_gas_limit` (`«callees_execute_block»`, checked against the AST). Hypotheses: the bound
of each of these 20 callees, then the contract of each callee at a guard-carrying
call site (16: `ww_alloc`, `ww_bal_init`, `wk_build_block_access_list_rlp`, `wk_build_mpt_indexed`, `wk_compute_state_root`, `ww_decode_transaction`, `ww_logs_bloom`, `ww_lst_new`, `ww_memzero`, `wk_process_general_purpose_requests`, `wk_process_transaction`, `wk_process_unchecked_system_transaction`, `wk_process_withdrawals`, `ww_state_fresh_tx`, `ww_track_ancestor_access`, `ro_validate_block_access_list_gas_limit`). Nothing else is assumed. -/
def GBody.«execute_block» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
  (TerminatingFunBoundedOn GuestInv (ofString "bal_init") K.«bal_init») →
  (TerminatingFunBoundedOn GuestInv (ofString "build_block_access_list_rlp") K.«build_block_access_list_rlp») →
  (TerminatingFunBoundedOn WorldOK (ofString "build_mpt_indexed") K.«build_mpt_indexed») →
  (TerminatingFunBoundedOn GuestInv (ofString "compute_requests_hash") K.«compute_requests_hash») →
  (TerminatingFunBoundedOn WorldOK (ofString "compute_state_root") K.«compute_state_root») →
  (TerminatingFunBoundedOn GuestInv (ofString "decode_transaction") K.«decode_transaction») →
  (TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256») →
  (TerminatingFunBoundedOn GuestInv (ofString "logs_bloom") K.«logs_bloom») →
  (TerminatingFunBoundedOn GuestInv (ofString "lst_new") K.«lst_new») →
  (TerminatingFunBoundedOn GuestInv (ofString "max") K.«max») →
  (TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») →
  (TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero») →
  (TerminatingFunBoundedOn ReqsFresh (ofString "process_general_purpose_requests") K.«process_general_purpose_requests») →
  (TerminatingFunBoundedOn TxReady (ofString "process_transaction") K.«process_transaction») →
  (TerminatingFunBoundedOn WorldOK (ofString "process_unchecked_system_transaction") K.«process_unchecked_system_transaction») →
  (TerminatingFunBoundedOn WorldOK (ofString "process_withdrawals") K.«process_withdrawals») →
  (TerminatingFunBoundedOn GuestInv (ofString "state_fresh_tx") K.«state_fresh_tx») →
  (TerminatingFunBoundedOn GuestInv (ofString "track_ancestor_access") K.«track_ancestor_access») →
  (TerminatingFunBoundedOn GuestInv (ofString "validate_block_access_list_gas_limit") K.«validate_block_access_list_gas_limit») →
  (WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "alloc")) →
  (WritesWithin (fun s => [])
    ["bal_accounts", "bal_idx_accts", "bal_idx_stor", "bal_index", "bal_key_buf", "heap_ptr"] (ofString "bal_init")) →
  (KeepsOn WorldOK WorldOK (ofString "build_block_access_list_rlp")) →
  (KeepsOn (WorldAvoids (fun s => [(locN s "out", 32)])) WorldOK (ofString "build_mpt_indexed")) →
  (KeepsOn (WorldAvoids (fun s => [(locN s "out", 32)])) WorldOK (ofString "compute_state_root")) →
  (WritesWithin (fun s => [])
    ["heap_ptr", "scratch_ptr"] (ofString "decode_transaction")) →
  (WritesWithin (fun s => [(locN s "out", 256), (globN s "keccak_pad", 136), (globN s "keccak_st", 200)])
    ["heap_ptr"] (ofString "logs_bloom")) →
  (WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "lst_new")) →
  (WritesWithin (fun s => [(locN s "dst", locN s "n")])
    [] (ofString "memzero")) →
  (KeepsOn ReqsFresh WorldOK (ofString "process_general_purpose_requests")) →
  (KeepsOn TxReady WorldOK (ofString "process_transaction")) →
  (KeepsOn WorldOK WorldOK (ofString "process_unchecked_system_transaction")) →
  (KeepsOn WorldOK WorldOK (ofString "process_withdrawals")) →
  (WritesWithin (fun s => [(globN s "ts", 72)])
    ["heap_ptr", "journal_n", "ts"] (ofString "state_fresh_tx")) →
  (WritesWithin (fun s => [(globN s "bs", 80)])
    [] (ofString "track_ancestor_access")) →
  (ReadOnlyFn (ofString "validate_block_access_list_gas_limit")) →
  TerminatingFunBoundedOn BlockReady (ofString "execute_block") K.«execute_block»

/-- The direct callees of `execute_block`, read off its AST body (revision 6). -/
theorem «callees_execute_block» : sameNames (progCallees (fnBody Guest.Software.guestFn_execute_block))
    ["alloc", "bal_init", "build_block_access_list_rlp", "build_mpt_indexed", "compute_requests_hash", "compute_state_root", "decode_transaction", "keccak256", "logs_bloom", "lst_new", "max", "memeq", "memzero", "process_general_purpose_requests", "process_transaction", "process_unchecked_system_transaction", "process_withdrawals", "state_fresh_tx", "track_ancestor_access", "validate_block_access_list_gas_limit"] = true := by decide

theorem «gbody_execute_block» : GBody.«execute_block» := by sorry

theorem «gb_execute_block» : TerminatingFunBoundedOn BlockReady (ofString "execute_block") K.«execute_block» :=
  «gbody_execute_block» «fb_alloc» «fb_bal_init» «fb_build_block_access_list_rlp» «gb_build_mpt_indexed» «fb_compute_requests_hash» «gb_compute_state_root» «fb_decode_transaction» «fb_keccak256» «fb_logs_bloom» «fb_lst_new» «fb_max» «fb_memeq» «fb_memzero» «gb_process_general_purpose_requests» «gb_process_transaction» «gb_process_unchecked_system_transaction» «gb_process_withdrawals» «fb_state_fresh_tx» «fb_track_ancestor_access» «fb_validate_block_access_list_gas_limit» «ww_alloc» «ww_bal_init» «wk_build_block_access_list_rlp» «wk_build_mpt_indexed» «wk_compute_state_root» «ww_decode_transaction» «ww_logs_bloom» «ww_lst_new» «ww_memzero» «wk_process_general_purpose_requests» «wk_process_transaction» «wk_process_unchecked_system_transaction» «wk_process_withdrawals» «ww_state_fresh_tx» «ww_track_ancestor_access» «ro_validate_block_access_list_gas_limit»

/-- The body of `payload_header` alone (AST line 32645, guard `WorldOK`, #0 CTR). Its direct callees are
exactly `alloc`, `block_rlp_length`, `build_mpt_indexed`, `compute_requests_hash`, `encode_execution_requests`, `encode_withdrawal_rlp`, `keccak256`, `memzero` (`«callees_payload_header»`, checked against the AST). Hypotheses: the bound
of each of these 8 callees, then the contract of each callee at a guard-carrying
call site (6: `ww_alloc`, `wk_block_rlp_length`, `wk_build_mpt_indexed`, `wk_encode_withdrawal_rlp`, `ww_keccak256`, `ww_memzero`). Nothing else is assumed. -/
def GBody.«payload_header» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
  (TerminatingFunBoundedOn GuestInv (ofString "block_rlp_length") K.«block_rlp_length») →
  (TerminatingFunBoundedOn WorldOK (ofString "build_mpt_indexed") K.«build_mpt_indexed») →
  (TerminatingFunBoundedOn GuestInv (ofString "compute_requests_hash") K.«compute_requests_hash») →
  (TerminatingFunBoundedOn GuestInv (ofString "encode_execution_requests") K.«encode_execution_requests») →
  (TerminatingFunBoundedOn GuestInv (ofString "encode_withdrawal_rlp") K.«encode_withdrawal_rlp») →
  (TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256») →
  (TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero») →
  (WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "alloc")) →
  (KeepsOn WorldOK WorldOK (ofString "block_rlp_length")) →
  (KeepsOn (WorldAvoids (fun s => [(locN s "out", 32)])) WorldOK (ofString "build_mpt_indexed")) →
  (KeepsOn WorldOK WorldOK (ofString "encode_withdrawal_rlp")) →
  (WritesWithin (fun s => [(locN s "out", 32), (globN s "keccak_pad", 136), (globN s "keccak_st", 200)])
    [] (ofString "keccak256")) →
  (WritesWithin (fun s => [(locN s "dst", locN s "n")])
    [] (ofString "memzero")) →
  TerminatingFunBoundedOn WorldOK (ofString "payload_header") K.«payload_header»

/-- The direct callees of `payload_header`, read off its AST body (revision 6). -/
theorem «callees_payload_header» : sameNames (progCallees (fnBody Guest.Software.guestFn_payload_header))
    ["alloc", "block_rlp_length", "build_mpt_indexed", "compute_requests_hash", "encode_execution_requests", "encode_withdrawal_rlp", "keccak256", "memzero"] = true := by decide

theorem «gbody_payload_header» : GBody.«payload_header» := by sorry

theorem «gb_payload_header» : TerminatingFunBoundedOn WorldOK (ofString "payload_header") K.«payload_header» :=
  «gbody_payload_header» «fb_alloc» «fb_block_rlp_length» «gb_build_mpt_indexed» «fb_compute_requests_hash» «fb_encode_execution_requests» «fb_encode_withdrawal_rlp» «fb_keccak256» «fb_memzero» «ww_alloc» «wk_block_rlp_length» «wk_build_mpt_indexed» «wk_encode_withdrawal_rlp» «ww_keccak256» «ww_memzero»

/-- The body of `state_init` alone (AST line 12708, guard `WorldOK`, loop-free). Its direct callees are
exactly `alloc`, `decode_witness_to_mpt`, `htab_new` (`«callees_state_init»`, checked against the AST). Hypotheses: the bound
of each of these 3 callees, then the contract of each callee at a guard-carrying
call site (1: `ww_alloc`). Nothing else is assumed. -/
def GBody.«state_init» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
  (TerminatingFunBoundedOn WorldOK (ofString "decode_witness_to_mpt") K.«decode_witness_to_mpt») →
  (TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new») →
  (WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "alloc")) →
  TerminatingFunBoundedOn WorldOK (ofString "state_init") K.«state_init»

/-- The direct callees of `state_init`, read off its AST body (revision 6). -/
theorem «callees_state_init» : sameNames (progCallees (fnBody Guest.Software.guestFn_state_init))
    ["alloc", "decode_witness_to_mpt", "htab_new"] = true := by decide

theorem «gbody_state_init» : GBody.«state_init» := by sorry

theorem «gb_state_init» : TerminatingFunBoundedOn WorldOK (ofString "state_init") K.«state_init» :=
  «gbody_state_init» «fb_alloc» «gb_decode_witness_to_mpt» «fb_htab_new» «ww_alloc»

/-- The body of `run_attempt` alone (AST line 33734, guard `WorldOK`, #0 CTR). Its direct callees are
exactly `alloc`, `check_gas_limit`, `execute_block`, `header_hash`, `is_valid_versioned_hashes`, `memeq`, `memzero`, `nodedb_build`, `payload_header`, `state_init`, `validate_header`, `validate_headers` (`«callees_run_attempt»`, checked against the AST). Hypotheses: the bound
of each of these 12 callees, then the contract of each callee at a guard-carrying
call site (11: `ww_alloc`, `ro_check_gas_limit`, `ww_header_hash`, `ww_is_valid_versioned_hashes`, `ro_memeq`, `ww_memzero`, `wk_nodedb_build`, `wk_payload_header`, `wk_state_init`, `wk_validate_header`, `ww_validate_headers`). Nothing else is assumed. -/
def GBody.«run_attempt» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
  (TerminatingFunBoundedOn GuestInv (ofString "check_gas_limit") K.«check_gas_limit») →
  (TerminatingFunBoundedOn BlockReady (ofString "execute_block") K.«execute_block») →
  (TerminatingFunBoundedOn GuestInv (ofString "header_hash") K.«header_hash») →
  (TerminatingFunBoundedOn GuestInv (ofString "is_valid_versioned_hashes") K.«is_valid_versioned_hashes») →
  (TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») →
  (TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero») →
  (TerminatingFunBoundedOn GuestInv (ofString "nodedb_build") K.«nodedb_build») →
  (TerminatingFunBoundedOn WorldOK (ofString "payload_header") K.«payload_header») →
  (TerminatingFunBoundedOn WorldOK (ofString "state_init") K.«state_init») →
  (TerminatingFunBoundedOn GuestInv (ofString "validate_header") K.«validate_header») →
  (TerminatingFunBoundedOn GuestInv (ofString "validate_headers") K.«validate_headers») →
  (WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "alloc")) →
  (ReadOnlyFn (ofString "check_gas_limit")) →
  (WritesWithin (fun s => [(locN s "out", 32), (globN s "keccak_pad", 136), (globN s "keccak_st", 200)])
    ["heap_ptr"] (ofString "header_hash")) →
  (WritesWithin (fun s => [])
    ["heap_ptr", "scratch_ptr"] (ofString "is_valid_versioned_hashes")) →
  (ReadOnlyFn (ofString "memeq")) →
  (WritesWithin (fun s => [(locN s "dst", locN s "n")])
    [] (ofString "memzero")) →
  (KeepsOn WorldOK WorldOK (ofString "nodedb_build")) →
  (KeepsOn WorldOK WorldOK (ofString "payload_header")) →
  (KeepsOn WorldOK WorldOK (ofString "state_init")) →
  (KeepsOn WorldOK WorldOK (ofString "validate_header")) →
  (WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200)])
    ["heap_ptr", "scratch_ptr"] (ofString "validate_headers")) →
  TerminatingFunBoundedOn WorldOK (ofString "run_attempt") K.«run_attempt»

/-- The direct callees of `run_attempt`, read off its AST body (revision 6). -/
theorem «callees_run_attempt» : sameNames (progCallees (fnBody Guest.Software.guestFn_run_attempt))
    ["alloc", "check_gas_limit", "execute_block", "header_hash", "is_valid_versioned_hashes", "memeq", "memzero", "nodedb_build", "payload_header", "state_init", "validate_header", "validate_headers"] = true := by decide

theorem «gbody_run_attempt» : GBody.«run_attempt» := by sorry

theorem «gb_run_attempt» : TerminatingFunBoundedOn WorldOK (ofString "run_attempt") K.«run_attempt» :=
  «gbody_run_attempt» «fb_alloc» «fb_check_gas_limit» «gb_execute_block» «fb_header_hash» «fb_is_valid_versioned_hashes» «fb_memeq» «fb_memzero» «fb_nodedb_build» «gb_payload_header» «gb_state_init» «fb_validate_header» «fb_validate_headers» «ww_alloc» «ro_check_gas_limit» «ww_header_hash» «ww_is_valid_versioned_hashes» «ro_memeq» «ww_memzero» «wk_nodedb_build» «wk_payload_header» «wk_state_init» «wk_validate_header» «ww_validate_headers»

/-- The body of `attempt_l1` alone (AST line 33847, guard `WorldOK`, loop-free). Its direct callees are
exactly `run_attempt` (`«callees_attempt_l1»`, checked against the AST). Hypotheses: the bound
of each of these 1 callees, then the contract of each callee at a guard-carrying
call site (0: none). Nothing else is assumed. -/
def GBody.«attempt_l1» : Prop :=
  (TerminatingFunBoundedOn WorldOK (ofString "run_attempt") K.«run_attempt») →
  TerminatingFunBoundedOn WorldOK (ofString "attempt_l1") K.«attempt_l1»

/-- The direct callees of `attempt_l1`, read off its AST body (revision 6). -/
theorem «callees_attempt_l1» : sameNames (progCallees (fnBody Guest.Software.guestFn_attempt_l1))
    ["run_attempt"] = true := by decide

theorem «lookup_attempt_l1» : originalRuntimeCode.lookup (ofString "attempt_l1") =
    some ((sourceFunctionEntry Guest.Software.guestFn_attempt_l1).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 880 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_attempt_l1) rfl

/-- PROVED by concrete-body composition (no longer a primitive). -/
theorem «gbody_attempt_l1» : GBody.«attempt_l1» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l1», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l1, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (LocalsOnly.of_localsFree localsFree_worldOK) _ (by simp) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 worldOK_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _ (callEntryOn_of_localsFree localsFree_worldOK _ _))
        worldOK_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l1»; omega

theorem «gb_attempt_l1» : TerminatingFunBoundedOn WorldOK (ofString "attempt_l1") K.«attempt_l1» :=
  «gbody_attempt_l1» «gb_run_attempt»

/-- The body of `attempt_l2` alone (AST line 33863, guard `WorldOK`, loop-free). Its direct callees are
exactly `attempt_l1` (`«callees_attempt_l2»`, checked against the AST). Hypotheses: the bound
of each of these 1 callees, then the contract of each callee at a guard-carrying
call site (0: none). Nothing else is assumed. -/
def GBody.«attempt_l2» : Prop :=
  (TerminatingFunBoundedOn WorldOK (ofString "attempt_l1") K.«attempt_l1») →
  TerminatingFunBoundedOn WorldOK (ofString "attempt_l2") K.«attempt_l2»

/-- The direct callees of `attempt_l2`, read off its AST body (revision 6). -/
theorem «callees_attempt_l2» : sameNames (progCallees (fnBody Guest.Software.guestFn_attempt_l2))
    ["attempt_l1"] = true := by decide

theorem «lookup_attempt_l2» : originalRuntimeCode.lookup (ofString "attempt_l2") =
    some ((sourceFunctionEntry Guest.Software.guestFn_attempt_l2).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 881 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_attempt_l2) rfl

/-- PROVED by concrete-body composition (no longer a primitive). -/
theorem «gbody_attempt_l2» : GBody.«attempt_l2» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l2», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l2, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (LocalsOnly.of_localsFree localsFree_worldOK) _ (by simp) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 worldOK_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _ (callEntryOn_of_localsFree localsFree_worldOK _ _))
        worldOK_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l2»; omega

theorem «gb_attempt_l2» : TerminatingFunBoundedOn WorldOK (ofString "attempt_l2") K.«attempt_l2» :=
  «gbody_attempt_l2» «gb_attempt_l1»

/-- The body of `attempt_l3` alone (AST line 33879, guard `WorldOK`, loop-free). Its direct callees are
exactly `attempt_l2` (`«callees_attempt_l3»`, checked against the AST). Hypotheses: the bound
of each of these 1 callees, then the contract of each callee at a guard-carrying
call site (0: none). Nothing else is assumed. -/
def GBody.«attempt_l3» : Prop :=
  (TerminatingFunBoundedOn WorldOK (ofString "attempt_l2") K.«attempt_l2») →
  TerminatingFunBoundedOn WorldOK (ofString "attempt_l3") K.«attempt_l3»

/-- The direct callees of `attempt_l3`, read off its AST body (revision 6). -/
theorem «callees_attempt_l3» : sameNames (progCallees (fnBody Guest.Software.guestFn_attempt_l3))
    ["attempt_l2"] = true := by decide

theorem «lookup_attempt_l3» : originalRuntimeCode.lookup (ofString "attempt_l3") =
    some ((sourceFunctionEntry Guest.Software.guestFn_attempt_l3).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 882 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_attempt_l3) rfl

/-- PROVED by concrete-body composition (no longer a primitive). -/
theorem «gbody_attempt_l3» : GBody.«attempt_l3» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l3», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l3, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (LocalsOnly.of_localsFree localsFree_worldOK) _ (by simp) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 worldOK_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _ (callEntryOn_of_localsFree localsFree_worldOK _ _))
        worldOK_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l3»; omega

theorem «gb_attempt_l3» : TerminatingFunBoundedOn WorldOK (ofString "attempt_l3") K.«attempt_l3» :=
  «gbody_attempt_l3» «gb_attempt_l2»

/-- The body of `attempt_l4` alone (AST line 33895, guard `WorldOK`, loop-free). Its direct callees are
exactly `attempt_l3` (`«callees_attempt_l4»`, checked against the AST). Hypotheses: the bound
of each of these 1 callees, then the contract of each callee at a guard-carrying
call site (0: none). Nothing else is assumed. -/
def GBody.«attempt_l4» : Prop :=
  (TerminatingFunBoundedOn WorldOK (ofString "attempt_l3") K.«attempt_l3») →
  TerminatingFunBoundedOn WorldOK (ofString "attempt_l4") K.«attempt_l4»

/-- The direct callees of `attempt_l4`, read off its AST body (revision 6). -/
theorem «callees_attempt_l4» : sameNames (progCallees (fnBody Guest.Software.guestFn_attempt_l4))
    ["attempt_l3"] = true := by decide

theorem «lookup_attempt_l4» : originalRuntimeCode.lookup (ofString "attempt_l4") =
    some ((sourceFunctionEntry Guest.Software.guestFn_attempt_l4).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 883 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_attempt_l4) rfl

/-- PROVED by concrete-body composition (no longer a primitive). -/
theorem «gbody_attempt_l4» : GBody.«attempt_l4» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l4», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l4, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (LocalsOnly.of_localsFree localsFree_worldOK) _ (by simp) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 worldOK_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _ (callEntryOn_of_localsFree localsFree_worldOK _ _))
        worldOK_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l4»; omega

theorem «gb_attempt_l4» : TerminatingFunBoundedOn WorldOK (ofString "attempt_l4") K.«attempt_l4» :=
  «gbody_attempt_l4» «gb_attempt_l3»

/-- The body of `attempt_l5` alone (AST line 33911, guard `WorldOK`, loop-free). Its direct callees are
exactly `attempt_l4` (`«callees_attempt_l5»`, checked against the AST). Hypotheses: the bound
of each of these 1 callees, then the contract of each callee at a guard-carrying
call site (0: none). Nothing else is assumed. -/
def GBody.«attempt_l5» : Prop :=
  (TerminatingFunBoundedOn WorldOK (ofString "attempt_l4") K.«attempt_l4») →
  TerminatingFunBoundedOn WorldOK (ofString "attempt_l5") K.«attempt_l5»

/-- The direct callees of `attempt_l5`, read off its AST body (revision 6). -/
theorem «callees_attempt_l5» : sameNames (progCallees (fnBody Guest.Software.guestFn_attempt_l5))
    ["attempt_l4"] = true := by decide

theorem «lookup_attempt_l5» : originalRuntimeCode.lookup (ofString "attempt_l5") =
    some ((sourceFunctionEntry Guest.Software.guestFn_attempt_l5).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 884 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_attempt_l5) rfl

/-- PROVED by concrete-body composition (no longer a primitive). -/
theorem «gbody_attempt_l5» : GBody.«attempt_l5» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l5», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l5, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (LocalsOnly.of_localsFree localsFree_worldOK) _ (by simp) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 worldOK_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _ (callEntryOn_of_localsFree localsFree_worldOK _ _))
        worldOK_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l5»; omega

theorem «gb_attempt_l5» : TerminatingFunBoundedOn WorldOK (ofString "attempt_l5") K.«attempt_l5» :=
  «gbody_attempt_l5» «gb_attempt_l4»

/-- The body of `attempt_l6` alone (AST line 33927, guard `WorldOK`, loop-free). Its direct callees are
exactly `attempt_l5` (`«callees_attempt_l6»`, checked against the AST). Hypotheses: the bound
of each of these 1 callees, then the contract of each callee at a guard-carrying
call site (0: none). Nothing else is assumed. -/
def GBody.«attempt_l6» : Prop :=
  (TerminatingFunBoundedOn WorldOK (ofString "attempt_l5") K.«attempt_l5») →
  TerminatingFunBoundedOn WorldOK (ofString "attempt_l6") K.«attempt_l6»

/-- The direct callees of `attempt_l6`, read off its AST body (revision 6). -/
theorem «callees_attempt_l6» : sameNames (progCallees (fnBody Guest.Software.guestFn_attempt_l6))
    ["attempt_l5"] = true := by decide

theorem «lookup_attempt_l6» : originalRuntimeCode.lookup (ofString "attempt_l6") =
    some ((sourceFunctionEntry Guest.Software.guestFn_attempt_l6).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 885 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_attempt_l6) rfl

/-- PROVED by concrete-body composition (no longer a primitive). -/
theorem «gbody_attempt_l6» : GBody.«attempt_l6» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l6», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l6, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (LocalsOnly.of_localsFree localsFree_worldOK) _ (by simp) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 worldOK_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _ (callEntryOn_of_localsFree localsFree_worldOK _ _))
        worldOK_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l6»; omega

theorem «gb_attempt_l6» : TerminatingFunBoundedOn WorldOK (ofString "attempt_l6") K.«attempt_l6» :=
  «gbody_attempt_l6» «gb_attempt_l5»

/-- The body of `attempt_l7` alone (AST line 33943, guard `WorldOK`, loop-free). Its direct callees are
exactly `attempt_l6` (`«callees_attempt_l7»`, checked against the AST). Hypotheses: the bound
of each of these 1 callees, then the contract of each callee at a guard-carrying
call site (0: none). Nothing else is assumed. -/
def GBody.«attempt_l7» : Prop :=
  (TerminatingFunBoundedOn WorldOK (ofString "attempt_l6") K.«attempt_l6») →
  TerminatingFunBoundedOn WorldOK (ofString "attempt_l7") K.«attempt_l7»

/-- The direct callees of `attempt_l7`, read off its AST body (revision 6). -/
theorem «callees_attempt_l7» : sameNames (progCallees (fnBody Guest.Software.guestFn_attempt_l7))
    ["attempt_l6"] = true := by decide

theorem «lookup_attempt_l7» : originalRuntimeCode.lookup (ofString "attempt_l7") =
    some ((sourceFunctionEntry Guest.Software.guestFn_attempt_l7).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 886 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_attempt_l7) rfl

/-- PROVED by concrete-body composition (no longer a primitive). -/
theorem «gbody_attempt_l7» : GBody.«attempt_l7» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l7», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l7, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (LocalsOnly.of_localsFree localsFree_worldOK) _ (by simp) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 worldOK_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _ (callEntryOn_of_localsFree localsFree_worldOK _ _))
        worldOK_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l7»; omega

theorem «gb_attempt_l7» : TerminatingFunBoundedOn WorldOK (ofString "attempt_l7") K.«attempt_l7» :=
  «gbody_attempt_l7» «gb_attempt_l6»

/-- The body of `verify_stateless_new_payload` alone (AST line 33959, guard `WorldOK`, loop-free). Its direct callees are
exactly `attempt_l7` (`«callees_verify_stateless_new_payload»`, checked against the AST). Hypotheses: the bound
of each of these 1 callees, then the contract of each callee at a guard-carrying
call site (0: none). Nothing else is assumed. -/
def GBody.«verify_stateless_new_payload» : Prop :=
  (TerminatingFunBoundedOn WorldOK (ofString "attempt_l7") K.«attempt_l7») →
  TerminatingFunBoundedOn WorldOK (ofString "verify_stateless_new_payload") K.«verify_stateless_new_payload»

/-- The direct callees of `verify_stateless_new_payload`, read off its AST body (revision 6). -/
theorem «callees_verify_stateless_new_payload» : sameNames (progCallees (fnBody Guest.Software.guestFn_verify_stateless_new_payload))
    ["attempt_l7"] = true := by decide

theorem «lookup_verify_stateless_new_payload» : originalRuntimeCode.lookup (ofString "verify_stateless_new_payload") =
    some ((sourceFunctionEntry Guest.Software.guestFn_verify_stateless_new_payload).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 887 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_verify_stateless_new_payload) rfl

/-- PROVED by concrete-body composition (no longer a primitive). -/
theorem «gbody_verify_stateless_new_payload» : GBody.«verify_stateless_new_payload» := by
  intro h1
  refine ⟨_, _, _, «lookup_verify_stateless_new_payload», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_verify_stateless_new_payload, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (LocalsOnly.of_localsFree localsFree_worldOK) _ (by simp) _ _
      (TerminatingProgBoundedOn.dec_onLocals (LocalsOnly.of_localsFree localsFree_worldOK) _ (by simp) _ _
        (TerminatingProgBoundedOn.seq_guestInv_after
          (TerminatingProgBoundedOn.callHandle_on h1 worldOK_guestInv _ _ _
            (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_assign s _ _ _)
              (fun s => clock_assign s _ _ _))) _ (callEntryOn_of_localsFree localsFree_worldOK _ _))
          worldOK_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))))) ?_
  unfold K.«verify_stateless_new_payload»; omega

theorem «gb_verify_stateless_new_payload» : TerminatingFunBoundedOn WorldOK (ofString "verify_stateless_new_payload") K.«verify_stateless_new_payload» :=
  «gbody_verify_stateless_new_payload» «gb_attempt_l7»

/-- The body of `main` alone (AST line 33979, guard `MainEntry`, loop-free). Its direct callees are
exactly `alloc`, `blake2_init`, `bls_precompiles_init`, `bn254_init`, `decode_host_input`, `evm_init`, `fork_init`, `header_init`, `htr_new_payload_request`, `keccak_init`, `mem_init`, `memzero`, `mpt_init`, `output_write`, `ripemd160_init`, `secp256k1_init`, `serialize_result`, `sha256_init`, `ssz_init`, `u256_ws_init`, `verify_stateless_new_payload` (`«callees_main»`, checked against the AST). Hypotheses: the bound
of each of these 21 callees, then the contract of each callee at a guard-carrying
call site (18: `ww_alloc`, `ww_blake2_init`, `ww_bls_precompiles_init`, `ww_bn254_init`, `wk_decode_host_input`, `ww_evm_init`, `ww_fork_init`, `ww_header_init`, `ww_htr_new_payload_request`, `ww_keccak_init`, `mem_init_world`, `ww_memzero`, `ww_mpt_init`, `ww_ripemd160_init`, `ro_secp256k1_init`, `ww_sha256_init`, `ww_ssz_init`, `ww_u256_ws_init`). Nothing else is assumed. -/
def GBody.«main» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
  (TerminatingFunBoundedOn GuestInv (ofString "blake2_init") K.«blake2_init») →
  (TerminatingFunBoundedOn GuestInv (ofString "bls_precompiles_init") K.«bls_precompiles_init») →
  (TerminatingFunBoundedOn GuestInv (ofString "bn254_init") K.«bn254_init») →
  (TerminatingFunBoundedOn GuestInv (ofString "decode_host_input") K.«decode_host_input») →
  (TerminatingFunBoundedOn GuestInv (ofString "evm_init") K.«evm_init») →
  (TerminatingFunBoundedOn GuestInv (ofString "fork_init") K.«fork_init») →
  (TerminatingFunBoundedOn GuestInv (ofString "header_init") K.«header_init») →
  (TerminatingFunBoundedOn GuestInv (ofString "htr_new_payload_request") K.«htr_new_payload_request») →
  (TerminatingFunBoundedOn GuestInv (ofString "keccak_init") K.«keccak_init») →
  (TerminatingFunBoundedOn GuestInv (ofString "mem_init") K.«mem_init») →
  (TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero») →
  (TerminatingFunBoundedOn GuestInv (ofString "mpt_init") K.«mpt_init») →
  (TerminatingFunBoundedOn GuestInv (ofString "output_write") K.«output_write») →
  (TerminatingFunBoundedOn GuestInv (ofString "ripemd160_init") K.«ripemd160_init») →
  (TerminatingFunBoundedOn GuestInv (ofString "secp256k1_init") K.«secp256k1_init») →
  (TerminatingFunBoundedOn GuestInv (ofString "serialize_result") K.«serialize_result») →
  (TerminatingFunBoundedOn GuestInv (ofString "sha256_init") K.«sha256_init») →
  (TerminatingFunBoundedOn GuestInv (ofString "ssz_init") K.«ssz_init») →
  (TerminatingFunBoundedOn GuestInv (ofString "u256_ws_init") K.«u256_ws_init») →
  (TerminatingFunBoundedOn WorldOK (ofString "verify_stateless_new_payload") K.«verify_stateless_new_payload») →
  (WritesWithin (fun s => [])
    ["heap_ptr"] (ofString "alloc")) →
  (WritesWithin (fun s => [(globN s "b2_iv", 64), (globN s "b2_sigma", 80)])
    ["b2_iv", "b2_sigma", "b2_v", "heap_ptr"] (ofString "blake2_init")) →
  (WritesWithin (fun s => [(globN s "bls_c", 7136), (globN s "bls_discount", 2048)])
    ["bls_c", "bls_discount", "heap_ptr"] (ofString "bls_precompiles_init")) →
  (WritesWithin (fun s => [(globN s "bn_expw", 352), (globN s "bn_gamma", 384)])
    ["bn_expw", "bn_gamma", "heap_ptr"] (ofString "bn254_init")) →
  (KeepsOn WorldOK WorldOK (ofString "decode_host_input")) →
  (WritesWithin (fun s => [(globN s "evm_empty", 8), (globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "null_address", 24), (globN s "transfer_topic", 32), (globN s "vm_system_address", 24)])
    ["evm_empty", "evm_key_buf", "heap_ptr", "null_address", "pre_hdr_buf", "transfer_topic", "vm_system_address"] (ofString "evm_init")) →
  (WritesWithin (fun s => [(globN s "beacon_roots_address", 24), (globN s "builder_deposit_address", 24), (globN s "builder_exit_address", 24), (globN s "consolidation_request_address", 24), (globN s "deposit_contract_address", 24), (globN s "deposit_event_signature_hash", 32), (globN s "history_storage_address", 24), (globN s "precompile_addrs", 360), (globN s "withdrawal_request_address", 24), (globN s "zero32", 32)])
    ["beacon_roots_address", "builder_deposit_address", "builder_exit_address", "consolidation_request_address", "deposit_contract_address", "deposit_event_signature_hash", "heap_ptr", "history_storage_address", "precompile_addrs", "withdrawal_request_address", "zero32"] (ofString "fork_init")) →
  (WritesWithin (fun s => [(globN s "hdr_zero8", 8)])
    ["hdr_zero8", "heap_ptr"] (ofString "header_init")) →
  (WritesWithin (fun s => [(locN s "out", 32), (globN s "ssz_len_chunk", 32)])
    ["heap_ptr"] (ofString "htr_new_payload_request")) →
  (WritesWithin (fun s => [(globN s "keccak_rc", 192)])
    ["heap_ptr", "keccak_pad", "keccak_rc", "keccak_st"] (ofString "keccak_init")) →
  (type_of% @mem_init_world) →
  (WritesWithin (fun s => [(locN s "dst", locN s "n")])
    [] (ofString "memzero")) →
  (WritesWithin (fun s => [(globN s "empty_code_hash", 32), (globN s "empty_trie_root", 32), (globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_hash_scratch", 40)])
    ["empty_code_hash", "empty_trie_root", "heap_ptr", "mpt_hash_scratch", "mpt_key_scratch", "mpt_nib_scratch"] (ofString "mpt_init")) →
  (WritesWithin (fun s => [(globN s "rmd_tab", 160)])
    ["heap_ptr", "rmd_h", "rmd_pad", "rmd_tab", "rmd_x"] (ofString "ripemd160_init")) →
  (ReadOnlyFn (ofString "secp256k1_init")) →
  (WritesWithin (fun s => [])
    ["heap_ptr", "sha_pad", "sha_st"] (ofString "sha256_init")) →
  (WritesWithin (fun s => [(globN s "zero_hashes", 2048)])
    ["heap_ptr", "ssz_len_chunk", "ssz_offs", "zero_hashes"] (ofString "ssz_init")) →
  (WritesWithin (fun s => [])
    ["heap_ptr", "u256_ws"] (ofString "u256_ws_init")) →
  TerminatingFunBoundedOn MainEntry (ofString "main") K.«main»

/-- The direct callees of `main`, read off its AST body (revision 6). -/
theorem «callees_main» : sameNames (progCallees (fnBody Guest.Software.guestFn_main))
    ["alloc", "blake2_init", "bls_precompiles_init", "bn254_init", "decode_host_input", "evm_init", "fork_init", "header_init", "htr_new_payload_request", "keccak_init", "mem_init", "memzero", "mpt_init", "output_write", "ripemd160_init", "secp256k1_init", "serialize_result", "sha256_init", "ssz_init", "u256_ws_init", "verify_stateless_new_payload"] = true := by decide

theorem «gbody_main» : GBody.«main» := by sorry

theorem «gb_main» : TerminatingFunBoundedOn MainEntry (ofString "main") K.«main» :=
  «gbody_main» «fb_alloc» «fb_blake2_init» «fb_bls_precompiles_init» «fb_bn254_init» «fb_decode_host_input» «fb_evm_init» «fb_fork_init» «fb_header_init» «fb_htr_new_payload_request» «fb_keccak_init» «fb_mem_init» «fb_memzero» «fb_mpt_init» «fb_output_write» «fb_ripemd160_init» «fb_secp256k1_init» «fb_serialize_result» «fb_sha256_init» «fb_ssz_init» «fb_u256_ws_init» «gb_verify_stateless_new_payload» «ww_alloc» «ww_blake2_init» «ww_bls_precompiles_init» «ww_bn254_init» «wk_decode_host_input» «ww_evm_init» «ww_fork_init» «ww_header_init» «ww_htr_new_payload_request» «ww_keccak_init» «mem_init_world» «ww_memzero» «ww_mpt_init» «ww_ripemd160_init» «ro_secp256k1_init» «ww_sha256_init» «ww_ssz_init» «ww_u256_ws_init»

/-! #### Assembly (PROVED): the primitive obligations imply `main`'s guarded bound -/

/-- Every primitive obligation the guarded compositions use: the `fb_*` bounds of the
unguarded callees of guarded functions, the §7 contract leaves, the generated callee
contracts and the `gbody_*` composition obligations. -/
structure Primitives : Prop where
  «fb__decode_step» : TerminatingFunBoundedOn GuestInv (ofString "_decode_step") K.«_decode_step»
  «fb__resolve_step» : TerminatingFunBoundedOn GuestInv (ofString "_resolve_step") K.«_resolve_step»
  «fb_mpt_fail» : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail»
  «fb_node_new_ext» : TerminatingFunBoundedOn GuestInv (ofString "node_new_ext") K.«node_new_ext»
  «fb_rlp_item» : TerminatingFunBoundedOn GuestInv (ofString "rlp_item") K.«rlp_item»
  «ak__decode_step» : KeepsOn ArenaReady ArenaReady (ofString "_decode_step")
  «ww__resolve_step» : WritesWithin (fun s => [])     ["heap_ptr", "scratch_ptr"] (ofString "_resolve_step")
  «ro_mpt_fail» : ReadOnlyFn (ofString "mpt_fail")
  «ww_node_new_ext» : WritesWithin (fun s => [])     ["heap_ptr"] (ofString "node_new_ext")
  «ww_rlp_item» : WritesWithin (fun s => [])     ["scratch_ptr"] (ofString "rlp_item")
  «gbody__decode_witness_node_body» : GBody.«_decode_witness_node_body»
  «fb_scratch_release» : TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release»
  «fb_scratch_mark» : TerminatingFunBoundedOn GuestInv (ofString "scratch_mark") K.«scratch_mark»
  «ro_scratch_mark» : ReadOnlyFn (ofString "scratch_mark")
  «fb__collapse_branch» : TerminatingFunBoundedOn GuestInv (ofString "_collapse_branch") K.«_collapse_branch»
  «fb__delete_ext_finish» : TerminatingFunBoundedOn GuestInv (ofString "_delete_ext_finish") K.«_delete_ext_finish»
  «fb_common_prefix_length» : TerminatingFunBoundedOn GuestInv (ofString "common_prefix_length") K.«common_prefix_length»
  «fb_memeq» : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»
  «fb_node_invalidate» : TerminatingFunBoundedOn GuestInv (ofString "node_invalidate") K.«node_invalidate»
  «fb_scratch_alloc» : TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc»
  «nf__collapse_branch» : NodeFn ["node"]     (fun s Nd =>       NodeKind s Nd "node" 3)     (ofString "_collapse_branch")
  «nf__delete_ext_finish» : NodeFn ["node", "nc"]     (fun s Nd =>       NodeKind s Nd "node" 2 ∧ KeyIn s Nd (locN s "seg") (locN s "sl"))     (ofString "_delete_ext_finish")
  «ro_common_prefix_length» : ReadOnlyFn (ofString "common_prefix_length")
  «rv_common_prefix_length» : RetLe (fun s => min (locN s "al") (locN s "bl")) (ofString "common_prefix_length")
  «ro_memeq» : ReadOnlyFn (ofString "memeq")
  «nf_node_invalidate» : NodeFn ["nd"]     (fun _ _ => True)     (ofString "node_invalidate")
  «ww_scratch_alloc» : WritesWithin (fun s => [])     ["scratch_ptr"] (ofString "scratch_alloc")
  «gbody__mpt_delete_node_body» : GBody.«_mpt_delete_node_body»
  «gbody__mpt_delete_node» : GBody.«_mpt_delete_node»
  «fb__insert_into_leaf» : TerminatingFunBoundedOn GuestInv (ofString "_insert_into_leaf") K.«_insert_into_leaf»
  «fb__split_extension» : TerminatingFunBoundedOn GuestInv (ofString "_split_extension") K.«_split_extension»
  «fb_node_new_leaf» : TerminatingFunBoundedOn GuestInv (ofString "node_new_leaf") K.«node_new_leaf»
  «nf__insert_into_leaf» : NodeFn ["node"]     (fun s Nd =>       NodeKind s Nd "node" 1 ∧ KeyIn s Nd (locN s "rk") (locN s "rl"))     (ofString "_insert_into_leaf")
  «nf__split_extension» : NodeFn ["node"]     (fun s Nd =>       NodeKind s Nd "node" 2 ∧ KeyIn s Nd (locN s "rk") (locN s "rl") ∧       locN s "pl" < memW s (locN s "node" + 40) ∧ locN s "pl" ≤ locN s "rl")     (ofString "_split_extension")
  «nf_node_new_ext» : NodeFn ["child"]     (fun s Nd =>       KeyIn s Nd (locN s "nib") (locN s "nlen"))     (ofString "node_new_ext")
  «nf_node_new_leaf» : NodeFn []     (fun s Nd =>       KeyIn s Nd (locN s "nib") (locN s "nlen"))     (ofString "node_new_leaf")
  «gbody__mpt_insert_node» : GBody.«_mpt_insert_node»
  «fb_mpt_nibble_key» : TerminatingFunBoundedOn GuestInv (ofString "mpt_nibble_key") K.«mpt_nibble_key»
  «ww_mpt_nibble_key» : WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_hash_scratch", 40)])     ["heap_ptr"] (ofString "mpt_nibble_key")
  «nk_mpt_nibble_key» : RetNibbles (ofString "mpt_nibble_key")
  «gbody_mpt_set» : GBody.«mpt_set»
  «fb_heap_mark» : TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark»
  «fb_heap_release» : TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release»
  «fb_mpt_new» : TerminatingFunBoundedOn GuestInv (ofString "mpt_new") K.«mpt_new»
  «fb_mpt_root» : TerminatingFunBoundedOn GuestInv (ofString "mpt_root") K.«mpt_root»
  «fb_rlp_encode_word» : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_word") K.«rlp_encode_word»
  «ro_heap_mark» : ReadOnlyFn (ofString "heap_mark")
  «ww_mpt_new» : WritesWithin (fun s => [])     ["heap_ptr"] (ofString "mpt_new")
  «wk_mpt_set» : KeepsOn MptObjReady WorldOK (ofString "mpt_set")
  «ww_rlp_encode_word» : WritesWithin (fun s => [(locN s "dst", 33)])     [] (ofString "rlp_encode_word")
  «gbody_build_mpt_indexed» : GBody.«build_mpt_indexed»
  «fb_alloc» : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»
  «fb_memcpy» : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»
  «fb_nodedb_lookup» : TerminatingFunBoundedOn GuestInv (ofString "nodedb_lookup") K.«nodedb_lookup»
  «ro_nodedb_lookup» : ReadOnlyFn (ofString "nodedb_lookup")
  «fb_cache_get_root» : TerminatingFunBoundedOn GuestInv (ofString "cache_get_root") K.«cache_get_root»
  «fb_encode_account» : TerminatingFunBoundedOn GuestInv (ofString "encode_account") K.«encode_account»
  «fb_htab_copy» : TerminatingFunBoundedOn GuestInv (ofString "htab_copy") K.«htab_copy»
  «fb_htab_get» : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get»
  «fb_htab_has» : TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.«htab_has»
  «fb_htab_item» : TerminatingFunBoundedOn GuestInv (ofString "htab_item") K.«htab_item»
  «fb_htab_new» : TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new»
  «fb_htab_set» : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set»
  «fb_rlp_encode_bytes» : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.«rlp_encode_bytes»
  «fb_u256_is_zero» : TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero»
  «fb_u256_to_be_min» : TerminatingFunBoundedOn GuestInv (ofString "u256_to_be_min") K.«u256_to_be_min»
  «fb_ws_get_account_optional» : TerminatingFunBoundedOn GuestInv (ofString "ws_get_account_optional") K.«ws_get_account_optional»
  «fb_ws_storage_root_of» : TerminatingFunBoundedOn GuestInv (ofString "ws_storage_root_of") K.«ws_storage_root_of»
  «ww_alloc» : WritesWithin (fun s => [])     ["heap_ptr"] (ofString "alloc")
  «ww_cache_get_root» : WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_nib_scratch", 64)])     ["heap_ptr", "scratch_ptr"] (ofString "cache_get_root")
  «ww_encode_account» : WritesWithin (fun s => [(locN s "out", 110), (globN s "mpt_hash_scratch", 40)])     [] (ofString "encode_account")
  «ww_htab_copy» : WritesWithin (fun s => [])     ["heap_ptr"] (ofString "htab_copy")
  «ro_htab_get» : ReadOnlyFn (ofString "htab_get")
  «ro_htab_has» : ReadOnlyFn (ofString "htab_has")
  «ro_htab_item» : ReadOnlyFn (ofString "htab_item")
  «htab_new_spec» : type_of% @htab_new_spec
  «htab_set_spec» : type_of% @htab_set_spec
  «ww_memcpy» : WritesWithin (fun s => [(locN s "dst", locN s "n")])     [] (ofString "memcpy")
  «wk_mpt_from_witness» : KeepsOn WorldOK WorldOK (ofString "mpt_from_witness")
  «wk_mpt_root» : KeepsOn (MptObjAvoids (fun s => [(locN s "out", 32)])) WorldOK (ofString "mpt_root")
  «ww_rlp_encode_bytes» : WritesWithin (fun s => [(locN s "dst", locN s "n" + 9)])     [] (ofString "rlp_encode_bytes")
  «ro_u256_is_zero» : ReadOnlyFn (ofString "u256_is_zero")
  «ww_u256_to_be_min» : WritesWithin (fun s => [(locN s "out", 32)])     [] (ofString "u256_to_be_min")
  «ww_ws_get_account_optional» : WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_nib_scratch", 64)])     ["heap_ptr", "scratch_ptr"] (ofString "ws_get_account_optional")
  «ww_ws_storage_root_of» : WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_nib_scratch", 64)])     ["heap_ptr", "scratch_ptr"] (ofString "ws_storage_root_of")
  «gbody_compute_state_root» : GBody.«compute_state_root»
  «fb_keccak256» : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»
  «fb_rlp_decode_fully» : TerminatingFunBoundedOn GuestInv (ofString "rlp_decode_fully") K.«rlp_decode_fully»
  «fb_trie_lookup» : TerminatingFunBoundedOn GuestInv (ofString "trie_lookup") K.«trie_lookup»
  «fb_u256_from_be» : TerminatingFunBoundedOn GuestInv (ofString "u256_from_be") K.«u256_from_be»
  «gbody_ws_get_storage» : GBody.«ws_get_storage»
  «fb_record_pre_state_read» : TerminatingFunBoundedOn GuestInv (ofString "record_pre_state_read") K.«record_pre_state_read»
  «fb_stor_lookup» : TerminatingFunBoundedOn GuestInv (ofString "stor_lookup") K.«stor_lookup»
  «wk_record_pre_state_read» : KeepsOn WorldOK WorldOK (ofString "record_pre_state_read")
  «ro_stor_lookup» : ReadOnlyFn (ofString "stor_lookup")
  «fb_st_le64» : TerminatingFunBoundedOn GuestInv (ofString "st_le64") K.«st_le64»
  «ww_st_le64» : WritesWithin (fun s => [(locN s "p", 8)])     [] (ofString "st_le64")
  «gbody_idx_start_storage» : GBody.«idx_start_storage»
  «fb_add_balance_change» : TerminatingFunBoundedOn GuestInv (ofString "add_balance_change") K.«add_balance_change»
  «fb_add_code_change» : TerminatingFunBoundedOn GuestInv (ofString "add_code_change") K.«add_code_change»
  «fb_add_nonce_change» : TerminatingFunBoundedOn GuestInv (ofString "add_nonce_change") K.«add_nonce_change»
  «fb_add_storage_write» : TerminatingFunBoundedOn GuestInv (ofString "add_storage_write") K.«add_storage_write»
  «fb_bal_remove_change» : TerminatingFunBoundedOn GuestInv (ofString "bal_remove_change") K.«bal_remove_change»
  «fb_get_code» : TerminatingFunBoundedOn GuestInv (ofString "get_code") K.«get_code»
  «fb_idx_start_account» : TerminatingFunBoundedOn GuestInv (ofString "idx_start_account") K.«idx_start_account»
  «fb_remove_storage_write» : TerminatingFunBoundedOn GuestInv (ofString "remove_storage_write") K.«remove_storage_write»
  «fb_u256_eq» : TerminatingFunBoundedOn GuestInv (ofString "u256_eq") K.«u256_eq»
  «wk_add_balance_change» : KeepsOn WorldOK WorldOK (ofString "add_balance_change")
  «wk_add_code_change» : KeepsOn WorldOK WorldOK (ofString "add_code_change")
  «wk_add_nonce_change» : KeepsOn WorldOK WorldOK (ofString "add_nonce_change")
  «wk_add_storage_write» : KeepsOn WorldOK WorldOK (ofString "add_storage_write")
  «wk_bal_remove_change» : KeepsOn WorldOK WorldOK (ofString "bal_remove_change")
  «wk_get_code» : KeepsOn WorldOK WorldOK (ofString "get_code")
  «wk_idx_start_account» : KeepsOn WorldOK WorldOK (ofString "idx_start_account")
  «wk_idx_start_storage» : KeepsOn WorldOK WorldOK (ofString "idx_start_storage")
  «wk_remove_storage_write» : KeepsOn WorldOK WorldOK (ofString "remove_storage_write")
  «ro_u256_eq» : ReadOnlyFn (ofString "u256_eq")
  «gbody_update_builder_from_tx» : GBody.«update_builder_from_tx»
  «fb_merge_tx_into_block» : TerminatingFunBoundedOn GuestInv (ofString "merge_tx_into_block") K.«merge_tx_into_block»
  «fb_htab_del» : TerminatingFunBoundedOn GuestInv (ofString "htab_del") K.«htab_del»
  «htab_del_spec» : type_of% @htab_del_spec
  «htab_del_progress_spec» : type_of% @htab_del_progress_spec
  «gbody_htab_truncate» : GBody.«htab_truncate»
  «htab_truncate_spec» : type_of% @htab_truncate_spec
  «gbody_rollback_child_access» : GBody.«rollback_child_access»
  «fb_address_to_u256» : TerminatingFunBoundedOn GuestInv (ofString "address_to_u256") K.«address_to_u256»
  «fb_create_finish» : TerminatingFunBoundedOn GuestInv (ofString "create_finish") K.«create_finish»
  «fb_credit_state_gas_refund» : TerminatingFunBoundedOn GuestInv (ofString "credit_state_gas_refund") K.«credit_state_gas_refund»
  «fb_frame_halt» : TerminatingFunBoundedOn GuestInv (ofString "frame_halt") K.«frame_halt»
  «fb_frame_mem_release» : TerminatingFunBoundedOn GuestInv (ofString "frame_mem_release") K.«frame_mem_release»
  «fb_incorporate_child_on_error» : TerminatingFunBoundedOn GuestInv (ofString "incorporate_child_on_error") K.«incorporate_child_on_error»
  «fb_incorporate_child_on_success» : TerminatingFunBoundedOn GuestInv (ofString "incorporate_child_on_success") K.«incorporate_child_on_success»
  «fb_min» : TerminatingFunBoundedOn GuestInv (ofString "min") K.«min»
  «fb_pc_add» : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add»
  «fb_refill_frame_state_gas» : TerminatingFunBoundedOn GuestInv (ofString "refill_frame_state_gas") K.«refill_frame_state_gas»
  «fb_set_retdata» : TerminatingFunBoundedOn GuestInv (ofString "set_retdata") K.«set_retdata»
  «fb_stack_push» : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push»
  «fb_state_restore» : TerminatingFunBoundedOn GuestInv (ofString "state_restore") K.«state_restore»
  «ek_create_finish» : KeepsOn EvmInv EvmInv (ofString "create_finish")
  «ek_frame_halt» : KeepsOn EvmInv EvmInv (ofString "frame_halt")
  «ek_refill_frame_state_gas» : KeepsOn EvmInv EvmInv (ofString "refill_frame_state_gas")
  «ek_state_restore» : KeepsOn EvmInv EvmInv (ofString "state_restore")
  «gbody_finish_child» : GBody.«finish_child»
  «fb_sk_make» : TerminatingFunBoundedOn GuestInv (ofString "sk_make") K.«sk_make»
  «ww_sk_make» : WritesWithin (fun s => [(globN s "sk_buf", 64)])     [] (ofString "sk_make")
  «gbody_get_storage» : GBody.«get_storage»
  «fb_charge_gas» : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»
  «fb_is_warm_storage_key» : TerminatingFunBoundedOn GuestInv (ofString "is_warm_storage_key") K.«is_warm_storage_key»
  «fb_stack_pop» : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»
  «fb_u256_to_be32» : TerminatingFunBoundedOn GuestInv (ofString "u256_to_be32") K.«u256_to_be32»
  «fb_warm_storage_key» : TerminatingFunBoundedOn GuestInv (ofString "warm_storage_key") K.«warm_storage_key»
  «ek_charge_gas» : KeepsOn EvmInv EvmInv (ofString "charge_gas")
  «ww_is_warm_storage_key» : WritesWithin (fun s => [(globN s "sk_buf", 64)])     [] (ofString "is_warm_storage_key")
  «ek_stack_pop» : KeepsOn EvmInv EvmInv (ofString "stack_pop")
  «ww_u256_to_be32» : WritesWithin (fun s => [(locN s "out", 32)])     [] (ofString "u256_to_be32")
  «ek_warm_storage_key» : KeepsOn EvmInv EvmInv (ofString "warm_storage_key")
  «gbody_op_sload» : GBody.«op_sload»
  «fb_charge_state_gas» : TerminatingFunBoundedOn GuestInv (ofString "charge_state_gas") K.«charge_state_gas»
  «fb_check_gas» : TerminatingFunBoundedOn GuestInv (ofString "check_gas") K.«check_gas»
  «fb_max» : TerminatingFunBoundedOn GuestInv (ofString "max") K.«max»
  «fb_require_not_static» : TerminatingFunBoundedOn GuestInv (ofString "require_not_static") K.«require_not_static»
  «fb_set_storage» : TerminatingFunBoundedOn GuestInv (ofString "set_storage") K.«set_storage»
  «ro_check_gas» : ReadOnlyFn (ofString "check_gas")
  «ek_get_storage_original» : KeepsOn EvmInv EvmInv (ofString "get_storage_original")
  «ro_max» : ReadOnlyFn (ofString "max")
  «ro_require_not_static» : ReadOnlyFn (ofString "require_not_static")
  «gbody_op_sstore» : GBody.«op_sstore»
  «fb_op_add» : TerminatingFunBoundedOn GuestInv (ofString "op_add") K.«op_add»
  «fb_op_addmod» : TerminatingFunBoundedOn GuestInv (ofString "op_addmod") K.«op_addmod»
  «fb_op_address» : TerminatingFunBoundedOn GuestInv (ofString "op_address") K.«op_address»
  «fb_op_and» : TerminatingFunBoundedOn GuestInv (ofString "op_and") K.«op_and»
  «fb_op_balance» : TerminatingFunBoundedOn GuestInv (ofString "op_balance") K.«op_balance»
  «fb_op_basefee» : TerminatingFunBoundedOn GuestInv (ofString "op_basefee") K.«op_basefee»
  «fb_op_blobbasefee» : TerminatingFunBoundedOn GuestInv (ofString "op_blobbasefee") K.«op_blobbasefee»
  «fb_op_blobhash» : TerminatingFunBoundedOn GuestInv (ofString "op_blobhash") K.«op_blobhash»
  «fb_op_blockhash» : TerminatingFunBoundedOn GuestInv (ofString "op_blockhash") K.«op_blockhash»
  «fb_op_byte» : TerminatingFunBoundedOn GuestInv (ofString "op_byte") K.«op_byte»
  «fb_op_call» : TerminatingFunBoundedOn GuestInv (ofString "op_call") K.«op_call»
  «fb_op_callcode» : TerminatingFunBoundedOn GuestInv (ofString "op_callcode") K.«op_callcode»
  «fb_op_calldatacopy» : TerminatingFunBoundedOn GuestInv (ofString "op_calldatacopy") K.«op_calldatacopy»
  «fb_op_calldataload» : TerminatingFunBoundedOn GuestInv (ofString "op_calldataload") K.«op_calldataload»
  «fb_op_calldatasize» : TerminatingFunBoundedOn GuestInv (ofString "op_calldatasize") K.«op_calldatasize»
  «fb_op_caller» : TerminatingFunBoundedOn GuestInv (ofString "op_caller") K.«op_caller»
  «fb_op_callvalue» : TerminatingFunBoundedOn GuestInv (ofString "op_callvalue") K.«op_callvalue»
  «fb_op_chainid» : TerminatingFunBoundedOn GuestInv (ofString "op_chainid") K.«op_chainid»
  «fb_op_clz» : TerminatingFunBoundedOn GuestInv (ofString "op_clz") K.«op_clz»
  «fb_op_codecopy» : TerminatingFunBoundedOn GuestInv (ofString "op_codecopy") K.«op_codecopy»
  «fb_op_codesize» : TerminatingFunBoundedOn GuestInv (ofString "op_codesize") K.«op_codesize»
  «fb_op_coinbase» : TerminatingFunBoundedOn GuestInv (ofString "op_coinbase") K.«op_coinbase»
  «fb_op_create» : TerminatingFunBoundedOn GuestInv (ofString "op_create") K.«op_create»
  «fb_op_create2» : TerminatingFunBoundedOn GuestInv (ofString "op_create2") K.«op_create2»
  «fb_op_delegatecall» : TerminatingFunBoundedOn GuestInv (ofString "op_delegatecall") K.«op_delegatecall»
  «fb_op_div» : TerminatingFunBoundedOn GuestInv (ofString "op_div") K.«op_div»
  «fb_op_dup» : TerminatingFunBoundedOn GuestInv (ofString "op_dup") K.«op_dup»
  «fb_op_dupn» : TerminatingFunBoundedOn GuestInv (ofString "op_dupn") K.«op_dupn»
  «fb_op_eq» : TerminatingFunBoundedOn GuestInv (ofString "op_eq") K.«op_eq»
  «fb_op_exchange» : TerminatingFunBoundedOn GuestInv (ofString "op_exchange") K.«op_exchange»
  «fb_op_exp» : TerminatingFunBoundedOn GuestInv (ofString "op_exp") K.«op_exp»
  «fb_op_extcodecopy» : TerminatingFunBoundedOn GuestInv (ofString "op_extcodecopy") K.«op_extcodecopy»
  «fb_op_extcodehash» : TerminatingFunBoundedOn GuestInv (ofString "op_extcodehash") K.«op_extcodehash»
  «fb_op_extcodesize» : TerminatingFunBoundedOn GuestInv (ofString "op_extcodesize") K.«op_extcodesize»
  «fb_op_gas» : TerminatingFunBoundedOn GuestInv (ofString "op_gas") K.«op_gas»
  «fb_op_gaslimit» : TerminatingFunBoundedOn GuestInv (ofString "op_gaslimit") K.«op_gaslimit»
  «fb_op_gasprice» : TerminatingFunBoundedOn GuestInv (ofString "op_gasprice") K.«op_gasprice»
  «fb_op_gt» : TerminatingFunBoundedOn GuestInv (ofString "op_gt") K.«op_gt»
  «fb_op_iszero» : TerminatingFunBoundedOn GuestInv (ofString "op_iszero") K.«op_iszero»
  «fb_op_jump» : TerminatingFunBoundedOn GuestInv (ofString "op_jump") K.«op_jump»
  «fb_op_jumpdest» : TerminatingFunBoundedOn GuestInv (ofString "op_jumpdest") K.«op_jumpdest»
  «fb_op_jumpi» : TerminatingFunBoundedOn GuestInv (ofString "op_jumpi") K.«op_jumpi»
  «fb_op_keccak» : TerminatingFunBoundedOn GuestInv (ofString "op_keccak") K.«op_keccak»
  «fb_op_log» : TerminatingFunBoundedOn GuestInv (ofString "op_log") K.«op_log»
  «fb_op_lt» : TerminatingFunBoundedOn GuestInv (ofString "op_lt") K.«op_lt»
  «fb_op_mcopy» : TerminatingFunBoundedOn GuestInv (ofString "op_mcopy") K.«op_mcopy»
  «fb_op_mload» : TerminatingFunBoundedOn GuestInv (ofString "op_mload") K.«op_mload»
  «fb_op_mod» : TerminatingFunBoundedOn GuestInv (ofString "op_mod") K.«op_mod»
  «fb_op_msize» : TerminatingFunBoundedOn GuestInv (ofString "op_msize") K.«op_msize»
  «fb_op_mstore» : TerminatingFunBoundedOn GuestInv (ofString "op_mstore") K.«op_mstore»
  «fb_op_mstore8» : TerminatingFunBoundedOn GuestInv (ofString "op_mstore8") K.«op_mstore8»
  «fb_op_mul» : TerminatingFunBoundedOn GuestInv (ofString "op_mul") K.«op_mul»
  «fb_op_mulmod» : TerminatingFunBoundedOn GuestInv (ofString "op_mulmod") K.«op_mulmod»
  «fb_op_not» : TerminatingFunBoundedOn GuestInv (ofString "op_not") K.«op_not»
  «fb_op_number» : TerminatingFunBoundedOn GuestInv (ofString "op_number") K.«op_number»
  «fb_op_or» : TerminatingFunBoundedOn GuestInv (ofString "op_or") K.«op_or»
  «fb_op_origin» : TerminatingFunBoundedOn GuestInv (ofString "op_origin") K.«op_origin»
  «fb_op_pc» : TerminatingFunBoundedOn GuestInv (ofString "op_pc") K.«op_pc»
  «fb_op_pop» : TerminatingFunBoundedOn GuestInv (ofString "op_pop") K.«op_pop»
  «fb_op_prevrandao» : TerminatingFunBoundedOn GuestInv (ofString "op_prevrandao") K.«op_prevrandao»
  «fb_op_push» : TerminatingFunBoundedOn GuestInv (ofString "op_push") K.«op_push»
  «fb_op_return» : TerminatingFunBoundedOn GuestInv (ofString "op_return") K.«op_return»
  «fb_op_returndatacopy» : TerminatingFunBoundedOn GuestInv (ofString "op_returndatacopy") K.«op_returndatacopy»
  «fb_op_returndatasize» : TerminatingFunBoundedOn GuestInv (ofString "op_returndatasize") K.«op_returndatasize»
  «fb_op_revert» : TerminatingFunBoundedOn GuestInv (ofString "op_revert") K.«op_revert»
  «fb_op_sar» : TerminatingFunBoundedOn GuestInv (ofString "op_sar") K.«op_sar»
  «fb_op_sdiv» : TerminatingFunBoundedOn GuestInv (ofString "op_sdiv") K.«op_sdiv»
  «fb_op_selfbalance» : TerminatingFunBoundedOn GuestInv (ofString "op_selfbalance") K.«op_selfbalance»
  «fb_op_selfdestruct» : TerminatingFunBoundedOn GuestInv (ofString "op_selfdestruct") K.«op_selfdestruct»
  «fb_op_sgt» : TerminatingFunBoundedOn GuestInv (ofString "op_sgt") K.«op_sgt»
  «fb_op_shl» : TerminatingFunBoundedOn GuestInv (ofString "op_shl") K.«op_shl»
  «fb_op_shr» : TerminatingFunBoundedOn GuestInv (ofString "op_shr") K.«op_shr»
  «fb_op_signextend» : TerminatingFunBoundedOn GuestInv (ofString "op_signextend") K.«op_signextend»
  «fb_op_slotnum» : TerminatingFunBoundedOn GuestInv (ofString "op_slotnum") K.«op_slotnum»
  «fb_op_slt» : TerminatingFunBoundedOn GuestInv (ofString "op_slt") K.«op_slt»
  «fb_op_smod» : TerminatingFunBoundedOn GuestInv (ofString "op_smod") K.«op_smod»
  «fb_op_staticcall» : TerminatingFunBoundedOn GuestInv (ofString "op_staticcall") K.«op_staticcall»
  «fb_op_stop» : TerminatingFunBoundedOn GuestInv (ofString "op_stop") K.«op_stop»
  «fb_op_sub» : TerminatingFunBoundedOn GuestInv (ofString "op_sub") K.«op_sub»
  «fb_op_swap» : TerminatingFunBoundedOn GuestInv (ofString "op_swap") K.«op_swap»
  «fb_op_swapn» : TerminatingFunBoundedOn GuestInv (ofString "op_swapn") K.«op_swapn»
  «fb_op_timestamp» : TerminatingFunBoundedOn GuestInv (ofString "op_timestamp") K.«op_timestamp»
  «fb_op_tload» : TerminatingFunBoundedOn GuestInv (ofString "op_tload") K.«op_tload»
  «fb_op_tstore» : TerminatingFunBoundedOn GuestInv (ofString "op_tstore") K.«op_tstore»
  «fb_op_xor» : TerminatingFunBoundedOn GuestInv (ofString "op_xor") K.«op_xor»
  «gbody_op_dispatch» : GBody.«op_dispatch»
  «fb_frame_epilogue» : TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.«frame_epilogue»
  «fb_frame_exception» : TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.«frame_exception»
  «finish_child_spec» : type_of% @finish_child_spec
  «frame_epilogue_spec» : type_of% @frame_epilogue_spec
  «frame_exception_spec» : type_of% @frame_exception_spec
  «op_dispatch_spec» : type_of% @op_dispatch_spec
  «gbody_run_frames» : GBody.«run_frames»
  «fb_depth0_prepare» : TerminatingFunBoundedOn GuestInv (ofString "depth0_prepare") K.«depth0_prepare»
  «fb_frame_open» : TerminatingFunBoundedOn GuestInv (ofString "frame_open") K.«frame_open»
  «fb_frame_start» : TerminatingFunBoundedOn GuestInv (ofString "frame_start") K.«frame_start»
  «fb_state_snapshot» : TerminatingFunBoundedOn GuestInv (ofString "state_snapshot") K.«state_snapshot»
  «ek_depth0_prepare» : KeepsOn EvmMsgReady EvmInv (ofString "depth0_prepare")
  «fk_frame_open» : KeepsOn FrameOpenReady EvmMsgReady (ofString "frame_open")
  «ek_frame_start» : KeepsOn EvmInv EvmInv (ofString "frame_start")
  «ro_state_snapshot» : ReadOnlyFn (ofString "state_snapshot")
  «gbody_process_message» : GBody.«process_message»
  «fb_destroy_storage» : TerminatingFunBoundedOn GuestInv (ofString "destroy_storage") K.«destroy_storage»
  «fb_increment_nonce» : TerminatingFunBoundedOn GuestInv (ofString "increment_nonce") K.«increment_nonce»
  «fb_mark_account_created» : TerminatingFunBoundedOn GuestInv (ofString "mark_account_created") K.«mark_account_created»
  «wk_destroy_storage» : KeepsOn WorldOK WorldOK (ofString "destroy_storage")
  «wk_increment_nonce» : KeepsOn WorldOK WorldOK (ofString "increment_nonce")
  «wk_mark_account_created» : KeepsOn WorldOK WorldOK (ofString "mark_account_created")
  «gbody_process_create_message» : GBody.«process_create_message»
  «fb_account_deployable» : TerminatingFunBoundedOn GuestInv (ofString "account_deployable") K.«account_deployable»
  «fb_frame_state_gas_used» : TerminatingFunBoundedOn GuestInv (ofString "frame_state_gas_used") K.«frame_state_gas_used»
  «fb_memzero» : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero»
  «wk_account_deployable» : KeepsOn WorldOK WorldOK (ofString "account_deployable")
  «ww_memzero» : WritesWithin (fun s => [(locN s "dst", locN s "n")])     [] (ofString "memzero")
  «gbody_process_message_call» : GBody.«process_message_call»
  «fb_ext_code_of» : TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.«ext_code_of»
  «fb_msg_new» : TerminatingFunBoundedOn GuestInv (ofString "msg_new") K.«msg_new»
  «fb_state_fresh_tx» : TerminatingFunBoundedOn GuestInv (ofString "state_fresh_tx") K.«state_fresh_tx»
  «fb_te_new» : TerminatingFunBoundedOn GuestInv (ofString "te_new") K.«te_new»
  «wk_ext_code_of» : KeepsOn WorldOK WorldOK (ofString "ext_code_of")
  «ww_msg_new» : WritesWithin (fun s => [])     ["heap_ptr"] (ofString "msg_new")
  «wk_process_message_call» : KeepsOn MsgReady WorldOK (ofString "process_message_call")
  «ww_state_fresh_tx» : WritesWithin (fun s => [(globN s "ts", 72)])     ["heap_ptr", "journal_n", "ts"] (ofString "state_fresh_tx")
  «ww_te_new» : WritesWithin (fun s => [])     ["heap_ptr"] (ofString "te_new")
  «gbody_process_unchecked_system_transaction» : GBody.«process_unchecked_system_transaction»
  «gbody_process_checked_system_transaction» : GBody.«process_checked_system_transaction»
  «fb_extract_deposit_data» : TerminatingFunBoundedOn GuestInv (ofString "extract_deposit_data") K.«extract_deposit_data»
  «fb_requests_append» : TerminatingFunBoundedOn GuestInv (ofString "requests_append") K.«requests_append»
  «ww_extract_deposit_data» : WritesWithin (fun s => [(locN s "out", 192)])     ["heap_ptr"] (ofString "extract_deposit_data")
  «wk_process_checked_system_transaction» : KeepsOn WorldOK WorldOK (ofString "process_checked_system_transaction")
  «wk_requests_append» : KeepsOn ReqRoom WorldOK (ofString "requests_append")
  «gbody_process_general_purpose_requests» : GBody.«process_general_purpose_requests»
  «fb_calculate_blob_gas_price» : TerminatingFunBoundedOn GuestInv (ofString "calculate_blob_gas_price") K.«calculate_blob_gas_price»
  «fb_calculate_total_blob_gas» : TerminatingFunBoundedOn GuestInv (ofString "calculate_total_blob_gas") K.«calculate_total_blob_gas»
  «fb_check_transaction» : TerminatingFunBoundedOn GuestInv (ofString "check_transaction") K.«check_transaction»
  «fb_clear_account_preserving_balance» : TerminatingFunBoundedOn GuestInv (ofString "clear_account_preserving_balance") K.«clear_account_preserving_balance»
  «fb_compute_contract_address» : TerminatingFunBoundedOn GuestInv (ofString "compute_contract_address") K.«compute_contract_address»
  «fb_create_ether» : TerminatingFunBoundedOn GuestInv (ofString "create_ether") K.«create_ether»
  «fb_encode_receipt» : TerminatingFunBoundedOn GuestInv (ofString "encode_receipt") K.«encode_receipt»
  «fb_encode_transaction» : TerminatingFunBoundedOn GuestInv (ofString "encode_transaction") K.«encode_transaction»
  «fb_fee_mul» : TerminatingFunBoundedOn GuestInv (ofString "fee_mul") K.«fee_mul»
  «fb_get_account» : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account»
  «fb_lst_new» : TerminatingFunBoundedOn GuestInv (ofString "lst_new") K.«lst_new»
  «fb_lst_push» : TerminatingFunBoundedOn GuestInv (ofString "lst_push") K.«lst_push»
  «fb_recover_sender_with_chain_id» : TerminatingFunBoundedOn GuestInv (ofString "recover_sender_with_chain_id") K.«recover_sender_with_chain_id»
  «fb_set_account_balance» : TerminatingFunBoundedOn GuestInv (ofString "set_account_balance") K.«set_account_balance»
  «fb_tx_chain_id» : TerminatingFunBoundedOn GuestInv (ofString "tx_chain_id") K.«tx_chain_id»
  «fb_tx_has_access_list» : TerminatingFunBoundedOn GuestInv (ofString "tx_has_access_list") K.«tx_has_access_list»
  «fb_tx_is_blob» : TerminatingFunBoundedOn GuestInv (ofString "tx_is_blob") K.«tx_is_blob»
  «fb_tx_is_setcode» : TerminatingFunBoundedOn GuestInv (ofString "tx_is_setcode") K.«tx_is_setcode»
  «fb_u256_sub» : TerminatingFunBoundedOn GuestInv (ofString "u256_sub") K.«u256_sub»
  «fb_udiv_small5» : TerminatingFunBoundedOn GuestInv (ofString "udiv_small5") K.«udiv_small5»
  «fb_validate_transaction» : TerminatingFunBoundedOn GuestInv (ofString "validate_transaction") K.«validate_transaction»
  «wk_calculate_blob_gas_price» : KeepsOn WorldOK WorldOK (ofString "calculate_blob_gas_price")
  «ro_calculate_total_blob_gas» : ReadOnlyFn (ofString "calculate_total_blob_gas")
  «wk_check_transaction» : KeepsOn WorldOK WorldOK (ofString "check_transaction")
  «wk_clear_account_preserving_balance» : KeepsOn WorldOK WorldOK (ofString "clear_account_preserving_balance")
  «ww_compute_contract_address» : WritesWithin (fun s => [(locN s "out", 20), (globN s "keccak_pad", 136), (globN s "keccak_st", 200)])     ["heap_ptr"] (ofString "compute_contract_address")
  «wk_create_ether» : KeepsOn WorldOK WorldOK (ofString "create_ether")
  «wk_encode_receipt» : KeepsOn WorldOK WorldOK (ofString "encode_receipt")
  «wk_encode_transaction» : KeepsOn WorldOK WorldOK (ofString "encode_transaction")
  «ro_fee_mul» : ReadOnlyFn (ofString "fee_mul")
  «wk_get_account» : KeepsOn WorldOK WorldOK (ofString "get_account")
  «ww_keccak256» : WritesWithin (fun s => [(locN s "out", 32), (globN s "keccak_pad", 136), (globN s "keccak_st", 200)])     [] (ofString "keccak256")
  «ww_lst_new» : WritesWithin (fun s => [])     ["heap_ptr"] (ofString "lst_new")
  «ww_lst_push» : WritesWithin (fun s => [(locN s "l", 24), (memW s (locN s "l"), locN s "esz" * memW s (locN s "l" + 16))])     ["heap_ptr"] (ofString "lst_push")
  «ro_min» : ReadOnlyFn (ofString "min")
  «ww_recover_sender_with_chain_id» : WritesWithin (fun s => [(locN s "out20", 20), (globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "u256_ws", 640)])     ["heap_ptr"] (ofString "recover_sender_with_chain_id")
  «wk_set_account_balance» : KeepsOn WorldOK WorldOK (ofString "set_account_balance")
  «ro_tx_chain_id» : ReadOnlyFn (ofString "tx_chain_id")
  «ro_tx_has_access_list» : ReadOnlyFn (ofString "tx_has_access_list")
  «ro_tx_is_blob» : ReadOnlyFn (ofString "tx_is_blob")
  «ro_tx_is_setcode» : ReadOnlyFn (ofString "tx_is_setcode")
  «ro_u256_sub» : ReadOnlyFn (ofString "u256_sub")
  «ro_udiv_small5» : ReadOnlyFn (ofString "udiv_small5")
  «ro_validate_transaction» : ReadOnlyFn (ofString "validate_transaction")
  «gbody_process_transaction» : GBody.«process_transaction»
  «fb_u256_mul» : TerminatingFunBoundedOn GuestInv (ofString "u256_mul") K.«u256_mul»
  «ro_u256_mul» : ReadOnlyFn (ofString "u256_mul")
  «gbody_process_withdrawals» : GBody.«process_withdrawals»
  «fb_bal_init» : TerminatingFunBoundedOn GuestInv (ofString "bal_init") K.«bal_init»
  «fb_build_block_access_list_rlp» : TerminatingFunBoundedOn GuestInv (ofString "build_block_access_list_rlp") K.«build_block_access_list_rlp»
  «fb_compute_requests_hash» : TerminatingFunBoundedOn GuestInv (ofString "compute_requests_hash") K.«compute_requests_hash»
  «fb_decode_transaction» : TerminatingFunBoundedOn GuestInv (ofString "decode_transaction") K.«decode_transaction»
  «fb_logs_bloom» : TerminatingFunBoundedOn GuestInv (ofString "logs_bloom") K.«logs_bloom»
  «fb_track_ancestor_access» : TerminatingFunBoundedOn GuestInv (ofString "track_ancestor_access") K.«track_ancestor_access»
  «fb_validate_block_access_list_gas_limit» : TerminatingFunBoundedOn GuestInv (ofString "validate_block_access_list_gas_limit") K.«validate_block_access_list_gas_limit»
  «ww_bal_init» : WritesWithin (fun s => [])     ["bal_accounts", "bal_idx_accts", "bal_idx_stor", "bal_index", "bal_key_buf", "heap_ptr"] (ofString "bal_init")
  «wk_build_block_access_list_rlp» : KeepsOn WorldOK WorldOK (ofString "build_block_access_list_rlp")
  «wk_build_mpt_indexed» : KeepsOn (WorldAvoids (fun s => [(locN s "out", 32)])) WorldOK (ofString "build_mpt_indexed")
  «wk_compute_state_root» : KeepsOn (WorldAvoids (fun s => [(locN s "out", 32)])) WorldOK (ofString "compute_state_root")
  «ww_decode_transaction» : WritesWithin (fun s => [])     ["heap_ptr", "scratch_ptr"] (ofString "decode_transaction")
  «ww_logs_bloom» : WritesWithin (fun s => [(locN s "out", 256), (globN s "keccak_pad", 136), (globN s "keccak_st", 200)])     ["heap_ptr"] (ofString "logs_bloom")
  «wk_process_general_purpose_requests» : KeepsOn ReqsFresh WorldOK (ofString "process_general_purpose_requests")
  «wk_process_transaction» : KeepsOn TxReady WorldOK (ofString "process_transaction")
  «wk_process_unchecked_system_transaction» : KeepsOn WorldOK WorldOK (ofString "process_unchecked_system_transaction")
  «wk_process_withdrawals» : KeepsOn WorldOK WorldOK (ofString "process_withdrawals")
  «ww_track_ancestor_access» : WritesWithin (fun s => [(globN s "bs", 80)])     [] (ofString "track_ancestor_access")
  «ro_validate_block_access_list_gas_limit» : ReadOnlyFn (ofString "validate_block_access_list_gas_limit")
  «gbody_execute_block» : GBody.«execute_block»
  «fb_block_rlp_length» : TerminatingFunBoundedOn GuestInv (ofString "block_rlp_length") K.«block_rlp_length»
  «fb_encode_execution_requests» : TerminatingFunBoundedOn GuestInv (ofString "encode_execution_requests") K.«encode_execution_requests»
  «fb_encode_withdrawal_rlp» : TerminatingFunBoundedOn GuestInv (ofString "encode_withdrawal_rlp") K.«encode_withdrawal_rlp»
  «wk_block_rlp_length» : KeepsOn WorldOK WorldOK (ofString "block_rlp_length")
  «wk_encode_withdrawal_rlp» : KeepsOn WorldOK WorldOK (ofString "encode_withdrawal_rlp")
  «gbody_payload_header» : GBody.«payload_header»
  «gbody_state_init» : GBody.«state_init»
  «fb_check_gas_limit» : TerminatingFunBoundedOn GuestInv (ofString "check_gas_limit") K.«check_gas_limit»
  «fb_header_hash» : TerminatingFunBoundedOn GuestInv (ofString "header_hash") K.«header_hash»
  «fb_is_valid_versioned_hashes» : TerminatingFunBoundedOn GuestInv (ofString "is_valid_versioned_hashes") K.«is_valid_versioned_hashes»
  «fb_nodedb_build» : TerminatingFunBoundedOn GuestInv (ofString "nodedb_build") K.«nodedb_build»
  «fb_validate_header» : TerminatingFunBoundedOn GuestInv (ofString "validate_header") K.«validate_header»
  «fb_validate_headers» : TerminatingFunBoundedOn GuestInv (ofString "validate_headers") K.«validate_headers»
  «ro_check_gas_limit» : ReadOnlyFn (ofString "check_gas_limit")
  «ww_header_hash» : WritesWithin (fun s => [(locN s "out", 32), (globN s "keccak_pad", 136), (globN s "keccak_st", 200)])     ["heap_ptr"] (ofString "header_hash")
  «ww_is_valid_versioned_hashes» : WritesWithin (fun s => [])     ["heap_ptr", "scratch_ptr"] (ofString "is_valid_versioned_hashes")
  «wk_nodedb_build» : KeepsOn WorldOK WorldOK (ofString "nodedb_build")
  «wk_payload_header» : KeepsOn WorldOK WorldOK (ofString "payload_header")
  «wk_state_init» : KeepsOn WorldOK WorldOK (ofString "state_init")
  «wk_validate_header» : KeepsOn WorldOK WorldOK (ofString "validate_header")
  «ww_validate_headers» : WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200)])     ["heap_ptr", "scratch_ptr"] (ofString "validate_headers")
  «gbody_run_attempt» : GBody.«run_attempt»
  «fb_blake2_init» : TerminatingFunBoundedOn GuestInv (ofString "blake2_init") K.«blake2_init»
  «fb_bls_precompiles_init» : TerminatingFunBoundedOn GuestInv (ofString "bls_precompiles_init") K.«bls_precompiles_init»
  «fb_bn254_init» : TerminatingFunBoundedOn GuestInv (ofString "bn254_init") K.«bn254_init»
  «fb_decode_host_input» : TerminatingFunBoundedOn GuestInv (ofString "decode_host_input") K.«decode_host_input»
  «fb_evm_init» : TerminatingFunBoundedOn GuestInv (ofString "evm_init") K.«evm_init»
  «fb_fork_init» : TerminatingFunBoundedOn GuestInv (ofString "fork_init") K.«fork_init»
  «fb_header_init» : TerminatingFunBoundedOn GuestInv (ofString "header_init") K.«header_init»
  «fb_htr_new_payload_request» : TerminatingFunBoundedOn GuestInv (ofString "htr_new_payload_request") K.«htr_new_payload_request»
  «fb_keccak_init» : TerminatingFunBoundedOn GuestInv (ofString "keccak_init") K.«keccak_init»
  «fb_mem_init» : TerminatingFunBoundedOn GuestInv (ofString "mem_init") K.«mem_init»
  «fb_mpt_init» : TerminatingFunBoundedOn GuestInv (ofString "mpt_init") K.«mpt_init»
  «fb_output_write» : TerminatingFunBoundedOn GuestInv (ofString "output_write") K.«output_write»
  «fb_ripemd160_init» : TerminatingFunBoundedOn GuestInv (ofString "ripemd160_init") K.«ripemd160_init»
  «fb_secp256k1_init» : TerminatingFunBoundedOn GuestInv (ofString "secp256k1_init") K.«secp256k1_init»
  «fb_serialize_result» : TerminatingFunBoundedOn GuestInv (ofString "serialize_result") K.«serialize_result»
  «fb_sha256_init» : TerminatingFunBoundedOn GuestInv (ofString "sha256_init") K.«sha256_init»
  «fb_ssz_init» : TerminatingFunBoundedOn GuestInv (ofString "ssz_init") K.«ssz_init»
  «fb_u256_ws_init» : TerminatingFunBoundedOn GuestInv (ofString "u256_ws_init") K.«u256_ws_init»
  «ww_blake2_init» : WritesWithin (fun s => [(globN s "b2_iv", 64), (globN s "b2_sigma", 80)])     ["b2_iv", "b2_sigma", "b2_v", "heap_ptr"] (ofString "blake2_init")
  «ww_bls_precompiles_init» : WritesWithin (fun s => [(globN s "bls_c", 7136), (globN s "bls_discount", 2048)])     ["bls_c", "bls_discount", "heap_ptr"] (ofString "bls_precompiles_init")
  «ww_bn254_init» : WritesWithin (fun s => [(globN s "bn_expw", 352), (globN s "bn_gamma", 384)])     ["bn_expw", "bn_gamma", "heap_ptr"] (ofString "bn254_init")
  «wk_decode_host_input» : KeepsOn WorldOK WorldOK (ofString "decode_host_input")
  «ww_evm_init» : WritesWithin (fun s => [(globN s "evm_empty", 8), (globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "null_address", 24), (globN s "transfer_topic", 32), (globN s "vm_system_address", 24)])     ["evm_empty", "evm_key_buf", "heap_ptr", "null_address", "pre_hdr_buf", "transfer_topic", "vm_system_address"] (ofString "evm_init")
  «ww_fork_init» : WritesWithin (fun s => [(globN s "beacon_roots_address", 24), (globN s "builder_deposit_address", 24), (globN s "builder_exit_address", 24), (globN s "consolidation_request_address", 24), (globN s "deposit_contract_address", 24), (globN s "deposit_event_signature_hash", 32), (globN s "history_storage_address", 24), (globN s "precompile_addrs", 360), (globN s "withdrawal_request_address", 24), (globN s "zero32", 32)])     ["beacon_roots_address", "builder_deposit_address", "builder_exit_address", "consolidation_request_address", "deposit_contract_address", "deposit_event_signature_hash", "heap_ptr", "history_storage_address", "precompile_addrs", "withdrawal_request_address", "zero32"] (ofString "fork_init")
  «ww_header_init» : WritesWithin (fun s => [(globN s "hdr_zero8", 8)])     ["hdr_zero8", "heap_ptr"] (ofString "header_init")
  «ww_htr_new_payload_request» : WritesWithin (fun s => [(locN s "out", 32), (globN s "ssz_len_chunk", 32)])     ["heap_ptr"] (ofString "htr_new_payload_request")
  «ww_keccak_init» : WritesWithin (fun s => [(globN s "keccak_rc", 192)])     ["heap_ptr", "keccak_pad", "keccak_rc", "keccak_st"] (ofString "keccak_init")
  «mem_init_world» : type_of% @mem_init_world
  «ww_mpt_init» : WritesWithin (fun s => [(globN s "empty_code_hash", 32), (globN s "empty_trie_root", 32), (globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_hash_scratch", 40)])     ["empty_code_hash", "empty_trie_root", "heap_ptr", "mpt_hash_scratch", "mpt_key_scratch", "mpt_nib_scratch"] (ofString "mpt_init")
  «ww_ripemd160_init» : WritesWithin (fun s => [(globN s "rmd_tab", 160)])     ["heap_ptr", "rmd_h", "rmd_pad", "rmd_tab", "rmd_x"] (ofString "ripemd160_init")
  «ro_secp256k1_init» : ReadOnlyFn (ofString "secp256k1_init")
  «ww_sha256_init» : WritesWithin (fun s => [])     ["heap_ptr", "sha_pad", "sha_st"] (ofString "sha256_init")
  «ww_ssz_init» : WritesWithin (fun s => [(globN s "zero_hashes", 2048)])     ["heap_ptr", "ssz_len_chunk", "ssz_offs", "zero_hashes"] (ofString "ssz_init")
  «ww_u256_ws_init» : WritesWithin (fun s => [])     ["heap_ptr", "u256_ws"] (ofString "u256_ws_init")
  «gbody_main» : GBody.«main»

theorem assembly_main (P : Primitives) :
    TerminatingFunBoundedOn MainEntry (ofString "main") K.«main» := by
  have «g__decode_witness_node_body» := P.«gbody__decode_witness_node_body» P.«fb__decode_step» P.«fb__resolve_step» P.«fb_mpt_fail» P.«fb_node_new_ext» P.«fb_rlp_item» P.«ak__decode_step» P.«ww__resolve_step» P.«ro_mpt_fail» P.«ww_node_new_ext» P.«ww_rlp_item»
  have «g__decode_witness_node_mpt» := «gbody__decode_witness_node_mpt» «g__decode_witness_node_body» P.«fb_scratch_release»
  have «g__decode_witness_node» := «gbody__decode_witness_node» «g__decode_witness_node_mpt» P.«fb_scratch_mark» P.«fb_scratch_release» P.«ro_scratch_mark»
  have «g__mpt_delete_node_body» := P.«gbody__mpt_delete_node_body» P.«fb__collapse_branch» P.«fb__delete_ext_finish» P.«fb_common_prefix_length» P.«fb_memeq» P.«fb_mpt_fail» P.«fb_node_invalidate» P.«fb_scratch_alloc» P.«nf__collapse_branch» P.«nf__delete_ext_finish» P.«ro_common_prefix_length» P.«rv_common_prefix_length» P.«ro_memeq» P.«ro_mpt_fail» P.«nf_node_invalidate» P.«ww_scratch_alloc»
  have «g__mpt_delete_node» := P.«gbody__mpt_delete_node» «g__mpt_delete_node_body» P.«fb_scratch_mark» P.«fb_scratch_release» P.«ro_scratch_mark»
  have «g__mpt_insert_node» := P.«gbody__mpt_insert_node» P.«fb__insert_into_leaf» P.«fb__split_extension» P.«fb_common_prefix_length» P.«fb_mpt_fail» P.«fb_node_invalidate» P.«fb_node_new_ext» P.«fb_node_new_leaf» P.«nf__insert_into_leaf» P.«nf__split_extension» P.«ro_common_prefix_length» P.«rv_common_prefix_length» P.«ro_mpt_fail» P.«nf_node_invalidate» P.«nf_node_new_ext» P.«nf_node_new_leaf»
  have «g_mpt_set» := P.«gbody_mpt_set» «g__mpt_delete_node» «g__mpt_insert_node» P.«fb_mpt_nibble_key» P.«ww_mpt_nibble_key» P.«nk_mpt_nibble_key»
  have «g_build_mpt_indexed» := P.«gbody_build_mpt_indexed» P.«fb_heap_mark» P.«fb_heap_release» P.«fb_mpt_new» P.«fb_mpt_root» «g_mpt_set» P.«fb_rlp_encode_word» P.«ro_heap_mark» P.«ww_mpt_new» P.«wk_mpt_set» P.«ww_rlp_encode_word»
  have «g_decode_witness_to_mpt» := «gbody_decode_witness_to_mpt» «g__decode_witness_node» P.«fb_alloc» P.«fb_memcpy» P.«fb_memeq» P.«fb_mpt_fail» P.«fb_nodedb_lookup» P.«ro_memeq» P.«ro_mpt_fail» P.«ro_nodedb_lookup»
  have «g_mpt_from_witness» := «gbody_mpt_from_witness» «g_decode_witness_to_mpt» P.«fb_mpt_new»
  have «g_compute_state_root» := P.«gbody_compute_state_root» P.«fb_alloc» P.«fb_cache_get_root» P.«fb_encode_account» P.«fb_htab_copy» P.«fb_htab_get» P.«fb_htab_has» P.«fb_htab_item» P.«fb_htab_new» P.«fb_htab_set» P.«fb_memcpy» «g_mpt_from_witness» P.«fb_mpt_root» «g_mpt_set» P.«fb_rlp_encode_bytes» P.«fb_u256_is_zero» P.«fb_u256_to_be_min» P.«fb_ws_get_account_optional» P.«fb_ws_storage_root_of» P.«ww_alloc» P.«ww_cache_get_root» P.«ww_encode_account» P.«ww_htab_copy» P.«ro_htab_get» P.«ro_htab_has» P.«ro_htab_item» P.«htab_new_spec» P.«htab_set_spec» P.«ww_memcpy» P.«wk_mpt_from_witness» P.«wk_mpt_root» P.«wk_mpt_set» P.«ww_rlp_encode_bytes» P.«ro_u256_is_zero» P.«ww_u256_to_be_min» P.«ww_ws_get_account_optional» P.«ww_ws_storage_root_of»
  have «g_ws_storage_trie» := «gbody_ws_storage_trie» «g_decode_witness_to_mpt» P.«fb_htab_get» P.«fb_htab_set» P.«ro_htab_get»
  have «g_ws_get_storage» := P.«gbody_ws_get_storage» P.«fb_alloc» P.«fb_heap_mark» P.«fb_heap_release» P.«fb_keccak256» P.«fb_memeq» P.«fb_rlp_decode_fully» P.«fb_trie_lookup» P.«fb_u256_from_be» P.«fb_ws_storage_root_of» «g_ws_storage_trie» P.«ro_memeq» P.«ww_ws_storage_root_of»
  have «g_get_pre_tx_storage» := «gbody_get_pre_tx_storage» P.«fb_record_pre_state_read» P.«fb_stor_lookup» «g_ws_get_storage» P.«wk_record_pre_state_read» P.«ro_stor_lookup»
  have «g_idx_start_storage» := P.«gbody_idx_start_storage» P.«fb_alloc» «g_get_pre_tx_storage» P.«fb_htab_get» P.«fb_htab_set» P.«fb_memcpy» P.«fb_st_le64» P.«ro_htab_get» P.«ww_memcpy» P.«ww_st_le64»
  have «g_update_builder_from_tx» := P.«gbody_update_builder_from_tx» P.«fb_add_balance_change» P.«fb_add_code_change» P.«fb_add_nonce_change» P.«fb_add_storage_write» P.«fb_bal_remove_change» P.«fb_get_code» P.«fb_htab_item» P.«fb_idx_start_account» «g_idx_start_storage» P.«fb_memeq» P.«fb_remove_storage_write» P.«fb_u256_eq» P.«wk_add_balance_change» P.«wk_add_code_change» P.«wk_add_nonce_change» P.«wk_add_storage_write» P.«wk_bal_remove_change» P.«wk_get_code» P.«ro_htab_item» P.«wk_idx_start_account» P.«wk_idx_start_storage» P.«ro_memeq» P.«wk_remove_storage_write» P.«ro_u256_eq»
  have «g_incorporate_tx_into_block» := «gbody_incorporate_tx_into_block» P.«fb_merge_tx_into_block» «g_update_builder_from_tx»
  have «g_htab_truncate» := P.«gbody_htab_truncate» P.«fb_htab_del» P.«htab_del_spec» P.«htab_del_progress_spec»
  have «g_rollback_child_access» := P.«gbody_rollback_child_access» «g_htab_truncate» P.«htab_truncate_spec»
  have «g_finish_child» := P.«gbody_finish_child» P.«fb_address_to_u256» P.«fb_create_finish» P.«fb_credit_state_gas_refund» P.«fb_frame_halt» P.«fb_frame_mem_release» P.«fb_incorporate_child_on_error» P.«fb_incorporate_child_on_success» P.«fb_memcpy» P.«fb_min» P.«fb_pc_add» P.«fb_refill_frame_state_gas» «g_rollback_child_access» P.«fb_scratch_release» P.«fb_set_retdata» P.«fb_stack_push» P.«fb_state_restore» P.«ek_create_finish» P.«ek_frame_halt» P.«ek_refill_frame_state_gas» P.«ek_state_restore»
  have «g_get_storage» := P.«gbody_get_storage» P.«fb_htab_set» P.«fb_record_pre_state_read» P.«fb_sk_make» P.«fb_stor_lookup» «g_ws_get_storage» P.«htab_set_spec» P.«wk_record_pre_state_read» P.«ww_sk_make» P.«ro_stor_lookup»
  have «g_op_sload» := P.«gbody_op_sload» P.«fb_charge_gas» «g_get_storage» P.«fb_is_warm_storage_key» P.«fb_pc_add» P.«fb_stack_pop» P.«fb_stack_push» P.«fb_u256_to_be32» P.«fb_warm_storage_key» P.«ek_charge_gas» P.«ww_is_warm_storage_key» P.«ek_stack_pop» P.«ww_u256_to_be32» P.«ek_warm_storage_key»
  have «g_get_storage_original» := «gbody_get_storage_original» P.«fb_htab_has» P.«fb_record_pre_state_read» P.«fb_stor_lookup» «g_ws_get_storage» P.«ro_htab_has» P.«wk_record_pre_state_read» P.«ro_stor_lookup»
  have «g_op_sstore» := P.«gbody_op_sstore» P.«fb_charge_gas» P.«fb_charge_state_gas» P.«fb_check_gas» P.«fb_credit_state_gas_refund» «g_get_storage» «g_get_storage_original» P.«fb_is_warm_storage_key» P.«fb_max» P.«fb_pc_add» P.«fb_require_not_static» P.«fb_set_storage» P.«fb_stack_pop» P.«fb_u256_eq» P.«fb_u256_is_zero» P.«fb_u256_to_be32» P.«fb_warm_storage_key» P.«ek_charge_gas» P.«ro_check_gas» P.«ek_get_storage_original» P.«ww_is_warm_storage_key» P.«ro_max» P.«ro_require_not_static» P.«ek_stack_pop» P.«ww_u256_to_be32» P.«ek_warm_storage_key»
  have «g_op_dispatch» := P.«gbody_op_dispatch» P.«fb_op_add» P.«fb_op_addmod» P.«fb_op_address» P.«fb_op_and» P.«fb_op_balance» P.«fb_op_basefee» P.«fb_op_blobbasefee» P.«fb_op_blobhash» P.«fb_op_blockhash» P.«fb_op_byte» P.«fb_op_call» P.«fb_op_callcode» P.«fb_op_calldatacopy» P.«fb_op_calldataload» P.«fb_op_calldatasize» P.«fb_op_caller» P.«fb_op_callvalue» P.«fb_op_chainid» P.«fb_op_clz» P.«fb_op_codecopy» P.«fb_op_codesize» P.«fb_op_coinbase» P.«fb_op_create» P.«fb_op_create2» P.«fb_op_delegatecall» P.«fb_op_div» P.«fb_op_dup» P.«fb_op_dupn» P.«fb_op_eq» P.«fb_op_exchange» P.«fb_op_exp» P.«fb_op_extcodecopy» P.«fb_op_extcodehash» P.«fb_op_extcodesize» P.«fb_op_gas» P.«fb_op_gaslimit» P.«fb_op_gasprice» P.«fb_op_gt» P.«fb_op_iszero» P.«fb_op_jump» P.«fb_op_jumpdest» P.«fb_op_jumpi» P.«fb_op_keccak» P.«fb_op_log» P.«fb_op_lt» P.«fb_op_mcopy» P.«fb_op_mload» P.«fb_op_mod» P.«fb_op_msize» P.«fb_op_mstore» P.«fb_op_mstore8» P.«fb_op_mul» P.«fb_op_mulmod» P.«fb_op_not» P.«fb_op_number» P.«fb_op_or» P.«fb_op_origin» P.«fb_op_pc» P.«fb_op_pop» P.«fb_op_prevrandao» P.«fb_op_push» P.«fb_op_return» P.«fb_op_returndatacopy» P.«fb_op_returndatasize» P.«fb_op_revert» P.«fb_op_sar» P.«fb_op_sdiv» P.«fb_op_selfbalance» P.«fb_op_selfdestruct» P.«fb_op_sgt» P.«fb_op_shl» P.«fb_op_shr» P.«fb_op_signextend» «g_op_sload» P.«fb_op_slotnum» P.«fb_op_slt» P.«fb_op_smod» «g_op_sstore» P.«fb_op_staticcall» P.«fb_op_stop» P.«fb_op_sub» P.«fb_op_swap» P.«fb_op_swapn» P.«fb_op_timestamp» P.«fb_op_tload» P.«fb_op_tstore» P.«fb_op_xor»
  have «g_run_frames» := P.«gbody_run_frames» «g_finish_child» P.«fb_frame_epilogue» P.«fb_frame_exception» «g_op_dispatch» P.«finish_child_spec» P.«frame_epilogue_spec» P.«frame_exception_spec» P.«op_dispatch_spec»
  have «g_process_message» := P.«gbody_process_message» P.«fb_depth0_prepare» P.«fb_frame_halt» P.«fb_frame_mem_release» P.«fb_frame_open» P.«fb_frame_start» P.«fb_refill_frame_state_gas» «g_run_frames» P.«fb_scratch_release» P.«fb_state_restore» P.«fb_state_snapshot» P.«ek_depth0_prepare» P.«fk_frame_open» P.«ek_frame_start» P.«ro_state_snapshot»
  have «g_process_create_message» := P.«gbody_process_create_message» P.«fb_create_finish» P.«fb_destroy_storage» P.«fb_frame_halt» P.«fb_increment_nonce» P.«fb_mark_account_created» «g_process_message» P.«fb_refill_frame_state_gas» P.«fb_state_restore» P.«fb_state_snapshot» P.«wk_destroy_storage» P.«wk_increment_nonce» P.«wk_mark_account_created» P.«ro_state_snapshot»
  have «g_process_message_call» := P.«gbody_process_message_call» P.«fb_account_deployable» P.«fb_alloc» P.«fb_frame_state_gas_used» P.«fb_memzero» «g_process_create_message» «g_process_message» P.«wk_account_deployable» P.«ww_alloc» P.«ww_memzero»
  have «g_process_unchecked_system_transaction» := P.«gbody_process_unchecked_system_transaction» P.«fb_alloc» P.«fb_ext_code_of» P.«fb_frame_mem_release» P.«fb_htab_new» «g_incorporate_tx_into_block» P.«fb_memcpy» P.«fb_msg_new» «g_process_message_call» P.«fb_scratch_release» P.«fb_state_fresh_tx» P.«fb_te_new» P.«wk_ext_code_of» P.«htab_new_spec» P.«ww_msg_new» P.«wk_process_message_call» P.«ww_state_fresh_tx» P.«ww_te_new»
  have «g_process_checked_system_transaction» := P.«gbody_process_checked_system_transaction» P.«fb_alloc» P.«fb_ext_code_of» «g_process_unchecked_system_transaction» P.«fb_state_fresh_tx» P.«ww_alloc» P.«wk_ext_code_of» P.«ww_state_fresh_tx»
  have «g_process_general_purpose_requests» := P.«gbody_process_general_purpose_requests» P.«fb_alloc» P.«fb_extract_deposit_data» P.«fb_memcpy» P.«fb_memeq» «g_process_checked_system_transaction» P.«fb_requests_append» P.«ww_alloc» P.«ww_extract_deposit_data» P.«ww_memcpy» P.«ro_memeq» P.«wk_process_checked_system_transaction» P.«wk_requests_append»
  have «g_process_transaction» := P.«gbody_process_transaction» P.«fb_alloc» P.«fb_calculate_blob_gas_price» P.«fb_calculate_total_blob_gas» P.«fb_check_transaction» P.«fb_clear_account_preserving_balance» P.«fb_compute_contract_address» P.«fb_create_ether» P.«fb_encode_receipt» P.«fb_encode_transaction» P.«fb_fee_mul» P.«fb_frame_mem_release» P.«fb_get_account» P.«fb_htab_item» P.«fb_htab_new» P.«fb_htab_set» «g_incorporate_tx_into_block» P.«fb_increment_nonce» P.«fb_keccak256» P.«fb_lst_new» P.«fb_lst_push» P.«fb_max» P.«fb_memcpy» P.«fb_min» P.«fb_msg_new» «g_process_message_call» P.«fb_recover_sender_with_chain_id» P.«fb_scratch_release» P.«fb_set_account_balance» P.«fb_state_fresh_tx» P.«fb_te_new» P.«fb_tx_chain_id» P.«fb_tx_has_access_list» P.«fb_tx_is_blob» P.«fb_tx_is_setcode» P.«fb_u256_sub» P.«fb_udiv_small5» P.«fb_validate_transaction» P.«ww_alloc» P.«wk_calculate_blob_gas_price» P.«ro_calculate_total_blob_gas» P.«wk_check_transaction» P.«wk_clear_account_preserving_balance» P.«ww_compute_contract_address» P.«wk_create_ether» P.«wk_encode_receipt» P.«wk_encode_transaction» P.«ro_fee_mul» P.«wk_get_account» P.«ro_htab_item» P.«htab_new_spec» P.«htab_set_spec» P.«wk_increment_nonce» P.«ww_keccak256» P.«ww_lst_new» P.«ww_lst_push» P.«ro_max» P.«ww_memcpy» P.«ro_min» P.«ww_msg_new» P.«wk_process_message_call» P.«ww_recover_sender_with_chain_id» P.«wk_set_account_balance» P.«ww_state_fresh_tx» P.«ww_te_new» P.«ro_tx_chain_id» P.«ro_tx_has_access_list» P.«ro_tx_is_blob» P.«ro_tx_is_setcode» P.«ro_u256_sub» P.«ro_udiv_small5» P.«ro_validate_transaction»
  have «g_process_withdrawals» := P.«gbody_process_withdrawals» P.«fb_create_ether» «g_incorporate_tx_into_block» P.«fb_state_fresh_tx» P.«fb_u256_mul» P.«wk_create_ether» P.«ww_state_fresh_tx» P.«ro_u256_mul»
  have «g_execute_block» := P.«gbody_execute_block» P.«fb_alloc» P.«fb_bal_init» P.«fb_build_block_access_list_rlp» «g_build_mpt_indexed» P.«fb_compute_requests_hash» «g_compute_state_root» P.«fb_decode_transaction» P.«fb_keccak256» P.«fb_logs_bloom» P.«fb_lst_new» P.«fb_max» P.«fb_memeq» P.«fb_memzero» «g_process_general_purpose_requests» «g_process_transaction» «g_process_unchecked_system_transaction» «g_process_withdrawals» P.«fb_state_fresh_tx» P.«fb_track_ancestor_access» P.«fb_validate_block_access_list_gas_limit» P.«ww_alloc» P.«ww_bal_init» P.«wk_build_block_access_list_rlp» P.«wk_build_mpt_indexed» P.«wk_compute_state_root» P.«ww_decode_transaction» P.«ww_logs_bloom» P.«ww_lst_new» P.«ww_memzero» P.«wk_process_general_purpose_requests» P.«wk_process_transaction» P.«wk_process_unchecked_system_transaction» P.«wk_process_withdrawals» P.«ww_state_fresh_tx» P.«ww_track_ancestor_access» P.«ro_validate_block_access_list_gas_limit»
  have «g_payload_header» := P.«gbody_payload_header» P.«fb_alloc» P.«fb_block_rlp_length» «g_build_mpt_indexed» P.«fb_compute_requests_hash» P.«fb_encode_execution_requests» P.«fb_encode_withdrawal_rlp» P.«fb_keccak256» P.«fb_memzero» P.«ww_alloc» P.«wk_block_rlp_length» P.«wk_build_mpt_indexed» P.«wk_encode_withdrawal_rlp» P.«ww_keccak256» P.«ww_memzero»
  have «g_state_init» := P.«gbody_state_init» P.«fb_alloc» «g_decode_witness_to_mpt» P.«fb_htab_new» P.«ww_alloc»
  have «g_run_attempt» := P.«gbody_run_attempt» P.«fb_alloc» P.«fb_check_gas_limit» «g_execute_block» P.«fb_header_hash» P.«fb_is_valid_versioned_hashes» P.«fb_memeq» P.«fb_memzero» P.«fb_nodedb_build» «g_payload_header» «g_state_init» P.«fb_validate_header» P.«fb_validate_headers» P.«ww_alloc» P.«ro_check_gas_limit» P.«ww_header_hash» P.«ww_is_valid_versioned_hashes» P.«ro_memeq» P.«ww_memzero» P.«wk_nodedb_build» P.«wk_payload_header» P.«wk_state_init» P.«wk_validate_header» P.«ww_validate_headers»
  have «g_attempt_l1» := «gbody_attempt_l1» «g_run_attempt»
  have «g_attempt_l2» := «gbody_attempt_l2» «g_attempt_l1»
  have «g_attempt_l3» := «gbody_attempt_l3» «g_attempt_l2»
  have «g_attempt_l4» := «gbody_attempt_l4» «g_attempt_l3»
  have «g_attempt_l5» := «gbody_attempt_l5» «g_attempt_l4»
  have «g_attempt_l6» := «gbody_attempt_l6» «g_attempt_l5»
  have «g_attempt_l7» := «gbody_attempt_l7» «g_attempt_l6»
  have «g_verify_stateless_new_payload» := «gbody_verify_stateless_new_payload» «g_attempt_l7»
  have «g_main» := P.«gbody_main» P.«fb_alloc» P.«fb_blake2_init» P.«fb_bls_precompiles_init» P.«fb_bn254_init» P.«fb_decode_host_input» P.«fb_evm_init» P.«fb_fork_init» P.«fb_header_init» P.«fb_htr_new_payload_request» P.«fb_keccak_init» P.«fb_mem_init» P.«fb_memzero» P.«fb_mpt_init» P.«fb_output_write» P.«fb_ripemd160_init» P.«fb_secp256k1_init» P.«fb_serialize_result» P.«fb_sha256_init» P.«fb_ssz_init» P.«fb_u256_ws_init» «g_verify_stateless_new_payload» P.«ww_alloc» P.«ww_blake2_init» P.«ww_bls_precompiles_init» P.«ww_bn254_init» P.«wk_decode_host_input» P.«ww_evm_init» P.«ww_fork_init» P.«ww_header_init» P.«ww_htr_new_payload_request» P.«ww_keccak_init» P.«mem_init_world» P.«ww_memzero» P.«ww_mpt_init» P.«ww_ripemd160_init» P.«ro_secp256k1_init» P.«ww_sha256_init» P.«ww_ssz_init» P.«ww_u256_ws_init»
  exact «g_main»

/-- The leaves discharge the primitives (each field is its `sorry` leaf). -/
theorem primitives : Primitives where
  «fb__decode_step» := «fb__decode_step»
  «fb__resolve_step» := «fb__resolve_step»
  «fb_mpt_fail» := «fb_mpt_fail»
  «fb_node_new_ext» := «fb_node_new_ext»
  «fb_rlp_item» := «fb_rlp_item»
  «ak__decode_step» := «ak__decode_step»
  «ww__resolve_step» := «ww__resolve_step»
  «ro_mpt_fail» := «ro_mpt_fail»
  «ww_node_new_ext» := «ww_node_new_ext»
  «ww_rlp_item» := «ww_rlp_item»
  «gbody__decode_witness_node_body» := «gbody__decode_witness_node_body»
  «fb_scratch_release» := «fb_scratch_release»
  «fb_scratch_mark» := «fb_scratch_mark»
  «ro_scratch_mark» := «ro_scratch_mark»
  «fb__collapse_branch» := «fb__collapse_branch»
  «fb__delete_ext_finish» := «fb__delete_ext_finish»
  «fb_common_prefix_length» := «fb_common_prefix_length»
  «fb_memeq» := «fb_memeq»
  «fb_node_invalidate» := «fb_node_invalidate»
  «fb_scratch_alloc» := «fb_scratch_alloc»
  «nf__collapse_branch» := «nf__collapse_branch»
  «nf__delete_ext_finish» := «nf__delete_ext_finish»
  «ro_common_prefix_length» := «ro_common_prefix_length»
  «rv_common_prefix_length» := «rv_common_prefix_length»
  «ro_memeq» := «ro_memeq»
  «nf_node_invalidate» := «nf_node_invalidate»
  «ww_scratch_alloc» := «ww_scratch_alloc»
  «gbody__mpt_delete_node_body» := «gbody__mpt_delete_node_body»
  «gbody__mpt_delete_node» := «gbody__mpt_delete_node»
  «fb__insert_into_leaf» := «fb__insert_into_leaf»
  «fb__split_extension» := «fb__split_extension»
  «fb_node_new_leaf» := «fb_node_new_leaf»
  «nf__insert_into_leaf» := «nf__insert_into_leaf»
  «nf__split_extension» := «nf__split_extension»
  «nf_node_new_ext» := «nf_node_new_ext»
  «nf_node_new_leaf» := «nf_node_new_leaf»
  «gbody__mpt_insert_node» := «gbody__mpt_insert_node»
  «fb_mpt_nibble_key» := «fb_mpt_nibble_key»
  «ww_mpt_nibble_key» := «ww_mpt_nibble_key»
  «nk_mpt_nibble_key» := «nk_mpt_nibble_key»
  «gbody_mpt_set» := «gbody_mpt_set»
  «fb_heap_mark» := «fb_heap_mark»
  «fb_heap_release» := «fb_heap_release»
  «fb_mpt_new» := «fb_mpt_new»
  «fb_mpt_root» := «fb_mpt_root»
  «fb_rlp_encode_word» := «fb_rlp_encode_word»
  «ro_heap_mark» := «ro_heap_mark»
  «ww_mpt_new» := «ww_mpt_new»
  «wk_mpt_set» := «wk_mpt_set»
  «ww_rlp_encode_word» := «ww_rlp_encode_word»
  «gbody_build_mpt_indexed» := «gbody_build_mpt_indexed»
  «fb_alloc» := «fb_alloc»
  «fb_memcpy» := «fb_memcpy»
  «fb_nodedb_lookup» := «fb_nodedb_lookup»
  «ro_nodedb_lookup» := «ro_nodedb_lookup»
  «fb_cache_get_root» := «fb_cache_get_root»
  «fb_encode_account» := «fb_encode_account»
  «fb_htab_copy» := «fb_htab_copy»
  «fb_htab_get» := «fb_htab_get»
  «fb_htab_has» := «fb_htab_has»
  «fb_htab_item» := «fb_htab_item»
  «fb_htab_new» := «fb_htab_new»
  «fb_htab_set» := «fb_htab_set»
  «fb_rlp_encode_bytes» := «fb_rlp_encode_bytes»
  «fb_u256_is_zero» := «fb_u256_is_zero»
  «fb_u256_to_be_min» := «fb_u256_to_be_min»
  «fb_ws_get_account_optional» := «fb_ws_get_account_optional»
  «fb_ws_storage_root_of» := «fb_ws_storage_root_of»
  «ww_alloc» := «ww_alloc»
  «ww_cache_get_root» := «ww_cache_get_root»
  «ww_encode_account» := «ww_encode_account»
  «ww_htab_copy» := «ww_htab_copy»
  «ro_htab_get» := «ro_htab_get»
  «ro_htab_has» := «ro_htab_has»
  «ro_htab_item» := «ro_htab_item»
  «htab_new_spec» := «htab_new_spec»
  «htab_set_spec» := «htab_set_spec»
  «ww_memcpy» := «ww_memcpy»
  «wk_mpt_from_witness» := «wk_mpt_from_witness»
  «wk_mpt_root» := «wk_mpt_root»
  «ww_rlp_encode_bytes» := «ww_rlp_encode_bytes»
  «ro_u256_is_zero» := «ro_u256_is_zero»
  «ww_u256_to_be_min» := «ww_u256_to_be_min»
  «ww_ws_get_account_optional» := «ww_ws_get_account_optional»
  «ww_ws_storage_root_of» := «ww_ws_storage_root_of»
  «gbody_compute_state_root» := «gbody_compute_state_root»
  «fb_keccak256» := «fb_keccak256»
  «fb_rlp_decode_fully» := «fb_rlp_decode_fully»
  «fb_trie_lookup» := «fb_trie_lookup»
  «fb_u256_from_be» := «fb_u256_from_be»
  «gbody_ws_get_storage» := «gbody_ws_get_storage»
  «fb_record_pre_state_read» := «fb_record_pre_state_read»
  «fb_stor_lookup» := «fb_stor_lookup»
  «wk_record_pre_state_read» := «wk_record_pre_state_read»
  «ro_stor_lookup» := «ro_stor_lookup»
  «fb_st_le64» := «fb_st_le64»
  «ww_st_le64» := «ww_st_le64»
  «gbody_idx_start_storage» := «gbody_idx_start_storage»
  «fb_add_balance_change» := «fb_add_balance_change»
  «fb_add_code_change» := «fb_add_code_change»
  «fb_add_nonce_change» := «fb_add_nonce_change»
  «fb_add_storage_write» := «fb_add_storage_write»
  «fb_bal_remove_change» := «fb_bal_remove_change»
  «fb_get_code» := «fb_get_code»
  «fb_idx_start_account» := «fb_idx_start_account»
  «fb_remove_storage_write» := «fb_remove_storage_write»
  «fb_u256_eq» := «fb_u256_eq»
  «wk_add_balance_change» := «wk_add_balance_change»
  «wk_add_code_change» := «wk_add_code_change»
  «wk_add_nonce_change» := «wk_add_nonce_change»
  «wk_add_storage_write» := «wk_add_storage_write»
  «wk_bal_remove_change» := «wk_bal_remove_change»
  «wk_get_code» := «wk_get_code»
  «wk_idx_start_account» := «wk_idx_start_account»
  «wk_idx_start_storage» := «wk_idx_start_storage»
  «wk_remove_storage_write» := «wk_remove_storage_write»
  «ro_u256_eq» := «ro_u256_eq»
  «gbody_update_builder_from_tx» := «gbody_update_builder_from_tx»
  «fb_merge_tx_into_block» := «fb_merge_tx_into_block»
  «fb_htab_del» := «fb_htab_del»
  «htab_del_spec» := «htab_del_spec»
  «htab_del_progress_spec» := «htab_del_progress_spec»
  «gbody_htab_truncate» := «gbody_htab_truncate»
  «htab_truncate_spec» := «htab_truncate_spec»
  «gbody_rollback_child_access» := «gbody_rollback_child_access»
  «fb_address_to_u256» := «fb_address_to_u256»
  «fb_create_finish» := «fb_create_finish»
  «fb_credit_state_gas_refund» := «fb_credit_state_gas_refund»
  «fb_frame_halt» := «fb_frame_halt»
  «fb_frame_mem_release» := «fb_frame_mem_release»
  «fb_incorporate_child_on_error» := «fb_incorporate_child_on_error»
  «fb_incorporate_child_on_success» := «fb_incorporate_child_on_success»
  «fb_min» := «fb_min»
  «fb_pc_add» := «fb_pc_add»
  «fb_refill_frame_state_gas» := «fb_refill_frame_state_gas»
  «fb_set_retdata» := «fb_set_retdata»
  «fb_stack_push» := «fb_stack_push»
  «fb_state_restore» := «fb_state_restore»
  «ek_create_finish» := «ek_create_finish»
  «ek_frame_halt» := «ek_frame_halt»
  «ek_refill_frame_state_gas» := «ek_refill_frame_state_gas»
  «ek_state_restore» := «ek_state_restore»
  «gbody_finish_child» := «gbody_finish_child»
  «fb_sk_make» := «fb_sk_make»
  «ww_sk_make» := «ww_sk_make»
  «gbody_get_storage» := «gbody_get_storage»
  «fb_charge_gas» := «fb_charge_gas»
  «fb_is_warm_storage_key» := «fb_is_warm_storage_key»
  «fb_stack_pop» := «fb_stack_pop»
  «fb_u256_to_be32» := «fb_u256_to_be32»
  «fb_warm_storage_key» := «fb_warm_storage_key»
  «ek_charge_gas» := «ek_charge_gas»
  «ww_is_warm_storage_key» := «ww_is_warm_storage_key»
  «ek_stack_pop» := «ek_stack_pop»
  «ww_u256_to_be32» := «ww_u256_to_be32»
  «ek_warm_storage_key» := «ek_warm_storage_key»
  «gbody_op_sload» := «gbody_op_sload»
  «fb_charge_state_gas» := «fb_charge_state_gas»
  «fb_check_gas» := «fb_check_gas»
  «fb_max» := «fb_max»
  «fb_require_not_static» := «fb_require_not_static»
  «fb_set_storage» := «fb_set_storage»
  «ro_check_gas» := «ro_check_gas»
  «ek_get_storage_original» := «ek_get_storage_original»
  «ro_max» := «ro_max»
  «ro_require_not_static» := «ro_require_not_static»
  «gbody_op_sstore» := «gbody_op_sstore»
  «fb_op_add» := «fb_op_add»
  «fb_op_addmod» := «fb_op_addmod»
  «fb_op_address» := «fb_op_address»
  «fb_op_and» := «fb_op_and»
  «fb_op_balance» := «fb_op_balance»
  «fb_op_basefee» := «fb_op_basefee»
  «fb_op_blobbasefee» := «fb_op_blobbasefee»
  «fb_op_blobhash» := «fb_op_blobhash»
  «fb_op_blockhash» := «fb_op_blockhash»
  «fb_op_byte» := «fb_op_byte»
  «fb_op_call» := «fb_op_call»
  «fb_op_callcode» := «fb_op_callcode»
  «fb_op_calldatacopy» := «fb_op_calldatacopy»
  «fb_op_calldataload» := «fb_op_calldataload»
  «fb_op_calldatasize» := «fb_op_calldatasize»
  «fb_op_caller» := «fb_op_caller»
  «fb_op_callvalue» := «fb_op_callvalue»
  «fb_op_chainid» := «fb_op_chainid»
  «fb_op_clz» := «fb_op_clz»
  «fb_op_codecopy» := «fb_op_codecopy»
  «fb_op_codesize» := «fb_op_codesize»
  «fb_op_coinbase» := «fb_op_coinbase»
  «fb_op_create» := «fb_op_create»
  «fb_op_create2» := «fb_op_create2»
  «fb_op_delegatecall» := «fb_op_delegatecall»
  «fb_op_div» := «fb_op_div»
  «fb_op_dup» := «fb_op_dup»
  «fb_op_dupn» := «fb_op_dupn»
  «fb_op_eq» := «fb_op_eq»
  «fb_op_exchange» := «fb_op_exchange»
  «fb_op_exp» := «fb_op_exp»
  «fb_op_extcodecopy» := «fb_op_extcodecopy»
  «fb_op_extcodehash» := «fb_op_extcodehash»
  «fb_op_extcodesize» := «fb_op_extcodesize»
  «fb_op_gas» := «fb_op_gas»
  «fb_op_gaslimit» := «fb_op_gaslimit»
  «fb_op_gasprice» := «fb_op_gasprice»
  «fb_op_gt» := «fb_op_gt»
  «fb_op_iszero» := «fb_op_iszero»
  «fb_op_jump» := «fb_op_jump»
  «fb_op_jumpdest» := «fb_op_jumpdest»
  «fb_op_jumpi» := «fb_op_jumpi»
  «fb_op_keccak» := «fb_op_keccak»
  «fb_op_log» := «fb_op_log»
  «fb_op_lt» := «fb_op_lt»
  «fb_op_mcopy» := «fb_op_mcopy»
  «fb_op_mload» := «fb_op_mload»
  «fb_op_mod» := «fb_op_mod»
  «fb_op_msize» := «fb_op_msize»
  «fb_op_mstore» := «fb_op_mstore»
  «fb_op_mstore8» := «fb_op_mstore8»
  «fb_op_mul» := «fb_op_mul»
  «fb_op_mulmod» := «fb_op_mulmod»
  «fb_op_not» := «fb_op_not»
  «fb_op_number» := «fb_op_number»
  «fb_op_or» := «fb_op_or»
  «fb_op_origin» := «fb_op_origin»
  «fb_op_pc» := «fb_op_pc»
  «fb_op_pop» := «fb_op_pop»
  «fb_op_prevrandao» := «fb_op_prevrandao»
  «fb_op_push» := «fb_op_push»
  «fb_op_return» := «fb_op_return»
  «fb_op_returndatacopy» := «fb_op_returndatacopy»
  «fb_op_returndatasize» := «fb_op_returndatasize»
  «fb_op_revert» := «fb_op_revert»
  «fb_op_sar» := «fb_op_sar»
  «fb_op_sdiv» := «fb_op_sdiv»
  «fb_op_selfbalance» := «fb_op_selfbalance»
  «fb_op_selfdestruct» := «fb_op_selfdestruct»
  «fb_op_sgt» := «fb_op_sgt»
  «fb_op_shl» := «fb_op_shl»
  «fb_op_shr» := «fb_op_shr»
  «fb_op_signextend» := «fb_op_signextend»
  «fb_op_slotnum» := «fb_op_slotnum»
  «fb_op_slt» := «fb_op_slt»
  «fb_op_smod» := «fb_op_smod»
  «fb_op_staticcall» := «fb_op_staticcall»
  «fb_op_stop» := «fb_op_stop»
  «fb_op_sub» := «fb_op_sub»
  «fb_op_swap» := «fb_op_swap»
  «fb_op_swapn» := «fb_op_swapn»
  «fb_op_timestamp» := «fb_op_timestamp»
  «fb_op_tload» := «fb_op_tload»
  «fb_op_tstore» := «fb_op_tstore»
  «fb_op_xor» := «fb_op_xor»
  «gbody_op_dispatch» := «gbody_op_dispatch»
  «fb_frame_epilogue» := «fb_frame_epilogue»
  «fb_frame_exception» := «fb_frame_exception»
  «finish_child_spec» := «finish_child_spec»
  «frame_epilogue_spec» := «frame_epilogue_spec»
  «frame_exception_spec» := «frame_exception_spec»
  «op_dispatch_spec» := «op_dispatch_spec»
  «gbody_run_frames» := «gbody_run_frames»
  «fb_depth0_prepare» := «fb_depth0_prepare»
  «fb_frame_open» := «fb_frame_open»
  «fb_frame_start» := «fb_frame_start»
  «fb_state_snapshot» := «fb_state_snapshot»
  «ek_depth0_prepare» := «ek_depth0_prepare»
  «fk_frame_open» := «fk_frame_open»
  «ek_frame_start» := «ek_frame_start»
  «ro_state_snapshot» := «ro_state_snapshot»
  «gbody_process_message» := «gbody_process_message»
  «fb_destroy_storage» := «fb_destroy_storage»
  «fb_increment_nonce» := «fb_increment_nonce»
  «fb_mark_account_created» := «fb_mark_account_created»
  «wk_destroy_storage» := «wk_destroy_storage»
  «wk_increment_nonce» := «wk_increment_nonce»
  «wk_mark_account_created» := «wk_mark_account_created»
  «gbody_process_create_message» := «gbody_process_create_message»
  «fb_account_deployable» := «fb_account_deployable»
  «fb_frame_state_gas_used» := «fb_frame_state_gas_used»
  «fb_memzero» := «fb_memzero»
  «wk_account_deployable» := «wk_account_deployable»
  «ww_memzero» := «ww_memzero»
  «gbody_process_message_call» := «gbody_process_message_call»
  «fb_ext_code_of» := «fb_ext_code_of»
  «fb_msg_new» := «fb_msg_new»
  «fb_state_fresh_tx» := «fb_state_fresh_tx»
  «fb_te_new» := «fb_te_new»
  «wk_ext_code_of» := «wk_ext_code_of»
  «ww_msg_new» := «ww_msg_new»
  «wk_process_message_call» := «wk_process_message_call»
  «ww_state_fresh_tx» := «ww_state_fresh_tx»
  «ww_te_new» := «ww_te_new»
  «gbody_process_unchecked_system_transaction» := «gbody_process_unchecked_system_transaction»
  «gbody_process_checked_system_transaction» := «gbody_process_checked_system_transaction»
  «fb_extract_deposit_data» := «fb_extract_deposit_data»
  «fb_requests_append» := «fb_requests_append»
  «ww_extract_deposit_data» := «ww_extract_deposit_data»
  «wk_process_checked_system_transaction» := «wk_process_checked_system_transaction»
  «wk_requests_append» := «wk_requests_append»
  «gbody_process_general_purpose_requests» := «gbody_process_general_purpose_requests»
  «fb_calculate_blob_gas_price» := «fb_calculate_blob_gas_price»
  «fb_calculate_total_blob_gas» := «fb_calculate_total_blob_gas»
  «fb_check_transaction» := «fb_check_transaction»
  «fb_clear_account_preserving_balance» := «fb_clear_account_preserving_balance»
  «fb_compute_contract_address» := «fb_compute_contract_address»
  «fb_create_ether» := «fb_create_ether»
  «fb_encode_receipt» := «fb_encode_receipt»
  «fb_encode_transaction» := «fb_encode_transaction»
  «fb_fee_mul» := «fb_fee_mul»
  «fb_get_account» := «fb_get_account»
  «fb_lst_new» := «fb_lst_new»
  «fb_lst_push» := «fb_lst_push»
  «fb_recover_sender_with_chain_id» := «fb_recover_sender_with_chain_id»
  «fb_set_account_balance» := «fb_set_account_balance»
  «fb_tx_chain_id» := «fb_tx_chain_id»
  «fb_tx_has_access_list» := «fb_tx_has_access_list»
  «fb_tx_is_blob» := «fb_tx_is_blob»
  «fb_tx_is_setcode» := «fb_tx_is_setcode»
  «fb_u256_sub» := «fb_u256_sub»
  «fb_udiv_small5» := «fb_udiv_small5»
  «fb_validate_transaction» := «fb_validate_transaction»
  «wk_calculate_blob_gas_price» := «wk_calculate_blob_gas_price»
  «ro_calculate_total_blob_gas» := «ro_calculate_total_blob_gas»
  «wk_check_transaction» := «wk_check_transaction»
  «wk_clear_account_preserving_balance» := «wk_clear_account_preserving_balance»
  «ww_compute_contract_address» := «ww_compute_contract_address»
  «wk_create_ether» := «wk_create_ether»
  «wk_encode_receipt» := «wk_encode_receipt»
  «wk_encode_transaction» := «wk_encode_transaction»
  «ro_fee_mul» := «ro_fee_mul»
  «wk_get_account» := «wk_get_account»
  «ww_keccak256» := «ww_keccak256»
  «ww_lst_new» := «ww_lst_new»
  «ww_lst_push» := «ww_lst_push»
  «ro_min» := «ro_min»
  «ww_recover_sender_with_chain_id» := «ww_recover_sender_with_chain_id»
  «wk_set_account_balance» := «wk_set_account_balance»
  «ro_tx_chain_id» := «ro_tx_chain_id»
  «ro_tx_has_access_list» := «ro_tx_has_access_list»
  «ro_tx_is_blob» := «ro_tx_is_blob»
  «ro_tx_is_setcode» := «ro_tx_is_setcode»
  «ro_u256_sub» := «ro_u256_sub»
  «ro_udiv_small5» := «ro_udiv_small5»
  «ro_validate_transaction» := «ro_validate_transaction»
  «gbody_process_transaction» := «gbody_process_transaction»
  «fb_u256_mul» := «fb_u256_mul»
  «ro_u256_mul» := «ro_u256_mul»
  «gbody_process_withdrawals» := «gbody_process_withdrawals»
  «fb_bal_init» := «fb_bal_init»
  «fb_build_block_access_list_rlp» := «fb_build_block_access_list_rlp»
  «fb_compute_requests_hash» := «fb_compute_requests_hash»
  «fb_decode_transaction» := «fb_decode_transaction»
  «fb_logs_bloom» := «fb_logs_bloom»
  «fb_track_ancestor_access» := «fb_track_ancestor_access»
  «fb_validate_block_access_list_gas_limit» := «fb_validate_block_access_list_gas_limit»
  «ww_bal_init» := «ww_bal_init»
  «wk_build_block_access_list_rlp» := «wk_build_block_access_list_rlp»
  «wk_build_mpt_indexed» := «wk_build_mpt_indexed»
  «wk_compute_state_root» := «wk_compute_state_root»
  «ww_decode_transaction» := «ww_decode_transaction»
  «ww_logs_bloom» := «ww_logs_bloom»
  «wk_process_general_purpose_requests» := «wk_process_general_purpose_requests»
  «wk_process_transaction» := «wk_process_transaction»
  «wk_process_unchecked_system_transaction» := «wk_process_unchecked_system_transaction»
  «wk_process_withdrawals» := «wk_process_withdrawals»
  «ww_track_ancestor_access» := «ww_track_ancestor_access»
  «ro_validate_block_access_list_gas_limit» := «ro_validate_block_access_list_gas_limit»
  «gbody_execute_block» := «gbody_execute_block»
  «fb_block_rlp_length» := «fb_block_rlp_length»
  «fb_encode_execution_requests» := «fb_encode_execution_requests»
  «fb_encode_withdrawal_rlp» := «fb_encode_withdrawal_rlp»
  «wk_block_rlp_length» := «wk_block_rlp_length»
  «wk_encode_withdrawal_rlp» := «wk_encode_withdrawal_rlp»
  «gbody_payload_header» := «gbody_payload_header»
  «gbody_state_init» := «gbody_state_init»
  «fb_check_gas_limit» := «fb_check_gas_limit»
  «fb_header_hash» := «fb_header_hash»
  «fb_is_valid_versioned_hashes» := «fb_is_valid_versioned_hashes»
  «fb_nodedb_build» := «fb_nodedb_build»
  «fb_validate_header» := «fb_validate_header»
  «fb_validate_headers» := «fb_validate_headers»
  «ro_check_gas_limit» := «ro_check_gas_limit»
  «ww_header_hash» := «ww_header_hash»
  «ww_is_valid_versioned_hashes» := «ww_is_valid_versioned_hashes»
  «wk_nodedb_build» := «wk_nodedb_build»
  «wk_payload_header» := «wk_payload_header»
  «wk_state_init» := «wk_state_init»
  «wk_validate_header» := «wk_validate_header»
  «ww_validate_headers» := «ww_validate_headers»
  «gbody_run_attempt» := «gbody_run_attempt»
  «fb_blake2_init» := «fb_blake2_init»
  «fb_bls_precompiles_init» := «fb_bls_precompiles_init»
  «fb_bn254_init» := «fb_bn254_init»
  «fb_decode_host_input» := «fb_decode_host_input»
  «fb_evm_init» := «fb_evm_init»
  «fb_fork_init» := «fb_fork_init»
  «fb_header_init» := «fb_header_init»
  «fb_htr_new_payload_request» := «fb_htr_new_payload_request»
  «fb_keccak_init» := «fb_keccak_init»
  «fb_mem_init» := «fb_mem_init»
  «fb_mpt_init» := «fb_mpt_init»
  «fb_output_write» := «fb_output_write»
  «fb_ripemd160_init» := «fb_ripemd160_init»
  «fb_secp256k1_init» := «fb_secp256k1_init»
  «fb_serialize_result» := «fb_serialize_result»
  «fb_sha256_init» := «fb_sha256_init»
  «fb_ssz_init» := «fb_ssz_init»
  «fb_u256_ws_init» := «fb_u256_ws_init»
  «ww_blake2_init» := «ww_blake2_init»
  «ww_bls_precompiles_init» := «ww_bls_precompiles_init»
  «ww_bn254_init» := «ww_bn254_init»
  «wk_decode_host_input» := «wk_decode_host_input»
  «ww_evm_init» := «ww_evm_init»
  «ww_fork_init» := «ww_fork_init»
  «ww_header_init» := «ww_header_init»
  «ww_htr_new_payload_request» := «ww_htr_new_payload_request»
  «ww_keccak_init» := «ww_keccak_init»
  «mem_init_world» := «mem_init_world»
  «ww_mpt_init» := «ww_mpt_init»
  «ww_ripemd160_init» := «ww_ripemd160_init»
  «ro_secp256k1_init» := «ro_secp256k1_init»
  «ww_sha256_init» := «ww_sha256_init»
  «ww_ssz_init» := «ww_ssz_init»
  «ww_u256_ws_init» := «ww_u256_ws_init»
  «gbody_main» := «gbody_main»


/-! ## 8. `K_pan` and the budget -/

/-- The proposed total source budget: the generated bound of `main` plus the entry tick. -/
def K_pan : Nat := K.«main» + 1

/-- Kernel-checked budget inequality (target side `32·K + 23077`, `ConcreteStage1To5Transfer`). -/
theorem K_pan_budget : 32 * K_pan + 23077 ≤ (10 ^ 299 - 1) / 10 ^ 4 := by decide

/-- The conditional assembly (round-3 assembly ruling), PROVED and `sorry`-free: the primitive
obligations imply the campaign target. `#print axioms assembly` lists no `sorryAx`. -/
theorem assembly (P : Primitives) : CoveredSourceTicksConsumedBounded K_pan :=
  coveredSourceTicksConsumedBounded_of_terminatingMainOnEntry (assembly_main P)

/-- End-to-end target of the campaign under this proposal: the assembly applied to the leaves. Its
`sorry` dependencies are exactly the primitive leaves (`primitives`). -/
theorem coveredSourceTicksConsumedBounded_K_pan : CoveredSourceTicksConsumedBounded K_pan :=
  assembly primitives

/-! ### Round-1 counterexamples, pinned (each is the tick count of the counterexample run) -/

/-- Item 2, `sort_elems` with `esz = 0`, `n = 2^62`: at least `n` merge iterations. -/
example : 2 ^ 62 ≤ K.«sort_elems» := by decide

/-- Item 2, `htr_payload` / `htr_new_payload_request` with `ntx = 2^59`: ≈ 2.9·10^16 ticks. -/
example : 29000000000000000 ≤ K.«htr_payload» := by decide
example : 29000000000000000 ≤ K.«htr_new_payload_request» := by decide

/-- Item 2, self-looping extension node: `6·W` resp. `5.25·W` ticks. -/
example : 6 * domainBytes ≤ K.«_mpt_insert_node» := by decide
example : 6 * domainBytes ≤ K.«trie_walk» := by decide

/-- Item 2, `rlp_list_count` over `W − 10` bytes of `0xc0` (9 ticks per byte). -/
example : 9 * domainBytes ≤ K.«tx_scalar_word» := by decide
example : 9 * domainBytes ≤ K.«hdr_word_field» := by decide

/-- Item 2, 16 000 lookups with `W/2`-byte keys: ≈ 7.7·10^12 ticks. -/
example : 7700000000000 ≤ K.«_decode_witness_node_body» := by decide

/-- Item 3, `htab_union_into` with `src.count = 2^62` aliasing `dst` (2^62 `htab_item` calls),
and `finish_child` reaching it. -/
example : 2 ^ 62 * (K.«htab_item» + 1) ≤ K.«htab_union_into» := by decide
example : 2 ^ 62 ≤ K.«finish_child» := by decide

/-- Item 5, `incorporate_child_on_error` after a `2^62` mint: ≈ 2^58 `run_frames` iterations. -/
example : 2 ^ 58 ≤ evmPotMax := by decide

end InitECandidate.Solver.Wave8GuestInv
