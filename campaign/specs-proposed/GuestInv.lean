import InitECandidate.Solver.PanTerminatingBounded

/-! PROPOSED STATEMENTS ONLY (Wave 8, mission 9409f9a9, track `guestinv-opus55`).

Replaces the presumed-false all-state `TerminatingFunBounded "main"` route by a guarded one:

* `GuestInv` — a locals-free, clock-free invariant on the non-memory part of the state
  (memory domains, base/top, code, globals' shape and the four allocator/journal globals);
* `TerminatingFunBoundedOn P fname K` plus `call`/`decCall`/handler/`seq` rules that thread
  `GuestInv` through `callEntryStateHOLFinite`;
* the bridge `TerminatingFunBoundedOn GuestInv "main" K → CoveredSourceTicksConsumedBounded (K+1)`
  (and its covered-input variant used for the `gas ≤ 2·10^8` bound);
* restated leaf interfaces with data-structure/memory-layout bounds, an explicit `K_pan`
  and a kernel-checked budget inequality.

Rationale, the conjunct-by-conjunct justification, preservation obligations and the
complete list of `sorry`s are in `campaign/notes/guestinv/DESIGN.md`.
`sorry` appears only in theorem bodies, never in a definition.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 400

namespace InitECandidate.Solver.Wave8GuestInv

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded

/-! ## 1. Layout constants (all from `InitE.Parameters` / `Guest/SoftwareAst.lean`) -/

/-- Upper end of the bump heap: `alloc` traps unless the new `heap_ptr ≤ 0xb0000000`
(`HeapPotential.cMax`, `Guest/SoftwareAst.lean:73-85`). -/
def heapLimit : Nat := scratchStart

/-- `journal_cap` is only ever assigned `0` (declaration) or `524288` (`state_init`,
`Guest/SoftwareAst.lean:12768`). -/
def journalCapMax : Nat := 524288

/-- Bytes of `ordinaryDomain` (`[sourceBase, heapEnd)`, aligned cells only). Every loop that
loads or stores a fresh address per iteration stops (with `.error`) within this many steps. -/
def domainBytes : Nat := heapEnd - sourceBase

theorem domainBytes_eq : domainBytes = 31104957928 := by decide

/-- Bump-heap arena bytes `[sourceBase, 0xb0000000)`; bounds every heap-allocated table. -/
def heapArenaBytes : Nat := heapLimit - sourceBase

theorem heapArenaBytes_eq : heapArenaBytes = 251658240 := by decide

/-- EVM call-depth bound: 1024 nested calls plus the top frame. -/
def maxFrames : Nat := 1025

/-- Maximum key length of every guest hash table (`htab_new` is only called with 20/32/52). -/
def maxKeyLen : Nat := 52

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

/-! ## 2. `GuestInv` -/

/-- `name` is a global bound to the word `w`. -/
def GlobalWord {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) (w : BitVec 64) :
    Prop :=
  s.globals.lookup (ofString name) = some (.val (.word w))

/-- Every declared global holds a single word (the declared shape `Shape.one`). -/
def GlobalsWellShaped {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ name ∈ guestGlobalNames, ∃ w, GlobalWord s name w

/-- `frame_mem_ptr` / `scratch_ptr` either both still hold their declaration value `0`
(before `mem_init`) or describe the shared arena `[0xb0000000, 0xb0bee000)` with the frame
memory growing up from the bottom, the scratch stack growing down from the top, and
`frame_mem_ptr ≤ scratch_ptr` (the separating check of `frame_mem_alloc`/`scratch_alloc`). -/
def ArenaOK (frameMem scratch : BitVec 64) : Prop :=
  (frameMem = 0 ∧ scratch = 0) ∨
    (scratchStart ≤ frameMem.toNat ∧ frameMem.toNat ≤ scratch.toNat ∧
      scratch.toNat ≤ scratchEnd)

/-- The guest invariant. It mentions neither `locals` nor `clock` nor `memory` nor `ffi`,
so it is preserved by `callEntryStateHOLFinite`, `setVarHOLFinite`, local restoration after a
call, and every memory store; only the global writes listed in DESIGN.md can break it. -/
structure GuestInvData {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop where
  code : s.code = originalRuntimeCode
  memaddrs : s.memaddrs = ordinaryDomain
  shMemaddrs : s.shMemaddrs = sharedDomain
  baseAddr : s.baseAddr = BitVec.ofNat 64 sourceBase
  topAddr : s.topAddr = BitVec.ofNat 64 heapEnd
  globals : GlobalsWellShaped s
  heap : ∃ hp, GlobalWord s "heap_ptr" hp ∧ hp.toNat ≤ heapLimit
  arena : ∃ fm sp, GlobalWord s "frame_mem_ptr" fm ∧ GlobalWord s "scratch_ptr" sp ∧ ArenaOK fm sp
  journal : ∃ n cap, GlobalWord s "journal_n" n ∧ GlobalWord s "journal_cap" cap ∧
    n.toNat ≤ cap.toNat ∧ cap.toNat ≤ journalCapMax

def GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInvData s

/-- After `mem_init`: the arenas are initialised and `heap_ptr` is inside the heap arena. -/
def GuestInvReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧
    (∃ hp, GlobalWord s "heap_ptr" hp ∧ sourceBase ≤ hp.toNat) ∧
    (∃ fm, GlobalWord s "frame_mem_ptr" fm ∧ scratchStart ≤ fm.toNat)

/-- The FFI state replays the oracle of an input whose declared gas limit is covered.
Only meaningful at `F = Guest.HostMemory`; false at every other carrier. -/
def CoveredFfi : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun {F} s => ∃ (h : F = Guest.HostMemory) (input : Guest.InputBlob),
    Guest.GasLimit.declaredGasLimit input ≤ maxCoveredGas ∧
    OracleConsistent sourceOracle (Guest.guestHostMemory input)
      (cast (congrArg HolFfiState h) s.ffi)

/-- `GuestInv` plus the covered input; used only at `main`/`run_attempt` level, where the
header gas limit `≤ 2·10^8` must be read off the input. -/
def GuestInvCovered : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ CoveredFfi s

/-! ### Locals/clock independence (proved) -/

theorem guestInv_congr {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hcode : t.code = s.code) (hmem : t.memaddrs = s.memaddrs) (hsh : t.shMemaddrs = s.shMemaddrs)
    (hbase : t.baseAddr = s.baseAddr) (htop : t.topAddr = s.topAddr)
    (hglob : t.globals = s.globals) (h : GuestInv s) : GuestInv t := by
  obtain ⟨c, m, sh, b, tp, g, hp, ar, j⟩ := h
  have hk : GlobalWord t = GlobalWord s := by
    funext name w
    unfold GlobalWord
    rw [hglob]
  refine ⟨hcode.trans c, hmem.trans m, hsh.trans sh, hbase.trans b, htop.trans tp, ?_, ?_, ?_, ?_⟩
  · unfold GlobalsWellShaped; rw [hk]; exact g
  · rw [hk]; exact hp
  · rw [hk]; exact ar
  · rw [hk]; exact j

theorem guestInv_callEntry {F : Type} (s : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (h : GuestInv s) :
    GuestInv (callEntryStateHOLFinite s callee) :=
  guestInv_congr (s := s) rfl rfl rfl rfl rfl rfl h

theorem guestInv_with_locals_clock {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (h : GuestInv s) :
    GuestInv { s with locals := locals, clock := k } :=
  guestInv_congr (s := s) rfl rfl rfl rfl rfl rfl h

theorem guestInv_setVar {F : Type} (name : MlS) (v : ValueHOL 64)
    (s : PanSemStateFiniteExact 64 F) (h : GuestInv s) : GuestInv (setVarHOLFinite name v s) :=
  guestInv_congr (s := s) rfl rfl rfl rfl rfl rfl h

theorem guestInv_with_memory {F : Type} (s : PanSemStateFiniteExact 64 F)
    (memory : BitVec 64 → HolWordLab 64) (h : GuestInv s) :
    GuestInv { s with memory := memory } :=
  guestInv_congr (s := s) rfl rfl rfl rfl rfl rfl h

/-! ## 3. Guarded function bounds and preservation -/

/-- `fname` is installed and its body is bounded by `K` from every `P` entry state. -/
def TerminatingFunBoundedOn (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) (K : Nat) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    TerminatingProgBoundedOn P body K

/-- Every non-timeout run of `prog` from a `P` state ends in a `Q` state (whatever the result;
the post state of an `.error`/`.finalFfi` result is never continued, so requiring `Q` there
costs nothing for `GuestInv`, which holds at every intermediate state). -/
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

/-- Same definition as `PanTerminatingCallOn.CallEntryOn` (branch `wave8/step0-opus55`),
repeated so this file elaborates on `wave8/base2` alone. -/
def CallEntryOn (P Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (fname : MlS)
    (arguments : List (ExpHOL 64)) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL),
    state.code = originalRuntimeCode → P state →
    evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values →
    lookupCodeHOLFinite state.code.lookup fname values = some (body, callee, returnShape) →
    Pc (callEntryStateHOLFinite state callee)

/-- `GuestInv` needs no call-site work: it survives argument passing unchanged. -/
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

/-- Every frozen all-state bound is in particular a guarded bound. -/
theorem TerminatingFunBoundedOn.of_unconditional
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {fname : MlS} {K : Nat}
    (h : TerminatingFunBounded fname K) : TerminatingFunBoundedOn P fname K := by
  obtain ⟨params, body, ret, hlook, hb⟩ := h
  exact ⟨params, body, ret, hlook, fun state hcode _ => hb state hcode⟩

/-! ### Proposed combinators (statements; proofs are adaptations of `PanTerminatingCallOn`) -/

/-- Locals/clock independence of a predicate: what makes `dec`, `ite`, call entry and
caller-locals restoration free. `GuestInv`, `GuestInvReady`, `GuestInvCovered` satisfy it. -/
def LocalsFree (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (k : Nat), P s → P { s with locals := locals, clock := k }

theorem localsFree_guestInv : LocalsFree GuestInv :=
  fun s locals k h => guestInv_with_locals_clock s locals k h

/-- Call without handler, callee guarded by `Pc` and discharged by `CallEntryOn`.
Proof: `PanTerminatingCallOn.TerminatingProgBoundedOn.call` verbatim. -/
theorem TerminatingProgBoundedOn.call_on
    {P Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {fname : MlS} {B : Nat}
    (hf : TerminatingFunBoundedOn Pc fname B)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (hentry : CallEntryOn P Pc fname arguments) :
    TerminatingProgBoundedOn P (.call (some (destination, none)) fname arguments) (B + 1) := by
  sorry

/-- `GuestInv` instance of `call_on`: no call-site obligation at all. -/
theorem TerminatingProgBoundedOn.call_guestInv {fname : MlS} {B : Nat}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) :
    TerminatingProgBoundedOn GuestInv (.call (some (destination, none)) fname arguments)
      (B + 1) :=
  TerminatingProgBoundedOn.call_on hf destination arguments (callEntryOn_guestInv fname arguments)

/-- `decCall`: the continuation runs on `setVar name v {post with locals := caller locals}`;
`GuestInv` of that state follows from `GuestInv post` (callee preservation) by `LocalsFree`. -/
theorem TerminatingProgBoundedOn.decCall_guestInv {fname : MlS} {B Bc : Nat}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (hpres : FunPreservesOn GuestInv GuestInv fname)
    (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {continuation : ProgHOL 64}
    (hcont : TerminatingProgBoundedOn GuestInv continuation Bc) :
    TerminatingProgBoundedOn GuestInv (.decCall name shape fname arguments continuation)
      (B + Bc + 1) := by
  sorry

/-- Call with an exception handler (e.g. `run_frames` → `op_dispatch` with `EvmErr`):
the handler runs after the callee raised, on a `GuestInv` state. -/
theorem TerminatingProgBoundedOn.callHandle_guestInv {fname : MlS} {B Bh : Nat}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (hpres : FunPreservesOn GuestInv GuestInv fname)
    (destination : Option (VarKind × MlS)) (exn : MlS) (var : MlS) {handler : ProgHOL 64}
    (hh : TerminatingProgBoundedOn GuestInv handler Bh) (arguments : List (ExpHOL 64)) :
    TerminatingProgBoundedOn GuestInv
      (.call (some (destination, some (exn, var, handler))) fname arguments) (B + Bh + 1) := by
  sorry

/-- Guarded `seq`: the second program starts where the first ended, so it needs preservation. -/
theorem TerminatingProgBoundedOn.seq_on
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn P first a) (hp : PreservesOn P P first)
    (h2 : TerminatingProgBoundedOn P second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  sorry

theorem TerminatingProgBoundedOn.ite_on
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {cond : ExpHOL 64}
    {yes no : ProgHOL 64} {a b : Nat}
    (hyes : TerminatingProgBoundedOn P yes a) (hno : TerminatingProgBoundedOn P no b) :
    TerminatingProgBoundedOn P (.ite cond yes no) (max a b) := by
  sorry

theorem TerminatingProgBoundedOn.dec_on
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : LocalsFree P)
    (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} {K : Nat}
    (hbody : TerminatingProgBoundedOn P body K) :
    TerminatingProgBoundedOn P (.dec name shape init body) K := by
  sorry

/-- Preservation through a handler-free call (locals restored, globals from callee post). -/
theorem PreservesOn.call_guestInv {fname : MlS} (hpres : FunPreservesOn GuestInv GuestInv fname)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) :
    PreservesOn GuestInv GuestInv (.call (some (destination, none)) fname arguments) := by
  sorry

/-! ## 4. Bridge: covered entry ⊨ `GuestInv`, and guarded `main` ⇒ covered clock bound -/

/-- The 67 global declarations evaluate to the word `0` (each is `Decl.decl Shape.one n (const 0)`). -/
theorem postDecls_globals (input : Guest.InputBlob) (stCtxt : StructContextExact)
    (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hdecls : @evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls) :
    ∀ name ∈ guestGlobalNames, GlobalWord s_decls name 0 := by
  sorry

/-- The covered post-declarations state satisfies `GuestInv` (arenas in the `0`/`0` branch,
`heap_ptr = 0 ≤ 0xb0000000`, `journal_n = journal_cap = 0`). Nothing `main` does first is
needed; `mem_init` then moves to `GuestInvReady` (`mem_init_ready`). -/
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
  have hg := postDecls_globals input stCtxt s_decls hdecls
  have hw : ∀ name ∈ guestGlobalNames, ∃ w, GlobalWord s_decls name w :=
    fun name hn => ⟨0, hg name hn⟩
  refine ⟨?_, hmeta.memaddrs, hmeta.shMemaddrs, hmeta.baseAddr, hmeta.topAddr, hw,
    ⟨0, hg "heap_ptr" (by decide), by decide⟩,
    ⟨0, 0, hg "frame_mem_ptr" (by decide), hg "scratch_ptr" (by decide), Or.inl ⟨rfl, rfl⟩⟩,
    ⟨0, 0, hg "journal_n" (by decide), hg "journal_cap" (by decide), le_refl _, by decide⟩⟩
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

/-- Main bridge (the replacement of `coveredSourceTicksConsumedBounded_of_terminatingMain`). -/
theorem coveredSourceTicksConsumedBounded_of_terminatingMainOn {K : Nat}
    (hmain : TerminatingFunBoundedOn GuestInv (ofString "main") K) :
    CoveredSourceTicksConsumedBounded (K + 1) := by
  sorry

/-- Covered variant: the guarded main bound may also use the covered input (gas ≤ 2·10^8). -/
theorem coveredSourceTicksConsumedBounded_of_terminatingMainOnCovered {K : Nat}
    (hmain : TerminatingFunBoundedOn GuestInvCovered (ofString "main") K) :
    CoveredSourceTicksConsumedBounded (K + 1) := by
  sorry

/-! ## 5. Memory well-formedness predicates (entry preconditions of specific leaves only) -/

/-- Aligned in-domain word `a` holds `w` (exactly what a successful `load` reads). -/
def MemWord {F : Type} (s : PanSemStateFiniteExact 64 F) (a w : BitVec 64) : Prop :=
  s.memaddrs a ∧ s.memory a = .word w

/-- `[a, a+la)` and `[b, b+lb)` are disjoint (as natural-number intervals). -/
def RangesDisjoint (a la b lb : Nat) : Prop := a + la ≤ b ∨ b + lb ≤ a

/-- A local variable holding a word. -/
def LocalWord {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) (w : BitVec 64) :
    Prop :=
  s.locals.lookup (ofString name) = some (.val (.word w))

/-- Layout of a crit-bit table header `t` (offsets from `htab_new`, `SoftwareAst.lean:4869`):
`+0` key_len ≤ 52, `+8` stride = round8 key_len, `+24` count ≤ `+80` node capacity,
`+32/+40/+48` keys/nodes/order arrays of `ncap+1` entries, all inside the heap or scratch
arena and disjoint from the 88-byte header and from each other; every child index stored in
a node is `≤ ncap`. -/
def HtabWF {F : Type} (s : PanSemStateFiniteExact 64 F) (t : BitVec 64) : Prop :=
  ∃ klen stride cnt keys nodes order ncap : BitVec 64,
    MemWord s t klen ∧ MemWord s (t + 8) stride ∧ MemWord s (t + 24) cnt ∧
    MemWord s (t + 32) keys ∧ MemWord s (t + 40) nodes ∧ MemWord s (t + 48) order ∧
    MemWord s (t + 80) ncap ∧
    klen.toNat ≤ maxKeyLen ∧ stride.toNat = (klen.toNat + 7) / 8 * 8 ∧
    cnt.toNat ≤ ncap.toNat ∧ (ncap.toNat + 1) * 32 ≤ heapArenaBytes ∧
    sourceBase ≤ t.toNat ∧ t.toNat + 88 ≤ scratchEnd ∧
    (∀ base len, (base, len) ∈ [(keys.toNat, (ncap.toNat + 1) * stride.toNat),
        (nodes.toNat, (ncap.toNat + 1) * 32), (order.toNat, (ncap.toNat + 1) * 8)] →
      sourceBase ≤ base ∧ base + len ≤ scratchEnd ∧ RangesDisjoint base len t.toNat 88) ∧
    RangesDisjoint keys.toNat ((ncap.toNat + 1) * stride.toNat)
      nodes.toNat ((ncap.toNat + 1) * 32) ∧
    RangesDisjoint keys.toNat ((ncap.toNat + 1) * stride.toNat)
      order.toNat ((ncap.toNat + 1) * 8) ∧
    RangesDisjoint nodes.toNat ((ncap.toNat + 1) * 32) order.toNat ((ncap.toNat + 1) * 8) ∧
    (∀ n : Nat, n ≤ ncap.toNat → ∀ off ∈ [8, 16], ∃ c : BitVec 64,
      MemWord s (nodes + BitVec.ofNat 64 (32 * n + off)) c ∧ c.toNat ≤ ncap.toNat)

/-- Entry precondition: the table argument `t` is well formed. -/
def HtabArgWF : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ ∃ t, LocalWord s "t" t ∧ HtabWF s t

/-- One EVM frame record `e` (offsets from `frame_new`, `SoftwareAst.lean:15372`): 280 bytes in
the scratch arena; its EVM memory `[e+24, e+24 + cap(e+40))` lies in the frame-memory arena
below `frame_mem_ptr`, hence disjoint from every frame record and stack. -/
def FrameRecWF {F : Type} (s : PanSemStateFiniteExact 64 F) (fm sp e : BitVec 64) : Prop :=
  ∃ mem cap len : BitVec 64,
    sp.toNat ≤ e.toNat ∧ e.toNat + 280 ≤ scratchEnd ∧
    MemWord s (e + 24) mem ∧ MemWord s (e + 40) cap ∧ MemWord s (e + 32) len ∧
    scratchStart ≤ mem.toNat ∧ mem.toNat + cap.toNat ≤ fm.toNat ∧ len.toNat ≤ cap.toNat

/-- The active chain: `ev`, then parents through the continuation records (`cur_cont+16 = 0`
marks the outermost frame, `+0`/`+8` hold the parent `ev`/`cur_cont`; `run_frames`,
`SoftwareAst.lean:18665`). At most `d` frames; the regular plus state gas (`+64`, `+72`) summed
over the chain is at most `g`. -/
def FrameChainWF {F : Type} (s : PanSemStateFiniteExact 64 F) (fm sp : BitVec 64) :
    Nat → BitVec 64 → BitVec 64 → Nat → Prop
  | 0, _, _, _ => False
  | d + 1, e, cont, g => ∃ gas sgas top : BitVec 64,
      FrameRecWF s fm sp e ∧ MemWord s (e + 64) gas ∧ MemWord s (e + 72) sgas ∧
      gas.toNat + sgas.toNat ≤ g ∧ MemWord s (cont + 16) top ∧
      (top = 0 ∨ ∃ pe pc : BitVec 64, MemWord s cont pe ∧ MemWord s (cont + 8) pc ∧
        FrameChainWF s fm sp d pe pc (g - gas.toNat - sgas.toNat))

/-- `run_frames` entry precondition with gas budget `G`. -/
def EvmFramesWF (G : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInvReady s ∧ ∃ fm sp e cont : BitVec 64,
    GlobalWord s "frame_mem_ptr" fm ∧ GlobalWord s "scratch_ptr" sp ∧
    GlobalWord s "ev" e ∧ GlobalWord s "cur_cont" cont ∧ FrameChainWF s fm sp maxFrames e cont G

/-- `process_message` entry: the message's regular (`msg+40`) and state (`msg+48`) gas,
copied by `frame_new` into the first frame, sum to at most `G`. -/
def MsgGasCapped (G : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInvReady s ∧ ∃ msg g sg : BitVec 64,
    LocalWord s "msg" msg ∧ MemWord s (msg + 40) g ∧ MemWord s (msg + 48) sg ∧
    g.toNat + sg.toNat ≤ G

/-- `process_transaction` entry: block gas limit `be+8` (set by `run_attempt` from header
`+104`, `SoftwareAst.lean:33817`) is at most `G`; `check_transaction` bounds tx gas by it. -/
def BlockGasCapped (G : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInvReady s ∧ ∃ be lim : BitVec 64,
    GlobalWord s "be" be ∧ MemWord s (be + 8) lim ∧ lim.toNat ≤ G

/-! ## 6. Restated leaf interface -/

namespace R

/-- Iterations of any loop that touches a fresh address per iteration (memory walks,
`memcpy`/`memzero`/`memeq`, array scans) from a `GuestInv` state. -/
def W : Nat := domainBytes
def H : Nat := heapArenaBytes
def J : Nat := journalCapMax
def D : Nat := maxFrames
def G : Nat := maxCoveredGas
def KL : Nat := maxKeyLen

/-! ### Primitives and hash tables (all-memory, `GuestInv` only) -/
def K_walk : Nat := 4 * W + 64
def K_htab_find_leaf : Nat := 4 * W + 4096
def K_htab_first_diff : Nat := W + 4096
def K_htab_set : Nat := 4 * K_htab_find_leaf + 8 * K_walk + 2 * K_htab_first_diff + 65536
def K_htab_del : Nat := 4 * K_htab_find_leaf + 8 * K_walk + 2 * K_htab_first_diff + 65536
def K_htab_keys : Nat := (W / 8 + 1) * (K_walk + 64) + 128
/-- Requires `HtabWF` (count lives in memory and is rewritten by every deletion). -/
def K_htab_truncate : Nat := (H / 32 + 1) * (K_htab_del + 64) + 64
def K_htab_union_into : Nat := (H / 32 + 1) * (K_htab_set + 64) + 64
def K_nodedb_build : Nat := W * (K_htab_set + 512) + 256
/-! Data-structure refinements (`HtabWF`: key_len ≤ 52, node indices ≤ ncap ≤ H/32). -/
def K_htab_find_leaf_wf : Nat := H / 32 + 4096
def K_htab_set_wf : Nat :=
  4 * K_htab_find_leaf_wf + 8 * (4 * KL + 64) + 2 * (9 * KL + 4096) + 3 * (4 * H + 64) + 65536
def K_htab_keys_wf : Nat := (H / 32 + 1) * (4 * (KL + 7) + 128) + 128

/-! ### RLP / MPT witness / MPT insert-delete -/
def K_rlp_validate_items_body : Nat := 8 * W + 4096
def K_rlp_list_count : Nat := K_rlp_validate_items_body + 2 * W + 128
def K_rlp_list_to_slices : Nat := K_rlp_list_count + 4 * W + 256
def K_decode_account_from_leaf : Nat := 4 * K_rlp_list_to_slices + 8 * W + 512
def K_tx_scalar_word : Nat := 2 * W + 128
def K_hdr_word_field : Nat := 2 * W + 128
def K_decode_access_list : Nat := 4 * W * K_rlp_list_to_slices + 1024
def K_decode_authorizations : Nat := 2 * W * (K_rlp_list_to_slices + K_tx_scalar_word) + 1024
def K_decode_blob_hashes : Nat := 2 * W * K_rlp_list_to_slices + 512
def K_decode_witness_node_body : Nat := 16 * W + 65536
def K_trie_walk : Nat := 4 * W + 4096
def K_node_rlp_finish : Nat := 2 * W + 4096
def K_node_rlp_fill : Nat := 18 * W * (K_node_rlp_finish + 64) + 8192
def K_collapse_branch : Nat := 2 * W + 1024
def K_mpt_insert_node : Nat := 4 * W + 8192
def K_mpt_delete_node_body : Nat := 8 * W * (K_collapse_branch + 128) + 16384
def K_build_mpt_indexed : Nat := 4 * W * (K_mpt_insert_node + K_node_rlp_fill + 256) + 8192

/-! ### State and journal -/
def K_get_account : Nat :=
  K_htab_find_leaf + K_trie_walk + K_decode_account_from_leaf + K_htab_set + 8192
def K_get_storage : Nat := K_get_account + K_htab_find_leaf + K_trie_walk + K_htab_set + 8192
def K_set_storage : Nat := K_get_storage + K_htab_set + 4096
/-- `journal_n ≤ journal_cap ≤ 2^19` (`GuestInv`); the body never writes `journal_n` except the
decrement, and `htab_set`/`htab_del` write no globals. -/
def K_state_restore : Nat := J * (K_htab_set + K_htab_del + 256) + 8192

/-! ### Arithmetic / crypto (constants unchanged where already data-independent) -/
def K_modinv_bin : Nat := 2048 * 256 + 4096
def K_fp_inv : Nat := K_modinv_bin + 4096
def K_fn_inv : Nat := K_modinv_bin + 4096
def K_u256_addmod : Nat := 4096
def K_u256_mulmod : Nat := 16384
def K_pre_modexp : Nat := 64 * W * (W + 4096) + 1048576
def K_p256_fp_mul : Nat := 1024
def K_p256_fp_sqr : Nat := 1024
def K_p256_ec_mul2 : Nat := 256 * 32 * (K_p256_fp_mul + K_p256_fp_sqr + 256) + 65536
def K_pre_p256verify : Nat := 4 * K_p256_ec_mul2 + 4 * K_modinv_bin + 65536
def K_secp256k1_ecrecover : Nat := 4 * K_p256_ec_mul2 + 4 * K_modinv_bin + 131072
def K_pre_ecrecover : Nat := K_secp256k1_ecrecover + 8192
def K_bn_divmnu : Nat := 16 * W * (W + 4096) + 65536
def K_fq12_inv : Nat := 16 * 16 * (K_modinv_bin + 16384) + 262144
def K_pre_alt_bn128_add : Nat := 4 * K_modinv_bin + 65536
def K_pre_alt_bn128_mul : Nat := 256 * K_pre_alt_bn128_add + 65536
def K_pre_alt_bn128_pairing_check : Nat := 16 * W * (K_fq12_inv + 262144) + 1048576
def K_bls_fp_inv_raw : Nat := 4096 * 512 + 16384
def K_bls_fp_inv : Nat := K_bls_fp_inv_raw + 8192
def K_fp2_inv : Nat := 2 * K_bls_fp_inv + 16384
def K_fp12_inv : Nat := 4 * K_fp2_inv + 131072
def K_g1_mul : Nat := 256 * 16384 + 2 * K_bls_fp_inv + 65536
def K_g2_mul : Nat := 256 * 65536 + 2 * K_fp2_inv + 131072
def K_pre_kzg_point_evaluation : Nat := 8 * (K_fp12_inv + K_g1_mul + K_g2_mul) + 2097152
def K_pre_bls_g1_add : Nat := 4 * K_bls_fp_inv + 131072
def K_pre_bls_g1_msm : Nat := 8 * W * K_g1_mul + 262144
def K_pre_bls_g2_add : Nat := 4 * K_fp2_inv + 262144
def K_pre_bls_g2_msm : Nat := 8 * W * K_g2_mul + 524288
def K_pre_bls_pairing : Nat := 16 * W * (K_fp12_inv + 524288) + 2097152
def K_pre_bls_map_fp_to_g1 : Nat := 8 * K_bls_fp_inv + 524288
def K_pre_bls_map_fp2_to_g2 : Nat := 8 * K_fp2_inv + 1048576

/-! ### SSZ, sorting, post-state -/
def K_pack_bytes : Nat := 4 * W + 4096
def K_merkleize : Nat := 128 * W + 65536
def K_merkleize_progressive : Nat := 64 * (K_merkleize + 4096) + 65536
def K_htr_bytes_list : Nat := K_pack_bytes + K_merkleize + 4096
def K_htr_plist_chunks : Nat := 2 * W + K_merkleize_progressive + 4096
def K_htr_payload : Nat :=
  8 * (K_htr_bytes_list + K_htr_plist_chunks + K_merkleize_progressive) + 65536
def K_htr_new_payload_request : Nat := 4 * K_htr_payload + 4 * K_htr_plist_chunks + 65536
def K_sort_elems : Nat := 64 * 8 * W + 65536
def K_compute_state_root : Nat :=
  4 * W * (K_sort_elems + K_mpt_insert_node + K_mpt_delete_node_body + 65536) + 262144
def K_build_block_access_list_rlp : Nat := 8 * W * (K_sort_elems + 4096) + 262144
def K_compute_block_commitments : Nat :=
  K_compute_state_root + K_build_block_access_list_rlp + 4 * K_build_mpt_indexed + 524288

/-! ### EVM -/
def K_keccak256 : Nat := (W / 136 + 2) * 256 + K_walk
def K_compute_jumpdests : Nat := 4 * W + 4096
def K_run_precompile : Nat :=
  K_pre_ecrecover + K_pre_modexp + K_pre_alt_bn128_pairing_check +
  K_pre_kzg_point_evaluation + K_pre_bls_g1_msm + K_pre_bls_g2_msm +
  K_pre_bls_pairing + K_pre_bls_map_fp2_to_g2 + K_pre_p256verify + 8 * W + 4194304
/-- Includes the omitted `state_restore` call (the source of the frozen counterexample). -/
def K_frame_epilogue : Nat := K_state_restore + 256
def K_create_finish : Nat := 2 * K_keccak256 + 4 * K_walk + 4 * K_get_account + 65536
/-- Sum over all direct callees of `finish_child` (incl. `state_restore`, `create_finish`). -/
def K_finish_child : Nat :=
  K_state_restore + K_create_finish + 16 * (K_walk + K_get_account) + 1048576
def K_op_exp : Nat := 32 * 8 * 512 + 16384
def K_op_memory_copy : Nat := 8 * W + K_keccak256 + K_get_account + 65536
def K_op_env_account : Nat := 2 * K_get_account + 4 * W + 65536
def K_op_sstore : Nat := 4 * K_set_storage + 65536
def K_generic_call : Nat :=
  4 * K_get_account + K_run_precompile + K_compute_jumpdests + K_state_restore + 262144
def K_generic_create : Nat :=
  4 * K_get_account + K_compute_jumpdests + K_state_restore + K_keccak256 + 8 * W + 262144
def K_op_selfdestruct : Nat := 4 * K_get_account + K_state_restore + 65536
def K_op_dispatch : Nat :=
  K_generic_call + K_generic_create + K_op_sstore + K_op_selfdestruct +
  K_op_exp + K_op_memory_copy + K_op_env_account + 524288
/-- `Φ = 2050·gas + 2·frames` (`PanTerminatingBounded.evmFramePotential`) with gas ≤ `Gas`. -/
def maxRunFramesIters (Gas : Nat) : Nat := 2050 * Gas + 2 * D + 4096
def K_run_frames (Gas : Nat) : Nat :=
  maxRunFramesIters Gas * (K_op_dispatch + K_frame_epilogue + K_finish_child + 256) + 65536
def K_process_message (Gas : Nat) : Nat :=
  K_run_frames Gas + K_run_precompile + K_compute_jumpdests + 262144

/-! ### Transactions, block, main -/
def K_process_transaction (Gas : Nat) : Nat :=
  K_decode_access_list + K_decode_authorizations + K_decode_blob_hashes +
  4 * K_secp256k1_ecrecover + K_process_message Gas + K_state_restore + 1048576
def K_run_attempt (Gas : Nat) : Nat :=
  W * (K_process_transaction Gas + 65536) + 4 * K_process_message Gas +
  K_compute_block_commitments + 4194304
def K_main_body (Gas : Nat) : Nat :=
  16 * K_htr_new_payload_request + 8 * K_run_attempt Gas + 16 * W + 16777216

end R

/-- The proposed total source budget (covered gas `2·10^8`). -/
def K_pan : Nat := R.K_main_body R.G + 1

/-- Fallback if the input→header gas link is not proved: gas bounded only by the word size. -/
def K_pan_wordGas : Nat := R.K_main_body (2 ^ 64) + 1

/-- Kernel-checked budget inequality (target side `32·K + 23077`). -/
theorem K_pan_budget : 32 * K_pan + 23077 ≤ (10 ^ 299 - 1) / 10 ^ 4 := by decide

theorem K_pan_wordGas_budget : 32 * K_pan_wordGas + 23077 ≤ (10 ^ 299 - 1) / 10 ^ 4 := by
  decide

/-- Headroom: `K_pan < 10^60`, so every constant above may be multiplied by `10^230`. -/
theorem K_pan_lt : K_pan < 10 ^ 60 := by decide

theorem K_pan_wordGas_lt : K_pan_wordGas < 10 ^ 70 := by decide

/-! ### 6a. The four FALSE leaves, restated -/

/-- FALSE frozen (`4·(2^64-1)+65536`, missing `state_restore`). Counterexample excluded: the
odd key pointer `1` aligns to `0 ∉ ordinaryDomain`, so `memeq` errors on its first load, and
`journal_n ≤ 2^19`. -/
theorem frame_epilogue_on :
    TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") R.K_frame_epilogue := by
  sorry

/-- Same composition argument; `finish_child` has no loop. -/
theorem finish_child_on :
    TerminatingFunBoundedOn GuestInv (ofString "finish_child") R.K_finish_child := by
  sorry

/-- FALSE frozen (`n·stride` wrap). With `GuestInv`, each iteration loads `order+8i` (a fresh
address), so at most `W/8+1` iterations; each `memcpy` is a walk of at most `W` bytes. -/
theorem htab_keys_on :
    TerminatingFunBoundedOn GuestInv (ofString "htab_keys") R.K_htab_keys := by
  sorry

/-- Data-structure refinement: `n ≤ ncap ≤ H/32`, `stride ≤ 56`. -/
theorem htab_keys_on_wf :
    TerminatingFunBoundedOn HtabArgWF (ofString "htab_keys") R.K_htab_keys_wf := by
  sorry

/-- FALSE frozen (`memeq(1,1,2^63)`). With `GuestInv` every scan is domain-bounded. -/
theorem htab_set_on :
    TerminatingFunBoundedOn GuestInv (ofString "htab_set") R.K_htab_set := by
  sorry

/-- Data-structure refinement: key length ≤ 52, node indices ≤ ncap. -/
theorem htab_set_on_wf :
    TerminatingFunBoundedOn HtabArgWF (ofString "htab_set") R.K_htab_set_wf := by
  sorry

/-! ### 6b. Journal / state (dependencies of the FALSE leaves) -/

theorem htab_find_leaf_on :
    TerminatingFunBoundedOn GuestInv (ofString "htab_find_leaf") R.K_htab_find_leaf := by sorry
theorem htab_del_on :
    TerminatingFunBoundedOn GuestInv (ofString "htab_del") R.K_htab_del := by sorry
theorem state_restore_on :
    TerminatingFunBoundedOn GuestInv (ofString "state_restore") R.K_state_restore := by sorry
theorem get_account_on :
    TerminatingFunBoundedOn GuestInv (ofString "get_account") R.K_get_account := by sorry
theorem get_storage_on :
    TerminatingFunBoundedOn GuestInv (ofString "get_storage") R.K_get_storage := by sorry
theorem set_storage_on :
    TerminatingFunBoundedOn GuestInv (ofString "set_storage") R.K_set_storage := by sorry

/-! ### 6c. Leaves whose loop measure lives in memory: explicit well-formedness -/

theorem htab_truncate_on_wf :
    TerminatingFunBoundedOn HtabArgWF (ofString "htab_truncate") R.K_htab_truncate := by sorry
/-- Precondition on the destination table argument `t`; see DESIGN.md (open question Q4). -/
theorem htab_union_into_on_wf :
    TerminatingFunBoundedOn HtabArgWF (ofString "htab_union_into") R.K_htab_union_into := by
  sorry
theorem run_frames_on :
    TerminatingFunBoundedOn (EvmFramesWF R.G) (ofString "run_frames") (R.K_run_frames R.G) := by
  sorry
theorem process_message_on :
    TerminatingFunBoundedOn (MsgGasCapped R.G) (ofString "process_message")
      (R.K_process_message R.G) := by sorry
theorem process_transaction_on :
    TerminatingFunBoundedOn (BlockGasCapped R.G) (ofString "process_transaction")
      (R.K_process_transaction R.G) := by sorry
theorem run_attempt_on :
    TerminatingFunBoundedOn GuestInvCovered (ofString "run_attempt") (R.K_run_attempt R.G) := by
  sorry
/-- Fallback chain if the header↔input gas link (Q1) is not proved: gas is a 64-bit word. -/
theorem run_attempt_on_wordGas :
    TerminatingFunBoundedOn GuestInv (ofString "run_attempt") (R.K_run_attempt (2 ^ 64)) := by
  sorry

/-! ### 6d. `main` and its initialisation prefix -/

theorem mem_init_ready :
    PreservesOn GuestInv GuestInvReady
      (sourceFunctionEntry Guest.Software.guestFn_mem_init).2.2.1 := by sorry
theorem main_on_covered :
    TerminatingFunBoundedOn GuestInvCovered (ofString "main") (R.K_main_body R.G) := by sorry
theorem main_on_wordGas :
    TerminatingFunBoundedOn GuestInv (ofString "main") (R.K_main_body (2 ^ 64)) := by sorry

/-- End-to-end target of the campaign under this proposal. -/
theorem coveredSourceTicksConsumedBounded_K_pan : CoveredSourceTicksConsumedBounded K_pan :=
  coveredSourceTicksConsumedBounded_of_terminatingMainOnCovered main_on_covered

/-! ### 6e. Remaining frozen declarations (audit: UNCLEAR), restated over `GuestInv` -/

theorem rlp_validate_items_body_on : TerminatingFunBoundedOn GuestInv
    (ofString "_rlp_validate_items_body") R.K_rlp_validate_items_body := by sorry
theorem rlp_list_count_on : TerminatingFunBoundedOn GuestInv
    (ofString "rlp_list_count") R.K_rlp_list_count := by sorry
theorem rlp_list_to_slices_on : TerminatingFunBoundedOn GuestInv
    (ofString "rlp_list_to_slices") R.K_rlp_list_to_slices := by sorry
theorem decode_account_from_leaf_on : TerminatingFunBoundedOn GuestInv
    (ofString "decode_account_from_leaf") R.K_decode_account_from_leaf := by sorry
theorem tx_scalar_word_on : TerminatingFunBoundedOn GuestInv
    (ofString "tx_scalar_word") R.K_tx_scalar_word := by sorry
theorem hdr_word_field_on : TerminatingFunBoundedOn GuestInv
    (ofString "hdr_word_field") R.K_hdr_word_field := by sorry
theorem decode_access_list_on : TerminatingFunBoundedOn GuestInv
    (ofString "decode_access_list") R.K_decode_access_list := by sorry
theorem decode_authorizations_on : TerminatingFunBoundedOn GuestInv
    (ofString "decode_authorizations") R.K_decode_authorizations := by sorry
theorem decode_blob_hashes_on : TerminatingFunBoundedOn GuestInv
    (ofString "decode_blob_hashes") R.K_decode_blob_hashes := by sorry
theorem decode_witness_node_body_on : TerminatingFunBoundedOn GuestInv
    (ofString "_decode_witness_node_body") R.K_decode_witness_node_body := by sorry
theorem trie_walk_on : TerminatingFunBoundedOn GuestInv
    (ofString "trie_walk") R.K_trie_walk := by sorry
theorem node_rlp_finish_on : TerminatingFunBoundedOn GuestInv
    (ofString "_node_rlp_finish") R.K_node_rlp_finish := by sorry
theorem node_rlp_fill_on : TerminatingFunBoundedOn GuestInv
    (ofString "_node_rlp_fill") R.K_node_rlp_fill := by sorry
theorem collapse_branch_on : TerminatingFunBoundedOn GuestInv
    (ofString "_collapse_branch") R.K_collapse_branch := by sorry
theorem mpt_insert_node_on : TerminatingFunBoundedOn GuestInv
    (ofString "_mpt_insert_node") R.K_mpt_insert_node := by sorry
theorem mpt_delete_node_body_on : TerminatingFunBoundedOn GuestInv
    (ofString "_mpt_delete_node_body") R.K_mpt_delete_node_body := by sorry
theorem build_mpt_indexed_on : TerminatingFunBoundedOn GuestInv
    (ofString "build_mpt_indexed") R.K_build_mpt_indexed := by sorry
theorem nodedb_build_on : TerminatingFunBoundedOn GuestInv
    (ofString "nodedb_build") R.K_nodedb_build := by sorry
theorem modinv_bin_on : TerminatingFunBoundedOn GuestInv
    (ofString "modinv_bin") R.K_modinv_bin := by sorry
theorem fp_inv_on : TerminatingFunBoundedOn GuestInv (ofString "fp_inv") R.K_fp_inv := by sorry
theorem fn_inv_on : TerminatingFunBoundedOn GuestInv (ofString "fn_inv") R.K_fn_inv := by sorry
theorem u256_addmod_on : TerminatingFunBoundedOn GuestInv
    (ofString "u256_addmod") R.K_u256_addmod := by sorry
theorem u256_mulmod_on : TerminatingFunBoundedOn GuestInv
    (ofString "u256_mulmod") R.K_u256_mulmod := by sorry
theorem pre_modexp_on : TerminatingFunBoundedOn GuestInv
    (ofString "pre_modexp") R.K_pre_modexp := by sorry
theorem p256_fp_mul_on : TerminatingFunBoundedOn GuestInv
    (ofString "p256_fp_mul") R.K_p256_fp_mul := by sorry
theorem p256_fp_sqr_on : TerminatingFunBoundedOn GuestInv
    (ofString "p256_fp_sqr") R.K_p256_fp_sqr := by sorry
theorem pre_p256verify_on : TerminatingFunBoundedOn GuestInv
    (ofString "pre_p256verify") R.K_pre_p256verify := by sorry
theorem secp256k1_ecrecover_on : TerminatingFunBoundedOn GuestInv
    (ofString "secp256k1_ecrecover") R.K_secp256k1_ecrecover := by sorry
theorem pre_ecrecover_on : TerminatingFunBoundedOn GuestInv
    (ofString "pre_ecrecover") R.K_pre_ecrecover := by sorry
theorem bn_divmnu_on : TerminatingFunBoundedOn GuestInv
    (ofString "bn_divmnu") R.K_bn_divmnu := by sorry
theorem fq12_inv_on : TerminatingFunBoundedOn GuestInv
    (ofString "fq12_inv") R.K_fq12_inv := by sorry
theorem pre_alt_bn128_add_on : TerminatingFunBoundedOn GuestInv
    (ofString "pre_alt_bn128_add") R.K_pre_alt_bn128_add := by sorry
theorem pre_alt_bn128_mul_on : TerminatingFunBoundedOn GuestInv
    (ofString "pre_alt_bn128_mul") R.K_pre_alt_bn128_mul := by sorry
theorem pre_alt_bn128_pairing_check_on : TerminatingFunBoundedOn GuestInv
    (ofString "pre_alt_bn128_pairing_check") R.K_pre_alt_bn128_pairing_check := by sorry
theorem bls_fp_inv_raw_on : TerminatingFunBoundedOn GuestInv
    (ofString "bls_fp_inv_raw") R.K_bls_fp_inv_raw := by sorry
theorem bls_fp_inv_on : TerminatingFunBoundedOn GuestInv
    (ofString "bls_fp_inv") R.K_bls_fp_inv := by sorry
theorem fp2_inv_on : TerminatingFunBoundedOn GuestInv (ofString "fp2_inv") R.K_fp2_inv := by
  sorry
theorem fp12_inv_on : TerminatingFunBoundedOn GuestInv (ofString "fp12_inv") R.K_fp12_inv := by
  sorry
theorem g1_mul_on : TerminatingFunBoundedOn GuestInv (ofString "g1_mul") R.K_g1_mul := by sorry
theorem g2_mul_on : TerminatingFunBoundedOn GuestInv (ofString "g2_mul") R.K_g2_mul := by sorry
theorem pre_kzg_point_evaluation_on : TerminatingFunBoundedOn GuestInv
    (ofString "pre_kzg_point_evaluation") R.K_pre_kzg_point_evaluation := by sorry
theorem pre_bls_g1_add_on : TerminatingFunBoundedOn GuestInv
    (ofString "pre_bls_g1_add") R.K_pre_bls_g1_add := by sorry
theorem pre_bls_g1_msm_on : TerminatingFunBoundedOn GuestInv
    (ofString "pre_bls_g1_msm") R.K_pre_bls_g1_msm := by sorry
theorem pre_bls_g2_add_on : TerminatingFunBoundedOn GuestInv
    (ofString "pre_bls_g2_add") R.K_pre_bls_g2_add := by sorry
theorem pre_bls_g2_msm_on : TerminatingFunBoundedOn GuestInv
    (ofString "pre_bls_g2_msm") R.K_pre_bls_g2_msm := by sorry
theorem pre_bls_pairing_on : TerminatingFunBoundedOn GuestInv
    (ofString "pre_bls_pairing") R.K_pre_bls_pairing := by sorry
theorem pre_bls_map_fp_to_g1_on : TerminatingFunBoundedOn GuestInv
    (ofString "pre_bls_map_fp_to_g1") R.K_pre_bls_map_fp_to_g1 := by sorry
theorem pre_bls_map_fp2_to_g2_on : TerminatingFunBoundedOn GuestInv
    (ofString "pre_bls_map_fp2_to_g2") R.K_pre_bls_map_fp2_to_g2 := by sorry
theorem pack_bytes_on : TerminatingFunBoundedOn GuestInv
    (ofString "pack_bytes") R.K_pack_bytes := by sorry
theorem merkleize_on : TerminatingFunBoundedOn GuestInv
    (ofString "merkleize") R.K_merkleize := by sorry
theorem merkleize_progressive_on : TerminatingFunBoundedOn GuestInv
    (ofString "merkleize_progressive") R.K_merkleize_progressive := by sorry
theorem htr_bytes_list_on : TerminatingFunBoundedOn GuestInv
    (ofString "htr_bytes_list") R.K_htr_bytes_list := by sorry
theorem htr_plist_chunks_on : TerminatingFunBoundedOn GuestInv
    (ofString "htr_plist_chunks") R.K_htr_plist_chunks := by sorry
theorem htr_payload_on : TerminatingFunBoundedOn GuestInv
    (ofString "htr_payload") R.K_htr_payload := by sorry
theorem htr_new_payload_request_on : TerminatingFunBoundedOn GuestInv
    (ofString "htr_new_payload_request") R.K_htr_new_payload_request := by sorry
theorem sort_elems_on : TerminatingFunBoundedOn GuestInv
    (ofString "sort_elems") R.K_sort_elems := by sorry
theorem compute_state_root_on : TerminatingFunBoundedOn GuestInv
    (ofString "compute_state_root") R.K_compute_state_root := by sorry
theorem build_block_access_list_rlp_on : TerminatingFunBoundedOn GuestInv
    (ofString "build_block_access_list_rlp") R.K_build_block_access_list_rlp := by sorry
theorem compute_jumpdests_on : TerminatingFunBoundedOn GuestInv
    (ofString "compute_jumpdests") R.K_compute_jumpdests := by sorry
theorem run_precompile_on : TerminatingFunBoundedOn GuestInv
    (ofString "run_precompile") R.K_run_precompile := by sorry
theorem op_exp_on : TerminatingFunBoundedOn GuestInv (ofString "op_exp") R.K_op_exp := by sorry
theorem op_keccak_on : TerminatingFunBoundedOn GuestInv
    (ofString "op_keccak") R.K_op_memory_copy := by sorry
theorem op_extcodecopy_on : TerminatingFunBoundedOn GuestInv
    (ofString "op_extcodecopy") R.K_op_memory_copy := by sorry
theorem op_balance_on : TerminatingFunBoundedOn GuestInv
    (ofString "op_balance") R.K_op_env_account := by sorry
theorem op_extcodehash_on : TerminatingFunBoundedOn GuestInv
    (ofString "op_extcodehash") R.K_op_env_account := by sorry
theorem op_sstore_on : TerminatingFunBoundedOn GuestInv
    (ofString "op_sstore") R.K_op_sstore := by sorry
theorem generic_call_on : TerminatingFunBoundedOn GuestInv
    (ofString "generic_call") R.K_generic_call := by sorry
theorem generic_create_on : TerminatingFunBoundedOn GuestInv
    (ofString "generic_create") R.K_generic_create := by sorry
theorem op_selfdestruct_on : TerminatingFunBoundedOn GuestInv
    (ofString "op_selfdestruct") R.K_op_selfdestruct := by sorry
theorem op_dispatch_on : TerminatingFunBoundedOn GuestInv
    (ofString "op_dispatch") R.K_op_dispatch := by sorry

end InitECandidate.Solver.Wave8GuestInv
