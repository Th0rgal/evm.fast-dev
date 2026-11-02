import InitECandidate.Solver.PanTerminatingBounded

/-! Revision-7 definitions and proved combinators for light-cone verification. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S00Spec

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
def «rlp_read_length» : Nat := Nat.max ((«rlp_fail» + 1)) (0) + ((domainBytes + 1) + 1) * (0 + 1)

/-- `rlp_item_header` (AST line 4432), log2 ≈ 66. -/
def «rlp_item_header» : Nat := Nat.max ((«rlp_fail» + 1)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0)) (0)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0) + («rlp_read_length» + 1) + Nat.max ((«rlp_fail» + 1)) (0) + Nat.max ((«rlp_fail» + 1)) (0)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0)) (0) + Nat.max ((«rlp_fail» + 1)) (0) + («rlp_read_length» + 1) + Nat.max ((«rlp_fail» + 1)) (0) + Nat.max ((«rlp_fail» + 1)) (0)

/-- `scratch_alloc` (AST line 154), log2 ≈ 2. -/
def «scratch_alloc» : Nat := Nat.max ((«trap_with» + 1)) (0) + Nat.max ((«trap_with» + 1)) (0)

/-- `_rlp_validate_items_body` (AST line 4507), log2 ≈ 319. -/
def «_rlp_validate_items_body» : Nat := (62209915858 + 1) * (Nat.max (0) ((«rlp_item_header» + 1) + Nat.max ((«scratch_alloc» + 1)) (0)) + 1)

/-- `scratch_mark` (AST line 176), log2 ≈ 0. -/
def «scratch_mark» : Nat := 0

/-- `scratch_release` (AST line 186), log2 ≈ 0. -/
def «scratch_release» : Nat := 0

/-- `rlp_validate_items` (AST line 4548), log2 ≈ 319. -/
def «rlp_validate_items» : Nat := («scratch_mark» + 1) + («_rlp_validate_items_body» + 1) + («scratch_release» + 1) + («scratch_release» + 1)

/-- `rlp_item_total` (AST line 4567), log2 ≈ 319. -/
def «rlp_item_total» : Nat := («rlp_item_header» + 1) + Nat.max ((«rlp_validate_items» + 1)) (0)

/-- `rlp_list_count` (AST line 4582), log2 ≈ 447. -/
def «rlp_list_count» : Nat := ((domainBytes + 1) + 1) * ((«rlp_item_total» + 1) + 1)

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
def «_decode_witness_node_body» : Nat := (22621787712 + 1) * (Nat.max ((«_decode_step» + 1)) (Nat.max ((«_resolve_step» + 1)) (Nat.max (0) (Nat.max (Nat.max ((«mpt_fail» + 1)) (0) + Nat.max ((«mpt_fail» + 1)) (0) + («node_new_ext» + 1)) (Nat.max (0) ((«rlp_item» + 1) + Nat.max ((«mpt_fail» + 1)) (0)))))) + 1)

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
def «_mpt_delete_node_body» : Nat := (2 ^ 66 + 1) * (Nat.max (0) (Nat.max ((«mpt_fail» + 1)) (0) + («node_invalidate» + 1) + Nat.max (Nat.max ((«memeq» + 1)) (0)) (Nat.max ((«common_prefix_length» + 1) + Nat.max (0) ((«scratch_alloc» + 1))) (Nat.max (Nat.max (0) ((«_collapse_branch» + 1))) ((«scratch_alloc» + 1))))) + 1) + (2 ^ 64 + 1) * (Nat.max ((«_delete_ext_finish» + 1)) ((«_collapse_branch» + 1)) + 1)

/-- `_mpt_delete_node` (AST line 10852), log2 ≈ 197. -/
def «_mpt_delete_node» : Nat := («scratch_mark» + 1) + («_mpt_delete_node_body» + 1) + («scratch_release» + 1) + («scratch_release» + 1)

/-- `_split_extension` (AST line 10561), log2 ≈ 65. -/
def «_split_extension» : Nat := («node_new_branch» + 1) + Nat.max ((«node_new_ext» + 1)) (0) + Nat.max (0) (Nat.max ((«mpt_fail» + 1)) (0) + («node_new_leaf» + 1))

/-- `_mpt_insert_node` (AST line 10598), log2 ≈ 197. -/
def «_mpt_insert_node» : Nat := (2 ^ 66 + 1) * (Nat.max ((«node_new_leaf» + 1)) (Nat.max ((«mpt_fail» + 1)) (0) + («node_invalidate» + 1) + Nat.max ((«_insert_into_leaf» + 1)) (Nat.max ((«common_prefix_length» + 1) + Nat.max (0) ((«_split_extension» + 1) + Nat.max ((«node_new_ext» + 1)) (0))) (0))) + 1)

/-- `_node_needs_rlp` (AST line 10989), log2 ≈ 0. -/
def «_node_needs_rlp» : Nat := 0

/-- `nibble_list_to_compact` (AST line 9877), log2 ≈ 35. -/
def «nibble_list_to_compact» : Nat := ((domainBytes + 1) + 1) * (0 + 1)

/-- `rlp_be_len` (AST line 4698), log2 ≈ 129. -/
def «rlp_be_len» : Nat := (8 + 1) * (0 + 1)

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
def «_node_rlp_fill» : Nat := («scratch_mark» + 1) + («scratch_alloc» + 1) + («_node_rlp_begin» + 1) + (2 ^ 62 + 1) * (Nat.max (Nat.max ((«_node_needs_rlp» + 1)) (0)) (Nat.max ((16 + 1) * ((«_node_needs_rlp» + 1) + 1)) (0)) + Nat.max ((«scratch_alloc» + 1) + («_node_rlp_begin» + 1)) ((«_node_rlp_finish» + 1)) + 1) + («scratch_release» + 1)

/-- `htab_has` (AST line 5022), log2 ≈ 67. -/
def «htab_has» : Nat := («htab_find_leaf» + 1) + («memeq» + 1)

/-- `is_warm_address` (AST line 15473), log2 ≈ 67. -/
def «is_warm_address» : Nat := («htab_has» + 1)

/-- `access_gas_cost` (AST line 15496), log2 ≈ 67. -/
def «access_gas_cost» : Nat := («is_warm_address» + 1)

/-- `access_list_payload_len` (AST line 11977), log2 ≈ 194. -/
def «access_list_payload_len» : Nat := (2 ^ 64 + 1) * ((«rlp_list_header_len» + 1) + («rlp_list_header_len» + 1) + 1)

/-- `htab_first_diff` (AST line 4951), log2 ≈ 129. -/
def «htab_first_diff» : Nat := ((domainBytes + 1) + 1) * (Nat.max ((8 + 1) * (0 + 1)) (0) + 1)

/-- `htab_grow` (AST line 5117), log2 ≈ 66. -/
def «htab_grow» : Nat := («alloc» + 1) + («memcpy» + 1) + («alloc» + 1) + («memcpy» + 1) + («alloc» + 1) + («memcpy» + 1)

/-- `htab_new_node` (AST line 5041), log2 ≈ 66. -/
def «htab_new_node» : Nat := Nat.max ((«htab_grow» + 1)) (0)

/-- `htab_new_internal` (AST line 5097), log2 ≈ 66. -/
def «htab_new_internal» : Nat := («htab_new_node» + 1)

/-- `htab_new_leaf` (AST line 5068), log2 ≈ 67. -/
def «htab_new_leaf» : Nat := («htab_new_node» + 1) + («memcpy» + 1)

/-- `htab_set` (AST line 5149), log2 ≈ 130. -/
def «htab_set» : Nat := («htab_find_leaf» + 1) + Nat.max ((«htab_new_leaf» + 1)) (0) + («memeq» + 1) + («htab_first_diff» + 1) + (7776239486 + 1) * (0 + 1) + («htab_new_leaf» + 1) + («htab_new_internal» + 1)

/-- `record_pre_state_read` (AST line 12980), log2 ≈ 130. -/
def «record_pre_state_read» : Nat := («htab_set» + 1)

/-- `decode_account_from_leaf` (AST line 11266), log2 ≈ 450. -/
def «decode_account_from_leaf» : Nat := («rlp_decode_fully» + 1) + («mpt_fail» + 1) + Nat.max ((«mpt_fail» + 1)) (0) + («rlp_list_to_slices» + 1) + Nat.max ((«mpt_fail» + 1)) (0) + («rlp_item» + 1) + («rlp_item» + 1) + («rlp_item» + 1) + («rlp_item» + 1) + Nat.max ((«mpt_fail» + 1)) (0) + Nat.max ((«mpt_fail» + 1)) (0) + (2 ^ 64 + 1) * (0 + 1) + Nat.max ((«mpt_fail» + 1)) (0) + («memzero» + 1) + (2 ^ 64 + 1) * (0 + 1) + Nat.max (0) (Nat.max ((«mpt_fail» + 1)) (0)) + Nat.max (0) (Nat.max ((«mpt_fail» + 1)) (0))

/-- `heap_mark` (AST line 88), log2 ≈ 0. -/
def «heap_mark» : Nat := 0

/-- `heap_release` (AST line 98), log2 ≈ 0. -/
def «heap_release» : Nat := 0

/-- `trie_walk` (AST line 10376), log2 ≈ 196. -/
def «trie_walk» : Nat := (71723149827058354885847154688 + 1) * (Nat.max ((«mpt_fail» + 1)) (0) + Nat.max (Nat.max ((«memeq» + 1)) (0)) (0) + Nat.max ((«memeq» + 1)) (0) + 1)

/-- `trie_lookup` (AST line 10432), log2 ≈ 196. -/
def «trie_lookup» : Nat := («key_to_nibbles» + 1) + («trie_walk» + 1)

end K
end InitECandidate.Solver.Wave8Leaves.S00Spec
