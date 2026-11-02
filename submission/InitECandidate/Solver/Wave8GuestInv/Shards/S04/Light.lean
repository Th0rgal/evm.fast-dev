import InitECandidate.Solver.PanTerminatingBounded

-- Verbatim rev7 definitions/combinators, renamed to avoid full-spec import.
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S04.Light

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

def domainBytes : Nat := heapEnd - sourceBase

theorem domainBytes_eq : domainBytes = 31104957928 := by decide

structure GuestInvData {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop where
  code : s.code = originalRuntimeCode
  memaddrs : s.memaddrs = ordinaryDomain
  shMemaddrs : s.shMemaddrs = sharedDomain
  baseAddr : s.baseAddr = BitVec.ofNat 64 sourceBase

def GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInvData s

/-- `name` is a global bound to the word `w`. -/
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

namespace K
def «trap_with» : Nat := 0
def «alloc» : Nat := Nat.max ((«trap_with» + 1)) (0) + Nat.max ((«trap_with» + 1)) (0)
def «mpt_fail» : Nat := 0
def «memcpy» : Nat := Nat.max (((domainBytes + 1) + 1) * (0 + 1) + ((domainBytes + 1) + 1) * (0 + 1)) (0) + ((domainBytes + 1) + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1)
def «memzero» : Nat := Nat.max (((domainBytes + 1) + 1) * (0 + 1) + ((domainBytes + 1) + 1) * (0 + 1)) (0) + ((domainBytes + 1) + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1)
def «key_to_nibbles» : Nat := ((domainBytes + 1) + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1)
def «rlp_fail» : Nat := 0
def «rlp_read_length» : Nat := Nat.max ((«rlp_fail» + 1)) (0) + ((domainBytes + 1) + 1) * (0 + 1)
def «rlp_item_header» : Nat := Nat.max ((«rlp_fail» + 1)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0)) (0)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0) + («rlp_read_length» + 1) + Nat.max ((«rlp_fail» + 1)) (0) + Nat.max ((«rlp_fail» + 1)) (0)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0)) (0) + Nat.max ((«rlp_fail» + 1)) (0) + («rlp_read_length» + 1) + Nat.max ((«rlp_fail» + 1)) (0) + Nat.max ((«rlp_fail» + 1)) (0)
def «scratch_alloc» : Nat := Nat.max ((«trap_with» + 1)) (0) + Nat.max ((«trap_with» + 1)) (0)
def «_rlp_validate_items_body» : Nat := (62209915858 + 1) * (Nat.max (0) ((«rlp_item_header» + 1) + Nat.max ((«scratch_alloc» + 1)) (0)) + 1)
def «scratch_mark» : Nat := 0
def «scratch_release» : Nat := 0
def «rlp_validate_items» : Nat := («scratch_mark» + 1) + («_rlp_validate_items_body» + 1) + («scratch_release» + 1) + («scratch_release» + 1)
def «rlp_item_total» : Nat := («rlp_item_header» + 1) + Nat.max ((«rlp_validate_items» + 1)) (0)
def «rlp_list_count» : Nat := ((domainBytes + 1) + 1) * ((«rlp_item_total» + 1) + 1)
def «rlp_item» : Nat := Nat.max ((«rlp_fail» + 1)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0)) (0)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0) + («rlp_read_length» + 1) + Nat.max ((«rlp_fail» + 1)) (0) + Nat.max ((«rlp_fail» + 1)) (0)) (0) + Nat.max (Nat.max ((«rlp_fail» + 1)) (0) + («rlp_list_count» + 1)) (0) + Nat.max ((«rlp_fail» + 1)) (0) + («rlp_read_length» + 1) + Nat.max ((«rlp_fail» + 1)) (0) + Nat.max ((«rlp_fail» + 1)) (0) + («rlp_list_count» + 1)
def «rlp_decode_fully» : Nat := («rlp_item» + 1) + Nat.max ((«rlp_fail» + 1)) (0)
def «rlp_item_total_unchecked» : Nat := Nat.max ((«rlp_read_length» + 1)) (0) + («rlp_read_length» + 1)
def «rlp_list_to_slices» : Nat := («rlp_list_count» + 1) + («alloc» + 1) + (2 ^ 64 + 1) * ((«rlp_item_total_unchecked» + 1) + 1)
def «htab_find_leaf» : Nat := (2 ^ 64 + 1) * (0 + 1)
def «memeq» : Nat := Nat.max ((2 ^ 64 + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1)) (0) + (2 ^ 64 + 1) * (0 + 1) + (2 ^ 64 + 1) * (0 + 1)
def «htab_get» : Nat := («htab_find_leaf» + 1) + («memeq» + 1)
def «nodedb_lookup» : Nat := («htab_get» + 1)
def «rlp_be_len» : Nat := (8 + 1) * (0 + 1)
def «rlp_header_len» : Nat := («rlp_be_len» + 1)
def «keccak_f1600» : Nat := (2 ^ 64 + 1) * (0 + 1)
def «keccak_absorb_block» : Nat := (2 ^ 64 + 1) * (0 + 1) + («keccak_f1600» + 1)
def «keccak256» : Nat := («memzero» + 1) + ((domainBytes + 1) + 1) * ((«keccak_absorb_block» + 1) + 1) + («memzero» + 1) + («memcpy» + 1) + («keccak_absorb_block» + 1) + Nat.max (0) ((«memcpy» + 1))
def «rlp_put_be» : Nat := (2 ^ 64 + 1) * (0 + 1)
def «rlp_write_header» : Nat := («rlp_be_len» + 1) + («rlp_put_be» + 1)
def «rlp_encode_bytes» : Nat := («rlp_write_header» + 1) + («memcpy» + 1)
def «rlp_encode_list_header» : Nat := («rlp_write_header» + 1)
def «rlp_list_header_len» : Nat := («rlp_header_len» + 1)
def «htab_has» : Nat := («htab_find_leaf» + 1) + («memeq» + 1)
def «is_warm_address» : Nat := («htab_has» + 1)
def «htab_first_diff» : Nat := ((domainBytes + 1) + 1) * (Nat.max ((8 + 1) * (0 + 1)) (0) + 1)
def «htab_grow» : Nat := («alloc» + 1) + («memcpy» + 1) + («alloc» + 1) + («memcpy» + 1) + («alloc» + 1) + («memcpy» + 1)
def «htab_new_node» : Nat := Nat.max ((«htab_grow» + 1)) (0)
def «htab_new_internal» : Nat := («htab_new_node» + 1)
def «htab_new_leaf» : Nat := («htab_new_node» + 1) + («memcpy» + 1)
def «htab_set» : Nat := («htab_find_leaf» + 1) + Nat.max ((«htab_new_leaf» + 1)) (0) + («memeq» + 1) + («htab_first_diff» + 1) + (7776239486 + 1) * (0 + 1) + («htab_new_leaf» + 1) + («htab_new_internal» + 1)
def «record_pre_state_read» : Nat := («htab_set» + 1)
def «decode_account_from_leaf» : Nat := («rlp_decode_fully» + 1) + («mpt_fail» + 1) + Nat.max ((«mpt_fail» + 1)) (0) + («rlp_list_to_slices» + 1) + Nat.max ((«mpt_fail» + 1)) (0) + («rlp_item» + 1) + («rlp_item» + 1) + («rlp_item» + 1) + («rlp_item» + 1) + Nat.max ((«mpt_fail» + 1)) (0) + Nat.max ((«mpt_fail» + 1)) (0) + (2 ^ 64 + 1) * (0 + 1) + Nat.max ((«mpt_fail» + 1)) (0) + («memzero» + 1) + (2 ^ 64 + 1) * (0 + 1) + Nat.max (0) (Nat.max ((«mpt_fail» + 1)) (0)) + Nat.max (0) (Nat.max ((«mpt_fail» + 1)) (0))
def «heap_mark» : Nat := 0
def «heap_release» : Nat := 0
def «trie_walk» : Nat := (71723149827058354885847154688 + 1) * (Nat.max ((«mpt_fail» + 1)) (0) + Nat.max (Nat.max ((«memeq» + 1)) (0)) (0) + Nat.max ((«memeq» + 1)) (0) + 1)
def «trie_lookup» : Nat := («key_to_nibbles» + 1) + («trie_walk» + 1)
def «ws_account_leaf» : Nat := («heap_mark» + 1) + («alloc» + 1) + («keccak256» + 1) + («trie_lookup» + 1) + («heap_release» + 1)
def «ws_get_account_optional» : Nat := («ws_account_leaf» + 1) + («alloc» + 1) + («decode_account_from_leaf» + 1)
def «acct_new» : Nat := («alloc» + 1)
def «acct_empty» : Nat := («acct_new» + 1)
def «get_pre_state_account_optional» : Nat := («htab_set» + 1) + («htab_get» + 1) + («record_pre_state_read» + 1) + («ws_get_account_optional» + 1)
def «get_account_optional» : Nat := («htab_set» + 1) + («htab_get» + 1) + («get_pre_state_account_optional» + 1)
def «get_account» : Nat := («get_account_optional» + 1) + Nat.max ((«acct_empty» + 1)) (0)
def «account_exists» : Nat := («get_account_optional» + 1)
def «acct_copy» : Nat := («alloc» + 1) + («memcpy» + 1)
def «u256_is_zero» : Nat := 0
def «acct_is_empty» : Nat := («memeq» + 1) + («u256_is_zero» + 1)
def «htab_new» : Nat := («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1)
def «lst_push» : Nat := Nat.max ((«alloc» + 1) + («memcpy» + 1)) (0)
def «add_sat» : Nat := 0
def «st_be32» : Nat := 0
def «bswap64» : Nat := 0
def «st_be64» : Nat := Nat.max ((«bswap64» + 1)) (0) + («st_be32» + 1) + («st_be32» + 1)
def «u256_from_be» : Nat := Nat.max ((«bswap64» + 1) + («bswap64» + 1) + («bswap64» + 1) + («bswap64» + 1)) (0) + (2 ^ 64 + 1) * (0 + 1)
def «udivmod» : Nat := Nat.max ((«trap_with» + 1)) (0) + (64 + 1) * (0 + 1)
def «rlp_encode_word» : Nat := («rlp_be_len» + 1) + («rlp_put_be» + 1)
def «bit_length64» : Nat := 0
def «u256_bit_length» : Nat := Nat.max ((«bit_length64» + 1)) (0) + Nat.max ((«bit_length64» + 1)) (0) + Nat.max ((«bit_length64» + 1)) (0) + («bit_length64» + 1)
def «u256_byte_length» : Nat := («u256_bit_length» + 1)
def «u256_limb» : Nat := 0
def «u256_to_be_min» : Nat := («u256_byte_length» + 1) + (2 ^ 64 + 1) * ((«u256_limb» + 1) + 1)
def «rlp_put_u256» : Nat := («heap_mark» + 1) + («alloc» + 1) + («u256_to_be_min» + 1) + («rlp_encode_bytes» + 1) + («heap_release» + 1)
def «htab_item» : Nat := 0
def «max» : Nat := 0
def «is_zero_bytes» : Nat := (2 ^ 64 + 1) * (0 + 1)
def «sk_make» : Nat := («memcpy» + 1) + («memcpy» + 1)
def «ws_get_code» : Nat := («memeq» + 1) + («nodedb_lookup» + 1)
def «get_code» : Nat := («memeq» + 1) + («htab_get» + 1) + («htab_get» + 1) + («sk_make» + 1) + («htab_set» + 1) + («ws_get_code» + 1)
def «ext_code_of» : Nat := («get_account» + 1) + («get_code» + 1)
def «htab_del» : Nat := («htab_find_leaf» + 1) + («memeq» + 1)
def «u256_eq» : Nat := 0
def «frame_state_gas_used» : Nat := 0
def «charge_gas» : Nat := 0
def «charge_state_gas» : Nat := («add_sat» + 1)
def «jset» : Nat := («htab_get» + 1) + Nat.max ((«trap_with» + 1)) (0) + («alloc» + 1) + («memcpy» + 1) + («htab_set» + 1)
def «jdel» : Nat := («htab_get» + 1) + Nat.max ((«trap_with» + 1)) (0) + («alloc» + 1) + («memcpy» + 1) + («htab_del» + 1)
def «destroy_storage» : Nat := («htab_get» + 1) + (2 ^ 63 + 1) * ((«htab_item» + 1) + Nat.max ((«sk_make» + 1) + («htab_set» + 1)) (0) + 1) + («jdel» + 1)
def «set_account» : Nat := («jset» + 1)
def «destroy_account» : Nat := («destroy_storage» + 1) + («set_account» + 1)
def «modify_state_commit» : Nat := («set_account» + 1) + («acct_is_empty» + 1) + Nat.max ((«destroy_account» + 1)) (0)
def «set_code» : Nat := («alloc» + 1) + («keccak256» + 1) + («memeq» + 1) + Nat.max ((«alloc» + 1) + («jset» + 1)) (0) + («get_account» + 1) + («acct_copy» + 1) + («modify_state_commit» + 1)
def «frame_halt» : Nat := 0
def «increment_nonce» : Nat := («get_account» + 1) + («acct_copy» + 1) + («modify_state_commit» + 1)
def «mark_account_created» : Nat := («htab_set» + 1)
def «compute_jumpdests» : Nat := («scratch_alloc» + 1) + («memzero» + 1) + (31104957928 + 1) * (0 + 1)
def «is_valid_delegation» : Nat := 0
def «get_delegated_code_address» : Nat := («is_valid_delegation» + 1)
def «get_pre_state_account» : Nat := («get_pre_state_account_optional» + 1) + Nat.max ((«acct_empty» + 1)) (0)
def «is_account_alive» : Nat := («get_account_optional» + 1) + («acct_is_empty» + 1)
def «warm_address» : Nat := («htab_set» + 1)
def «prepare_dispatch» : Nat := Nat.max ((«get_pre_state_account» + 1) + («acct_is_empty» + 1) + Nat.max ((«charge_state_gas» + 1)) (0)) (0) + («u256_is_zero» + 1) + Nat.max ((«is_account_alive» + 1) + Nat.max ((«charge_state_gas» + 1)) (0)) (0) + («ext_code_of» + 1) + («get_delegated_code_address» + 1) + Nat.max ((«alloc» + 1) + («memcpy» + 1) + («is_warm_address» + 1) + Nat.max ((«charge_gas» + 1)) ((«charge_gas» + 1) + («warm_address» + 1)) + («ext_code_of» + 1)) (0) + («compute_jumpdests» + 1)
def «ec_set_infinity» : Nat := 0
def «u256_add_carry» : Nat := 0
def «u256_lt» : Nat := 0
def «u256_sub» : Nat := 0
def «fp_add» : Nat := («u256_add_carry» + 1) + Nat.max ((«u256_sub» + 1)) (0) + («u256_lt» + 1) + Nat.max ((«u256_sub» + 1)) (0)
def «fp_reduce» : Nat := («u256_lt» + 1) + Nat.max ((«u256_sub» + 1)) (0)
def «u256_add» : Nat := 0
def «fp_mul» : Nat := Nat.max ((«u256_add» + 1)) (0) + («fp_reduce» + 1)
def «fp_sqr» : Nat := Nat.max ((«u256_add» + 1)) (0) + («fp_reduce» + 1)
def «fp_sub» : Nat := («u256_lt» + 1) + («u256_sub» + 1) + Nat.max ((«u256_add» + 1)) (0)
def «ec_double» : Nat := («u256_is_zero» + 1) + («u256_is_zero» + 1) + Nat.max ((«ec_set_infinity» + 1)) (0) + («fp_sqr» + 1) + («fp_mul» + 1) + («fp_add» + 1) + («fp_add» + 1) + («fp_sqr» + 1) + («fp_add» + 1) + («fp_add» + 1) + («fp_sqr» + 1) + («fp_add» + 1) + («fp_sub» + 1) + («fp_sub» + 1) + («fp_mul» + 1) + («fp_sqr» + 1) + («fp_add» + 1) + («fp_add» + 1) + («fp_add» + 1) + («fp_sub» + 1) + («fp_mul» + 1) + («fp_add» + 1)
def «ec_set_affine» : Nat := 0
def «ec_add_affine» : Nat := («u256_is_zero» + 1) + Nat.max ((«ec_set_affine» + 1)) (0) + («fp_sqr» + 1) + («fp_mul» + 1) + («fp_mul» + 1) + («fp_mul» + 1) + («u256_eq» + 1) + Nat.max ((«fp_add» + 1) + («u256_is_zero» + 1) + Nat.max ((«ec_set_infinity» + 1)) (0) + («ec_double» + 1)) (0) + («fp_sub» + 1) + («fp_sub» + 1) + («fp_sqr» + 1) + («fp_mul» + 1) + («fp_mul» + 1) + («fp_sqr» + 1) + («fp_sub» + 1) + («fp_add» + 1) + («fp_sub» + 1) + («fp_sub» + 1) + («fp_mul» + 1) + («fp_mul» + 1) + («fp_sub» + 1) + («fp_mul» + 1)
def «ec_is_infinity» : Nat := («u256_is_zero» + 1)
def «mod_half» : Nat := («u256_add_carry» + 1)
def «mod_sub» : Nat := («u256_lt» + 1) + («u256_sub» + 1) + Nat.max ((«u256_add» + 1)) (0)
def «modinv_bin» : Nat := («u256_is_zero» + 1) + (513 + 1) * ((2 ^ 8 + 1) * ((«mod_half» + 1) + 1) + (2 ^ 8 + 1) * ((«mod_half» + 1) + 1) + («u256_lt» + 1) + («u256_sub» + 1) + («mod_sub» + 1) + 1)
def «fp_inv» : Nat := («modinv_bin» + 1)
def «ec_to_affine» : Nat := («u256_is_zero» + 1) + («fp_inv» + 1) + («fp_sqr» + 1) + («fp_mul» + 1) + («fp_mul» + 1) + («fp_mul» + 1) + («ec_set_affine» + 1)
def «u256_bit» : Nat := («u256_limb» + 1)
def «ec_mul2» : Nat := («ec_set_infinity» + 1) + («u256_bit_length» + 1) + («u256_bit_length» + 1) + («max» + 1) + («heap_mark» + 1) + («alloc» + 1) + («ec_set_affine» + 1) + («ec_add_affine» + 1) + («ec_is_infinity» + 1) + Nat.max ((«ec_to_affine» + 1)) (0) + (2 ^ 64 + 1) * ((«ec_double» + 1) + («u256_bit» + 1) + («u256_bit» + 1) + Nat.max (Nat.max (Nat.max ((«ec_add_affine» + 1)) (0)) ((«ec_add_affine» + 1))) (Nat.max ((«ec_add_affine» + 1)) (0)) + 1) + («heap_release» + 1)
def «fn_inv» : Nat := («modinv_bin» + 1)
def «digits_len» : Nat := (2 ^ 64 + 1) * (0 + 1)
def «digits_to_u256» : Nat := 0
def «div64by32» : Nat := (32 + 1) * (0 + 1)
def «nlz32» : Nat := 0
def «divmnu» : Nat := Nat.max ((31104957944 + 1) * ((«div64by32» + 1) + 1)) (0) + («nlz32» + 1) + (31104957944 + 1) * (0 + 1) + (31104957944 + 1) * (0 + 1) + (31104957944 + 1) * (Nat.max (0) ((«div64by32» + 1)) + (3 + 1) * (0 + 1) + (31104957944 + 1) * (0 + 1) + Nat.max ((31104957944 + 1) * (0 + 1)) (0) + 1) + (31104957944 + 1) * (0 + 1) + (31104957944 + 1) * (0 + 1)
def «u256_to_digits» : Nat := 0
def «digits_divmod» : Nat := («u256_to_digits» + 1) + («digits_len» + 1) + («digits_len» + 1) + (16 + 1) * (0 + 1) + Nat.max ((«digits_to_u256» + 1)) (0) + (8 + 1) * (0 + 1) + («divmnu» + 1) + («digits_to_u256» + 1)
def «mul64x64» : Nat := 0
def «u256_divmod» : Nat := («u256_lt» + 1) + Nat.max ((«udivmod» + 1)) (0) + («u256_to_digits» + 1) + («digits_divmod» + 1) + («digits_to_u256» + 1)
def «u256_mod» : Nat := («u256_divmod» + 1)
def «u256_mul_full» : Nat := («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1) + («mul64x64» + 1)
def «u256_mulmod» : Nat := Nat.max ((«mul64x64» + 1) + Nat.max ((«u256_mod» + 1)) (0) + («u256_to_digits» + 1) + («digits_divmod» + 1)) (0) + («u256_mul_full» + 1) + («u256_to_digits» + 1) + («u256_to_digits» + 1) + («digits_divmod» + 1)
def «fn_mul» : Nat := («u256_mulmod» + 1)
def «fp_neg» : Nat := («u256_is_zero» + 1) + («u256_sub» + 1)
def «fp_pow» : Nat := (2 ^ 8 + 1) * (Nat.max ((«fp_sqr» + 1)) (0) + («u256_bit» + 1) + Nat.max ((«fp_mul» + 1)) (0) + 1)
def «fp_sqrt» : Nat := («fp_pow» + 1)
def «secp256k1_decompress_r» : Nat := Nat.max ((«u256_add_carry» + 1)) (0) + («u256_lt» + 1) + («fp_sqr» + 1) + («fp_mul» + 1) + («fp_add» + 1) + («fp_sqrt» + 1) + («fp_sqr» + 1) + («u256_eq» + 1) + Nat.max ((«fp_neg» + 1)) (0) + («ec_set_affine» + 1)
def «u256_to_be32» : Nat := Nat.max ((«bswap64» + 1) + («bswap64» + 1) + («bswap64» + 1) + («bswap64» + 1)) (0) + («st_be64» + 1) + («st_be64» + 1) + («st_be64» + 1) + («st_be64» + 1)
def «secp256k1_recover» : Nat := («u256_is_zero» + 1) + («u256_lt» + 1) + («u256_is_zero» + 1) + («u256_lt» + 1) + («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («secp256k1_decompress_r» + 1) + Nat.max ((«heap_release» + 1)) (0) + («u256_from_be» + 1) + («u256_lt» + 1) + Nat.max ((«u256_sub» + 1)) (0) + («fn_inv» + 1) + («u256_is_zero» + 1) + Nat.max ((«u256_sub» + 1)) (0) + («fn_mul» + 1) + («fn_mul» + 1) + («ec_mul2» + 1) + («ec_to_affine» + 1) + Nat.max ((«u256_to_be32» + 1) + («u256_to_be32» + 1)) (0) + («heap_release» + 1)
def «u256_gt» : Nat := («u256_lt» + 1)
def «recover_authority» : Nat := («u256_is_zero» + 1) + («u256_lt» + 1) + («u256_is_zero» + 1) + («u256_gt» + 1) + («heap_mark» + 1) + («alloc» + 1) + («rlp_put_u256» + 1) + («rlp_encode_bytes» + 1) + («rlp_encode_word» + 1) + («rlp_list_header_len» + 1) + («rlp_encode_list_header» + 1) + («alloc» + 1) + («keccak256» + 1) + («alloc» + 1) + («secp256k1_recover» + 1) + Nat.max ((«heap_release» + 1)) (0) + («keccak256» + 1) + («heap_release» + 1) + («alloc» + 1) + («memcpy» + 1)
def «u256_fits_word» : Nat := 0
def «validate_authorization_checks» : Nat := («get_account» + 1) + («get_code» + 1) + Nat.max ((«is_valid_delegation» + 1)) (0)
def «set_delegation» : Nat := («htab_new» + 1) + («htab_set» + 1) + («u256_is_zero» + 1) + Nat.max ((«htab_set» + 1)) (0) + («htab_new» + 1) + (2 ^ 64 + 1) * ((«u256_is_zero» + 1) + («u256_fits_word» + 1) + Nat.max (Nat.max ((«recover_authority» + 1) + Nat.max ((«warm_address» + 1) + («validate_authorization_checks» + 1)) (0)) (0)) (0) + Nat.max ((«account_exists» + 1) + Nat.max ((«charge_state_gas» + 1)) (0) + («htab_has» + 1) + Nat.max ((«charge_gas» + 1) + («htab_set» + 1)) (0) + («get_pre_state_account» + 1) + («get_code» + 1) + («is_valid_delegation» + 1) + («memeq» + 1) + Nat.max ((«set_code» + 1)) ((«htab_has» + 1) + Nat.max ((«charge_state_gas» + 1)) (0) + («htab_set» + 1) + («alloc» + 1) + («memcpy» + 1) + («set_code» + 1)) + («increment_nonce» + 1)) (0) + 1)
def «depth0_prepare» : Nat := Nat.max ((«set_delegation» + 1) + («frame_state_gas_used» + 1)) (0) + («prepare_dispatch» + 1)
def «frame_mem_alloc» : Nat := Nat.max ((«trap_with» + 1)) (0) + Nat.max ((«trap_with» + 1)) (0)
def «frame_mem_mark» : Nat := 0
def «htab_count» : Nat := 0
def «htab_new_scratch» : Nat := («scratch_alloc» + 1) + («scratch_alloc» + 1) + («scratch_alloc» + 1) + («scratch_alloc» + 1)
def «lst_new_scratch» : Nat := («scratch_alloc» + 1) + («scratch_alloc» + 1)
def «frame_new» : Nat := («scratch_mark» + 1) + («frame_mem_mark» + 1) + («scratch_alloc» + 1) + («memzero» + 1) + («scratch_alloc» + 1) + («frame_mem_alloc» + 1) + («compute_jumpdests» + 1) + («lst_new_scratch» + 1) + («htab_new_scratch» + 1) + («htab_count» + 1) + («htab_count» + 1)
def «frame_open» : Nat := («frame_new» + 1) + («scratch_alloc» + 1) + («memzero» + 1)
def «refill_frame_state_gas» : Nat := 0
def «frame_exception» : Nat := («refill_frame_state_gas» + 1) + Nat.max ((«frame_halt» + 1)) (0)
def «log_append» : Nat := («lst_push» + 1)
def «emit_transfer_log» : Nat := («u256_is_zero» + 1) + («alloc» + 1) + («alloc» + 1) + («memcpy» + 1) + («memzero» + 1) + («memcpy» + 1) + («memzero» + 1) + («memcpy» + 1) + («alloc» + 1) + («u256_to_be32» + 1) + («log_append» + 1)
def «move_ether» : Nat := («get_account» + 1) + («u256_lt» + 1) + («acct_copy» + 1) + («u256_sub» + 1) + («modify_state_commit» + 1) + («get_account» + 1) + («acct_copy» + 1) + («u256_add» + 1) + («modify_state_commit» + 1)
def «precompile_index» : Nat := («is_zero_bytes» + 1)
def «fq_mul» : Nat := («u256_lt» + 1) + Nat.max ((«u256_sub» + 1)) (0)
def «fq_from_mont» : Nat := («fq_mul» + 1)
def «fq_inv» : Nat := («modinv_bin» + 1) + («fq_mul» + 1)
def «bn254_g1_to_bytes» : Nat := («u256_is_zero» + 1) + Nat.max ((«memzero» + 1)) (0) + («fq_inv» + 1) + («fq_mul» + 1) + («fq_mul» + 1) + («fq_from_mont» + 1) + («fq_from_mont» + 1) + («u256_to_be32» + 1) + («u256_to_be32» + 1)
def «fe_set_one» : Nat := («memzero» + 1)
def «fe_set_zero» : Nat := («memzero» + 1)
def «ecp_set_inf» : Nat := («fe_set_one» + 1) + («fe_set_one» + 1) + («fe_set_zero» + 1)
def «fq_add» : Nat := («u256_add» + 1) + («u256_lt» + 1) + Nat.max ((«u256_sub» + 1)) (0)
def «fq_to_mont» : Nat := («fq_mul» + 1)
def «bn254_parse_g1» : Nat := («u256_from_be» + 1) + («u256_from_be» + 1) + («u256_lt» + 1) + («u256_lt» + 1) + («u256_is_zero» + 1) + («u256_is_zero» + 1) + Nat.max ((«ecp_set_inf» + 1)) (0) + («fq_to_mont» + 1) + («fq_to_mont» + 1) + («fq_mul» + 1) + («fq_mul» + 1) + («fq_mul» + 1) + («fq_add» + 1) + («u256_eq» + 1)
def «fq_mul_small» : Nat := («bit_length64» + 1) + (64 + 1) * ((«fq_add» + 1) + Nat.max ((«fq_add» + 1)) (0) + 1)
def «fq_sub» : Nat := («u256_lt» + 1) + («u256_sub» + 1) + Nat.max ((«u256_add» + 1)) (0)
def «fq12_reduce» : Nat := (11 + 1) * ((«fq_mul_small» + 1) + («fq_mul_small» + 1) + («fq_sub» + 1) + («fq_add» + 1) + 1)
def «fq12_mul» : Nat := («heap_mark» + 1) + («alloc» + 1) + (23 + 1) * ((12 + 1) * ((«fq_mul» + 1) + («fq_add» + 1) + 1) + 1) + («fq12_reduce» + 1) + («memcpy» + 1) + («heap_release» + 1)
def «fq2_mul» : Nat := («fq_mul» + 1) + («fq_mul» + 1) + («fq_mul» + 1) + («fq_mul» + 1) + («fq_sub» + 1) + («fq_add» + 1)
def «fe_mul» : Nat := Nat.max ((«fq_mul» + 1)) (0) + Nat.max ((«fq2_mul» + 1)) (0) + («fq12_mul» + 1)
def «fe_mul_small» : Nat := (31104957944 + 1) * ((«fq_mul_small» + 1) + 1)
def «fq12_sqr» : Nat := («heap_mark» + 1) + («alloc» + 1) + (23 + 1) * ((22 + 1) * ((«fq_mul» + 1) + («fq_add» + 1) + 1) + («fq_add» + 1) + Nat.max ((«fq_mul» + 1) + («fq_add» + 1)) (0) + 1) + («fq12_reduce» + 1) + («memcpy» + 1) + («heap_release» + 1)
def «fe_sqr» : Nat := Nat.max ((«fq12_sqr» + 1)) (0) + («fe_mul» + 1)
def «fe_sub» : Nat := (31104957944 + 1) * ((«fq_sub» + 1) + 1)
def «ecp_double» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («fe_sqr» + 1) + («fe_mul_small» + 1) + («fe_mul» + 1) + («fe_mul» + 1) + («fe_mul» + 1) + («fe_sqr» + 1) + («fe_mul_small» + 1) + («fe_sub» + 1) + («fe_sqr» + 1) + («fe_mul» + 1) + («fe_mul_small» + 1) + («fe_mul_small» + 1) + («fe_sub» + 1) + («fe_mul» + 1) + («fe_sqr» + 1) + («fe_mul» + 1) + («fe_mul_small» + 1) + («fe_sub» + 1) + («fe_mul» + 1) + («fe_mul_small» + 1) + («memcpy» + 1) + («memcpy» + 1) + («memcpy» + 1) + («heap_release» + 1)
def «fe_eq» : Nat := («memeq» + 1)
def «fe_is_zero» : Nat := («is_zero_bytes» + 1)
def «ecp_add» : Nat := («fe_is_zero» + 1) + Nat.max ((«memcpy» + 1)) (0) + («fe_is_zero» + 1) + Nat.max ((«memcpy» + 1)) (0) + («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («fe_mul» + 1) + («fe_mul» + 1) + («fe_mul» + 1) + («fe_mul» + 1) + («fe_eq» + 1) + Nat.max ((«fe_eq» + 1) + («heap_release» + 1) + Nat.max ((«ecp_double» + 1)) (0) + («ecp_set_inf» + 1)) (0) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («alloc» + 1) + («fe_sub» + 1) + («fe_sub» + 1) + («fe_sqr» + 1) + («fe_mul» + 1) + («fe_mul» + 1) + («fe_mul» + 1) + («fe_sqr» + 1) + («fe_mul» + 1) + («fe_sub» + 1) + («fe_mul_small» + 1) + («fe_sub» + 1) + («fe_mul» + 1) + («fe_sub» + 1) + («fe_mul» + 1) + («fe_mul» + 1) + («fe_sub» + 1) + («fe_mul» + 1) + («memcpy» + 1) + («memcpy» + 1) + («memcpy» + 1) + («heap_release» + 1)
def «bn254_g1_add» : Nat := («heap_mark» + 1) + («alloc» + 1) + («alloc» + 1) + («bn254_parse_g1» + 1) + Nat.max ((«heap_release» + 1)) (0) + («bn254_parse_g1» + 1) + Nat.max ((«heap_release» + 1)) (0) + («ecp_add» + 1) + («bn254_g1_to_bytes» + 1) + («heap_release» + 1)
def «buffer_read» : Nat := Nat.max ((«memcpy» + 1)) (0) + («memzero» + 1)
def «pre_alt_bn128_add» : Nat := («charge_gas» + 1) + («alloc» + 1) + («heap_mark» + 1) + («alloc» + 1) + («buffer_read» + 1) + («bn254_g1_add» + 1) + («heap_release» + 1)
end K
end InitECandidate.Solver.Wave8Leaves.S04.Light
