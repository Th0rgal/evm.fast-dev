import InitECandidate.Solver.PanTerminatingBounded

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.PanTerminatingCallOn` — precondition-guarded `call` / `decCall`

Step 0 contract item 7: call rules whose callee body is only bounded under a precondition
(`TerminatingProgBoundedOn Pc body B`). The precondition is discharged at the call site by
`CallEntryOn`, which quantifies over exactly the callee entry states the semantics can build
from a `P` caller state.
-/

namespace InitECandidate.Solver.PanTerminatingCallOn

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingBounded

/-- Call-site discharge of the callee precondition `Pc`: every callee entry state reachable from a
`P` caller state (arguments evaluated, `fname` looked up) satisfies `Pc`. -/
def CallEntryOn (P Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (fname : MlS)
    (arguments : List (ExpHOL 64)) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL),
    state.code = originalRuntimeCode → P state →
    evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values →
    lookupCodeHOLFinite state.code.lookup fname values = some (body, callee, returnShape) →
    Pc (callEntryStateHOLFinite state callee)

/-- Shared prefix of `call` / `decCall`: if arguments or lookup fail the run errors in place, if
the clock is zero it times out, otherwise the callee body runs from the entry state. -/
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

/-- Contract item 7 (`call`): a returning call to `fname`, whose body is bounded by `B` on `Pc`,
from any `P` state whose callee entry states satisfy `Pc`, is bounded by `B + 1`. -/
theorem TerminatingProgBoundedOn.call {P Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64} {ret : ShapeHOL} {B : Nat}
    (hlook : originalRuntimeCode.lookup fname = some (params, body, ret))
    (hbody : TerminatingProgBoundedOn Pc body B)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (hentry : CallEntryOn P Pc fname arguments) :
    TerminatingProgBoundedOn P (.call (some (destination, none)) fname arguments) (B + 1) := by
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

/-- Contract item 7 (`decCall`): `.decCall name shape fname args cont` with the callee bounded
by `B` on `Pc` (discharged by `CallEntryOn`) and the continuation bounded by `Bc` on `Pk`
(discharged on every resumed state built from a `P` caller) is bounded by `B + Bc + 1`. -/
theorem TerminatingProgBoundedOn.decCall
    {P Pc Pk : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64} {ret : ShapeHOL}
    {B Bc : Nat}
    (hlook : originalRuntimeCode.lookup fname = some (params, body, ret))
    (hbody : TerminatingProgBoundedOn Pc body B)
    (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64))
    {continuation : ProgHOL 64} (hcont : TerminatingProgBoundedOn Pk continuation Bc)
    (hentry : CallEntryOn P Pc fname arguments)
    (hresume : ∀ {F : Type} (state post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64),
      state.code = originalRuntimeCode → P state → post.code = originalRuntimeCode →
      Pk (setVarHOLFinite name value { post with locals := state.locals })) :
    TerminatingProgBoundedOn P (.decCall name shape fname arguments continuation)
      (B + Bc + 1) := by
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
      obtain ⟨_, hrunBound⟩ := callee_body_bound hlook hbody hentry state hcode hP values body'
        callee ret' hargs hl
      by_cases hz : state.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee)
          body').1
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
              set resumed := setVarHOLFinite name value { post with locals := state.locals } with hres
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              have hcb := hcont resumed hresCode
                (hresume state post value hcode hP (hmeta.trans hcode)) hnt
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

end InitECandidate.Solver.PanTerminatingCallOn
