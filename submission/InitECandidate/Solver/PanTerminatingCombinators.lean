import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.PanTerminatingCallOn
import InitECandidate.Solver.PanTerminatingNoRepeat

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.PanTerminatingCombinators

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanRunBounded InitECandidate.Solver.PanTerminatingBounded

theorem evalP_code {F : Type} (state : PanSemStateFiniteExact 64 F) (program : ProgHOL 64) :
    (evaluateHOLFiniteState state program).2.code = state.code :=
  (PanRunBounded.evaluateHOLFiniteState_metadata state program).1

theorem TerminatingProgBounded.tick : TerminatingProgBounded (.tick : ProgHOL 64) 1 := by
  intro F state _
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_tick] at hnt ⊢
  by_cases hzero : state.clock = 0
  · simp [hzero] at hnt
  · simp [hzero, decClockHOLFinite]; omega

private theorem terminating_body_of_fun {fname : MlS} {B : Nat}
    (hfun : TerminatingFunBounded fname B)
    {F : Type} {state : PanSemStateFiniteExact 64 F} (hcode : state.code = originalRuntimeCode)
    {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {locals : HolFiniteMapExact MlS (ValueHOL 64)} {returnShape : ShapeHOL}
    (hlookup : lookupCodeHOLFinite state.code.lookup fname values = some (body, locals, returnShape)) :
    TerminatingRunBounded (callEntryStateHOLFinite state locals) body B := by
  obtain ⟨params, installed, ret, hlook, hbody⟩ := hfun
  have same := lookupCodeHOLFinite_installed_body state.code.lookup fname params installed body
    ret returnShape values locals (by rw [hcode]; exact hlook) hlookup
  subst same
  exact hbody (callEntryStateHOLFinite state locals) hcode

private theorem tail_clock_of_body {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (result : Option (PanSemResultExact 64))
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body, callee, returnShape))
    (clock : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result, post))
    (noTimeout : result ≠ some .timeOut) :
    let output := evaluateHOLFiniteState state (.call none function arguments)
    output.1 ≠ some .timeOut ∧ output.2.clock = post.clock := by
  dsimp only
  rw [evaluateHOLFiniteState_call, args]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg clock, run]
  cases result with
  | none => simp
  | some result =>
    cases result <;> simp_all [emptyLocalsHOLFinite]
    split <;> simp

theorem TerminatingProgBounded.call {fname : MlS} {B : Nat} (hfun : TerminatingFunBounded fname B)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) :
    TerminatingProgBounded (.call (some (destination, none)) fname arguments) (B + 1) := by
  intro F state hcode
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  cases hargs : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
  | none => exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  | some values =>
    rw [hargs] at hnt
    dsimp only at hnt ⊢
    cases hlookup : lookupCodeHOLFinite state.code.lookup fname values with
    | none => exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    | some found =>
      obtain ⟨body, callee, returnShape⟩ := found
      rw [hlookup] at hnt
      dsimp only at hnt ⊢
      by_cases hzero : state.clock = 0
      · rw [if_pos hzero] at hnt; exact absurd rfl hnt
      · rw [if_neg hzero] at hnt ⊢
        have hentry := terminating_body_of_fun hfun hcode hlookup
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨result, post⟩
        rw [hrun] at hnt
        have hntBody : result ≠ some .timeOut := fun hbad => by subst hbad; simp at hnt
        have hbound := hentry (by rw [hrun]; exact hntBody)
        rw [hrun] at hbound
        obtain ⟨hspent, hkept⟩ := hbound
        have hpair := evaluate_call_body_clock_no_timeout state post fname destination arguments values body callee
          returnShape result hargs hlookup hzero hrun hntBody
        dsimp only at hpair
        rw [evaluateHOLFiniteState_call, hargs] at hpair
        dsimp only at hpair
        rw [hlookup] at hpair
        dsimp only at hpair
        rw [if_neg hzero, hrun] at hpair
        rw [hpair.2]
        change state.clock - 1 ≤ post.clock + B at hspent
        change post.clock ≤ state.clock - 1 at hkept
        exact ⟨by omega, by omega⟩

theorem TerminatingProgBounded.tailCall {fname : MlS} {B : Nat}
    (hfun : TerminatingFunBounded fname B) (arguments : List (ExpHOL 64)) :
    TerminatingProgBounded (.call none fname arguments) (B + 1) := by
  intro F state hcode
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  cases hargs : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
  | none => exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  | some values =>
    rw [hargs] at hnt
    dsimp only at hnt ⊢
    cases hlookup : lookupCodeHOLFinite state.code.lookup fname values with
    | none => exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    | some found =>
      obtain ⟨body, callee, returnShape⟩ := found
      rw [hlookup] at hnt
      dsimp only at hnt ⊢
      by_cases hzero : state.clock = 0
      · rw [if_pos hzero] at hnt; exact absurd rfl hnt
      · rw [if_neg hzero] at hnt ⊢
        have hentry := terminating_body_of_fun hfun hcode hlookup
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨result, post⟩
        rw [hrun] at hnt
        have hntBody : result ≠ some .timeOut := fun hbad => by subst hbad; simp at hnt
        have hbound := hentry (by rw [hrun]; exact hntBody)
        rw [hrun] at hbound
        obtain ⟨hspent, hkept⟩ := hbound
        have hpair := tail_clock_of_body state post fname arguments values body callee
          returnShape result hargs hlookup hzero hrun hntBody
        dsimp only at hpair
        rw [evaluateHOLFiniteState_call, hargs] at hpair
        dsimp only at hpair
        rw [hlookup] at hpair
        dsimp only at hpair
        rw [if_neg hzero, hrun] at hpair
        rw [hpair.2]
        change state.clock - 1 ≤ post.clock + B at hspent
        change post.clock ≤ state.clock - 1 at hkept
        exact ⟨by omega, by omega⟩

theorem TerminatingProgBounded.decCall {fname : MlS} {B Bc : Nat}
    (hfun : TerminatingFunBounded fname B) (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64))
    {continuation : ProgHOL 64} (hcont : TerminatingProgBounded continuation Bc) :
    TerminatingProgBounded (.decCall name shape fname arguments continuation) (B + Bc + 1) := by
  intro F state hcode
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  cases hargs : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
  | none => exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  | some values =>
    rw [hargs] at hnt
    dsimp only at hnt ⊢
    cases hlookup : lookupCodeHOLFinite state.code.lookup fname values with
    | none => exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    | some found =>
      obtain ⟨body, callee, returnShape⟩ := found
      rw [hlookup] at hnt
      dsimp only at hnt ⊢
      by_cases hzero : state.clock = 0
      · rw [if_pos hzero] at hnt; exact absurd rfl hnt
      · rw [if_neg hzero] at hnt ⊢
        have hentry := terminating_body_of_fun hfun hcode hlookup
        have hmeta := evalP_code (callEntryStateHOLFinite state callee) body
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨result, post⟩
        rw [hrun] at hnt hmeta
        dsimp only at hnt hmeta ⊢
        have bodyClock : result ≠ some .timeOut → state.clock - 1 ≤ post.clock + B ∧ post.clock ≤ state.clock - 1 := by
          intro hsafe
          have hbound := hentry (by rw [hrun]; exact hsafe)
          rw [hrun] at hbound
          exact hbound
        cases result with
        | none =>
          dsimp only at hnt ⊢
          obtain ⟨hspent, hkept⟩ := bodyClock (by simp)
          exact ⟨by omega, by omega⟩
        | some r =>
          cases r with
          | returned value =>
            dsimp only at hnt ⊢
            obtain ⟨hspent, hkept⟩ := bodyClock (by simp)
            by_cases hshape : (shapeEqHOL (shapeOfHOLExact value) shape &&
                shapeEqHOL (shapeOfHOLExact value) returnShape) = true
            · rw [if_pos hshape] at hnt ⊢
              let resumed := setVarHOLFinite name value { post with locals := state.locals }
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              rcases hcontRun : evaluateHOLFiniteState resumed continuation with ⟨cres, cpost⟩
              rw [hcontRun] at hnt
              dsimp only at hnt ⊢
              have htail := hcont resumed hresCode (by rw [hcontRun]; exact hnt)
              rw [hcontRun] at htail
              obtain ⟨hspentC, hkeptC⟩ := htail
              change post.clock ≤ cpost.clock + Bc at hspentC
              change cpost.clock ≤ post.clock at hkeptC
              exact ⟨by omega, by omega⟩
            · rw [if_neg hshape]; dsimp only; exact ⟨by omega, by omega⟩
          | timeOut => exact absurd rfl hnt
          | error =>
            obtain ⟨hspent, hkept⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩
          | «break» =>
            dsimp only at hnt ⊢
            obtain ⟨hspent, hkept⟩ := bodyClock (by simp)
            exact ⟨by omega, by omega⟩
          | «continue» =>
            dsimp only at hnt ⊢
            obtain ⟨hspent, hkept⟩ := bodyClock (by simp)
            exact ⟨by omega, by omega⟩
          | exception _ _ =>
            obtain ⟨hspent, hkept⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩
          | finalFfi _ =>
            obtain ⟨hspent, hkept⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩

def LoopStep (μ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat)
    (condition : ExpHOL 64) (body : ProgHOL 64) (K : Nat)
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun _ => True) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (word : BitVec 64),
    state.code = originalRuntimeCode → P state →
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) condition =
      some (.val (.word word)) →
    word ≠ 0 → state.clock ≠ 0 →
    let output := evaluateHOLFiniteState (decClockHOLFinite state) body
    output.1 ≠ some .timeOut →
      state.clock - 1 ≤ output.2.clock + K ∧ output.2.clock ≤ state.clock - 1 ∧
      (output.1 = none ∨ output.1 = some .continue → μ output.2 < μ state ∧ output.2.code = state.code ∧ P output.2)

theorem while_step_of_progBounded (μ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat)
    (condition : ExpHOL 64) {body : ProgHOL 64} {K : Nat}
    (hbody : TerminatingProgBounded body K)
    (hdrop : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (word : BitVec 64),
      state.code = originalRuntimeCode →
      evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) condition =
        some (.val (.word word)) →
      word ≠ 0 → state.clock ≠ 0 →
      let output := evaluateHOLFiniteState (decClockHOLFinite state) body
      output.1 = none ∨ output.1 = some .continue → μ output.2 < μ state) :
    LoopStep μ condition body K := by
  intro F state word hcode _ hcond hnz hclk
  dsimp only
  intro hnt
  obtain ⟨hspent, hkept⟩ := hbody (decClockHOLFinite state) (by simpa [decClockHOLFinite] using hcode) hnt
  refine ⟨hspent, hkept, fun hflow => ⟨hdrop state word hcode hcond hnz hclk hflow, ?_⟩⟩
  exact ⟨evalP_code (decClockHOLFinite state) body, trivial⟩

theorem TerminatingProgBoundedOn.while_measure
    (μ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat)
    (condition : ExpHOL 64) (body : ProgHOL 64) {n K : Nat}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hstep : LoopStep μ condition body K P) :
    TerminatingProgBoundedOn (fun state => P state ∧ μ state ≤ n)
      (.while condition body) ((n + 1) * (K + 1)) := by
  intro F state hcode ⟨hP, hrank⟩
  induction n using Nat.strongRecOn generalizing state with
  | ind n ih =>
    unfold TerminatingRunBounded
    dsimp only
    intro hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    revert hnt; split <;> intro hnt
    · rename_i word hword
      by_cases hzeroWord : word = 0
      · rw [if_neg (by simp [hzeroWord])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
      · rw [if_pos hzeroWord] at hnt ⊢
        by_cases hclock : state.clock = 0
        · rw [if_pos hclock] at hnt; exact absurd rfl hnt
        · rw [if_neg hclock] at hnt ⊢
          rcases hbody : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨result, post⟩
          rw [hbody] at hnt
          dsimp only at hnt ⊢
          have stepped (hsafe : result ≠ some .timeOut) := by
            have hstepped := hstep state word hcode hP hword hzeroWord hclock (by rw [hbody]; exact hsafe)
            rw [hbody] at hstepped
            exact hstepped
          cases result with
          | none =>
            dsimp only at hnt ⊢
            obtain ⟨hspent, hkept, hdrop⟩ := stepped (by simp)
            obtain ⟨hmu, hpostCode, hpostP⟩ := hdrop (Or.inl rfl)
            dsimp only at hmu hpostCode
            obtain ⟨htailSpent, htailKept⟩ := ih (μ post) (by omega) post (hpostCode.trans hcode) hpostP (Nat.le_refl _) hnt
            dsimp only at hspent hkept htailSpent htailKept
            have hmul : (μ post + 1) * (K + 1) + (K + 1) ≤ (n + 1) * (K + 1) := by
              rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
            exact ⟨by omega, by omega⟩
          | some r =>
            cases r with
            | «continue» =>
              dsimp only at hnt ⊢
              obtain ⟨hspent, hkept, hdrop⟩ := stepped (by simp)
              obtain ⟨hmu, hpostCode, hpostP⟩ := hdrop (Or.inr rfl)
              dsimp only at hmu hpostCode
              obtain ⟨htailSpent, htailKept⟩ := ih (μ post) (by omega) post (hpostCode.trans hcode) hpostP (Nat.le_refl _) hnt
              dsimp only at hspent hkept htailSpent htailKept
              have hmul : (μ post + 1) * (K + 1) + (K + 1) ≤ (n + 1) * (K + 1) := by
                rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
              exact ⟨by omega, by omega⟩
            | «break» =>
              dsimp only at hnt ⊢
              obtain ⟨hspent, hkept, _⟩ := stepped (by simp)
              dsimp only at hspent hkept
              have h1 : K + 1 ≤ (n + 1) * (K + 1) := Nat.le_mul_of_pos_left _ (by omega)
              exact ⟨by omega, by omega⟩
            | timeOut => exact absurd rfl hnt
            | _ =>
              dsimp only at hnt ⊢
              obtain ⟨hspent, hkept, _⟩ := stepped (by simp)
              dsimp only at hspent hkept
              have h1 : K + 1 ≤ (n + 1) * (K + 1) := Nat.le_mul_of_pos_left _ (by omega)
              exact ⟨by omega, by omega⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

/-- Build the loop-step obligation from an invariant-restricted body bound.
The body starts after the loop's clock tick, so its precondition is stated
at that entry state. Only continuing outcomes must preserve the invariant. -/
theorem while_step_of_progBoundedOn
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (μ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat)
    (condition : ExpHOL 64) {body : ProgHOL 64} {K : Nat}
    (hbody : TerminatingProgBoundedOn P body K)
    (hentry : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      P state → P (decClockHOLFinite state))
    (hdrop : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (word : BitVec 64),
      state.code = originalRuntimeCode → P state →
      evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) condition =
        some (.val (.word word)) →
      word ≠ 0 → state.clock ≠ 0 →
      let output := evaluateHOLFiniteState (decClockHOLFinite state) body
      output.1 = none ∨ output.1 = some .continue → μ output.2 < μ state ∧ P output.2) :
    LoopStep μ condition body K P := by
  intro F state word hcode hP hcond hnz hclk
  dsimp only
  intro hnt
  obtain ⟨hspent, hkept⟩ := hbody (decClockHOLFinite state) hcode (hentry state hP) hnt
  refine ⟨hspent, hkept, ?_⟩
  intro hflow
  obtain ⟨hmu, hpost⟩ := hdrop state word hcode hP hcond hnz hclk hflow
  exact ⟨hmu, evalP_code (decClockHOLFinite state) body, hpost⟩

theorem TerminatingProgBounded.while_step (μ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat)
    (condition : ExpHOL 64) (body : ProgHOL 64) {n K : Nat} (hstep : LoopStep μ condition body K)
    (hcap : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), μ state ≤ n) :
    TerminatingProgBounded (.while condition body) ((n + 1) * (K + 1)) :=
  fun state hcode => TerminatingProgBoundedOn.while_measure μ condition body hstep state hcode ⟨trivial, hcap state⟩

theorem TerminatingProgBounded.while_measure (μ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat)
    (condition : ExpHOL 64) (body : ProgHOL 64) {n K : Nat} (hstep : LoopStep μ condition body K)
    (hcap : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), μ state ≤ n) :
    TerminatingProgBounded (.while condition body) ((n + 1) * (K + 1)) :=
  TerminatingProgBounded.while_step μ condition body hstep hcap

end InitECandidate.Solver.PanTerminatingCombinators
