import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant
import InitECandidate.Solver.GuestTrapAlign

set_option autoImplicit false

namespace InitECandidate.Solver.PanRunBounded

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep

def ClockPreserving {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) : Prop :=
  ∀ state : PanSemStateFiniteExact width σ,
    (evaluateHOLFiniteState state program).2.clock = state.clock

def extStraightLine {width : Nat} [NeZero width] : ProgHOL width → Bool
  | .dec _ _ _ body => extStraightLine body
  | .seq first second => extStraightLine first && extStraightLine second
  | .ite _ yes no => extStraightLine yes && extStraightLine no
  | .skip | .break | .continue | .annot _ _ => true
  | .assign _ _ _ | .storeByte _ _ | .store _ _ | .store32 _ _ | .raise _ _ | .return _ => true
  | .primitive _ _ _ | .extCall _ _ _ _ _ => true
  | .shMemLoad _ _ _ _ | .shMemStore _ _ _ => true
  | _ => false

theorem evaluateHOLFiniteState_metadata {F : Type} (state : PanSemStateFiniteExact 64 F) (program : ProgHOL 64) :
    (evaluateHOLFiniteState state program).2.code = state.code ∧
      (evaluateHOLFiniteState state program).2.memaddrs = state.memaddrs ∧
      (evaluateHOLFiniteState state program).2.be = state.be ∧
      (evaluateHOLFiniteState state program).2.shMemaddrs = state.shMemaddrs ∧
      (evaluateHOLFiniteState state program).2.eshapes = state.eshapes := by
  have invariant := evaluateInvariantsHOLFinite program
    (PanPropsEvalStateFiniteExact.ofPanSemFinite state)
    (evaluateHOLFiniteState state program).1
    (PanPropsEvalStateFiniteExact.ofPanSemFinite (evaluateHOLFiniteState state program).2) (by
      simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
        PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite]
      )
  exact ⟨invariant.2.2.2.2.2.2.1,invariant.1,invariant.2.2.1,invariant.2.1,invariant.2.2.2.1⟩

theorem evaluate_store_control_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) :
    ((evaluateHOLFiniteState state (.store destination value)).1 = none ∨
      (evaluateHOLFiniteState state (.store destination value)).1 = some .error) ∧
    (evaluateHOLFiniteState state (.store destination value)).2.locals = state.locals ∧
    (evaluateHOLFiniteState state (.store destination value)).2.clock = state.clock := by
  rw [evaluateHOLFiniteState_store]
  split
  · split
    · split <;> simp
    · simp
  · simp

theorem evaluate_storeByte_control_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) :
    ((evaluateHOLFiniteState state (.storeByte destination value)).1 = none ∨
      (evaluateHOLFiniteState state (.storeByte destination value)).1 = some .error) ∧
    (evaluateHOLFiniteState state (.storeByte destination value)).2.clock = state.clock ∧
    (evaluateHOLFiniteState state (.storeByte destination value)).2.locals = state.locals ∧
    (evaluateHOLFiniteState state (.storeByte destination value)).2.globals = state.globals ∧
    (evaluateHOLFiniteState state (.storeByte destination value)).2.code = state.code ∧
    (evaluateHOLFiniteState state (.storeByte destination value)).2.memaddrs = state.memaddrs ∧
    (evaluateHOLFiniteState state (.storeByte destination value)).2.be = state.be := by
  rw [evaluateHOLFiniteState_storeByte]
  split
  · split
    · split <;> simp
    · simp
  · simp

theorem evaluate_external_call_clock {F : Type} (state : PanSemStateFiniteExact 64 F)
    (function : MlS) (configuration configurationLength array arrayLength : ExpHOL 64) :
    (evaluateHOLFiniteState state (.extCall function configuration configurationLength array arrayLength)).2.clock = state.clock := by
  rw [evaluateHOLFiniteState_extCall_source]
  split
  · split
    · split <;> rfl
    · rfl
  · rfl

theorem evaluate_external_call_no_timeout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (function : MlS) (configuration configurationLength array arrayLength : ExpHOL 64) :
    (evaluateHOLFiniteState state (.extCall function configuration configurationLength array arrayLength)).1 ≠ some .timeOut := by
  rw [evaluateHOLFiniteState_extCall_source]
  split
  · split
    · split <;> simp
    · simp
  · simp

theorem evaluate_raise_no_timeout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (exception : MlS) (expression : ExpHOL 64) :
    (evaluateHOLFiniteState state (.raise exception expression)).1 ≠ some .timeOut := by
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split <;> simp
  · simp

theorem evaluate_sequence_no_timeout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (first second : ProgHOL 64)
    (one : (evaluateHOLFiniteState state first).1 ≠ some .timeOut)
    (two : ∀ next : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState next second).1 ≠ some .timeOut) :
    (evaluateHOLFiniteState state (.seq first second)).1 ≠ some .timeOut := by
  rw [evaluateHOLFiniteState_seq]
  dsimp only
  split
  · exact two _
  · exact one

theorem clockPreserving_skip {width : Nat} {σ : Type} [NeZero width] : ClockPreserving (σ := σ) (.skip : ProgHOL width) := by
  intro state
  rw [evaluateHOLFiniteState_skip]

theorem clockPreserving_assign {width : Nat} {σ : Type} [NeZero width] (kind : VarKind) (name : MlS) (value : ExpHOL width) :
    ClockPreserving (σ := σ) (.assign kind name value) := by
  intro state
  rw [evaluateHOLFiniteState_assign]
  split <;> try rfl
  split
  · cases kind <;> rfl
  · rfl

theorem clockPreserving_store {width : Nat} {σ : Type} [NeZero width] (destination value : ExpHOL width) :
    ClockPreserving (σ := σ) (.store destination value) := by
  intro state
  rw [evaluateHOLFiniteState_store]
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

theorem clockPreserving_return {width : Nat} {σ : Type} [NeZero width] (value : ExpHOL width) :
    ClockPreserving (σ := σ) (.return value) := by
  intro state
  rw [evaluateHOLFiniteState_return]
  split <;> try rfl
  split <;> rfl

theorem clockPreserving_raise {width : Nat} {σ : Type} [NeZero width] (name : MlS) (value : ExpHOL width) :
    ClockPreserving (σ := σ) (.raise name value) := by
  intro state
  rw [evaluateHOLFiniteState_raise]
  split <;> try rfl
  dsimp only
  split <;> rfl

theorem clockPreserving_seq {width : Nat} {σ : Type} [NeZero width] (first second : ProgHOL width)
    (one : ClockPreserving (σ := σ) first) (two : ClockPreserving (σ := σ) second) :
    ClockPreserving (σ := σ) (.seq first second) := by
  intro state
  rw [evaluateHOLFiniteState_seq]
  dsimp only
  have fixed : fixClockHOLFinite state (evaluateHOLFiniteState state first) =
      evaluateHOLFiniteState state first := by
    exact fixClockHOLFinite_evaluateState state first
  rw [fixed]
  split
  · exact (two _).trans (one state)
  · exact one state

theorem clockPreserving_ite {width : Nat} {σ : Type} [NeZero width] (condition : ExpHOL width) (yes no : ProgHOL width)
    (hy : ClockPreserving (σ := σ) yes) (hn : ClockPreserving (σ := σ) no) :
    ClockPreserving (σ := σ) (.ite condition yes no) := by
  intro state
  rw [evaluateHOLFiniteState_ite]
  split <;> try rfl
  split
  · exact hn state
  · exact hy state

theorem clockPreserving_dec {width : Nat} {σ : Type} [NeZero width] (name : MlS) (shape : ShapeHOL)
    (initializer : ExpHOL width) (body : ProgHOL width)
    (h : ClockPreserving (σ := σ) body) :
    ClockPreserving (σ := σ) (.dec name shape initializer body) := by
  intro state
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split <;> try rfl
  split
  · exact (h _).trans (by rfl)
  · rfl

theorem clockPreserving_of_extStraightLine {F : Type} (program : ProgHOL 64)
    (supported : extStraightLine program = true) : ClockPreserving (σ := F) program := by
  cases hprogram : program with
  | skip => exact clockPreserving_skip
  | dec name shape initializer body =>
    exact clockPreserving_dec name shape initializer body
      (clockPreserving_of_extStraightLine body (by simpa [hprogram, extStraightLine] using supported))
  | assign kind name value => exact clockPreserving_assign kind name value
  | storeByte destination value =>
    intro state
    exact (evaluate_storeByte_control_frame state destination value).2.1
  | store destination value => exact clockPreserving_store destination value
  | store32 address value =>
    intro state
    rw [evaluateHOLFiniteState_store32]
    split <;> repeat' first | split | rfl
  | shMemLoad operator kind name address =>
    intro state
    rw [evaluateHOLFiniteState_shMemLoad_source]
    split
    · split
      · dsimp only
        unfold shMemLoadHOLFiniteExact
        repeat' first | split | rfl | (cases kind <;> rfl)
      · rfl
    · rfl
  | shMemStore operator address value =>
    intro state
    classical
    rw [evaluateHOLFiniteState_shMemStore_total]
    dsimp only
    split
    · change (shMemStoreHOLExact state.toExact _ _ (nbOpHOL operator)).2.clock = state.clock
      unfold shMemStoreHOLExact
      split <;> split
      all_goals first | rfl | (split <;> rfl)
    · rfl
  | seq first second =>
    have pieces : extStraightLine first = true ∧ extStraightLine second = true := by
      simpa only [hprogram, extStraightLine, Bool.and_eq_true] using supported
    exact clockPreserving_seq first second (clockPreserving_of_extStraightLine first pieces.1)
      (clockPreserving_of_extStraightLine second pieces.2)
  | ite condition yes no =>
    have pieces : extStraightLine yes = true ∧ extStraightLine no = true := by
      simpa only [hprogram, extStraightLine, Bool.and_eq_true] using supported
    exact clockPreserving_ite condition yes no (clockPreserving_of_extStraightLine yes pieces.1)
      (clockPreserving_of_extStraightLine no pieces.2)
  | «break» => intro state; rw [evaluateHOLFiniteState_break]
  | «continue» => intro state; rw [evaluateHOLFiniteState_continue]
  | annot tag text => intro state; rw [evaluateHOLFiniteState_annot]
  | raise name value => exact clockPreserving_raise name value
  | «return» value => exact clockPreserving_return value
  | primitive name operator arguments =>
    intro state
    rw [evaluateHOLFiniteState_primitive]
    repeat' first | split | rfl
  | extCall function a b c d => intro state; exact evaluate_external_call_clock state function a b c d
  | _ => simp [hprogram, extStraightLine] at supported
termination_by sizeOf program
decreasing_by all_goals simp_all <;> omega

theorem evaluate_extStraightLine_no_timeout {F : Type} (program : ProgHOL 64)
    (supported : extStraightLine program = true) (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state program).1 ≠ some .timeOut := by
  cases shape : program with
  | skip => simp [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    have child : extStraightLine body = true := by simpa only [shape,extStraightLine] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_extStraightLine_no_timeout body child _
      · simp
  | assign kind name value =>
    rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp
  | storeByte destination value =>
    rcases (evaluate_storeByte_control_frame state destination value).1 with normal | error
    · rw [normal]; simp
    · rw [error]; simp
  | store destination value =>
    rcases (evaluate_store_control_frame state destination value).1 with normal | error
    · rw [normal]; simp
    · rw [error]; simp
  | store32 address value =>
    rw [evaluateHOLFiniteState_store32]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | shMemLoad operator kind name address =>
    rw [evaluateHOLFiniteState_shMemLoad_source]
    split
    · split
      · dsimp only
        unfold shMemLoadHOLFiniteExact
        repeat' first | split | simp
      · simp
    · simp
  | shMemStore operator address value =>
    classical
    rw [evaluateHOLFiniteState_shMemStore_total]
    dsimp only
    split
    · unfold shMemStoreHOLExact
      repeat' first | split | simp
    · simp
  | seq first second =>
    have children : extStraightLine first = true ∧ extStraightLine second = true := by
      simpa only [shape,extStraightLine,Bool.and_eq_true] using supported
    exact evaluate_sequence_no_timeout state first second (evaluate_extStraightLine_no_timeout first children.1 state)
      (fun next => evaluate_extStraightLine_no_timeout second children.2 next)
  | ite condition yes no =>
    have children : extStraightLine yes = true ∧ extStraightLine no = true := by
      simpa only [shape,extStraightLine,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_extStraightLine_no_timeout no children.2 state
      · exact evaluate_extStraightLine_no_timeout yes children.1 state
    · simp
  | «break» => simp [evaluateHOLFiniteState_break]
  | «continue» => simp [evaluateHOLFiniteState_continue]
  | annot tag text => simp [evaluateHOLFiniteState_annot]
  | raise name value => exact evaluate_raise_no_timeout state name value
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | primitive name operator arguments =>
    rw [evaluateHOLFiniteState_primitive]
    repeat' first | split | simp
  | extCall function a b c d => exact evaluate_external_call_no_timeout state function a b c d
  | _ => simp [shape,extStraightLine] at supported
termination_by sizeOf program
decreasing_by all_goals simp_all <;> omega

theorem lookupCodeHOLFinite_installed_body
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (name : MlS) (parameters : List (MlS × ShapeHOL)) (body foundBody : ProgHOL 64)
    (returnShape foundShape : ShapeHOL) (values : List (ValueHOL 64))
    (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (installed : code name = some (parameters,body,returnShape))
    (found : PanSemStateFiniteExact.lookupCodeHOLFinite code name values = some (foundBody,locals,foundShape)) :
    foundBody = body := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at found
  split at found
  · cases found
  · rename_i exactBody exactLocals exactShape raw
    have same : exactBody = body := by
      simp only [lookupCodeHOLExact,installed] at raw
      split at raw
      · exact ((Prod.mk.inj (Option.some.inj raw)).1).symm
      · cases raw
    have equal := Option.some.inj found
    exact ((Prod.mk.inj equal).1).symm.trans same

theorem evaluate_call_body_clock_no_timeout {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (function : MlS)
    (destination : Option (VarKind × MlS))
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (result : Option (PanSemResultExact 64))
    (args : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (clock : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result,post))
    (noTimeout : result ≠ some .timeOut) :
    let output := evaluateHOLFiniteState state (.call (some (destination,none)) function arguments)
    output.1 ≠ some .timeOut ∧ output.2.clock = post.clock := by
  dsimp only
  rw [evaluateHOLFiniteState_call,args]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg clock,run]
  cases result with
  | none => simp
  | some result =>
    cases result <;> simp_all [emptyLocalsHOLFinite]
    split
    · cases destination with
      | none => simp
      | some destination =>
        rcases destination with ⟨kind,name⟩
        dsimp only
        split <;> cases kind <;> simp [setKvarHOLFinite,setVarHOLFinite,setGlobalHOLFinite]
    · simp

theorem evaluate_uniformCallee_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (function : MlS) (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) (bodyCost : Nat)
    (budget : bodyCost + 1 ≤ state.clock)
    (bodies : ∀ values body locals returnShape,
      lookupCodeHOLFinite state.code.lookup function values = some (body,locals,returnShape) →
      let entry := callEntryStateHOLFinite state locals
      let evaluated := evaluateHOLFiniteState entry body
      entry.clock ≤ evaluated.2.clock + bodyCost ∧ evaluated.2.clock ≤ entry.clock ∧
        evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,none)) function arguments)
    state.clock ≤ evaluated.2.clock + (bodyCost + 1) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => rw [evaluateHOLFiniteState_call,args]; simp
  | some values =>
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => rw [evaluateHOLFiniteState_call,args]; dsimp only; rw [lookup]; simp
    | some installed =>
      obtain ⟨body,callee,returnShape⟩ := installed
      let entry := callEntryStateHOLFinite state callee
      have bounded := bodies values body callee returnShape lookup
      change entry.clock ≤ (evaluateHOLFiniteState entry body).2.clock + bodyCost ∧
        (evaluateHOLFiniteState entry body).2.clock ≤ entry.clock ∧
        (evaluateHOLFiniteState entry body).1 ≠ some .timeOut at bounded
      cases ran : evaluateHOLFiniteState entry body with
      | mk result post =>
        rw [ran] at bounded
        dsimp only at bounded
        have output := evaluate_call_body_clock_no_timeout state post function destination arguments values body callee
          returnShape result args lookup (by omega) ran bounded.2.2
        dsimp only
        rw [output.2]
        have spent : state.clock - 1 ≤ post.clock + bodyCost := bounded.1
        have kept : post.clock ≤ state.clock - 1 := bounded.2.1
        exact ⟨by omega,by omega,output.1⟩

theorem evaluate_tailCall_uniform_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (function : MlS) (arguments : List (ExpHOL 64)) (bodyCost : Nat)
    (budget : bodyCost + 1 ≤ state.clock)
    (bodies : ∀ values body locals returnShape,
      lookupCodeHOLFinite state.code.lookup function values = some (body,locals,returnShape) →
      let entry := callEntryStateHOLFinite state locals
      let evaluated := evaluateHOLFiniteState entry body
      entry.clock ≤ evaluated.2.clock + bodyCost ∧ evaluated.2.clock ≤ entry.clock ∧
        evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.call none function arguments)
    state.clock ≤ evaluated.2.clock + (bodyCost + 1) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => rw [evaluateHOLFiniteState_call,args]; simp
  | some values =>
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => rw [evaluateHOLFiniteState_call,args]; dsimp only; rw [lookup]; simp
    | some installed =>
      obtain ⟨body,callee,returnShape⟩ := installed
      have bounded := bodies values body callee returnShape lookup
      change (callEntryStateHOLFinite state callee).clock ≤
          (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.clock + bodyCost ∧
        (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.clock ≤
          (callEntryStateHOLFinite state callee).clock ∧
        (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).1 ≠ some .timeOut at bounded
      have nonzero : state.clock ≠ 0 := by omega
      cases ran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
      | mk result post =>
        rw [ran] at bounded
        obtain ⟨spent,kept,safe⟩ := bounded
        change state.clock - 1 ≤ post.clock + bodyCost at spent
        change post.clock ≤ state.clock - 1 at kept
        rw [evaluateHOLFiniteState_call,args]
        dsimp only
        rw [lookup]
        dsimp only
        rw [if_neg nonzero,ran]
        rcases result with _ | (_ | _ | _ | _ | _ | _ | _ | _ | _)
        all_goals first
          | (simp at safe; done)
          | (dsimp only; split <;> ((try simp only [emptyLocalsHOLFinite]); exact ⟨by omega,by omega,by simp⟩))
          | (dsimp only; (try simp only [emptyLocalsHOLFinite]); exact ⟨by omega,by omega,by simp [safe]⟩)

theorem evaluate_decCall_continuation_bounded {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (name function : MlS)
    (shape returnShape : ShapeHOL) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (result : Option (PanSemResultExact 64)) (cost tailCost : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (nonzero : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result,post))
    (remaining : post.clock ≤ (callEntryStateHOLFinite state callee).clock)
    (bound : state.clock ≤ post.clock + cost)
    (noTimeout : result ≠ some .timeOut)
    (continuationBound : ∀ value, result = some (.returned value) →
      let resumed := setVarHOLFinite name value {post with locals := state.locals}
      let evaluated := evaluateHOLFiniteState resumed continuation
      resumed.clock ≤ evaluated.2.clock + tailCost ∧ evaluated.2.clock ≤ resumed.clock ∧ evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.decCall name shape function arguments continuation)
    state.clock ≤ evaluated.2.clock + (cost + tailCost) ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have postRemaining : post.clock ≤ state.clock := by
    change post.clock ≤ state.clock - 1 at remaining
    omega
  rw [evaluateHOLFiniteState_decCall_total,args]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg nonzero,run]
  have fixed : fixClockHOLFinite (callEntryStateHOLFinite state callee) (result,post) = (result,post) := by
    simp [fixClockHOLFinite,Nat.not_lt.mpr remaining]
  rw [fixed]
  dsimp only
  cases result with
  | none => exact ⟨by change state.clock ≤ post.clock + (cost + tailCost); omega,postRemaining,by simp⟩
  | some result =>
    cases result with
    | returned value =>
      simp only
      split
      · let resumed := setVarHOLFinite name value {post with locals := state.locals}
        have tail := continuationBound value rfl
        change post.clock ≤ (evaluateHOLFiniteState resumed continuation).2.clock + tailCost ∧
          (evaluateHOLFiniteState resumed continuation).2.clock ≤ post.clock ∧
          (evaluateHOLFiniteState resumed continuation).1 ≠ some .timeOut at tail
        change state.clock ≤ (evaluateHOLFiniteState resumed continuation).2.clock + (cost + tailCost) ∧
          (evaluateHOLFiniteState resumed continuation).2.clock ≤ state.clock ∧
          (evaluateHOLFiniteState resumed continuation).1 ≠ some .timeOut
        exact ⟨by omega,by omega,tail.2.2⟩
      · exact ⟨by change state.clock ≤ post.clock + (cost + tailCost); omega,postRemaining,by simp⟩
    | timeOut => exact False.elim (noTimeout rfl)
    | error => exact ⟨by change state.clock ≤ post.clock + (cost + tailCost); omega,postRemaining,by simp⟩
    | «break» => exact ⟨by change state.clock ≤ post.clock + (cost + tailCost); omega,postRemaining,by simp⟩
    | «continue» => exact ⟨by change state.clock ≤ post.clock + (cost + tailCost); omega,postRemaining,by simp⟩
    | exception exception value => exact ⟨by change state.clock ≤ post.clock + (cost + tailCost); omega,postRemaining,by simp⟩
    | finalFfi ffi => exact ⟨by change state.clock ≤ post.clock + (cost + tailCost); omega,postRemaining,by simp⟩

theorem evaluate_decCall_uniform_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (bodyCost tailCost : Nat) (budget : bodyCost + 1 + tailCost ≤ state.clock)
    (bodies : ∀ values body locals returnShape,
      lookupCodeHOLFinite state.code.lookup function values = some (body,locals,returnShape) →
      let entry := callEntryStateHOLFinite state locals
      let evaluated := evaluateHOLFiniteState entry body
      entry.clock ≤ evaluated.2.clock + bodyCost ∧ evaluated.2.clock ≤ entry.clock ∧
        evaluated.1 ≠ some .timeOut)
    (tail : ∀ next : PanSemStateFiniteExact 64 F, next.code = state.code → tailCost ≤ next.clock →
      next.clock ≤ (evaluateHOLFiniteState next continuation).2.clock + tailCost ∧
        (evaluateHOLFiniteState next continuation).2.clock ≤ next.clock ∧
        (evaluateHOLFiniteState next continuation).1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.decCall name shape function arguments continuation)
    state.clock ≤ evaluated.2.clock + (bodyCost + 1 + tailCost) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state name shape function arguments continuation args]
    simp
  | some values =>
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none =>
      rw [evaluateHOLFiniteState_decCall_lookup_none state name shape function arguments continuation values args lookup]
      simp
    | some installed =>
      obtain ⟨body,callee,returnShape⟩ := installed
      have bounded := bodies values body callee returnShape lookup
      change (callEntryStateHOLFinite state callee).clock ≤
          (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.clock + bodyCost ∧
        (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.clock ≤
          (callEntryStateHOLFinite state callee).clock ∧
        (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).1 ≠ some .timeOut at bounded
      have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
      cases ran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
      | mk result post =>
        rw [ran] at bounded meta'
        obtain ⟨spent,kept,safe⟩ := bounded
        change state.clock - 1 ≤ post.clock + bodyCost at spent
        have whole := evaluate_decCall_continuation_bounded state post name function shape returnShape arguments values
          body continuation callee result (bodyCost + 1) tailCost args lookup (by omega) ran kept (by omega) safe
          (by
            intro value _
            apply tail
            · change post.code = state.code
              exact meta'.1
            · change tailCost ≤ post.clock
              omega)
        simpa only [Nat.add_assoc] using whole

theorem evaluate_sequence_code_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (first tail : ProgHOL 64) (firstCost tailCost : Nat)
    (firstBound : state.clock ≤ (evaluateHOLFiniteState state first).2.clock + firstCost ∧
      (evaluateHOLFiniteState state first).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state first).1 ≠ some .timeOut)
    (tailBound : ∀ next : PanSemStateFiniteExact 64 F, next.code = state.code → tailCost ≤ next.clock →
      next.clock ≤ (evaluateHOLFiniteState next tail).2.clock + tailCost ∧
        (evaluateHOLFiniteState next tail).2.clock ≤ next.clock ∧
        (evaluateHOLFiniteState next tail).1 ≠ some .timeOut)
    (budget : firstCost + tailCost ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.seq first tail)
    state.clock ≤ evaluated.2.clock + (firstCost + tailCost) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have metadata := evaluateHOLFiniteState_metadata state first
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state first with
  | mk result next =>
    rw [run] at firstBound metadata
    dsimp only at firstBound metadata ⊢
    cases result with
    | some result =>
      dsimp only
      exact ⟨by have consumed := firstBound.1; omega,firstBound.2⟩
    | none =>
      dsimp only
      have tail := tailBound next metadata.1 (by have consumed := firstBound.1; omega)
      exact ⟨by have a := firstBound.1; have b := tail.1; omega,
        Nat.le_trans tail.2.1 firstBound.2.1,tail.2.2⟩

theorem evaluate_handled_call_bounded {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (function handlerId handlerVar : MlS)
    (destination : Option (VarKind × MlS))
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body handler : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (result : Option (PanSemResultExact 64)) (bodyCost handlerCost : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (nonzero : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result,post))
    (bound : state.clock ≤ post.clock + bodyCost) (remaining : post.clock ≤ state.clock)
    (noTimeout : result ≠ some .timeOut)
    (handlerBound : ∀ value, result = some (.exception handlerId value) →
      let resumed := setVarHOLFinite handlerVar value {post with locals := state.locals}
      let evaluated := evaluateHOLFiniteState resumed handler
      resumed.clock ≤ evaluated.2.clock + handlerCost ∧ evaluated.2.clock ≤ resumed.clock ∧ evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,some (handlerId,handlerVar,handler))) function arguments)
    state.clock ≤ evaluated.2.clock + (bodyCost + handlerCost) ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rw [evaluateHOLFiniteState_call,args]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg nonzero,run]
  cases result with
  | none => exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,remaining,by simp⟩
  | some result =>
    cases result with
    | returned value =>
      simp only
      split
      · cases destination with
        | none => exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,remaining,by simp⟩
        | some destination =>
          rcases destination with ⟨kind,name⟩
          dsimp only
          split <;> cases kind <;>
            exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,
              by exact remaining,by simp⟩
      · exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,remaining,by simp⟩
    | timeOut => exact False.elim (noTimeout rfl)
    | error => exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,remaining,by simp⟩
    | «break» => exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,remaining,by simp⟩
    | «continue» => exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,remaining,by simp⟩
    | finalFfi ffi => exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,remaining,by simp⟩
    | exception exceptionId value =>
      simp only
      by_cases equal : exceptionId = handlerId
      · subst exceptionId
        rw [if_pos rfl]
        cases shape : state.eshapes.lookup handlerId with
        | none => exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,remaining,by simp⟩
        | some declared =>
          simp only
          split
          · have tail := handlerBound value rfl
            change post.clock ≤ _ + handlerCost ∧ _ ≤ post.clock ∧ _ at tail
            exact ⟨by omega,by omega,tail.2.2⟩
          · exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,remaining,by simp⟩
      · rw [if_neg equal]
        exact ⟨by change state.clock ≤ post.clock + (bodyCost + handlerCost); omega,remaining,by simp⟩

def ProgBounded (program : ProgHOL 64) (cost : Nat) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode → cost ≤ state.clock →
    state.clock ≤ (evaluateHOLFiniteState state program).2.clock + cost ∧
      (evaluateHOLFiniteState state program).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state program).1 ≠ some .timeOut

def FunBounded (function : MlS) (cost : Nat) : Prop :=
  ∃ parameters body returnShape, originalRuntimeCode.lookup function = some (parameters,body,returnShape) ∧
    ProgBounded body cost

namespace ProgBounded

theorem weaken {program : ProgHOL 64} {cost larger : Nat} (bounded : ProgBounded program cost)
    (le : cost ≤ larger) : ProgBounded program larger := by
  intro F state code budget
  obtain ⟨a,b,c⟩ := bounded state code (by omega)
  exact ⟨by omega,b,c⟩

theorem straight (program : ProgHOL 64) (supported : extStraightLine program = true) : ProgBounded program 0 := by
  intro F state _ _
  have clock := clockPreserving_of_extStraightLine (F := F) program supported state
  exact ⟨by omega,by omega,evaluate_extStraightLine_no_timeout program supported state⟩

theorem seq {first tail : ProgHOL 64} {a b : Nat} (left : ProgBounded first a) (right : ProgBounded tail b) :
    ProgBounded (.seq first tail) (a + b) := by
  intro F state code budget
  exact evaluate_sequence_code_bounded state first tail a b (left state code (by omega))
    (fun next nextCode nextBudget => right next (nextCode.trans code) nextBudget) budget

theorem ite (condition : ExpHOL 64) {yes no : ProgHOL 64} {cost : Nat}
    (left : ProgBounded yes cost) (right : ProgBounded no cost) :
    ProgBounded (.ite condition yes no) cost := by
  intro F state code budget
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact right state code budget
    · exact left state code budget
  · simp

theorem dec (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) {body : ProgHOL 64} {cost : Nat}
    (inner : ProgBounded body cost) : ProgBounded (.dec name shape initializer body) cost := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · simp
  · rename_i value _
    split
    · exact inner (setVarHOLFinite name value state) code budget
    · simp

theorem bodies_of_fun {function : MlS} {cost : Nat} (installed : FunBounded function cost)
    {F : Type} (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode)
    (budget : cost + 1 ≤ state.clock) :
    ∀ values body locals returnShape,
      lookupCodeHOLFinite state.code.lookup function values = some (body,locals,returnShape) →
      let entry := callEntryStateHOLFinite state locals
      let evaluated := evaluateHOLFiniteState entry body
      entry.clock ≤ evaluated.2.clock + cost ∧ evaluated.2.clock ≤ entry.clock ∧
        evaluated.1 ≠ some .timeOut := by
  obtain ⟨parameters,installedBody,returnShape,lookup,bounded⟩ := installed
  intro values body locals foundShape found
  have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters installedBody body
    returnShape foundShape values locals (by rw [code]; exact lookup) found
  subst same
  exact bounded (callEntryStateHOLFinite state locals) code (by change cost ≤ state.clock - 1; omega)

theorem call {function : MlS} {cost : Nat} (installed : FunBounded function cost)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) :
    ProgBounded (.call (some (destination,none)) function arguments) (cost + 1) := by
  intro F state code budget
  exact evaluate_uniformCallee_call_bounded state function destination arguments cost budget
    (bodies_of_fun installed state code budget)

theorem tail {function : MlS} {cost : Nat} (installed : FunBounded function cost)
    (arguments : List (ExpHOL 64)) :
    ProgBounded (.call none function arguments) (cost + 1) := by
  intro F state code budget
  exact evaluate_tailCall_uniform_bounded state function arguments cost budget
    (bodies_of_fun installed state code budget)

theorem decCall {function : MlS} {cost tailCost : Nat} (installed : FunBounded function cost)
    (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {continuation : ProgHOL 64}
    (rest : ProgBounded continuation tailCost) :
    ProgBounded (.decCall name shape function arguments continuation) (cost + 1 + tailCost) := by
  intro F state code budget
  exact evaluate_decCall_uniform_bounded state name function shape arguments continuation cost tailCost budget
    (bodies_of_fun installed state code (by omega))
    (fun next nextCode nextBudget => rest next (nextCode.trans code) nextBudget)

theorem handledCall {function : MlS} {cost handlerCost : Nat} (installed : FunBounded function cost)
    (handlerId handlerVar : MlS) (destination : Option (VarKind × MlS))
    (arguments : List (ExpHOL 64)) {handler : ProgHOL 64}
    (handlerBounded : ProgBounded handler handlerCost) :
    ProgBounded (.call (some (destination,some (handlerId,handlerVar,handler))) function arguments)
      (cost + 1 + handlerCost) := by
  intro F state code budget
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => rw [evaluateHOLFiniteState_call,args]; simp
  | some values =>
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => rw [evaluateHOLFiniteState_call,args]; dsimp only; rw [lookup]; simp
    | some found =>
      obtain ⟨body,callee,returnShape⟩ := found
      have bounded := bodies_of_fun installed state code (by omega) values body callee returnShape lookup
      change (callEntryStateHOLFinite state callee).clock ≤
          (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.clock + cost ∧
        (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.clock ≤
          (callEntryStateHOLFinite state callee).clock ∧
        (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).1 ≠ some .timeOut at bounded
      have metadata := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
      cases ran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
      | mk result post =>
        rw [ran] at bounded metadata
        obtain ⟨spent,kept,safe⟩ := bounded
        change state.clock - 1 ≤ post.clock + cost at spent
        change post.clock ≤ state.clock - 1 at kept
        have whole := evaluate_handled_call_bounded state post function handlerId handlerVar destination
          arguments values body handler callee returnShape result (cost + 1) handlerCost args lookup
          (by omega) ran (by omega) (by omega) safe (by
            intro value _
            apply handlerBounded
            · exact metadata.1.trans code
            · change handlerCost ≤ post.clock
              omega)
        simpa only [Nat.add_assoc] using whole

end ProgBounded

theorem FunBounded.call_bounded {function : MlS} {cost : Nat} (installed : FunBounded function cost)
    {F : Type} (state : PanSemStateFiniteExact 64 F) (destination : Option (VarKind × MlS))
    (arguments : List (ExpHOL 64)) (code : state.code = originalRuntimeCode) (budget : cost + 1 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (.call (some (destination,none)) function arguments)
    state.clock ≤ result.2.clock + (cost + 1) ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut :=
  ProgBounded.call installed destination arguments state code budget

def RunBounded {F : Type} (state : PanSemStateFiniteExact 64 F) (program : ProgHOL 64) (cost : Nat) : Prop :=
  state.clock ≤ (evaluateHOLFiniteState state program).2.clock + cost ∧
    (evaluateHOLFiniteState state program).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state program).1 ≠ some .timeOut

namespace RunBounded

theorem weaken {F : Type} {state : PanSemStateFiniteExact 64 F} {program : ProgHOL 64} {cost larger : Nat}
    (bounded : RunBounded state program cost) (le : cost ≤ larger) : RunBounded state program larger :=
  ⟨by have := bounded.1; omega,bounded.2.1,bounded.2.2⟩

theorem ofProg {F : Type} {state : PanSemStateFiniteExact 64 F} {program : ProgHOL 64} {cost : Nat}
    (bounded : ProgBounded program cost) (code : state.code = originalRuntimeCode) (budget : cost ≤ state.clock) :
    RunBounded state program cost :=
  bounded state code budget

theorem seq {F : Type} {state : PanSemStateFiniteExact 64 F} {first tail : ProgHOL 64} {a b : Nat}
    (left : RunBounded state first a) (budget : a + b ≤ state.clock)
    (right : ∀ next, evaluateHOLFiniteState state first = (none,next) → next.code = state.code →
      b ≤ next.clock → RunBounded next tail b) :
    RunBounded state (.seq first tail) (a + b) := by
  have meta' := evaluateHOLFiniteState_metadata state first
  unfold RunBounded at left ⊢
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state first with
  | mk result middle =>
    rw [run] at left meta'
    dsimp only at left meta'
    obtain ⟨l1,l2,l3⟩ := left
    cases result with
    | none =>
      dsimp only
      obtain ⟨r1,r2,r3⟩ := right middle run meta'.1 (by omega)
      exact ⟨by omega,by omega,r3⟩
    | some r =>
      dsimp only
      exact ⟨by omega,l2,l3⟩

theorem ite {F : Type} (s : PanSemStateFiniteExact 64 F) (condition : ExpHOL 64)
    {yes no : ProgHOL 64} {cost : Nat} (left : RunBounded s yes cost) (right : RunBounded s no cost) :
    RunBounded s (.ite condition yes no) cost := by
  unfold RunBounded at left right ⊢
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact right
    · exact left
  · simp

theorem decConst {F : Type} (state : PanSemStateFiniteExact 64 F) (name : MlS) (k : BitVec 64)
    {body : ProgHOL 64} {cost : Nat}
    (inner : RunBounded (setVarHOLFinite name (.val (.word k)) state) body cost) :
    RunBounded state (.dec name .one (.const k) body) cost := by
  unfold RunBounded at inner ⊢
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  exact inner

theorem decWord {F : Type} (state : PanSemStateFiniteExact 64 F) (name : MlS) (initializer : ExpHOL 64)
    (value : BitVec 64) {body : ProgHOL 64} {cost : Nat}
    (evaluated : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      initializer = some (.val (.word value)))
    (inner : RunBounded (setVarHOLFinite name (.val (.word value)) state) body cost) :
    RunBounded state (.dec name .one initializer body) cost := by
  unfold RunBounded at inner ⊢
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [evaluated]
  dsimp only
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word value))) = true := by
    simp [shapeOfHOLExact,shapeEqHOL]
  rw [if_pos shapeOk]
  exact inner

theorem dec {F : Type} (state : PanSemStateFiniteExact 64 F) (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64)
    {body : ProgHOL 64} {cost : Nat}
    (inner : ∀ value, @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      initializer = some value → RunBounded (setVarHOLFinite name value state) body cost) :
    RunBounded state (.dec name shape initializer body) cost := by
  unfold RunBounded
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · simp
  · rename_i value evaluated
    split
    · exact inner value evaluated
    · simp

theorem call {F : Type} {state : PanSemStateFiniteExact 64 F} {function : MlS}
    {destination : Option (VarKind × MlS)} {arguments : List (ExpHOL 64)} {values : List (ValueHOL 64)} {bodyCost : Nat}
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments = some values)
    (budget : bodyCost + 1 ≤ state.clock)
    (bodies : ∀ body locals returnShape,
      lookupCodeHOLFinite state.code.lookup function values = some (body,locals,returnShape) →
      RunBounded (callEntryStateHOLFinite state locals) body bodyCost) :
    RunBounded state (.call (some (destination,none)) function arguments) (bodyCost + 1) := by
  unfold RunBounded
  cases lookup : lookupCodeHOLFinite state.code.lookup function values with
  | none => rw [evaluateHOLFiniteState_call,args]; dsimp only; rw [lookup]; simp
  | some installed =>
    obtain ⟨body,callee,returnShape⟩ := installed
    have bounded := bodies body callee returnShape lookup
    unfold RunBounded at bounded
    cases ran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
    | mk result post =>
      rw [ran] at bounded
      dsimp only at bounded
      have output := evaluate_call_body_clock_no_timeout state post function destination arguments values body callee
        returnShape result args lookup (by omega) ran bounded.2.2
      rw [output.2]
      have spent : state.clock - 1 ≤ post.clock + bodyCost := bounded.1
      have kept : post.clock ≤ state.clock - 1 := bounded.2.1
      exact ⟨by omega,by omega,output.1⟩

theorem decCall {F : Type} {state : PanSemStateFiniteExact 64 F} {name function : MlS} {shape : ShapeHOL}
    {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64} {values : List (ValueHOL 64)} {bodyCost tailCost : Nat}
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments = some values)
    (budget : bodyCost + 1 + tailCost ≤ state.clock)
    (bodies : ∀ body locals returnShape,
      lookupCodeHOLFinite state.code.lookup function values = some (body,locals,returnShape) →
      RunBounded (callEntryStateHOLFinite state locals) body bodyCost ∧
      ∀ value post, evaluateHOLFiniteState (callEntryStateHOLFinite state locals) body = (some (.returned value),post) →
        tailCost ≤ post.clock →
        RunBounded (setVarHOLFinite name value {post with locals := state.locals}) continuation tailCost) :
    RunBounded state (.decCall name shape function arguments continuation) (bodyCost + 1 + tailCost) := by
  cases lookup : lookupCodeHOLFinite state.code.lookup function values with
  | none =>
    unfold RunBounded
    rw [evaluateHOLFiniteState_decCall_lookup_none state name shape function arguments continuation values args lookup]
    simp
  | some installed =>
    obtain ⟨body,callee,returnShape⟩ := installed
    obtain ⟨bounded,resume⟩ := bodies body callee returnShape lookup
    unfold RunBounded at bounded
    cases ran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
    | mk result post =>
      rw [ran] at bounded
      obtain ⟨spent,kept,safe⟩ := bounded
      change state.clock - 1 ≤ post.clock + bodyCost at spent
      have whole := evaluate_decCall_continuation_bounded state post name function shape returnShape arguments values
        body continuation callee result (bodyCost + 1) tailCost args lookup (by omega) ran kept (by omega) safe
        (by
          intro value returned
          subst returned
          exact resume value post ran (by omega))
      unfold RunBounded
      simpa only [Nat.add_assoc] using whole

theorem handledCall {F : Type} (s : PanSemStateFiniteExact 64 F)
    (function handlerId handlerVar : MlS) (destination : Option (VarKind × MlS))
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body handler : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (bodyCost handlerCost : Nat)
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body,callee,returnShape))
    (code : s.code = originalRuntimeCode) (budget : bodyCost + 1 + handlerCost ≤ s.clock)
    (bounded : RunBounded (callEntryStateHOLFinite s callee) body bodyCost)
    (handlerBounded : ProgBounded handler handlerCost) :
    RunBounded s (.call (some (destination,some (handlerId,handlerVar,handler))) function arguments)
      (bodyCost + 1 + handlerCost) := by
  have metadata := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
  cases run : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
  | mk result post =>
    unfold RunBounded at bounded
    rw [run] at bounded metadata
    have spent : s.clock ≤ post.clock + (bodyCost + 1) := by
      have h := bounded.1
      change s.clock - 1 ≤ post.clock + bodyCost at h
      omega
    have remaining : post.clock ≤ s.clock := by
      have h := bounded.2.1
      change post.clock ≤ s.clock - 1 at h
      omega
    exact evaluate_handled_call_bounded s post function handlerId handlerVar destination arguments values body handler callee
      returnShape result (bodyCost + 1) handlerCost args lookup (by omega) run spent remaining bounded.2.2 (by
        intro value _
        apply handlerBounded
        · exact metadata.1.trans code
        · change handlerCost ≤ post.clock
          omega)

end RunBounded

def avoidsLocal (key : MlS) : ProgHOL 64 → Bool
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .store _ _ | .storeByte _ _ | .store32 _ _ | .extCall _ _ _ _ _ => true
  | .assign .global _ _ => true
  | .assign .local name _ => !(name == key)
  | .primitive name _ _ => !(name == key)
  | .seq first second => avoidsLocal key first && avoidsLocal key second
  | .ite _ yes no => avoidsLocal key yes && avoidsLocal key no
  | .dec name _ _ body => (name == key) || avoidsLocal key body
  | .while _ body => avoidsLocal key body
  | .call none _ _ => true
  | .call (some (none,none)) _ _ => true
  | .call (some (some (.global,_),none)) _ _ => true
  | .call (some (some (.local,name),none)) _ _ => !(name == key)
  | .decCall name _ _ _ continuation => (name == key) || avoidsLocal key continuation
  | _ => false

theorem resVarEq_lookup {width : Nat} [NeZero width] (map : HolFiniteMapExact MlS (ValueHOL width))
    (name key : MlS) (saved : Option (ValueHOL width)) :
    (HolFiniteMapExact.resVarEq map (name,saved)).lookup key = if key = name then saved else map.lookup key := by
  cases saved <;> by_cases h : key = name <;>
    simp [FDOMSUB_HOL,FUPDATE_HOL,h]

def Flowing (result : Option (PanSemResultExact 64)) : Prop :=
  result = none ∨ result = some .break ∨ result = some .continue

theorem dec_flowing {F : Type} {s post : PanSemStateFiniteExact 64 F} {name : MlS} {shape : ShapeHOL}
    {initializer : ExpHOL 64} {body : ProgHOL 64} {r : Option (PanSemResultExact 64)} (flow : Flowing r)
    (run : evaluateHOLFiniteState s (.dec name shape initializer body) = (r,post)) :
    ∃ value inner, evaluateHOLFiniteState (setVarHOLFinite name value s) body = (r,inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (name,s.locals.lookup name) := by
  rw [evaluateHOLFiniteState_dec_total] at run
  dsimp only at run
  split at run
  · simp at run; obtain ⟨rfl,_⟩ := run; rcases flow with h|h|h <;> simp at h
  · rename_i value _
    split at run
    · cases h : evaluateHOLFiniteState (setVarHOLFinite name value s) body with
      | mk r' inner =>
        rw [h] at run
        simp only [Prod.mk.injEq] at run
        obtain ⟨e,p⟩ := run
        subst e
        exact ⟨value,inner,h,by rw [← p]⟩
    · simp at run; obtain ⟨rfl,_⟩ := run; rcases flow with h|h|h <;> simp at h

theorem while_flowing {F : Type} {s post : PanSemStateFiniteExact 64 F} {condition : ExpHOL 64} {body : ProgHOL 64}
    {r : Option (PanSemResultExact 64)} (flow : Flowing r)
    (run : evaluateHOLFiniteState s (.while condition body) = (r,post)) :
    post = s ∨ ∃ mid r1, evaluateHOLFiniteState (decClockHOLFinite s) body = (r1,mid) ∧ Flowing r1 ∧
      mid.clock < s.clock ∧ ((r1 = some .break ∧ post = mid) ∨
        ((r1 = none ∨ r1 = some .continue) ∧ evaluateHOLFiniteState mid (.while condition body) = (r,post))) := by
  rw [evaluateHOLFiniteState_while_total] at run
  split at run
  · split at run
    · split at run
      · simp at run; obtain ⟨rfl,_⟩ := run; rcases flow with h|h|h <;> simp at h
      · rename_i nonzero
        dsimp only at run
        rw [fixClockHOLFinite_evaluateState] at run
        have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite s) body with
        | mk r1 mid =>
          rw [bodyRun] at run remaining
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at remaining
            omega
          right
          cases r1 with
          | none => exact ⟨mid,none,rfl,Or.inl rfl,smaller,Or.inr ⟨Or.inl rfl,run⟩⟩
          | some r1 =>
            cases r1 with
            | «continue» => exact ⟨mid,some .continue,rfl,Or.inr (Or.inr rfl),smaller,Or.inr ⟨Or.inr rfl,run⟩⟩
            | «break» =>
              simp at run; obtain ⟨rfl,rfl⟩ := run
              exact ⟨mid,some .break,rfl,Or.inr (Or.inl rfl),smaller,Or.inl ⟨rfl,rfl⟩⟩
            | _ => simp at run; obtain ⟨rfl,_⟩ := run; rcases flow with h|h|h <;> simp at h
    · simp at run; exact Or.inl run.2.symm
  · simp at run; obtain ⟨rfl,_⟩ := run; rcases flow with h|h|h <;> simp at h

theorem decCall_flowing {F : Type} {s post : PanSemStateFiniteExact 64 F} {name function : MlS}
    {shape : ShapeHOL} {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64}
    {r : Option (PanSemResultExact 64)} (flow : Flowing r)
    (run : evaluateHOLFiniteState s (.decCall name shape function arguments continuation) = (r,post)) :
    ∃ (_w : ValueHOL 64) (resumed inner : PanSemStateFiniteExact 64 F),
      (∀ k, k ≠ name → resumed.locals.lookup k = s.locals.lookup k) ∧ resumed.clock < s.clock ∧
      evaluateHOLFiniteState resumed continuation = (r,inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (name,s.locals.lookup name) := by
  rw [evaluateHOLFiniteState_decCall_total] at run
  unfold Flowing at flow
  cases args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with
  | none => rw [args] at run; simp at run; obtain ⟨rfl,_⟩ := run; simp at flow
  | some values =>
    rw [args] at run
    dsimp only at run
    cases lookup : lookupCodeHOLFinite s.code.lookup function values with
    | none => rw [lookup] at run; simp at run; obtain ⟨rfl,_⟩ := run; simp at flow
    | some installed =>
      obtain ⟨body,callee,returnShape⟩ := installed
      rw [lookup] at run
      dsimp only at run
      split at run
      · simp at run; obtain ⟨rfl,_⟩ := run; simp at flow
      · rename_i nonzero
        have remaining := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r1 bodyPost =>
          rw [bodyRun] at run remaining
          dsimp only [fixClockHOLFinite] at run
          rcases r1 with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first
            | (simp at run; obtain ⟨rfl,_⟩ := run; simp at flow)
            | skip
          simp only [] at run
          split at run
          · obtain ⟨e,p⟩ := Prod.mk.inj run
            refine ⟨w,_,_,?rl,?ck,Prod.ext e rfl,by rw [← p]⟩
            case rl =>
              intro k different
              simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
            case ck =>
              change (if _ then _ else _) < s.clock
              change bodyPost.clock ≤ s.clock - 1 at remaining
              split <;> omega
          · simp at run; obtain ⟨rfl,_⟩ := run; simp at flow

set_option maxHeartbeats 800000 in
theorem evaluate_avoidsLocal_flowing {F : Type} (key : MlS) (program : ProgHOL 64)
    (supported : avoidsLocal key program = true) (state : PanSemStateFiniteExact 64 F)
    (flow : Flowing (evaluateHOLFiniteState state program).1) :
    (evaluateHOLFiniteState state program).2.locals.lookup key = state.locals.lookup key := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]
  | «break» => rw [evaluateHOLFiniteState_break]
  | «continue» => rw [evaluateHOLFiniteState_continue]
  | annot tag text => rw [evaluateHOLFiniteState_annot]
  | raise name value =>
    rw [shape,evaluateHOLFiniteState_raise] at flow
    unfold Flowing at flow
    split at flow
    · dsimp only at flow; split at flow <;> simp at flow
    · simp at flow
  | «return» value =>
    rw [shape,evaluateHOLFiniteState_return] at flow
    unfold Flowing at flow
    split at flow
    · simp at flow
    · split at flow <;> simp at flow
  | store destination value => rw [(evaluate_store_control_frame state destination value).2.1]
  | storeByte destination value => rw [(evaluate_storeByte_control_frame state destination value).2.2.1]
  | store32 address value =>
    rw [evaluateHOLFiniteState_store32]
    split <;> repeat' first | split | rfl
  | extCall function a b c d =>
    rw [shape,evaluateHOLFiniteState_extCall_source] at flow
    rw [evaluateHOLFiniteState_extCall_source]
    unfold Flowing at flow
    repeat' first | split | rfl
    all_goals simp_all [emptyLocalsHOLFinite]
  | assign kind name value =>
    rw [evaluateHOLFiniteState_assign]
    cases kind with
    | global =>
      split
      · rfl
      · split
        · simp [setKvarHOLFinite,setGlobalHOLFinite]
        · rfl
    | «local» =>
      have different : name ≠ key := by simpa [shape,avoidsLocal] using supported
      split
      · rfl
      · split
        · simp [setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different]
        · rfl
  | primitive name operator arguments =>
    have different : name ≠ key := by simpa [shape,avoidsLocal] using supported
    rw [evaluateHOLFiniteState_primitive]
    repeat' first | split | rfl
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different]
  | seq first second =>
    have children : avoidsLocal key first = true ∧ avoidsLocal key second = true := by
      simpa only [shape,avoidsLocal,Bool.and_eq_true] using supported
    rw [shape,evaluateHOLFiniteState_seq_line780] at flow
    rw [evaluateHOLFiniteState_seq_line780]
    have remaining := evaluateHOLFiniteState_clock_le state first
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at flow remaining
      have one := evaluate_avoidsLocal_flowing key first children.1 state
      rw [firstRun] at one
      cases result with
      | none => exact (evaluate_avoidsLocal_flowing key second children.2 middle flow).trans (one (Or.inl rfl))
      | some r => exact one flow
  | ite condition yes no =>
    have children : avoidsLocal key yes = true ∧ avoidsLocal key no = true := by
      simpa only [shape,avoidsLocal,Bool.and_eq_true] using supported
    rw [shape,evaluateHOLFiniteState_ite] at flow
    rw [evaluateHOLFiniteState_ite]
    split
    · rename_i flag hflag
      rw [hflag] at flow
      dsimp only at flow ⊢
      split
      · rw [if_pos (by assumption)] at flow
        exact evaluate_avoidsLocal_flowing key no children.2 state flow
      · rw [if_neg (by assumption)] at flow
        exact evaluate_avoidsLocal_flowing key yes children.1 state flow
    · rfl
  | dec name kind initializer body =>
    cases run : evaluateHOLFiniteState state (.dec name kind initializer body) with
    | mk result post =>
      rw [shape,run] at flow
      dsimp only at flow
      obtain ⟨value,inner,bodyRun,locals⟩ := dec_flowing flow run
      change post.locals.lookup key = _
      rw [locals,resVarEq_lookup]
      by_cases same : key = name
      · rw [if_pos same,same]
      · rw [if_neg same]
        have child : avoidsLocal key body = true := by
          have := supported; simp [shape,avoidsLocal] at this
          rcases this with h | h
          · exact absurd h.symm same
          · exact h
        have inner' := evaluate_avoidsLocal_flowing key body child (setVarHOLFinite name value state) (by rw [bodyRun]; exact flow)
        rw [bodyRun] at inner'
        rw [inner']
        simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm same]
  | «while» condition body =>
    have child : avoidsLocal key body = true := by simpa only [shape,avoidsLocal] using supported
    cases run : evaluateHOLFiniteState state (.while condition body) with
    | mk result post =>
      rw [shape,run] at flow
      dsimp only at flow
      change post.locals.lookup key = _
      rcases while_flowing flow run with rfl | ⟨mid,r1,bodyRun,bodyFlow,smaller,exit⟩
      · rfl
      · have one := evaluate_avoidsLocal_flowing key body child (decClockHOLFinite state) (by rw [bodyRun]; exact bodyFlow)
        rw [bodyRun] at one
        change mid.locals.lookup key = state.locals.lookup key at one
        rcases exit with ⟨_,rfl⟩ | ⟨_,loop⟩
        · exact one
        · have two := evaluate_avoidsLocal_flowing key (.while condition body) (by simpa [avoidsLocal] using child) mid
            (by rw [loop]; exact flow)
          rw [loop] at two
          exact two.trans one
  | call info function arguments =>
    have dest : info = none ∨ info = some (none,none) ∨ (∃ g, info = some (some (.global,g),none)) ∨
        (∃ n, n ≠ key ∧ info = some (some (.local,n),none)) := by
      rcases info with _ | ⟨_ | ⟨kind,n⟩,_ | h⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · simp [shape,avoidsLocal] at supported
      · cases kind
        · simp [shape,avoidsLocal] at supported
          exact Or.inr (Or.inr (Or.inr ⟨n,supported,rfl⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨n,rfl⟩))
      · cases kind <;> simp [shape,avoidsLocal] at supported
    rw [shape,evaluateHOLFiniteState_call] at flow
    rw [evaluateHOLFiniteState_call]
    unfold Flowing at flow
    rcases dest with rfl | rfl | ⟨g,rfl⟩ | ⟨n,different,rfl⟩
    all_goals dsimp only at flow ⊢
    all_goals
      repeat' first | split | rfl
    all_goals simp_all [setKvarHOLFinite,setVarHOLFinite,setGlobalHOLFinite,emptyLocalsHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE]
  | decCall name shape' function arguments continuation =>
    cases run : evaluateHOLFiniteState state (.decCall name shape' function arguments continuation) with
    | mk result post =>
      rw [shape,run] at flow
      dsimp only at flow
      change post.locals.lookup key = _
      obtain ⟨_w,resumed,inner,rl,smaller,contRun,locals⟩ := decCall_flowing flow run
      rw [locals,resVarEq_lookup]
      by_cases same : key = name
      · rw [if_pos same,same]
      · rw [if_neg same]
        have child : avoidsLocal key continuation = true := by
          have := supported; simp [shape,avoidsLocal] at this
          rcases this with h | h
          · exact absurd h.symm same
          · exact h
        have inner' := evaluate_avoidsLocal_flowing key continuation child resumed (by rw [contRun]; exact flow)
        rw [contRun] at inner'
        rw [inner',rl key same]
  | _ => simp [shape,avoidsLocal] at supported
termination_by (state.clock,sizeOf program)
decreasing_by all_goals (simp_all [decClockHOLFinite,setVarHOLFinite]; omega)

def noTopContinue : ProgHOL 64 → Bool
  | .continue => false
  | .seq first second => noTopContinue first && noTopContinue second
  | .ite _ yes no => noTopContinue yes && noTopContinue no
  | .dec _ _ _ body => noTopContinue body
  | .decCall _ _ _ _ continuation => noTopContinue continuation
  | .skip | .assign _ _ _ | .primitive _ _ _ | .store _ _ | .storeByte _ _ | .store32 _ _ | .break | .raise _ _ | .return _
  | .extCall _ _ _ _ _ | .shMemLoad _ _ _ _ | .shMemStore _ _ _ | .annot _ _ | .while _ _ => true
  | .call none _ _ | .call (some (_,none)) _ _ => true
  | _ => false

theorem evaluate_noTopContinue {F : Type} (program : ProgHOL 64) (supported : noTopContinue program = true)
    (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state program).1 ≠ some .continue := by
  cases shape : program with
  | «continue» => simp [shape,noTopContinue] at supported
  | seq first second =>
    have children : noTopContinue first = true ∧ noTopContinue second = true := by
      simpa only [shape,noTopContinue,Bool.and_eq_true] using supported
    have remaining := evaluateHOLFiniteState_clock_le state first
    rw [evaluateHOLFiniteState_seq_line780]
    have one := evaluate_noTopContinue first children.1 state
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at one remaining
      cases result with
      | none => exact evaluate_noTopContinue second children.2 middle
      | some r => exact one
  | ite condition yes no =>
    have children : noTopContinue yes = true ∧ noTopContinue no = true := by
      simpa only [shape,noTopContinue,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noTopContinue no children.2 state
      · exact evaluate_noTopContinue yes children.1 state
    · simp
  | dec name kind initializer body =>
    have child : noTopContinue body = true := by simpa only [shape,noTopContinue] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_noTopContinue body child _
      · simp
  | decCall name shape' function arguments continuation =>
    have child : noTopContinue continuation = true := by simpa only [shape,noTopContinue] using supported
    intro hcont
    cases run : evaluateHOLFiniteState state (.decCall name shape' function arguments continuation) with
    | mk result post =>
      rw [run] at hcont
      dsimp only at hcont
      subst hcont
      obtain ⟨_w,resumed,inner,_,smaller,contRun,_⟩ := decCall_flowing (Or.inr (Or.inr rfl)) run
      have := evaluate_noTopContinue continuation child resumed
      rw [contRun] at this
      exact this rfl
  | skip => simp [evaluateHOLFiniteState_skip]
  | «break» => simp [evaluateHOLFiniteState_break]
  | annot tag text => simp [evaluateHOLFiniteState_annot]
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]; split
    · dsimp only; split <;> simp
    · simp
  | «return» value =>
    rw [evaluateHOLFiniteState_return]; split
    · simp
    · split <;> simp
  | store destination value => rcases (evaluate_store_control_frame state destination value).1 with h | h <;> rw [h] <;> simp
  | storeByte destination value => rcases (evaluate_storeByte_control_frame state destination value).1 with h | h <;> rw [h] <;> simp
  | store32 address value =>
    rw [evaluateHOLFiniteState_store32]
    repeat' first | split | simp
  | shMemLoad operator kind name address =>
    rw [evaluateHOLFiniteState_shMemLoad_source]
    split
    · split
      · dsimp only
        unfold shMemLoadHOLFiniteExact
        repeat' first | split | simp
      · simp
    · simp
  | shMemStore operator address value =>
    classical
    rw [evaluateHOLFiniteState_shMemStore_total]
    dsimp only
    split
    · unfold shMemStoreHOLExact
      repeat' first | split | simp
    · simp
  | assign kind name value =>
    rw [evaluateHOLFiniteState_assign]; split
    · simp
    · split <;> simp
  | primitive name operator arguments =>
    rw [evaluateHOLFiniteState_primitive]
    repeat' first | split | simp
  | extCall function a b c d =>
    rw [evaluateHOLFiniteState_extCall_source]
    repeat' first | split | simp
  | call info function arguments =>
    have handlerFree : info = none ∨ ∃ d, info = some (d,none) := by
      rcases info with _ | ⟨d,_ | h⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨d,rfl⟩
      · simp [shape,noTopContinue] at supported
    rw [evaluateHOLFiniteState_call]
    rcases handlerFree with rfl | ⟨d,rfl⟩
    all_goals dsimp only
    all_goals repeat' first | split | simp | simp_all
  | «while» condition body =>
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at remaining
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining
              omega
            cases result with
            | none => exact evaluate_noTopContinue (.while condition body) (by simp [noTopContinue]) middle
            | some result =>
              cases result with
              | «continue» => exact evaluate_noTopContinue (.while condition body) (by simp [noTopContinue]) middle
              | _ => simp
      · simp
    · simp
  | _ => simp [shape,noTopContinue] at supported
termination_by (state.clock,sizeOf program)
decreasing_by all_goals (simp_all [decClockHOLFinite,setVarHOLFinite]; omega)

def RankedOutcome {F : Type} (state : PanSemStateFiniteExact 64 F) (condition : ExpHOL 64) (budget : Nat)
    (Rank : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat → Prop) (Broke : Prop)
    (r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F) : Prop :=
  state.clock ≤ r.2.clock + budget ∧ r.2.clock ≤ state.clock ∧ r.1 ≠ some .timeOut ∧
    (r.1 = none → ∃ m, Rank r.2 m ∧ r.2.code = state.code ∧
      (evalHOLFinite r.2 (h := fun a => Classical.propDecidable (r.2.memaddrs a)) condition = some (.val (.word 0)) ∨ Broke))

theorem rankedWhile_run (condition : ExpHOL 64) (body : ProgHOL 64) (cost : Nat)
    (Rank : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat → Prop) (Broke : Prop)
    (exit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), Rank s 0 → ∀ w : BitVec 64,
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condition = some (.val (.word w)) → w = 0)
    (step : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) (w : BitVec 64), s.code = originalRuntimeCode →
      Rank s (n + 1) →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condition = some (.val (.word w)) →
      w ≠ 0 → cost + 1 ≤ s.clock →
      s.clock - 1 ≤ (evaluateHOLFiniteState (decClockHOLFinite s) body).2.clock + cost ∧
        (evaluateHOLFiniteState (decClockHOLFinite s) body).2.clock ≤ s.clock - 1 ∧
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 ≠ some .timeOut ∧
        ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
            (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue →
          ∃ m, m ≤ n ∧ Rank (evaluateHOLFiniteState (decClockHOLFinite s) body).2 m ∧
            (evaluateHOLFiniteState (decClockHOLFinite s) body).2.code = s.code) ∧
        ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .break → Broke ∧
          ∃ m, Rank (evaluateHOLFiniteState (decClockHOLFinite s) body).2 m ∧
            (evaluateHOLFiniteState (decClockHOLFinite s) body).2.code = s.code)) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      Rank state n → n * (cost + 1) ≤ state.clock →
      RankedOutcome state condition (n * (cost + 1)) Rank Broke (evaluateHOLFiniteState state (.while condition body)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code ranked budget
    rw [evaluateHOLFiniteState_while_total]
    split
    · rename_i w hw
      by_cases zero : w = 0
      · subst zero
        simp only [ne_eq,not_true_eq_false,if_false]
        exact ⟨Nat.le_add_right _ _,le_refl _,by simp,fun _ => ⟨n,ranked,rfl,Or.inl hw⟩⟩
      · rw [if_pos zero]
        cases n with
        | zero => exact absurd (exit state ranked w hw) zero
        | succ k =>
          have oneIteration : cost + 1 ≤ (k + 1) * (cost + 1) := Nat.le_mul_of_pos_left _ (by omega)
          have clock : state.clock ≠ 0 := by omega
          rw [if_neg clock]
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have stepRun := step state k w code ranked hw zero (by omega)
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at stepRun
            dsimp only at stepRun
            obtain ⟨spent,kept,safe,advance,broken⟩ := stepRun
            have again : ∀ m, m ≤ k → Rank middle m → middle.code = state.code →
                RankedOutcome state condition ((k + 1) * (cost + 1)) Rank Broke
                  (evaluateHOLFiniteState middle (.while condition body)) := by
              intro m small rankedNext nextCode
              have mono : m * (cost + 1) ≤ k * (cost + 1) := Nat.mul_le_mul_right _ small
              have expand : (k + 1) * (cost + 1) = k * (cost + 1) + (cost + 1) := Nat.succ_mul _ _
              obtain ⟨t1,t2,t3,t4⟩ := ih m (by omega) middle (nextCode.trans code) rankedNext (by omega)
              refine ⟨by omega,by omega,t3,fun normal => ?_⟩
              obtain ⟨m',r',c',e'⟩ := t4 normal
              exact ⟨m',r',c'.trans nextCode,e'⟩
            cases result with
            | none =>
              obtain ⟨m,small,rankedNext,nextCode⟩ := advance (Or.inl rfl)
              exact again m small rankedNext nextCode
            | some r =>
              cases r with
              | «continue» =>
                obtain ⟨m,small,rankedNext,nextCode⟩ := advance (Or.inr rfl)
                exact again m small rankedNext nextCode
              | «break» =>
                obtain ⟨flag,m,rankedNext,nextCode⟩ := broken rfl
                exact ⟨by simp; omega,by simp; omega,by simp,fun _ => ⟨m,rankedNext,nextCode,Or.inr flag⟩⟩
              | timeOut => exact absurd rfl safe
              | _ => exact ⟨by simp; omega,by simp; omega,by simp,by simp⟩
    · exact ⟨Nat.le_add_right _ _,le_refl _,by simp,by simp⟩

inductive CountedBody (counter : MlS) (step : BitVec 64) : ProgHOL 64 → Nat → Prop
  | incr : CountedBody counter step (.assign .local counter (.op .add [.var .local counter,.const step])) 0
  | seq (first : ProgHOL 64) {tail : ProgHOL 64} {a b : Nat} (bounded : ProgBounded first a)
      (avoid : avoidsLocal counter first = true) (noCont : noTopContinue first = true)
      (rest : CountedBody counter step tail b) : CountedBody counter step (.seq first tail) (a + b)
  | dec (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) {body : ProgHOL 64} {cost : Nat}
      (distinct : counter ≠ name) (rest : CountedBody counter step body cost) :
      CountedBody counter step (.dec name shape initializer body) cost

theorem CountedBody.run {counter : MlS} {step : BitVec 64} {body : ProgHOL 64} {cost : Nat}
    (counted : CountedBody counter step body cost) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (w : BitVec 64)
    (atCounter : state.locals.lookup counter = some (.val (.word w))) (budget : cost ≤ state.clock) :
    state.clock ≤ (evaluateHOLFiniteState state body).2.clock + cost ∧
      (evaluateHOLFiniteState state body).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state body).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState state body).1 ≠ some .continue ∧
      ((evaluateHOLFiniteState state body).1 = none →
        (evaluateHOLFiniteState state body).2.locals.lookup counter = some (.val (.word (w + step))) ∧
        (evaluateHOLFiniteState state body).2.code = state.code) := by
  induction counted generalizing state with
  | incr =>
    have run : evaluateHOLFiniteState state (.assign .local counter (.op .add [.var .local counter,.const step])) =
        (none,setVarHOLFinite counter (.val (.word (w + step))) state) := by
      simp [evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,atCounter,wordOpHOL,wordOp,valueIsWord,
        valueWord,lookupKvarHOLExact,isValidValueHOLExact,setKvarHOLFinite,shapeOfHOLExact,shapeEqHOL]
    rw [run]
    refine ⟨by simp [setVarHOLFinite],by simp [setVarHOLFinite],by simp,by simp,fun _ => ⟨?_,rfl⟩⟩
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  | seq first bounded avoid noCont rest ih =>
    rename_i tail a b
    have firstBound := bounded state code (by omega)
    have frame := evaluate_avoidsLocal_flowing counter first avoid state
    have noContinue := evaluate_noTopContinue first noCont state
    have meta' := evaluateHOLFiniteState_metadata state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at firstBound frame noContinue meta'
      dsimp only at firstBound frame noContinue meta'
      obtain ⟨spent,kept,safe⟩ := firstBound
      cases result with
      | none =>
        dsimp only
        have kept' := frame (Or.inl rfl)
        obtain ⟨t1,t2,t3,t4,t5⟩ := ih middle (meta'.1.trans code) (by rw [kept']; exact atCounter) (by omega)
        refine ⟨by omega,by omega,t3,t4,fun normal => ?_⟩
        obtain ⟨i1,i2⟩ := t5 normal
        exact ⟨i1,i2.trans meta'.1⟩
      | some r =>
        dsimp only
        refine ⟨by omega,by omega,safe,noContinue,fun h => by simp at h⟩
  | dec name shape initializer distinct rest ih =>
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact ⟨Nat.le_add_right _ _,le_refl _,by simp,by simp,by simp⟩
    · rename_i val _
      split
      · let inner := setVarHOLFinite name val state
        have atInner : inner.locals.lookup counter = some (.val (.word w)) := by
          simp [inner,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm distinct,atCounter]
        obtain ⟨t1,t2,t3,t4,t5⟩ := ih inner code atInner budget
        cases run : evaluateHOLFiniteState inner _ with
        | mk res post =>
          rw [run] at t1 t2 t3 t4 t5
          dsimp only at t1 t2 t3 t4 t5 ⊢
          refine ⟨t1,t2,t3,t4,fun normal => ?_⟩
          obtain ⟨i1,i2⟩ := t5 normal
          refine ⟨?_,i2⟩
          rw [resVarEq_lookup,if_neg distinct]
          exact i1
      · exact ⟨Nat.le_add_right _ _,le_refl _,by simp,by simp,by simp⟩

theorem holAsmSignedLess_small (a b : BitVec 64) (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63) :
    Compiler.Encoders.Asm.holAsmSignedLess a b = decide (a.toNat < b.toNat) := by
  have ha' : a.toNat < 9223372036854775808 := ha
  have hb' : b.toNat < 9223372036854775808 := hb
  unfold Compiler.Encoders.Asm.holAsmSignedLess
  simp [ha',hb']

theorem eval_counted_condition {F : Type} (state : PanSemStateFiniteExact 64 F) (counter : MlS) (op : Cmp)
    (hop : op = .less ∨ op = .lower) (K w : BitVec 64) (hK : K.toNat < 2 ^ 63) (hw : w.toNat < 2 ^ 63)
    (atCounter : state.locals.lookup counter = some (.val (.word w))) :
    evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp op (.var .local counter) (.const K)) =
      some (.val (.word (if w.toNat < K.toNat then 1 else 0))) := by
  rw [evalHOLFinite_eq_toExact]
  rcases hop with rfl | rfl
  · simp only [evalHOLExact,atCounter]
    simp only [Compiler.Encoders.Asm.wordCmpHOL,holAsmSignedLess_small w K hw hK]
    by_cases lt : w.toNat < K.toNat <;> simp [lt]
  · simp only [evalHOLExact,atCounter]
    simp only [Compiler.Encoders.Asm.wordCmpHOL]
    by_cases lt : w.toNat < K.toNat
    · simp [lt,BitVec.lt_def]
    · simp [lt,BitVec.lt_def]

theorem countedWhile_run (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower) (K step : BitVec 64)
    (small : K.toNat + step.toNat < 2 ^ 63) (positive : 0 < step.toNat) {body : ProgHOL 64} {cost : Nat}
    (counted : CountedBody counter step body cost) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) → w.toNat ≤ K.toNat + step.toNat →
      K.toNat - w.toNat = n → n * (cost + 1) ≤ state.clock →
      state.clock ≤ (evaluateHOLFiniteState state (.while (.cmp op (.var .local counter) (.const K)) body)).2.clock + n * (cost + 1) ∧
        (evaluateHOLFiniteState state (.while (.cmp op (.var .local counter) (.const K)) body)).2.clock ≤ state.clock ∧
        (evaluateHOLFiniteState state (.while (.cmp op (.var .local counter) (.const K)) body)).1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code w atCounter within distance budget
    have condition := eval_counted_condition state counter op hop K w (by omega) (by omega) atCounter
    rw [evaluateHOLFiniteState_while_total,condition]
    by_cases lt : w.toNat < K.toNat
    · rw [if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide,if_true,ne_eq,not_false_eq_true]
      have positiveRank : 0 < n := by omega
      have clock : state.clock ≠ 0 := by
        have : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
        omega
      rw [if_neg clock]
      rw [fixClockHOLFinite_evaluateState]
      have stepRun := counted.run (decClockHOLFinite state) code w atCounter (by
        change cost ≤ state.clock - 1
        have : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
        omega)
      have meta' := evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
      cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
      | mk result middle =>
        rw [bodyRun] at stepRun meta'
        dsimp only at stepRun meta'
        obtain ⟨spent,kept,safe,noCont,advance⟩ := stepRun
        change state.clock - 1 ≤ middle.clock + cost at spent
        change middle.clock ≤ state.clock - 1 at kept
        have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
        cases result with
        | none =>
          dsimp only
          obtain ⟨nextCounter,nextCode⟩ := advance rfl
          have natural : (w + step).toNat = w.toNat + step.toNat := by
            rw [BitVec.toNat_add_of_lt (by omega)]
          have nextRank : K.toNat - (w + step).toNat < n := by rw [natural]; omega
          have tail := ih (K.toNat - (w + step).toNat) nextRank middle (nextCode.trans code) (w + step) nextCounter
            (by rw [natural]; omega) rfl (by
              have : (K.toNat - (w + step).toNat) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
                rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
              omega)
          obtain ⟨t1,t2,t3⟩ := tail
          refine ⟨?_,by omega,t3⟩
          have : (K.toNat - (w + step).toNat) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
          omega
        | some r =>
          cases r with
          | «continue» => exact absurd rfl noCont
          | «break» => exact ⟨by simp; omega,by simp; omega,by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega,by simp; omega,by simp⟩
    · rw [if_neg lt]
      simp

theorem countedWhile_from {F : Type} (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower) (K step : BitVec 64)
    (small : K.toNat + step.toNat < 2 ^ 63) (positive : 0 < step.toNat) {body : ProgHOL 64} {cost : Nat}
    (counted : CountedBody counter step body cost) (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (w : BitVec 64)
    (atCounter : state.locals.lookup counter = some (.val (.word w))) (within : w.toNat ≤ K.toNat)
    (budget : K.toNat * (cost + 1) ≤ state.clock) :
    state.clock ≤ (evaluateHOLFiniteState state (.while (.cmp op (.var .local counter) (.const K)) body)).2.clock + K.toNat * (cost + 1) ∧
      (evaluateHOLFiniteState state (.while (.cmp op (.var .local counter) (.const K)) body)).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state (.while (.cmp op (.var .local counter) (.const K)) body)).1 ≠ some .timeOut := by
  have mono : (K.toNat - w.toNat) * (cost + 1) ≤ K.toNat * (cost + 1) := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨a,b,c⟩ := countedWhile_run counter op hop K step small positive counted (K.toNat - w.toNat) state code w
    atCounter (by omega) rfl (by omega)
  exact ⟨by omega,b,c⟩

theorem ProgBounded.countedDec (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower) (K step start : BitVec 64)
    (small : K.toNat + step.toNat < 2 ^ 63) (positive : 0 < step.toNat) (begin : start.toNat ≤ K.toNat)
    {body tail : ProgHOL 64} {cost tailCost : Nat} (counted : CountedBody counter step body cost)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const start) (.seq (.while (.cmp op (.var .local counter) (.const K)) body) tail))
      (K.toNat * (cost + 1) + tailCost) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  let entered := setVarHOLFinite counter (.val (.word start)) state
  have atCounter : entered.locals.lookup counter = some (.val (.word start)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have loop := countedWhile_from counter op hop K step small positive counted entered code start atCounter begin
    (by change K.toNat * (cost + 1) ≤ state.clock; omega)
  have meta' := evaluateHOLFiniteState_metadata entered (.while (.cmp op (.var .local counter) (.const K)) body)
  change state.clock ≤ (evaluateHOLFiniteState entered _).2.clock + _ ∧
    (evaluateHOLFiniteState entered _).2.clock ≤ state.clock ∧ (evaluateHOLFiniteState entered _).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780]
  cases loopRun : evaluateHOLFiniteState entered (.while (.cmp op (.var .local counter) (.const K)) body) with
  | mk result middle =>
    rw [loopRun] at loop meta'
    dsimp only at loop meta'
    obtain ⟨spent,kept,safe⟩ := loop
    change state.clock ≤ middle.clock + K.toNat * (cost + 1) at spent
    change middle.clock ≤ state.clock at kept
    cases result with
    | none =>
      dsimp only
      obtain ⟨t1,t2,t3⟩ := rest middle (meta'.1.trans code) (by omega)
      exact ⟨by omega,by omega,t3⟩
    | some r =>
      dsimp only
      exact ⟨by omega,kept,safe⟩

theorem ProgBounded.countedAssign (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower) (K step start : BitVec 64)
    (small : K.toNat + step.toNat < 2 ^ 63) (positive : 0 < step.toNat) (begin : start.toNat ≤ K.toNat)
    {body tail : ProgHOL 64} {cost tailCost : Nat} (counted : CountedBody counter step body cost)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.seq (.assign .local counter (.const start)) (.seq (.while (.cmp op (.var .local counter) (.const K)) body) tail))
      (K.toNat * (cost + 1) + tailCost) := by
  intro F state code budget
  by_cases valid : isValidValueHOLExact state.toExact .local counter (.val (.word start)) = true
  · have assignRun : evaluateHOLFiniteState state (.assign .local counter (.const start)) =
        (none,setKvarHOLFinite .local counter (.val (.word start)) state) := by
      simp [evaluateHOLFiniteState_assign,evalHOLExact,valid]
    rw [evaluateHOLFiniteState_seq_line780,assignRun]
    dsimp only
    let entered := setKvarHOLFinite .local counter (.val (.word start)) state
    have atCounter : entered.locals.lookup counter = some (.val (.word start)) := by
      simp [entered,setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have enteredCode : entered.code = originalRuntimeCode := code
    have loop := countedWhile_from counter op hop K step small positive counted entered enteredCode start atCounter begin
      (by change K.toNat * (cost + 1) ≤ state.clock; omega)
    have meta' := evaluateHOLFiniteState_metadata entered (.while (.cmp op (.var .local counter) (.const K)) body)
    change state.clock ≤ (evaluateHOLFiniteState entered _).2.clock + _ ∧
      (evaluateHOLFiniteState entered _).2.clock ≤ state.clock ∧ (evaluateHOLFiniteState entered _).1 ≠ some .timeOut
    rw [evaluateHOLFiniteState_seq_line780]
    cases loopRun : evaluateHOLFiniteState entered (.while (.cmp op (.var .local counter) (.const K)) body) with
    | mk result middle =>
      rw [loopRun] at loop meta'
      dsimp only at loop meta'
      obtain ⟨spent,kept,safe⟩ := loop
      change state.clock ≤ middle.clock + K.toNat * (cost + 1) at spent
      change middle.clock ≤ state.clock at kept
      cases result with
      | none =>
        dsimp only
        obtain ⟨t1,t2,t3⟩ := rest middle (meta'.1.trans code) (by omega)
        exact ⟨by omega,by omega,t3⟩
      | some r =>
        dsimp only
        exact ⟨by omega,kept,safe⟩
  · have assignRun : evaluateHOLFiniteState state (.assign .local counter (.const start)) = (some .error,state) := by
      simp [evaluateHOLFiniteState_assign,evalHOLExact,valid]
    rw [evaluateHOLFiniteState_seq_line780,assignRun]
    simp

theorem eval_variable_counted_condition {F : Type}
    (state : PanSemStateFiniteExact 64 F) (counter limit : MlS) (op : Cmp)
    (hop : op = .less ∨ op = .lower) (K w : BitVec 64)
    (signed : op = .less → K.toNat < 2 ^ 63) (within : w.toNat ≤ K.toNat)
    (atCounter : state.locals.lookup counter = some (.val (.word w)))
    (atLimit : state.locals.lookup limit = some (.val (.word K))) :
    evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp op (.var .local counter) (.var .local limit)) =
      some (.val (.word (if w.toNat < K.toNat then 1 else 0))) := by
  rw [evalHOLFinite_eq_toExact]
  rcases hop with rfl | rfl
  · have small := signed rfl
    simp only [evalHOLExact,atCounter,atLimit]
    simp only [Compiler.Encoders.Asm.wordCmpHOL,
      holAsmSignedLess_small w K (by omega) small]
    by_cases lt : w.toNat < K.toNat <;> simp [lt]
  · simp only [evalHOLExact,atCounter,atLimit]
    simp only [Compiler.Encoders.Asm.wordCmpHOL]
    by_cases lt : w.toNat < K.toNat <;> simp [lt,BitVec.lt_def]

theorem variableCountedWhile_run (counter limit : MlS) (op : Cmp)
    (hop : op = .less ∨ op = .lower) (K : BitVec 64)
    (signed : op = .less → K.toNat < 2 ^ 63)
    {body : ProgHOL 64} {cost : Nat} (counted : CountedBody counter 1 body cost)
    (preservesLimit : avoidsLocal limit body = true) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      state.locals.lookup limit = some (.val (.word K)) → w.toNat ≤ K.toNat →
      K.toNat - w.toNat = n → n * (cost + 1) ≤ state.clock →
      let evaluated := evaluateHOLFiniteState state
        (.while (.cmp op (.var .local counter) (.var .local limit)) body)
      state.clock ≤ evaluated.2.clock + n * (cost + 1) ∧
        evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code w atCounter atLimit within distance budget
    have condition := eval_variable_counted_condition state counter limit op hop K w
      signed within atCounter atLimit
    dsimp only
    rw [evaluateHOLFiniteState_while_total,condition]
    by_cases lt : w.toNat < K.toNat
    · rw [if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide,if_true,ne_eq,not_false_eq_true]
      have positiveRank : 0 < n := by omega
      have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
      have clock : state.clock ≠ 0 := by omega
      rw [if_neg clock,fixClockHOLFinite_evaluateState]
      have stepRun := counted.run (decClockHOLFinite state) code w atCounter
        (by change cost ≤ state.clock - 1; omega)
      have frame := evaluate_avoidsLocal_flowing limit body preservesLimit (decClockHOLFinite state)
      cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
      | mk result middle =>
        rw [bodyRun] at stepRun frame
        dsimp only at stepRun frame
        obtain ⟨spent,kept,safe,noCont,advance⟩ := stepRun
        change state.clock - 1 ≤ middle.clock + cost at spent
        change middle.clock ≤ state.clock - 1 at kept
        cases result with
        | none =>
          dsimp only
          obtain ⟨nextCounter,nextCode⟩ := advance rfl
          have natural : (w + 1).toNat = w.toNat + 1 := by
            rw [BitVec.toNat_add_of_lt (by have bound := K.isLt; simp; omega)]
            rfl
          have nextRank : K.toNat - (w + 1).toNat < n := by rw [natural]; omega
          have nextLimit : middle.locals.lookup limit = some (.val (.word K)) := by
            rw [frame (Or.inl rfl)]
            exact atLimit
          have tail := ih (K.toNat - (w + 1).toNat) nextRank middle (nextCode.trans code)
            (w + 1) nextCounter nextLimit (by rw [natural]; omega) rfl (by
              have decrease : (K.toNat - (w + 1).toNat) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
                rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
              omega)
          obtain ⟨t1,t2,t3⟩ := tail
          have decrease : (K.toNat - (w + 1).toNat) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
          exact ⟨by omega,by omega,t3⟩
        | some r =>
          cases r with
          | «continue» => exact absurd rfl noCont
          | «break» => exact ⟨by simp; omega,by simp; omega,by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega,by simp; omega,by simp⟩
    · rw [if_neg lt]
      simp

theorem variableCountedWhile_zero_bounded {F : Type}
    (counter limit : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    {body : ProgHOL 64} {cost : Nat} (counted : CountedBody counter 1 body cost)
    (preservesLimit : avoidsLocal limit body = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode)
    (K : BitVec 64)
    (atCounter : state.locals.lookup counter = some (.val (.word 0)))
    (atLimit : state.locals.lookup limit = some (.val (.word K)))
    (budget : (2 ^ 64 - 1) * (cost + 1) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state
      (.while (.cmp op (.var .local counter) (.var .local limit)) body)
    state.clock ≤ evaluated.2.clock + (2 ^ 64 - 1) * (cost + 1) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  by_cases signed : op = .less → K.toNat < 2 ^ 63
  · have ceiling : K.toNat * (cost + 1) ≤ (2 ^ 64 - 1) * (cost + 1) :=
      Nat.mul_le_mul_right _ (by have bound := K.isLt; omega)
    have bounded := variableCountedWhile_run counter limit op hop K signed counted preservesLimit
      K.toNat state code 0 atCounter atLimit (by simp) (by simp) (by omega)
    dsimp only at bounded ⊢
    exact ⟨by omega,bounded.2.1,bounded.2.2⟩
  · have comparison : op = .less := by
      rcases hop with eq | eq
      · exact eq
      · exfalso
        apply signed
        intro impossible
        cases eq.symm.trans impossible
    have negative : ¬ K.toNat < 9223372036854775808 := by
      intro small
      exact signed (fun _ => small)
    subst op
    have condition : evalHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .less (.var .local counter) (.var .local limit)) = some (.val (.word 0)) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact,atCounter,atLimit,Compiler.Encoders.Asm.wordCmpHOL,
        Compiler.Encoders.Asm.holAsmSignedLess,negative]
    dsimp only
    rw [evaluateHOLFiniteState_while_total,condition]
    simp

theorem cappedCountedWhile_run (counter : MlS) (condition : ExpHOL 64) (K : BitVec 64)
    (stop : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.locals.lookup counter = some (.val (.word K)) →
      evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) condition = none ∨
      evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) condition = some (.val (.word (0#64))))
    {body : ProgHOL 64} {cost : Nat} (counted : CountedBody counter 1 body cost) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      w.toNat ≤ K.toNat → K.toNat - w.toNat = n → n * (cost + 1) ≤ state.clock →
      let evaluated := evaluateHOLFiniteState state (.while condition body)
      state.clock ≤ evaluated.2.clock + n * (cost + 1) ∧
        evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code w atCounter within distance budget
    dsimp only
    rw [evaluateHOLFiniteState_while_total]
    cases guardRun : evalHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a)) condition with
    | none => simp
    | some value =>
      cases value with
      | rStruct fields => simp
      | nStruct name fields => simp
      | val word =>
        cases word with
        | word test =>
          by_cases zero : test = 0
          · simp [zero]
          · dsimp only
            rw [if_pos zero]
            have lt : w.toNat < K.toNat := by
              by_contra notLt
              have same : w = K := BitVec.eq_of_toNat_eq (by omega)
              have ended := stop state (by simpa only [same] using atCounter)
              rcases ended with rejected | finished
              · rw [guardRun] at rejected
                cases rejected
              · rw [guardRun] at finished
                have equal : test = 0 := by cases finished; rfl
                exact zero equal
            have positiveRank : 0 < n := by omega
            have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
            have clock : state.clock ≠ 0 := by omega
            rw [if_neg clock,fixClockHOLFinite_evaluateState]
            have stepRun := counted.run (decClockHOLFinite state) code w atCounter
              (by change cost ≤ state.clock - 1; omega)
            cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
            | mk result middle =>
              rw [bodyRun] at stepRun
              dsimp only at stepRun
              obtain ⟨spent,kept,safe,noCont,advance⟩ := stepRun
              change state.clock - 1 ≤ middle.clock + cost at spent
              change middle.clock ≤ state.clock - 1 at kept
              cases result with
              | none =>
                dsimp only
                obtain ⟨nextCounter,nextCode⟩ := advance rfl
                have natural : (w + 1).toNat = w.toNat + 1 := by
                  rw [BitVec.toNat_add_of_lt (by have bound := K.isLt; simp; omega)]
                  rfl
                have nextRank : K.toNat - (w + 1).toNat < n := by rw [natural]; omega
                have decrease : (K.toNat - (w + 1).toNat) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
                  rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
                have tail := ih (K.toNat - (w + 1).toNat) nextRank middle (nextCode.trans code)
                  (w + 1) nextCounter (by rw [natural]; omega) rfl (by omega)
                obtain ⟨t1,t2,t3⟩ := tail
                exact ⟨by omega,by omega,t3⟩
              | some r =>
                cases r with
                | «continue» => exact absurd rfl noCont
                | «break» => exact ⟨by simp; omega,by simp; omega,by simp⟩
                | timeOut => exact absurd rfl safe
                | _ => exact ⟨by simp; omega,by simp; omega,by simp⟩

end InitECandidate.Solver.PanRunBounded
