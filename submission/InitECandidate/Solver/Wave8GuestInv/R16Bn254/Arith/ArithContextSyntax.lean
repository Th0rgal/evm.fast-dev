import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ArithContextControl

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestCodeLookup

def arithContextPureSyntax (allowed : MlS → Bool) : ProgHOL 64 → Bool
  | .skip | .break | .continue | .annot _ _ | .return _ | .assign .local _ _ | .store _ _ | .storeByte _ _ | .primitive _ _ _ => true
  | .dec _ _ _ body => arithContextPureSyntax allowed body
  | .seq first second | .ite _ first second => arithContextPureSyntax allowed first && arithContextPureSyntax allowed second
  | .while _ body => arithContextPureSyntax allowed body
  | .call none name _ | .call (some (none, none)) name _ | .call (some (some (.local,_), none)) name _ => allowed name
  | .decCall _ _ name _ body => allowed name && arithContextPureSyntax allowed body
  | _ => false

theorem arithContextPure_of_syntax (allowed : MlS → Bool)
    (functions : ∀ name, allowed name = true → ArithContextPureFunction name)
    (program : ProgHOL 64) (hs : arithContextPureSyntax allowed program = true) :
    ArithContextPure program := by
  cases program with
  | skip => exact ArithContextPure.skip
  | «break» => intro F s hc; rw [evaluateHOLFiniteState_break]
  | «continue» => intro F s hc; rw [evaluateHOLFiniteState_continue]
  | annot tag text => intro F s hc; rw [evaluateHOLFiniteState_annot]
  | «return» e => exact ArithContextPure.ret e
  | assign kind name e =>
      cases kind with
      | «local» => exact ArithContextPure.assign name e
      | «global» => simp [arithContextPureSyntax] at hs
  | store dst value => exact ArithContextPure.store dst value
  | storeByte dst value => exact ArithContextPure.storeByte dst value
  | primitive name op args => exact ArithContextPure.primitive name op args
  | dec name shape e body =>
      exact ArithContextPure.dec name shape e (arithContextPure_of_syntax allowed functions body hs)
  | seq first second =>
      have hs' : arithContextPureSyntax allowed first = true ∧ arithContextPureSyntax allowed second = true :=
        by simpa only [arithContextPureSyntax, Bool.and_eq_true] using hs
      exact @ArithContextPure.seq first second (arithContextPure_of_syntax allowed functions first hs'.1)
        (arithContextPure_of_syntax allowed functions second hs'.2)
  | ite e first second =>
      have hs' : arithContextPureSyntax allowed first = true ∧ arithContextPureSyntax allowed second = true :=
        by simpa only [arithContextPureSyntax, Bool.and_eq_true] using hs
      exact @ArithContextPure.ite e first second (arithContextPure_of_syntax allowed functions first hs'.1)
        (arithContextPure_of_syntax allowed functions second hs'.2)
  | «while» e body =>
      exact ArithContextPure.loop e (arithContextPure_of_syntax allowed functions body hs)
  | call info name args =>
      cases info with
      | none => exact ArithContextPure.call name args none (by intro key; simp) (functions name hs)
      | some info =>
          rcases info with ⟨dest, handler⟩
          cases handler with
          | none =>
              cases dest with
              | none => exact ArithContextPure.call name args (some none) (by intro key; simp) (functions name hs)
              | some dest =>
                  rcases dest with ⟨kind,key⟩
                  cases kind with
                  | «local» =>
                      exact ArithContextPure.call name args (some (some (.local,key)))
                        (by intro k; simp) (functions name hs)
                  | «global» => simp [arithContextPureSyntax] at hs
          | some handler => simp [arithContextPureSyntax] at hs
  | decCall resultName shape name args body =>
      have hs' : allowed name = true ∧ arithContextPureSyntax allowed body = true :=
        by simpa only [arithContextPureSyntax, Bool.and_eq_true] using hs
      exact @ArithContextPure.decCall resultName shape name args body (functions name hs'.1)
        (arithContextPure_of_syntax allowed functions body hs'.2)
  | _ => simp [arithContextPureSyntax] at hs
termination_by sizeOf program

theorem arithContextPureFunction_of_installed (name : MlS) (parameters : List (MlS × ShapeHOL))
    (body : ProgHOL 64) (shape : ShapeHOL)
    (installed : InitECandidate.Solver.GuestCodeLookup.originalRuntimeCode.lookup name = some (parameters, body, shape))
    (hp : ArithContextPure body) : ArithContextPureFunction name := by
  intro values found callee rs hlk
  have he := lookupCodeHOLFinite_installed_body InitECandidate.Solver.GuestCodeLookup.originalRuntimeCode.lookup
    name parameters body found shape rs values callee installed hlk
  subst found
  exact @hp

theorem arithContextPure_noCalls (body : ProgHOL 64)
    (hs : arithContextPureSyntax (fun _ => false) body = true) : ArithContextPure body :=
  arithContextPure_of_syntax (fun _ => false) (by intro n h; cases h) body hs

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
