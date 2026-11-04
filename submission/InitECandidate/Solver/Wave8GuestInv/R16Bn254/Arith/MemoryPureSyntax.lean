import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryPureCalls
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryPureLoop

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def memoryPureSyntax (allowed : MlS → Bool) : ProgHOL 64 → Bool
  | .skip | .break | .continue | .annot _ _ | .return _ | .assign _ _ _ | .primitive _ _ _ => true
  | .dec _ _ _ body => memoryPureSyntax allowed body
  | .seq first second | .ite _ first second => memoryPureSyntax allowed first && memoryPureSyntax allowed second
  | .while _ body => memoryPureSyntax allowed body
  | .call none name _ | .call (some (_, none)) name _ => allowed name
  | .decCall _ _ name _ body => allowed name && memoryPureSyntax allowed body
  | _ => false

theorem memoryPure_of_syntax (allowed : MlS → Bool)
    (functions : ∀ name, allowed name = true → MemoryPureFunction name)
    (program : ProgHOL 64) (hs : memoryPureSyntax allowed program = true) :
    MemoryPure program := by
  cases program with
  | skip => exact MemoryPure.skip
  | «break» => intro F s hc; rw [evaluateHOLFiniteState_break]
  | «continue» => intro F s hc; rw [evaluateHOLFiniteState_continue]
  | annot tag text => intro F s hc; rw [evaluateHOLFiniteState_annot]
  | «return» e => exact MemoryPure.ret e
  | assign kind name e => exact MemoryPure.assign kind name e
  | primitive name op args => exact MemoryPure.primitive name op args
  | dec name shape e body =>
      exact MemoryPure.dec name shape e (memoryPure_of_syntax allowed functions body hs)
  | seq first second =>
      have hs' : memoryPureSyntax allowed first = true ∧ memoryPureSyntax allowed second = true :=
        by simpa only [memoryPureSyntax, Bool.and_eq_true] using hs
      exact @MemoryPure.seq first second (memoryPure_of_syntax allowed functions first hs'.1)
        (memoryPure_of_syntax allowed functions second hs'.2)
  | ite e first second =>
      have hs' : memoryPureSyntax allowed first = true ∧ memoryPureSyntax allowed second = true :=
        by simpa only [memoryPureSyntax, Bool.and_eq_true] using hs
      exact @MemoryPure.ite e first second (memoryPure_of_syntax allowed functions first hs'.1)
        (memoryPure_of_syntax allowed functions second hs'.2)
  | «while» e body =>
      exact MemoryPure.loop e (memoryPure_of_syntax allowed functions body hs)
  | call info name args =>
      cases info with
      | none => exact MemoryPure.call name args none (functions name hs)
      | some info =>
          rcases info with ⟨dest, handler⟩
          cases handler with
          | none => exact MemoryPure.call name args (some dest) (functions name hs)
          | some handler => simp [memoryPureSyntax] at hs
  | decCall resultName shape name args body =>
      have hs' : allowed name = true ∧ memoryPureSyntax allowed body = true :=
        by simpa only [memoryPureSyntax, Bool.and_eq_true] using hs
      exact @MemoryPure.decCall resultName shape name args body (functions name hs'.1)
        (memoryPure_of_syntax allowed functions body hs'.2)
  | _ => simp [memoryPureSyntax] at hs
termination_by sizeOf program

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
