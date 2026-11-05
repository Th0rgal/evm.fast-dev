import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BackendDecomposition

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

/-- Compose independently certified chunks while retaining the exact bitmap
state at the chunk boundary. -/
theorem compile_append
    (left right : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (before middle after : AppList (BitVec 64) × Nat)
    (leftBodies rightBodies : List (Nat × HolProg 64))
    (leftFrames rightFrames : List Nat)
    (hl : WordToStack.Native.compileWordToStackNative riscvConfig false registers
      left before = (leftBodies, leftFrames, middle))
    (hr : WordToStack.Native.compileWordToStackNative riscvConfig false registers
      right middle = (rightBodies, rightFrames, after)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      (left ++ right) before =
        (leftBodies ++ rightBodies, leftFrames ++ rightFrames, after) := by
  induction left generalizing before leftBodies leftFrames with
  | nil =>
    simp only [WordToStack.Native.compileWordToStackNative] at hl
    cases hl
    exact hr
  | cons entry rest ih =>
    rcases entry with ⟨identifier, arguments, body⟩
    generalize hhead : WordToStack.Native.compileProgNative riscvConfig false body
      arguments registers before = head at *
    rcases head with ⟨headBody, headFrame, headState⟩
    generalize htail : WordToStack.Native.compileWordToStackNative riscvConfig false
      registers rest headState = tail at *
    rcases tail with ⟨tailBodies, tailFrames, tailState⟩
    simp only [WordToStack.Native.compileWordToStackNative, hhead, htail] at hl
    cases hl
    exact compileWordToStack_cons identifier arguments body (rest ++ right)
      before headState after headBody headFrame (tailBodies ++ rightBodies)
      (tailFrames ++ rightFrames) hhead (ih headState tailBodies tailFrames htail)

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
