import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames00

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table00
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := Chunk00.words
noncomputable def bodies : List (Nat × HolProg 64) := Chunk00.bodies
noncomputable def frames : List (Nat) := Chunk00.frames

theorem compiled : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.list [4], 1) = (bodies, frames, Function79.stackResult.2.2) :=
  Chunk00.compiled

theorem collected : StackRawCall.collectInfo (StackPasses.nativeStubs ++ bodies) .ln =
    Frames00.info := by
  exact Frames00.collected

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table00
