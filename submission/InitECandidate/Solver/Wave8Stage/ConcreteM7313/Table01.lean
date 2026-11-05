import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames01
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table00

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table01
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := Table00.words ++ Chunk01.words
noncomputable def bodies : List (Nat × HolProg 64) := Table00.bodies ++ Chunk01.bodies
noncomputable def frames : List (Nat) := Table00.frames ++ Chunk01.frames

theorem compiled : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.list [4], 1) = (bodies, frames, Function95.stackResult.2.2) :=
  TableComposition.compile_append _ _ _ _ _ _ _ _ _ Table00.compiled Chunk01.compiled

theorem collected : StackRawCall.collectInfo (StackPasses.nativeStubs ++ bodies) .ln =
    Frames01.info := by
  unfold bodies
  rw [← List.append_assoc, TableComposition.collectInfo_append, Table00.collected,
    Frames01.info_eq]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table01
