import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk00
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk01

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.FirstTwoChunks
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

theorem compiled : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    (Chunk00.words ++ Chunk01.words) (.list [4], 1) =
      (Chunk00.bodies ++ Chunk01.bodies, Chunk00.frames ++ Chunk01.frames,
        Function95.stackResult.2.2) :=
  TableComposition.compile_append _ _ _ _ _ _ _ _ _ Chunk00.compiled Chunk01.compiled

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.FirstTwoChunks
