import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames04
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table03

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table04
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := Table03.words ++ Chunk04.words
noncomputable def bodies : List (Nat × HolProg 64) := Table03.bodies ++ Chunk04.bodies
noncomputable def frames : List (Nat) := Table03.frames ++ Chunk04.frames

theorem compiled : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.list [4], 1) = (bodies, frames, Function143.stackResult.2.2) :=
  TableComposition.compile_append _ _ _ _ _ _ _ _ _ Table03.compiled Chunk04.compiled

theorem collected : StackRawCall.collectInfo (StackPasses.nativeStubs ++ bodies) .ln =
    Frames04.info := by
  unfold bodies
  rw [← List.append_assoc, TableComposition.collectInfo_append, Table03.collected,
    Frames04.info_eq]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table04
