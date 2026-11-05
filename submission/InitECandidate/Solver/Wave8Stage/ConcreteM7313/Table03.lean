import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames03
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table02

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table03
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := Table02.words ++ Chunk03.words
noncomputable def bodies : List (Nat × HolProg 64) := Table02.bodies ++ Chunk03.bodies
noncomputable def frames : List (Nat) := Table02.frames ++ Chunk03.frames

theorem compiled : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.list [4], 1) = (bodies, frames, Function127.stackResult.2.2) :=
  TableComposition.compile_append _ _ _ _ _ _ _ _ _ Table02.compiled Chunk03.compiled

theorem collected : StackRawCall.collectInfo (StackPasses.nativeStubs ++ bodies) .ln =
    Frames03.info := by
  unfold bodies
  rw [← List.append_assoc, TableComposition.collectInfo_append, Table02.collected,
    Frames03.info_eq]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table03
