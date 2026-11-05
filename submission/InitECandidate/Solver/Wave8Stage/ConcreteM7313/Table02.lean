import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Frames02
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table01

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table02
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := Table01.words ++ Chunk02.words
noncomputable def bodies : List (Nat × HolProg 64) := Table01.bodies ++ Chunk02.bodies
noncomputable def frames : List (Nat) := Table01.frames ++ Chunk02.frames

theorem compiled : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.list [4], 1) = (bodies, frames, Function111.stackResult.2.2) :=
  TableComposition.compile_append _ _ _ _ _ _ _ _ _ Table01.compiled Chunk02.compiled

theorem collected : StackRawCall.collectInfo (StackPasses.nativeStubs ++ bodies) .ln =
    Frames02.info := by
  unfold bodies
  rw [← List.append_assoc, TableComposition.collectInfo_append, Table01.collected,
    Frames02.info_eq]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Table02
