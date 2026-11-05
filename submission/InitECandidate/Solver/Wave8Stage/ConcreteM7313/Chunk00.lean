import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function79
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk00
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard00.name, PrefixChecks.Shard00.arity, Function64.program),
  (PrefixChecks.Shard01.name, PrefixChecks.Shard01.arity, Function65.program),
  (PrefixChecks.Shard02.name, PrefixChecks.Shard02.arity, Function66.program),
  (PrefixChecks.Shard03.name, PrefixChecks.Shard03.arity, Function67.program),
  (PrefixChecks.Shard04.name, PrefixChecks.Shard04.arity, Function68.program),
  (PrefixChecks.Shard05.name, PrefixChecks.Shard05.arity, Function69.program),
  (PrefixChecks.Shard06.name, PrefixChecks.Shard06.arity, Function70.program),
  (PrefixChecks.Shard07.name, PrefixChecks.Shard07.arity, Function71.program),
  (PrefixChecks.Shard08.name, PrefixChecks.Shard08.arity, Function72.program),
  (PrefixChecks.Shard09.name, PrefixChecks.Shard09.arity, Function73.program),
  (PrefixChecks.Shard10.name, PrefixChecks.Shard10.arity, Function74.program),
  (PrefixChecks.Shard11.name, PrefixChecks.Shard11.arity, Function75.program),
  (PrefixChecks.Shard12.name, PrefixChecks.Shard12.arity, Function76.program),
  (PrefixChecks.Shard13.name, PrefixChecks.Shard13.arity, Function77.program),
  (PrefixChecks.Shard14.name, PrefixChecks.Shard14.arity, Function78.program),
  (PrefixChecks.Shard15.name, PrefixChecks.Shard15.arity, Function79.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard00.name, Function64.stackResult.1),
  (PrefixChecks.Shard01.name, Function65.stackResult.1),
  (PrefixChecks.Shard02.name, Function66.stackResult.1),
  (PrefixChecks.Shard03.name, Function67.stackResult.1),
  (PrefixChecks.Shard04.name, Function68.stackResult.1),
  (PrefixChecks.Shard05.name, Function69.stackResult.1),
  (PrefixChecks.Shard06.name, Function70.stackResult.1),
  (PrefixChecks.Shard07.name, Function71.stackResult.1),
  (PrefixChecks.Shard08.name, Function72.stackResult.1),
  (PrefixChecks.Shard09.name, Function73.stackResult.1),
  (PrefixChecks.Shard10.name, Function74.stackResult.1),
  (PrefixChecks.Shard11.name, Function75.stackResult.1),
  (PrefixChecks.Shard12.name, Function76.stackResult.1),
  (PrefixChecks.Shard13.name, Function77.stackResult.1),
  (PrefixChecks.Shard14.name, Function78.stackResult.1),
  (PrefixChecks.Shard15.name, Function79.stackResult.1)
]

noncomputable def frames : List Nat := [
  Function64.stackResult.2.1,
  Function65.stackResult.2.1,
  Function66.stackResult.2.1,
  Function67.stackResult.2.1,
  Function68.stackResult.2.1,
  Function69.stackResult.2.1,
  Function70.stackResult.2.1,
  Function71.stackResult.2.1,
  Function72.stackResult.2.1,
  Function73.stackResult.2.1,
  Function74.stackResult.2.1,
  Function75.stackResult.2.1,
  Function76.stackResult.2.1,
  Function77.stackResult.2.1,
  Function78.stackResult.2.1,
  Function79.stackResult.2.1
]

theorem compiled : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.list [4], 1) = (bodies, frames, Function79.stackResult.2.2) := by
  unfold words bodies frames
  apply compileWordToStack_cons
  · exact Function64.stackResult_eq
  apply compileWordToStack_cons
  · exact Function65.stackResult_eq
  apply compileWordToStack_cons
  · exact Function66.stackResult_eq
  apply compileWordToStack_cons
  · exact Function67.stackResult_eq
  apply compileWordToStack_cons
  · exact Function68.stackResult_eq
  apply compileWordToStack_cons
  · exact Function69.stackResult_eq
  apply compileWordToStack_cons
  · exact Function70.stackResult_eq
  apply compileWordToStack_cons
  · exact Function71.stackResult_eq
  apply compileWordToStack_cons
  · exact Function72.stackResult_eq
  apply compileWordToStack_cons
  · exact Function73.stackResult_eq
  apply compileWordToStack_cons
  · exact Function74.stackResult_eq
  apply compileWordToStack_cons
  · exact Function75.stackResult_eq
  apply compileWordToStack_cons
  · exact Function76.stackResult_eq
  apply compileWordToStack_cons
  · exact Function77.stackResult_eq
  apply compileWordToStack_cons
  · exact Function78.stackResult_eq
  apply compileWordToStack_cons
  · exact Function79.stackResult_eq
  rfl

theorem words_eq :
    ((ConcreteCompilerWord.source.take 16).zip
      [oracle64, oracle65, oracle66, oracle67, oracle68, oracle69, oracle70, oracle71,
       oracle72, oracle73, oracle74, oracle75, oracle76, oracle77, oracle78, oracle79]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [wordFunction oracle64 PrefixChecks.Shard00.entry,
    wordFunction oracle65 PrefixChecks.Shard01.entry,
    wordFunction oracle66 PrefixChecks.Shard02.entry,
    wordFunction oracle67 PrefixChecks.Shard03.entry,
    wordFunction oracle68 PrefixChecks.Shard04.entry,
    wordFunction oracle69 PrefixChecks.Shard05.entry,
    wordFunction oracle70 PrefixChecks.Shard06.entry,
    wordFunction oracle71 PrefixChecks.Shard07.entry,
    wordFunction oracle72 PrefixChecks.Shard08.entry,
    wordFunction oracle73 PrefixChecks.Shard09.entry,
    wordFunction oracle74 PrefixChecks.Shard10.entry,
    wordFunction oracle75 PrefixChecks.Shard11.entry,
    wordFunction oracle76 PrefixChecks.Shard12.entry,
    wordFunction oracle77 PrefixChecks.Shard13.entry,
    wordFunction oracle78 PrefixChecks.Shard14.entry,
    wordFunction oracle79 PrefixChecks.Shard15.entry] = words
  simp only [Function64.wordFunction_eq, Function65.wordFunction_eq,
    Function66.wordFunction_eq, Function67.wordFunction_eq, Function68.wordFunction_eq,
    Function69.wordFunction_eq, Function70.wordFunction_eq, Function71.wordFunction_eq,
    Function72.wordFunction_eq, Function73.wordFunction_eq, Function74.wordFunction_eq,
    Function75.wordFunction_eq, Function76.wordFunction_eq, Function77.wordFunction_eq,
    Function78.wordFunction_eq, Function79.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk00
