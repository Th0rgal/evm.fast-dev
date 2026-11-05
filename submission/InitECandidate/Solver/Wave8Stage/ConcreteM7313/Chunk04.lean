import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function143
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk04
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard64.name, PrefixChecks.Shard64.arity, Function128.program),
  (PrefixChecks.Shard65.name, PrefixChecks.Shard65.arity, Function129.program),
  (PrefixChecks.Shard66.name, PrefixChecks.Shard66.arity, Function130.program),
  (PrefixChecks.Shard67.name, PrefixChecks.Shard67.arity, Function131.program),
  (PrefixChecks.Shard68.name, PrefixChecks.Shard68.arity, Function132.program),
  (PrefixChecks.Shard69.name, PrefixChecks.Shard69.arity, Function133.program),
  (PrefixChecks.Shard70.name, PrefixChecks.Shard70.arity, Function134.program),
  (PrefixChecks.Shard71.name, PrefixChecks.Shard71.arity, Function135.program),
  (PrefixChecks.Shard72.name, PrefixChecks.Shard72.arity, Function136.program),
  (PrefixChecks.Shard73.name, PrefixChecks.Shard73.arity, Function137.program),
  (PrefixChecks.Shard74.name, PrefixChecks.Shard74.arity, Function138.program),
  (PrefixChecks.Shard75.name, PrefixChecks.Shard75.arity, Function139.program),
  (PrefixChecks.Shard76.name, PrefixChecks.Shard76.arity, Function140.program),
  (PrefixChecks.Shard77.name, PrefixChecks.Shard77.arity, Function141.program),
  (PrefixChecks.Shard78.name, PrefixChecks.Shard78.arity, Function142.program),
  (PrefixChecks.Shard79.name, PrefixChecks.Shard79.arity, Function143.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard64.name, Function128.stackResult.1),
  (PrefixChecks.Shard65.name, Function129.stackResult.1),
  (PrefixChecks.Shard66.name, Function130.stackResult.1),
  (PrefixChecks.Shard67.name, Function131.stackResult.1),
  (PrefixChecks.Shard68.name, Function132.stackResult.1),
  (PrefixChecks.Shard69.name, Function133.stackResult.1),
  (PrefixChecks.Shard70.name, Function134.stackResult.1),
  (PrefixChecks.Shard71.name, Function135.stackResult.1),
  (PrefixChecks.Shard72.name, Function136.stackResult.1),
  (PrefixChecks.Shard73.name, Function137.stackResult.1),
  (PrefixChecks.Shard74.name, Function138.stackResult.1),
  (PrefixChecks.Shard75.name, Function139.stackResult.1),
  (PrefixChecks.Shard76.name, Function140.stackResult.1),
  (PrefixChecks.Shard77.name, Function141.stackResult.1),
  (PrefixChecks.Shard78.name, Function142.stackResult.1),
  (PrefixChecks.Shard79.name, Function143.stackResult.1)
]

noncomputable def frames : List Nat := [
  Function128.stackResult.2.1,
  Function129.stackResult.2.1,
  Function130.stackResult.2.1,
  Function131.stackResult.2.1,
  Function132.stackResult.2.1,
  Function133.stackResult.2.1,
  Function134.stackResult.2.1,
  Function135.stackResult.2.1,
  Function136.stackResult.2.1,
  Function137.stackResult.2.1,
  Function138.stackResult.2.1,
  Function139.stackResult.2.1,
  Function140.stackResult.2.1,
  Function141.stackResult.2.1,
  Function142.stackResult.2.1,
  Function143.stackResult.2.1
]

theorem compiled : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words Function127.stackResult.2.2 = (bodies, frames, Function143.stackResult.2.2) := by
  unfold words bodies frames
  apply compileWordToStack_cons
  · exact Function128.stackResult_eq
  apply compileWordToStack_cons
  · exact Function129.stackResult_eq
  apply compileWordToStack_cons
  · exact Function130.stackResult_eq
  apply compileWordToStack_cons
  · exact Function131.stackResult_eq
  apply compileWordToStack_cons
  · exact Function132.stackResult_eq
  apply compileWordToStack_cons
  · exact Function133.stackResult_eq
  apply compileWordToStack_cons
  · exact Function134.stackResult_eq
  apply compileWordToStack_cons
  · exact Function135.stackResult_eq
  apply compileWordToStack_cons
  · exact Function136.stackResult_eq
  apply compileWordToStack_cons
  · exact Function137.stackResult_eq
  apply compileWordToStack_cons
  · exact Function138.stackResult_eq
  apply compileWordToStack_cons
  · exact Function139.stackResult_eq
  apply compileWordToStack_cons
  · exact Function140.stackResult_eq
  apply compileWordToStack_cons
  · exact Function141.stackResult_eq
  apply compileWordToStack_cons
  · exact Function142.stackResult_eq
  apply compileWordToStack_cons
  · exact Function143.stackResult_eq
  rfl

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 64).take 16).zip
      [oracle128, oracle129, oracle130, oracle131, oracle132, oracle133, oracle134, oracle135, oracle136, oracle137, oracle138, oracle139, oracle140, oracle141, oracle142, oracle143]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle128 PrefixChecks.Shard64.entry,
    wordFunction oracle129 PrefixChecks.Shard65.entry,
    wordFunction oracle130 PrefixChecks.Shard66.entry,
    wordFunction oracle131 PrefixChecks.Shard67.entry,
    wordFunction oracle132 PrefixChecks.Shard68.entry,
    wordFunction oracle133 PrefixChecks.Shard69.entry,
    wordFunction oracle134 PrefixChecks.Shard70.entry,
    wordFunction oracle135 PrefixChecks.Shard71.entry,
    wordFunction oracle136 PrefixChecks.Shard72.entry,
    wordFunction oracle137 PrefixChecks.Shard73.entry,
    wordFunction oracle138 PrefixChecks.Shard74.entry,
    wordFunction oracle139 PrefixChecks.Shard75.entry,
    wordFunction oracle140 PrefixChecks.Shard76.entry,
    wordFunction oracle141 PrefixChecks.Shard77.entry,
    wordFunction oracle142 PrefixChecks.Shard78.entry,
    wordFunction oracle143 PrefixChecks.Shard79.entry] = words
  simp only [
    Function128.wordFunction_eq,
    Function129.wordFunction_eq,
    Function130.wordFunction_eq,
    Function131.wordFunction_eq,
    Function132.wordFunction_eq,
    Function133.wordFunction_eq,
    Function134.wordFunction_eq,
    Function135.wordFunction_eq,
    Function136.wordFunction_eq,
    Function137.wordFunction_eq,
    Function138.wordFunction_eq,
    Function139.wordFunction_eq,
    Function140.wordFunction_eq,
    Function141.wordFunction_eq,
    Function142.wordFunction_eq,
    Function143.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk04
