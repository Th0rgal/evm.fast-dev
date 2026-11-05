import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function127
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk03
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard48.name, PrefixChecks.Shard48.arity, Function112.program),
  (PrefixChecks.Shard49.name, PrefixChecks.Shard49.arity, Function113.program),
  (PrefixChecks.Shard50.name, PrefixChecks.Shard50.arity, Function114.program),
  (PrefixChecks.Shard51.name, PrefixChecks.Shard51.arity, Function115.program),
  (PrefixChecks.Shard52.name, PrefixChecks.Shard52.arity, Function116.program),
  (PrefixChecks.Shard53.name, PrefixChecks.Shard53.arity, Function117.program),
  (PrefixChecks.Shard54.name, PrefixChecks.Shard54.arity, Function118.program),
  (PrefixChecks.Shard55.name, PrefixChecks.Shard55.arity, Function119.program),
  (PrefixChecks.Shard56.name, PrefixChecks.Shard56.arity, Function120.program),
  (PrefixChecks.Shard57.name, PrefixChecks.Shard57.arity, Function121.program),
  (PrefixChecks.Shard58.name, PrefixChecks.Shard58.arity, Function122.program),
  (PrefixChecks.Shard59.name, PrefixChecks.Shard59.arity, Function123.program),
  (PrefixChecks.Shard60.name, PrefixChecks.Shard60.arity, Function124.program),
  (PrefixChecks.Shard61.name, PrefixChecks.Shard61.arity, Function125.program),
  (PrefixChecks.Shard62.name, PrefixChecks.Shard62.arity, Function126.program),
  (PrefixChecks.Shard63.name, PrefixChecks.Shard63.arity, Function127.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard48.name, Function112.stackResult.1),
  (PrefixChecks.Shard49.name, Function113.stackResult.1),
  (PrefixChecks.Shard50.name, Function114.stackResult.1),
  (PrefixChecks.Shard51.name, Function115.stackResult.1),
  (PrefixChecks.Shard52.name, Function116.stackResult.1),
  (PrefixChecks.Shard53.name, Function117.stackResult.1),
  (PrefixChecks.Shard54.name, Function118.stackResult.1),
  (PrefixChecks.Shard55.name, Function119.stackResult.1),
  (PrefixChecks.Shard56.name, Function120.stackResult.1),
  (PrefixChecks.Shard57.name, Function121.stackResult.1),
  (PrefixChecks.Shard58.name, Function122.stackResult.1),
  (PrefixChecks.Shard59.name, Function123.stackResult.1),
  (PrefixChecks.Shard60.name, Function124.stackResult.1),
  (PrefixChecks.Shard61.name, Function125.stackResult.1),
  (PrefixChecks.Shard62.name, Function126.stackResult.1),
  (PrefixChecks.Shard63.name, Function127.stackResult.1)
]

noncomputable def frames : List Nat := [
  Function112.stackResult.2.1,
  Function113.stackResult.2.1,
  Function114.stackResult.2.1,
  Function115.stackResult.2.1,
  Function116.stackResult.2.1,
  Function117.stackResult.2.1,
  Function118.stackResult.2.1,
  Function119.stackResult.2.1,
  Function120.stackResult.2.1,
  Function121.stackResult.2.1,
  Function122.stackResult.2.1,
  Function123.stackResult.2.1,
  Function124.stackResult.2.1,
  Function125.stackResult.2.1,
  Function126.stackResult.2.1,
  Function127.stackResult.2.1
]

theorem compiled : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words Function111.stackResult.2.2 = (bodies, frames, Function127.stackResult.2.2) := by
  unfold words bodies frames
  apply compileWordToStack_cons
  · exact Function112.stackResult_eq
  apply compileWordToStack_cons
  · exact Function113.stackResult_eq
  apply compileWordToStack_cons
  · exact Function114.stackResult_eq
  apply compileWordToStack_cons
  · exact Function115.stackResult_eq
  apply compileWordToStack_cons
  · exact Function116.stackResult_eq
  apply compileWordToStack_cons
  · exact Function117.stackResult_eq
  apply compileWordToStack_cons
  · exact Function118.stackResult_eq
  apply compileWordToStack_cons
  · exact Function119.stackResult_eq
  apply compileWordToStack_cons
  · exact Function120.stackResult_eq
  apply compileWordToStack_cons
  · exact Function121.stackResult_eq
  apply compileWordToStack_cons
  · exact Function122.stackResult_eq
  apply compileWordToStack_cons
  · exact Function123.stackResult_eq
  apply compileWordToStack_cons
  · exact Function124.stackResult_eq
  apply compileWordToStack_cons
  · exact Function125.stackResult_eq
  apply compileWordToStack_cons
  · exact Function126.stackResult_eq
  apply compileWordToStack_cons
  · exact Function127.stackResult_eq
  rfl

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 48).take 16).zip
      [oracle112, oracle113, oracle114, oracle115, oracle116, oracle117, oracle118, oracle119, oracle120, oracle121, oracle122, oracle123, oracle124, oracle125, oracle126, oracle127]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle112 PrefixChecks.Shard48.entry,
    wordFunction oracle113 PrefixChecks.Shard49.entry,
    wordFunction oracle114 PrefixChecks.Shard50.entry,
    wordFunction oracle115 PrefixChecks.Shard51.entry,
    wordFunction oracle116 PrefixChecks.Shard52.entry,
    wordFunction oracle117 PrefixChecks.Shard53.entry,
    wordFunction oracle118 PrefixChecks.Shard54.entry,
    wordFunction oracle119 PrefixChecks.Shard55.entry,
    wordFunction oracle120 PrefixChecks.Shard56.entry,
    wordFunction oracle121 PrefixChecks.Shard57.entry,
    wordFunction oracle122 PrefixChecks.Shard58.entry,
    wordFunction oracle123 PrefixChecks.Shard59.entry,
    wordFunction oracle124 PrefixChecks.Shard60.entry,
    wordFunction oracle125 PrefixChecks.Shard61.entry,
    wordFunction oracle126 PrefixChecks.Shard62.entry,
    wordFunction oracle127 PrefixChecks.Shard63.entry] = words
  simp only [
    Function112.wordFunction_eq,
    Function113.wordFunction_eq,
    Function114.wordFunction_eq,
    Function115.wordFunction_eq,
    Function116.wordFunction_eq,
    Function117.wordFunction_eq,
    Function118.wordFunction_eq,
    Function119.wordFunction_eq,
    Function120.wordFunction_eq,
    Function121.wordFunction_eq,
    Function122.wordFunction_eq,
    Function123.wordFunction_eq,
    Function124.wordFunction_eq,
    Function125.wordFunction_eq,
    Function126.wordFunction_eq,
    Function127.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk03
