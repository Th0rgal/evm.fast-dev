import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function111
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk02
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard32.name, PrefixChecks.Shard32.arity, Function96.program),
  (PrefixChecks.Shard33.name, PrefixChecks.Shard33.arity, Function97.program),
  (PrefixChecks.Shard34.name, PrefixChecks.Shard34.arity, Function98.program),
  (PrefixChecks.Shard35.name, PrefixChecks.Shard35.arity, Function99.program),
  (PrefixChecks.Shard36.name, PrefixChecks.Shard36.arity, Function100.program),
  (PrefixChecks.Shard37.name, PrefixChecks.Shard37.arity, Function101.program),
  (PrefixChecks.Shard38.name, PrefixChecks.Shard38.arity, Function102.program),
  (PrefixChecks.Shard39.name, PrefixChecks.Shard39.arity, Function103.program),
  (PrefixChecks.Shard40.name, PrefixChecks.Shard40.arity, Function104.program),
  (PrefixChecks.Shard41.name, PrefixChecks.Shard41.arity, Function105.program),
  (PrefixChecks.Shard42.name, PrefixChecks.Shard42.arity, Function106.program),
  (PrefixChecks.Shard43.name, PrefixChecks.Shard43.arity, Function107.program),
  (PrefixChecks.Shard44.name, PrefixChecks.Shard44.arity, Function108.program),
  (PrefixChecks.Shard45.name, PrefixChecks.Shard45.arity, Function109.program),
  (PrefixChecks.Shard46.name, PrefixChecks.Shard46.arity, Function110.program),
  (PrefixChecks.Shard47.name, PrefixChecks.Shard47.arity, Function111.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard32.name, Function96.stackResult.1),
  (PrefixChecks.Shard33.name, Function97.stackResult.1),
  (PrefixChecks.Shard34.name, Function98.stackResult.1),
  (PrefixChecks.Shard35.name, Function99.stackResult.1),
  (PrefixChecks.Shard36.name, Function100.stackResult.1),
  (PrefixChecks.Shard37.name, Function101.stackResult.1),
  (PrefixChecks.Shard38.name, Function102.stackResult.1),
  (PrefixChecks.Shard39.name, Function103.stackResult.1),
  (PrefixChecks.Shard40.name, Function104.stackResult.1),
  (PrefixChecks.Shard41.name, Function105.stackResult.1),
  (PrefixChecks.Shard42.name, Function106.stackResult.1),
  (PrefixChecks.Shard43.name, Function107.stackResult.1),
  (PrefixChecks.Shard44.name, Function108.stackResult.1),
  (PrefixChecks.Shard45.name, Function109.stackResult.1),
  (PrefixChecks.Shard46.name, Function110.stackResult.1),
  (PrefixChecks.Shard47.name, Function111.stackResult.1)
]

noncomputable def frames : List Nat := [
  Function96.stackResult.2.1,
  Function97.stackResult.2.1,
  Function98.stackResult.2.1,
  Function99.stackResult.2.1,
  Function100.stackResult.2.1,
  Function101.stackResult.2.1,
  Function102.stackResult.2.1,
  Function103.stackResult.2.1,
  Function104.stackResult.2.1,
  Function105.stackResult.2.1,
  Function106.stackResult.2.1,
  Function107.stackResult.2.1,
  Function108.stackResult.2.1,
  Function109.stackResult.2.1,
  Function110.stackResult.2.1,
  Function111.stackResult.2.1
]

theorem compiled : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words Function95.stackResult.2.2 = (bodies, frames, Function111.stackResult.2.2) := by
  unfold words bodies frames
  apply compileWordToStack_cons
  · exact Function96.stackResult_eq
  apply compileWordToStack_cons
  · exact Function97.stackResult_eq
  apply compileWordToStack_cons
  · exact Function98.stackResult_eq
  apply compileWordToStack_cons
  · exact Function99.stackResult_eq
  apply compileWordToStack_cons
  · exact Function100.stackResult_eq
  apply compileWordToStack_cons
  · exact Function101.stackResult_eq
  apply compileWordToStack_cons
  · exact Function102.stackResult_eq
  apply compileWordToStack_cons
  · exact Function103.stackResult_eq
  apply compileWordToStack_cons
  · exact Function104.stackResult_eq
  apply compileWordToStack_cons
  · exact Function105.stackResult_eq
  apply compileWordToStack_cons
  · exact Function106.stackResult_eq
  apply compileWordToStack_cons
  · exact Function107.stackResult_eq
  apply compileWordToStack_cons
  · exact Function108.stackResult_eq
  apply compileWordToStack_cons
  · exact Function109.stackResult_eq
  apply compileWordToStack_cons
  · exact Function110.stackResult_eq
  apply compileWordToStack_cons
  · exact Function111.stackResult_eq
  rfl

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 32).take 16).zip
      [oracle96, oracle97, oracle98, oracle99, oracle100, oracle101, oracle102, oracle103, oracle104, oracle105, oracle106, oracle107, oracle108, oracle109, oracle110, oracle111]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle96 PrefixChecks.Shard32.entry,
    wordFunction oracle97 PrefixChecks.Shard33.entry,
    wordFunction oracle98 PrefixChecks.Shard34.entry,
    wordFunction oracle99 PrefixChecks.Shard35.entry,
    wordFunction oracle100 PrefixChecks.Shard36.entry,
    wordFunction oracle101 PrefixChecks.Shard37.entry,
    wordFunction oracle102 PrefixChecks.Shard38.entry,
    wordFunction oracle103 PrefixChecks.Shard39.entry,
    wordFunction oracle104 PrefixChecks.Shard40.entry,
    wordFunction oracle105 PrefixChecks.Shard41.entry,
    wordFunction oracle106 PrefixChecks.Shard42.entry,
    wordFunction oracle107 PrefixChecks.Shard43.entry,
    wordFunction oracle108 PrefixChecks.Shard44.entry,
    wordFunction oracle109 PrefixChecks.Shard45.entry,
    wordFunction oracle110 PrefixChecks.Shard46.entry,
    wordFunction oracle111 PrefixChecks.Shard47.entry] = words
  simp only [
    Function96.wordFunction_eq,
    Function97.wordFunction_eq,
    Function98.wordFunction_eq,
    Function99.wordFunction_eq,
    Function100.wordFunction_eq,
    Function101.wordFunction_eq,
    Function102.wordFunction_eq,
    Function103.wordFunction_eq,
    Function104.wordFunction_eq,
    Function105.wordFunction_eq,
    Function106.wordFunction_eq,
    Function107.wordFunction_eq,
    Function108.wordFunction_eq,
    Function109.wordFunction_eq,
    Function110.wordFunction_eq,
    Function111.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk02
