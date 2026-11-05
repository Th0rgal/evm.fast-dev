import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function95
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk01
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard16.name, PrefixChecks.Shard16.arity, Function80.program),
  (PrefixChecks.Shard17.name, PrefixChecks.Shard17.arity, Function81.program),
  (PrefixChecks.Shard18.name, PrefixChecks.Shard18.arity, Function82.program),
  (PrefixChecks.Shard19.name, PrefixChecks.Shard19.arity, Function83.program),
  (PrefixChecks.Shard20.name, PrefixChecks.Shard20.arity, Function84.program),
  (PrefixChecks.Shard21.name, PrefixChecks.Shard21.arity, Function85.program),
  (PrefixChecks.Shard22.name, PrefixChecks.Shard22.arity, Function86.program),
  (PrefixChecks.Shard23.name, PrefixChecks.Shard23.arity, Function87.program),
  (PrefixChecks.Shard24.name, PrefixChecks.Shard24.arity, Function88.program),
  (PrefixChecks.Shard25.name, PrefixChecks.Shard25.arity, Function89.program),
  (PrefixChecks.Shard26.name, PrefixChecks.Shard26.arity, Function90.program),
  (PrefixChecks.Shard27.name, PrefixChecks.Shard27.arity, Function91.program),
  (PrefixChecks.Shard28.name, PrefixChecks.Shard28.arity, Function92.program),
  (PrefixChecks.Shard29.name, PrefixChecks.Shard29.arity, Function93.program),
  (PrefixChecks.Shard30.name, PrefixChecks.Shard30.arity, Function94.program),
  (PrefixChecks.Shard31.name, PrefixChecks.Shard31.arity, Function95.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard16.name, Function80.stackResult.1),
  (PrefixChecks.Shard17.name, Function81.stackResult.1),
  (PrefixChecks.Shard18.name, Function82.stackResult.1),
  (PrefixChecks.Shard19.name, Function83.stackResult.1),
  (PrefixChecks.Shard20.name, Function84.stackResult.1),
  (PrefixChecks.Shard21.name, Function85.stackResult.1),
  (PrefixChecks.Shard22.name, Function86.stackResult.1),
  (PrefixChecks.Shard23.name, Function87.stackResult.1),
  (PrefixChecks.Shard24.name, Function88.stackResult.1),
  (PrefixChecks.Shard25.name, Function89.stackResult.1),
  (PrefixChecks.Shard26.name, Function90.stackResult.1),
  (PrefixChecks.Shard27.name, Function91.stackResult.1),
  (PrefixChecks.Shard28.name, Function92.stackResult.1),
  (PrefixChecks.Shard29.name, Function93.stackResult.1),
  (PrefixChecks.Shard30.name, Function94.stackResult.1),
  (PrefixChecks.Shard31.name, Function95.stackResult.1)
]

noncomputable def frames : List Nat := [
  Function80.stackResult.2.1,
  Function81.stackResult.2.1,
  Function82.stackResult.2.1,
  Function83.stackResult.2.1,
  Function84.stackResult.2.1,
  Function85.stackResult.2.1,
  Function86.stackResult.2.1,
  Function87.stackResult.2.1,
  Function88.stackResult.2.1,
  Function89.stackResult.2.1,
  Function90.stackResult.2.1,
  Function91.stackResult.2.1,
  Function92.stackResult.2.1,
  Function93.stackResult.2.1,
  Function94.stackResult.2.1,
  Function95.stackResult.2.1
]

theorem compiled : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words Function79.stackResult.2.2 = (bodies, frames, Function95.stackResult.2.2) := by
  unfold words bodies frames
  apply compileWordToStack_cons
  · exact Function80.stackResult_eq
  apply compileWordToStack_cons
  · exact Function81.stackResult_eq
  apply compileWordToStack_cons
  · exact Function82.stackResult_eq
  apply compileWordToStack_cons
  · exact Function83.stackResult_eq
  apply compileWordToStack_cons
  · exact Function84.stackResult_eq
  apply compileWordToStack_cons
  · exact Function85.stackResult_eq
  apply compileWordToStack_cons
  · exact Function86.stackResult_eq
  apply compileWordToStack_cons
  · exact Function87.stackResult_eq
  apply compileWordToStack_cons
  · exact Function88.stackResult_eq
  apply compileWordToStack_cons
  · exact Function89.stackResult_eq
  apply compileWordToStack_cons
  · exact Function90.stackResult_eq
  apply compileWordToStack_cons
  · exact Function91.stackResult_eq
  apply compileWordToStack_cons
  · exact Function92.stackResult_eq
  apply compileWordToStack_cons
  · exact Function93.stackResult_eq
  apply compileWordToStack_cons
  · exact Function94.stackResult_eq
  apply compileWordToStack_cons
  · exact Function95.stackResult_eq
  rfl

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 16).take 16).zip
      [oracle80, oracle81, oracle82, oracle83, oracle84, oracle85, oracle86, oracle87, oracle88, oracle89, oracle90, oracle91, oracle92, oracle93, oracle94, oracle95]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle80 PrefixChecks.Shard16.entry,
    wordFunction oracle81 PrefixChecks.Shard17.entry,
    wordFunction oracle82 PrefixChecks.Shard18.entry,
    wordFunction oracle83 PrefixChecks.Shard19.entry,
    wordFunction oracle84 PrefixChecks.Shard20.entry,
    wordFunction oracle85 PrefixChecks.Shard21.entry,
    wordFunction oracle86 PrefixChecks.Shard22.entry,
    wordFunction oracle87 PrefixChecks.Shard23.entry,
    wordFunction oracle88 PrefixChecks.Shard24.entry,
    wordFunction oracle89 PrefixChecks.Shard25.entry,
    wordFunction oracle90 PrefixChecks.Shard26.entry,
    wordFunction oracle91 PrefixChecks.Shard27.entry,
    wordFunction oracle92 PrefixChecks.Shard28.entry,
    wordFunction oracle93 PrefixChecks.Shard29.entry,
    wordFunction oracle94 PrefixChecks.Shard30.entry,
    wordFunction oracle95 PrefixChecks.Shard31.entry] = words
  simp only [
    Function80.wordFunction_eq,
    Function81.wordFunction_eq,
    Function82.wordFunction_eq,
    Function83.wordFunction_eq,
    Function84.wordFunction_eq,
    Function85.wordFunction_eq,
    Function86.wordFunction_eq,
    Function87.wordFunction_eq,
    Function88.wordFunction_eq,
    Function89.wordFunction_eq,
    Function90.wordFunction_eq,
    Function91.wordFunction_eq,
    Function92.wordFunction_eq,
    Function93.wordFunction_eq,
    Function94.wordFunction_eq,
    Function95.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk01
