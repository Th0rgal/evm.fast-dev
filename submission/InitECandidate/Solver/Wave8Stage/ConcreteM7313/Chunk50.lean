import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word864
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word865
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word866
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word867
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word868
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word869
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word870
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word871
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word872
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word873
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word874
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word875
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word876
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word877
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000
set_option cbv.maxSteps 40000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk50
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

wave8_certified_reduce stackResult864 := WordToStack.Native.compileProgNative
  riscvConfig false Word864.program PrefixChecks.Shard800.arity registers (.nil, 4519)
theorem stackResult864_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word864.program
      PrefixChecks.Shard800.arity registers (prefixList, 4519) =
    (stackResult864.1, stackResult864.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult864.2.2.1, 4520)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word864.program
    PrefixChecks.Shard800.arity registers prefixList 4519
    stackResult864.1 stackResult864.2.1 stackResult864.2.2.1 4520 stackResult864_eq
wave8_certified_reduce stackResult865 := WordToStack.Native.compileProgNative
  riscvConfig false Word865.program PrefixChecks.Shard801.arity registers (.nil, 4520)
theorem stackResult865_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word865.program
      PrefixChecks.Shard801.arity registers (prefixList, 4520) =
    (stackResult865.1, stackResult865.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult865.2.2.1, 4524)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word865.program
    PrefixChecks.Shard801.arity registers prefixList 4520
    stackResult865.1 stackResult865.2.1 stackResult865.2.2.1 4524 stackResult865_eq
wave8_certified_reduce stackResult866 := WordToStack.Native.compileProgNative
  riscvConfig false Word866.program PrefixChecks.Shard802.arity registers (.nil, 4524)
theorem stackResult866_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word866.program
      PrefixChecks.Shard802.arity registers (prefixList, 4524) =
    (stackResult866.1, stackResult866.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult866.2.2.1, 4526)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word866.program
    PrefixChecks.Shard802.arity registers prefixList 4524
    stackResult866.1 stackResult866.2.1 stackResult866.2.2.1 4526 stackResult866_eq
wave8_certified_reduce stackResult867 := WordToStack.Native.compileProgNative
  riscvConfig false Word867.program PrefixChecks.Shard803.arity registers (.nil, 4526)
theorem stackResult867_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word867.program
      PrefixChecks.Shard803.arity registers (prefixList, 4526) =
    (stackResult867.1, stackResult867.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult867.2.2.1, 4541)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word867.program
    PrefixChecks.Shard803.arity registers prefixList 4526
    stackResult867.1 stackResult867.2.1 stackResult867.2.2.1 4541 stackResult867_eq
wave8_certified_reduce stackResult868 := WordToStack.Native.compileProgNative
  riscvConfig false Word868.program PrefixChecks.Shard804.arity registers (.nil, 4541)
theorem stackResult868_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word868.program
      PrefixChecks.Shard804.arity registers (prefixList, 4541) =
    (stackResult868.1, stackResult868.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult868.2.2.1, 4581)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word868.program
    PrefixChecks.Shard804.arity registers prefixList 4541
    stackResult868.1 stackResult868.2.1 stackResult868.2.2.1 4581 stackResult868_eq
wave8_certified_reduce stackResult869 := WordToStack.Native.compileProgNative
  riscvConfig false Word869.program PrefixChecks.Shard805.arity registers (.nil, 4581)
theorem stackResult869_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word869.program
      PrefixChecks.Shard805.arity registers (prefixList, 4581) =
    (stackResult869.1, stackResult869.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult869.2.2.1, 4595)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word869.program
    PrefixChecks.Shard805.arity registers prefixList 4581
    stackResult869.1 stackResult869.2.1 stackResult869.2.2.1 4595 stackResult869_eq
wave8_certified_reduce stackResult870 := WordToStack.Native.compileProgNative
  riscvConfig false Word870.program PrefixChecks.Shard806.arity registers (.nil, 4595)
theorem stackResult870_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word870.program
      PrefixChecks.Shard806.arity registers (prefixList, 4595) =
    (stackResult870.1, stackResult870.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult870.2.2.1, 4596)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word870.program
    PrefixChecks.Shard806.arity registers prefixList 4595
    stackResult870.1 stackResult870.2.1 stackResult870.2.2.1 4596 stackResult870_eq
wave8_certified_reduce stackResult871 := WordToStack.Native.compileProgNative
  riscvConfig false Word871.program PrefixChecks.Shard807.arity registers (.nil, 4596)
theorem stackResult871_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word871.program
      PrefixChecks.Shard807.arity registers (prefixList, 4596) =
    (stackResult871.1, stackResult871.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult871.2.2.1, 4597)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word871.program
    PrefixChecks.Shard807.arity registers prefixList 4596
    stackResult871.1 stackResult871.2.1 stackResult871.2.2.1 4597 stackResult871_eq
wave8_certified_reduce stackResult872 := WordToStack.Native.compileProgNative
  riscvConfig false Word872.program PrefixChecks.Shard808.arity registers (.nil, 4597)
theorem stackResult872_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word872.program
      PrefixChecks.Shard808.arity registers (prefixList, 4597) =
    (stackResult872.1, stackResult872.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult872.2.2.1, 4598)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word872.program
    PrefixChecks.Shard808.arity registers prefixList 4597
    stackResult872.1 stackResult872.2.1 stackResult872.2.2.1 4598 stackResult872_eq
wave8_certified_reduce stackResult873 := WordToStack.Native.compileProgNative
  riscvConfig false Word873.program PrefixChecks.Shard809.arity registers (.nil, 4598)
theorem stackResult873_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word873.program
      PrefixChecks.Shard809.arity registers (prefixList, 4598) =
    (stackResult873.1, stackResult873.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult873.2.2.1, 4599)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word873.program
    PrefixChecks.Shard809.arity registers prefixList 4598
    stackResult873.1 stackResult873.2.1 stackResult873.2.2.1 4599 stackResult873_eq
wave8_certified_reduce stackResult874 := WordToStack.Native.compileProgNative
  riscvConfig false Word874.program PrefixChecks.Shard810.arity registers (.nil, 4599)
theorem stackResult874_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word874.program
      PrefixChecks.Shard810.arity registers (prefixList, 4599) =
    (stackResult874.1, stackResult874.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult874.2.2.1, 4600)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word874.program
    PrefixChecks.Shard810.arity registers prefixList 4599
    stackResult874.1 stackResult874.2.1 stackResult874.2.2.1 4600 stackResult874_eq
wave8_certified_reduce stackResult875 := WordToStack.Native.compileProgNative
  riscvConfig false Word875.program PrefixChecks.Shard811.arity registers (.nil, 4600)
theorem stackResult875_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word875.program
      PrefixChecks.Shard811.arity registers (prefixList, 4600) =
    (stackResult875.1, stackResult875.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult875.2.2.1, 4601)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word875.program
    PrefixChecks.Shard811.arity registers prefixList 4600
    stackResult875.1 stackResult875.2.1 stackResult875.2.2.1 4601 stackResult875_eq
wave8_certified_reduce stackResult876 := WordToStack.Native.compileProgNative
  riscvConfig false Word876.program PrefixChecks.Shard812.arity registers (.nil, 4601)
theorem stackResult876_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word876.program
      PrefixChecks.Shard812.arity registers (prefixList, 4601) =
    (stackResult876.1, stackResult876.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult876.2.2.1, 4602)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word876.program
    PrefixChecks.Shard812.arity registers prefixList 4601
    stackResult876.1 stackResult876.2.1 stackResult876.2.2.1 4602 stackResult876_eq
wave8_certified_reduce stackResult877 := WordToStack.Native.compileProgNative
  riscvConfig false Word877.program PrefixChecks.Shard813.arity registers (.nil, 4602)
theorem stackResult877_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word877.program
      PrefixChecks.Shard813.arity registers (prefixList, 4602) =
    (stackResult877.1, stackResult877.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult877.2.2.1, 4603)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word877.program
    PrefixChecks.Shard813.arity registers prefixList 4602
    stackResult877.1 stackResult877.2.1 stackResult877.2.2.1 4603 stackResult877_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard800.name, PrefixChecks.Shard800.arity, Word864.program),
  (PrefixChecks.Shard801.name, PrefixChecks.Shard801.arity, Word865.program),
  (PrefixChecks.Shard802.name, PrefixChecks.Shard802.arity, Word866.program),
  (PrefixChecks.Shard803.name, PrefixChecks.Shard803.arity, Word867.program),
  (PrefixChecks.Shard804.name, PrefixChecks.Shard804.arity, Word868.program),
  (PrefixChecks.Shard805.name, PrefixChecks.Shard805.arity, Word869.program),
  (PrefixChecks.Shard806.name, PrefixChecks.Shard806.arity, Word870.program),
  (PrefixChecks.Shard807.name, PrefixChecks.Shard807.arity, Word871.program),
  (PrefixChecks.Shard808.name, PrefixChecks.Shard808.arity, Word872.program),
  (PrefixChecks.Shard809.name, PrefixChecks.Shard809.arity, Word873.program),
  (PrefixChecks.Shard810.name, PrefixChecks.Shard810.arity, Word874.program),
  (PrefixChecks.Shard811.name, PrefixChecks.Shard811.arity, Word875.program),
  (PrefixChecks.Shard812.name, PrefixChecks.Shard812.arity, Word876.program),
  (PrefixChecks.Shard813.name, PrefixChecks.Shard813.arity, Word877.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard800.name, stackResult864.1),
  (PrefixChecks.Shard801.name, stackResult865.1),
  (PrefixChecks.Shard802.name, stackResult866.1),
  (PrefixChecks.Shard803.name, stackResult867.1),
  (PrefixChecks.Shard804.name, stackResult868.1),
  (PrefixChecks.Shard805.name, stackResult869.1),
  (PrefixChecks.Shard806.name, stackResult870.1),
  (PrefixChecks.Shard807.name, stackResult871.1),
  (PrefixChecks.Shard808.name, stackResult872.1),
  (PrefixChecks.Shard809.name, stackResult873.1),
  (PrefixChecks.Shard810.name, stackResult874.1),
  (PrefixChecks.Shard811.name, stackResult875.1),
  (PrefixChecks.Shard812.name, stackResult876.1),
  (PrefixChecks.Shard813.name, stackResult877.1)
]

noncomputable def frames : List Nat := [
  stackResult864.2.1,
  stackResult865.2.1,
  stackResult866.2.1,
  stackResult867.2.1,
  stackResult868.2.1,
  stackResult869.2.1,
  stackResult870.2.1,
  stackResult871.2.1,
  stackResult872.2.1,
  stackResult873.2.1,
  stackResult874.2.1,
  stackResult875.2.1,
  stackResult876.2.1,
  stackResult877.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult864.2.2.1) stackResult865.2.2.1) stackResult866.2.2.1) stackResult867.2.2.1) stackResult868.2.2.1) stackResult869.2.2.1) stackResult870.2.2.1) stackResult871.2.2.1) stackResult872.2.2.1) stackResult873.2.2.1) stackResult874.2.2.1) stackResult875.2.2.1) stackResult876.2.2.1) stackResult877.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 4519) = (bodies, frames, (bitmapDelta, 4603)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult864_from _
  apply compileWordToStack_cons
  · exact stackResult865_from _
  apply compileWordToStack_cons
  · exact stackResult866_from _
  apply compileWordToStack_cons
  · exact stackResult867_from _
  apply compileWordToStack_cons
  · exact stackResult868_from _
  apply compileWordToStack_cons
  · exact stackResult869_from _
  apply compileWordToStack_cons
  · exact stackResult870_from _
  apply compileWordToStack_cons
  · exact stackResult871_from _
  apply compileWordToStack_cons
  · exact stackResult872_from _
  apply compileWordToStack_cons
  · exact stackResult873_from _
  apply compileWordToStack_cons
  · exact stackResult874_from _
  apply compileWordToStack_cons
  · exact stackResult875_from _
  apply compileWordToStack_cons
  · exact stackResult876_from _
  apply compileWordToStack_cons
  · exact stackResult877_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 4519) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 4603)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 4519 bodies frames bitmapDelta 4603 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 800).take 14).zip
      [oracle864, oracle865, oracle866, oracle867, oracle868, oracle869, oracle870, oracle871, oracle872, oracle873, oracle874, oracle875, oracle876, oracle877]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle864 PrefixChecks.Shard800.entry,
    wordFunction oracle865 PrefixChecks.Shard801.entry,
    wordFunction oracle866 PrefixChecks.Shard802.entry,
    wordFunction oracle867 PrefixChecks.Shard803.entry,
    wordFunction oracle868 PrefixChecks.Shard804.entry,
    wordFunction oracle869 PrefixChecks.Shard805.entry,
    wordFunction oracle870 PrefixChecks.Shard806.entry,
    wordFunction oracle871 PrefixChecks.Shard807.entry,
    wordFunction oracle872 PrefixChecks.Shard808.entry,
    wordFunction oracle873 PrefixChecks.Shard809.entry,
    wordFunction oracle874 PrefixChecks.Shard810.entry,
    wordFunction oracle875 PrefixChecks.Shard811.entry,
    wordFunction oracle876 PrefixChecks.Shard812.entry,
    wordFunction oracle877 PrefixChecks.Shard813.entry] = words
  simp only [
    Word864.wordFunction_eq,
    Word865.wordFunction_eq,
    Word866.wordFunction_eq,
    Word867.wordFunction_eq,
    Word868.wordFunction_eq,
    Word869.wordFunction_eq,
    Word870.wordFunction_eq,
    Word871.wordFunction_eq,
    Word872.wordFunction_eq,
    Word873.wordFunction_eq,
    Word874.wordFunction_eq,
    Word875.wordFunction_eq,
    Word876.wordFunction_eq,
    Word877.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk50
