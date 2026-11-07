import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word400
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word401
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word402
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word403
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word404
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word405
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word406
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word407
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word408
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word409
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word410
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word411
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word412
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word413
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word414
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word415
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk21
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult400 := WordToStack.Native.compileProgNative
  riscvConfig false Word400.program PrefixChecks.Shard336.arity registers (.nil, 1184)
theorem stackResult400_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word400.program
      PrefixChecks.Shard336.arity registers (prefixList, 1184) =
    (stackResult400.1, stackResult400.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult400.2.2.1, 1187)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word400.program
    PrefixChecks.Shard336.arity registers prefixList 1184
    stackResult400.1 stackResult400.2.1 stackResult400.2.2.1 1187 stackResult400_eq
wave8_kernel_reduce stackResult401 := WordToStack.Native.compileProgNative
  riscvConfig false Word401.program PrefixChecks.Shard337.arity registers (.nil, 1187)
theorem stackResult401_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word401.program
      PrefixChecks.Shard337.arity registers (prefixList, 1187) =
    (stackResult401.1, stackResult401.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult401.2.2.1, 1197)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word401.program
    PrefixChecks.Shard337.arity registers prefixList 1187
    stackResult401.1 stackResult401.2.1 stackResult401.2.2.1 1197 stackResult401_eq
wave8_kernel_reduce stackResult402 := WordToStack.Native.compileProgNative
  riscvConfig false Word402.program PrefixChecks.Shard338.arity registers (.nil, 1197)
theorem stackResult402_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word402.program
      PrefixChecks.Shard338.arity registers (prefixList, 1197) =
    (stackResult402.1, stackResult402.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult402.2.2.1, 1199)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word402.program
    PrefixChecks.Shard338.arity registers prefixList 1197
    stackResult402.1 stackResult402.2.1 stackResult402.2.2.1 1199 stackResult402_eq
wave8_kernel_reduce stackResult403 := WordToStack.Native.compileProgNative
  riscvConfig false Word403.program PrefixChecks.Shard339.arity registers (.nil, 1199)
theorem stackResult403_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word403.program
      PrefixChecks.Shard339.arity registers (prefixList, 1199) =
    (stackResult403.1, stackResult403.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult403.2.2.1, 1201)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word403.program
    PrefixChecks.Shard339.arity registers prefixList 1199
    stackResult403.1 stackResult403.2.1 stackResult403.2.2.1 1201 stackResult403_eq
wave8_kernel_reduce stackResult404 := WordToStack.Native.compileProgNative
  riscvConfig false Word404.program PrefixChecks.Shard340.arity registers (.nil, 1201)
theorem stackResult404_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word404.program
      PrefixChecks.Shard340.arity registers (prefixList, 1201) =
    (stackResult404.1, stackResult404.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult404.2.2.1, 1205)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word404.program
    PrefixChecks.Shard340.arity registers prefixList 1201
    stackResult404.1 stackResult404.2.1 stackResult404.2.2.1 1205 stackResult404_eq
wave8_kernel_reduce stackResult405 := WordToStack.Native.compileProgNative
  riscvConfig false Word405.program PrefixChecks.Shard341.arity registers (.nil, 1205)
theorem stackResult405_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word405.program
      PrefixChecks.Shard341.arity registers (prefixList, 1205) =
    (stackResult405.1, stackResult405.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult405.2.2.1, 1207)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word405.program
    PrefixChecks.Shard341.arity registers prefixList 1205
    stackResult405.1 stackResult405.2.1 stackResult405.2.2.1 1207 stackResult405_eq
wave8_kernel_reduce stackResult406 := WordToStack.Native.compileProgNative
  riscvConfig false Word406.program PrefixChecks.Shard342.arity registers (.nil, 1207)
theorem stackResult406_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word406.program
      PrefixChecks.Shard342.arity registers (prefixList, 1207) =
    (stackResult406.1, stackResult406.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult406.2.2.1, 1210)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word406.program
    PrefixChecks.Shard342.arity registers prefixList 1207
    stackResult406.1 stackResult406.2.1 stackResult406.2.2.1 1210 stackResult406_eq
wave8_kernel_reduce stackResult407 := WordToStack.Native.compileProgNative
  riscvConfig false Word407.program PrefixChecks.Shard343.arity registers (.nil, 1210)
theorem stackResult407_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word407.program
      PrefixChecks.Shard343.arity registers (prefixList, 1210) =
    (stackResult407.1, stackResult407.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult407.2.2.1, 1212)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word407.program
    PrefixChecks.Shard343.arity registers prefixList 1210
    stackResult407.1 stackResult407.2.1 stackResult407.2.2.1 1212 stackResult407_eq
wave8_kernel_reduce stackResult408 := WordToStack.Native.compileProgNative
  riscvConfig false Word408.program PrefixChecks.Shard344.arity registers (.nil, 1212)
theorem stackResult408_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word408.program
      PrefixChecks.Shard344.arity registers (prefixList, 1212) =
    (stackResult408.1, stackResult408.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult408.2.2.1, 1218)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word408.program
    PrefixChecks.Shard344.arity registers prefixList 1212
    stackResult408.1 stackResult408.2.1 stackResult408.2.2.1 1218 stackResult408_eq
wave8_kernel_reduce stackResult409 := WordToStack.Native.compileProgNative
  riscvConfig false Word409.program PrefixChecks.Shard345.arity registers (.nil, 1218)
theorem stackResult409_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word409.program
      PrefixChecks.Shard345.arity registers (prefixList, 1218) =
    (stackResult409.1, stackResult409.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult409.2.2.1, 1220)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word409.program
    PrefixChecks.Shard345.arity registers prefixList 1218
    stackResult409.1 stackResult409.2.1 stackResult409.2.2.1 1220 stackResult409_eq
wave8_kernel_reduce stackResult410 := WordToStack.Native.compileProgNative
  riscvConfig false Word410.program PrefixChecks.Shard346.arity registers (.nil, 1220)
theorem stackResult410_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word410.program
      PrefixChecks.Shard346.arity registers (prefixList, 1220) =
    (stackResult410.1, stackResult410.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult410.2.2.1, 1226)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word410.program
    PrefixChecks.Shard346.arity registers prefixList 1220
    stackResult410.1 stackResult410.2.1 stackResult410.2.2.1 1226 stackResult410_eq
wave8_kernel_reduce stackResult411 := WordToStack.Native.compileProgNative
  riscvConfig false Word411.program PrefixChecks.Shard347.arity registers (.nil, 1226)
theorem stackResult411_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word411.program
      PrefixChecks.Shard347.arity registers (prefixList, 1226) =
    (stackResult411.1, stackResult411.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult411.2.2.1, 1230)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word411.program
    PrefixChecks.Shard347.arity registers prefixList 1226
    stackResult411.1 stackResult411.2.1 stackResult411.2.2.1 1230 stackResult411_eq
wave8_kernel_reduce stackResult412 := WordToStack.Native.compileProgNative
  riscvConfig false Word412.program PrefixChecks.Shard348.arity registers (.nil, 1230)
theorem stackResult412_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word412.program
      PrefixChecks.Shard348.arity registers (prefixList, 1230) =
    (stackResult412.1, stackResult412.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult412.2.2.1, 1232)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word412.program
    PrefixChecks.Shard348.arity registers prefixList 1230
    stackResult412.1 stackResult412.2.1 stackResult412.2.2.1 1232 stackResult412_eq
wave8_kernel_reduce stackResult413 := WordToStack.Native.compileProgNative
  riscvConfig false Word413.program PrefixChecks.Shard349.arity registers (.nil, 1232)
theorem stackResult413_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word413.program
      PrefixChecks.Shard349.arity registers (prefixList, 1232) =
    (stackResult413.1, stackResult413.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult413.2.2.1, 1233)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word413.program
    PrefixChecks.Shard349.arity registers prefixList 1232
    stackResult413.1 stackResult413.2.1 stackResult413.2.2.1 1233 stackResult413_eq
wave8_kernel_reduce stackResult414 := WordToStack.Native.compileProgNative
  riscvConfig false Word414.program PrefixChecks.Shard350.arity registers (.nil, 1233)
theorem stackResult414_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word414.program
      PrefixChecks.Shard350.arity registers (prefixList, 1233) =
    (stackResult414.1, stackResult414.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult414.2.2.1, 1237)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word414.program
    PrefixChecks.Shard350.arity registers prefixList 1233
    stackResult414.1 stackResult414.2.1 stackResult414.2.2.1 1237 stackResult414_eq
wave8_kernel_reduce stackResult415 := WordToStack.Native.compileProgNative
  riscvConfig false Word415.program PrefixChecks.Shard351.arity registers (.nil, 1237)
theorem stackResult415_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word415.program
      PrefixChecks.Shard351.arity registers (prefixList, 1237) =
    (stackResult415.1, stackResult415.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult415.2.2.1, 1240)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word415.program
    PrefixChecks.Shard351.arity registers prefixList 1237
    stackResult415.1 stackResult415.2.1 stackResult415.2.2.1 1240 stackResult415_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard336.name, PrefixChecks.Shard336.arity, Word400.program),
  (PrefixChecks.Shard337.name, PrefixChecks.Shard337.arity, Word401.program),
  (PrefixChecks.Shard338.name, PrefixChecks.Shard338.arity, Word402.program),
  (PrefixChecks.Shard339.name, PrefixChecks.Shard339.arity, Word403.program),
  (PrefixChecks.Shard340.name, PrefixChecks.Shard340.arity, Word404.program),
  (PrefixChecks.Shard341.name, PrefixChecks.Shard341.arity, Word405.program),
  (PrefixChecks.Shard342.name, PrefixChecks.Shard342.arity, Word406.program),
  (PrefixChecks.Shard343.name, PrefixChecks.Shard343.arity, Word407.program),
  (PrefixChecks.Shard344.name, PrefixChecks.Shard344.arity, Word408.program),
  (PrefixChecks.Shard345.name, PrefixChecks.Shard345.arity, Word409.program),
  (PrefixChecks.Shard346.name, PrefixChecks.Shard346.arity, Word410.program),
  (PrefixChecks.Shard347.name, PrefixChecks.Shard347.arity, Word411.program),
  (PrefixChecks.Shard348.name, PrefixChecks.Shard348.arity, Word412.program),
  (PrefixChecks.Shard349.name, PrefixChecks.Shard349.arity, Word413.program),
  (PrefixChecks.Shard350.name, PrefixChecks.Shard350.arity, Word414.program),
  (PrefixChecks.Shard351.name, PrefixChecks.Shard351.arity, Word415.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard336.name, stackResult400.1),
  (PrefixChecks.Shard337.name, stackResult401.1),
  (PrefixChecks.Shard338.name, stackResult402.1),
  (PrefixChecks.Shard339.name, stackResult403.1),
  (PrefixChecks.Shard340.name, stackResult404.1),
  (PrefixChecks.Shard341.name, stackResult405.1),
  (PrefixChecks.Shard342.name, stackResult406.1),
  (PrefixChecks.Shard343.name, stackResult407.1),
  (PrefixChecks.Shard344.name, stackResult408.1),
  (PrefixChecks.Shard345.name, stackResult409.1),
  (PrefixChecks.Shard346.name, stackResult410.1),
  (PrefixChecks.Shard347.name, stackResult411.1),
  (PrefixChecks.Shard348.name, stackResult412.1),
  (PrefixChecks.Shard349.name, stackResult413.1),
  (PrefixChecks.Shard350.name, stackResult414.1),
  (PrefixChecks.Shard351.name, stackResult415.1)
]

noncomputable def frames : List Nat := [
  stackResult400.2.1,
  stackResult401.2.1,
  stackResult402.2.1,
  stackResult403.2.1,
  stackResult404.2.1,
  stackResult405.2.1,
  stackResult406.2.1,
  stackResult407.2.1,
  stackResult408.2.1,
  stackResult409.2.1,
  stackResult410.2.1,
  stackResult411.2.1,
  stackResult412.2.1,
  stackResult413.2.1,
  stackResult414.2.1,
  stackResult415.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult400.2.2.1) stackResult401.2.2.1) stackResult402.2.2.1) stackResult403.2.2.1) stackResult404.2.2.1) stackResult405.2.2.1) stackResult406.2.2.1) stackResult407.2.2.1) stackResult408.2.2.1) stackResult409.2.2.1) stackResult410.2.2.1) stackResult411.2.2.1) stackResult412.2.2.1) stackResult413.2.2.1) stackResult414.2.2.1) stackResult415.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 1184) = (bodies, frames, (bitmapDelta, 1240)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult400_from _
  apply compileWordToStack_cons
  · exact stackResult401_from _
  apply compileWordToStack_cons
  · exact stackResult402_from _
  apply compileWordToStack_cons
  · exact stackResult403_from _
  apply compileWordToStack_cons
  · exact stackResult404_from _
  apply compileWordToStack_cons
  · exact stackResult405_from _
  apply compileWordToStack_cons
  · exact stackResult406_from _
  apply compileWordToStack_cons
  · exact stackResult407_from _
  apply compileWordToStack_cons
  · exact stackResult408_from _
  apply compileWordToStack_cons
  · exact stackResult409_from _
  apply compileWordToStack_cons
  · exact stackResult410_from _
  apply compileWordToStack_cons
  · exact stackResult411_from _
  apply compileWordToStack_cons
  · exact stackResult412_from _
  apply compileWordToStack_cons
  · exact stackResult413_from _
  apply compileWordToStack_cons
  · exact stackResult414_from _
  apply compileWordToStack_cons
  · exact stackResult415_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 1184) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 1240)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 1184 bodies frames bitmapDelta 1240 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 336).take 16).zip
      [oracle400, oracle401, oracle402, oracle403, oracle404, oracle405, oracle406, oracle407, oracle408, oracle409, oracle410, oracle411, oracle412, oracle413, oracle414, oracle415]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle400 PrefixChecks.Shard336.entry,
    wordFunction oracle401 PrefixChecks.Shard337.entry,
    wordFunction oracle402 PrefixChecks.Shard338.entry,
    wordFunction oracle403 PrefixChecks.Shard339.entry,
    wordFunction oracle404 PrefixChecks.Shard340.entry,
    wordFunction oracle405 PrefixChecks.Shard341.entry,
    wordFunction oracle406 PrefixChecks.Shard342.entry,
    wordFunction oracle407 PrefixChecks.Shard343.entry,
    wordFunction oracle408 PrefixChecks.Shard344.entry,
    wordFunction oracle409 PrefixChecks.Shard345.entry,
    wordFunction oracle410 PrefixChecks.Shard346.entry,
    wordFunction oracle411 PrefixChecks.Shard347.entry,
    wordFunction oracle412 PrefixChecks.Shard348.entry,
    wordFunction oracle413 PrefixChecks.Shard349.entry,
    wordFunction oracle414 PrefixChecks.Shard350.entry,
    wordFunction oracle415 PrefixChecks.Shard351.entry] = words
  simp only [
    Word400.wordFunction_eq,
    Word401.wordFunction_eq,
    Word402.wordFunction_eq,
    Word403.wordFunction_eq,
    Word404.wordFunction_eq,
    Word405.wordFunction_eq,
    Word406.wordFunction_eq,
    Word407.wordFunction_eq,
    Word408.wordFunction_eq,
    Word409.wordFunction_eq,
    Word410.wordFunction_eq,
    Word411.wordFunction_eq,
    Word412.wordFunction_eq,
    Word413.wordFunction_eq,
    Word414.wordFunction_eq,
    Word415.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk21
