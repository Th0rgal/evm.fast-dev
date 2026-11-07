import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word416
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word417
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word418
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word419
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word420
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word421
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word422
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word423
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word424
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word425
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word426
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word427
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word428
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word429
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word430
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word431
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk22
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult416 := WordToStack.Native.compileProgNative
  riscvConfig false Word416.program PrefixChecks.Shard352.arity registers (.nil, 1240)
theorem stackResult416_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word416.program
      PrefixChecks.Shard352.arity registers (prefixList, 1240) =
    (stackResult416.1, stackResult416.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult416.2.2.1, 1242)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word416.program
    PrefixChecks.Shard352.arity registers prefixList 1240
    stackResult416.1 stackResult416.2.1 stackResult416.2.2.1 1242 stackResult416_eq
wave8_kernel_reduce stackResult417 := WordToStack.Native.compileProgNative
  riscvConfig false Word417.program PrefixChecks.Shard353.arity registers (.nil, 1242)
theorem stackResult417_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word417.program
      PrefixChecks.Shard353.arity registers (prefixList, 1242) =
    (stackResult417.1, stackResult417.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult417.2.2.1, 1244)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word417.program
    PrefixChecks.Shard353.arity registers prefixList 1242
    stackResult417.1 stackResult417.2.1 stackResult417.2.2.1 1244 stackResult417_eq
wave8_kernel_reduce stackResult418 := WordToStack.Native.compileProgNative
  riscvConfig false Word418.program PrefixChecks.Shard354.arity registers (.nil, 1244)
theorem stackResult418_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word418.program
      PrefixChecks.Shard354.arity registers (prefixList, 1244) =
    (stackResult418.1, stackResult418.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult418.2.2.1, 1246)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word418.program
    PrefixChecks.Shard354.arity registers prefixList 1244
    stackResult418.1 stackResult418.2.1 stackResult418.2.2.1 1246 stackResult418_eq
wave8_kernel_reduce stackResult419 := WordToStack.Native.compileProgNative
  riscvConfig false Word419.program PrefixChecks.Shard355.arity registers (.nil, 1246)
theorem stackResult419_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word419.program
      PrefixChecks.Shard355.arity registers (prefixList, 1246) =
    (stackResult419.1, stackResult419.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult419.2.2.1, 1247)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word419.program
    PrefixChecks.Shard355.arity registers prefixList 1246
    stackResult419.1 stackResult419.2.1 stackResult419.2.2.1 1247 stackResult419_eq
wave8_kernel_reduce stackResult420 := WordToStack.Native.compileProgNative
  riscvConfig false Word420.program PrefixChecks.Shard356.arity registers (.nil, 1247)
theorem stackResult420_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word420.program
      PrefixChecks.Shard356.arity registers (prefixList, 1247) =
    (stackResult420.1, stackResult420.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult420.2.2.1, 1253)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word420.program
    PrefixChecks.Shard356.arity registers prefixList 1247
    stackResult420.1 stackResult420.2.1 stackResult420.2.2.1 1253 stackResult420_eq
wave8_kernel_reduce stackResult421 := WordToStack.Native.compileProgNative
  riscvConfig false Word421.program PrefixChecks.Shard357.arity registers (.nil, 1253)
theorem stackResult421_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word421.program
      PrefixChecks.Shard357.arity registers (prefixList, 1253) =
    (stackResult421.1, stackResult421.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult421.2.2.1, 1258)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word421.program
    PrefixChecks.Shard357.arity registers prefixList 1253
    stackResult421.1 stackResult421.2.1 stackResult421.2.2.1 1258 stackResult421_eq
wave8_kernel_reduce stackResult422 := WordToStack.Native.compileProgNative
  riscvConfig false Word422.program PrefixChecks.Shard358.arity registers (.nil, 1258)
theorem stackResult422_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word422.program
      PrefixChecks.Shard358.arity registers (prefixList, 1258) =
    (stackResult422.1, stackResult422.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult422.2.2.1, 1260)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word422.program
    PrefixChecks.Shard358.arity registers prefixList 1258
    stackResult422.1 stackResult422.2.1 stackResult422.2.2.1 1260 stackResult422_eq
wave8_kernel_reduce stackResult423 := WordToStack.Native.compileProgNative
  riscvConfig false Word423.program PrefixChecks.Shard359.arity registers (.nil, 1260)
theorem stackResult423_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word423.program
      PrefixChecks.Shard359.arity registers (prefixList, 1260) =
    (stackResult423.1, stackResult423.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult423.2.2.1, 1263)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word423.program
    PrefixChecks.Shard359.arity registers prefixList 1260
    stackResult423.1 stackResult423.2.1 stackResult423.2.2.1 1263 stackResult423_eq
wave8_kernel_reduce stackResult424 := WordToStack.Native.compileProgNative
  riscvConfig false Word424.program PrefixChecks.Shard360.arity registers (.nil, 1263)
theorem stackResult424_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word424.program
      PrefixChecks.Shard360.arity registers (prefixList, 1263) =
    (stackResult424.1, stackResult424.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult424.2.2.1, 1267)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word424.program
    PrefixChecks.Shard360.arity registers prefixList 1263
    stackResult424.1 stackResult424.2.1 stackResult424.2.2.1 1267 stackResult424_eq
wave8_kernel_reduce stackResult425 := WordToStack.Native.compileProgNative
  riscvConfig false Word425.program PrefixChecks.Shard361.arity registers (.nil, 1267)
theorem stackResult425_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word425.program
      PrefixChecks.Shard361.arity registers (prefixList, 1267) =
    (stackResult425.1, stackResult425.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult425.2.2.1, 1268)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word425.program
    PrefixChecks.Shard361.arity registers prefixList 1267
    stackResult425.1 stackResult425.2.1 stackResult425.2.2.1 1268 stackResult425_eq
wave8_kernel_reduce stackResult426 := WordToStack.Native.compileProgNative
  riscvConfig false Word426.program PrefixChecks.Shard362.arity registers (.nil, 1268)
theorem stackResult426_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word426.program
      PrefixChecks.Shard362.arity registers (prefixList, 1268) =
    (stackResult426.1, stackResult426.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult426.2.2.1, 1273)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word426.program
    PrefixChecks.Shard362.arity registers prefixList 1268
    stackResult426.1 stackResult426.2.1 stackResult426.2.2.1 1273 stackResult426_eq
wave8_kernel_reduce stackResult427 := WordToStack.Native.compileProgNative
  riscvConfig false Word427.program PrefixChecks.Shard363.arity registers (.nil, 1273)
theorem stackResult427_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word427.program
      PrefixChecks.Shard363.arity registers (prefixList, 1273) =
    (stackResult427.1, stackResult427.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult427.2.2.1, 1282)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word427.program
    PrefixChecks.Shard363.arity registers prefixList 1273
    stackResult427.1 stackResult427.2.1 stackResult427.2.2.1 1282 stackResult427_eq
wave8_kernel_reduce stackResult428 := WordToStack.Native.compileProgNative
  riscvConfig false Word428.program PrefixChecks.Shard364.arity registers (.nil, 1282)
theorem stackResult428_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word428.program
      PrefixChecks.Shard364.arity registers (prefixList, 1282) =
    (stackResult428.1, stackResult428.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult428.2.2.1, 1286)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word428.program
    PrefixChecks.Shard364.arity registers prefixList 1282
    stackResult428.1 stackResult428.2.1 stackResult428.2.2.1 1286 stackResult428_eq
wave8_kernel_reduce stackResult429 := WordToStack.Native.compileProgNative
  riscvConfig false Word429.program PrefixChecks.Shard365.arity registers (.nil, 1286)
theorem stackResult429_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word429.program
      PrefixChecks.Shard365.arity registers (prefixList, 1286) =
    (stackResult429.1, stackResult429.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult429.2.2.1, 1289)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word429.program
    PrefixChecks.Shard365.arity registers prefixList 1286
    stackResult429.1 stackResult429.2.1 stackResult429.2.2.1 1289 stackResult429_eq
wave8_kernel_reduce stackResult430 := WordToStack.Native.compileProgNative
  riscvConfig false Word430.program PrefixChecks.Shard366.arity registers (.nil, 1289)
theorem stackResult430_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word430.program
      PrefixChecks.Shard366.arity registers (prefixList, 1289) =
    (stackResult430.1, stackResult430.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult430.2.2.1, 1292)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word430.program
    PrefixChecks.Shard366.arity registers prefixList 1289
    stackResult430.1 stackResult430.2.1 stackResult430.2.2.1 1292 stackResult430_eq
wave8_kernel_reduce stackResult431 := WordToStack.Native.compileProgNative
  riscvConfig false Word431.program PrefixChecks.Shard367.arity registers (.nil, 1292)
theorem stackResult431_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word431.program
      PrefixChecks.Shard367.arity registers (prefixList, 1292) =
    (stackResult431.1, stackResult431.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult431.2.2.1, 1300)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word431.program
    PrefixChecks.Shard367.arity registers prefixList 1292
    stackResult431.1 stackResult431.2.1 stackResult431.2.2.1 1300 stackResult431_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard352.name, PrefixChecks.Shard352.arity, Word416.program),
  (PrefixChecks.Shard353.name, PrefixChecks.Shard353.arity, Word417.program),
  (PrefixChecks.Shard354.name, PrefixChecks.Shard354.arity, Word418.program),
  (PrefixChecks.Shard355.name, PrefixChecks.Shard355.arity, Word419.program),
  (PrefixChecks.Shard356.name, PrefixChecks.Shard356.arity, Word420.program),
  (PrefixChecks.Shard357.name, PrefixChecks.Shard357.arity, Word421.program),
  (PrefixChecks.Shard358.name, PrefixChecks.Shard358.arity, Word422.program),
  (PrefixChecks.Shard359.name, PrefixChecks.Shard359.arity, Word423.program),
  (PrefixChecks.Shard360.name, PrefixChecks.Shard360.arity, Word424.program),
  (PrefixChecks.Shard361.name, PrefixChecks.Shard361.arity, Word425.program),
  (PrefixChecks.Shard362.name, PrefixChecks.Shard362.arity, Word426.program),
  (PrefixChecks.Shard363.name, PrefixChecks.Shard363.arity, Word427.program),
  (PrefixChecks.Shard364.name, PrefixChecks.Shard364.arity, Word428.program),
  (PrefixChecks.Shard365.name, PrefixChecks.Shard365.arity, Word429.program),
  (PrefixChecks.Shard366.name, PrefixChecks.Shard366.arity, Word430.program),
  (PrefixChecks.Shard367.name, PrefixChecks.Shard367.arity, Word431.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard352.name, stackResult416.1),
  (PrefixChecks.Shard353.name, stackResult417.1),
  (PrefixChecks.Shard354.name, stackResult418.1),
  (PrefixChecks.Shard355.name, stackResult419.1),
  (PrefixChecks.Shard356.name, stackResult420.1),
  (PrefixChecks.Shard357.name, stackResult421.1),
  (PrefixChecks.Shard358.name, stackResult422.1),
  (PrefixChecks.Shard359.name, stackResult423.1),
  (PrefixChecks.Shard360.name, stackResult424.1),
  (PrefixChecks.Shard361.name, stackResult425.1),
  (PrefixChecks.Shard362.name, stackResult426.1),
  (PrefixChecks.Shard363.name, stackResult427.1),
  (PrefixChecks.Shard364.name, stackResult428.1),
  (PrefixChecks.Shard365.name, stackResult429.1),
  (PrefixChecks.Shard366.name, stackResult430.1),
  (PrefixChecks.Shard367.name, stackResult431.1)
]

noncomputable def frames : List Nat := [
  stackResult416.2.1,
  stackResult417.2.1,
  stackResult418.2.1,
  stackResult419.2.1,
  stackResult420.2.1,
  stackResult421.2.1,
  stackResult422.2.1,
  stackResult423.2.1,
  stackResult424.2.1,
  stackResult425.2.1,
  stackResult426.2.1,
  stackResult427.2.1,
  stackResult428.2.1,
  stackResult429.2.1,
  stackResult430.2.1,
  stackResult431.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult416.2.2.1) stackResult417.2.2.1) stackResult418.2.2.1) stackResult419.2.2.1) stackResult420.2.2.1) stackResult421.2.2.1) stackResult422.2.2.1) stackResult423.2.2.1) stackResult424.2.2.1) stackResult425.2.2.1) stackResult426.2.2.1) stackResult427.2.2.1) stackResult428.2.2.1) stackResult429.2.2.1) stackResult430.2.2.1) stackResult431.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 1240) = (bodies, frames, (bitmapDelta, 1300)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult416_from _
  apply compileWordToStack_cons
  · exact stackResult417_from _
  apply compileWordToStack_cons
  · exact stackResult418_from _
  apply compileWordToStack_cons
  · exact stackResult419_from _
  apply compileWordToStack_cons
  · exact stackResult420_from _
  apply compileWordToStack_cons
  · exact stackResult421_from _
  apply compileWordToStack_cons
  · exact stackResult422_from _
  apply compileWordToStack_cons
  · exact stackResult423_from _
  apply compileWordToStack_cons
  · exact stackResult424_from _
  apply compileWordToStack_cons
  · exact stackResult425_from _
  apply compileWordToStack_cons
  · exact stackResult426_from _
  apply compileWordToStack_cons
  · exact stackResult427_from _
  apply compileWordToStack_cons
  · exact stackResult428_from _
  apply compileWordToStack_cons
  · exact stackResult429_from _
  apply compileWordToStack_cons
  · exact stackResult430_from _
  apply compileWordToStack_cons
  · exact stackResult431_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 1240) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 1300)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 1240 bodies frames bitmapDelta 1300 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 352).take 16).zip
      [oracle416, oracle417, oracle418, oracle419, oracle420, oracle421, oracle422, oracle423, oracle424, oracle425, oracle426, oracle427, oracle428, oracle429, oracle430, oracle431]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle416 PrefixChecks.Shard352.entry,
    wordFunction oracle417 PrefixChecks.Shard353.entry,
    wordFunction oracle418 PrefixChecks.Shard354.entry,
    wordFunction oracle419 PrefixChecks.Shard355.entry,
    wordFunction oracle420 PrefixChecks.Shard356.entry,
    wordFunction oracle421 PrefixChecks.Shard357.entry,
    wordFunction oracle422 PrefixChecks.Shard358.entry,
    wordFunction oracle423 PrefixChecks.Shard359.entry,
    wordFunction oracle424 PrefixChecks.Shard360.entry,
    wordFunction oracle425 PrefixChecks.Shard361.entry,
    wordFunction oracle426 PrefixChecks.Shard362.entry,
    wordFunction oracle427 PrefixChecks.Shard363.entry,
    wordFunction oracle428 PrefixChecks.Shard364.entry,
    wordFunction oracle429 PrefixChecks.Shard365.entry,
    wordFunction oracle430 PrefixChecks.Shard366.entry,
    wordFunction oracle431 PrefixChecks.Shard367.entry] = words
  simp only [
    Word416.wordFunction_eq,
    Word417.wordFunction_eq,
    Word418.wordFunction_eq,
    Word419.wordFunction_eq,
    Word420.wordFunction_eq,
    Word421.wordFunction_eq,
    Word422.wordFunction_eq,
    Word423.wordFunction_eq,
    Word424.wordFunction_eq,
    Word425.wordFunction_eq,
    Word426.wordFunction_eq,
    Word427.wordFunction_eq,
    Word428.wordFunction_eq,
    Word429.wordFunction_eq,
    Word430.wordFunction_eq,
    Word431.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk22
