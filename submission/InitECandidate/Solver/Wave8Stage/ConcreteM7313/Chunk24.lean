import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word448
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word449
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word450
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word451
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word452
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word453
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word454
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word455
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word456
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word457
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word458
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word459
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word460
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word461
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word462
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word463
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk24
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult448 := WordToStack.Native.compileProgNative
  riscvConfig false Word448.program PrefixChecks.Shard384.arity registers (.nil, 1348)
theorem stackResult448_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word448.program
      PrefixChecks.Shard384.arity registers (prefixList, 1348) =
    (stackResult448.1, stackResult448.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult448.2.2.1, 1351)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word448.program
    PrefixChecks.Shard384.arity registers prefixList 1348
    stackResult448.1 stackResult448.2.1 stackResult448.2.2.1 1351 stackResult448_eq
wave8_kernel_reduce stackResult449 := WordToStack.Native.compileProgNative
  riscvConfig false Word449.program PrefixChecks.Shard385.arity registers (.nil, 1351)
theorem stackResult449_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word449.program
      PrefixChecks.Shard385.arity registers (prefixList, 1351) =
    (stackResult449.1, stackResult449.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult449.2.2.1, 1362)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word449.program
    PrefixChecks.Shard385.arity registers prefixList 1351
    stackResult449.1 stackResult449.2.1 stackResult449.2.2.1 1362 stackResult449_eq
wave8_kernel_reduce stackResult450 := WordToStack.Native.compileProgNative
  riscvConfig false Word450.program PrefixChecks.Shard386.arity registers (.nil, 1362)
theorem stackResult450_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word450.program
      PrefixChecks.Shard386.arity registers (prefixList, 1362) =
    (stackResult450.1, stackResult450.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult450.2.2.1, 1372)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word450.program
    PrefixChecks.Shard386.arity registers prefixList 1362
    stackResult450.1 stackResult450.2.1 stackResult450.2.2.1 1372 stackResult450_eq
wave8_kernel_reduce stackResult451 := WordToStack.Native.compileProgNative
  riscvConfig false Word451.program PrefixChecks.Shard387.arity registers (.nil, 1372)
theorem stackResult451_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word451.program
      PrefixChecks.Shard387.arity registers (prefixList, 1372) =
    (stackResult451.1, stackResult451.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult451.2.2.1, 1373)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word451.program
    PrefixChecks.Shard387.arity registers prefixList 1372
    stackResult451.1 stackResult451.2.1 stackResult451.2.2.1 1373 stackResult451_eq
wave8_kernel_reduce stackResult452 := WordToStack.Native.compileProgNative
  riscvConfig false Word452.program PrefixChecks.Shard388.arity registers (.nil, 1373)
theorem stackResult452_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word452.program
      PrefixChecks.Shard388.arity registers (prefixList, 1373) =
    (stackResult452.1, stackResult452.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult452.2.2.1, 1375)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word452.program
    PrefixChecks.Shard388.arity registers prefixList 1373
    stackResult452.1 stackResult452.2.1 stackResult452.2.2.1 1375 stackResult452_eq
wave8_kernel_reduce stackResult453 := WordToStack.Native.compileProgNative
  riscvConfig false Word453.program PrefixChecks.Shard389.arity registers (.nil, 1375)
theorem stackResult453_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word453.program
      PrefixChecks.Shard389.arity registers (prefixList, 1375) =
    (stackResult453.1, stackResult453.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult453.2.2.1, 1379)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word453.program
    PrefixChecks.Shard389.arity registers prefixList 1375
    stackResult453.1 stackResult453.2.1 stackResult453.2.2.1 1379 stackResult453_eq
wave8_kernel_reduce stackResult454 := WordToStack.Native.compileProgNative
  riscvConfig false Word454.program PrefixChecks.Shard390.arity registers (.nil, 1379)
theorem stackResult454_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word454.program
      PrefixChecks.Shard390.arity registers (prefixList, 1379) =
    (stackResult454.1, stackResult454.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult454.2.2.1, 1396)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word454.program
    PrefixChecks.Shard390.arity registers prefixList 1379
    stackResult454.1 stackResult454.2.1 stackResult454.2.2.1 1396 stackResult454_eq
wave8_kernel_reduce stackResult455 := WordToStack.Native.compileProgNative
  riscvConfig false Word455.program PrefixChecks.Shard391.arity registers (.nil, 1396)
theorem stackResult455_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word455.program
      PrefixChecks.Shard391.arity registers (prefixList, 1396) =
    (stackResult455.1, stackResult455.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult455.2.2.1, 1398)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word455.program
    PrefixChecks.Shard391.arity registers prefixList 1396
    stackResult455.1 stackResult455.2.1 stackResult455.2.2.1 1398 stackResult455_eq
wave8_kernel_reduce stackResult456 := WordToStack.Native.compileProgNative
  riscvConfig false Word456.program PrefixChecks.Shard392.arity registers (.nil, 1398)
theorem stackResult456_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word456.program
      PrefixChecks.Shard392.arity registers (prefixList, 1398) =
    (stackResult456.1, stackResult456.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult456.2.2.1, 1398)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word456.program
    PrefixChecks.Shard392.arity registers prefixList 1398
    stackResult456.1 stackResult456.2.1 stackResult456.2.2.1 1398 stackResult456_eq
wave8_kernel_reduce stackResult457 := WordToStack.Native.compileProgNative
  riscvConfig false Word457.program PrefixChecks.Shard393.arity registers (.nil, 1398)
theorem stackResult457_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word457.program
      PrefixChecks.Shard393.arity registers (prefixList, 1398) =
    (stackResult457.1, stackResult457.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult457.2.2.1, 1407)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word457.program
    PrefixChecks.Shard393.arity registers prefixList 1398
    stackResult457.1 stackResult457.2.1 stackResult457.2.2.1 1407 stackResult457_eq
wave8_kernel_reduce stackResult458 := WordToStack.Native.compileProgNative
  riscvConfig false Word458.program PrefixChecks.Shard394.arity registers (.nil, 1407)
theorem stackResult458_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word458.program
      PrefixChecks.Shard394.arity registers (prefixList, 1407) =
    (stackResult458.1, stackResult458.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult458.2.2.1, 1409)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word458.program
    PrefixChecks.Shard394.arity registers prefixList 1407
    stackResult458.1 stackResult458.2.1 stackResult458.2.2.1 1409 stackResult458_eq
wave8_kernel_reduce stackResult459 := WordToStack.Native.compileProgNative
  riscvConfig false Word459.program PrefixChecks.Shard395.arity registers (.nil, 1409)
theorem stackResult459_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word459.program
      PrefixChecks.Shard395.arity registers (prefixList, 1409) =
    (stackResult459.1, stackResult459.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult459.2.2.1, 1469)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word459.program
    PrefixChecks.Shard395.arity registers prefixList 1409
    stackResult459.1 stackResult459.2.1 stackResult459.2.2.1 1469 stackResult459_eq
wave8_kernel_reduce stackResult460 := WordToStack.Native.compileProgNative
  riscvConfig false Word460.program PrefixChecks.Shard396.arity registers (.nil, 1469)
theorem stackResult460_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word460.program
      PrefixChecks.Shard396.arity registers (prefixList, 1469) =
    (stackResult460.1, stackResult460.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult460.2.2.1, 1483)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word460.program
    PrefixChecks.Shard396.arity registers prefixList 1469
    stackResult460.1 stackResult460.2.1 stackResult460.2.2.1 1483 stackResult460_eq
wave8_kernel_reduce stackResult461 := WordToStack.Native.compileProgNative
  riscvConfig false Word461.program PrefixChecks.Shard397.arity registers (.nil, 1483)
theorem stackResult461_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word461.program
      PrefixChecks.Shard397.arity registers (prefixList, 1483) =
    (stackResult461.1, stackResult461.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult461.2.2.1, 1487)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word461.program
    PrefixChecks.Shard397.arity registers prefixList 1483
    stackResult461.1 stackResult461.2.1 stackResult461.2.2.1 1487 stackResult461_eq
wave8_kernel_reduce stackResult462 := WordToStack.Native.compileProgNative
  riscvConfig false Word462.program PrefixChecks.Shard398.arity registers (.nil, 1487)
theorem stackResult462_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word462.program
      PrefixChecks.Shard398.arity registers (prefixList, 1487) =
    (stackResult462.1, stackResult462.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult462.2.2.1, 1487)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word462.program
    PrefixChecks.Shard398.arity registers prefixList 1487
    stackResult462.1 stackResult462.2.1 stackResult462.2.2.1 1487 stackResult462_eq
wave8_kernel_reduce stackResult463 := WordToStack.Native.compileProgNative
  riscvConfig false Word463.program PrefixChecks.Shard399.arity registers (.nil, 1487)
theorem stackResult463_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word463.program
      PrefixChecks.Shard399.arity registers (prefixList, 1487) =
    (stackResult463.1, stackResult463.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult463.2.2.1, 1487)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word463.program
    PrefixChecks.Shard399.arity registers prefixList 1487
    stackResult463.1 stackResult463.2.1 stackResult463.2.2.1 1487 stackResult463_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard384.name, PrefixChecks.Shard384.arity, Word448.program),
  (PrefixChecks.Shard385.name, PrefixChecks.Shard385.arity, Word449.program),
  (PrefixChecks.Shard386.name, PrefixChecks.Shard386.arity, Word450.program),
  (PrefixChecks.Shard387.name, PrefixChecks.Shard387.arity, Word451.program),
  (PrefixChecks.Shard388.name, PrefixChecks.Shard388.arity, Word452.program),
  (PrefixChecks.Shard389.name, PrefixChecks.Shard389.arity, Word453.program),
  (PrefixChecks.Shard390.name, PrefixChecks.Shard390.arity, Word454.program),
  (PrefixChecks.Shard391.name, PrefixChecks.Shard391.arity, Word455.program),
  (PrefixChecks.Shard392.name, PrefixChecks.Shard392.arity, Word456.program),
  (PrefixChecks.Shard393.name, PrefixChecks.Shard393.arity, Word457.program),
  (PrefixChecks.Shard394.name, PrefixChecks.Shard394.arity, Word458.program),
  (PrefixChecks.Shard395.name, PrefixChecks.Shard395.arity, Word459.program),
  (PrefixChecks.Shard396.name, PrefixChecks.Shard396.arity, Word460.program),
  (PrefixChecks.Shard397.name, PrefixChecks.Shard397.arity, Word461.program),
  (PrefixChecks.Shard398.name, PrefixChecks.Shard398.arity, Word462.program),
  (PrefixChecks.Shard399.name, PrefixChecks.Shard399.arity, Word463.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard384.name, stackResult448.1),
  (PrefixChecks.Shard385.name, stackResult449.1),
  (PrefixChecks.Shard386.name, stackResult450.1),
  (PrefixChecks.Shard387.name, stackResult451.1),
  (PrefixChecks.Shard388.name, stackResult452.1),
  (PrefixChecks.Shard389.name, stackResult453.1),
  (PrefixChecks.Shard390.name, stackResult454.1),
  (PrefixChecks.Shard391.name, stackResult455.1),
  (PrefixChecks.Shard392.name, stackResult456.1),
  (PrefixChecks.Shard393.name, stackResult457.1),
  (PrefixChecks.Shard394.name, stackResult458.1),
  (PrefixChecks.Shard395.name, stackResult459.1),
  (PrefixChecks.Shard396.name, stackResult460.1),
  (PrefixChecks.Shard397.name, stackResult461.1),
  (PrefixChecks.Shard398.name, stackResult462.1),
  (PrefixChecks.Shard399.name, stackResult463.1)
]

noncomputable def frames : List Nat := [
  stackResult448.2.1,
  stackResult449.2.1,
  stackResult450.2.1,
  stackResult451.2.1,
  stackResult452.2.1,
  stackResult453.2.1,
  stackResult454.2.1,
  stackResult455.2.1,
  stackResult456.2.1,
  stackResult457.2.1,
  stackResult458.2.1,
  stackResult459.2.1,
  stackResult460.2.1,
  stackResult461.2.1,
  stackResult462.2.1,
  stackResult463.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult448.2.2.1) stackResult449.2.2.1) stackResult450.2.2.1) stackResult451.2.2.1) stackResult452.2.2.1) stackResult453.2.2.1) stackResult454.2.2.1) stackResult455.2.2.1) stackResult456.2.2.1) stackResult457.2.2.1) stackResult458.2.2.1) stackResult459.2.2.1) stackResult460.2.2.1) stackResult461.2.2.1) stackResult462.2.2.1) stackResult463.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 1348) = (bodies, frames, (bitmapDelta, 1487)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult448_from _
  apply compileWordToStack_cons
  · exact stackResult449_from _
  apply compileWordToStack_cons
  · exact stackResult450_from _
  apply compileWordToStack_cons
  · exact stackResult451_from _
  apply compileWordToStack_cons
  · exact stackResult452_from _
  apply compileWordToStack_cons
  · exact stackResult453_from _
  apply compileWordToStack_cons
  · exact stackResult454_from _
  apply compileWordToStack_cons
  · exact stackResult455_from _
  apply compileWordToStack_cons
  · exact stackResult456_from _
  apply compileWordToStack_cons
  · exact stackResult457_from _
  apply compileWordToStack_cons
  · exact stackResult458_from _
  apply compileWordToStack_cons
  · exact stackResult459_from _
  apply compileWordToStack_cons
  · exact stackResult460_from _
  apply compileWordToStack_cons
  · exact stackResult461_from _
  apply compileWordToStack_cons
  · exact stackResult462_from _
  apply compileWordToStack_cons
  · exact stackResult463_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 1348) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 1487)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 1348 bodies frames bitmapDelta 1487 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 384).take 16).zip
      [oracle448, oracle449, oracle450, oracle451, oracle452, oracle453, oracle454, oracle455, oracle456, oracle457, oracle458, oracle459, oracle460, oracle461, oracle462, oracle463]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle448 PrefixChecks.Shard384.entry,
    wordFunction oracle449 PrefixChecks.Shard385.entry,
    wordFunction oracle450 PrefixChecks.Shard386.entry,
    wordFunction oracle451 PrefixChecks.Shard387.entry,
    wordFunction oracle452 PrefixChecks.Shard388.entry,
    wordFunction oracle453 PrefixChecks.Shard389.entry,
    wordFunction oracle454 PrefixChecks.Shard390.entry,
    wordFunction oracle455 PrefixChecks.Shard391.entry,
    wordFunction oracle456 PrefixChecks.Shard392.entry,
    wordFunction oracle457 PrefixChecks.Shard393.entry,
    wordFunction oracle458 PrefixChecks.Shard394.entry,
    wordFunction oracle459 PrefixChecks.Shard395.entry,
    wordFunction oracle460 PrefixChecks.Shard396.entry,
    wordFunction oracle461 PrefixChecks.Shard397.entry,
    wordFunction oracle462 PrefixChecks.Shard398.entry,
    wordFunction oracle463 PrefixChecks.Shard399.entry] = words
  simp only [
    Word448.wordFunction_eq,
    Word449.wordFunction_eq,
    Word450.wordFunction_eq,
    Word451.wordFunction_eq,
    Word452.wordFunction_eq,
    Word453.wordFunction_eq,
    Word454.wordFunction_eq,
    Word455.wordFunction_eq,
    Word456.wordFunction_eq,
    Word457.wordFunction_eq,
    Word458.wordFunction_eq,
    Word459.wordFunction_eq,
    Word460.wordFunction_eq,
    Word461.wordFunction_eq,
    Word462.wordFunction_eq,
    Word463.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk24
