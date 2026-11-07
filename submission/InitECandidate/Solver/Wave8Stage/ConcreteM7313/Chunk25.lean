import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word464
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word465
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word466
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word467
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word468
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word469
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word470
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word471
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word472
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word473
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word474
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word475
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word476
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word477
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word478
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word479
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk25
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult464 := WordToStack.Native.compileProgNative
  riscvConfig false Word464.program PrefixChecks.Shard400.arity registers (.nil, 1487)
theorem stackResult464_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word464.program
      PrefixChecks.Shard400.arity registers (prefixList, 1487) =
    (stackResult464.1, stackResult464.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult464.2.2.1, 1488)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word464.program
    PrefixChecks.Shard400.arity registers prefixList 1487
    stackResult464.1 stackResult464.2.1 stackResult464.2.2.1 1488 stackResult464_eq
wave8_kernel_reduce stackResult465 := WordToStack.Native.compileProgNative
  riscvConfig false Word465.program PrefixChecks.Shard401.arity registers (.nil, 1488)
theorem stackResult465_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word465.program
      PrefixChecks.Shard401.arity registers (prefixList, 1488) =
    (stackResult465.1, stackResult465.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult465.2.2.1, 1489)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word465.program
    PrefixChecks.Shard401.arity registers prefixList 1488
    stackResult465.1 stackResult465.2.1 stackResult465.2.2.1 1489 stackResult465_eq
wave8_kernel_reduce stackResult466 := WordToStack.Native.compileProgNative
  riscvConfig false Word466.program PrefixChecks.Shard402.arity registers (.nil, 1489)
theorem stackResult466_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word466.program
      PrefixChecks.Shard402.arity registers (prefixList, 1489) =
    (stackResult466.1, stackResult466.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult466.2.2.1, 1492)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word466.program
    PrefixChecks.Shard402.arity registers prefixList 1489
    stackResult466.1 stackResult466.2.1 stackResult466.2.2.1 1492 stackResult466_eq
wave8_kernel_reduce stackResult467 := WordToStack.Native.compileProgNative
  riscvConfig false Word467.program PrefixChecks.Shard403.arity registers (.nil, 1492)
theorem stackResult467_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word467.program
      PrefixChecks.Shard403.arity registers (prefixList, 1492) =
    (stackResult467.1, stackResult467.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult467.2.2.1, 1493)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word467.program
    PrefixChecks.Shard403.arity registers prefixList 1492
    stackResult467.1 stackResult467.2.1 stackResult467.2.2.1 1493 stackResult467_eq
wave8_kernel_reduce stackResult468 := WordToStack.Native.compileProgNative
  riscvConfig false Word468.program PrefixChecks.Shard404.arity registers (.nil, 1493)
theorem stackResult468_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word468.program
      PrefixChecks.Shard404.arity registers (prefixList, 1493) =
    (stackResult468.1, stackResult468.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult468.2.2.1, 1493)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word468.program
    PrefixChecks.Shard404.arity registers prefixList 1493
    stackResult468.1 stackResult468.2.1 stackResult468.2.2.1 1493 stackResult468_eq
wave8_kernel_reduce stackResult469 := WordToStack.Native.compileProgNative
  riscvConfig false Word469.program PrefixChecks.Shard405.arity registers (.nil, 1493)
theorem stackResult469_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word469.program
      PrefixChecks.Shard405.arity registers (prefixList, 1493) =
    (stackResult469.1, stackResult469.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult469.2.2.1, 1493)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word469.program
    PrefixChecks.Shard405.arity registers prefixList 1493
    stackResult469.1 stackResult469.2.1 stackResult469.2.2.1 1493 stackResult469_eq
wave8_kernel_reduce stackResult470 := WordToStack.Native.compileProgNative
  riscvConfig false Word470.program PrefixChecks.Shard406.arity registers (.nil, 1493)
theorem stackResult470_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word470.program
      PrefixChecks.Shard406.arity registers (prefixList, 1493) =
    (stackResult470.1, stackResult470.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult470.2.2.1, 1493)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word470.program
    PrefixChecks.Shard406.arity registers prefixList 1493
    stackResult470.1 stackResult470.2.1 stackResult470.2.2.1 1493 stackResult470_eq
wave8_kernel_reduce stackResult471 := WordToStack.Native.compileProgNative
  riscvConfig false Word471.program PrefixChecks.Shard407.arity registers (.nil, 1493)
theorem stackResult471_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word471.program
      PrefixChecks.Shard407.arity registers (prefixList, 1493) =
    (stackResult471.1, stackResult471.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult471.2.2.1, 1494)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word471.program
    PrefixChecks.Shard407.arity registers prefixList 1493
    stackResult471.1 stackResult471.2.1 stackResult471.2.2.1 1494 stackResult471_eq
wave8_kernel_reduce stackResult472 := WordToStack.Native.compileProgNative
  riscvConfig false Word472.program PrefixChecks.Shard408.arity registers (.nil, 1494)
theorem stackResult472_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word472.program
      PrefixChecks.Shard408.arity registers (prefixList, 1494) =
    (stackResult472.1, stackResult472.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult472.2.2.1, 1495)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word472.program
    PrefixChecks.Shard408.arity registers prefixList 1494
    stackResult472.1 stackResult472.2.1 stackResult472.2.2.1 1495 stackResult472_eq
wave8_kernel_reduce stackResult473 := WordToStack.Native.compileProgNative
  riscvConfig false Word473.program PrefixChecks.Shard409.arity registers (.nil, 1495)
theorem stackResult473_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word473.program
      PrefixChecks.Shard409.arity registers (prefixList, 1495) =
    (stackResult473.1, stackResult473.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult473.2.2.1, 1495)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word473.program
    PrefixChecks.Shard409.arity registers prefixList 1495
    stackResult473.1 stackResult473.2.1 stackResult473.2.2.1 1495 stackResult473_eq
wave8_kernel_reduce stackResult474 := WordToStack.Native.compileProgNative
  riscvConfig false Word474.program PrefixChecks.Shard410.arity registers (.nil, 1495)
theorem stackResult474_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word474.program
      PrefixChecks.Shard410.arity registers (prefixList, 1495) =
    (stackResult474.1, stackResult474.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult474.2.2.1, 1495)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word474.program
    PrefixChecks.Shard410.arity registers prefixList 1495
    stackResult474.1 stackResult474.2.1 stackResult474.2.2.1 1495 stackResult474_eq
wave8_kernel_reduce stackResult475 := WordToStack.Native.compileProgNative
  riscvConfig false Word475.program PrefixChecks.Shard411.arity registers (.nil, 1495)
theorem stackResult475_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word475.program
      PrefixChecks.Shard411.arity registers (prefixList, 1495) =
    (stackResult475.1, stackResult475.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult475.2.2.1, 1495)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word475.program
    PrefixChecks.Shard411.arity registers prefixList 1495
    stackResult475.1 stackResult475.2.1 stackResult475.2.2.1 1495 stackResult475_eq
wave8_kernel_reduce stackResult476 := WordToStack.Native.compileProgNative
  riscvConfig false Word476.program PrefixChecks.Shard412.arity registers (.nil, 1495)
theorem stackResult476_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word476.program
      PrefixChecks.Shard412.arity registers (prefixList, 1495) =
    (stackResult476.1, stackResult476.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult476.2.2.1, 1497)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word476.program
    PrefixChecks.Shard412.arity registers prefixList 1495
    stackResult476.1 stackResult476.2.1 stackResult476.2.2.1 1497 stackResult476_eq
wave8_kernel_reduce stackResult477 := WordToStack.Native.compileProgNative
  riscvConfig false Word477.program PrefixChecks.Shard413.arity registers (.nil, 1497)
theorem stackResult477_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word477.program
      PrefixChecks.Shard413.arity registers (prefixList, 1497) =
    (stackResult477.1, stackResult477.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult477.2.2.1, 1498)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word477.program
    PrefixChecks.Shard413.arity registers prefixList 1497
    stackResult477.1 stackResult477.2.1 stackResult477.2.2.1 1498 stackResult477_eq
wave8_kernel_reduce stackResult478 := WordToStack.Native.compileProgNative
  riscvConfig false Word478.program PrefixChecks.Shard414.arity registers (.nil, 1498)
theorem stackResult478_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word478.program
      PrefixChecks.Shard414.arity registers (prefixList, 1498) =
    (stackResult478.1, stackResult478.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult478.2.2.1, 1500)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word478.program
    PrefixChecks.Shard414.arity registers prefixList 1498
    stackResult478.1 stackResult478.2.1 stackResult478.2.2.1 1500 stackResult478_eq
wave8_kernel_reduce stackResult479 := WordToStack.Native.compileProgNative
  riscvConfig false Word479.program PrefixChecks.Shard415.arity registers (.nil, 1500)
theorem stackResult479_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word479.program
      PrefixChecks.Shard415.arity registers (prefixList, 1500) =
    (stackResult479.1, stackResult479.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult479.2.2.1, 1503)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word479.program
    PrefixChecks.Shard415.arity registers prefixList 1500
    stackResult479.1 stackResult479.2.1 stackResult479.2.2.1 1503 stackResult479_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard400.name, PrefixChecks.Shard400.arity, Word464.program),
  (PrefixChecks.Shard401.name, PrefixChecks.Shard401.arity, Word465.program),
  (PrefixChecks.Shard402.name, PrefixChecks.Shard402.arity, Word466.program),
  (PrefixChecks.Shard403.name, PrefixChecks.Shard403.arity, Word467.program),
  (PrefixChecks.Shard404.name, PrefixChecks.Shard404.arity, Word468.program),
  (PrefixChecks.Shard405.name, PrefixChecks.Shard405.arity, Word469.program),
  (PrefixChecks.Shard406.name, PrefixChecks.Shard406.arity, Word470.program),
  (PrefixChecks.Shard407.name, PrefixChecks.Shard407.arity, Word471.program),
  (PrefixChecks.Shard408.name, PrefixChecks.Shard408.arity, Word472.program),
  (PrefixChecks.Shard409.name, PrefixChecks.Shard409.arity, Word473.program),
  (PrefixChecks.Shard410.name, PrefixChecks.Shard410.arity, Word474.program),
  (PrefixChecks.Shard411.name, PrefixChecks.Shard411.arity, Word475.program),
  (PrefixChecks.Shard412.name, PrefixChecks.Shard412.arity, Word476.program),
  (PrefixChecks.Shard413.name, PrefixChecks.Shard413.arity, Word477.program),
  (PrefixChecks.Shard414.name, PrefixChecks.Shard414.arity, Word478.program),
  (PrefixChecks.Shard415.name, PrefixChecks.Shard415.arity, Word479.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard400.name, stackResult464.1),
  (PrefixChecks.Shard401.name, stackResult465.1),
  (PrefixChecks.Shard402.name, stackResult466.1),
  (PrefixChecks.Shard403.name, stackResult467.1),
  (PrefixChecks.Shard404.name, stackResult468.1),
  (PrefixChecks.Shard405.name, stackResult469.1),
  (PrefixChecks.Shard406.name, stackResult470.1),
  (PrefixChecks.Shard407.name, stackResult471.1),
  (PrefixChecks.Shard408.name, stackResult472.1),
  (PrefixChecks.Shard409.name, stackResult473.1),
  (PrefixChecks.Shard410.name, stackResult474.1),
  (PrefixChecks.Shard411.name, stackResult475.1),
  (PrefixChecks.Shard412.name, stackResult476.1),
  (PrefixChecks.Shard413.name, stackResult477.1),
  (PrefixChecks.Shard414.name, stackResult478.1),
  (PrefixChecks.Shard415.name, stackResult479.1)
]

noncomputable def frames : List Nat := [
  stackResult464.2.1,
  stackResult465.2.1,
  stackResult466.2.1,
  stackResult467.2.1,
  stackResult468.2.1,
  stackResult469.2.1,
  stackResult470.2.1,
  stackResult471.2.1,
  stackResult472.2.1,
  stackResult473.2.1,
  stackResult474.2.1,
  stackResult475.2.1,
  stackResult476.2.1,
  stackResult477.2.1,
  stackResult478.2.1,
  stackResult479.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult464.2.2.1) stackResult465.2.2.1) stackResult466.2.2.1) stackResult467.2.2.1) stackResult468.2.2.1) stackResult469.2.2.1) stackResult470.2.2.1) stackResult471.2.2.1) stackResult472.2.2.1) stackResult473.2.2.1) stackResult474.2.2.1) stackResult475.2.2.1) stackResult476.2.2.1) stackResult477.2.2.1) stackResult478.2.2.1) stackResult479.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 1487) = (bodies, frames, (bitmapDelta, 1503)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult464_from _
  apply compileWordToStack_cons
  · exact stackResult465_from _
  apply compileWordToStack_cons
  · exact stackResult466_from _
  apply compileWordToStack_cons
  · exact stackResult467_from _
  apply compileWordToStack_cons
  · exact stackResult468_from _
  apply compileWordToStack_cons
  · exact stackResult469_from _
  apply compileWordToStack_cons
  · exact stackResult470_from _
  apply compileWordToStack_cons
  · exact stackResult471_from _
  apply compileWordToStack_cons
  · exact stackResult472_from _
  apply compileWordToStack_cons
  · exact stackResult473_from _
  apply compileWordToStack_cons
  · exact stackResult474_from _
  apply compileWordToStack_cons
  · exact stackResult475_from _
  apply compileWordToStack_cons
  · exact stackResult476_from _
  apply compileWordToStack_cons
  · exact stackResult477_from _
  apply compileWordToStack_cons
  · exact stackResult478_from _
  apply compileWordToStack_cons
  · exact stackResult479_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 1487) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 1503)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 1487 bodies frames bitmapDelta 1503 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 400).take 16).zip
      [oracle464, oracle465, oracle466, oracle467, oracle468, oracle469, oracle470, oracle471, oracle472, oracle473, oracle474, oracle475, oracle476, oracle477, oracle478, oracle479]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle464 PrefixChecks.Shard400.entry,
    wordFunction oracle465 PrefixChecks.Shard401.entry,
    wordFunction oracle466 PrefixChecks.Shard402.entry,
    wordFunction oracle467 PrefixChecks.Shard403.entry,
    wordFunction oracle468 PrefixChecks.Shard404.entry,
    wordFunction oracle469 PrefixChecks.Shard405.entry,
    wordFunction oracle470 PrefixChecks.Shard406.entry,
    wordFunction oracle471 PrefixChecks.Shard407.entry,
    wordFunction oracle472 PrefixChecks.Shard408.entry,
    wordFunction oracle473 PrefixChecks.Shard409.entry,
    wordFunction oracle474 PrefixChecks.Shard410.entry,
    wordFunction oracle475 PrefixChecks.Shard411.entry,
    wordFunction oracle476 PrefixChecks.Shard412.entry,
    wordFunction oracle477 PrefixChecks.Shard413.entry,
    wordFunction oracle478 PrefixChecks.Shard414.entry,
    wordFunction oracle479 PrefixChecks.Shard415.entry] = words
  simp only [
    Word464.wordFunction_eq,
    Word465.wordFunction_eq,
    Word466.wordFunction_eq,
    Word467.wordFunction_eq,
    Word468.wordFunction_eq,
    Word469.wordFunction_eq,
    Word470.wordFunction_eq,
    Word471.wordFunction_eq,
    Word472.wordFunction_eq,
    Word473.wordFunction_eq,
    Word474.wordFunction_eq,
    Word475.wordFunction_eq,
    Word476.wordFunction_eq,
    Word477.wordFunction_eq,
    Word478.wordFunction_eq,
    Word479.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk25
