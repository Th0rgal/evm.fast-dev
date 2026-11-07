import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word624
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word625
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word626
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word627
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word628
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word629
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word630
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word631
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word632
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word633
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word634
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word635
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word636
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word637
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word638
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word639
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk35
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult624 := WordToStack.Native.compileProgNative
  riscvConfig false Word624.program PrefixChecks.Shard560.arity registers (.nil, 2525)
theorem stackResult624_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word624.program
      PrefixChecks.Shard560.arity registers (prefixList, 2525) =
    (stackResult624.1, stackResult624.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult624.2.2.1, 2551)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word624.program
    PrefixChecks.Shard560.arity registers prefixList 2525
    stackResult624.1 stackResult624.2.1 stackResult624.2.2.1 2551 stackResult624_eq
wave8_kernel_reduce stackResult625 := WordToStack.Native.compileProgNative
  riscvConfig false Word625.program PrefixChecks.Shard561.arity registers (.nil, 2551)
theorem stackResult625_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word625.program
      PrefixChecks.Shard561.arity registers (prefixList, 2551) =
    (stackResult625.1, stackResult625.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult625.2.2.1, 2557)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word625.program
    PrefixChecks.Shard561.arity registers prefixList 2551
    stackResult625.1 stackResult625.2.1 stackResult625.2.2.1 2557 stackResult625_eq
wave8_kernel_reduce stackResult626 := WordToStack.Native.compileProgNative
  riscvConfig false Word626.program PrefixChecks.Shard562.arity registers (.nil, 2557)
theorem stackResult626_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word626.program
      PrefixChecks.Shard562.arity registers (prefixList, 2557) =
    (stackResult626.1, stackResult626.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult626.2.2.1, 2561)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word626.program
    PrefixChecks.Shard562.arity registers prefixList 2557
    stackResult626.1 stackResult626.2.1 stackResult626.2.2.1 2561 stackResult626_eq
wave8_kernel_reduce stackResult627 := WordToStack.Native.compileProgNative
  riscvConfig false Word627.program PrefixChecks.Shard563.arity registers (.nil, 2561)
theorem stackResult627_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word627.program
      PrefixChecks.Shard563.arity registers (prefixList, 2561) =
    (stackResult627.1, stackResult627.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult627.2.2.1, 2561)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word627.program
    PrefixChecks.Shard563.arity registers prefixList 2561
    stackResult627.1 stackResult627.2.1 stackResult627.2.2.1 2561 stackResult627_eq
wave8_kernel_reduce stackResult628 := WordToStack.Native.compileProgNative
  riscvConfig false Word628.program PrefixChecks.Shard564.arity registers (.nil, 2561)
theorem stackResult628_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word628.program
      PrefixChecks.Shard564.arity registers (prefixList, 2561) =
    (stackResult628.1, stackResult628.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult628.2.2.1, 2561)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word628.program
    PrefixChecks.Shard564.arity registers prefixList 2561
    stackResult628.1 stackResult628.2.1 stackResult628.2.2.1 2561 stackResult628_eq
wave8_kernel_reduce stackResult629 := WordToStack.Native.compileProgNative
  riscvConfig false Word629.program PrefixChecks.Shard565.arity registers (.nil, 2561)
theorem stackResult629_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word629.program
      PrefixChecks.Shard565.arity registers (prefixList, 2561) =
    (stackResult629.1, stackResult629.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult629.2.2.1, 2561)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word629.program
    PrefixChecks.Shard565.arity registers prefixList 2561
    stackResult629.1 stackResult629.2.1 stackResult629.2.2.1 2561 stackResult629_eq
wave8_kernel_reduce stackResult630 := WordToStack.Native.compileProgNative
  riscvConfig false Word630.program PrefixChecks.Shard566.arity registers (.nil, 2561)
theorem stackResult630_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word630.program
      PrefixChecks.Shard566.arity registers (prefixList, 2561) =
    (stackResult630.1, stackResult630.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult630.2.2.1, 2565)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word630.program
    PrefixChecks.Shard566.arity registers prefixList 2561
    stackResult630.1 stackResult630.2.1 stackResult630.2.2.1 2565 stackResult630_eq
wave8_kernel_reduce stackResult631 := WordToStack.Native.compileProgNative
  riscvConfig false Word631.program PrefixChecks.Shard567.arity registers (.nil, 2565)
theorem stackResult631_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word631.program
      PrefixChecks.Shard567.arity registers (prefixList, 2565) =
    (stackResult631.1, stackResult631.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult631.2.2.1, 2572)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word631.program
    PrefixChecks.Shard567.arity registers prefixList 2565
    stackResult631.1 stackResult631.2.1 stackResult631.2.2.1 2572 stackResult631_eq
wave8_kernel_reduce stackResult632 := WordToStack.Native.compileProgNative
  riscvConfig false Word632.program PrefixChecks.Shard568.arity registers (.nil, 2572)
theorem stackResult632_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word632.program
      PrefixChecks.Shard568.arity registers (prefixList, 2572) =
    (stackResult632.1, stackResult632.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult632.2.2.1, 2575)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word632.program
    PrefixChecks.Shard568.arity registers prefixList 2572
    stackResult632.1 stackResult632.2.1 stackResult632.2.2.1 2575 stackResult632_eq
wave8_kernel_reduce stackResult633 := WordToStack.Native.compileProgNative
  riscvConfig false Word633.program PrefixChecks.Shard569.arity registers (.nil, 2575)
theorem stackResult633_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word633.program
      PrefixChecks.Shard569.arity registers (prefixList, 2575) =
    (stackResult633.1, stackResult633.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult633.2.2.1, 2575)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word633.program
    PrefixChecks.Shard569.arity registers prefixList 2575
    stackResult633.1 stackResult633.2.1 stackResult633.2.2.1 2575 stackResult633_eq
wave8_kernel_reduce stackResult634 := WordToStack.Native.compileProgNative
  riscvConfig false Word634.program PrefixChecks.Shard570.arity registers (.nil, 2575)
theorem stackResult634_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word634.program
      PrefixChecks.Shard570.arity registers (prefixList, 2575) =
    (stackResult634.1, stackResult634.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult634.2.2.1, 2585)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word634.program
    PrefixChecks.Shard570.arity registers prefixList 2575
    stackResult634.1 stackResult634.2.1 stackResult634.2.2.1 2585 stackResult634_eq
wave8_kernel_reduce stackResult635 := WordToStack.Native.compileProgNative
  riscvConfig false Word635.program PrefixChecks.Shard571.arity registers (.nil, 2585)
theorem stackResult635_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word635.program
      PrefixChecks.Shard571.arity registers (prefixList, 2585) =
    (stackResult635.1, stackResult635.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult635.2.2.1, 2585)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word635.program
    PrefixChecks.Shard571.arity registers prefixList 2585
    stackResult635.1 stackResult635.2.1 stackResult635.2.2.1 2585 stackResult635_eq
wave8_kernel_reduce stackResult636 := WordToStack.Native.compileProgNative
  riscvConfig false Word636.program PrefixChecks.Shard572.arity registers (.nil, 2585)
theorem stackResult636_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word636.program
      PrefixChecks.Shard572.arity registers (prefixList, 2585) =
    (stackResult636.1, stackResult636.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult636.2.2.1, 2585)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word636.program
    PrefixChecks.Shard572.arity registers prefixList 2585
    stackResult636.1 stackResult636.2.1 stackResult636.2.2.1 2585 stackResult636_eq
wave8_kernel_reduce stackResult637 := WordToStack.Native.compileProgNative
  riscvConfig false Word637.program PrefixChecks.Shard573.arity registers (.nil, 2585)
theorem stackResult637_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word637.program
      PrefixChecks.Shard573.arity registers (prefixList, 2585) =
    (stackResult637.1, stackResult637.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult637.2.2.1, 2585)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word637.program
    PrefixChecks.Shard573.arity registers prefixList 2585
    stackResult637.1 stackResult637.2.1 stackResult637.2.2.1 2585 stackResult637_eq
wave8_kernel_reduce stackResult638 := WordToStack.Native.compileProgNative
  riscvConfig false Word638.program PrefixChecks.Shard574.arity registers (.nil, 2585)
theorem stackResult638_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word638.program
      PrefixChecks.Shard574.arity registers (prefixList, 2585) =
    (stackResult638.1, stackResult638.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult638.2.2.1, 2588)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word638.program
    PrefixChecks.Shard574.arity registers prefixList 2585
    stackResult638.1 stackResult638.2.1 stackResult638.2.2.1 2588 stackResult638_eq
wave8_kernel_reduce stackResult639 := WordToStack.Native.compileProgNative
  riscvConfig false Word639.program PrefixChecks.Shard575.arity registers (.nil, 2588)
theorem stackResult639_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word639.program
      PrefixChecks.Shard575.arity registers (prefixList, 2588) =
    (stackResult639.1, stackResult639.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult639.2.2.1, 2592)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word639.program
    PrefixChecks.Shard575.arity registers prefixList 2588
    stackResult639.1 stackResult639.2.1 stackResult639.2.2.1 2592 stackResult639_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard560.name, PrefixChecks.Shard560.arity, Word624.program),
  (PrefixChecks.Shard561.name, PrefixChecks.Shard561.arity, Word625.program),
  (PrefixChecks.Shard562.name, PrefixChecks.Shard562.arity, Word626.program),
  (PrefixChecks.Shard563.name, PrefixChecks.Shard563.arity, Word627.program),
  (PrefixChecks.Shard564.name, PrefixChecks.Shard564.arity, Word628.program),
  (PrefixChecks.Shard565.name, PrefixChecks.Shard565.arity, Word629.program),
  (PrefixChecks.Shard566.name, PrefixChecks.Shard566.arity, Word630.program),
  (PrefixChecks.Shard567.name, PrefixChecks.Shard567.arity, Word631.program),
  (PrefixChecks.Shard568.name, PrefixChecks.Shard568.arity, Word632.program),
  (PrefixChecks.Shard569.name, PrefixChecks.Shard569.arity, Word633.program),
  (PrefixChecks.Shard570.name, PrefixChecks.Shard570.arity, Word634.program),
  (PrefixChecks.Shard571.name, PrefixChecks.Shard571.arity, Word635.program),
  (PrefixChecks.Shard572.name, PrefixChecks.Shard572.arity, Word636.program),
  (PrefixChecks.Shard573.name, PrefixChecks.Shard573.arity, Word637.program),
  (PrefixChecks.Shard574.name, PrefixChecks.Shard574.arity, Word638.program),
  (PrefixChecks.Shard575.name, PrefixChecks.Shard575.arity, Word639.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard560.name, stackResult624.1),
  (PrefixChecks.Shard561.name, stackResult625.1),
  (PrefixChecks.Shard562.name, stackResult626.1),
  (PrefixChecks.Shard563.name, stackResult627.1),
  (PrefixChecks.Shard564.name, stackResult628.1),
  (PrefixChecks.Shard565.name, stackResult629.1),
  (PrefixChecks.Shard566.name, stackResult630.1),
  (PrefixChecks.Shard567.name, stackResult631.1),
  (PrefixChecks.Shard568.name, stackResult632.1),
  (PrefixChecks.Shard569.name, stackResult633.1),
  (PrefixChecks.Shard570.name, stackResult634.1),
  (PrefixChecks.Shard571.name, stackResult635.1),
  (PrefixChecks.Shard572.name, stackResult636.1),
  (PrefixChecks.Shard573.name, stackResult637.1),
  (PrefixChecks.Shard574.name, stackResult638.1),
  (PrefixChecks.Shard575.name, stackResult639.1)
]

noncomputable def frames : List Nat := [
  stackResult624.2.1,
  stackResult625.2.1,
  stackResult626.2.1,
  stackResult627.2.1,
  stackResult628.2.1,
  stackResult629.2.1,
  stackResult630.2.1,
  stackResult631.2.1,
  stackResult632.2.1,
  stackResult633.2.1,
  stackResult634.2.1,
  stackResult635.2.1,
  stackResult636.2.1,
  stackResult637.2.1,
  stackResult638.2.1,
  stackResult639.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult624.2.2.1) stackResult625.2.2.1) stackResult626.2.2.1) stackResult627.2.2.1) stackResult628.2.2.1) stackResult629.2.2.1) stackResult630.2.2.1) stackResult631.2.2.1) stackResult632.2.2.1) stackResult633.2.2.1) stackResult634.2.2.1) stackResult635.2.2.1) stackResult636.2.2.1) stackResult637.2.2.1) stackResult638.2.2.1) stackResult639.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 2525) = (bodies, frames, (bitmapDelta, 2592)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult624_from _
  apply compileWordToStack_cons
  · exact stackResult625_from _
  apply compileWordToStack_cons
  · exact stackResult626_from _
  apply compileWordToStack_cons
  · exact stackResult627_from _
  apply compileWordToStack_cons
  · exact stackResult628_from _
  apply compileWordToStack_cons
  · exact stackResult629_from _
  apply compileWordToStack_cons
  · exact stackResult630_from _
  apply compileWordToStack_cons
  · exact stackResult631_from _
  apply compileWordToStack_cons
  · exact stackResult632_from _
  apply compileWordToStack_cons
  · exact stackResult633_from _
  apply compileWordToStack_cons
  · exact stackResult634_from _
  apply compileWordToStack_cons
  · exact stackResult635_from _
  apply compileWordToStack_cons
  · exact stackResult636_from _
  apply compileWordToStack_cons
  · exact stackResult637_from _
  apply compileWordToStack_cons
  · exact stackResult638_from _
  apply compileWordToStack_cons
  · exact stackResult639_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 2525) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 2592)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 2525 bodies frames bitmapDelta 2592 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 560).take 16).zip
      [oracle624, oracle625, oracle626, oracle627, oracle628, oracle629, oracle630, oracle631, oracle632, oracle633, oracle634, oracle635, oracle636, oracle637, oracle638, oracle639]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle624 PrefixChecks.Shard560.entry,
    wordFunction oracle625 PrefixChecks.Shard561.entry,
    wordFunction oracle626 PrefixChecks.Shard562.entry,
    wordFunction oracle627 PrefixChecks.Shard563.entry,
    wordFunction oracle628 PrefixChecks.Shard564.entry,
    wordFunction oracle629 PrefixChecks.Shard565.entry,
    wordFunction oracle630 PrefixChecks.Shard566.entry,
    wordFunction oracle631 PrefixChecks.Shard567.entry,
    wordFunction oracle632 PrefixChecks.Shard568.entry,
    wordFunction oracle633 PrefixChecks.Shard569.entry,
    wordFunction oracle634 PrefixChecks.Shard570.entry,
    wordFunction oracle635 PrefixChecks.Shard571.entry,
    wordFunction oracle636 PrefixChecks.Shard572.entry,
    wordFunction oracle637 PrefixChecks.Shard573.entry,
    wordFunction oracle638 PrefixChecks.Shard574.entry,
    wordFunction oracle639 PrefixChecks.Shard575.entry] = words
  simp only [
    Word624.wordFunction_eq,
    Word625.wordFunction_eq,
    Word626.wordFunction_eq,
    Word627.wordFunction_eq,
    Word628.wordFunction_eq,
    Word629.wordFunction_eq,
    Word630.wordFunction_eq,
    Word631.wordFunction_eq,
    Word632.wordFunction_eq,
    Word633.wordFunction_eq,
    Word634.wordFunction_eq,
    Word635.wordFunction_eq,
    Word636.wordFunction_eq,
    Word637.wordFunction_eq,
    Word638.wordFunction_eq,
    Word639.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk35
