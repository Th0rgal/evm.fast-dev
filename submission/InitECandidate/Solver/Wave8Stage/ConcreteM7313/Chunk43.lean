import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word752
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word753
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word754
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word755
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word756
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word757
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word758
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word759
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word760
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word761
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word762
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word763
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word764
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word765
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word766
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word767
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk43
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult752 := WordToStack.Native.compileProgNative
  riscvConfig false Word752.program PrefixChecks.Shard688.arity registers (.nil, 3319)
theorem stackResult752_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word752.program
      PrefixChecks.Shard688.arity registers (prefixList, 3319) =
    (stackResult752.1, stackResult752.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult752.2.2.1, 3339)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word752.program
    PrefixChecks.Shard688.arity registers prefixList 3319
    stackResult752.1 stackResult752.2.1 stackResult752.2.2.1 3339 stackResult752_eq
wave8_kernel_reduce stackResult753 := WordToStack.Native.compileProgNative
  riscvConfig false Word753.program PrefixChecks.Shard689.arity registers (.nil, 3339)
theorem stackResult753_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word753.program
      PrefixChecks.Shard689.arity registers (prefixList, 3339) =
    (stackResult753.1, stackResult753.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult753.2.2.1, 3346)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word753.program
    PrefixChecks.Shard689.arity registers prefixList 3339
    stackResult753.1 stackResult753.2.1 stackResult753.2.2.1 3346 stackResult753_eq
wave8_kernel_reduce stackResult754 := WordToStack.Native.compileProgNative
  riscvConfig false Word754.program PrefixChecks.Shard690.arity registers (.nil, 3346)
theorem stackResult754_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word754.program
      PrefixChecks.Shard690.arity registers (prefixList, 3346) =
    (stackResult754.1, stackResult754.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult754.2.2.1, 3370)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word754.program
    PrefixChecks.Shard690.arity registers prefixList 3346
    stackResult754.1 stackResult754.2.1 stackResult754.2.2.1 3370 stackResult754_eq
wave8_kernel_reduce stackResult755 := WordToStack.Native.compileProgNative
  riscvConfig false Word755.program PrefixChecks.Shard691.arity registers (.nil, 3370)
theorem stackResult755_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word755.program
      PrefixChecks.Shard691.arity registers (prefixList, 3370) =
    (stackResult755.1, stackResult755.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult755.2.2.1, 3371)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word755.program
    PrefixChecks.Shard691.arity registers prefixList 3370
    stackResult755.1 stackResult755.2.1 stackResult755.2.2.1 3371 stackResult755_eq
wave8_kernel_reduce stackResult756 := WordToStack.Native.compileProgNative
  riscvConfig false Word756.program PrefixChecks.Shard692.arity registers (.nil, 3371)
theorem stackResult756_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word756.program
      PrefixChecks.Shard692.arity registers (prefixList, 3371) =
    (stackResult756.1, stackResult756.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult756.2.2.1, 3373)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word756.program
    PrefixChecks.Shard692.arity registers prefixList 3371
    stackResult756.1 stackResult756.2.1 stackResult756.2.2.1 3373 stackResult756_eq
wave8_kernel_reduce stackResult757 := WordToStack.Native.compileProgNative
  riscvConfig false Word757.program PrefixChecks.Shard693.arity registers (.nil, 3373)
theorem stackResult757_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word757.program
      PrefixChecks.Shard693.arity registers (prefixList, 3373) =
    (stackResult757.1, stackResult757.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult757.2.2.1, 3378)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word757.program
    PrefixChecks.Shard693.arity registers prefixList 3373
    stackResult757.1 stackResult757.2.1 stackResult757.2.2.1 3378 stackResult757_eq
wave8_kernel_reduce stackResult758 := WordToStack.Native.compileProgNative
  riscvConfig false Word758.program PrefixChecks.Shard694.arity registers (.nil, 3378)
theorem stackResult758_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word758.program
      PrefixChecks.Shard694.arity registers (prefixList, 3378) =
    (stackResult758.1, stackResult758.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult758.2.2.1, 3390)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word758.program
    PrefixChecks.Shard694.arity registers prefixList 3378
    stackResult758.1 stackResult758.2.1 stackResult758.2.2.1 3390 stackResult758_eq
wave8_kernel_reduce stackResult759 := WordToStack.Native.compileProgNative
  riscvConfig false Word759.program PrefixChecks.Shard695.arity registers (.nil, 3390)
theorem stackResult759_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word759.program
      PrefixChecks.Shard695.arity registers (prefixList, 3390) =
    (stackResult759.1, stackResult759.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult759.2.2.1, 3390)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word759.program
    PrefixChecks.Shard695.arity registers prefixList 3390
    stackResult759.1 stackResult759.2.1 stackResult759.2.2.1 3390 stackResult759_eq
wave8_kernel_reduce stackResult760 := WordToStack.Native.compileProgNative
  riscvConfig false Word760.program PrefixChecks.Shard696.arity registers (.nil, 3390)
theorem stackResult760_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word760.program
      PrefixChecks.Shard696.arity registers (prefixList, 3390) =
    (stackResult760.1, stackResult760.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult760.2.2.1, 3392)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word760.program
    PrefixChecks.Shard696.arity registers prefixList 3390
    stackResult760.1 stackResult760.2.1 stackResult760.2.2.1 3392 stackResult760_eq
wave8_kernel_reduce stackResult761 := WordToStack.Native.compileProgNative
  riscvConfig false Word761.program PrefixChecks.Shard697.arity registers (.nil, 3392)
theorem stackResult761_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word761.program
      PrefixChecks.Shard697.arity registers (prefixList, 3392) =
    (stackResult761.1, stackResult761.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult761.2.2.1, 3403)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word761.program
    PrefixChecks.Shard697.arity registers prefixList 3392
    stackResult761.1 stackResult761.2.1 stackResult761.2.2.1 3403 stackResult761_eq
wave8_kernel_reduce stackResult762 := WordToStack.Native.compileProgNative
  riscvConfig false Word762.program PrefixChecks.Shard698.arity registers (.nil, 3403)
theorem stackResult762_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word762.program
      PrefixChecks.Shard698.arity registers (prefixList, 3403) =
    (stackResult762.1, stackResult762.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult762.2.2.1, 3414)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word762.program
    PrefixChecks.Shard698.arity registers prefixList 3403
    stackResult762.1 stackResult762.2.1 stackResult762.2.2.1 3414 stackResult762_eq
wave8_kernel_reduce stackResult763 := WordToStack.Native.compileProgNative
  riscvConfig false Word763.program PrefixChecks.Shard699.arity registers (.nil, 3414)
theorem stackResult763_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word763.program
      PrefixChecks.Shard699.arity registers (prefixList, 3414) =
    (stackResult763.1, stackResult763.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult763.2.2.1, 3423)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word763.program
    PrefixChecks.Shard699.arity registers prefixList 3414
    stackResult763.1 stackResult763.2.1 stackResult763.2.2.1 3423 stackResult763_eq
wave8_kernel_reduce stackResult764 := WordToStack.Native.compileProgNative
  riscvConfig false Word764.program PrefixChecks.Shard700.arity registers (.nil, 3423)
theorem stackResult764_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word764.program
      PrefixChecks.Shard700.arity registers (prefixList, 3423) =
    (stackResult764.1, stackResult764.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult764.2.2.1, 3425)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word764.program
    PrefixChecks.Shard700.arity registers prefixList 3423
    stackResult764.1 stackResult764.2.1 stackResult764.2.2.1 3425 stackResult764_eq
wave8_kernel_reduce stackResult765 := WordToStack.Native.compileProgNative
  riscvConfig false Word765.program PrefixChecks.Shard701.arity registers (.nil, 3425)
theorem stackResult765_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word765.program
      PrefixChecks.Shard701.arity registers (prefixList, 3425) =
    (stackResult765.1, stackResult765.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult765.2.2.1, 3453)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word765.program
    PrefixChecks.Shard701.arity registers prefixList 3425
    stackResult765.1 stackResult765.2.1 stackResult765.2.2.1 3453 stackResult765_eq
wave8_kernel_reduce stackResult766 := WordToStack.Native.compileProgNative
  riscvConfig false Word766.program PrefixChecks.Shard702.arity registers (.nil, 3453)
theorem stackResult766_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word766.program
      PrefixChecks.Shard702.arity registers (prefixList, 3453) =
    (stackResult766.1, stackResult766.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult766.2.2.1, 3453)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word766.program
    PrefixChecks.Shard702.arity registers prefixList 3453
    stackResult766.1 stackResult766.2.1 stackResult766.2.2.1 3453 stackResult766_eq
wave8_kernel_reduce stackResult767 := WordToStack.Native.compileProgNative
  riscvConfig false Word767.program PrefixChecks.Shard703.arity registers (.nil, 3453)
theorem stackResult767_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word767.program
      PrefixChecks.Shard703.arity registers (prefixList, 3453) =
    (stackResult767.1, stackResult767.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult767.2.2.1, 3453)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word767.program
    PrefixChecks.Shard703.arity registers prefixList 3453
    stackResult767.1 stackResult767.2.1 stackResult767.2.2.1 3453 stackResult767_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard688.name, PrefixChecks.Shard688.arity, Word752.program),
  (PrefixChecks.Shard689.name, PrefixChecks.Shard689.arity, Word753.program),
  (PrefixChecks.Shard690.name, PrefixChecks.Shard690.arity, Word754.program),
  (PrefixChecks.Shard691.name, PrefixChecks.Shard691.arity, Word755.program),
  (PrefixChecks.Shard692.name, PrefixChecks.Shard692.arity, Word756.program),
  (PrefixChecks.Shard693.name, PrefixChecks.Shard693.arity, Word757.program),
  (PrefixChecks.Shard694.name, PrefixChecks.Shard694.arity, Word758.program),
  (PrefixChecks.Shard695.name, PrefixChecks.Shard695.arity, Word759.program),
  (PrefixChecks.Shard696.name, PrefixChecks.Shard696.arity, Word760.program),
  (PrefixChecks.Shard697.name, PrefixChecks.Shard697.arity, Word761.program),
  (PrefixChecks.Shard698.name, PrefixChecks.Shard698.arity, Word762.program),
  (PrefixChecks.Shard699.name, PrefixChecks.Shard699.arity, Word763.program),
  (PrefixChecks.Shard700.name, PrefixChecks.Shard700.arity, Word764.program),
  (PrefixChecks.Shard701.name, PrefixChecks.Shard701.arity, Word765.program),
  (PrefixChecks.Shard702.name, PrefixChecks.Shard702.arity, Word766.program),
  (PrefixChecks.Shard703.name, PrefixChecks.Shard703.arity, Word767.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard688.name, stackResult752.1),
  (PrefixChecks.Shard689.name, stackResult753.1),
  (PrefixChecks.Shard690.name, stackResult754.1),
  (PrefixChecks.Shard691.name, stackResult755.1),
  (PrefixChecks.Shard692.name, stackResult756.1),
  (PrefixChecks.Shard693.name, stackResult757.1),
  (PrefixChecks.Shard694.name, stackResult758.1),
  (PrefixChecks.Shard695.name, stackResult759.1),
  (PrefixChecks.Shard696.name, stackResult760.1),
  (PrefixChecks.Shard697.name, stackResult761.1),
  (PrefixChecks.Shard698.name, stackResult762.1),
  (PrefixChecks.Shard699.name, stackResult763.1),
  (PrefixChecks.Shard700.name, stackResult764.1),
  (PrefixChecks.Shard701.name, stackResult765.1),
  (PrefixChecks.Shard702.name, stackResult766.1),
  (PrefixChecks.Shard703.name, stackResult767.1)
]

noncomputable def frames : List Nat := [
  stackResult752.2.1,
  stackResult753.2.1,
  stackResult754.2.1,
  stackResult755.2.1,
  stackResult756.2.1,
  stackResult757.2.1,
  stackResult758.2.1,
  stackResult759.2.1,
  stackResult760.2.1,
  stackResult761.2.1,
  stackResult762.2.1,
  stackResult763.2.1,
  stackResult764.2.1,
  stackResult765.2.1,
  stackResult766.2.1,
  stackResult767.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult752.2.2.1) stackResult753.2.2.1) stackResult754.2.2.1) stackResult755.2.2.1) stackResult756.2.2.1) stackResult757.2.2.1) stackResult758.2.2.1) stackResult759.2.2.1) stackResult760.2.2.1) stackResult761.2.2.1) stackResult762.2.2.1) stackResult763.2.2.1) stackResult764.2.2.1) stackResult765.2.2.1) stackResult766.2.2.1) stackResult767.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 3319) = (bodies, frames, (bitmapDelta, 3453)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult752_from _
  apply compileWordToStack_cons
  · exact stackResult753_from _
  apply compileWordToStack_cons
  · exact stackResult754_from _
  apply compileWordToStack_cons
  · exact stackResult755_from _
  apply compileWordToStack_cons
  · exact stackResult756_from _
  apply compileWordToStack_cons
  · exact stackResult757_from _
  apply compileWordToStack_cons
  · exact stackResult758_from _
  apply compileWordToStack_cons
  · exact stackResult759_from _
  apply compileWordToStack_cons
  · exact stackResult760_from _
  apply compileWordToStack_cons
  · exact stackResult761_from _
  apply compileWordToStack_cons
  · exact stackResult762_from _
  apply compileWordToStack_cons
  · exact stackResult763_from _
  apply compileWordToStack_cons
  · exact stackResult764_from _
  apply compileWordToStack_cons
  · exact stackResult765_from _
  apply compileWordToStack_cons
  · exact stackResult766_from _
  apply compileWordToStack_cons
  · exact stackResult767_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 3319) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 3453)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 3319 bodies frames bitmapDelta 3453 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 688).take 16).zip
      [oracle752, oracle753, oracle754, oracle755, oracle756, oracle757, oracle758, oracle759, oracle760, oracle761, oracle762, oracle763, oracle764, oracle765, oracle766, oracle767]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle752 PrefixChecks.Shard688.entry,
    wordFunction oracle753 PrefixChecks.Shard689.entry,
    wordFunction oracle754 PrefixChecks.Shard690.entry,
    wordFunction oracle755 PrefixChecks.Shard691.entry,
    wordFunction oracle756 PrefixChecks.Shard692.entry,
    wordFunction oracle757 PrefixChecks.Shard693.entry,
    wordFunction oracle758 PrefixChecks.Shard694.entry,
    wordFunction oracle759 PrefixChecks.Shard695.entry,
    wordFunction oracle760 PrefixChecks.Shard696.entry,
    wordFunction oracle761 PrefixChecks.Shard697.entry,
    wordFunction oracle762 PrefixChecks.Shard698.entry,
    wordFunction oracle763 PrefixChecks.Shard699.entry,
    wordFunction oracle764 PrefixChecks.Shard700.entry,
    wordFunction oracle765 PrefixChecks.Shard701.entry,
    wordFunction oracle766 PrefixChecks.Shard702.entry,
    wordFunction oracle767 PrefixChecks.Shard703.entry] = words
  simp only [
    Word752.wordFunction_eq,
    Word753.wordFunction_eq,
    Word754.wordFunction_eq,
    Word755.wordFunction_eq,
    Word756.wordFunction_eq,
    Word757.wordFunction_eq,
    Word758.wordFunction_eq,
    Word759.wordFunction_eq,
    Word760.wordFunction_eq,
    Word761.wordFunction_eq,
    Word762.wordFunction_eq,
    Word763.wordFunction_eq,
    Word764.wordFunction_eq,
    Word765.wordFunction_eq,
    Word766.wordFunction_eq,
    Word767.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk43
