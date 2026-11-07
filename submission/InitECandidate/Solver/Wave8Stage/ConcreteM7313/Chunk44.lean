import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word768
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word769
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word770
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word771
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word772
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word773
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word774
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word775
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word776
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word777
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word778
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word779
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word780
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word781
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word782
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word783
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk44
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult768 := WordToStack.Native.compileProgNative
  riscvConfig false Word768.program PrefixChecks.Shard704.arity registers (.nil, 3453)
theorem stackResult768_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word768.program
      PrefixChecks.Shard704.arity registers (prefixList, 3453) =
    (stackResult768.1, stackResult768.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult768.2.2.1, 3454)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word768.program
    PrefixChecks.Shard704.arity registers prefixList 3453
    stackResult768.1 stackResult768.2.1 stackResult768.2.2.1 3454 stackResult768_eq
wave8_kernel_reduce stackResult769 := WordToStack.Native.compileProgNative
  riscvConfig false Word769.program PrefixChecks.Shard705.arity registers (.nil, 3454)
theorem stackResult769_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word769.program
      PrefixChecks.Shard705.arity registers (prefixList, 3454) =
    (stackResult769.1, stackResult769.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult769.2.2.1, 3455)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word769.program
    PrefixChecks.Shard705.arity registers prefixList 3454
    stackResult769.1 stackResult769.2.1 stackResult769.2.2.1 3455 stackResult769_eq
wave8_kernel_reduce stackResult770 := WordToStack.Native.compileProgNative
  riscvConfig false Word770.program PrefixChecks.Shard706.arity registers (.nil, 3455)
theorem stackResult770_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word770.program
      PrefixChecks.Shard706.arity registers (prefixList, 3455) =
    (stackResult770.1, stackResult770.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult770.2.2.1, 3481)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word770.program
    PrefixChecks.Shard706.arity registers prefixList 3455
    stackResult770.1 stackResult770.2.1 stackResult770.2.2.1 3481 stackResult770_eq
wave8_kernel_reduce stackResult771 := WordToStack.Native.compileProgNative
  riscvConfig false Word771.program PrefixChecks.Shard707.arity registers (.nil, 3481)
theorem stackResult771_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word771.program
      PrefixChecks.Shard707.arity registers (prefixList, 3481) =
    (stackResult771.1, stackResult771.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult771.2.2.1, 3510)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word771.program
    PrefixChecks.Shard707.arity registers prefixList 3481
    stackResult771.1 stackResult771.2.1 stackResult771.2.2.1 3510 stackResult771_eq
wave8_kernel_reduce stackResult772 := WordToStack.Native.compileProgNative
  riscvConfig false Word772.program PrefixChecks.Shard708.arity registers (.nil, 3510)
theorem stackResult772_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word772.program
      PrefixChecks.Shard708.arity registers (prefixList, 3510) =
    (stackResult772.1, stackResult772.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult772.2.2.1, 3519)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word772.program
    PrefixChecks.Shard708.arity registers prefixList 3510
    stackResult772.1 stackResult772.2.1 stackResult772.2.2.1 3519 stackResult772_eq
wave8_kernel_reduce stackResult773 := WordToStack.Native.compileProgNative
  riscvConfig false Word773.program PrefixChecks.Shard709.arity registers (.nil, 3519)
theorem stackResult773_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word773.program
      PrefixChecks.Shard709.arity registers (prefixList, 3519) =
    (stackResult773.1, stackResult773.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult773.2.2.1, 3523)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word773.program
    PrefixChecks.Shard709.arity registers prefixList 3519
    stackResult773.1 stackResult773.2.1 stackResult773.2.2.1 3523 stackResult773_eq
wave8_kernel_reduce stackResult774 := WordToStack.Native.compileProgNative
  riscvConfig false Word774.program PrefixChecks.Shard710.arity registers (.nil, 3523)
theorem stackResult774_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word774.program
      PrefixChecks.Shard710.arity registers (prefixList, 3523) =
    (stackResult774.1, stackResult774.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult774.2.2.1, 3527)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word774.program
    PrefixChecks.Shard710.arity registers prefixList 3523
    stackResult774.1 stackResult774.2.1 stackResult774.2.2.1 3527 stackResult774_eq
wave8_kernel_reduce stackResult775 := WordToStack.Native.compileProgNative
  riscvConfig false Word775.program PrefixChecks.Shard711.arity registers (.nil, 3527)
theorem stackResult775_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word775.program
      PrefixChecks.Shard711.arity registers (prefixList, 3527) =
    (stackResult775.1, stackResult775.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult775.2.2.1, 3531)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word775.program
    PrefixChecks.Shard711.arity registers prefixList 3527
    stackResult775.1 stackResult775.2.1 stackResult775.2.2.1 3531 stackResult775_eq
wave8_kernel_reduce stackResult776 := WordToStack.Native.compileProgNative
  riscvConfig false Word776.program PrefixChecks.Shard712.arity registers (.nil, 3531)
theorem stackResult776_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word776.program
      PrefixChecks.Shard712.arity registers (prefixList, 3531) =
    (stackResult776.1, stackResult776.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult776.2.2.1, 3537)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word776.program
    PrefixChecks.Shard712.arity registers prefixList 3531
    stackResult776.1 stackResult776.2.1 stackResult776.2.2.1 3537 stackResult776_eq
wave8_kernel_reduce stackResult777 := WordToStack.Native.compileProgNative
  riscvConfig false Word777.program PrefixChecks.Shard713.arity registers (.nil, 3537)
theorem stackResult777_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word777.program
      PrefixChecks.Shard713.arity registers (prefixList, 3537) =
    (stackResult777.1, stackResult777.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult777.2.2.1, 3542)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word777.program
    PrefixChecks.Shard713.arity registers prefixList 3537
    stackResult777.1 stackResult777.2.1 stackResult777.2.2.1 3542 stackResult777_eq
wave8_kernel_reduce stackResult778 := WordToStack.Native.compileProgNative
  riscvConfig false Word778.program PrefixChecks.Shard714.arity registers (.nil, 3542)
theorem stackResult778_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word778.program
      PrefixChecks.Shard714.arity registers (prefixList, 3542) =
    (stackResult778.1, stackResult778.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult778.2.2.1, 3545)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word778.program
    PrefixChecks.Shard714.arity registers prefixList 3542
    stackResult778.1 stackResult778.2.1 stackResult778.2.2.1 3545 stackResult778_eq
wave8_kernel_reduce stackResult779 := WordToStack.Native.compileProgNative
  riscvConfig false Word779.program PrefixChecks.Shard715.arity registers (.nil, 3545)
theorem stackResult779_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word779.program
      PrefixChecks.Shard715.arity registers (prefixList, 3545) =
    (stackResult779.1, stackResult779.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult779.2.2.1, 3545)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word779.program
    PrefixChecks.Shard715.arity registers prefixList 3545
    stackResult779.1 stackResult779.2.1 stackResult779.2.2.1 3545 stackResult779_eq
wave8_kernel_reduce stackResult780 := WordToStack.Native.compileProgNative
  riscvConfig false Word780.program PrefixChecks.Shard716.arity registers (.nil, 3545)
theorem stackResult780_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word780.program
      PrefixChecks.Shard716.arity registers (prefixList, 3545) =
    (stackResult780.1, stackResult780.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult780.2.2.1, 3546)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word780.program
    PrefixChecks.Shard716.arity registers prefixList 3545
    stackResult780.1 stackResult780.2.1 stackResult780.2.2.1 3546 stackResult780_eq
wave8_kernel_reduce stackResult781 := WordToStack.Native.compileProgNative
  riscvConfig false Word781.program PrefixChecks.Shard717.arity registers (.nil, 3546)
theorem stackResult781_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word781.program
      PrefixChecks.Shard717.arity registers (prefixList, 3546) =
    (stackResult781.1, stackResult781.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult781.2.2.1, 3549)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word781.program
    PrefixChecks.Shard717.arity registers prefixList 3546
    stackResult781.1 stackResult781.2.1 stackResult781.2.2.1 3549 stackResult781_eq
wave8_kernel_reduce stackResult782 := WordToStack.Native.compileProgNative
  riscvConfig false Word782.program PrefixChecks.Shard718.arity registers (.nil, 3549)
theorem stackResult782_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word782.program
      PrefixChecks.Shard718.arity registers (prefixList, 3549) =
    (stackResult782.1, stackResult782.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult782.2.2.1, 3581)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word782.program
    PrefixChecks.Shard718.arity registers prefixList 3549
    stackResult782.1 stackResult782.2.1 stackResult782.2.2.1 3581 stackResult782_eq
wave8_kernel_reduce stackResult783 := WordToStack.Native.compileProgNative
  riscvConfig false Word783.program PrefixChecks.Shard719.arity registers (.nil, 3581)
theorem stackResult783_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word783.program
      PrefixChecks.Shard719.arity registers (prefixList, 3581) =
    (stackResult783.1, stackResult783.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult783.2.2.1, 3617)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word783.program
    PrefixChecks.Shard719.arity registers prefixList 3581
    stackResult783.1 stackResult783.2.1 stackResult783.2.2.1 3617 stackResult783_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard704.name, PrefixChecks.Shard704.arity, Word768.program),
  (PrefixChecks.Shard705.name, PrefixChecks.Shard705.arity, Word769.program),
  (PrefixChecks.Shard706.name, PrefixChecks.Shard706.arity, Word770.program),
  (PrefixChecks.Shard707.name, PrefixChecks.Shard707.arity, Word771.program),
  (PrefixChecks.Shard708.name, PrefixChecks.Shard708.arity, Word772.program),
  (PrefixChecks.Shard709.name, PrefixChecks.Shard709.arity, Word773.program),
  (PrefixChecks.Shard710.name, PrefixChecks.Shard710.arity, Word774.program),
  (PrefixChecks.Shard711.name, PrefixChecks.Shard711.arity, Word775.program),
  (PrefixChecks.Shard712.name, PrefixChecks.Shard712.arity, Word776.program),
  (PrefixChecks.Shard713.name, PrefixChecks.Shard713.arity, Word777.program),
  (PrefixChecks.Shard714.name, PrefixChecks.Shard714.arity, Word778.program),
  (PrefixChecks.Shard715.name, PrefixChecks.Shard715.arity, Word779.program),
  (PrefixChecks.Shard716.name, PrefixChecks.Shard716.arity, Word780.program),
  (PrefixChecks.Shard717.name, PrefixChecks.Shard717.arity, Word781.program),
  (PrefixChecks.Shard718.name, PrefixChecks.Shard718.arity, Word782.program),
  (PrefixChecks.Shard719.name, PrefixChecks.Shard719.arity, Word783.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard704.name, stackResult768.1),
  (PrefixChecks.Shard705.name, stackResult769.1),
  (PrefixChecks.Shard706.name, stackResult770.1),
  (PrefixChecks.Shard707.name, stackResult771.1),
  (PrefixChecks.Shard708.name, stackResult772.1),
  (PrefixChecks.Shard709.name, stackResult773.1),
  (PrefixChecks.Shard710.name, stackResult774.1),
  (PrefixChecks.Shard711.name, stackResult775.1),
  (PrefixChecks.Shard712.name, stackResult776.1),
  (PrefixChecks.Shard713.name, stackResult777.1),
  (PrefixChecks.Shard714.name, stackResult778.1),
  (PrefixChecks.Shard715.name, stackResult779.1),
  (PrefixChecks.Shard716.name, stackResult780.1),
  (PrefixChecks.Shard717.name, stackResult781.1),
  (PrefixChecks.Shard718.name, stackResult782.1),
  (PrefixChecks.Shard719.name, stackResult783.1)
]

noncomputable def frames : List Nat := [
  stackResult768.2.1,
  stackResult769.2.1,
  stackResult770.2.1,
  stackResult771.2.1,
  stackResult772.2.1,
  stackResult773.2.1,
  stackResult774.2.1,
  stackResult775.2.1,
  stackResult776.2.1,
  stackResult777.2.1,
  stackResult778.2.1,
  stackResult779.2.1,
  stackResult780.2.1,
  stackResult781.2.1,
  stackResult782.2.1,
  stackResult783.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult768.2.2.1) stackResult769.2.2.1) stackResult770.2.2.1) stackResult771.2.2.1) stackResult772.2.2.1) stackResult773.2.2.1) stackResult774.2.2.1) stackResult775.2.2.1) stackResult776.2.2.1) stackResult777.2.2.1) stackResult778.2.2.1) stackResult779.2.2.1) stackResult780.2.2.1) stackResult781.2.2.1) stackResult782.2.2.1) stackResult783.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 3453) = (bodies, frames, (bitmapDelta, 3617)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult768_from _
  apply compileWordToStack_cons
  · exact stackResult769_from _
  apply compileWordToStack_cons
  · exact stackResult770_from _
  apply compileWordToStack_cons
  · exact stackResult771_from _
  apply compileWordToStack_cons
  · exact stackResult772_from _
  apply compileWordToStack_cons
  · exact stackResult773_from _
  apply compileWordToStack_cons
  · exact stackResult774_from _
  apply compileWordToStack_cons
  · exact stackResult775_from _
  apply compileWordToStack_cons
  · exact stackResult776_from _
  apply compileWordToStack_cons
  · exact stackResult777_from _
  apply compileWordToStack_cons
  · exact stackResult778_from _
  apply compileWordToStack_cons
  · exact stackResult779_from _
  apply compileWordToStack_cons
  · exact stackResult780_from _
  apply compileWordToStack_cons
  · exact stackResult781_from _
  apply compileWordToStack_cons
  · exact stackResult782_from _
  apply compileWordToStack_cons
  · exact stackResult783_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 3453) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 3617)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 3453 bodies frames bitmapDelta 3617 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 704).take 16).zip
      [oracle768, oracle769, oracle770, oracle771, oracle772, oracle773, oracle774, oracle775, oracle776, oracle777, oracle778, oracle779, oracle780, oracle781, oracle782, oracle783]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle768 PrefixChecks.Shard704.entry,
    wordFunction oracle769 PrefixChecks.Shard705.entry,
    wordFunction oracle770 PrefixChecks.Shard706.entry,
    wordFunction oracle771 PrefixChecks.Shard707.entry,
    wordFunction oracle772 PrefixChecks.Shard708.entry,
    wordFunction oracle773 PrefixChecks.Shard709.entry,
    wordFunction oracle774 PrefixChecks.Shard710.entry,
    wordFunction oracle775 PrefixChecks.Shard711.entry,
    wordFunction oracle776 PrefixChecks.Shard712.entry,
    wordFunction oracle777 PrefixChecks.Shard713.entry,
    wordFunction oracle778 PrefixChecks.Shard714.entry,
    wordFunction oracle779 PrefixChecks.Shard715.entry,
    wordFunction oracle780 PrefixChecks.Shard716.entry,
    wordFunction oracle781 PrefixChecks.Shard717.entry,
    wordFunction oracle782 PrefixChecks.Shard718.entry,
    wordFunction oracle783 PrefixChecks.Shard719.entry] = words
  simp only [
    Word768.wordFunction_eq,
    Word769.wordFunction_eq,
    Word770.wordFunction_eq,
    Word771.wordFunction_eq,
    Word772.wordFunction_eq,
    Word773.wordFunction_eq,
    Word774.wordFunction_eq,
    Word775.wordFunction_eq,
    Word776.wordFunction_eq,
    Word777.wordFunction_eq,
    Word778.wordFunction_eq,
    Word779.wordFunction_eq,
    Word780.wordFunction_eq,
    Word781.wordFunction_eq,
    Word782.wordFunction_eq,
    Word783.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk44
