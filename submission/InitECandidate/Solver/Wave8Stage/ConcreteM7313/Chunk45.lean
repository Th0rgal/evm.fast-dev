import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word784
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word785
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word786
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word787
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word788
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word789
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word790
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word791
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word792
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word793
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word794
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word795
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word796
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word797
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word798
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word799
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk45
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult784 := WordToStack.Native.compileProgNative
  riscvConfig false Word784.program PrefixChecks.Shard720.arity registers (.nil, 3617)
theorem stackResult784_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word784.program
      PrefixChecks.Shard720.arity registers (prefixList, 3617) =
    (stackResult784.1, stackResult784.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult784.2.2.1, 3624)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word784.program
    PrefixChecks.Shard720.arity registers prefixList 3617
    stackResult784.1 stackResult784.2.1 stackResult784.2.2.1 3624 stackResult784_eq
wave8_kernel_reduce stackResult785 := WordToStack.Native.compileProgNative
  riscvConfig false Word785.program PrefixChecks.Shard721.arity registers (.nil, 3624)
theorem stackResult785_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word785.program
      PrefixChecks.Shard721.arity registers (prefixList, 3624) =
    (stackResult785.1, stackResult785.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult785.2.2.1, 3633)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word785.program
    PrefixChecks.Shard721.arity registers prefixList 3624
    stackResult785.1 stackResult785.2.1 stackResult785.2.2.1 3633 stackResult785_eq
wave8_kernel_reduce stackResult786 := WordToStack.Native.compileProgNative
  riscvConfig false Word786.program PrefixChecks.Shard722.arity registers (.nil, 3633)
theorem stackResult786_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word786.program
      PrefixChecks.Shard722.arity registers (prefixList, 3633) =
    (stackResult786.1, stackResult786.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult786.2.2.1, 3642)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word786.program
    PrefixChecks.Shard722.arity registers prefixList 3633
    stackResult786.1 stackResult786.2.1 stackResult786.2.2.1 3642 stackResult786_eq
wave8_kernel_reduce stackResult787 := WordToStack.Native.compileProgNative
  riscvConfig false Word787.program PrefixChecks.Shard723.arity registers (.nil, 3642)
theorem stackResult787_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word787.program
      PrefixChecks.Shard723.arity registers (prefixList, 3642) =
    (stackResult787.1, stackResult787.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult787.2.2.1, 3650)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word787.program
    PrefixChecks.Shard723.arity registers prefixList 3642
    stackResult787.1 stackResult787.2.1 stackResult787.2.2.1 3650 stackResult787_eq
wave8_kernel_reduce stackResult788 := WordToStack.Native.compileProgNative
  riscvConfig false Word788.program PrefixChecks.Shard724.arity registers (.nil, 3650)
theorem stackResult788_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word788.program
      PrefixChecks.Shard724.arity registers (prefixList, 3650) =
    (stackResult788.1, stackResult788.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult788.2.2.1, 3658)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word788.program
    PrefixChecks.Shard724.arity registers prefixList 3650
    stackResult788.1 stackResult788.2.1 stackResult788.2.2.1 3658 stackResult788_eq
wave8_kernel_reduce stackResult789 := WordToStack.Native.compileProgNative
  riscvConfig false Word789.program PrefixChecks.Shard725.arity registers (.nil, 3658)
theorem stackResult789_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word789.program
      PrefixChecks.Shard725.arity registers (prefixList, 3658) =
    (stackResult789.1, stackResult789.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult789.2.2.1, 3663)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word789.program
    PrefixChecks.Shard725.arity registers prefixList 3658
    stackResult789.1 stackResult789.2.1 stackResult789.2.2.1 3663 stackResult789_eq
wave8_kernel_reduce stackResult790 := WordToStack.Native.compileProgNative
  riscvConfig false Word790.program PrefixChecks.Shard726.arity registers (.nil, 3663)
theorem stackResult790_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word790.program
      PrefixChecks.Shard726.arity registers (prefixList, 3663) =
    (stackResult790.1, stackResult790.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult790.2.2.1, 3703)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word790.program
    PrefixChecks.Shard726.arity registers prefixList 3663
    stackResult790.1 stackResult790.2.1 stackResult790.2.2.1 3703 stackResult790_eq
wave8_kernel_reduce stackResult791 := WordToStack.Native.compileProgNative
  riscvConfig false Word791.program PrefixChecks.Shard727.arity registers (.nil, 3703)
theorem stackResult791_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word791.program
      PrefixChecks.Shard727.arity registers (prefixList, 3703) =
    (stackResult791.1, stackResult791.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult791.2.2.1, 3747)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word791.program
    PrefixChecks.Shard727.arity registers prefixList 3703
    stackResult791.1 stackResult791.2.1 stackResult791.2.2.1 3747 stackResult791_eq
wave8_kernel_reduce stackResult792 := WordToStack.Native.compileProgNative
  riscvConfig false Word792.program PrefixChecks.Shard728.arity registers (.nil, 3747)
theorem stackResult792_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word792.program
      PrefixChecks.Shard728.arity registers (prefixList, 3747) =
    (stackResult792.1, stackResult792.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult792.2.2.1, 3755)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word792.program
    PrefixChecks.Shard728.arity registers prefixList 3747
    stackResult792.1 stackResult792.2.1 stackResult792.2.2.1 3755 stackResult792_eq
wave8_kernel_reduce stackResult793 := WordToStack.Native.compileProgNative
  riscvConfig false Word793.program PrefixChecks.Shard729.arity registers (.nil, 3755)
theorem stackResult793_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word793.program
      PrefixChecks.Shard729.arity registers (prefixList, 3755) =
    (stackResult793.1, stackResult793.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult793.2.2.1, 3769)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word793.program
    PrefixChecks.Shard729.arity registers prefixList 3755
    stackResult793.1 stackResult793.2.1 stackResult793.2.2.1 3769 stackResult793_eq
wave8_kernel_reduce stackResult794 := WordToStack.Native.compileProgNative
  riscvConfig false Word794.program PrefixChecks.Shard730.arity registers (.nil, 3769)
theorem stackResult794_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word794.program
      PrefixChecks.Shard730.arity registers (prefixList, 3769) =
    (stackResult794.1, stackResult794.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult794.2.2.1, 3780)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word794.program
    PrefixChecks.Shard730.arity registers prefixList 3769
    stackResult794.1 stackResult794.2.1 stackResult794.2.2.1 3780 stackResult794_eq
wave8_kernel_reduce stackResult795 := WordToStack.Native.compileProgNative
  riscvConfig false Word795.program PrefixChecks.Shard731.arity registers (.nil, 3780)
theorem stackResult795_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word795.program
      PrefixChecks.Shard731.arity registers (prefixList, 3780) =
    (stackResult795.1, stackResult795.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult795.2.2.1, 3789)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word795.program
    PrefixChecks.Shard731.arity registers prefixList 3780
    stackResult795.1 stackResult795.2.1 stackResult795.2.2.1 3789 stackResult795_eq
wave8_kernel_reduce stackResult796 := WordToStack.Native.compileProgNative
  riscvConfig false Word796.program PrefixChecks.Shard732.arity registers (.nil, 3789)
theorem stackResult796_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word796.program
      PrefixChecks.Shard732.arity registers (prefixList, 3789) =
    (stackResult796.1, stackResult796.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult796.2.2.1, 3817)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word796.program
    PrefixChecks.Shard732.arity registers prefixList 3789
    stackResult796.1 stackResult796.2.1 stackResult796.2.2.1 3817 stackResult796_eq
wave8_kernel_reduce stackResult797 := WordToStack.Native.compileProgNative
  riscvConfig false Word797.program PrefixChecks.Shard733.arity registers (.nil, 3817)
theorem stackResult797_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word797.program
      PrefixChecks.Shard733.arity registers (prefixList, 3817) =
    (stackResult797.1, stackResult797.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult797.2.2.1, 3820)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word797.program
    PrefixChecks.Shard733.arity registers prefixList 3817
    stackResult797.1 stackResult797.2.1 stackResult797.2.2.1 3820 stackResult797_eq
wave8_kernel_reduce stackResult798 := WordToStack.Native.compileProgNative
  riscvConfig false Word798.program PrefixChecks.Shard734.arity registers (.nil, 3820)
theorem stackResult798_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word798.program
      PrefixChecks.Shard734.arity registers (prefixList, 3820) =
    (stackResult798.1, stackResult798.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult798.2.2.1, 3834)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word798.program
    PrefixChecks.Shard734.arity registers prefixList 3820
    stackResult798.1 stackResult798.2.1 stackResult798.2.2.1 3834 stackResult798_eq
wave8_kernel_reduce stackResult799 := WordToStack.Native.compileProgNative
  riscvConfig false Word799.program PrefixChecks.Shard735.arity registers (.nil, 3834)
theorem stackResult799_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word799.program
      PrefixChecks.Shard735.arity registers (prefixList, 3834) =
    (stackResult799.1, stackResult799.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult799.2.2.1, 3840)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word799.program
    PrefixChecks.Shard735.arity registers prefixList 3834
    stackResult799.1 stackResult799.2.1 stackResult799.2.2.1 3840 stackResult799_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard720.name, PrefixChecks.Shard720.arity, Word784.program),
  (PrefixChecks.Shard721.name, PrefixChecks.Shard721.arity, Word785.program),
  (PrefixChecks.Shard722.name, PrefixChecks.Shard722.arity, Word786.program),
  (PrefixChecks.Shard723.name, PrefixChecks.Shard723.arity, Word787.program),
  (PrefixChecks.Shard724.name, PrefixChecks.Shard724.arity, Word788.program),
  (PrefixChecks.Shard725.name, PrefixChecks.Shard725.arity, Word789.program),
  (PrefixChecks.Shard726.name, PrefixChecks.Shard726.arity, Word790.program),
  (PrefixChecks.Shard727.name, PrefixChecks.Shard727.arity, Word791.program),
  (PrefixChecks.Shard728.name, PrefixChecks.Shard728.arity, Word792.program),
  (PrefixChecks.Shard729.name, PrefixChecks.Shard729.arity, Word793.program),
  (PrefixChecks.Shard730.name, PrefixChecks.Shard730.arity, Word794.program),
  (PrefixChecks.Shard731.name, PrefixChecks.Shard731.arity, Word795.program),
  (PrefixChecks.Shard732.name, PrefixChecks.Shard732.arity, Word796.program),
  (PrefixChecks.Shard733.name, PrefixChecks.Shard733.arity, Word797.program),
  (PrefixChecks.Shard734.name, PrefixChecks.Shard734.arity, Word798.program),
  (PrefixChecks.Shard735.name, PrefixChecks.Shard735.arity, Word799.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard720.name, stackResult784.1),
  (PrefixChecks.Shard721.name, stackResult785.1),
  (PrefixChecks.Shard722.name, stackResult786.1),
  (PrefixChecks.Shard723.name, stackResult787.1),
  (PrefixChecks.Shard724.name, stackResult788.1),
  (PrefixChecks.Shard725.name, stackResult789.1),
  (PrefixChecks.Shard726.name, stackResult790.1),
  (PrefixChecks.Shard727.name, stackResult791.1),
  (PrefixChecks.Shard728.name, stackResult792.1),
  (PrefixChecks.Shard729.name, stackResult793.1),
  (PrefixChecks.Shard730.name, stackResult794.1),
  (PrefixChecks.Shard731.name, stackResult795.1),
  (PrefixChecks.Shard732.name, stackResult796.1),
  (PrefixChecks.Shard733.name, stackResult797.1),
  (PrefixChecks.Shard734.name, stackResult798.1),
  (PrefixChecks.Shard735.name, stackResult799.1)
]

noncomputable def frames : List Nat := [
  stackResult784.2.1,
  stackResult785.2.1,
  stackResult786.2.1,
  stackResult787.2.1,
  stackResult788.2.1,
  stackResult789.2.1,
  stackResult790.2.1,
  stackResult791.2.1,
  stackResult792.2.1,
  stackResult793.2.1,
  stackResult794.2.1,
  stackResult795.2.1,
  stackResult796.2.1,
  stackResult797.2.1,
  stackResult798.2.1,
  stackResult799.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult784.2.2.1) stackResult785.2.2.1) stackResult786.2.2.1) stackResult787.2.2.1) stackResult788.2.2.1) stackResult789.2.2.1) stackResult790.2.2.1) stackResult791.2.2.1) stackResult792.2.2.1) stackResult793.2.2.1) stackResult794.2.2.1) stackResult795.2.2.1) stackResult796.2.2.1) stackResult797.2.2.1) stackResult798.2.2.1) stackResult799.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 3617) = (bodies, frames, (bitmapDelta, 3840)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult784_from _
  apply compileWordToStack_cons
  · exact stackResult785_from _
  apply compileWordToStack_cons
  · exact stackResult786_from _
  apply compileWordToStack_cons
  · exact stackResult787_from _
  apply compileWordToStack_cons
  · exact stackResult788_from _
  apply compileWordToStack_cons
  · exact stackResult789_from _
  apply compileWordToStack_cons
  · exact stackResult790_from _
  apply compileWordToStack_cons
  · exact stackResult791_from _
  apply compileWordToStack_cons
  · exact stackResult792_from _
  apply compileWordToStack_cons
  · exact stackResult793_from _
  apply compileWordToStack_cons
  · exact stackResult794_from _
  apply compileWordToStack_cons
  · exact stackResult795_from _
  apply compileWordToStack_cons
  · exact stackResult796_from _
  apply compileWordToStack_cons
  · exact stackResult797_from _
  apply compileWordToStack_cons
  · exact stackResult798_from _
  apply compileWordToStack_cons
  · exact stackResult799_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 3617) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 3840)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 3617 bodies frames bitmapDelta 3840 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 720).take 16).zip
      [oracle784, oracle785, oracle786, oracle787, oracle788, oracle789, oracle790, oracle791, oracle792, oracle793, oracle794, oracle795, oracle796, oracle797, oracle798, oracle799]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle784 PrefixChecks.Shard720.entry,
    wordFunction oracle785 PrefixChecks.Shard721.entry,
    wordFunction oracle786 PrefixChecks.Shard722.entry,
    wordFunction oracle787 PrefixChecks.Shard723.entry,
    wordFunction oracle788 PrefixChecks.Shard724.entry,
    wordFunction oracle789 PrefixChecks.Shard725.entry,
    wordFunction oracle790 PrefixChecks.Shard726.entry,
    wordFunction oracle791 PrefixChecks.Shard727.entry,
    wordFunction oracle792 PrefixChecks.Shard728.entry,
    wordFunction oracle793 PrefixChecks.Shard729.entry,
    wordFunction oracle794 PrefixChecks.Shard730.entry,
    wordFunction oracle795 PrefixChecks.Shard731.entry,
    wordFunction oracle796 PrefixChecks.Shard732.entry,
    wordFunction oracle797 PrefixChecks.Shard733.entry,
    wordFunction oracle798 PrefixChecks.Shard734.entry,
    wordFunction oracle799 PrefixChecks.Shard735.entry] = words
  simp only [
    Word784.wordFunction_eq,
    Word785.wordFunction_eq,
    Word786.wordFunction_eq,
    Word787.wordFunction_eq,
    Word788.wordFunction_eq,
    Word789.wordFunction_eq,
    Word790.wordFunction_eq,
    Word791.wordFunction_eq,
    Word792.wordFunction_eq,
    Word793.wordFunction_eq,
    Word794.wordFunction_eq,
    Word795.wordFunction_eq,
    Word796.wordFunction_eq,
    Word797.wordFunction_eq,
    Word798.wordFunction_eq,
    Word799.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk45
