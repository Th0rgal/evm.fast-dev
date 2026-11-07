import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word816
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word817
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word818
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word819
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word820
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word821
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word822
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word823
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word824
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word825
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word826
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word827
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word828
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word829
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word830
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word831
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk47
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult816 := WordToStack.Native.compileProgNative
  riscvConfig false Word816.program PrefixChecks.Shard752.arity registers (.nil, 4058)
theorem stackResult816_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word816.program
      PrefixChecks.Shard752.arity registers (prefixList, 4058) =
    (stackResult816.1, stackResult816.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult816.2.2.1, 4067)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word816.program
    PrefixChecks.Shard752.arity registers prefixList 4058
    stackResult816.1 stackResult816.2.1 stackResult816.2.2.1 4067 stackResult816_eq
wave8_kernel_reduce stackResult817 := WordToStack.Native.compileProgNative
  riscvConfig false Word817.program PrefixChecks.Shard753.arity registers (.nil, 4067)
theorem stackResult817_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word817.program
      PrefixChecks.Shard753.arity registers (prefixList, 4067) =
    (stackResult817.1, stackResult817.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult817.2.2.1, 4087)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word817.program
    PrefixChecks.Shard753.arity registers prefixList 4067
    stackResult817.1 stackResult817.2.1 stackResult817.2.2.1 4087 stackResult817_eq
wave8_kernel_reduce stackResult818 := WordToStack.Native.compileProgNative
  riscvConfig false Word818.program PrefixChecks.Shard754.arity registers (.nil, 4087)
theorem stackResult818_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word818.program
      PrefixChecks.Shard754.arity registers (prefixList, 4087) =
    (stackResult818.1, stackResult818.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult818.2.2.1, 4089)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word818.program
    PrefixChecks.Shard754.arity registers prefixList 4087
    stackResult818.1 stackResult818.2.1 stackResult818.2.2.1 4089 stackResult818_eq
wave8_kernel_reduce stackResult819 := WordToStack.Native.compileProgNative
  riscvConfig false Word819.program PrefixChecks.Shard755.arity registers (.nil, 4089)
theorem stackResult819_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word819.program
      PrefixChecks.Shard755.arity registers (prefixList, 4089) =
    (stackResult819.1, stackResult819.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult819.2.2.1, 4089)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word819.program
    PrefixChecks.Shard755.arity registers prefixList 4089
    stackResult819.1 stackResult819.2.1 stackResult819.2.2.1 4089 stackResult819_eq
wave8_kernel_reduce stackResult820 := WordToStack.Native.compileProgNative
  riscvConfig false Word820.program PrefixChecks.Shard756.arity registers (.nil, 4089)
theorem stackResult820_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word820.program
      PrefixChecks.Shard756.arity registers (prefixList, 4089) =
    (stackResult820.1, stackResult820.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult820.2.2.1, 4089)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word820.program
    PrefixChecks.Shard756.arity registers prefixList 4089
    stackResult820.1 stackResult820.2.1 stackResult820.2.2.1 4089 stackResult820_eq
wave8_kernel_reduce stackResult821 := WordToStack.Native.compileProgNative
  riscvConfig false Word821.program PrefixChecks.Shard757.arity registers (.nil, 4089)
theorem stackResult821_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word821.program
      PrefixChecks.Shard757.arity registers (prefixList, 4089) =
    (stackResult821.1, stackResult821.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult821.2.2.1, 4092)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word821.program
    PrefixChecks.Shard757.arity registers prefixList 4089
    stackResult821.1 stackResult821.2.1 stackResult821.2.2.1 4092 stackResult821_eq
wave8_kernel_reduce stackResult822 := WordToStack.Native.compileProgNative
  riscvConfig false Word822.program PrefixChecks.Shard758.arity registers (.nil, 4092)
theorem stackResult822_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word822.program
      PrefixChecks.Shard758.arity registers (prefixList, 4092) =
    (stackResult822.1, stackResult822.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult822.2.2.1, 4098)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word822.program
    PrefixChecks.Shard758.arity registers prefixList 4092
    stackResult822.1 stackResult822.2.1 stackResult822.2.2.1 4098 stackResult822_eq
wave8_kernel_reduce stackResult823 := WordToStack.Native.compileProgNative
  riscvConfig false Word823.program PrefixChecks.Shard759.arity registers (.nil, 4098)
theorem stackResult823_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word823.program
      PrefixChecks.Shard759.arity registers (prefixList, 4098) =
    (stackResult823.1, stackResult823.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult823.2.2.1, 4101)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word823.program
    PrefixChecks.Shard759.arity registers prefixList 4098
    stackResult823.1 stackResult823.2.1 stackResult823.2.2.1 4101 stackResult823_eq
wave8_kernel_reduce stackResult824 := WordToStack.Native.compileProgNative
  riscvConfig false Word824.program PrefixChecks.Shard760.arity registers (.nil, 4101)
theorem stackResult824_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word824.program
      PrefixChecks.Shard760.arity registers (prefixList, 4101) =
    (stackResult824.1, stackResult824.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult824.2.2.1, 4107)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word824.program
    PrefixChecks.Shard760.arity registers prefixList 4101
    stackResult824.1 stackResult824.2.1 stackResult824.2.2.1 4107 stackResult824_eq
wave8_kernel_reduce stackResult825 := WordToStack.Native.compileProgNative
  riscvConfig false Word825.program PrefixChecks.Shard761.arity registers (.nil, 4107)
theorem stackResult825_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word825.program
      PrefixChecks.Shard761.arity registers (prefixList, 4107) =
    (stackResult825.1, stackResult825.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult825.2.2.1, 4111)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word825.program
    PrefixChecks.Shard761.arity registers prefixList 4107
    stackResult825.1 stackResult825.2.1 stackResult825.2.2.1 4111 stackResult825_eq
wave8_kernel_reduce stackResult826 := WordToStack.Native.compileProgNative
  riscvConfig false Word826.program PrefixChecks.Shard762.arity registers (.nil, 4111)
theorem stackResult826_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word826.program
      PrefixChecks.Shard762.arity registers (prefixList, 4111) =
    (stackResult826.1, stackResult826.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult826.2.2.1, 4114)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word826.program
    PrefixChecks.Shard762.arity registers prefixList 4111
    stackResult826.1 stackResult826.2.1 stackResult826.2.2.1 4114 stackResult826_eq
wave8_kernel_reduce stackResult827 := WordToStack.Native.compileProgNative
  riscvConfig false Word827.program PrefixChecks.Shard763.arity registers (.nil, 4114)
theorem stackResult827_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word827.program
      PrefixChecks.Shard763.arity registers (prefixList, 4114) =
    (stackResult827.1, stackResult827.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult827.2.2.1, 4117)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word827.program
    PrefixChecks.Shard763.arity registers prefixList 4114
    stackResult827.1 stackResult827.2.1 stackResult827.2.2.1 4117 stackResult827_eq
wave8_kernel_reduce stackResult828 := WordToStack.Native.compileProgNative
  riscvConfig false Word828.program PrefixChecks.Shard764.arity registers (.nil, 4117)
theorem stackResult828_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word828.program
      PrefixChecks.Shard764.arity registers (prefixList, 4117) =
    (stackResult828.1, stackResult828.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult828.2.2.1, 4120)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word828.program
    PrefixChecks.Shard764.arity registers prefixList 4117
    stackResult828.1 stackResult828.2.1 stackResult828.2.2.1 4120 stackResult828_eq
wave8_kernel_reduce stackResult829 := WordToStack.Native.compileProgNative
  riscvConfig false Word829.program PrefixChecks.Shard765.arity registers (.nil, 4120)
theorem stackResult829_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word829.program
      PrefixChecks.Shard765.arity registers (prefixList, 4120) =
    (stackResult829.1, stackResult829.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult829.2.2.1, 4121)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word829.program
    PrefixChecks.Shard765.arity registers prefixList 4120
    stackResult829.1 stackResult829.2.1 stackResult829.2.2.1 4121 stackResult829_eq
wave8_kernel_reduce stackResult830 := WordToStack.Native.compileProgNative
  riscvConfig false Word830.program PrefixChecks.Shard766.arity registers (.nil, 4121)
theorem stackResult830_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word830.program
      PrefixChecks.Shard766.arity registers (prefixList, 4121) =
    (stackResult830.1, stackResult830.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult830.2.2.1, 4123)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word830.program
    PrefixChecks.Shard766.arity registers prefixList 4121
    stackResult830.1 stackResult830.2.1 stackResult830.2.2.1 4123 stackResult830_eq
wave8_kernel_reduce stackResult831 := WordToStack.Native.compileProgNative
  riscvConfig false Word831.program PrefixChecks.Shard767.arity registers (.nil, 4123)
theorem stackResult831_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word831.program
      PrefixChecks.Shard767.arity registers (prefixList, 4123) =
    (stackResult831.1, stackResult831.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult831.2.2.1, 4127)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word831.program
    PrefixChecks.Shard767.arity registers prefixList 4123
    stackResult831.1 stackResult831.2.1 stackResult831.2.2.1 4127 stackResult831_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard752.name, PrefixChecks.Shard752.arity, Word816.program),
  (PrefixChecks.Shard753.name, PrefixChecks.Shard753.arity, Word817.program),
  (PrefixChecks.Shard754.name, PrefixChecks.Shard754.arity, Word818.program),
  (PrefixChecks.Shard755.name, PrefixChecks.Shard755.arity, Word819.program),
  (PrefixChecks.Shard756.name, PrefixChecks.Shard756.arity, Word820.program),
  (PrefixChecks.Shard757.name, PrefixChecks.Shard757.arity, Word821.program),
  (PrefixChecks.Shard758.name, PrefixChecks.Shard758.arity, Word822.program),
  (PrefixChecks.Shard759.name, PrefixChecks.Shard759.arity, Word823.program),
  (PrefixChecks.Shard760.name, PrefixChecks.Shard760.arity, Word824.program),
  (PrefixChecks.Shard761.name, PrefixChecks.Shard761.arity, Word825.program),
  (PrefixChecks.Shard762.name, PrefixChecks.Shard762.arity, Word826.program),
  (PrefixChecks.Shard763.name, PrefixChecks.Shard763.arity, Word827.program),
  (PrefixChecks.Shard764.name, PrefixChecks.Shard764.arity, Word828.program),
  (PrefixChecks.Shard765.name, PrefixChecks.Shard765.arity, Word829.program),
  (PrefixChecks.Shard766.name, PrefixChecks.Shard766.arity, Word830.program),
  (PrefixChecks.Shard767.name, PrefixChecks.Shard767.arity, Word831.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard752.name, stackResult816.1),
  (PrefixChecks.Shard753.name, stackResult817.1),
  (PrefixChecks.Shard754.name, stackResult818.1),
  (PrefixChecks.Shard755.name, stackResult819.1),
  (PrefixChecks.Shard756.name, stackResult820.1),
  (PrefixChecks.Shard757.name, stackResult821.1),
  (PrefixChecks.Shard758.name, stackResult822.1),
  (PrefixChecks.Shard759.name, stackResult823.1),
  (PrefixChecks.Shard760.name, stackResult824.1),
  (PrefixChecks.Shard761.name, stackResult825.1),
  (PrefixChecks.Shard762.name, stackResult826.1),
  (PrefixChecks.Shard763.name, stackResult827.1),
  (PrefixChecks.Shard764.name, stackResult828.1),
  (PrefixChecks.Shard765.name, stackResult829.1),
  (PrefixChecks.Shard766.name, stackResult830.1),
  (PrefixChecks.Shard767.name, stackResult831.1)
]

noncomputable def frames : List Nat := [
  stackResult816.2.1,
  stackResult817.2.1,
  stackResult818.2.1,
  stackResult819.2.1,
  stackResult820.2.1,
  stackResult821.2.1,
  stackResult822.2.1,
  stackResult823.2.1,
  stackResult824.2.1,
  stackResult825.2.1,
  stackResult826.2.1,
  stackResult827.2.1,
  stackResult828.2.1,
  stackResult829.2.1,
  stackResult830.2.1,
  stackResult831.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult816.2.2.1) stackResult817.2.2.1) stackResult818.2.2.1) stackResult819.2.2.1) stackResult820.2.2.1) stackResult821.2.2.1) stackResult822.2.2.1) stackResult823.2.2.1) stackResult824.2.2.1) stackResult825.2.2.1) stackResult826.2.2.1) stackResult827.2.2.1) stackResult828.2.2.1) stackResult829.2.2.1) stackResult830.2.2.1) stackResult831.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 4058) = (bodies, frames, (bitmapDelta, 4127)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult816_from _
  apply compileWordToStack_cons
  · exact stackResult817_from _
  apply compileWordToStack_cons
  · exact stackResult818_from _
  apply compileWordToStack_cons
  · exact stackResult819_from _
  apply compileWordToStack_cons
  · exact stackResult820_from _
  apply compileWordToStack_cons
  · exact stackResult821_from _
  apply compileWordToStack_cons
  · exact stackResult822_from _
  apply compileWordToStack_cons
  · exact stackResult823_from _
  apply compileWordToStack_cons
  · exact stackResult824_from _
  apply compileWordToStack_cons
  · exact stackResult825_from _
  apply compileWordToStack_cons
  · exact stackResult826_from _
  apply compileWordToStack_cons
  · exact stackResult827_from _
  apply compileWordToStack_cons
  · exact stackResult828_from _
  apply compileWordToStack_cons
  · exact stackResult829_from _
  apply compileWordToStack_cons
  · exact stackResult830_from _
  apply compileWordToStack_cons
  · exact stackResult831_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 4058) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 4127)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 4058 bodies frames bitmapDelta 4127 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 752).take 16).zip
      [oracle816, oracle817, oracle818, oracle819, oracle820, oracle821, oracle822, oracle823, oracle824, oracle825, oracle826, oracle827, oracle828, oracle829, oracle830, oracle831]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle816 PrefixChecks.Shard752.entry,
    wordFunction oracle817 PrefixChecks.Shard753.entry,
    wordFunction oracle818 PrefixChecks.Shard754.entry,
    wordFunction oracle819 PrefixChecks.Shard755.entry,
    wordFunction oracle820 PrefixChecks.Shard756.entry,
    wordFunction oracle821 PrefixChecks.Shard757.entry,
    wordFunction oracle822 PrefixChecks.Shard758.entry,
    wordFunction oracle823 PrefixChecks.Shard759.entry,
    wordFunction oracle824 PrefixChecks.Shard760.entry,
    wordFunction oracle825 PrefixChecks.Shard761.entry,
    wordFunction oracle826 PrefixChecks.Shard762.entry,
    wordFunction oracle827 PrefixChecks.Shard763.entry,
    wordFunction oracle828 PrefixChecks.Shard764.entry,
    wordFunction oracle829 PrefixChecks.Shard765.entry,
    wordFunction oracle830 PrefixChecks.Shard766.entry,
    wordFunction oracle831 PrefixChecks.Shard767.entry] = words
  simp only [
    Word816.wordFunction_eq,
    Word817.wordFunction_eq,
    Word818.wordFunction_eq,
    Word819.wordFunction_eq,
    Word820.wordFunction_eq,
    Word821.wordFunction_eq,
    Word822.wordFunction_eq,
    Word823.wordFunction_eq,
    Word824.wordFunction_eq,
    Word825.wordFunction_eq,
    Word826.wordFunction_eq,
    Word827.wordFunction_eq,
    Word828.wordFunction_eq,
    Word829.wordFunction_eq,
    Word830.wordFunction_eq,
    Word831.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk47
