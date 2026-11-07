import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word704
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word705
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word706
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word707
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word708
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word709
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word710
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word711
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word712
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word713
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word714
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word715
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word716
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word717
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word718
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word719
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk40
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult704 := WordToStack.Native.compileProgNative
  riscvConfig false Word704.program PrefixChecks.Shard640.arity registers (.nil, 3150)
theorem stackResult704_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word704.program
      PrefixChecks.Shard640.arity registers (prefixList, 3150) =
    (stackResult704.1, stackResult704.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult704.2.2.1, 3151)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word704.program
    PrefixChecks.Shard640.arity registers prefixList 3150
    stackResult704.1 stackResult704.2.1 stackResult704.2.2.1 3151 stackResult704_eq
wave8_kernel_reduce stackResult705 := WordToStack.Native.compileProgNative
  riscvConfig false Word705.program PrefixChecks.Shard641.arity registers (.nil, 3151)
theorem stackResult705_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word705.program
      PrefixChecks.Shard641.arity registers (prefixList, 3151) =
    (stackResult705.1, stackResult705.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult705.2.2.1, 3151)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word705.program
    PrefixChecks.Shard641.arity registers prefixList 3151
    stackResult705.1 stackResult705.2.1 stackResult705.2.2.1 3151 stackResult705_eq
wave8_kernel_reduce stackResult706 := WordToStack.Native.compileProgNative
  riscvConfig false Word706.program PrefixChecks.Shard642.arity registers (.nil, 3151)
theorem stackResult706_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word706.program
      PrefixChecks.Shard642.arity registers (prefixList, 3151) =
    (stackResult706.1, stackResult706.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult706.2.2.1, 3151)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word706.program
    PrefixChecks.Shard642.arity registers prefixList 3151
    stackResult706.1 stackResult706.2.1 stackResult706.2.2.1 3151 stackResult706_eq
wave8_kernel_reduce stackResult707 := WordToStack.Native.compileProgNative
  riscvConfig false Word707.program PrefixChecks.Shard643.arity registers (.nil, 3151)
theorem stackResult707_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word707.program
      PrefixChecks.Shard643.arity registers (prefixList, 3151) =
    (stackResult707.1, stackResult707.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult707.2.2.1, 3151)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word707.program
    PrefixChecks.Shard643.arity registers prefixList 3151
    stackResult707.1 stackResult707.2.1 stackResult707.2.2.1 3151 stackResult707_eq
wave8_kernel_reduce stackResult708 := WordToStack.Native.compileProgNative
  riscvConfig false Word708.program PrefixChecks.Shard644.arity registers (.nil, 3151)
theorem stackResult708_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word708.program
      PrefixChecks.Shard644.arity registers (prefixList, 3151) =
    (stackResult708.1, stackResult708.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult708.2.2.1, 3151)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word708.program
    PrefixChecks.Shard644.arity registers prefixList 3151
    stackResult708.1 stackResult708.2.1 stackResult708.2.2.1 3151 stackResult708_eq
wave8_kernel_reduce stackResult709 := WordToStack.Native.compileProgNative
  riscvConfig false Word709.program PrefixChecks.Shard645.arity registers (.nil, 3151)
theorem stackResult709_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word709.program
      PrefixChecks.Shard645.arity registers (prefixList, 3151) =
    (stackResult709.1, stackResult709.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult709.2.2.1, 3151)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word709.program
    PrefixChecks.Shard645.arity registers prefixList 3151
    stackResult709.1 stackResult709.2.1 stackResult709.2.2.1 3151 stackResult709_eq
wave8_kernel_reduce stackResult710 := WordToStack.Native.compileProgNative
  riscvConfig false Word710.program PrefixChecks.Shard646.arity registers (.nil, 3151)
theorem stackResult710_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word710.program
      PrefixChecks.Shard646.arity registers (prefixList, 3151) =
    (stackResult710.1, stackResult710.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult710.2.2.1, 3153)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word710.program
    PrefixChecks.Shard646.arity registers prefixList 3151
    stackResult710.1 stackResult710.2.1 stackResult710.2.2.1 3153 stackResult710_eq
wave8_kernel_reduce stackResult711 := WordToStack.Native.compileProgNative
  riscvConfig false Word711.program PrefixChecks.Shard647.arity registers (.nil, 3153)
theorem stackResult711_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word711.program
      PrefixChecks.Shard647.arity registers (prefixList, 3153) =
    (stackResult711.1, stackResult711.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult711.2.2.1, 3155)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word711.program
    PrefixChecks.Shard647.arity registers prefixList 3153
    stackResult711.1 stackResult711.2.1 stackResult711.2.2.1 3155 stackResult711_eq
wave8_kernel_reduce stackResult712 := WordToStack.Native.compileProgNative
  riscvConfig false Word712.program PrefixChecks.Shard648.arity registers (.nil, 3155)
theorem stackResult712_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word712.program
      PrefixChecks.Shard648.arity registers (prefixList, 3155) =
    (stackResult712.1, stackResult712.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult712.2.2.1, 3157)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word712.program
    PrefixChecks.Shard648.arity registers prefixList 3155
    stackResult712.1 stackResult712.2.1 stackResult712.2.2.1 3157 stackResult712_eq
wave8_kernel_reduce stackResult713 := WordToStack.Native.compileProgNative
  riscvConfig false Word713.program PrefixChecks.Shard649.arity registers (.nil, 3157)
theorem stackResult713_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word713.program
      PrefixChecks.Shard649.arity registers (prefixList, 3157) =
    (stackResult713.1, stackResult713.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult713.2.2.1, 3157)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word713.program
    PrefixChecks.Shard649.arity registers prefixList 3157
    stackResult713.1 stackResult713.2.1 stackResult713.2.2.1 3157 stackResult713_eq
wave8_kernel_reduce stackResult714 := WordToStack.Native.compileProgNative
  riscvConfig false Word714.program PrefixChecks.Shard650.arity registers (.nil, 3157)
theorem stackResult714_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word714.program
      PrefixChecks.Shard650.arity registers (prefixList, 3157) =
    (stackResult714.1, stackResult714.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult714.2.2.1, 3230)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word714.program
    PrefixChecks.Shard650.arity registers prefixList 3157
    stackResult714.1 stackResult714.2.1 stackResult714.2.2.1 3230 stackResult714_eq
wave8_kernel_reduce stackResult715 := WordToStack.Native.compileProgNative
  riscvConfig false Word715.program PrefixChecks.Shard651.arity registers (.nil, 3230)
theorem stackResult715_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word715.program
      PrefixChecks.Shard651.arity registers (prefixList, 3230) =
    (stackResult715.1, stackResult715.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult715.2.2.1, 3230)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word715.program
    PrefixChecks.Shard651.arity registers prefixList 3230
    stackResult715.1 stackResult715.2.1 stackResult715.2.2.1 3230 stackResult715_eq
wave8_kernel_reduce stackResult716 := WordToStack.Native.compileProgNative
  riscvConfig false Word716.program PrefixChecks.Shard652.arity registers (.nil, 3230)
theorem stackResult716_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word716.program
      PrefixChecks.Shard652.arity registers (prefixList, 3230) =
    (stackResult716.1, stackResult716.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult716.2.2.1, 3230)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word716.program
    PrefixChecks.Shard652.arity registers prefixList 3230
    stackResult716.1 stackResult716.2.1 stackResult716.2.2.1 3230 stackResult716_eq
wave8_kernel_reduce stackResult717 := WordToStack.Native.compileProgNative
  riscvConfig false Word717.program PrefixChecks.Shard653.arity registers (.nil, 3230)
theorem stackResult717_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word717.program
      PrefixChecks.Shard653.arity registers (prefixList, 3230) =
    (stackResult717.1, stackResult717.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult717.2.2.1, 3230)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word717.program
    PrefixChecks.Shard653.arity registers prefixList 3230
    stackResult717.1 stackResult717.2.1 stackResult717.2.2.1 3230 stackResult717_eq
wave8_kernel_reduce stackResult718 := WordToStack.Native.compileProgNative
  riscvConfig false Word718.program PrefixChecks.Shard654.arity registers (.nil, 3230)
theorem stackResult718_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word718.program
      PrefixChecks.Shard654.arity registers (prefixList, 3230) =
    (stackResult718.1, stackResult718.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult718.2.2.1, 3230)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word718.program
    PrefixChecks.Shard654.arity registers prefixList 3230
    stackResult718.1 stackResult718.2.1 stackResult718.2.2.1 3230 stackResult718_eq
wave8_kernel_reduce stackResult719 := WordToStack.Native.compileProgNative
  riscvConfig false Word719.program PrefixChecks.Shard655.arity registers (.nil, 3230)
theorem stackResult719_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word719.program
      PrefixChecks.Shard655.arity registers (prefixList, 3230) =
    (stackResult719.1, stackResult719.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult719.2.2.1, 3231)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word719.program
    PrefixChecks.Shard655.arity registers prefixList 3230
    stackResult719.1 stackResult719.2.1 stackResult719.2.2.1 3231 stackResult719_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard640.name, PrefixChecks.Shard640.arity, Word704.program),
  (PrefixChecks.Shard641.name, PrefixChecks.Shard641.arity, Word705.program),
  (PrefixChecks.Shard642.name, PrefixChecks.Shard642.arity, Word706.program),
  (PrefixChecks.Shard643.name, PrefixChecks.Shard643.arity, Word707.program),
  (PrefixChecks.Shard644.name, PrefixChecks.Shard644.arity, Word708.program),
  (PrefixChecks.Shard645.name, PrefixChecks.Shard645.arity, Word709.program),
  (PrefixChecks.Shard646.name, PrefixChecks.Shard646.arity, Word710.program),
  (PrefixChecks.Shard647.name, PrefixChecks.Shard647.arity, Word711.program),
  (PrefixChecks.Shard648.name, PrefixChecks.Shard648.arity, Word712.program),
  (PrefixChecks.Shard649.name, PrefixChecks.Shard649.arity, Word713.program),
  (PrefixChecks.Shard650.name, PrefixChecks.Shard650.arity, Word714.program),
  (PrefixChecks.Shard651.name, PrefixChecks.Shard651.arity, Word715.program),
  (PrefixChecks.Shard652.name, PrefixChecks.Shard652.arity, Word716.program),
  (PrefixChecks.Shard653.name, PrefixChecks.Shard653.arity, Word717.program),
  (PrefixChecks.Shard654.name, PrefixChecks.Shard654.arity, Word718.program),
  (PrefixChecks.Shard655.name, PrefixChecks.Shard655.arity, Word719.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard640.name, stackResult704.1),
  (PrefixChecks.Shard641.name, stackResult705.1),
  (PrefixChecks.Shard642.name, stackResult706.1),
  (PrefixChecks.Shard643.name, stackResult707.1),
  (PrefixChecks.Shard644.name, stackResult708.1),
  (PrefixChecks.Shard645.name, stackResult709.1),
  (PrefixChecks.Shard646.name, stackResult710.1),
  (PrefixChecks.Shard647.name, stackResult711.1),
  (PrefixChecks.Shard648.name, stackResult712.1),
  (PrefixChecks.Shard649.name, stackResult713.1),
  (PrefixChecks.Shard650.name, stackResult714.1),
  (PrefixChecks.Shard651.name, stackResult715.1),
  (PrefixChecks.Shard652.name, stackResult716.1),
  (PrefixChecks.Shard653.name, stackResult717.1),
  (PrefixChecks.Shard654.name, stackResult718.1),
  (PrefixChecks.Shard655.name, stackResult719.1)
]

noncomputable def frames : List Nat := [
  stackResult704.2.1,
  stackResult705.2.1,
  stackResult706.2.1,
  stackResult707.2.1,
  stackResult708.2.1,
  stackResult709.2.1,
  stackResult710.2.1,
  stackResult711.2.1,
  stackResult712.2.1,
  stackResult713.2.1,
  stackResult714.2.1,
  stackResult715.2.1,
  stackResult716.2.1,
  stackResult717.2.1,
  stackResult718.2.1,
  stackResult719.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult704.2.2.1) stackResult705.2.2.1) stackResult706.2.2.1) stackResult707.2.2.1) stackResult708.2.2.1) stackResult709.2.2.1) stackResult710.2.2.1) stackResult711.2.2.1) stackResult712.2.2.1) stackResult713.2.2.1) stackResult714.2.2.1) stackResult715.2.2.1) stackResult716.2.2.1) stackResult717.2.2.1) stackResult718.2.2.1) stackResult719.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 3150) = (bodies, frames, (bitmapDelta, 3231)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult704_from _
  apply compileWordToStack_cons
  · exact stackResult705_from _
  apply compileWordToStack_cons
  · exact stackResult706_from _
  apply compileWordToStack_cons
  · exact stackResult707_from _
  apply compileWordToStack_cons
  · exact stackResult708_from _
  apply compileWordToStack_cons
  · exact stackResult709_from _
  apply compileWordToStack_cons
  · exact stackResult710_from _
  apply compileWordToStack_cons
  · exact stackResult711_from _
  apply compileWordToStack_cons
  · exact stackResult712_from _
  apply compileWordToStack_cons
  · exact stackResult713_from _
  apply compileWordToStack_cons
  · exact stackResult714_from _
  apply compileWordToStack_cons
  · exact stackResult715_from _
  apply compileWordToStack_cons
  · exact stackResult716_from _
  apply compileWordToStack_cons
  · exact stackResult717_from _
  apply compileWordToStack_cons
  · exact stackResult718_from _
  apply compileWordToStack_cons
  · exact stackResult719_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 3150) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 3231)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 3150 bodies frames bitmapDelta 3231 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 640).take 16).zip
      [oracle704, oracle705, oracle706, oracle707, oracle708, oracle709, oracle710, oracle711, oracle712, oracle713, oracle714, oracle715, oracle716, oracle717, oracle718, oracle719]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle704 PrefixChecks.Shard640.entry,
    wordFunction oracle705 PrefixChecks.Shard641.entry,
    wordFunction oracle706 PrefixChecks.Shard642.entry,
    wordFunction oracle707 PrefixChecks.Shard643.entry,
    wordFunction oracle708 PrefixChecks.Shard644.entry,
    wordFunction oracle709 PrefixChecks.Shard645.entry,
    wordFunction oracle710 PrefixChecks.Shard646.entry,
    wordFunction oracle711 PrefixChecks.Shard647.entry,
    wordFunction oracle712 PrefixChecks.Shard648.entry,
    wordFunction oracle713 PrefixChecks.Shard649.entry,
    wordFunction oracle714 PrefixChecks.Shard650.entry,
    wordFunction oracle715 PrefixChecks.Shard651.entry,
    wordFunction oracle716 PrefixChecks.Shard652.entry,
    wordFunction oracle717 PrefixChecks.Shard653.entry,
    wordFunction oracle718 PrefixChecks.Shard654.entry,
    wordFunction oracle719 PrefixChecks.Shard655.entry] = words
  simp only [
    Word704.wordFunction_eq,
    Word705.wordFunction_eq,
    Word706.wordFunction_eq,
    Word707.wordFunction_eq,
    Word708.wordFunction_eq,
    Word709.wordFunction_eq,
    Word710.wordFunction_eq,
    Word711.wordFunction_eq,
    Word712.wordFunction_eq,
    Word713.wordFunction_eq,
    Word714.wordFunction_eq,
    Word715.wordFunction_eq,
    Word716.wordFunction_eq,
    Word717.wordFunction_eq,
    Word718.wordFunction_eq,
    Word719.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk40
