import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word640
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word641
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word642
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word643
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word644
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word645
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word646
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word647
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word648
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word649
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word650
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word651
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word652
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word653
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word654
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word655
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk36
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult640 := WordToStack.Native.compileProgNative
  riscvConfig false Word640.program PrefixChecks.Shard576.arity registers (.nil, 2592)
theorem stackResult640_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word640.program
      PrefixChecks.Shard576.arity registers (prefixList, 2592) =
    (stackResult640.1, stackResult640.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult640.2.2.1, 2593)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word640.program
    PrefixChecks.Shard576.arity registers prefixList 2592
    stackResult640.1 stackResult640.2.1 stackResult640.2.2.1 2593 stackResult640_eq
wave8_kernel_reduce stackResult641 := WordToStack.Native.compileProgNative
  riscvConfig false Word641.program PrefixChecks.Shard577.arity registers (.nil, 2593)
theorem stackResult641_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word641.program
      PrefixChecks.Shard577.arity registers (prefixList, 2593) =
    (stackResult641.1, stackResult641.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult641.2.2.1, 2618)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word641.program
    PrefixChecks.Shard577.arity registers prefixList 2593
    stackResult641.1 stackResult641.2.1 stackResult641.2.2.1 2618 stackResult641_eq
wave8_kernel_reduce stackResult642 := WordToStack.Native.compileProgNative
  riscvConfig false Word642.program PrefixChecks.Shard578.arity registers (.nil, 2618)
theorem stackResult642_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word642.program
      PrefixChecks.Shard578.arity registers (prefixList, 2618) =
    (stackResult642.1, stackResult642.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult642.2.2.1, 2620)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word642.program
    PrefixChecks.Shard578.arity registers prefixList 2618
    stackResult642.1 stackResult642.2.1 stackResult642.2.2.1 2620 stackResult642_eq
wave8_kernel_reduce stackResult643 := WordToStack.Native.compileProgNative
  riscvConfig false Word643.program PrefixChecks.Shard579.arity registers (.nil, 2620)
theorem stackResult643_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word643.program
      PrefixChecks.Shard579.arity registers (prefixList, 2620) =
    (stackResult643.1, stackResult643.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult643.2.2.1, 2623)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word643.program
    PrefixChecks.Shard579.arity registers prefixList 2620
    stackResult643.1 stackResult643.2.1 stackResult643.2.2.1 2623 stackResult643_eq
wave8_kernel_reduce stackResult644 := WordToStack.Native.compileProgNative
  riscvConfig false Word644.program PrefixChecks.Shard580.arity registers (.nil, 2623)
theorem stackResult644_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word644.program
      PrefixChecks.Shard580.arity registers (prefixList, 2623) =
    (stackResult644.1, stackResult644.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult644.2.2.1, 2624)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word644.program
    PrefixChecks.Shard580.arity registers prefixList 2623
    stackResult644.1 stackResult644.2.1 stackResult644.2.2.1 2624 stackResult644_eq
wave8_kernel_reduce stackResult645 := WordToStack.Native.compileProgNative
  riscvConfig false Word645.program PrefixChecks.Shard581.arity registers (.nil, 2624)
theorem stackResult645_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word645.program
      PrefixChecks.Shard581.arity registers (prefixList, 2624) =
    (stackResult645.1, stackResult645.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult645.2.2.1, 2630)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word645.program
    PrefixChecks.Shard581.arity registers prefixList 2624
    stackResult645.1 stackResult645.2.1 stackResult645.2.2.1 2630 stackResult645_eq
wave8_kernel_reduce stackResult646 := WordToStack.Native.compileProgNative
  riscvConfig false Word646.program PrefixChecks.Shard582.arity registers (.nil, 2630)
theorem stackResult646_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word646.program
      PrefixChecks.Shard582.arity registers (prefixList, 2630) =
    (stackResult646.1, stackResult646.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult646.2.2.1, 2633)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word646.program
    PrefixChecks.Shard582.arity registers prefixList 2630
    stackResult646.1 stackResult646.2.1 stackResult646.2.2.1 2633 stackResult646_eq
wave8_kernel_reduce stackResult647 := WordToStack.Native.compileProgNative
  riscvConfig false Word647.program PrefixChecks.Shard583.arity registers (.nil, 2633)
theorem stackResult647_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word647.program
      PrefixChecks.Shard583.arity registers (prefixList, 2633) =
    (stackResult647.1, stackResult647.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult647.2.2.1, 2633)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word647.program
    PrefixChecks.Shard583.arity registers prefixList 2633
    stackResult647.1 stackResult647.2.1 stackResult647.2.2.1 2633 stackResult647_eq
wave8_kernel_reduce stackResult648 := WordToStack.Native.compileProgNative
  riscvConfig false Word648.program PrefixChecks.Shard584.arity registers (.nil, 2633)
theorem stackResult648_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word648.program
      PrefixChecks.Shard584.arity registers (prefixList, 2633) =
    (stackResult648.1, stackResult648.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult648.2.2.1, 2633)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word648.program
    PrefixChecks.Shard584.arity registers prefixList 2633
    stackResult648.1 stackResult648.2.1 stackResult648.2.2.1 2633 stackResult648_eq
wave8_kernel_reduce stackResult649 := WordToStack.Native.compileProgNative
  riscvConfig false Word649.program PrefixChecks.Shard585.arity registers (.nil, 2633)
theorem stackResult649_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word649.program
      PrefixChecks.Shard585.arity registers (prefixList, 2633) =
    (stackResult649.1, stackResult649.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult649.2.2.1, 2633)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word649.program
    PrefixChecks.Shard585.arity registers prefixList 2633
    stackResult649.1 stackResult649.2.1 stackResult649.2.2.1 2633 stackResult649_eq
wave8_kernel_reduce stackResult650 := WordToStack.Native.compileProgNative
  riscvConfig false Word650.program PrefixChecks.Shard586.arity registers (.nil, 2633)
theorem stackResult650_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word650.program
      PrefixChecks.Shard586.arity registers (prefixList, 2633) =
    (stackResult650.1, stackResult650.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult650.2.2.1, 2660)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word650.program
    PrefixChecks.Shard586.arity registers prefixList 2633
    stackResult650.1 stackResult650.2.1 stackResult650.2.2.1 2660 stackResult650_eq
wave8_kernel_reduce stackResult651 := WordToStack.Native.compileProgNative
  riscvConfig false Word651.program PrefixChecks.Shard587.arity registers (.nil, 2660)
theorem stackResult651_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word651.program
      PrefixChecks.Shard587.arity registers (prefixList, 2660) =
    (stackResult651.1, stackResult651.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult651.2.2.1, 2685)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word651.program
    PrefixChecks.Shard587.arity registers prefixList 2660
    stackResult651.1 stackResult651.2.1 stackResult651.2.2.1 2685 stackResult651_eq
wave8_kernel_reduce stackResult652 := WordToStack.Native.compileProgNative
  riscvConfig false Word652.program PrefixChecks.Shard588.arity registers (.nil, 2685)
theorem stackResult652_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word652.program
      PrefixChecks.Shard588.arity registers (prefixList, 2685) =
    (stackResult652.1, stackResult652.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult652.2.2.1, 2694)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word652.program
    PrefixChecks.Shard588.arity registers prefixList 2685
    stackResult652.1 stackResult652.2.1 stackResult652.2.2.1 2694 stackResult652_eq
wave8_kernel_reduce stackResult653 := WordToStack.Native.compileProgNative
  riscvConfig false Word653.program PrefixChecks.Shard589.arity registers (.nil, 2694)
theorem stackResult653_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word653.program
      PrefixChecks.Shard589.arity registers (prefixList, 2694) =
    (stackResult653.1, stackResult653.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult653.2.2.1, 2701)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word653.program
    PrefixChecks.Shard589.arity registers prefixList 2694
    stackResult653.1 stackResult653.2.1 stackResult653.2.2.1 2701 stackResult653_eq
wave8_kernel_reduce stackResult654 := WordToStack.Native.compileProgNative
  riscvConfig false Word654.program PrefixChecks.Shard590.arity registers (.nil, 2701)
theorem stackResult654_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word654.program
      PrefixChecks.Shard590.arity registers (prefixList, 2701) =
    (stackResult654.1, stackResult654.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult654.2.2.1, 2708)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word654.program
    PrefixChecks.Shard590.arity registers prefixList 2701
    stackResult654.1 stackResult654.2.1 stackResult654.2.2.1 2708 stackResult654_eq
wave8_kernel_reduce stackResult655 := WordToStack.Native.compileProgNative
  riscvConfig false Word655.program PrefixChecks.Shard591.arity registers (.nil, 2708)
theorem stackResult655_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word655.program
      PrefixChecks.Shard591.arity registers (prefixList, 2708) =
    (stackResult655.1, stackResult655.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult655.2.2.1, 2733)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word655.program
    PrefixChecks.Shard591.arity registers prefixList 2708
    stackResult655.1 stackResult655.2.1 stackResult655.2.2.1 2733 stackResult655_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard576.name, PrefixChecks.Shard576.arity, Word640.program),
  (PrefixChecks.Shard577.name, PrefixChecks.Shard577.arity, Word641.program),
  (PrefixChecks.Shard578.name, PrefixChecks.Shard578.arity, Word642.program),
  (PrefixChecks.Shard579.name, PrefixChecks.Shard579.arity, Word643.program),
  (PrefixChecks.Shard580.name, PrefixChecks.Shard580.arity, Word644.program),
  (PrefixChecks.Shard581.name, PrefixChecks.Shard581.arity, Word645.program),
  (PrefixChecks.Shard582.name, PrefixChecks.Shard582.arity, Word646.program),
  (PrefixChecks.Shard583.name, PrefixChecks.Shard583.arity, Word647.program),
  (PrefixChecks.Shard584.name, PrefixChecks.Shard584.arity, Word648.program),
  (PrefixChecks.Shard585.name, PrefixChecks.Shard585.arity, Word649.program),
  (PrefixChecks.Shard586.name, PrefixChecks.Shard586.arity, Word650.program),
  (PrefixChecks.Shard587.name, PrefixChecks.Shard587.arity, Word651.program),
  (PrefixChecks.Shard588.name, PrefixChecks.Shard588.arity, Word652.program),
  (PrefixChecks.Shard589.name, PrefixChecks.Shard589.arity, Word653.program),
  (PrefixChecks.Shard590.name, PrefixChecks.Shard590.arity, Word654.program),
  (PrefixChecks.Shard591.name, PrefixChecks.Shard591.arity, Word655.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard576.name, stackResult640.1),
  (PrefixChecks.Shard577.name, stackResult641.1),
  (PrefixChecks.Shard578.name, stackResult642.1),
  (PrefixChecks.Shard579.name, stackResult643.1),
  (PrefixChecks.Shard580.name, stackResult644.1),
  (PrefixChecks.Shard581.name, stackResult645.1),
  (PrefixChecks.Shard582.name, stackResult646.1),
  (PrefixChecks.Shard583.name, stackResult647.1),
  (PrefixChecks.Shard584.name, stackResult648.1),
  (PrefixChecks.Shard585.name, stackResult649.1),
  (PrefixChecks.Shard586.name, stackResult650.1),
  (PrefixChecks.Shard587.name, stackResult651.1),
  (PrefixChecks.Shard588.name, stackResult652.1),
  (PrefixChecks.Shard589.name, stackResult653.1),
  (PrefixChecks.Shard590.name, stackResult654.1),
  (PrefixChecks.Shard591.name, stackResult655.1)
]

noncomputable def frames : List Nat := [
  stackResult640.2.1,
  stackResult641.2.1,
  stackResult642.2.1,
  stackResult643.2.1,
  stackResult644.2.1,
  stackResult645.2.1,
  stackResult646.2.1,
  stackResult647.2.1,
  stackResult648.2.1,
  stackResult649.2.1,
  stackResult650.2.1,
  stackResult651.2.1,
  stackResult652.2.1,
  stackResult653.2.1,
  stackResult654.2.1,
  stackResult655.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult640.2.2.1) stackResult641.2.2.1) stackResult642.2.2.1) stackResult643.2.2.1) stackResult644.2.2.1) stackResult645.2.2.1) stackResult646.2.2.1) stackResult647.2.2.1) stackResult648.2.2.1) stackResult649.2.2.1) stackResult650.2.2.1) stackResult651.2.2.1) stackResult652.2.2.1) stackResult653.2.2.1) stackResult654.2.2.1) stackResult655.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 2592) = (bodies, frames, (bitmapDelta, 2733)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult640_from _
  apply compileWordToStack_cons
  · exact stackResult641_from _
  apply compileWordToStack_cons
  · exact stackResult642_from _
  apply compileWordToStack_cons
  · exact stackResult643_from _
  apply compileWordToStack_cons
  · exact stackResult644_from _
  apply compileWordToStack_cons
  · exact stackResult645_from _
  apply compileWordToStack_cons
  · exact stackResult646_from _
  apply compileWordToStack_cons
  · exact stackResult647_from _
  apply compileWordToStack_cons
  · exact stackResult648_from _
  apply compileWordToStack_cons
  · exact stackResult649_from _
  apply compileWordToStack_cons
  · exact stackResult650_from _
  apply compileWordToStack_cons
  · exact stackResult651_from _
  apply compileWordToStack_cons
  · exact stackResult652_from _
  apply compileWordToStack_cons
  · exact stackResult653_from _
  apply compileWordToStack_cons
  · exact stackResult654_from _
  apply compileWordToStack_cons
  · exact stackResult655_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 2592) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 2733)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 2592 bodies frames bitmapDelta 2733 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 576).take 16).zip
      [oracle640, oracle641, oracle642, oracle643, oracle644, oracle645, oracle646, oracle647, oracle648, oracle649, oracle650, oracle651, oracle652, oracle653, oracle654, oracle655]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle640 PrefixChecks.Shard576.entry,
    wordFunction oracle641 PrefixChecks.Shard577.entry,
    wordFunction oracle642 PrefixChecks.Shard578.entry,
    wordFunction oracle643 PrefixChecks.Shard579.entry,
    wordFunction oracle644 PrefixChecks.Shard580.entry,
    wordFunction oracle645 PrefixChecks.Shard581.entry,
    wordFunction oracle646 PrefixChecks.Shard582.entry,
    wordFunction oracle647 PrefixChecks.Shard583.entry,
    wordFunction oracle648 PrefixChecks.Shard584.entry,
    wordFunction oracle649 PrefixChecks.Shard585.entry,
    wordFunction oracle650 PrefixChecks.Shard586.entry,
    wordFunction oracle651 PrefixChecks.Shard587.entry,
    wordFunction oracle652 PrefixChecks.Shard588.entry,
    wordFunction oracle653 PrefixChecks.Shard589.entry,
    wordFunction oracle654 PrefixChecks.Shard590.entry,
    wordFunction oracle655 PrefixChecks.Shard591.entry] = words
  simp only [
    Word640.wordFunction_eq,
    Word641.wordFunction_eq,
    Word642.wordFunction_eq,
    Word643.wordFunction_eq,
    Word644.wordFunction_eq,
    Word645.wordFunction_eq,
    Word646.wordFunction_eq,
    Word647.wordFunction_eq,
    Word648.wordFunction_eq,
    Word649.wordFunction_eq,
    Word650.wordFunction_eq,
    Word651.wordFunction_eq,
    Word652.wordFunction_eq,
    Word653.wordFunction_eq,
    Word654.wordFunction_eq,
    Word655.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk36
