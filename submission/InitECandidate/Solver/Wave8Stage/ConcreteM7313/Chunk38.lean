import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word672
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word673
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word674
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word675
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word676
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word677
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word678
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word679
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word680
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word681
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word682
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word683
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word684
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word685
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word686
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word687
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk38
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult672 := WordToStack.Native.compileProgNative
  riscvConfig false Word672.program PrefixChecks.Shard608.arity registers (.nil, 2787)
theorem stackResult672_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word672.program
      PrefixChecks.Shard608.arity registers (prefixList, 2787) =
    (stackResult672.1, stackResult672.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult672.2.2.1, 2788)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word672.program
    PrefixChecks.Shard608.arity registers prefixList 2787
    stackResult672.1 stackResult672.2.1 stackResult672.2.2.1 2788 stackResult672_eq
wave8_kernel_reduce stackResult673 := WordToStack.Native.compileProgNative
  riscvConfig false Word673.program PrefixChecks.Shard609.arity registers (.nil, 2788)
theorem stackResult673_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word673.program
      PrefixChecks.Shard609.arity registers (prefixList, 2788) =
    (stackResult673.1, stackResult673.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult673.2.2.1, 2789)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word673.program
    PrefixChecks.Shard609.arity registers prefixList 2788
    stackResult673.1 stackResult673.2.1 stackResult673.2.2.1 2789 stackResult673_eq
wave8_kernel_reduce stackResult674 := WordToStack.Native.compileProgNative
  riscvConfig false Word674.program PrefixChecks.Shard610.arity registers (.nil, 2789)
theorem stackResult674_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word674.program
      PrefixChecks.Shard610.arity registers (prefixList, 2789) =
    (stackResult674.1, stackResult674.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult674.2.2.1, 2790)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word674.program
    PrefixChecks.Shard610.arity registers prefixList 2789
    stackResult674.1 stackResult674.2.1 stackResult674.2.2.1 2790 stackResult674_eq
wave8_kernel_reduce stackResult675 := WordToStack.Native.compileProgNative
  riscvConfig false Word675.program PrefixChecks.Shard611.arity registers (.nil, 2790)
theorem stackResult675_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word675.program
      PrefixChecks.Shard611.arity registers (prefixList, 2790) =
    (stackResult675.1, stackResult675.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult675.2.2.1, 2791)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word675.program
    PrefixChecks.Shard611.arity registers prefixList 2790
    stackResult675.1 stackResult675.2.1 stackResult675.2.2.1 2791 stackResult675_eq
wave8_kernel_reduce stackResult676 := WordToStack.Native.compileProgNative
  riscvConfig false Word676.program PrefixChecks.Shard612.arity registers (.nil, 2791)
theorem stackResult676_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word676.program
      PrefixChecks.Shard612.arity registers (prefixList, 2791) =
    (stackResult676.1, stackResult676.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult676.2.2.1, 2791)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word676.program
    PrefixChecks.Shard612.arity registers prefixList 2791
    stackResult676.1 stackResult676.2.1 stackResult676.2.2.1 2791 stackResult676_eq
wave8_kernel_reduce stackResult677 := WordToStack.Native.compileProgNative
  riscvConfig false Word677.program PrefixChecks.Shard613.arity registers (.nil, 2791)
theorem stackResult677_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word677.program
      PrefixChecks.Shard613.arity registers (prefixList, 2791) =
    (stackResult677.1, stackResult677.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult677.2.2.1, 2791)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word677.program
    PrefixChecks.Shard613.arity registers prefixList 2791
    stackResult677.1 stackResult677.2.1 stackResult677.2.2.1 2791 stackResult677_eq
wave8_kernel_reduce stackResult678 := WordToStack.Native.compileProgNative
  riscvConfig false Word678.program PrefixChecks.Shard614.arity registers (.nil, 2791)
theorem stackResult678_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word678.program
      PrefixChecks.Shard614.arity registers (prefixList, 2791) =
    (stackResult678.1, stackResult678.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult678.2.2.1, 2792)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word678.program
    PrefixChecks.Shard614.arity registers prefixList 2791
    stackResult678.1 stackResult678.2.1 stackResult678.2.2.1 2792 stackResult678_eq
wave8_kernel_reduce stackResult679 := WordToStack.Native.compileProgNative
  riscvConfig false Word679.program PrefixChecks.Shard615.arity registers (.nil, 2792)
theorem stackResult679_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word679.program
      PrefixChecks.Shard615.arity registers (prefixList, 2792) =
    (stackResult679.1, stackResult679.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult679.2.2.1, 2793)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word679.program
    PrefixChecks.Shard615.arity registers prefixList 2792
    stackResult679.1 stackResult679.2.1 stackResult679.2.2.1 2793 stackResult679_eq
wave8_kernel_reduce stackResult680 := WordToStack.Native.compileProgNative
  riscvConfig false Word680.program PrefixChecks.Shard616.arity registers (.nil, 2793)
theorem stackResult680_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word680.program
      PrefixChecks.Shard616.arity registers (prefixList, 2793) =
    (stackResult680.1, stackResult680.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult680.2.2.1, 2796)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word680.program
    PrefixChecks.Shard616.arity registers prefixList 2793
    stackResult680.1 stackResult680.2.1 stackResult680.2.2.1 2796 stackResult680_eq
wave8_kernel_reduce stackResult681 := WordToStack.Native.compileProgNative
  riscvConfig false Word681.program PrefixChecks.Shard617.arity registers (.nil, 2796)
theorem stackResult681_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word681.program
      PrefixChecks.Shard617.arity registers (prefixList, 2796) =
    (stackResult681.1, stackResult681.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult681.2.2.1, 2796)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word681.program
    PrefixChecks.Shard617.arity registers prefixList 2796
    stackResult681.1 stackResult681.2.1 stackResult681.2.2.1 2796 stackResult681_eq
wave8_kernel_reduce stackResult682 := WordToStack.Native.compileProgNative
  riscvConfig false Word682.program PrefixChecks.Shard618.arity registers (.nil, 2796)
theorem stackResult682_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word682.program
      PrefixChecks.Shard618.arity registers (prefixList, 2796) =
    (stackResult682.1, stackResult682.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult682.2.2.1, 2828)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word682.program
    PrefixChecks.Shard618.arity registers prefixList 2796
    stackResult682.1 stackResult682.2.1 stackResult682.2.2.1 2828 stackResult682_eq
wave8_kernel_reduce stackResult683 := WordToStack.Native.compileProgNative
  riscvConfig false Word683.program PrefixChecks.Shard619.arity registers (.nil, 2828)
theorem stackResult683_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word683.program
      PrefixChecks.Shard619.arity registers (prefixList, 2828) =
    (stackResult683.1, stackResult683.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult683.2.2.1, 2875)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word683.program
    PrefixChecks.Shard619.arity registers prefixList 2828
    stackResult683.1 stackResult683.2.1 stackResult683.2.2.1 2875 stackResult683_eq
wave8_kernel_reduce stackResult684 := WordToStack.Native.compileProgNative
  riscvConfig false Word684.program PrefixChecks.Shard620.arity registers (.nil, 2875)
theorem stackResult684_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word684.program
      PrefixChecks.Shard620.arity registers (prefixList, 2875) =
    (stackResult684.1, stackResult684.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult684.2.2.1, 2886)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word684.program
    PrefixChecks.Shard620.arity registers prefixList 2875
    stackResult684.1 stackResult684.2.1 stackResult684.2.2.1 2886 stackResult684_eq
wave8_kernel_reduce stackResult685 := WordToStack.Native.compileProgNative
  riscvConfig false Word685.program PrefixChecks.Shard621.arity registers (.nil, 2886)
theorem stackResult685_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word685.program
      PrefixChecks.Shard621.arity registers (prefixList, 2886) =
    (stackResult685.1, stackResult685.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult685.2.2.1, 2922)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word685.program
    PrefixChecks.Shard621.arity registers prefixList 2886
    stackResult685.1 stackResult685.2.1 stackResult685.2.2.1 2922 stackResult685_eq
wave8_kernel_reduce stackResult686 := WordToStack.Native.compileProgNative
  riscvConfig false Word686.program PrefixChecks.Shard622.arity registers (.nil, 2922)
theorem stackResult686_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word686.program
      PrefixChecks.Shard622.arity registers (prefixList, 2922) =
    (stackResult686.1, stackResult686.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult686.2.2.1, 2925)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word686.program
    PrefixChecks.Shard622.arity registers prefixList 2922
    stackResult686.1 stackResult686.2.1 stackResult686.2.2.1 2925 stackResult686_eq
wave8_kernel_reduce stackResult687 := WordToStack.Native.compileProgNative
  riscvConfig false Word687.program PrefixChecks.Shard623.arity registers (.nil, 2925)
theorem stackResult687_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word687.program
      PrefixChecks.Shard623.arity registers (prefixList, 2925) =
    (stackResult687.1, stackResult687.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult687.2.2.1, 2926)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word687.program
    PrefixChecks.Shard623.arity registers prefixList 2925
    stackResult687.1 stackResult687.2.1 stackResult687.2.2.1 2926 stackResult687_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard608.name, PrefixChecks.Shard608.arity, Word672.program),
  (PrefixChecks.Shard609.name, PrefixChecks.Shard609.arity, Word673.program),
  (PrefixChecks.Shard610.name, PrefixChecks.Shard610.arity, Word674.program),
  (PrefixChecks.Shard611.name, PrefixChecks.Shard611.arity, Word675.program),
  (PrefixChecks.Shard612.name, PrefixChecks.Shard612.arity, Word676.program),
  (PrefixChecks.Shard613.name, PrefixChecks.Shard613.arity, Word677.program),
  (PrefixChecks.Shard614.name, PrefixChecks.Shard614.arity, Word678.program),
  (PrefixChecks.Shard615.name, PrefixChecks.Shard615.arity, Word679.program),
  (PrefixChecks.Shard616.name, PrefixChecks.Shard616.arity, Word680.program),
  (PrefixChecks.Shard617.name, PrefixChecks.Shard617.arity, Word681.program),
  (PrefixChecks.Shard618.name, PrefixChecks.Shard618.arity, Word682.program),
  (PrefixChecks.Shard619.name, PrefixChecks.Shard619.arity, Word683.program),
  (PrefixChecks.Shard620.name, PrefixChecks.Shard620.arity, Word684.program),
  (PrefixChecks.Shard621.name, PrefixChecks.Shard621.arity, Word685.program),
  (PrefixChecks.Shard622.name, PrefixChecks.Shard622.arity, Word686.program),
  (PrefixChecks.Shard623.name, PrefixChecks.Shard623.arity, Word687.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard608.name, stackResult672.1),
  (PrefixChecks.Shard609.name, stackResult673.1),
  (PrefixChecks.Shard610.name, stackResult674.1),
  (PrefixChecks.Shard611.name, stackResult675.1),
  (PrefixChecks.Shard612.name, stackResult676.1),
  (PrefixChecks.Shard613.name, stackResult677.1),
  (PrefixChecks.Shard614.name, stackResult678.1),
  (PrefixChecks.Shard615.name, stackResult679.1),
  (PrefixChecks.Shard616.name, stackResult680.1),
  (PrefixChecks.Shard617.name, stackResult681.1),
  (PrefixChecks.Shard618.name, stackResult682.1),
  (PrefixChecks.Shard619.name, stackResult683.1),
  (PrefixChecks.Shard620.name, stackResult684.1),
  (PrefixChecks.Shard621.name, stackResult685.1),
  (PrefixChecks.Shard622.name, stackResult686.1),
  (PrefixChecks.Shard623.name, stackResult687.1)
]

noncomputable def frames : List Nat := [
  stackResult672.2.1,
  stackResult673.2.1,
  stackResult674.2.1,
  stackResult675.2.1,
  stackResult676.2.1,
  stackResult677.2.1,
  stackResult678.2.1,
  stackResult679.2.1,
  stackResult680.2.1,
  stackResult681.2.1,
  stackResult682.2.1,
  stackResult683.2.1,
  stackResult684.2.1,
  stackResult685.2.1,
  stackResult686.2.1,
  stackResult687.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult672.2.2.1) stackResult673.2.2.1) stackResult674.2.2.1) stackResult675.2.2.1) stackResult676.2.2.1) stackResult677.2.2.1) stackResult678.2.2.1) stackResult679.2.2.1) stackResult680.2.2.1) stackResult681.2.2.1) stackResult682.2.2.1) stackResult683.2.2.1) stackResult684.2.2.1) stackResult685.2.2.1) stackResult686.2.2.1) stackResult687.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 2787) = (bodies, frames, (bitmapDelta, 2926)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult672_from _
  apply compileWordToStack_cons
  · exact stackResult673_from _
  apply compileWordToStack_cons
  · exact stackResult674_from _
  apply compileWordToStack_cons
  · exact stackResult675_from _
  apply compileWordToStack_cons
  · exact stackResult676_from _
  apply compileWordToStack_cons
  · exact stackResult677_from _
  apply compileWordToStack_cons
  · exact stackResult678_from _
  apply compileWordToStack_cons
  · exact stackResult679_from _
  apply compileWordToStack_cons
  · exact stackResult680_from _
  apply compileWordToStack_cons
  · exact stackResult681_from _
  apply compileWordToStack_cons
  · exact stackResult682_from _
  apply compileWordToStack_cons
  · exact stackResult683_from _
  apply compileWordToStack_cons
  · exact stackResult684_from _
  apply compileWordToStack_cons
  · exact stackResult685_from _
  apply compileWordToStack_cons
  · exact stackResult686_from _
  apply compileWordToStack_cons
  · exact stackResult687_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 2787) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 2926)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 2787 bodies frames bitmapDelta 2926 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 608).take 16).zip
      [oracle672, oracle673, oracle674, oracle675, oracle676, oracle677, oracle678, oracle679, oracle680, oracle681, oracle682, oracle683, oracle684, oracle685, oracle686, oracle687]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle672 PrefixChecks.Shard608.entry,
    wordFunction oracle673 PrefixChecks.Shard609.entry,
    wordFunction oracle674 PrefixChecks.Shard610.entry,
    wordFunction oracle675 PrefixChecks.Shard611.entry,
    wordFunction oracle676 PrefixChecks.Shard612.entry,
    wordFunction oracle677 PrefixChecks.Shard613.entry,
    wordFunction oracle678 PrefixChecks.Shard614.entry,
    wordFunction oracle679 PrefixChecks.Shard615.entry,
    wordFunction oracle680 PrefixChecks.Shard616.entry,
    wordFunction oracle681 PrefixChecks.Shard617.entry,
    wordFunction oracle682 PrefixChecks.Shard618.entry,
    wordFunction oracle683 PrefixChecks.Shard619.entry,
    wordFunction oracle684 PrefixChecks.Shard620.entry,
    wordFunction oracle685 PrefixChecks.Shard621.entry,
    wordFunction oracle686 PrefixChecks.Shard622.entry,
    wordFunction oracle687 PrefixChecks.Shard623.entry] = words
  simp only [
    Word672.wordFunction_eq,
    Word673.wordFunction_eq,
    Word674.wordFunction_eq,
    Word675.wordFunction_eq,
    Word676.wordFunction_eq,
    Word677.wordFunction_eq,
    Word678.wordFunction_eq,
    Word679.wordFunction_eq,
    Word680.wordFunction_eq,
    Word681.wordFunction_eq,
    Word682.wordFunction_eq,
    Word683.wordFunction_eq,
    Word684.wordFunction_eq,
    Word685.wordFunction_eq,
    Word686.wordFunction_eq,
    Word687.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk38
