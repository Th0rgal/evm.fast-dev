import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word288
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word289
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word290
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word291
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word292
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word293
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word294
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word295
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word296
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word297
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word298
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word299
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word300
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word301
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word302
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word303
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk14
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult288 := WordToStack.Native.compileProgNative
  riscvConfig false Word288.program PrefixChecks.Shard224.arity registers (.nil, 789)
theorem stackResult288_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word288.program
      PrefixChecks.Shard224.arity registers (prefixList, 789) =
    (stackResult288.1, stackResult288.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult288.2.2.1, 789)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word288.program
    PrefixChecks.Shard224.arity registers prefixList 789
    stackResult288.1 stackResult288.2.1 stackResult288.2.2.1 789 stackResult288_eq
wave8_kernel_reduce stackResult289 := WordToStack.Native.compileProgNative
  riscvConfig false Word289.program PrefixChecks.Shard225.arity registers (.nil, 789)
theorem stackResult289_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word289.program
      PrefixChecks.Shard225.arity registers (prefixList, 789) =
    (stackResult289.1, stackResult289.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult289.2.2.1, 792)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word289.program
    PrefixChecks.Shard225.arity registers prefixList 789
    stackResult289.1 stackResult289.2.1 stackResult289.2.2.1 792 stackResult289_eq
wave8_kernel_reduce stackResult290 := WordToStack.Native.compileProgNative
  riscvConfig false Word290.program PrefixChecks.Shard226.arity registers (.nil, 792)
theorem stackResult290_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word290.program
      PrefixChecks.Shard226.arity registers (prefixList, 792) =
    (stackResult290.1, stackResult290.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult290.2.2.1, 792)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word290.program
    PrefixChecks.Shard226.arity registers prefixList 792
    stackResult290.1 stackResult290.2.1 stackResult290.2.2.1 792 stackResult290_eq
wave8_kernel_reduce stackResult291 := WordToStack.Native.compileProgNative
  riscvConfig false Word291.program PrefixChecks.Shard227.arity registers (.nil, 792)
theorem stackResult291_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word291.program
      PrefixChecks.Shard227.arity registers (prefixList, 792) =
    (stackResult291.1, stackResult291.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult291.2.2.1, 793)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word291.program
    PrefixChecks.Shard227.arity registers prefixList 792
    stackResult291.1 stackResult291.2.1 stackResult291.2.2.1 793 stackResult291_eq
wave8_kernel_reduce stackResult292 := WordToStack.Native.compileProgNative
  riscvConfig false Word292.program PrefixChecks.Shard228.arity registers (.nil, 793)
theorem stackResult292_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word292.program
      PrefixChecks.Shard228.arity registers (prefixList, 793) =
    (stackResult292.1, stackResult292.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult292.2.2.1, 796)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word292.program
    PrefixChecks.Shard228.arity registers prefixList 793
    stackResult292.1 stackResult292.2.1 stackResult292.2.2.1 796 stackResult292_eq
wave8_kernel_reduce stackResult293 := WordToStack.Native.compileProgNative
  riscvConfig false Word293.program PrefixChecks.Shard229.arity registers (.nil, 796)
theorem stackResult293_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word293.program
      PrefixChecks.Shard229.arity registers (prefixList, 796) =
    (stackResult293.1, stackResult293.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult293.2.2.1, 799)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word293.program
    PrefixChecks.Shard229.arity registers prefixList 796
    stackResult293.1 stackResult293.2.1 stackResult293.2.2.1 799 stackResult293_eq
wave8_kernel_reduce stackResult294 := WordToStack.Native.compileProgNative
  riscvConfig false Word294.program PrefixChecks.Shard230.arity registers (.nil, 799)
theorem stackResult294_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word294.program
      PrefixChecks.Shard230.arity registers (prefixList, 799) =
    (stackResult294.1, stackResult294.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult294.2.2.1, 800)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word294.program
    PrefixChecks.Shard230.arity registers prefixList 799
    stackResult294.1 stackResult294.2.1 stackResult294.2.2.1 800 stackResult294_eq
wave8_kernel_reduce stackResult295 := WordToStack.Native.compileProgNative
  riscvConfig false Word295.program PrefixChecks.Shard231.arity registers (.nil, 800)
theorem stackResult295_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word295.program
      PrefixChecks.Shard231.arity registers (prefixList, 800) =
    (stackResult295.1, stackResult295.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult295.2.2.1, 801)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word295.program
    PrefixChecks.Shard231.arity registers prefixList 800
    stackResult295.1 stackResult295.2.1 stackResult295.2.2.1 801 stackResult295_eq
wave8_kernel_reduce stackResult296 := WordToStack.Native.compileProgNative
  riscvConfig false Word296.program PrefixChecks.Shard232.arity registers (.nil, 801)
theorem stackResult296_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word296.program
      PrefixChecks.Shard232.arity registers (prefixList, 801) =
    (stackResult296.1, stackResult296.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult296.2.2.1, 802)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word296.program
    PrefixChecks.Shard232.arity registers prefixList 801
    stackResult296.1 stackResult296.2.1 stackResult296.2.2.1 802 stackResult296_eq
wave8_kernel_reduce stackResult297 := WordToStack.Native.compileProgNative
  riscvConfig false Word297.program PrefixChecks.Shard233.arity registers (.nil, 802)
theorem stackResult297_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word297.program
      PrefixChecks.Shard233.arity registers (prefixList, 802) =
    (stackResult297.1, stackResult297.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult297.2.2.1, 803)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word297.program
    PrefixChecks.Shard233.arity registers prefixList 802
    stackResult297.1 stackResult297.2.1 stackResult297.2.2.1 803 stackResult297_eq
wave8_kernel_reduce stackResult298 := WordToStack.Native.compileProgNative
  riscvConfig false Word298.program PrefixChecks.Shard234.arity registers (.nil, 803)
theorem stackResult298_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word298.program
      PrefixChecks.Shard234.arity registers (prefixList, 803) =
    (stackResult298.1, stackResult298.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult298.2.2.1, 805)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word298.program
    PrefixChecks.Shard234.arity registers prefixList 803
    stackResult298.1 stackResult298.2.1 stackResult298.2.2.1 805 stackResult298_eq
wave8_kernel_reduce stackResult299 := WordToStack.Native.compileProgNative
  riscvConfig false Word299.program PrefixChecks.Shard235.arity registers (.nil, 805)
theorem stackResult299_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word299.program
      PrefixChecks.Shard235.arity registers (prefixList, 805) =
    (stackResult299.1, stackResult299.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult299.2.2.1, 805)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word299.program
    PrefixChecks.Shard235.arity registers prefixList 805
    stackResult299.1 stackResult299.2.1 stackResult299.2.2.1 805 stackResult299_eq
wave8_kernel_reduce stackResult300 := WordToStack.Native.compileProgNative
  riscvConfig false Word300.program PrefixChecks.Shard236.arity registers (.nil, 805)
theorem stackResult300_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word300.program
      PrefixChecks.Shard236.arity registers (prefixList, 805) =
    (stackResult300.1, stackResult300.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult300.2.2.1, 810)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word300.program
    PrefixChecks.Shard236.arity registers prefixList 805
    stackResult300.1 stackResult300.2.1 stackResult300.2.2.1 810 stackResult300_eq
wave8_kernel_reduce stackResult301 := WordToStack.Native.compileProgNative
  riscvConfig false Word301.program PrefixChecks.Shard237.arity registers (.nil, 810)
theorem stackResult301_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word301.program
      PrefixChecks.Shard237.arity registers (prefixList, 810) =
    (stackResult301.1, stackResult301.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult301.2.2.1, 825)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word301.program
    PrefixChecks.Shard237.arity registers prefixList 810
    stackResult301.1 stackResult301.2.1 stackResult301.2.2.1 825 stackResult301_eq
wave8_kernel_reduce stackResult302 := WordToStack.Native.compileProgNative
  riscvConfig false Word302.program PrefixChecks.Shard238.arity registers (.nil, 825)
theorem stackResult302_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word302.program
      PrefixChecks.Shard238.arity registers (prefixList, 825) =
    (stackResult302.1, stackResult302.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult302.2.2.1, 832)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word302.program
    PrefixChecks.Shard238.arity registers prefixList 825
    stackResult302.1 stackResult302.2.1 stackResult302.2.2.1 832 stackResult302_eq
wave8_kernel_reduce stackResult303 := WordToStack.Native.compileProgNative
  riscvConfig false Word303.program PrefixChecks.Shard239.arity registers (.nil, 832)
theorem stackResult303_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word303.program
      PrefixChecks.Shard239.arity registers (prefixList, 832) =
    (stackResult303.1, stackResult303.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult303.2.2.1, 834)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word303.program
    PrefixChecks.Shard239.arity registers prefixList 832
    stackResult303.1 stackResult303.2.1 stackResult303.2.2.1 834 stackResult303_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard224.name, PrefixChecks.Shard224.arity, Word288.program),
  (PrefixChecks.Shard225.name, PrefixChecks.Shard225.arity, Word289.program),
  (PrefixChecks.Shard226.name, PrefixChecks.Shard226.arity, Word290.program),
  (PrefixChecks.Shard227.name, PrefixChecks.Shard227.arity, Word291.program),
  (PrefixChecks.Shard228.name, PrefixChecks.Shard228.arity, Word292.program),
  (PrefixChecks.Shard229.name, PrefixChecks.Shard229.arity, Word293.program),
  (PrefixChecks.Shard230.name, PrefixChecks.Shard230.arity, Word294.program),
  (PrefixChecks.Shard231.name, PrefixChecks.Shard231.arity, Word295.program),
  (PrefixChecks.Shard232.name, PrefixChecks.Shard232.arity, Word296.program),
  (PrefixChecks.Shard233.name, PrefixChecks.Shard233.arity, Word297.program),
  (PrefixChecks.Shard234.name, PrefixChecks.Shard234.arity, Word298.program),
  (PrefixChecks.Shard235.name, PrefixChecks.Shard235.arity, Word299.program),
  (PrefixChecks.Shard236.name, PrefixChecks.Shard236.arity, Word300.program),
  (PrefixChecks.Shard237.name, PrefixChecks.Shard237.arity, Word301.program),
  (PrefixChecks.Shard238.name, PrefixChecks.Shard238.arity, Word302.program),
  (PrefixChecks.Shard239.name, PrefixChecks.Shard239.arity, Word303.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard224.name, stackResult288.1),
  (PrefixChecks.Shard225.name, stackResult289.1),
  (PrefixChecks.Shard226.name, stackResult290.1),
  (PrefixChecks.Shard227.name, stackResult291.1),
  (PrefixChecks.Shard228.name, stackResult292.1),
  (PrefixChecks.Shard229.name, stackResult293.1),
  (PrefixChecks.Shard230.name, stackResult294.1),
  (PrefixChecks.Shard231.name, stackResult295.1),
  (PrefixChecks.Shard232.name, stackResult296.1),
  (PrefixChecks.Shard233.name, stackResult297.1),
  (PrefixChecks.Shard234.name, stackResult298.1),
  (PrefixChecks.Shard235.name, stackResult299.1),
  (PrefixChecks.Shard236.name, stackResult300.1),
  (PrefixChecks.Shard237.name, stackResult301.1),
  (PrefixChecks.Shard238.name, stackResult302.1),
  (PrefixChecks.Shard239.name, stackResult303.1)
]

noncomputable def frames : List Nat := [
  stackResult288.2.1,
  stackResult289.2.1,
  stackResult290.2.1,
  stackResult291.2.1,
  stackResult292.2.1,
  stackResult293.2.1,
  stackResult294.2.1,
  stackResult295.2.1,
  stackResult296.2.1,
  stackResult297.2.1,
  stackResult298.2.1,
  stackResult299.2.1,
  stackResult300.2.1,
  stackResult301.2.1,
  stackResult302.2.1,
  stackResult303.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult288.2.2.1) stackResult289.2.2.1) stackResult290.2.2.1) stackResult291.2.2.1) stackResult292.2.2.1) stackResult293.2.2.1) stackResult294.2.2.1) stackResult295.2.2.1) stackResult296.2.2.1) stackResult297.2.2.1) stackResult298.2.2.1) stackResult299.2.2.1) stackResult300.2.2.1) stackResult301.2.2.1) stackResult302.2.2.1) stackResult303.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 789) = (bodies, frames, (bitmapDelta, 834)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult288_from _
  apply compileWordToStack_cons
  · exact stackResult289_from _
  apply compileWordToStack_cons
  · exact stackResult290_from _
  apply compileWordToStack_cons
  · exact stackResult291_from _
  apply compileWordToStack_cons
  · exact stackResult292_from _
  apply compileWordToStack_cons
  · exact stackResult293_from _
  apply compileWordToStack_cons
  · exact stackResult294_from _
  apply compileWordToStack_cons
  · exact stackResult295_from _
  apply compileWordToStack_cons
  · exact stackResult296_from _
  apply compileWordToStack_cons
  · exact stackResult297_from _
  apply compileWordToStack_cons
  · exact stackResult298_from _
  apply compileWordToStack_cons
  · exact stackResult299_from _
  apply compileWordToStack_cons
  · exact stackResult300_from _
  apply compileWordToStack_cons
  · exact stackResult301_from _
  apply compileWordToStack_cons
  · exact stackResult302_from _
  apply compileWordToStack_cons
  · exact stackResult303_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 789) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 834)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 789 bodies frames bitmapDelta 834 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 224).take 16).zip
      [oracle288, oracle289, oracle290, oracle291, oracle292, oracle293, oracle294, oracle295, oracle296, oracle297, oracle298, oracle299, oracle300, oracle301, oracle302, oracle303]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle288 PrefixChecks.Shard224.entry,
    wordFunction oracle289 PrefixChecks.Shard225.entry,
    wordFunction oracle290 PrefixChecks.Shard226.entry,
    wordFunction oracle291 PrefixChecks.Shard227.entry,
    wordFunction oracle292 PrefixChecks.Shard228.entry,
    wordFunction oracle293 PrefixChecks.Shard229.entry,
    wordFunction oracle294 PrefixChecks.Shard230.entry,
    wordFunction oracle295 PrefixChecks.Shard231.entry,
    wordFunction oracle296 PrefixChecks.Shard232.entry,
    wordFunction oracle297 PrefixChecks.Shard233.entry,
    wordFunction oracle298 PrefixChecks.Shard234.entry,
    wordFunction oracle299 PrefixChecks.Shard235.entry,
    wordFunction oracle300 PrefixChecks.Shard236.entry,
    wordFunction oracle301 PrefixChecks.Shard237.entry,
    wordFunction oracle302 PrefixChecks.Shard238.entry,
    wordFunction oracle303 PrefixChecks.Shard239.entry] = words
  simp only [
    Word288.wordFunction_eq,
    Word289.wordFunction_eq,
    Word290.wordFunction_eq,
    Word291.wordFunction_eq,
    Word292.wordFunction_eq,
    Word293.wordFunction_eq,
    Word294.wordFunction_eq,
    Word295.wordFunction_eq,
    Word296.wordFunction_eq,
    Word297.wordFunction_eq,
    Word298.wordFunction_eq,
    Word299.wordFunction_eq,
    Word300.wordFunction_eq,
    Word301.wordFunction_eq,
    Word302.wordFunction_eq,
    Word303.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk14
