import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word544
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word545
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word546
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word547
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word548
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word549
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word550
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word551
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word552
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word553
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word554
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word555
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word556
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word557
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word558
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word559
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000
set_option cbv.maxSteps 40000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk30
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

wave8_certified_reduce stackResult544 := WordToStack.Native.compileProgNative
  riscvConfig false Word544.program PrefixChecks.Shard480.arity registers (.nil, 1799)
theorem stackResult544_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word544.program
      PrefixChecks.Shard480.arity registers (prefixList, 1799) =
    (stackResult544.1, stackResult544.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult544.2.2.1, 1804)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word544.program
    PrefixChecks.Shard480.arity registers prefixList 1799
    stackResult544.1 stackResult544.2.1 stackResult544.2.2.1 1804 stackResult544_eq
wave8_certified_reduce stackResult545 := WordToStack.Native.compileProgNative
  riscvConfig false Word545.program PrefixChecks.Shard481.arity registers (.nil, 1804)
theorem stackResult545_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word545.program
      PrefixChecks.Shard481.arity registers (prefixList, 1804) =
    (stackResult545.1, stackResult545.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult545.2.2.1, 1805)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word545.program
    PrefixChecks.Shard481.arity registers prefixList 1804
    stackResult545.1 stackResult545.2.1 stackResult545.2.2.1 1805 stackResult545_eq
wave8_certified_reduce stackResult546 := WordToStack.Native.compileProgNative
  riscvConfig false Word546.program PrefixChecks.Shard482.arity registers (.nil, 1805)
theorem stackResult546_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word546.program
      PrefixChecks.Shard482.arity registers (prefixList, 1805) =
    (stackResult546.1, stackResult546.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult546.2.2.1, 1826)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word546.program
    PrefixChecks.Shard482.arity registers prefixList 1805
    stackResult546.1 stackResult546.2.1 stackResult546.2.2.1 1826 stackResult546_eq
wave8_certified_reduce stackResult547 := WordToStack.Native.compileProgNative
  riscvConfig false Word547.program PrefixChecks.Shard483.arity registers (.nil, 1826)
theorem stackResult547_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word547.program
      PrefixChecks.Shard483.arity registers (prefixList, 1826) =
    (stackResult547.1, stackResult547.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult547.2.2.1, 1828)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word547.program
    PrefixChecks.Shard483.arity registers prefixList 1826
    stackResult547.1 stackResult547.2.1 stackResult547.2.2.1 1828 stackResult547_eq
wave8_certified_reduce stackResult548 := WordToStack.Native.compileProgNative
  riscvConfig false Word548.program PrefixChecks.Shard484.arity registers (.nil, 1828)
theorem stackResult548_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word548.program
      PrefixChecks.Shard484.arity registers (prefixList, 1828) =
    (stackResult548.1, stackResult548.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult548.2.2.1, 1830)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word548.program
    PrefixChecks.Shard484.arity registers prefixList 1828
    stackResult548.1 stackResult548.2.1 stackResult548.2.2.1 1830 stackResult548_eq
wave8_certified_reduce stackResult549 := WordToStack.Native.compileProgNative
  riscvConfig false Word549.program PrefixChecks.Shard485.arity registers (.nil, 1830)
theorem stackResult549_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word549.program
      PrefixChecks.Shard485.arity registers (prefixList, 1830) =
    (stackResult549.1, stackResult549.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult549.2.2.1, 1839)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word549.program
    PrefixChecks.Shard485.arity registers prefixList 1830
    stackResult549.1 stackResult549.2.1 stackResult549.2.2.1 1839 stackResult549_eq
wave8_certified_reduce stackResult550 := WordToStack.Native.compileProgNative
  riscvConfig false Word550.program PrefixChecks.Shard486.arity registers (.nil, 1839)
theorem stackResult550_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word550.program
      PrefixChecks.Shard486.arity registers (prefixList, 1839) =
    (stackResult550.1, stackResult550.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult550.2.2.1, 1861)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word550.program
    PrefixChecks.Shard486.arity registers prefixList 1839
    stackResult550.1 stackResult550.2.1 stackResult550.2.2.1 1861 stackResult550_eq
wave8_certified_reduce stackResult551 := WordToStack.Native.compileProgNative
  riscvConfig false Word551.program PrefixChecks.Shard487.arity registers (.nil, 1861)
theorem stackResult551_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word551.program
      PrefixChecks.Shard487.arity registers (prefixList, 1861) =
    (stackResult551.1, stackResult551.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult551.2.2.1, 1867)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word551.program
    PrefixChecks.Shard487.arity registers prefixList 1861
    stackResult551.1 stackResult551.2.1 stackResult551.2.2.1 1867 stackResult551_eq
wave8_certified_reduce stackResult552 := WordToStack.Native.compileProgNative
  riscvConfig false Word552.program PrefixChecks.Shard488.arity registers (.nil, 1867)
theorem stackResult552_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word552.program
      PrefixChecks.Shard488.arity registers (prefixList, 1867) =
    (stackResult552.1, stackResult552.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult552.2.2.1, 1874)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word552.program
    PrefixChecks.Shard488.arity registers prefixList 1867
    stackResult552.1 stackResult552.2.1 stackResult552.2.2.1 1874 stackResult552_eq
wave8_certified_reduce stackResult553 := WordToStack.Native.compileProgNative
  riscvConfig false Word553.program PrefixChecks.Shard489.arity registers (.nil, 1874)
theorem stackResult553_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word553.program
      PrefixChecks.Shard489.arity registers (prefixList, 1874) =
    (stackResult553.1, stackResult553.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult553.2.2.1, 1878)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word553.program
    PrefixChecks.Shard489.arity registers prefixList 1874
    stackResult553.1 stackResult553.2.1 stackResult553.2.2.1 1878 stackResult553_eq
wave8_certified_reduce stackResult554 := WordToStack.Native.compileProgNative
  riscvConfig false Word554.program PrefixChecks.Shard490.arity registers (.nil, 1878)
theorem stackResult554_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word554.program
      PrefixChecks.Shard490.arity registers (prefixList, 1878) =
    (stackResult554.1, stackResult554.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult554.2.2.1, 1886)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word554.program
    PrefixChecks.Shard490.arity registers prefixList 1878
    stackResult554.1 stackResult554.2.1 stackResult554.2.2.1 1886 stackResult554_eq
wave8_certified_reduce stackResult555 := WordToStack.Native.compileProgNative
  riscvConfig false Word555.program PrefixChecks.Shard491.arity registers (.nil, 1886)
theorem stackResult555_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word555.program
      PrefixChecks.Shard491.arity registers (prefixList, 1886) =
    (stackResult555.1, stackResult555.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult555.2.2.1, 1890)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word555.program
    PrefixChecks.Shard491.arity registers prefixList 1886
    stackResult555.1 stackResult555.2.1 stackResult555.2.2.1 1890 stackResult555_eq
wave8_certified_reduce stackResult556 := WordToStack.Native.compileProgNative
  riscvConfig false Word556.program PrefixChecks.Shard492.arity registers (.nil, 1890)
theorem stackResult556_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word556.program
      PrefixChecks.Shard492.arity registers (prefixList, 1890) =
    (stackResult556.1, stackResult556.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult556.2.2.1, 1894)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word556.program
    PrefixChecks.Shard492.arity registers prefixList 1890
    stackResult556.1 stackResult556.2.1 stackResult556.2.2.1 1894 stackResult556_eq
wave8_certified_reduce stackResult557 := WordToStack.Native.compileProgNative
  riscvConfig false Word557.program PrefixChecks.Shard493.arity registers (.nil, 1894)
theorem stackResult557_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word557.program
      PrefixChecks.Shard493.arity registers (prefixList, 1894) =
    (stackResult557.1, stackResult557.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult557.2.2.1, 1897)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word557.program
    PrefixChecks.Shard493.arity registers prefixList 1894
    stackResult557.1 stackResult557.2.1 stackResult557.2.2.1 1897 stackResult557_eq
wave8_certified_reduce stackResult558 := WordToStack.Native.compileProgNative
  riscvConfig false Word558.program PrefixChecks.Shard494.arity registers (.nil, 1897)
theorem stackResult558_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word558.program
      PrefixChecks.Shard494.arity registers (prefixList, 1897) =
    (stackResult558.1, stackResult558.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult558.2.2.1, 1907)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word558.program
    PrefixChecks.Shard494.arity registers prefixList 1897
    stackResult558.1 stackResult558.2.1 stackResult558.2.2.1 1907 stackResult558_eq
wave8_certified_reduce stackResult559 := WordToStack.Native.compileProgNative
  riscvConfig false Word559.program PrefixChecks.Shard495.arity registers (.nil, 1907)
theorem stackResult559_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word559.program
      PrefixChecks.Shard495.arity registers (prefixList, 1907) =
    (stackResult559.1, stackResult559.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult559.2.2.1, 1910)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word559.program
    PrefixChecks.Shard495.arity registers prefixList 1907
    stackResult559.1 stackResult559.2.1 stackResult559.2.2.1 1910 stackResult559_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard480.name, PrefixChecks.Shard480.arity, Word544.program),
  (PrefixChecks.Shard481.name, PrefixChecks.Shard481.arity, Word545.program),
  (PrefixChecks.Shard482.name, PrefixChecks.Shard482.arity, Word546.program),
  (PrefixChecks.Shard483.name, PrefixChecks.Shard483.arity, Word547.program),
  (PrefixChecks.Shard484.name, PrefixChecks.Shard484.arity, Word548.program),
  (PrefixChecks.Shard485.name, PrefixChecks.Shard485.arity, Word549.program),
  (PrefixChecks.Shard486.name, PrefixChecks.Shard486.arity, Word550.program),
  (PrefixChecks.Shard487.name, PrefixChecks.Shard487.arity, Word551.program),
  (PrefixChecks.Shard488.name, PrefixChecks.Shard488.arity, Word552.program),
  (PrefixChecks.Shard489.name, PrefixChecks.Shard489.arity, Word553.program),
  (PrefixChecks.Shard490.name, PrefixChecks.Shard490.arity, Word554.program),
  (PrefixChecks.Shard491.name, PrefixChecks.Shard491.arity, Word555.program),
  (PrefixChecks.Shard492.name, PrefixChecks.Shard492.arity, Word556.program),
  (PrefixChecks.Shard493.name, PrefixChecks.Shard493.arity, Word557.program),
  (PrefixChecks.Shard494.name, PrefixChecks.Shard494.arity, Word558.program),
  (PrefixChecks.Shard495.name, PrefixChecks.Shard495.arity, Word559.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard480.name, stackResult544.1),
  (PrefixChecks.Shard481.name, stackResult545.1),
  (PrefixChecks.Shard482.name, stackResult546.1),
  (PrefixChecks.Shard483.name, stackResult547.1),
  (PrefixChecks.Shard484.name, stackResult548.1),
  (PrefixChecks.Shard485.name, stackResult549.1),
  (PrefixChecks.Shard486.name, stackResult550.1),
  (PrefixChecks.Shard487.name, stackResult551.1),
  (PrefixChecks.Shard488.name, stackResult552.1),
  (PrefixChecks.Shard489.name, stackResult553.1),
  (PrefixChecks.Shard490.name, stackResult554.1),
  (PrefixChecks.Shard491.name, stackResult555.1),
  (PrefixChecks.Shard492.name, stackResult556.1),
  (PrefixChecks.Shard493.name, stackResult557.1),
  (PrefixChecks.Shard494.name, stackResult558.1),
  (PrefixChecks.Shard495.name, stackResult559.1)
]

noncomputable def frames : List Nat := [
  stackResult544.2.1,
  stackResult545.2.1,
  stackResult546.2.1,
  stackResult547.2.1,
  stackResult548.2.1,
  stackResult549.2.1,
  stackResult550.2.1,
  stackResult551.2.1,
  stackResult552.2.1,
  stackResult553.2.1,
  stackResult554.2.1,
  stackResult555.2.1,
  stackResult556.2.1,
  stackResult557.2.1,
  stackResult558.2.1,
  stackResult559.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult544.2.2.1) stackResult545.2.2.1) stackResult546.2.2.1) stackResult547.2.2.1) stackResult548.2.2.1) stackResult549.2.2.1) stackResult550.2.2.1) stackResult551.2.2.1) stackResult552.2.2.1) stackResult553.2.2.1) stackResult554.2.2.1) stackResult555.2.2.1) stackResult556.2.2.1) stackResult557.2.2.1) stackResult558.2.2.1) stackResult559.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 1799) = (bodies, frames, (bitmapDelta, 1910)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult544_from _
  apply compileWordToStack_cons
  · exact stackResult545_from _
  apply compileWordToStack_cons
  · exact stackResult546_from _
  apply compileWordToStack_cons
  · exact stackResult547_from _
  apply compileWordToStack_cons
  · exact stackResult548_from _
  apply compileWordToStack_cons
  · exact stackResult549_from _
  apply compileWordToStack_cons
  · exact stackResult550_from _
  apply compileWordToStack_cons
  · exact stackResult551_from _
  apply compileWordToStack_cons
  · exact stackResult552_from _
  apply compileWordToStack_cons
  · exact stackResult553_from _
  apply compileWordToStack_cons
  · exact stackResult554_from _
  apply compileWordToStack_cons
  · exact stackResult555_from _
  apply compileWordToStack_cons
  · exact stackResult556_from _
  apply compileWordToStack_cons
  · exact stackResult557_from _
  apply compileWordToStack_cons
  · exact stackResult558_from _
  apply compileWordToStack_cons
  · exact stackResult559_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 1799) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 1910)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 1799 bodies frames bitmapDelta 1910 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 480).take 16).zip
      [oracle544, oracle545, oracle546, oracle547, oracle548, oracle549, oracle550, oracle551, oracle552, oracle553, oracle554, oracle555, oracle556, oracle557, oracle558, oracle559]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle544 PrefixChecks.Shard480.entry,
    wordFunction oracle545 PrefixChecks.Shard481.entry,
    wordFunction oracle546 PrefixChecks.Shard482.entry,
    wordFunction oracle547 PrefixChecks.Shard483.entry,
    wordFunction oracle548 PrefixChecks.Shard484.entry,
    wordFunction oracle549 PrefixChecks.Shard485.entry,
    wordFunction oracle550 PrefixChecks.Shard486.entry,
    wordFunction oracle551 PrefixChecks.Shard487.entry,
    wordFunction oracle552 PrefixChecks.Shard488.entry,
    wordFunction oracle553 PrefixChecks.Shard489.entry,
    wordFunction oracle554 PrefixChecks.Shard490.entry,
    wordFunction oracle555 PrefixChecks.Shard491.entry,
    wordFunction oracle556 PrefixChecks.Shard492.entry,
    wordFunction oracle557 PrefixChecks.Shard493.entry,
    wordFunction oracle558 PrefixChecks.Shard494.entry,
    wordFunction oracle559 PrefixChecks.Shard495.entry] = words
  simp only [
    Word544.wordFunction_eq,
    Word545.wordFunction_eq,
    Word546.wordFunction_eq,
    Word547.wordFunction_eq,
    Word548.wordFunction_eq,
    Word549.wordFunction_eq,
    Word550.wordFunction_eq,
    Word551.wordFunction_eq,
    Word552.wordFunction_eq,
    Word553.wordFunction_eq,
    Word554.wordFunction_eq,
    Word555.wordFunction_eq,
    Word556.wordFunction_eq,
    Word557.wordFunction_eq,
    Word558.wordFunction_eq,
    Word559.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk30
