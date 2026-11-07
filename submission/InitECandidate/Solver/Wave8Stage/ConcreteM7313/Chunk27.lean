import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word496
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word497
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word498
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word499
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word500
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word501
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word502
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word503
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word504
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word505
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word506
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word507
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word508
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word509
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word510
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word511
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk27
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult496 := WordToStack.Native.compileProgNative
  riscvConfig false Word496.program PrefixChecks.Shard432.arity registers (.nil, 1542)
theorem stackResult496_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word496.program
      PrefixChecks.Shard432.arity registers (prefixList, 1542) =
    (stackResult496.1, stackResult496.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult496.2.2.1, 1543)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word496.program
    PrefixChecks.Shard432.arity registers prefixList 1542
    stackResult496.1 stackResult496.2.1 stackResult496.2.2.1 1543 stackResult496_eq
wave8_kernel_reduce stackResult497 := WordToStack.Native.compileProgNative
  riscvConfig false Word497.program PrefixChecks.Shard433.arity registers (.nil, 1543)
theorem stackResult497_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word497.program
      PrefixChecks.Shard433.arity registers (prefixList, 1543) =
    (stackResult497.1, stackResult497.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult497.2.2.1, 1549)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word497.program
    PrefixChecks.Shard433.arity registers prefixList 1543
    stackResult497.1 stackResult497.2.1 stackResult497.2.2.1 1549 stackResult497_eq
wave8_kernel_reduce stackResult498 := WordToStack.Native.compileProgNative
  riscvConfig false Word498.program PrefixChecks.Shard434.arity registers (.nil, 1549)
theorem stackResult498_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word498.program
      PrefixChecks.Shard434.arity registers (prefixList, 1549) =
    (stackResult498.1, stackResult498.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult498.2.2.1, 1555)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word498.program
    PrefixChecks.Shard434.arity registers prefixList 1549
    stackResult498.1 stackResult498.2.1 stackResult498.2.2.1 1555 stackResult498_eq
wave8_kernel_reduce stackResult499 := WordToStack.Native.compileProgNative
  riscvConfig false Word499.program PrefixChecks.Shard435.arity registers (.nil, 1555)
theorem stackResult499_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word499.program
      PrefixChecks.Shard435.arity registers (prefixList, 1555) =
    (stackResult499.1, stackResult499.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult499.2.2.1, 1561)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word499.program
    PrefixChecks.Shard435.arity registers prefixList 1555
    stackResult499.1 stackResult499.2.1 stackResult499.2.2.1 1561 stackResult499_eq
wave8_kernel_reduce stackResult500 := WordToStack.Native.compileProgNative
  riscvConfig false Word500.program PrefixChecks.Shard436.arity registers (.nil, 1561)
theorem stackResult500_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word500.program
      PrefixChecks.Shard436.arity registers (prefixList, 1561) =
    (stackResult500.1, stackResult500.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult500.2.2.1, 1567)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word500.program
    PrefixChecks.Shard436.arity registers prefixList 1561
    stackResult500.1 stackResult500.2.1 stackResult500.2.2.1 1567 stackResult500_eq
wave8_kernel_reduce stackResult501 := WordToStack.Native.compileProgNative
  riscvConfig false Word501.program PrefixChecks.Shard437.arity registers (.nil, 1567)
theorem stackResult501_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word501.program
      PrefixChecks.Shard437.arity registers (prefixList, 1567) =
    (stackResult501.1, stackResult501.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult501.2.2.1, 1573)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word501.program
    PrefixChecks.Shard437.arity registers prefixList 1567
    stackResult501.1 stackResult501.2.1 stackResult501.2.2.1 1573 stackResult501_eq
wave8_kernel_reduce stackResult502 := WordToStack.Native.compileProgNative
  riscvConfig false Word502.program PrefixChecks.Shard438.arity registers (.nil, 1573)
theorem stackResult502_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word502.program
      PrefixChecks.Shard438.arity registers (prefixList, 1573) =
    (stackResult502.1, stackResult502.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult502.2.2.1, 1579)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word502.program
    PrefixChecks.Shard438.arity registers prefixList 1573
    stackResult502.1 stackResult502.2.1 stackResult502.2.2.1 1579 stackResult502_eq
wave8_kernel_reduce stackResult503 := WordToStack.Native.compileProgNative
  riscvConfig false Word503.program PrefixChecks.Shard439.arity registers (.nil, 1579)
theorem stackResult503_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word503.program
      PrefixChecks.Shard439.arity registers (prefixList, 1579) =
    (stackResult503.1, stackResult503.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult503.2.2.1, 1585)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word503.program
    PrefixChecks.Shard439.arity registers prefixList 1579
    stackResult503.1 stackResult503.2.1 stackResult503.2.2.1 1585 stackResult503_eq
wave8_kernel_reduce stackResult504 := WordToStack.Native.compileProgNative
  riscvConfig false Word504.program PrefixChecks.Shard440.arity registers (.nil, 1585)
theorem stackResult504_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word504.program
      PrefixChecks.Shard440.arity registers (prefixList, 1585) =
    (stackResult504.1, stackResult504.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult504.2.2.1, 1592)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word504.program
    PrefixChecks.Shard440.arity registers prefixList 1585
    stackResult504.1 stackResult504.2.1 stackResult504.2.2.1 1592 stackResult504_eq
wave8_kernel_reduce stackResult505 := WordToStack.Native.compileProgNative
  riscvConfig false Word505.program PrefixChecks.Shard441.arity registers (.nil, 1592)
theorem stackResult505_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word505.program
      PrefixChecks.Shard441.arity registers (prefixList, 1592) =
    (stackResult505.1, stackResult505.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult505.2.2.1, 1599)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word505.program
    PrefixChecks.Shard441.arity registers prefixList 1592
    stackResult505.1 stackResult505.2.1 stackResult505.2.2.1 1599 stackResult505_eq
wave8_kernel_reduce stackResult506 := WordToStack.Native.compileProgNative
  riscvConfig false Word506.program PrefixChecks.Shard442.arity registers (.nil, 1599)
theorem stackResult506_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word506.program
      PrefixChecks.Shard442.arity registers (prefixList, 1599) =
    (stackResult506.1, stackResult506.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult506.2.2.1, 1606)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word506.program
    PrefixChecks.Shard442.arity registers prefixList 1599
    stackResult506.1 stackResult506.2.1 stackResult506.2.2.1 1606 stackResult506_eq
wave8_kernel_reduce stackResult507 := WordToStack.Native.compileProgNative
  riscvConfig false Word507.program PrefixChecks.Shard443.arity registers (.nil, 1606)
theorem stackResult507_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word507.program
      PrefixChecks.Shard443.arity registers (prefixList, 1606) =
    (stackResult507.1, stackResult507.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult507.2.2.1, 1613)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word507.program
    PrefixChecks.Shard443.arity registers prefixList 1606
    stackResult507.1 stackResult507.2.1 stackResult507.2.2.1 1613 stackResult507_eq
wave8_kernel_reduce stackResult508 := WordToStack.Native.compileProgNative
  riscvConfig false Word508.program PrefixChecks.Shard444.arity registers (.nil, 1613)
theorem stackResult508_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word508.program
      PrefixChecks.Shard444.arity registers (prefixList, 1613) =
    (stackResult508.1, stackResult508.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult508.2.2.1, 1619)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word508.program
    PrefixChecks.Shard444.arity registers prefixList 1613
    stackResult508.1 stackResult508.2.1 stackResult508.2.2.1 1619 stackResult508_eq
wave8_kernel_reduce stackResult509 := WordToStack.Native.compileProgNative
  riscvConfig false Word509.program PrefixChecks.Shard445.arity registers (.nil, 1619)
theorem stackResult509_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word509.program
      PrefixChecks.Shard445.arity registers (prefixList, 1619) =
    (stackResult509.1, stackResult509.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult509.2.2.1, 1625)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word509.program
    PrefixChecks.Shard445.arity registers prefixList 1619
    stackResult509.1 stackResult509.2.1 stackResult509.2.2.1 1625 stackResult509_eq
wave8_kernel_reduce stackResult510 := WordToStack.Native.compileProgNative
  riscvConfig false Word510.program PrefixChecks.Shard446.arity registers (.nil, 1625)
theorem stackResult510_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word510.program
      PrefixChecks.Shard446.arity registers (prefixList, 1625) =
    (stackResult510.1, stackResult510.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult510.2.2.1, 1631)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word510.program
    PrefixChecks.Shard446.arity registers prefixList 1625
    stackResult510.1 stackResult510.2.1 stackResult510.2.2.1 1631 stackResult510_eq
wave8_kernel_reduce stackResult511 := WordToStack.Native.compileProgNative
  riscvConfig false Word511.program PrefixChecks.Shard447.arity registers (.nil, 1631)
theorem stackResult511_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word511.program
      PrefixChecks.Shard447.arity registers (prefixList, 1631) =
    (stackResult511.1, stackResult511.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult511.2.2.1, 1637)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word511.program
    PrefixChecks.Shard447.arity registers prefixList 1631
    stackResult511.1 stackResult511.2.1 stackResult511.2.2.1 1637 stackResult511_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard432.name, PrefixChecks.Shard432.arity, Word496.program),
  (PrefixChecks.Shard433.name, PrefixChecks.Shard433.arity, Word497.program),
  (PrefixChecks.Shard434.name, PrefixChecks.Shard434.arity, Word498.program),
  (PrefixChecks.Shard435.name, PrefixChecks.Shard435.arity, Word499.program),
  (PrefixChecks.Shard436.name, PrefixChecks.Shard436.arity, Word500.program),
  (PrefixChecks.Shard437.name, PrefixChecks.Shard437.arity, Word501.program),
  (PrefixChecks.Shard438.name, PrefixChecks.Shard438.arity, Word502.program),
  (PrefixChecks.Shard439.name, PrefixChecks.Shard439.arity, Word503.program),
  (PrefixChecks.Shard440.name, PrefixChecks.Shard440.arity, Word504.program),
  (PrefixChecks.Shard441.name, PrefixChecks.Shard441.arity, Word505.program),
  (PrefixChecks.Shard442.name, PrefixChecks.Shard442.arity, Word506.program),
  (PrefixChecks.Shard443.name, PrefixChecks.Shard443.arity, Word507.program),
  (PrefixChecks.Shard444.name, PrefixChecks.Shard444.arity, Word508.program),
  (PrefixChecks.Shard445.name, PrefixChecks.Shard445.arity, Word509.program),
  (PrefixChecks.Shard446.name, PrefixChecks.Shard446.arity, Word510.program),
  (PrefixChecks.Shard447.name, PrefixChecks.Shard447.arity, Word511.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard432.name, stackResult496.1),
  (PrefixChecks.Shard433.name, stackResult497.1),
  (PrefixChecks.Shard434.name, stackResult498.1),
  (PrefixChecks.Shard435.name, stackResult499.1),
  (PrefixChecks.Shard436.name, stackResult500.1),
  (PrefixChecks.Shard437.name, stackResult501.1),
  (PrefixChecks.Shard438.name, stackResult502.1),
  (PrefixChecks.Shard439.name, stackResult503.1),
  (PrefixChecks.Shard440.name, stackResult504.1),
  (PrefixChecks.Shard441.name, stackResult505.1),
  (PrefixChecks.Shard442.name, stackResult506.1),
  (PrefixChecks.Shard443.name, stackResult507.1),
  (PrefixChecks.Shard444.name, stackResult508.1),
  (PrefixChecks.Shard445.name, stackResult509.1),
  (PrefixChecks.Shard446.name, stackResult510.1),
  (PrefixChecks.Shard447.name, stackResult511.1)
]

noncomputable def frames : List Nat := [
  stackResult496.2.1,
  stackResult497.2.1,
  stackResult498.2.1,
  stackResult499.2.1,
  stackResult500.2.1,
  stackResult501.2.1,
  stackResult502.2.1,
  stackResult503.2.1,
  stackResult504.2.1,
  stackResult505.2.1,
  stackResult506.2.1,
  stackResult507.2.1,
  stackResult508.2.1,
  stackResult509.2.1,
  stackResult510.2.1,
  stackResult511.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult496.2.2.1) stackResult497.2.2.1) stackResult498.2.2.1) stackResult499.2.2.1) stackResult500.2.2.1) stackResult501.2.2.1) stackResult502.2.2.1) stackResult503.2.2.1) stackResult504.2.2.1) stackResult505.2.2.1) stackResult506.2.2.1) stackResult507.2.2.1) stackResult508.2.2.1) stackResult509.2.2.1) stackResult510.2.2.1) stackResult511.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 1542) = (bodies, frames, (bitmapDelta, 1637)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult496_from _
  apply compileWordToStack_cons
  · exact stackResult497_from _
  apply compileWordToStack_cons
  · exact stackResult498_from _
  apply compileWordToStack_cons
  · exact stackResult499_from _
  apply compileWordToStack_cons
  · exact stackResult500_from _
  apply compileWordToStack_cons
  · exact stackResult501_from _
  apply compileWordToStack_cons
  · exact stackResult502_from _
  apply compileWordToStack_cons
  · exact stackResult503_from _
  apply compileWordToStack_cons
  · exact stackResult504_from _
  apply compileWordToStack_cons
  · exact stackResult505_from _
  apply compileWordToStack_cons
  · exact stackResult506_from _
  apply compileWordToStack_cons
  · exact stackResult507_from _
  apply compileWordToStack_cons
  · exact stackResult508_from _
  apply compileWordToStack_cons
  · exact stackResult509_from _
  apply compileWordToStack_cons
  · exact stackResult510_from _
  apply compileWordToStack_cons
  · exact stackResult511_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 1542) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 1637)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 1542 bodies frames bitmapDelta 1637 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 432).take 16).zip
      [oracle496, oracle497, oracle498, oracle499, oracle500, oracle501, oracle502, oracle503, oracle504, oracle505, oracle506, oracle507, oracle508, oracle509, oracle510, oracle511]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle496 PrefixChecks.Shard432.entry,
    wordFunction oracle497 PrefixChecks.Shard433.entry,
    wordFunction oracle498 PrefixChecks.Shard434.entry,
    wordFunction oracle499 PrefixChecks.Shard435.entry,
    wordFunction oracle500 PrefixChecks.Shard436.entry,
    wordFunction oracle501 PrefixChecks.Shard437.entry,
    wordFunction oracle502 PrefixChecks.Shard438.entry,
    wordFunction oracle503 PrefixChecks.Shard439.entry,
    wordFunction oracle504 PrefixChecks.Shard440.entry,
    wordFunction oracle505 PrefixChecks.Shard441.entry,
    wordFunction oracle506 PrefixChecks.Shard442.entry,
    wordFunction oracle507 PrefixChecks.Shard443.entry,
    wordFunction oracle508 PrefixChecks.Shard444.entry,
    wordFunction oracle509 PrefixChecks.Shard445.entry,
    wordFunction oracle510 PrefixChecks.Shard446.entry,
    wordFunction oracle511 PrefixChecks.Shard447.entry] = words
  simp only [
    Word496.wordFunction_eq,
    Word497.wordFunction_eq,
    Word498.wordFunction_eq,
    Word499.wordFunction_eq,
    Word500.wordFunction_eq,
    Word501.wordFunction_eq,
    Word502.wordFunction_eq,
    Word503.wordFunction_eq,
    Word504.wordFunction_eq,
    Word505.wordFunction_eq,
    Word506.wordFunction_eq,
    Word507.wordFunction_eq,
    Word508.wordFunction_eq,
    Word509.wordFunction_eq,
    Word510.wordFunction_eq,
    Word511.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk27
