import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word528
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word529
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word530
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word531
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word532
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word533
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word534
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word535
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word536
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word537
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word538
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word539
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word540
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word541
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word542
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word543
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000
set_option cbv.maxSteps 40000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk29
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

wave8_certified_reduce stackResult528 := WordToStack.Native.compileProgNative
  riscvConfig false Word528.program PrefixChecks.Shard464.arity registers (.nil, 1729)
theorem stackResult528_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word528.program
      PrefixChecks.Shard464.arity registers (prefixList, 1729) =
    (stackResult528.1, stackResult528.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult528.2.2.1, 1732)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word528.program
    PrefixChecks.Shard464.arity registers prefixList 1729
    stackResult528.1 stackResult528.2.1 stackResult528.2.2.1 1732 stackResult528_eq
wave8_certified_reduce stackResult529 := WordToStack.Native.compileProgNative
  riscvConfig false Word529.program PrefixChecks.Shard465.arity registers (.nil, 1732)
theorem stackResult529_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word529.program
      PrefixChecks.Shard465.arity registers (prefixList, 1732) =
    (stackResult529.1, stackResult529.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult529.2.2.1, 1734)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word529.program
    PrefixChecks.Shard465.arity registers prefixList 1732
    stackResult529.1 stackResult529.2.1 stackResult529.2.2.1 1734 stackResult529_eq
wave8_certified_reduce stackResult530 := WordToStack.Native.compileProgNative
  riscvConfig false Word530.program PrefixChecks.Shard466.arity registers (.nil, 1734)
theorem stackResult530_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word530.program
      PrefixChecks.Shard466.arity registers (prefixList, 1734) =
    (stackResult530.1, stackResult530.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult530.2.2.1, 1740)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word530.program
    PrefixChecks.Shard466.arity registers prefixList 1734
    stackResult530.1 stackResult530.2.1 stackResult530.2.2.1 1740 stackResult530_eq
wave8_certified_reduce stackResult531 := WordToStack.Native.compileProgNative
  riscvConfig false Word531.program PrefixChecks.Shard467.arity registers (.nil, 1740)
theorem stackResult531_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word531.program
      PrefixChecks.Shard467.arity registers (prefixList, 1740) =
    (stackResult531.1, stackResult531.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult531.2.2.1, 1745)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word531.program
    PrefixChecks.Shard467.arity registers prefixList 1740
    stackResult531.1 stackResult531.2.1 stackResult531.2.2.1 1745 stackResult531_eq
wave8_certified_reduce stackResult532 := WordToStack.Native.compileProgNative
  riscvConfig false Word532.program PrefixChecks.Shard468.arity registers (.nil, 1745)
theorem stackResult532_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word532.program
      PrefixChecks.Shard468.arity registers (prefixList, 1745) =
    (stackResult532.1, stackResult532.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult532.2.2.1, 1751)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word532.program
    PrefixChecks.Shard468.arity registers prefixList 1745
    stackResult532.1 stackResult532.2.1 stackResult532.2.2.1 1751 stackResult532_eq
wave8_certified_reduce stackResult533 := WordToStack.Native.compileProgNative
  riscvConfig false Word533.program PrefixChecks.Shard469.arity registers (.nil, 1751)
theorem stackResult533_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word533.program
      PrefixChecks.Shard469.arity registers (prefixList, 1751) =
    (stackResult533.1, stackResult533.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult533.2.2.1, 1754)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word533.program
    PrefixChecks.Shard469.arity registers prefixList 1751
    stackResult533.1 stackResult533.2.1 stackResult533.2.2.1 1754 stackResult533_eq
wave8_certified_reduce stackResult534 := WordToStack.Native.compileProgNative
  riscvConfig false Word534.program PrefixChecks.Shard470.arity registers (.nil, 1754)
theorem stackResult534_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word534.program
      PrefixChecks.Shard470.arity registers (prefixList, 1754) =
    (stackResult534.1, stackResult534.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult534.2.2.1, 1771)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word534.program
    PrefixChecks.Shard470.arity registers prefixList 1754
    stackResult534.1 stackResult534.2.1 stackResult534.2.2.1 1771 stackResult534_eq
wave8_certified_reduce stackResult535 := WordToStack.Native.compileProgNative
  riscvConfig false Word535.program PrefixChecks.Shard471.arity registers (.nil, 1771)
theorem stackResult535_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word535.program
      PrefixChecks.Shard471.arity registers (prefixList, 1771) =
    (stackResult535.1, stackResult535.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult535.2.2.1, 1774)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word535.program
    PrefixChecks.Shard471.arity registers prefixList 1771
    stackResult535.1 stackResult535.2.1 stackResult535.2.2.1 1774 stackResult535_eq
wave8_certified_reduce stackResult536 := WordToStack.Native.compileProgNative
  riscvConfig false Word536.program PrefixChecks.Shard472.arity registers (.nil, 1774)
theorem stackResult536_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word536.program
      PrefixChecks.Shard472.arity registers (prefixList, 1774) =
    (stackResult536.1, stackResult536.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult536.2.2.1, 1783)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word536.program
    PrefixChecks.Shard472.arity registers prefixList 1774
    stackResult536.1 stackResult536.2.1 stackResult536.2.2.1 1783 stackResult536_eq
wave8_certified_reduce stackResult537 := WordToStack.Native.compileProgNative
  riscvConfig false Word537.program PrefixChecks.Shard473.arity registers (.nil, 1783)
theorem stackResult537_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word537.program
      PrefixChecks.Shard473.arity registers (prefixList, 1783) =
    (stackResult537.1, stackResult537.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult537.2.2.1, 1786)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word537.program
    PrefixChecks.Shard473.arity registers prefixList 1783
    stackResult537.1 stackResult537.2.1 stackResult537.2.2.1 1786 stackResult537_eq
wave8_certified_reduce stackResult538 := WordToStack.Native.compileProgNative
  riscvConfig false Word538.program PrefixChecks.Shard474.arity registers (.nil, 1786)
theorem stackResult538_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word538.program
      PrefixChecks.Shard474.arity registers (prefixList, 1786) =
    (stackResult538.1, stackResult538.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult538.2.2.1, 1786)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word538.program
    PrefixChecks.Shard474.arity registers prefixList 1786
    stackResult538.1 stackResult538.2.1 stackResult538.2.2.1 1786 stackResult538_eq
wave8_certified_reduce stackResult539 := WordToStack.Native.compileProgNative
  riscvConfig false Word539.program PrefixChecks.Shard475.arity registers (.nil, 1786)
theorem stackResult539_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word539.program
      PrefixChecks.Shard475.arity registers (prefixList, 1786) =
    (stackResult539.1, stackResult539.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult539.2.2.1, 1789)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word539.program
    PrefixChecks.Shard475.arity registers prefixList 1786
    stackResult539.1 stackResult539.2.1 stackResult539.2.2.1 1789 stackResult539_eq
wave8_certified_reduce stackResult540 := WordToStack.Native.compileProgNative
  riscvConfig false Word540.program PrefixChecks.Shard476.arity registers (.nil, 1789)
theorem stackResult540_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word540.program
      PrefixChecks.Shard476.arity registers (prefixList, 1789) =
    (stackResult540.1, stackResult540.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult540.2.2.1, 1789)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word540.program
    PrefixChecks.Shard476.arity registers prefixList 1789
    stackResult540.1 stackResult540.2.1 stackResult540.2.2.1 1789 stackResult540_eq
wave8_certified_reduce stackResult541 := WordToStack.Native.compileProgNative
  riscvConfig false Word541.program PrefixChecks.Shard477.arity registers (.nil, 1789)
theorem stackResult541_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word541.program
      PrefixChecks.Shard477.arity registers (prefixList, 1789) =
    (stackResult541.1, stackResult541.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult541.2.2.1, 1789)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word541.program
    PrefixChecks.Shard477.arity registers prefixList 1789
    stackResult541.1 stackResult541.2.1 stackResult541.2.2.1 1789 stackResult541_eq
wave8_certified_reduce stackResult542 := WordToStack.Native.compileProgNative
  riscvConfig false Word542.program PrefixChecks.Shard478.arity registers (.nil, 1789)
theorem stackResult542_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word542.program
      PrefixChecks.Shard478.arity registers (prefixList, 1789) =
    (stackResult542.1, stackResult542.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult542.2.2.1, 1794)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word542.program
    PrefixChecks.Shard478.arity registers prefixList 1789
    stackResult542.1 stackResult542.2.1 stackResult542.2.2.1 1794 stackResult542_eq
wave8_certified_reduce stackResult543 := WordToStack.Native.compileProgNative
  riscvConfig false Word543.program PrefixChecks.Shard479.arity registers (.nil, 1794)
theorem stackResult543_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word543.program
      PrefixChecks.Shard479.arity registers (prefixList, 1794) =
    (stackResult543.1, stackResult543.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult543.2.2.1, 1799)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word543.program
    PrefixChecks.Shard479.arity registers prefixList 1794
    stackResult543.1 stackResult543.2.1 stackResult543.2.2.1 1799 stackResult543_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard464.name, PrefixChecks.Shard464.arity, Word528.program),
  (PrefixChecks.Shard465.name, PrefixChecks.Shard465.arity, Word529.program),
  (PrefixChecks.Shard466.name, PrefixChecks.Shard466.arity, Word530.program),
  (PrefixChecks.Shard467.name, PrefixChecks.Shard467.arity, Word531.program),
  (PrefixChecks.Shard468.name, PrefixChecks.Shard468.arity, Word532.program),
  (PrefixChecks.Shard469.name, PrefixChecks.Shard469.arity, Word533.program),
  (PrefixChecks.Shard470.name, PrefixChecks.Shard470.arity, Word534.program),
  (PrefixChecks.Shard471.name, PrefixChecks.Shard471.arity, Word535.program),
  (PrefixChecks.Shard472.name, PrefixChecks.Shard472.arity, Word536.program),
  (PrefixChecks.Shard473.name, PrefixChecks.Shard473.arity, Word537.program),
  (PrefixChecks.Shard474.name, PrefixChecks.Shard474.arity, Word538.program),
  (PrefixChecks.Shard475.name, PrefixChecks.Shard475.arity, Word539.program),
  (PrefixChecks.Shard476.name, PrefixChecks.Shard476.arity, Word540.program),
  (PrefixChecks.Shard477.name, PrefixChecks.Shard477.arity, Word541.program),
  (PrefixChecks.Shard478.name, PrefixChecks.Shard478.arity, Word542.program),
  (PrefixChecks.Shard479.name, PrefixChecks.Shard479.arity, Word543.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard464.name, stackResult528.1),
  (PrefixChecks.Shard465.name, stackResult529.1),
  (PrefixChecks.Shard466.name, stackResult530.1),
  (PrefixChecks.Shard467.name, stackResult531.1),
  (PrefixChecks.Shard468.name, stackResult532.1),
  (PrefixChecks.Shard469.name, stackResult533.1),
  (PrefixChecks.Shard470.name, stackResult534.1),
  (PrefixChecks.Shard471.name, stackResult535.1),
  (PrefixChecks.Shard472.name, stackResult536.1),
  (PrefixChecks.Shard473.name, stackResult537.1),
  (PrefixChecks.Shard474.name, stackResult538.1),
  (PrefixChecks.Shard475.name, stackResult539.1),
  (PrefixChecks.Shard476.name, stackResult540.1),
  (PrefixChecks.Shard477.name, stackResult541.1),
  (PrefixChecks.Shard478.name, stackResult542.1),
  (PrefixChecks.Shard479.name, stackResult543.1)
]

noncomputable def frames : List Nat := [
  stackResult528.2.1,
  stackResult529.2.1,
  stackResult530.2.1,
  stackResult531.2.1,
  stackResult532.2.1,
  stackResult533.2.1,
  stackResult534.2.1,
  stackResult535.2.1,
  stackResult536.2.1,
  stackResult537.2.1,
  stackResult538.2.1,
  stackResult539.2.1,
  stackResult540.2.1,
  stackResult541.2.1,
  stackResult542.2.1,
  stackResult543.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult528.2.2.1) stackResult529.2.2.1) stackResult530.2.2.1) stackResult531.2.2.1) stackResult532.2.2.1) stackResult533.2.2.1) stackResult534.2.2.1) stackResult535.2.2.1) stackResult536.2.2.1) stackResult537.2.2.1) stackResult538.2.2.1) stackResult539.2.2.1) stackResult540.2.2.1) stackResult541.2.2.1) stackResult542.2.2.1) stackResult543.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 1729) = (bodies, frames, (bitmapDelta, 1799)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult528_from _
  apply compileWordToStack_cons
  · exact stackResult529_from _
  apply compileWordToStack_cons
  · exact stackResult530_from _
  apply compileWordToStack_cons
  · exact stackResult531_from _
  apply compileWordToStack_cons
  · exact stackResult532_from _
  apply compileWordToStack_cons
  · exact stackResult533_from _
  apply compileWordToStack_cons
  · exact stackResult534_from _
  apply compileWordToStack_cons
  · exact stackResult535_from _
  apply compileWordToStack_cons
  · exact stackResult536_from _
  apply compileWordToStack_cons
  · exact stackResult537_from _
  apply compileWordToStack_cons
  · exact stackResult538_from _
  apply compileWordToStack_cons
  · exact stackResult539_from _
  apply compileWordToStack_cons
  · exact stackResult540_from _
  apply compileWordToStack_cons
  · exact stackResult541_from _
  apply compileWordToStack_cons
  · exact stackResult542_from _
  apply compileWordToStack_cons
  · exact stackResult543_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 1729) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 1799)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 1729 bodies frames bitmapDelta 1799 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 464).take 16).zip
      [oracle528, oracle529, oracle530, oracle531, oracle532, oracle533, oracle534, oracle535, oracle536, oracle537, oracle538, oracle539, oracle540, oracle541, oracle542, oracle543]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle528 PrefixChecks.Shard464.entry,
    wordFunction oracle529 PrefixChecks.Shard465.entry,
    wordFunction oracle530 PrefixChecks.Shard466.entry,
    wordFunction oracle531 PrefixChecks.Shard467.entry,
    wordFunction oracle532 PrefixChecks.Shard468.entry,
    wordFunction oracle533 PrefixChecks.Shard469.entry,
    wordFunction oracle534 PrefixChecks.Shard470.entry,
    wordFunction oracle535 PrefixChecks.Shard471.entry,
    wordFunction oracle536 PrefixChecks.Shard472.entry,
    wordFunction oracle537 PrefixChecks.Shard473.entry,
    wordFunction oracle538 PrefixChecks.Shard474.entry,
    wordFunction oracle539 PrefixChecks.Shard475.entry,
    wordFunction oracle540 PrefixChecks.Shard476.entry,
    wordFunction oracle541 PrefixChecks.Shard477.entry,
    wordFunction oracle542 PrefixChecks.Shard478.entry,
    wordFunction oracle543 PrefixChecks.Shard479.entry] = words
  simp only [
    Word528.wordFunction_eq,
    Word529.wordFunction_eq,
    Word530.wordFunction_eq,
    Word531.wordFunction_eq,
    Word532.wordFunction_eq,
    Word533.wordFunction_eq,
    Word534.wordFunction_eq,
    Word535.wordFunction_eq,
    Word536.wordFunction_eq,
    Word537.wordFunction_eq,
    Word538.wordFunction_eq,
    Word539.wordFunction_eq,
    Word540.wordFunction_eq,
    Word541.wordFunction_eq,
    Word542.wordFunction_eq,
    Word543.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk29
