import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word560
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word561
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word562
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word563
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word564
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word565
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word566
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word567
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word568
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word569
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word570
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word571
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word572
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word573
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word574
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word575
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000
set_option cbv.maxSteps 40000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk31
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

wave8_certified_reduce stackResult560 := WordToStack.Native.compileProgNative
  riscvConfig false Word560.program PrefixChecks.Shard496.arity registers (.nil, 1910)
theorem stackResult560_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word560.program
      PrefixChecks.Shard496.arity registers (prefixList, 1910) =
    (stackResult560.1, stackResult560.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult560.2.2.1, 1923)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word560.program
    PrefixChecks.Shard496.arity registers prefixList 1910
    stackResult560.1 stackResult560.2.1 stackResult560.2.2.1 1923 stackResult560_eq
wave8_certified_reduce stackResult561 := WordToStack.Native.compileProgNative
  riscvConfig false Word561.program PrefixChecks.Shard497.arity registers (.nil, 1923)
theorem stackResult561_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word561.program
      PrefixChecks.Shard497.arity registers (prefixList, 1923) =
    (stackResult561.1, stackResult561.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult561.2.2.1, 1924)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word561.program
    PrefixChecks.Shard497.arity registers prefixList 1923
    stackResult561.1 stackResult561.2.1 stackResult561.2.2.1 1924 stackResult561_eq
wave8_certified_reduce stackResult562 := WordToStack.Native.compileProgNative
  riscvConfig false Word562.program PrefixChecks.Shard498.arity registers (.nil, 1924)
theorem stackResult562_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word562.program
      PrefixChecks.Shard498.arity registers (prefixList, 1924) =
    (stackResult562.1, stackResult562.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult562.2.2.1, 1927)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word562.program
    PrefixChecks.Shard498.arity registers prefixList 1924
    stackResult562.1 stackResult562.2.1 stackResult562.2.2.1 1927 stackResult562_eq
wave8_certified_reduce stackResult563 := WordToStack.Native.compileProgNative
  riscvConfig false Word563.program PrefixChecks.Shard499.arity registers (.nil, 1927)
theorem stackResult563_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word563.program
      PrefixChecks.Shard499.arity registers (prefixList, 1927) =
    (stackResult563.1, stackResult563.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult563.2.2.1, 1928)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word563.program
    PrefixChecks.Shard499.arity registers prefixList 1927
    stackResult563.1 stackResult563.2.1 stackResult563.2.2.1 1928 stackResult563_eq
wave8_certified_reduce stackResult564 := WordToStack.Native.compileProgNative
  riscvConfig false Word564.program PrefixChecks.Shard500.arity registers (.nil, 1928)
theorem stackResult564_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word564.program
      PrefixChecks.Shard500.arity registers (prefixList, 1928) =
    (stackResult564.1, stackResult564.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult564.2.2.1, 1931)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word564.program
    PrefixChecks.Shard500.arity registers prefixList 1928
    stackResult564.1 stackResult564.2.1 stackResult564.2.2.1 1931 stackResult564_eq
wave8_certified_reduce stackResult565 := WordToStack.Native.compileProgNative
  riscvConfig false Word565.program PrefixChecks.Shard501.arity registers (.nil, 1931)
theorem stackResult565_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word565.program
      PrefixChecks.Shard501.arity registers (prefixList, 1931) =
    (stackResult565.1, stackResult565.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult565.2.2.1, 1933)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word565.program
    PrefixChecks.Shard501.arity registers prefixList 1931
    stackResult565.1 stackResult565.2.1 stackResult565.2.2.1 1933 stackResult565_eq
wave8_certified_reduce stackResult566 := WordToStack.Native.compileProgNative
  riscvConfig false Word566.program PrefixChecks.Shard502.arity registers (.nil, 1933)
theorem stackResult566_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word566.program
      PrefixChecks.Shard502.arity registers (prefixList, 1933) =
    (stackResult566.1, stackResult566.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult566.2.2.1, 1941)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word566.program
    PrefixChecks.Shard502.arity registers prefixList 1933
    stackResult566.1 stackResult566.2.1 stackResult566.2.2.1 1941 stackResult566_eq
wave8_certified_reduce stackResult567 := WordToStack.Native.compileProgNative
  riscvConfig false Word567.program PrefixChecks.Shard503.arity registers (.nil, 1941)
theorem stackResult567_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word567.program
      PrefixChecks.Shard503.arity registers (prefixList, 1941) =
    (stackResult567.1, stackResult567.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult567.2.2.1, 1959)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word567.program
    PrefixChecks.Shard503.arity registers prefixList 1941
    stackResult567.1 stackResult567.2.1 stackResult567.2.2.1 1959 stackResult567_eq
wave8_certified_reduce stackResult568 := WordToStack.Native.compileProgNative
  riscvConfig false Word568.program PrefixChecks.Shard504.arity registers (.nil, 1959)
theorem stackResult568_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word568.program
      PrefixChecks.Shard504.arity registers (prefixList, 1959) =
    (stackResult568.1, stackResult568.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult568.2.2.1, 1962)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word568.program
    PrefixChecks.Shard504.arity registers prefixList 1959
    stackResult568.1 stackResult568.2.1 stackResult568.2.2.1 1962 stackResult568_eq
wave8_certified_reduce stackResult569 := WordToStack.Native.compileProgNative
  riscvConfig false Word569.program PrefixChecks.Shard505.arity registers (.nil, 1962)
theorem stackResult569_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word569.program
      PrefixChecks.Shard505.arity registers (prefixList, 1962) =
    (stackResult569.1, stackResult569.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult569.2.2.1, 1976)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word569.program
    PrefixChecks.Shard505.arity registers prefixList 1962
    stackResult569.1 stackResult569.2.1 stackResult569.2.2.1 1976 stackResult569_eq
wave8_certified_reduce stackResult570 := WordToStack.Native.compileProgNative
  riscvConfig false Word570.program PrefixChecks.Shard506.arity registers (.nil, 1976)
theorem stackResult570_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word570.program
      PrefixChecks.Shard506.arity registers (prefixList, 1976) =
    (stackResult570.1, stackResult570.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult570.2.2.1, 1987)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word570.program
    PrefixChecks.Shard506.arity registers prefixList 1976
    stackResult570.1 stackResult570.2.1 stackResult570.2.2.1 1987 stackResult570_eq
wave8_certified_reduce stackResult571 := WordToStack.Native.compileProgNative
  riscvConfig false Word571.program PrefixChecks.Shard507.arity registers (.nil, 1987)
theorem stackResult571_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word571.program
      PrefixChecks.Shard507.arity registers (prefixList, 1987) =
    (stackResult571.1, stackResult571.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult571.2.2.1, 1991)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word571.program
    PrefixChecks.Shard507.arity registers prefixList 1987
    stackResult571.1 stackResult571.2.1 stackResult571.2.2.1 1991 stackResult571_eq
wave8_certified_reduce stackResult572 := WordToStack.Native.compileProgNative
  riscvConfig false Word572.program PrefixChecks.Shard508.arity registers (.nil, 1991)
theorem stackResult572_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word572.program
      PrefixChecks.Shard508.arity registers (prefixList, 1991) =
    (stackResult572.1, stackResult572.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult572.2.2.1, 1991)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word572.program
    PrefixChecks.Shard508.arity registers prefixList 1991
    stackResult572.1 stackResult572.2.1 stackResult572.2.2.1 1991 stackResult572_eq
wave8_certified_reduce stackResult573 := WordToStack.Native.compileProgNative
  riscvConfig false Word573.program PrefixChecks.Shard509.arity registers (.nil, 1991)
theorem stackResult573_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word573.program
      PrefixChecks.Shard509.arity registers (prefixList, 1991) =
    (stackResult573.1, stackResult573.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult573.2.2.1, 1995)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word573.program
    PrefixChecks.Shard509.arity registers prefixList 1991
    stackResult573.1 stackResult573.2.1 stackResult573.2.2.1 1995 stackResult573_eq
wave8_certified_reduce stackResult574 := WordToStack.Native.compileProgNative
  riscvConfig false Word574.program PrefixChecks.Shard510.arity registers (.nil, 1995)
theorem stackResult574_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word574.program
      PrefixChecks.Shard510.arity registers (prefixList, 1995) =
    (stackResult574.1, stackResult574.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult574.2.2.1, 2002)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word574.program
    PrefixChecks.Shard510.arity registers prefixList 1995
    stackResult574.1 stackResult574.2.1 stackResult574.2.2.1 2002 stackResult574_eq
wave8_certified_reduce stackResult575 := WordToStack.Native.compileProgNative
  riscvConfig false Word575.program PrefixChecks.Shard511.arity registers (.nil, 2002)
theorem stackResult575_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word575.program
      PrefixChecks.Shard511.arity registers (prefixList, 2002) =
    (stackResult575.1, stackResult575.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult575.2.2.1, 2007)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word575.program
    PrefixChecks.Shard511.arity registers prefixList 2002
    stackResult575.1 stackResult575.2.1 stackResult575.2.2.1 2007 stackResult575_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard496.name, PrefixChecks.Shard496.arity, Word560.program),
  (PrefixChecks.Shard497.name, PrefixChecks.Shard497.arity, Word561.program),
  (PrefixChecks.Shard498.name, PrefixChecks.Shard498.arity, Word562.program),
  (PrefixChecks.Shard499.name, PrefixChecks.Shard499.arity, Word563.program),
  (PrefixChecks.Shard500.name, PrefixChecks.Shard500.arity, Word564.program),
  (PrefixChecks.Shard501.name, PrefixChecks.Shard501.arity, Word565.program),
  (PrefixChecks.Shard502.name, PrefixChecks.Shard502.arity, Word566.program),
  (PrefixChecks.Shard503.name, PrefixChecks.Shard503.arity, Word567.program),
  (PrefixChecks.Shard504.name, PrefixChecks.Shard504.arity, Word568.program),
  (PrefixChecks.Shard505.name, PrefixChecks.Shard505.arity, Word569.program),
  (PrefixChecks.Shard506.name, PrefixChecks.Shard506.arity, Word570.program),
  (PrefixChecks.Shard507.name, PrefixChecks.Shard507.arity, Word571.program),
  (PrefixChecks.Shard508.name, PrefixChecks.Shard508.arity, Word572.program),
  (PrefixChecks.Shard509.name, PrefixChecks.Shard509.arity, Word573.program),
  (PrefixChecks.Shard510.name, PrefixChecks.Shard510.arity, Word574.program),
  (PrefixChecks.Shard511.name, PrefixChecks.Shard511.arity, Word575.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard496.name, stackResult560.1),
  (PrefixChecks.Shard497.name, stackResult561.1),
  (PrefixChecks.Shard498.name, stackResult562.1),
  (PrefixChecks.Shard499.name, stackResult563.1),
  (PrefixChecks.Shard500.name, stackResult564.1),
  (PrefixChecks.Shard501.name, stackResult565.1),
  (PrefixChecks.Shard502.name, stackResult566.1),
  (PrefixChecks.Shard503.name, stackResult567.1),
  (PrefixChecks.Shard504.name, stackResult568.1),
  (PrefixChecks.Shard505.name, stackResult569.1),
  (PrefixChecks.Shard506.name, stackResult570.1),
  (PrefixChecks.Shard507.name, stackResult571.1),
  (PrefixChecks.Shard508.name, stackResult572.1),
  (PrefixChecks.Shard509.name, stackResult573.1),
  (PrefixChecks.Shard510.name, stackResult574.1),
  (PrefixChecks.Shard511.name, stackResult575.1)
]

noncomputable def frames : List Nat := [
  stackResult560.2.1,
  stackResult561.2.1,
  stackResult562.2.1,
  stackResult563.2.1,
  stackResult564.2.1,
  stackResult565.2.1,
  stackResult566.2.1,
  stackResult567.2.1,
  stackResult568.2.1,
  stackResult569.2.1,
  stackResult570.2.1,
  stackResult571.2.1,
  stackResult572.2.1,
  stackResult573.2.1,
  stackResult574.2.1,
  stackResult575.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult560.2.2.1) stackResult561.2.2.1) stackResult562.2.2.1) stackResult563.2.2.1) stackResult564.2.2.1) stackResult565.2.2.1) stackResult566.2.2.1) stackResult567.2.2.1) stackResult568.2.2.1) stackResult569.2.2.1) stackResult570.2.2.1) stackResult571.2.2.1) stackResult572.2.2.1) stackResult573.2.2.1) stackResult574.2.2.1) stackResult575.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 1910) = (bodies, frames, (bitmapDelta, 2007)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult560_from _
  apply compileWordToStack_cons
  · exact stackResult561_from _
  apply compileWordToStack_cons
  · exact stackResult562_from _
  apply compileWordToStack_cons
  · exact stackResult563_from _
  apply compileWordToStack_cons
  · exact stackResult564_from _
  apply compileWordToStack_cons
  · exact stackResult565_from _
  apply compileWordToStack_cons
  · exact stackResult566_from _
  apply compileWordToStack_cons
  · exact stackResult567_from _
  apply compileWordToStack_cons
  · exact stackResult568_from _
  apply compileWordToStack_cons
  · exact stackResult569_from _
  apply compileWordToStack_cons
  · exact stackResult570_from _
  apply compileWordToStack_cons
  · exact stackResult571_from _
  apply compileWordToStack_cons
  · exact stackResult572_from _
  apply compileWordToStack_cons
  · exact stackResult573_from _
  apply compileWordToStack_cons
  · exact stackResult574_from _
  apply compileWordToStack_cons
  · exact stackResult575_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 1910) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 2007)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 1910 bodies frames bitmapDelta 2007 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 496).take 16).zip
      [oracle560, oracle561, oracle562, oracle563, oracle564, oracle565, oracle566, oracle567, oracle568, oracle569, oracle570, oracle571, oracle572, oracle573, oracle574, oracle575]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle560 PrefixChecks.Shard496.entry,
    wordFunction oracle561 PrefixChecks.Shard497.entry,
    wordFunction oracle562 PrefixChecks.Shard498.entry,
    wordFunction oracle563 PrefixChecks.Shard499.entry,
    wordFunction oracle564 PrefixChecks.Shard500.entry,
    wordFunction oracle565 PrefixChecks.Shard501.entry,
    wordFunction oracle566 PrefixChecks.Shard502.entry,
    wordFunction oracle567 PrefixChecks.Shard503.entry,
    wordFunction oracle568 PrefixChecks.Shard504.entry,
    wordFunction oracle569 PrefixChecks.Shard505.entry,
    wordFunction oracle570 PrefixChecks.Shard506.entry,
    wordFunction oracle571 PrefixChecks.Shard507.entry,
    wordFunction oracle572 PrefixChecks.Shard508.entry,
    wordFunction oracle573 PrefixChecks.Shard509.entry,
    wordFunction oracle574 PrefixChecks.Shard510.entry,
    wordFunction oracle575 PrefixChecks.Shard511.entry] = words
  simp only [
    Word560.wordFunction_eq,
    Word561.wordFunction_eq,
    Word562.wordFunction_eq,
    Word563.wordFunction_eq,
    Word564.wordFunction_eq,
    Word565.wordFunction_eq,
    Word566.wordFunction_eq,
    Word567.wordFunction_eq,
    Word568.wordFunction_eq,
    Word569.wordFunction_eq,
    Word570.wordFunction_eq,
    Word571.wordFunction_eq,
    Word572.wordFunction_eq,
    Word573.wordFunction_eq,
    Word574.wordFunction_eq,
    Word575.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk31
