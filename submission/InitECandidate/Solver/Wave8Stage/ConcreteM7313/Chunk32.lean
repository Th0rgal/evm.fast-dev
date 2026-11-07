import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word576
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word577
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word578
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word579
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word580
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word581
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word582
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word583
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word584
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word585
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word586
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word587
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word588
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word589
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word590
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word591
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000
set_option cbv.maxSteps 40000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk32
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

wave8_certified_reduce stackResult576 := WordToStack.Native.compileProgNative
  riscvConfig false Word576.program PrefixChecks.Shard512.arity registers (.nil, 2007)
theorem stackResult576_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word576.program
      PrefixChecks.Shard512.arity registers (prefixList, 2007) =
    (stackResult576.1, stackResult576.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult576.2.2.1, 2017)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word576.program
    PrefixChecks.Shard512.arity registers prefixList 2007
    stackResult576.1 stackResult576.2.1 stackResult576.2.2.1 2017 stackResult576_eq
wave8_certified_reduce stackResult577 := WordToStack.Native.compileProgNative
  riscvConfig false Word577.program PrefixChecks.Shard513.arity registers (.nil, 2017)
theorem stackResult577_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word577.program
      PrefixChecks.Shard513.arity registers (prefixList, 2017) =
    (stackResult577.1, stackResult577.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult577.2.2.1, 2022)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word577.program
    PrefixChecks.Shard513.arity registers prefixList 2017
    stackResult577.1 stackResult577.2.1 stackResult577.2.2.1 2022 stackResult577_eq
wave8_certified_reduce stackResult578 := WordToStack.Native.compileProgNative
  riscvConfig false Word578.program PrefixChecks.Shard514.arity registers (.nil, 2022)
theorem stackResult578_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word578.program
      PrefixChecks.Shard514.arity registers (prefixList, 2022) =
    (stackResult578.1, stackResult578.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult578.2.2.1, 2026)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word578.program
    PrefixChecks.Shard514.arity registers prefixList 2022
    stackResult578.1 stackResult578.2.1 stackResult578.2.2.1 2026 stackResult578_eq
wave8_certified_reduce stackResult579 := WordToStack.Native.compileProgNative
  riscvConfig false Word579.program PrefixChecks.Shard515.arity registers (.nil, 2026)
theorem stackResult579_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word579.program
      PrefixChecks.Shard515.arity registers (prefixList, 2026) =
    (stackResult579.1, stackResult579.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult579.2.2.1, 2030)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word579.program
    PrefixChecks.Shard515.arity registers prefixList 2026
    stackResult579.1 stackResult579.2.1 stackResult579.2.2.1 2030 stackResult579_eq
wave8_certified_reduce stackResult580 := WordToStack.Native.compileProgNative
  riscvConfig false Word580.program PrefixChecks.Shard516.arity registers (.nil, 2030)
theorem stackResult580_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word580.program
      PrefixChecks.Shard516.arity registers (prefixList, 2030) =
    (stackResult580.1, stackResult580.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult580.2.2.1, 2034)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word580.program
    PrefixChecks.Shard516.arity registers prefixList 2030
    stackResult580.1 stackResult580.2.1 stackResult580.2.2.1 2034 stackResult580_eq
wave8_certified_reduce stackResult581 := WordToStack.Native.compileProgNative
  riscvConfig false Word581.program PrefixChecks.Shard517.arity registers (.nil, 2034)
theorem stackResult581_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word581.program
      PrefixChecks.Shard517.arity registers (prefixList, 2034) =
    (stackResult581.1, stackResult581.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult581.2.2.1, 2038)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word581.program
    PrefixChecks.Shard517.arity registers prefixList 2034
    stackResult581.1 stackResult581.2.1 stackResult581.2.2.1 2038 stackResult581_eq
wave8_certified_reduce stackResult582 := WordToStack.Native.compileProgNative
  riscvConfig false Word582.program PrefixChecks.Shard518.arity registers (.nil, 2038)
theorem stackResult582_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word582.program
      PrefixChecks.Shard518.arity registers (prefixList, 2038) =
    (stackResult582.1, stackResult582.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult582.2.2.1, 2043)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word582.program
    PrefixChecks.Shard518.arity registers prefixList 2038
    stackResult582.1 stackResult582.2.1 stackResult582.2.2.1 2043 stackResult582_eq
wave8_certified_reduce stackResult583 := WordToStack.Native.compileProgNative
  riscvConfig false Word583.program PrefixChecks.Shard519.arity registers (.nil, 2043)
theorem stackResult583_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word583.program
      PrefixChecks.Shard519.arity registers (prefixList, 2043) =
    (stackResult583.1, stackResult583.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult583.2.2.1, 2047)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word583.program
    PrefixChecks.Shard519.arity registers prefixList 2043
    stackResult583.1 stackResult583.2.1 stackResult583.2.2.1 2047 stackResult583_eq
wave8_certified_reduce stackResult584 := WordToStack.Native.compileProgNative
  riscvConfig false Word584.program PrefixChecks.Shard520.arity registers (.nil, 2047)
theorem stackResult584_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word584.program
      PrefixChecks.Shard520.arity registers (prefixList, 2047) =
    (stackResult584.1, stackResult584.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult584.2.2.1, 2059)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word584.program
    PrefixChecks.Shard520.arity registers prefixList 2047
    stackResult584.1 stackResult584.2.1 stackResult584.2.2.1 2059 stackResult584_eq
wave8_certified_reduce stackResult585 := WordToStack.Native.compileProgNative
  riscvConfig false Word585.program PrefixChecks.Shard521.arity registers (.nil, 2059)
theorem stackResult585_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word585.program
      PrefixChecks.Shard521.arity registers (prefixList, 2059) =
    (stackResult585.1, stackResult585.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult585.2.2.1, 2070)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word585.program
    PrefixChecks.Shard521.arity registers prefixList 2059
    stackResult585.1 stackResult585.2.1 stackResult585.2.2.1 2070 stackResult585_eq
wave8_certified_reduce stackResult586 := WordToStack.Native.compileProgNative
  riscvConfig false Word586.program PrefixChecks.Shard522.arity registers (.nil, 2070)
theorem stackResult586_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word586.program
      PrefixChecks.Shard522.arity registers (prefixList, 2070) =
    (stackResult586.1, stackResult586.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult586.2.2.1, 2077)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word586.program
    PrefixChecks.Shard522.arity registers prefixList 2070
    stackResult586.1 stackResult586.2.1 stackResult586.2.2.1 2077 stackResult586_eq
wave8_certified_reduce stackResult587 := WordToStack.Native.compileProgNative
  riscvConfig false Word587.program PrefixChecks.Shard523.arity registers (.nil, 2077)
theorem stackResult587_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word587.program
      PrefixChecks.Shard523.arity registers (prefixList, 2077) =
    (stackResult587.1, stackResult587.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult587.2.2.1, 2084)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word587.program
    PrefixChecks.Shard523.arity registers prefixList 2077
    stackResult587.1 stackResult587.2.1 stackResult587.2.2.1 2084 stackResult587_eq
wave8_certified_reduce stackResult588 := WordToStack.Native.compileProgNative
  riscvConfig false Word588.program PrefixChecks.Shard524.arity registers (.nil, 2084)
theorem stackResult588_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word588.program
      PrefixChecks.Shard524.arity registers (prefixList, 2084) =
    (stackResult588.1, stackResult588.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult588.2.2.1, 2101)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word588.program
    PrefixChecks.Shard524.arity registers prefixList 2084
    stackResult588.1 stackResult588.2.1 stackResult588.2.2.1 2101 stackResult588_eq
wave8_certified_reduce stackResult589 := WordToStack.Native.compileProgNative
  riscvConfig false Word589.program PrefixChecks.Shard525.arity registers (.nil, 2101)
theorem stackResult589_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word589.program
      PrefixChecks.Shard525.arity registers (prefixList, 2101) =
    (stackResult589.1, stackResult589.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult589.2.2.1, 2102)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word589.program
    PrefixChecks.Shard525.arity registers prefixList 2101
    stackResult589.1 stackResult589.2.1 stackResult589.2.2.1 2102 stackResult589_eq
wave8_certified_reduce stackResult590 := WordToStack.Native.compileProgNative
  riscvConfig false Word590.program PrefixChecks.Shard526.arity registers (.nil, 2102)
theorem stackResult590_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word590.program
      PrefixChecks.Shard526.arity registers (prefixList, 2102) =
    (stackResult590.1, stackResult590.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult590.2.2.1, 2122)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word590.program
    PrefixChecks.Shard526.arity registers prefixList 2102
    stackResult590.1 stackResult590.2.1 stackResult590.2.2.1 2122 stackResult590_eq
wave8_certified_reduce stackResult591 := WordToStack.Native.compileProgNative
  riscvConfig false Word591.program PrefixChecks.Shard527.arity registers (.nil, 2122)
theorem stackResult591_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word591.program
      PrefixChecks.Shard527.arity registers (prefixList, 2122) =
    (stackResult591.1, stackResult591.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult591.2.2.1, 2127)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word591.program
    PrefixChecks.Shard527.arity registers prefixList 2122
    stackResult591.1 stackResult591.2.1 stackResult591.2.2.1 2127 stackResult591_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard512.name, PrefixChecks.Shard512.arity, Word576.program),
  (PrefixChecks.Shard513.name, PrefixChecks.Shard513.arity, Word577.program),
  (PrefixChecks.Shard514.name, PrefixChecks.Shard514.arity, Word578.program),
  (PrefixChecks.Shard515.name, PrefixChecks.Shard515.arity, Word579.program),
  (PrefixChecks.Shard516.name, PrefixChecks.Shard516.arity, Word580.program),
  (PrefixChecks.Shard517.name, PrefixChecks.Shard517.arity, Word581.program),
  (PrefixChecks.Shard518.name, PrefixChecks.Shard518.arity, Word582.program),
  (PrefixChecks.Shard519.name, PrefixChecks.Shard519.arity, Word583.program),
  (PrefixChecks.Shard520.name, PrefixChecks.Shard520.arity, Word584.program),
  (PrefixChecks.Shard521.name, PrefixChecks.Shard521.arity, Word585.program),
  (PrefixChecks.Shard522.name, PrefixChecks.Shard522.arity, Word586.program),
  (PrefixChecks.Shard523.name, PrefixChecks.Shard523.arity, Word587.program),
  (PrefixChecks.Shard524.name, PrefixChecks.Shard524.arity, Word588.program),
  (PrefixChecks.Shard525.name, PrefixChecks.Shard525.arity, Word589.program),
  (PrefixChecks.Shard526.name, PrefixChecks.Shard526.arity, Word590.program),
  (PrefixChecks.Shard527.name, PrefixChecks.Shard527.arity, Word591.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard512.name, stackResult576.1),
  (PrefixChecks.Shard513.name, stackResult577.1),
  (PrefixChecks.Shard514.name, stackResult578.1),
  (PrefixChecks.Shard515.name, stackResult579.1),
  (PrefixChecks.Shard516.name, stackResult580.1),
  (PrefixChecks.Shard517.name, stackResult581.1),
  (PrefixChecks.Shard518.name, stackResult582.1),
  (PrefixChecks.Shard519.name, stackResult583.1),
  (PrefixChecks.Shard520.name, stackResult584.1),
  (PrefixChecks.Shard521.name, stackResult585.1),
  (PrefixChecks.Shard522.name, stackResult586.1),
  (PrefixChecks.Shard523.name, stackResult587.1),
  (PrefixChecks.Shard524.name, stackResult588.1),
  (PrefixChecks.Shard525.name, stackResult589.1),
  (PrefixChecks.Shard526.name, stackResult590.1),
  (PrefixChecks.Shard527.name, stackResult591.1)
]

noncomputable def frames : List Nat := [
  stackResult576.2.1,
  stackResult577.2.1,
  stackResult578.2.1,
  stackResult579.2.1,
  stackResult580.2.1,
  stackResult581.2.1,
  stackResult582.2.1,
  stackResult583.2.1,
  stackResult584.2.1,
  stackResult585.2.1,
  stackResult586.2.1,
  stackResult587.2.1,
  stackResult588.2.1,
  stackResult589.2.1,
  stackResult590.2.1,
  stackResult591.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult576.2.2.1) stackResult577.2.2.1) stackResult578.2.2.1) stackResult579.2.2.1) stackResult580.2.2.1) stackResult581.2.2.1) stackResult582.2.2.1) stackResult583.2.2.1) stackResult584.2.2.1) stackResult585.2.2.1) stackResult586.2.2.1) stackResult587.2.2.1) stackResult588.2.2.1) stackResult589.2.2.1) stackResult590.2.2.1) stackResult591.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 2007) = (bodies, frames, (bitmapDelta, 2127)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult576_from _
  apply compileWordToStack_cons
  · exact stackResult577_from _
  apply compileWordToStack_cons
  · exact stackResult578_from _
  apply compileWordToStack_cons
  · exact stackResult579_from _
  apply compileWordToStack_cons
  · exact stackResult580_from _
  apply compileWordToStack_cons
  · exact stackResult581_from _
  apply compileWordToStack_cons
  · exact stackResult582_from _
  apply compileWordToStack_cons
  · exact stackResult583_from _
  apply compileWordToStack_cons
  · exact stackResult584_from _
  apply compileWordToStack_cons
  · exact stackResult585_from _
  apply compileWordToStack_cons
  · exact stackResult586_from _
  apply compileWordToStack_cons
  · exact stackResult587_from _
  apply compileWordToStack_cons
  · exact stackResult588_from _
  apply compileWordToStack_cons
  · exact stackResult589_from _
  apply compileWordToStack_cons
  · exact stackResult590_from _
  apply compileWordToStack_cons
  · exact stackResult591_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 2007) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 2127)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 2007 bodies frames bitmapDelta 2127 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 512).take 16).zip
      [oracle576, oracle577, oracle578, oracle579, oracle580, oracle581, oracle582, oracle583, oracle584, oracle585, oracle586, oracle587, oracle588, oracle589, oracle590, oracle591]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle576 PrefixChecks.Shard512.entry,
    wordFunction oracle577 PrefixChecks.Shard513.entry,
    wordFunction oracle578 PrefixChecks.Shard514.entry,
    wordFunction oracle579 PrefixChecks.Shard515.entry,
    wordFunction oracle580 PrefixChecks.Shard516.entry,
    wordFunction oracle581 PrefixChecks.Shard517.entry,
    wordFunction oracle582 PrefixChecks.Shard518.entry,
    wordFunction oracle583 PrefixChecks.Shard519.entry,
    wordFunction oracle584 PrefixChecks.Shard520.entry,
    wordFunction oracle585 PrefixChecks.Shard521.entry,
    wordFunction oracle586 PrefixChecks.Shard522.entry,
    wordFunction oracle587 PrefixChecks.Shard523.entry,
    wordFunction oracle588 PrefixChecks.Shard524.entry,
    wordFunction oracle589 PrefixChecks.Shard525.entry,
    wordFunction oracle590 PrefixChecks.Shard526.entry,
    wordFunction oracle591 PrefixChecks.Shard527.entry] = words
  simp only [
    Word576.wordFunction_eq,
    Word577.wordFunction_eq,
    Word578.wordFunction_eq,
    Word579.wordFunction_eq,
    Word580.wordFunction_eq,
    Word581.wordFunction_eq,
    Word582.wordFunction_eq,
    Word583.wordFunction_eq,
    Word584.wordFunction_eq,
    Word585.wordFunction_eq,
    Word586.wordFunction_eq,
    Word587.wordFunction_eq,
    Word588.wordFunction_eq,
    Word589.wordFunction_eq,
    Word590.wordFunction_eq,
    Word591.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk32
