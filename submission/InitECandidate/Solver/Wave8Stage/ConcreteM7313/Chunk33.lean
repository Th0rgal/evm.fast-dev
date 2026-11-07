import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word592
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word593
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word594
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word595
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word596
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word597
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word598
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word599
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word600
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word601
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word602
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word603
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word604
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word605
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word606
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word607
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000
set_option cbv.maxSteps 40000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk33
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

wave8_certified_reduce stackResult592 := WordToStack.Native.compileProgNative
  riscvConfig false Word592.program PrefixChecks.Shard528.arity registers (.nil, 2127)
theorem stackResult592_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word592.program
      PrefixChecks.Shard528.arity registers (prefixList, 2127) =
    (stackResult592.1, stackResult592.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult592.2.2.1, 2130)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word592.program
    PrefixChecks.Shard528.arity registers prefixList 2127
    stackResult592.1 stackResult592.2.1 stackResult592.2.2.1 2130 stackResult592_eq
wave8_certified_reduce stackResult593 := WordToStack.Native.compileProgNative
  riscvConfig false Word593.program PrefixChecks.Shard529.arity registers (.nil, 2130)
theorem stackResult593_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word593.program
      PrefixChecks.Shard529.arity registers (prefixList, 2130) =
    (stackResult593.1, stackResult593.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult593.2.2.1, 2157)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word593.program
    PrefixChecks.Shard529.arity registers prefixList 2130
    stackResult593.1 stackResult593.2.1 stackResult593.2.2.1 2157 stackResult593_eq
wave8_certified_reduce stackResult594 := WordToStack.Native.compileProgNative
  riscvConfig false Word594.program PrefixChecks.Shard530.arity registers (.nil, 2157)
theorem stackResult594_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word594.program
      PrefixChecks.Shard530.arity registers (prefixList, 2157) =
    (stackResult594.1, stackResult594.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult594.2.2.1, 2173)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word594.program
    PrefixChecks.Shard530.arity registers prefixList 2157
    stackResult594.1 stackResult594.2.1 stackResult594.2.2.1 2173 stackResult594_eq
wave8_certified_reduce stackResult595 := WordToStack.Native.compileProgNative
  riscvConfig false Word595.program PrefixChecks.Shard531.arity registers (.nil, 2173)
theorem stackResult595_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word595.program
      PrefixChecks.Shard531.arity registers (prefixList, 2173) =
    (stackResult595.1, stackResult595.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult595.2.2.1, 2261)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word595.program
    PrefixChecks.Shard531.arity registers prefixList 2173
    stackResult595.1 stackResult595.2.1 stackResult595.2.2.1 2261 stackResult595_eq
wave8_certified_reduce stackResult596 := WordToStack.Native.compileProgNative
  riscvConfig false Word596.program PrefixChecks.Shard532.arity registers (.nil, 2261)
theorem stackResult596_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word596.program
      PrefixChecks.Shard532.arity registers (prefixList, 2261) =
    (stackResult596.1, stackResult596.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult596.2.2.1, 2264)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word596.program
    PrefixChecks.Shard532.arity registers prefixList 2261
    stackResult596.1 stackResult596.2.1 stackResult596.2.2.1 2264 stackResult596_eq
wave8_certified_reduce stackResult597 := WordToStack.Native.compileProgNative
  riscvConfig false Word597.program PrefixChecks.Shard533.arity registers (.nil, 2264)
theorem stackResult597_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word597.program
      PrefixChecks.Shard533.arity registers (prefixList, 2264) =
    (stackResult597.1, stackResult597.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult597.2.2.1, 2266)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word597.program
    PrefixChecks.Shard533.arity registers prefixList 2264
    stackResult597.1 stackResult597.2.1 stackResult597.2.2.1 2266 stackResult597_eq
wave8_certified_reduce stackResult598 := WordToStack.Native.compileProgNative
  riscvConfig false Word598.program PrefixChecks.Shard534.arity registers (.nil, 2266)
theorem stackResult598_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word598.program
      PrefixChecks.Shard534.arity registers (prefixList, 2266) =
    (stackResult598.1, stackResult598.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult598.2.2.1, 2272)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word598.program
    PrefixChecks.Shard534.arity registers prefixList 2266
    stackResult598.1 stackResult598.2.1 stackResult598.2.2.1 2272 stackResult598_eq
wave8_certified_reduce stackResult599 := WordToStack.Native.compileProgNative
  riscvConfig false Word599.program PrefixChecks.Shard535.arity registers (.nil, 2272)
theorem stackResult599_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word599.program
      PrefixChecks.Shard535.arity registers (prefixList, 2272) =
    (stackResult599.1, stackResult599.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult599.2.2.1, 2274)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word599.program
    PrefixChecks.Shard535.arity registers prefixList 2272
    stackResult599.1 stackResult599.2.1 stackResult599.2.2.1 2274 stackResult599_eq
wave8_certified_reduce stackResult600 := WordToStack.Native.compileProgNative
  riscvConfig false Word600.program PrefixChecks.Shard536.arity registers (.nil, 2274)
theorem stackResult600_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word600.program
      PrefixChecks.Shard536.arity registers (prefixList, 2274) =
    (stackResult600.1, stackResult600.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult600.2.2.1, 2275)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word600.program
    PrefixChecks.Shard536.arity registers prefixList 2274
    stackResult600.1 stackResult600.2.1 stackResult600.2.2.1 2275 stackResult600_eq
wave8_certified_reduce stackResult601 := WordToStack.Native.compileProgNative
  riscvConfig false Word601.program PrefixChecks.Shard537.arity registers (.nil, 2275)
theorem stackResult601_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word601.program
      PrefixChecks.Shard537.arity registers (prefixList, 2275) =
    (stackResult601.1, stackResult601.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult601.2.2.1, 2302)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word601.program
    PrefixChecks.Shard537.arity registers prefixList 2275
    stackResult601.1 stackResult601.2.1 stackResult601.2.2.1 2302 stackResult601_eq
wave8_certified_reduce stackResult602 := WordToStack.Native.compileProgNative
  riscvConfig false Word602.program PrefixChecks.Shard538.arity registers (.nil, 2302)
theorem stackResult602_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word602.program
      PrefixChecks.Shard538.arity registers (prefixList, 2302) =
    (stackResult602.1, stackResult602.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult602.2.2.1, 2307)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word602.program
    PrefixChecks.Shard538.arity registers prefixList 2302
    stackResult602.1 stackResult602.2.1 stackResult602.2.2.1 2307 stackResult602_eq
wave8_certified_reduce stackResult603 := WordToStack.Native.compileProgNative
  riscvConfig false Word603.program PrefixChecks.Shard539.arity registers (.nil, 2307)
theorem stackResult603_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word603.program
      PrefixChecks.Shard539.arity registers (prefixList, 2307) =
    (stackResult603.1, stackResult603.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult603.2.2.1, 2314)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word603.program
    PrefixChecks.Shard539.arity registers prefixList 2307
    stackResult603.1 stackResult603.2.1 stackResult603.2.2.1 2314 stackResult603_eq
wave8_certified_reduce stackResult604 := WordToStack.Native.compileProgNative
  riscvConfig false Word604.program PrefixChecks.Shard540.arity registers (.nil, 2314)
theorem stackResult604_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word604.program
      PrefixChecks.Shard540.arity registers (prefixList, 2314) =
    (stackResult604.1, stackResult604.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult604.2.2.1, 2314)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word604.program
    PrefixChecks.Shard540.arity registers prefixList 2314
    stackResult604.1 stackResult604.2.1 stackResult604.2.2.1 2314 stackResult604_eq
wave8_certified_reduce stackResult605 := WordToStack.Native.compileProgNative
  riscvConfig false Word605.program PrefixChecks.Shard541.arity registers (.nil, 2314)
theorem stackResult605_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word605.program
      PrefixChecks.Shard541.arity registers (prefixList, 2314) =
    (stackResult605.1, stackResult605.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult605.2.2.1, 2317)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word605.program
    PrefixChecks.Shard541.arity registers prefixList 2314
    stackResult605.1 stackResult605.2.1 stackResult605.2.2.1 2317 stackResult605_eq
wave8_certified_reduce stackResult606 := WordToStack.Native.compileProgNative
  riscvConfig false Word606.program PrefixChecks.Shard542.arity registers (.nil, 2317)
theorem stackResult606_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word606.program
      PrefixChecks.Shard542.arity registers (prefixList, 2317) =
    (stackResult606.1, stackResult606.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult606.2.2.1, 2328)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word606.program
    PrefixChecks.Shard542.arity registers prefixList 2317
    stackResult606.1 stackResult606.2.1 stackResult606.2.2.1 2328 stackResult606_eq
wave8_certified_reduce stackResult607 := WordToStack.Native.compileProgNative
  riscvConfig false Word607.program PrefixChecks.Shard543.arity registers (.nil, 2328)
theorem stackResult607_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word607.program
      PrefixChecks.Shard543.arity registers (prefixList, 2328) =
    (stackResult607.1, stackResult607.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult607.2.2.1, 2334)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word607.program
    PrefixChecks.Shard543.arity registers prefixList 2328
    stackResult607.1 stackResult607.2.1 stackResult607.2.2.1 2334 stackResult607_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard528.name, PrefixChecks.Shard528.arity, Word592.program),
  (PrefixChecks.Shard529.name, PrefixChecks.Shard529.arity, Word593.program),
  (PrefixChecks.Shard530.name, PrefixChecks.Shard530.arity, Word594.program),
  (PrefixChecks.Shard531.name, PrefixChecks.Shard531.arity, Word595.program),
  (PrefixChecks.Shard532.name, PrefixChecks.Shard532.arity, Word596.program),
  (PrefixChecks.Shard533.name, PrefixChecks.Shard533.arity, Word597.program),
  (PrefixChecks.Shard534.name, PrefixChecks.Shard534.arity, Word598.program),
  (PrefixChecks.Shard535.name, PrefixChecks.Shard535.arity, Word599.program),
  (PrefixChecks.Shard536.name, PrefixChecks.Shard536.arity, Word600.program),
  (PrefixChecks.Shard537.name, PrefixChecks.Shard537.arity, Word601.program),
  (PrefixChecks.Shard538.name, PrefixChecks.Shard538.arity, Word602.program),
  (PrefixChecks.Shard539.name, PrefixChecks.Shard539.arity, Word603.program),
  (PrefixChecks.Shard540.name, PrefixChecks.Shard540.arity, Word604.program),
  (PrefixChecks.Shard541.name, PrefixChecks.Shard541.arity, Word605.program),
  (PrefixChecks.Shard542.name, PrefixChecks.Shard542.arity, Word606.program),
  (PrefixChecks.Shard543.name, PrefixChecks.Shard543.arity, Word607.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard528.name, stackResult592.1),
  (PrefixChecks.Shard529.name, stackResult593.1),
  (PrefixChecks.Shard530.name, stackResult594.1),
  (PrefixChecks.Shard531.name, stackResult595.1),
  (PrefixChecks.Shard532.name, stackResult596.1),
  (PrefixChecks.Shard533.name, stackResult597.1),
  (PrefixChecks.Shard534.name, stackResult598.1),
  (PrefixChecks.Shard535.name, stackResult599.1),
  (PrefixChecks.Shard536.name, stackResult600.1),
  (PrefixChecks.Shard537.name, stackResult601.1),
  (PrefixChecks.Shard538.name, stackResult602.1),
  (PrefixChecks.Shard539.name, stackResult603.1),
  (PrefixChecks.Shard540.name, stackResult604.1),
  (PrefixChecks.Shard541.name, stackResult605.1),
  (PrefixChecks.Shard542.name, stackResult606.1),
  (PrefixChecks.Shard543.name, stackResult607.1)
]

noncomputable def frames : List Nat := [
  stackResult592.2.1,
  stackResult593.2.1,
  stackResult594.2.1,
  stackResult595.2.1,
  stackResult596.2.1,
  stackResult597.2.1,
  stackResult598.2.1,
  stackResult599.2.1,
  stackResult600.2.1,
  stackResult601.2.1,
  stackResult602.2.1,
  stackResult603.2.1,
  stackResult604.2.1,
  stackResult605.2.1,
  stackResult606.2.1,
  stackResult607.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult592.2.2.1) stackResult593.2.2.1) stackResult594.2.2.1) stackResult595.2.2.1) stackResult596.2.2.1) stackResult597.2.2.1) stackResult598.2.2.1) stackResult599.2.2.1) stackResult600.2.2.1) stackResult601.2.2.1) stackResult602.2.2.1) stackResult603.2.2.1) stackResult604.2.2.1) stackResult605.2.2.1) stackResult606.2.2.1) stackResult607.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 2127) = (bodies, frames, (bitmapDelta, 2334)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult592_from _
  apply compileWordToStack_cons
  · exact stackResult593_from _
  apply compileWordToStack_cons
  · exact stackResult594_from _
  apply compileWordToStack_cons
  · exact stackResult595_from _
  apply compileWordToStack_cons
  · exact stackResult596_from _
  apply compileWordToStack_cons
  · exact stackResult597_from _
  apply compileWordToStack_cons
  · exact stackResult598_from _
  apply compileWordToStack_cons
  · exact stackResult599_from _
  apply compileWordToStack_cons
  · exact stackResult600_from _
  apply compileWordToStack_cons
  · exact stackResult601_from _
  apply compileWordToStack_cons
  · exact stackResult602_from _
  apply compileWordToStack_cons
  · exact stackResult603_from _
  apply compileWordToStack_cons
  · exact stackResult604_from _
  apply compileWordToStack_cons
  · exact stackResult605_from _
  apply compileWordToStack_cons
  · exact stackResult606_from _
  apply compileWordToStack_cons
  · exact stackResult607_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 2127) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 2334)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 2127 bodies frames bitmapDelta 2334 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 528).take 16).zip
      [oracle592, oracle593, oracle594, oracle595, oracle596, oracle597, oracle598, oracle599, oracle600, oracle601, oracle602, oracle603, oracle604, oracle605, oracle606, oracle607]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle592 PrefixChecks.Shard528.entry,
    wordFunction oracle593 PrefixChecks.Shard529.entry,
    wordFunction oracle594 PrefixChecks.Shard530.entry,
    wordFunction oracle595 PrefixChecks.Shard531.entry,
    wordFunction oracle596 PrefixChecks.Shard532.entry,
    wordFunction oracle597 PrefixChecks.Shard533.entry,
    wordFunction oracle598 PrefixChecks.Shard534.entry,
    wordFunction oracle599 PrefixChecks.Shard535.entry,
    wordFunction oracle600 PrefixChecks.Shard536.entry,
    wordFunction oracle601 PrefixChecks.Shard537.entry,
    wordFunction oracle602 PrefixChecks.Shard538.entry,
    wordFunction oracle603 PrefixChecks.Shard539.entry,
    wordFunction oracle604 PrefixChecks.Shard540.entry,
    wordFunction oracle605 PrefixChecks.Shard541.entry,
    wordFunction oracle606 PrefixChecks.Shard542.entry,
    wordFunction oracle607 PrefixChecks.Shard543.entry] = words
  simp only [
    Word592.wordFunction_eq,
    Word593.wordFunction_eq,
    Word594.wordFunction_eq,
    Word595.wordFunction_eq,
    Word596.wordFunction_eq,
    Word597.wordFunction_eq,
    Word598.wordFunction_eq,
    Word599.wordFunction_eq,
    Word600.wordFunction_eq,
    Word601.wordFunction_eq,
    Word602.wordFunction_eq,
    Word603.wordFunction_eq,
    Word604.wordFunction_eq,
    Word605.wordFunction_eq,
    Word606.wordFunction_eq,
    Word607.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk33
