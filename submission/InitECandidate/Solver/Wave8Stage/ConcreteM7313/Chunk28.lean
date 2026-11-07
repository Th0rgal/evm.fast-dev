import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word512
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word513
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word514
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word515
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word516
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word517
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word518
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word519
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word520
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word521
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word522
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word523
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word524
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word525
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word526
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word527
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000
set_option cbv.maxSteps 40000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk28
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition

wave8_certified_reduce stackResult512 := WordToStack.Native.compileProgNative
  riscvConfig false Word512.program PrefixChecks.Shard448.arity registers (.nil, 1637)
theorem stackResult512_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word512.program
      PrefixChecks.Shard448.arity registers (prefixList, 1637) =
    (stackResult512.1, stackResult512.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult512.2.2.1, 1643)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word512.program
    PrefixChecks.Shard448.arity registers prefixList 1637
    stackResult512.1 stackResult512.2.1 stackResult512.2.2.1 1643 stackResult512_eq
wave8_certified_reduce stackResult513 := WordToStack.Native.compileProgNative
  riscvConfig false Word513.program PrefixChecks.Shard449.arity registers (.nil, 1643)
theorem stackResult513_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word513.program
      PrefixChecks.Shard449.arity registers (prefixList, 1643) =
    (stackResult513.1, stackResult513.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult513.2.2.1, 1648)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word513.program
    PrefixChecks.Shard449.arity registers prefixList 1643
    stackResult513.1 stackResult513.2.1 stackResult513.2.2.1 1648 stackResult513_eq
wave8_certified_reduce stackResult514 := WordToStack.Native.compileProgNative
  riscvConfig false Word514.program PrefixChecks.Shard450.arity registers (.nil, 1648)
theorem stackResult514_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word514.program
      PrefixChecks.Shard450.arity registers (prefixList, 1648) =
    (stackResult514.1, stackResult514.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult514.2.2.1, 1653)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word514.program
    PrefixChecks.Shard450.arity registers prefixList 1648
    stackResult514.1 stackResult514.2.1 stackResult514.2.2.1 1653 stackResult514_eq
wave8_certified_reduce stackResult515 := WordToStack.Native.compileProgNative
  riscvConfig false Word515.program PrefixChecks.Shard451.arity registers (.nil, 1653)
theorem stackResult515_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word515.program
      PrefixChecks.Shard451.arity registers (prefixList, 1653) =
    (stackResult515.1, stackResult515.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult515.2.2.1, 1658)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word515.program
    PrefixChecks.Shard451.arity registers prefixList 1653
    stackResult515.1 stackResult515.2.1 stackResult515.2.2.1 1658 stackResult515_eq
wave8_certified_reduce stackResult516 := WordToStack.Native.compileProgNative
  riscvConfig false Word516.program PrefixChecks.Shard452.arity registers (.nil, 1658)
theorem stackResult516_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word516.program
      PrefixChecks.Shard452.arity registers (prefixList, 1658) =
    (stackResult516.1, stackResult516.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult516.2.2.1, 1663)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word516.program
    PrefixChecks.Shard452.arity registers prefixList 1658
    stackResult516.1 stackResult516.2.1 stackResult516.2.2.1 1663 stackResult516_eq
wave8_certified_reduce stackResult517 := WordToStack.Native.compileProgNative
  riscvConfig false Word517.program PrefixChecks.Shard453.arity registers (.nil, 1663)
theorem stackResult517_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word517.program
      PrefixChecks.Shard453.arity registers (prefixList, 1663) =
    (stackResult517.1, stackResult517.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult517.2.2.1, 1667)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word517.program
    PrefixChecks.Shard453.arity registers prefixList 1663
    stackResult517.1 stackResult517.2.1 stackResult517.2.2.1 1667 stackResult517_eq
wave8_certified_reduce stackResult518 := WordToStack.Native.compileProgNative
  riscvConfig false Word518.program PrefixChecks.Shard454.arity registers (.nil, 1667)
theorem stackResult518_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word518.program
      PrefixChecks.Shard454.arity registers (prefixList, 1667) =
    (stackResult518.1, stackResult518.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult518.2.2.1, 1674)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word518.program
    PrefixChecks.Shard454.arity registers prefixList 1667
    stackResult518.1 stackResult518.2.1 stackResult518.2.2.1 1674 stackResult518_eq
wave8_certified_reduce stackResult519 := WordToStack.Native.compileProgNative
  riscvConfig false Word519.program PrefixChecks.Shard455.arity registers (.nil, 1674)
theorem stackResult519_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word519.program
      PrefixChecks.Shard455.arity registers (prefixList, 1674) =
    (stackResult519.1, stackResult519.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult519.2.2.1, 1681)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word519.program
    PrefixChecks.Shard455.arity registers prefixList 1674
    stackResult519.1 stackResult519.2.1 stackResult519.2.2.1 1681 stackResult519_eq
wave8_certified_reduce stackResult520 := WordToStack.Native.compileProgNative
  riscvConfig false Word520.program PrefixChecks.Shard456.arity registers (.nil, 1681)
theorem stackResult520_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word520.program
      PrefixChecks.Shard456.arity registers (prefixList, 1681) =
    (stackResult520.1, stackResult520.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult520.2.2.1, 1688)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word520.program
    PrefixChecks.Shard456.arity registers prefixList 1681
    stackResult520.1 stackResult520.2.1 stackResult520.2.2.1 1688 stackResult520_eq
wave8_certified_reduce stackResult521 := WordToStack.Native.compileProgNative
  riscvConfig false Word521.program PrefixChecks.Shard457.arity registers (.nil, 1688)
theorem stackResult521_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word521.program
      PrefixChecks.Shard457.arity registers (prefixList, 1688) =
    (stackResult521.1, stackResult521.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult521.2.2.1, 1695)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word521.program
    PrefixChecks.Shard457.arity registers prefixList 1688
    stackResult521.1 stackResult521.2.1 stackResult521.2.2.1 1695 stackResult521_eq
wave8_certified_reduce stackResult522 := WordToStack.Native.compileProgNative
  riscvConfig false Word522.program PrefixChecks.Shard458.arity registers (.nil, 1695)
theorem stackResult522_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word522.program
      PrefixChecks.Shard458.arity registers (prefixList, 1695) =
    (stackResult522.1, stackResult522.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult522.2.2.1, 1700)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word522.program
    PrefixChecks.Shard458.arity registers prefixList 1695
    stackResult522.1 stackResult522.2.1 stackResult522.2.2.1 1700 stackResult522_eq
wave8_certified_reduce stackResult523 := WordToStack.Native.compileProgNative
  riscvConfig false Word523.program PrefixChecks.Shard459.arity registers (.nil, 1700)
theorem stackResult523_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word523.program
      PrefixChecks.Shard459.arity registers (prefixList, 1700) =
    (stackResult523.1, stackResult523.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult523.2.2.1, 1716)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word523.program
    PrefixChecks.Shard459.arity registers prefixList 1700
    stackResult523.1 stackResult523.2.1 stackResult523.2.2.1 1716 stackResult523_eq
wave8_certified_reduce stackResult524 := WordToStack.Native.compileProgNative
  riscvConfig false Word524.program PrefixChecks.Shard460.arity registers (.nil, 1716)
theorem stackResult524_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word524.program
      PrefixChecks.Shard460.arity registers (prefixList, 1716) =
    (stackResult524.1, stackResult524.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult524.2.2.1, 1717)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word524.program
    PrefixChecks.Shard460.arity registers prefixList 1716
    stackResult524.1 stackResult524.2.1 stackResult524.2.2.1 1717 stackResult524_eq
wave8_certified_reduce stackResult525 := WordToStack.Native.compileProgNative
  riscvConfig false Word525.program PrefixChecks.Shard461.arity registers (.nil, 1717)
theorem stackResult525_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word525.program
      PrefixChecks.Shard461.arity registers (prefixList, 1717) =
    (stackResult525.1, stackResult525.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult525.2.2.1, 1720)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word525.program
    PrefixChecks.Shard461.arity registers prefixList 1717
    stackResult525.1 stackResult525.2.1 stackResult525.2.2.1 1720 stackResult525_eq
wave8_certified_reduce stackResult526 := WordToStack.Native.compileProgNative
  riscvConfig false Word526.program PrefixChecks.Shard462.arity registers (.nil, 1720)
theorem stackResult526_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word526.program
      PrefixChecks.Shard462.arity registers (prefixList, 1720) =
    (stackResult526.1, stackResult526.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult526.2.2.1, 1726)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word526.program
    PrefixChecks.Shard462.arity registers prefixList 1720
    stackResult526.1 stackResult526.2.1 stackResult526.2.2.1 1726 stackResult526_eq
wave8_certified_reduce stackResult527 := WordToStack.Native.compileProgNative
  riscvConfig false Word527.program PrefixChecks.Shard463.arity registers (.nil, 1726)
theorem stackResult527_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word527.program
      PrefixChecks.Shard463.arity registers (prefixList, 1726) =
    (stackResult527.1, stackResult527.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult527.2.2.1, 1729)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word527.program
    PrefixChecks.Shard463.arity registers prefixList 1726
    stackResult527.1 stackResult527.2.1 stackResult527.2.2.1 1729 stackResult527_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard448.name, PrefixChecks.Shard448.arity, Word512.program),
  (PrefixChecks.Shard449.name, PrefixChecks.Shard449.arity, Word513.program),
  (PrefixChecks.Shard450.name, PrefixChecks.Shard450.arity, Word514.program),
  (PrefixChecks.Shard451.name, PrefixChecks.Shard451.arity, Word515.program),
  (PrefixChecks.Shard452.name, PrefixChecks.Shard452.arity, Word516.program),
  (PrefixChecks.Shard453.name, PrefixChecks.Shard453.arity, Word517.program),
  (PrefixChecks.Shard454.name, PrefixChecks.Shard454.arity, Word518.program),
  (PrefixChecks.Shard455.name, PrefixChecks.Shard455.arity, Word519.program),
  (PrefixChecks.Shard456.name, PrefixChecks.Shard456.arity, Word520.program),
  (PrefixChecks.Shard457.name, PrefixChecks.Shard457.arity, Word521.program),
  (PrefixChecks.Shard458.name, PrefixChecks.Shard458.arity, Word522.program),
  (PrefixChecks.Shard459.name, PrefixChecks.Shard459.arity, Word523.program),
  (PrefixChecks.Shard460.name, PrefixChecks.Shard460.arity, Word524.program),
  (PrefixChecks.Shard461.name, PrefixChecks.Shard461.arity, Word525.program),
  (PrefixChecks.Shard462.name, PrefixChecks.Shard462.arity, Word526.program),
  (PrefixChecks.Shard463.name, PrefixChecks.Shard463.arity, Word527.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard448.name, stackResult512.1),
  (PrefixChecks.Shard449.name, stackResult513.1),
  (PrefixChecks.Shard450.name, stackResult514.1),
  (PrefixChecks.Shard451.name, stackResult515.1),
  (PrefixChecks.Shard452.name, stackResult516.1),
  (PrefixChecks.Shard453.name, stackResult517.1),
  (PrefixChecks.Shard454.name, stackResult518.1),
  (PrefixChecks.Shard455.name, stackResult519.1),
  (PrefixChecks.Shard456.name, stackResult520.1),
  (PrefixChecks.Shard457.name, stackResult521.1),
  (PrefixChecks.Shard458.name, stackResult522.1),
  (PrefixChecks.Shard459.name, stackResult523.1),
  (PrefixChecks.Shard460.name, stackResult524.1),
  (PrefixChecks.Shard461.name, stackResult525.1),
  (PrefixChecks.Shard462.name, stackResult526.1),
  (PrefixChecks.Shard463.name, stackResult527.1)
]

noncomputable def frames : List Nat := [
  stackResult512.2.1,
  stackResult513.2.1,
  stackResult514.2.1,
  stackResult515.2.1,
  stackResult516.2.1,
  stackResult517.2.1,
  stackResult518.2.1,
  stackResult519.2.1,
  stackResult520.2.1,
  stackResult521.2.1,
  stackResult522.2.1,
  stackResult523.2.1,
  stackResult524.2.1,
  stackResult525.2.1,
  stackResult526.2.1,
  stackResult527.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult512.2.2.1) stackResult513.2.2.1) stackResult514.2.2.1) stackResult515.2.2.1) stackResult516.2.2.1) stackResult517.2.2.1) stackResult518.2.2.1) stackResult519.2.2.1) stackResult520.2.2.1) stackResult521.2.2.1) stackResult522.2.2.1) stackResult523.2.2.1) stackResult524.2.2.1) stackResult525.2.2.1) stackResult526.2.2.1) stackResult527.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 1637) = (bodies, frames, (bitmapDelta, 1729)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult512_from _
  apply compileWordToStack_cons
  · exact stackResult513_from _
  apply compileWordToStack_cons
  · exact stackResult514_from _
  apply compileWordToStack_cons
  · exact stackResult515_from _
  apply compileWordToStack_cons
  · exact stackResult516_from _
  apply compileWordToStack_cons
  · exact stackResult517_from _
  apply compileWordToStack_cons
  · exact stackResult518_from _
  apply compileWordToStack_cons
  · exact stackResult519_from _
  apply compileWordToStack_cons
  · exact stackResult520_from _
  apply compileWordToStack_cons
  · exact stackResult521_from _
  apply compileWordToStack_cons
  · exact stackResult522_from _
  apply compileWordToStack_cons
  · exact stackResult523_from _
  apply compileWordToStack_cons
  · exact stackResult524_from _
  apply compileWordToStack_cons
  · exact stackResult525_from _
  apply compileWordToStack_cons
  · exact stackResult526_from _
  apply compileWordToStack_cons
  · exact stackResult527_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 1637) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 1729)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 1637 bodies frames bitmapDelta 1729 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 448).take 16).zip
      [oracle512, oracle513, oracle514, oracle515, oracle516, oracle517, oracle518, oracle519, oracle520, oracle521, oracle522, oracle523, oracle524, oracle525, oracle526, oracle527]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle512 PrefixChecks.Shard448.entry,
    wordFunction oracle513 PrefixChecks.Shard449.entry,
    wordFunction oracle514 PrefixChecks.Shard450.entry,
    wordFunction oracle515 PrefixChecks.Shard451.entry,
    wordFunction oracle516 PrefixChecks.Shard452.entry,
    wordFunction oracle517 PrefixChecks.Shard453.entry,
    wordFunction oracle518 PrefixChecks.Shard454.entry,
    wordFunction oracle519 PrefixChecks.Shard455.entry,
    wordFunction oracle520 PrefixChecks.Shard456.entry,
    wordFunction oracle521 PrefixChecks.Shard457.entry,
    wordFunction oracle522 PrefixChecks.Shard458.entry,
    wordFunction oracle523 PrefixChecks.Shard459.entry,
    wordFunction oracle524 PrefixChecks.Shard460.entry,
    wordFunction oracle525 PrefixChecks.Shard461.entry,
    wordFunction oracle526 PrefixChecks.Shard462.entry,
    wordFunction oracle527 PrefixChecks.Shard463.entry] = words
  simp only [
    Word512.wordFunction_eq,
    Word513.wordFunction_eq,
    Word514.wordFunction_eq,
    Word515.wordFunction_eq,
    Word516.wordFunction_eq,
    Word517.wordFunction_eq,
    Word518.wordFunction_eq,
    Word519.wordFunction_eq,
    Word520.wordFunction_eq,
    Word521.wordFunction_eq,
    Word522.wordFunction_eq,
    Word523.wordFunction_eq,
    Word524.wordFunction_eq,
    Word525.wordFunction_eq,
    Word526.wordFunction_eq,
    Word527.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk28
