import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word272
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word273
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word274
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word275
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word276
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word277
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word278
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word279
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word280
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word281
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word282
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word283
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word284
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word285
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word286
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word287
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk13
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult272 := WordToStack.Native.compileProgNative
  riscvConfig false Word272.program PrefixChecks.Shard208.arity registers (.nil, 658)
theorem stackResult272_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word272.program
      PrefixChecks.Shard208.arity registers (prefixList, 658) =
    (stackResult272.1, stackResult272.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult272.2.2.1, 659)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word272.program
    PrefixChecks.Shard208.arity registers prefixList 658
    stackResult272.1 stackResult272.2.1 stackResult272.2.2.1 659 stackResult272_eq
wave8_kernel_reduce stackResult273 := WordToStack.Native.compileProgNative
  riscvConfig false Word273.program PrefixChecks.Shard209.arity registers (.nil, 659)
theorem stackResult273_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word273.program
      PrefixChecks.Shard209.arity registers (prefixList, 659) =
    (stackResult273.1, stackResult273.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult273.2.2.1, 660)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word273.program
    PrefixChecks.Shard209.arity registers prefixList 659
    stackResult273.1 stackResult273.2.1 stackResult273.2.2.1 660 stackResult273_eq
wave8_kernel_reduce stackResult274 := WordToStack.Native.compileProgNative
  riscvConfig false Word274.program PrefixChecks.Shard210.arity registers (.nil, 660)
theorem stackResult274_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word274.program
      PrefixChecks.Shard210.arity registers (prefixList, 660) =
    (stackResult274.1, stackResult274.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult274.2.2.1, 690)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word274.program
    PrefixChecks.Shard210.arity registers prefixList 660
    stackResult274.1 stackResult274.2.1 stackResult274.2.2.1 690 stackResult274_eq
wave8_kernel_reduce stackResult275 := WordToStack.Native.compileProgNative
  riscvConfig false Word275.program PrefixChecks.Shard211.arity registers (.nil, 690)
theorem stackResult275_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word275.program
      PrefixChecks.Shard211.arity registers (prefixList, 690) =
    (stackResult275.1, stackResult275.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult275.2.2.1, 695)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word275.program
    PrefixChecks.Shard211.arity registers prefixList 690
    stackResult275.1 stackResult275.2.1 stackResult275.2.2.1 695 stackResult275_eq
wave8_kernel_reduce stackResult276 := WordToStack.Native.compileProgNative
  riscvConfig false Word276.program PrefixChecks.Shard212.arity registers (.nil, 695)
theorem stackResult276_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word276.program
      PrefixChecks.Shard212.arity registers (prefixList, 695) =
    (stackResult276.1, stackResult276.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult276.2.2.1, 721)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word276.program
    PrefixChecks.Shard212.arity registers prefixList 695
    stackResult276.1 stackResult276.2.1 stackResult276.2.2.1 721 stackResult276_eq
wave8_kernel_reduce stackResult277 := WordToStack.Native.compileProgNative
  riscvConfig false Word277.program PrefixChecks.Shard213.arity registers (.nil, 721)
theorem stackResult277_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word277.program
      PrefixChecks.Shard213.arity registers (prefixList, 721) =
    (stackResult277.1, stackResult277.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult277.2.2.1, 725)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word277.program
    PrefixChecks.Shard213.arity registers prefixList 721
    stackResult277.1 stackResult277.2.1 stackResult277.2.2.1 725 stackResult277_eq
wave8_kernel_reduce stackResult278 := WordToStack.Native.compileProgNative
  riscvConfig false Word278.program PrefixChecks.Shard214.arity registers (.nil, 725)
theorem stackResult278_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word278.program
      PrefixChecks.Shard214.arity registers (prefixList, 725) =
    (stackResult278.1, stackResult278.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult278.2.2.1, 730)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word278.program
    PrefixChecks.Shard214.arity registers prefixList 725
    stackResult278.1 stackResult278.2.1 stackResult278.2.2.1 730 stackResult278_eq
wave8_kernel_reduce stackResult279 := WordToStack.Native.compileProgNative
  riscvConfig false Word279.program PrefixChecks.Shard215.arity registers (.nil, 730)
theorem stackResult279_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word279.program
      PrefixChecks.Shard215.arity registers (prefixList, 730) =
    (stackResult279.1, stackResult279.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult279.2.2.1, 743)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word279.program
    PrefixChecks.Shard215.arity registers prefixList 730
    stackResult279.1 stackResult279.2.1 stackResult279.2.2.1 743 stackResult279_eq
wave8_kernel_reduce stackResult280 := WordToStack.Native.compileProgNative
  riscvConfig false Word280.program PrefixChecks.Shard216.arity registers (.nil, 743)
theorem stackResult280_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word280.program
      PrefixChecks.Shard216.arity registers (prefixList, 743) =
    (stackResult280.1, stackResult280.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult280.2.2.1, 744)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word280.program
    PrefixChecks.Shard216.arity registers prefixList 743
    stackResult280.1 stackResult280.2.1 stackResult280.2.2.1 744 stackResult280_eq
wave8_kernel_reduce stackResult281 := WordToStack.Native.compileProgNative
  riscvConfig false Word281.program PrefixChecks.Shard217.arity registers (.nil, 744)
theorem stackResult281_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word281.program
      PrefixChecks.Shard217.arity registers (prefixList, 744) =
    (stackResult281.1, stackResult281.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult281.2.2.1, 751)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word281.program
    PrefixChecks.Shard217.arity registers prefixList 744
    stackResult281.1 stackResult281.2.1 stackResult281.2.2.1 751 stackResult281_eq
wave8_kernel_reduce stackResult282 := WordToStack.Native.compileProgNative
  riscvConfig false Word282.program PrefixChecks.Shard218.arity registers (.nil, 751)
theorem stackResult282_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word282.program
      PrefixChecks.Shard218.arity registers (prefixList, 751) =
    (stackResult282.1, stackResult282.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult282.2.2.1, 752)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word282.program
    PrefixChecks.Shard218.arity registers prefixList 751
    stackResult282.1 stackResult282.2.1 stackResult282.2.2.1 752 stackResult282_eq
wave8_kernel_reduce stackResult283 := WordToStack.Native.compileProgNative
  riscvConfig false Word283.program PrefixChecks.Shard219.arity registers (.nil, 752)
theorem stackResult283_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word283.program
      PrefixChecks.Shard219.arity registers (prefixList, 752) =
    (stackResult283.1, stackResult283.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult283.2.2.1, 767)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word283.program
    PrefixChecks.Shard219.arity registers prefixList 752
    stackResult283.1 stackResult283.2.1 stackResult283.2.2.1 767 stackResult283_eq
wave8_kernel_reduce stackResult284 := WordToStack.Native.compileProgNative
  riscvConfig false Word284.program PrefixChecks.Shard220.arity registers (.nil, 767)
theorem stackResult284_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word284.program
      PrefixChecks.Shard220.arity registers (prefixList, 767) =
    (stackResult284.1, stackResult284.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult284.2.2.1, 769)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word284.program
    PrefixChecks.Shard220.arity registers prefixList 767
    stackResult284.1 stackResult284.2.1 stackResult284.2.2.1 769 stackResult284_eq
wave8_kernel_reduce stackResult285 := WordToStack.Native.compileProgNative
  riscvConfig false Word285.program PrefixChecks.Shard221.arity registers (.nil, 769)
theorem stackResult285_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word285.program
      PrefixChecks.Shard221.arity registers (prefixList, 769) =
    (stackResult285.1, stackResult285.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult285.2.2.1, 782)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word285.program
    PrefixChecks.Shard221.arity registers prefixList 769
    stackResult285.1 stackResult285.2.1 stackResult285.2.2.1 782 stackResult285_eq
wave8_kernel_reduce stackResult286 := WordToStack.Native.compileProgNative
  riscvConfig false Word286.program PrefixChecks.Shard222.arity registers (.nil, 782)
theorem stackResult286_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word286.program
      PrefixChecks.Shard222.arity registers (prefixList, 782) =
    (stackResult286.1, stackResult286.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult286.2.2.1, 782)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word286.program
    PrefixChecks.Shard222.arity registers prefixList 782
    stackResult286.1 stackResult286.2.1 stackResult286.2.2.1 782 stackResult286_eq
wave8_kernel_reduce stackResult287 := WordToStack.Native.compileProgNative
  riscvConfig false Word287.program PrefixChecks.Shard223.arity registers (.nil, 782)
theorem stackResult287_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word287.program
      PrefixChecks.Shard223.arity registers (prefixList, 782) =
    (stackResult287.1, stackResult287.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult287.2.2.1, 789)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word287.program
    PrefixChecks.Shard223.arity registers prefixList 782
    stackResult287.1 stackResult287.2.1 stackResult287.2.2.1 789 stackResult287_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard208.name, PrefixChecks.Shard208.arity, Word272.program),
  (PrefixChecks.Shard209.name, PrefixChecks.Shard209.arity, Word273.program),
  (PrefixChecks.Shard210.name, PrefixChecks.Shard210.arity, Word274.program),
  (PrefixChecks.Shard211.name, PrefixChecks.Shard211.arity, Word275.program),
  (PrefixChecks.Shard212.name, PrefixChecks.Shard212.arity, Word276.program),
  (PrefixChecks.Shard213.name, PrefixChecks.Shard213.arity, Word277.program),
  (PrefixChecks.Shard214.name, PrefixChecks.Shard214.arity, Word278.program),
  (PrefixChecks.Shard215.name, PrefixChecks.Shard215.arity, Word279.program),
  (PrefixChecks.Shard216.name, PrefixChecks.Shard216.arity, Word280.program),
  (PrefixChecks.Shard217.name, PrefixChecks.Shard217.arity, Word281.program),
  (PrefixChecks.Shard218.name, PrefixChecks.Shard218.arity, Word282.program),
  (PrefixChecks.Shard219.name, PrefixChecks.Shard219.arity, Word283.program),
  (PrefixChecks.Shard220.name, PrefixChecks.Shard220.arity, Word284.program),
  (PrefixChecks.Shard221.name, PrefixChecks.Shard221.arity, Word285.program),
  (PrefixChecks.Shard222.name, PrefixChecks.Shard222.arity, Word286.program),
  (PrefixChecks.Shard223.name, PrefixChecks.Shard223.arity, Word287.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard208.name, stackResult272.1),
  (PrefixChecks.Shard209.name, stackResult273.1),
  (PrefixChecks.Shard210.name, stackResult274.1),
  (PrefixChecks.Shard211.name, stackResult275.1),
  (PrefixChecks.Shard212.name, stackResult276.1),
  (PrefixChecks.Shard213.name, stackResult277.1),
  (PrefixChecks.Shard214.name, stackResult278.1),
  (PrefixChecks.Shard215.name, stackResult279.1),
  (PrefixChecks.Shard216.name, stackResult280.1),
  (PrefixChecks.Shard217.name, stackResult281.1),
  (PrefixChecks.Shard218.name, stackResult282.1),
  (PrefixChecks.Shard219.name, stackResult283.1),
  (PrefixChecks.Shard220.name, stackResult284.1),
  (PrefixChecks.Shard221.name, stackResult285.1),
  (PrefixChecks.Shard222.name, stackResult286.1),
  (PrefixChecks.Shard223.name, stackResult287.1)
]

noncomputable def frames : List Nat := [
  stackResult272.2.1,
  stackResult273.2.1,
  stackResult274.2.1,
  stackResult275.2.1,
  stackResult276.2.1,
  stackResult277.2.1,
  stackResult278.2.1,
  stackResult279.2.1,
  stackResult280.2.1,
  stackResult281.2.1,
  stackResult282.2.1,
  stackResult283.2.1,
  stackResult284.2.1,
  stackResult285.2.1,
  stackResult286.2.1,
  stackResult287.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult272.2.2.1) stackResult273.2.2.1) stackResult274.2.2.1) stackResult275.2.2.1) stackResult276.2.2.1) stackResult277.2.2.1) stackResult278.2.2.1) stackResult279.2.2.1) stackResult280.2.2.1) stackResult281.2.2.1) stackResult282.2.2.1) stackResult283.2.2.1) stackResult284.2.2.1) stackResult285.2.2.1) stackResult286.2.2.1) stackResult287.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 658) = (bodies, frames, (bitmapDelta, 789)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult272_from _
  apply compileWordToStack_cons
  · exact stackResult273_from _
  apply compileWordToStack_cons
  · exact stackResult274_from _
  apply compileWordToStack_cons
  · exact stackResult275_from _
  apply compileWordToStack_cons
  · exact stackResult276_from _
  apply compileWordToStack_cons
  · exact stackResult277_from _
  apply compileWordToStack_cons
  · exact stackResult278_from _
  apply compileWordToStack_cons
  · exact stackResult279_from _
  apply compileWordToStack_cons
  · exact stackResult280_from _
  apply compileWordToStack_cons
  · exact stackResult281_from _
  apply compileWordToStack_cons
  · exact stackResult282_from _
  apply compileWordToStack_cons
  · exact stackResult283_from _
  apply compileWordToStack_cons
  · exact stackResult284_from _
  apply compileWordToStack_cons
  · exact stackResult285_from _
  apply compileWordToStack_cons
  · exact stackResult286_from _
  apply compileWordToStack_cons
  · exact stackResult287_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 658) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 789)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 658 bodies frames bitmapDelta 789 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 208).take 16).zip
      [oracle272, oracle273, oracle274, oracle275, oracle276, oracle277, oracle278, oracle279, oracle280, oracle281, oracle282, oracle283, oracle284, oracle285, oracle286, oracle287]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle272 PrefixChecks.Shard208.entry,
    wordFunction oracle273 PrefixChecks.Shard209.entry,
    wordFunction oracle274 PrefixChecks.Shard210.entry,
    wordFunction oracle275 PrefixChecks.Shard211.entry,
    wordFunction oracle276 PrefixChecks.Shard212.entry,
    wordFunction oracle277 PrefixChecks.Shard213.entry,
    wordFunction oracle278 PrefixChecks.Shard214.entry,
    wordFunction oracle279 PrefixChecks.Shard215.entry,
    wordFunction oracle280 PrefixChecks.Shard216.entry,
    wordFunction oracle281 PrefixChecks.Shard217.entry,
    wordFunction oracle282 PrefixChecks.Shard218.entry,
    wordFunction oracle283 PrefixChecks.Shard219.entry,
    wordFunction oracle284 PrefixChecks.Shard220.entry,
    wordFunction oracle285 PrefixChecks.Shard221.entry,
    wordFunction oracle286 PrefixChecks.Shard222.entry,
    wordFunction oracle287 PrefixChecks.Shard223.entry] = words
  simp only [
    Word272.wordFunction_eq,
    Word273.wordFunction_eq,
    Word274.wordFunction_eq,
    Word275.wordFunction_eq,
    Word276.wordFunction_eq,
    Word277.wordFunction_eq,
    Word278.wordFunction_eq,
    Word279.wordFunction_eq,
    Word280.wordFunction_eq,
    Word281.wordFunction_eq,
    Word282.wordFunction_eq,
    Word283.wordFunction_eq,
    Word284.wordFunction_eq,
    Word285.wordFunction_eq,
    Word286.wordFunction_eq,
    Word287.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk13
