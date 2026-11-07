import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word800
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word801
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word802
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word803
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word804
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word805
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word806
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word807
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word808
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word809
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word810
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word811
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word812
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word813
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word814
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word815
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk46
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult800 := WordToStack.Native.compileProgNative
  riscvConfig false Word800.program PrefixChecks.Shard736.arity registers (.nil, 3840)
theorem stackResult800_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word800.program
      PrefixChecks.Shard736.arity registers (prefixList, 3840) =
    (stackResult800.1, stackResult800.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult800.2.2.1, 3857)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word800.program
    PrefixChecks.Shard736.arity registers prefixList 3840
    stackResult800.1 stackResult800.2.1 stackResult800.2.2.1 3857 stackResult800_eq
wave8_kernel_reduce stackResult801 := WordToStack.Native.compileProgNative
  riscvConfig false Word801.program PrefixChecks.Shard737.arity registers (.nil, 3857)
theorem stackResult801_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word801.program
      PrefixChecks.Shard737.arity registers (prefixList, 3857) =
    (stackResult801.1, stackResult801.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult801.2.2.1, 3900)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word801.program
    PrefixChecks.Shard737.arity registers prefixList 3857
    stackResult801.1 stackResult801.2.1 stackResult801.2.2.1 3900 stackResult801_eq
wave8_kernel_reduce stackResult802 := WordToStack.Native.compileProgNative
  riscvConfig false Word802.program PrefixChecks.Shard738.arity registers (.nil, 3900)
theorem stackResult802_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word802.program
      PrefixChecks.Shard738.arity registers (prefixList, 3900) =
    (stackResult802.1, stackResult802.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult802.2.2.1, 3909)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word802.program
    PrefixChecks.Shard738.arity registers prefixList 3900
    stackResult802.1 stackResult802.2.1 stackResult802.2.2.1 3909 stackResult802_eq
wave8_kernel_reduce stackResult803 := WordToStack.Native.compileProgNative
  riscvConfig false Word803.program PrefixChecks.Shard739.arity registers (.nil, 3909)
theorem stackResult803_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word803.program
      PrefixChecks.Shard739.arity registers (prefixList, 3909) =
    (stackResult803.1, stackResult803.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult803.2.2.1, 3926)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word803.program
    PrefixChecks.Shard739.arity registers prefixList 3909
    stackResult803.1 stackResult803.2.1 stackResult803.2.2.1 3926 stackResult803_eq
wave8_kernel_reduce stackResult804 := WordToStack.Native.compileProgNative
  riscvConfig false Word804.program PrefixChecks.Shard740.arity registers (.nil, 3926)
theorem stackResult804_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word804.program
      PrefixChecks.Shard740.arity registers (prefixList, 3926) =
    (stackResult804.1, stackResult804.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult804.2.2.1, 3932)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word804.program
    PrefixChecks.Shard740.arity registers prefixList 3926
    stackResult804.1 stackResult804.2.1 stackResult804.2.2.1 3932 stackResult804_eq
wave8_kernel_reduce stackResult805 := WordToStack.Native.compileProgNative
  riscvConfig false Word805.program PrefixChecks.Shard741.arity registers (.nil, 3932)
theorem stackResult805_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word805.program
      PrefixChecks.Shard741.arity registers (prefixList, 3932) =
    (stackResult805.1, stackResult805.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult805.2.2.1, 3949)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word805.program
    PrefixChecks.Shard741.arity registers prefixList 3932
    stackResult805.1 stackResult805.2.1 stackResult805.2.2.1 3949 stackResult805_eq
wave8_kernel_reduce stackResult806 := WordToStack.Native.compileProgNative
  riscvConfig false Word806.program PrefixChecks.Shard742.arity registers (.nil, 3949)
theorem stackResult806_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word806.program
      PrefixChecks.Shard742.arity registers (prefixList, 3949) =
    (stackResult806.1, stackResult806.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult806.2.2.1, 3953)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word806.program
    PrefixChecks.Shard742.arity registers prefixList 3949
    stackResult806.1 stackResult806.2.1 stackResult806.2.2.1 3953 stackResult806_eq
wave8_kernel_reduce stackResult807 := WordToStack.Native.compileProgNative
  riscvConfig false Word807.program PrefixChecks.Shard743.arity registers (.nil, 3953)
theorem stackResult807_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word807.program
      PrefixChecks.Shard743.arity registers (prefixList, 3953) =
    (stackResult807.1, stackResult807.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult807.2.2.1, 3956)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word807.program
    PrefixChecks.Shard743.arity registers prefixList 3953
    stackResult807.1 stackResult807.2.1 stackResult807.2.2.1 3956 stackResult807_eq
wave8_kernel_reduce stackResult808 := WordToStack.Native.compileProgNative
  riscvConfig false Word808.program PrefixChecks.Shard744.arity registers (.nil, 3956)
theorem stackResult808_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word808.program
      PrefixChecks.Shard744.arity registers (prefixList, 3956) =
    (stackResult808.1, stackResult808.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult808.2.2.1, 3985)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word808.program
    PrefixChecks.Shard744.arity registers prefixList 3956
    stackResult808.1 stackResult808.2.1 stackResult808.2.2.1 3985 stackResult808_eq
wave8_kernel_reduce stackResult809 := WordToStack.Native.compileProgNative
  riscvConfig false Word809.program PrefixChecks.Shard745.arity registers (.nil, 3985)
theorem stackResult809_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word809.program
      PrefixChecks.Shard745.arity registers (prefixList, 3985) =
    (stackResult809.1, stackResult809.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult809.2.2.1, 3986)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word809.program
    PrefixChecks.Shard745.arity registers prefixList 3985
    stackResult809.1 stackResult809.2.1 stackResult809.2.2.1 3986 stackResult809_eq
wave8_kernel_reduce stackResult810 := WordToStack.Native.compileProgNative
  riscvConfig false Word810.program PrefixChecks.Shard746.arity registers (.nil, 3986)
theorem stackResult810_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word810.program
      PrefixChecks.Shard746.arity registers (prefixList, 3986) =
    (stackResult810.1, stackResult810.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult810.2.2.1, 3995)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word810.program
    PrefixChecks.Shard746.arity registers prefixList 3986
    stackResult810.1 stackResult810.2.1 stackResult810.2.2.1 3995 stackResult810_eq
wave8_kernel_reduce stackResult811 := WordToStack.Native.compileProgNative
  riscvConfig false Word811.program PrefixChecks.Shard747.arity registers (.nil, 3995)
theorem stackResult811_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word811.program
      PrefixChecks.Shard747.arity registers (prefixList, 3995) =
    (stackResult811.1, stackResult811.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult811.2.2.1, 4009)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word811.program
    PrefixChecks.Shard747.arity registers prefixList 3995
    stackResult811.1 stackResult811.2.1 stackResult811.2.2.1 4009 stackResult811_eq
wave8_kernel_reduce stackResult812 := WordToStack.Native.compileProgNative
  riscvConfig false Word812.program PrefixChecks.Shard748.arity registers (.nil, 4009)
theorem stackResult812_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word812.program
      PrefixChecks.Shard748.arity registers (prefixList, 4009) =
    (stackResult812.1, stackResult812.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult812.2.2.1, 4018)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word812.program
    PrefixChecks.Shard748.arity registers prefixList 4009
    stackResult812.1 stackResult812.2.1 stackResult812.2.2.1 4018 stackResult812_eq
wave8_kernel_reduce stackResult813 := WordToStack.Native.compileProgNative
  riscvConfig false Word813.program PrefixChecks.Shard749.arity registers (.nil, 4018)
theorem stackResult813_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word813.program
      PrefixChecks.Shard749.arity registers (prefixList, 4018) =
    (stackResult813.1, stackResult813.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult813.2.2.1, 4032)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word813.program
    PrefixChecks.Shard749.arity registers prefixList 4018
    stackResult813.1 stackResult813.2.1 stackResult813.2.2.1 4032 stackResult813_eq
wave8_kernel_reduce stackResult814 := WordToStack.Native.compileProgNative
  riscvConfig false Word814.program PrefixChecks.Shard750.arity registers (.nil, 4032)
theorem stackResult814_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word814.program
      PrefixChecks.Shard750.arity registers (prefixList, 4032) =
    (stackResult814.1, stackResult814.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult814.2.2.1, 4050)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word814.program
    PrefixChecks.Shard750.arity registers prefixList 4032
    stackResult814.1 stackResult814.2.1 stackResult814.2.2.1 4050 stackResult814_eq
wave8_kernel_reduce stackResult815 := WordToStack.Native.compileProgNative
  riscvConfig false Word815.program PrefixChecks.Shard751.arity registers (.nil, 4050)
theorem stackResult815_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word815.program
      PrefixChecks.Shard751.arity registers (prefixList, 4050) =
    (stackResult815.1, stackResult815.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult815.2.2.1, 4058)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word815.program
    PrefixChecks.Shard751.arity registers prefixList 4050
    stackResult815.1 stackResult815.2.1 stackResult815.2.2.1 4058 stackResult815_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard736.name, PrefixChecks.Shard736.arity, Word800.program),
  (PrefixChecks.Shard737.name, PrefixChecks.Shard737.arity, Word801.program),
  (PrefixChecks.Shard738.name, PrefixChecks.Shard738.arity, Word802.program),
  (PrefixChecks.Shard739.name, PrefixChecks.Shard739.arity, Word803.program),
  (PrefixChecks.Shard740.name, PrefixChecks.Shard740.arity, Word804.program),
  (PrefixChecks.Shard741.name, PrefixChecks.Shard741.arity, Word805.program),
  (PrefixChecks.Shard742.name, PrefixChecks.Shard742.arity, Word806.program),
  (PrefixChecks.Shard743.name, PrefixChecks.Shard743.arity, Word807.program),
  (PrefixChecks.Shard744.name, PrefixChecks.Shard744.arity, Word808.program),
  (PrefixChecks.Shard745.name, PrefixChecks.Shard745.arity, Word809.program),
  (PrefixChecks.Shard746.name, PrefixChecks.Shard746.arity, Word810.program),
  (PrefixChecks.Shard747.name, PrefixChecks.Shard747.arity, Word811.program),
  (PrefixChecks.Shard748.name, PrefixChecks.Shard748.arity, Word812.program),
  (PrefixChecks.Shard749.name, PrefixChecks.Shard749.arity, Word813.program),
  (PrefixChecks.Shard750.name, PrefixChecks.Shard750.arity, Word814.program),
  (PrefixChecks.Shard751.name, PrefixChecks.Shard751.arity, Word815.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard736.name, stackResult800.1),
  (PrefixChecks.Shard737.name, stackResult801.1),
  (PrefixChecks.Shard738.name, stackResult802.1),
  (PrefixChecks.Shard739.name, stackResult803.1),
  (PrefixChecks.Shard740.name, stackResult804.1),
  (PrefixChecks.Shard741.name, stackResult805.1),
  (PrefixChecks.Shard742.name, stackResult806.1),
  (PrefixChecks.Shard743.name, stackResult807.1),
  (PrefixChecks.Shard744.name, stackResult808.1),
  (PrefixChecks.Shard745.name, stackResult809.1),
  (PrefixChecks.Shard746.name, stackResult810.1),
  (PrefixChecks.Shard747.name, stackResult811.1),
  (PrefixChecks.Shard748.name, stackResult812.1),
  (PrefixChecks.Shard749.name, stackResult813.1),
  (PrefixChecks.Shard750.name, stackResult814.1),
  (PrefixChecks.Shard751.name, stackResult815.1)
]

noncomputable def frames : List Nat := [
  stackResult800.2.1,
  stackResult801.2.1,
  stackResult802.2.1,
  stackResult803.2.1,
  stackResult804.2.1,
  stackResult805.2.1,
  stackResult806.2.1,
  stackResult807.2.1,
  stackResult808.2.1,
  stackResult809.2.1,
  stackResult810.2.1,
  stackResult811.2.1,
  stackResult812.2.1,
  stackResult813.2.1,
  stackResult814.2.1,
  stackResult815.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult800.2.2.1) stackResult801.2.2.1) stackResult802.2.2.1) stackResult803.2.2.1) stackResult804.2.2.1) stackResult805.2.2.1) stackResult806.2.2.1) stackResult807.2.2.1) stackResult808.2.2.1) stackResult809.2.2.1) stackResult810.2.2.1) stackResult811.2.2.1) stackResult812.2.2.1) stackResult813.2.2.1) stackResult814.2.2.1) stackResult815.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 3840) = (bodies, frames, (bitmapDelta, 4058)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult800_from _
  apply compileWordToStack_cons
  · exact stackResult801_from _
  apply compileWordToStack_cons
  · exact stackResult802_from _
  apply compileWordToStack_cons
  · exact stackResult803_from _
  apply compileWordToStack_cons
  · exact stackResult804_from _
  apply compileWordToStack_cons
  · exact stackResult805_from _
  apply compileWordToStack_cons
  · exact stackResult806_from _
  apply compileWordToStack_cons
  · exact stackResult807_from _
  apply compileWordToStack_cons
  · exact stackResult808_from _
  apply compileWordToStack_cons
  · exact stackResult809_from _
  apply compileWordToStack_cons
  · exact stackResult810_from _
  apply compileWordToStack_cons
  · exact stackResult811_from _
  apply compileWordToStack_cons
  · exact stackResult812_from _
  apply compileWordToStack_cons
  · exact stackResult813_from _
  apply compileWordToStack_cons
  · exact stackResult814_from _
  apply compileWordToStack_cons
  · exact stackResult815_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 3840) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 4058)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 3840 bodies frames bitmapDelta 4058 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 736).take 16).zip
      [oracle800, oracle801, oracle802, oracle803, oracle804, oracle805, oracle806, oracle807, oracle808, oracle809, oracle810, oracle811, oracle812, oracle813, oracle814, oracle815]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle800 PrefixChecks.Shard736.entry,
    wordFunction oracle801 PrefixChecks.Shard737.entry,
    wordFunction oracle802 PrefixChecks.Shard738.entry,
    wordFunction oracle803 PrefixChecks.Shard739.entry,
    wordFunction oracle804 PrefixChecks.Shard740.entry,
    wordFunction oracle805 PrefixChecks.Shard741.entry,
    wordFunction oracle806 PrefixChecks.Shard742.entry,
    wordFunction oracle807 PrefixChecks.Shard743.entry,
    wordFunction oracle808 PrefixChecks.Shard744.entry,
    wordFunction oracle809 PrefixChecks.Shard745.entry,
    wordFunction oracle810 PrefixChecks.Shard746.entry,
    wordFunction oracle811 PrefixChecks.Shard747.entry,
    wordFunction oracle812 PrefixChecks.Shard748.entry,
    wordFunction oracle813 PrefixChecks.Shard749.entry,
    wordFunction oracle814 PrefixChecks.Shard750.entry,
    wordFunction oracle815 PrefixChecks.Shard751.entry] = words
  simp only [
    Word800.wordFunction_eq,
    Word801.wordFunction_eq,
    Word802.wordFunction_eq,
    Word803.wordFunction_eq,
    Word804.wordFunction_eq,
    Word805.wordFunction_eq,
    Word806.wordFunction_eq,
    Word807.wordFunction_eq,
    Word808.wordFunction_eq,
    Word809.wordFunction_eq,
    Word810.wordFunction_eq,
    Word811.wordFunction_eq,
    Word812.wordFunction_eq,
    Word813.wordFunction_eq,
    Word814.wordFunction_eq,
    Word815.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk46
