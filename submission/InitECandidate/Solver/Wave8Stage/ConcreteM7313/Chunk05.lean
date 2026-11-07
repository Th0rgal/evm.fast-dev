import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function150
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word152
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word153
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word155
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word156
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word157
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word158
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word159
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult144 := WordToStack.Native.compileProgNative
  riscvConfig false Function144.program PrefixChecks.Shard80.arity registers (.nil, 107)
theorem stackResult144_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Function144.program
      PrefixChecks.Shard80.arity registers (prefixList, 107) =
    (stackResult144.1, stackResult144.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult144.2.2.1, 110)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Function144.program
    PrefixChecks.Shard80.arity registers prefixList 107
    stackResult144.1 stackResult144.2.1 stackResult144.2.2.1 110 stackResult144_eq
wave8_kernel_reduce stackResult145 := WordToStack.Native.compileProgNative
  riscvConfig false Function145.program PrefixChecks.Shard81.arity registers (.nil, 110)
theorem stackResult145_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Function145.program
      PrefixChecks.Shard81.arity registers (prefixList, 110) =
    (stackResult145.1, stackResult145.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult145.2.2.1, 111)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Function145.program
    PrefixChecks.Shard81.arity registers prefixList 110
    stackResult145.1 stackResult145.2.1 stackResult145.2.2.1 111 stackResult145_eq
wave8_kernel_reduce stackResult146 := WordToStack.Native.compileProgNative
  riscvConfig false Function146.program PrefixChecks.Shard82.arity registers (.nil, 111)
theorem stackResult146_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Function146.program
      PrefixChecks.Shard82.arity registers (prefixList, 111) =
    (stackResult146.1, stackResult146.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult146.2.2.1, 115)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Function146.program
    PrefixChecks.Shard82.arity registers prefixList 111
    stackResult146.1 stackResult146.2.1 stackResult146.2.2.1 115 stackResult146_eq
wave8_kernel_reduce stackResult147 := WordToStack.Native.compileProgNative
  riscvConfig false Function147.program PrefixChecks.Shard83.arity registers (.nil, 115)
theorem stackResult147_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Function147.program
      PrefixChecks.Shard83.arity registers (prefixList, 115) =
    (stackResult147.1, stackResult147.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult147.2.2.1, 123)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Function147.program
    PrefixChecks.Shard83.arity registers prefixList 115
    stackResult147.1 stackResult147.2.1 stackResult147.2.2.1 123 stackResult147_eq
wave8_kernel_reduce stackResult148 := WordToStack.Native.compileProgNative
  riscvConfig false Function148.program PrefixChecks.Shard84.arity registers (.nil, 123)
theorem stackResult148_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Function148.program
      PrefixChecks.Shard84.arity registers (prefixList, 123) =
    (stackResult148.1, stackResult148.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult148.2.2.1, 125)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Function148.program
    PrefixChecks.Shard84.arity registers prefixList 123
    stackResult148.1 stackResult148.2.1 stackResult148.2.2.1 125 stackResult148_eq
wave8_kernel_reduce stackResult149 := WordToStack.Native.compileProgNative
  riscvConfig false Function149.program PrefixChecks.Shard85.arity registers (.nil, 125)
theorem stackResult149_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Function149.program
      PrefixChecks.Shard85.arity registers (prefixList, 125) =
    (stackResult149.1, stackResult149.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult149.2.2.1, 127)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Function149.program
    PrefixChecks.Shard85.arity registers prefixList 125
    stackResult149.1 stackResult149.2.1 stackResult149.2.2.1 127 stackResult149_eq
wave8_kernel_reduce stackResult150 := WordToStack.Native.compileProgNative
  riscvConfig false Function150.program PrefixChecks.Shard86.arity registers (.nil, 127)
theorem stackResult150_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Function150.program
      PrefixChecks.Shard86.arity registers (prefixList, 127) =
    (stackResult150.1, stackResult150.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult150.2.2.1, 127)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Function150.program
    PrefixChecks.Shard86.arity registers prefixList 127
    stackResult150.1 stackResult150.2.1 stackResult150.2.2.1 127 stackResult150_eq
noncomputable abbrev stackResult151 := Chunk05Stack151.stackResult
theorem stackResult151_eq :
    WordToStack.Native.compileProgNative riscvConfig false Word151.program
      PrefixChecks.Shard87.arity registers (.nil, 127) = stackResult151 :=
  Chunk05Stack151.stackResult_eq
theorem stackResult151_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word151.program
      PrefixChecks.Shard87.arity registers (prefixList, 127) =
    (stackResult151.1, stackResult151.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult151.2.2.1, 127)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word151.program
    PrefixChecks.Shard87.arity registers prefixList 127
    stackResult151.1 stackResult151.2.1 stackResult151.2.2.1 127 stackResult151_eq
wave8_kernel_reduce stackResult152 := WordToStack.Native.compileProgNative
  riscvConfig false Word152.program PrefixChecks.Shard88.arity registers (.nil, 127)
theorem stackResult152_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word152.program
      PrefixChecks.Shard88.arity registers (prefixList, 127) =
    (stackResult152.1, stackResult152.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult152.2.2.1, 128)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word152.program
    PrefixChecks.Shard88.arity registers prefixList 127
    stackResult152.1 stackResult152.2.1 stackResult152.2.2.1 128 stackResult152_eq
wave8_kernel_reduce stackResult153 := WordToStack.Native.compileProgNative
  riscvConfig false Word153.program PrefixChecks.Shard89.arity registers (.nil, 128)
theorem stackResult153_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word153.program
      PrefixChecks.Shard89.arity registers (prefixList, 128) =
    (stackResult153.1, stackResult153.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult153.2.2.1, 136)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word153.program
    PrefixChecks.Shard89.arity registers prefixList 128
    stackResult153.1 stackResult153.2.1 stackResult153.2.2.1 136 stackResult153_eq
noncomputable abbrev stackResult154 := Chunk05Word154.stackResult
theorem stackResult154_eq :
    WordToStack.Native.compileProgNative riscvConfig false Chunk05Word154.program
      PrefixChecks.Shard90.arity registers (.nil, 136) = stackResult154 :=
  Chunk05Word154.stackResult_eq
theorem stackResult154_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Chunk05Word154.program
      PrefixChecks.Shard90.arity registers (prefixList, 136) =
    (stackResult154.1, stackResult154.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult154.2.2.1, 136)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Chunk05Word154.program
    PrefixChecks.Shard90.arity registers prefixList 136
    stackResult154.1 stackResult154.2.1 stackResult154.2.2.1 136 stackResult154_eq
wave8_kernel_reduce stackResult155 := WordToStack.Native.compileProgNative
  riscvConfig false Word155.program PrefixChecks.Shard91.arity registers (.nil, 136)
theorem stackResult155_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word155.program
      PrefixChecks.Shard91.arity registers (prefixList, 136) =
    (stackResult155.1, stackResult155.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult155.2.2.1, 139)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word155.program
    PrefixChecks.Shard91.arity registers prefixList 136
    stackResult155.1 stackResult155.2.1 stackResult155.2.2.1 139 stackResult155_eq
wave8_kernel_reduce stackResult156 := WordToStack.Native.compileProgNative
  riscvConfig false Word156.program PrefixChecks.Shard92.arity registers (.nil, 139)
theorem stackResult156_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word156.program
      PrefixChecks.Shard92.arity registers (prefixList, 139) =
    (stackResult156.1, stackResult156.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult156.2.2.1, 139)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word156.program
    PrefixChecks.Shard92.arity registers prefixList 139
    stackResult156.1 stackResult156.2.1 stackResult156.2.2.1 139 stackResult156_eq
wave8_kernel_reduce stackResult157 := WordToStack.Native.compileProgNative
  riscvConfig false Word157.program PrefixChecks.Shard93.arity registers (.nil, 139)
theorem stackResult157_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word157.program
      PrefixChecks.Shard93.arity registers (prefixList, 139) =
    (stackResult157.1, stackResult157.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult157.2.2.1, 140)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word157.program
    PrefixChecks.Shard93.arity registers prefixList 139
    stackResult157.1 stackResult157.2.1 stackResult157.2.2.1 140 stackResult157_eq
wave8_kernel_reduce stackResult158 := WordToStack.Native.compileProgNative
  riscvConfig false Word158.program PrefixChecks.Shard94.arity registers (.nil, 140)
theorem stackResult158_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word158.program
      PrefixChecks.Shard94.arity registers (prefixList, 140) =
    (stackResult158.1, stackResult158.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult158.2.2.1, 146)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word158.program
    PrefixChecks.Shard94.arity registers prefixList 140
    stackResult158.1 stackResult158.2.1 stackResult158.2.2.1 146 stackResult158_eq
wave8_kernel_reduce stackResult159 := WordToStack.Native.compileProgNative
  riscvConfig false Word159.program PrefixChecks.Shard95.arity registers (.nil, 146)
theorem stackResult159_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word159.program
      PrefixChecks.Shard95.arity registers (prefixList, 146) =
    (stackResult159.1, stackResult159.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult159.2.2.1, 146)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word159.program
    PrefixChecks.Shard95.arity registers prefixList 146
    stackResult159.1 stackResult159.2.1 stackResult159.2.2.1 146 stackResult159_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard80.name, PrefixChecks.Shard80.arity, Function144.program),
  (PrefixChecks.Shard81.name, PrefixChecks.Shard81.arity, Function145.program),
  (PrefixChecks.Shard82.name, PrefixChecks.Shard82.arity, Function146.program),
  (PrefixChecks.Shard83.name, PrefixChecks.Shard83.arity, Function147.program),
  (PrefixChecks.Shard84.name, PrefixChecks.Shard84.arity, Function148.program),
  (PrefixChecks.Shard85.name, PrefixChecks.Shard85.arity, Function149.program),
  (PrefixChecks.Shard86.name, PrefixChecks.Shard86.arity, Function150.program),
  (PrefixChecks.Shard87.name, PrefixChecks.Shard87.arity, Word151.program),
  (PrefixChecks.Shard88.name, PrefixChecks.Shard88.arity, Word152.program),
  (PrefixChecks.Shard89.name, PrefixChecks.Shard89.arity, Word153.program),
  (PrefixChecks.Shard90.name, PrefixChecks.Shard90.arity, Chunk05Word154.program),
  (PrefixChecks.Shard91.name, PrefixChecks.Shard91.arity, Word155.program),
  (PrefixChecks.Shard92.name, PrefixChecks.Shard92.arity, Word156.program),
  (PrefixChecks.Shard93.name, PrefixChecks.Shard93.arity, Word157.program),
  (PrefixChecks.Shard94.name, PrefixChecks.Shard94.arity, Word158.program),
  (PrefixChecks.Shard95.name, PrefixChecks.Shard95.arity, Word159.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard80.name, stackResult144.1),
  (PrefixChecks.Shard81.name, stackResult145.1),
  (PrefixChecks.Shard82.name, stackResult146.1),
  (PrefixChecks.Shard83.name, stackResult147.1),
  (PrefixChecks.Shard84.name, stackResult148.1),
  (PrefixChecks.Shard85.name, stackResult149.1),
  (PrefixChecks.Shard86.name, stackResult150.1),
  (PrefixChecks.Shard87.name, stackResult151.1),
  (PrefixChecks.Shard88.name, stackResult152.1),
  (PrefixChecks.Shard89.name, stackResult153.1),
  (PrefixChecks.Shard90.name, stackResult154.1),
  (PrefixChecks.Shard91.name, stackResult155.1),
  (PrefixChecks.Shard92.name, stackResult156.1),
  (PrefixChecks.Shard93.name, stackResult157.1),
  (PrefixChecks.Shard94.name, stackResult158.1),
  (PrefixChecks.Shard95.name, stackResult159.1)
]

noncomputable def frames : List Nat := [
  stackResult144.2.1,
  stackResult145.2.1,
  stackResult146.2.1,
  stackResult147.2.1,
  stackResult148.2.1,
  stackResult149.2.1,
  stackResult150.2.1,
  stackResult151.2.1,
  stackResult152.2.1,
  stackResult153.2.1,
  stackResult154.2.1,
  stackResult155.2.1,
  stackResult156.2.1,
  stackResult157.2.1,
  stackResult158.2.1,
  stackResult159.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult144.2.2.1) stackResult145.2.2.1) stackResult146.2.2.1) stackResult147.2.2.1) stackResult148.2.2.1) stackResult149.2.2.1) stackResult150.2.2.1) stackResult151.2.2.1) stackResult152.2.2.1) stackResult153.2.2.1) stackResult154.2.2.1) stackResult155.2.2.1) stackResult156.2.2.1) stackResult157.2.2.1) stackResult158.2.2.1) stackResult159.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 107) = (bodies, frames, (bitmapDelta, 146)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult144_from _
  apply compileWordToStack_cons
  · exact stackResult145_from _
  apply compileWordToStack_cons
  · exact stackResult146_from _
  apply compileWordToStack_cons
  · exact stackResult147_from _
  apply compileWordToStack_cons
  · exact stackResult148_from _
  apply compileWordToStack_cons
  · exact stackResult149_from _
  apply compileWordToStack_cons
  · exact stackResult150_from _
  apply compileWordToStack_cons
  · exact stackResult151_from _
  apply compileWordToStack_cons
  · exact stackResult152_from _
  apply compileWordToStack_cons
  · exact stackResult153_from _
  apply compileWordToStack_cons
  · exact stackResult154_from _
  apply compileWordToStack_cons
  · exact stackResult155_from _
  apply compileWordToStack_cons
  · exact stackResult156_from _
  apply compileWordToStack_cons
  · exact stackResult157_from _
  apply compileWordToStack_cons
  · exact stackResult158_from _
  apply compileWordToStack_cons
  · exact stackResult159_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 107) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 146)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 107 bodies frames bitmapDelta 146 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 80).take 16).zip
      [oracle144, oracle145, oracle146, oracle147, oracle148, oracle149, oracle150, oracle151, oracle152, oracle153, oracle154, oracle155, oracle156, oracle157, oracle158, oracle159]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle144 PrefixChecks.Shard80.entry,
    wordFunction oracle145 PrefixChecks.Shard81.entry,
    wordFunction oracle146 PrefixChecks.Shard82.entry,
    wordFunction oracle147 PrefixChecks.Shard83.entry,
    wordFunction oracle148 PrefixChecks.Shard84.entry,
    wordFunction oracle149 PrefixChecks.Shard85.entry,
    wordFunction oracle150 PrefixChecks.Shard86.entry,
    wordFunction oracle151 PrefixChecks.Shard87.entry,
    wordFunction oracle152 PrefixChecks.Shard88.entry,
    wordFunction oracle153 PrefixChecks.Shard89.entry,
    wordFunction oracle154 PrefixChecks.Shard90.entry,
    wordFunction oracle155 PrefixChecks.Shard91.entry,
    wordFunction oracle156 PrefixChecks.Shard92.entry,
    wordFunction oracle157 PrefixChecks.Shard93.entry,
    wordFunction oracle158 PrefixChecks.Shard94.entry,
    wordFunction oracle159 PrefixChecks.Shard95.entry] = words
  simp only [
    Function144.wordFunction_eq,
    Function145.wordFunction_eq,
    Function146.wordFunction_eq,
    Function147.wordFunction_eq,
    Function148.wordFunction_eq,
    Function149.wordFunction_eq,
    Function150.wordFunction_eq,
    Word151.wordFunction_eq,
    Word152.wordFunction_eq,
    Word153.wordFunction_eq,
    Chunk05Word154.wordFunction_eq,
    Word155.wordFunction_eq,
    Word156.wordFunction_eq,
    Word157.wordFunction_eq,
    Word158.wordFunction_eq,
    Word159.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05
