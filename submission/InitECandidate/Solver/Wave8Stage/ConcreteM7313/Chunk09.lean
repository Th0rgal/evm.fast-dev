import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word208
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word209
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word210
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word211
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word212
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word213
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word214
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word215
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word216
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word217
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word218
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word219
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word220
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word221
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word222
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word223
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk09
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult208 := WordToStack.Native.compileProgNative
  riscvConfig false Word208.program PrefixChecks.Shard144.arity registers (.nil, 258)
theorem stackResult208_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word208.program
      PrefixChecks.Shard144.arity registers (prefixList, 258) =
    (stackResult208.1, stackResult208.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult208.2.2.1, 261)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word208.program
    PrefixChecks.Shard144.arity registers prefixList 258
    stackResult208.1 stackResult208.2.1 stackResult208.2.2.1 261 stackResult208_eq
wave8_kernel_reduce stackResult209 := WordToStack.Native.compileProgNative
  riscvConfig false Word209.program PrefixChecks.Shard145.arity registers (.nil, 261)
theorem stackResult209_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word209.program
      PrefixChecks.Shard145.arity registers (prefixList, 261) =
    (stackResult209.1, stackResult209.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult209.2.2.1, 261)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word209.program
    PrefixChecks.Shard145.arity registers prefixList 261
    stackResult209.1 stackResult209.2.1 stackResult209.2.2.1 261 stackResult209_eq
wave8_kernel_reduce stackResult210 := WordToStack.Native.compileProgNative
  riscvConfig false Word210.program PrefixChecks.Shard146.arity registers (.nil, 261)
theorem stackResult210_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word210.program
      PrefixChecks.Shard146.arity registers (prefixList, 261) =
    (stackResult210.1, stackResult210.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult210.2.2.1, 269)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word210.program
    PrefixChecks.Shard146.arity registers prefixList 261
    stackResult210.1 stackResult210.2.1 stackResult210.2.2.1 269 stackResult210_eq
wave8_kernel_reduce stackResult211 := WordToStack.Native.compileProgNative
  riscvConfig false Word211.program PrefixChecks.Shard147.arity registers (.nil, 269)
theorem stackResult211_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word211.program
      PrefixChecks.Shard147.arity registers (prefixList, 269) =
    (stackResult211.1, stackResult211.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult211.2.2.1, 270)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word211.program
    PrefixChecks.Shard147.arity registers prefixList 269
    stackResult211.1 stackResult211.2.1 stackResult211.2.2.1 270 stackResult211_eq
wave8_kernel_reduce stackResult212 := WordToStack.Native.compileProgNative
  riscvConfig false Word212.program PrefixChecks.Shard148.arity registers (.nil, 270)
theorem stackResult212_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word212.program
      PrefixChecks.Shard148.arity registers (prefixList, 270) =
    (stackResult212.1, stackResult212.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult212.2.2.1, 273)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word212.program
    PrefixChecks.Shard148.arity registers prefixList 270
    stackResult212.1 stackResult212.2.1 stackResult212.2.2.1 273 stackResult212_eq
wave8_kernel_reduce stackResult213 := WordToStack.Native.compileProgNative
  riscvConfig false Word213.program PrefixChecks.Shard149.arity registers (.nil, 273)
theorem stackResult213_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word213.program
      PrefixChecks.Shard149.arity registers (prefixList, 273) =
    (stackResult213.1, stackResult213.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult213.2.2.1, 273)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word213.program
    PrefixChecks.Shard149.arity registers prefixList 273
    stackResult213.1 stackResult213.2.1 stackResult213.2.2.1 273 stackResult213_eq
wave8_kernel_reduce stackResult214 := WordToStack.Native.compileProgNative
  riscvConfig false Word214.program PrefixChecks.Shard150.arity registers (.nil, 273)
theorem stackResult214_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word214.program
      PrefixChecks.Shard150.arity registers (prefixList, 273) =
    (stackResult214.1, stackResult214.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult214.2.2.1, 273)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word214.program
    PrefixChecks.Shard150.arity registers prefixList 273
    stackResult214.1 stackResult214.2.1 stackResult214.2.2.1 273 stackResult214_eq
wave8_kernel_reduce stackResult215 := WordToStack.Native.compileProgNative
  riscvConfig false Word215.program PrefixChecks.Shard151.arity registers (.nil, 273)
theorem stackResult215_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word215.program
      PrefixChecks.Shard151.arity registers (prefixList, 273) =
    (stackResult215.1, stackResult215.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult215.2.2.1, 273)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word215.program
    PrefixChecks.Shard151.arity registers prefixList 273
    stackResult215.1 stackResult215.2.1 stackResult215.2.2.1 273 stackResult215_eq
wave8_kernel_reduce stackResult216 := WordToStack.Native.compileProgNative
  riscvConfig false Word216.program PrefixChecks.Shard152.arity registers (.nil, 273)
theorem stackResult216_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word216.program
      PrefixChecks.Shard152.arity registers (prefixList, 273) =
    (stackResult216.1, stackResult216.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult216.2.2.1, 273)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word216.program
    PrefixChecks.Shard152.arity registers prefixList 273
    stackResult216.1 stackResult216.2.1 stackResult216.2.2.1 273 stackResult216_eq
wave8_kernel_reduce stackResult217 := WordToStack.Native.compileProgNative
  riscvConfig false Word217.program PrefixChecks.Shard153.arity registers (.nil, 273)
theorem stackResult217_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word217.program
      PrefixChecks.Shard153.arity registers (prefixList, 273) =
    (stackResult217.1, stackResult217.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult217.2.2.1, 276)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word217.program
    PrefixChecks.Shard153.arity registers prefixList 273
    stackResult217.1 stackResult217.2.1 stackResult217.2.2.1 276 stackResult217_eq
wave8_kernel_reduce stackResult218 := WordToStack.Native.compileProgNative
  riscvConfig false Word218.program PrefixChecks.Shard154.arity registers (.nil, 276)
theorem stackResult218_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word218.program
      PrefixChecks.Shard154.arity registers (prefixList, 276) =
    (stackResult218.1, stackResult218.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult218.2.2.1, 276)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word218.program
    PrefixChecks.Shard154.arity registers prefixList 276
    stackResult218.1 stackResult218.2.1 stackResult218.2.2.1 276 stackResult218_eq
wave8_kernel_reduce stackResult219 := WordToStack.Native.compileProgNative
  riscvConfig false Word219.program PrefixChecks.Shard155.arity registers (.nil, 276)
theorem stackResult219_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word219.program
      PrefixChecks.Shard155.arity registers (prefixList, 276) =
    (stackResult219.1, stackResult219.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult219.2.2.1, 276)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word219.program
    PrefixChecks.Shard155.arity registers prefixList 276
    stackResult219.1 stackResult219.2.1 stackResult219.2.2.1 276 stackResult219_eq
wave8_kernel_reduce stackResult220 := WordToStack.Native.compileProgNative
  riscvConfig false Word220.program PrefixChecks.Shard156.arity registers (.nil, 276)
theorem stackResult220_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word220.program
      PrefixChecks.Shard156.arity registers (prefixList, 276) =
    (stackResult220.1, stackResult220.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult220.2.2.1, 276)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word220.program
    PrefixChecks.Shard156.arity registers prefixList 276
    stackResult220.1 stackResult220.2.1 stackResult220.2.2.1 276 stackResult220_eq
wave8_kernel_reduce stackResult221 := WordToStack.Native.compileProgNative
  riscvConfig false Word221.program PrefixChecks.Shard157.arity registers (.nil, 276)
theorem stackResult221_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word221.program
      PrefixChecks.Shard157.arity registers (prefixList, 276) =
    (stackResult221.1, stackResult221.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult221.2.2.1, 276)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word221.program
    PrefixChecks.Shard157.arity registers prefixList 276
    stackResult221.1 stackResult221.2.1 stackResult221.2.2.1 276 stackResult221_eq
wave8_kernel_reduce stackResult222 := WordToStack.Native.compileProgNative
  riscvConfig false Word222.program PrefixChecks.Shard158.arity registers (.nil, 276)
theorem stackResult222_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word222.program
      PrefixChecks.Shard158.arity registers (prefixList, 276) =
    (stackResult222.1, stackResult222.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult222.2.2.1, 276)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word222.program
    PrefixChecks.Shard158.arity registers prefixList 276
    stackResult222.1 stackResult222.2.1 stackResult222.2.2.1 276 stackResult222_eq
wave8_kernel_reduce stackResult223 := WordToStack.Native.compileProgNative
  riscvConfig false Word223.program PrefixChecks.Shard159.arity registers (.nil, 276)
theorem stackResult223_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word223.program
      PrefixChecks.Shard159.arity registers (prefixList, 276) =
    (stackResult223.1, stackResult223.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult223.2.2.1, 298)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word223.program
    PrefixChecks.Shard159.arity registers prefixList 276
    stackResult223.1 stackResult223.2.1 stackResult223.2.2.1 298 stackResult223_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard144.name, PrefixChecks.Shard144.arity, Word208.program),
  (PrefixChecks.Shard145.name, PrefixChecks.Shard145.arity, Word209.program),
  (PrefixChecks.Shard146.name, PrefixChecks.Shard146.arity, Word210.program),
  (PrefixChecks.Shard147.name, PrefixChecks.Shard147.arity, Word211.program),
  (PrefixChecks.Shard148.name, PrefixChecks.Shard148.arity, Word212.program),
  (PrefixChecks.Shard149.name, PrefixChecks.Shard149.arity, Word213.program),
  (PrefixChecks.Shard150.name, PrefixChecks.Shard150.arity, Word214.program),
  (PrefixChecks.Shard151.name, PrefixChecks.Shard151.arity, Word215.program),
  (PrefixChecks.Shard152.name, PrefixChecks.Shard152.arity, Word216.program),
  (PrefixChecks.Shard153.name, PrefixChecks.Shard153.arity, Word217.program),
  (PrefixChecks.Shard154.name, PrefixChecks.Shard154.arity, Word218.program),
  (PrefixChecks.Shard155.name, PrefixChecks.Shard155.arity, Word219.program),
  (PrefixChecks.Shard156.name, PrefixChecks.Shard156.arity, Word220.program),
  (PrefixChecks.Shard157.name, PrefixChecks.Shard157.arity, Word221.program),
  (PrefixChecks.Shard158.name, PrefixChecks.Shard158.arity, Word222.program),
  (PrefixChecks.Shard159.name, PrefixChecks.Shard159.arity, Word223.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard144.name, stackResult208.1),
  (PrefixChecks.Shard145.name, stackResult209.1),
  (PrefixChecks.Shard146.name, stackResult210.1),
  (PrefixChecks.Shard147.name, stackResult211.1),
  (PrefixChecks.Shard148.name, stackResult212.1),
  (PrefixChecks.Shard149.name, stackResult213.1),
  (PrefixChecks.Shard150.name, stackResult214.1),
  (PrefixChecks.Shard151.name, stackResult215.1),
  (PrefixChecks.Shard152.name, stackResult216.1),
  (PrefixChecks.Shard153.name, stackResult217.1),
  (PrefixChecks.Shard154.name, stackResult218.1),
  (PrefixChecks.Shard155.name, stackResult219.1),
  (PrefixChecks.Shard156.name, stackResult220.1),
  (PrefixChecks.Shard157.name, stackResult221.1),
  (PrefixChecks.Shard158.name, stackResult222.1),
  (PrefixChecks.Shard159.name, stackResult223.1)
]

noncomputable def frames : List Nat := [
  stackResult208.2.1,
  stackResult209.2.1,
  stackResult210.2.1,
  stackResult211.2.1,
  stackResult212.2.1,
  stackResult213.2.1,
  stackResult214.2.1,
  stackResult215.2.1,
  stackResult216.2.1,
  stackResult217.2.1,
  stackResult218.2.1,
  stackResult219.2.1,
  stackResult220.2.1,
  stackResult221.2.1,
  stackResult222.2.1,
  stackResult223.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult208.2.2.1) stackResult209.2.2.1) stackResult210.2.2.1) stackResult211.2.2.1) stackResult212.2.2.1) stackResult213.2.2.1) stackResult214.2.2.1) stackResult215.2.2.1) stackResult216.2.2.1) stackResult217.2.2.1) stackResult218.2.2.1) stackResult219.2.2.1) stackResult220.2.2.1) stackResult221.2.2.1) stackResult222.2.2.1) stackResult223.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 258) = (bodies, frames, (bitmapDelta, 298)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult208_from _
  apply compileWordToStack_cons
  · exact stackResult209_from _
  apply compileWordToStack_cons
  · exact stackResult210_from _
  apply compileWordToStack_cons
  · exact stackResult211_from _
  apply compileWordToStack_cons
  · exact stackResult212_from _
  apply compileWordToStack_cons
  · exact stackResult213_from _
  apply compileWordToStack_cons
  · exact stackResult214_from _
  apply compileWordToStack_cons
  · exact stackResult215_from _
  apply compileWordToStack_cons
  · exact stackResult216_from _
  apply compileWordToStack_cons
  · exact stackResult217_from _
  apply compileWordToStack_cons
  · exact stackResult218_from _
  apply compileWordToStack_cons
  · exact stackResult219_from _
  apply compileWordToStack_cons
  · exact stackResult220_from _
  apply compileWordToStack_cons
  · exact stackResult221_from _
  apply compileWordToStack_cons
  · exact stackResult222_from _
  apply compileWordToStack_cons
  · exact stackResult223_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 258) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 298)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 258 bodies frames bitmapDelta 298 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 144).take 16).zip
      [oracle208, oracle209, oracle210, oracle211, oracle212, oracle213, oracle214, oracle215, oracle216, oracle217, oracle218, oracle219, oracle220, oracle221, oracle222, oracle223]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle208 PrefixChecks.Shard144.entry,
    wordFunction oracle209 PrefixChecks.Shard145.entry,
    wordFunction oracle210 PrefixChecks.Shard146.entry,
    wordFunction oracle211 PrefixChecks.Shard147.entry,
    wordFunction oracle212 PrefixChecks.Shard148.entry,
    wordFunction oracle213 PrefixChecks.Shard149.entry,
    wordFunction oracle214 PrefixChecks.Shard150.entry,
    wordFunction oracle215 PrefixChecks.Shard151.entry,
    wordFunction oracle216 PrefixChecks.Shard152.entry,
    wordFunction oracle217 PrefixChecks.Shard153.entry,
    wordFunction oracle218 PrefixChecks.Shard154.entry,
    wordFunction oracle219 PrefixChecks.Shard155.entry,
    wordFunction oracle220 PrefixChecks.Shard156.entry,
    wordFunction oracle221 PrefixChecks.Shard157.entry,
    wordFunction oracle222 PrefixChecks.Shard158.entry,
    wordFunction oracle223 PrefixChecks.Shard159.entry] = words
  simp only [
    Word208.wordFunction_eq,
    Word209.wordFunction_eq,
    Word210.wordFunction_eq,
    Word211.wordFunction_eq,
    Word212.wordFunction_eq,
    Word213.wordFunction_eq,
    Word214.wordFunction_eq,
    Word215.wordFunction_eq,
    Word216.wordFunction_eq,
    Word217.wordFunction_eq,
    Word218.wordFunction_eq,
    Word219.wordFunction_eq,
    Word220.wordFunction_eq,
    Word221.wordFunction_eq,
    Word222.wordFunction_eq,
    Word223.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk09
