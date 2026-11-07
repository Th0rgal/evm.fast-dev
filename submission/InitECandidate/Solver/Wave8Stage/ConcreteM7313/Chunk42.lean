import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word736
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word737
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word738
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word739
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word740
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word741
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word742
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word743
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word744
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word745
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word746
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word747
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word748
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word749
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word750
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word751
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk42
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult736 := WordToStack.Native.compileProgNative
  riscvConfig false Word736.program PrefixChecks.Shard672.arity registers (.nil, 3267)
theorem stackResult736_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word736.program
      PrefixChecks.Shard672.arity registers (prefixList, 3267) =
    (stackResult736.1, stackResult736.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult736.2.2.1, 3269)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word736.program
    PrefixChecks.Shard672.arity registers prefixList 3267
    stackResult736.1 stackResult736.2.1 stackResult736.2.2.1 3269 stackResult736_eq
wave8_kernel_reduce stackResult737 := WordToStack.Native.compileProgNative
  riscvConfig false Word737.program PrefixChecks.Shard673.arity registers (.nil, 3269)
theorem stackResult737_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word737.program
      PrefixChecks.Shard673.arity registers (prefixList, 3269) =
    (stackResult737.1, stackResult737.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult737.2.2.1, 3269)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word737.program
    PrefixChecks.Shard673.arity registers prefixList 3269
    stackResult737.1 stackResult737.2.1 stackResult737.2.2.1 3269 stackResult737_eq
wave8_kernel_reduce stackResult738 := WordToStack.Native.compileProgNative
  riscvConfig false Word738.program PrefixChecks.Shard674.arity registers (.nil, 3269)
theorem stackResult738_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word738.program
      PrefixChecks.Shard674.arity registers (prefixList, 3269) =
    (stackResult738.1, stackResult738.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult738.2.2.1, 3270)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word738.program
    PrefixChecks.Shard674.arity registers prefixList 3269
    stackResult738.1 stackResult738.2.1 stackResult738.2.2.1 3270 stackResult738_eq
wave8_kernel_reduce stackResult739 := WordToStack.Native.compileProgNative
  riscvConfig false Word739.program PrefixChecks.Shard675.arity registers (.nil, 3270)
theorem stackResult739_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word739.program
      PrefixChecks.Shard675.arity registers (prefixList, 3270) =
    (stackResult739.1, stackResult739.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult739.2.2.1, 3278)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word739.program
    PrefixChecks.Shard675.arity registers prefixList 3270
    stackResult739.1 stackResult739.2.1 stackResult739.2.2.1 3278 stackResult739_eq
wave8_kernel_reduce stackResult740 := WordToStack.Native.compileProgNative
  riscvConfig false Word740.program PrefixChecks.Shard676.arity registers (.nil, 3278)
theorem stackResult740_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word740.program
      PrefixChecks.Shard676.arity registers (prefixList, 3278) =
    (stackResult740.1, stackResult740.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult740.2.2.1, 3283)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word740.program
    PrefixChecks.Shard676.arity registers prefixList 3278
    stackResult740.1 stackResult740.2.1 stackResult740.2.2.1 3283 stackResult740_eq
wave8_kernel_reduce stackResult741 := WordToStack.Native.compileProgNative
  riscvConfig false Word741.program PrefixChecks.Shard677.arity registers (.nil, 3283)
theorem stackResult741_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word741.program
      PrefixChecks.Shard677.arity registers (prefixList, 3283) =
    (stackResult741.1, stackResult741.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult741.2.2.1, 3285)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word741.program
    PrefixChecks.Shard677.arity registers prefixList 3283
    stackResult741.1 stackResult741.2.1 stackResult741.2.2.1 3285 stackResult741_eq
wave8_kernel_reduce stackResult742 := WordToStack.Native.compileProgNative
  riscvConfig false Word742.program PrefixChecks.Shard678.arity registers (.nil, 3285)
theorem stackResult742_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word742.program
      PrefixChecks.Shard678.arity registers (prefixList, 3285) =
    (stackResult742.1, stackResult742.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult742.2.2.1, 3287)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word742.program
    PrefixChecks.Shard678.arity registers prefixList 3285
    stackResult742.1 stackResult742.2.1 stackResult742.2.2.1 3287 stackResult742_eq
wave8_kernel_reduce stackResult743 := WordToStack.Native.compileProgNative
  riscvConfig false Word743.program PrefixChecks.Shard679.arity registers (.nil, 3287)
theorem stackResult743_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word743.program
      PrefixChecks.Shard679.arity registers (prefixList, 3287) =
    (stackResult743.1, stackResult743.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult743.2.2.1, 3294)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word743.program
    PrefixChecks.Shard679.arity registers prefixList 3287
    stackResult743.1 stackResult743.2.1 stackResult743.2.2.1 3294 stackResult743_eq
wave8_kernel_reduce stackResult744 := WordToStack.Native.compileProgNative
  riscvConfig false Word744.program PrefixChecks.Shard680.arity registers (.nil, 3294)
theorem stackResult744_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word744.program
      PrefixChecks.Shard680.arity registers (prefixList, 3294) =
    (stackResult744.1, stackResult744.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult744.2.2.1, 3303)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word744.program
    PrefixChecks.Shard680.arity registers prefixList 3294
    stackResult744.1 stackResult744.2.1 stackResult744.2.2.1 3303 stackResult744_eq
wave8_kernel_reduce stackResult745 := WordToStack.Native.compileProgNative
  riscvConfig false Word745.program PrefixChecks.Shard681.arity registers (.nil, 3303)
theorem stackResult745_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word745.program
      PrefixChecks.Shard681.arity registers (prefixList, 3303) =
    (stackResult745.1, stackResult745.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult745.2.2.1, 3305)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word745.program
    PrefixChecks.Shard681.arity registers prefixList 3303
    stackResult745.1 stackResult745.2.1 stackResult745.2.2.1 3305 stackResult745_eq
wave8_kernel_reduce stackResult746 := WordToStack.Native.compileProgNative
  riscvConfig false Word746.program PrefixChecks.Shard682.arity registers (.nil, 3305)
theorem stackResult746_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word746.program
      PrefixChecks.Shard682.arity registers (prefixList, 3305) =
    (stackResult746.1, stackResult746.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult746.2.2.1, 3306)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word746.program
    PrefixChecks.Shard682.arity registers prefixList 3305
    stackResult746.1 stackResult746.2.1 stackResult746.2.2.1 3306 stackResult746_eq
wave8_kernel_reduce stackResult747 := WordToStack.Native.compileProgNative
  riscvConfig false Word747.program PrefixChecks.Shard683.arity registers (.nil, 3306)
theorem stackResult747_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word747.program
      PrefixChecks.Shard683.arity registers (prefixList, 3306) =
    (stackResult747.1, stackResult747.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult747.2.2.1, 3307)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word747.program
    PrefixChecks.Shard683.arity registers prefixList 3306
    stackResult747.1 stackResult747.2.1 stackResult747.2.2.1 3307 stackResult747_eq
wave8_kernel_reduce stackResult748 := WordToStack.Native.compileProgNative
  riscvConfig false Word748.program PrefixChecks.Shard684.arity registers (.nil, 3307)
theorem stackResult748_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word748.program
      PrefixChecks.Shard684.arity registers (prefixList, 3307) =
    (stackResult748.1, stackResult748.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult748.2.2.1, 3310)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word748.program
    PrefixChecks.Shard684.arity registers prefixList 3307
    stackResult748.1 stackResult748.2.1 stackResult748.2.2.1 3310 stackResult748_eq
wave8_kernel_reduce stackResult749 := WordToStack.Native.compileProgNative
  riscvConfig false Word749.program PrefixChecks.Shard685.arity registers (.nil, 3310)
theorem stackResult749_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word749.program
      PrefixChecks.Shard685.arity registers (prefixList, 3310) =
    (stackResult749.1, stackResult749.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult749.2.2.1, 3313)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word749.program
    PrefixChecks.Shard685.arity registers prefixList 3310
    stackResult749.1 stackResult749.2.1 stackResult749.2.2.1 3313 stackResult749_eq
wave8_kernel_reduce stackResult750 := WordToStack.Native.compileProgNative
  riscvConfig false Word750.program PrefixChecks.Shard686.arity registers (.nil, 3313)
theorem stackResult750_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word750.program
      PrefixChecks.Shard686.arity registers (prefixList, 3313) =
    (stackResult750.1, stackResult750.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult750.2.2.1, 3316)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word750.program
    PrefixChecks.Shard686.arity registers prefixList 3313
    stackResult750.1 stackResult750.2.1 stackResult750.2.2.1 3316 stackResult750_eq
wave8_kernel_reduce stackResult751 := WordToStack.Native.compileProgNative
  riscvConfig false Word751.program PrefixChecks.Shard687.arity registers (.nil, 3316)
theorem stackResult751_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word751.program
      PrefixChecks.Shard687.arity registers (prefixList, 3316) =
    (stackResult751.1, stackResult751.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult751.2.2.1, 3319)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word751.program
    PrefixChecks.Shard687.arity registers prefixList 3316
    stackResult751.1 stackResult751.2.1 stackResult751.2.2.1 3319 stackResult751_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard672.name, PrefixChecks.Shard672.arity, Word736.program),
  (PrefixChecks.Shard673.name, PrefixChecks.Shard673.arity, Word737.program),
  (PrefixChecks.Shard674.name, PrefixChecks.Shard674.arity, Word738.program),
  (PrefixChecks.Shard675.name, PrefixChecks.Shard675.arity, Word739.program),
  (PrefixChecks.Shard676.name, PrefixChecks.Shard676.arity, Word740.program),
  (PrefixChecks.Shard677.name, PrefixChecks.Shard677.arity, Word741.program),
  (PrefixChecks.Shard678.name, PrefixChecks.Shard678.arity, Word742.program),
  (PrefixChecks.Shard679.name, PrefixChecks.Shard679.arity, Word743.program),
  (PrefixChecks.Shard680.name, PrefixChecks.Shard680.arity, Word744.program),
  (PrefixChecks.Shard681.name, PrefixChecks.Shard681.arity, Word745.program),
  (PrefixChecks.Shard682.name, PrefixChecks.Shard682.arity, Word746.program),
  (PrefixChecks.Shard683.name, PrefixChecks.Shard683.arity, Word747.program),
  (PrefixChecks.Shard684.name, PrefixChecks.Shard684.arity, Word748.program),
  (PrefixChecks.Shard685.name, PrefixChecks.Shard685.arity, Word749.program),
  (PrefixChecks.Shard686.name, PrefixChecks.Shard686.arity, Word750.program),
  (PrefixChecks.Shard687.name, PrefixChecks.Shard687.arity, Word751.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard672.name, stackResult736.1),
  (PrefixChecks.Shard673.name, stackResult737.1),
  (PrefixChecks.Shard674.name, stackResult738.1),
  (PrefixChecks.Shard675.name, stackResult739.1),
  (PrefixChecks.Shard676.name, stackResult740.1),
  (PrefixChecks.Shard677.name, stackResult741.1),
  (PrefixChecks.Shard678.name, stackResult742.1),
  (PrefixChecks.Shard679.name, stackResult743.1),
  (PrefixChecks.Shard680.name, stackResult744.1),
  (PrefixChecks.Shard681.name, stackResult745.1),
  (PrefixChecks.Shard682.name, stackResult746.1),
  (PrefixChecks.Shard683.name, stackResult747.1),
  (PrefixChecks.Shard684.name, stackResult748.1),
  (PrefixChecks.Shard685.name, stackResult749.1),
  (PrefixChecks.Shard686.name, stackResult750.1),
  (PrefixChecks.Shard687.name, stackResult751.1)
]

noncomputable def frames : List Nat := [
  stackResult736.2.1,
  stackResult737.2.1,
  stackResult738.2.1,
  stackResult739.2.1,
  stackResult740.2.1,
  stackResult741.2.1,
  stackResult742.2.1,
  stackResult743.2.1,
  stackResult744.2.1,
  stackResult745.2.1,
  stackResult746.2.1,
  stackResult747.2.1,
  stackResult748.2.1,
  stackResult749.2.1,
  stackResult750.2.1,
  stackResult751.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult736.2.2.1) stackResult737.2.2.1) stackResult738.2.2.1) stackResult739.2.2.1) stackResult740.2.2.1) stackResult741.2.2.1) stackResult742.2.2.1) stackResult743.2.2.1) stackResult744.2.2.1) stackResult745.2.2.1) stackResult746.2.2.1) stackResult747.2.2.1) stackResult748.2.2.1) stackResult749.2.2.1) stackResult750.2.2.1) stackResult751.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 3267) = (bodies, frames, (bitmapDelta, 3319)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult736_from _
  apply compileWordToStack_cons
  · exact stackResult737_from _
  apply compileWordToStack_cons
  · exact stackResult738_from _
  apply compileWordToStack_cons
  · exact stackResult739_from _
  apply compileWordToStack_cons
  · exact stackResult740_from _
  apply compileWordToStack_cons
  · exact stackResult741_from _
  apply compileWordToStack_cons
  · exact stackResult742_from _
  apply compileWordToStack_cons
  · exact stackResult743_from _
  apply compileWordToStack_cons
  · exact stackResult744_from _
  apply compileWordToStack_cons
  · exact stackResult745_from _
  apply compileWordToStack_cons
  · exact stackResult746_from _
  apply compileWordToStack_cons
  · exact stackResult747_from _
  apply compileWordToStack_cons
  · exact stackResult748_from _
  apply compileWordToStack_cons
  · exact stackResult749_from _
  apply compileWordToStack_cons
  · exact stackResult750_from _
  apply compileWordToStack_cons
  · exact stackResult751_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 3267) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 3319)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 3267 bodies frames bitmapDelta 3319 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 672).take 16).zip
      [oracle736, oracle737, oracle738, oracle739, oracle740, oracle741, oracle742, oracle743, oracle744, oracle745, oracle746, oracle747, oracle748, oracle749, oracle750, oracle751]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle736 PrefixChecks.Shard672.entry,
    wordFunction oracle737 PrefixChecks.Shard673.entry,
    wordFunction oracle738 PrefixChecks.Shard674.entry,
    wordFunction oracle739 PrefixChecks.Shard675.entry,
    wordFunction oracle740 PrefixChecks.Shard676.entry,
    wordFunction oracle741 PrefixChecks.Shard677.entry,
    wordFunction oracle742 PrefixChecks.Shard678.entry,
    wordFunction oracle743 PrefixChecks.Shard679.entry,
    wordFunction oracle744 PrefixChecks.Shard680.entry,
    wordFunction oracle745 PrefixChecks.Shard681.entry,
    wordFunction oracle746 PrefixChecks.Shard682.entry,
    wordFunction oracle747 PrefixChecks.Shard683.entry,
    wordFunction oracle748 PrefixChecks.Shard684.entry,
    wordFunction oracle749 PrefixChecks.Shard685.entry,
    wordFunction oracle750 PrefixChecks.Shard686.entry,
    wordFunction oracle751 PrefixChecks.Shard687.entry] = words
  simp only [
    Word736.wordFunction_eq,
    Word737.wordFunction_eq,
    Word738.wordFunction_eq,
    Word739.wordFunction_eq,
    Word740.wordFunction_eq,
    Word741.wordFunction_eq,
    Word742.wordFunction_eq,
    Word743.wordFunction_eq,
    Word744.wordFunction_eq,
    Word745.wordFunction_eq,
    Word746.wordFunction_eq,
    Word747.wordFunction_eq,
    Word748.wordFunction_eq,
    Word749.wordFunction_eq,
    Word750.wordFunction_eq,
    Word751.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk42
