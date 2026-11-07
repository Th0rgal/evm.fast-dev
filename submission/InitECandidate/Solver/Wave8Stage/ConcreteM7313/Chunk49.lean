import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word848
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word849
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word850
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word851
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word852
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word853
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word854
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word855
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word856
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word857
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word858
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word859
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word860
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word861
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word862
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word863
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk49
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult848 := WordToStack.Native.compileProgNative
  riscvConfig false Word848.program PrefixChecks.Shard784.arity registers (.nil, 4240)
theorem stackResult848_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word848.program
      PrefixChecks.Shard784.arity registers (prefixList, 4240) =
    (stackResult848.1, stackResult848.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult848.2.2.1, 4268)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word848.program
    PrefixChecks.Shard784.arity registers prefixList 4240
    stackResult848.1 stackResult848.2.1 stackResult848.2.2.1 4268 stackResult848_eq
wave8_kernel_reduce stackResult849 := WordToStack.Native.compileProgNative
  riscvConfig false Word849.program PrefixChecks.Shard785.arity registers (.nil, 4268)
theorem stackResult849_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word849.program
      PrefixChecks.Shard785.arity registers (prefixList, 4268) =
    (stackResult849.1, stackResult849.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult849.2.2.1, 4270)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word849.program
    PrefixChecks.Shard785.arity registers prefixList 4268
    stackResult849.1 stackResult849.2.1 stackResult849.2.2.1 4270 stackResult849_eq
wave8_kernel_reduce stackResult850 := WordToStack.Native.compileProgNative
  riscvConfig false Word850.program PrefixChecks.Shard786.arity registers (.nil, 4270)
theorem stackResult850_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word850.program
      PrefixChecks.Shard786.arity registers (prefixList, 4270) =
    (stackResult850.1, stackResult850.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult850.2.2.1, 4306)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word850.program
    PrefixChecks.Shard786.arity registers prefixList 4270
    stackResult850.1 stackResult850.2.1 stackResult850.2.2.1 4306 stackResult850_eq
wave8_kernel_reduce stackResult851 := WordToStack.Native.compileProgNative
  riscvConfig false Word851.program PrefixChecks.Shard787.arity registers (.nil, 4306)
theorem stackResult851_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word851.program
      PrefixChecks.Shard787.arity registers (prefixList, 4306) =
    (stackResult851.1, stackResult851.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult851.2.2.1, 4309)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word851.program
    PrefixChecks.Shard787.arity registers prefixList 4306
    stackResult851.1 stackResult851.2.1 stackResult851.2.2.1 4309 stackResult851_eq
wave8_kernel_reduce stackResult852 := WordToStack.Native.compileProgNative
  riscvConfig false Word852.program PrefixChecks.Shard788.arity registers (.nil, 4309)
theorem stackResult852_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word852.program
      PrefixChecks.Shard788.arity registers (prefixList, 4309) =
    (stackResult852.1, stackResult852.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult852.2.2.1, 4332)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word852.program
    PrefixChecks.Shard788.arity registers prefixList 4309
    stackResult852.1 stackResult852.2.1 stackResult852.2.2.1 4332 stackResult852_eq
wave8_kernel_reduce stackResult853 := WordToStack.Native.compileProgNative
  riscvConfig false Word853.program PrefixChecks.Shard789.arity registers (.nil, 4332)
theorem stackResult853_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word853.program
      PrefixChecks.Shard789.arity registers (prefixList, 4332) =
    (stackResult853.1, stackResult853.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult853.2.2.1, 4340)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word853.program
    PrefixChecks.Shard789.arity registers prefixList 4332
    stackResult853.1 stackResult853.2.1 stackResult853.2.2.1 4340 stackResult853_eq
wave8_kernel_reduce stackResult854 := WordToStack.Native.compileProgNative
  riscvConfig false Word854.program PrefixChecks.Shard790.arity registers (.nil, 4340)
theorem stackResult854_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word854.program
      PrefixChecks.Shard790.arity registers (prefixList, 4340) =
    (stackResult854.1, stackResult854.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult854.2.2.1, 4359)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word854.program
    PrefixChecks.Shard790.arity registers prefixList 4340
    stackResult854.1 stackResult854.2.1 stackResult854.2.2.1 4359 stackResult854_eq
wave8_kernel_reduce stackResult855 := WordToStack.Native.compileProgNative
  riscvConfig false Word855.program PrefixChecks.Shard791.arity registers (.nil, 4359)
theorem stackResult855_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word855.program
      PrefixChecks.Shard791.arity registers (prefixList, 4359) =
    (stackResult855.1, stackResult855.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult855.2.2.1, 4359)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word855.program
    PrefixChecks.Shard791.arity registers prefixList 4359
    stackResult855.1 stackResult855.2.1 stackResult855.2.2.1 4359 stackResult855_eq
wave8_kernel_reduce stackResult856 := WordToStack.Native.compileProgNative
  riscvConfig false Word856.program PrefixChecks.Shard792.arity registers (.nil, 4359)
theorem stackResult856_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word856.program
      PrefixChecks.Shard792.arity registers (prefixList, 4359) =
    (stackResult856.1, stackResult856.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult856.2.2.1, 4359)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word856.program
    PrefixChecks.Shard792.arity registers prefixList 4359
    stackResult856.1 stackResult856.2.1 stackResult856.2.2.1 4359 stackResult856_eq
wave8_kernel_reduce stackResult857 := WordToStack.Native.compileProgNative
  riscvConfig false Word857.program PrefixChecks.Shard793.arity registers (.nil, 4359)
theorem stackResult857_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word857.program
      PrefixChecks.Shard793.arity registers (prefixList, 4359) =
    (stackResult857.1, stackResult857.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult857.2.2.1, 4360)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word857.program
    PrefixChecks.Shard793.arity registers prefixList 4359
    stackResult857.1 stackResult857.2.1 stackResult857.2.2.1 4360 stackResult857_eq
wave8_kernel_reduce stackResult858 := WordToStack.Native.compileProgNative
  riscvConfig false Word858.program PrefixChecks.Shard794.arity registers (.nil, 4360)
theorem stackResult858_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word858.program
      PrefixChecks.Shard794.arity registers (prefixList, 4360) =
    (stackResult858.1, stackResult858.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult858.2.2.1, 4363)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word858.program
    PrefixChecks.Shard794.arity registers prefixList 4360
    stackResult858.1 stackResult858.2.1 stackResult858.2.2.1 4363 stackResult858_eq
wave8_kernel_reduce stackResult859 := WordToStack.Native.compileProgNative
  riscvConfig false Word859.program PrefixChecks.Shard795.arity registers (.nil, 4363)
theorem stackResult859_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word859.program
      PrefixChecks.Shard795.arity registers (prefixList, 4363) =
    (stackResult859.1, stackResult859.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult859.2.2.1, 4365)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word859.program
    PrefixChecks.Shard795.arity registers prefixList 4363
    stackResult859.1 stackResult859.2.1 stackResult859.2.2.1 4365 stackResult859_eq
wave8_kernel_reduce stackResult860 := WordToStack.Native.compileProgNative
  riscvConfig false Word860.program PrefixChecks.Shard796.arity registers (.nil, 4365)
theorem stackResult860_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word860.program
      PrefixChecks.Shard796.arity registers (prefixList, 4365) =
    (stackResult860.1, stackResult860.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult860.2.2.1, 4377)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word860.program
    PrefixChecks.Shard796.arity registers prefixList 4365
    stackResult860.1 stackResult860.2.1 stackResult860.2.2.1 4377 stackResult860_eq
wave8_kernel_reduce stackResult861 := WordToStack.Native.compileProgNative
  riscvConfig false Word861.program PrefixChecks.Shard797.arity registers (.nil, 4377)
theorem stackResult861_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word861.program
      PrefixChecks.Shard797.arity registers (prefixList, 4377) =
    (stackResult861.1, stackResult861.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult861.2.2.1, 4381)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word861.program
    PrefixChecks.Shard797.arity registers prefixList 4377
    stackResult861.1 stackResult861.2.1 stackResult861.2.2.1 4381 stackResult861_eq
wave8_kernel_reduce stackResult862 := WordToStack.Native.compileProgNative
  riscvConfig false Word862.program PrefixChecks.Shard798.arity registers (.nil, 4381)
theorem stackResult862_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word862.program
      PrefixChecks.Shard798.arity registers (prefixList, 4381) =
    (stackResult862.1, stackResult862.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult862.2.2.1, 4401)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word862.program
    PrefixChecks.Shard798.arity registers prefixList 4381
    stackResult862.1 stackResult862.2.1 stackResult862.2.2.1 4401 stackResult862_eq
wave8_kernel_reduce stackResult863 := WordToStack.Native.compileProgNative
  riscvConfig false Word863.program PrefixChecks.Shard799.arity registers (.nil, 4401)
theorem stackResult863_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word863.program
      PrefixChecks.Shard799.arity registers (prefixList, 4401) =
    (stackResult863.1, stackResult863.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult863.2.2.1, 4519)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word863.program
    PrefixChecks.Shard799.arity registers prefixList 4401
    stackResult863.1 stackResult863.2.1 stackResult863.2.2.1 4519 stackResult863_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard784.name, PrefixChecks.Shard784.arity, Word848.program),
  (PrefixChecks.Shard785.name, PrefixChecks.Shard785.arity, Word849.program),
  (PrefixChecks.Shard786.name, PrefixChecks.Shard786.arity, Word850.program),
  (PrefixChecks.Shard787.name, PrefixChecks.Shard787.arity, Word851.program),
  (PrefixChecks.Shard788.name, PrefixChecks.Shard788.arity, Word852.program),
  (PrefixChecks.Shard789.name, PrefixChecks.Shard789.arity, Word853.program),
  (PrefixChecks.Shard790.name, PrefixChecks.Shard790.arity, Word854.program),
  (PrefixChecks.Shard791.name, PrefixChecks.Shard791.arity, Word855.program),
  (PrefixChecks.Shard792.name, PrefixChecks.Shard792.arity, Word856.program),
  (PrefixChecks.Shard793.name, PrefixChecks.Shard793.arity, Word857.program),
  (PrefixChecks.Shard794.name, PrefixChecks.Shard794.arity, Word858.program),
  (PrefixChecks.Shard795.name, PrefixChecks.Shard795.arity, Word859.program),
  (PrefixChecks.Shard796.name, PrefixChecks.Shard796.arity, Word860.program),
  (PrefixChecks.Shard797.name, PrefixChecks.Shard797.arity, Word861.program),
  (PrefixChecks.Shard798.name, PrefixChecks.Shard798.arity, Word862.program),
  (PrefixChecks.Shard799.name, PrefixChecks.Shard799.arity, Word863.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard784.name, stackResult848.1),
  (PrefixChecks.Shard785.name, stackResult849.1),
  (PrefixChecks.Shard786.name, stackResult850.1),
  (PrefixChecks.Shard787.name, stackResult851.1),
  (PrefixChecks.Shard788.name, stackResult852.1),
  (PrefixChecks.Shard789.name, stackResult853.1),
  (PrefixChecks.Shard790.name, stackResult854.1),
  (PrefixChecks.Shard791.name, stackResult855.1),
  (PrefixChecks.Shard792.name, stackResult856.1),
  (PrefixChecks.Shard793.name, stackResult857.1),
  (PrefixChecks.Shard794.name, stackResult858.1),
  (PrefixChecks.Shard795.name, stackResult859.1),
  (PrefixChecks.Shard796.name, stackResult860.1),
  (PrefixChecks.Shard797.name, stackResult861.1),
  (PrefixChecks.Shard798.name, stackResult862.1),
  (PrefixChecks.Shard799.name, stackResult863.1)
]

noncomputable def frames : List Nat := [
  stackResult848.2.1,
  stackResult849.2.1,
  stackResult850.2.1,
  stackResult851.2.1,
  stackResult852.2.1,
  stackResult853.2.1,
  stackResult854.2.1,
  stackResult855.2.1,
  stackResult856.2.1,
  stackResult857.2.1,
  stackResult858.2.1,
  stackResult859.2.1,
  stackResult860.2.1,
  stackResult861.2.1,
  stackResult862.2.1,
  stackResult863.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult848.2.2.1) stackResult849.2.2.1) stackResult850.2.2.1) stackResult851.2.2.1) stackResult852.2.2.1) stackResult853.2.2.1) stackResult854.2.2.1) stackResult855.2.2.1) stackResult856.2.2.1) stackResult857.2.2.1) stackResult858.2.2.1) stackResult859.2.2.1) stackResult860.2.2.1) stackResult861.2.2.1) stackResult862.2.2.1) stackResult863.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 4240) = (bodies, frames, (bitmapDelta, 4519)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult848_from _
  apply compileWordToStack_cons
  · exact stackResult849_from _
  apply compileWordToStack_cons
  · exact stackResult850_from _
  apply compileWordToStack_cons
  · exact stackResult851_from _
  apply compileWordToStack_cons
  · exact stackResult852_from _
  apply compileWordToStack_cons
  · exact stackResult853_from _
  apply compileWordToStack_cons
  · exact stackResult854_from _
  apply compileWordToStack_cons
  · exact stackResult855_from _
  apply compileWordToStack_cons
  · exact stackResult856_from _
  apply compileWordToStack_cons
  · exact stackResult857_from _
  apply compileWordToStack_cons
  · exact stackResult858_from _
  apply compileWordToStack_cons
  · exact stackResult859_from _
  apply compileWordToStack_cons
  · exact stackResult860_from _
  apply compileWordToStack_cons
  · exact stackResult861_from _
  apply compileWordToStack_cons
  · exact stackResult862_from _
  apply compileWordToStack_cons
  · exact stackResult863_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 4240) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 4519)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 4240 bodies frames bitmapDelta 4519 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 784).take 16).zip
      [oracle848, oracle849, oracle850, oracle851, oracle852, oracle853, oracle854, oracle855, oracle856, oracle857, oracle858, oracle859, oracle860, oracle861, oracle862, oracle863]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle848 PrefixChecks.Shard784.entry,
    wordFunction oracle849 PrefixChecks.Shard785.entry,
    wordFunction oracle850 PrefixChecks.Shard786.entry,
    wordFunction oracle851 PrefixChecks.Shard787.entry,
    wordFunction oracle852 PrefixChecks.Shard788.entry,
    wordFunction oracle853 PrefixChecks.Shard789.entry,
    wordFunction oracle854 PrefixChecks.Shard790.entry,
    wordFunction oracle855 PrefixChecks.Shard791.entry,
    wordFunction oracle856 PrefixChecks.Shard792.entry,
    wordFunction oracle857 PrefixChecks.Shard793.entry,
    wordFunction oracle858 PrefixChecks.Shard794.entry,
    wordFunction oracle859 PrefixChecks.Shard795.entry,
    wordFunction oracle860 PrefixChecks.Shard796.entry,
    wordFunction oracle861 PrefixChecks.Shard797.entry,
    wordFunction oracle862 PrefixChecks.Shard798.entry,
    wordFunction oracle863 PrefixChecks.Shard799.entry] = words
  simp only [
    Word848.wordFunction_eq,
    Word849.wordFunction_eq,
    Word850.wordFunction_eq,
    Word851.wordFunction_eq,
    Word852.wordFunction_eq,
    Word853.wordFunction_eq,
    Word854.wordFunction_eq,
    Word855.wordFunction_eq,
    Word856.wordFunction_eq,
    Word857.wordFunction_eq,
    Word858.wordFunction_eq,
    Word859.wordFunction_eq,
    Word860.wordFunction_eq,
    Word861.wordFunction_eq,
    Word862.wordFunction_eq,
    Word863.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk49
