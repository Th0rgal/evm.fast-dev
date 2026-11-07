import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word336
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word337
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word338
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word339
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word340
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word341
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word342
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word343
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word344
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word345
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word346
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word347
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word348
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word349
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word350
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word351
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk17
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult336 := WordToStack.Native.compileProgNative
  riscvConfig false Word336.program PrefixChecks.Shard272.arity registers (.nil, 969)
theorem stackResult336_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word336.program
      PrefixChecks.Shard272.arity registers (prefixList, 969) =
    (stackResult336.1, stackResult336.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult336.2.2.1, 970)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word336.program
    PrefixChecks.Shard272.arity registers prefixList 969
    stackResult336.1 stackResult336.2.1 stackResult336.2.2.1 970 stackResult336_eq
wave8_kernel_reduce stackResult337 := WordToStack.Native.compileProgNative
  riscvConfig false Word337.program PrefixChecks.Shard273.arity registers (.nil, 970)
theorem stackResult337_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word337.program
      PrefixChecks.Shard273.arity registers (prefixList, 970) =
    (stackResult337.1, stackResult337.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult337.2.2.1, 971)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word337.program
    PrefixChecks.Shard273.arity registers prefixList 970
    stackResult337.1 stackResult337.2.1 stackResult337.2.2.1 971 stackResult337_eq
wave8_kernel_reduce stackResult338 := WordToStack.Native.compileProgNative
  riscvConfig false Word338.program PrefixChecks.Shard274.arity registers (.nil, 971)
theorem stackResult338_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word338.program
      PrefixChecks.Shard274.arity registers (prefixList, 971) =
    (stackResult338.1, stackResult338.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult338.2.2.1, 972)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word338.program
    PrefixChecks.Shard274.arity registers prefixList 971
    stackResult338.1 stackResult338.2.1 stackResult338.2.2.1 972 stackResult338_eq
wave8_kernel_reduce stackResult339 := WordToStack.Native.compileProgNative
  riscvConfig false Word339.program PrefixChecks.Shard275.arity registers (.nil, 972)
theorem stackResult339_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word339.program
      PrefixChecks.Shard275.arity registers (prefixList, 972) =
    (stackResult339.1, stackResult339.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult339.2.2.1, 973)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word339.program
    PrefixChecks.Shard275.arity registers prefixList 972
    stackResult339.1 stackResult339.2.1 stackResult339.2.2.1 973 stackResult339_eq
wave8_kernel_reduce stackResult340 := WordToStack.Native.compileProgNative
  riscvConfig false Word340.program PrefixChecks.Shard276.arity registers (.nil, 973)
theorem stackResult340_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word340.program
      PrefixChecks.Shard276.arity registers (prefixList, 973) =
    (stackResult340.1, stackResult340.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult340.2.2.1, 974)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word340.program
    PrefixChecks.Shard276.arity registers prefixList 973
    stackResult340.1 stackResult340.2.1 stackResult340.2.2.1 974 stackResult340_eq
wave8_kernel_reduce stackResult341 := WordToStack.Native.compileProgNative
  riscvConfig false Word341.program PrefixChecks.Shard277.arity registers (.nil, 974)
theorem stackResult341_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word341.program
      PrefixChecks.Shard277.arity registers (prefixList, 974) =
    (stackResult341.1, stackResult341.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult341.2.2.1, 975)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word341.program
    PrefixChecks.Shard277.arity registers prefixList 974
    stackResult341.1 stackResult341.2.1 stackResult341.2.2.1 975 stackResult341_eq
wave8_kernel_reduce stackResult342 := WordToStack.Native.compileProgNative
  riscvConfig false Word342.program PrefixChecks.Shard278.arity registers (.nil, 975)
theorem stackResult342_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word342.program
      PrefixChecks.Shard278.arity registers (prefixList, 975) =
    (stackResult342.1, stackResult342.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult342.2.2.1, 985)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word342.program
    PrefixChecks.Shard278.arity registers prefixList 975
    stackResult342.1 stackResult342.2.1 stackResult342.2.2.1 985 stackResult342_eq
wave8_kernel_reduce stackResult343 := WordToStack.Native.compileProgNative
  riscvConfig false Word343.program PrefixChecks.Shard279.arity registers (.nil, 985)
theorem stackResult343_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word343.program
      PrefixChecks.Shard279.arity registers (prefixList, 985) =
    (stackResult343.1, stackResult343.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult343.2.2.1, 989)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word343.program
    PrefixChecks.Shard279.arity registers prefixList 985
    stackResult343.1 stackResult343.2.1 stackResult343.2.2.1 989 stackResult343_eq
wave8_kernel_reduce stackResult344 := WordToStack.Native.compileProgNative
  riscvConfig false Word344.program PrefixChecks.Shard280.arity registers (.nil, 989)
theorem stackResult344_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word344.program
      PrefixChecks.Shard280.arity registers (prefixList, 989) =
    (stackResult344.1, stackResult344.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult344.2.2.1, 999)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word344.program
    PrefixChecks.Shard280.arity registers prefixList 989
    stackResult344.1 stackResult344.2.1 stackResult344.2.2.1 999 stackResult344_eq
wave8_kernel_reduce stackResult345 := WordToStack.Native.compileProgNative
  riscvConfig false Word345.program PrefixChecks.Shard281.arity registers (.nil, 999)
theorem stackResult345_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word345.program
      PrefixChecks.Shard281.arity registers (prefixList, 999) =
    (stackResult345.1, stackResult345.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult345.2.2.1, 1025)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word345.program
    PrefixChecks.Shard281.arity registers prefixList 999
    stackResult345.1 stackResult345.2.1 stackResult345.2.2.1 1025 stackResult345_eq
wave8_kernel_reduce stackResult346 := WordToStack.Native.compileProgNative
  riscvConfig false Word346.program PrefixChecks.Shard282.arity registers (.nil, 1025)
theorem stackResult346_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word346.program
      PrefixChecks.Shard282.arity registers (prefixList, 1025) =
    (stackResult346.1, stackResult346.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult346.2.2.1, 1026)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word346.program
    PrefixChecks.Shard282.arity registers prefixList 1025
    stackResult346.1 stackResult346.2.1 stackResult346.2.2.1 1026 stackResult346_eq
wave8_kernel_reduce stackResult347 := WordToStack.Native.compileProgNative
  riscvConfig false Word347.program PrefixChecks.Shard283.arity registers (.nil, 1026)
theorem stackResult347_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word347.program
      PrefixChecks.Shard283.arity registers (prefixList, 1026) =
    (stackResult347.1, stackResult347.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult347.2.2.1, 1026)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word347.program
    PrefixChecks.Shard283.arity registers prefixList 1026
    stackResult347.1 stackResult347.2.1 stackResult347.2.2.1 1026 stackResult347_eq
wave8_kernel_reduce stackResult348 := WordToStack.Native.compileProgNative
  riscvConfig false Word348.program PrefixChecks.Shard284.arity registers (.nil, 1026)
theorem stackResult348_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word348.program
      PrefixChecks.Shard284.arity registers (prefixList, 1026) =
    (stackResult348.1, stackResult348.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult348.2.2.1, 1026)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word348.program
    PrefixChecks.Shard284.arity registers prefixList 1026
    stackResult348.1 stackResult348.2.1 stackResult348.2.2.1 1026 stackResult348_eq
wave8_kernel_reduce stackResult349 := WordToStack.Native.compileProgNative
  riscvConfig false Word349.program PrefixChecks.Shard285.arity registers (.nil, 1026)
theorem stackResult349_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word349.program
      PrefixChecks.Shard285.arity registers (prefixList, 1026) =
    (stackResult349.1, stackResult349.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult349.2.2.1, 1026)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word349.program
    PrefixChecks.Shard285.arity registers prefixList 1026
    stackResult349.1 stackResult349.2.1 stackResult349.2.2.1 1026 stackResult349_eq
wave8_kernel_reduce stackResult350 := WordToStack.Native.compileProgNative
  riscvConfig false Word350.program PrefixChecks.Shard286.arity registers (.nil, 1026)
theorem stackResult350_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word350.program
      PrefixChecks.Shard286.arity registers (prefixList, 1026) =
    (stackResult350.1, stackResult350.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult350.2.2.1, 1026)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word350.program
    PrefixChecks.Shard286.arity registers prefixList 1026
    stackResult350.1 stackResult350.2.1 stackResult350.2.2.1 1026 stackResult350_eq
wave8_kernel_reduce stackResult351 := WordToStack.Native.compileProgNative
  riscvConfig false Word351.program PrefixChecks.Shard287.arity registers (.nil, 1026)
theorem stackResult351_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word351.program
      PrefixChecks.Shard287.arity registers (prefixList, 1026) =
    (stackResult351.1, stackResult351.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult351.2.2.1, 1026)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word351.program
    PrefixChecks.Shard287.arity registers prefixList 1026
    stackResult351.1 stackResult351.2.1 stackResult351.2.2.1 1026 stackResult351_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard272.name, PrefixChecks.Shard272.arity, Word336.program),
  (PrefixChecks.Shard273.name, PrefixChecks.Shard273.arity, Word337.program),
  (PrefixChecks.Shard274.name, PrefixChecks.Shard274.arity, Word338.program),
  (PrefixChecks.Shard275.name, PrefixChecks.Shard275.arity, Word339.program),
  (PrefixChecks.Shard276.name, PrefixChecks.Shard276.arity, Word340.program),
  (PrefixChecks.Shard277.name, PrefixChecks.Shard277.arity, Word341.program),
  (PrefixChecks.Shard278.name, PrefixChecks.Shard278.arity, Word342.program),
  (PrefixChecks.Shard279.name, PrefixChecks.Shard279.arity, Word343.program),
  (PrefixChecks.Shard280.name, PrefixChecks.Shard280.arity, Word344.program),
  (PrefixChecks.Shard281.name, PrefixChecks.Shard281.arity, Word345.program),
  (PrefixChecks.Shard282.name, PrefixChecks.Shard282.arity, Word346.program),
  (PrefixChecks.Shard283.name, PrefixChecks.Shard283.arity, Word347.program),
  (PrefixChecks.Shard284.name, PrefixChecks.Shard284.arity, Word348.program),
  (PrefixChecks.Shard285.name, PrefixChecks.Shard285.arity, Word349.program),
  (PrefixChecks.Shard286.name, PrefixChecks.Shard286.arity, Word350.program),
  (PrefixChecks.Shard287.name, PrefixChecks.Shard287.arity, Word351.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard272.name, stackResult336.1),
  (PrefixChecks.Shard273.name, stackResult337.1),
  (PrefixChecks.Shard274.name, stackResult338.1),
  (PrefixChecks.Shard275.name, stackResult339.1),
  (PrefixChecks.Shard276.name, stackResult340.1),
  (PrefixChecks.Shard277.name, stackResult341.1),
  (PrefixChecks.Shard278.name, stackResult342.1),
  (PrefixChecks.Shard279.name, stackResult343.1),
  (PrefixChecks.Shard280.name, stackResult344.1),
  (PrefixChecks.Shard281.name, stackResult345.1),
  (PrefixChecks.Shard282.name, stackResult346.1),
  (PrefixChecks.Shard283.name, stackResult347.1),
  (PrefixChecks.Shard284.name, stackResult348.1),
  (PrefixChecks.Shard285.name, stackResult349.1),
  (PrefixChecks.Shard286.name, stackResult350.1),
  (PrefixChecks.Shard287.name, stackResult351.1)
]

noncomputable def frames : List Nat := [
  stackResult336.2.1,
  stackResult337.2.1,
  stackResult338.2.1,
  stackResult339.2.1,
  stackResult340.2.1,
  stackResult341.2.1,
  stackResult342.2.1,
  stackResult343.2.1,
  stackResult344.2.1,
  stackResult345.2.1,
  stackResult346.2.1,
  stackResult347.2.1,
  stackResult348.2.1,
  stackResult349.2.1,
  stackResult350.2.1,
  stackResult351.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult336.2.2.1) stackResult337.2.2.1) stackResult338.2.2.1) stackResult339.2.2.1) stackResult340.2.2.1) stackResult341.2.2.1) stackResult342.2.2.1) stackResult343.2.2.1) stackResult344.2.2.1) stackResult345.2.2.1) stackResult346.2.2.1) stackResult347.2.2.1) stackResult348.2.2.1) stackResult349.2.2.1) stackResult350.2.2.1) stackResult351.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 969) = (bodies, frames, (bitmapDelta, 1026)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult336_from _
  apply compileWordToStack_cons
  · exact stackResult337_from _
  apply compileWordToStack_cons
  · exact stackResult338_from _
  apply compileWordToStack_cons
  · exact stackResult339_from _
  apply compileWordToStack_cons
  · exact stackResult340_from _
  apply compileWordToStack_cons
  · exact stackResult341_from _
  apply compileWordToStack_cons
  · exact stackResult342_from _
  apply compileWordToStack_cons
  · exact stackResult343_from _
  apply compileWordToStack_cons
  · exact stackResult344_from _
  apply compileWordToStack_cons
  · exact stackResult345_from _
  apply compileWordToStack_cons
  · exact stackResult346_from _
  apply compileWordToStack_cons
  · exact stackResult347_from _
  apply compileWordToStack_cons
  · exact stackResult348_from _
  apply compileWordToStack_cons
  · exact stackResult349_from _
  apply compileWordToStack_cons
  · exact stackResult350_from _
  apply compileWordToStack_cons
  · exact stackResult351_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 969) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 1026)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 969 bodies frames bitmapDelta 1026 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 272).take 16).zip
      [oracle336, oracle337, oracle338, oracle339, oracle340, oracle341, oracle342, oracle343, oracle344, oracle345, oracle346, oracle347, oracle348, oracle349, oracle350, oracle351]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle336 PrefixChecks.Shard272.entry,
    wordFunction oracle337 PrefixChecks.Shard273.entry,
    wordFunction oracle338 PrefixChecks.Shard274.entry,
    wordFunction oracle339 PrefixChecks.Shard275.entry,
    wordFunction oracle340 PrefixChecks.Shard276.entry,
    wordFunction oracle341 PrefixChecks.Shard277.entry,
    wordFunction oracle342 PrefixChecks.Shard278.entry,
    wordFunction oracle343 PrefixChecks.Shard279.entry,
    wordFunction oracle344 PrefixChecks.Shard280.entry,
    wordFunction oracle345 PrefixChecks.Shard281.entry,
    wordFunction oracle346 PrefixChecks.Shard282.entry,
    wordFunction oracle347 PrefixChecks.Shard283.entry,
    wordFunction oracle348 PrefixChecks.Shard284.entry,
    wordFunction oracle349 PrefixChecks.Shard285.entry,
    wordFunction oracle350 PrefixChecks.Shard286.entry,
    wordFunction oracle351 PrefixChecks.Shard287.entry] = words
  simp only [
    Word336.wordFunction_eq,
    Word337.wordFunction_eq,
    Word338.wordFunction_eq,
    Word339.wordFunction_eq,
    Word340.wordFunction_eq,
    Word341.wordFunction_eq,
    Word342.wordFunction_eq,
    Word343.wordFunction_eq,
    Word344.wordFunction_eq,
    Word345.wordFunction_eq,
    Word346.wordFunction_eq,
    Word347.wordFunction_eq,
    Word348.wordFunction_eq,
    Word349.wordFunction_eq,
    Word350.wordFunction_eq,
    Word351.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk17
