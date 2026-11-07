import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word352
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word353
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word354
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word355
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word356
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word357
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word358
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word359
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word360
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word361
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word362
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word363
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word364
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word365
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word366
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word367
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk18
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult352 := WordToStack.Native.compileProgNative
  riscvConfig false Word352.program PrefixChecks.Shard288.arity registers (.nil, 1026)
theorem stackResult352_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word352.program
      PrefixChecks.Shard288.arity registers (prefixList, 1026) =
    (stackResult352.1, stackResult352.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult352.2.2.1, 1026)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word352.program
    PrefixChecks.Shard288.arity registers prefixList 1026
    stackResult352.1 stackResult352.2.1 stackResult352.2.2.1 1026 stackResult352_eq
wave8_kernel_reduce stackResult353 := WordToStack.Native.compileProgNative
  riscvConfig false Word353.program PrefixChecks.Shard289.arity registers (.nil, 1026)
theorem stackResult353_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word353.program
      PrefixChecks.Shard289.arity registers (prefixList, 1026) =
    (stackResult353.1, stackResult353.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult353.2.2.1, 1026)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word353.program
    PrefixChecks.Shard289.arity registers prefixList 1026
    stackResult353.1 stackResult353.2.1 stackResult353.2.2.1 1026 stackResult353_eq
wave8_kernel_reduce stackResult354 := WordToStack.Native.compileProgNative
  riscvConfig false Word354.program PrefixChecks.Shard290.arity registers (.nil, 1026)
theorem stackResult354_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word354.program
      PrefixChecks.Shard290.arity registers (prefixList, 1026) =
    (stackResult354.1, stackResult354.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult354.2.2.1, 1026)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word354.program
    PrefixChecks.Shard290.arity registers prefixList 1026
    stackResult354.1 stackResult354.2.1 stackResult354.2.2.1 1026 stackResult354_eq
wave8_kernel_reduce stackResult355 := WordToStack.Native.compileProgNative
  riscvConfig false Word355.program PrefixChecks.Shard291.arity registers (.nil, 1026)
theorem stackResult355_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word355.program
      PrefixChecks.Shard291.arity registers (prefixList, 1026) =
    (stackResult355.1, stackResult355.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult355.2.2.1, 1026)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word355.program
    PrefixChecks.Shard291.arity registers prefixList 1026
    stackResult355.1 stackResult355.2.1 stackResult355.2.2.1 1026 stackResult355_eq
wave8_kernel_reduce stackResult356 := WordToStack.Native.compileProgNative
  riscvConfig false Word356.program PrefixChecks.Shard292.arity registers (.nil, 1026)
theorem stackResult356_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word356.program
      PrefixChecks.Shard292.arity registers (prefixList, 1026) =
    (stackResult356.1, stackResult356.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult356.2.2.1, 1026)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word356.program
    PrefixChecks.Shard292.arity registers prefixList 1026
    stackResult356.1 stackResult356.2.1 stackResult356.2.2.1 1026 stackResult356_eq
wave8_kernel_reduce stackResult357 := WordToStack.Native.compileProgNative
  riscvConfig false Word357.program PrefixChecks.Shard293.arity registers (.nil, 1026)
theorem stackResult357_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word357.program
      PrefixChecks.Shard293.arity registers (prefixList, 1026) =
    (stackResult357.1, stackResult357.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult357.2.2.1, 1031)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word357.program
    PrefixChecks.Shard293.arity registers prefixList 1026
    stackResult357.1 stackResult357.2.1 stackResult357.2.2.1 1031 stackResult357_eq
wave8_kernel_reduce stackResult358 := WordToStack.Native.compileProgNative
  riscvConfig false Word358.program PrefixChecks.Shard294.arity registers (.nil, 1031)
theorem stackResult358_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word358.program
      PrefixChecks.Shard294.arity registers (prefixList, 1031) =
    (stackResult358.1, stackResult358.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult358.2.2.1, 1032)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word358.program
    PrefixChecks.Shard294.arity registers prefixList 1031
    stackResult358.1 stackResult358.2.1 stackResult358.2.2.1 1032 stackResult358_eq
wave8_kernel_reduce stackResult359 := WordToStack.Native.compileProgNative
  riscvConfig false Word359.program PrefixChecks.Shard295.arity registers (.nil, 1032)
theorem stackResult359_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word359.program
      PrefixChecks.Shard295.arity registers (prefixList, 1032) =
    (stackResult359.1, stackResult359.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult359.2.2.1, 1032)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word359.program
    PrefixChecks.Shard295.arity registers prefixList 1032
    stackResult359.1 stackResult359.2.1 stackResult359.2.2.1 1032 stackResult359_eq
wave8_kernel_reduce stackResult360 := WordToStack.Native.compileProgNative
  riscvConfig false Word360.program PrefixChecks.Shard296.arity registers (.nil, 1032)
theorem stackResult360_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word360.program
      PrefixChecks.Shard296.arity registers (prefixList, 1032) =
    (stackResult360.1, stackResult360.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult360.2.2.1, 1034)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word360.program
    PrefixChecks.Shard296.arity registers prefixList 1032
    stackResult360.1 stackResult360.2.1 stackResult360.2.2.1 1034 stackResult360_eq
wave8_kernel_reduce stackResult361 := WordToStack.Native.compileProgNative
  riscvConfig false Word361.program PrefixChecks.Shard297.arity registers (.nil, 1034)
theorem stackResult361_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word361.program
      PrefixChecks.Shard297.arity registers (prefixList, 1034) =
    (stackResult361.1, stackResult361.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult361.2.2.1, 1041)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word361.program
    PrefixChecks.Shard297.arity registers prefixList 1034
    stackResult361.1 stackResult361.2.1 stackResult361.2.2.1 1041 stackResult361_eq
wave8_kernel_reduce stackResult362 := WordToStack.Native.compileProgNative
  riscvConfig false Word362.program PrefixChecks.Shard298.arity registers (.nil, 1041)
theorem stackResult362_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word362.program
      PrefixChecks.Shard298.arity registers (prefixList, 1041) =
    (stackResult362.1, stackResult362.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult362.2.2.1, 1043)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word362.program
    PrefixChecks.Shard298.arity registers prefixList 1041
    stackResult362.1 stackResult362.2.1 stackResult362.2.2.1 1043 stackResult362_eq
wave8_kernel_reduce stackResult363 := WordToStack.Native.compileProgNative
  riscvConfig false Word363.program PrefixChecks.Shard299.arity registers (.nil, 1043)
theorem stackResult363_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word363.program
      PrefixChecks.Shard299.arity registers (prefixList, 1043) =
    (stackResult363.1, stackResult363.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult363.2.2.1, 1048)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word363.program
    PrefixChecks.Shard299.arity registers prefixList 1043
    stackResult363.1 stackResult363.2.1 stackResult363.2.2.1 1048 stackResult363_eq
wave8_kernel_reduce stackResult364 := WordToStack.Native.compileProgNative
  riscvConfig false Word364.program PrefixChecks.Shard300.arity registers (.nil, 1048)
theorem stackResult364_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word364.program
      PrefixChecks.Shard300.arity registers (prefixList, 1048) =
    (stackResult364.1, stackResult364.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult364.2.2.1, 1050)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word364.program
    PrefixChecks.Shard300.arity registers prefixList 1048
    stackResult364.1 stackResult364.2.1 stackResult364.2.2.1 1050 stackResult364_eq
wave8_kernel_reduce stackResult365 := WordToStack.Native.compileProgNative
  riscvConfig false Word365.program PrefixChecks.Shard301.arity registers (.nil, 1050)
theorem stackResult365_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word365.program
      PrefixChecks.Shard301.arity registers (prefixList, 1050) =
    (stackResult365.1, stackResult365.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult365.2.2.1, 1060)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word365.program
    PrefixChecks.Shard301.arity registers prefixList 1050
    stackResult365.1 stackResult365.2.1 stackResult365.2.2.1 1060 stackResult365_eq
wave8_kernel_reduce stackResult366 := WordToStack.Native.compileProgNative
  riscvConfig false Word366.program PrefixChecks.Shard302.arity registers (.nil, 1060)
theorem stackResult366_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word366.program
      PrefixChecks.Shard302.arity registers (prefixList, 1060) =
    (stackResult366.1, stackResult366.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult366.2.2.1, 1062)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word366.program
    PrefixChecks.Shard302.arity registers prefixList 1060
    stackResult366.1 stackResult366.2.1 stackResult366.2.2.1 1062 stackResult366_eq
wave8_kernel_reduce stackResult367 := WordToStack.Native.compileProgNative
  riscvConfig false Word367.program PrefixChecks.Shard303.arity registers (.nil, 1062)
theorem stackResult367_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word367.program
      PrefixChecks.Shard303.arity registers (prefixList, 1062) =
    (stackResult367.1, stackResult367.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult367.2.2.1, 1083)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word367.program
    PrefixChecks.Shard303.arity registers prefixList 1062
    stackResult367.1 stackResult367.2.1 stackResult367.2.2.1 1083 stackResult367_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard288.name, PrefixChecks.Shard288.arity, Word352.program),
  (PrefixChecks.Shard289.name, PrefixChecks.Shard289.arity, Word353.program),
  (PrefixChecks.Shard290.name, PrefixChecks.Shard290.arity, Word354.program),
  (PrefixChecks.Shard291.name, PrefixChecks.Shard291.arity, Word355.program),
  (PrefixChecks.Shard292.name, PrefixChecks.Shard292.arity, Word356.program),
  (PrefixChecks.Shard293.name, PrefixChecks.Shard293.arity, Word357.program),
  (PrefixChecks.Shard294.name, PrefixChecks.Shard294.arity, Word358.program),
  (PrefixChecks.Shard295.name, PrefixChecks.Shard295.arity, Word359.program),
  (PrefixChecks.Shard296.name, PrefixChecks.Shard296.arity, Word360.program),
  (PrefixChecks.Shard297.name, PrefixChecks.Shard297.arity, Word361.program),
  (PrefixChecks.Shard298.name, PrefixChecks.Shard298.arity, Word362.program),
  (PrefixChecks.Shard299.name, PrefixChecks.Shard299.arity, Word363.program),
  (PrefixChecks.Shard300.name, PrefixChecks.Shard300.arity, Word364.program),
  (PrefixChecks.Shard301.name, PrefixChecks.Shard301.arity, Word365.program),
  (PrefixChecks.Shard302.name, PrefixChecks.Shard302.arity, Word366.program),
  (PrefixChecks.Shard303.name, PrefixChecks.Shard303.arity, Word367.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard288.name, stackResult352.1),
  (PrefixChecks.Shard289.name, stackResult353.1),
  (PrefixChecks.Shard290.name, stackResult354.1),
  (PrefixChecks.Shard291.name, stackResult355.1),
  (PrefixChecks.Shard292.name, stackResult356.1),
  (PrefixChecks.Shard293.name, stackResult357.1),
  (PrefixChecks.Shard294.name, stackResult358.1),
  (PrefixChecks.Shard295.name, stackResult359.1),
  (PrefixChecks.Shard296.name, stackResult360.1),
  (PrefixChecks.Shard297.name, stackResult361.1),
  (PrefixChecks.Shard298.name, stackResult362.1),
  (PrefixChecks.Shard299.name, stackResult363.1),
  (PrefixChecks.Shard300.name, stackResult364.1),
  (PrefixChecks.Shard301.name, stackResult365.1),
  (PrefixChecks.Shard302.name, stackResult366.1),
  (PrefixChecks.Shard303.name, stackResult367.1)
]

noncomputable def frames : List Nat := [
  stackResult352.2.1,
  stackResult353.2.1,
  stackResult354.2.1,
  stackResult355.2.1,
  stackResult356.2.1,
  stackResult357.2.1,
  stackResult358.2.1,
  stackResult359.2.1,
  stackResult360.2.1,
  stackResult361.2.1,
  stackResult362.2.1,
  stackResult363.2.1,
  stackResult364.2.1,
  stackResult365.2.1,
  stackResult366.2.1,
  stackResult367.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult352.2.2.1) stackResult353.2.2.1) stackResult354.2.2.1) stackResult355.2.2.1) stackResult356.2.2.1) stackResult357.2.2.1) stackResult358.2.2.1) stackResult359.2.2.1) stackResult360.2.2.1) stackResult361.2.2.1) stackResult362.2.2.1) stackResult363.2.2.1) stackResult364.2.2.1) stackResult365.2.2.1) stackResult366.2.2.1) stackResult367.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 1026) = (bodies, frames, (bitmapDelta, 1083)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult352_from _
  apply compileWordToStack_cons
  · exact stackResult353_from _
  apply compileWordToStack_cons
  · exact stackResult354_from _
  apply compileWordToStack_cons
  · exact stackResult355_from _
  apply compileWordToStack_cons
  · exact stackResult356_from _
  apply compileWordToStack_cons
  · exact stackResult357_from _
  apply compileWordToStack_cons
  · exact stackResult358_from _
  apply compileWordToStack_cons
  · exact stackResult359_from _
  apply compileWordToStack_cons
  · exact stackResult360_from _
  apply compileWordToStack_cons
  · exact stackResult361_from _
  apply compileWordToStack_cons
  · exact stackResult362_from _
  apply compileWordToStack_cons
  · exact stackResult363_from _
  apply compileWordToStack_cons
  · exact stackResult364_from _
  apply compileWordToStack_cons
  · exact stackResult365_from _
  apply compileWordToStack_cons
  · exact stackResult366_from _
  apply compileWordToStack_cons
  · exact stackResult367_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 1026) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 1083)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 1026 bodies frames bitmapDelta 1083 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 288).take 16).zip
      [oracle352, oracle353, oracle354, oracle355, oracle356, oracle357, oracle358, oracle359, oracle360, oracle361, oracle362, oracle363, oracle364, oracle365, oracle366, oracle367]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle352 PrefixChecks.Shard288.entry,
    wordFunction oracle353 PrefixChecks.Shard289.entry,
    wordFunction oracle354 PrefixChecks.Shard290.entry,
    wordFunction oracle355 PrefixChecks.Shard291.entry,
    wordFunction oracle356 PrefixChecks.Shard292.entry,
    wordFunction oracle357 PrefixChecks.Shard293.entry,
    wordFunction oracle358 PrefixChecks.Shard294.entry,
    wordFunction oracle359 PrefixChecks.Shard295.entry,
    wordFunction oracle360 PrefixChecks.Shard296.entry,
    wordFunction oracle361 PrefixChecks.Shard297.entry,
    wordFunction oracle362 PrefixChecks.Shard298.entry,
    wordFunction oracle363 PrefixChecks.Shard299.entry,
    wordFunction oracle364 PrefixChecks.Shard300.entry,
    wordFunction oracle365 PrefixChecks.Shard301.entry,
    wordFunction oracle366 PrefixChecks.Shard302.entry,
    wordFunction oracle367 PrefixChecks.Shard303.entry] = words
  simp only [
    Word352.wordFunction_eq,
    Word353.wordFunction_eq,
    Word354.wordFunction_eq,
    Word355.wordFunction_eq,
    Word356.wordFunction_eq,
    Word357.wordFunction_eq,
    Word358.wordFunction_eq,
    Word359.wordFunction_eq,
    Word360.wordFunction_eq,
    Word361.wordFunction_eq,
    Word362.wordFunction_eq,
    Word363.wordFunction_eq,
    Word364.wordFunction_eq,
    Word365.wordFunction_eq,
    Word366.wordFunction_eq,
    Word367.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk18
