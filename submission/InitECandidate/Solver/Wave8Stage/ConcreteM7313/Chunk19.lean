import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word368
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word369
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word370
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word371
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word372
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word373
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word374
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word375
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word376
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word377
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word378
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word379
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word380
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word381
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word382
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word383
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk19
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult368 := WordToStack.Native.compileProgNative
  riscvConfig false Word368.program PrefixChecks.Shard304.arity registers (.nil, 1083)
theorem stackResult368_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word368.program
      PrefixChecks.Shard304.arity registers (prefixList, 1083) =
    (stackResult368.1, stackResult368.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult368.2.2.1, 1083)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word368.program
    PrefixChecks.Shard304.arity registers prefixList 1083
    stackResult368.1 stackResult368.2.1 stackResult368.2.2.1 1083 stackResult368_eq
wave8_kernel_reduce stackResult369 := WordToStack.Native.compileProgNative
  riscvConfig false Word369.program PrefixChecks.Shard305.arity registers (.nil, 1083)
theorem stackResult369_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word369.program
      PrefixChecks.Shard305.arity registers (prefixList, 1083) =
    (stackResult369.1, stackResult369.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult369.2.2.1, 1084)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word369.program
    PrefixChecks.Shard305.arity registers prefixList 1083
    stackResult369.1 stackResult369.2.1 stackResult369.2.2.1 1084 stackResult369_eq
wave8_kernel_reduce stackResult370 := WordToStack.Native.compileProgNative
  riscvConfig false Word370.program PrefixChecks.Shard306.arity registers (.nil, 1084)
theorem stackResult370_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word370.program
      PrefixChecks.Shard306.arity registers (prefixList, 1084) =
    (stackResult370.1, stackResult370.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult370.2.2.1, 1088)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word370.program
    PrefixChecks.Shard306.arity registers prefixList 1084
    stackResult370.1 stackResult370.2.1 stackResult370.2.2.1 1088 stackResult370_eq
wave8_kernel_reduce stackResult371 := WordToStack.Native.compileProgNative
  riscvConfig false Word371.program PrefixChecks.Shard307.arity registers (.nil, 1088)
theorem stackResult371_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word371.program
      PrefixChecks.Shard307.arity registers (prefixList, 1088) =
    (stackResult371.1, stackResult371.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult371.2.2.1, 1088)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word371.program
    PrefixChecks.Shard307.arity registers prefixList 1088
    stackResult371.1 stackResult371.2.1 stackResult371.2.2.1 1088 stackResult371_eq
wave8_kernel_reduce stackResult372 := WordToStack.Native.compileProgNative
  riscvConfig false Word372.program PrefixChecks.Shard308.arity registers (.nil, 1088)
theorem stackResult372_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word372.program
      PrefixChecks.Shard308.arity registers (prefixList, 1088) =
    (stackResult372.1, stackResult372.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult372.2.2.1, 1088)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word372.program
    PrefixChecks.Shard308.arity registers prefixList 1088
    stackResult372.1 stackResult372.2.1 stackResult372.2.2.1 1088 stackResult372_eq
wave8_kernel_reduce stackResult373 := WordToStack.Native.compileProgNative
  riscvConfig false Word373.program PrefixChecks.Shard309.arity registers (.nil, 1088)
theorem stackResult373_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word373.program
      PrefixChecks.Shard309.arity registers (prefixList, 1088) =
    (stackResult373.1, stackResult373.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult373.2.2.1, 1088)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word373.program
    PrefixChecks.Shard309.arity registers prefixList 1088
    stackResult373.1 stackResult373.2.1 stackResult373.2.2.1 1088 stackResult373_eq
wave8_kernel_reduce stackResult374 := WordToStack.Native.compileProgNative
  riscvConfig false Word374.program PrefixChecks.Shard310.arity registers (.nil, 1088)
theorem stackResult374_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word374.program
      PrefixChecks.Shard310.arity registers (prefixList, 1088) =
    (stackResult374.1, stackResult374.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult374.2.2.1, 1088)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word374.program
    PrefixChecks.Shard310.arity registers prefixList 1088
    stackResult374.1 stackResult374.2.1 stackResult374.2.2.1 1088 stackResult374_eq
wave8_kernel_reduce stackResult375 := WordToStack.Native.compileProgNative
  riscvConfig false Word375.program PrefixChecks.Shard311.arity registers (.nil, 1088)
theorem stackResult375_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word375.program
      PrefixChecks.Shard311.arity registers (prefixList, 1088) =
    (stackResult375.1, stackResult375.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult375.2.2.1, 1088)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word375.program
    PrefixChecks.Shard311.arity registers prefixList 1088
    stackResult375.1 stackResult375.2.1 stackResult375.2.2.1 1088 stackResult375_eq
wave8_kernel_reduce stackResult376 := WordToStack.Native.compileProgNative
  riscvConfig false Word376.program PrefixChecks.Shard312.arity registers (.nil, 1088)
theorem stackResult376_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word376.program
      PrefixChecks.Shard312.arity registers (prefixList, 1088) =
    (stackResult376.1, stackResult376.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult376.2.2.1, 1088)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word376.program
    PrefixChecks.Shard312.arity registers prefixList 1088
    stackResult376.1 stackResult376.2.1 stackResult376.2.2.1 1088 stackResult376_eq
wave8_kernel_reduce stackResult377 := WordToStack.Native.compileProgNative
  riscvConfig false Word377.program PrefixChecks.Shard313.arity registers (.nil, 1088)
theorem stackResult377_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word377.program
      PrefixChecks.Shard313.arity registers (prefixList, 1088) =
    (stackResult377.1, stackResult377.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult377.2.2.1, 1092)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word377.program
    PrefixChecks.Shard313.arity registers prefixList 1088
    stackResult377.1 stackResult377.2.1 stackResult377.2.2.1 1092 stackResult377_eq
wave8_kernel_reduce stackResult378 := WordToStack.Native.compileProgNative
  riscvConfig false Word378.program PrefixChecks.Shard314.arity registers (.nil, 1092)
theorem stackResult378_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word378.program
      PrefixChecks.Shard314.arity registers (prefixList, 1092) =
    (stackResult378.1, stackResult378.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult378.2.2.1, 1108)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word378.program
    PrefixChecks.Shard314.arity registers prefixList 1092
    stackResult378.1 stackResult378.2.1 stackResult378.2.2.1 1108 stackResult378_eq
wave8_kernel_reduce stackResult379 := WordToStack.Native.compileProgNative
  riscvConfig false Word379.program PrefixChecks.Shard315.arity registers (.nil, 1108)
theorem stackResult379_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word379.program
      PrefixChecks.Shard315.arity registers (prefixList, 1108) =
    (stackResult379.1, stackResult379.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult379.2.2.1, 1113)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word379.program
    PrefixChecks.Shard315.arity registers prefixList 1108
    stackResult379.1 stackResult379.2.1 stackResult379.2.2.1 1113 stackResult379_eq
wave8_kernel_reduce stackResult380 := WordToStack.Native.compileProgNative
  riscvConfig false Word380.program PrefixChecks.Shard316.arity registers (.nil, 1113)
theorem stackResult380_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word380.program
      PrefixChecks.Shard316.arity registers (prefixList, 1113) =
    (stackResult380.1, stackResult380.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult380.2.2.1, 1118)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word380.program
    PrefixChecks.Shard316.arity registers prefixList 1113
    stackResult380.1 stackResult380.2.1 stackResult380.2.2.1 1118 stackResult380_eq
wave8_kernel_reduce stackResult381 := WordToStack.Native.compileProgNative
  riscvConfig false Word381.program PrefixChecks.Shard317.arity registers (.nil, 1118)
theorem stackResult381_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word381.program
      PrefixChecks.Shard317.arity registers (prefixList, 1118) =
    (stackResult381.1, stackResult381.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult381.2.2.1, 1124)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word381.program
    PrefixChecks.Shard317.arity registers prefixList 1118
    stackResult381.1 stackResult381.2.1 stackResult381.2.2.1 1124 stackResult381_eq
wave8_kernel_reduce stackResult382 := WordToStack.Native.compileProgNative
  riscvConfig false Word382.program PrefixChecks.Shard318.arity registers (.nil, 1124)
theorem stackResult382_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word382.program
      PrefixChecks.Shard318.arity registers (prefixList, 1124) =
    (stackResult382.1, stackResult382.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult382.2.2.1, 1129)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word382.program
    PrefixChecks.Shard318.arity registers prefixList 1124
    stackResult382.1 stackResult382.2.1 stackResult382.2.2.1 1129 stackResult382_eq
wave8_kernel_reduce stackResult383 := WordToStack.Native.compileProgNative
  riscvConfig false Word383.program PrefixChecks.Shard319.arity registers (.nil, 1129)
theorem stackResult383_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word383.program
      PrefixChecks.Shard319.arity registers (prefixList, 1129) =
    (stackResult383.1, stackResult383.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult383.2.2.1, 1129)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word383.program
    PrefixChecks.Shard319.arity registers prefixList 1129
    stackResult383.1 stackResult383.2.1 stackResult383.2.2.1 1129 stackResult383_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard304.name, PrefixChecks.Shard304.arity, Word368.program),
  (PrefixChecks.Shard305.name, PrefixChecks.Shard305.arity, Word369.program),
  (PrefixChecks.Shard306.name, PrefixChecks.Shard306.arity, Word370.program),
  (PrefixChecks.Shard307.name, PrefixChecks.Shard307.arity, Word371.program),
  (PrefixChecks.Shard308.name, PrefixChecks.Shard308.arity, Word372.program),
  (PrefixChecks.Shard309.name, PrefixChecks.Shard309.arity, Word373.program),
  (PrefixChecks.Shard310.name, PrefixChecks.Shard310.arity, Word374.program),
  (PrefixChecks.Shard311.name, PrefixChecks.Shard311.arity, Word375.program),
  (PrefixChecks.Shard312.name, PrefixChecks.Shard312.arity, Word376.program),
  (PrefixChecks.Shard313.name, PrefixChecks.Shard313.arity, Word377.program),
  (PrefixChecks.Shard314.name, PrefixChecks.Shard314.arity, Word378.program),
  (PrefixChecks.Shard315.name, PrefixChecks.Shard315.arity, Word379.program),
  (PrefixChecks.Shard316.name, PrefixChecks.Shard316.arity, Word380.program),
  (PrefixChecks.Shard317.name, PrefixChecks.Shard317.arity, Word381.program),
  (PrefixChecks.Shard318.name, PrefixChecks.Shard318.arity, Word382.program),
  (PrefixChecks.Shard319.name, PrefixChecks.Shard319.arity, Word383.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard304.name, stackResult368.1),
  (PrefixChecks.Shard305.name, stackResult369.1),
  (PrefixChecks.Shard306.name, stackResult370.1),
  (PrefixChecks.Shard307.name, stackResult371.1),
  (PrefixChecks.Shard308.name, stackResult372.1),
  (PrefixChecks.Shard309.name, stackResult373.1),
  (PrefixChecks.Shard310.name, stackResult374.1),
  (PrefixChecks.Shard311.name, stackResult375.1),
  (PrefixChecks.Shard312.name, stackResult376.1),
  (PrefixChecks.Shard313.name, stackResult377.1),
  (PrefixChecks.Shard314.name, stackResult378.1),
  (PrefixChecks.Shard315.name, stackResult379.1),
  (PrefixChecks.Shard316.name, stackResult380.1),
  (PrefixChecks.Shard317.name, stackResult381.1),
  (PrefixChecks.Shard318.name, stackResult382.1),
  (PrefixChecks.Shard319.name, stackResult383.1)
]

noncomputable def frames : List Nat := [
  stackResult368.2.1,
  stackResult369.2.1,
  stackResult370.2.1,
  stackResult371.2.1,
  stackResult372.2.1,
  stackResult373.2.1,
  stackResult374.2.1,
  stackResult375.2.1,
  stackResult376.2.1,
  stackResult377.2.1,
  stackResult378.2.1,
  stackResult379.2.1,
  stackResult380.2.1,
  stackResult381.2.1,
  stackResult382.2.1,
  stackResult383.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult368.2.2.1) stackResult369.2.2.1) stackResult370.2.2.1) stackResult371.2.2.1) stackResult372.2.2.1) stackResult373.2.2.1) stackResult374.2.2.1) stackResult375.2.2.1) stackResult376.2.2.1) stackResult377.2.2.1) stackResult378.2.2.1) stackResult379.2.2.1) stackResult380.2.2.1) stackResult381.2.2.1) stackResult382.2.2.1) stackResult383.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 1083) = (bodies, frames, (bitmapDelta, 1129)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult368_from _
  apply compileWordToStack_cons
  · exact stackResult369_from _
  apply compileWordToStack_cons
  · exact stackResult370_from _
  apply compileWordToStack_cons
  · exact stackResult371_from _
  apply compileWordToStack_cons
  · exact stackResult372_from _
  apply compileWordToStack_cons
  · exact stackResult373_from _
  apply compileWordToStack_cons
  · exact stackResult374_from _
  apply compileWordToStack_cons
  · exact stackResult375_from _
  apply compileWordToStack_cons
  · exact stackResult376_from _
  apply compileWordToStack_cons
  · exact stackResult377_from _
  apply compileWordToStack_cons
  · exact stackResult378_from _
  apply compileWordToStack_cons
  · exact stackResult379_from _
  apply compileWordToStack_cons
  · exact stackResult380_from _
  apply compileWordToStack_cons
  · exact stackResult381_from _
  apply compileWordToStack_cons
  · exact stackResult382_from _
  apply compileWordToStack_cons
  · exact stackResult383_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 1083) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 1129)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 1083 bodies frames bitmapDelta 1129 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 304).take 16).zip
      [oracle368, oracle369, oracle370, oracle371, oracle372, oracle373, oracle374, oracle375, oracle376, oracle377, oracle378, oracle379, oracle380, oracle381, oracle382, oracle383]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle368 PrefixChecks.Shard304.entry,
    wordFunction oracle369 PrefixChecks.Shard305.entry,
    wordFunction oracle370 PrefixChecks.Shard306.entry,
    wordFunction oracle371 PrefixChecks.Shard307.entry,
    wordFunction oracle372 PrefixChecks.Shard308.entry,
    wordFunction oracle373 PrefixChecks.Shard309.entry,
    wordFunction oracle374 PrefixChecks.Shard310.entry,
    wordFunction oracle375 PrefixChecks.Shard311.entry,
    wordFunction oracle376 PrefixChecks.Shard312.entry,
    wordFunction oracle377 PrefixChecks.Shard313.entry,
    wordFunction oracle378 PrefixChecks.Shard314.entry,
    wordFunction oracle379 PrefixChecks.Shard315.entry,
    wordFunction oracle380 PrefixChecks.Shard316.entry,
    wordFunction oracle381 PrefixChecks.Shard317.entry,
    wordFunction oracle382 PrefixChecks.Shard318.entry,
    wordFunction oracle383 PrefixChecks.Shard319.entry] = words
  simp only [
    Word368.wordFunction_eq,
    Word369.wordFunction_eq,
    Word370.wordFunction_eq,
    Word371.wordFunction_eq,
    Word372.wordFunction_eq,
    Word373.wordFunction_eq,
    Word374.wordFunction_eq,
    Word375.wordFunction_eq,
    Word376.wordFunction_eq,
    Word377.wordFunction_eq,
    Word378.wordFunction_eq,
    Word379.wordFunction_eq,
    Word380.wordFunction_eq,
    Word381.wordFunction_eq,
    Word382.wordFunction_eq,
    Word383.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk19
