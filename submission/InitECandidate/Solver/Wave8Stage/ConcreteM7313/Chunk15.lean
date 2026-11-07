import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word304
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word305
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word306
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word307
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word308
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word309
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word310
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word311
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word312
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word313
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word314
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word315
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word316
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word317
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word318
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word319
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk15
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult304 := WordToStack.Native.compileProgNative
  riscvConfig false Word304.program PrefixChecks.Shard240.arity registers (.nil, 834)
theorem stackResult304_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word304.program
      PrefixChecks.Shard240.arity registers (prefixList, 834) =
    (stackResult304.1, stackResult304.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult304.2.2.1, 838)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word304.program
    PrefixChecks.Shard240.arity registers prefixList 834
    stackResult304.1 stackResult304.2.1 stackResult304.2.2.1 838 stackResult304_eq
wave8_kernel_reduce stackResult305 := WordToStack.Native.compileProgNative
  riscvConfig false Word305.program PrefixChecks.Shard241.arity registers (.nil, 838)
theorem stackResult305_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word305.program
      PrefixChecks.Shard241.arity registers (prefixList, 838) =
    (stackResult305.1, stackResult305.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult305.2.2.1, 844)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word305.program
    PrefixChecks.Shard241.arity registers prefixList 838
    stackResult305.1 stackResult305.2.1 stackResult305.2.2.1 844 stackResult305_eq
wave8_kernel_reduce stackResult306 := WordToStack.Native.compileProgNative
  riscvConfig false Word306.program PrefixChecks.Shard242.arity registers (.nil, 844)
theorem stackResult306_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word306.program
      PrefixChecks.Shard242.arity registers (prefixList, 844) =
    (stackResult306.1, stackResult306.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult306.2.2.1, 847)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word306.program
    PrefixChecks.Shard242.arity registers prefixList 844
    stackResult306.1 stackResult306.2.1 stackResult306.2.2.1 847 stackResult306_eq
wave8_kernel_reduce stackResult307 := WordToStack.Native.compileProgNative
  riscvConfig false Word307.program PrefixChecks.Shard243.arity registers (.nil, 847)
theorem stackResult307_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word307.program
      PrefixChecks.Shard243.arity registers (prefixList, 847) =
    (stackResult307.1, stackResult307.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult307.2.2.1, 848)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word307.program
    PrefixChecks.Shard243.arity registers prefixList 847
    stackResult307.1 stackResult307.2.1 stackResult307.2.2.1 848 stackResult307_eq
wave8_kernel_reduce stackResult308 := WordToStack.Native.compileProgNative
  riscvConfig false Word308.program PrefixChecks.Shard244.arity registers (.nil, 848)
theorem stackResult308_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word308.program
      PrefixChecks.Shard244.arity registers (prefixList, 848) =
    (stackResult308.1, stackResult308.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult308.2.2.1, 849)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word308.program
    PrefixChecks.Shard244.arity registers prefixList 848
    stackResult308.1 stackResult308.2.1 stackResult308.2.2.1 849 stackResult308_eq
wave8_kernel_reduce stackResult309 := WordToStack.Native.compileProgNative
  riscvConfig false Word309.program PrefixChecks.Shard245.arity registers (.nil, 849)
theorem stackResult309_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word309.program
      PrefixChecks.Shard245.arity registers (prefixList, 849) =
    (stackResult309.1, stackResult309.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult309.2.2.1, 850)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word309.program
    PrefixChecks.Shard245.arity registers prefixList 849
    stackResult309.1 stackResult309.2.1 stackResult309.2.2.1 850 stackResult309_eq
wave8_kernel_reduce stackResult310 := WordToStack.Native.compileProgNative
  riscvConfig false Word310.program PrefixChecks.Shard246.arity registers (.nil, 850)
theorem stackResult310_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word310.program
      PrefixChecks.Shard246.arity registers (prefixList, 850) =
    (stackResult310.1, stackResult310.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult310.2.2.1, 855)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word310.program
    PrefixChecks.Shard246.arity registers prefixList 850
    stackResult310.1 stackResult310.2.1 stackResult310.2.2.1 855 stackResult310_eq
wave8_kernel_reduce stackResult311 := WordToStack.Native.compileProgNative
  riscvConfig false Word311.program PrefixChecks.Shard247.arity registers (.nil, 855)
theorem stackResult311_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word311.program
      PrefixChecks.Shard247.arity registers (prefixList, 855) =
    (stackResult311.1, stackResult311.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult311.2.2.1, 859)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word311.program
    PrefixChecks.Shard247.arity registers prefixList 855
    stackResult311.1 stackResult311.2.1 stackResult311.2.2.1 859 stackResult311_eq
wave8_kernel_reduce stackResult312 := WordToStack.Native.compileProgNative
  riscvConfig false Word312.program PrefixChecks.Shard248.arity registers (.nil, 859)
theorem stackResult312_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word312.program
      PrefixChecks.Shard248.arity registers (prefixList, 859) =
    (stackResult312.1, stackResult312.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult312.2.2.1, 862)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word312.program
    PrefixChecks.Shard248.arity registers prefixList 859
    stackResult312.1 stackResult312.2.1 stackResult312.2.2.1 862 stackResult312_eq
wave8_kernel_reduce stackResult313 := WordToStack.Native.compileProgNative
  riscvConfig false Word313.program PrefixChecks.Shard249.arity registers (.nil, 862)
theorem stackResult313_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word313.program
      PrefixChecks.Shard249.arity registers (prefixList, 862) =
    (stackResult313.1, stackResult313.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult313.2.2.1, 865)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word313.program
    PrefixChecks.Shard249.arity registers prefixList 862
    stackResult313.1 stackResult313.2.1 stackResult313.2.2.1 865 stackResult313_eq
wave8_kernel_reduce stackResult314 := WordToStack.Native.compileProgNative
  riscvConfig false Word314.program PrefixChecks.Shard250.arity registers (.nil, 865)
theorem stackResult314_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word314.program
      PrefixChecks.Shard250.arity registers (prefixList, 865) =
    (stackResult314.1, stackResult314.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult314.2.2.1, 869)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word314.program
    PrefixChecks.Shard250.arity registers prefixList 865
    stackResult314.1 stackResult314.2.1 stackResult314.2.2.1 869 stackResult314_eq
wave8_kernel_reduce stackResult315 := WordToStack.Native.compileProgNative
  riscvConfig false Word315.program PrefixChecks.Shard251.arity registers (.nil, 869)
theorem stackResult315_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word315.program
      PrefixChecks.Shard251.arity registers (prefixList, 869) =
    (stackResult315.1, stackResult315.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult315.2.2.1, 876)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word315.program
    PrefixChecks.Shard251.arity registers prefixList 869
    stackResult315.1 stackResult315.2.1 stackResult315.2.2.1 876 stackResult315_eq
wave8_kernel_reduce stackResult316 := WordToStack.Native.compileProgNative
  riscvConfig false Word316.program PrefixChecks.Shard252.arity registers (.nil, 876)
theorem stackResult316_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word316.program
      PrefixChecks.Shard252.arity registers (prefixList, 876) =
    (stackResult316.1, stackResult316.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult316.2.2.1, 880)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word316.program
    PrefixChecks.Shard252.arity registers prefixList 876
    stackResult316.1 stackResult316.2.1 stackResult316.2.2.1 880 stackResult316_eq
wave8_kernel_reduce stackResult317 := WordToStack.Native.compileProgNative
  riscvConfig false Word317.program PrefixChecks.Shard253.arity registers (.nil, 880)
theorem stackResult317_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word317.program
      PrefixChecks.Shard253.arity registers (prefixList, 880) =
    (stackResult317.1, stackResult317.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult317.2.2.1, 882)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word317.program
    PrefixChecks.Shard253.arity registers prefixList 880
    stackResult317.1 stackResult317.2.1 stackResult317.2.2.1 882 stackResult317_eq
wave8_kernel_reduce stackResult318 := WordToStack.Native.compileProgNative
  riscvConfig false Word318.program PrefixChecks.Shard254.arity registers (.nil, 882)
theorem stackResult318_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word318.program
      PrefixChecks.Shard254.arity registers (prefixList, 882) =
    (stackResult318.1, stackResult318.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult318.2.2.1, 891)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word318.program
    PrefixChecks.Shard254.arity registers prefixList 882
    stackResult318.1 stackResult318.2.1 stackResult318.2.2.1 891 stackResult318_eq
wave8_kernel_reduce stackResult319 := WordToStack.Native.compileProgNative
  riscvConfig false Word319.program PrefixChecks.Shard255.arity registers (.nil, 891)
theorem stackResult319_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word319.program
      PrefixChecks.Shard255.arity registers (prefixList, 891) =
    (stackResult319.1, stackResult319.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult319.2.2.1, 895)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word319.program
    PrefixChecks.Shard255.arity registers prefixList 891
    stackResult319.1 stackResult319.2.1 stackResult319.2.2.1 895 stackResult319_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard240.name, PrefixChecks.Shard240.arity, Word304.program),
  (PrefixChecks.Shard241.name, PrefixChecks.Shard241.arity, Word305.program),
  (PrefixChecks.Shard242.name, PrefixChecks.Shard242.arity, Word306.program),
  (PrefixChecks.Shard243.name, PrefixChecks.Shard243.arity, Word307.program),
  (PrefixChecks.Shard244.name, PrefixChecks.Shard244.arity, Word308.program),
  (PrefixChecks.Shard245.name, PrefixChecks.Shard245.arity, Word309.program),
  (PrefixChecks.Shard246.name, PrefixChecks.Shard246.arity, Word310.program),
  (PrefixChecks.Shard247.name, PrefixChecks.Shard247.arity, Word311.program),
  (PrefixChecks.Shard248.name, PrefixChecks.Shard248.arity, Word312.program),
  (PrefixChecks.Shard249.name, PrefixChecks.Shard249.arity, Word313.program),
  (PrefixChecks.Shard250.name, PrefixChecks.Shard250.arity, Word314.program),
  (PrefixChecks.Shard251.name, PrefixChecks.Shard251.arity, Word315.program),
  (PrefixChecks.Shard252.name, PrefixChecks.Shard252.arity, Word316.program),
  (PrefixChecks.Shard253.name, PrefixChecks.Shard253.arity, Word317.program),
  (PrefixChecks.Shard254.name, PrefixChecks.Shard254.arity, Word318.program),
  (PrefixChecks.Shard255.name, PrefixChecks.Shard255.arity, Word319.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard240.name, stackResult304.1),
  (PrefixChecks.Shard241.name, stackResult305.1),
  (PrefixChecks.Shard242.name, stackResult306.1),
  (PrefixChecks.Shard243.name, stackResult307.1),
  (PrefixChecks.Shard244.name, stackResult308.1),
  (PrefixChecks.Shard245.name, stackResult309.1),
  (PrefixChecks.Shard246.name, stackResult310.1),
  (PrefixChecks.Shard247.name, stackResult311.1),
  (PrefixChecks.Shard248.name, stackResult312.1),
  (PrefixChecks.Shard249.name, stackResult313.1),
  (PrefixChecks.Shard250.name, stackResult314.1),
  (PrefixChecks.Shard251.name, stackResult315.1),
  (PrefixChecks.Shard252.name, stackResult316.1),
  (PrefixChecks.Shard253.name, stackResult317.1),
  (PrefixChecks.Shard254.name, stackResult318.1),
  (PrefixChecks.Shard255.name, stackResult319.1)
]

noncomputable def frames : List Nat := [
  stackResult304.2.1,
  stackResult305.2.1,
  stackResult306.2.1,
  stackResult307.2.1,
  stackResult308.2.1,
  stackResult309.2.1,
  stackResult310.2.1,
  stackResult311.2.1,
  stackResult312.2.1,
  stackResult313.2.1,
  stackResult314.2.1,
  stackResult315.2.1,
  stackResult316.2.1,
  stackResult317.2.1,
  stackResult318.2.1,
  stackResult319.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult304.2.2.1) stackResult305.2.2.1) stackResult306.2.2.1) stackResult307.2.2.1) stackResult308.2.2.1) stackResult309.2.2.1) stackResult310.2.2.1) stackResult311.2.2.1) stackResult312.2.2.1) stackResult313.2.2.1) stackResult314.2.2.1) stackResult315.2.2.1) stackResult316.2.2.1) stackResult317.2.2.1) stackResult318.2.2.1) stackResult319.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 834) = (bodies, frames, (bitmapDelta, 895)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult304_from _
  apply compileWordToStack_cons
  · exact stackResult305_from _
  apply compileWordToStack_cons
  · exact stackResult306_from _
  apply compileWordToStack_cons
  · exact stackResult307_from _
  apply compileWordToStack_cons
  · exact stackResult308_from _
  apply compileWordToStack_cons
  · exact stackResult309_from _
  apply compileWordToStack_cons
  · exact stackResult310_from _
  apply compileWordToStack_cons
  · exact stackResult311_from _
  apply compileWordToStack_cons
  · exact stackResult312_from _
  apply compileWordToStack_cons
  · exact stackResult313_from _
  apply compileWordToStack_cons
  · exact stackResult314_from _
  apply compileWordToStack_cons
  · exact stackResult315_from _
  apply compileWordToStack_cons
  · exact stackResult316_from _
  apply compileWordToStack_cons
  · exact stackResult317_from _
  apply compileWordToStack_cons
  · exact stackResult318_from _
  apply compileWordToStack_cons
  · exact stackResult319_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 834) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 895)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 834 bodies frames bitmapDelta 895 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 240).take 16).zip
      [oracle304, oracle305, oracle306, oracle307, oracle308, oracle309, oracle310, oracle311, oracle312, oracle313, oracle314, oracle315, oracle316, oracle317, oracle318, oracle319]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle304 PrefixChecks.Shard240.entry,
    wordFunction oracle305 PrefixChecks.Shard241.entry,
    wordFunction oracle306 PrefixChecks.Shard242.entry,
    wordFunction oracle307 PrefixChecks.Shard243.entry,
    wordFunction oracle308 PrefixChecks.Shard244.entry,
    wordFunction oracle309 PrefixChecks.Shard245.entry,
    wordFunction oracle310 PrefixChecks.Shard246.entry,
    wordFunction oracle311 PrefixChecks.Shard247.entry,
    wordFunction oracle312 PrefixChecks.Shard248.entry,
    wordFunction oracle313 PrefixChecks.Shard249.entry,
    wordFunction oracle314 PrefixChecks.Shard250.entry,
    wordFunction oracle315 PrefixChecks.Shard251.entry,
    wordFunction oracle316 PrefixChecks.Shard252.entry,
    wordFunction oracle317 PrefixChecks.Shard253.entry,
    wordFunction oracle318 PrefixChecks.Shard254.entry,
    wordFunction oracle319 PrefixChecks.Shard255.entry] = words
  simp only [
    Word304.wordFunction_eq,
    Word305.wordFunction_eq,
    Word306.wordFunction_eq,
    Word307.wordFunction_eq,
    Word308.wordFunction_eq,
    Word309.wordFunction_eq,
    Word310.wordFunction_eq,
    Word311.wordFunction_eq,
    Word312.wordFunction_eq,
    Word313.wordFunction_eq,
    Word314.wordFunction_eq,
    Word315.wordFunction_eq,
    Word316.wordFunction_eq,
    Word317.wordFunction_eq,
    Word318.wordFunction_eq,
    Word319.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk15
