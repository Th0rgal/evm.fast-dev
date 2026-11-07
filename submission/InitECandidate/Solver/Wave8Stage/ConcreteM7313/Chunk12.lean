import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word256
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word257
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word258
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word259
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word260
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word261
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word262
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word263
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word264
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word265
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word266
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word267
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word268
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word269
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word270
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word271
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk12
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult256 := WordToStack.Native.compileProgNative
  riscvConfig false Word256.program PrefixChecks.Shard192.arity registers (.nil, 534)
theorem stackResult256_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word256.program
      PrefixChecks.Shard192.arity registers (prefixList, 534) =
    (stackResult256.1, stackResult256.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult256.2.2.1, 549)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word256.program
    PrefixChecks.Shard192.arity registers prefixList 534
    stackResult256.1 stackResult256.2.1 stackResult256.2.2.1 549 stackResult256_eq
wave8_kernel_reduce stackResult257 := WordToStack.Native.compileProgNative
  riscvConfig false Word257.program PrefixChecks.Shard193.arity registers (.nil, 549)
theorem stackResult257_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word257.program
      PrefixChecks.Shard193.arity registers (prefixList, 549) =
    (stackResult257.1, stackResult257.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult257.2.2.1, 557)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word257.program
    PrefixChecks.Shard193.arity registers prefixList 549
    stackResult257.1 stackResult257.2.1 stackResult257.2.2.1 557 stackResult257_eq
wave8_kernel_reduce stackResult258 := WordToStack.Native.compileProgNative
  riscvConfig false Word258.program PrefixChecks.Shard194.arity registers (.nil, 557)
theorem stackResult258_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word258.program
      PrefixChecks.Shard194.arity registers (prefixList, 557) =
    (stackResult258.1, stackResult258.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult258.2.2.1, 559)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word258.program
    PrefixChecks.Shard194.arity registers prefixList 557
    stackResult258.1 stackResult258.2.1 stackResult258.2.2.1 559 stackResult258_eq
wave8_kernel_reduce stackResult259 := WordToStack.Native.compileProgNative
  riscvConfig false Word259.program PrefixChecks.Shard195.arity registers (.nil, 559)
theorem stackResult259_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word259.program
      PrefixChecks.Shard195.arity registers (prefixList, 559) =
    (stackResult259.1, stackResult259.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult259.2.2.1, 589)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word259.program
    PrefixChecks.Shard195.arity registers prefixList 559
    stackResult259.1 stackResult259.2.1 stackResult259.2.2.1 589 stackResult259_eq
wave8_kernel_reduce stackResult260 := WordToStack.Native.compileProgNative
  riscvConfig false Word260.program PrefixChecks.Shard196.arity registers (.nil, 589)
theorem stackResult260_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word260.program
      PrefixChecks.Shard196.arity registers (prefixList, 589) =
    (stackResult260.1, stackResult260.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult260.2.2.1, 598)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word260.program
    PrefixChecks.Shard196.arity registers prefixList 589
    stackResult260.1 stackResult260.2.1 stackResult260.2.2.1 598 stackResult260_eq
wave8_kernel_reduce stackResult261 := WordToStack.Native.compileProgNative
  riscvConfig false Word261.program PrefixChecks.Shard197.arity registers (.nil, 598)
theorem stackResult261_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word261.program
      PrefixChecks.Shard197.arity registers (prefixList, 598) =
    (stackResult261.1, stackResult261.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult261.2.2.1, 605)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word261.program
    PrefixChecks.Shard197.arity registers prefixList 598
    stackResult261.1 stackResult261.2.1 stackResult261.2.2.1 605 stackResult261_eq
wave8_kernel_reduce stackResult262 := WordToStack.Native.compileProgNative
  riscvConfig false Word262.program PrefixChecks.Shard198.arity registers (.nil, 605)
theorem stackResult262_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word262.program
      PrefixChecks.Shard198.arity registers (prefixList, 605) =
    (stackResult262.1, stackResult262.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult262.2.2.1, 612)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word262.program
    PrefixChecks.Shard198.arity registers prefixList 605
    stackResult262.1 stackResult262.2.1 stackResult262.2.2.1 612 stackResult262_eq
wave8_kernel_reduce stackResult263 := WordToStack.Native.compileProgNative
  riscvConfig false Word263.program PrefixChecks.Shard199.arity registers (.nil, 612)
theorem stackResult263_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word263.program
      PrefixChecks.Shard199.arity registers (prefixList, 612) =
    (stackResult263.1, stackResult263.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult263.2.2.1, 620)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word263.program
    PrefixChecks.Shard199.arity registers prefixList 612
    stackResult263.1 stackResult263.2.1 stackResult263.2.2.1 620 stackResult263_eq
wave8_kernel_reduce stackResult264 := WordToStack.Native.compileProgNative
  riscvConfig false Word264.program PrefixChecks.Shard200.arity registers (.nil, 620)
theorem stackResult264_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word264.program
      PrefixChecks.Shard200.arity registers (prefixList, 620) =
    (stackResult264.1, stackResult264.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult264.2.2.1, 626)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word264.program
    PrefixChecks.Shard200.arity registers prefixList 620
    stackResult264.1 stackResult264.2.1 stackResult264.2.2.1 626 stackResult264_eq
wave8_kernel_reduce stackResult265 := WordToStack.Native.compileProgNative
  riscvConfig false Word265.program PrefixChecks.Shard201.arity registers (.nil, 626)
theorem stackResult265_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word265.program
      PrefixChecks.Shard201.arity registers (prefixList, 626) =
    (stackResult265.1, stackResult265.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult265.2.2.1, 635)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word265.program
    PrefixChecks.Shard201.arity registers prefixList 626
    stackResult265.1 stackResult265.2.1 stackResult265.2.2.1 635 stackResult265_eq
wave8_kernel_reduce stackResult266 := WordToStack.Native.compileProgNative
  riscvConfig false Word266.program PrefixChecks.Shard202.arity registers (.nil, 635)
theorem stackResult266_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word266.program
      PrefixChecks.Shard202.arity registers (prefixList, 635) =
    (stackResult266.1, stackResult266.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult266.2.2.1, 644)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word266.program
    PrefixChecks.Shard202.arity registers prefixList 635
    stackResult266.1 stackResult266.2.1 stackResult266.2.2.1 644 stackResult266_eq
wave8_kernel_reduce stackResult267 := WordToStack.Native.compileProgNative
  riscvConfig false Word267.program PrefixChecks.Shard203.arity registers (.nil, 644)
theorem stackResult267_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word267.program
      PrefixChecks.Shard203.arity registers (prefixList, 644) =
    (stackResult267.1, stackResult267.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult267.2.2.1, 652)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word267.program
    PrefixChecks.Shard203.arity registers prefixList 644
    stackResult267.1 stackResult267.2.1 stackResult267.2.2.1 652 stackResult267_eq
wave8_kernel_reduce stackResult268 := WordToStack.Native.compileProgNative
  riscvConfig false Word268.program PrefixChecks.Shard204.arity registers (.nil, 652)
theorem stackResult268_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word268.program
      PrefixChecks.Shard204.arity registers (prefixList, 652) =
    (stackResult268.1, stackResult268.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult268.2.2.1, 654)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word268.program
    PrefixChecks.Shard204.arity registers prefixList 652
    stackResult268.1 stackResult268.2.1 stackResult268.2.2.1 654 stackResult268_eq
wave8_kernel_reduce stackResult269 := WordToStack.Native.compileProgNative
  riscvConfig false Word269.program PrefixChecks.Shard205.arity registers (.nil, 654)
theorem stackResult269_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word269.program
      PrefixChecks.Shard205.arity registers (prefixList, 654) =
    (stackResult269.1, stackResult269.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult269.2.2.1, 655)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word269.program
    PrefixChecks.Shard205.arity registers prefixList 654
    stackResult269.1 stackResult269.2.1 stackResult269.2.2.1 655 stackResult269_eq
wave8_kernel_reduce stackResult270 := WordToStack.Native.compileProgNative
  riscvConfig false Word270.program PrefixChecks.Shard206.arity registers (.nil, 655)
theorem stackResult270_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word270.program
      PrefixChecks.Shard206.arity registers (prefixList, 655) =
    (stackResult270.1, stackResult270.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult270.2.2.1, 656)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word270.program
    PrefixChecks.Shard206.arity registers prefixList 655
    stackResult270.1 stackResult270.2.1 stackResult270.2.2.1 656 stackResult270_eq
wave8_kernel_reduce stackResult271 := WordToStack.Native.compileProgNative
  riscvConfig false Word271.program PrefixChecks.Shard207.arity registers (.nil, 656)
theorem stackResult271_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word271.program
      PrefixChecks.Shard207.arity registers (prefixList, 656) =
    (stackResult271.1, stackResult271.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult271.2.2.1, 658)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word271.program
    PrefixChecks.Shard207.arity registers prefixList 656
    stackResult271.1 stackResult271.2.1 stackResult271.2.2.1 658 stackResult271_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard192.name, PrefixChecks.Shard192.arity, Word256.program),
  (PrefixChecks.Shard193.name, PrefixChecks.Shard193.arity, Word257.program),
  (PrefixChecks.Shard194.name, PrefixChecks.Shard194.arity, Word258.program),
  (PrefixChecks.Shard195.name, PrefixChecks.Shard195.arity, Word259.program),
  (PrefixChecks.Shard196.name, PrefixChecks.Shard196.arity, Word260.program),
  (PrefixChecks.Shard197.name, PrefixChecks.Shard197.arity, Word261.program),
  (PrefixChecks.Shard198.name, PrefixChecks.Shard198.arity, Word262.program),
  (PrefixChecks.Shard199.name, PrefixChecks.Shard199.arity, Word263.program),
  (PrefixChecks.Shard200.name, PrefixChecks.Shard200.arity, Word264.program),
  (PrefixChecks.Shard201.name, PrefixChecks.Shard201.arity, Word265.program),
  (PrefixChecks.Shard202.name, PrefixChecks.Shard202.arity, Word266.program),
  (PrefixChecks.Shard203.name, PrefixChecks.Shard203.arity, Word267.program),
  (PrefixChecks.Shard204.name, PrefixChecks.Shard204.arity, Word268.program),
  (PrefixChecks.Shard205.name, PrefixChecks.Shard205.arity, Word269.program),
  (PrefixChecks.Shard206.name, PrefixChecks.Shard206.arity, Word270.program),
  (PrefixChecks.Shard207.name, PrefixChecks.Shard207.arity, Word271.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard192.name, stackResult256.1),
  (PrefixChecks.Shard193.name, stackResult257.1),
  (PrefixChecks.Shard194.name, stackResult258.1),
  (PrefixChecks.Shard195.name, stackResult259.1),
  (PrefixChecks.Shard196.name, stackResult260.1),
  (PrefixChecks.Shard197.name, stackResult261.1),
  (PrefixChecks.Shard198.name, stackResult262.1),
  (PrefixChecks.Shard199.name, stackResult263.1),
  (PrefixChecks.Shard200.name, stackResult264.1),
  (PrefixChecks.Shard201.name, stackResult265.1),
  (PrefixChecks.Shard202.name, stackResult266.1),
  (PrefixChecks.Shard203.name, stackResult267.1),
  (PrefixChecks.Shard204.name, stackResult268.1),
  (PrefixChecks.Shard205.name, stackResult269.1),
  (PrefixChecks.Shard206.name, stackResult270.1),
  (PrefixChecks.Shard207.name, stackResult271.1)
]

noncomputable def frames : List Nat := [
  stackResult256.2.1,
  stackResult257.2.1,
  stackResult258.2.1,
  stackResult259.2.1,
  stackResult260.2.1,
  stackResult261.2.1,
  stackResult262.2.1,
  stackResult263.2.1,
  stackResult264.2.1,
  stackResult265.2.1,
  stackResult266.2.1,
  stackResult267.2.1,
  stackResult268.2.1,
  stackResult269.2.1,
  stackResult270.2.1,
  stackResult271.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult256.2.2.1) stackResult257.2.2.1) stackResult258.2.2.1) stackResult259.2.2.1) stackResult260.2.2.1) stackResult261.2.2.1) stackResult262.2.2.1) stackResult263.2.2.1) stackResult264.2.2.1) stackResult265.2.2.1) stackResult266.2.2.1) stackResult267.2.2.1) stackResult268.2.2.1) stackResult269.2.2.1) stackResult270.2.2.1) stackResult271.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 534) = (bodies, frames, (bitmapDelta, 658)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult256_from _
  apply compileWordToStack_cons
  · exact stackResult257_from _
  apply compileWordToStack_cons
  · exact stackResult258_from _
  apply compileWordToStack_cons
  · exact stackResult259_from _
  apply compileWordToStack_cons
  · exact stackResult260_from _
  apply compileWordToStack_cons
  · exact stackResult261_from _
  apply compileWordToStack_cons
  · exact stackResult262_from _
  apply compileWordToStack_cons
  · exact stackResult263_from _
  apply compileWordToStack_cons
  · exact stackResult264_from _
  apply compileWordToStack_cons
  · exact stackResult265_from _
  apply compileWordToStack_cons
  · exact stackResult266_from _
  apply compileWordToStack_cons
  · exact stackResult267_from _
  apply compileWordToStack_cons
  · exact stackResult268_from _
  apply compileWordToStack_cons
  · exact stackResult269_from _
  apply compileWordToStack_cons
  · exact stackResult270_from _
  apply compileWordToStack_cons
  · exact stackResult271_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 534) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 658)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 534 bodies frames bitmapDelta 658 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 192).take 16).zip
      [oracle256, oracle257, oracle258, oracle259, oracle260, oracle261, oracle262, oracle263, oracle264, oracle265, oracle266, oracle267, oracle268, oracle269, oracle270, oracle271]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle256 PrefixChecks.Shard192.entry,
    wordFunction oracle257 PrefixChecks.Shard193.entry,
    wordFunction oracle258 PrefixChecks.Shard194.entry,
    wordFunction oracle259 PrefixChecks.Shard195.entry,
    wordFunction oracle260 PrefixChecks.Shard196.entry,
    wordFunction oracle261 PrefixChecks.Shard197.entry,
    wordFunction oracle262 PrefixChecks.Shard198.entry,
    wordFunction oracle263 PrefixChecks.Shard199.entry,
    wordFunction oracle264 PrefixChecks.Shard200.entry,
    wordFunction oracle265 PrefixChecks.Shard201.entry,
    wordFunction oracle266 PrefixChecks.Shard202.entry,
    wordFunction oracle267 PrefixChecks.Shard203.entry,
    wordFunction oracle268 PrefixChecks.Shard204.entry,
    wordFunction oracle269 PrefixChecks.Shard205.entry,
    wordFunction oracle270 PrefixChecks.Shard206.entry,
    wordFunction oracle271 PrefixChecks.Shard207.entry] = words
  simp only [
    Word256.wordFunction_eq,
    Word257.wordFunction_eq,
    Word258.wordFunction_eq,
    Word259.wordFunction_eq,
    Word260.wordFunction_eq,
    Word261.wordFunction_eq,
    Word262.wordFunction_eq,
    Word263.wordFunction_eq,
    Word264.wordFunction_eq,
    Word265.wordFunction_eq,
    Word266.wordFunction_eq,
    Word267.wordFunction_eq,
    Word268.wordFunction_eq,
    Word269.wordFunction_eq,
    Word270.wordFunction_eq,
    Word271.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk12
