import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word656
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word657
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word658
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word659
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word660
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word661
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word662
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word663
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word664
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word665
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word666
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word667
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word668
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word669
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word670
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word671
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk37
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult656 := WordToStack.Native.compileProgNative
  riscvConfig false Word656.program PrefixChecks.Shard592.arity registers (.nil, 2733)
theorem stackResult656_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word656.program
      PrefixChecks.Shard592.arity registers (prefixList, 2733) =
    (stackResult656.1, stackResult656.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult656.2.2.1, 2742)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word656.program
    PrefixChecks.Shard592.arity registers prefixList 2733
    stackResult656.1 stackResult656.2.1 stackResult656.2.2.1 2742 stackResult656_eq
wave8_kernel_reduce stackResult657 := WordToStack.Native.compileProgNative
  riscvConfig false Word657.program PrefixChecks.Shard593.arity registers (.nil, 2742)
theorem stackResult657_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word657.program
      PrefixChecks.Shard593.arity registers (prefixList, 2742) =
    (stackResult657.1, stackResult657.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult657.2.2.1, 2744)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word657.program
    PrefixChecks.Shard593.arity registers prefixList 2742
    stackResult657.1 stackResult657.2.1 stackResult657.2.2.1 2744 stackResult657_eq
wave8_kernel_reduce stackResult658 := WordToStack.Native.compileProgNative
  riscvConfig false Word658.program PrefixChecks.Shard594.arity registers (.nil, 2744)
theorem stackResult658_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word658.program
      PrefixChecks.Shard594.arity registers (prefixList, 2744) =
    (stackResult658.1, stackResult658.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult658.2.2.1, 2746)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word658.program
    PrefixChecks.Shard594.arity registers prefixList 2744
    stackResult658.1 stackResult658.2.1 stackResult658.2.2.1 2746 stackResult658_eq
wave8_kernel_reduce stackResult659 := WordToStack.Native.compileProgNative
  riscvConfig false Word659.program PrefixChecks.Shard595.arity registers (.nil, 2746)
theorem stackResult659_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word659.program
      PrefixChecks.Shard595.arity registers (prefixList, 2746) =
    (stackResult659.1, stackResult659.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult659.2.2.1, 2749)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word659.program
    PrefixChecks.Shard595.arity registers prefixList 2746
    stackResult659.1 stackResult659.2.1 stackResult659.2.2.1 2749 stackResult659_eq
wave8_kernel_reduce stackResult660 := WordToStack.Native.compileProgNative
  riscvConfig false Word660.program PrefixChecks.Shard596.arity registers (.nil, 2749)
theorem stackResult660_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word660.program
      PrefixChecks.Shard596.arity registers (prefixList, 2749) =
    (stackResult660.1, stackResult660.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult660.2.2.1, 2750)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word660.program
    PrefixChecks.Shard596.arity registers prefixList 2749
    stackResult660.1 stackResult660.2.1 stackResult660.2.2.1 2750 stackResult660_eq
wave8_kernel_reduce stackResult661 := WordToStack.Native.compileProgNative
  riscvConfig false Word661.program PrefixChecks.Shard597.arity registers (.nil, 2750)
theorem stackResult661_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word661.program
      PrefixChecks.Shard597.arity registers (prefixList, 2750) =
    (stackResult661.1, stackResult661.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult661.2.2.1, 2751)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word661.program
    PrefixChecks.Shard597.arity registers prefixList 2750
    stackResult661.1 stackResult661.2.1 stackResult661.2.2.1 2751 stackResult661_eq
wave8_kernel_reduce stackResult662 := WordToStack.Native.compileProgNative
  riscvConfig false Word662.program PrefixChecks.Shard598.arity registers (.nil, 2751)
theorem stackResult662_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word662.program
      PrefixChecks.Shard598.arity registers (prefixList, 2751) =
    (stackResult662.1, stackResult662.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult662.2.2.1, 2751)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word662.program
    PrefixChecks.Shard598.arity registers prefixList 2751
    stackResult662.1 stackResult662.2.1 stackResult662.2.2.1 2751 stackResult662_eq
wave8_kernel_reduce stackResult663 := WordToStack.Native.compileProgNative
  riscvConfig false Word663.program PrefixChecks.Shard599.arity registers (.nil, 2751)
theorem stackResult663_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word663.program
      PrefixChecks.Shard599.arity registers (prefixList, 2751) =
    (stackResult663.1, stackResult663.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult663.2.2.1, 2751)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word663.program
    PrefixChecks.Shard599.arity registers prefixList 2751
    stackResult663.1 stackResult663.2.1 stackResult663.2.2.1 2751 stackResult663_eq
wave8_kernel_reduce stackResult664 := WordToStack.Native.compileProgNative
  riscvConfig false Word664.program PrefixChecks.Shard600.arity registers (.nil, 2751)
theorem stackResult664_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word664.program
      PrefixChecks.Shard600.arity registers (prefixList, 2751) =
    (stackResult664.1, stackResult664.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult664.2.2.1, 2752)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word664.program
    PrefixChecks.Shard600.arity registers prefixList 2751
    stackResult664.1 stackResult664.2.1 stackResult664.2.2.1 2752 stackResult664_eq
wave8_kernel_reduce stackResult665 := WordToStack.Native.compileProgNative
  riscvConfig false Word665.program PrefixChecks.Shard601.arity registers (.nil, 2752)
theorem stackResult665_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word665.program
      PrefixChecks.Shard601.arity registers (prefixList, 2752) =
    (stackResult665.1, stackResult665.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult665.2.2.1, 2755)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word665.program
    PrefixChecks.Shard601.arity registers prefixList 2752
    stackResult665.1 stackResult665.2.1 stackResult665.2.2.1 2755 stackResult665_eq
wave8_kernel_reduce stackResult666 := WordToStack.Native.compileProgNative
  riscvConfig false Word666.program PrefixChecks.Shard602.arity registers (.nil, 2755)
theorem stackResult666_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word666.program
      PrefixChecks.Shard602.arity registers (prefixList, 2755) =
    (stackResult666.1, stackResult666.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult666.2.2.1, 2761)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word666.program
    PrefixChecks.Shard602.arity registers prefixList 2755
    stackResult666.1 stackResult666.2.1 stackResult666.2.2.1 2761 stackResult666_eq
wave8_kernel_reduce stackResult667 := WordToStack.Native.compileProgNative
  riscvConfig false Word667.program PrefixChecks.Shard603.arity registers (.nil, 2761)
theorem stackResult667_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word667.program
      PrefixChecks.Shard603.arity registers (prefixList, 2761) =
    (stackResult667.1, stackResult667.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult667.2.2.1, 2765)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word667.program
    PrefixChecks.Shard603.arity registers prefixList 2761
    stackResult667.1 stackResult667.2.1 stackResult667.2.2.1 2765 stackResult667_eq
wave8_kernel_reduce stackResult668 := WordToStack.Native.compileProgNative
  riscvConfig false Word668.program PrefixChecks.Shard604.arity registers (.nil, 2765)
theorem stackResult668_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word668.program
      PrefixChecks.Shard604.arity registers (prefixList, 2765) =
    (stackResult668.1, stackResult668.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult668.2.2.1, 2772)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word668.program
    PrefixChecks.Shard604.arity registers prefixList 2765
    stackResult668.1 stackResult668.2.1 stackResult668.2.2.1 2772 stackResult668_eq
wave8_kernel_reduce stackResult669 := WordToStack.Native.compileProgNative
  riscvConfig false Word669.program PrefixChecks.Shard605.arity registers (.nil, 2772)
theorem stackResult669_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word669.program
      PrefixChecks.Shard605.arity registers (prefixList, 2772) =
    (stackResult669.1, stackResult669.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult669.2.2.1, 2782)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word669.program
    PrefixChecks.Shard605.arity registers prefixList 2772
    stackResult669.1 stackResult669.2.1 stackResult669.2.2.1 2782 stackResult669_eq
wave8_kernel_reduce stackResult670 := WordToStack.Native.compileProgNative
  riscvConfig false Word670.program PrefixChecks.Shard606.arity registers (.nil, 2782)
theorem stackResult670_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word670.program
      PrefixChecks.Shard606.arity registers (prefixList, 2782) =
    (stackResult670.1, stackResult670.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult670.2.2.1, 2785)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word670.program
    PrefixChecks.Shard606.arity registers prefixList 2782
    stackResult670.1 stackResult670.2.1 stackResult670.2.2.1 2785 stackResult670_eq
wave8_kernel_reduce stackResult671 := WordToStack.Native.compileProgNative
  riscvConfig false Word671.program PrefixChecks.Shard607.arity registers (.nil, 2785)
theorem stackResult671_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word671.program
      PrefixChecks.Shard607.arity registers (prefixList, 2785) =
    (stackResult671.1, stackResult671.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult671.2.2.1, 2787)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word671.program
    PrefixChecks.Shard607.arity registers prefixList 2785
    stackResult671.1 stackResult671.2.1 stackResult671.2.2.1 2787 stackResult671_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard592.name, PrefixChecks.Shard592.arity, Word656.program),
  (PrefixChecks.Shard593.name, PrefixChecks.Shard593.arity, Word657.program),
  (PrefixChecks.Shard594.name, PrefixChecks.Shard594.arity, Word658.program),
  (PrefixChecks.Shard595.name, PrefixChecks.Shard595.arity, Word659.program),
  (PrefixChecks.Shard596.name, PrefixChecks.Shard596.arity, Word660.program),
  (PrefixChecks.Shard597.name, PrefixChecks.Shard597.arity, Word661.program),
  (PrefixChecks.Shard598.name, PrefixChecks.Shard598.arity, Word662.program),
  (PrefixChecks.Shard599.name, PrefixChecks.Shard599.arity, Word663.program),
  (PrefixChecks.Shard600.name, PrefixChecks.Shard600.arity, Word664.program),
  (PrefixChecks.Shard601.name, PrefixChecks.Shard601.arity, Word665.program),
  (PrefixChecks.Shard602.name, PrefixChecks.Shard602.arity, Word666.program),
  (PrefixChecks.Shard603.name, PrefixChecks.Shard603.arity, Word667.program),
  (PrefixChecks.Shard604.name, PrefixChecks.Shard604.arity, Word668.program),
  (PrefixChecks.Shard605.name, PrefixChecks.Shard605.arity, Word669.program),
  (PrefixChecks.Shard606.name, PrefixChecks.Shard606.arity, Word670.program),
  (PrefixChecks.Shard607.name, PrefixChecks.Shard607.arity, Word671.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard592.name, stackResult656.1),
  (PrefixChecks.Shard593.name, stackResult657.1),
  (PrefixChecks.Shard594.name, stackResult658.1),
  (PrefixChecks.Shard595.name, stackResult659.1),
  (PrefixChecks.Shard596.name, stackResult660.1),
  (PrefixChecks.Shard597.name, stackResult661.1),
  (PrefixChecks.Shard598.name, stackResult662.1),
  (PrefixChecks.Shard599.name, stackResult663.1),
  (PrefixChecks.Shard600.name, stackResult664.1),
  (PrefixChecks.Shard601.name, stackResult665.1),
  (PrefixChecks.Shard602.name, stackResult666.1),
  (PrefixChecks.Shard603.name, stackResult667.1),
  (PrefixChecks.Shard604.name, stackResult668.1),
  (PrefixChecks.Shard605.name, stackResult669.1),
  (PrefixChecks.Shard606.name, stackResult670.1),
  (PrefixChecks.Shard607.name, stackResult671.1)
]

noncomputable def frames : List Nat := [
  stackResult656.2.1,
  stackResult657.2.1,
  stackResult658.2.1,
  stackResult659.2.1,
  stackResult660.2.1,
  stackResult661.2.1,
  stackResult662.2.1,
  stackResult663.2.1,
  stackResult664.2.1,
  stackResult665.2.1,
  stackResult666.2.1,
  stackResult667.2.1,
  stackResult668.2.1,
  stackResult669.2.1,
  stackResult670.2.1,
  stackResult671.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult656.2.2.1) stackResult657.2.2.1) stackResult658.2.2.1) stackResult659.2.2.1) stackResult660.2.2.1) stackResult661.2.2.1) stackResult662.2.2.1) stackResult663.2.2.1) stackResult664.2.2.1) stackResult665.2.2.1) stackResult666.2.2.1) stackResult667.2.2.1) stackResult668.2.2.1) stackResult669.2.2.1) stackResult670.2.2.1) stackResult671.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 2733) = (bodies, frames, (bitmapDelta, 2787)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult656_from _
  apply compileWordToStack_cons
  · exact stackResult657_from _
  apply compileWordToStack_cons
  · exact stackResult658_from _
  apply compileWordToStack_cons
  · exact stackResult659_from _
  apply compileWordToStack_cons
  · exact stackResult660_from _
  apply compileWordToStack_cons
  · exact stackResult661_from _
  apply compileWordToStack_cons
  · exact stackResult662_from _
  apply compileWordToStack_cons
  · exact stackResult663_from _
  apply compileWordToStack_cons
  · exact stackResult664_from _
  apply compileWordToStack_cons
  · exact stackResult665_from _
  apply compileWordToStack_cons
  · exact stackResult666_from _
  apply compileWordToStack_cons
  · exact stackResult667_from _
  apply compileWordToStack_cons
  · exact stackResult668_from _
  apply compileWordToStack_cons
  · exact stackResult669_from _
  apply compileWordToStack_cons
  · exact stackResult670_from _
  apply compileWordToStack_cons
  · exact stackResult671_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 2733) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 2787)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 2733 bodies frames bitmapDelta 2787 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 592).take 16).zip
      [oracle656, oracle657, oracle658, oracle659, oracle660, oracle661, oracle662, oracle663, oracle664, oracle665, oracle666, oracle667, oracle668, oracle669, oracle670, oracle671]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle656 PrefixChecks.Shard592.entry,
    wordFunction oracle657 PrefixChecks.Shard593.entry,
    wordFunction oracle658 PrefixChecks.Shard594.entry,
    wordFunction oracle659 PrefixChecks.Shard595.entry,
    wordFunction oracle660 PrefixChecks.Shard596.entry,
    wordFunction oracle661 PrefixChecks.Shard597.entry,
    wordFunction oracle662 PrefixChecks.Shard598.entry,
    wordFunction oracle663 PrefixChecks.Shard599.entry,
    wordFunction oracle664 PrefixChecks.Shard600.entry,
    wordFunction oracle665 PrefixChecks.Shard601.entry,
    wordFunction oracle666 PrefixChecks.Shard602.entry,
    wordFunction oracle667 PrefixChecks.Shard603.entry,
    wordFunction oracle668 PrefixChecks.Shard604.entry,
    wordFunction oracle669 PrefixChecks.Shard605.entry,
    wordFunction oracle670 PrefixChecks.Shard606.entry,
    wordFunction oracle671 PrefixChecks.Shard607.entry] = words
  simp only [
    Word656.wordFunction_eq,
    Word657.wordFunction_eq,
    Word658.wordFunction_eq,
    Word659.wordFunction_eq,
    Word660.wordFunction_eq,
    Word661.wordFunction_eq,
    Word662.wordFunction_eq,
    Word663.wordFunction_eq,
    Word664.wordFunction_eq,
    Word665.wordFunction_eq,
    Word666.wordFunction_eq,
    Word667.wordFunction_eq,
    Word668.wordFunction_eq,
    Word669.wordFunction_eq,
    Word670.wordFunction_eq,
    Word671.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk37
