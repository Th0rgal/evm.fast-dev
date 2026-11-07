import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word720
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word721
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word722
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word723
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word724
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word725
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word726
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word727
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word728
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word729
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word730
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word731
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word732
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word733
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word734
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word735
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk41
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult720 := WordToStack.Native.compileProgNative
  riscvConfig false Word720.program PrefixChecks.Shard656.arity registers (.nil, 3231)
theorem stackResult720_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word720.program
      PrefixChecks.Shard656.arity registers (prefixList, 3231) =
    (stackResult720.1, stackResult720.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult720.2.2.1, 3241)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word720.program
    PrefixChecks.Shard656.arity registers prefixList 3231
    stackResult720.1 stackResult720.2.1 stackResult720.2.2.1 3241 stackResult720_eq
wave8_kernel_reduce stackResult721 := WordToStack.Native.compileProgNative
  riscvConfig false Word721.program PrefixChecks.Shard657.arity registers (.nil, 3241)
theorem stackResult721_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word721.program
      PrefixChecks.Shard657.arity registers (prefixList, 3241) =
    (stackResult721.1, stackResult721.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult721.2.2.1, 3242)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word721.program
    PrefixChecks.Shard657.arity registers prefixList 3241
    stackResult721.1 stackResult721.2.1 stackResult721.2.2.1 3242 stackResult721_eq
wave8_kernel_reduce stackResult722 := WordToStack.Native.compileProgNative
  riscvConfig false Word722.program PrefixChecks.Shard658.arity registers (.nil, 3242)
theorem stackResult722_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word722.program
      PrefixChecks.Shard658.arity registers (prefixList, 3242) =
    (stackResult722.1, stackResult722.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult722.2.2.1, 3244)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word722.program
    PrefixChecks.Shard658.arity registers prefixList 3242
    stackResult722.1 stackResult722.2.1 stackResult722.2.2.1 3244 stackResult722_eq
wave8_kernel_reduce stackResult723 := WordToStack.Native.compileProgNative
  riscvConfig false Word723.program PrefixChecks.Shard659.arity registers (.nil, 3244)
theorem stackResult723_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word723.program
      PrefixChecks.Shard659.arity registers (prefixList, 3244) =
    (stackResult723.1, stackResult723.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult723.2.2.1, 3245)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word723.program
    PrefixChecks.Shard659.arity registers prefixList 3244
    stackResult723.1 stackResult723.2.1 stackResult723.2.2.1 3245 stackResult723_eq
wave8_kernel_reduce stackResult724 := WordToStack.Native.compileProgNative
  riscvConfig false Word724.program PrefixChecks.Shard660.arity registers (.nil, 3245)
theorem stackResult724_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word724.program
      PrefixChecks.Shard660.arity registers (prefixList, 3245) =
    (stackResult724.1, stackResult724.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult724.2.2.1, 3247)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word724.program
    PrefixChecks.Shard660.arity registers prefixList 3245
    stackResult724.1 stackResult724.2.1 stackResult724.2.2.1 3247 stackResult724_eq
wave8_kernel_reduce stackResult725 := WordToStack.Native.compileProgNative
  riscvConfig false Word725.program PrefixChecks.Shard661.arity registers (.nil, 3247)
theorem stackResult725_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word725.program
      PrefixChecks.Shard661.arity registers (prefixList, 3247) =
    (stackResult725.1, stackResult725.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult725.2.2.1, 3247)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word725.program
    PrefixChecks.Shard661.arity registers prefixList 3247
    stackResult725.1 stackResult725.2.1 stackResult725.2.2.1 3247 stackResult725_eq
wave8_kernel_reduce stackResult726 := WordToStack.Native.compileProgNative
  riscvConfig false Word726.program PrefixChecks.Shard662.arity registers (.nil, 3247)
theorem stackResult726_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word726.program
      PrefixChecks.Shard662.arity registers (prefixList, 3247) =
    (stackResult726.1, stackResult726.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult726.2.2.1, 3253)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word726.program
    PrefixChecks.Shard662.arity registers prefixList 3247
    stackResult726.1 stackResult726.2.1 stackResult726.2.2.1 3253 stackResult726_eq
wave8_kernel_reduce stackResult727 := WordToStack.Native.compileProgNative
  riscvConfig false Word727.program PrefixChecks.Shard663.arity registers (.nil, 3253)
theorem stackResult727_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word727.program
      PrefixChecks.Shard663.arity registers (prefixList, 3253) =
    (stackResult727.1, stackResult727.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult727.2.2.1, 3257)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word727.program
    PrefixChecks.Shard663.arity registers prefixList 3253
    stackResult727.1 stackResult727.2.1 stackResult727.2.2.1 3257 stackResult727_eq
wave8_kernel_reduce stackResult728 := WordToStack.Native.compileProgNative
  riscvConfig false Word728.program PrefixChecks.Shard664.arity registers (.nil, 3257)
theorem stackResult728_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word728.program
      PrefixChecks.Shard664.arity registers (prefixList, 3257) =
    (stackResult728.1, stackResult728.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult728.2.2.1, 3260)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word728.program
    PrefixChecks.Shard664.arity registers prefixList 3257
    stackResult728.1 stackResult728.2.1 stackResult728.2.2.1 3260 stackResult728_eq
wave8_kernel_reduce stackResult729 := WordToStack.Native.compileProgNative
  riscvConfig false Word729.program PrefixChecks.Shard665.arity registers (.nil, 3260)
theorem stackResult729_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word729.program
      PrefixChecks.Shard665.arity registers (prefixList, 3260) =
    (stackResult729.1, stackResult729.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult729.2.2.1, 3261)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word729.program
    PrefixChecks.Shard665.arity registers prefixList 3260
    stackResult729.1 stackResult729.2.1 stackResult729.2.2.1 3261 stackResult729_eq
wave8_kernel_reduce stackResult730 := WordToStack.Native.compileProgNative
  riscvConfig false Word730.program PrefixChecks.Shard666.arity registers (.nil, 3261)
theorem stackResult730_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word730.program
      PrefixChecks.Shard666.arity registers (prefixList, 3261) =
    (stackResult730.1, stackResult730.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult730.2.2.1, 3262)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word730.program
    PrefixChecks.Shard666.arity registers prefixList 3261
    stackResult730.1 stackResult730.2.1 stackResult730.2.2.1 3262 stackResult730_eq
wave8_kernel_reduce stackResult731 := WordToStack.Native.compileProgNative
  riscvConfig false Word731.program PrefixChecks.Shard667.arity registers (.nil, 3262)
theorem stackResult731_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word731.program
      PrefixChecks.Shard667.arity registers (prefixList, 3262) =
    (stackResult731.1, stackResult731.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult731.2.2.1, 3262)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word731.program
    PrefixChecks.Shard667.arity registers prefixList 3262
    stackResult731.1 stackResult731.2.1 stackResult731.2.2.1 3262 stackResult731_eq
wave8_kernel_reduce stackResult732 := WordToStack.Native.compileProgNative
  riscvConfig false Word732.program PrefixChecks.Shard668.arity registers (.nil, 3262)
theorem stackResult732_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word732.program
      PrefixChecks.Shard668.arity registers (prefixList, 3262) =
    (stackResult732.1, stackResult732.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult732.2.2.1, 3262)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word732.program
    PrefixChecks.Shard668.arity registers prefixList 3262
    stackResult732.1 stackResult732.2.1 stackResult732.2.2.1 3262 stackResult732_eq
wave8_kernel_reduce stackResult733 := WordToStack.Native.compileProgNative
  riscvConfig false Word733.program PrefixChecks.Shard669.arity registers (.nil, 3262)
theorem stackResult733_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word733.program
      PrefixChecks.Shard669.arity registers (prefixList, 3262) =
    (stackResult733.1, stackResult733.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult733.2.2.1, 3263)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word733.program
    PrefixChecks.Shard669.arity registers prefixList 3262
    stackResult733.1 stackResult733.2.1 stackResult733.2.2.1 3263 stackResult733_eq
wave8_kernel_reduce stackResult734 := WordToStack.Native.compileProgNative
  riscvConfig false Word734.program PrefixChecks.Shard670.arity registers (.nil, 3263)
theorem stackResult734_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word734.program
      PrefixChecks.Shard670.arity registers (prefixList, 3263) =
    (stackResult734.1, stackResult734.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult734.2.2.1, 3265)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word734.program
    PrefixChecks.Shard670.arity registers prefixList 3263
    stackResult734.1 stackResult734.2.1 stackResult734.2.2.1 3265 stackResult734_eq
wave8_kernel_reduce stackResult735 := WordToStack.Native.compileProgNative
  riscvConfig false Word735.program PrefixChecks.Shard671.arity registers (.nil, 3265)
theorem stackResult735_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word735.program
      PrefixChecks.Shard671.arity registers (prefixList, 3265) =
    (stackResult735.1, stackResult735.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult735.2.2.1, 3267)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word735.program
    PrefixChecks.Shard671.arity registers prefixList 3265
    stackResult735.1 stackResult735.2.1 stackResult735.2.2.1 3267 stackResult735_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard656.name, PrefixChecks.Shard656.arity, Word720.program),
  (PrefixChecks.Shard657.name, PrefixChecks.Shard657.arity, Word721.program),
  (PrefixChecks.Shard658.name, PrefixChecks.Shard658.arity, Word722.program),
  (PrefixChecks.Shard659.name, PrefixChecks.Shard659.arity, Word723.program),
  (PrefixChecks.Shard660.name, PrefixChecks.Shard660.arity, Word724.program),
  (PrefixChecks.Shard661.name, PrefixChecks.Shard661.arity, Word725.program),
  (PrefixChecks.Shard662.name, PrefixChecks.Shard662.arity, Word726.program),
  (PrefixChecks.Shard663.name, PrefixChecks.Shard663.arity, Word727.program),
  (PrefixChecks.Shard664.name, PrefixChecks.Shard664.arity, Word728.program),
  (PrefixChecks.Shard665.name, PrefixChecks.Shard665.arity, Word729.program),
  (PrefixChecks.Shard666.name, PrefixChecks.Shard666.arity, Word730.program),
  (PrefixChecks.Shard667.name, PrefixChecks.Shard667.arity, Word731.program),
  (PrefixChecks.Shard668.name, PrefixChecks.Shard668.arity, Word732.program),
  (PrefixChecks.Shard669.name, PrefixChecks.Shard669.arity, Word733.program),
  (PrefixChecks.Shard670.name, PrefixChecks.Shard670.arity, Word734.program),
  (PrefixChecks.Shard671.name, PrefixChecks.Shard671.arity, Word735.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard656.name, stackResult720.1),
  (PrefixChecks.Shard657.name, stackResult721.1),
  (PrefixChecks.Shard658.name, stackResult722.1),
  (PrefixChecks.Shard659.name, stackResult723.1),
  (PrefixChecks.Shard660.name, stackResult724.1),
  (PrefixChecks.Shard661.name, stackResult725.1),
  (PrefixChecks.Shard662.name, stackResult726.1),
  (PrefixChecks.Shard663.name, stackResult727.1),
  (PrefixChecks.Shard664.name, stackResult728.1),
  (PrefixChecks.Shard665.name, stackResult729.1),
  (PrefixChecks.Shard666.name, stackResult730.1),
  (PrefixChecks.Shard667.name, stackResult731.1),
  (PrefixChecks.Shard668.name, stackResult732.1),
  (PrefixChecks.Shard669.name, stackResult733.1),
  (PrefixChecks.Shard670.name, stackResult734.1),
  (PrefixChecks.Shard671.name, stackResult735.1)
]

noncomputable def frames : List Nat := [
  stackResult720.2.1,
  stackResult721.2.1,
  stackResult722.2.1,
  stackResult723.2.1,
  stackResult724.2.1,
  stackResult725.2.1,
  stackResult726.2.1,
  stackResult727.2.1,
  stackResult728.2.1,
  stackResult729.2.1,
  stackResult730.2.1,
  stackResult731.2.1,
  stackResult732.2.1,
  stackResult733.2.1,
  stackResult734.2.1,
  stackResult735.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult720.2.2.1) stackResult721.2.2.1) stackResult722.2.2.1) stackResult723.2.2.1) stackResult724.2.2.1) stackResult725.2.2.1) stackResult726.2.2.1) stackResult727.2.2.1) stackResult728.2.2.1) stackResult729.2.2.1) stackResult730.2.2.1) stackResult731.2.2.1) stackResult732.2.2.1) stackResult733.2.2.1) stackResult734.2.2.1) stackResult735.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 3231) = (bodies, frames, (bitmapDelta, 3267)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult720_from _
  apply compileWordToStack_cons
  · exact stackResult721_from _
  apply compileWordToStack_cons
  · exact stackResult722_from _
  apply compileWordToStack_cons
  · exact stackResult723_from _
  apply compileWordToStack_cons
  · exact stackResult724_from _
  apply compileWordToStack_cons
  · exact stackResult725_from _
  apply compileWordToStack_cons
  · exact stackResult726_from _
  apply compileWordToStack_cons
  · exact stackResult727_from _
  apply compileWordToStack_cons
  · exact stackResult728_from _
  apply compileWordToStack_cons
  · exact stackResult729_from _
  apply compileWordToStack_cons
  · exact stackResult730_from _
  apply compileWordToStack_cons
  · exact stackResult731_from _
  apply compileWordToStack_cons
  · exact stackResult732_from _
  apply compileWordToStack_cons
  · exact stackResult733_from _
  apply compileWordToStack_cons
  · exact stackResult734_from _
  apply compileWordToStack_cons
  · exact stackResult735_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 3231) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 3267)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 3231 bodies frames bitmapDelta 3267 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 656).take 16).zip
      [oracle720, oracle721, oracle722, oracle723, oracle724, oracle725, oracle726, oracle727, oracle728, oracle729, oracle730, oracle731, oracle732, oracle733, oracle734, oracle735]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle720 PrefixChecks.Shard656.entry,
    wordFunction oracle721 PrefixChecks.Shard657.entry,
    wordFunction oracle722 PrefixChecks.Shard658.entry,
    wordFunction oracle723 PrefixChecks.Shard659.entry,
    wordFunction oracle724 PrefixChecks.Shard660.entry,
    wordFunction oracle725 PrefixChecks.Shard661.entry,
    wordFunction oracle726 PrefixChecks.Shard662.entry,
    wordFunction oracle727 PrefixChecks.Shard663.entry,
    wordFunction oracle728 PrefixChecks.Shard664.entry,
    wordFunction oracle729 PrefixChecks.Shard665.entry,
    wordFunction oracle730 PrefixChecks.Shard666.entry,
    wordFunction oracle731 PrefixChecks.Shard667.entry,
    wordFunction oracle732 PrefixChecks.Shard668.entry,
    wordFunction oracle733 PrefixChecks.Shard669.entry,
    wordFunction oracle734 PrefixChecks.Shard670.entry,
    wordFunction oracle735 PrefixChecks.Shard671.entry] = words
  simp only [
    Word720.wordFunction_eq,
    Word721.wordFunction_eq,
    Word722.wordFunction_eq,
    Word723.wordFunction_eq,
    Word724.wordFunction_eq,
    Word725.wordFunction_eq,
    Word726.wordFunction_eq,
    Word727.wordFunction_eq,
    Word728.wordFunction_eq,
    Word729.wordFunction_eq,
    Word730.wordFunction_eq,
    Word731.wordFunction_eq,
    Word732.wordFunction_eq,
    Word733.wordFunction_eq,
    Word734.wordFunction_eq,
    Word735.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk41
