import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word608
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word609
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word610
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word611
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word612
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word613
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word614
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word615
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word616
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word617
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word618
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word619
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word620
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word621
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word622
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word623
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk34
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult608 := WordToStack.Native.compileProgNative
  riscvConfig false Word608.program PrefixChecks.Shard544.arity registers (.nil, 2334)
theorem stackResult608_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word608.program
      PrefixChecks.Shard544.arity registers (prefixList, 2334) =
    (stackResult608.1, stackResult608.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult608.2.2.1, 2344)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word608.program
    PrefixChecks.Shard544.arity registers prefixList 2334
    stackResult608.1 stackResult608.2.1 stackResult608.2.2.1 2344 stackResult608_eq
wave8_kernel_reduce stackResult609 := WordToStack.Native.compileProgNative
  riscvConfig false Word609.program PrefixChecks.Shard545.arity registers (.nil, 2344)
theorem stackResult609_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word609.program
      PrefixChecks.Shard545.arity registers (prefixList, 2344) =
    (stackResult609.1, stackResult609.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult609.2.2.1, 2344)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word609.program
    PrefixChecks.Shard545.arity registers prefixList 2344
    stackResult609.1 stackResult609.2.1 stackResult609.2.2.1 2344 stackResult609_eq
wave8_kernel_reduce stackResult610 := WordToStack.Native.compileProgNative
  riscvConfig false Word610.program PrefixChecks.Shard546.arity registers (.nil, 2344)
theorem stackResult610_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word610.program
      PrefixChecks.Shard546.arity registers (prefixList, 2344) =
    (stackResult610.1, stackResult610.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult610.2.2.1, 2347)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word610.program
    PrefixChecks.Shard546.arity registers prefixList 2344
    stackResult610.1 stackResult610.2.1 stackResult610.2.2.1 2347 stackResult610_eq
wave8_kernel_reduce stackResult611 := WordToStack.Native.compileProgNative
  riscvConfig false Word611.program PrefixChecks.Shard547.arity registers (.nil, 2347)
theorem stackResult611_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word611.program
      PrefixChecks.Shard547.arity registers (prefixList, 2347) =
    (stackResult611.1, stackResult611.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult611.2.2.1, 2349)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word611.program
    PrefixChecks.Shard547.arity registers prefixList 2347
    stackResult611.1 stackResult611.2.1 stackResult611.2.2.1 2349 stackResult611_eq
wave8_kernel_reduce stackResult612 := WordToStack.Native.compileProgNative
  riscvConfig false Word612.program PrefixChecks.Shard548.arity registers (.nil, 2349)
theorem stackResult612_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word612.program
      PrefixChecks.Shard548.arity registers (prefixList, 2349) =
    (stackResult612.1, stackResult612.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult612.2.2.1, 2350)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word612.program
    PrefixChecks.Shard548.arity registers prefixList 2349
    stackResult612.1 stackResult612.2.1 stackResult612.2.2.1 2350 stackResult612_eq
wave8_kernel_reduce stackResult613 := WordToStack.Native.compileProgNative
  riscvConfig false Word613.program PrefixChecks.Shard549.arity registers (.nil, 2350)
theorem stackResult613_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word613.program
      PrefixChecks.Shard549.arity registers (prefixList, 2350) =
    (stackResult613.1, stackResult613.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult613.2.2.1, 2352)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word613.program
    PrefixChecks.Shard549.arity registers prefixList 2350
    stackResult613.1 stackResult613.2.1 stackResult613.2.2.1 2352 stackResult613_eq
wave8_kernel_reduce stackResult614 := WordToStack.Native.compileProgNative
  riscvConfig false Word614.program PrefixChecks.Shard550.arity registers (.nil, 2352)
theorem stackResult614_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word614.program
      PrefixChecks.Shard550.arity registers (prefixList, 2352) =
    (stackResult614.1, stackResult614.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult614.2.2.1, 2362)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word614.program
    PrefixChecks.Shard550.arity registers prefixList 2352
    stackResult614.1 stackResult614.2.1 stackResult614.2.2.1 2362 stackResult614_eq
wave8_kernel_reduce stackResult615 := WordToStack.Native.compileProgNative
  riscvConfig false Word615.program PrefixChecks.Shard551.arity registers (.nil, 2362)
theorem stackResult615_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word615.program
      PrefixChecks.Shard551.arity registers (prefixList, 2362) =
    (stackResult615.1, stackResult615.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult615.2.2.1, 2371)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word615.program
    PrefixChecks.Shard551.arity registers prefixList 2362
    stackResult615.1 stackResult615.2.1 stackResult615.2.2.1 2371 stackResult615_eq
wave8_kernel_reduce stackResult616 := WordToStack.Native.compileProgNative
  riscvConfig false Word616.program PrefixChecks.Shard552.arity registers (.nil, 2371)
theorem stackResult616_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word616.program
      PrefixChecks.Shard552.arity registers (prefixList, 2371) =
    (stackResult616.1, stackResult616.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult616.2.2.1, 2387)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word616.program
    PrefixChecks.Shard552.arity registers prefixList 2371
    stackResult616.1 stackResult616.2.1 stackResult616.2.2.1 2387 stackResult616_eq
wave8_kernel_reduce stackResult617 := WordToStack.Native.compileProgNative
  riscvConfig false Word617.program PrefixChecks.Shard553.arity registers (.nil, 2387)
theorem stackResult617_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word617.program
      PrefixChecks.Shard553.arity registers (prefixList, 2387) =
    (stackResult617.1, stackResult617.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult617.2.2.1, 2403)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word617.program
    PrefixChecks.Shard553.arity registers prefixList 2387
    stackResult617.1 stackResult617.2.1 stackResult617.2.2.1 2403 stackResult617_eq
wave8_kernel_reduce stackResult618 := WordToStack.Native.compileProgNative
  riscvConfig false Word618.program PrefixChecks.Shard554.arity registers (.nil, 2403)
theorem stackResult618_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word618.program
      PrefixChecks.Shard554.arity registers (prefixList, 2403) =
    (stackResult618.1, stackResult618.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult618.2.2.1, 2421)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word618.program
    PrefixChecks.Shard554.arity registers prefixList 2403
    stackResult618.1 stackResult618.2.1 stackResult618.2.2.1 2421 stackResult618_eq
wave8_kernel_reduce stackResult619 := WordToStack.Native.compileProgNative
  riscvConfig false Word619.program PrefixChecks.Shard555.arity registers (.nil, 2421)
theorem stackResult619_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word619.program
      PrefixChecks.Shard555.arity registers (prefixList, 2421) =
    (stackResult619.1, stackResult619.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult619.2.2.1, 2428)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word619.program
    PrefixChecks.Shard555.arity registers prefixList 2421
    stackResult619.1 stackResult619.2.1 stackResult619.2.2.1 2428 stackResult619_eq
wave8_kernel_reduce stackResult620 := WordToStack.Native.compileProgNative
  riscvConfig false Word620.program PrefixChecks.Shard556.arity registers (.nil, 2428)
theorem stackResult620_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word620.program
      PrefixChecks.Shard556.arity registers (prefixList, 2428) =
    (stackResult620.1, stackResult620.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult620.2.2.1, 2432)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word620.program
    PrefixChecks.Shard556.arity registers prefixList 2428
    stackResult620.1 stackResult620.2.1 stackResult620.2.2.1 2432 stackResult620_eq
wave8_kernel_reduce stackResult621 := WordToStack.Native.compileProgNative
  riscvConfig false Word621.program PrefixChecks.Shard557.arity registers (.nil, 2432)
theorem stackResult621_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word621.program
      PrefixChecks.Shard557.arity registers (prefixList, 2432) =
    (stackResult621.1, stackResult621.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult621.2.2.1, 2467)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word621.program
    PrefixChecks.Shard557.arity registers prefixList 2432
    stackResult621.1 stackResult621.2.1 stackResult621.2.2.1 2467 stackResult621_eq
wave8_kernel_reduce stackResult622 := WordToStack.Native.compileProgNative
  riscvConfig false Word622.program PrefixChecks.Shard558.arity registers (.nil, 2467)
theorem stackResult622_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word622.program
      PrefixChecks.Shard558.arity registers (prefixList, 2467) =
    (stackResult622.1, stackResult622.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult622.2.2.1, 2499)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word622.program
    PrefixChecks.Shard558.arity registers prefixList 2467
    stackResult622.1 stackResult622.2.1 stackResult622.2.2.1 2499 stackResult622_eq
wave8_kernel_reduce stackResult623 := WordToStack.Native.compileProgNative
  riscvConfig false Word623.program PrefixChecks.Shard559.arity registers (.nil, 2499)
theorem stackResult623_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word623.program
      PrefixChecks.Shard559.arity registers (prefixList, 2499) =
    (stackResult623.1, stackResult623.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult623.2.2.1, 2525)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word623.program
    PrefixChecks.Shard559.arity registers prefixList 2499
    stackResult623.1 stackResult623.2.1 stackResult623.2.2.1 2525 stackResult623_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard544.name, PrefixChecks.Shard544.arity, Word608.program),
  (PrefixChecks.Shard545.name, PrefixChecks.Shard545.arity, Word609.program),
  (PrefixChecks.Shard546.name, PrefixChecks.Shard546.arity, Word610.program),
  (PrefixChecks.Shard547.name, PrefixChecks.Shard547.arity, Word611.program),
  (PrefixChecks.Shard548.name, PrefixChecks.Shard548.arity, Word612.program),
  (PrefixChecks.Shard549.name, PrefixChecks.Shard549.arity, Word613.program),
  (PrefixChecks.Shard550.name, PrefixChecks.Shard550.arity, Word614.program),
  (PrefixChecks.Shard551.name, PrefixChecks.Shard551.arity, Word615.program),
  (PrefixChecks.Shard552.name, PrefixChecks.Shard552.arity, Word616.program),
  (PrefixChecks.Shard553.name, PrefixChecks.Shard553.arity, Word617.program),
  (PrefixChecks.Shard554.name, PrefixChecks.Shard554.arity, Word618.program),
  (PrefixChecks.Shard555.name, PrefixChecks.Shard555.arity, Word619.program),
  (PrefixChecks.Shard556.name, PrefixChecks.Shard556.arity, Word620.program),
  (PrefixChecks.Shard557.name, PrefixChecks.Shard557.arity, Word621.program),
  (PrefixChecks.Shard558.name, PrefixChecks.Shard558.arity, Word622.program),
  (PrefixChecks.Shard559.name, PrefixChecks.Shard559.arity, Word623.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard544.name, stackResult608.1),
  (PrefixChecks.Shard545.name, stackResult609.1),
  (PrefixChecks.Shard546.name, stackResult610.1),
  (PrefixChecks.Shard547.name, stackResult611.1),
  (PrefixChecks.Shard548.name, stackResult612.1),
  (PrefixChecks.Shard549.name, stackResult613.1),
  (PrefixChecks.Shard550.name, stackResult614.1),
  (PrefixChecks.Shard551.name, stackResult615.1),
  (PrefixChecks.Shard552.name, stackResult616.1),
  (PrefixChecks.Shard553.name, stackResult617.1),
  (PrefixChecks.Shard554.name, stackResult618.1),
  (PrefixChecks.Shard555.name, stackResult619.1),
  (PrefixChecks.Shard556.name, stackResult620.1),
  (PrefixChecks.Shard557.name, stackResult621.1),
  (PrefixChecks.Shard558.name, stackResult622.1),
  (PrefixChecks.Shard559.name, stackResult623.1)
]

noncomputable def frames : List Nat := [
  stackResult608.2.1,
  stackResult609.2.1,
  stackResult610.2.1,
  stackResult611.2.1,
  stackResult612.2.1,
  stackResult613.2.1,
  stackResult614.2.1,
  stackResult615.2.1,
  stackResult616.2.1,
  stackResult617.2.1,
  stackResult618.2.1,
  stackResult619.2.1,
  stackResult620.2.1,
  stackResult621.2.1,
  stackResult622.2.1,
  stackResult623.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult608.2.2.1) stackResult609.2.2.1) stackResult610.2.2.1) stackResult611.2.2.1) stackResult612.2.2.1) stackResult613.2.2.1) stackResult614.2.2.1) stackResult615.2.2.1) stackResult616.2.2.1) stackResult617.2.2.1) stackResult618.2.2.1) stackResult619.2.2.1) stackResult620.2.2.1) stackResult621.2.2.1) stackResult622.2.2.1) stackResult623.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 2334) = (bodies, frames, (bitmapDelta, 2525)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult608_from _
  apply compileWordToStack_cons
  · exact stackResult609_from _
  apply compileWordToStack_cons
  · exact stackResult610_from _
  apply compileWordToStack_cons
  · exact stackResult611_from _
  apply compileWordToStack_cons
  · exact stackResult612_from _
  apply compileWordToStack_cons
  · exact stackResult613_from _
  apply compileWordToStack_cons
  · exact stackResult614_from _
  apply compileWordToStack_cons
  · exact stackResult615_from _
  apply compileWordToStack_cons
  · exact stackResult616_from _
  apply compileWordToStack_cons
  · exact stackResult617_from _
  apply compileWordToStack_cons
  · exact stackResult618_from _
  apply compileWordToStack_cons
  · exact stackResult619_from _
  apply compileWordToStack_cons
  · exact stackResult620_from _
  apply compileWordToStack_cons
  · exact stackResult621_from _
  apply compileWordToStack_cons
  · exact stackResult622_from _
  apply compileWordToStack_cons
  · exact stackResult623_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 2334) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 2525)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 2334 bodies frames bitmapDelta 2525 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 544).take 16).zip
      [oracle608, oracle609, oracle610, oracle611, oracle612, oracle613, oracle614, oracle615, oracle616, oracle617, oracle618, oracle619, oracle620, oracle621, oracle622, oracle623]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle608 PrefixChecks.Shard544.entry,
    wordFunction oracle609 PrefixChecks.Shard545.entry,
    wordFunction oracle610 PrefixChecks.Shard546.entry,
    wordFunction oracle611 PrefixChecks.Shard547.entry,
    wordFunction oracle612 PrefixChecks.Shard548.entry,
    wordFunction oracle613 PrefixChecks.Shard549.entry,
    wordFunction oracle614 PrefixChecks.Shard550.entry,
    wordFunction oracle615 PrefixChecks.Shard551.entry,
    wordFunction oracle616 PrefixChecks.Shard552.entry,
    wordFunction oracle617 PrefixChecks.Shard553.entry,
    wordFunction oracle618 PrefixChecks.Shard554.entry,
    wordFunction oracle619 PrefixChecks.Shard555.entry,
    wordFunction oracle620 PrefixChecks.Shard556.entry,
    wordFunction oracle621 PrefixChecks.Shard557.entry,
    wordFunction oracle622 PrefixChecks.Shard558.entry,
    wordFunction oracle623 PrefixChecks.Shard559.entry] = words
  simp only [
    Word608.wordFunction_eq,
    Word609.wordFunction_eq,
    Word610.wordFunction_eq,
    Word611.wordFunction_eq,
    Word612.wordFunction_eq,
    Word613.wordFunction_eq,
    Word614.wordFunction_eq,
    Word615.wordFunction_eq,
    Word616.wordFunction_eq,
    Word617.wordFunction_eq,
    Word618.wordFunction_eq,
    Word619.wordFunction_eq,
    Word620.wordFunction_eq,
    Word621.wordFunction_eq,
    Word622.wordFunction_eq,
    Word623.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk34
