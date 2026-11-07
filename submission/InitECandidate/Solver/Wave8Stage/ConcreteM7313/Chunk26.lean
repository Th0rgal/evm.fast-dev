import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word480
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word481
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word482
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word483
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word484
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word485
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word486
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word487
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word488
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word489
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word490
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word491
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word492
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word493
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word494
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word495
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk26
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult480 := WordToStack.Native.compileProgNative
  riscvConfig false Word480.program PrefixChecks.Shard416.arity registers (.nil, 1503)
theorem stackResult480_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word480.program
      PrefixChecks.Shard416.arity registers (prefixList, 1503) =
    (stackResult480.1, stackResult480.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult480.2.2.1, 1511)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word480.program
    PrefixChecks.Shard416.arity registers prefixList 1503
    stackResult480.1 stackResult480.2.1 stackResult480.2.2.1 1511 stackResult480_eq
wave8_kernel_reduce stackResult481 := WordToStack.Native.compileProgNative
  riscvConfig false Word481.program PrefixChecks.Shard417.arity registers (.nil, 1511)
theorem stackResult481_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word481.program
      PrefixChecks.Shard417.arity registers (prefixList, 1511) =
    (stackResult481.1, stackResult481.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult481.2.2.1, 1513)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word481.program
    PrefixChecks.Shard417.arity registers prefixList 1511
    stackResult481.1 stackResult481.2.1 stackResult481.2.2.1 1513 stackResult481_eq
wave8_kernel_reduce stackResult482 := WordToStack.Native.compileProgNative
  riscvConfig false Word482.program PrefixChecks.Shard418.arity registers (.nil, 1513)
theorem stackResult482_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word482.program
      PrefixChecks.Shard418.arity registers (prefixList, 1513) =
    (stackResult482.1, stackResult482.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult482.2.2.1, 1516)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word482.program
    PrefixChecks.Shard418.arity registers prefixList 1513
    stackResult482.1 stackResult482.2.1 stackResult482.2.2.1 1516 stackResult482_eq
wave8_kernel_reduce stackResult483 := WordToStack.Native.compileProgNative
  riscvConfig false Word483.program PrefixChecks.Shard419.arity registers (.nil, 1516)
theorem stackResult483_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word483.program
      PrefixChecks.Shard419.arity registers (prefixList, 1516) =
    (stackResult483.1, stackResult483.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult483.2.2.1, 1520)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word483.program
    PrefixChecks.Shard419.arity registers prefixList 1516
    stackResult483.1 stackResult483.2.1 stackResult483.2.2.1 1520 stackResult483_eq
wave8_kernel_reduce stackResult484 := WordToStack.Native.compileProgNative
  riscvConfig false Word484.program PrefixChecks.Shard420.arity registers (.nil, 1520)
theorem stackResult484_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word484.program
      PrefixChecks.Shard420.arity registers (prefixList, 1520) =
    (stackResult484.1, stackResult484.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult484.2.2.1, 1522)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word484.program
    PrefixChecks.Shard420.arity registers prefixList 1520
    stackResult484.1 stackResult484.2.1 stackResult484.2.2.1 1522 stackResult484_eq
wave8_kernel_reduce stackResult485 := WordToStack.Native.compileProgNative
  riscvConfig false Word485.program PrefixChecks.Shard421.arity registers (.nil, 1522)
theorem stackResult485_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word485.program
      PrefixChecks.Shard421.arity registers (prefixList, 1522) =
    (stackResult485.1, stackResult485.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult485.2.2.1, 1524)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word485.program
    PrefixChecks.Shard421.arity registers prefixList 1522
    stackResult485.1 stackResult485.2.1 stackResult485.2.2.1 1524 stackResult485_eq
wave8_kernel_reduce stackResult486 := WordToStack.Native.compileProgNative
  riscvConfig false Word486.program PrefixChecks.Shard422.arity registers (.nil, 1524)
theorem stackResult486_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word486.program
      PrefixChecks.Shard422.arity registers (prefixList, 1524) =
    (stackResult486.1, stackResult486.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult486.2.2.1, 1524)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word486.program
    PrefixChecks.Shard422.arity registers prefixList 1524
    stackResult486.1 stackResult486.2.1 stackResult486.2.2.1 1524 stackResult486_eq
wave8_kernel_reduce stackResult487 := WordToStack.Native.compileProgNative
  riscvConfig false Word487.program PrefixChecks.Shard423.arity registers (.nil, 1524)
theorem stackResult487_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word487.program
      PrefixChecks.Shard423.arity registers (prefixList, 1524) =
    (stackResult487.1, stackResult487.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult487.2.2.1, 1526)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word487.program
    PrefixChecks.Shard423.arity registers prefixList 1524
    stackResult487.1 stackResult487.2.1 stackResult487.2.2.1 1526 stackResult487_eq
wave8_kernel_reduce stackResult488 := WordToStack.Native.compileProgNative
  riscvConfig false Word488.program PrefixChecks.Shard424.arity registers (.nil, 1526)
theorem stackResult488_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word488.program
      PrefixChecks.Shard424.arity registers (prefixList, 1526) =
    (stackResult488.1, stackResult488.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult488.2.2.1, 1528)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word488.program
    PrefixChecks.Shard424.arity registers prefixList 1526
    stackResult488.1 stackResult488.2.1 stackResult488.2.2.1 1528 stackResult488_eq
wave8_kernel_reduce stackResult489 := WordToStack.Native.compileProgNative
  riscvConfig false Word489.program PrefixChecks.Shard425.arity registers (.nil, 1528)
theorem stackResult489_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word489.program
      PrefixChecks.Shard425.arity registers (prefixList, 1528) =
    (stackResult489.1, stackResult489.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult489.2.2.1, 1539)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word489.program
    PrefixChecks.Shard425.arity registers prefixList 1528
    stackResult489.1 stackResult489.2.1 stackResult489.2.2.1 1539 stackResult489_eq
wave8_kernel_reduce stackResult490 := WordToStack.Native.compileProgNative
  riscvConfig false Word490.program PrefixChecks.Shard426.arity registers (.nil, 1539)
theorem stackResult490_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word490.program
      PrefixChecks.Shard426.arity registers (prefixList, 1539) =
    (stackResult490.1, stackResult490.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult490.2.2.1, 1539)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word490.program
    PrefixChecks.Shard426.arity registers prefixList 1539
    stackResult490.1 stackResult490.2.1 stackResult490.2.2.1 1539 stackResult490_eq
wave8_kernel_reduce stackResult491 := WordToStack.Native.compileProgNative
  riscvConfig false Word491.program PrefixChecks.Shard427.arity registers (.nil, 1539)
theorem stackResult491_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word491.program
      PrefixChecks.Shard427.arity registers (prefixList, 1539) =
    (stackResult491.1, stackResult491.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult491.2.2.1, 1539)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word491.program
    PrefixChecks.Shard427.arity registers prefixList 1539
    stackResult491.1 stackResult491.2.1 stackResult491.2.2.1 1539 stackResult491_eq
wave8_kernel_reduce stackResult492 := WordToStack.Native.compileProgNative
  riscvConfig false Word492.program PrefixChecks.Shard428.arity registers (.nil, 1539)
theorem stackResult492_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word492.program
      PrefixChecks.Shard428.arity registers (prefixList, 1539) =
    (stackResult492.1, stackResult492.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult492.2.2.1, 1539)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word492.program
    PrefixChecks.Shard428.arity registers prefixList 1539
    stackResult492.1 stackResult492.2.1 stackResult492.2.2.1 1539 stackResult492_eq
wave8_kernel_reduce stackResult493 := WordToStack.Native.compileProgNative
  riscvConfig false Word493.program PrefixChecks.Shard429.arity registers (.nil, 1539)
theorem stackResult493_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word493.program
      PrefixChecks.Shard429.arity registers (prefixList, 1539) =
    (stackResult493.1, stackResult493.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult493.2.2.1, 1540)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word493.program
    PrefixChecks.Shard429.arity registers prefixList 1539
    stackResult493.1 stackResult493.2.1 stackResult493.2.2.1 1540 stackResult493_eq
wave8_kernel_reduce stackResult494 := WordToStack.Native.compileProgNative
  riscvConfig false Word494.program PrefixChecks.Shard430.arity registers (.nil, 1540)
theorem stackResult494_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word494.program
      PrefixChecks.Shard430.arity registers (prefixList, 1540) =
    (stackResult494.1, stackResult494.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult494.2.2.1, 1541)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word494.program
    PrefixChecks.Shard430.arity registers prefixList 1540
    stackResult494.1 stackResult494.2.1 stackResult494.2.2.1 1541 stackResult494_eq
wave8_kernel_reduce stackResult495 := WordToStack.Native.compileProgNative
  riscvConfig false Word495.program PrefixChecks.Shard431.arity registers (.nil, 1541)
theorem stackResult495_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word495.program
      PrefixChecks.Shard431.arity registers (prefixList, 1541) =
    (stackResult495.1, stackResult495.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult495.2.2.1, 1542)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word495.program
    PrefixChecks.Shard431.arity registers prefixList 1541
    stackResult495.1 stackResult495.2.1 stackResult495.2.2.1 1542 stackResult495_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard416.name, PrefixChecks.Shard416.arity, Word480.program),
  (PrefixChecks.Shard417.name, PrefixChecks.Shard417.arity, Word481.program),
  (PrefixChecks.Shard418.name, PrefixChecks.Shard418.arity, Word482.program),
  (PrefixChecks.Shard419.name, PrefixChecks.Shard419.arity, Word483.program),
  (PrefixChecks.Shard420.name, PrefixChecks.Shard420.arity, Word484.program),
  (PrefixChecks.Shard421.name, PrefixChecks.Shard421.arity, Word485.program),
  (PrefixChecks.Shard422.name, PrefixChecks.Shard422.arity, Word486.program),
  (PrefixChecks.Shard423.name, PrefixChecks.Shard423.arity, Word487.program),
  (PrefixChecks.Shard424.name, PrefixChecks.Shard424.arity, Word488.program),
  (PrefixChecks.Shard425.name, PrefixChecks.Shard425.arity, Word489.program),
  (PrefixChecks.Shard426.name, PrefixChecks.Shard426.arity, Word490.program),
  (PrefixChecks.Shard427.name, PrefixChecks.Shard427.arity, Word491.program),
  (PrefixChecks.Shard428.name, PrefixChecks.Shard428.arity, Word492.program),
  (PrefixChecks.Shard429.name, PrefixChecks.Shard429.arity, Word493.program),
  (PrefixChecks.Shard430.name, PrefixChecks.Shard430.arity, Word494.program),
  (PrefixChecks.Shard431.name, PrefixChecks.Shard431.arity, Word495.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard416.name, stackResult480.1),
  (PrefixChecks.Shard417.name, stackResult481.1),
  (PrefixChecks.Shard418.name, stackResult482.1),
  (PrefixChecks.Shard419.name, stackResult483.1),
  (PrefixChecks.Shard420.name, stackResult484.1),
  (PrefixChecks.Shard421.name, stackResult485.1),
  (PrefixChecks.Shard422.name, stackResult486.1),
  (PrefixChecks.Shard423.name, stackResult487.1),
  (PrefixChecks.Shard424.name, stackResult488.1),
  (PrefixChecks.Shard425.name, stackResult489.1),
  (PrefixChecks.Shard426.name, stackResult490.1),
  (PrefixChecks.Shard427.name, stackResult491.1),
  (PrefixChecks.Shard428.name, stackResult492.1),
  (PrefixChecks.Shard429.name, stackResult493.1),
  (PrefixChecks.Shard430.name, stackResult494.1),
  (PrefixChecks.Shard431.name, stackResult495.1)
]

noncomputable def frames : List Nat := [
  stackResult480.2.1,
  stackResult481.2.1,
  stackResult482.2.1,
  stackResult483.2.1,
  stackResult484.2.1,
  stackResult485.2.1,
  stackResult486.2.1,
  stackResult487.2.1,
  stackResult488.2.1,
  stackResult489.2.1,
  stackResult490.2.1,
  stackResult491.2.1,
  stackResult492.2.1,
  stackResult493.2.1,
  stackResult494.2.1,
  stackResult495.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult480.2.2.1) stackResult481.2.2.1) stackResult482.2.2.1) stackResult483.2.2.1) stackResult484.2.2.1) stackResult485.2.2.1) stackResult486.2.2.1) stackResult487.2.2.1) stackResult488.2.2.1) stackResult489.2.2.1) stackResult490.2.2.1) stackResult491.2.2.1) stackResult492.2.2.1) stackResult493.2.2.1) stackResult494.2.2.1) stackResult495.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 1503) = (bodies, frames, (bitmapDelta, 1542)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult480_from _
  apply compileWordToStack_cons
  · exact stackResult481_from _
  apply compileWordToStack_cons
  · exact stackResult482_from _
  apply compileWordToStack_cons
  · exact stackResult483_from _
  apply compileWordToStack_cons
  · exact stackResult484_from _
  apply compileWordToStack_cons
  · exact stackResult485_from _
  apply compileWordToStack_cons
  · exact stackResult486_from _
  apply compileWordToStack_cons
  · exact stackResult487_from _
  apply compileWordToStack_cons
  · exact stackResult488_from _
  apply compileWordToStack_cons
  · exact stackResult489_from _
  apply compileWordToStack_cons
  · exact stackResult490_from _
  apply compileWordToStack_cons
  · exact stackResult491_from _
  apply compileWordToStack_cons
  · exact stackResult492_from _
  apply compileWordToStack_cons
  · exact stackResult493_from _
  apply compileWordToStack_cons
  · exact stackResult494_from _
  apply compileWordToStack_cons
  · exact stackResult495_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 1503) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 1542)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 1503 bodies frames bitmapDelta 1542 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 416).take 16).zip
      [oracle480, oracle481, oracle482, oracle483, oracle484, oracle485, oracle486, oracle487, oracle488, oracle489, oracle490, oracle491, oracle492, oracle493, oracle494, oracle495]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle480 PrefixChecks.Shard416.entry,
    wordFunction oracle481 PrefixChecks.Shard417.entry,
    wordFunction oracle482 PrefixChecks.Shard418.entry,
    wordFunction oracle483 PrefixChecks.Shard419.entry,
    wordFunction oracle484 PrefixChecks.Shard420.entry,
    wordFunction oracle485 PrefixChecks.Shard421.entry,
    wordFunction oracle486 PrefixChecks.Shard422.entry,
    wordFunction oracle487 PrefixChecks.Shard423.entry,
    wordFunction oracle488 PrefixChecks.Shard424.entry,
    wordFunction oracle489 PrefixChecks.Shard425.entry,
    wordFunction oracle490 PrefixChecks.Shard426.entry,
    wordFunction oracle491 PrefixChecks.Shard427.entry,
    wordFunction oracle492 PrefixChecks.Shard428.entry,
    wordFunction oracle493 PrefixChecks.Shard429.entry,
    wordFunction oracle494 PrefixChecks.Shard430.entry,
    wordFunction oracle495 PrefixChecks.Shard431.entry] = words
  simp only [
    Word480.wordFunction_eq,
    Word481.wordFunction_eq,
    Word482.wordFunction_eq,
    Word483.wordFunction_eq,
    Word484.wordFunction_eq,
    Word485.wordFunction_eq,
    Word486.wordFunction_eq,
    Word487.wordFunction_eq,
    Word488.wordFunction_eq,
    Word489.wordFunction_eq,
    Word490.wordFunction_eq,
    Word491.wordFunction_eq,
    Word492.wordFunction_eq,
    Word493.wordFunction_eq,
    Word494.wordFunction_eq,
    Word495.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk26
