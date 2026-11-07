import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word432
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word433
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word434
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word435
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word436
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word437
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word438
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word439
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word440
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word441
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word442
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word443
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word444
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word445
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word446
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word447
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk23
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult432 := WordToStack.Native.compileProgNative
  riscvConfig false Word432.program PrefixChecks.Shard368.arity registers (.nil, 1300)
theorem stackResult432_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word432.program
      PrefixChecks.Shard368.arity registers (prefixList, 1300) =
    (stackResult432.1, stackResult432.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult432.2.2.1, 1302)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word432.program
    PrefixChecks.Shard368.arity registers prefixList 1300
    stackResult432.1 stackResult432.2.1 stackResult432.2.2.1 1302 stackResult432_eq
wave8_kernel_reduce stackResult433 := WordToStack.Native.compileProgNative
  riscvConfig false Word433.program PrefixChecks.Shard369.arity registers (.nil, 1302)
theorem stackResult433_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word433.program
      PrefixChecks.Shard369.arity registers (prefixList, 1302) =
    (stackResult433.1, stackResult433.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult433.2.2.1, 1312)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word433.program
    PrefixChecks.Shard369.arity registers prefixList 1302
    stackResult433.1 stackResult433.2.1 stackResult433.2.2.1 1312 stackResult433_eq
wave8_kernel_reduce stackResult434 := WordToStack.Native.compileProgNative
  riscvConfig false Word434.program PrefixChecks.Shard370.arity registers (.nil, 1312)
theorem stackResult434_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word434.program
      PrefixChecks.Shard370.arity registers (prefixList, 1312) =
    (stackResult434.1, stackResult434.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult434.2.2.1, 1312)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word434.program
    PrefixChecks.Shard370.arity registers prefixList 1312
    stackResult434.1 stackResult434.2.1 stackResult434.2.2.1 1312 stackResult434_eq
wave8_kernel_reduce stackResult435 := WordToStack.Native.compileProgNative
  riscvConfig false Word435.program PrefixChecks.Shard371.arity registers (.nil, 1312)
theorem stackResult435_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word435.program
      PrefixChecks.Shard371.arity registers (prefixList, 1312) =
    (stackResult435.1, stackResult435.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult435.2.2.1, 1314)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word435.program
    PrefixChecks.Shard371.arity registers prefixList 1312
    stackResult435.1 stackResult435.2.1 stackResult435.2.2.1 1314 stackResult435_eq
wave8_kernel_reduce stackResult436 := WordToStack.Native.compileProgNative
  riscvConfig false Word436.program PrefixChecks.Shard372.arity registers (.nil, 1314)
theorem stackResult436_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word436.program
      PrefixChecks.Shard372.arity registers (prefixList, 1314) =
    (stackResult436.1, stackResult436.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult436.2.2.1, 1316)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word436.program
    PrefixChecks.Shard372.arity registers prefixList 1314
    stackResult436.1 stackResult436.2.1 stackResult436.2.2.1 1316 stackResult436_eq
wave8_kernel_reduce stackResult437 := WordToStack.Native.compileProgNative
  riscvConfig false Word437.program PrefixChecks.Shard373.arity registers (.nil, 1316)
theorem stackResult437_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word437.program
      PrefixChecks.Shard373.arity registers (prefixList, 1316) =
    (stackResult437.1, stackResult437.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult437.2.2.1, 1318)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word437.program
    PrefixChecks.Shard373.arity registers prefixList 1316
    stackResult437.1 stackResult437.2.1 stackResult437.2.2.1 1318 stackResult437_eq
wave8_kernel_reduce stackResult438 := WordToStack.Native.compileProgNative
  riscvConfig false Word438.program PrefixChecks.Shard374.arity registers (.nil, 1318)
theorem stackResult438_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word438.program
      PrefixChecks.Shard374.arity registers (prefixList, 1318) =
    (stackResult438.1, stackResult438.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult438.2.2.1, 1322)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word438.program
    PrefixChecks.Shard374.arity registers prefixList 1318
    stackResult438.1 stackResult438.2.1 stackResult438.2.2.1 1322 stackResult438_eq
wave8_kernel_reduce stackResult439 := WordToStack.Native.compileProgNative
  riscvConfig false Word439.program PrefixChecks.Shard375.arity registers (.nil, 1322)
theorem stackResult439_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word439.program
      PrefixChecks.Shard375.arity registers (prefixList, 1322) =
    (stackResult439.1, stackResult439.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult439.2.2.1, 1330)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word439.program
    PrefixChecks.Shard375.arity registers prefixList 1322
    stackResult439.1 stackResult439.2.1 stackResult439.2.2.1 1330 stackResult439_eq
wave8_kernel_reduce stackResult440 := WordToStack.Native.compileProgNative
  riscvConfig false Word440.program PrefixChecks.Shard376.arity registers (.nil, 1330)
theorem stackResult440_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word440.program
      PrefixChecks.Shard376.arity registers (prefixList, 1330) =
    (stackResult440.1, stackResult440.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult440.2.2.1, 1331)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word440.program
    PrefixChecks.Shard376.arity registers prefixList 1330
    stackResult440.1 stackResult440.2.1 stackResult440.2.2.1 1331 stackResult440_eq
wave8_kernel_reduce stackResult441 := WordToStack.Native.compileProgNative
  riscvConfig false Word441.program PrefixChecks.Shard377.arity registers (.nil, 1331)
theorem stackResult441_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word441.program
      PrefixChecks.Shard377.arity registers (prefixList, 1331) =
    (stackResult441.1, stackResult441.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult441.2.2.1, 1336)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word441.program
    PrefixChecks.Shard377.arity registers prefixList 1331
    stackResult441.1 stackResult441.2.1 stackResult441.2.2.1 1336 stackResult441_eq
wave8_kernel_reduce stackResult442 := WordToStack.Native.compileProgNative
  riscvConfig false Word442.program PrefixChecks.Shard378.arity registers (.nil, 1336)
theorem stackResult442_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word442.program
      PrefixChecks.Shard378.arity registers (prefixList, 1336) =
    (stackResult442.1, stackResult442.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult442.2.2.1, 1338)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word442.program
    PrefixChecks.Shard378.arity registers prefixList 1336
    stackResult442.1 stackResult442.2.1 stackResult442.2.2.1 1338 stackResult442_eq
wave8_kernel_reduce stackResult443 := WordToStack.Native.compileProgNative
  riscvConfig false Word443.program PrefixChecks.Shard379.arity registers (.nil, 1338)
theorem stackResult443_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word443.program
      PrefixChecks.Shard379.arity registers (prefixList, 1338) =
    (stackResult443.1, stackResult443.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult443.2.2.1, 1340)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word443.program
    PrefixChecks.Shard379.arity registers prefixList 1338
    stackResult443.1 stackResult443.2.1 stackResult443.2.2.1 1340 stackResult443_eq
wave8_kernel_reduce stackResult444 := WordToStack.Native.compileProgNative
  riscvConfig false Word444.program PrefixChecks.Shard380.arity registers (.nil, 1340)
theorem stackResult444_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word444.program
      PrefixChecks.Shard380.arity registers (prefixList, 1340) =
    (stackResult444.1, stackResult444.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult444.2.2.1, 1342)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word444.program
    PrefixChecks.Shard380.arity registers prefixList 1340
    stackResult444.1 stackResult444.2.1 stackResult444.2.2.1 1342 stackResult444_eq
wave8_kernel_reduce stackResult445 := WordToStack.Native.compileProgNative
  riscvConfig false Word445.program PrefixChecks.Shard381.arity registers (.nil, 1342)
theorem stackResult445_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word445.program
      PrefixChecks.Shard381.arity registers (prefixList, 1342) =
    (stackResult445.1, stackResult445.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult445.2.2.1, 1344)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word445.program
    PrefixChecks.Shard381.arity registers prefixList 1342
    stackResult445.1 stackResult445.2.1 stackResult445.2.2.1 1344 stackResult445_eq
wave8_kernel_reduce stackResult446 := WordToStack.Native.compileProgNative
  riscvConfig false Word446.program PrefixChecks.Shard382.arity registers (.nil, 1344)
theorem stackResult446_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word446.program
      PrefixChecks.Shard382.arity registers (prefixList, 1344) =
    (stackResult446.1, stackResult446.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult446.2.2.1, 1345)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word446.program
    PrefixChecks.Shard382.arity registers prefixList 1344
    stackResult446.1 stackResult446.2.1 stackResult446.2.2.1 1345 stackResult446_eq
wave8_kernel_reduce stackResult447 := WordToStack.Native.compileProgNative
  riscvConfig false Word447.program PrefixChecks.Shard383.arity registers (.nil, 1345)
theorem stackResult447_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word447.program
      PrefixChecks.Shard383.arity registers (prefixList, 1345) =
    (stackResult447.1, stackResult447.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult447.2.2.1, 1348)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word447.program
    PrefixChecks.Shard383.arity registers prefixList 1345
    stackResult447.1 stackResult447.2.1 stackResult447.2.2.1 1348 stackResult447_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard368.name, PrefixChecks.Shard368.arity, Word432.program),
  (PrefixChecks.Shard369.name, PrefixChecks.Shard369.arity, Word433.program),
  (PrefixChecks.Shard370.name, PrefixChecks.Shard370.arity, Word434.program),
  (PrefixChecks.Shard371.name, PrefixChecks.Shard371.arity, Word435.program),
  (PrefixChecks.Shard372.name, PrefixChecks.Shard372.arity, Word436.program),
  (PrefixChecks.Shard373.name, PrefixChecks.Shard373.arity, Word437.program),
  (PrefixChecks.Shard374.name, PrefixChecks.Shard374.arity, Word438.program),
  (PrefixChecks.Shard375.name, PrefixChecks.Shard375.arity, Word439.program),
  (PrefixChecks.Shard376.name, PrefixChecks.Shard376.arity, Word440.program),
  (PrefixChecks.Shard377.name, PrefixChecks.Shard377.arity, Word441.program),
  (PrefixChecks.Shard378.name, PrefixChecks.Shard378.arity, Word442.program),
  (PrefixChecks.Shard379.name, PrefixChecks.Shard379.arity, Word443.program),
  (PrefixChecks.Shard380.name, PrefixChecks.Shard380.arity, Word444.program),
  (PrefixChecks.Shard381.name, PrefixChecks.Shard381.arity, Word445.program),
  (PrefixChecks.Shard382.name, PrefixChecks.Shard382.arity, Word446.program),
  (PrefixChecks.Shard383.name, PrefixChecks.Shard383.arity, Word447.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard368.name, stackResult432.1),
  (PrefixChecks.Shard369.name, stackResult433.1),
  (PrefixChecks.Shard370.name, stackResult434.1),
  (PrefixChecks.Shard371.name, stackResult435.1),
  (PrefixChecks.Shard372.name, stackResult436.1),
  (PrefixChecks.Shard373.name, stackResult437.1),
  (PrefixChecks.Shard374.name, stackResult438.1),
  (PrefixChecks.Shard375.name, stackResult439.1),
  (PrefixChecks.Shard376.name, stackResult440.1),
  (PrefixChecks.Shard377.name, stackResult441.1),
  (PrefixChecks.Shard378.name, stackResult442.1),
  (PrefixChecks.Shard379.name, stackResult443.1),
  (PrefixChecks.Shard380.name, stackResult444.1),
  (PrefixChecks.Shard381.name, stackResult445.1),
  (PrefixChecks.Shard382.name, stackResult446.1),
  (PrefixChecks.Shard383.name, stackResult447.1)
]

noncomputable def frames : List Nat := [
  stackResult432.2.1,
  stackResult433.2.1,
  stackResult434.2.1,
  stackResult435.2.1,
  stackResult436.2.1,
  stackResult437.2.1,
  stackResult438.2.1,
  stackResult439.2.1,
  stackResult440.2.1,
  stackResult441.2.1,
  stackResult442.2.1,
  stackResult443.2.1,
  stackResult444.2.1,
  stackResult445.2.1,
  stackResult446.2.1,
  stackResult447.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult432.2.2.1) stackResult433.2.2.1) stackResult434.2.2.1) stackResult435.2.2.1) stackResult436.2.2.1) stackResult437.2.2.1) stackResult438.2.2.1) stackResult439.2.2.1) stackResult440.2.2.1) stackResult441.2.2.1) stackResult442.2.2.1) stackResult443.2.2.1) stackResult444.2.2.1) stackResult445.2.2.1) stackResult446.2.2.1) stackResult447.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 1300) = (bodies, frames, (bitmapDelta, 1348)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult432_from _
  apply compileWordToStack_cons
  · exact stackResult433_from _
  apply compileWordToStack_cons
  · exact stackResult434_from _
  apply compileWordToStack_cons
  · exact stackResult435_from _
  apply compileWordToStack_cons
  · exact stackResult436_from _
  apply compileWordToStack_cons
  · exact stackResult437_from _
  apply compileWordToStack_cons
  · exact stackResult438_from _
  apply compileWordToStack_cons
  · exact stackResult439_from _
  apply compileWordToStack_cons
  · exact stackResult440_from _
  apply compileWordToStack_cons
  · exact stackResult441_from _
  apply compileWordToStack_cons
  · exact stackResult442_from _
  apply compileWordToStack_cons
  · exact stackResult443_from _
  apply compileWordToStack_cons
  · exact stackResult444_from _
  apply compileWordToStack_cons
  · exact stackResult445_from _
  apply compileWordToStack_cons
  · exact stackResult446_from _
  apply compileWordToStack_cons
  · exact stackResult447_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 1300) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 1348)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 1300 bodies frames bitmapDelta 1348 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 368).take 16).zip
      [oracle432, oracle433, oracle434, oracle435, oracle436, oracle437, oracle438, oracle439, oracle440, oracle441, oracle442, oracle443, oracle444, oracle445, oracle446, oracle447]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle432 PrefixChecks.Shard368.entry,
    wordFunction oracle433 PrefixChecks.Shard369.entry,
    wordFunction oracle434 PrefixChecks.Shard370.entry,
    wordFunction oracle435 PrefixChecks.Shard371.entry,
    wordFunction oracle436 PrefixChecks.Shard372.entry,
    wordFunction oracle437 PrefixChecks.Shard373.entry,
    wordFunction oracle438 PrefixChecks.Shard374.entry,
    wordFunction oracle439 PrefixChecks.Shard375.entry,
    wordFunction oracle440 PrefixChecks.Shard376.entry,
    wordFunction oracle441 PrefixChecks.Shard377.entry,
    wordFunction oracle442 PrefixChecks.Shard378.entry,
    wordFunction oracle443 PrefixChecks.Shard379.entry,
    wordFunction oracle444 PrefixChecks.Shard380.entry,
    wordFunction oracle445 PrefixChecks.Shard381.entry,
    wordFunction oracle446 PrefixChecks.Shard382.entry,
    wordFunction oracle447 PrefixChecks.Shard383.entry] = words
  simp only [
    Word432.wordFunction_eq,
    Word433.wordFunction_eq,
    Word434.wordFunction_eq,
    Word435.wordFunction_eq,
    Word436.wordFunction_eq,
    Word437.wordFunction_eq,
    Word438.wordFunction_eq,
    Word439.wordFunction_eq,
    Word440.wordFunction_eq,
    Word441.wordFunction_eq,
    Word442.wordFunction_eq,
    Word443.wordFunction_eq,
    Word444.wordFunction_eq,
    Word445.wordFunction_eq,
    Word446.wordFunction_eq,
    Word447.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk23
