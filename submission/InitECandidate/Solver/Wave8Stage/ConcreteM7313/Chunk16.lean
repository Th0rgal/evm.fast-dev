import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word320
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word321
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word322
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word323
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word324
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word325
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word326
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word327
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word328
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word329
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word330
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word331
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word332
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word333
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word334
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word335
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk16
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult320 := WordToStack.Native.compileProgNative
  riscvConfig false Word320.program PrefixChecks.Shard256.arity registers (.nil, 895)
theorem stackResult320_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word320.program
      PrefixChecks.Shard256.arity registers (prefixList, 895) =
    (stackResult320.1, stackResult320.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult320.2.2.1, 898)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word320.program
    PrefixChecks.Shard256.arity registers prefixList 895
    stackResult320.1 stackResult320.2.1 stackResult320.2.2.1 898 stackResult320_eq
wave8_kernel_reduce stackResult321 := WordToStack.Native.compileProgNative
  riscvConfig false Word321.program PrefixChecks.Shard257.arity registers (.nil, 898)
theorem stackResult321_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word321.program
      PrefixChecks.Shard257.arity registers (prefixList, 898) =
    (stackResult321.1, stackResult321.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult321.2.2.1, 902)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word321.program
    PrefixChecks.Shard257.arity registers prefixList 898
    stackResult321.1 stackResult321.2.1 stackResult321.2.2.1 902 stackResult321_eq
wave8_kernel_reduce stackResult322 := WordToStack.Native.compileProgNative
  riscvConfig false Word322.program PrefixChecks.Shard258.arity registers (.nil, 902)
theorem stackResult322_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word322.program
      PrefixChecks.Shard258.arity registers (prefixList, 902) =
    (stackResult322.1, stackResult322.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult322.2.2.1, 913)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word322.program
    PrefixChecks.Shard258.arity registers prefixList 902
    stackResult322.1 stackResult322.2.1 stackResult322.2.2.1 913 stackResult322_eq
wave8_kernel_reduce stackResult323 := WordToStack.Native.compileProgNative
  riscvConfig false Word323.program PrefixChecks.Shard259.arity registers (.nil, 913)
theorem stackResult323_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word323.program
      PrefixChecks.Shard259.arity registers (prefixList, 913) =
    (stackResult323.1, stackResult323.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult323.2.2.1, 913)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word323.program
    PrefixChecks.Shard259.arity registers prefixList 913
    stackResult323.1 stackResult323.2.1 stackResult323.2.2.1 913 stackResult323_eq
wave8_kernel_reduce stackResult324 := WordToStack.Native.compileProgNative
  riscvConfig false Word324.program PrefixChecks.Shard260.arity registers (.nil, 913)
theorem stackResult324_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word324.program
      PrefixChecks.Shard260.arity registers (prefixList, 913) =
    (stackResult324.1, stackResult324.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult324.2.2.1, 922)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word324.program
    PrefixChecks.Shard260.arity registers prefixList 913
    stackResult324.1 stackResult324.2.1 stackResult324.2.2.1 922 stackResult324_eq
wave8_kernel_reduce stackResult325 := WordToStack.Native.compileProgNative
  riscvConfig false Word325.program PrefixChecks.Shard261.arity registers (.nil, 922)
theorem stackResult325_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word325.program
      PrefixChecks.Shard261.arity registers (prefixList, 922) =
    (stackResult325.1, stackResult325.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult325.2.2.1, 924)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word325.program
    PrefixChecks.Shard261.arity registers prefixList 922
    stackResult325.1 stackResult325.2.1 stackResult325.2.2.1 924 stackResult325_eq
wave8_kernel_reduce stackResult326 := WordToStack.Native.compileProgNative
  riscvConfig false Word326.program PrefixChecks.Shard262.arity registers (.nil, 924)
theorem stackResult326_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word326.program
      PrefixChecks.Shard262.arity registers (prefixList, 924) =
    (stackResult326.1, stackResult326.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult326.2.2.1, 924)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word326.program
    PrefixChecks.Shard262.arity registers prefixList 924
    stackResult326.1 stackResult326.2.1 stackResult326.2.2.1 924 stackResult326_eq
wave8_kernel_reduce stackResult327 := WordToStack.Native.compileProgNative
  riscvConfig false Word327.program PrefixChecks.Shard263.arity registers (.nil, 924)
theorem stackResult327_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word327.program
      PrefixChecks.Shard263.arity registers (prefixList, 924) =
    (stackResult327.1, stackResult327.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult327.2.2.1, 925)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word327.program
    PrefixChecks.Shard263.arity registers prefixList 924
    stackResult327.1 stackResult327.2.1 stackResult327.2.2.1 925 stackResult327_eq
wave8_kernel_reduce stackResult328 := WordToStack.Native.compileProgNative
  riscvConfig false Word328.program PrefixChecks.Shard264.arity registers (.nil, 925)
theorem stackResult328_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word328.program
      PrefixChecks.Shard264.arity registers (prefixList, 925) =
    (stackResult328.1, stackResult328.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult328.2.2.1, 928)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word328.program
    PrefixChecks.Shard264.arity registers prefixList 925
    stackResult328.1 stackResult328.2.1 stackResult328.2.2.1 928 stackResult328_eq
wave8_kernel_reduce stackResult329 := WordToStack.Native.compileProgNative
  riscvConfig false Word329.program PrefixChecks.Shard265.arity registers (.nil, 928)
theorem stackResult329_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word329.program
      PrefixChecks.Shard265.arity registers (prefixList, 928) =
    (stackResult329.1, stackResult329.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult329.2.2.1, 933)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word329.program
    PrefixChecks.Shard265.arity registers prefixList 928
    stackResult329.1 stackResult329.2.1 stackResult329.2.2.1 933 stackResult329_eq
wave8_kernel_reduce stackResult330 := WordToStack.Native.compileProgNative
  riscvConfig false Word330.program PrefixChecks.Shard266.arity registers (.nil, 933)
theorem stackResult330_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word330.program
      PrefixChecks.Shard266.arity registers (prefixList, 933) =
    (stackResult330.1, stackResult330.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult330.2.2.1, 936)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word330.program
    PrefixChecks.Shard266.arity registers prefixList 933
    stackResult330.1 stackResult330.2.1 stackResult330.2.2.1 936 stackResult330_eq
wave8_kernel_reduce stackResult331 := WordToStack.Native.compileProgNative
  riscvConfig false Word331.program PrefixChecks.Shard267.arity registers (.nil, 936)
theorem stackResult331_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word331.program
      PrefixChecks.Shard267.arity registers (prefixList, 936) =
    (stackResult331.1, stackResult331.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult331.2.2.1, 939)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word331.program
    PrefixChecks.Shard267.arity registers prefixList 936
    stackResult331.1 stackResult331.2.1 stackResult331.2.2.1 939 stackResult331_eq
wave8_kernel_reduce stackResult332 := WordToStack.Native.compileProgNative
  riscvConfig false Word332.program PrefixChecks.Shard268.arity registers (.nil, 939)
theorem stackResult332_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word332.program
      PrefixChecks.Shard268.arity registers (prefixList, 939) =
    (stackResult332.1, stackResult332.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult332.2.2.1, 945)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word332.program
    PrefixChecks.Shard268.arity registers prefixList 939
    stackResult332.1 stackResult332.2.1 stackResult332.2.2.1 945 stackResult332_eq
wave8_kernel_reduce stackResult333 := WordToStack.Native.compileProgNative
  riscvConfig false Word333.program PrefixChecks.Shard269.arity registers (.nil, 945)
theorem stackResult333_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word333.program
      PrefixChecks.Shard269.arity registers (prefixList, 945) =
    (stackResult333.1, stackResult333.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult333.2.2.1, 960)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word333.program
    PrefixChecks.Shard269.arity registers prefixList 945
    stackResult333.1 stackResult333.2.1 stackResult333.2.2.1 960 stackResult333_eq
wave8_kernel_reduce stackResult334 := WordToStack.Native.compileProgNative
  riscvConfig false Word334.program PrefixChecks.Shard270.arity registers (.nil, 960)
theorem stackResult334_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word334.program
      PrefixChecks.Shard270.arity registers (prefixList, 960) =
    (stackResult334.1, stackResult334.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult334.2.2.1, 968)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word334.program
    PrefixChecks.Shard270.arity registers prefixList 960
    stackResult334.1 stackResult334.2.1 stackResult334.2.2.1 968 stackResult334_eq
wave8_kernel_reduce stackResult335 := WordToStack.Native.compileProgNative
  riscvConfig false Word335.program PrefixChecks.Shard271.arity registers (.nil, 968)
theorem stackResult335_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word335.program
      PrefixChecks.Shard271.arity registers (prefixList, 968) =
    (stackResult335.1, stackResult335.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult335.2.2.1, 969)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word335.program
    PrefixChecks.Shard271.arity registers prefixList 968
    stackResult335.1 stackResult335.2.1 stackResult335.2.2.1 969 stackResult335_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard256.name, PrefixChecks.Shard256.arity, Word320.program),
  (PrefixChecks.Shard257.name, PrefixChecks.Shard257.arity, Word321.program),
  (PrefixChecks.Shard258.name, PrefixChecks.Shard258.arity, Word322.program),
  (PrefixChecks.Shard259.name, PrefixChecks.Shard259.arity, Word323.program),
  (PrefixChecks.Shard260.name, PrefixChecks.Shard260.arity, Word324.program),
  (PrefixChecks.Shard261.name, PrefixChecks.Shard261.arity, Word325.program),
  (PrefixChecks.Shard262.name, PrefixChecks.Shard262.arity, Word326.program),
  (PrefixChecks.Shard263.name, PrefixChecks.Shard263.arity, Word327.program),
  (PrefixChecks.Shard264.name, PrefixChecks.Shard264.arity, Word328.program),
  (PrefixChecks.Shard265.name, PrefixChecks.Shard265.arity, Word329.program),
  (PrefixChecks.Shard266.name, PrefixChecks.Shard266.arity, Word330.program),
  (PrefixChecks.Shard267.name, PrefixChecks.Shard267.arity, Word331.program),
  (PrefixChecks.Shard268.name, PrefixChecks.Shard268.arity, Word332.program),
  (PrefixChecks.Shard269.name, PrefixChecks.Shard269.arity, Word333.program),
  (PrefixChecks.Shard270.name, PrefixChecks.Shard270.arity, Word334.program),
  (PrefixChecks.Shard271.name, PrefixChecks.Shard271.arity, Word335.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard256.name, stackResult320.1),
  (PrefixChecks.Shard257.name, stackResult321.1),
  (PrefixChecks.Shard258.name, stackResult322.1),
  (PrefixChecks.Shard259.name, stackResult323.1),
  (PrefixChecks.Shard260.name, stackResult324.1),
  (PrefixChecks.Shard261.name, stackResult325.1),
  (PrefixChecks.Shard262.name, stackResult326.1),
  (PrefixChecks.Shard263.name, stackResult327.1),
  (PrefixChecks.Shard264.name, stackResult328.1),
  (PrefixChecks.Shard265.name, stackResult329.1),
  (PrefixChecks.Shard266.name, stackResult330.1),
  (PrefixChecks.Shard267.name, stackResult331.1),
  (PrefixChecks.Shard268.name, stackResult332.1),
  (PrefixChecks.Shard269.name, stackResult333.1),
  (PrefixChecks.Shard270.name, stackResult334.1),
  (PrefixChecks.Shard271.name, stackResult335.1)
]

noncomputable def frames : List Nat := [
  stackResult320.2.1,
  stackResult321.2.1,
  stackResult322.2.1,
  stackResult323.2.1,
  stackResult324.2.1,
  stackResult325.2.1,
  stackResult326.2.1,
  stackResult327.2.1,
  stackResult328.2.1,
  stackResult329.2.1,
  stackResult330.2.1,
  stackResult331.2.1,
  stackResult332.2.1,
  stackResult333.2.1,
  stackResult334.2.1,
  stackResult335.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult320.2.2.1) stackResult321.2.2.1) stackResult322.2.2.1) stackResult323.2.2.1) stackResult324.2.2.1) stackResult325.2.2.1) stackResult326.2.2.1) stackResult327.2.2.1) stackResult328.2.2.1) stackResult329.2.2.1) stackResult330.2.2.1) stackResult331.2.2.1) stackResult332.2.2.1) stackResult333.2.2.1) stackResult334.2.2.1) stackResult335.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 895) = (bodies, frames, (bitmapDelta, 969)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult320_from _
  apply compileWordToStack_cons
  · exact stackResult321_from _
  apply compileWordToStack_cons
  · exact stackResult322_from _
  apply compileWordToStack_cons
  · exact stackResult323_from _
  apply compileWordToStack_cons
  · exact stackResult324_from _
  apply compileWordToStack_cons
  · exact stackResult325_from _
  apply compileWordToStack_cons
  · exact stackResult326_from _
  apply compileWordToStack_cons
  · exact stackResult327_from _
  apply compileWordToStack_cons
  · exact stackResult328_from _
  apply compileWordToStack_cons
  · exact stackResult329_from _
  apply compileWordToStack_cons
  · exact stackResult330_from _
  apply compileWordToStack_cons
  · exact stackResult331_from _
  apply compileWordToStack_cons
  · exact stackResult332_from _
  apply compileWordToStack_cons
  · exact stackResult333_from _
  apply compileWordToStack_cons
  · exact stackResult334_from _
  apply compileWordToStack_cons
  · exact stackResult335_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 895) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 969)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 895 bodies frames bitmapDelta 969 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 256).take 16).zip
      [oracle320, oracle321, oracle322, oracle323, oracle324, oracle325, oracle326, oracle327, oracle328, oracle329, oracle330, oracle331, oracle332, oracle333, oracle334, oracle335]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle320 PrefixChecks.Shard256.entry,
    wordFunction oracle321 PrefixChecks.Shard257.entry,
    wordFunction oracle322 PrefixChecks.Shard258.entry,
    wordFunction oracle323 PrefixChecks.Shard259.entry,
    wordFunction oracle324 PrefixChecks.Shard260.entry,
    wordFunction oracle325 PrefixChecks.Shard261.entry,
    wordFunction oracle326 PrefixChecks.Shard262.entry,
    wordFunction oracle327 PrefixChecks.Shard263.entry,
    wordFunction oracle328 PrefixChecks.Shard264.entry,
    wordFunction oracle329 PrefixChecks.Shard265.entry,
    wordFunction oracle330 PrefixChecks.Shard266.entry,
    wordFunction oracle331 PrefixChecks.Shard267.entry,
    wordFunction oracle332 PrefixChecks.Shard268.entry,
    wordFunction oracle333 PrefixChecks.Shard269.entry,
    wordFunction oracle334 PrefixChecks.Shard270.entry,
    wordFunction oracle335 PrefixChecks.Shard271.entry] = words
  simp only [
    Word320.wordFunction_eq,
    Word321.wordFunction_eq,
    Word322.wordFunction_eq,
    Word323.wordFunction_eq,
    Word324.wordFunction_eq,
    Word325.wordFunction_eq,
    Word326.wordFunction_eq,
    Word327.wordFunction_eq,
    Word328.wordFunction_eq,
    Word329.wordFunction_eq,
    Word330.wordFunction_eq,
    Word331.wordFunction_eq,
    Word332.wordFunction_eq,
    Word333.wordFunction_eq,
    Word334.wordFunction_eq,
    Word335.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk16
