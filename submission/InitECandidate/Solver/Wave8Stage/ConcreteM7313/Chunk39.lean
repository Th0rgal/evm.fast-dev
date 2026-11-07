import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word688
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word689
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word690
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word691
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word692
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word693
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word694
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word695
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word696
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word697
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word698
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word699
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word700
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word701
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word702
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word703
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.TableComposition
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 128000000
set_option cbv.maxSteps 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk39
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

wave8_kernel_reduce stackResult688 := WordToStack.Native.compileProgNative
  riscvConfig false Word688.program PrefixChecks.Shard624.arity registers (.nil, 2926)
theorem stackResult688_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word688.program
      PrefixChecks.Shard624.arity registers (prefixList, 2926) =
    (stackResult688.1, stackResult688.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult688.2.2.1, 2937)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word688.program
    PrefixChecks.Shard624.arity registers prefixList 2926
    stackResult688.1 stackResult688.2.1 stackResult688.2.2.1 2937 stackResult688_eq
wave8_kernel_reduce stackResult689 := WordToStack.Native.compileProgNative
  riscvConfig false Word689.program PrefixChecks.Shard625.arity registers (.nil, 2937)
theorem stackResult689_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word689.program
      PrefixChecks.Shard625.arity registers (prefixList, 2937) =
    (stackResult689.1, stackResult689.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult689.2.2.1, 2938)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word689.program
    PrefixChecks.Shard625.arity registers prefixList 2937
    stackResult689.1 stackResult689.2.1 stackResult689.2.2.1 2938 stackResult689_eq
wave8_kernel_reduce stackResult690 := WordToStack.Native.compileProgNative
  riscvConfig false Word690.program PrefixChecks.Shard626.arity registers (.nil, 2938)
theorem stackResult690_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word690.program
      PrefixChecks.Shard626.arity registers (prefixList, 2938) =
    (stackResult690.1, stackResult690.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult690.2.2.1, 2940)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word690.program
    PrefixChecks.Shard626.arity registers prefixList 2938
    stackResult690.1 stackResult690.2.1 stackResult690.2.2.1 2940 stackResult690_eq
wave8_kernel_reduce stackResult691 := WordToStack.Native.compileProgNative
  riscvConfig false Word691.program PrefixChecks.Shard627.arity registers (.nil, 2940)
theorem stackResult691_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word691.program
      PrefixChecks.Shard627.arity registers (prefixList, 2940) =
    (stackResult691.1, stackResult691.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult691.2.2.1, 2968)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word691.program
    PrefixChecks.Shard627.arity registers prefixList 2940
    stackResult691.1 stackResult691.2.1 stackResult691.2.2.1 2968 stackResult691_eq
wave8_kernel_reduce stackResult692 := WordToStack.Native.compileProgNative
  riscvConfig false Word692.program PrefixChecks.Shard628.arity registers (.nil, 2968)
theorem stackResult692_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word692.program
      PrefixChecks.Shard628.arity registers (prefixList, 2968) =
    (stackResult692.1, stackResult692.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult692.2.2.1, 2971)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word692.program
    PrefixChecks.Shard628.arity registers prefixList 2968
    stackResult692.1 stackResult692.2.1 stackResult692.2.2.1 2971 stackResult692_eq
wave8_kernel_reduce stackResult693 := WordToStack.Native.compileProgNative
  riscvConfig false Word693.program PrefixChecks.Shard629.arity registers (.nil, 2971)
theorem stackResult693_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word693.program
      PrefixChecks.Shard629.arity registers (prefixList, 2971) =
    (stackResult693.1, stackResult693.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult693.2.2.1, 3012)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word693.program
    PrefixChecks.Shard629.arity registers prefixList 2971
    stackResult693.1 stackResult693.2.1 stackResult693.2.2.1 3012 stackResult693_eq
wave8_kernel_reduce stackResult694 := WordToStack.Native.compileProgNative
  riscvConfig false Word694.program PrefixChecks.Shard630.arity registers (.nil, 3012)
theorem stackResult694_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word694.program
      PrefixChecks.Shard630.arity registers (prefixList, 3012) =
    (stackResult694.1, stackResult694.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult694.2.2.1, 3028)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word694.program
    PrefixChecks.Shard630.arity registers prefixList 3012
    stackResult694.1 stackResult694.2.1 stackResult694.2.2.1 3028 stackResult694_eq
wave8_kernel_reduce stackResult695 := WordToStack.Native.compileProgNative
  riscvConfig false Word695.program PrefixChecks.Shard631.arity registers (.nil, 3028)
theorem stackResult695_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word695.program
      PrefixChecks.Shard631.arity registers (prefixList, 3028) =
    (stackResult695.1, stackResult695.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult695.2.2.1, 3042)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word695.program
    PrefixChecks.Shard631.arity registers prefixList 3028
    stackResult695.1 stackResult695.2.1 stackResult695.2.2.1 3042 stackResult695_eq
wave8_kernel_reduce stackResult696 := WordToStack.Native.compileProgNative
  riscvConfig false Word696.program PrefixChecks.Shard632.arity registers (.nil, 3042)
theorem stackResult696_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word696.program
      PrefixChecks.Shard632.arity registers (prefixList, 3042) =
    (stackResult696.1, stackResult696.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult696.2.2.1, 3066)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word696.program
    PrefixChecks.Shard632.arity registers prefixList 3042
    stackResult696.1 stackResult696.2.1 stackResult696.2.2.1 3066 stackResult696_eq
wave8_kernel_reduce stackResult697 := WordToStack.Native.compileProgNative
  riscvConfig false Word697.program PrefixChecks.Shard633.arity registers (.nil, 3066)
theorem stackResult697_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word697.program
      PrefixChecks.Shard633.arity registers (prefixList, 3066) =
    (stackResult697.1, stackResult697.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult697.2.2.1, 3075)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word697.program
    PrefixChecks.Shard633.arity registers prefixList 3066
    stackResult697.1 stackResult697.2.1 stackResult697.2.2.1 3075 stackResult697_eq
wave8_kernel_reduce stackResult698 := WordToStack.Native.compileProgNative
  riscvConfig false Word698.program PrefixChecks.Shard634.arity registers (.nil, 3075)
theorem stackResult698_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word698.program
      PrefixChecks.Shard634.arity registers (prefixList, 3075) =
    (stackResult698.1, stackResult698.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult698.2.2.1, 3085)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word698.program
    PrefixChecks.Shard634.arity registers prefixList 3075
    stackResult698.1 stackResult698.2.1 stackResult698.2.2.1 3085 stackResult698_eq
wave8_kernel_reduce stackResult699 := WordToStack.Native.compileProgNative
  riscvConfig false Word699.program PrefixChecks.Shard635.arity registers (.nil, 3085)
theorem stackResult699_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word699.program
      PrefixChecks.Shard635.arity registers (prefixList, 3085) =
    (stackResult699.1, stackResult699.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult699.2.2.1, 3093)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word699.program
    PrefixChecks.Shard635.arity registers prefixList 3085
    stackResult699.1 stackResult699.2.1 stackResult699.2.2.1 3093 stackResult699_eq
wave8_kernel_reduce stackResult700 := WordToStack.Native.compileProgNative
  riscvConfig false Word700.program PrefixChecks.Shard636.arity registers (.nil, 3093)
theorem stackResult700_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word700.program
      PrefixChecks.Shard636.arity registers (prefixList, 3093) =
    (stackResult700.1, stackResult700.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult700.2.2.1, 3131)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word700.program
    PrefixChecks.Shard636.arity registers prefixList 3093
    stackResult700.1 stackResult700.2.1 stackResult700.2.2.1 3131 stackResult700_eq
wave8_kernel_reduce stackResult701 := WordToStack.Native.compileProgNative
  riscvConfig false Word701.program PrefixChecks.Shard637.arity registers (.nil, 3131)
theorem stackResult701_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word701.program
      PrefixChecks.Shard637.arity registers (prefixList, 3131) =
    (stackResult701.1, stackResult701.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult701.2.2.1, 3138)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word701.program
    PrefixChecks.Shard637.arity registers prefixList 3131
    stackResult701.1 stackResult701.2.1 stackResult701.2.2.1 3138 stackResult701_eq
wave8_kernel_reduce stackResult702 := WordToStack.Native.compileProgNative
  riscvConfig false Word702.program PrefixChecks.Shard638.arity registers (.nil, 3138)
theorem stackResult702_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word702.program
      PrefixChecks.Shard638.arity registers (prefixList, 3138) =
    (stackResult702.1, stackResult702.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult702.2.2.1, 3145)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word702.program
    PrefixChecks.Shard638.arity registers prefixList 3138
    stackResult702.1 stackResult702.2.1 stackResult702.2.2.1 3145 stackResult702_eq
wave8_kernel_reduce stackResult703 := WordToStack.Native.compileProgNative
  riscvConfig false Word703.program PrefixChecks.Shard639.arity registers (.nil, 3145)
theorem stackResult703_from (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileProgNative riscvConfig false Word703.program
      PrefixChecks.Shard639.arity registers (prefixList, 3145) =
    (stackResult703.1, stackResult703.2.1,
      (BitmapPrepend.prependAppList prefixList stackResult703.2.2.1, 3150)) :=
  BitmapPrepend.compileProgNative_from_nil riscvConfig false Word703.program
    PrefixChecks.Shard639.arity registers prefixList 3145
    stackResult703.1 stackResult703.2.1 stackResult703.2.2.1 3150 stackResult703_eq

noncomputable def words : List (Nat × Nat × WordLangProgHOL (BitVec 64)) := [
  (PrefixChecks.Shard624.name, PrefixChecks.Shard624.arity, Word688.program),
  (PrefixChecks.Shard625.name, PrefixChecks.Shard625.arity, Word689.program),
  (PrefixChecks.Shard626.name, PrefixChecks.Shard626.arity, Word690.program),
  (PrefixChecks.Shard627.name, PrefixChecks.Shard627.arity, Word691.program),
  (PrefixChecks.Shard628.name, PrefixChecks.Shard628.arity, Word692.program),
  (PrefixChecks.Shard629.name, PrefixChecks.Shard629.arity, Word693.program),
  (PrefixChecks.Shard630.name, PrefixChecks.Shard630.arity, Word694.program),
  (PrefixChecks.Shard631.name, PrefixChecks.Shard631.arity, Word695.program),
  (PrefixChecks.Shard632.name, PrefixChecks.Shard632.arity, Word696.program),
  (PrefixChecks.Shard633.name, PrefixChecks.Shard633.arity, Word697.program),
  (PrefixChecks.Shard634.name, PrefixChecks.Shard634.arity, Word698.program),
  (PrefixChecks.Shard635.name, PrefixChecks.Shard635.arity, Word699.program),
  (PrefixChecks.Shard636.name, PrefixChecks.Shard636.arity, Word700.program),
  (PrefixChecks.Shard637.name, PrefixChecks.Shard637.arity, Word701.program),
  (PrefixChecks.Shard638.name, PrefixChecks.Shard638.arity, Word702.program),
  (PrefixChecks.Shard639.name, PrefixChecks.Shard639.arity, Word703.program)
]

noncomputable def bodies : List (Nat × HolProg 64) := [
  (PrefixChecks.Shard624.name, stackResult688.1),
  (PrefixChecks.Shard625.name, stackResult689.1),
  (PrefixChecks.Shard626.name, stackResult690.1),
  (PrefixChecks.Shard627.name, stackResult691.1),
  (PrefixChecks.Shard628.name, stackResult692.1),
  (PrefixChecks.Shard629.name, stackResult693.1),
  (PrefixChecks.Shard630.name, stackResult694.1),
  (PrefixChecks.Shard631.name, stackResult695.1),
  (PrefixChecks.Shard632.name, stackResult696.1),
  (PrefixChecks.Shard633.name, stackResult697.1),
  (PrefixChecks.Shard634.name, stackResult698.1),
  (PrefixChecks.Shard635.name, stackResult699.1),
  (PrefixChecks.Shard636.name, stackResult700.1),
  (PrefixChecks.Shard637.name, stackResult701.1),
  (PrefixChecks.Shard638.name, stackResult702.1),
  (PrefixChecks.Shard639.name, stackResult703.1)
]

noncomputable def frames : List Nat := [
  stackResult688.2.1,
  stackResult689.2.1,
  stackResult690.2.1,
  stackResult691.2.1,
  stackResult692.2.1,
  stackResult693.2.1,
  stackResult694.2.1,
  stackResult695.2.1,
  stackResult696.2.1,
  stackResult697.2.1,
  stackResult698.2.1,
  stackResult699.2.1,
  stackResult700.2.1,
  stackResult701.2.1,
  stackResult702.2.1,
  stackResult703.2.1
]

noncomputable def bitmapDelta : AppList (BitVec 64) :=
  (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList (BitmapPrepend.prependAppList .nil stackResult688.2.2.1) stackResult689.2.2.1) stackResult690.2.2.1) stackResult691.2.2.1) stackResult692.2.2.1) stackResult693.2.2.1) stackResult694.2.2.1) stackResult695.2.2.1) stackResult696.2.2.1) stackResult697.2.2.1) stackResult698.2.2.1) stackResult699.2.2.1) stackResult700.2.2.1) stackResult701.2.2.1) stackResult702.2.2.1) stackResult703.2.2.1)

theorem compiled_nil : WordToStack.Native.compileWordToStackNative riscvConfig false registers
    words (.nil, 2926) = (bodies, frames, (bitmapDelta, 3150)) := by
  unfold words bodies frames bitmapDelta
  apply compileWordToStack_cons
  · exact stackResult688_from _
  apply compileWordToStack_cons
  · exact stackResult689_from _
  apply compileWordToStack_cons
  · exact stackResult690_from _
  apply compileWordToStack_cons
  · exact stackResult691_from _
  apply compileWordToStack_cons
  · exact stackResult692_from _
  apply compileWordToStack_cons
  · exact stackResult693_from _
  apply compileWordToStack_cons
  · exact stackResult694_from _
  apply compileWordToStack_cons
  · exact stackResult695_from _
  apply compileWordToStack_cons
  · exact stackResult696_from _
  apply compileWordToStack_cons
  · exact stackResult697_from _
  apply compileWordToStack_cons
  · exact stackResult698_from _
  apply compileWordToStack_cons
  · exact stackResult699_from _
  apply compileWordToStack_cons
  · exact stackResult700_from _
  apply compileWordToStack_cons
  · exact stackResult701_from _
  apply compileWordToStack_cons
  · exact stackResult702_from _
  apply compileWordToStack_cons
  · exact stackResult703_from _
  rfl

theorem compiled (prefixList : AppList (BitVec 64)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      words (prefixList, 2926) =
    (bodies, frames, (BitmapPrepend.prependAppList prefixList bitmapDelta, 3150)) :=
  BitmapPrepend.compileWordToStackNative_from_nil riscvConfig false registers words
    prefixList 2926 bodies frames bitmapDelta 3150 compiled_nil

theorem words_eq :
    (((ConcreteCompilerWord.source.drop 624).take 16).zip
      [oracle688, oracle689, oracle690, oracle691, oracle692, oracle693, oracle694, oracle695, oracle696, oracle697, oracle698, oracle699, oracle700, oracle701, oracle702, oracle703]).map
      (fun p => wordFunction p.2 p.1) = words := by
  change [
    wordFunction oracle688 PrefixChecks.Shard624.entry,
    wordFunction oracle689 PrefixChecks.Shard625.entry,
    wordFunction oracle690 PrefixChecks.Shard626.entry,
    wordFunction oracle691 PrefixChecks.Shard627.entry,
    wordFunction oracle692 PrefixChecks.Shard628.entry,
    wordFunction oracle693 PrefixChecks.Shard629.entry,
    wordFunction oracle694 PrefixChecks.Shard630.entry,
    wordFunction oracle695 PrefixChecks.Shard631.entry,
    wordFunction oracle696 PrefixChecks.Shard632.entry,
    wordFunction oracle697 PrefixChecks.Shard633.entry,
    wordFunction oracle698 PrefixChecks.Shard634.entry,
    wordFunction oracle699 PrefixChecks.Shard635.entry,
    wordFunction oracle700 PrefixChecks.Shard636.entry,
    wordFunction oracle701 PrefixChecks.Shard637.entry,
    wordFunction oracle702 PrefixChecks.Shard638.entry,
    wordFunction oracle703 PrefixChecks.Shard639.entry] = words
  simp only [
    Word688.wordFunction_eq,
    Word689.wordFunction_eq,
    Word690.wordFunction_eq,
    Word691.wordFunction_eq,
    Word692.wordFunction_eq,
    Word693.wordFunction_eq,
    Word694.wordFunction_eq,
    Word695.wordFunction_eq,
    Word696.wordFunction_eq,
    Word697.wordFunction_eq,
    Word698.wordFunction_eq,
    Word699.wordFunction_eq,
    Word700.wordFunction_eq,
    Word701.wordFunction_eq,
    Word702.wordFunction_eq,
    Word703.wordFunction_eq, words]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk39
