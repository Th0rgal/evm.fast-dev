import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_00
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_01
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_02
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_03
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_04
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_05
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_06
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_07
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_08
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_09
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_10
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_11
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_12
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_13
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_14
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_15
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_16
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_17
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_18
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_19
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_20
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_21
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_22
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151_23
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition

noncomputable def body00 : HolProg 64 := seqHolList Shard00.comp.1 Shard00.compTail.1
noncomputable def max00 : Nat := max Shard00.maxV Shard00.maxTail

theorem step00 :
    maxVarHOL (transform oracle151 Word151ClashTree.part5689Suffix) = max00 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part5689Suffix) (.nil, 127) (22, 15, 14) =
      (body00, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard00.parts Shard00.progs Word151ClashTree.part5689Suffix Word151ClashTree.part5944
    Shard00.maxV Shard00.maxTail Shard00.comp.1 Shard00.compTail.1 (.nil, 127)
    rfl Shard00.progs_eq Shard00.maxV_eq Shard00.maxTail_eq Shard00.comp_eq Shard00.compTail_eq


noncomputable def body01 : HolProg 64 := seqHolList Shard01.comp.1 body00
noncomputable def max01 : Nat := max Shard01.maxV max00

theorem step01 :
    maxVarHOL (transform oracle151 Word151ClashTree.part5433Suffix) = max01 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part5433Suffix) (.nil, 127) (22, 15, 14) =
      (body01, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard01.parts Shard01.progs Word151ClashTree.part5433Suffix Word151ClashTree.part5689Suffix
    Shard01.maxV max00 Shard01.comp.1 body00 (.nil, 127)
    rfl Shard01.progs_eq Shard01.maxV_eq step00.1 Shard01.comp_eq step00.2


noncomputable def body02 : HolProg 64 := seqHolList Shard02.comp.1 body01
noncomputable def max02 : Nat := max Shard02.maxV max01

theorem step02 :
    maxVarHOL (transform oracle151 Word151ClashTree.part5177Suffix) = max02 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part5177Suffix) (.nil, 127) (22, 15, 14) =
      (body02, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard02.parts Shard02.progs Word151ClashTree.part5177Suffix Word151ClashTree.part5433Suffix
    Shard02.maxV max01 Shard02.comp.1 body01 (.nil, 127)
    rfl Shard02.progs_eq Shard02.maxV_eq step01.1 Shard02.comp_eq step01.2


noncomputable def body03 : HolProg 64 := seqHolList Shard03.comp.1 body02
noncomputable def max03 : Nat := max Shard03.maxV max02

theorem step03 :
    maxVarHOL (transform oracle151 Word151ClashTree.part4921Suffix) = max03 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part4921Suffix) (.nil, 127) (22, 15, 14) =
      (body03, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard03.parts Shard03.progs Word151ClashTree.part4921Suffix Word151ClashTree.part5177Suffix
    Shard03.maxV max02 Shard03.comp.1 body02 (.nil, 127)
    rfl Shard03.progs_eq Shard03.maxV_eq step02.1 Shard03.comp_eq step02.2


noncomputable def body04 : HolProg 64 := seqHolList Shard04.comp.1 body03
noncomputable def max04 : Nat := max Shard04.maxV max03

theorem step04 :
    maxVarHOL (transform oracle151 Word151ClashTree.part4665Suffix) = max04 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part4665Suffix) (.nil, 127) (22, 15, 14) =
      (body04, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard04.parts Shard04.progs Word151ClashTree.part4665Suffix Word151ClashTree.part4921Suffix
    Shard04.maxV max03 Shard04.comp.1 body03 (.nil, 127)
    rfl Shard04.progs_eq Shard04.maxV_eq step03.1 Shard04.comp_eq step03.2


noncomputable def body05 : HolProg 64 := seqHolList Shard05.comp.1 body04
noncomputable def max05 : Nat := max Shard05.maxV max04

theorem step05 :
    maxVarHOL (transform oracle151 Word151ClashTree.part4409Suffix) = max05 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part4409Suffix) (.nil, 127) (22, 15, 14) =
      (body05, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard05.parts Shard05.progs Word151ClashTree.part4409Suffix Word151ClashTree.part4665Suffix
    Shard05.maxV max04 Shard05.comp.1 body04 (.nil, 127)
    rfl Shard05.progs_eq Shard05.maxV_eq step04.1 Shard05.comp_eq step04.2


noncomputable def body06 : HolProg 64 := seqHolList Shard06.comp.1 body05
noncomputable def max06 : Nat := max Shard06.maxV max05

theorem step06 :
    maxVarHOL (transform oracle151 Word151ClashTree.part4153Suffix) = max06 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part4153Suffix) (.nil, 127) (22, 15, 14) =
      (body06, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard06.parts Shard06.progs Word151ClashTree.part4153Suffix Word151ClashTree.part4409Suffix
    Shard06.maxV max05 Shard06.comp.1 body05 (.nil, 127)
    rfl Shard06.progs_eq Shard06.maxV_eq step05.1 Shard06.comp_eq step05.2


noncomputable def body07 : HolProg 64 := seqHolList Shard07.comp.1 body06
noncomputable def max07 : Nat := max Shard07.maxV max06

theorem step07 :
    maxVarHOL (transform oracle151 Word151ClashTree.part3897Suffix) = max07 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part3897Suffix) (.nil, 127) (22, 15, 14) =
      (body07, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard07.parts Shard07.progs Word151ClashTree.part3897Suffix Word151ClashTree.part4153Suffix
    Shard07.maxV max06 Shard07.comp.1 body06 (.nil, 127)
    rfl Shard07.progs_eq Shard07.maxV_eq step06.1 Shard07.comp_eq step06.2


noncomputable def body08 : HolProg 64 := seqHolList Shard08.comp.1 body07
noncomputable def max08 : Nat := max Shard08.maxV max07

theorem step08 :
    maxVarHOL (transform oracle151 Word151ClashTree.part3641Suffix) = max08 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part3641Suffix) (.nil, 127) (22, 15, 14) =
      (body08, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard08.parts Shard08.progs Word151ClashTree.part3641Suffix Word151ClashTree.part3897Suffix
    Shard08.maxV max07 Shard08.comp.1 body07 (.nil, 127)
    rfl Shard08.progs_eq Shard08.maxV_eq step07.1 Shard08.comp_eq step07.2


noncomputable def body09 : HolProg 64 := seqHolList Shard09.comp.1 body08
noncomputable def max09 : Nat := max Shard09.maxV max08

theorem step09 :
    maxVarHOL (transform oracle151 Word151ClashTree.part3385Suffix) = max09 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part3385Suffix) (.nil, 127) (22, 15, 14) =
      (body09, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard09.parts Shard09.progs Word151ClashTree.part3385Suffix Word151ClashTree.part3641Suffix
    Shard09.maxV max08 Shard09.comp.1 body08 (.nil, 127)
    rfl Shard09.progs_eq Shard09.maxV_eq step08.1 Shard09.comp_eq step08.2


noncomputable def body10 : HolProg 64 := seqHolList Shard10.comp.1 body09
noncomputable def max10 : Nat := max Shard10.maxV max09

theorem step10 :
    maxVarHOL (transform oracle151 Word151ClashTree.part3129Suffix) = max10 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part3129Suffix) (.nil, 127) (22, 15, 14) =
      (body10, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard10.parts Shard10.progs Word151ClashTree.part3129Suffix Word151ClashTree.part3385Suffix
    Shard10.maxV max09 Shard10.comp.1 body09 (.nil, 127)
    rfl Shard10.progs_eq Shard10.maxV_eq step09.1 Shard10.comp_eq step09.2


noncomputable def body11 : HolProg 64 := seqHolList Shard11.comp.1 body10
noncomputable def max11 : Nat := max Shard11.maxV max10

theorem step11 :
    maxVarHOL (transform oracle151 Word151ClashTree.part2873Suffix) = max11 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part2873Suffix) (.nil, 127) (22, 15, 14) =
      (body11, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard11.parts Shard11.progs Word151ClashTree.part2873Suffix Word151ClashTree.part3129Suffix
    Shard11.maxV max10 Shard11.comp.1 body10 (.nil, 127)
    rfl Shard11.progs_eq Shard11.maxV_eq step10.1 Shard11.comp_eq step10.2


noncomputable def body12 : HolProg 64 := seqHolList Shard12.comp.1 body11
noncomputable def max12 : Nat := max Shard12.maxV max11

theorem step12 :
    maxVarHOL (transform oracle151 Word151ClashTree.part2617Suffix) = max12 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part2617Suffix) (.nil, 127) (22, 15, 14) =
      (body12, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard12.parts Shard12.progs Word151ClashTree.part2617Suffix Word151ClashTree.part2873Suffix
    Shard12.maxV max11 Shard12.comp.1 body11 (.nil, 127)
    rfl Shard12.progs_eq Shard12.maxV_eq step11.1 Shard12.comp_eq step11.2


noncomputable def body13 : HolProg 64 := seqHolList Shard13.comp.1 body12
noncomputable def max13 : Nat := max Shard13.maxV max12

theorem step13 :
    maxVarHOL (transform oracle151 Word151ClashTree.part2361Suffix) = max13 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part2361Suffix) (.nil, 127) (22, 15, 14) =
      (body13, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard13.parts Shard13.progs Word151ClashTree.part2361Suffix Word151ClashTree.part2617Suffix
    Shard13.maxV max12 Shard13.comp.1 body12 (.nil, 127)
    rfl Shard13.progs_eq Shard13.maxV_eq step12.1 Shard13.comp_eq step12.2


noncomputable def body14 : HolProg 64 := seqHolList Shard14.comp.1 body13
noncomputable def max14 : Nat := max Shard14.maxV max13

theorem step14 :
    maxVarHOL (transform oracle151 Word151ClashTree.part2105Suffix) = max14 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part2105Suffix) (.nil, 127) (22, 15, 14) =
      (body14, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard14.parts Shard14.progs Word151ClashTree.part2105Suffix Word151ClashTree.part2361Suffix
    Shard14.maxV max13 Shard14.comp.1 body13 (.nil, 127)
    rfl Shard14.progs_eq Shard14.maxV_eq step13.1 Shard14.comp_eq step13.2


noncomputable def body15 : HolProg 64 := seqHolList Shard15.comp.1 body14
noncomputable def max15 : Nat := max Shard15.maxV max14

theorem step15 :
    maxVarHOL (transform oracle151 Word151ClashTree.part1849Suffix) = max15 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part1849Suffix) (.nil, 127) (22, 15, 14) =
      (body15, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard15.parts Shard15.progs Word151ClashTree.part1849Suffix Word151ClashTree.part2105Suffix
    Shard15.maxV max14 Shard15.comp.1 body14 (.nil, 127)
    rfl Shard15.progs_eq Shard15.maxV_eq step14.1 Shard15.comp_eq step14.2


noncomputable def body16 : HolProg 64 := seqHolList Shard16.comp.1 body15
noncomputable def max16 : Nat := max Shard16.maxV max15

theorem step16 :
    maxVarHOL (transform oracle151 Word151ClashTree.part1593Suffix) = max16 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part1593Suffix) (.nil, 127) (22, 15, 14) =
      (body16, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard16.parts Shard16.progs Word151ClashTree.part1593Suffix Word151ClashTree.part1849Suffix
    Shard16.maxV max15 Shard16.comp.1 body15 (.nil, 127)
    rfl Shard16.progs_eq Shard16.maxV_eq step15.1 Shard16.comp_eq step15.2


noncomputable def body17 : HolProg 64 := seqHolList Shard17.comp.1 body16
noncomputable def max17 : Nat := max Shard17.maxV max16

theorem step17 :
    maxVarHOL (transform oracle151 Word151ClashTree.part1337Suffix) = max17 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part1337Suffix) (.nil, 127) (22, 15, 14) =
      (body17, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard17.parts Shard17.progs Word151ClashTree.part1337Suffix Word151ClashTree.part1593Suffix
    Shard17.maxV max16 Shard17.comp.1 body16 (.nil, 127)
    rfl Shard17.progs_eq Shard17.maxV_eq step16.1 Shard17.comp_eq step16.2


noncomputable def body18 : HolProg 64 := seqHolList Shard18.comp.1 body17
noncomputable def max18 : Nat := max Shard18.maxV max17

theorem step18 :
    maxVarHOL (transform oracle151 Word151ClashTree.part1081Suffix) = max18 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part1081Suffix) (.nil, 127) (22, 15, 14) =
      (body18, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard18.parts Shard18.progs Word151ClashTree.part1081Suffix Word151ClashTree.part1337Suffix
    Shard18.maxV max17 Shard18.comp.1 body17 (.nil, 127)
    rfl Shard18.progs_eq Shard18.maxV_eq step17.1 Shard18.comp_eq step17.2


noncomputable def body19 : HolProg 64 := seqHolList Shard19.comp.1 body18
noncomputable def max19 : Nat := max Shard19.maxV max18

theorem step19 :
    maxVarHOL (transform oracle151 Word151ClashTree.part825Suffix) = max19 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part825Suffix) (.nil, 127) (22, 15, 14) =
      (body19, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard19.parts Shard19.progs Word151ClashTree.part825Suffix Word151ClashTree.part1081Suffix
    Shard19.maxV max18 Shard19.comp.1 body18 (.nil, 127)
    rfl Shard19.progs_eq Shard19.maxV_eq step18.1 Shard19.comp_eq step18.2


noncomputable def body20 : HolProg 64 := seqHolList Shard20.comp.1 body19
noncomputable def max20 : Nat := max Shard20.maxV max19

theorem step20 :
    maxVarHOL (transform oracle151 Word151ClashTree.part569Suffix) = max20 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part569Suffix) (.nil, 127) (22, 15, 14) =
      (body20, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard20.parts Shard20.progs Word151ClashTree.part569Suffix Word151ClashTree.part825Suffix
    Shard20.maxV max19 Shard20.comp.1 body19 (.nil, 127)
    rfl Shard20.progs_eq Shard20.maxV_eq step19.1 Shard20.comp_eq step19.2


noncomputable def body21 : HolProg 64 := seqHolList Shard21.comp.1 body20
noncomputable def max21 : Nat := max Shard21.maxV max20

theorem step21 :
    maxVarHOL (transform oracle151 Word151ClashTree.part313Suffix) = max21 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part313Suffix) (.nil, 127) (22, 15, 14) =
      (body21, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard21.parts Shard21.progs Word151ClashTree.part313Suffix Word151ClashTree.part569Suffix
    Shard21.maxV max20 Shard21.comp.1 body20 (.nil, 127)
    rfl Shard21.progs_eq Shard21.maxV_eq step20.1 Shard21.comp_eq step20.2


noncomputable def body22 : HolProg 64 := seqHolList Shard22.comp.1 body21
noncomputable def max22 : Nat := max Shard22.maxV max21

theorem step22 :
    maxVarHOL (transform oracle151 Word151ClashTree.part57Suffix) = max22 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part57Suffix) (.nil, 127) (22, 15, 14) =
      (body22, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard22.parts Shard22.progs Word151ClashTree.part57Suffix Word151ClashTree.part313Suffix
    Shard22.maxV max21 Shard22.comp.1 body21 (.nil, 127)
    rfl Shard22.progs_eq Shard22.maxV_eq step21.1 Shard22.comp_eq step21.2


noncomputable def body23 : HolProg 64 := seqHolList Shard23.comp.1 body22
noncomputable def max23 : Nat := max Shard23.maxV max22

theorem step23 :
    maxVarHOL (transform oracle151 Word151ClashTree.part0Suffix) = max23 ∧
    WordToStack.Native.compNative riscvConfig false
      (transform oracle151 Word151ClashTree.part0Suffix) (.nil, 127) (22, 15, 14) =
      (body23, (.nil, 127)) :=
  step_seqList oracle151 riscvConfig false (22, 15, 14) (.nil, 127)
    Shard23.parts Shard23.progs Word151ClashTree.part0Suffix Word151ClashTree.part57Suffix
    Shard23.maxV max22 Shard23.comp.1 body22 (.nil, 127)
    rfl Shard23.progs_eq Shard23.maxV_eq step22.1 Shard23.comp_eq step22.2


wave8_kernel_reduce max23Val := max23
theorem max23_eq : max23 = 70 := max23Val_eq

theorem program_eq_transform : Word151.program = transform oracle151 Word151ClashTree.part0Suffix := by
  change WordRemove.removeMustTerminate (WordAlloc.applyColour (WordAlloc.totalColour (oracle151.getD .ln)) PrefixChecks.Shard87.prefixProgram) = _
  rw [Word151ClashTree.prefix_eq]
  rfl

theorem maxVar_program : maxVarHOL Word151.program = 70 := by
  rw [program_eq_transform, step23.1, max23_eq]

wave8_kernel_reduce finalBody := (.seq (.stackAlloc 15) body23 : HolProg 64)

noncomputable def stackResult : HolProg 64 × Nat × (AppList (BitVec 64) × Nat) :=
  (finalBody, 15, (.nil, 127))

theorem stackResult_eq :
    WordToStack.Native.compileProgNative riscvConfig false Word151.program
      PrefixChecks.Shard87.arity registers (.nil, 127) = stackResult := by
  have h := StackCompileComposition.compile_program riscvConfig false Word151.program
    PrefixChecks.Shard87.arity registers 70 (.nil, 127) (.nil, 127) body23
    maxVar_program
  have hb : WordToStack.Native.compNative riscvConfig false Word151.program (.nil, 127)
      (registers,
        if max ((70 / 2 + 1) - registers) (PrefixChecks.Shard87.arity - registers) = 0 then 0
        else max ((70 / 2 + 1) - registers) (PrefixChecks.Shard87.arity - registers) + 1,
        max ((70 / 2 + 1) - registers) (PrefixChecks.Shard87.arity - registers)) = (body23, (.nil, 127)) := by
    rw [program_eq_transform]
    exact step23.2
  rw [h hb]
  unfold stackResult
  rw [← finalBody_eq]
  rfl

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151
