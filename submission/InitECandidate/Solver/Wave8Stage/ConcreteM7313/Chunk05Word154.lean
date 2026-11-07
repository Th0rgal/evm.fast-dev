import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154_00
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154_01
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154_02
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154_03
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154_04
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154_05
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154_06
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154_07
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154_08
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154_09
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154_10
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154_11
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154_12
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154_13
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154_14
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154_15
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154_16
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154_17
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154_18
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154_19
import InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard90

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition Chunk05Stack151

noncomputable def raw00 : WordLangProgHOL (BitVec 64) := Block00.rawSuffix
noncomputable def tree00 : RegAlloc.ClashTree := seqTreeList Block00.trees Block00.treeTail
noncomputable def chk00 : Option (Spt Unit × Spt Unit) := Block00.chk
noncomputable def body00 : HolProg 64 := seqHolList Block00.comp.1 Block00.compTail.1
noncomputable def max00 : Nat := max Block00.maxV Block00.maxTail

theorem stackTail00 : everyStackVarHOL stackPred
    (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) Block00.p9809) = true := by
  rw [Block00.colTail_eq]
  exact Block00.stackTail_eq

theorem step00 :
    WordAlloc.getClashTree raw00 [] = tree00 ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree00 .ln .ln = chk00 ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) raw00) = true ∧
    (WordAlloc.getForced riscvConfig raw00 []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 raw00) = max00 ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 raw00) (.nil, 136) (22, 13, 12) =
      (body00, (.nil, 136)) :=
  step_word154 Block00.parts Block00.colPs Block00.progs Block00.trees raw00 Block00.p9809
    Block00.treeTail Block00.chkTail chk00 Block00.maxV Block00.maxTail
    Block00.comp.1 Block00.compTail.1 (.nil, 136) (.nil, 136)
    rfl Block00.trees_eq Block00.treeTail_eq Block00.chkTail_eq Block00.chk_eq
    Block00.colPs_eq Block00.stackOk_eq stackTail00
    Block00.forcedOk_eq Block00.forcedTail_eq
    Block00.progs_eq Block00.maxV_eq Block00.maxTail_eq
    Block00.comp_eq Block00.compTail_eq


noncomputable def raw01 : WordLangProgHOL (BitVec 64) := seqList Block01.parts raw00
noncomputable def tree01 : RegAlloc.ClashTree := seqTreeList Block01.trees tree00
wave8_kernel_reduce chk01 := checkTreeList (WordAlloc.totalColour (oracle154.getD .ln)) Block01.trees chk00
noncomputable def body01 : HolProg 64 := seqHolList Block01.comp.1 body00
noncomputable def max01 : Nat := max Block01.maxV max00

theorem step01 :
    WordAlloc.getClashTree raw01 [] = tree01 ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree01 .ln .ln = chk01 ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) raw01) = true ∧
    (WordAlloc.getForced riscvConfig raw01 []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 raw01) = max01 ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 raw01) (.nil, 136) (22, 13, 12) =
      (body01, (.nil, 136)) :=
  step_word154 Block01.parts Block01.colPs Block01.progs Block01.trees raw01 raw00
    tree00 chk00 chk01 Block01.maxV max00
    Block01.comp.1 body00 (.nil, 136) (.nil, 136)
    rfl Block01.trees_eq step00.1 step00.2.1 chk01_eq
    Block01.colPs_eq Block01.stackOk_eq step00.2.2.1
    Block01.forcedOk_eq step00.2.2.2.1
    Block01.progs_eq Block01.maxV_eq step00.2.2.2.2.1
    Block01.comp_eq step00.2.2.2.2.2


noncomputable def raw02 : WordLangProgHOL (BitVec 64) := seqList Block02.parts raw01
noncomputable def tree02 : RegAlloc.ClashTree := seqTreeList Block02.trees tree01
wave8_kernel_reduce chk02 := checkTreeList (WordAlloc.totalColour (oracle154.getD .ln)) Block02.trees chk01
noncomputable def body02 : HolProg 64 := seqHolList Block02.comp.1 body01
noncomputable def max02 : Nat := max Block02.maxV max01

theorem step02 :
    WordAlloc.getClashTree raw02 [] = tree02 ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree02 .ln .ln = chk02 ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) raw02) = true ∧
    (WordAlloc.getForced riscvConfig raw02 []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 raw02) = max02 ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 raw02) (.nil, 136) (22, 13, 12) =
      (body02, (.nil, 136)) :=
  step_word154 Block02.parts Block02.colPs Block02.progs Block02.trees raw02 raw01
    tree01 chk01 chk02 Block02.maxV max01
    Block02.comp.1 body01 (.nil, 136) (.nil, 136)
    rfl Block02.trees_eq step01.1 step01.2.1 chk02_eq
    Block02.colPs_eq Block02.stackOk_eq step01.2.2.1
    Block02.forcedOk_eq step01.2.2.2.1
    Block02.progs_eq Block02.maxV_eq step01.2.2.2.2.1
    Block02.comp_eq step01.2.2.2.2.2


noncomputable def raw03 : WordLangProgHOL (BitVec 64) := seqList Block03.parts raw02
noncomputable def tree03 : RegAlloc.ClashTree := seqTreeList Block03.trees tree02
wave8_kernel_reduce chk03 := checkTreeList (WordAlloc.totalColour (oracle154.getD .ln)) Block03.trees chk02
noncomputable def body03 : HolProg 64 := seqHolList Block03.comp.1 body02
noncomputable def max03 : Nat := max Block03.maxV max02

theorem step03 :
    WordAlloc.getClashTree raw03 [] = tree03 ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree03 .ln .ln = chk03 ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) raw03) = true ∧
    (WordAlloc.getForced riscvConfig raw03 []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 raw03) = max03 ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 raw03) (.nil, 136) (22, 13, 12) =
      (body03, (.nil, 136)) :=
  step_word154 Block03.parts Block03.colPs Block03.progs Block03.trees raw03 raw02
    tree02 chk02 chk03 Block03.maxV max02
    Block03.comp.1 body02 (.nil, 136) (.nil, 136)
    rfl Block03.trees_eq step02.1 step02.2.1 chk03_eq
    Block03.colPs_eq Block03.stackOk_eq step02.2.2.1
    Block03.forcedOk_eq step02.2.2.2.1
    Block03.progs_eq Block03.maxV_eq step02.2.2.2.2.1
    Block03.comp_eq step02.2.2.2.2.2


noncomputable def raw04 : WordLangProgHOL (BitVec 64) := seqList Block04.parts raw03
noncomputable def tree04 : RegAlloc.ClashTree := seqTreeList Block04.trees tree03
wave8_kernel_reduce chk04 := checkTreeList (WordAlloc.totalColour (oracle154.getD .ln)) Block04.trees chk03
noncomputable def body04 : HolProg 64 := seqHolList Block04.comp.1 body03
noncomputable def max04 : Nat := max Block04.maxV max03

theorem step04 :
    WordAlloc.getClashTree raw04 [] = tree04 ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree04 .ln .ln = chk04 ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) raw04) = true ∧
    (WordAlloc.getForced riscvConfig raw04 []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 raw04) = max04 ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 raw04) (.nil, 136) (22, 13, 12) =
      (body04, (.nil, 136)) :=
  step_word154 Block04.parts Block04.colPs Block04.progs Block04.trees raw04 raw03
    tree03 chk03 chk04 Block04.maxV max03
    Block04.comp.1 body03 (.nil, 136) (.nil, 136)
    rfl Block04.trees_eq step03.1 step03.2.1 chk04_eq
    Block04.colPs_eq Block04.stackOk_eq step03.2.2.1
    Block04.forcedOk_eq step03.2.2.2.1
    Block04.progs_eq Block04.maxV_eq step03.2.2.2.2.1
    Block04.comp_eq step03.2.2.2.2.2


noncomputable def raw05 : WordLangProgHOL (BitVec 64) := seqList Block05.parts raw04
noncomputable def tree05 : RegAlloc.ClashTree := seqTreeList Block05.trees tree04
wave8_kernel_reduce chk05 := checkTreeList (WordAlloc.totalColour (oracle154.getD .ln)) Block05.trees chk04
noncomputable def body05 : HolProg 64 := seqHolList Block05.comp.1 body04
noncomputable def max05 : Nat := max Block05.maxV max04

theorem step05 :
    WordAlloc.getClashTree raw05 [] = tree05 ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree05 .ln .ln = chk05 ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) raw05) = true ∧
    (WordAlloc.getForced riscvConfig raw05 []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 raw05) = max05 ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 raw05) (.nil, 136) (22, 13, 12) =
      (body05, (.nil, 136)) :=
  step_word154 Block05.parts Block05.colPs Block05.progs Block05.trees raw05 raw04
    tree04 chk04 chk05 Block05.maxV max04
    Block05.comp.1 body04 (.nil, 136) (.nil, 136)
    rfl Block05.trees_eq step04.1 step04.2.1 chk05_eq
    Block05.colPs_eq Block05.stackOk_eq step04.2.2.1
    Block05.forcedOk_eq step04.2.2.2.1
    Block05.progs_eq Block05.maxV_eq step04.2.2.2.2.1
    Block05.comp_eq step04.2.2.2.2.2


noncomputable def raw06 : WordLangProgHOL (BitVec 64) := seqList Block06.parts raw05
noncomputable def tree06 : RegAlloc.ClashTree := seqTreeList Block06.trees tree05
wave8_kernel_reduce chk06 := checkTreeList (WordAlloc.totalColour (oracle154.getD .ln)) Block06.trees chk05
noncomputable def body06 : HolProg 64 := seqHolList Block06.comp.1 body05
noncomputable def max06 : Nat := max Block06.maxV max05

theorem step06 :
    WordAlloc.getClashTree raw06 [] = tree06 ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree06 .ln .ln = chk06 ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) raw06) = true ∧
    (WordAlloc.getForced riscvConfig raw06 []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 raw06) = max06 ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 raw06) (.nil, 136) (22, 13, 12) =
      (body06, (.nil, 136)) :=
  step_word154 Block06.parts Block06.colPs Block06.progs Block06.trees raw06 raw05
    tree05 chk05 chk06 Block06.maxV max05
    Block06.comp.1 body05 (.nil, 136) (.nil, 136)
    rfl Block06.trees_eq step05.1 step05.2.1 chk06_eq
    Block06.colPs_eq Block06.stackOk_eq step05.2.2.1
    Block06.forcedOk_eq step05.2.2.2.1
    Block06.progs_eq Block06.maxV_eq step05.2.2.2.2.1
    Block06.comp_eq step05.2.2.2.2.2


noncomputable def raw07 : WordLangProgHOL (BitVec 64) := seqList Block07.parts raw06
noncomputable def tree07 : RegAlloc.ClashTree := seqTreeList Block07.trees tree06
wave8_kernel_reduce chk07 := checkTreeList (WordAlloc.totalColour (oracle154.getD .ln)) Block07.trees chk06
noncomputable def body07 : HolProg 64 := seqHolList Block07.comp.1 body06
noncomputable def max07 : Nat := max Block07.maxV max06

theorem step07 :
    WordAlloc.getClashTree raw07 [] = tree07 ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree07 .ln .ln = chk07 ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) raw07) = true ∧
    (WordAlloc.getForced riscvConfig raw07 []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 raw07) = max07 ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 raw07) (.nil, 136) (22, 13, 12) =
      (body07, (.nil, 136)) :=
  step_word154 Block07.parts Block07.colPs Block07.progs Block07.trees raw07 raw06
    tree06 chk06 chk07 Block07.maxV max06
    Block07.comp.1 body06 (.nil, 136) (.nil, 136)
    rfl Block07.trees_eq step06.1 step06.2.1 chk07_eq
    Block07.colPs_eq Block07.stackOk_eq step06.2.2.1
    Block07.forcedOk_eq step06.2.2.2.1
    Block07.progs_eq Block07.maxV_eq step06.2.2.2.2.1
    Block07.comp_eq step06.2.2.2.2.2


noncomputable def raw08 : WordLangProgHOL (BitVec 64) := seqList Block08.parts raw07
noncomputable def tree08 : RegAlloc.ClashTree := seqTreeList Block08.trees tree07
wave8_kernel_reduce chk08 := checkTreeList (WordAlloc.totalColour (oracle154.getD .ln)) Block08.trees chk07
noncomputable def body08 : HolProg 64 := seqHolList Block08.comp.1 body07
noncomputable def max08 : Nat := max Block08.maxV max07

theorem step08 :
    WordAlloc.getClashTree raw08 [] = tree08 ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree08 .ln .ln = chk08 ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) raw08) = true ∧
    (WordAlloc.getForced riscvConfig raw08 []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 raw08) = max08 ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 raw08) (.nil, 136) (22, 13, 12) =
      (body08, (.nil, 136)) :=
  step_word154 Block08.parts Block08.colPs Block08.progs Block08.trees raw08 raw07
    tree07 chk07 chk08 Block08.maxV max07
    Block08.comp.1 body07 (.nil, 136) (.nil, 136)
    rfl Block08.trees_eq step07.1 step07.2.1 chk08_eq
    Block08.colPs_eq Block08.stackOk_eq step07.2.2.1
    Block08.forcedOk_eq step07.2.2.2.1
    Block08.progs_eq Block08.maxV_eq step07.2.2.2.2.1
    Block08.comp_eq step07.2.2.2.2.2


noncomputable def raw09 : WordLangProgHOL (BitVec 64) := seqList Block09.parts raw08
noncomputable def tree09 : RegAlloc.ClashTree := seqTreeList Block09.trees tree08
wave8_kernel_reduce chk09 := checkTreeList (WordAlloc.totalColour (oracle154.getD .ln)) Block09.trees chk08
noncomputable def body09 : HolProg 64 := seqHolList Block09.comp.1 body08
noncomputable def max09 : Nat := max Block09.maxV max08

theorem step09 :
    WordAlloc.getClashTree raw09 [] = tree09 ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree09 .ln .ln = chk09 ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) raw09) = true ∧
    (WordAlloc.getForced riscvConfig raw09 []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 raw09) = max09 ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 raw09) (.nil, 136) (22, 13, 12) =
      (body09, (.nil, 136)) :=
  step_word154 Block09.parts Block09.colPs Block09.progs Block09.trees raw09 raw08
    tree08 chk08 chk09 Block09.maxV max08
    Block09.comp.1 body08 (.nil, 136) (.nil, 136)
    rfl Block09.trees_eq step08.1 step08.2.1 chk09_eq
    Block09.colPs_eq Block09.stackOk_eq step08.2.2.1
    Block09.forcedOk_eq step08.2.2.2.1
    Block09.progs_eq Block09.maxV_eq step08.2.2.2.2.1
    Block09.comp_eq step08.2.2.2.2.2


noncomputable def raw10 : WordLangProgHOL (BitVec 64) := seqList Block10.parts raw09
noncomputable def tree10 : RegAlloc.ClashTree := seqTreeList Block10.trees tree09
wave8_kernel_reduce chk10 := checkTreeList (WordAlloc.totalColour (oracle154.getD .ln)) Block10.trees chk09
noncomputable def body10 : HolProg 64 := seqHolList Block10.comp.1 body09
noncomputable def max10 : Nat := max Block10.maxV max09

theorem step10 :
    WordAlloc.getClashTree raw10 [] = tree10 ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree10 .ln .ln = chk10 ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) raw10) = true ∧
    (WordAlloc.getForced riscvConfig raw10 []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 raw10) = max10 ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 raw10) (.nil, 136) (22, 13, 12) =
      (body10, (.nil, 136)) :=
  step_word154 Block10.parts Block10.colPs Block10.progs Block10.trees raw10 raw09
    tree09 chk09 chk10 Block10.maxV max09
    Block10.comp.1 body09 (.nil, 136) (.nil, 136)
    rfl Block10.trees_eq step09.1 step09.2.1 chk10_eq
    Block10.colPs_eq Block10.stackOk_eq step09.2.2.1
    Block10.forcedOk_eq step09.2.2.2.1
    Block10.progs_eq Block10.maxV_eq step09.2.2.2.2.1
    Block10.comp_eq step09.2.2.2.2.2


noncomputable def raw11 : WordLangProgHOL (BitVec 64) := seqList Block11.parts raw10
noncomputable def tree11 : RegAlloc.ClashTree := seqTreeList Block11.trees tree10
wave8_kernel_reduce chk11 := checkTreeList (WordAlloc.totalColour (oracle154.getD .ln)) Block11.trees chk10
noncomputable def body11 : HolProg 64 := seqHolList Block11.comp.1 body10
noncomputable def max11 : Nat := max Block11.maxV max10

theorem step11 :
    WordAlloc.getClashTree raw11 [] = tree11 ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree11 .ln .ln = chk11 ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) raw11) = true ∧
    (WordAlloc.getForced riscvConfig raw11 []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 raw11) = max11 ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 raw11) (.nil, 136) (22, 13, 12) =
      (body11, (.nil, 136)) :=
  step_word154 Block11.parts Block11.colPs Block11.progs Block11.trees raw11 raw10
    tree10 chk10 chk11 Block11.maxV max10
    Block11.comp.1 body10 (.nil, 136) (.nil, 136)
    rfl Block11.trees_eq step10.1 step10.2.1 chk11_eq
    Block11.colPs_eq Block11.stackOk_eq step10.2.2.1
    Block11.forcedOk_eq step10.2.2.2.1
    Block11.progs_eq Block11.maxV_eq step10.2.2.2.2.1
    Block11.comp_eq step10.2.2.2.2.2


noncomputable def raw12 : WordLangProgHOL (BitVec 64) := seqList Block12.parts raw11
noncomputable def tree12 : RegAlloc.ClashTree := seqTreeList Block12.trees tree11
wave8_kernel_reduce chk12 := checkTreeList (WordAlloc.totalColour (oracle154.getD .ln)) Block12.trees chk11
noncomputable def body12 : HolProg 64 := seqHolList Block12.comp.1 body11
noncomputable def max12 : Nat := max Block12.maxV max11

theorem step12 :
    WordAlloc.getClashTree raw12 [] = tree12 ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree12 .ln .ln = chk12 ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) raw12) = true ∧
    (WordAlloc.getForced riscvConfig raw12 []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 raw12) = max12 ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 raw12) (.nil, 136) (22, 13, 12) =
      (body12, (.nil, 136)) :=
  step_word154 Block12.parts Block12.colPs Block12.progs Block12.trees raw12 raw11
    tree11 chk11 chk12 Block12.maxV max11
    Block12.comp.1 body11 (.nil, 136) (.nil, 136)
    rfl Block12.trees_eq step11.1 step11.2.1 chk12_eq
    Block12.colPs_eq Block12.stackOk_eq step11.2.2.1
    Block12.forcedOk_eq step11.2.2.2.1
    Block12.progs_eq Block12.maxV_eq step11.2.2.2.2.1
    Block12.comp_eq step11.2.2.2.2.2


noncomputable def raw13 : WordLangProgHOL (BitVec 64) := seqList Block13.parts raw12
noncomputable def tree13 : RegAlloc.ClashTree := seqTreeList Block13.trees tree12
wave8_kernel_reduce chk13 := checkTreeList (WordAlloc.totalColour (oracle154.getD .ln)) Block13.trees chk12
noncomputable def body13 : HolProg 64 := seqHolList Block13.comp.1 body12
noncomputable def max13 : Nat := max Block13.maxV max12

theorem step13 :
    WordAlloc.getClashTree raw13 [] = tree13 ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree13 .ln .ln = chk13 ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) raw13) = true ∧
    (WordAlloc.getForced riscvConfig raw13 []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 raw13) = max13 ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 raw13) (.nil, 136) (22, 13, 12) =
      (body13, (.nil, 136)) :=
  step_word154 Block13.parts Block13.colPs Block13.progs Block13.trees raw13 raw12
    tree12 chk12 chk13 Block13.maxV max12
    Block13.comp.1 body12 (.nil, 136) (.nil, 136)
    rfl Block13.trees_eq step12.1 step12.2.1 chk13_eq
    Block13.colPs_eq Block13.stackOk_eq step12.2.2.1
    Block13.forcedOk_eq step12.2.2.2.1
    Block13.progs_eq Block13.maxV_eq step12.2.2.2.2.1
    Block13.comp_eq step12.2.2.2.2.2


noncomputable def raw14 : WordLangProgHOL (BitVec 64) := seqList Block14.parts raw13
noncomputable def tree14 : RegAlloc.ClashTree := seqTreeList Block14.trees tree13
wave8_kernel_reduce chk14 := checkTreeList (WordAlloc.totalColour (oracle154.getD .ln)) Block14.trees chk13
noncomputable def body14 : HolProg 64 := seqHolList Block14.comp.1 body13
noncomputable def max14 : Nat := max Block14.maxV max13

theorem step14 :
    WordAlloc.getClashTree raw14 [] = tree14 ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree14 .ln .ln = chk14 ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) raw14) = true ∧
    (WordAlloc.getForced riscvConfig raw14 []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 raw14) = max14 ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 raw14) (.nil, 136) (22, 13, 12) =
      (body14, (.nil, 136)) :=
  step_word154 Block14.parts Block14.colPs Block14.progs Block14.trees raw14 raw13
    tree13 chk13 chk14 Block14.maxV max13
    Block14.comp.1 body13 (.nil, 136) (.nil, 136)
    rfl Block14.trees_eq step13.1 step13.2.1 chk14_eq
    Block14.colPs_eq Block14.stackOk_eq step13.2.2.1
    Block14.forcedOk_eq step13.2.2.2.1
    Block14.progs_eq Block14.maxV_eq step13.2.2.2.2.1
    Block14.comp_eq step13.2.2.2.2.2


noncomputable def raw15 : WordLangProgHOL (BitVec 64) := seqList Block15.parts raw14
noncomputable def tree15 : RegAlloc.ClashTree := seqTreeList Block15.trees tree14
wave8_kernel_reduce chk15 := checkTreeList (WordAlloc.totalColour (oracle154.getD .ln)) Block15.trees chk14
noncomputable def body15 : HolProg 64 := seqHolList Block15.comp.1 body14
noncomputable def max15 : Nat := max Block15.maxV max14

theorem step15 :
    WordAlloc.getClashTree raw15 [] = tree15 ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree15 .ln .ln = chk15 ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) raw15) = true ∧
    (WordAlloc.getForced riscvConfig raw15 []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 raw15) = max15 ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 raw15) (.nil, 136) (22, 13, 12) =
      (body15, (.nil, 136)) :=
  step_word154 Block15.parts Block15.colPs Block15.progs Block15.trees raw15 raw14
    tree14 chk14 chk15 Block15.maxV max14
    Block15.comp.1 body14 (.nil, 136) (.nil, 136)
    rfl Block15.trees_eq step14.1 step14.2.1 chk15_eq
    Block15.colPs_eq Block15.stackOk_eq step14.2.2.1
    Block15.forcedOk_eq step14.2.2.2.1
    Block15.progs_eq Block15.maxV_eq step14.2.2.2.2.1
    Block15.comp_eq step14.2.2.2.2.2


noncomputable def raw16 : WordLangProgHOL (BitVec 64) := seqList Block16.parts raw15
noncomputable def tree16 : RegAlloc.ClashTree := seqTreeList Block16.trees tree15
wave8_kernel_reduce chk16 := checkTreeList (WordAlloc.totalColour (oracle154.getD .ln)) Block16.trees chk15
noncomputable def body16 : HolProg 64 := seqHolList Block16.comp.1 body15
noncomputable def max16 : Nat := max Block16.maxV max15

theorem step16 :
    WordAlloc.getClashTree raw16 [] = tree16 ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree16 .ln .ln = chk16 ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) raw16) = true ∧
    (WordAlloc.getForced riscvConfig raw16 []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 raw16) = max16 ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 raw16) (.nil, 136) (22, 13, 12) =
      (body16, (.nil, 136)) :=
  step_word154 Block16.parts Block16.colPs Block16.progs Block16.trees raw16 raw15
    tree15 chk15 chk16 Block16.maxV max15
    Block16.comp.1 body15 (.nil, 136) (.nil, 136)
    rfl Block16.trees_eq step15.1 step15.2.1 chk16_eq
    Block16.colPs_eq Block16.stackOk_eq step15.2.2.1
    Block16.forcedOk_eq step15.2.2.2.1
    Block16.progs_eq Block16.maxV_eq step15.2.2.2.2.1
    Block16.comp_eq step15.2.2.2.2.2


noncomputable def raw17 : WordLangProgHOL (BitVec 64) := seqList Block17.parts raw16
noncomputable def tree17 : RegAlloc.ClashTree := seqTreeList Block17.trees tree16
wave8_kernel_reduce chk17 := checkTreeList (WordAlloc.totalColour (oracle154.getD .ln)) Block17.trees chk16
noncomputable def body17 : HolProg 64 := seqHolList Block17.comp.1 body16
noncomputable def max17 : Nat := max Block17.maxV max16

theorem step17 :
    WordAlloc.getClashTree raw17 [] = tree17 ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree17 .ln .ln = chk17 ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) raw17) = true ∧
    (WordAlloc.getForced riscvConfig raw17 []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 raw17) = max17 ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 raw17) (.nil, 136) (22, 13, 12) =
      (body17, (.nil, 136)) :=
  step_word154 Block17.parts Block17.colPs Block17.progs Block17.trees raw17 raw16
    tree16 chk16 chk17 Block17.maxV max16
    Block17.comp.1 body16 (.nil, 136) (.nil, 136)
    rfl Block17.trees_eq step16.1 step16.2.1 chk17_eq
    Block17.colPs_eq Block17.stackOk_eq step16.2.2.1
    Block17.forcedOk_eq step16.2.2.2.1
    Block17.progs_eq Block17.maxV_eq step16.2.2.2.2.1
    Block17.comp_eq step16.2.2.2.2.2


noncomputable def raw18 : WordLangProgHOL (BitVec 64) := seqList Block18.parts raw17
noncomputable def tree18 : RegAlloc.ClashTree := seqTreeList Block18.trees tree17
wave8_kernel_reduce chk18 := checkTreeList (WordAlloc.totalColour (oracle154.getD .ln)) Block18.trees chk17
noncomputable def body18 : HolProg 64 := seqHolList Block18.comp.1 body17
noncomputable def max18 : Nat := max Block18.maxV max17

theorem step18 :
    WordAlloc.getClashTree raw18 [] = tree18 ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree18 .ln .ln = chk18 ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) raw18) = true ∧
    (WordAlloc.getForced riscvConfig raw18 []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 raw18) = max18 ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 raw18) (.nil, 136) (22, 13, 12) =
      (body18, (.nil, 136)) :=
  step_word154 Block18.parts Block18.colPs Block18.progs Block18.trees raw18 raw17
    tree17 chk17 chk18 Block18.maxV max17
    Block18.comp.1 body17 (.nil, 136) (.nil, 136)
    rfl Block18.trees_eq step17.1 step17.2.1 chk18_eq
    Block18.colPs_eq Block18.stackOk_eq step17.2.2.1
    Block18.forcedOk_eq step17.2.2.2.1
    Block18.progs_eq Block18.maxV_eq step17.2.2.2.2.1
    Block18.comp_eq step17.2.2.2.2.2


noncomputable def raw19 : WordLangProgHOL (BitVec 64) := seqList Block19.parts raw18
noncomputable def tree19 : RegAlloc.ClashTree := seqTreeList Block19.trees tree18
wave8_kernel_reduce chk19 := checkTreeList (WordAlloc.totalColour (oracle154.getD .ln)) Block19.trees chk18
noncomputable def body19 : HolProg 64 := seqHolList Block19.comp.1 body18
noncomputable def max19 : Nat := max Block19.maxV max18

theorem step19 :
    WordAlloc.getClashTree raw19 [] = tree19 ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree19 .ln .ln = chk19 ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) raw19) = true ∧
    (WordAlloc.getForced riscvConfig raw19 []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 raw19) = max19 ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 raw19) (.nil, 136) (22, 13, 12) =
      (body19, (.nil, 136)) :=
  step_word154 Block19.parts Block19.colPs Block19.progs Block19.trees raw19 raw18
    tree18 chk18 chk19 Block19.maxV max18
    Block19.comp.1 body18 (.nil, 136) (.nil, 136)
    rfl Block19.trees_eq step18.1 step18.2.1 chk19_eq
    Block19.colPs_eq Block19.stackOk_eq step18.2.2.1
    Block19.forcedOk_eq step18.2.2.2.1
    Block19.progs_eq Block19.maxV_eq step18.2.2.2.2.1
    Block19.comp_eq step18.2.2.2.2.2


theorem prefix_eq_raw19 : PrefixChecks.Shard90.prefixProgram = raw19 := by rfl

wave8_kernel_reduce evenVal := WordAlloc.everyEvenColour (oracle154.getD .ln)
wave8_kernel_reduce chk19Ok := chk19.isSome
wave8_kernel_reduce max19Val := max19

theorem checked19 : (RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) tree19 .ln .ln).isSome = true := by
  rw [step19.2.1]
  exact chk19Ok_eq

noncomputable def allocated : WordLangProgHOL (BitVec 64) :=
  WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) PrefixChecks.Shard90.prefixProgram

noncomputable def program : WordLangProgHOL (BitVec 64) :=
  WordRemove.removeMustTerminate allocated

theorem accepted :
    WordAlloc.oracleColourOk registers oracle154 tree19 PrefixChecks.Shard90.prefixProgram
      (WordAlloc.getForced riscvConfig PrefixChecks.Shard90.prefixProgram []) = some allocated := by
  refine Word151Allocation.accept registers (oracle154.getD .ln) tree19 PrefixChecks.Shard90.prefixProgram
    (WordAlloc.getForced riscvConfig PrefixChecks.Shard90.prefixProgram []) evenVal_eq checked19 ?_ ?_
  · rw [prefix_eq_raw19]; exact step19.2.2.1
  · rw [prefix_eq_raw19]; exact step19.2.2.2.1

theorem allocated_eq :
    WordToWord.wordAllocWith RegAlloc.regAllocExecutable PrefixChecks.Shard90.name riscvConfig
      (InitE.oracleCompilerConfig []).wordToWordConf.regAlg registers
      PrefixChecks.Shard90.prefixProgram oracle154 = allocated := by
  refine Word151Allocation.alloc_of_accept RegAlloc.regAllocExecutable PrefixChecks.Shard90.name _
    registers riscvConfig PrefixChecks.Shard90.prefixProgram allocated oracle154 tree19 ?_ accepted
  rw [prefix_eq_raw19]
  exact step19.1

theorem wordFunction_eq :
    wordFunction oracle154 PrefixChecks.Shard90.entry =
      (PrefixChecks.Shard90.name, PrefixChecks.Shard90.arity, program) := by
  unfold wordFunction
  rw [PrefixChecks.Shard90.word_eq.trans PrefixChecks.Shard90.wordCompileEq,
    PrefixChecks.Shard90.arity_eq, PrefixChecks.Shard90.name_eq,
    PrefixChecks.Shard90.prefixCompileEq, allocated_eq]
  rfl

theorem program_eq_transform : program = transform oracle154 raw19 := by
  change WordRemove.removeMustTerminate
    (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) PrefixChecks.Shard90.prefixProgram) = _
  rw [prefix_eq_raw19]
  rfl

theorem maxVar_program : maxVarHOL program = 66 := by
  rw [program_eq_transform, step19.2.2.2.2.1]
  exact max19Val_eq

wave8_kernel_reduce finalBody := (.seq (.stackAlloc 13) body19 : HolProg 64)

noncomputable def stackResult : HolProg 64 × Nat × (AppList (BitVec 64) × Nat) :=
  (finalBody, 13, (.nil, 136))

theorem stackResult_eq :
    WordToStack.Native.compileProgNative riscvConfig false program
      PrefixChecks.Shard90.arity registers (.nil, 136) = stackResult := by
  have h := StackCompileComposition.compile_program riscvConfig false program
    PrefixChecks.Shard90.arity registers 66 (.nil, 136) (.nil, 136) body19
    maxVar_program
  have hb : WordToStack.Native.compNative riscvConfig false program (.nil, 136)
      (registers,
        if max ((66 / 2 + 1) - registers) (PrefixChecks.Shard90.arity - registers) = 0 then 0
        else max ((66 / 2 + 1) - registers) (PrefixChecks.Shard90.arity - registers) + 1,
        max ((66 / 2 + 1) - registers) (PrefixChecks.Shard90.arity - registers)) = (body19, (.nil, 136)) := by
    rw [program_eq_transform]
    exact step19.2.2.2.2.2
  rw [h hb]
  unfold stackResult
  rw [← finalBody_eq]
  rfl

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154
