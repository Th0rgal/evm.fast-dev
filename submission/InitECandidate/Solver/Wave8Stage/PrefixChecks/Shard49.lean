import InitECandidate.Solver.Wave8Stage.PrefixChecks.Support
import InitECandidate.Solver.Wave8Stage.CertifiedListSpine

/-! One original compiler entry, independently checked through named passes. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard49
open InitECandidate.Solver.Wave8Stage
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

wave8_list_entry entry := ConcreteCompilerWord.source at 49
wave8_certified_reduce arity := entry.2.1
wave8_certified_reduce name := entry.1

wave8_expose word := entry.2.2 until Flapjack.loopToWordCompFuncHOL
wave8_expose optimise := word.last until Flapjack.optimiseHOL
wave8_expose loop := optimise.last until Flapjack.compFuncHOLExact
wave8_expose crepSimp := loop.last until Flapjack.crepSimpProgHOL
wave8_expose inline := crepSimp.last until Flapjack.CrepInlineCanonical.inlineProgHOLCoreExact
wave8_expose crep := inline.last until Flapjack.compFuncExactHOLW

wave8_certified_reduce panProgram := crep.last

open Flapjack
wave8_certified_reduce crepProgram := compFuncExactHOLW
  crep.arg2 crep.arg3
  crep.arg4 panProgram

theorem crepCompileEq : crep = crepProgram :=
  Eq.trans (congrArg (fun body => compFuncExactHOLW crep.arg2
    crep.arg3 crep.arg4 body)
    panProgram_eq) crepProgram_eq

open Flapjack
wave8_certified_reduce inlineProgram := CrepInlineCanonical.inlineProgHOLCoreExact inline.arg4 inline.arg5 inline.arg6 crepProgram

theorem inlineCompileEq : inline = inlineProgram :=
  Eq.trans (congrArg (fun body => CrepInlineCanonical.inlineProgHOLCoreExact inline.arg4 inline.arg5 inline.arg6 body)
    (Eq.trans crep_eq crepCompileEq)) inlineProgram_eq

open Flapjack
wave8_certified_reduce crepSimpProgram := crepSimpProgHOL (width := 64) inlineProgram

theorem crepSimpCompileEq : crepSimp = crepSimpProgram :=
  Eq.trans (congrArg (fun body => crepSimpProgHOL (width := 64) body)
    (Eq.trans inline_eq inlineCompileEq)) crepSimpProgram_eq

open Flapjack
wave8_certified_reduce loopProgram := compFuncHOLExact (width := 64) loop.arg2 loop.arg3 loop.arg4 crepSimpProgram

theorem loopCompileEq : loop = loopProgram :=
  Eq.trans (congrArg (fun body => compFuncHOLExact (width := 64) loop.arg2 loop.arg3 loop.arg4 body)
    (Eq.trans crepSimp_eq crepSimpCompileEq)) loopProgram_eq

open Flapjack
wave8_certified_reduce optimisedProgram := optimiseHOL (width := 64) loopProgram

theorem optimiseCompileEq : optimise = optimisedProgram :=
  Eq.trans (congrArg (fun body => optimiseHOL (width := 64) body)
    (Eq.trans loop_eq loopCompileEq)) optimisedProgram_eq

open Flapjack
wave8_certified_reduce wordProgram := loopToWordCompFuncHOL (width := 64) word.arg2 word.arg3 optimisedProgram

theorem wordCompileEq : word = wordProgram :=
  Eq.trans (congrArg (fun body => loopToWordCompFuncHOL (width := 64) word.arg2 word.arg3 body)
    (Eq.trans optimise_eq optimiseCompileEq)) wordProgram_eq

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

wave8_certified_reduce simplified := WordSimp.compileExp wordProgram
wave8_certified_reduce temporary := maxVarHOL simplified + 1
wave8_certified_reduce selected := WordInst.instSelectExecutable riscvConfig temporary simplified
wave8_certified_reduce ssa := WordAlloc.fullSsaCcTrans arity selected
wave8_certified_reduce dead := Flapjack.WordAlloc.removeDeadProg ssa
wave8_certified_reduce common := WordCse.wordCommonSubexpElim dead
wave8_certified_reduce copied := WordCopy.copyProp common
wave8_certified_reduce twoRegister := WordInst.threeToTwoRegProg riscvConfig.twoRegArith copied
wave8_certified_reduce reachable := WordUnreach.removeUnreach twoRegister
wave8_certified_reduce prefixProgram := Flapjack.WordAlloc.removeDeadProg reachable

theorem prefixCompileEq :
    WordCostCompilerControl.preAllocation riscvConfig riscvConfig.twoRegArith arity
      wordProgram = prefixProgram := by
  simp only [WordCostCompilerControl.preAllocation, simplified_eq, temporary_eq,
    selected_eq, ssa_eq, dead_eq, common_eq, copied_eq, twoRegister_eq, reachable_eq, prefixProgram_eq]

theorem checkedProgram :
    WordCostCheck.checkProgram ConcreteWordCostAnnotations.summaries WordSourceOracle.terminal
      20000 prefixProgram (ConcreteWordCostAnnotations.summaries (some name)) = true := by
  cbv

theorem checkedEntry : ConcreteWordCheckInput.check entry = true := by
  unfold ConcreteWordCheckInput.check
  rw [word_eq.trans wordCompileEq, arity_eq, name_eq, prefixCompileEq]
  exact checkedProgram

wave8_list_spine entries := (ConcreteCompilerWord.source.drop 49).take 1

theorem checked : entries.all ConcreteWordCheckInput.check = true := by
  wave8_all [checkedEntry]

end InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard49
