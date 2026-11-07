import InitECandidate.Solver.Wave8Stage.PrefixChecks.Support
import InitECandidate.Solver.Wave8Stage.CertifiedListSpine
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses
import InitECandidate.Solver.Wave8Stage.CertifiedPreAlloc
import InitECandidate.Solver.Wave8Stage.CertifiedCse

/-! One original compiler entry, independently checked through named passes (`Shard282`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 64000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard282
open InitECandidate.Solver.Wave8Stage
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

wave8_list_entry entry := ConcreteCompilerWord.source at 282
wave8_certified_reduce arity := entry.2.1
wave8_certified_reduce name := entry.1

wave8_expose word := entry.2.2 until Flapjack.loopToWordCompFuncHOL
wave8_expose optimise := word.last until Flapjack.optimiseHOL
wave8_expose loop := optimise.last until Flapjack.compFuncHOLExact
wave8_expose crepSimp := loop.last until Flapjack.crepSimpProgHOL
wave8_expose inline := crepSimp.last until Flapjack.CrepInlineCanonical.inlineProgHOLCoreExact
wave8_expose crep := inline.last until Flapjack.compFuncExactHOLW

wave8_certified_reduce panProgram := crep.last
wave8_certified_reduce crepK := crep.arg2
wave8_certified_reduce crepM := crep.arg3
wave8_certified_reduce crepParams := crep.arg4

wave8_kernel_reduce crepProgram :=
  InitECandidate.Solver.CrepKernelComputation.compFuncExactHOLW (width := 64) crepK crepM crepParams panProgram

theorem crepCompileEq : crep = crepProgram :=
  Eq.trans
    (congrArg4 (compFuncExactHOLW (width := 64)) crepK_eq crepM_eq crepParams_eq panProgram_eq)
    (Eq.trans
      (compFuncExactHOLW_eq crepK crepM crepParams panProgram)
      crepProgram_eq)

wave8_certified_reduce inlineProgram :=
  CrepInlineCanonical.inlineProgHOLCoreExact inline.arg4 inline.arg5 inline.arg6 crepProgram

theorem inlineCompileEq : inline = inlineProgram :=
  Eq.trans (congrArg (fun body => CrepInlineCanonical.inlineProgHOLCoreExact inline.arg4 inline.arg5 inline.arg6 body)
    (Eq.trans crep_eq crepCompileEq)) inlineProgram_eq

wave8_kernel_reduce crepSimpProgram := crepSimpProgHOL (width := 64) inlineProgram

theorem crepSimpCompileEq : crepSimp = crepSimpProgram :=
  Eq.trans (congrArg (fun body => crepSimpProgHOL (width := 64) body)
    (Eq.trans inline_eq inlineCompileEq)) crepSimpProgram_eq

wave8_certified_reduce loopM := loop.arg2
wave8_certified_reduce loopFns := loop.arg3
wave8_certified_reduce loopVars := loop.arg4

wave8_kernel_reduce loopProgram :=
  compFuncHOLExact (width := 64) loopM loopFns loopVars crepSimpProgram

theorem loopCompileEq : loop = loopProgram :=
  Eq.trans
    (congrArg4 (compFuncHOLExact (width := 64)) loopM_eq loopFns_eq loopVars_eq
      (Eq.trans crepSimp_eq crepSimpCompileEq))
    loopProgram_eq

wave8_kernel_reduce optimisedProgram := optimiseStructural (width := 64) loopProgram

theorem optimiseCompileEq : optimise = optimisedProgram :=
  Eq.trans
    (congrArg (fun body => optimiseHOL (width := 64) body) (Eq.trans loop_eq loopCompileEq))
    (Eq.trans (optimiseStructural_eq loopProgram) optimisedProgram_eq)

wave8_certified_reduce wordName := word.arg2
wave8_certified_reduce wordParams := word.arg3

wave8_kernel_reduce wordProgram :=
  loopToWordCompFuncHOL (width := 64) wordName wordParams optimisedProgram

theorem wordCompileEq : word = wordProgram :=
  Eq.trans
    (congrArg3 (loopToWordCompFuncHOL (width := 64)) wordName_eq wordParams_eq
      (Eq.trans optimise_eq optimiseCompileEq))
    wordProgram_eq

wave8_certified_reduce simplified := WordSimp.compileExp wordProgram
wave8_certified_reduce temporary := maxVarHOL simplified + 1
wave8_certified_reduce selected := WordInst.instSelectExecutable riscvConfig temporary simplified

wave8_certified_reduce ssa := WordAlloc.fullSsaCcTrans arity selected

wave8_chunked_remove_dead dead := ssa

wave8_certified_cse common := dead

wave8_certified_prealloc

theorem prefixCompileEq :
    WordCostCompilerControl.preAllocation riscvConfig riscvConfig.twoRegArith arity
      wordProgram = prefixProgram :=
  preAllocation_step arity
    wordProgram simplified temporary selected ssa dead common copied twoRegister reachable prefixProgram
    simplified_eq temporary_eq selected_eq ssa_eq dead_eq common_eq copied_eq twoRegister_eq reachable_eq prefixProgram_eq

wave8_certified_check_program

theorem checkedEntry : ConcreteWordCheckInput.check entry = true := by
  unfold ConcreteWordCheckInput.check
  rw [word_eq.trans wordCompileEq, arity_eq, name_eq, prefixCompileEq]
  exact checkedProgram

wave8_list_spine entries := (ConcreteCompilerWord.source.drop 282).take 1

theorem checked : entries.all ConcreteWordCheckInput.check = true := by
  wave8_all [checkedEntry]

end InitECandidate.Solver.Wave8Stage.PrefixChecks.Shard282
