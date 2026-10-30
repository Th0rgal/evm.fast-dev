import InitECandidate.Solver.SelfContainedPipelineBridge
import InitECandidate.Solver.SelfContainedIsoReducedK
import InitECandidate.Solver.SelfContainedSixPassMaster
import InitECandidate.Solver.LoopToWordToStackNamesAndLabToTargetClockMaster
import InitECandidate.Solver.FlapjackElevenPassSimulationAndClockGrandMaster


set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# Concrete baseline Stage 1–5 pipeline master (FullBaseline-free)

This leaf module is built only on cached `Solver/` modules whose transitive
closure excludes `InitECandidate.Proofs.FullBaseline` and every
`InitECandidate.Proofs.Bounded*` module.

It provides:
1. `certificate_of_target_not_timeOut`: for any `K`, a finite baseline
   certificate from a uniform target non-timeout premise, with the concrete
   oracle compilation and stack-depth witnesses made explicit.
2. `certificate_of_post_bootstrap_target_not_timeOut`: the same reducer at
   `bootstrapSteps + K_post`.
3. Concrete five-stage reducers on `baselineMachineConfig` and
   `baselineInitialState`: general chain, linear clocks, exact isometries,
   basic-block target bounds, and the six-pass reduced budget.
4. Re-exported pass-level simulation/clock theorems for the eleven compiler
   passes, instantiated without importing the FullBaseline hierarchy.
-/

namespace InitECandidate.Solver.SelfContainedConcretePipelineMaster

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace
open InitECandidate.Solver.YukonCleanVerifierCheck (baselineHeapLen baselineAdj2 baselineAdj4)
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedPipelineBridge
open InitECandidate.Solver.SelfContainedMasterK
open InitECandidate.Solver.SelfContainedBasicBlockBridge
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget

private theorem baselineWithFiniteK_machineConfig_eq (K : Nat) :
    (baselineWithFiniteK K).machineConfig = baselineMachineConfig := rfl

private theorem baselineWithFiniteK_initialMemory_eq (K : Nat) (input : Guest.InputBlob) :
    (baselineWithFiniteK K).initialMemory input =
      (fun a =>
        if machineSharedDomain a then byteToBits ((Guest.guestHostMemory input a).getD 0)
        else initialMemory a) := by
  have h := submission_record_memory InitECandidate.code (.finite K)
    nativePc baselineNames 2 baselineMmio input
  have hpure : romMemory InitECandidate.code = initialMemory := rfl
  rw [hpure] at h
  have hd : submissionSharedDomain = machineSharedDomain := rfl
  unfold hostOverlay at h
  rw [hd] at h
  exact h

private theorem baselineWithFiniteK_initialState_eq (K : Nat) :
    (baselineWithFiniteK K).initialState = baselineInitialState := by
  funext input
  unfold Submission.initialState
  rw [baselineWithFiniteK_initialMemory_eq K input]
  rfl

/-- Concrete oracle compilation and stack-depth witness isolating the only
artifact facts absent when `InitECandidate.Proofs.FullBaseline` is unbuilt. -/
structure ConcreteOracleCompilationWitness : Type where
  oracles : List (Option (Spt Nat))
  c : Backend.Config
  depth : Nat
  hlab : c.labConf = baselineLabConfig
  compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
    sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth)
  depthBound : depth ≤ 7480

/-- Full-baseline `machineSemHOL` termination on `baselineInitialState input`
derived solely from the oracle compilation witness and `sourceBehaviour = .terminate`
(100% `FullBaseline`-free counterpart of `InitE.full_baseline_terminates`). -/
theorem oracle_full_baseline_terminates
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (source : sourceBehaviour input = .terminate outcome events) :
    machineSemHOL baselineMachineConfig (sourceFfi input)
      (baselineInitialState input) (.terminate outcome events) := by
  have hmem : panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      c.labConf.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig c.labConf.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs := by
    rw [hlab]
    exact YukonCleanVerifierCheck.baseline_pan_installed input
  have hinst := YukonCleanVerifierCheck.oracle_baseline_installation input c hmem
  obtain ⟨post, shift, related⟩ := YukonBaselineCompat.full_evaluator_exact
    (sourceFfi input) (baselineInitialState input) (baselineInitialState_related input)
  have nonfail : sourceBehaviour input ≠ HolBehaviour.fail := by
    rw [source]
    intro impossible
    cases impossible
  have correct := oracle_baseline_behaviour_eq oracles input baselineMachineConfig post
    InitECandidate.nativeCode InitECandidate.bitmaps c depth baselineHeapLen
    baselineAdj2 baselineAdj4 3788 0 compiled depthBound
    (YukonCleanVerifierCheck.oracle_baseline_installation_transport input c post related hinst)
    nonfail
  have postTerm := target_termination_of_behaviour_eq baselineMachineConfig
    (sourceFfi input) post outcome events (fun b hb => (correct b hb).trans source)
  obtain ⟨k0, ms0, ffi0, run0, io0⟩ := postTerm
  exact ⟨bootstrapSteps + k0, ms0, ffi0, (shift k0).trans run0, io0⟩

/-- Under `machineSemHOL mc ffi ms (.terminate outcome events)`, any non-`.timeOut`
target evaluation at `steps` halts with `outcome` and `events`. -/
theorem targetTerminatesAt_and_agree_of_not_timeOut {width : Nat} [NeZero width]
    {S Q σ : Type} (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S)
    (outcome : HolOutcome) (events : List HolIoEvent) (steps : Nat)
    (hsem : machineSemHOL mc ffi ms (.terminate outcome events))
    (hnt : (evaluateTargetHOL mc ffi steps ms).1 ≠ .timeOut) :
    ∃ ms1 ffi1,
      evaluateTargetHOL mc ffi steps ms = (.halt outcome, ms1, ffi1) ∧
      ffi1.ioEvents = events := by
  obtain ⟨k0, ms0, ffi0, run0, io0⟩ := hsem
  obtain ⟨ms1, hrun1⟩ := SelfContainedTargetBound.evaluateTarget_halt_of_not_timeOut_and_halt
    mc ffi ms k0 steps outcome ms0 ffi0 run0 hnt
  exact ⟨ms1, ffi0, hrun1, io0⟩

/-- Uniform target non-timeout at an arbitrary finite budget `K`, with the
unbuilt concrete oracle compilation and stack-depth witnesses explicit.
No FullBaseline certificate is imported. -/
theorem certificate_of_target_not_timeOut
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth K : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input) K
          (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK K) (.finite K) := by
  refine ⟨rfl, baselineWithFiniteK_admitted K, ?_⟩
  intro input hgas outcome events source covered
  have hsem := oracle_full_baseline_terminates oracles c depth hlab compiled depthBound
    input outcome events source
  have hnt := not_timeOut input hgas outcome events source covered
  obtain ⟨post, finalFfi, hrun, hio⟩ :=
    targetTerminatesAt_and_agree_of_not_timeOut baselineMachineConfig
      (sourceFfi input) (baselineInitialState input) outcome events K hsem hnt
  refine ⟨K, Nat.le_refl K, outcome, post, finalFfi, ?_, ?_⟩
  · rw [baselineWithFiniteK_machineConfig_eq, baselineWithFiniteK_initialState_eq]
    exact hrun
  · rw [hio]
    exact matchingResult_refl input outcome events covered

/-- Packaged witness corollary: given any `ConcreteOracleCompilationWitness`,
we recover the exact `YukonSelfContainedCert.certificate_of_target_not_timeOut`
signature (`∀ K, not_timeOut → Certificate (baselineWithFiniteK K) (.finite K)`). -/
theorem certificate_of_target_not_timeOut_of_witness
    (w : ConcreteOracleCompilationWitness) (K : Nat)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input) K
          (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK K) (.finite K) :=
  certificate_of_target_not_timeOut w.oracles w.c w.depth K
    w.hlab w.compiled w.depthBound not_timeOut

/-- Baseline `.infinity` compatibility for any finite budget `K`. -/
theorem baseline_infinity_certificate_of_finite (K : Nat)
    (finite : InitE.Certificate (baselineWithFiniteK K) (.finite K)) :
    InitE.Certificate SelfContainedEndToEndCert.submission .infinity := by
  refine ⟨rfl, InitECandidate.Solver.FastEnv.baselineSubmission_admitted, ?_⟩
  intro input gas outcome events source covered
  obtain ⟨steps, _, execution⟩ := finite.correct input gas outcome events source covered
  exact ⟨steps, trivial,
    (SelfContainedEndToEndCert.matchingExecutionAt_with_score
      InitECandidate.Solver.FastEnv.baselineSubmission (.finite K)
      input outcome events steps).mp execution⟩

/-- The same arbitrary-budget reducer expressed through the post-bootstrap
split used by the concrete five-stage clock pipeline. -/
theorem certificate_of_post_bootstrap_target_not_timeOut
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth K_post : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          (bootstrapSteps + K_post) (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK (bootstrapSteps + K_post))
      (.finite (bootstrapSteps + K_post)) :=
  certificate_of_target_not_timeOut oracles c depth (bootstrapSteps + K_post)
    hlab compiled depthBound not_timeOut

/-- A bounded post-bootstrap target execution, supplied as a `machineSemHOL`
termination premise, turns uniform non-timeout into target termination within
`K`. -/
theorem targetTerminatesWithin_of_not_timeOut {S Q σ : Type}
    (mc : MachineConfig 64 S Q) (ffi : HolFfiState σ) (ms : S)
    (outcome : HolOutcome) (events : List HolIoEvent) (K : Nat)
    (hsem : machineSemHOL mc ffi ms (.terminate outcome events))
    (hnt : (evaluateTargetHOL mc ffi K ms).1 ≠ .timeOut) :
    targetTerminatesWithin (.finite K) mc ffi ms := by
  obtain ⟨ms1, ffi1, hrun, _⟩ :=
    targetTerminatesAt_and_agree_of_not_timeOut mc ffi ms outcome events K hsem hnt
  exact ⟨K, Nat.le_refl K, outcome, ms1, ffi1, hrun⟩

/-- Concrete Stage 1–4 (`PanSem -> WordSem -> StackSem -> LabSem`) halt and I/O
bridge on `baselineMachineConfig` and `baselineInstalledState`: given a non-`timeOut`
`PanSem` run at `k_pan` together with non-`timeOut` runs at `k_word`, `k_stack`,
and `k_lab`, the concrete `LabSem` initial state halts with the exact source
`outcome` and `events`, isolating only the Stage 5 (`LabToTarget`) target
non-`timeOut` step. -/
theorem concrete_baseline_source_to_lab_halt_of_pan_not_timeOut
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (source : sourceBehaviour input = .terminate outcome events)
    (k_pan k_word k_stack k_lab : Nat)
    (pan_not_timeOut : ∀ (stCtxt : StructContextExact)
        (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory),
      decsStcnamesHOLExact [] sourceDeclarations = some stCtxt →
      @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
        { sourceInitialState input with structs := stCtxt }
        (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
        sourceDeclarations = some s_decls →
      (PanSemStateFiniteExact.evaluateHOLFiniteState
        { s_decls with clock := k_pan }
        (.call none (ofString "main") [] : ProgHOL 64)).1 ≠ some .timeOut)
    (word_not_timeOut : ∀ (t : AsmState 64)
        (m : BitVec 64 → WordLocW 64) (bitmapsDm sdm : BitVec 64 → Bool)
        (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
        (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
      (WordSemStateFiniteExact.evaluate
        (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
        { pipelinePanToWordInitState (oracleCompilerConfig oracles) baselineMachineConfig
            (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
            InitECandidate.nativeCode 3788 ltconf sourceDeclarations wprog
            InitECandidate.bitmaps p 0 with clock := k_word }).1 ≠ some .timeOut)
    (stack_not_timeOut : ∀ (t : AsmState 64)
        (m : BitVec 64 → WordLocW 64) (bitmapsDm sdm : BitVec 64 → Bool)
        (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
      (StackSemEvaluate.evaluate
        ((.call none (.inl BvlToBvi.initGlobalsLocation) none : StackLang.HolProg 64),
          { pipelineStackInitState (oracleCompilerConfig oracles) baselineMachineConfig
              (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
              InitECandidate.nativeCode 3788 ltconf InitECandidate.bitmaps p 0 with
              clock := k_stack })).1 ≠ some .timeOut)
    (lab_not_timeOut : ∀ (t : AsmState 64)
        (m : BitVec 64 → WordLocW 64) (bitmapsDm sdm : BitVec 64 → Bool)
        (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
      (LabSem.evaluate
        { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
            (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
            InitECandidate.nativeCode 3788 ltconf p with clock := k_lab }).1 ≠ .timeOut) :
    ∃ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
      (bitmapsDm sdm : BitVec 64 → Bool)
      (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
      (LabSem.evaluate
        { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
            (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
            InitECandidate.nativeCode 3788 ltconf p with clock := k_lab }).1 = .halt outcome ∧
      (LabSem.evaluate
        { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
            (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
            InitECandidate.nativeCode 3788 ltconf p with clock := k_lab }).2.ffi.ioEvents = events := by
  have hsem := Pancake.PanToTarget.semanticsDecls_mainFirstHOL (sourceInitialState input)
    (ofString "main") (Guest.Software.guestAst.map Pancake.PanLang.declToHOL) sourceHasMain
  have hterm : PanSemStateFiniteExact.semanticsDecls (sourceInitialState input)
      (ofString "main") sourceDeclarations = .terminate outcome events :=
    hsem.trans source
  have nonfail' : PanSemStateFiniteExact.semanticsDecls (sourceInitialState input)
      (ofString "main") sourceDeclarations ≠ HolBehaviour.fail := by
    rw [hterm]; intro h; cases h
  obtain ⟨stCtxt, s_decls, hst, hev_decls, -, -, -, -, -, -, -⟩ :=
    SelfContainedStageBounds.semanticsDecls_terminate_extract (sourceInitialState input)
      (ofString "main") sourceDeclarations outcome events hterm
  rcases hev_pan : PanSemStateFiniteExact.evaluateHOLFiniteState
      { s_decls with clock := k_pan }
      (.call none (ofString "main") [] : ProgHOL 64) with ⟨res_src, s_src_post⟩
  have hnt_pan : res_src ≠ some .timeOut := by
    have h := pan_not_timeOut stCtxt s_decls hst hev_decls
    rw [hev_pan] at h
    exact h
  obtain ⟨hclass_src, hio_src⟩ :=
    SelfContainedStageBounds.semanticsDecls_terminate_at_clock (sourceInitialState input)
      (ofString "main") sourceDeclarations outcome events hterm stCtxt s_decls hst hev_decls
      k_pan res_src s_src_post hev_pan hnt_pan
  have hmem : panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      c.labConf.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig c.labConf.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs := by
    rw [hlab]
    exact YukonCleanVerifierCheck.baseline_pan_installed input
  have installed := YukonCleanVerifierCheck.oracle_baseline_installation input c hmem
  obtain ⟨hmc, _, hsplit, hbase, hlen, htop, hglobals, hdomain,
    haligned, hadj2, hadj4, hleft, hright, hmax_heap, hendian, hinstalled, hlimits⟩ := installed
  have hconfig : baselineMachineConfig.target.config = riscvConfig := by rw [hmc.1]; rfl
  have hcomp := compiled
  rw [← hconfig, compileProgMaxAsmExecutable_eq] at hcomp
  have hcfg := oracleBackendConfigOk oracles
  rw [← hconfig] at hcfg
  have hinit := oracleMachineInitOk oracles baselineMachineConfig hmc
  rw [← hconfig] at hinit
  have hprecise : optionLt (some depth)
      (some (readLimits baselineMachineConfig.target.config (oracleCompilerConfig oracles)
        baselineMachineConfig baselineInstalledState).1) = true := by
    change optionLt (some depth)
      (some (readLimits baselineMachineConfig.target.config pancakeRiscVBackendConfig
        baselineMachineConfig baselineInstalledState).1) = true
    rw [hlimits]
    simpa only [optionLt, decide_eq_true_eq] using
      (Nat.lt_of_le_of_lt depthBound oracle_stack_bound_fits)
  obtain ⟨col, wprog, wconf, fs, p, ltconf, hwtw, hwts, _, rfl, hmax⟩ :=
    compileProgMax_some (oracleCompilerConfig oracles) baselineMachineConfig sourceDeclarations
      InitECandidate.nativeCode InitECandidate.bitmaps c (some depth) hcomp
  obtain ⟨t, m, bitmapPtr, bitmapsDm, sdm, hpm, hgi, hsdm, a1, a2, a3, hle, hbig, hdisj, m0, m1,
    m2, m3, m4, hstar, _, _⟩ := hinstalled
  have hpm' : ∀ a, decide ((sourceInitialState input).memaddrs a) = true →
      m a = wlabWlocExact ((sourceInitialState input).memory a) :=
    fun a h => hpm a (of_decide_eq_true h)
  have hsdm' : (fun a => decide ((sourceInitialState input).shMemaddrs a)) =
      fun a => sdm a && holByteAligned a := by
    funext a; rw [hsdm]; simp only [Bool.decide_and, Bool.decide_eq_true]
  obtain ⟨hhalt_lab, hio_lab⟩ :=
    source_to_lab_halt_of_stage_clock_chain
      (oracleCompilerConfig oracles) baselineMachineConfig (sourceFfi input)
      t m bitmapPtr bitmapsDm sdm baselineInstalledState
      InitECandidate.nativeCode 3788 ltconf sourceDeclarations col wprog
      InitECandidate.bitmaps wconf fs p 0 (some depth)
      (sourceInitialState input) (ofString "main") globalsWords baselineHeapLen
      hcfg (riscvMachineConfigOk baselineMachineConfig hmc) hinit
      (by rw [hconfig]; decide) hwtw hwts hmax sourceDistinctFunctions hgi
      ⟨a1, a2, a3, hle, hbig, hdisj, m0, m1, m2, m3, m4, hstar⟩
      hpm' hsdm' hbase hsplit
      (hadj2 ▸ hleft) (hadj4 ▸ hright) hmax_heap (oracleHeapLimit_lt oracles)
      haligned hendian rfl hlen hglobals hdomain htop rfl
      (by simpa only [sourceDeclarations, globalsWords] using sourceGlobalsSize.symm)
      sourceDistinctParams (source_globals_allocatable input)
      rfl rfl rfl sourceExceptionBound rfl nonfail' hprecise
      stCtxt s_decls hst hev_decls
      k_pan k_word k_stack k_lab
      res_src s_src_post outcome hev_pan hclass_src
      (word_not_timeOut t m bitmapsDm sdm wprog p ltconf)
      (stack_not_timeOut t m bitmapsDm sdm p ltconf)
      (lab_not_timeOut t m bitmapsDm sdm p ltconf)
  exact ⟨t, m, bitmapsDm, sdm, p, ltconf, hhalt_lab, hio_lab.trans hio_src⟩

/-- Concrete general five-stage pipeline certificate, directly specialized to
`baselineMachineConfig` and `baselineInitialState`. -/
theorem concrete_five_stage_clock_chain_certificate :
    type_of% @SelfContainedPipelineBridge.finite_certificate_of_source_to_target_clock_chain :=
  @SelfContainedPipelineBridge.finite_certificate_of_source_to_target_clock_chain

/-- Concrete linear Stage 1–5 clock-budget certificate. -/
theorem concrete_linear_stage_clock_bounds_certificate
    (oracles : List (Option (Spt Nat))) (c : Backend.Config)
    (depth K_pan_max C_front D_front C_back D_back C_target : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (k_pan k_word k_stack k_lab : Guest.InputBlob → Nat)
    (h_pan_bound : ∀ input, k_pan input ≤ K_pan_max)
    (h_front_bound : ∀ input, k_word input ≤ C_front * k_pan input + D_front)
    (h_stack_bound : ∀ input, k_stack input ≤ k_word input + D_back)
    (h_back_bound : ∀ input, k_lab input ≤ C_back * k_word input + D_back)
    (pan_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory),
          decsStcnamesHOLExact [] sourceDeclarations = some stCtxt →
          @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
            { sourceInitialState input with structs := stCtxt }
            (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
            sourceDeclarations = some s_decls →
          (PanSemStateFiniteExact.evaluateHOLFiniteState
            { s_decls with clock := k_pan input }
            (.call none (ofString "main") [] : ProgHOL 64)).1 ≠ some .timeOut)
    (word_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (WordSemStateFiniteExact.evaluate
            (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
            { pipelinePanToWordInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 3788 ltconf sourceDeclarations wprog
                InitECandidate.bitmaps p 0 with clock := k_word input }).1 ≠ some .timeOut)
    (stack_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (StackSemEvaluate.evaluate
            ((.call none (.inl BvlToBvi.initGlobalsLocation) none : StackLang.HolProg 64),
              { pipelineStackInitState (oracleCompilerConfig oracles) baselineMachineConfig
                  (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                  InitECandidate.nativeCode 3788 ltconf InitECandidate.bitmaps p 0 with
                  clock := k_stack input })).1 ≠ some .timeOut)
    (lab_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (LabSem.evaluate
            { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 3788 ltconf p with
                clock := k_lab input }).1 ≠ .timeOut)
    (target_not_timeOut_of_lab_halt : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (LabSem.evaluate
            { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 3788 ltconf p with
                clock := k_lab input }).1 = .halt outcome →
          (LabSem.evaluate
            { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 3788 ltconf p with
                clock := k_lab input }).2.ffi.ioEvents = events →
          (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
            (bootstrapSteps + linearPipelineTargetBudget K_pan_max C_front D_front C_back D_back C_target)
            (baselineInitialState input)).1 ≠ .timeOut) :
    (∀ input,
      k_stack input ≤ C_front * K_pan_max + D_front + D_back ∧
      C_target * k_lab input ≤
        linearPipelineTargetBudget K_pan_max C_front D_front C_back D_back C_target) ∧
    InitE.Certificate
      (baselineWithFiniteK (bootstrapSteps +
        linearPipelineTargetBudget K_pan_max C_front D_front C_back D_back C_target))
      (.finite (bootstrapSteps +
        linearPipelineTargetBudget K_pan_max C_front D_front C_back D_back C_target)) := by
  refine ⟨?_, ?_⟩
  · intro input
    refine ⟨?_, ?_⟩
    · have hf := h_front_bound input
      have hp : C_front * k_pan input ≤ C_front * K_pan_max :=
        Nat.mul_le_mul_left C_front (h_pan_bound input)
      have hs := h_stack_bound input
      omega
    · have h1 := linearPipelineTargetBudget_of_stage_bounds
        (k_pan input) (k_word input) (k_lab input) (C_target * k_lab input)
        C_front D_front C_back D_back C_target
        (h_front_bound input) (h_back_bound input) (Nat.le_refl _)
      have h2 := linearPipelineTargetBudget_mono_k_pan
        C_front D_front C_back D_back C_target (h_pan_bound input)
      exact Nat.le_trans h1 h2
  · exact SelfContainedPipelineBridge.finite_certificate_of_source_to_target_clock_chain
      oracles c depth
      (linearPipelineTargetBudget K_pan_max C_front D_front C_back D_back C_target)
      hlab compiled depthBound k_pan k_word k_stack k_lab
      pan_not_timeOut word_not_timeOut stack_not_timeOut
      lab_not_timeOut target_not_timeOut_of_lab_halt

/-- Concrete refined five-stage certificate. -/
theorem concrete_refined_finite_certificate :
    type_of% @SelfContainedEndToEndCert.end_to_end_refined_finite_certificate :=
  @SelfContainedEndToEndCert.end_to_end_refined_finite_certificate

/-- Concrete exact-isometry reduced-budget five-stage certificate. -/
theorem concrete_iso_reduced_finite_certificate :
    type_of% @SelfContainedIsoReducedK.end_to_end_iso_reduced_finite_certificate :=
  @SelfContainedIsoReducedK.end_to_end_iso_reduced_finite_certificate

/-- Concrete basic-block end-to-end certificate. -/
theorem concrete_basic_block_end_to_end_master_certificate :
    type_of% @SelfContainedBasicBlockBridge.self_contained_basic_block_end_to_end_master_certificate :=
  @SelfContainedBasicBlockBridge.self_contained_basic_block_end_to_end_master_certificate

/-- Concrete basic-block LabToTarget multi-step target bound. -/
theorem concrete_lab_to_target_basic_block_multi_step_bound :
    type_of% @SelfContainedBasicBlockBridge.lab_to_target_basic_block_multi_step_bound :=
  @SelfContainedBasicBlockBridge.lab_to_target_basic_block_multi_step_bound

/-- Concrete basic-block backend clock composition and exact run. -/
theorem concrete_backend_basic_block_clock_chain_and_run :
    type_of% @SelfContainedBasicBlockBridge.backend_basic_block_clock_chain_and_run :=
  @SelfContainedBasicBlockBridge.backend_basic_block_clock_chain_and_run

/-- Six-pass reduced-budget certificate from uniform target non-timeout. -/
theorem concrete_six_pass_reduced_finite_certificate :
    type_of% @SelfContainedSixPassMaster.reduced_finite_certificate :=
  @SelfContainedSixPassMaster.reduced_finite_certificate

/-- Exact six-pass budget bound for arbitrary source clock, offset and total
basic-block factor. -/
theorem concrete_six_pass_reduced_budget_bound (k d B_total : Nat)
    (hk : k ≤ refinedSourceClock) (hd : d ≤ pipeOffset) (hB : B_total ≤ 8) :
    bootstrapSteps + B_total *
      (SelfContainedSixPassMaster.sixPassSlope 1 3 * (k + d)) ≤
      SelfContainedSixPassMaster.sixPassReducedK :=
  SelfContainedSixPassMaster.reduced_budget_bound k d B_total hk hd hB

/-- The refined basic-block instantiation is exactly `refinedCandidateK`. -/
theorem concrete_refined_basic_block_budget_exact :
    basicBlockPipelineTargetBudget bootstrapSteps refinedSourceClock
      1 pipeOffset 1 0 frontFactor 0 7 = refinedCandidateK := by
  unfold basicBlockPipelineTargetBudget refinedCandidateK
  decide

/-- Exact isometry of PanToCrep, re-exported without the FullBaseline graph. -/
theorem concrete_pan_to_crep_full_entry_clock_iso :
    type_of% @PanToCrepExactClockIso.pan_to_crep_full_entry_clock_iso :=
  @PanToCrepExactClockIso.pan_to_crep_full_entry_clock_iso

/-- Exact LoopToWord clock isometry. -/
theorem concrete_loop_to_word_clock_iso :
    type_of% @LoopWordStackExactClockIso.loop_to_word_clock_iso :=
  @LoopWordStackExactClockIso.loop_to_word_clock_iso

/-- WordToStack clock-plus-offset entry simulation. -/
theorem concrete_word_to_stack_clock_affine :
    type_of% @LoopWordStackExactClockIso.word_to_stack_clock_affine :=
  @LoopWordStackExactClockIso.word_to_stack_clock_affine

/-- StackRawCall through StackNames end-to-end linear clock. -/
theorem concrete_stackRawCall_to_stackNames_linear_clock :
    type_of% @FlapjackElevenPassSimulationAndClockGrandMaster.grand_stackRawCall_to_stackNames_linear :=
  @FlapjackElevenPassSimulationAndClockGrandMaster.grand_stackRawCall_to_stackNames_linear

/-- LabToTarget target clock is the Lab end clock plus an explicit offset. -/
theorem concrete_labToTarget_clock_plus_k :
    type_of% @LoopToWordToStackNamesAndLabToTargetClockMaster.labToTarget_clock_plus_k :=
  @LoopToWordToStackNamesAndLabToTargetClockMaster.labToTarget_clock_plus_k

/-- PanToCrep and LoopToWord have unit slopes; the affine composition retains
only CrepToLoop and StackToLab multiplicative factors. -/
theorem concrete_front_factor_after_exact_isometries
    (c_cl d_cl c_sl d_sl d_ws k : Nat) :
    LoopWordStackExactClockIso.affine c_sl d_sl
      (LoopWordStackExactClockIso.affine 1 d_ws
        (LoopWordStackExactClockIso.affine 1 0
          (LoopWordStackExactClockIso.affine c_cl d_cl
            (PanToCrepExactClockIso.panToCrepClockBudget k)))) =
    LoopWordStackExactClockIso.affine (c_sl * c_cl)
      (c_sl * (d_cl + d_ws) + d_sl) k := by
  have heq : PanToCrepExactClockIso.panToCrepClockBudget k =
      LoopWordStackExactClockIso.affine 1 0 k := rfl
  rw [heq]
  simpa using LoopWordStackExactClockIso.front_factor_after_iso 1 0 c_cl d_cl c_sl d_sl d_ws k

/-- Unified Stage 1–5 concrete pipeline reducer to a uniform `PanSem` non-timeout
premise on `baselineMachineConfig` and `baselineInitialState`:
Given `k_pan input ≤ K_pan_max`, the uniform `PanSem` non-timeout premise
`pan_not_timeOut`, and the concrete Stage 2–5 clock-transfer witness from `PanSem`
non-timeout at `k_pan` through `WordSem` (`k_word`), `StackSem` (`k_stack`),
`LabSem` (`k_lab`), and `Target` (`bootstrapSteps + K_post`), we obtain both
`InitE.Certificate (baselineWithFiniteK K) (.finite K)` for
`K = bootstrapSteps + linearPipelineTargetBudget K_pan_max C_front D_front C_back D_back C_target`
and `InitE.Certificate submission .infinity`. -/
theorem concrete_pipeline_certificate_of_uniform_pan_not_timeOut
    (oracles : List (Option (Spt Nat))) (c : Backend.Config)
    (depth K_pan_max C_front D_front C_back D_back C_target : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (k_pan k_word k_stack k_lab : Guest.InputBlob → Nat)
    (h_pan_bound : ∀ input, k_pan input ≤ K_pan_max)
    (h_front_bound : ∀ input, k_word input ≤ C_front * k_pan input + D_front)
    (h_stack_bound : ∀ input, k_stack input ≤ k_word input + D_back)
    (h_back_bound : ∀ input, k_lab input ≤ C_back * k_word input + D_back)
    (pan_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory),
          decsStcnamesHOLExact [] sourceDeclarations = some stCtxt →
          @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
            { sourceInitialState input with structs := stCtxt }
            (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
            sourceDeclarations = some s_decls →
          (PanSemStateFiniteExact.evaluateHOLFiniteState
            { s_decls with clock := k_pan input }
            (.call none (ofString "main") [] : ProgHOL 64)).1 ≠ some .timeOut)
    (stage2_to_5_clock_transfer :
      (∀ (input : Guest.InputBlob),
        Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
        ∀ (outcome : HolOutcome) (events : List HolIoEvent),
          sourceBehaviour input = .terminate outcome events →
          coveredOutcome outcome →
          ∀ (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory),
            decsStcnamesHOLExact [] sourceDeclarations = some stCtxt →
            @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
              { sourceInitialState input with structs := stCtxt }
              (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
              sourceDeclarations = some s_decls →
            (PanSemStateFiniteExact.evaluateHOLFiniteState
              { s_decls with clock := k_pan input }
              (.call none (ofString "main") [] : ProgHOL 64)).1 ≠ some .timeOut) →
      (∀ (input : Guest.InputBlob),
        Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
        ∀ (outcome : HolOutcome) (events : List HolIoEvent),
          sourceBehaviour input = .terminate outcome events →
          coveredOutcome outcome →
          (∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
            (bitmapsDm sdm : BitVec 64 → Bool)
            (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
            (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
            (WordSemStateFiniteExact.evaluate
              (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
              { pipelinePanToWordInitState (oracleCompilerConfig oracles) baselineMachineConfig
                  (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                  InitECandidate.nativeCode 3788 ltconf sourceDeclarations wprog
                  InitECandidate.bitmaps p 0 with clock := k_word input }).1 ≠ some .timeOut) ∧
          (∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
            (bitmapsDm sdm : BitVec 64 → Bool)
            (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
            (StackSemEvaluate.evaluate
              ((.call none (.inl BvlToBvi.initGlobalsLocation) none : StackLang.HolProg 64),
                { pipelineStackInitState (oracleCompilerConfig oracles) baselineMachineConfig
                    (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                    InitECandidate.nativeCode 3788 ltconf InitECandidate.bitmaps p 0 with
                    clock := k_stack input })).1 ≠ some .timeOut) ∧
          (∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
            (bitmapsDm sdm : BitVec 64 → Bool)
            (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
            (LabSem.evaluate
              { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                  (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                  InitECandidate.nativeCode 3788 ltconf p with
                  clock := k_lab input }).1 ≠ .timeOut) ∧
          (∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
            (bitmapsDm sdm : BitVec 64 → Bool)
            (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
            (LabSem.evaluate
              { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                  (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                  InitECandidate.nativeCode 3788 ltconf p with
                  clock := k_lab input }).1 = .halt outcome →
            (LabSem.evaluate
              { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                  (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                  InitECandidate.nativeCode 3788 ltconf p with
                  clock := k_lab input }).2.ffi.ioEvents = events →
            (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
              (bootstrapSteps + linearPipelineTargetBudget K_pan_max C_front D_front C_back D_back C_target)
              (baselineInitialState input)).1 ≠ .timeOut))) :
    let K := bootstrapSteps +
      linearPipelineTargetBudget K_pan_max C_front D_front C_back D_back C_target
    (∀ input,
      k_stack input ≤ C_front * K_pan_max + D_front + D_back ∧
      C_target * k_lab input ≤
        linearPipelineTargetBudget K_pan_max C_front D_front C_back D_back C_target) ∧
    InitE.Certificate (baselineWithFiniteK K) (.finite K) ∧
    InitE.Certificate SelfContainedEndToEndCert.submission .infinity := by
  dsimp only
  have htr := stage2_to_5_clock_transfer pan_not_timeOut
  obtain ⟨hbounds, hcert⟩ :=
    concrete_linear_stage_clock_bounds_certificate
      oracles c depth K_pan_max C_front D_front C_back D_back C_target
      hlab compiled depthBound k_pan k_word k_stack k_lab
      h_pan_bound h_front_bound h_stack_bound h_back_bound
      pan_not_timeOut
      (fun input hgas out ev src cov => (htr input hgas out ev src cov).1)
      (fun input hgas out ev src cov => (htr input hgas out ev src cov).2.1)
      (fun input hgas out ev src cov => (htr input hgas out ev src cov).2.2.1)
      (fun input hgas out ev src cov => (htr input hgas out ev src cov).2.2.2)
  exact ⟨hbounds, hcert, baseline_infinity_certificate_of_finite _ hcert⟩

end InitECandidate.Solver.SelfContainedConcretePipelineMaster
