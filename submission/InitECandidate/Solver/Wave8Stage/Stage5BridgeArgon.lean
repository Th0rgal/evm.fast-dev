import InitECandidate.Solver.Wave8Stage.Stage5FrontendArgon
import InitECandidate.Solver.Wave8Stage.Stage5StagesArgon
import InitECandidate.Solver.Wave8Stage.Stage5TargetArgon

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 200000

namespace InitECandidate.Solver.Wave8Stage.Stage5BridgeArgon
open Classical InitE InitECandidate.Proofs
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.LoopToWordStateRelImpSemanticsSupport
open InitECandidate.Solver
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Stage
open InitECandidate.Solver.SelfContainedPipelineBridge

theorem stageTransfer_from_obligations
    (k_pan : Nat)
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (h_front : FrontendStaticBudget.listBudget ConcreteCompilerCrep.source ≤ 448)
    (h_word_all : ConcreteCompilerWord.source.all ConcreteWordCheckInput.check = true)
    (h_m7313 : ∀ col wprog wconf fs p,
      WordToWord.compile (oracleCompilerConfig w.oracles).wordToWordConf riscvConfig
        (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, wprog) →
      WordToStack.Native.compileNative riscvConfig false wprog =
        (InitECandidate.bitmaps, wconf, fs, p) →
      Stage4.codeStepBudget (FullMakeInitSemantics.code2
        (oracleCompilerConfig w.oracles).stackConf (oracleCompilerConfig w.oracles).dataConf
        (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig w.oracles).dataConf - 1)
        (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset p) ≤ 7313) :
    UniformSourceClock.CoveredSourceUniformNotTimeOut k_pan →
    FiniteRebudget.UniformNotTimeOut ArtifactEnv.baselineSubmission (118223496 * k_pan + 119233963) := by
  intro hpan input hgas outcome events hsource hcov
  obtain ⟨stCtxt, s_decls, res, s_post, hst, hdecls, hrun, hclass, _⟩ :=
    UniformSourceClock.covered_source_uniform_terminates_of_uniform_not_timeOut
      hpan input outcome events hgas hsource hcov
  have hnt_pan : res ≠ some .timeOut := by intro ht; subst ht; cases hclass
  have hne_pan : panEntryClass res ≠ .RunError := by
    rw [hclass]; intro h; cases h
  have hsem := Pancake.PanToTarget.semanticsDecls_mainFirstHOL (sourceInitialState input)
    (ofString "main") (Guest.Software.guestAst.map Pancake.PanLang.declToHOL) sourceHasMain
  have hterm : PanSemStateFiniteExact.semanticsDecls (sourceInitialState input)
      (ofString "main") sourceDeclarations = .terminate outcome events :=
    hsem.trans hsource
  have hnonfail : PanSemStateFiniteExact.semanticsDecls (sourceInitialState input)
      (ofString "main") sourceDeclarations ≠ .fail := by
    rw [hterm]; intro h; cases h
  obtain ⟨post, shift, _, post_rel⟩ := ConcreteBaseline.ExactBootstrap.full_evaluator_exact
    (sourceFfi input) (ConcreteBaseline.baselineInitialState input)
    (ConcreteBaseline.baselineInitialState_related input)
  let c := oracleCompilerConfig w.oracles
  have hmc_fe : isRiscvMachineConfig FastEnv.baselineMachineConfig :=
    R12_Stage4BoundArgon.fastEnv_baseline_machine_isRiscv
  have hconfig_fe : FastEnv.baselineMachineConfig.target.config = riscvConfig := by
    rw [hmc_fe.1]; rfl
  have hisa_fe : FastEnv.baselineMachineConfig.target.config.isa ≠ .ag32 := by
    rw [hconfig_fe]; exact riscvConfig_isa_ne_ag32
  obtain ⟨col, wprog, wconf, fs, p, ltconf, hwtw, hwts, hlab, hc_eq⟩ :=
    unpack_compileProgMax c FastEnv.baselineMachineConfig hconfig_fe sourceDeclarations
      InitECandidate.nativeCode InitECandidate.bitmaps w.c w.depth w.compiled
  have hltconf : ltconf = baselineLabConfig := hc_eq.symm.trans w.hlab
  have hpan_inst_post : panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      (some FastEnv.baselineNames) (11, 13) FastEnv.baselineMachineConfig
      FastEnv.baselineMmio post (wlabWlocExact ∘ sourceMemory) ordinaryDomain sharedDomain :=
    panInstalled_fe_of_ae _ _ _ _ _ _ _ _
      (ArtifactEnv.panInstalled_transport
        (ArtifactEnv.baseline_endpoint_agreement post post_rel)
        ArtifactEnv.baseline_pan_installed_core)
  obtain ⟨t, m, bitmapPtr, bitmapDm, sharedDm, hm_ord, hgi_post, hshared,
    ha2, ha4, hab, horder, hspace, hdisjoint, hm0, hm1, hm2, hm3, hm4, hbitmap, hffiN, hmmio⟩ :=
    hpan_inst_post
  have hnames :
      StackNames.findNameSpt c.stackConf.regNames 2 = 11 ∧
      StackNames.findNameSpt c.stackConf.regNames 4 = 13 := by
    simp only [c, oracleCompilerConfig, pancakeRiscVBackendConfig,
      Flapjack.Compiler.pancakeBackendConf, riscvBackendConfig,
      StackNames.findNameSpt, riscvNames]
    simp [sptLookup, sptInsert]
  let dm_unaligned : BitVec 64 → Bool := fun a =>
    decide (t.regs (StackNames.findNameSpt c.stackConf.regNames 2) ≤ a ∧
      a < t.regs (StackNames.findNameSpt c.stackConf.regNames 4)) || bitmapDm a
  have hdm_eq : (fun a => decide (t.regs 11 ≤ a ∧ a < t.regs 13) || bitmapDm a) = dm_unaligned := by
    dsimp only [dm_unaligned]; rw [hnames.1, hnames.2]
  have hgi_post_c : goodInitState FastEnv.baselineMachineConfig post
      InitECandidate.nativeCode 3788 t m dm_unaligned sharedDm :=
    Eq.mp (congrArg (fun dm => goodInitState FastEnv.baselineMachineConfig post
      InitECandidate.nativeCode 3788 t m dm sharedDm) hdm_eq) hgi_post
  let lab_post := pipelineLabInitState c FastEnv.baselineMachineConfig (sourceFfi input)
    t m bitmapDm sharedDm post InitECandidate.nativeCode 3788 ltconf p
  let stack_pair := FullMakeInit.fullMakeInit c.stackConf c.dataConf
    (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
    InitECandidate.bitmaps p lab_post
    (fun k => decide (k ∈ FastEnv.baselineMachineConfig.calleeSavedRegs)) 0
    (fun _ => (ltconf, [], []))
  let stack_post := stack_pair.1
  have hA_post := panToTargetFullMakeInitAssumptions
    c FastEnv.baselineMachineConfig (sourceFfi input) t m bitmapPtr
    bitmapDm sharedDm post (LabToTarget.compile riscvConfig)
    InitECandidate.nativeCode 3788 ltconf sourceDeclarations col wprog
    InitECandidate.bitmaps wconf fs p 0 (oracleBackendConfigOk w.oracles)
    (riscvMachineConfigOk _ hmc_fe)
    (oracleMachineInitOk w.oracles _ hmc_fe) hisa_fe
    hwtw hwts sourceDistinctFunctions
    (by
      rw [hnames.1, hnames.2]
      exact ⟨ha2, ha4, hab, horder, hspace, hdisjoint, hm0, hm1, hm2, hm3, hm4, hbitmap⟩)
  change FullMakeInitSemantics.Assumptions _ _ _ _ _ _ _ lab_post _ _ _ at hA_post
  have hsuccess_post : stack_pair.2 ≠ none :=
    (FullMakeInitSemantics.fullMakeInitSemantics
      ⟨(show FullMakeInit.fullMakeInit _ _ _ _ _ _ _ _ _ _ _ = (stack_pair.1, stack_pair.2) from rfl), hA_post⟩).1
  obtain ⟨aux_post, haux_post⟩ := Option.ne_none_iff_exists'.mp hsuccess_post
  have hinit_post : FullMakeInit.fullMakeInit c.stackConf c.dataConf
      (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
      InitECandidate.bitmaps p lab_post
      (fun k => decide (k ∈ FastEnv.baselineMachineConfig.calleeSavedRegs)) 0
      (fun _ => (ltconf, [], [])) = (stack_post, some aux_post) := Prod.ext rfl haux_post
  obtain ⟨heapLen_bv, hfront_post⟩ := frontendRelation_from_initialization
    input w post post_rel t m bitmapDm sharedDm ltconf p wprog
    hm_ord hshared hgi_post_c stack_post aux_post hA_post hinit_post hnonfail
  have hsafe_mem_post : RuntimeLabels.MemorySafe storeConstsStubLocation lab_post.memDomain lab_post.memory := by
    apply RuntimeLabels.memorySafe_of_goodInitState storeConstsStubLocation _ _ _ _ t m _ _ _ hgi_post_c
    intro a ha; change (_ && holByteAligned a) = true at ha; simp only [Bool.and_eq_true] at ha; exact ha.2
  obtain ⟨hlab_nt_max, hlab_ne_max⟩ := lab_bounds_from_frontend
    input k_pan c col wprog wconf fs p ltconf lab_post stack_post aux_post
    hwtw hwts hinit_post hA_post hsafe_mem_post rfl heapLen_bv hfront_post
    stCtxt s_decls hst hdecls res s_post hrun hne_pan hnt_pan
    h_front h_word_all (h_m7313 col wprog wconf fs p hwtw hwts)
  have hffi_lt : ltconf.ffiNames = some FastEnv.baselineMachineConfig.ffiNames := by
    rw [hltconf, ArtifactEnv.baseline_installation_metadata.1,
        ← R12_Stage4BoundArgon.baselineNames_eq, hffiN]
  have hshmem_eq : FastEnv.baselineMmio = ltconf.shmemExtra := by
    rw [hltconf, ArtifactEnv.baseline_mmio_projection, R12_Stage4BoundArgon.baselineMmio_eq]
  have hmmio_lt := Eq.mp (congrArg (fun sh =>
      ∀ i, mmioPcsMinIndex FastEnv.baselineMachineConfig.ffiNames = some i →
        sh.map (fun rec => (FastEnv.baselineMachineConfig.target.getPc post).toNat + rec.entryPc) =
          (FastEnv.baselineMachineConfig.ffiEntryPcs.map BitVec.toNat).drop i ∧
        FastEnv.baselineMachineConfig.mmioInfo =
          List.zip ((List.range sh.length).map (fun index => index + i))
            (sh.map (fun rec => (rec.nbytes,
              HolAddr.addr rec.addrReg (BitVec.ofNat 64 rec.addrOff), rec.reg,
              BitVec.ofNat 64 rec.exitPc + FastEnv.baselineMachineConfig.target.getPc post))) ∧
        3788 + InitECandidate.nativeCode.length + ffiOffset * (i + 3) < 2 ^ 64) hshmem_eq) hmmio
  exact target_not_timeOut_from_lab_bounds
    input k_pan w post shift col wprog wconf fs p ltconf hwtw hwts hlab
    t m bitmapDm sharedDm hgi_post_c hffi_lt hmmio_lt hlab_nt_max hlab_ne_max

end InitECandidate.Solver.Wave8Stage.Stage5BridgeArgon
