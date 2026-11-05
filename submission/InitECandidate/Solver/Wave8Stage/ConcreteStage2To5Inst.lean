import InitECandidate.Solver.Wave8Stage.ConcreteIntegration
import InitECandidate.Solver.Wave8Stage.Stage5FrontendArgon

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace InitECandidate.Solver.Wave8Stage.ConcreteStage2To5Inst
open Classical InitE
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Pancake.Proofs.PanToTarget
open InitECandidate.Solver InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Stage
open InitECandidate.Solver.SelfContainedPipelineBridge
open InitECandidate.Solver.Wave8GuestInv.InitializedPipelineTransfer
open InitECandidate.Solver.Wave8GuestInv.InitializedLabTransfer

noncomputable def concreteTargetClock
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (oracles : List (Option (Spt Nat)))
    (p : List (Nat × HolProg 64)) (k_pan : Nat) : Nat :=
  let c := oracleCompilerConfig oracles
  let M := Stage4.codeStepBudget (FullMakeInitSemantics.code2 c.stackConf c.dataConf
    (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset p)
  InitE.bootstrapSteps +
    9 * (2 * (M + 1) * stackClock sourceDeclarations (ofString "main") wprog k_pan + (3 * M + 2) + 1)

theorem pan_to_target_concrete_affine_not_timeOut
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (input : Guest.InputBlob) (k_pan : Nat)
    (hnonfail : PanSemStateFiniteExact.semanticsDecls
      (sourceInitialState input) (ofString "main") sourceDeclarations ≠ .fail)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hst : decsStcnamesHOLExact [] sourceDeclarations = some stCtxt)
    (hdecls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
      {sourceInitialState input with structs := stCtxt}
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls)
    (res : Option (PanSemResultExact 64)) (s_post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hrun : PanSemStateFiniteExact.evaluateHOLFiniteState {s_decls with clock := k_pan}
      (.call none (ofString "main") [] : ProgHOL 64) = (res, s_post))
    (hne_pan : panEntryClass res ≠ .RunError)
    (hnt_pan : res ≠ some .timeOut) :
    ∃ col wprog wconf fs p ltconf,
      WordToWord.compile (oracleCompilerConfig w.oracles).wordToWordConf riscvConfig
        (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, wprog) ∧
      WordToStack.Native.compileNative riscvConfig false wprog =
        (InitECandidate.bitmaps, wconf, fs, p) ∧
      LabToTarget.compile riscvConfig (oracleCompilerConfig w.oracles).labConf
        (StackToLab.compile (oracleCompilerConfig w.oracles).stackConf
          (oracleCompilerConfig w.oracles).dataConf
          (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig w.oracles).dataConf - 1)
          (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3))
          riscvConfig.addrOffset p) = some (InitECandidate.nativeCode, ltconf) ∧
      (evaluateTargetHOL ArtifactEnv.baselineSubmission.machineConfig (sourceFfi input)
        (concreteTargetClock wprog w.oracles p k_pan)
        (ArtifactEnv.baselineSubmission.initialState input)).1 ≠ .timeOut := by
  obtain ⟨post, shift, _, post_rel⟩ := ConcreteBaseline.ExactBootstrap.full_evaluator_exact
    (sourceFfi input) (ConcreteBaseline.baselineInitialState input)
    (ConcreteBaseline.baselineInitialState_related input)
  let c := oracleCompilerConfig w.oracles
  have hmc_fe : isRiscvMachineConfig FastEnv.baselineMachineConfig :=
    R12_Stage4BoundArgon.fastEnv_baseline_machine_isRiscv
  have hmc_ok_fe := riscvMachineConfigOk _ hmc_fe
  have hconfig_fe : FastEnv.baselineMachineConfig.target.config = riscvConfig := by
    rw [hmc_fe.1]; rfl
  have hisa_fe : FastEnv.baselineMachineConfig.target.config.isa ≠ .ag32 := by
    rw [hconfig_fe]; exact Stage5BridgeArgon.riscvConfig_isa_ne_ag32
  obtain ⟨col, wprog, wconf, fs, p, ltconf, hwtw, hwts, hlab, hc_eq⟩ :=
    Stage5BridgeArgon.unpack_compileProgMax c FastEnv.baselineMachineConfig hconfig_fe
      sourceDeclarations InitECandidate.nativeCode InitECandidate.bitmaps w.c w.depth w.compiled
  have hltconf : ltconf = baselineLabConfig := hc_eq.symm.trans w.hlab
  have hlab_rv : LabToTarget.compile riscvConfig c.labConf
      (StackToLab.compile c.stackConf c.dataConf
        (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
        (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3))
        riscvConfig.addrOffset p) = some (InitECandidate.nativeCode, ltconf) := by
    simpa only [hconfig_fe] using hlab
  refine ⟨col, wprog, wconf, fs, p, ltconf, hwtw, hwts, hlab_rv, ?_⟩
  have hpan_inst_post : panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      (some FastEnv.baselineNames) (11, 13) FastEnv.baselineMachineConfig
      FastEnv.baselineMmio post (wlabWlocExact ∘ sourceMemory) ordinaryDomain sharedDomain :=
    Stage5BridgeArgon.panInstalled_fe_of_ae _ _ _ _ _ _ _ _
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
    hmc_ok_fe (oracleMachineInitOk w.oracles _ hmc_fe) hisa_fe
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
  obtain ⟨heapLen_bv, hfront_post⟩ := Stage5BridgeArgon.frontendRelation_from_initialization
    input w post post_rel t m bitmapDm sharedDm ltconf p wprog
    hm_ord hshared hgi_post_c stack_post aux_post hA_post hinit_post hnonfail
  have hsafe_mem_post : RuntimeLabels.MemorySafe storeConstsStubLocation lab_post.memDomain lab_post.memory := by
    apply RuntimeLabels.memorySafe_of_goodInitState storeConstsStubLocation _ _ _ _ t m _ _ _ hgi_post_c
    intro a ha; change (_ && holByteAligned a) = true at ha; simp only [Bool.and_eq_true] at ha; exact ha.2
  have hlab_nt := pan_to_initialized_lab_not_timeOut
    riscvConfig c.wordToWordConf sourceDeclarations col wprog InitECandidate.bitmaps wconf fs p
    c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
    lab_post (fun k => decide (k ∈ FastEnv.baselineMachineConfig.calleeSavedRegs)) 0 ltconf
    stack_post aux_post (Or.inr rfl) Stage5BridgeArgon.riscvConfig_regs_bound
    Stage5BridgeArgon.riscvConfig_isa_ne_ag32 hwtw hwts hinit_post
    (sourceInitialState input) (ofString "main") globalsWords heapLen_bv hfront_post
    stCtxt s_decls hst hdecls k_pan res s_post hrun hne_pan hnt_pan hA_post hsafe_mem_post
  let M := Stage4.codeStepBudget (FullMakeInitSemantics.code2 c.stackConf c.dataConf
    (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset p)
  let k_lab := 2 * (M + 1) * stackClock sourceDeclarations (ofString "main") wprog k_pan + (3 * M + 2)
  have hstack_complete := pan_to_initialized_stack_complete
    riscvConfig c.wordToWordConf sourceDeclarations col wprog InitECandidate.bitmaps wconf fs p
    c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
    lab_post (fun k => decide (k ∈ FastEnv.baselineMachineConfig.calleeSavedRegs)) 0 ltconf
    stack_post aux_post (Or.inr rfl) Stage5BridgeArgon.riscvConfig_regs_bound
    Stage5BridgeArgon.riscvConfig_isa_ne_ag32 hwtw hwts hinit_post
    (sourceInitialState input) (ofString "main") globalsWords heapLen_bv hfront_post
    stCtxt s_decls hst hdecls k_pan res s_post hrun hne_pan hnt_pan
  have hready := EntryClassTransfer.stack_complete_ready _ hstack_complete
  have hnonfail_lab := CompletedNonfailure.lab_nonfail_of_ready
    c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
    InitECandidate.bitmaps p lab_post
    (fun k => decide (k ∈ FastEnv.baselineMachineConfig.calleeSavedRegs)) 0
    (fun _ => (ltconf, [], [])) stack_post (some aux_post) hinit_post hA_post
    (stackClock sourceDeclarations (ofString "main") wprog k_pan) hready.1 hready.2
  have hlab_ne := Wave8Stage.lab_run_not_error_of_nonfail lab_post hnonfail_lab k_lab
  let code_lab := StackToLab.compile c.stackConf c.dataConf
    (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset p
  let coracle : Nat → LabToTarget.Config × LabProgHOL 64 := fun _ =>
    (ltconf, StackToLab.compileNoStubs c.stackConf.regNames c.stackConf.jump riscvConfig.addrOffset
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) [])
  let lab_unaligned := InitializedTransfer.initialLab FastEnv.baselineMachineConfig post
    (sourceFfi input) code_lab InitECandidate.nativeCode 3788 t m dm_unaligned sharedDm coracle
  have hlab_eq_align : lab_post = alignDm (alignSdm lab_unaligned) :=
    Stage5BridgeArgon.pipelineLabInitState_eq_align c FastEnv.baselineMachineConfig hconfig_fe
      (sourceFfi input) t m bitmapDm sharedDm post InitECandidate.nativeCode 3788 ltconf p
  have hlab_unaligned_nt : (LabSem.evaluate { lab_unaligned with clock := k_lab }).1 ≠ .timeOut := by
    rw [← Stage4.lab_align_result (Or.inr rfl) lab_unaligned k_lab, ← hlab_eq_align]
    exact hlab_nt
  have hlab_unaligned_ne : (LabSem.evaluate { lab_unaligned with clock := k_lab }).1 ≠ .error := by
    rw [← Stage4.lab_align_result (Or.inr rfl) lab_unaligned k_lab, ← hlab_eq_align]
    exact hlab_ne
  have hcfg_ok : BackendProof.backendConfigOk FastEnv.baselineMachineConfig.target.config c := by
    rw [hconfig_fe]; exact oracleBackendConfigOk w.oracles
  have hcode_lab_eq : StackToLab.compile c.stackConf c.dataConf
      (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
      (FastEnv.baselineMachineConfig.target.config.regCount -
        (FastEnv.baselineMachineConfig.target.config.avoidRegs.length + 3))
      FastEnv.baselineMachineConfig.target.config.addrOffset p = code_lab := by
    dsimp only [code_lab]; rw [hconfig_fe]
  have hlab_code : compile FastEnv.baselineMachineConfig.target.config c.labConf code_lab =
      some (InitECandidate.nativeCode, ltconf) :=
    Eq.mp (congrArg (fun x => compile FastEnv.baselineMachineConfig.target.config c.labConf x =
      some (InitECandidate.nativeCode, ltconf)) hcode_lab_eq) hlab
  have hgood_code : goodCode FastEnv.baselineMachineConfig.target.config (.ln : Spt (Spt Nat)) code_lab := by
    have := panToTargetGoodCodeFromSource (β := Nat) c FastEnv.baselineMachineConfig
      sourceDeclarations col wprog InitECandidate.bitmaps wconf fs p
      hcfg_ok (Or.inr rfl) hisa_fe (by rw [hconfig_fe]; exact hwtw)
      (by rw [hconfig_fe]; exact hwts) sourceDistinctFunctions sourceGoodCode
    exact Eq.mp (congrArg (goodCode FastEnv.baselineMachineConfig.target.config (.ln : Spt (Spt Nat))) hcode_lab_eq) this
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
  have horacle_ok := panToTargetCompilerOracleOk FastEnv.baselineMachineConfig.target.config
    c.labConf ltconf code_lab InitECandidate.nativeCode FastEnv.baselineMachineConfig.ffiNames
    c.stackConf.regNames c.stackConf.jump riscvConfig.addrOffset
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3))
    hlab_code hcfg_ok.2.2.2.2.1 hffi_lt
  have hnis := panToTargetNoInstallOrNoShareMem sourceDeclarations riscvConfig riscvConfig.isa _
    c.wordToWordConf col wprog InitECandidate.bitmaps wconf fs p c.stackConf c.dataConf
    (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
    FastEnv.baselineMachineConfig.ffiNames ⟨sourceDistinctFunctions, Stage5BridgeArgon.riscvConfig_isa_ne_ag32, rfl, hwtw, hwts⟩
  have hno_install : LabProps.noInstall code_lab :=
    from_pan_to_lab_no_install sourceDeclarations riscvConfig riscvConfig.isa _
      c.wordToWordConf col wprog InitECandidate.bitmaps wconf fs p c.stackConf c.dataConf
      (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
      ⟨sourceDistinctFunctions, Stage5BridgeArgon.riscvConfig_isa_ne_ag32, rfl, hwtw, hwts⟩
  have hffiOk : ∀ ffis, c.labConf.ffiNames = some ffis → ∀ name ∈ ffis, ∃ s, name = .extCall s := by
    intro ffis hsome
    have hnone : c.labConf.ffiNames = none := by
      change (oracleCompilerConfig w.oracles).labConf.ffiNames = none
      rfl
    rw [hnone] at hsome; cases hsome
  have hlab_imp : compileLab FastEnv.baselineMachineConfig.target.config c.labConf
      (LabFilter.filterSkip code_lab) = some (InitECandidate.nativeCode, ltconf) := hlab_code
  obtain ⟨ffis_tmp, hffis_tmp, i_idx, hi_idx⟩ := BackendProof.compileLabIMPMmioPcsMinIndex
    FastEnv.baselineMachineConfig.target.config c.labConf (LabFilter.filterSkip code_lab)
    InitECandidate.nativeCode ltconf
    ⟨hlab_imp, by
      cases hfn : c.labConf.ffiNames with
      | none => trivial
      | some l => exact hffiOk l hfn⟩
  have hffis_eq : FastEnv.baselineMachineConfig.ffiNames = ffis_tmp :=
    Option.some.inj (hffi_lt.symm.trans hffis_tmp)
  rw [← hffis_eq] at hi_idx
  obtain ⟨hentries_i, hmmio_i, hbound_i⟩ := hmmio_lt i_idx hi_idx
  obtain ⟨code2, labs, newNames, info, shiftedInfo, hbytes_eq, hInit⟩ :=
    Stage5BridgeArgon.general_compile_initialization FastEnv.baselineMachineConfig post code_lab
      c.labConf ltconf InitECandidate.nativeCode 3788 i_idx t m dm_unaligned sharedDm coracle
      hmc_ok_fe (fun _ => horacle_ok) hgood_code hcfg_ok.2.2.2.2.2.1 hcfg_ok.2.2.2.2.1
      hlab_code hffi_lt hgi_post_c
      hentries_i hmmio_i hnis hi_idx hbound_i hffiOk
  have hmc_cb_fe : ConcreteBaseline.baselineMachineConfig = FastEnv.baselineMachineConfig :=
    LeanBridge.config_eq.trans R12_Stage4BoundArgon.baselineMachineConfig_eq.symm
  rw [hmc_cb_fe] at shift
  have hlab_code2_ne : (LabSem.evaluate
      { InitializedTransfer.initialLab FastEnv.baselineMachineConfig post (sourceFfi input)
          code_lab (progToBytes code2) 3788 t m dm_unaligned sharedDm coracle with
        clock := k_lab }).1 ≠ .error :=
    Eq.mp (congrArg (fun bs => (LabSem.evaluate
      { InitializedTransfer.initialLab FastEnv.baselineMachineConfig post (sourceFfi input)
          code_lab bs 3788 t m dm_unaligned sharedDm coracle with
        clock := k_lab }).1 ≠ .error) hbytes_eq) hlab_unaligned_ne
  have hlab_code2_nt : (LabSem.evaluate
      { InitializedTransfer.initialLab FastEnv.baselineMachineConfig post (sourceFfi input)
          code_lab (progToBytes code2) 3788 t m dm_unaligned sharedDm coracle with
        clock := k_lab }).1 ≠ .timeOut :=
    Eq.mp (congrArg (fun bs => (LabSem.evaluate
      { InitializedTransfer.initialLab FastEnv.baselineMachineConfig post (sourceFfi input)
          code_lab bs 3788 t m dm_unaligned sharedDm coracle with
        clock := k_lab }).1 ≠ .timeOut) hbytes_eq) hlab_unaligned_nt
  have htarget_nt := Wave8Stage.stage5_lab_to_target_affine_not_timeOut
    FastEnv.baselineMachineConfig hmc_fe.1 (ConcreteBaseline.baselineInitialState input) post
    (sourceFfi input) code_lab code2 labs c.labConf.initClock i_idx 3788
    t m dm_unaligned sharedDm coracle newNames info shiftedInfo hInit hno_install k_lab
    hlab_code2_ne hlab_code2_nt bootstrapSteps shift
  rw [ArtifactEnv.baselineSubmission_machineConfig, ArtifactEnv.baselineSubmission_initialState,
      ← R12_Stage4BoundArgon.baselineMachineConfig_eq, ← LeanBridge.initial_eq]
  exact htarget_nt

theorem uncertified_uniform_not_timeOut_of_compile
    (w : LeanBridge.ConcreteOracleCompilationWitness) (k_pan : Nat)
    (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (wconf : WordToStack.Native.Config) (fs : List Nat) (p : List (Nat × HolProg 64))
    (hwtw : WordToWord.compile (oracleCompilerConfig w.oracles).wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, wprog))
    (hwts : WordToStack.Native.compileNative riscvConfig false wprog =
      (InitECandidate.bitmaps, wconf, fs, p))
    (hpan : UniformSourceClock.CoveredSourceUniformNotTimeOut k_pan) :
    FiniteRebudget.UniformNotTimeOut ArtifactEnv.baselineSubmission
      (concreteTargetClock wprog w.oracles p k_pan) := by
  intro input hgas outcome events hsource hcov
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
  obtain ⟨col', wprog', wconf', fs', p', _, hwtw', hwts', _, hnt⟩ :=
    pan_to_target_concrete_affine_not_timeOut w input k_pan hnonfail stCtxt s_decls hst hdecls
      res s_post hrun hne_pan hnt_pan
  have hwprog_eq : wprog = wprog' := (Prod.mk.inj (hwtw.symm.trans hwtw')).2
  subst hwprog_eq
  have hp_eq : p = p' := (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj (hwts.symm.trans hwts')).2).2).2
  subst hp_eq
  exact hnt

theorem uncertified_uniform_not_timeOut_exists
    (w : LeanBridge.ConcreteOracleCompilationWitness) (k_pan : Nat)
    (hpan : UniformSourceClock.CoveredSourceUniformNotTimeOut k_pan) :
    ∃ col wprog wconf fs p ltconf,
      WordToWord.compile (oracleCompilerConfig w.oracles).wordToWordConf riscvConfig
        (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, wprog) ∧
      WordToStack.Native.compileNative riscvConfig false wprog =
        (InitECandidate.bitmaps, wconf, fs, p) ∧
      LabToTarget.compile riscvConfig (oracleCompilerConfig w.oracles).labConf
        (StackToLab.compile (oracleCompilerConfig w.oracles).stackConf
          (oracleCompilerConfig w.oracles).dataConf
          (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig w.oracles).dataConf - 1)
          (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3))
          riscvConfig.addrOffset p) = some (InitECandidate.nativeCode, ltconf) ∧
      FiniteRebudget.UniformNotTimeOut ArtifactEnv.baselineSubmission
        (concreteTargetClock wprog w.oracles p k_pan) ∧
      InitE.Certificate
        (LeanBridge.finiteSubmission (concreteTargetClock wprog w.oracles p k_pan))
        (.finite (concreteTargetClock wprog w.oracles p k_pan)) := by
  have hmc_fe : isRiscvMachineConfig FastEnv.baselineMachineConfig :=
    R12_Stage4BoundArgon.fastEnv_baseline_machine_isRiscv
  have hconfig_fe : FastEnv.baselineMachineConfig.target.config = riscvConfig := by
    rw [hmc_fe.1]; rfl
  obtain ⟨col, wprog, wconf, fs, p, ltconf, hwtw, hwts, hlab, _⟩ :=
    Stage5BridgeArgon.unpack_compileProgMax (oracleCompilerConfig w.oracles)
      FastEnv.baselineMachineConfig hconfig_fe sourceDeclarations
      InitECandidate.nativeCode InitECandidate.bitmaps w.c w.depth w.compiled
  have hlab_rv : LabToTarget.compile riscvConfig (oracleCompilerConfig w.oracles).labConf
      (StackToLab.compile (oracleCompilerConfig w.oracles).stackConf
        (oracleCompilerConfig w.oracles).dataConf
        (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig w.oracles).dataConf - 1)
        (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3))
        riscvConfig.addrOffset p) = some (InitECandidate.nativeCode, ltconf) := by
    simpa only [hconfig_fe] using hlab
  have hunif := uncertified_uniform_not_timeOut_of_compile w k_pan col wprog wconf fs p hwtw hwts hpan
  exact ⟨col, wprog, wconf, fs, p, ltconf, hwtw, hwts, hlab_rv, hunif,
    LeanBridge.finite_certificate_of_witness w (concreteTargetClock wprog w.oracles p k_pan) hunif⟩

theorem uniform_not_timeOut_mono
    (sub : InitE.Submission) {k₁ k₂ : Nat} (hle : k₁ ≤ k₂)
    (h : FiniteRebudget.UniformNotTimeOut sub k₁) :
    FiniteRebudget.UniformNotTimeOut sub k₂ := by
  intro input hgas outcome events hsource hcov
  have hnt := h input hgas outcome events hsource hcov
  rcases hrun : evaluateTargetHOL sub.machineConfig (sourceFfi input) k₁
      (sub.initialState input) with ⟨res, post, ffi'⟩
  rw [hrun] at hnt
  have hpad := evaluateTargetAddClock sub.machineConfig (sourceFfi input) k₁
    (sub.initialState input) (k₂ - k₁) res post ffi' hrun hnt
  rw [Nat.add_sub_of_le hle] at hpad
  rw [hpad]
  exact hnt

theorem uncertified_uniform_not_timeOut_bounded
    (w : LeanBridge.ConcreteOracleCompilationWitness) (k_pan bound : Nat)
    (hbound : ∀ col wprog wconf fs p,
      WordToWord.compile (oracleCompilerConfig w.oracles).wordToWordConf riscvConfig
        (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, wprog) →
      WordToStack.Native.compileNative riscvConfig false wprog =
        (InitECandidate.bitmaps, wconf, fs, p) →
      concreteTargetClock wprog w.oracles p k_pan ≤ bound)
    (hpan : UniformSourceClock.CoveredSourceUniformNotTimeOut k_pan) :
    FiniteRebudget.UniformNotTimeOut ArtifactEnv.baselineSubmission bound := by
  obtain ⟨col, wprog, wconf, fs, p, _, hwtw, hwts, _, hunif, _⟩ :=
    uncertified_uniform_not_timeOut_exists w k_pan hpan
  exact uniform_not_timeOut_mono ArtifactEnv.baselineSubmission
    (hbound col wprog wconf fs p hwtw hwts) hunif

end InitECandidate.Solver.Wave8Stage.ConcreteStage2To5Inst
