import InitECandidate.Solver.Wave8Stage.Stage5InitializationArgon

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

theorem target_not_timeOut_from_lab_bounds
    (input : Guest.InputBlob) (k_pan : Nat)
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (post : RiscV.L3.riscv_state)
    (shift : ∀ clock, evaluateTargetHOL ConcreteBaseline.baselineMachineConfig (sourceFfi input)
      (bootstrapSteps + clock) (ConcreteBaseline.baselineInitialState input) =
      evaluateTargetHOL ConcreteBaseline.baselineMachineConfig (sourceFfi input) clock post)
    (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (wconf : WordToStack.Native.Config) (fs : List Nat) (p : List (Nat × HolProg 64))
    (ltconf : LabToTarget.Config)
    (hwtw : WordToWord.compile (oracleCompilerConfig w.oracles).wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, wprog))
    (hwts : WordToStack.Native.compileNative riscvConfig false wprog =
      (InitECandidate.bitmaps, wconf, fs, p))
    (hlab : LabToTarget.compile FastEnv.baselineMachineConfig.target.config
      (oracleCompilerConfig w.oracles).labConf
      (StackToLab.compile (oracleCompilerConfig w.oracles).stackConf
        (oracleCompilerConfig w.oracles).dataConf
        (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig w.oracles).dataConf - 1)
        (FastEnv.baselineMachineConfig.target.config.regCount -
          (FastEnv.baselineMachineConfig.target.config.avoidRegs.length + 3))
        FastEnv.baselineMachineConfig.target.config.addrOffset p) =
      some (InitECandidate.nativeCode, ltconf))
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapDm sharedDm : BitVec 64 → Bool)
    (hgi_post_c : goodInitState FastEnv.baselineMachineConfig post
      InitECandidate.nativeCode 3788 t m
      (fun a => decide
        (t.regs (StackNames.findNameSpt (oracleCompilerConfig w.oracles).stackConf.regNames 2) ≤ a ∧
         a < t.regs (StackNames.findNameSpt (oracleCompilerConfig w.oracles).stackConf.regNames 4)) || bitmapDm a)
      sharedDm)
    (hffi_lt : ltconf.ffiNames = some FastEnv.baselineMachineConfig.ffiNames)
    (hmmio_lt : ∀ i, mmioPcsMinIndex FastEnv.baselineMachineConfig.ffiNames = some i →
      ltconf.shmemExtra.map (fun rec => (FastEnv.baselineMachineConfig.target.getPc post).toNat + rec.entryPc) =
        (FastEnv.baselineMachineConfig.ffiEntryPcs.map BitVec.toNat).drop i ∧
      FastEnv.baselineMachineConfig.mmioInfo =
        List.zip ((List.range ltconf.shmemExtra.length).map (fun index => index + i))
          (ltconf.shmemExtra.map (fun rec => (rec.nbytes,
            HolAddr.addr rec.addrReg (BitVec.ofNat 64 rec.addrOff), rec.reg,
            BitVec.ofNat 64 rec.exitPc + FastEnv.baselineMachineConfig.target.getPc post))) ∧
      3788 + InitECandidate.nativeCode.length + ffiOffset * (i + 3) < 2 ^ 64) :
    let c := oracleCompilerConfig w.oracles
    let lab_post := pipelineLabInitState c FastEnv.baselineMachineConfig (sourceFfi input)
      t m bitmapDm sharedDm post InitECandidate.nativeCode 3788 ltconf p
    let k_lab_max := 2 * (7313 + 1) * (2 * (449 * k_pan + 452)) + (3 * 7313 + 2)
    (LabSem.evaluate { lab_post with clock := k_lab_max }).1 ≠ .timeOut →
    (LabSem.evaluate { lab_post with clock := k_lab_max }).1 ≠ .error →
    (evaluateTargetHOL ArtifactEnv.baselineSubmission.machineConfig (sourceFfi input)
      (118223496 * k_pan + 119233963)
      (ArtifactEnv.baselineSubmission.initialState input)).1 ≠ .timeOut := by
  intro c lab_post k_lab_max hlab_nt_max hlab_ne_max
  have hmc_fe : isRiscvMachineConfig FastEnv.baselineMachineConfig :=
    R12_Stage4BoundArgon.fastEnv_baseline_machine_isRiscv
  have hmc_ok_fe := riscvMachineConfigOk _ hmc_fe
  have hconfig_fe : FastEnv.baselineMachineConfig.target.config = riscvConfig := by
    rw [hmc_fe.1]; rfl
  have hisa_fe : FastEnv.baselineMachineConfig.target.config.isa ≠ .ag32 := by
    rw [hconfig_fe]; exact riscvConfig_isa_ne_ag32
  let dm_unaligned : BitVec 64 → Bool := fun a =>
    decide (t.regs (StackNames.findNameSpt c.stackConf.regNames 2) ≤ a ∧
      a < t.regs (StackNames.findNameSpt c.stackConf.regNames 4)) || bitmapDm a
  let code_lab := StackToLab.compile c.stackConf c.dataConf
    (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset p
  let coracle : Nat → LabToTarget.Config × LabProgHOL 64 := fun _ =>
    (ltconf, StackToLab.compileNoStubs c.stackConf.regNames c.stackConf.jump riscvConfig.addrOffset
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) [])
  let lab_unaligned := InitializedTransfer.initialLab FastEnv.baselineMachineConfig post
    (sourceFfi input) code_lab InitECandidate.nativeCode 3788 t m dm_unaligned sharedDm coracle
  have hlab_eq_align : lab_post = alignDm (alignSdm lab_unaligned) :=
    pipelineLabInitState_eq_align c FastEnv.baselineMachineConfig hconfig_fe
      (sourceFfi input) t m bitmapDm sharedDm post InitECandidate.nativeCode 3788 ltconf p
  have hlab_unaligned_nt : (LabSem.evaluate { lab_unaligned with clock := k_lab_max }).1 ≠ .timeOut := by
    rw [← Stage4.lab_align_result (Or.inr rfl) lab_unaligned k_lab_max, ← hlab_eq_align]
    exact hlab_nt_max
  have hlab_unaligned_ne : (LabSem.evaluate { lab_unaligned with clock := k_lab_max }).1 ≠ .error := by
    rw [← Stage4.lab_align_result (Or.inr rfl) lab_unaligned k_lab_max, ← hlab_eq_align]
    exact hlab_ne_max
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
  have horacle_ok := panToTargetCompilerOracleOk FastEnv.baselineMachineConfig.target.config
    c.labConf ltconf code_lab InitECandidate.nativeCode FastEnv.baselineMachineConfig.ffiNames
    c.stackConf.regNames c.stackConf.jump riscvConfig.addrOffset
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3))
    hlab_code hcfg_ok.2.2.2.2.1 hffi_lt
  have hnis := panToTargetNoInstallOrNoShareMem sourceDeclarations riscvConfig riscvConfig.isa _
    c.wordToWordConf col wprog InitECandidate.bitmaps wconf fs p c.stackConf c.dataConf
    (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
    FastEnv.baselineMachineConfig.ffiNames ⟨sourceDistinctFunctions, riscvConfig_isa_ne_ag32, rfl, hwtw, hwts⟩
  have hno_install : LabProps.noInstall code_lab :=
    from_pan_to_lab_no_install sourceDeclarations riscvConfig riscvConfig.isa _
      c.wordToWordConf col wprog InitECandidate.bitmaps wconf fs p c.stackConf c.dataConf
      (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
      ⟨sourceDistinctFunctions, riscvConfig_isa_ne_ag32, rfl, hwtw, hwts⟩
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
    general_compile_initialization FastEnv.baselineMachineConfig post code_lab
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
        clock := k_lab_max }).1 ≠ .error :=
    Eq.mp (congrArg (fun bs => (LabSem.evaluate
      { InitializedTransfer.initialLab FastEnv.baselineMachineConfig post (sourceFfi input)
          code_lab bs 3788 t m dm_unaligned sharedDm coracle with
        clock := k_lab_max }).1 ≠ .error) hbytes_eq) hlab_unaligned_ne
  have hlab_code2_nt : (LabSem.evaluate
      { InitializedTransfer.initialLab FastEnv.baselineMachineConfig post (sourceFfi input)
          code_lab (progToBytes code2) 3788 t m dm_unaligned sharedDm coracle with
        clock := k_lab_max }).1 ≠ .timeOut :=
    Eq.mp (congrArg (fun bs => (LabSem.evaluate
      { InitializedTransfer.initialLab FastEnv.baselineMachineConfig post (sourceFfi input)
          code_lab bs 3788 t m dm_unaligned sharedDm coracle with
        clock := k_lab_max }).1 ≠ .timeOut) hbytes_eq) hlab_unaligned_nt
  have htarget_nt := Wave8Stage.stage5_lab_to_target_affine_not_timeOut
    FastEnv.baselineMachineConfig hmc_fe.1 (ConcreteBaseline.baselineInitialState input) post
    (sourceFfi input) code_lab code2 labs c.labConf.initClock i_idx 3788
    t m dm_unaligned sharedDm coracle newNames info shiftedInfo hInit hno_install k_lab_max
    hlab_code2_ne hlab_code2_nt bootstrapSteps shift
  have hK_eq : bootstrapSteps + 9 * (k_lab_max + 1) = 118223496 * k_pan + 119233963 := by
    rw [InitE.bootstrapSteps_eq]
    dsimp only [k_lab_max]
    exact R12_Stage4BoundArgon.target_clock_decomposition k_pan
  rw [hK_eq] at htarget_nt
  rw [ArtifactEnv.baselineSubmission_machineConfig, ArtifactEnv.baselineSubmission_initialState,
      ← R12_Stage4BoundArgon.baselineMachineConfig_eq, ← LeanBridge.initial_eq]
  exact htarget_nt

end InitECandidate.Solver.Wave8Stage.Stage5BridgeArgon
