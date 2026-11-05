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

theorem frontendRelation_of_fields
    (input : Guest.InputBlob)
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config Guest.HostMemory)
    (cfg : LabToTarget.Config) (heapLen : BitVec 64)
    (hmem : ∀ a, (sourceInitialState input).memaddrs a →
      (InitializedPipelineTransfer.nativeWordState riscvConfig wprog InitECandidate.bitmaps stack cfg).memory a =
        wlabWlocExact ((sourceInitialState input).memory a))
    (hnolab : noLabelsHOL
      (InitializedPipelineTransfer.nativeWordState riscvConfig wprog InitECandidate.bitmaps stack cfg).memory
      (fun a => (InitializedPipelineTransfer.nativeWordState riscvConfig wprog InitECandidate.bitmaps stack cfg).mdomain a = true))
    (hdom : (fun a => (InitializedPipelineTransfer.nativeWordState riscvConfig wprog InitECandidate.bitmaps stack cfg).mdomain a = true) =
      (fun a => (sourceInitialState input).memaddrs a ∨ StackRemove.addresses (sourceInitialState input).topAddr globalsWords a))
    (hshared : (fun a => (InitializedPipelineTransfer.nativeWordState riscvConfig wprog InitECandidate.bitmaps stack cfg).shMdomain a = true) =
      (sourceInitialState input).shMemaddrs)
    (hbe : (InitializedPipelineTransfer.nativeWordState riscvConfig wprog InitECandidate.bitmaps stack cfg).be = (sourceInitialState input).be)
    (hffi : (InitializedPipelineTransfer.nativeWordState riscvConfig wprog InitECandidate.bitmaps stack cfg).ffi = (sourceInitialState input).ffi)
    (hcurr : (InitializedPipelineTransfer.nativeWordState riscvConfig wprog InitECandidate.bitmaps stack cfg).store.lookup .currHeap = some (.word (sourceInitialState input).baseAddr))
    (hlen : (InitializedPipelineTransfer.nativeWordState riscvConfig wprog InitECandidate.bitmaps stack cfg).store.lookup .heapLength = some (.word heapLen))
    (htop : (sourceInitialState input).topAddr = (sourceInitialState input).baseAddr + 2 * heapLen - panBytesInWord 64 * BitVec.ofNat 64 globalsWords)
    (hnonfail : PanSemStateFiniteExact.semanticsDecls (sourceInitialState input) (ofString "main") sourceDeclarations ≠ .fail) :
    InitializedPipelineTransfer.FrontendRelation (sourceInitialState input)
      (InitializedPipelineTransfer.frontendWordState riscvConfig sourceDeclarations wprog InitECandidate.bitmaps stack cfg)
      riscvConfig.isa sourceDeclarations (ofString "main") globalsWords heapLen := by
  exact ⟨hmem, hnolab, rfl, sourceGlobalsSize.symm, sourceDistinctParams,
    hdom, hshared, hbe, hffi, hcurr, hlen, htop, sourceDistinctFunctions,
    R12_Stage1To2BoundArgon.sourceInitialState_topAddr_byteAligned input,
    SourceHeapFacts.source_globals_allocatable input,
    rfl, rfl, rfl, rfl, sourceExceptionBound, rfl,
    sptLookup_sptInsert_zero (WordLocW.loc 1 0) Spt.ln, Or.inr rfl, hnonfail⟩

theorem frontendRelation_from_initialization
    (input : Guest.InputBlob) (w : LeanBridge.ConcreteOracleCompilationWitness)
    (post : RiscV.L3.riscv_state)
    (post_rel : targetStateRel riscvTarget installedAsm post)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapDm sharedDm : BitVec 64 → Bool)
    (ltconf : LabToTarget.Config) (p : List (Nat × HolProg 64))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (hm_ord : ∀ a, ordinaryDomain a → m a = wlabWlocExact (sourceMemory a))
    (hshared : sharedDomain = fun a => sharedDm a = true ∧ holByteAligned a = true)
    (hgi_post_c : goodInitState FastEnv.baselineMachineConfig post
      InitECandidate.nativeCode 3788 t m
      (fun a => decide
        (t.regs (StackNames.findNameSpt (oracleCompilerConfig w.oracles).stackConf.regNames 2) ≤ a ∧
         a < t.regs (StackNames.findNameSpt (oracleCompilerConfig w.oracles).stackConf.regNames 4)) || bitmapDm a)
      sharedDm) :
    let c := oracleCompilerConfig w.oracles
    let lab_post := pipelineLabInitState c FastEnv.baselineMachineConfig (sourceFfi input)
      t m bitmapDm sharedDm post InitECandidate.nativeCode 3788 ltconf p
    ∀ (stack_post aux_post : StackSemStateFiniteExact 64 LabToTarget.Config Guest.HostMemory),
    FullMakeInitSemantics.Assumptions c.stackConf c.dataConf
      (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
      InitECandidate.bitmaps p lab_post
      (fun k => decide (k ∈ FastEnv.baselineMachineConfig.calleeSavedRegs)) 0
      (fun _ => (ltconf, [], [])) →
    FullMakeInit.fullMakeInit c.stackConf c.dataConf
      (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
      InitECandidate.bitmaps p lab_post
      (fun k => decide (k ∈ FastEnv.baselineMachineConfig.calleeSavedRegs)) 0
      (fun _ => (ltconf, [], [])) = (stack_post, some aux_post) →
    PanSemStateFiniteExact.semanticsDecls (sourceInitialState input)
      (ofString "main") sourceDeclarations ≠ .fail →
    ∃ heapLen_bv, InitializedPipelineTransfer.FrontendRelation
      (sourceInitialState input)
      (InitializedPipelineTransfer.frontendWordState riscvConfig sourceDeclarations
        wprog InitECandidate.bitmaps stack_post ltconf)
      riscvConfig.isa sourceDeclarations (ofString "main") globalsWords heapLen_bv := by
  intro c lab_post stack_post aux_post hA_post hinit_post hnonfail
  have hmc_fe : isRiscvMachineConfig FastEnv.baselineMachineConfig :=
    R12_Stage4BoundArgon.fastEnv_baseline_machine_isRiscv
  have hinst_post := LeanBridge.oracle_baseline_installation_transport input w.c post post_rel
    (LeanBridge.oracle_baseline_installation input w.c
      (by rw [w.hlab]; exact ArtifactEnv.baseline_pan_installed input))
  obtain ⟨_, _, hsplit, hbase, hlen, htop, hglobals, hdomain,
    haligned, hadj2, hadj4, hleft, hright, hmax_heap, hendian, _, _⟩ := hinst_post
  rw [← R12_Stage4BoundArgon.baselineMachineConfig_eq] at hsplit hbase hlen hdomain haligned hadj2 hadj4 hleft hright hmax_heap hendian
  let wst_post := InitializedPipelineTransfer.nativeWordState riscvConfig wprog InitECandidate.bitmaps stack_post ltconf
  let pre_post := InitializedPipelineTransfer.frontendWordState riscvConfig sourceDeclarations wprog InitECandidate.bitmaps stack_post ltconf
  have hregs_post := hgi_post_c.1.2.2.2.1
  have hmc_ok_fe := riscvMachineConfigOk _ hmc_fe
  have hreg_post : ∀ r, asmRegOkExact r FastEnv.baselineMachineConfig.target.config = true →
      t.regs r = FastEnv.baselineMachineConfig.target.getReg post r := by
    intro r hr
    simp only [asmRegOkExact, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hr
    exact (hregs_post r hr).symm
  have hr2 := hreg_post _ hmc_ok_fe.2.2.2.1
  have hr3 := hreg_post _ hmc_ok_fe.2.2.2.2.1
  have hr4 := hreg_post _ hmc_ok_fe.2.2.2.2.2.1
  have hmword_post := hgi_post_c.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h2_reg : lab_post.regs lab_post.lenReg = .word (sourceInitialState input).baseAddr := by
    rw [pipelineLabInitState_regs_lenReg, hr2, hbase]
  have h3_reg : lab_post.regs lab_post.ptr2Reg = .word (FastEnv.baselineMachineConfig.target.getReg post FastEnv.baselineMachineConfig.ptr2Reg) := by
    rw [pipelineLabInitState_regs_ptr2Reg, hr3]
  have h4_reg : lab_post.regs lab_post.len2Reg = .word (FastEnv.baselineMachineConfig.target.getReg post FastEnv.baselineMachineConfig.len2Reg) := by
    rw [pipelineLabInitState_regs_len2Reg, hr4]
  obtain ⟨_, _, -, -, -, g2, -, -, a2, -⟩ := panToTargetInitCodeRun hA_post
  rw [h2_reg] at g2; cases g2
  have hbase_mod : (sourceInitialState input).baseAddr.toNat % (64 / 8) = 0 :=
    (holByteAligned_iff_mod (Or.inr rfl) _).1 a2
  obtain ⟨_, g2', hcurr, hheapLW⟩ :=
    panToTargetWordInitStore (ac := riscvConfig)
      (k := riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length))
      (wcode := sptFromAList wprog)
      (worac := fun _ => ((InitECandidate.bitmaps.length, ltconf), [])) hA_post hinit_post
  rw [h2_reg] at g2'; cases g2'
  rw [readPointers_s2 hA_post h2_reg h3_reg h4_reg] at hheapLW
  have hlo_post : (sourceInitialState input).baseAddr +
      StackRemove.bytesInWord 64 * BitVec.ofNat 64 StackRemove.maxStackAlloc ≤
      FastEnv.baselineMachineConfig.target.getReg post FastEnv.baselineMachineConfig.ptr2Reg := by
    rw [← hbase]
    simpa only [LeanBridge.baselineAdj2, BitVec.mul_comm] using (hadj2 ▸ hleft)
  have hhi_post : FastEnv.baselineMachineConfig.target.getReg post FastEnv.baselineMachineConfig.ptr2Reg ≤
      FastEnv.baselineMachineConfig.target.getReg post FastEnv.baselineMachineConfig.len2Reg -
      StackRemove.bytesInWord 64 * BitVec.ofNat 64 StackRemove.maxStackAlloc := by
    simpa only [LeanBridge.baselineAdj4, BitVec.mul_comm] using (hadj4 ▸ hright)
  have hheap_post : (FastEnv.baselineMachineConfig.target.getReg post FastEnv.baselineMachineConfig.ptr2Reg +
      -1 * FastEnv.baselineMachineConfig.target.getReg post FastEnv.baselineMachineConfig.lenReg).toNat ≤
      (StackRemove.bytesInWord 64).toNat * (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1) :=
    hmax_heap
  have hsnd := panToTargetHeapLimitSnd (Or.inr rfl) (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (sourceInitialState input).baseAddr
    (FastEnv.baselineMachineConfig.target.getReg post FastEnv.baselineMachineConfig.ptr2Reg)
    (FastEnv.baselineMachineConfig.target.getReg post FastEnv.baselineMachineConfig.len2Reg) a2
    (hbase ▸ hsplit) (by rw [BitVec.mul_comm]; exact hlo_post)
    (by rw [BitVec.mul_comm]; exact hhi_post)
    (by rw [← hbase, BitVec.add_comm, Nat.mul_comm]; exact hheap_post)
    (oracleHeapLimit_lt w.oracles) (hbase ▸ haligned)
  rw [BitVec.add_comm (-1 * (sourceInitialState input).baseAddr), ← hlen] at hsnd
  have hmd := panToTargetWordInitMdomain (ac := riscvConfig)
    (k := riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length))
    (wcode := sptFromAList wprog)
    (worac := fun _ => ((InitECandidate.bitmaps.length, ltconf), []))
    (sourceInitialState input).baseAddr
    (FastEnv.baselineMachineConfig.target.getReg post FastEnv.baselineMachineConfig.ptr2Reg)
    (FastEnv.baselineMachineConfig.target.getReg post FastEnv.baselineMachineConfig.len2Reg)
    hA_post hinit_post h2_reg h3_reg h4_reg
    (by rw [BitVec.mul_comm]; exact hlo_post)
    (by rw [BitVec.mul_comm]; exact hhi_post)
    (by rw [← hbase, BitVec.add_comm, Nat.mul_comm]; exact hheap_post)
    (oracleHeapLimit_lt w.oracles) (hbase ▸ haligned)
  rw [← hlen] at hmd
  have hmdP : (fun a => wst_post.mdomain a = true) =
      StackRemove.addresses (sourceInitialState input).baseAddr LeanBridge.baselineHeapLen := by
    funext a; rw [hmd a, decide_eq_true_eq]
  obtain ⟨hffi_w, hbe_w, hsh_w, hmem_w⟩ := panToTargetWordInitMemory
    (ac := riscvConfig)
    (k := riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length))
    (wcode := sptFromAList wprog)
    (worac := fun _ => ((InitECandidate.bitmaps.length, ltconf), [])) hA_post hinit_post
  have hin : ∀ a, (sourceInitialState input).memaddrs a → wst_post.mdomain a = true := by
    intro a ha
    have : StackRemove.addresses (sourceInitialState input).baseAddr LeanBridge.baselineHeapLen a := by
      rw [← addressesSplitGlobals (Or.inr rfl) (sourceInitialState input).baseAddr LeanBridge.baselineHeapLen globalsWords hglobals]
      exact .inl ((hbase ▸ hdomain) ▸ ha)
    rw [← hmdP] at this; exact this
  have hpm_src : ∀ a, (sourceInitialState input).memaddrs a →
      m a = wlabWlocExact ((sourceInitialState input).memory a) := by
    have hdom_eq := InitE.source_memory_domain input
    intro a ha
    have ha_ord : ordinaryDomain a := by rw [← hdom_eq]; exact ha
    exact hm_ord a ha_ord
  have hbw_eq : StackRemove.bytesInWord 64 = (wordSemBytesInWord : BitVec 64) := rfl
  let heapLen_bv := BitVec.ofNat 64 (StackRemove.Proofs.InitLimits.getStackHeapLimit
      (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
      ((sourceInitialState input).baseAddr,
       FastEnv.baselineMachineConfig.target.getReg post FastEnv.baselineMachineConfig.ptr2Reg,
       FastEnv.baselineMachineConfig.target.getReg post FastEnv.baselineMachineConfig.len2Reg)).2 *
    StackRemove.bytesInWord 64
  have hfront_post : InitializedPipelineTransfer.FrontendRelation
      (sourceInitialState input) pre_post riscvConfig.isa sourceDeclarations
      (ofString "main") globalsWords heapLen_bv := by
    apply frontendRelation_of_fields input wprog stack_post ltconf heapLen_bv
      ?_ ?_ ?_ ?_ ?_ ?_ hcurr hheapLW ?_ hnonfail
    · intro a ha
      exact (hmem_w a (hin a ha)).trans (hpm_src a ha)
    · intro a ha
      have hadr : StackRemove.addresses (sourceInitialState input).baseAddr LeanBridge.baselineHeapLen a := by
        rw [← hmdP]; exact ha
      obtain ⟨w_val, -, hw_val⟩ := hmword_post a
      rw [LabToTarget.holByteAlign_of_aligned (Or.inr rfl) a
        (addresses_mod (Or.inr rfl) (sourceInitialState input).baseAddr hbase_mod LeanBridge.baselineHeapLen a hadr)] at hw_val
      exact ⟨w_val, (hmem_w a ha).trans hw_val⟩
    · show (fun a => wst_post.mdomain a = true) = _
      have hmemaddrs' : (sourceInitialState input).memaddrs =
          StackRemove.addresses (sourceInitialState input).baseAddr (LeanBridge.baselineHeapLen - globalsWords) := by
        rw [← hbase]; exact hdomain
      rw [hmdP, ← addressesSplitGlobals (Or.inr rfl) (sourceInitialState input).baseAddr LeanBridge.baselineHeapLen globalsWords hglobals,
        hmemaddrs', htop, hbw_eq]
    · show (fun a => wst_post.shMdomain a = true) = _
      rw [hsh_w]
      funext a
      change ((sharedDm a && holByteAligned a) = true) = sharedDomain a
      rw [hshared]
      simp [Bool.and_eq_true]
    · exact hbe_w.trans hendian
    · exact hffi_w
    · rw [htop]
      have e1 : (2 : BitVec 64) * heapLen_bv =
          (wordSemBytesInWord : BitVec 64) * BitVec.ofNat 64 LeanBridge.baselineHeapLen := by
        dsimp only [heapLen_bv]
        rw [← hsnd, BitVec.ofNat_mul, hbw_eq, BitVec.mul_comm (wordSemBytesInWord : BitVec 64),
            ← BitVec.mul_assoc]
        rfl
      rw [e1, mul64_div8_bv globalsWords]
  exact ⟨heapLen_bv, hfront_post⟩

end InitECandidate.Solver.Wave8Stage.Stage5BridgeArgon
