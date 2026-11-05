import InitECandidate.Solver.Wave8GuestInv.LeanBridge
import InitECandidate.Solver.Wave8GuestInv.Assembly
import InitECandidate.Solver.Wave8GuestInv.CertifiedPipelineTransfer
import InitECandidate.Solver.Wave8Stage.R12_Stage1To2BoundArgon
import InitECandidate.Solver.Wave8Stage.R12_Stage2To3BoundArgon
import InitECandidate.Solver.Wave8Stage.R12_Stage4BoundArgon
import InitECandidate.Solver.Wave8Stage.Stage4LabGlue

/-!
# Stage 5 Bridge: `StageTransfer` from Finite Obligations (`Stage5Bridge`)

Composes the verified Stage 1-4 bounds (`R12_Stage1To2BoundArgon`, `R12_Stage2To3BoundArgon`,
`R12_Stage4BoundArgon`) with the Stage 5 Lab-to-target affine transfer
(`Wave8Stage.stage5_lab_to_target_affine_not_timeOut`) on the actual bootstrapped machine state,
yielding `UniformSourceClock.CoveredSourceUniformNotTimeOut K_pan →
FiniteRebudget.UniformNotTimeOut ArtifactEnv.baselineSubmission K_target` from three finite
obligations:
* `h_front`: `FrontendStaticBudget.listBudget ConcreteCompilerCrep.source ≤ 448`;
* `h_word_all`: the Word-level cost certificate check on every compiled entry;
* `h_m7313`: the Stage 4 `codeStepBudget` bound `M ≤ 7313` on the installed stack code.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8Stage.Stage5Bridge
open Classical InitE
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

private theorem successfulIndex {α : Type} [DecidableEq α] (values : List α)
    (target : α) (offset index : Nat) (h : Misc.findIndex target values offset = some index) :
    ∃ i, ∃ hi : i < values.length, index = offset + i ∧ values[i]'hi = target := by
  induction values generalizing offset with
  | nil => simp [Misc.findIndex] at h
  | cons head tail ih =>
    by_cases he : head = target
    · have hs : offset = index := by simpa only [Misc.findIndex, if_pos he, Option.some.injEq] using h
      exact ⟨0, by simp, by omega, he⟩
    · have ht : Misc.findIndex target tail (offset + 1) = some index := by
        simpa only [Misc.findIndex, if_neg he] using h
      obtain ⟨i, hi, hindex, hvalue⟩ := ih (offset + 1) ht
      exact ⟨i + 1, by simp; omega, by omega, by simpa using hvalue⟩

private theorem bufferNotFfi {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) (pc : BitVec width) (size space i : Nat)
    (hstart : startPcOk mc pc) (hboundary : mmioPcsMinIndex mc.ffiNames = some i)
    (hbound : space + size + ffiOffset * (i + 3) < 2 ^ width) :
    ∀ bn, bn < space → BitVec.ofNat width bn + BitVec.ofNat width size + pc ∉
      mc.ffiEntryPcs.take i := by
  obtain ⟨_, _, _, _, _, _, _, boundary, hindex, hprefix, _, _⟩ := hstart
  have hi : boundary = i := Option.some.inj (hindex.symm.trans hboundary)
  subst boundary
  intro bn hbn hmem
  obtain ⟨j, hj, hvalue⟩ := List.mem_take_iff_getElem.mp hmem
  have hji : j < i := by omega
  have hfind := (hprefix j hji).2.2.2.2
  obtain ⟨found, _, hreturned, hentry⟩ := successfulIndex mc.ffiEntryPcs
    (pc - BitVec.ofNat width ((3 + j) * ffiOffset)) 0 j hfind
  have hfj : found = j := by omega
  subst found
  have he : BitVec.ofNat width bn + BitVec.ofNat width size + pc =
      pc - BitVec.ofNat width ((3 + j) * ffiOffset) := hvalue.symm.trans hentry
  have hs : (BitVec.ofNat width bn + BitVec.ofNat width size +
      BitVec.ofNat width ((3 + j) * ffiOffset)) + pc = pc := by
    calc
      _ = (BitVec.ofNat width bn + BitVec.ofNat width size + pc) +
          BitVec.ofNat width ((3 + j) * ffiOffset) := by ac_rfl
      _ = (pc - BitVec.ofNat width ((3 + j) * ffiOffset)) +
          BitVec.ofNat width ((3 + j) * ffiOffset) := congrArg (fun x => x + _) he
      _ = pc := BitVec.sub_add_cancel _ _
  have hz := congrArg (fun x => x - pc) hs
  simp only [BitVec.add_sub_cancel, BitVec.sub_self] at hz
  have hzNat := congrArg BitVec.toNat hz
  have hlt : bn + size + (3 + j) * ffiOffset < 2 ^ width := by
    simp only [ffiOffset] at hbound ⊢
    omega
  rw [← BitVec.ofNat_add, ← BitVec.ofNat_add, BitVec.toNat_ofNat] at hzNat
  simp only [BitVec.toNat_zero, Nat.mod_eq_of_lt hlt] at hzNat
  simp only [ffiOffset] at hzNat
  omega

private theorem goodCodeFiltered {width : Nat} [NeZero width] {G : Type}
    (config : AsmConfigExact width) (labels : Spt (Spt G)) (code : LabProgHOL width) :
    goodCode config labels code → goodCode config labels (LabFilter.filterSkip code) := by
  rintro ⟨hend, hsec, hdistinct, hlabels, hdisjoint, htargets, hpre⟩
  refine ⟨Flapjack.Compiler.Backend.LabFilter.Proofs.secEndsWithLabelFilterSkip code hend,
    ?_, ?_, ?_, ?_, ?_, LabToTarget.allEncOkPreFilterSkip code config hpre⟩
  · intro sectionData hmem line hline
    rw [LabFilter.filterSkipMap] at hmem
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hmem
    exact hsec original horiginal line (List.mem_filter.mp hline).1
  · simpa only [LabToTarget.FilterSkip.mapSectionNumFilterSkip] using hdistinct
  · intro sectionData hmem
    have hlabelsMem : LabProps.LabelSets.extractLabels sectionData.lines ∈
        (LabFilter.filterSkip code).map (fun sectionData => LabProps.LabelSets.extractLabels sectionData.lines) :=
      List.mem_map.mpr ⟨sectionData, hmem, rfl⟩
    rw [LabToTarget.FilterSkip.filterSkipExtractLabels] at hlabelsMem
    obtain ⟨original, horiginal, heq⟩ := List.mem_map.mp hlabelsMem
    rw [← heq]
    exact hlabels original horiginal
  · simpa only [LabToTarget.FilterSkip.mapSectionNumFilterSkip] using hdisjoint
  · simpa only [LabToTarget.FilterSkip.getLabelsFilterSkip,
      LabToTarget.FilterSkip.getCodeLabelsFilterSkip] using htargets

/-- Projection lemmas stated on variables so their `rfl` checks are cheap for the kernel. -/
private theorem nativeMakeInit_be {width : Nat} [NeZero width] {C F : Type}
    (conf : AsmConfigExact width) (k : Nat) (t : StackSemStateFiniteExact width C F)
    (code : Spt (Nat × WordLangProgHOL (BitVec width)))
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    (WordToStack.Native.Initialization.makeInit conf k t code coracle).be = t.be := rfl

private theorem nativeMakeInit_ffi {width : Nat} [NeZero width] {C F : Type}
    (conf : AsmConfigExact width) (k : Nat) (t : StackSemStateFiniteExact width C F)
    (code : Spt (Nat × WordLangProgHOL (BitVec width)))
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    (WordToStack.Native.Initialization.makeInit conf k t code coracle).ffi = t.ffi := rfl

private theorem frontendWordState_be {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (panCode : List (DeclHOL width))
    (code : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (stack : StackSemStateFiniteExact width C F) (cfg : C) :
    (InitializedPipelineTransfer.frontendWordState ac panCode code bitmaps stack cfg).be = stack.be := rfl

private theorem frontendWordState_ffi {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (panCode : List (DeclHOL width))
    (code : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (stack : StackSemStateFiniteExact width C F) (cfg : C) :
    (InitializedPipelineTransfer.frontendWordState ac panCode code bitmaps stack cfg).ffi = stack.ffi := rfl

/-- Clock monotonicity of Lab non-timeout, stated on variables so the kernel never has to
unfold `LabSem.evaluate` on a concrete state. -/
private theorem lab_not_timeOut_mono {width : Nat} [NeZero width] {C F : Type}
    (s : LabSem.State width C F) (k k' : Nat) (hle : k ≤ k')
    (h : (LabSem.evaluate { s with clock := k }).1 ≠ .timeOut) :
    (LabSem.evaluate { s with clock := k' }).1 ≠ .timeOut := by
  obtain ⟨res, r, hev⟩ : ∃ res r, LabSem.evaluate { s with clock := k } = (res, r) := ⟨_, _, rfl⟩
  have hres : res ≠ .timeOut := by rw [hev] at h; exact h
  have hadd := LabProps.evaluateAddClock { s with clock := k } res r (k' - k) ⟨hev, hres⟩
  have hclk : k + (k' - k) = k' := Nat.add_sub_of_le hle
  simp only [hclk] at hadd
  rw [hadd]; exact hres

theorem general_compile_initialization
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (ms : RiscV.L3.riscv_state)
    (code : LabProgHOL 64) (c cNext : LabToTarget.Config)
    (bytes : List (BitVec 8)) (cbspace i : Nat) (t : AsmState 64)
    (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → LabToTarget.Config × LabProgHOL 64)
    (hmc : mcConfOk mc)
    (horacle : noShareMemInst code → compilerOracleOk coracle cNext.labels bytes.length mc.target.config mc.ffiNames)
    (hgood : goodCode mc.target.config (.ln : Spt (Spt Nat)) code)
    (hlabs : c.labels = .ln) (hpos : c.pos = 0)
    (hcompile : LabToTarget.compile mc.target.config c code = some (bytes, cNext))
    (hffi : cNext.ffiNames = some mc.ffiNames)
    (hinit : goodInitState mc ms bytes cbspace t m dm sdm)
    (hentries : cNext.shmemExtra.map (fun rec => (mc.target.getPc ms).toNat + rec.entryPc) =
      (mc.ffiEntryPcs.map BitVec.toNat).drop i)
    (hmmio : mc.mmioInfo = List.zip ((List.range cNext.shmemExtra.length).map (fun index => index + i))
      (cNext.shmemExtra.map (fun rec => (rec.nbytes,
        HolAddr.addr rec.addrReg (BitVec.ofNat 64 rec.addrOff), rec.reg,
        BitVec.ofNat 64 rec.exitPc + mc.target.getPc ms))))
    (hsafe : noInstallOrNoShareMem code mc.ffiNames)
    (hboundary : mmioPcsMinIndex mc.ffiNames = some i)
    (hbound : cbspace + bytes.length + ffiOffset * (i + 3) < 2 ^ 64)
    (hprovided : ∀ ffis, c.ffiNames = some ffis → ∀ name ∈ ffis, ∃ s, name = .extCall s) :
    ∃ code2 labs newNames info shiftedInfo,
      bytes = progToBytes code2 ∧
      InitializedTransfer.Initialization mc ms code code2 labs c.initClock i cbspace
        t m dm sdm coracle newNames info shiftedInfo := by
  have hcomp := hcompile
  simp only [LabToTarget.compile, LabToTarget.compileLab, hlabs, hpos] at hcomp
  generalize hchoice : (match c.ffiNames with
    | some names => (names, Misc.listSubset (findFfiNames (LabFilter.filterSkip code)) names)
    | none => (findFfiNames (LabFilter.filterSkip code), true)) = choice at hcomp
  rcases choice with ⟨ffis, ffisOk⟩
  let finish (names : List HolFfiName) (ok : Bool) :=
    if ok then
      match removeLabels c.initClock mc.target.config 0 .ln names (LabFilter.filterSkip code) with
      | none => none
      | some (output, labs) =>
          let (newNames, info) := getShmemInfo output 0 [] []
          some (progToBytes output, { c with
            labels := labs
            pos := (progToBytes output).length + 0
            secPosLen := getSymbols 0 output
            ffiNames := some (names ++ newNames)
            shmemExtra := info })
    else none
  have hfinished : finish ffis ffisOk = some (bytes, cNext) := by
    cases hcfg : c.ffiNames with
    | none =>
      simp only [hcfg, Prod.mk.injEq] at hchoice
      rw [← hchoice.1, ← hchoice.2]
      cases hr : removeLabels c.initClock mc.target.config 0 .ln
          (findFfiNames (LabFilter.filterSkip code)) (LabFilter.filterSkip code) <;>
        simpa only [finish, hcfg, hr] using hcomp
    | some supplied =>
      simp only [hcfg, Prod.mk.injEq] at hchoice
      rw [← hchoice.1, ← hchoice.2]
      cases hr : removeLabels c.initClock mc.target.config 0 .ln supplied (LabFilter.filterSkip code) <;>
        simpa only [finish, hcfg, hr] using hcomp
  dsimp only [finish] at hfinished
  by_cases hok : ffisOk = true
  · simp only [hok, ↓reduceIte] at hfinished
    cases hremove : removeLabels c.initClock mc.target.config 0 .ln ffis (LabFilter.filterSkip code) with
    | none => simp only [hremove, reduceCtorEq] at hfinished
    | some output =>
      rcases output with ⟨code2, labs⟩
      simp only [hremove] at hfinished
      cases hinfo : getShmemInfo code2 0 [] [] with
      | mk newNames info =>
        simp only [hinfo, Option.some.injEq, Prod.mk.injEq] at hfinished
        obtain ⟨hbytes, hcNext⟩ := hfinished
        subst hbytes; subst hcNext
        have hnames : mc.ffiNames = ffis ++ newNames := by
          simpa only [Option.some.injEq] using hffi.symm
        have hffis : ∀ name ∈ ffis, ∃ s, name = HolFfiName.extCall s := by
          cases hcfg : c.ffiNames with
          | none =>
            simp only [hcfg, Prod.mk.injEq] at hchoice
            rw [← hchoice.1]
            exact findFfiNamesEvery (LabFilter.filterSkip code) _ rfl
          | some supplied =>
            simp only [hcfg, Prod.mk.injEq] at hchoice
            rw [← hchoice.1]
            exact hprovided supplied hcfg
        have hnew : ∀ name ∈ newNames, ∀ s, name ≠ HolFfiName.extCall s := by
          obtain ⟨_, heq, hshared⟩ := getShmemInfo_mappedNames code2 0 [] [] newNames info hinfo
          simp only [List.nil_append] at heq
          rw [heq]
          intro name hmem s
          obtain ⟨op, rfl⟩ := hshared name hmem
          intro heq; cases heq
        have hb : mmioPcsMinIndex mc.ffiNames = some ffis.length := by
          rw [hnames]
          exact mmioPcsMinIndex_append newNames ffis ⟨hnew, hffis⟩
        have hilen : i = ffis.length := Option.some.inj (hboundary.symm.trans hb)
        have htake : mc.ffiNames.take i = ffis := by
          rw [hnames, hilen, List.take_append_length]
        have hdrop : mc.ffiNames.drop i = newNames := by
          rw [hnames, hilen, List.drop_append_length]
        have hsubset : Misc.listSubset (findFfiNames (LabFilter.filterSkip code)) ffis = true := by
          cases hcfg : c.ffiNames with
          | none =>
            simp only [hcfg, Prod.mk.injEq] at hchoice
            rw [← hchoice.1]
            exact listSubsetRefl _
          | some supplied =>
            simp only [hcfg, Prod.mk.injEq] at hchoice
            rw [← hchoice.1]
            exact hchoice.2.trans hok
        let shiftedInfo' := info.map (fun rec => { rec with
          entryPc := (mc.target.getPc ms).toNat + rec.entryPc,
          exitPc := (mc.target.getPc ms).toNat + rec.exitPc })
        refine ⟨code2, labs, newNames, info, shiftedInfo', rfl,
          goodCodeFiltered _ _ _ hgood, hmc, ?_, ?_, ?_, hinit, hinfo, rfl, hdrop,
          hboundary, ?_, ?_, ?_, ?_⟩
        · intro hno
          obtain ⟨hall, hzero⟩ := horacle ((LabToTarget.FilterSkip.noShareMemFilterSkip code).mp hno)
          refine ⟨?_, hzero⟩
          intro k
          exact ⟨goodCodeFiltered _ _ _ (hall k).1,
            (LabToTarget.FilterSkip.noShareMemFilterSkip (coracle k).2).mpr (hall k).2⟩
        · rw [htake]
          simp only [Misc.listSubset, List.all_eq_true, decide_eq_true_eq] at hsubset ⊢
          intro name hmem
          exact hsubset name (List.mem_filter.mp hmem).1
        · simpa only [htake] using hremove
        · simpa only [shiftedInfo', List.map_map, Function.comp_def] using hentries
        · simpa only [shiftedInfo', List.length_map, List.map_map, Function.comp_def,
            BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm] using hmmio
        · exact LabToTarget.noInstallOrNoShareMemFilterSkip code mc.ffiNames hsafe
        · have hstart : startPcOk mc (mc.target.getPc ms) := by
            rw [← hinit.2.2.1]
            exact hinit.2.2.2.1
          exact bufferNotFfi mc _ _ cbspace i hstart hboundary hbound
  · simp only [hok, ↓reduceIte, reduceCtorEq] at hfinished

theorem stageTransfer_from_obligations
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
    UniformSourceClock.CoveredSourceUniformNotTimeOut K_pan →
    FiniteRebudget.UniformNotTimeOut ArtifactEnv.baselineSubmission K_target := by
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
  -- Bootstrap run to actual `post : riscv_state`
  obtain ⟨post, shift, _, post_rel⟩ := ConcreteBaseline.ExactBootstrap.full_evaluator_exact
    (sourceFfi input) (ConcreteBaseline.baselineInitialState input)
    (ConcreteBaseline.baselineInitialState_related input)
  -- Unpack ConcreteOracleCompilationWitness
  let c := oracleCompilerConfig w.oracles
  have hmc_fe : isRiscvMachineConfig FastEnv.baselineMachineConfig :=
    R12_Stage4BoundArgon.fastEnv_baseline_machine_isRiscv
  have hconfig_fe : FastEnv.baselineMachineConfig.target.config = riscvConfig := by
    rw [hmc_fe.1]; rfl
  have hcomp := w.compiled
  rw [← hconfig_fe, compileProgMaxAsmExecutable_eq] at hcomp
  obtain ⟨col, wprog, wconf, fs, p, ltconf, hwtw, hwts, hlab, hc_eq, _⟩ :=
    compileProgMax_some c FastEnv.baselineMachineConfig sourceDeclarations
      InitECandidate.nativeCode InitECandidate.bitmaps w.c (some w.depth) hcomp
  rw [hconfig_fe] at hwtw hwts
  have hltconf : ltconf = baselineLabConfig := by
    have := congrArg Backend.Config.labConf hc_eq
    dsimp only at this
    exact this.symm.trans w.hlab
  -- Transport `panInstalled` to `post`!
  have hpan_inst_core := R12_Stage4BoundArgon.fastEnv_baseline_pan_installed_core
  have hpan_inst_post : panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      (some FastEnv.baselineNames) (11, 13) FastEnv.baselineMachineConfig
      FastEnv.baselineMmio post (wlabWlocExact ∘ sourceMemory) ordinaryDomain sharedDomain := by
    rw [R12_Stage4BoundArgon.baselineNames_eq, R12_Stage4BoundArgon.baselineMachineConfig_eq,
        R12_Stage4BoundArgon.baselineMmio_eq]
    exact ArtifactEnv.panInstalled_transport
      (ArtifactEnv.baseline_endpoint_agreement post post_rel)
      ArtifactEnv.baseline_pan_installed_core
  obtain ⟨t, m, bitmapPtr, bitmapDm, sharedDm, hm_ord, hgi_post, hshared,
    ha2, ha4, hab, horder, hspace, hdisjoint, hm0, hm1, hm2, hm3, hm4, hbitmap, hffiN, hmmio⟩ :=
    hpan_inst_post
  have hnames :
      StackNames.findNameSpt c.stackConf.regNames 2 = 11 ∧
      StackNames.findNameSpt c.stackConf.regNames 3 = 12 ∧
      StackNames.findNameSpt c.stackConf.regNames 4 = 13 := by
    simp only [c, oracleCompilerConfig, pancakeRiscVBackendConfig_eq, riscvBackendConfig_eq_executable]
    decide_cbv
  let dm_unaligned : BitVec 64 → Bool := fun a =>
    decide (t.regs (StackNames.findNameSpt c.stackConf.regNames 2) ≤ a ∧
      a < t.regs (StackNames.findNameSpt c.stackConf.regNames 4)) || bitmapDm a
  have hgi_post_c : goodInitState FastEnv.baselineMachineConfig post
      InitECandidate.nativeCode 3788 t m dm_unaligned sharedDm := by
    simpa only [dm_unaligned, hnames.1, hnames.2.2] using hgi_post
  -- Also `goodInitState` at `FastEnv.baselineInstalledState` (for `ConcreteFrontendState.fields` if needed, or directly on `post`!)
  -- Wait: let's check what state `lab_post` is!
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
    (oracleMachineInitOk w.oracles _ hmc_fe) (by decide)
    hwtw hwts sourceDistinctFunctions
    (by simpa only [c, hnames.1, hnames.2.2] using
      And.intro ha2 ⟨ha4, hab, horder, hspace, hdisjoint, hm0, hm1, hm2, hm3, hm4, hbitmap⟩)
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
  -- Now let's check `FrontendRelation` for `stack_post`!
  -- In `SelfContainedPipelineBridge.lean` lines 396-502, `FrontendRelation` is proved for ANY `ms` (`post`) with `OracleBaselineInstallation`!
  have hinst_post := LeanBridge.oracle_baseline_installation_transport input w.c post post_rel
    (LeanBridge.oracle_baseline_installation input w.c
      (by rw [w.hlab]; exact ArtifactEnv.baseline_pan_installed input))
  obtain ⟨_, _, hsplit, hbase, hlen, htop, hglobals, hdomain,
    haligned, hadj2, hadj4, hleft, hright, hmax_heap, hendian, _, _⟩ := hinst_post
  -- Wait: `hbase`, `hsplit`, etc. are on `ArtifactEnv.baselineMachineConfig` and `post`; rewrite with `baselineMachineConfig_eq.symm`!
  rw [← R12_Stage4BoundArgon.baselineMachineConfig_eq] at hsplit hbase hlen hdomain haligned hadj2 hadj4 hleft hright hmax_heap hendian
  -- Derive `FrontendRelation` on `frontendWordState riscvConfig sourceDeclarations wprog InitECandidate.bitmaps stack_post ltconf`!
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
    simp [lab_post, pipelineLabInitState, LabToTarget.makeInit, hr2, hbase]
  have h3_reg : lab_post.regs lab_post.ptr2Reg = .word (FastEnv.baselineMachineConfig.target.getReg post FastEnv.baselineMachineConfig.ptr2Reg) := by
    simp [lab_post, pipelineLabInitState, LabToTarget.makeInit, hr3]
  have h4_reg : lab_post.regs lab_post.len2Reg = .word (FastEnv.baselineMachineConfig.target.getReg post FastEnv.baselineMachineConfig.len2Reg) := by
    simp [lab_post, pipelineLabInitState, LabToTarget.makeInit, hr4]
  obtain ⟨_, _, -, -, -, g2, -, -, a2, -⟩ := panToTargetInitCodeRun hA_post
  rw [h2_reg] at g2; cases g2
  have hbase_mod : (sourceInitialState input).baseAddr.toNat % (64 / 8) = 0 :=
    (holByteAligned_iff_mod (Or.inr rfl) _).1 a2
  have h_kreg : FastEnv.baselineMachineConfig.target.config.regCount -
      (5 + FastEnv.baselineMachineConfig.target.config.avoidRegs.length) =
      riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length) := by rw [hconfig_fe]
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
    intro a ha
    exact hm_ord a ha
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
    refine ⟨?_, ?_, rfl, sourceGlobalsSize.symm, sourceDistinctParams,
      ?_, ?_, ?_, ?_, hcurr, hheapLW, ?_, sourceDistinctFunctions,
      R12_Stage1To2BoundArgon.sourceInitialState_topAddr_byteAligned input,
      SourceHeapFacts.source_globals_allocatable input,
      rfl, rfl, rfl, rfl, sourceExceptionBound, rfl,
      sptLookup_sptInsert_zero (WordLocW.loc 1 0) Spt.ln, Or.inr rfl, hnonfail⟩
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
    · -- Generic `rfl` lemmas keep the kernel from comparing the two word states field by
      -- field (which would evaluate the compiled `code` field against the fvar `wprog`).
      have h1 : stack_post.be = lab_post.be := (nativeMakeInit_be _ _ _ _ _).symm.trans hbe_w
      exact (frontendWordState_be riscvConfig sourceDeclarations wprog bitmaps stack_post ltconf).trans
        (h1.trans hendian)
    · have h1 : stack_post.ffi = lab_post.ffi := (nativeMakeInit_ffi _ _ _ _ _).symm.trans hffi_w
      exact (frontendWordState_ffi riscvConfig sourceDeclarations wprog bitmaps stack_post ltconf).trans h1
    · rw [htop]
      have e1 : (2 : BitVec 64) * heapLen_bv =
          (wordSemBytesInWord : BitVec 64) * BitVec.ofNat 64 LeanBridge.baselineHeapLen := by
        dsimp only [heapLen_bv]
        rw [← hsnd, BitVec.ofNat_mul, hbw_eq, BitVec.mul_comm _ (wordSemBytesInWord : BitVec 64),
            ← BitVec.mul_assoc, BitVec.mul_comm (2 : BitVec 64), BitVec.mul_assoc]
        rfl
      have e2 : BitVec.ofNat 64 (globalsWords * 64 / 8) =
          panBytesInWord 64 * BitVec.ofNat 64 globalsWords := by decide
      rw [e1, e2]
  -- Now run Stages 1-4 directly on `post` (`lab_post` / `stack_post`)!
  have hsafe_mem_post : RuntimeLabels.MemorySafe storeConstsStubLocation lab_post.memDomain lab_post.memory := by
    apply RuntimeLabels.memorySafe_of_goodInitState storeConstsStubLocation _ _ _ _ t m _ _ _ hgi_post_c
    intro a ha; change (_ && holByteAligned a) = true at ha; simp only [Bool.and_eq_true] at ha; exact ha.2
  have hchecked := ConcreteWordCheckInput.original_of_all h_word_all
  have hlab_nt := CertifiedPipelineTransfer.pan_to_certified_lab_not_timeOut
    riscvConfig c.wordToWordConf sourceDeclarations col wprog InitECandidate.bitmaps
    wconf fs p c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
    lab_post (fun k => decide (k ∈ FastEnv.baselineMachineConfig.calleeSavedRegs)) 0 ltconf
    stack_post aux_post (Or.inr rfl) (by decide) (by decide) hwtw hwts hinit_post
    ConcreteWordCostAnnotations.summaries WordSourceOracle.terminal InitE.sourceOracle 20000
    R12_Stage2To3BoundArgon.noLabels R12_Stage2To3BoundArgon.indirect hchecked
    R12_Stage2To3BoundArgon.entryBound rfl WordSourceOracle.terminalOracle
    (sourceInitialState input) (ofString "main") globalsWords heapLen_bv
    hfront_post stCtxt s_decls hst hdecls K_pan res s_post hrun hne_pan hnt_pan hA_post hsafe_mem_post
  have hstack_comp := CertifiedPipelineTransfer.pan_to_certified_stack_complete
    riscvConfig c.wordToWordConf sourceDeclarations col wprog InitECandidate.bitmaps
    wconf fs p c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
    lab_post (fun k => decide (k ∈ FastEnv.baselineMachineConfig.calleeSavedRegs)) 0 ltconf
    stack_post aux_post (Or.inr rfl) (by decide) (by decide) hwtw hwts hinit_post
    ConcreteWordCostAnnotations.summaries WordSourceOracle.terminal InitE.sourceOracle 20000
    R12_Stage2To3BoundArgon.noLabels R12_Stage2To3BoundArgon.indirect hchecked
    R12_Stage2To3BoundArgon.entryBound rfl WordSourceOracle.terminalOracle
    (sourceInitialState input) (ofString "main") globalsWords heapLen_bv
    hfront_post stCtxt s_decls hst hdecls K_pan res s_post hrun hne_pan hnt_pan
  have ready := EntryClassTransfer.stack_complete_ready _ hstack_comp
  have nonfail_lab := CompletedNonfailure.lab_nonfail_of_ready c.stackConf c.dataConf
    (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
    InitECandidate.bitmaps p lab_post
    (fun k => decide (k ∈ FastEnv.baselineMachineConfig.calleeSavedRegs)) 0
    (fun _ => (ltconf, [], [])) stack_post (some aux_post) hinit_post hA_post
    (CertifiedPipelineTransfer.certifiedStackClock sourceDeclarations (ofString "main") K_pan)
    ready.1 ready.2
  -- Monotonicity of Lab clock up to concrete k_lab_max
  let M := Stage4.codeStepBudget (FullMakeInitSemantics.code2 c.stackConf c.dataConf
    (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset p)
  have hM_bound : M ≤ 7313 := h_m7313 col wprog wconf fs p hwtw hwts
  have h_static : FrontendStaticBudget.staticFrontBudget sourceDeclarations (ofString "main") ≤ 448 := by
    rw [R12_Stage1To2BoundArgon.staticFrontBudget_sourceDeclarations_eq]; exact h_front
  have h_stack_bound := (R12_Stage1To2BoundArgon.wordClock_and_certifiedStackClock_bound h_static K_pan).2
  let k_lab_old := 2 * (M + 1) * (CertifiedPipelineTransfer.certifiedStackClock sourceDeclarations (ofString "main") K_pan) + (3 * M + 2)
  let k_lab_max := 2 * (7313 + 1) * (2 * (449 * K_pan + 452)) + (3 * 7313 + 2)
  have hk_lab_le : k_lab_old ≤ k_lab_max := by
    change 2 * (M + 1) * R12_Stage1To2BoundArgon.certifiedStackClock sourceDeclarations
      (ofString "main") K_pan + (3 * M + 2) ≤ k_lab_max
    have h1 : 2 * (M + 1) ≤ 2 * (7313 + 1) := by omega
    have h2 := Nat.mul_le_mul h1 h_stack_bound
    omega
  have hlab_nt_max : (LabSem.evaluate { lab_post with clock := k_lab_max }).1 ≠ .timeOut :=
    lab_not_timeOut_mono lab_post k_lab_old k_lab_max hk_lab_le hlab_nt
  have hlab_ne_max : (LabSem.evaluate { lab_post with clock := k_lab_max }).1 ≠ .error :=
    lab_run_not_error_of_nonfail lab_post nonfail_lab k_lab_max
  -- Strip alignDm / alignSdm from `lab_post`!
  let code_lab := StackToLab.compile c.stackConf c.dataConf
    (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset p
  let coracle : Nat → LabToTarget.Config × LabProgHOL 64 := fun _ =>
    (ltconf, StackToLab.compileNoStubs c.stackConf.regNames c.stackConf.jump riscvConfig.addrOffset
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) [])
  let lab_unaligned := InitializedTransfer.initialLab FastEnv.baselineMachineConfig post
    (sourceFfi input) code_lab InitECandidate.nativeCode 3788 t m dm_unaligned sharedDm coracle
  have hlab_eq_align : lab_post = alignDm (alignSdm lab_unaligned) := by
    unfold lab_post pipelineLabInitState lab_unaligned InitializedTransfer.initialLab
      alignDm alignSdm LabToTarget.makeInit dm_unaligned code_lab coracle
    rw [hconfig_fe]
  have hlab_unaligned_nt : (LabSem.evaluate { lab_unaligned with clock := k_lab_max }).1 ≠ .timeOut := by
    rw [← Stage4.lab_align_result (Or.inr rfl) lab_unaligned k_lab_max, ← hlab_eq_align]
    exact hlab_nt_max
  have hlab_unaligned_ne : (LabSem.evaluate { lab_unaligned with clock := k_lab_max }).1 ≠ .error := by
    rw [← Stage4.lab_align_result (Or.inr rfl) lab_unaligned k_lab_max, ← hlab_eq_align]
    exact hlab_ne_max
  -- Now prove `InitializedTransfer.Initialization` at `post`!
  have hcfg_ok : BackendProof.backendConfigOk FastEnv.baselineMachineConfig.target.config c := by
    rw [hconfig_fe]; exact oracleBackendConfigOk w.oracles
  have hisa_fe : FastEnv.baselineMachineConfig.target.config.isa ≠ .ag32 := by
    rw [hconfig_fe]; decide
  have hgood_code : goodCode FastEnv.baselineMachineConfig.target.config (.ln : Spt (Spt Nat)) code_lab := by
    have := panToTargetGoodCodeFromSource (β := Nat) c FastEnv.baselineMachineConfig
      sourceDeclarations col wprog InitECandidate.bitmaps wconf fs p
      hcfg_ok (Or.inr rfl) hisa_fe (by rw [hconfig_fe]; exact hwtw)
      (by rw [hconfig_fe]; exact hwts) sourceDistinctFunctions sourceGoodCode
    simpa only [code_lab, hconfig_fe] using this
  have hffi_lt : ltconf.ffiNames = some FastEnv.baselineMachineConfig.ffiNames := by
    rw [hltconf, ArtifactEnv.baseline_installation_metadata.1,
      ← R12_Stage4BoundArgon.baselineNames_eq, hffiN]
  have horacle_ok := panToTargetCompilerOracleOk FastEnv.baselineMachineConfig.target.config
    c.labConf ltconf code_lab InitECandidate.nativeCode FastEnv.baselineMachineConfig.ffiNames
    c.stackConf.regNames c.stackConf.jump riscvConfig.addrOffset
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3))
    (by simpa only [code_lab, hconfig_fe] using hlab) hcfg_ok.2.2.2.2.1 hffi_lt
  have hnis := panToTargetNoInstallOrNoShareMem sourceDeclarations riscvConfig riscvConfig.isa _
    c.wordToWordConf col wprog InitECandidate.bitmaps wconf fs p c.stackConf c.dataConf
    (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
    FastEnv.baselineMachineConfig.ffiNames ⟨sourceDistinctFunctions, by decide, rfl, hwtw, hwts⟩
  have hno_install : LabProps.noInstall code_lab :=
    from_pan_to_lab_no_install sourceDeclarations riscvConfig riscvConfig.isa _
      c.wordToWordConf col wprog InitECandidate.bitmaps wconf fs p c.stackConf c.dataConf
      (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
      ⟨sourceDistinctFunctions, by decide, rfl, hwtw, hwts⟩
  have hffiOk : ∀ ffis, c.labConf.ffiNames = some ffis → ∀ name ∈ ffis, ∃ s, name = .extCall s := by
    intro ffis hsome
    have hnone : c.labConf.ffiNames = none := by
      simp only [c, oracleCompilerConfig, pancakeRiscVBackendConfig_eq,
        riscvBackendConfig_eq_executable, Flapjack.Compiler.pancakeBackendConf]
      rfl
    rw [hnone] at hsome; cases hsome
  obtain ⟨ffis_tmp, hffis_tmp, i_idx, hi_idx⟩ := BackendProof.compileLabIMPMmioPcsMinIndex
    FastEnv.baselineMachineConfig.target.config c.labConf (LabFilter.filterSkip code_lab)
    InitECandidate.nativeCode ltconf
    ⟨hlab, by
      cases hfn : c.labConf.ffiNames with
      | none => trivial
      | some l => exact hffiOk l hfn⟩
  rw [hffi_lt] at hffis_tmp; injection hffis_tmp with hffis_eq; subst hffis_eq
  have hmmio_lt : ∀ i, mmioPcsMinIndex FastEnv.baselineMachineConfig.ffiNames = some i →
      ltconf.shmemExtra.map (fun rec => (FastEnv.baselineMachineConfig.target.getPc post).toNat + rec.entryPc) =
        (FastEnv.baselineMachineConfig.ffiEntryPcs.map BitVec.toNat).drop i ∧
      FastEnv.baselineMachineConfig.mmioInfo =
        List.zip ((List.range ltconf.shmemExtra.length).map (fun index => index + i))
          (ltconf.shmemExtra.map (fun rec => (rec.nbytes,
            HolAddr.addr rec.addrReg (BitVec.ofNat 64 rec.addrOff), rec.reg,
            BitVec.ofNat 64 rec.exitPc + FastEnv.baselineMachineConfig.target.getPc post))) ∧
      3788 + InitECandidate.nativeCode.length + ffiOffset * (i + 3) < 2 ^ 64 := by
    rw [hltconf, ArtifactEnv.baseline_mmio_projection, ← R12_Stage4BoundArgon.baselineMmio_eq]
    exact hmmio
  obtain ⟨hentries_i, hmmio_i, hbound_i⟩ := hmmio_lt i_idx hi_idx
  obtain ⟨code2, labs, newNames, info, shiftedInfo, hbytes_eq, hInit⟩ :=
    general_compile_initialization FastEnv.baselineMachineConfig post code_lab
      c.labConf ltconf InitECandidate.nativeCode 3788 i_idx t m dm_unaligned sharedDm coracle
      hmc_ok_fe (fun _ => horacle_ok) hgood_code hcfg_ok.2.2.2.2.2.1 hcfg_ok.2.2.2.2.1
      (by simpa only [code_lab, hconfig_fe] using hlab) hffi_lt hgi_post_c
      hentries_i hmmio_i hnis hi_idx hbound_i hffiOk
  -- Now apply `Stage5Transfer.stage5_lab_to_target_affine_not_timeOut`!
  have hmc_cb_fe : ConcreteBaseline.baselineMachineConfig = FastEnv.baselineMachineConfig :=
    LeanBridge.config_eq.trans R12_Stage4BoundArgon.baselineMachineConfig_eq.symm
  rw [hmc_cb_fe] at shift
  dsimp only [lab_unaligned] at hlab_unaligned_ne hlab_unaligned_nt
  rw [hbytes_eq] at hlab_unaligned_ne hlab_unaligned_nt
  have htarget_nt := Wave8Stage.stage5_lab_to_target_affine_not_timeOut
    FastEnv.baselineMachineConfig hmc_fe.1 (ConcreteBaseline.baselineInitialState input) post
    (sourceFfi input) code_lab code2 labs c.labConf.initClock i_idx 3788
    t m dm_unaligned sharedDm coracle newNames info shiftedInfo hInit hno_install k_lab_max
    hlab_unaligned_ne hlab_unaligned_nt bootstrapSteps shift
  -- Rewrite budget `bootstrapSteps + 9 * (k_lab_max + 1)` to `K_target` and machine/initial state!
  have hK_eq : bootstrapSteps + 9 * (k_lab_max + 1) = K_target := by
    rw [InitE.bootstrapSteps_eq]
    dsimp only [k_lab_max]
    unfold K_target
    generalize K_pan = k
    omega
  rw [hK_eq] at htarget_nt
  rw [ArtifactEnv.baselineSubmission_machineConfig, ArtifactEnv.baselineSubmission_initialState,
      ← R12_Stage4BoundArgon.baselineMachineConfig_eq, ← LeanBridge.initial_eq]
  exact htarget_nt

end InitECandidate.Solver.Wave8Stage.Stage5Bridge
