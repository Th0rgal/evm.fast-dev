import InitECandidate.Solver.UniformSourceClock
import InitECandidate.Solver.Wave8GuestInv.LeanBridge
import InitECandidate.Solver.Wave8Stage.R12_Stage1To2BoundArgon
import InitECandidate.Solver.Wave8Stage.R12_Stage4BoundArgon
import InitECandidate.Solver.Wave8Stage.Stage4LabGlue

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

theorem successfulIndex {α : Type} [DecidableEq α] (values : List α)
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

theorem bufferNotFfi {width : Nat} [NeZero width] {S Q : Type}
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

theorem goodCodeFiltered {width : Nat} [NeZero width] {G : Type}
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
        let shiftedInfo := info.map (fun rec => { rec with
          entryPc := (mc.target.getPc ms).toNat + rec.entryPc,
          exitPc := (mc.target.getPc ms).toNat + rec.entryPc })
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

theorem riscvConfig_isa_ne_ag32 : riscvConfig.isa ≠ .ag32 := by
  rintro h; cases h

theorem riscvConfig_regs_bound :
    riscvConfig.avoidRegs.length + 13 ≤ riscvConfig.regCount := by
  decide

theorem mul64_div8_bv (n : Nat) :
    BitVec.ofNat 64 (n * 64 / 8) = panBytesInWord 64 * BitVec.ofNat 64 n := by
  have h : n * 64 / 8 = 8 * n := by omega
  rw [h, BitVec.ofNat_mul]; rfl

theorem unpack_compileProgMax
    (c : Backend.Config)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (hcfg : mc.target.config = riscvConfig)
    (panCode : List (DeclHOL 64))
    (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (c' : Backend.Config) (depth : Nat)
    (h : compileProgMaxAsmExecutable c riscvConfig panCode = (some (bytes, bitmaps, c'), some depth)) :
    ∃ col wprog wconf fs p ltconf,
      WordToWord.compile c.wordToWordConf riscvConfig
        (panToWordCompileProgHOL riscvConfig.isa panCode) = (col, wprog) ∧
      WordToStack.Native.compileNative riscvConfig false wprog = (bitmaps, wconf, fs, p) ∧
      LabToTarget.compile mc.target.config c.labConf
        (StackToLab.compile c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
          (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
          mc.target.config.addrOffset p) = some (bytes, ltconf) ∧
      c'.labConf = ltconf := by
  rw [← hcfg, compileProgMaxAsmExecutable_eq] at h
  obtain ⟨col, wprog, wconf, fs, p, ltconf, hwtw, hwts, hlab, hc_eq, _⟩ :=
    compileProgMax_some c mc panCode bytes bitmaps c' (some depth) h
  rw [hcfg] at hwtw hwts
  exact ⟨col, wprog, wconf, fs, p, ltconf, hwtw, hwts, hlab,
    congrArg Backend.Config.labConf hc_eq⟩

theorem pipelineLabInitState_eq_align {F : Type}
    (c : Backend.Config)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (hcfg : mc.target.config = riscvConfig)
    (ffi : HolFfiState F) (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapDm sharedDm : BitVec 64 → Bool) (ms : RiscV.L3.riscv_state)
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltconf : LabToTarget.Config)
    (p : List (Nat × HolProg 64)) :
    pipelineLabInitState c mc ffi t m bitmapDm sharedDm ms bytes cbspace ltconf p =
      alignDm (alignSdm (InitializedTransfer.initialLab mc ms ffi
        (StackToLab.compile c.stackConf c.dataConf
          (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
          (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset p)
        bytes cbspace t m
        (fun a => decide (t.regs (StackNames.findNameSpt c.stackConf.regNames 2) ≤ a ∧
          a < t.regs (StackNames.findNameSpt c.stackConf.regNames 4)) || bitmapDm a)
        sharedDm
        (fun _ => (ltconf, StackToLab.compileNoStubs c.stackConf.regNames c.stackConf.jump
          riscvConfig.addrOffset
          (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) [])))) := by
  unfold pipelineLabInitState InitializedTransfer.initialLab alignDm alignSdm LabToTarget.makeInit
  rw [hcfg]

theorem panInstalled_fe_of_ae
    (bytes : List (BitVec 8)) (cbspace : Nat) (bitmaps : List (BitVec 64)) (dataSp : Nat)
    (ms : RiscV.L3.riscv_state) (mem : BitVec 64 → WordLocW 64)
    (ordDm shDm : BitVec 64 → Prop)
    (h : panInstalled bytes cbspace bitmaps dataSp
      (some ArtifactEnv.baselineNames) (11, 13) ArtifactEnv.baselineMachineConfig
      ArtifactEnv.baselineMmio ms mem ordDm shDm) :
    panInstalled bytes cbspace bitmaps dataSp
      (some FastEnv.baselineNames) (11, 13) FastEnv.baselineMachineConfig
      FastEnv.baselineMmio ms mem ordDm shDm := by
  rw [R12_Stage4BoundArgon.baselineNames_eq, R12_Stage4BoundArgon.baselineMachineConfig_eq,
      R12_Stage4BoundArgon.baselineMmio_eq]
  exact h

theorem pipelineLabInitState_regs_lenReg {F : Type}
    (c : Backend.Config)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (ffi : HolFfiState F) (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapDm sharedDm : BitVec 64 → Bool) (ms : RiscV.L3.riscv_state)
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltconf : LabToTarget.Config)
    (p : List (Nat × HolProg 64)) :
    (pipelineLabInitState c mc ffi t m bitmapDm sharedDm ms bytes cbspace ltconf p).regs
      (pipelineLabInitState c mc ffi t m bitmapDm sharedDm ms bytes cbspace ltconf p).lenReg =
      .word (t.regs mc.lenReg) := rfl

theorem pipelineLabInitState_regs_ptr2Reg {F : Type}
    (c : Backend.Config)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (ffi : HolFfiState F) (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapDm sharedDm : BitVec 64 → Bool) (ms : RiscV.L3.riscv_state)
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltconf : LabToTarget.Config)
    (p : List (Nat × HolProg 64)) :
    (pipelineLabInitState c mc ffi t m bitmapDm sharedDm ms bytes cbspace ltconf p).regs
      (pipelineLabInitState c mc ffi t m bitmapDm sharedDm ms bytes cbspace ltconf p).ptr2Reg =
      .word (t.regs mc.ptr2Reg) := rfl

theorem pipelineLabInitState_regs_len2Reg {F : Type}
    (c : Backend.Config)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (ffi : HolFfiState F) (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapDm sharedDm : BitVec 64 → Bool) (ms : RiscV.L3.riscv_state)
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltconf : LabToTarget.Config)
    (p : List (Nat × HolProg 64)) :
    (pipelineLabInitState c mc ffi t m bitmapDm sharedDm ms bytes cbspace ltconf p).regs
      (pipelineLabInitState c mc ffi t m bitmapDm sharedDm ms bytes cbspace ltconf p).len2Reg =
      .word (t.regs mc.len2Reg) := rfl

end InitECandidate.Solver.Wave8Stage.Stage5BridgeArgon
