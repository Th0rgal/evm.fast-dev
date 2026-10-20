import InitECandidate.Proofs.BoundedStackToLab
import InitECandidate.Solver.BoundedCertificate

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.StackToLabClockBound` — Linear Clock Relation Across `StackRemove`, `StackNames`, `StackToLab`, and `LabFilter`

This module proves:
1. The exact clock relation across `StackRemove` (`initCode` `0`-tick preservation via
   `stack_remove_init_code_clock_preserve` and `+1` entry call shift via
   `stack_remove_init_clocked_shift`) and `StackNames` (`0`-tick renaming via
   `stack_names_clocked_agree`).
2. The linear clock relation across `StackToLab` (`k_lab = (k_stack - 1) + ck_lab + 2`)
   and clock monotonicity `LabProps.evaluateAddClock` across `LabFilter` for `k_filt ≤ k_lab`.
3. The theorem `backend_halt_of_linear_lab_clock_budget` composing
   `pan_to_target_backend_halt_agree_of_not_timeOut` with any linear clock bound
   `K_lab ≤ C_lab * k_word + D_lab`.
-/

namespace InitECandidate.Solver

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver.BoundedCertificate
open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs.InitClock
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.Proofs.PanToTarget

/-- 1. Clock relation across `StackRemove` (`initCode` `0`-tick via
`stack_remove_init_code_clock_preserve` and `+1` entry shift) and `StackNames` (`0`-tick
renaming): `initCode` is structurally `clockNeutralHOL` and consumes `0` clock ticks, and calling
procedure `0` on `StackNames.renameState c f s2` at clock `k_body + 1` produces the exact same
result and FFI state as calling `start` on `t` at clock `k_body`. -/
theorem stack_remove_to_names_init_linear_clock {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap pointer start : Nat)
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C))
    (f : Spt Nat)
    (s2 t : StackSemStateFiniteExact width C F) (k_body : Nat)
    (hentry : sptLookup 0 s2.code =
      some (.seq (StackRemove.initCode generateGc maxHeap pointer)
        (.call none (.inl start) none)))
    (hrun : StackSemEvaluate.evaluate (StackRemove.initCode generateGc maxHeap pointer, s2) =
      (none, t))
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (ha : ¬s2.useAlloc) (hs : ¬s2.useStore) (hk : ¬s2.useStack)
    (hc : s2.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f)) :
    clockNeutralHOL (StackRemove.initCode (width := width) generateGc maxHeap pointer) ∧
    StackSemEvaluate.evaluate
      (StackRemove.initCode generateGc maxHeap pointer, { s2 with clock := k_body }) =
      (none, { t with clock := k_body }) ∧
    (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { StackNames.renameState c f s2 with clock := k_body + 1 })).1 =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k_body })).1 ∧
    (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { StackNames.renameState c f s2 with clock := k_body + 1 })).2.ffi =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k_body })).2.ffi := by
  obtain ⟨hneutral, hinit_clk⟩ :=
    stack_remove_init_code_clock_preserve generateGc maxHeap pointer s2 t none k_body hrun
  have hshift :=
    stack_remove_init_clocked_shift generateGc maxHeap pointer start s2 t k_body hentry hrun
  have hnames :=
    stack_names_clocked_agree hf ha hs hk hc 0 (k_body + 1)
  exact ⟨hneutral, hinit_clk, hnames.1.trans hshift.1, hnames.2.trans hshift.2⟩

/-- 2. Linear clock relation across `StackToLab`: any `StackSem` entry call at clock `k_stack`
finishing with `FlattenSemantics.stackEntryClass res = .CompleteResult outcome` satisfies
`1 ≤ k_stack` and produces a halting `LabSem.evaluate` run at clock
`k_lab = (k_stack - 1) + ck_lab + 2` with the exact same outcome and I/O events. -/
theorem stack_to_lab_linear_clock_halt {width : Nat} [NeZero width] {C F : Type}
    {start : Nat}
    {s1 : StackSemStateFiniteExact width C F}
    {s2 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (halt : FlattenCallCorrect.haltAssum C F s1.code)
    (rel : StateRel.stateRel s1 s2)
    (hpc : LabSem.locToPc start 0 s2.code = some s2.pc)
    (k_stack : Nat) (outcome : HolOutcome) (ev : List HolIoEvent)
    (hrun : FlattenSemantics.stackRuns start s1 k_stack = (.CompleteResult outcome, ev)) :
    1 ≤ k_stack ∧
    ∃ ck_lab,
      (LabSem.evaluate { s2 with clock := (k_stack - 1) + ck_lab + 2 }).1 = .halt outcome ∧
      (LabSem.evaluate { s2 with clock := (k_stack - 1) + ck_lab + 2 }).2.ffi.ioEvents = ev := by
  have hk_pos : 1 ≤ k_stack := by
    cases k_stack with
    | zero =>
      exfalso
      simp only [FlattenSemantics.stackRuns] at hrun
      rcases hev : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
          { s1 with clock := 0 }) with ⟨res, post⟩
      rw [hev] at hrun
      simp only [Prod.map, Prod.mk.injEq] at hrun
      have hclass := hrun.1
      rw [StackSemEvaluate.evaluate_call] at hev
      simp only at hev
      cases hfind : StackSemControl.findCode (.inl start) s1.regs s1.code with
      | none =>
        rw [hfind] at hev
        injection hev with hres _
        subst hres
        simp [FlattenSemantics.stackEntryClass] at hclass
      | some prog =>
        simp only [hfind, if_true] at hev
        injection hev with hres _
        subst hres
        simp [FlattenSemantics.stackEntryClass] at hclass
    | succ n => exact Nat.succ_le_succ (Nat.zero_le n)
  obtain ⟨ck_lab, hhalt0, hev0⟩ :=
    stack_to_lab_clocked_halt halt rel hpc k_stack outcome ev hrun
  refine ⟨hk_pos, ck_lab, ?_⟩
  rcases hlab0 : LabSem.evaluate { s2 with clock := k_stack + ck_lab - 1 } with ⟨res0, next0⟩
  rw [hlab0] at hhalt0 hev0
  simp only at hhalt0 hev0
  subst hhalt0
  have hadd := LabProps.evaluateAddClock { s2 with clock := k_stack + ck_lab - 1 }
    (.halt outcome) next0 2 ⟨hlab0, by rintro ⟨⟩⟩
  simp only at hadd
  have hclk_eq : k_stack + ck_lab - 1 + 2 = (k_stack - 1) + ck_lab + 2 := by omega
  rw [hclk_eq] at hadd
  rw [hadd]
  exact ⟨rfl, hev0⟩

/-- 3. Monotonicity of `LabSem.evaluate` for `k_filt ≤ k_lab` via `LabProps.evaluateAddClock`,
composed with `LabFilter` (`LabFilter.Proofs.stateRel`) and domain alignment (`alignDm` + `alignSdm`):
if the aligned unfiltered `LabSem` state halts at clock `k_filt` and `k_filt ≤ k_lab`, then
the filtered `LabSem` state `s` halts at `k_filt` AND at `k_lab` with the exact same outcome
and FFI state. -/
theorem lab_filter_clock_mono_and_align_halt {width : Nat} [NeZero width] {C F : Type}
    (hw : goodDimindex width)
    (s t : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hr : LabFilter.Proofs.stateRel s t)
    (k_filt k_lab : Nat)
    (hle : k_filt ≤ k_lab)
    (outcome : HolOutcome)
    (next : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hhalt : LabSem.evaluate { alignDm (alignSdm t) with clock := k_filt } = (.halt outcome, next)) :
    (LabSem.evaluate { s with clock := k_filt }).1 = .halt outcome ∧
    (LabSem.evaluate { s with clock := k_filt }).2.ffi = next.ffi ∧
    (LabSem.evaluate { s with clock := k_lab }).1 = .halt outcome ∧
    (LabSem.evaluate { s with clock := k_lab }).2.ffi = next.ffi := by
  obtain ⟨hhalt_filt, hffi_filt⟩ :=
    lab_filter_align_clocked_halt hw s t hr k_filt outcome next hhalt
  rcases hev_filt : LabSem.evaluate { s with clock := k_filt } with ⟨res_filt, next_filt⟩
  rw [hev_filt] at hhalt_filt hffi_filt
  simp only at hhalt_filt hffi_filt
  subst hhalt_filt
  have hadd := LabProps.evaluateAddClock { s with clock := k_filt }
    (.halt outcome) next_filt (k_lab - k_filt) ⟨hev_filt, by rintro ⟨⟩⟩
  simp only [Nat.add_sub_of_le hle] at hadd
  rw [hadd]
  exact ⟨rfl, hffi_filt, rfl, hffi_filt⟩

/-- 4. `backend_halt_of_linear_lab_clock_budget`: composes
`pan_to_target_backend_halt_agree_of_not_timeOut` with any linear clock bound
`K_lab ≤ C_lab * k_word + D_lab`, proving that if `evaluateTargetHOL mc ffi K_lab ms` does not
time out at `K_lab`, then both `evaluateTargetHOL mc ffi K_lab ms` and
`evaluateTargetHOL mc ffi (C_lab * k_word + D_lab) ms` halt with `.halt outcome` and identical
FFI I/O events `s_word_post.ffi.ioEvents`. -/
theorem backend_halt_of_linear_lab_clock_budget {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapPtr : BitVec width) (bitmapsDm sdm : BitVec width → Bool) (ms : S)
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltconf : LabToTarget.Config)
    (panCode : List (Pancake.PanLang.DeclHOL width)) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) (bitmaps : List (BitVec width))
    (wconf : WordToStack.Native.Config) (fs : List Nat) (p : List (Nat × StackLang.HolProg width))
    (dataSp : Nat) (stackMax : Option Nat)
    (hcfg : BackendProof.backendConfigOk mc.target.config c) (hmc : LabToTarget.mcConfOk mc)
    (hinit : BackendProof.mcInitOk mc.target.config c mc) (hisa : mc.target.config.isa ≠ .ag32)
    (hwtw : WordToWord.compile c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog))
    (hwts : WordToStack.Native.compileNative mc.target.config false wprog =
      (bitmaps, wconf, fs, p))
    (hlab : LabToTarget.compile mc.target.config c.labConf
      (StackToLab.compile c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
        (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
        mc.target.config.addrOffset p) = some (bytes, ltconf))
    (hmax : stackMax = WordDepth.maxDepth wconf.stackFrameSize
      (WordDepth.fullCallGraph BvlToBvi.initGlobalsLocation (sptFromAList wprog)))
    (hnodup : ((Pancake.PanLang.functionsHOL panCode).map Prod.fst).Nodup)
    (hffiOk : match c.labConf.ffiNames with
      | none => True
      | some l => ∀ x ∈ l, ∃ s, x = HolFfiName.extCall s)
    (hgi : goodInitState mc ms bytes cbspace t m
      (fun w => decide (t.regs (StackNames.findNameSpt c.stackConf.regNames 2) ≤ w ∧
        w < t.regs (StackNames.findNameSpt c.stackConf.regNames 4)) || bitmapsDm w) sdm)
    (hffiN : ltconf.ffiNames = some mc.ffiNames)
    (hmmio : ∀ i, mmioPcsMinIndex mc.ffiNames = some i →
      ltconf.shmemExtra.map (fun rec => (mc.target.getPc ms).toNat + rec.entryPc) =
          (mc.ffiEntryPcs.map BitVec.toNat).drop i ∧
        mc.mmioInfo = List.zip ((List.range ltconf.shmemExtra.length).map (fun index => index + i))
          (ltconf.shmemExtra.map fun rec => (rec.nbytes,
            HolAddr.addr rec.addrReg (BitVec.ofNat width rec.addrOff),
            rec.reg, BitVec.ofNat width rec.exitPc + mc.target.getPc ms)) ∧
        cbspace + bytes.length + LabToTarget.ffiOffset * (i + 3) < 2 ^ width)
    (hsource : pancakeGoodCodeHOL panCode = true)
    (hpi :
      let regNames := c.stackConf.regNames
      let r1 := StackNames.findNameSpt regNames 2
      let r2 := StackNames.findNameSpt regNames 4
      let biw := StackRemove.bytesInWord width
      let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
      holByteAligned (t.regs r1) = true ∧ holByteAligned (t.regs r2) = true ∧
      holByteAligned bitmapPtr = true ∧ t.regs r1 ≤ t.regs r2 ∧
      1024 * biw ≤ t.regs r2 - t.regs r1 ∧
      (∀ w, ¬ (heapStackDm w = true ∧ bitmapsDm w = true)) ∧
      m (t.regs r1) = .word bitmapPtr ∧
      m (t.regs r1 + biw) = .word (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) ∧
      m (t.regs r1 + 2 * biw) = .word (bitmapPtr + biw * BitVec.ofNat width dataSp +
        biw * BitVec.ofNat width bitmaps.length) ∧
      m (t.regs r1 + 3 * biw) = .word (mc.target.getPc ms + BitVec.ofNat width bytes.length) ∧
      m (t.regs r1 + 4 * biw) =
        .word (mc.target.getPc ms + BitVec.ofNat width cbspace + BitVec.ofNat width bytes.length) ∧
      SetSep.star (Misc.wordList bitmapPtr (bitmaps.map WordLocW.word))
        (Misc.wordListExists (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) dataSp)
        (SetSep.fun2Set (m, fun a => holByteAligned a = true ∧ bitmapsDm a = true)))
    (hlo : mc.target.getReg ms mc.lenReg +
      StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc ≤
        mc.target.getReg ms mc.ptr2Reg)
    (hhi : mc.target.getReg ms mc.ptr2Reg ≤ mc.target.getReg ms mc.len2Reg -
      StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc)
    (hheap : (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg).toNat ≤
      (StackRemove.bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1))
    (hheapLt : (StackRemove.bytesInWord width).toNat *
      (2 * DataToWord.maxHeapLimit width c.dataConf - 1) < 2 ^ width)
    (halign : holAligned (wordShiftAmount width + 1)
      (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg) = true)
    (hresLimit : optionLt stackMax
      (some (BackendProof.readLimits mc.target.config c mc ms).1) = true)
    (hsem : WordSemStateFiniteExact.semantics
      (let regNames := c.stackConf.regNames
       let r1 := StackNames.findNameSpt regNames 2
       let r2 := StackNames.findNameSpt regNames 4
       let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
       let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
       let maxHeap := 2 * DataToWord.maxHeapLimit width c.dataConf - 1
       let labst := LabToTarget.makeInit (C := LabToTarget.Config) mc ffi t m
         (fun a => (heapStackDm a || bitmapsDm a) && holByteAligned a)
         (fun a => sdm a && holByteAligned a) ms
         (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p)
         (LabToTarget.compile mc.target.config)
         (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
         (fun _ => (ltconf, StackToLab.compileNoStubs regNames c.stackConf.jump
           mc.target.config.addrOffset sp []))
       let sst := (FullMakeInit.fullMakeInit c.stackConf c.dataConf maxHeap sp
         mc.target.config.addrOffset bitmaps p labst (fun k => decide (k ∈ mc.calleeSavedRegs))
         dataSp (fun _ => (ltconf, [], []))).1
       WordToStack.Native.Initialization.makeInit mc.target.config
         (mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)) sst
         (sptFromAList wprog)
         (fun _ => ((bitmaps.length, ltconf), ([] : List (Nat × Nat × WordLangProgHOL (BitVec width))))))
      BvlToBvi.initGlobalsLocation ≠ .fail)
    (k_word : Nat) (res : Option (WordSemResult width)) (outcome : HolOutcome)
    (s_word_post : WordSemStateFiniteExact width (Nat × LabToTarget.Config) σ)
    (hres_ok : match res with
      | some (.finalFfi e) => outcome = .ffiOutcome e
      | some (.result (WordLocW.loc 1 0) _) => outcome = .success
      | some .notEnoughSpace => outcome = .resourceLimitHit
      | _ => False)
    (hrun_w0 : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { (let regNames := c.stackConf.regNames
         let r1 := StackNames.findNameSpt regNames 2
         let r2 := StackNames.findNameSpt regNames 4
         let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
         let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
         let maxHeap := 2 * DataToWord.maxHeapLimit width c.dataConf - 1
         let labst := LabToTarget.makeInit (C := LabToTarget.Config) mc ffi t m
           (fun a => (heapStackDm a || bitmapsDm a) && holByteAligned a)
           (fun a => sdm a && holByteAligned a) ms
           (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p)
           (LabToTarget.compile mc.target.config)
           (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
           (fun _ => (ltconf, StackToLab.compileNoStubs regNames c.stackConf.jump
             mc.target.config.addrOffset sp []))
         let sst := (FullMakeInit.fullMakeInit c.stackConf c.dataConf maxHeap sp
           mc.target.config.addrOffset bitmaps p labst (fun k => decide (k ∈ mc.calleeSavedRegs))
           dataSp (fun _ => (ltconf, [], []))).1
         let wst := WordToStack.Native.Initialization.makeInit mc.target.config
           (mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)) sst
           (sptFromAList wprog)
           (fun _ => ((bitmaps.length, ltconf), ([] : List (Nat × Nat × WordLangProgHOL (BitVec width)))))
         { wst with code := sptFromAList (panToWordCompileProgHOL mc.target.config.isa panCode) })
        with clock := k_word } = (res, s_word_post))
    (K_lab C_lab D_lab : Nat)
    (hlinear : K_lab ≤ C_lab * k_word + D_lab)
    (hnt : (evaluateTargetHOL mc ffi K_lab ms).1 ≠ .timeOut) :
    (evaluateTargetHOL mc ffi K_lab ms).1 = .halt outcome ∧
    (evaluateTargetHOL mc ffi K_lab ms).2.2.ioEvents = s_word_post.ffi.ioEvents ∧
    (evaluateTargetHOL mc ffi (C_lab * k_word + D_lab) ms).1 = .halt outcome ∧
    (evaluateTargetHOL mc ffi (C_lab * k_word + D_lab) ms).2.2.ioEvents =
      s_word_post.ffi.ioEvents := by
  obtain ⟨hhalt, hio⟩ := pan_to_target_backend_halt_agree_of_not_timeOut
    c mc ffi t m bitmapPtr bitmapsDm sdm ms bytes cbspace ltconf panCode col wprog bitmaps wconf
    fs p dataSp stackMax hcfg hmc hinit hisa hwtw hwts hlab hmax hnodup hffiOk hgi hffiN hmmio
    hsource hpi hlo hhi hheap hheapLt halign hresLimit hsem k_word res outcome s_word_post
    hres_ok hrun_w0 K_lab hnt
  rcases hrunK : evaluateTargetHOL mc ffi K_lab ms with ⟨resK, msK, ffiK⟩
  rw [hrunK] at hhalt hio
  simp only at hhalt hio
  subst hhalt
  have hadd := evaluateTargetAddClock mc ffi K_lab ms (C_lab * k_word + D_lab - K_lab)
    (.halt outcome) msK ffiK hrunK (by rintro ⟨⟩)
  rw [Nat.add_sub_of_le hlinear] at hadd
  rw [hadd]
  exact ⟨rfl, hio, rfl, hio⟩

#print axioms stack_remove_to_names_init_linear_clock
#print axioms stack_to_lab_linear_clock_halt
#print axioms lab_filter_clock_mono_and_align_halt
#print axioms backend_halt_of_linear_lab_clock_budget

end InitECandidate.Solver
