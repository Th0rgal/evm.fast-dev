import InitECandidate.Solver.Wave8Stage.QuantitativeStep
import InitECandidate.Solver.Wave8Stage.QuantitativeAsm
import InitECandidate.Solver.Wave8Stage.QuantitativeControl
import InitECandidate.Solver.Wave8Stage.QuantitativeCbw
import InitECandidate.Solver.Wave8Stage.QuantitativeShareMem
import InitECandidate.Solver.Wave8Stage.QuantitativeCallFfi
import InitECandidate.Solver.Wave8Stage.CanonicalRuntime
import InitECandidate.Solver.Wave8Stage.UnfilteredTransfer
import InitECandidate.Solver.Wave8Stage.InitializedTransfer
import InitECandidate.Solver.Wave8Stage.Stage5Transfer
import Flapjack.Compiler.Backend.Semantics.TargetProps.EvaluateAddClock

/-! Slope-7 specialization of Stage 5 Lab-to-Target transfer (`6 * clock + 6`
extra target steps, yielding total post-bootstrap fuel `7 * (k_lab + 1)`).
Every Lab instruction consumes at most `l ≤ 6` target steps (or `6` in
`CallFFI` returning with `l ≤ 6` jump plus `1` FFI step, consuming `1` Lab
clock tick so net extra fuel is `l ≤ 6`). -/
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.Slope7Transfer
open Flapjack Flapjack.Compiler.Encoders Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.AsmSem Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.RiscV.L3
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Stage.Quantitative
open InitECandidate.Solver.Wave8Stage.InitializedTransfer

/-- Slope-7 compiler correctness: `k ≤ 6 * s1.clock + 6` extra target steps. -/
def CompileCorrectFor7 {width : Nat} [NeZero width] (S Q : Type) {F : Type}
    (s1 : LabSem.State width Config F) : Prop :=
  ∀ (res : MachineResult) (mc : MachineConfig width S Q) (s2 : LabSem.State width Config F)
    (code2 : LabProgHOL width) (labs : Spt (Spt Nat)) (t1 : AsmState width) (ms1 : S)
    (p : BitVec width),
    oracleTie mc ms1 s1 ∧ evaluate s1 = (res, s2) ∧ res ≠ .error ∧
      encoderCorrect mc.target ∧ stateRel (mc, code2, labs, p) s1 t1 ms1 ∧
      CodeBound mc.target code2 →
    ∃ k, k ≤ 6 * s1.clock + 6 ∧ ∃ ms2,
      evaluateTargetHOL mc s1.ffi (s1.clock + k) ms1 = (res, ms2, s2.ffi)

theorem compileCorrect7_step {width : Nat} [NeZero width] {S Q F : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 s1' s2 : LabSem.State width Config F} {t1' : AsmState width}
    {ms1 ms2 : S} {res : MachineResult} {l : Nat}
    (hbound : CodeBound mc.target code2) (hlBound : l ≤ 6)
    (ht : oracleTie mc ms1 s1) (hec : encoderCorrect mc.target) (hclock : s1.clock ≠ 0)
    (hl : ∀ k, evaluateTargetHOL mc s1.ffi (k + l) ms1 =
        evaluateTargetHOL (shiftInterfer l mc) s1.ffi k ms2 ∧
      findNextInterference mc s1.ffi (k + l) ms1 =
        findNextInterference (shiftInterfer l mc) s1.ffi k ms2)
    (hl0 : l ≠ 0)
    (hs' : s1'.clock = s1.clock - 1 ∧ s1'.ffi = s1.ffi ∧ s1'.ioRegs = s1.ioRegs ∧
      s1'.ioFpRegs = s1.ioFpRegs ∧ s1'.ccRegs = s1.ccRegs ∧ s1'.ccFpRegs = s1.ccFpRegs)
    (hrel' : stateRel (shiftInterfer l mc, code2, labs, p) s1' t1' ms2)
    (hev : evaluate s1' = (res, s2)) (hres : res ≠ .error)
    (ih : CompileCorrectFor7 S Q s1') :
    ∃ k, k ≤ 6 * s1.clock + 6 ∧ ∃ ms3,
      evaluateTargetHOL mc s1.ffi (s1.clock + k) ms1 = (res, ms3, s2.ffi) := by
  obtain ⟨hc, hffi, hio, hiofp, hcc, hccfp⟩ := hs'
  have ht' : oracleTie (shiftInterfer l mc) ms2 s1' :=
    oracleTie_step mc ms1 ms2 s1 s1' l ⟨ht, fun k => (hl k).2, hio, hiofp, hcc, hccfp, hffi⟩
  obtain ⟨k', hkBound, ms3, hk⟩ := ih res (shiftInterfer l mc) s2 code2 labs t1' ms2 p
    ⟨ht', hev, hres, hec, hrel', hbound⟩
  refine ⟨k' + l - 1, by omega, ms3, ?_⟩
  rw [show s1.clock + (k' + l - 1) = (s1'.clock + k') + l by omega, (hl _).1, ← hffi]
  exact hk

theorem compileCorrect7_error {width : Nat} [NeZero width] {S Q F : Type}
    (s1 : LabSem.State width Config F) (h : evaluate s1 = (.error, s1)) :
    CompileCorrectFor7 S Q s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨-, hev, hres, -, -, -⟩
  rw [h] at hev
  exact absurd (Prod.mk.inj hev).1.symm hres

theorem compileCorrect7_timeOut {width : Nat} [NeZero width] {S Q F : Type}
    (s1 : LabSem.State width Config F) (hc : s1.clock = 0) :
    CompileCorrectFor7 S Q s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨-, hev, -, -, -, -⟩
  rw [evaluate, if_pos hc] at hev
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
  exact ⟨0, by omega, ms1, by rw [hc]; rfl⟩

theorem compileCorrect7_asmInst {width : Nat} [NeZero width] {S Q F : Type}
    (s1 : LabSem.State width Config F) (i : HolInst width) (bytes : List (BitVec 8)) (n : Nat)
    (hclock : s1.clock ≠ 0) (hfetch : asmFetch s1 = some (.asm (.asmi (.inst i)) bytes n))
    (ih : ¬ (asmInst i s1).failed → CompileCorrectFor7 S Q (incPc (decClock (asmInst i s1)))) :
    CompileCorrectFor7 S Q s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨ht, hev, hres, hec, hrel, hbound⟩
  rw [evaluate] at hev
  simp only [hclock, ↓reduceIte, hfetch] at hev
  by_cases hf : (asmInst i s1).failed = true
  · simp only [hf, ↓reduceIte, Prod.mk.injEq] at hev; exact absurd hev.1.symm hres
  · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hev
    obtain ⟨bytes', len', hok, hmem, hpos, hdis⟩ :=
      fetchedAsmLine hrel hfetch (by intro op re a h; cases h)
    simp only [lineOk, cbwToAsmHOL] at hok
    obtain ⟨htf, hout, _⟩ := instLemma i s1 mc code2 labs p t1 ms1 bytes' ms1
      ⟨hf, hrel, hpos⟩
    obtain ⟨l, hlBound, ms2, hl⟩ := stepNopOfLine s1.ffi hrel hec hbound (.inst i) bytes' hmem hok.1 hpos hok.2.2 hdis
      (by simpa [asmUpd, AsmSem.updPc] using htf)
      (fun a ha => by simpa [asmUpd, AsmSem.updPc] using hout a ha) (by intro x h; cases h)
    have hrel1 := (instLemma i s1 mc code2 labs p t1 ms1 bytes' ms2 ⟨hf, hrel, hpos⟩).2.2
      (hl 0).2.2.1
    have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l hrel1
    obtain ⟨_, _, hcl, hffi, hio, hiofp, hcc, hccfp, -⟩ := asmInstConsts i s1
    exact compileCorrect7_step (s1' := incPc (decClock (asmInst i s1))) hbound hlBound ht hec hclock
      (fun k => ⟨(hl k).1, (hl k).2.1⟩) (hl 0).2.2.2
      ⟨by simp [incPc, decClock, hcl], hffi, hio, hiofp, hcc, hccfp⟩ hrel' hev hres (ih hf)

theorem compileCorrect7_jumpReg {width : Nat} [NeZero width] {S Q F : Type}
    (s1 : LabSem.State width Config F) (r : Nat) (bytes : List (BitVec 8)) (n : Nat)
    (hclock : s1.clock ≠ 0) (hfetch : asmFetch s1 = some (.asm (.asmi (.jumpReg r)) bytes n))
    (ih : ∀ n1 n2 pc, s1.regs r = .loc n1 n2 → locToPc n1 n2 s1.code = some pc →
      CompileCorrectFor7 S Q (updPc pc (decClock s1))) :
    CompileCorrectFor7 S Q s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨ht, hev, hres, hec, hrel, hbound⟩
  rw [evaluate] at hev
  simp only [hclock, ↓reduceIte, hfetch] at hev
  cases hr : s1.regs r with
  | word _ => simp only [hr, Prod.mk.injEq] at hev; exact absurd hev.1.symm hres
  | loc n1 n2 =>
    simp only [hr] at hev
    cases hpc : locToPc n1 n2 s1.code with
    | none => simp only [hpc, Prod.mk.injEq] at hev; exact absurd hev.1.symm hres
    | some pc =>
      simp only [hpc] at hev
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
        c28, c29, c30, c31, -, -, -, -, -, -, -, ht1f, -, -, -, -, -, c45, -⟩ := id hrel
      have hreg : t1.regs r = p + BitVec.ofNat width (posVal pc 0 code2) := by
        have := c30 r
        rw [hr] at this
        simp only [wordLocVal, c28 n1 n2 pc hpc, Option.some.injEq] at this
        exact this.symm
      obtain ⟨bytes', len', hok, hmem, hpos, hdis⟩ :=
        fetchedAsmLine hrel hfetch (by intro op re a h; cases h)
      simp only [lineOk, cbwToAsmHOL] at hok
      have hal := Quantitative.stateRel_aligned_target hrel hec pc
      obtain ⟨l, hlBound, ms2, hl⟩ := stepOfLine s1.ffi hrel hec hbound _ bytes' hmem hok.1 hpos hok.2.2 hdis
        (by simp [asmUpd, AsmSem.updPc, AsmSem.assertState, AsmSem.readReg, hreg, c45, hal, ht1f])
      have htrel := (hl 0).2.2.1
      simp only [asmUpd, AsmSem.updPc, AsmSem.assertState, AsmSem.readReg, hreg, c45, hal,
        Bool.not_true, Bool.false_or, ht1f] at htrel
      have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l
        (stateRel_frame hrel s1.regs s1.fpRegs s1.memory pc (s1.clock - 1) t1.regs t1.fpRegs
          t1.mem _ htrel c30 c29 (fun x hx => (c31 x hx).2.2) (fun _ _ => rfl) rfl)
      exact compileCorrect7_step (s1' := LabSem.updPc pc (decClock s1)) hbound hlBound ht hec hclock
        (fun k => ⟨(hl k).1, (hl k).2.1⟩) (hl 0).2.2.2
        ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ hrel' hev hres (ih n1 n2 pc hr hpc)

theorem compileCorrect7_jump {width : Nat} [NeZero width] {S Q F : Type}
    (s1 : LabSem.State width Config F) (jt : Lab) (w : BitVec width)
    (bytes : List (BitVec 8)) (n : Nat) (hclock : s1.clock ≠ 0)
    (hfetch : asmFetch s1 = some (.labAsm (.jump jt) w bytes n))
    (ih : ∀ pc, getPcValue jt s1 = some pc → CompileCorrectFor7 S Q (updPc pc (decClock s1))) :
    CompileCorrectFor7 S Q s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨ht, hev, hres, hec, hrel, hbound⟩
  rw [evaluate] at hev
  simp only [hclock, ↓reduceIte, hfetch] at hev
  cases hpc : getPcValue jt s1 with
  | none => simp only [hpc, Prod.mk.injEq] at hev; exact absurd hev.1.symm hres
  | some pc =>
    simp only [hpc] at hev
    obtain ⟨hfind, -⟩ := Quantitative.findPos_of_getPcValue hrel jt pc hpc
    obtain ⟨w', bytes', len', hok, hmem, hpos, hdis⟩ := fetchedLabAsmLine hrel hfetch
    have hv := lineOk_labelTarget _ _ _ _ _ _ _ _ (Or.inl ⟨jt, rfl⟩) hok
    simp only [getLabel, labInst, hfind] at hv
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, c29, c30, c31, -, -, -, -, -, -, -, ht1f, -, htpc, -⟩ := id hrel
    obtain ⟨l, hlBound, ms2, hl⟩ := stepOfLine s1.ffi hrel hec hbound _ bytes' hmem hv.1 hpos hv.2.2 hdis
      (by simp [asmUpd, jumpToOffset, AsmSem.updPc, ht1f])
    have htrel := (hl 0).2.2.1
    have hnewpc : t1.pc + (BitVec.ofNat width (posVal pc 0 code2) -
        BitVec.ofNat width (posVal s1.pc 0 code2)) = p + BitVec.ofNat width (posVal pc 0 code2) := by
      rw [htpc]; ring
    simp only [asmUpd, jumpToOffset, AsmSem.updPc, hnewpc] at htrel
    have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l
      (stateRel_frame hrel s1.regs s1.fpRegs s1.memory pc (s1.clock - 1) t1.regs t1.fpRegs
        t1.mem _ htrel c30 c29 (fun x hx => (c31 x hx).2.2) (fun _ _ => rfl) rfl)
    exact compileCorrect7_step (s1' := LabSem.updPc pc (decClock s1)) hbound hlBound ht hec hclock
      (fun k => ⟨(hl k).1, (hl k).2.1⟩) (hl 0).2.2.2
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ hrel' hev hres (ih pc hpc)

theorem compileCorrect7_jumpCmp {width : Nat} [NeZero width] {S Q F : Type}
    (s1 : LabSem.State width Config F) (cmp : HolCmp) (rr : Nat) (ri : HolRegImm width)
    (jt : Lab) (w : BitVec width) (bytes : List (BitVec 8)) (n : Nat) (hclock : s1.clock ≠ 0)
    (hfetch : asmFetch s1 = some (.labAsm (.jumpCmp cmp rr ri jt) w bytes n))
    (ihFalse : wordSemWordCmp cmp (s1.regs rr) (LabSem.regImm ri s1) = some false →
      CompileCorrectFor7 S Q (incPc (decClock s1)))
    (ihTrue : ∀ pc, wordSemWordCmp cmp (s1.regs rr) (LabSem.regImm ri s1) = some true →
      getPcValue jt s1 = some pc → CompileCorrectFor7 S Q (updPc pc (decClock s1))) :
    CompileCorrectFor7 S Q s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨ht, hev, hres, hec, hrel, hbound⟩
  rw [evaluate] at hev
  simp only [hclock, ↓reduceIte, hfetch] at hev
  obtain ⟨w', bytes', len', hok, hmem, hpos, hdis⟩ := fetchedLabAsmLine hrel hfetch
  have hv := lineOk_labelTarget _ _ _ _ _ _ _ _ (Or.inr (Or.inl ⟨cmp, rr, ri, jt, rfl⟩)) hok
  simp only [getLabel, labInst] at hv
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, c29, c30, c31, -, -, -, -, -, -, -, ht1f, -, htpc, -⟩ := id hrel
  cases hc : wordSemWordCmp cmp (s1.regs rr) (LabSem.regImm ri s1) with
  | none => simp only [hc, Prod.mk.injEq] at hev; exact absurd hev.1.symm hres
  | some b =>
    have htc := wordCmp_lemma mc code2 labs p s1 t1 ms1 cmp rr ri b ⟨hrel, hc⟩
    cases b with
    | false =>
      simp only [hc] at hev
      obtain ⟨l, hlBound, ms2, hl⟩ := stepNopOfLine s1.ffi hrel hec hbound _ bytes' hmem hv.1 hpos hv.2.2 hdis
        (by simp [asmUpd, ← htc, AsmSem.updPc, ht1f]) (fun _ _ => by simp [asmUpd, ← htc, AsmSem.updPc])
        (by intro x h; cases h)
      have htrel := (hl 0).2.2.1
      have hnewpc : t1.pc + BitVec.ofNat width bytes'.length =
          p + BitVec.ofNat width (posVal (s1.pc + 1) 0 code2) := by
        rw [htpc, hpos, BitVec.ofNat_add, BitVec.add_assoc]
      simp only [asmUpd, ← htc, Bool.false_eq_true, ↓reduceIte, AsmSem.updPc, hnewpc] at htrel
      have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l
        (stateRel_frame hrel s1.regs s1.fpRegs s1.memory (s1.pc + 1) (s1.clock - 1) t1.regs
          t1.fpRegs t1.mem _ htrel c30 c29 (fun x hx => (c31 x hx).2.2) (fun _ _ => rfl) rfl)
      exact compileCorrect7_step (s1' := incPc (decClock s1)) hbound hlBound ht hec hclock
        (fun k => ⟨(hl k).1, (hl k).2.1⟩) (hl 0).2.2.2
        ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ hrel' hev hres (ihFalse hc)
    | true =>
      simp only [hc] at hev
      cases hpc : getPcValue jt s1 with
      | none => simp only [hpc, Prod.mk.injEq] at hev; exact absurd hev.1.symm hres
      | some pc =>
        simp only [hpc] at hev
        obtain ⟨hfind, -⟩ := Quantitative.findPos_of_getPcValue hrel jt pc hpc
        simp only [hfind] at hv
        obtain ⟨l, hlBound, ms2, hl⟩ := stepOfLine s1.ffi hrel hec hbound _ bytes' hmem hv.1 hpos hv.2.2 hdis
          (by simp [asmUpd, ← htc, jumpToOffset, AsmSem.updPc, ht1f])
        have htrel := (hl 0).2.2.1
        have hnewpc : t1.pc + (BitVec.ofNat width (posVal pc 0 code2) -
            BitVec.ofNat width (posVal s1.pc 0 code2)) =
            p + BitVec.ofNat width (posVal pc 0 code2) := by
          rw [htpc]; ring
        simp only [asmUpd, ← htc, ↓reduceIte, jumpToOffset, AsmSem.updPc, hnewpc] at htrel
        have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l
          (stateRel_frame hrel s1.regs s1.fpRegs s1.memory pc (s1.clock - 1) t1.regs t1.fpRegs
            t1.mem _ htrel c30 c29 (fun x hx => (c31 x hx).2.2) (fun _ _ => rfl) rfl)
        exact compileCorrect7_step (s1' := LabSem.updPc pc (decClock s1)) hbound hlBound ht hec hclock
          (fun k => ⟨(hl k).1, (hl k).2.1⟩) (hl 0).2.2.2
          ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ hrel' hev hres (ihTrue pc hc hpc)

theorem compileCorrect7_call {width : Nat} [NeZero width] {S Q F : Type}
    (s1 : LabSem.State width Config F) (lab : Lab) (w : BitVec width)
    (bytes : List (BitVec 8)) (n : Nat) (_hclock : s1.clock ≠ 0)
    (hfetch : asmFetch s1 = some (.labAsm (.call lab) w bytes n)) :
    CompileCorrectFor7 S Q s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨-, -, -, -, hrel, -⟩
  obtain ⟨w', bytes', len', hok, -⟩ := fetchedLabAsmLine hrel hfetch
  simp [lineOk] at hok

theorem compileCorrect7_locValue {width : Nat} [NeZero width] {S Q F : Type}
    (s1 : LabSem.State width Config F) (reg : Nat) (lab : Lab) (w : BitVec width)
    (bytes : List (BitVec 8)) (n : Nat) (hclock : s1.clock ≠ 0)
    (hfetch : asmFetch s1 = some (.labAsm (.locValue reg lab) w bytes n))
    (ih : getPcValue lab s1 ≠ none →
      CompileCorrectFor7 S Q (incPc (decClock (updReg reg (labToLoc lab) s1)))) :
    CompileCorrectFor7 S Q s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨ht, hev, hres, hec, hrel, hbound⟩
  rw [evaluate] at hev
  simp only [hclock, ↓reduceIte, hfetch] at hev
  cases hpc : getPcValue lab s1 with
  | none => simp only [hpc, ↓reduceIte, Prod.mk.injEq] at hev; exact absurd hev.1.symm hres
  | some pc =>
    simp only [hpc, reduceCtorEq, ↓reduceIte] at hev
    rcases lab with ⟨l1, l2⟩
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      c28, c29, c30, c31, -, -, -, -, -, -, -, ht1f, -, htpc, -⟩ := id hrel
    have hlook := c28 l1 l2 pc hpc
    have hfind := labLookup_implies_findPos l1 l2 labs _ hlook
    obtain ⟨w', bytes', len', hok, hmem, hpos, hdis⟩ := fetchedLabAsmLine hrel hfetch
    have hv := lineOk_labelTarget _ _ _ _ _ _ _ _ (Or.inr (Or.inr ⟨reg, .lab l1 l2, rfl⟩)) hok
    simp only [getLabel, labInst, hfind] at hv
    obtain ⟨l, hlBound, ms2, hl⟩ := stepNopOfLine s1.ffi hrel hec hbound _ bytes' hmem hv.1 hpos hv.2.2 hdis
      (by simp [asmUpd, AsmSem.updPc, AsmSem.updReg, ht1f])
      (fun _ _ => by simp [asmUpd, AsmSem.updPc, AsmSem.updReg]) (by intro x h; cases h)
    have htrel := (hl 0).2.2.1
    have hnewpc : t1.pc + BitVec.ofNat width bytes'.length =
        p + BitVec.ofNat width (posVal (s1.pc + 1) 0 code2) := by
      rw [htpc, hpos, BitVec.ofNat_add, BitVec.add_assoc]
    have hval : t1.pc + (BitVec.ofNat width (posVal pc 0 code2) -
        BitVec.ofNat width (posVal s1.pc 0 code2)) = p + BitVec.ofNat width (posVal pc 0 code2) := by
      rw [htpc]; ring
    simp only [asmUpd, AsmSem.updPc, AsmSem.updReg, hnewpc, hval] at htrel
    have hregs : ∀ r, wordLocVal p labs
        ((fun key => if key = reg then labToLoc (.lab l1 l2) else s1.regs key) r) =
        some ((fun r' => if r' = reg then p + BitVec.ofNat width (posVal pc 0 code2)
          else t1.regs r') r) := by
      intro r
      by_cases hr : r = reg
      · simp [hr, labToLoc, wordLocVal, hlook]
      · simp only [hr, ↓reduceIte]; exact c30 r
    have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l
      (stateRel_frame hrel _ s1.fpRegs s1.memory (s1.pc + 1) (s1.clock - 1) _ t1.fpRegs
        t1.mem _ htrel hregs c29 (fun x hx => (c31 x hx).2.2) (fun _ _ => rfl) rfl)
    exact compileCorrect7_step (s1' := incPc (decClock (updReg reg (labToLoc (.lab l1 l2)) s1)))
      hbound hlBound ht hec hclock (fun k => ⟨(hl k).1, (hl k).2.1⟩) (hl 0).2.2.2
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ hrel' hev hres (ih (by simp [hpc]))

theorem compileCorrect7_halt {width : Nat} [NeZero width] {S Q F : Type}
    (s1 : LabSem.State width Config F) (w : BitVec width) (bytes : List (BitVec 8)) (n : Nat)
    (hclock : s1.clock ≠ 0) (hfetch : asmFetch s1 = some (.labAsm .halt w bytes n)) :
    CompileCorrectFor7 S Q s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨ht, hev, hres, hec, hrel, hbound⟩
  rw [evaluate] at hev
  simp only [hclock, ↓reduceIte, hfetch] at hev
  obtain ⟨-, -, -, c4, -, c6, c7, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c25, -,
    -, -, -, c30, -, -, -, -, -, -, -, -, ht1f, -, htpc, -⟩ := id hrel
  cases hv : s1.regs s1.ptrReg with
  | loc _ _ => simp only [hv, Prod.mk.injEq] at hev; exact absurd hev.1.symm hres
  | word v =>
    simp only [hv] at hev
    obtain ⟨rfl, hs2⟩ : res = .halt (if v = 0 then .success else .resourceLimitHit) ∧
        s2 = s1 := by
      split at hev <;> simp_all
    rw [hs2]
    obtain ⟨w', bytes', len', hok, hmem, hpos, hdis⟩ := fetchedLabAsmLine hrel hfetch
    simp only [lineOk] at hok
    obtain ⟨l, hlBound, ms2, hl⟩ := stepOfLine s1.ffi hrel hec hbound _ bytes' hmem hok.1 hpos hok.2.2 hdis
      (by simp [asmUpd, jumpToOffset, AsmSem.updPc, ht1f])
    obtain ⟨-, hgpc, -, hgreg, -⟩ := (hl 0).2.2.1
    have hhalt : mc.target.getPc ms2 = mc.haltPc := by
      rw [hgpc, ← c25]
      simp only [asmUpd, jumpToOffset, AsmSem.updPc, htpc, BitVec.ofNat_add]
      ring
    have hptr : mc.target.getReg ms2 mc.ptrReg = v := by
      have hok6 := c6
      simp only [asmRegOkExact, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hok6
      rw [hgreg _ (by rw [c7]; exact hok6), c7]
      simp only [asmUpd, jumpToOffset, AsmSem.updPc]
      exact wordLocVal_word_target (c30 _) hv
    refine ⟨l, by omega, ms2, ?_⟩
    rw [(hl s1.clock).1]
    obtain ⟨k, hk⟩ : ∃ k, s1.clock = k + 1 := ⟨s1.clock - 1, by omega⟩
    rw [hk, evaluateTargetHOL]
    have hnp : ¬ ((shiftInterfer l mc).progAddresses ((shiftInterfer l mc).target.getPc ms2) ∧
        (shiftInterfer l mc).target.getPc ms2 ∉ (shiftInterfer l mc).ffiEntryPcs) := by
      intro h; exact c4 (by simpa [shiftInterfer, hhalt] using h.1)
    simp only [hnp, ↓reduceIte]
    simp [shiftInterfer, hhalt, hptr]

theorem compileCorrect7_cbw {width : Nat} [NeZero width] {S Q F : Type}
    (s1 : LabSem.State width Config F) (r1 r2 : Nat)
    (bytes : List (BitVec 8)) (n : Nat)
    (hclock : s1.clock ≠ 0) (hfetch : asmFetch s1 = some (.asm (.cbw r1 r2) bytes n))
    (ih : ∀ w1 w2 newCb, s1.regs r1 = .word w1 → s1.regs r2 = .word w2 →
      wordSemBufferWrite s1.codeBuffer w1 (w2.setWidth 8) = some newCb →
      CompileCorrectFor7 S Q (incPc (decClock { s1 with codeBuffer := newCb }))) :
    CompileCorrectFor7 S Q s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨ht, hev, hres, hec, hrel, hbound⟩
  rw [evaluate] at hev
  simp only [hclock, ↓reduceIte, hfetch] at hev
  cases hr1 : s1.regs r1 with
  | loc _ _ => simp only [hr1] at hev; exact absurd (Prod.mk.inj hev).1.symm hres
  | word w1 =>
  cases hr2 : s1.regs r2 with
  | loc _ _ => simp only [hr1, hr2] at hev; exact absurd (Prod.mk.inj hev).1.symm hres
  | word w2 =>
  simp only [hr1, hr2] at hev
  cases hbw : wordSemBufferWrite s1.codeBuffer w1 (w2.setWidth 8) with
  | none => simp only [hbw] at hev; exact absurd (Prod.mk.inj hev).1.symm hres
  | some newCb =>
  simp only [hbw] at hev
  have hbw' := hbw
  simp only [wordSemBufferWrite] at hbw'
  split at hbw'
  case isFalse => cases hbw'
  case isTrue hcond =>
  cases hbw'
  obtain ⟨haddr, hsp⟩ := hcond
  have haddr' : w1 = s1.codeBuffer.position + BitVec.ofNat width s1.codeBuffer.buffer.length := by
    rw [← haddr]; simp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, c30, -, c32, -, c34, -, c36, -, -, ht1f, -, htpc, -, -, -, -, -, c47, -⟩ := id hrel
  have htr1 : t1.regs r1 = w1 := by
    have := c30 r1; rw [hr1] at this; simpa [wordLocVal] using this.symm
  have htr2 : t1.regs r2 = w2 := by
    have := c30 r2; rw [hr2] at this; simpa [wordLocVal] using this.symm
  have hw0 := c32 0 hsp
  simp only [Nat.add_zero] at hw0
  obtain ⟨bytes', len', hok, hmem, hpos, hdis⟩ :=
    fetchedAsmLine hrel hfetch (by intro op re a h; cases h)
  simp only [lineOk, cbwToAsmHOL] at hok
  have hA : AsmSem.addrHOL (.addr r1 0#width) t1 = w1 := by
    simp [AsmSem.addrHOL, AsmSem.readReg, htr1]
  have hdom : t1.memDomain w1 := haddr' ▸ hw0.1
  have hupd : AsmSem.instUpd (.mem .store8 r2 (.addr r1 0#width)) t1 =
      { t1 with mem := fun x => if x = w1 then w2.setWidth 8 else t1.mem x } := by
    simp only [AsmSem.instUpd, AsmSem.memOp, asm_memStore_eq, hA,
      holLOG2_one, holAligned_zero, Nat.sub_self, BitVec.add_zero, ite_self, rmwOk,
      hdom, decide_true, Bool.and_true, wmwMem, AsmSem.readReg, htr2]
    simp [AsmSem.assertState, ht1f]
  have hupd' : AsmSem.instUpd (.mem .store8 r2 (.addr r1 (0 : BitVec width))) t1 =
      { t1 with mem := fun x => if x = w1 then w2.setWidth 8 else t1.mem x } := hupd
  have hphysicalBound := posVal_bound (s1.pc + 1) 0 code2 _ labs _ 0 c47
  rw [hpos] at hphysicalBound
  have hb2 : bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes'
      (fun x => if x = w1 then w2.setWidth 8 else t1.mem x) t1.memDomain
      (fun a => s1.memDomain a = true) := by
    refine bytesInMem_update _ _ _ _ _ _ _ ⟨fun k hk => ?_, hmem⟩
    rw [haddr', c34, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact Quantitative.add_ofNat_ne p _ _ (by omega) (by omega) (by omega)
  obtain ⟨l, hlBound, ms2, hl⟩ := stepNopOfLineMem s1.ffi hrel hec hbound _ bytes' hmem hok.1 hpos hok.2.2 hdis
    (by simp [asmUpd, AsmSem.updPc, hupd, ht1f])
    (by
      simp only [asmUpd, AsmSem.updPc, hupd']
      rw [htpc]; exact bytesInMem_impliesMemory _ _ _ _ _ hb2)
    (by intro x h; cases h)
  have htrel := (hl 0).2.2.1
  simp only [asmUpd, AsmSem.updPc, hupd', haddr'] at htrel
  have hrel1 := Quantitative.stateRel_cbw hrel (w2.setWidth 8) hsp _ htrel
    (by rw [htpc, BitVec.add_assoc, ← BitVec.ofNat_add, hpos])
  have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l hrel1
  exact compileCorrect7_step (s1' := incPc (decClock { s1 with
      codeBuffer := ⟨s1.codeBuffer.position, s1.codeBuffer.buffer ++ [w2.setWidth 8],
        s1.codeBuffer.spaceLeft - 1⟩ })) hbound hlBound ht hec hclock
    (fun k => ⟨(hl k).1, (hl k).2.1⟩) (hl 0).2.2.2
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ hrel' hev hres (ih w1 w2 _ hr1 hr2 hbw)

theorem compileCorrect7_shareMem {width : Nat} [NeZero width] {S Q F : Type}
    (s1 : LabSem.State width Config F) (m : HolMemop) (r : Nat)
    (ad : HolAddr width) (bytes : List (BitVec 8)) (n : Nat)
    (hclock : s1.clock ≠ 0) (hfetch : asmFetch s1 = some (.asm (.shareMem m r ad) bytes n))
    (ih : ∀ ffi' bs s', shareMemOp m r ad s1 = some (.ret ffi' bs, s') →
      CompileCorrectFor7 S Q { s' with
        ioRegs := holShiftSeq 1 s'.ioRegs
        ioFpRegs := holShiftSeq 1 s'.ioFpRegs }) :
    CompileCorrectFor7 S Q s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨ht, hev, hres, hec, hrel, hbound⟩
  obtain ⟨c1, c2, c3, -, -, -, -, -, -, -, -, -, -, -, c15, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, c30, -, -, c33, -, -, -, -, -, -, -, c41, -, -, -, -, -, c47, -, c49, c50, c51, c52,
    -⟩ := id hrel
  obtain ⟨base, off⟩ := ad
  obtain ⟨bytes', hf2, henc, hbm, -, hpos, hok⟩ :=
    imp_bytesInMemory_shareMem mc labs _ s1 code2 p t1 m r (.addr base off) bytes n
      ⟨hfetch, c49, c47, c33⟩
  obtain ⟨i, hi, -⟩ := c15
  obtain ⟨index, hle, hfi, hinfo⟩ := c51.1 s1.pc m r (.addr base off) bytes' bytes'.length i
    ⟨hf2, hi⟩
  have hpc : mc.target.getPc ms1 = p + BitVec.ofNat width (posVal s1.pc 0 code2) :=
    c1.2.1.trans c41
  rw [← hpc] at hfi
  have hlt : index < mc.ffiNames.length := by
    have := (Misc.findIndexLessLength _ _ _ _ hfi).2
    rw [c52]; omega
  have hn : ¬ (mc.progAddresses (mc.target.getPc ms1) ∧
      mc.target.getPc ms1 ∉ mc.ffiEntryPcs) :=
    fun h => h.2 (Misc.findIndex_isMem _ _ _ _ hfi)
  obtain ⟨hcc, hhalt⟩ := ffiEntryPcs_not_ccache_or_halt _ mc index
    ⟨hfi, (c50.2 index i ⟨hi, hlt, hle⟩).1, (c50.2 index i ⟨hi, hlt, hle⟩).2⟩
  have hentry : holEl index mc.ffiEntryPcs = t1.pc := by
    have := (findIndex_holEl _ _ 0 index hfi).2
    rw [Nat.sub_zero] at this
    rw [this, c1.2.1]
  have hts0 : targetStateRel mc.target { t1 with pc := holEl index mc.ffiEntryPcs } ms1 := by
    rw [hentry]; exact c1
  simp only [asmOkExact, asmInstOkExact, asmRegOkExact, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at hok
  have hgr : ∀ x, x < mc.target.config.regCount →
      mc.target.config.avoidRegs.contains x = false → mc.target.getReg ms1 x = t1.regs x :=
    fun x h1 h2 => c1.2.2.2.1 x ⟨h1, h2⟩
  have htreg : ∀ x w, s1.regs x = .word w → t1.regs x = w := by
    intro x w hx
    have := c30 x; rw [hx] at this; simpa [wordLocVal] using this.symm
  have henc' : bytesInMemoryHOL (mc.target.getPc ms1)
      (mc.target.config.encode (.inst (.mem m r (.addr base off)))) (mc.target.getByte ms1)
      mc.progAddresses := by
    obtain ⟨cnt, hcnt⟩ := (encWithNop_iff _ _ _).mp henc
    rw [hcnt, bytesInMemory_append] at hbm
    rw [hpc, c3]
    refine bytesInMemory_changeMem _ _ t1.mem _ _ ⟨hbm.1, fun k hk => ?_⟩
    exact (c1.2.2.1 _ (bytesInMemoryInDomain _ _ _ _ k ⟨hbm.1, hk⟩)).symm
  have hshared : ∀ v, s1.sharedMemDomain (holByteAlign v) = true →
      mc.sharedAddresses v := by
    intro v hv
    rw [c51.2.2.2]; exact c51.2.2.1 v hv
  have hshared0 : ∀ v, s1.sharedMemDomain v = true → mc.sharedAddresses v := by
    intro v hv; rw [c51.2.2.2]; exact hv
  have hwidth : 4 ≤ width / 8 := by rcases c2 with h | h <;> simp [h]
  rw [evaluate] at hev
  simp only [hclock, ↓reduceIte, hfetch] at hev
  obtain ⟨x, next, hso⟩ : ∃ x next, shareMemOp m r (.addr base off) s1 = some (x, next) := by
    split at hev
    · exact absurd (Prod.mk.inj hev).1.symm hres
    · exact ⟨_, _, ‹_›⟩
    · exact ⟨_, _, ‹_›⟩
  have hcore :
      (∀ c, evaluateTargetHOL mc s1.ffi (c + 1) ms1 =
        match x with
        | .final e => (.halt (.ffiOutcome e), ms1, s1.ffi)
        | .ret f bs => evaluateTargetHOL { mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }
            f c (mc.ffiInterfer 0 (index, bs, ms1))) ∧
      (∀ e, x = .final e → next = s1) ∧
      (∀ f bs, x = .ret f bs →
        nextInterference mc s1.ffi ms1 = some
          (.ffiApp index bs ms1 (mc.ffiInterfer 0 (index, bs, ms1)),
            { mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }, f) ∧
        callFFIRelHOL s1.ffi f ∧
        ∃ tregs regs, targetStateRel mc.target
            { t1 with regs := tregs, pc := p + BitVec.ofNat width (posVal (s1.pc + 1) 0 code2) }
            (mc.ffiInterfer 0 (index, bs, ms1)) ∧
          (∀ y, wordLocVal p labs (regs y) = some (tregs y)) ∧
          next = { s1 with ffi := f, regs := regs, pc := s1.pc + 1, clock := s1.clock - 1 }) := by
    have hgb : ∀ wb, s1.regs base = .word wb → mc.target.getReg ms1 base = wb :=
      fun wb hb => (hgr base hok.1.2.1 hok.1.2.2).trans (htreg base wb hb)
    rcases Quantitative.shareMemOp_load_or_store (width := width) m with
      ⟨size, hsz, hgi, hop, hvalid⟩ | ⟨size, hsz, hgi, hop, hvalid⟩
    all_goals
      rw [hgi] at hinfo
      obtain ⟨he, hlk⟩ := hinfo
      have hm := (Quantitative.sptAListLookup_eq_lookup index mc.mmioInfo).trans hlk
      have hsize0 : BitVec.ofNat 8 size = 0 ↔ size = 0 := by
        rcases hsz with rfl | rfl | rfl | rfl <;> decide
      have hv := (hvalid (mc.target.getPc ms1) r (.addr base off)
        (p + BitVec.ofNat width (posVal s1.pc 0 code2 + bytes'.length)) mc.target ms1
        mc.progAddresses).2 henc'
      rw [hop] at hso
    · simp only [shareMemLoad, addrValue] at hso
      cases hb : s1.regs base with
      | loc _ _ => simp [hb] at hso
      | word wb =>
      simp only [hb] at hso
      by_cases hcond : (if size = 0 then
          ((wb + off).toNat % (width / 8) == 0 && s1.sharedMemDomain (wb + off))
        else s1.sharedMemDomain (riscvByteAlignHOL (wb + off))) = true
      swap
      · rw [if_neg hcond] at hso; cases hso
      rw [if_pos hcond] at hso
      have hal : BitVec.ofNat 8 size = 0 →
          (mc.target.getReg ms1 base + off).toNat % (width / 8) = 0 := by
        intro h0
        rw [hsize0] at h0
        rw [if_pos h0] at hcond
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        rw [hgb wb hb]; exact hcond.1
      have hsh : mc.sharedAddresses (mc.target.getReg ms1 base + off) := by
        rw [hgb wb hb]
        by_cases h0 : size = 0
        · rw [if_pos h0] at hcond
          simp only [Bool.and_eq_true] at hcond
          exact hshared0 _ hcond.2
        · rw [if_neg h0, riscvByteAlignHOL_eq c2] at hcond
          exact hshared _ hcond
      have hstep := fun c => Quantitative.evaluateTarget_mappedRead mc s1.ffi c ms1 index _ base r off _
        hn hhalt hcc hfi he hm hal hsh hv
      have hcallT : HolByte.wordToBytes (mc.target.getReg ms1 base + off) false =
          sharedMemoryWordBytes (wb + off) := by
        rw [hgb wb hb, Quantitative.sharedMemoryWordBytes_eq]
      rw [hcallT] at hstep
      cases hcall : callFFIHOL s1.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 size]
          (sharedMemoryWordBytes (wb + off)) with
      | final e =>
        rw [hcall] at hso hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hso
        obtain ⟨rfl, rfl⟩ := hso
        exact ⟨hstep, fun _ _ => rfl, fun _ _ h => by cases h⟩
      | ret f bs =>
        rw [hcall] at hso hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hso
        obtain ⟨rfl, rfl⟩ := hso
        refine ⟨hstep, (fun _ h => by cases h), fun f' bs' h => ?_⟩
        cases h
        obtain ⟨op, hop', hmatch⟩ := c50.1 ms1 0 index bs t1 (BitVec.ofNat 8 size) base off r _
          (mc.target.getReg ms1 base + off) s1.ffi f i
          ⟨hi, hle, hlt, .refl, hlk, c3, rfl, hts0⟩
        rw [he] at hop'
        cases hop'
        have htrel := hmatch ⟨by split; exact hal ‹_›; trivial, hsh, hv, by
          rw [hcallT]; exact hcall⟩
        refine ⟨nextInterferenceSharedMem mc s1.ffi ms1 index base r _ off _ .mappedRead bs f
            ⟨hn, hhalt, hcc, hfi, he, hm, hal, hsh, fun _ => ⟨hv, by rw [he, hcallT]; exact hcall⟩,
              fun h => by cases h⟩,
          ⟨_, _, _, _, hcall⟩, fun n => if n = r then HolByte.wordOfBytes false 0 bs else t1.regs n,
          _, ?_, ?_, rfl⟩
        · rw [hpos]; exact htrel
        · intro y
          by_cases hy : y = r
          · simp [hy, wordLocVal, Quantitative.wordOfBytesHOL8_eq]
          · simpa [hy] using c30 y
    · simp only [shareMemStore, addrValue] at hso
      cases hw : s1.regs r with
      | loc _ _ => simp [hw] at hso
      | word w =>
      cases hb : s1.regs base with
      | loc _ _ => simp [hw, hb] at hso
      | word wb =>
      simp only [hw, hb] at hso
      by_cases hcond : (if size = 0 then
          ((wb + off).toNat % (width / 8) == 0 && s1.sharedMemDomain (wb + off))
        else s1.sharedMemDomain (riscvByteAlignHOL (wb + off))) = true
      swap
      · rw [if_neg hcond] at hso; cases hso
      rw [if_pos hcond] at hso
      have hal : BitVec.ofNat 8 size = 0 →
          (mc.target.getReg ms1 base + off).toNat % (width / 8) = 0 := by
        intro h0
        rw [hsize0] at h0
        rw [if_pos h0] at hcond
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        rw [hgb wb hb]; exact hcond.1
      have hsh : mc.sharedAddresses (mc.target.getReg ms1 base + off) := by
        rw [hgb wb hb]
        by_cases h0 : size = 0
        · rw [if_pos h0] at hcond
          simp only [Bool.and_eq_true] at hcond
          exact hshared0 _ hcond.2
        · rw [if_neg h0, riscvByteAlignHOL_eq c2] at hcond
          exact hshared _ hcond
      have hstep := fun c => Quantitative.evaluateTarget_mappedWrite mc s1.ffi c ms1 index _ base r off _
        hn hhalt hcc hfi he hm hal hsh hv
      have hgw : mc.target.getReg ms1 r = w :=
        (hgr r hok.1.1.1 hok.1.1.2).trans (htreg r w hw)
      have hcallT : ((if BitVec.ofNat 8 size = 0 then
            HolByte.wordToBytes (mc.target.getReg ms1 r) false
          else HolByte.wordToBytesAux (BitVec.ofNat 8 size).toNat (mc.target.getReg ms1 r) false) ++
          HolByte.wordToBytes (mc.target.getReg ms1 base + off) false) =
          ((if size = 0 then sharedMemoryWordBytes w
            else (sharedMemoryWordBytes w).take size) ++ sharedMemoryWordBytes (wb + off)) := by
        rw [hgb wb hb, hgw, Quantitative.sharedMemoryWordBytes_eq, Quantitative.sharedMemoryWordBytes_eq]
        rcases hsz with rfl | rfl | rfl | rfl
        · rfl
        all_goals
          simp only [BitVec.ofNat_eq_ofNat, show ¬ ((1 : Nat) = 0) from by decide,
            show ¬ ((2 : Nat) = 0) from by decide, show ¬ ((4 : Nat) = 0) from by decide,
            ↓reduceIte]
          rw [Quantitative.take_wordToBytes _ _ (by omega)]
          rfl
      rw [hcallT] at hstep
      cases hcall : callFFIHOL s1.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 size]
          ((if size = 0 then sharedMemoryWordBytes w
            else (sharedMemoryWordBytes w).take size) ++ sharedMemoryWordBytes (wb + off)) with
      | final e =>
        rw [hcall] at hso hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hso
        obtain ⟨rfl, rfl⟩ := hso
        exact ⟨hstep, fun _ _ => rfl, fun _ _ h => by cases h⟩
      | ret f bs =>
        rw [hcall] at hso hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hso
        obtain ⟨rfl, rfl⟩ := hso
        refine ⟨hstep, (fun _ h => by cases h), fun f' bs' h => ?_⟩
        cases h
        obtain ⟨op, hop', hmatch⟩ := c50.1 ms1 0 index bs t1 (BitVec.ofNat 8 size) base off r _
          (mc.target.getReg ms1 base + off) s1.ffi f i
          ⟨hi, hle, hlt, .refl, hlk, c3, rfl, hts0⟩
        rw [he] at hop'
        cases hop'
        have htrel := hmatch ⟨by split; exact hal ‹_›; trivial, hsh, hv, by
          rw [hcallT]; exact hcall⟩
        refine ⟨nextInterferenceSharedMem mc s1.ffi ms1 index base r _ off _ .mappedWrite bs f
            ⟨hn, hhalt, hcc, hfi, he, hm, hal, hsh, (fun h => by cases h),
              fun _ => ⟨hv, by rw [he, hcallT]; exact hcall⟩⟩,
          ⟨_, _, _, _, hcall⟩, t1.regs, s1.regs, ?_, c30, rfl⟩
        rw [hpos]; exact htrel
  obtain ⟨hstep, hfinal, hret⟩ := hcore
  have hclk : ∀ k, s1.clock + k = (s1.clock - 1 + k) + 1 := fun k => by omega
  split at hev
  · exact absurd (Prod.mk.inj hev).1.symm hres
  · rename_i outcome next' hshare
    rw [hso] at hshare
    simp only [Option.some.injEq, Prod.mk.injEq] at hshare
    obtain ⟨rfl, rfl⟩ := hshare
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
    refine ⟨0, by omega, ms1, ?_⟩
    rw [hclk, hstep]
    dsimp only
    rw [hfinal _ rfl]
  · rename_i f bs next' hshare
    have hshare' := hshare
    rw [hso] at hshare'
    simp only [Option.some.injEq, Prod.mk.injEq] at hshare'
    obtain ⟨rfl, rfl⟩ := hshare'
    obtain ⟨hnext, hffi, tregs, regs, htrel, hregs, hnexteq⟩ := hret f bs rfl
    subst hnexteq
    have hrel' := Quantitative.stateRel_shareMem hrel f hffi regs (holShiftSeq 1 s1.ioRegs)
      (holShiftSeq 1 s1.ioFpRegs) tregs _ htrel hregs rfl
    obtain ⟨k, hkBound, ms2, hk⟩ := ih f bs _ hshare res _ s2 code2 labs _ _ p
      ⟨oracleTie_ffiNext mc ms1 s1 _ index bs ms1 _ _ f ⟨ht, hnext, rfl, rfl, rfl, rfl, rfl⟩,
        hev, hres, hec, hrel', hbound⟩
    refine ⟨k, by simp only at hkBound; omega, ms2, ?_⟩
    rw [hclk, hstep]
    exact hk

theorem compileCorrect7_callFFI {width : Nat} [NeZero width] {S Q F : Type}
    (s1 : LabSem.State width Config F) (name : MlString)
    (w : BitVec width) (bytes : List (BitVec 8)) (n : Nat)
    (hclock : s1.clock ≠ 0) (hfetch : asmFetch s1 = some (.labAsm (.callFFI name) w bytes n))
    (ih : ∀ (len start len2 start2 : BitVec width) (n1 n2 : Nat) (conf bytes2 : List (BitVec 8))
        (newPc : Nat) (newFfi : HolFfiState F) (newBytes : List (BitVec 8)),
      s1.regs s1.lenReg = .word len → s1.regs s1.ptrReg = .word start →
      s1.regs s1.len2Reg = .word len2 → s1.regs s1.ptr2Reg = .word start2 →
      s1.regs s1.linkReg = .loc n1 n2 →
      readBytearrayWordHOL start len.toNat
        (memLoadByteAuxExact s1.memory s1.memDomain s1.be) = some conf →
      readBytearrayWordHOL start2 len2.toNat
        (memLoadByteAuxExact s1.memory s1.memDomain s1.be) = some bytes2 →
      locToPc n1 n2 s1.code = some newPc →
      callFFIHOL s1.ffi (.extCall name) conf bytes2 = .ret newFfi newBytes →
      CompileCorrectFor7 S Q { s1 with
        memory := writeBytearrayExact start2 newBytes s1.memory s1.memDomain s1.be
        ffi := newFfi
        ioRegs := holShiftSeq 1 s1.ioRegs
        ioFpRegs := holShiftSeq 1 s1.ioFpRegs
        regs := fun r => getRegValue (s1.ioRegs 0 (.extCall name) r) (s1.regs r) WordLocW.word
        fpRegs := fun r => s1.ioFpRegs 0 r
        pc := newPc
        clock := s1.clock - 1 }) :
    CompileCorrectFor7 S Q s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨ht, hev, hres, hec, hrel, hbound⟩
  rw [evaluate] at hev
  simp only [hclock, ↓reduceIte, hfetch] at hev
  split at hev
  rotate_left
  · exact absurd (Prod.mk.inj hev).1.symm hres
  rename_i len start len2 start2 n1 n2 hlen hptr hlen2 hptr2 hlink
  split at hev
  rotate_left
  · exact absurd (Prod.mk.inj hev).1.symm hres
  rename_i conf bytes2 newPc hrd1 hrd2 hloc
  obtain ⟨c1, c2, c3, -, -, c6, c7, c8, c9, c10, c11, c12, c13, -, c15, c16, -, -, -, -, -, c22,
    -, c24, -, -, -, c28, -, c30, c31, -, -, -, -, -, -, -, ht1f, c40, htpc, -, -, c44, -, -, -,
    -, -, c50, -, c52, -⟩ := id hrel
  obtain ⟨w', bytes', len', hok, hmem, hpos, hdis⟩ := fetchedLabAsmLine hrel hfetch
  simp only [lineOk] at hok
  obtain ⟨l, hlBound, ms2, hl⟩ := stepOfLine s1.ffi hrel hec hbound _ bytes' hmem hok.1 hpos hok.2.2 hdis
    (by simp [asmUpd, jumpToOffset, AsmSem.updPc, ht1f])
  have hts := (hl 0).2.2.1
  obtain ⟨-, hgpc, hgmem, hgreg, -⟩ := hts
  obtain ⟨i, hi, hiinfo⟩ := c15
  obtain ⟨y, hy⟩ := hasIoName_findIndex s1.code name (imp_hasIoName s1 name w bytes n hfetch)
  have hmemNames : HolFfiName.extCall name ∈ mc.ffiNames := by
    have hm1 := Misc.findIndex_isMem _ _ _ _ hy
    simp only [Misc.listSubset, List.all_eq_true, decide_eq_true_eq] at c22
    exact c22 _ (List.mem_filter.mpr ⟨hm1, rfl⟩)
  have : Nonempty HolFfiName := ⟨.extCall name⟩
  have hidx : getFfiIndex mc.ffiNames (.extCall name) < i :=
    ffiName_not_mapped _ i _ ⟨hi, ⟨name, rfl⟩, hmemNames⟩
  have hidxt : getFfiIndex (mc.ffiNames.take (holThe (mmioPcsMinIndex mc.ffiNames)))
      (.extCall name) = getFfiIndex mc.ffiNames (.extCall name) := by
    rw [hi]; exact Quantitative.getFfiIndex_take _ _ _ hmemNames hidx
  obtain ⟨-, hnp, hnh, hnc, hfi⟩ := c24 _ i ⟨hmemNames, hi, hidx⟩
  have he := el_getFfiIndex_mem _ _ hmemNames
  have hlk : mc.mmioInfo.lookup (getFfiIndex mc.ffiNames (.extCall name)) = none := by
    have := hiinfo (getFfiIndex mc.ffiNames (.extCall name))
    rwa [if_neg (by omega)] at this
  have hm := (Quantitative.sptAListLookup_eq_lookup _ mc.mmioInfo).trans hlk
  have hjpc : t1.pc + (0 - BitVec.ofNat width (posVal s1.pc 0 code2 +
      (3 + getFfiIndex (mc.ffiNames.take (holThe (mmioPcsMinIndex mc.ffiNames)))
        (.extCall name)) * ffiOffset)) =
      p - BitVec.ofNat width ((3 + getFfiIndex mc.ffiNames (.extCall name)) * ffiOffset) := by
    rw [htpc, hidxt, BitVec.ofNat_add]; ring
  have hpc2 : mc.target.getPc ms2 =
      p - BitVec.ofNat width ((3 + getFfiIndex mc.ffiNames (.extCall name)) * ffiOffset) := by
    rw [hgpc]; simp only [asmUpd, jumpToOffset, AsmSem.updPc]; exact hjpc
  rw [← hpc2] at hnp hnh hnc hfi
  have hn : ¬ (mc.progAddresses (mc.target.getPc ms2) ∧
      mc.target.getPc ms2 ∉ mc.ffiEntryPcs) := fun h => hnp h.1
  have hreg : ∀ r, asmRegOkExact r mc.target.config = true →
      mc.target.getReg ms2 r = t1.regs r := by
    intro r hr
    simp only [asmRegOkExact, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hr
    exact hgreg r hr
  classical
  have hfun : (fun a => if mc.progAddresses a then some (mc.target.getByte ms2 a) else none) =
      (fun a => if mc.progAddresses a then some (t1.mem a) else none) := by
    funext a
    by_cases ha : mc.progAddresses a
    · rw [if_pos ha, if_pos ha, hgmem a (c3 ▸ ha)]; rfl
    · rw [if_neg ha, if_neg ha]
  have hrd : readFfiBytearraysHOL mc ms2 = (some conf, some bytes2) := by
    simp only [readFfiBytearraysHOL, readFfiBytearrayHOL, hfun]
    rw [c7, c9, c11, c13, hreg _ c6, hreg _ c8, hreg _ c10, hreg _ c12,
      wordLocVal_word_target (c30 _) hptr, wordLocVal_word_target (c30 _) hlen,
      wordLocVal_word_target (c30 _) hptr2, wordLocVal_word_target (c30 _) hlen2,
      readBytearray_stateRel mc code2 labs p s1 t1 ms1 _ _ _ ⟨hrel, hrd1⟩,
      readBytearray_stateRel mc code2 labs p s1 t1 ms1 _ _ _ ⟨hrel, hrd2⟩]
  have hstep : ∀ c, evaluateTargetHOL (shiftInterfer l mc) s1.ffi (c + 1) ms2 =
      match callFFIHOL s1.ffi (.extCall name) conf bytes2 with
      | .final e => (.halt (.ffiOutcome e), ms2, s1.ffi)
      | .ret newFfi newBytes =>
          evaluateTargetHOL { shiftInterfer l mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }
            newFfi c (mc.ffiInterfer 0 (getFfiIndex mc.ffiNames (.extCall name), newBytes, ms2)) :=
    fun c => Quantitative.evaluateTarget_extCall (shiftInterfer l mc) s1.ffi c ms2 _ name conf bytes2
      hn hnh hnc hfi he hm hrd
  have hclk : ∀ k, s1.clock + k = (s1.clock - 1 + k) + 1 := fun k => by omega
  cases hcall : callFFIHOL s1.ffi (.extCall name) conf bytes2 with
  | final e =>
    rw [hcall] at hev
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
    refine ⟨l, by omega, ms2, ?_⟩
    rw [(hl s1.clock).1, show s1.clock = s1.clock - 1 + 1 by omega, hstep, hcall]
  | ret newFfi newBytes =>
    rw [hcall] at hev
    have hlenb : newBytes.length = len2.toNat :=
      (StackRemove.callFFILengthHOL _ _ _ _ _ _ hcall).trans (readBytearrayWordHOL_length _ _ _ _ hrd2)
    have hrd2' : readBytearrayWordHOL start2 newBytes.length
        (memLoadByteAuxExact s1.memory s1.memDomain s1.be) = some bytes2 := by
      rw [hlenb]; exact hrd2
    have hstart2 : t1.regs s1.ptr2Reg = start2 := wordLocVal_word_target (c30 _) hptr2
    have hlinkv : t1.regs s1.linkReg = p + BitVec.ofNat width (posVal newPc 0 code2) := by
      have := c30 s1.linkReg
      rw [hlink] at this
      simp only [wordLocVal, c28 n1 n2 newPc hloc, Option.some.injEq] at this
      exact this.symm
    obtain ⟨hres1, hres2⟩ := oracleTie_extCallResidues mc ms1 ms2 s1 l _ name conf bytes2 newBytes
      newFfi t1 ⟨ht, fun k => (hl k).2.1, hn, hnh, hnc, hfi, he, hlk, hrd, hcall⟩
    have hts2 : targetStateRel mc.target
        { t1 with
          pc := p - BitVec.ofNat width ((3 + getFfiIndex mc.ffiNames (.extCall name)) * ffiOffset) }
        ms2 := by
      have := (hl 0).2.2.1
      simp only [asmUpd, jumpToOffset, AsmSem.updPc, hjpc] at this
      exact this
    have htrel := c16 ms2 0 _ newBytes t1 conf bytes2 s1.ffi newFfi i
      ⟨hi, hidx, hrd, .refl, by rw [he]; exact hcall, c3, hts2,
        by rw [hlinkv]; exact Quantitative.stateRel_aligned_target hrel hec newPc⟩
    dsimp only at htrel
    rw [← hres1, ← hres2, hstart2, hlinkv] at htrel
    have hdom : ∀ a, s1.memDomain (riscvByteAlignHOL a) = true → s1.memDomain a = true :=
      fun a h => (c31 a (by rwa [← riscvByteAlignHOL_eq c2])).2.1
    have hbe : s1.be = mc.target.config.bigEndian := c40.trans c44
    have hrel'0 := Quantitative.stateRel_ffiReturn hrel newFfi ⟨_, _, _, _, hcall⟩
      (fun r => getRegValue (s1.ioRegs 0 (.extCall name) r) (s1.regs r) WordLocW.word)
      (fun r => s1.ioFpRegs 0 r)
      (writeBytearrayExact start2 newBytes s1.memory s1.memDomain s1.be)
      (holShiftSeq 1 s1.ioRegs) (holShiftSeq 1 s1.ioFpRegs) newPc (s1.clock - 1)
      _ _ _ _ htrel
      (fun r => by
        cases hio : s1.ioRegs 0 (.extCall name) r with
        | none => simpa [getRegValue] using c30 r
        | some v => simp [getRegValue, wordLocVal])
      (fun _ => rfl)
      (fun a ha => by
        obtain ⟨h1, h2, h3⟩ := c31 a ha
        have := callFFI_bytearray_lemma mc p labs s1 t1 a newBytes start2 bytes2
          ⟨ha, c2, h1, h2, hbe, hrd2', by rw [← hbe]; exact h3⟩
        simpa only [← hbe] using this)
      (fun a ha => asmWriteBytearray_outside s1.memory s1.memDomain s1.be t1.mem hdom newBytes
        start2 bytes2 hrd2' a ha)
      rfl
    have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l hrel'0
    have ht2 := oracleTie_shiftInterfer mc ms1 ms2 s1 l ⟨ht, fun k => (hl k).2.1⟩
    have hnext := nextInterferenceExtCall (shiftInterfer l mc) s1.ffi ms2 _ name conf bytes2
      newBytes newFfi ⟨hn, hnh, hnc, hfi, he, hm, hrd, hcall⟩
    have ht3 : oracleTie { shiftInterfer l mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }
        (mc.ffiInterfer 0 (getFfiIndex mc.ffiNames (.extCall name), newBytes, ms2))
        { s1 with
          memory := writeBytearrayExact start2 newBytes s1.memory s1.memDomain s1.be
          ffi := newFfi
          ioRegs := holShiftSeq 1 s1.ioRegs
          ioFpRegs := holShiftSeq 1 s1.ioFpRegs
          regs := fun r => getRegValue (s1.ioRegs 0 (.extCall name) r) (s1.regs r) WordLocW.word
          fpRegs := fun r => s1.ioFpRegs 0 r
          pc := newPc
          clock := s1.clock - 1 } :=
      oracleTie_ffiNext (shiftInterfer l mc) ms2 s1 _ _ newBytes ms2 _ _ newFfi
        ⟨ht2, hnext, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨k, hkBound, ms3, hk⟩ := ih len start len2 start2 n1 n2 conf bytes2 newPc newFfi newBytes
      hlen hptr hlen2 hptr2 hlink hrd1 hrd2 hloc hcall res _ s2 code2 labs _ _ p
      ⟨ht3, hev, hres, hec, hrel', hbound⟩
    refine ⟨k + l, by simp only at hkBound; omega, ms3, ?_⟩
    rw [show s1.clock + (k + l) = (s1.clock + k) + l by omega, (hl _).1, hclk, hstep, hcall]
    exact hk

theorem compileCorrectFor7_all {width : Nat} [NeZero width] {S Q F : Type}
    (s1 : LabSem.State width Config F) : CompileCorrectFor7 S Q s1 := by
  induction hcl : s1.clock using Nat.strong_induction_on generalizing s1 with
  | _ c ihc =>
  have IH : ∀ s' : LabSem.State width Config F, s'.clock < s1.clock →
      CompileCorrectFor7 S Q s' := fun s' hs => ihc _ (hcl ▸ hs) s' rfl
  by_cases hc : s1.clock = 0
  · exact compileCorrect7_timeOut s1 hc
  have herr : ∀ (h : evaluate s1 = (.error, s1)), CompileCorrectFor7 S Q s1 :=
    compileCorrect7_error s1
  cases hf : asmFetch s1 with
  | none => exact herr (by rw [evaluate]; simp [hc, hf])
  | some line =>
  cases line with
  | label => exact herr (by rw [evaluate]; simp [hc, hf])
  | asm a bytes n =>
    cases a with
    | asmi i =>
      cases i with
      | inst ins =>
        exact compileCorrect7_asmInst s1 ins bytes n hc hf fun _ => IH _ (by
          obtain ⟨-, -, hcl', -⟩ := asmInstConsts ins s1
          simp [incPc, decClock, hcl']; omega)
      | jumpReg r =>
        exact compileCorrect7_jumpReg s1 r bytes n hc hf fun _ _ _ _ _ => IH _ (by
          simp [LabSem.updPc, decClock]; omega)
      | _ => exact herr (by rw [evaluate]; simp [hc, hf])
    | cbw r1 r2 =>
      exact compileCorrect7_cbw s1 r1 r2 bytes n hc hf fun _ _ _ _ _ _ => IH _ (by
        simp [incPc, decClock]; omega)
    | shareMem m r ad =>
      exact compileCorrect7_shareMem s1 m r ad bytes n hc hf fun ffi' bs s' hs => IH _ (by
        have := shareMemOp_ret_clock m r ad s1 s' ffi' bs hs
        simp only; omega)
  | labAsm a w bytes n =>
    cases a with
    | jump jt =>
      exact compileCorrect7_jump s1 jt w bytes n hc hf fun _ _ => IH _ (by
        simp [LabSem.updPc, decClock]; omega)
    | jumpCmp cmp rr ri jt =>
      exact compileCorrect7_jumpCmp s1 cmp rr ri jt w bytes n hc hf
        (fun _ => IH _ (by simp [incPc, decClock]; omega))
        (fun _ _ _ => IH _ (by simp [LabSem.updPc, decClock]; omega))
    | call lab =>
      exact compileCorrect7_call s1 lab w bytes n hc hf
    | locValue reg lab =>
      exact compileCorrect7_locValue s1 reg lab w bytes n hc hf fun _ => IH _ (by
        simp [incPc, decClock, LabSem.updReg]; omega)
    | install =>
      intro res mc s2 code2 labs t1 ms1 p h
      obtain ⟨_, _, _, _, hrel, hbound⟩ := h
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsimilar, -⟩ := hrel
      exact (hbound.noInstall s1.code hsimilar s1.pc w bytes n hf).elim
    | callFFI name =>
      exact compileCorrect7_callFFI s1 name w bytes n hc hf
        fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => IH _ (by simp only; omega)
    | halt => exact compileCorrect7_halt s1 w bytes n hc hf

theorem lab_to_target_slope7_run {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (target : mc.target = riscvTarget)
    (lab : LabSem.State 64 Config F) (t : AsmState 64) (ms : riscv_state)
    (source code2 : LabProgHOL 64) (labs acc : Spt (Spt Nat))
    (ffis : List HolFfiName) (clock : Nat)
    (compiled : removeLabels clock riscvConfig 0 acc ffis source = some (code2, labs))
    (safe : LabProps.noInstall code2)
    (related : LabToTarget.stateRel (mc, code2, labs, mc.target.getPc ms) lab t ms)
    (tied : oracleTie mc ms lab)
    (k_lab : Nat) (result : MachineResult) (post : LabSem.State 64 Config F)
    (run : LabSem.evaluate {lab with clock := k_lab} = (result, post))
    (notError : result ≠ .error) (notTimeout : result ≠ .timeOut) :
    ∃ ms2, evaluateTargetHOL mc lab.ffi (7 * (k_lab + 1)) ms = (result, ms2, post.ffi) := by
  have bounded : CodeBound mc.target code2 := by
    rw [target]
    exact CanonicalRuntime.codeBound code2
      (CanonicalLineBounds.removeLabels_bound clock 0 acc ffis source code2 labs (by decide) compiled)
      safe
  have enc : encoderCorrect mc.target := by
    rw [target]
    exact Flapjack.RiscV.TargetProof.riscv_encoder_correct
  have tiedClock : oracleTie mc ms {lab with clock := k_lab} := tied
  have relClock := (stateRel_clock (mc, code2, labs, mc.target.getPc ms) lab t ms k_lab).mpr related
  obtain ⟨extra, bound, ms2, simulation⟩ :=
    compileCorrectFor7_all {lab with clock := k_lab} result mc post code2 labs t ms
      (mc.target.getPc ms) ⟨tiedClock, run, notError, enc, relClock, bounded⟩
  have fuel : k_lab + extra ≤ 7 * (k_lab + 1) := by simp only at bound; omega
  have extended := evaluateTargetAddClock mc lab.ffi (k_lab + extra) ms
    (7 * (k_lab + 1) - (k_lab + extra)) result ms2 post.ffi simulation notTimeout
  rw [Nat.add_sub_of_le fuel] at extended
  exact ⟨ms2, extended⟩

theorem initialized_slope7_not_timeOut {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (target : mc.target = riscvTarget)
    (ms : riscv_state) (ffi : HolFfiState F)
    (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat)) (clock i cbspace : Nat)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64)
    (names : List HolFfiName) (info shiftedInfo : List ShmemInfoNum)
    (init : Initialization mc ms code code2 labs clock i cbspace t m dm sdm coracle
      names info shiftedInfo)
    (safe : LabProps.noInstall code) (k_lab : Nat)
    (notError : (LabSem.evaluate
      {initialLab mc ms ffi code (progToBytes code2) cbspace t m dm sdm coracle with
        clock := k_lab}).1 ≠ .error)
    (notTimeout : (LabSem.evaluate
      {initialLab mc ms ffi code (progToBytes code2) cbspace t m dm sdm coracle with
        clock := k_lab}).1 ≠ .timeOut) :
    (evaluateTargetHOL mc ffi (7 * (k_lab + 1)) ms).1 ≠ .timeOut := by
  let lab := initialLab mc ms ffi code (progToBytes code2) cbspace t m dm sdm coracle
  have related := initialized_stateRel mc ms ffi code code2 labs clock i cbspace t m dm sdm
    coracle names info shiftedInfo init
  have compiled := init.2.2.2.2.1
  rw [target] at compiled
  have observation := UnfilteredTransfer.filter_observation mc lab rfl rfl k_lab notTimeout
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, similar, _⟩ := id related
  have targetSafe : LabProps.noInstall code2 :=
    CanonicalRuntime.noInstall_similar code2 _ (codeSimilar_sym _ _ similar)
      (UnfilteredTransfer.noInstall_filterSkip lab.code safe)
  have tied0 : oracleTie mc ms lab :=
    oracleTie_makeInit mc ffi t m dm sdm ms code (compile mc.target.config) _ cbspace coracle
  have tied : oracleTie mc ms (UnfilteredTransfer.filtered mc lab) := tied0
  have notErrorF : (LabSem.evaluate {UnfilteredTransfer.filtered mc lab with clock := k_lab}).1 ≠ .error := by
    rw [observation.1]; exact notError
  have notTimeoutF : (LabSem.evaluate {UnfilteredTransfer.filtered mc lab with clock := k_lab}).1 ≠ .timeOut := by
    rw [observation.1]; exact notTimeout
  obtain ⟨ms2, simulation⟩ := lab_to_target_slope7_run mc target
    (UnfilteredTransfer.filtered mc lab) t ms (LabFilter.filterSkip lab.code) code2 labs .ln
    (mc.ffiNames.take i) clock compiled targetSafe related tied k_lab _ _ rfl
    notErrorF notTimeoutF
  have hffi : (UnfilteredTransfer.filtered mc lab).ffi = ffi := rfl
  rw [hffi] at simulation
  rw [simulation]
  exact notTimeoutF

/-- Full initialized Stage 5 transfer at slope 7 (`bootstrap + 7 * (k_lab + 1)`),
and monotonically extended to any larger budget `K ≥ bootstrap + 7 * (k_lab + 1)`. -/
theorem stage5_lab_to_target_slope7_not_timeOut {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (target : mc.target = riscvTarget)
    (initial installed : riscv_state) (ffi : HolFfiState F)
    (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat)) (clock i cbspace : Nat)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64)
    (names : List HolFfiName) (info shiftedInfo : List ShmemInfoNum)
    (init : Initialization mc installed code code2 labs clock i cbspace t m dm sdm coracle
      names info shiftedInfo)
    (safe : LabProps.noInstall code) (k_lab : Nat)
    (notError : (LabSem.evaluate
      {initialLab mc installed ffi code (progToBytes code2) cbspace t m dm sdm coracle with
        clock := k_lab}).1 ≠ .error)
    (notTimeout : (LabSem.evaluate
      {initialLab mc installed ffi code (progToBytes code2) cbspace t m dm sdm coracle with
        clock := k_lab}).1 ≠ .timeOut)
    (bootstrap K : Nat)
    (hK : bootstrap + 7 * (k_lab + 1) ≤ K)
    (bootstrapRun : ∀ fuel, evaluateTargetHOL mc ffi (bootstrap + fuel) initial =
      evaluateTargetHOL mc ffi fuel installed) :
    (evaluateTargetHOL mc ffi K initial).1 ≠ .timeOut := by
  have hbase : (evaluateTargetHOL mc ffi (bootstrap + 7 * (k_lab + 1)) initial).1 ≠ .timeOut := by
    rw [bootstrapRun]
    exact initialized_slope7_not_timeOut mc target installed ffi code code2 labs clock i cbspace t
      m dm sdm coracle names info shiftedInfo init safe k_lab notError notTimeout
  cases hrun : evaluateTargetHOL mc ffi (bootstrap + 7 * (k_lab + 1)) initial with
  | mk res rest =>
    rcases rest with ⟨ms2, ffi2⟩
    have hnt : res ≠ .timeOut := by simpa [hrun] using hbase
    have hext := evaluateTargetAddClock mc ffi (bootstrap + 7 * (k_lab + 1)) initial
      (K - (bootstrap + 7 * (k_lab + 1))) res ms2 ffi2 hrun hnt
    rw [Nat.add_sub_of_le hK] at hext
    simpa [hext] using hnt

end InitECandidate.Solver.Wave8Stage.Slope7Transfer
