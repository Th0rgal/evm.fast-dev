import InitECandidate.Solver.Wave8Stage.QuantitativeCommon
import Flapjack.Compiler.Backend.LabToTarget.BytesInMemoryFetch
import Flapjack.Compiler.Backend.LabToTarget.FfiEntryDisjoint
import Flapjack.Compiler.Backend.LabToTarget.InstFrame
import Flapjack.Compiler.Backend.Semantics.TargetProps.AsmStepEvaluate
import Flapjack.Compiler.Backend.LabToTarget.Interference
import Flapjack.Compiler.Backend.LabToTarget.NopSteps

/-! Flapjack infrastructure shared by the `compile_correct` cases: the
leading instruction of a fetched, validly encoded target line is simulated by
`asm_step_IMP_evaluate_step_find_next` from the full `state_rel`. -/
namespace InitECandidate.Solver.Wave8Stage.Quantitative
open Flapjack Flapjack.Compiler.Encoders Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.AsmSem Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang

/-- The two orientations of the original optional link-register guard agree. -/
theorem linkGuard_flip {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (s : AsmState width)
    (h : match c.linkReg with
      | none => True
      | some r => s.lr = r) :
    match c.linkReg with
    | some r => s.lr = r
    | none => True := by
  revert h; cases c.linkReg <;> exact id

/-- Simulate the leading instruction `instr` of a fetched line whose bytes
`bytes'` encode it with NOP padding. -/
theorem stepOfLine {width : Nat} [NeZero width] {S Q F σ : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 : LabSem.State width Config F} {t1 : AsmState width} {ms1 : S}
    (io : HolFfiState σ) (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1)
    (hec : encoderCorrect mc.target) (hbound : CodeBound mc.target code2) (instr : HolAsm width) (bytes' : List (BitVec 8))
    (hmem : bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes' t1.mem
      t1.memDomain (fun a => s1.memDomain a = true))
    (henc : encWithNop mc.target.config.encode instr bytes')
    (hpos : posVal (s1.pc + 1) 0 code2 = posVal s1.pc 0 code2 + bytes'.length)
    (hok : asmOkExact instr mc.target.config = true)
    (hdis : ffiEntryPcsDisjoint mc t1 bytes'.length)
    (hnf : ¬ (asmUpd instr (t1.pc + BitVec.ofNat width (mc.target.config.encode instr).length)
      t1).failed) :
    ∃ l, l ≤ 6 ∧ ∃ ms2, ∀ k,
      evaluateTargetHOL mc io (k + l) ms1 = evaluateTargetHOL (shiftInterfer l mc) io k ms2 ∧
      findNextInterference mc io (k + l) ms1 =
        findNextInterference (shiftInterfer l mc) io k ms2 ∧
      targetStateRel mc.target
        (asmUpd instr (t1.pc + BitVec.ofNat width (mc.target.config.encode instr).length) t1)
        ms2 ∧
      l ≠ 0 := by
  obtain ⟨B, bounded, budget⟩ := hbound.bounded
  obtain ⟨c1, -, c3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    c27, -, -, -, -, -, -, -, -, -, -, -, ht1f, -, htpc, -, c43, c44, c45, -⟩ := hrel
  obtain ⟨count, rfl⟩ := (encWithNop_iff _ _ _).mp henc
  have hlen : (mc.target.config.encode instr).length ≤
      (mc.target.config.encode instr ++
        (List.replicate count (mc.target.config.encode (.inst .skip))).flatten).length := by
    simp
  have hcost := budget s1.pc instr _ count hpos rfl
  have simulation : ∃ l, l ≤ B instr + 1 ∧ ∃ ms2, ∀ k,
      evaluateTargetHOL mc io (k + l) ms1 = evaluateTargetHOL (shiftInterfer l mc) io k ms2 ∧
      findNextInterference mc io (k + l) ms1 = findNextInterference (shiftInterfer l mc) io k ms2 ∧
      targetStateRel mc.target
        (asmUpd instr (t1.pc + BitVec.ofNat width (mc.target.config.encode instr).length) t1)
        ms2 ∧ l ≠ 0 := by
    apply BoundedAsm.asmStepImpEvaluate_bounded mc t1 ms1 io instr B bounded
    refine ⟨hec, c3, ffiEntryPcsDisjoint_shorter mc t1 _ _ ⟨hdis, hlen⟩, c27, ?_, c1⟩
    refine ⟨?_, linkGuard_flip _ _ c43, c44, c45, rfl, hnf, hok⟩
    rw [htpc]
    exact bytesInMem_encWithNop _ _ _ _ _ _ _ henc hmem
  obtain ⟨l, hl, ms2, hs⟩ := simulation
  exact ⟨l, by omega, ms2, hs⟩

/-- Simulate a whole NOP-padded line `bytes'` encoding the non-`Call`
instruction `instr` (`asm_step_IMP_evaluate_step_nop`), given that the line's
bytes are still in the target memory after the instruction. -/
theorem stepNopOfLineMem {width : Nat} [NeZero width] {S Q F σ : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 : LabSem.State width Config F} {t1 : AsmState width} {ms1 : S}
    (io : HolFfiState σ) (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1)
    (hec : encoderCorrect mc.target) (hbound : CodeBound mc.target code2) (instr : HolAsm width) (bytes' : List (BitVec 8))
    (hmem : bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes' t1.mem
      t1.memDomain (fun a => s1.memDomain a = true))
    (henc : encWithNop mc.target.config.encode instr bytes')
    (hpos : posVal (s1.pc + 1) 0 code2 = posVal s1.pc 0 code2 + bytes'.length)
    (hok : asmOkExact instr mc.target.config = true)
    (hdis : ffiEntryPcsDisjoint mc t1 bytes'.length)
    (hnf : ¬ (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1).failed)
    (hb2 : bytesInMemoryHOL t1.pc bytes'
      (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1).mem t1.memDomain)
    (hcall : ∀ x, instr ≠ .call x) :
    ∃ l, l ≤ 6 ∧ ∃ ms2, ∀ k,
      evaluateTargetHOL mc io (k + l) ms1 = evaluateTargetHOL (shiftInterfer l mc) io k ms2 ∧
      findNextInterference mc io (k + l) ms1 =
        findNextInterference (shiftInterfer l mc) io k ms2 ∧
      targetStateRel mc.target (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1)
        ms2 ∧
      l ≠ 0 := by
  obtain ⟨B, bounded, budget⟩ := hbound.bounded
  obtain ⟨c1, -, c3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    c27, -, -, -, -, -, -, -, -, -, -, -, -, -, htpc, -, c43, c44, c45, -⟩ := hrel
  have hb := bytesInMem_impliesMemory _ _ _ _ _ hmem
  rw [← htpc] at hb
  apply BoundedNop.asmStepImpEvaluateStepNop_bounded mc t1 ms1 io instr _ bytes' B bounded 6
    (fun count heq => budget s1.pc instr bytes' count hpos heq)
  refine ⟨hec, c3, hdis, c27, hb2, ?_, rfl, c1, hcall⟩
  exact ⟨hb, henc, c43, c44, c45, rfl, hnf, hok⟩

/-- Simulate a whole NOP-padded line `bytes'` encoding the non-`Call`
instruction `instr` (`asm_step_IMP_evaluate_step_nop`), when the instruction
leaves memory unchanged outside the source memory domain. -/
theorem stepNopOfLine {width : Nat} [NeZero width] {S Q F σ : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 : LabSem.State width Config F} {t1 : AsmState width} {ms1 : S}
    (io : HolFfiState σ) (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1)
    (hec : encoderCorrect mc.target) (hbound : CodeBound mc.target code2) (instr : HolAsm width) (bytes' : List (BitVec 8))
    (hmem : bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes' t1.mem
      t1.memDomain (fun a => s1.memDomain a = true))
    (henc : encWithNop mc.target.config.encode instr bytes')
    (hpos : posVal (s1.pc + 1) 0 code2 = posVal s1.pc 0 code2 + bytes'.length)
    (hok : asmOkExact instr mc.target.config = true)
    (hdis : ffiEntryPcsDisjoint mc t1 bytes'.length)
    (hnf : ¬ (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1).failed)
    (hmemeq : ∀ a, ¬ s1.memDomain a = true →
      (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1).mem a = t1.mem a)
    (hcall : ∀ x, instr ≠ .call x) :
    ∃ l, l ≤ 6 ∧ ∃ ms2, ∀ k,
      evaluateTargetHOL mc io (k + l) ms1 = evaluateTargetHOL (shiftInterfer l mc) io k ms2 ∧
      findNextInterference mc io (k + l) ms1 =
        findNextInterference (shiftInterfer l mc) io k ms2 ∧
      targetStateRel mc.target (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1)
        ms2 ∧
      l ≠ 0 := by
  obtain ⟨B, bounded, budget⟩ := hbound.bounded
  obtain ⟨c1, -, c3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    c27, -, -, -, -, -, -, -, -, -, -, -, -, -, htpc, -, c43, c44, c45, -⟩ := hrel
  have hb := bytesInMem_impliesMemory _ _ _ _ _ hmem
  rw [← htpc] at hb
  have hb2 := bytesInMem_impliesMemory_change _ t1.mem
    (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1).mem _ bytes' _
    (fun a ha => (hmemeq a ha).symm) hmem
  rw [← htpc] at hb2
  apply BoundedNop.asmStepImpEvaluateStepNop_bounded mc t1 ms1 io instr _ bytes' B bounded 6
    (fun count heq => budget s1.pc instr bytes' count hpos heq)
  refine ⟨hec, c3, hdis, c27, hb2, ?_, rfl, c1, hcall⟩
  exact ⟨hb, henc, c43, c44, c45, rfl, hnf, hok⟩


end InitECandidate.Solver.Wave8Stage.Quantitative
