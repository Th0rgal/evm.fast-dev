import InitECandidate.Solver.Wave8Stage.BoundedNop
import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.Common

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.Quantitative
open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps
  Compiler.Backend Compiler.Backend.LabSem Compiler.Backend.LabToTarget
  Compiler.Backend.Semantics.TargetProps Compiler.Backend.LabProps

/-- Quantitative facts about the actual target code. These will be discharged
from canonical RISC-V compilation, rather than assumed of arbitrary padding. -/
structure CodeBound {width : Nat} [NeZero width] {S Q : Type}
    (target : HolAsmTarget width S Q) (code : LabProgHOL width) : Prop where
  bounded : ∃ B : HolAsm width → Nat, BoundedAsm.HasBoundedEncoder target B ∧
    ∀ pc i bytes count,
      posVal (pc + 1) 0 code = posVal pc 0 code + bytes.length →
      bytes = target.config.encode i ++
        (List.replicate count (target.config.encode (.inst .skip))).flatten →
      B i + 1 + count * (B (.inst .skip) + 1) ≤ 6
  noInstall : ∀ source, codeSimilar source code → LabProps.noInstall source

/-- The full compiler-correctness conclusion, retaining a bound on extra fuel.
No source error is admitted, and no state or interference premise is removed. -/
def CompileCorrectFor {width : Nat} [NeZero width] (S Q : Type) {F : Type}
    (s1 : LabSem.State width Config F) : Prop :=
  ∀ (res : MachineResult) (mc : MachineConfig width S Q) (s2 : LabSem.State width Config F)
    (code2 : LabProgHOL width) (labs : Spt (Spt Nat)) (t1 : AsmState width) (ms1 : S)
    (p : BitVec width),
    oracleTie mc ms1 s1 ∧ evaluate s1 = (res, s2) ∧ res ≠ .error ∧
      encoderCorrect mc.target ∧ stateRel (mc, code2, labs, p) s1 t1 ms1 ∧
      CodeBound mc.target code2 →
    ∃ k, k ≤ 8 * s1.clock + 9 ∧ ∃ ms2,
      evaluateTargetHOL mc s1.ffi (s1.clock + k) ms1 = (res, ms2, s2.ffi)

theorem compileCorrect_step {width : Nat} [NeZero width] {S Q F : Type}
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
    (ih : CompileCorrectFor S Q s1') :
    ∃ k, k ≤ 8 * s1.clock + 9 ∧ ∃ ms3,
      evaluateTargetHOL mc s1.ffi (s1.clock + k) ms1 = (res, ms3, s2.ffi) := by
  obtain ⟨hc, hffi, hio, hiofp, hcc, hccfp⟩ := hs'
  have ht' : oracleTie (shiftInterfer l mc) ms2 s1' :=
    oracleTie_step mc ms1 ms2 s1 s1' l ⟨ht, fun k => (hl k).2, hio, hiofp, hcc, hccfp, hffi⟩
  obtain ⟨k', hkBound, ms3, hk⟩ := ih res (shiftInterfer l mc) s2 code2 labs t1' ms2 p
    ⟨ht', hev, hres, hec, hrel', hbound⟩
  refine ⟨k' + l - 1, by omega, ms3, ?_⟩
  rw [show s1.clock + (k' + l - 1) = (s1'.clock + k') + l by omega, (hl _).1, ← hffi]
  exact hk

end InitECandidate.Solver.Wave8Stage.Quantitative
