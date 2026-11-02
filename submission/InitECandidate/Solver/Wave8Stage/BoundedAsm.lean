import Flapjack.Compiler.Backend.Semantics.TargetProps.AsmStepEvaluate
import InitECandidate.Solver.Wave8Stage.BoundedEncoder

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.BoundedAsm
open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps Compiler.Backend.Semantics.TargetProps
open Compiler.Encoders.RiscV.Target RiscV.L3

/-- Encoder correctness with a retained bound on its existential counter. -/
def HasBoundedEncoder {width : Nat} [NeZero width] {S Q : Type}
    (t : HolAsmTarget width S Q) (B : HolAsm width → Nat) : Prop :=
  ∀ (s1 : AsmState width) (i : HolAsm width) (s2 : AsmState width) (ms : S),
    asmStep t.config s1 i s2 ∧ targetStateRel t s1 ms →
    ∃ n, n ≤ B i ∧ ∀ env : Nat → S → S,
      interferenceOk env (t.proj s1.memDomain) →
      let pcs := allPcs (t.config.encode i).length s1.pc
      asserts n (fun k s => env (n - k) (t.next s)) ms
        (fun ms' => t.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → t.getByte ms' pc = t.getByte ms pc) ∧
          t.getPc ms' ∈ pcs t.config.codeAlignment)
        (fun ms' => targetStateRel t s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) t.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x → t.getByte ms1 x = t.getByte ms2 x)

theorem riscv_bounded_encoder : HasBoundedEncoder riscvTarget (fun _ => 5) :=
  BoundedEncoder.bounded

/-- The original assembly-step simulation with its numerical witness retained.
The proof follows `asmStepImpEvaluate`; its only change is sourcing the
encoder witness from bounded encoder correctness and retaining `n ≤ B`. -/
theorem asmStepImpEvaluate_bounded {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (c : MachineConfig width S Q) (s1 : AsmState width)
    (ms1 : S) (io : HolFfiState σ) (i : HolAsm width)
    (B : HolAsm width → Nat) (bounded : HasBoundedEncoder c.target B)
    (h : encoderCorrect c.target ∧ c.progAddresses = s1.memDomain ∧
      ffiEntryPcsDisjoint c s1 (c.target.config.encode i).length ∧
      interferenceOk c.nextInterfer (c.target.proj s1.memDomain) ∧
      asmStep c.target.config s1 i
        (asmUpd i (s1.pc + BitVec.ofNat width (c.target.config.encode i).length) s1) ∧
      targetStateRel c.target s1 ms1) :
    ∃ l, l ≤ B i + 1 ∧ ∃ ms2, ∀ k,
      evaluateTargetHOL c io (k + l) ms1 = evaluateTargetHOL (shiftInterfer l c) io k ms2 ∧
      findNextInterference c io (k + l) ms1 = findNextInterference (shiftInterfer l c) io k ms2 ∧
      targetStateRel c.target
        (asmUpd i (s1.pc + BitVec.ofNat width (c.target.config.encode i).length) s1) ms2 ∧
      l ≠ 0 := by
  rcases h with ⟨henc, hdm, hdis, hinter, hstep, hrel⟩
  obtain ⟨n, hn, hs⟩ := bounded s1 i _ ms1 ⟨hstep, hrel⟩
  have hnon := encOkNotEmpty c.target.config i ⟨henc.1.1, hstep.2.2.2.2.2.2⟩
  have hlen : 0 < (c.target.config.encode i).length := by
    exact List.length_pos_iff.mpr hnon
  have hbytes : bytesInMemoryHOL s1.pc (c.target.config.encode i) (c.target.getByte ms1)
      (fun a => c.progAddresses a ∧ a ∉ c.ffiEntryPcs) := by
    apply bytesInMemory_diff s1.pc _ (c.target.getByte ms1) _ s1.memDomain
      (fun a => a ∈ c.ffiEntryPcs)
    refine ⟨?_, ?_, hdis⟩
    · rw [hdm]
    · apply bytesInMemory_changeMem s1.pc _ s1.mem _ s1.memDomain
      refine ⟨hstep.1, ?_⟩
      intro j hj
      apply (hrel.2.2.1 _ ?_).symm
      have hd := bytesInMemory_allPcs _ _ _ _ 0 hstep.1
      apply hd
      rw [allPcs_eq]
      exact ⟨j, by simpa using hj, by simp⟩
  have hnormal : c.progAddresses (c.target.getPc ms1) ∧ c.target.getPc ms1 ∉ c.ffiEntryPcs := by
    have hd := bytesInMemory_allPcs _ _ _ _ 0 hbytes
    apply hd
    rw [allPcs_eq, hrel.2.1]
    exact ⟨0, by simpa using hlen, by simp⟩
  have ha : ∀ env, interferenceOk env (c.target.proj s1.memDomain) →
      asserts n (fun k s => env k (c.target.next s)) ms1
        (fun ms => c.target.stateOk ms = true ∧
          (∀ pc, pc ∈ allPcs (c.target.config.encode i).length s1.pc 0 →
            c.target.getByte ms pc = c.target.getByte ms1 pc) ∧
          c.target.getPc ms ∈ allPcs (c.target.config.encode i).length s1.pc c.target.config.codeAlignment)
        (fun ms => targetStateRel c.target
          (asmUpd i (s1.pc + BitVec.ofNat width (c.target.config.encode i).length) s1) ms) := by
    intro env he
    have ht := (hs (fun k => env (n - k)) (fun k ms => he (n - k) ms)).1
    apply asserts_weaken n _ _ ms1 _ _ _ _ ht
    intro k hk
    constructor
    · funext ms
      have hidx : n - (n - k) = k := by omega
      simp only [hidx]
    · exact fun hx => hx
  have hobs : ∀ ms ms', c.target.proj s1.memDomain ms = c.target.proj s1.memDomain ms' →
      c.target.stateOk ms = c.target.stateOk ms' ∧ c.target.getPc ms = c.target.getPc ms' ∧
      ∀ a, s1.memDomain a → c.target.getByte ms a = c.target.getByte ms' a := by
    intro ms ms' hp
    exact (henc.1.2 ms ms' s1 hp).2
  obtain ⟨ms2, hout⟩ := evaluateEqEvaluate_all n ms1 c io s1.memDomain i s1.pc _
    ⟨hnormal, hrel.1, hdm, hinter, fun _ _ hr => hr.1, hobs, ha,
      (hs c.nextInterfer hinter).2, 0, by simpa using hrel.2.1,
      by simpa using hlen, hbytes⟩
  refine ⟨n + 1, by omega, ms2, ?_⟩
  intro k
  exact ⟨(hout k).1, (hout k).2.1, (hout k).2.2, by omega⟩


end InitECandidate.Solver.Wave8Stage.BoundedAsm
