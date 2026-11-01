import Flapjack.RiscV.CorrectnessEncoding.Complete
import InitECandidate.Solver.Wave8Stage.RiscvLengthBound
import InitECandidate.Solver.Wave8Stage.ExposeWitness

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
set_option pp.proofs false

namespace InitECandidate.Solver.Wave8Stage.BoundedEncoder
open Flapjack RiscV.L3 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps Compiler.Encoders.RiscV.Target
open Flapjack.RiscV.TargetProof

/-- The complete encoder assertions, with their native step counter retained. -/
def Witness (s1 s2 : AsmState 64) (i : HolAsm 64) (ms : riscv_state) (n : Nat) : Prop :=
  ∀ env : Nat → riscv_state → riscv_state,
    interferenceOk env (riscvTarget.proj s1.memDomain) →
    let pcs := allPcs (riscvTarget.config.encode i).length s1.pc
    asserts n (fun k s => env (n - k) (riscvTarget.next s)) ms
      (fun ms' => riscvTarget.stateOk ms' = true ∧
        (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
        riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
      (fun ms' => targetStateRel riscvTarget s2 ms') ∧
    asserts2 (n + 1) (fun k => env (n + 1 - k)) riscvTarget.next ms
      (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
        riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x)

/-- Every valid RISC-V assembler step has an encoder witness of at most five;
the evaluator consumes `n + 1`, hence at most six native steps. -/
theorem bounded (s1 : AsmState 64) (i : HolAsm 64) (s2 : AsmState 64)
    (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 i s2 ∧ targetStateRel riscvTarget s1 ms) :
    ∃ n, n ≤ 5 ∧ Witness s1 s2 i ms n := by
  cases i with
  | inst ins =>
    cases ins with
    | skip =>
      expose_witness riscv_encoder_correct_skip s1 s2 ms h
      decide
    | const r c =>
      expose_witness riscv_encoder_correct_const r c s1 s2 ms h
      change (riscvAst (.inst (.const r c))).length - 1 ≤ 5
      have := RiscvLengthBound.ast_length_le_six (.inst (.const r c))
      omega
    | arith a =>
      cases a with
      | binop op r t right =>
        cases right <;> cases op <;>
          expose_witness riscv_encoder_correct_binop _ r t _ s1 s2 ms h <;> decide
      | shift op r t right =>
        cases op <;> cases right <;>
          expose_witness riscv_encoder_correct_shift _ r t _ s1 s2 ms h <;> first
          | exact (show 0 ≤ 5 from by decide)
          | exact (show 2 ≤ 5 from by decide)
          | exact (show 4 ≤ 5 from by decide)
      | div r t u =>
        expose_witness riscv_encoder_correct_div r t u s1 s2 ms h
        decide
      | longMul r t u v =>
        expose_witness riscv_encoder_correct_longmul r t u v s1 s2 ms h
        decide
      | longDiv r t u v q =>
        have good := h.1.2.2.2.2.2.2
        simp [riscvTarget, riscvConfig, asmOkExact, asmInstOkExact, asmArithOkExact] at good
      | addCarry r t u v =>
        expose_witness riscv_encoder_correct_addcarry r t u v s1 s2 ms h
        exact (show 5 ≤ 5 from by decide)
      | addOverflow r t u v =>
        expose_witness riscv_encoder_correct_addoverflow r t u v s1 s2 ms h
        exact (show 5 ≤ 5 from by decide)
      | subOverflow r t u v =>
        expose_witness riscv_encoder_correct_suboverflow r t u v s1 s2 ms h
        exact (show 5 ≤ 5 from by decide)
    | mem m r ad =>
      cases ad with
      | addr base w =>
        expose_witness riscv_encoder_correct_mem m r base w s1 s2 ms h
        decide
  | jump c =>
    by_cases range : -1048576 ≤ c.toInt ∧ c.toInt ≤ 1048575
    · expose_witness Jump.near_case c s1 s2 ms h range
      decide
    · expose_witness Jump.far_case c s1 s2 ms h range
      decide
  | jumpCmp c r right a =>
    by_cases near : -4092 ≤ a.toInt ∧ a.toInt ≤ 4095
    · cases right with
      | imm i =>
        expose_witness JumpCmp.near_immediate_case c r i a s1 s2 ms h near
        decide
      | reg t =>
        by_cases test : c = .test ∨ c = .notTest
        · expose_witness JumpCmp.near_register_test_case c r t a s1 s2 ms h near test
          decide
        · expose_witness JumpCmp.near_reg_simple c r t a s1 s2 ms h near
            ⟨fun e => test (Or.inl e), fun e => test (Or.inr e)⟩
          decide
    · cases right with
      | imm i =>
        cases chosen : wordCmpHOL c (readReg r s1) i
        · expose_witness JumpCmp.far_immediate_false_case c r i a s1 s2 ms h near chosen
          decide
        · expose_witness JumpCmp.far_immediate_true_case c r i a s1 s2 ms h near chosen
          decide
      | reg t =>
        by_cases test : c = .test ∨ c = .notTest
        · cases chosen : wordCmpHOL c (readReg r s1) (readReg t s1)
          · expose_witness JumpCmp.far_register_test_false_case c r t a s1 s2 ms h near test chosen
            decide
          · expose_witness JumpCmp.far_register_test_true_case c r t a s1 s2 ms h near test chosen
            decide
        · have simple : c ≠ .test ∧ c ≠ .notTest :=
            ⟨fun e => test (Or.inl e), fun e => test (Or.inr e)⟩
          cases chosen : wordCmpHOL c (readReg r s1) (readReg t s1)
          · expose_witness JumpCmp.far_register_false_case c r t a s1 s2 ms h near simple chosen
            decide
          · expose_witness JumpCmp.far_register_true_case c r t a s1 s2 ms h near simple chosen
            decide
  | call c =>
    by_cases range : -1048576 ≤ c.toInt ∧ c.toInt ≤ 1048575
    · expose_witness Call.near_case c s1 s2 ms h range
      decide
    · expose_witness Call.far_case c s1 s2 ms h range
      decide
  | jumpReg r =>
    expose_witness riscv_encoder_correct_jumpReg r s1 s2 ms h
    decide
  | loc r c =>
    expose_witness riscv_encoder_correct_loc r c s1 s2 ms h
    decide

#print axioms bounded
end InitECandidate.Solver.Wave8Stage.BoundedEncoder
