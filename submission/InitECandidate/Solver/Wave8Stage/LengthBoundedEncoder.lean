import InitECandidate.Solver.Wave8Stage.BoundedEncoder
import Flapjack.RiscV.CorrectnessEncoding.Length
import InitECandidate.Solver.Wave8Stage.RiscvLengthBound
import InitECandidate.Solver.Wave8Stage.ExposeWitness

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
set_option pp.proofs false

namespace InitECandidate.Solver.Wave8Stage.LengthBoundedEncoder
open Flapjack RiscV.L3 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps Compiler.Encoders.RiscV.Target
open Flapjack.RiscV.TargetProof BoundedEncoder

private theorem jump_range (c : BitVec 64) :
    inSignedRange (18446744073708503040#64) (1048575#64) c = true ↔
      -1048576 ≤ c.toInt ∧ c.toInt ≤ 1048575 := by
  change (decide (-1048576 ≤ c.toInt) && decide (c.toInt ≤ 1048575)) = true ↔ _
  simp only [Bool.and_eq_true, decide_eq_true_eq]

private theorem comparison_range (c : BitVec 64) :
    inSignedRange (18446744073709547524#64) (4095#64) c = true ↔ -4092 ≤ c.toInt ∧ c.toInt ≤ 4095 := by
  change (decide (-4092 ≤ c.toInt) && decide (c.toInt ≤ 4095)) = true ↔ _
  simp only [Bool.and_eq_true, decide_eq_true_eq]

private theorem jump_range_raw (c : BitVec 64) :
    inSignedRange (-1048576) 1048575 c = true ↔
      -1048576 ≤ c.toInt ∧ c.toInt ≤ 1048575 := jump_range c

private theorem comparison_range_raw (c : BitVec 64) :
    inSignedRange (-4092) 4095 c = true ↔ -4092 ≤ c.toInt ∧ c.toInt ≤ 4095 :=
  comparison_range c

macro "close_cost" : tactic => `(tactic|
  (simp_all only [riscvAst, riscvEncodeFail, riscvMemop, jump_range, comparison_range,
    jump_range_raw, comparison_range_raw, List.length_cons, List.length_nil,
    Bool.false_eq_true, Bool.true_eq_false, or_false, false_or, not_false_eq_true,
    not_true_eq_false, and_true, true_and, reduceCtorEq, ↓reduceIte] <;> omega))

/-- Native execution consumes no more instructions than the actual lowering.
This sharper bound permits counting canonical NOP padding in the same budget. -/
theorem bounded_by_length (s1 : AsmState 64) (i : HolAsm 64) (s2 : AsmState 64)
    (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 i s2 ∧ targetStateRel riscvTarget s1 ms) :
    ∃ n, n + 1 ≤ (riscvAst i).length ∧ Witness s1 s2 i ms n := by
  cases i with
  | inst ins =>
    cases ins with
    | skip =>
      expose_witness riscv_encoder_correct_skip s1 s2 ms h
      close_cost
    | const r c =>
      expose_witness riscv_encoder_correct_const r c s1 s2 ms h
      have positive := List.length_pos_iff.mpr (const_register_nonempty r c)
      omega
    | arith a =>
      cases a with
      | binop op r t right =>
        cases right <;> cases op <;>
          expose_witness riscv_encoder_correct_binop _ r t _ s1 s2 ms h <;> close_cost
      | shift op r t right =>
        cases op <;> cases right <;>
          expose_witness riscv_encoder_correct_shift _ r t _ s1 s2 ms h <;> close_cost
      | div r t u =>
        expose_witness riscv_encoder_correct_div r t u s1 s2 ms h
        close_cost
      | longMul r t u v =>
        expose_witness riscv_encoder_correct_longmul r t u v s1 s2 ms h
        close_cost
      | longDiv r t u v q =>
        have good := h.1.2.2.2.2.2.2
        simp [riscvTarget, riscvConfig, asmOkExact, asmInstOkExact, asmArithOkExact] at good
      | addCarry r t u v =>
        expose_witness riscv_encoder_correct_addcarry r t u v s1 s2 ms h
        close_cost
      | addOverflow r t u v =>
        expose_witness riscv_encoder_correct_addoverflow r t u v s1 s2 ms h
        close_cost
      | subOverflow r t u v =>
        expose_witness riscv_encoder_correct_suboverflow r t u v s1 s2 ms h
        close_cost
    | mem m r ad =>
      cases ad with
      | addr base w =>
        expose_witness riscv_encoder_correct_mem m r base w s1 s2 ms h
        cases m <;> close_cost
  | jump c =>
    by_cases range : -1048576 ≤ c.toInt ∧ c.toInt ≤ 1048575
    · expose_witness Jump.near_case c s1 s2 ms h range
      close_cost
    · expose_witness Jump.far_case c s1 s2 ms h range
      close_cost
  | jumpCmp c r right a =>
    by_cases near : -4092 ≤ a.toInt ∧ a.toInt ≤ 4095
    · cases right with
      | imm i =>
        expose_witness JumpCmp.near_immediate_case c r i a s1 s2 ms h near
        cases c <;> close_cost
      | reg t =>
        by_cases test : c = .test ∨ c = .notTest
        · expose_witness JumpCmp.near_register_test_case c r t a s1 s2 ms h near test
          cases c <;> close_cost
        · expose_witness JumpCmp.near_reg_simple c r t a s1 s2 ms h near
            ⟨fun e => test (Or.inl e), fun e => test (Or.inr e)⟩
          cases c <;> close_cost
    · cases right with
      | imm i =>
        cases chosen : wordCmpHOL c (readReg r s1) i
        · expose_witness JumpCmp.far_immediate_false_case c r i a s1 s2 ms h near chosen
          cases c <;> close_cost
        · expose_witness JumpCmp.far_immediate_true_case c r i a s1 s2 ms h near chosen
          cases c <;> close_cost
      | reg t =>
        by_cases test : c = .test ∨ c = .notTest
        · cases chosen : wordCmpHOL c (readReg r s1) (readReg t s1)
          · expose_witness JumpCmp.far_register_test_false_case c r t a s1 s2 ms h near test chosen
            cases c <;> close_cost
          · expose_witness JumpCmp.far_register_test_true_case c r t a s1 s2 ms h near test chosen
            cases c <;> close_cost
        · have simple : c ≠ .test ∧ c ≠ .notTest :=
            ⟨fun e => test (Or.inl e), fun e => test (Or.inr e)⟩
          cases chosen : wordCmpHOL c (readReg r s1) (readReg t s1)
          · expose_witness JumpCmp.far_register_false_case c r t a s1 s2 ms h near simple chosen
            cases c <;> close_cost
          · expose_witness JumpCmp.far_register_true_case c r t a s1 s2 ms h near simple chosen
            cases c <;> close_cost
  | call c =>
    by_cases range : -1048576 ≤ c.toInt ∧ c.toInt ≤ 1048575
    · expose_witness Call.near_case c s1 s2 ms h range
      close_cost
    · expose_witness Call.far_case c s1 s2 ms h range
      close_cost
  | jumpReg r =>
    expose_witness riscv_encoder_correct_jumpReg r s1 s2 ms h
    close_cost
  | loc r c =>
    expose_witness riscv_encoder_correct_loc r c s1 s2 ms h
    close_cost

#print axioms bounded_by_length
end InitECandidate.Solver.Wave8Stage.LengthBoundedEncoder
