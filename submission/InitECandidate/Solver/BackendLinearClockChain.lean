import InitECandidate.Solver.WordToStackClockBound
import InitECandidate.Solver.StackToLabClockBound
import InitECandidate.Solver.LabToTargetMultiStepBound
import InitECandidate.Solver.YukonPipelineBridge

set_option autoImplicit false

/-!
Composition of backend budgets. The linear stage bounds and the bounded machine
trace are explicit obligations: the imported existential simulations do not
supply them. In particular, this module does not certify constants for the
baseline ROM, nor infer a Stack non-timeout premise from Word non-timeout.
-/
namespace InitECandidate.Solver.BackendLinearClockChain

open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabSem

/-- Word -> Stack -> Lab -> machine budget, including the initial Lab clock. -/
def backendBudget (k_word C_ws D_ws C_sl D_sl stepFactor : Nat) : Nat :=
  (stepFactor + 1) * (C_sl * (C_ws * k_word + D_ws) + D_sl)

/-- The two backend affine expansions combine into the bridge's coefficients. -/
theorem backendBudget_eq_pipeline
    (k_word C_ws D_ws C_sl D_sl stepFactor : Nat) :
    backendBudget k_word C_ws D_ws C_sl D_sl stepFactor =
      linearPipelineTargetBudget k_word 1 0 (C_sl * C_ws)
        (C_sl * D_ws + D_sl) (stepFactor + 1) := by
  simp [backendBudget, linearPipelineTargetBudget, Nat.mul_add, Nat.mul_assoc,
    Nat.add_assoc]

/-- Every bounded Lab trace fits the composed Word -> Stack -> Lab budget. -/
theorem clock_chain_bound
    (k_word k_stack k_lab extra C_ws D_ws C_sl D_sl stepFactor : Nat)
    (hws : k_stack ≤ C_ws * k_word + D_ws)
    (hsl : k_lab ≤ C_sl * k_stack + D_sl)
    (hextra : extra ≤ multiStepTargetBound stepFactor k_lab) :
    k_lab + extra ≤ backendBudget k_word C_ws D_ws C_sl D_sl stepFactor := by
  have hb := Nat.le_trans hsl
    (Nat.add_le_add_right (Nat.mul_le_mul_left C_sl hws) D_sl)
  have ht : k_lab + extra ≤ (stepFactor + 1) * k_lab := by
    simpa [multiStepTargetBound, Nat.add_mul, Nat.add_comm] using
      Nat.add_le_add_left hextra k_lab
  exact ht.trans (Nat.mul_le_mul_left (stepFactor + 1) hb)

/-- Add the frontend bound using the existing Yukon pipeline bridge. -/
theorem pan_clock_chain_bound
    (k_pan k_word k_stack k_lab extra C_front D_front C_ws D_ws C_sl D_sl
      stepFactor : Nat)
    (hfront : k_word ≤ C_front * k_pan + D_front)
    (hws : k_stack ≤ C_ws * k_word + D_ws)
    (hsl : k_lab ≤ C_sl * k_stack + D_sl)
    (hextra : extra ≤ multiStepTargetBound stepFactor k_lab) :
    k_lab + extra ≤ linearPipelineTargetBudget k_pan C_front D_front
      (C_sl * C_ws) (C_sl * D_ws + D_sl) (stepFactor + 1) := by
  have hb := clock_chain_bound k_word k_stack k_lab extra C_ws D_ws C_sl D_sl
    stepFactor hws hsl hextra
  rw [backendBudget_eq_pipeline] at hb
  exact hb.trans (by
    simpa [backendBudget, linearPipelineTargetBudget, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc] using
      linearPipelineTargetBudget_of_stage_bounds k_pan k_word
        (C_sl * (C_ws * k_word + D_ws) + D_sl)
        (backendBudget k_word C_ws D_ws C_sl D_sl stepFactor)
        C_front D_front (C_sl * C_ws) (C_sl * D_ws + D_sl) (stepFactor + 1)
        hfront (by simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]) (Nat.le_refl _))

/-- Transfer the actual bounded multi-step trace to the composed machine budget.
The step laws, terminal run, and linear clock estimates remain proof obligations.
This theorem applies in particular to width 64 and the RISC-V machine config. -/
theorem target_run_of_clock_chain {width : Nat} [NeZero width] {S Q F : Type}
    (k_word k_stack k_lab C_ws D_ws C_sl D_sl stepFactor : Nat)
    (mcSeq : Nat → MachineConfig width S Q)
    (sSeq : Nat → LabSem.State width LabToTarget.Config F)
    (msSeq : Nat → S) (lSeq : Nat → Nat)
    (s_end : LabSem.State width LabToTarget.Config F) (res : MachineResult)
    (hnt : res ≠ .timeOut)
    (hws : k_stack ≤ C_ws * k_word + D_ws)
    (hsl : k_lab ≤ C_sl * k_stack + D_sl)
    (hclock : (sSeq 0).clock = k_lab)
    (hbase : ∃ ms_end,
      evaluateTargetHOL (mcSeq k_lab) (sSeq k_lab).ffi (sSeq k_lab).clock (msSeq k_lab) =
        (res, ms_end, s_end.ffi))
    (hstep : ∀ i < k_lab,
      (sSeq i).clock ≠ 0 ∧
      (∀ k, evaluateTargetHOL (mcSeq i) (sSeq i).ffi (k + lSeq i) (msSeq i) =
        evaluateTargetHOL (mcSeq (i + 1)) (sSeq i).ffi k (msSeq (i + 1))) ∧
      lSeq i ≠ 0 ∧ lSeq i ≤ stepFactor + 1 ∧
      (sSeq (i + 1)).clock = (sSeq i).clock - 1 ∧
      (sSeq (i + 1)).ffi = (sSeq i).ffi) :
    ∃ ms_end,
      evaluateTargetHOL (mcSeq 0) (sSeq 0).ffi
        (backendBudget k_word C_ws D_ws C_sl D_sl stepFactor) (msSeq 0) =
          (res, ms_end, s_end.ffi) := by
  obtain ⟨extra, he, ms_end, hr⟩ := lab_to_target_multi_step_clock_bound
    stepFactor k_lab mcSeq sSeq msSeq lSeq s_end res hbase hstep
  rw [hclock] at hr
  have hb := clock_chain_bound k_word k_stack k_lab extra C_ws D_ws C_sl D_sl
    stepFactor hws hsl he
  have hn : (evaluateTargetHOL (mcSeq 0) (sSeq 0).ffi (k_lab + extra) (msSeq 0)).1 ≠
      .timeOut := by rw [hr]; exact hnt
  obtain ⟨ha, _⟩ := evaluateTarget_add_clock_of_not_timeOut (mcSeq 0) (sSeq 0).ffi
    (msSeq 0) (k_lab + extra)
    (backendBudget k_word C_ws D_ws C_sl D_sl stepFactor - (k_lab + extra)) hn
  rw [Nat.add_sub_of_le hb] at ha
  exact ⟨ms_end, ha.trans hr⟩

/-- A numerical sufficient condition, not an instantiation for the baseline ROM:
a total slope at most 4503 and offset at most 119925473 fit the score ceiling. -/
theorem finite_ceiling_of_affine_coefficients
    (k_pan slope offset : Nat) (hk : k_pan ≤ 200000000)
    (hslope : slope ≤ 4503) (hoffset : offset ≤ 119925473) :
    slope * k_pan + offset < 900719925474 := by
  have h := Nat.mul_le_mul hslope hk
  omega

#print axioms target_run_of_clock_chain
#print axioms pan_clock_chain_bound
#print axioms finite_ceiling_of_affine_coefficients

end InitECandidate.Solver.BackendLinearClockChain
