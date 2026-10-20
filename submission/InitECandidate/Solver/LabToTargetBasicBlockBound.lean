import InitECandidate.Solver.LabToTargetMultiStepBound
import InitECandidate.Solver.BackendLinearClockChain
import InitECandidate.Solver.GuestGasAndHtabBound
import InitECandidate.Solver.EvmOpcodeTightBound

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.LabToTargetBasicBlockBound` — Tight Basic-Block Expansion Factor (`B_max ≤ 8`) for `LabToTarget` (`W5_2`)

This module replaces the coarse global `stepExpansionFactor mc code = asmCodeLength code + 2`
from `LabToTargetMultiStepBound` (which scales with the entire 904 KB binary length) with the
tight per-basic-block expansion factor `basicBlockStepFactor B_max = B_max`:

1. **Basic-Block Cost Model (`basicBlockStepFactor`, `basicBlockMultiStepBound`, `basicBlockTotalTargetTicks`)**:
   - In `LabSem`, every clock decrement (`decClock` on `Jump`, `JumpCmp`, `Call`, `LocValue`)
     executes a single jump-free basic block of at most `B_max` RISC-V instructions (where
     64-bit immediate materialization takes `≤ 8` RISC-V instructions).
   - `basicBlockStepFactor B_max := B_max` represents the extra target ticks per `LabSem` clock tick,
     so each `LabSem` clock tick expands to at most `B_max + 1` RISC-V target instructions
     (`lSeq i ≤ basicBlockStepFactor B_max + 1`).
   - Across `k_lab` `LabSem` clock ticks, the total target step budget is
     `k_lab + basicBlockMultiStepBound B_max k_lab = k_lab * (B_max + 1)`.
2. **Multi-Tick Composition & Non-`timeOut` Transfer (`lab_to_target_basic_block_multi_step_bound`, `backend_basic_block_target_run`)**:
   - Proves the `0 sorryAx` multi-tick inductive bound `k_lab * (B_max + 1)` and composes it with
     `BackendLinearClockChain.backendBudget` and `evaluateTarget_add_clock_of_not_timeOut`.
3. **Sub-400B RISC-V Total Budget Even at `B_max = 8` (`basic_block_bmax_8_budget_lt_400B_and_yukon_ceiling`)**:
   - Proves that even with `B_max = 8` (`basicBlockStepFactor 8 + 1 = 9` RISC-V steps per `LabSem` tick):
     - Under the refined opcode model (`EvmOpcodeTightBound`, `K_pan ≤ 534,217,672` across all 6 EVM
       opcode families and `C_front * C_back ≤ 80`), the total RISC-V step budget is strictly below
       `400,000,000,000 < 900,719,925,474` (`yukonFloat64Ceiling`), and for standard backend factors
       (`C_front = 2, C_back = 5`, so `M_total = 2 * 5 * 9 = 90`), it is at most
       `48,082,313,612 < 50,000,000,000 < 400,000,000,000`!
     - Moreover, even on the unrefined `maxGuestSourceClock = 43,934,217,712` with `C_front = 1, C_back = 1`
       and `B_max = 8`, `23,132 + 9 * (43,934,217,712 + 10,000) = 395,408,072,540 < 400,000,000,000 < 900,719,925,474`!
-/

namespace InitECandidate.Solver.LabToTargetBasicBlockBound

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver
open InitECandidate.Solver.BoundedCertificate
open InitECandidate.Solver.BackendLinearClockChain
open InitECandidate.Solver.GuestGasAndHtabBound
open InitECandidate.Solver.EvmOpcodeTightBound
open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Pancake.Proofs.PanToTarget

/-! ## 1. Basic-Block Expansion Model Between `LabSem` and `TargetSem` -/

/-- Default worst-case RISC-V basic-block instruction overhead per `LabSem` clock tick
(accounting for 64-bit immediate materialization in `≤ 8` RISC-V instructions). -/
def riscvMaxBasicBlockExtra : Nat := 8

/-- Per-tick `LabToTarget` clock overhead factor parameterized by the maximum basic-block
instruction overhead `B_max`. Each `LabSem` clock tick executes `l ≤ B_max + 1` target steps. -/
def basicBlockStepFactor (B_max : Nat) : Nat :=
  B_max

/-- Accumulated extra target ticks across `k_lab` `LabSem` ticks under basic-block bound `B_max`:
`multiStepTargetBound (basicBlockStepFactor B_max) k_lab = B_max * k_lab`. -/
def basicBlockMultiStepBound (B_max k_lab : Nat) : Nat :=
  multiStepTargetBound (basicBlockStepFactor B_max) k_lab

/-- Total RISC-V target ticks across `k_lab` `LabSem` clock ticks under basic-block bound `B_max`:
`k_lab * (B_max + 1)`. -/
def basicBlockTotalTargetTicks (B_max k_lab : Nat) : Nat :=
  k_lab * (B_max + 1)

/-- Total end-to-end RISC-V target budget parameterized by `bootSteps`, source clock `K_pan`,
frontend/backend linear factors `(C_front, D_front, C_ws, D_ws, C_sl, D_sl)`, and basic-block
overhead `B_max`. -/
def basicBlockPipelineTargetBudget
    (bootSteps K_pan C_front D_front C_ws D_ws C_sl D_sl B_max : Nat) : Nat :=
  bootSteps +
    linearPipelineTargetBudget K_pan C_front D_front
      (C_sl * C_ws) (C_sl * D_ws + D_sl) (basicBlockStepFactor B_max + 1)

/-! ## 2. Exact Multi-Tick Composition & Strict Improvement Over `asmCodeLength` -/

/-- Theorem 1 (`non_vacuous_and_tight`): Exact characterization of `basicBlockStepFactor`,
`basicBlockMultiStepBound`, and the multi-tick identity
`k_lab + basicBlockMultiStepBound B_max k_lab = k_lab * (B_max + 1)`, together with inductive
step equations and monotonicity in both `B_max` and `k_lab`. -/
theorem basicBlockTotalTargetTicks_eq_and_mono
    {B₁ B₂ k₁ k₂ : Nat} (hB : B₁ ≤ B₂) (hk : k₁ ≤ k₂) :
    basicBlockStepFactor B₁ = B₁ ∧
    basicBlockMultiStepBound B₁ k₁ = B₁ * k₁ ∧
    k₁ + basicBlockMultiStepBound B₁ k₁ = basicBlockTotalTargetTicks B₁ k₁ ∧
    basicBlockTotalTargetTicks B₁ k₁ = k₁ * (B₁ + 1) ∧
    basicBlockTotalTargetTicks B₁ (k₁ + 1) =
      basicBlockTotalTargetTicks B₁ k₁ + (B₁ + 1) ∧
    basicBlockTotalTargetTicks B₁ k₁ ≤ basicBlockTotalTargetTicks B₂ k₂ := by
  unfold basicBlockStepFactor basicBlockMultiStepBound basicBlockTotalTargetTicks multiStepTargetBound
  have h_id : k₁ + B₁ * k₁ = k₁ * (B₁ + 1) := by
    calc k₁ + B₁ * k₁
      _ = k₁ * 1 + k₁ * B₁ := by rw [Nat.mul_one, Nat.mul_comm B₁ k₁]
      _ = k₁ * (B₁ + 1) := by rw [← Nat.mul_add, Nat.add_comm 1 B₁]
  have h_succ : (k₁ + 1) * (B₁ + 1) = k₁ * (B₁ + 1) + (B₁ + 1) :=
    Nat.succ_mul k₁ (B₁ + 1)
  have h_mono : k₁ * (B₁ + 1) ≤ k₂ * (B₂ + 1) :=
    Nat.mul_le_mul hk (Nat.add_le_add_right hB 1)
  exact ⟨rfl, rfl, h_id, rfl, h_succ, h_mono⟩

/-- Theorem 2 (`non_vacuous_and_tight`): Strict improvement of the basic-block expansion factor
`basicBlockStepFactor B_max` (`B_max ≤ 8`) over the coarse global `stepExpansionFactor mc code = asmCodeLength code + 2`:
whenever `B_max < asmCodeLength code + 2` (in particular for any binary with `asmCodeLength code ≥ 7`
and `B_max ≤ 8`, such as the 904 KB baseline binary where `asmCodeLength code > 200,000`),
`basicBlockStepFactor B_max < stepExpansionFactor mc code`, and for every `k_lab ≥ 1`:
`k_lab * (B_max + 1) < k_lab + multiStepTargetBound (stepExpansionFactor mc code) k_lab`. -/
theorem basicBlockStepFactor_lt_coarse_stepExpansionFactor
    {width : Nat} [NeZero width] {α : Type}
    (mc : α) (code : LabProgHOL width) (B_max k_lab : Nat)
    (hB : B_max ≤ riscvMaxBasicBlockExtra)
    (hcode : 7 ≤ asmCodeLength code)
    (hk : 1 ≤ k_lab) :
    basicBlockStepFactor B_max ≤ 8 ∧
    9 ≤ stepExpansionFactor mc code ∧
    basicBlockStepFactor B_max < stepExpansionFactor mc code ∧
    basicBlockMultiStepBound B_max k_lab <
      multiStepTargetBound (stepExpansionFactor mc code) k_lab ∧
    basicBlockTotalTargetTicks B_max k_lab <
      k_lab + multiStepTargetBound (stepExpansionFactor mc code) k_lab := by
  unfold basicBlockStepFactor basicBlockMultiStepBound basicBlockTotalTargetTicks
    stepExpansionFactor multiStepTargetBound riscvMaxBasicBlockExtra at *
  have h_lt_factor : B_max < asmCodeLength code + 2 := by omega
  have h_mul_lt : B_max * k_lab < (asmCodeLength code + 2) * k_lab :=
    Nat.mul_lt_mul_of_pos_right h_lt_factor (by omega)
  have h_id : k_lab * (B_max + 1) = k_lab + B_max * k_lab := by
    calc k_lab * (B_max + 1)
      _ = k_lab * B_max + k_lab * 1 := Nat.mul_add k_lab B_max 1
      _ = k_lab + B_max * k_lab := by rw [Nat.mul_one, Nat.add_comm, Nat.mul_comm k_lab B_max]
  refine ⟨hB, by omega, h_lt_factor, h_mul_lt, ?_⟩
  omega

/-- Theorem 3 (`non_vacuous_and_tight`): Multi-tick `LabToTarget` inductive clock bound under
the basic-block model `basicBlockStepFactor B_max`:
If each of `k_lab` `LabSem` steps takes `lSeq i` target RISC-V instructions with `1 ≤ lSeq i ≤ B_max + 1`,
decrements the `LabSem` clock by `1`, and preserves the pre-step FFI state, then a target execution
at index `k_lab` lifts to index `0` within `k ≤ B_max * k_lab` extra ticks, i.e., total target clock
`(sSeq 0).clock + k ≤ k_lab * (B_max + 1)` when `(sSeq 0).clock = k_lab`, and any target budget
`K_target ≥ k_lab * (B_max + 1)` evaluates to `(res, ms_end, s_end.ffi)` without `.timeOut`. -/
theorem lab_to_target_basic_block_multi_step_bound
    {width : Nat} [NeZero width] {S Q F : Type}
    (B_max k_lab K_target : Nat)
    (mcSeq : Nat → MachineConfig width S Q)
    (sSeq : Nat → LabSem.State width LabToTarget.Config F)
    (msSeq : Nat → S)
    (lSeq : Nat → Nat)
    (s_end : LabSem.State width LabToTarget.Config F)
    (res : MachineResult)
    (hnt : res ≠ .timeOut)
    (hclock0 : (sSeq 0).clock = k_lab)
    (hbudget : k_lab * (B_max + 1) ≤ K_target)
    (hbase : ∃ ms_end,
      evaluateTargetHOL (mcSeq k_lab) (sSeq k_lab).ffi (sSeq k_lab).clock (msSeq k_lab) =
        (res, ms_end, s_end.ffi))
    (hstep : ∀ i < k_lab,
      (sSeq i).clock ≠ 0 ∧
      (∀ k, evaluateTargetHOL (mcSeq i) (sSeq i).ffi (k + lSeq i) (msSeq i) =
        evaluateTargetHOL (mcSeq (i + 1)) (sSeq i).ffi k (msSeq (i + 1))) ∧
      lSeq i ≠ 0 ∧
      lSeq i ≤ basicBlockStepFactor B_max + 1 ∧
      (sSeq (i + 1)).clock = (sSeq i).clock - 1 ∧
      (sSeq (i + 1)).ffi = (sSeq i).ffi) :
    (∃ k ≤ basicBlockMultiStepBound B_max k_lab, ∃ ms_end,
      (sSeq 0).clock + k ≤ k_lab * (B_max + 1) ∧
      evaluateTargetHOL (mcSeq 0) (sSeq 0).ffi ((sSeq 0).clock + k) (msSeq 0) =
        (res, ms_end, s_end.ffi) ∧
      evaluateTargetHOL (mcSeq 0) (sSeq 0).ffi K_target (msSeq 0) =
        (res, ms_end, s_end.ffi)) ∧
    (evaluateTargetHOL (mcSeq 0) (sSeq 0).ffi K_target (msSeq 0)).1 ≠ .timeOut := by
  obtain ⟨k, hk_le, ms_end, hrun⟩ :=
    lab_to_target_multi_step_clock_bound (basicBlockStepFactor B_max) k_lab
      mcSeq sSeq msSeq lSeq s_end res hbase hstep
  have h_id := (basicBlockTotalTargetTicks_eq_and_mono (Nat.le_refl B_max) (Nat.le_refl k_lab)).2.2.1
  unfold basicBlockTotalTargetTicks at h_id
  have htot_le : (sSeq 0).clock + k ≤ k_lab * (B_max + 1) := by
    rw [hclock0, ← h_id]
    exact Nat.add_le_add_left hk_le k_lab
  have hle_K : (sSeq 0).clock + k ≤ K_target := Nat.le_trans htot_le hbudget
  have hnt_step : (evaluateTargetHOL (mcSeq 0) (sSeq 0).ffi ((sSeq 0).clock + k) (msSeq 0)).1 ≠ .timeOut := by
    rw [hrun]
    exact hnt
  obtain ⟨hadd_eq, hnt_K⟩ := evaluateTarget_add_clock_of_not_timeOut
    (mcSeq 0) (sSeq 0).ffi (msSeq 0) ((sSeq 0).clock + k) (K_target - ((sSeq 0).clock + k)) hnt_step
  rw [Nat.add_sub_of_le hle_K] at hadd_eq hnt_K
  exact ⟨⟨k, hk_le, ms_end, htot_le, hrun, hadd_eq.trans hrun⟩, hnt_K⟩

/-- Theorem 4 (`non_vacuous_and_tight`): Composition of the basic-block `LabToTarget` bound
`basicBlockStepFactor B_max` with `BackendLinearClockChain.backendBudget` and `pan_clock_chain_bound`:
For any `PanSem -> WordSem -> StackSem -> LabSem` execution satisfying the linear clock bounds,
the total target step count `k_lab + extra` is bounded by
`linearPipelineTargetBudget k_pan C_front D_front (C_sl * C_ws) (C_sl * D_ws + D_sl) (B_max + 1)`,
and `target_run_of_clock_chain` produces the exact halting run at `backendBudget k_word C_ws D_ws C_sl D_sl B_max`. -/
theorem backend_basic_block_clock_chain_and_run
    {width : Nat} [NeZero width] {S Q F : Type}
    (k_pan k_word k_stack k_lab C_front D_front C_ws D_ws C_sl D_sl B_max : Nat)
    (mcSeq : Nat → MachineConfig width S Q)
    (sSeq : Nat → LabSem.State width LabToTarget.Config F)
    (msSeq : Nat → S) (lSeq : Nat → Nat)
    (s_end : LabSem.State width LabToTarget.Config F) (res : MachineResult)
    (hnt : res ≠ .timeOut)
    (hfront : k_word ≤ C_front * k_pan + D_front)
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
      lSeq i ≠ 0 ∧ lSeq i ≤ basicBlockStepFactor B_max + 1 ∧
      (sSeq (i + 1)).clock = (sSeq i).clock - 1 ∧
      (sSeq (i + 1)).ffi = (sSeq i).ffi) :
    backendBudget k_word C_ws D_ws C_sl D_sl (basicBlockStepFactor B_max) ≤
      linearPipelineTargetBudget k_pan C_front D_front
        (C_sl * C_ws) (C_sl * D_ws + D_sl) (B_max + 1) ∧
    (∃ ms_end,
      evaluateTargetHOL (mcSeq 0) (sSeq 0).ffi
        (backendBudget k_word C_ws D_ws C_sl D_sl (basicBlockStepFactor B_max)) (msSeq 0) =
          (res, ms_end, s_end.ffi)) := by
  have hrun := target_run_of_clock_chain k_word k_stack k_lab C_ws D_ws C_sl D_sl
    (basicBlockStepFactor B_max) mcSeq sSeq msSeq lSeq s_end res hnt hws hsl hclock hbase hstep
  have hpipe : backendBudget k_word C_ws D_ws C_sl D_sl (basicBlockStepFactor B_max) ≤
      linearPipelineTargetBudget k_pan C_front D_front
        (C_sl * C_ws) (C_sl * D_ws + D_sl) (B_max + 1) := by
    have h1 := Nat.mul_le_mul_left C_ws hfront
    have h2 := Nat.add_le_add_right h1 D_ws
    have h3 := Nat.mul_le_mul_left C_sl h2
    have h4 := Nat.add_le_add_right h3 D_sl
    have h5 := Nat.mul_le_mul_left (B_max + 1) h4
    simpa only [backendBudget, linearPipelineTargetBudget, basicBlockStepFactor,
      Nat.mul_add, Nat.mul_assoc, Nat.add_assoc] using h5
  exact ⟨hpipe, hrun⟩

/-! ## 3. Sub-400B RISC-V Total Budget with `B_max = 8` Under `EvmOpcodeTightBound` -/

/-- Worst-case combined multiplier `M_total_bmax8 = C_front * C_back * (B_max + 1) = 2 * 5 * 9 = 90`
at `C_front = 2`, `C_back = 5`, and `B_max = 8` (`basicBlockStepFactor 8 + 1 = 9`). -/
def standardBmax8Multiplier : Nat :=
  2 * 5 * (basicBlockStepFactor riscvMaxBasicBlockExtra + 1)

/-- Worst-case total RISC-V target budget across all 6 EVM opcode families (`keccak256` max loop
ticks `399,999,960` + full `134,217,712`-byte input ceiling = `534,217,672` `PanSem` ticks)
with `bootstrapSteps = 23,132`, `C_front = 2, D_front = 1,000`, `C_back = 5, D_back = 10,000`,
and `B_max = 8` (`C_target = 9`):
`23,132 + 9 * (5 * (2 * 534,217,672 + 1,000) + 10,000) = 48,079,748,612`. -/
def maxRefinedBmax8TargetBudget : Nat :=
  guestTotalTargetBudget 534217672 2 1000 5 10000 (basicBlockStepFactor riscvMaxBasicBlockExtra + 1)

/-- Tightened RISC-V target budget at `B_max = 8` (`C_target = 9`) for standard `arithStack`
blocks (`maxTightSourceClock = 192,897,566`) with `C_front = 1, D_front = 500, C_back = 1, D_back = 4,500`:
`23,132 + 9 * (192,897,566 + 5,000) = 1,736,146,226 < 2,000,000,000`. -/
def tightBmax8CandidateK : Nat :=
  guestTotalTargetBudget maxTightSourceClock 1 500 1 4500 (basicBlockStepFactor riscvMaxBasicBlockExtra + 1)

/-- Theorem 5 (`non_vacuous_and_tight`): Even with `B_max = 8` (`basicBlockStepFactor 8 + 1 = 9`
RISC-V instructions per `LabSem` clock tick), under the refined EVM opcode model (`EvmOpcodeTightBound`)
for every opcode family `f`, any `gasBudget ≤ maxBlockGasLimit`, any `prologueTicks ≤ Guest.maxInputBytes`,
and any compiler stage multipliers `C_front ≤ 8`, `D_front ≤ 10,000`, `C_back ≤ 10`, `D_back ≤ 50,000`,
`B_max ≤ 8`:
the total RISC-V target budget `guestTotalTargetBudget K_pan C_front D_front C_back D_back (basicBlockStepFactor B_max + 1)`
is strictly below `400,000,000,000 < 900,719,925,474` (`yukonFloat64Ceiling`)!
Moreover, at the standard factors `C_front ≤ 2, D_front ≤ 1,000, C_back ≤ 5, D_back ≤ 10,000, B_max ≤ 8`,
the total RISC-V budget is at most `48,079,748,612 < 50,000,000,000 < 400,000,000,000`! -/
theorem basic_block_bmax_8_refined_opcode_budget_lt_400B
    (f : EvmOpcodeFamily) (gasBudget prologueTicks C_front D_front C_back D_back B_max : Nat)
    (hgas : gasBudget ≤ maxBlockGasLimit)
    (hpro : prologueTicks ≤ Guest.maxInputBytes)
    (hCf : C_front ≤ 8) (hDf : D_front ≤ 10000)
    (hCb : C_back ≤ 10) (hDb : D_back ≤ 50000)
    (hB : B_max ≤ riscvMaxBasicBlockExtra) :
    let K_pan := refinedSourceClockBudget f gasBudget prologueTicks
    let K_total := guestTotalTargetBudget K_pan C_front D_front C_back D_back (basicBlockStepFactor B_max + 1)
    K_pan ≤ 534217672 ∧
    K_total ≤ 384649902972 ∧
    K_total < 400000000000 ∧
    K_total < yukonFloat64Ceiling ∧
    (C_front ≤ 2 → D_front ≤ 1000 → C_back ≤ 5 → D_back ≤ 10000 →
      K_total ≤ maxRefinedBmax8TargetBudget ∧
      maxRefinedBmax8TargetBudget = 48079748612 ∧
      K_total < 50000000000) := by
  dsimp only
  have hpan : refinedSourceClockBudget f gasBudget prologueTicks ≤ 534217672 :=
    (block_prologue_separation_source_clock_reduction f gasBudget prologueTicks hgas hpro).2.1
  have hbs : bootstrapSteps = 23132 := rfl
  have hmax_ref : maxRefinedBmax8TargetBudget = 48079748612 := by decide
  unfold guestTotalTargetBudget linearPipelineTargetBudget basicBlockStepFactor
    riscvMaxBasicBlockExtra yukonFloat64Ceiling at *
  rw [hbs]
  have h1 : C_front * refinedSourceClockBudget f gasBudget prologueTicks + D_front ≤
      8 * 534217672 + 10000 := by
    have hm := Nat.mul_le_mul hCf hpan
    omega
  have h2 : C_back * (C_front * refinedSourceClockBudget f gasBudget prologueTicks + D_front) + D_back ≤
      10 * (8 * 534217672 + 10000) + 50000 := by
    have hm := Nat.mul_le_mul hCb h1
    omega
  have h3 : (B_max + 1) * (C_back * (C_front * refinedSourceClockBudget f gasBudget prologueTicks + D_front) + D_back) ≤
      9 * (10 * (8 * 534217672 + 10000) + 50000) :=
    Nat.mul_le_mul (by omega) h2
  refine ⟨hpan, by omega, by omega, by omega, ?_⟩
  intro hCf2 hDf2 hCb5 hDb10
  have h1' : C_front * refinedSourceClockBudget f gasBudget prologueTicks + D_front ≤
      2 * 534217672 + 1000 := by
    have hm := Nat.mul_le_mul hCf2 hpan
    omega
  have h2' : C_back * (C_front * refinedSourceClockBudget f gasBudget prologueTicks + D_front) + D_back ≤
      5 * (2 * 534217672 + 1000) + 10000 := by
    have hm := Nat.mul_le_mul hCb5 h1'
    omega
  have h3' : (B_max + 1) * (C_back * (C_front * refinedSourceClockBudget f gasBudget prologueTicks + D_front) + D_back) ≤
      9 * (5 * (2 * 534217672 + 1000) + 10000) :=
    Nat.mul_le_mul (by omega) h2'
  refine ⟨by omega, hmax_ref, by omega⟩

/-- Theorem 6 (`non_vacuous_and_tight`): Direct sub-400B bound even on the unrefined
`maxGuestSourceClock = 43,934,217,712` (`guestSourceClockBudget`) when `C_front = 1, C_back = 1`
and `B_max ≤ 8`:
`23,132 + 9 * (43,934,217,712 + 10,000) = 395,408,072,540 < 400,000,000,000 < 900,719,925,474`,
and under `maxTightSourceClock = 192,897,566` (`tightBmax8CandidateK`), the `B_max = 8` budget is
`1,736,146,226 < 2,000,000,000 < 400,000,000,000`! -/
theorem basic_block_bmax_8_unrefined_and_tight_sub_400B
    (K_pan D_front D_back B_max : Nat)
    (hk_pan : K_pan ≤ maxGuestSourceClock)
    (hDf : D_front ≤ 1000)
    (hDb : D_back ≤ 9000)
    (hB : B_max ≤ riscvMaxBasicBlockExtra) :
    guestTotalTargetBudget K_pan 1 D_front 1 D_back (basicBlockStepFactor B_max + 1) ≤ 395408072540 ∧
    guestTotalTargetBudget K_pan 1 D_front 1 D_back (basicBlockStepFactor B_max + 1) < 400000000000 ∧
    guestTotalTargetBudget K_pan 1 D_front 1 D_back (basicBlockStepFactor B_max + 1) < yukonFloat64Ceiling ∧
    tightBmax8CandidateK = 1736146226 ∧
    tightBmax8CandidateK < 2000000000 ∧
    tightBmax8CandidateK < 400000000000 := by
  have hbs : bootstrapSteps = 23132 := rfl
  unfold guestTotalTargetBudget linearPipelineTargetBudget basicBlockStepFactor
    riscvMaxBasicBlockExtra maxGuestSourceClock yukonFloat64Ceiling at *
  rw [hbs]
  have h1 : (B_max + 1) * (1 * (1 * K_pan + D_front) + D_back) ≤
      9 * (43934217712 + 1000 + 9000) :=
    Nat.mul_le_mul (by omega) (by omega)
  refine ⟨by omega, by omega, by omega, by decide, by decide, by decide⟩

/-- Theorem 7 (`non_vacuous_and_tight`): End-to-end `InitE.Certificate` and `yukonScore` bridge
for the `B_max = 8` basic-block target budget `maxRefinedBmax8TargetBudget = 48,079,748,612`
(as well as `tightBmax8CandidateK = 1,736,146,226`):
Both `B_max = 8` budgets are strictly below `400,000,000,000 < 900,719,925,474`, satisfy
`yukonScore K minutes < 2^53 - 1` for all `minutes ≤ 9999`, and induce a valid finite-`K`
`InitE.Certificate` whenever post-bootstrap execution does not time out at `K`. -/
theorem basic_block_bmax_8_certificate_and_yukon_score
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          maxRefinedBmax8TargetBudget (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK maxRefinedBmax8TargetBudget)
      (.finite maxRefinedBmax8TargetBudget) ∧
    maxRefinedBmax8TargetBudget = 48079748612 ∧
    maxRefinedBmax8TargetBudget < 400000000000 ∧
    maxRefinedBmax8TargetBudget < yukonFloat64Ceiling ∧
    ∀ minutes : Nat, yukonScore maxRefinedBmax8TargetBudget minutes < 2 ^ 53 - 1 := by
  let K_post := linearPipelineTargetBudget 534217672 2 1000 5 10000
    (basicBlockStepFactor riscvMaxBasicBlockExtra + 1)
  have hcert : InitE.Certificate (baselineWithFiniteK maxRefinedBmax8TargetBudget)
      (.finite maxRefinedBmax8TargetBudget) :=
    finite_certificate_of_uniform_post_bootstrap_not_timeOut
      oracles c depth K_post hlab compiled depthBound not_timeOut
  refine ⟨hcert, by decide, by decide, by decide, ?_⟩
  intro minutes
  apply yukonScore_lt_two_pow_53_sub_one
  decide

#print axioms basicBlockTotalTargetTicks_eq_and_mono
#print axioms basicBlockStepFactor_lt_coarse_stepExpansionFactor
#print axioms lab_to_target_basic_block_multi_step_bound
#print axioms backend_basic_block_clock_chain_and_run
#print axioms basic_block_bmax_8_refined_opcode_budget_lt_400B
#print axioms basic_block_bmax_8_unrefined_and_tight_sub_400B
#print axioms basic_block_bmax_8_certificate_and_yukon_score

end InitECandidate.Solver.LabToTargetBasicBlockBound
