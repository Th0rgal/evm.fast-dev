import InitECandidate.Solver.VerifySpeedBound
import InitECandidate.Solver.GuestGasAndHtabBound
import InitECandidate.Solver.BoundedCertificate

set_option autoImplicit false

/-!
# Finite-`K` master composition

`candidateFiniteK = bootstrapSteps + linearPipelineTargetBudget maxGuestSourceClock 2 1000 5 10000 2`
`= 23,132 + 878,684,384,240 = 878,684,407,372 < 900,719,925,474`.
-/

namespace InitECandidate.Solver.FiniteKMasterComposition

open Classical
open InitE
open InitECandidate.Proofs
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open InitECandidate.Solver
open InitECandidate.Solver.GuestGasAndHtabBound
open InitECandidate.Solver.BoundedCertificate

/-- Post-bootstrap target budget at the maximal guest source clock. -/
def candidatePostK : Nat :=
  linearPipelineTargetBudget maxGuestSourceClock 2 1000 5 10000 2

/-- The explicit finite budget candidate. -/
def candidateFiniteK : Nat :=
  guestTotalTargetBudget maxGuestSourceClock 2 1000 5 10000 2

theorem candidateFiniteK_eq_bootstrap_add : candidateFiniteK = bootstrapSteps + candidatePostK := rfl

theorem candidatePostK_eq : candidatePostK = 878684384240 := by
  unfold candidatePostK linearPipelineTargetBudget maxGuestSourceClock; rfl

theorem candidateFiniteK_eq : candidateFiniteK = 878684407372 := by
  rw [candidateFiniteK_eq_bootstrap_add, InitE.bootstrapSteps_eq, candidatePostK_eq]

/-- Strict crossing of the Yukon float64 ceiling. -/
theorem candidateFiniteK_lt_ceiling : candidateFiniteK < yukonFloat64Ceiling :=
  guestTotalTargetBudget_lt_yukon_ceiling_of_le_max _ 2 1000 5 10000 2
    (Nat.le_refl _) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem candidateFiniteK_le_900719925474 : candidateFiniteK ≤ 900719925474 := by
  rw [candidateFiniteK_eq]; decide

theorem candidateFiniteK_le_900719925473 : candidateFiniteK ≤ 900719925473 := by
  rw [candidateFiniteK_eq]; decide

/-- Every verification time yields an exactly representable Yukon score. -/
theorem yukonScore_candidate_lt (minutes : Nat) :
    yukonScore candidateFiniteK minutes < 2 ^ 53 - 1 :=
  yukonScore_lt_two_pow_53_sub_one candidateFiniteK_le_900719925473

/-- Every guest-source clock and pipeline factor admitted by the gas/htab bound
fits below `candidateFiniteK` (so `candidateFiniteK` is the tight envelope). -/
theorem guest_budget_le_candidate
    (K_pan C_front D_front C_back D_back C_target : Nat)
    (hk : K_pan ≤ maxGuestSourceClock)
    (hCf : C_front ≤ 2) (hDf : D_front ≤ 1000)
    (hCb : C_back ≤ 5) (hDb : D_back ≤ 10000) (hCt : C_target ≤ 2) :
    guestTotalTargetBudget K_pan C_front D_front C_back D_back C_target ≤ candidateFiniteK := by
  unfold candidateFiniteK guestTotalTargetBudget linearPipelineTargetBudget
  apply Nat.add_le_add_left
  have h1 : C_front * K_pan + D_front ≤ 2 * maxGuestSourceClock + 1000 :=
    Nat.add_le_add (Nat.mul_le_mul hCf hk) hDf
  have h2 : C_back * (C_front * K_pan + D_front) + D_back ≤
      5 * (2 * maxGuestSourceClock + 1000) + 10000 :=
    Nat.add_le_add (Nat.mul_le_mul hCb h1) hDb
  exact Nat.mul_le_mul hCt h2

/-- Master assembly: once the per-pass (PanToWord / StackToLab / Target) witnesses
are plugged in as the uniform non-`timeOut` obligation at `candidateFiniteK`,
the finite certificate is discharged. -/
theorem master_finite_certificate
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
          candidateFiniteK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK candidateFiniteK) (.finite candidateFiniteK) ∧
      candidateFiniteK < yukonFloat64Ceiling ∧
      ∀ minutes, yukonScore candidateFiniteK minutes < 2 ^ 53 - 1 := by
  refine ⟨?_, candidateFiniteK_lt_ceiling, yukonScore_candidate_lt⟩
  exact finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth candidatePostK hlab compiled depthBound not_timeOut


end InitECandidate.Solver.FiniteKMasterComposition
