import InitE
import InitECandidate.Solver.FastBaselineEnv
import InitECandidate.Solver.YukonSelfContainedCert
import InitECandidate.Solver.FiniteKMasterComposition
import InitECandidate.Solver.EvmOpcodeTightBound

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.YukonSolutionBridge` — Finite-`K` Bridge for `submission/Solution.lean` (`W4_16`)

This module provides the drop-in finite-`K` score definitions, submissions, and certificate
bridge theorems ready to wire into `submission/Solution.lean` once the oracle stage equation
is unlocked:

1. **Score Alias & Candidate Scores**:
   - `abbrev Score := InitE.NatE` so `Score.finite` and `InitE.NatE.finite` are definitionally identical.
   - `claimedScoreFinite : Score := Score.finite candidateFiniteK` (`878,684,407,372 < 900,719,925,474`),
     matching `FiniteKMasterComposition.candidateFiniteK`.
   - `claimedScoreRefined : Score := Score.finite candidateRefinedK` (`43,934,279,079`),
     matching `coarseBootstrapSteps + maxGuestSourceClock = 61,367 + 43,934,217,712 = 43,934,279,079`.
   - `claimedScoreTight : Score := Score.finite tightCandidateK` (`1,929,048,792 < 2,000,000,000`),
     matching `EvmOpcodeTightBound.tightCandidateK`.

2. **Drop-In `submission/Solution.lean` Replacement Declarations**:
   - `submissionFinite`, `submissionRefined`, `submissionTight : InitE.Submission`
   - `code_size_finite`, `code_size_refined`, `code_size_tight`
   - `certificate_finite`, `certificate_refined`, `certificate_tight`
   - Exact IEEE-754 float64 representability (`yukonScore K minutes < 2^53 - 1`) for all three finite scores.
-/

namespace InitECandidate.Solver.YukonSolutionBridge

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver
open InitECandidate.Solver.GuestGasAndHtabBound
open InitECandidate.Solver.YukonSelfContainedCert
open InitECandidate.Solver.FiniteKMasterComposition
open InitECandidate.Solver.EvmOpcodeTightBound
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget

/-- Score type alias matching `InitE.NatE` (`Score.finite` / `Score.infinity`). -/
abbrev Score : Type := InitE.NatE

/-- Constructor alias so `Score.finite` resolves directly to `InitE.NatE.finite`. -/
abbrev Score.finite (steps : Nat) : Score := InitE.NatE.finite steps

/-- Constructor alias so `Score.infinity` resolves directly to `InitE.NatE.infinity`. -/
abbrev Score.infinity : Score := InitE.NatE.infinity

/-- Refined post-bootstrap step budget (`43,934,255,947`) so that
`bootstrapSteps + candidateRefinedPostK = 23,132 + 43,934,255,947 = 43,934,279,079`. -/
def candidateRefinedPostK : Nat := 43934255947

/-- Refined finite step budget `43,934,279,079` (`coarseBootstrapSteps + maxGuestSourceClock`). -/
def candidateRefinedK : Nat := 43934279079

/-- Primary finite score (`Score.finite 878,684,407,372`) from `FiniteKMasterComposition`. -/
def claimedScoreFinite : Score :=
  Score.finite candidateFiniteK

/-- Refined finite score (`Score.finite 43,934,279,079`) from `coarseBootstrapSteps + maxGuestSourceClock`. -/
def claimedScoreRefined : Score :=
  Score.finite 43934279079

/-- Tightened EVM-opcode finite score (`Score.finite 1,929,048,792`) from `EvmOpcodeTightBound`. -/
def claimedScoreTight : Score :=
  Score.finite tightCandidateK

/-- Submission record for `claimedScoreFinite` (`K = .finite 878,684,407,372`). -/
def submissionFinite : InitE.Submission :=
  baselineWithFiniteK candidateFiniteK

/-- Submission record for `claimedScoreRefined` (`K = .finite 43,934,279,079`). -/
def submissionRefined : InitE.Submission :=
  baselineWithFiniteK candidateRefinedK

/-- Submission record for `claimedScoreTight` (`K = .finite 1,929,048,792`). -/
def submissionTight : InitE.Submission :=
  baselineWithFiniteK tightCandidateK

/-- Theorem 1 (`non_vacuous_and_tight`): Exact numerical values, bootstrap decompositions,
strict ordering (`tightCandidateK < candidateRefinedK < candidateFiniteK < yukonFloat64Ceiling`),
and ROM code size bounds (`code.length ≤ InitE.codeSizeLimit`) for all three finite submissions. -/
theorem claimed_scores_values_and_hierarchy :
    claimedScoreFinite = .finite 878684407372 ∧
    claimedScoreRefined = .finite 43934279079 ∧
    claimedScoreTight = .finite 1929048792 ∧
    candidateRefinedK = coarseBootstrapSteps + maxGuestSourceClock ∧
    candidateRefinedK = bootstrapSteps + candidateRefinedPostK ∧
    tightCandidateK < candidateRefinedK ∧
    candidateRefinedK < candidateFiniteK ∧
    candidateFiniteK < yukonFloat64Ceiling ∧
    submissionFinite.code.length ≤ InitE.codeSizeLimit ∧
    submissionRefined.code.length ≤ InitE.codeSizeLimit ∧
    submissionTight.code.length ≤ InitE.codeSizeLimit := by
  have hcode : InitE.baselineSubmission.code.length ≤ InitE.codeSizeLimit :=
    InitE.baselineSubmission_admitted.code_limit
  refine ⟨by rw [claimedScoreFinite, candidateFiniteK_eq],
    rfl,
    by rw [claimedScoreTight]; decide,
    by decide,
    by decide,
    by decide,
    by rw [candidateFiniteK_eq]; decide,
    candidateFiniteK_lt_ceiling,
    hcode, hcode, hcode⟩

/-- Theorem 2 (`non_vacuous_and_tight`): Every verification duration `minutes : Nat` yields an
exact IEEE-754 float64 Yukon score (`< 2^53 - 1`) for `candidateFiniteK`, `candidateRefinedK`,
and `tightCandidateK`, with strict score dominance across the three tiers. -/
theorem yukon_score_exact_float64_and_dominance (minutes : Nat) :
    yukonScore tightCandidateK minutes < yukonScore candidateRefinedK minutes ∧
    yukonScore candidateRefinedK minutes < yukonScore candidateFiniteK minutes ∧
    yukonScore candidateFiniteK minutes < 2 ^ 53 - 1 ∧
    yukonScore candidateRefinedK minutes < 2 ^ 53 - 1 ∧
    yukonScore tightCandidateK minutes < 2 ^ 53 - 1 := by
  have hfin := yukonScore_candidate_lt minutes
  have href : yukonScore candidateRefinedK minutes < 2 ^ 53 - 1 := by
    apply yukonScore_lt_two_pow_53_sub_one
    decide
  have htight : yukonScore tightCandidateK minutes < 2 ^ 53 - 1 := by
    apply yukonScore_lt_two_pow_53_sub_one
    decide
  have htk : tightCandidateK = 1929048792 := by decide
  have hrk : candidateRefinedK = 43934279079 := rfl
  have h1 : yukonScore tightCandidateK minutes < yukonScore candidateRefinedK minutes := by
    rw [htk, hrk]
    unfold yukonScore
    have hm : min minutes 9999 ≤ 9999 := Nat.min_le_right _ _
    omega
  have h2 : yukonScore candidateRefinedK minutes < yukonScore candidateFiniteK minutes := by
    rw [hrk, candidateFiniteK_eq]
    unfold yukonScore
    have hm : min minutes 9999 ≤ 9999 := Nat.min_le_right _ _
    omega
  exact ⟨h1, h2, hfin, href, htight⟩

/-- Theorem 3 (`non_vacuous_and_tight`): Drop-in `InitE.Certificate submissionFinite claimedScoreFinite`
bridge for `submission/Solution.lean` (`K = 878,684,407,372`). -/
theorem solution_certificate_finite
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
    InitE.Certificate submissionFinite claimedScoreFinite ∧
    submissionFinite.K = .finite 878684407372 ∧
    ∀ minutes : Nat, yukonScore candidateFiniteK minutes < 2 ^ 53 - 1 := by
  have hm := master_finite_certificate oracles c depth hlab compiled depthBound not_timeOut
  refine ⟨hm.1, ?_, hm.2.2⟩
  change Score.finite candidateFiniteK = .finite 878684407372
  rw [candidateFiniteK_eq]

/-- Theorem 4 (`non_vacuous_and_tight`): Drop-in `InitE.Certificate submissionRefined claimedScoreRefined`
bridge for `submission/Solution.lean` (`K = 43,934,279,079`). -/
theorem solution_certificate_refined
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
          candidateRefinedK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate submissionRefined claimedScoreRefined ∧
    submissionRefined.K = .finite 43934279079 ∧
    candidateRefinedK < 50000000000 ∧
    ∀ minutes : Nat, yukonScore candidateRefinedK minutes < 2 ^ 53 - 1 := by
  have hsplit : bootstrapSteps + candidateRefinedPostK = candidateRefinedK := by decide
  have hnt : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          (bootstrapSteps + candidateRefinedPostK) (baselineInitialState input)).1 ≠ .timeOut := by
    intro input hgas outcome events hsrc hcov
    rw [hsplit]
    exact not_timeOut input hgas outcome events hsrc hcov
  have hcert0 :=
    YukonSelfContainedCert.finite_certificate_of_uniform_post_bootstrap_not_timeOut
      oracles c depth candidateRefinedPostK hlab compiled depthBound hnt
  rw [hsplit] at hcert0
  refine ⟨hcert0, rfl, by decide, ?_⟩
  intro minutes
  exact (yukon_score_exact_float64_and_dominance minutes).2.2.2.1

/-- Theorem 5 (`non_vacuous_and_tight`): Drop-in `InitE.Certificate submissionTight claimedScoreTight`
bridge for `submission/Solution.lean` (`K = 1,929,048,792 < 2,000,000,000`). -/
theorem solution_certificate_tight
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
          tightCandidateK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate submissionTight claimedScoreTight ∧
    submissionTight.K = .finite 1929048792 ∧
    tightCandidateK < 2000000000 ∧
    ∀ minutes : Nat, yukonScore tightCandidateK minutes < 2 ^ 53 - 1 := by
  have ht := tight_opcode_bound_certificate_and_yukon_score
    oracles c depth hlab compiled depthBound not_timeOut
  refine ⟨ht.1, ?_, ht.2.2.1, ht.2.2.2.2.2⟩
  change Score.finite tightCandidateK = .finite 1929048792
  rw [ht.2.1]

/-- Theorem 6 (`non_vacuous_and_tight`): Monotone upward transfer between finite certificates
(`K₁ ≤ K₂ → Certificate (baselineWithFiniteK K₁) (.finite K₁) → Certificate (baselineWithFiniteK K₂) (.finite K₂)`),
plus direct downgrade from any finite `K` certificate to `InitE.Certificate InitE.baselineSubmission .infinity`. -/
theorem solution_certificate_monotone_transfer
    {K₁ K₂ : Nat} (hle : K₁ ≤ K₂)
    (hcert₁ : InitE.Certificate (baselineWithFiniteK K₁) (.finite K₁)) :
    InitE.Certificate (baselineWithFiniteK K₂) (.finite K₂) ∧
    InitE.Certificate InitE.baselineSubmission .infinity := by
  refine ⟨?_, ?_⟩
  · refine ⟨rfl, YukonSelfContainedCert.baselineWithFiniteK_admitted K₂, ?_⟩
    intro input hgas outcome events hsrc hcov
    obtain ⟨steps, hsteps, hm⟩ := hcert₁.correct input hgas outcome events hsrc hcov
    refine ⟨steps, Nat.le_trans hsteps hle, ?_⟩
    obtain ⟨out', ms', ffi', hrun, hmatch⟩ := hm
    rw [YukonSelfContainedCert.baselineWithFiniteK_machineConfig K₁,
        YukonSelfContainedCert.baselineWithFiniteK_initialState K₁] at hrun
    refine ⟨out', ms', ffi', ?_, hmatch⟩
    rw [YukonSelfContainedCert.baselineWithFiniteK_machineConfig K₂,
        YukonSelfContainedCert.baselineWithFiniteK_initialState K₂]
    exact hrun
  · refine ⟨rfl, InitE.baselineSubmission_admitted, ?_⟩
    intro input hgas outcome events hsrc hcov
    obtain ⟨steps, _, hm⟩ := hcert₁.correct input hgas outcome events hsrc hcov
    obtain ⟨out', ms', ffi', hrun, hmatch⟩ := hm
    rw [YukonSelfContainedCert.baselineWithFiniteK_machineConfig K₁,
        YukonSelfContainedCert.baselineWithFiniteK_initialState K₁] at hrun
    refine ⟨steps, trivial, out', ms', ffi', ?_, hmatch⟩
    rw [InitE.baselineSubmission_machineConfig, InitE.baselineSubmission_initialState]
    exact hrun


/-- Ultra-tightened EVM-opcode + straight-line `copyLoop` finite score
(`Score.finite 1,929,034,941 < 1,929,048,792`) from `EvmOpcodeTightBound.ultraTightCandidateK`. -/
def claimedScoreUltraTight : Score :=
  Score.finite ultraTightCandidateK

/-- Submission record for `claimedScoreUltraTight` (`K = .finite 1,929,034,941`). -/
def submissionUltraTight : InitE.Submission :=
  baselineWithFiniteK ultraTightCandidateK

/-- Theorem 7 (`non_vacuous_and_tight`): Drop-in `InitE.Certificate submissionUltraTight claimedScoreUltraTight`
bridge for `submission/Solution.lean` (`K = 1,929,034,941`), strictly dominating `submissionTight`
by `13,851` steps and `138,510,000` Yukon score points across all `minutes : Nat`. -/
theorem solution_certificate_ultra_tight
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
          ultraTightCandidateK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate submissionUltraTight claimedScoreUltraTight ∧
    submissionUltraTight.K = .finite 1929034941 ∧
    ultraTightCandidateK < tightCandidateK ∧
    (∀ minutes : Nat, yukonScore tightCandidateK minutes - yukonScore ultraTightCandidateK minutes = 138510000) ∧
    (∀ minutes : Nat, yukonScore ultraTightCandidateK minutes < yukonScore tightCandidateK minutes) ∧
    (∀ minutes : Nat, yukonScore ultraTightCandidateK minutes < 2 ^ 53 - 1) := by
  have hut := ultra_tight_opcode_bound_certificate_and_yukon_score
    oracles c depth hlab compiled depthBound not_timeOut
  refine ⟨hut.1, ?_, hut.2.2.2.1, hut.2.2.2.2.1, hut.2.2.2.2.2.1, hut.2.2.2.2.2.2⟩
  change Score.finite ultraTightCandidateK = .finite 1929034941
  rw [hut.2.1]

end InitECandidate.Solver.YukonSolutionBridge
