import InitECandidate.Solver.FourPassClockIsometryChain
import InitECandidate.Solver.StackRemoveBodyClockBound
import InitECandidate.Solver.SelfContainedBasicBlockBridge

set_option autoImplicit false

/-!
Six-pass reduced budget bridge. The slope assumptions C_sr = 1 and C_cl = 3
are explicit; no Guest-wide semantic instance is inferred from arithmetic.
The imported basic-block convention counts B_max EXTRA steps, hence eight
TOTAL steps means B_max <= 7. B_max <= 8 alone gives nine total steps.
Certificates retain the uniform target non-timeout obligation, rather than
claiming it follows from clock-neutral straight-line bodies.
-/
namespace InitECandidate.Solver.SixPassPipelineReducedBridge
open InitE Flapjack
open InitECandidate.Solver
open FourPassClockIsometryChain
open SelfContainedMasterK
open SelfContainedBoundedCertificate
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target

/-- Reduced multiplicative coefficient, before target instruction expansion. -/
def sixPassSlope (c_sr c_cl : Nat) : Nat :=
  StackNamesExactClockIso.C_sn *
    (c_sr * (C_ws * (C_lw * (c_cl * PanToCrepExactClockIso.C_pc))))

def sixPassReducedPostK : Nat := 8 * (3 * (refinedSourceClock + pipeOffset))
def sixPassReducedK : Nat := bootstrapSteps + sixPassReducedPostK

/-- The four exact isometries leave only the two remaining slopes. -/
theorem six_pass_slope_reduction (c_sr c_cl : Nat) :
    sixPassSlope c_sr c_cl = c_sr * c_cl := by
  exact (four_pass_multiplicative_isometry c_cl 0 0 c_sr 0 0).2.2.2.2.2.2.2.2.2.1

/-- Neutral StackRemove and triple CrepToLoop give exactly slope three. -/
theorem six_pass_slope_three (c_sr c_cl : Nat)
    (hsr : c_sr = 1) (hcl : c_cl = 3) : sixPassSlope c_sr c_cl = 3 := by
  rw [six_pass_slope_reduction, hsr, hcl]

/-- Exact affine offset, including both nonzero middle offsets. -/
theorem six_pass_affine_exact (d_cl d_ws d_sr k : Nat) :
    frontToLabAffine 3 d_cl d_ws 1 d_sr k = 3 * k + (d_cl + d_ws + d_sr) := by
  have h := (four_pass_multiplicative_isometry 3 d_cl d_ws 1 d_sr k).2.2.2.2.2.2.2.2.2.2.1
  simpa [LoopWordStackExactClockIso.affine] using h

/-- Connecting the admitted StackRemove fragment to the four-pass slope result.
This states clock neutrality, not whole-program target termination. -/
theorem neutral_body_and_reduced_slope {w : Nat} [NeZero w]
    (jump : Bool) (bounds : BitVec w × BitVec w) (ptr : Nat) (p : HolProg w)
    (h : StackRemoveBodyClockBound.Body jump p) :
    clockNeutralHOL (StackRemove.comp jump bounds ptr p) ∧ sixPassSlope 1 3 = 3 :=
  ⟨StackRemoveBodyClockBound.comp_neutral jump bounds ptr p h,
    six_pass_slope_three 1 3 rfl rfl⟩

/-- Exact reduced post-bootstrap budget. -/
theorem reduced_post_exact : sixPassReducedPostK = 11029660656 := by decide

/-- Exact total budget, with the verified bootstrap included. -/
theorem reduced_budget_exact : sixPassReducedK = 11029683788 := by
  rw [sixPassReducedK, bootstrapSteps_eq, reduced_post_exact]

/-- The saturated source/offset/instruction budget is exactly the claimed K. -/
theorem reduced_budget_formula :
    sixPassReducedK = 23132 + 8 * 3 * (459564194 + 5000) := by
  rw [reduced_budget_exact]

/-- Eight total instructions corresponds to seven extra in the imported bridge. -/
theorem basic_block_eight_total (B_extra k : Nat) (h : B_extra ≤ 7) :
    SelfContainedBasicBlockBridge.basicBlockTotalTargetTicks B_extra k ≤ 8 * k := by
  unfold SelfContainedBasicBlockBridge.basicBlockTotalTargetTicks
  calc
    k * (B_extra + 1) ≤ k * 8 := Nat.mul_le_mul_left k (by omega)
    _ = 8 * k := Nat.mul_comm _ _

/-- Literal B_extra <= 8 gives nine total instructions, not eight. -/
theorem basic_block_eight_extra_corrected :
    bootstrapSteps + SelfContainedBasicBlockBridge.basicBlockTotalTargetTicks 8
      (3 * (refinedSourceClock + pipeOffset)) = 12408391370 := by
  rw [bootstrapSteps_eq]
  decide

/-- The source clock, aggregate affine offset and total instruction factor compose. -/
theorem reduced_budget_bound (k d B_total : Nat)
    (hk : k ≤ refinedSourceClock) (hd : d ≤ pipeOffset) (hB : B_total ≤ 8) :
    bootstrapSteps + B_total * (sixPassSlope 1 3 * (k + d)) ≤ sixPassReducedK := by
  rw [six_pass_slope_three 1 3 rfl rfl]
  exact Nat.add_le_add_left
    (Nat.mul_le_mul hB (Nat.mul_le_mul_left 3 (Nat.add_le_add hk hd))) _

/-- Imported basic-block budget specializes exactly to the reduced six-pass K. -/
theorem reduced_basic_block_budget_exact :
    SelfContainedBasicBlockBridge.basicBlockPipelineTargetBudget
      bootstrapSteps refinedSourceClock 3 (3 * pipeOffset) 1 0 1 0 7 =
      sixPassReducedK := by
  rw [reduced_budget_exact, bootstrapSteps_eq]
  decide

/-- The finite bound lies more than 81 times below the Yukon ceiling. -/
theorem reduced_ceiling_margin :
    81 * sixPassReducedK < 900719925474 ∧
    sixPassReducedK < 900719925474 ∧ 0 < sixPassReducedK := by
  rw [reduced_budget_exact]
  decide

/-- All minute fields remain strictly below the float64 infinity score. -/
theorem reduced_score_representable (minutes : Nat) :
    yukonScore sixPassReducedK minutes < 2 ^ 53 - 1 := by
  apply yukonScore_lt_two_pow_53_sub_one
  have h := reduced_ceiling_margin.2.1
  omega

/-- Certificate bridge at the reduced budget; uniform non-timeout remains explicit. -/
theorem reduced_finite_certificate
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        sixPassReducedK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK sixPassReducedK) (.finite sixPassReducedK) :=
  finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth sixPassReducedPostK hlab compiled depthBound not_timeOut

/-- A reduced finite certificate also certifies the baseline infinity claim. -/
theorem reduced_baseline_compatible
    (finite : InitE.Certificate (baselineWithFiniteK sixPassReducedK) (.finite sixPassReducedK)) :
    InitE.Certificate SelfContainedEndToEndCert.submission .infinity := by
  refine ⟨rfl, InitE.baselineSubmission_admitted, ?_⟩
  intro input gas outcome events source covered
  obtain ⟨steps, _, execution⟩ := finite.correct input gas outcome events source covered
  exact ⟨steps, trivial,
    (SelfContainedEndToEndCert.matchingExecutionAt_with_score InitE.baselineSubmission
      (.finite sixPassReducedK) input outcome events steps).mp execution⟩

#print axioms reduced_finite_certificate
#print axioms reduced_baseline_compatible
#print axioms neutral_body_and_reduced_slope
end InitECandidate.Solver.SixPassPipelineReducedBridge
