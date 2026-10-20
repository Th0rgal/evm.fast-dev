import InitECandidate.Solver.GuestMemoryAndAccountOpcodeBounds
import InitECandidate.Solver.StackRemoveStoreConstsZeroBridge

set_option autoImplicit false

/-!
EIP-7825 arithmetic envelope, conditional on transaction-local clusters.
The opcode/probe costs are the imported hand-transcribed model, not a
Guest-wide semantic bound. Factor six is an explicit target expansion
hypothesis (C_cmp = 4 alone does not establish it). Compiler correctness and
uniform target non-timeout remain explicit certificate obligations.
The reduced six-pass K uses a different source envelope and cannot be
inferred from the per-transaction source ceiling comparison.
-/
namespace InitECandidate.Solver.PerTxEip7825TargetMasterK
open InitE Flapjack
open InitECandidate.Solver
open SelfContainedMasterK SelfContainedBoundedCertificate SelfContainedSixPassMaster
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target

 def perTxSourceK : Nat := 20_436_764_234
 def perTxSixPassTargetK : Nat := 23_132 + 6 * perTxSourceK

theorem per_tx_probes_bridge (c w m : Nat) (h : 21 * c + w ≤ m) :
    80 * (c * (w + c)) ≤ m * m :=
  GuestMemoryAndAccountOpcodeBounds.per_tx_probes c w m h

theorem per_tx_split_bridge (ms : List Nat)
    (hcap : ∀ m ∈ ms, m ≤ 167772) (hsum : ms.sum ≤ 2000000) :
    (ms.map (fun m => m * m)).sum ≤ 335544000000 :=
  GuestMemoryAndAccountOpcodeBounds.per_tx_split ms hcap hsum

/-- Floor division is the integral consequence of the scaled probe bound. -/
theorem per_tx_collision_ticks (ms : List Nat)
    (hcap : ∀ m ∈ ms, m ≤ 167772) (hsum : ms.sum ≤ 2000000) :
    GuestSloadExactProbeTicks.pEff * ((ms.map (fun m => m * m)).sum / 80)
      ≤ 16777200000 := by
  have h := per_tx_split_bridge ms hcap hsum
  have hp : GuestSloadExactProbeTicks.pEff = 4 := rfl
  rw [hp]
  omega

theorem per_tx_push31_exact :
    prologueTicks + 18 * GuestEvmStepOpcodeBounds.gasCap = 3659564234 := by decide

theorem per_tx_source_exact :
    prologueTicks + 18 * GuestEvmStepOpcodeBounds.gasCap + 16777200000 = perTxSourceK :=
  GuestMemoryAndAccountOpcodeBounds.per_tx_kPan.2.1

theorem per_tx_source_below_imported_ceiling :
    perTxSourceK < GuestEvmStepOpcodeBounds.maxGuestSourceClock :=
  GuestMemoryAndAccountOpcodeBounds.per_tx_kPan.2.2

/-- The supplied module actually defines this ceiling as 43,934,217,712. -/
theorem imported_source_ceiling_exact :
    GuestEvmStepOpcodeBounds.maxGuestSourceClock = 43934217712 := rfl

/-- The stricter ceiling requested in the task also covers this envelope. -/
theorem per_tx_source_below_requested_ceiling : perTxSourceK < 43914839586 := by decide

theorem per_tx_combined_bound (ms : List Nat)
    (hcap : ∀ m ∈ ms, m ≤ 167772) (hsum : ms.sum ≤ 2000000) :
    prologueTicks + 18 * GuestEvmStepOpcodeBounds.gasCap +
      GuestSloadExactProbeTicks.pEff * ((ms.map (fun m => m * m)).sum / 80)
      ≤ perTxSourceK := by
  have h := per_tx_collision_ticks ms hcap hsum
  have he := per_tx_source_exact
  omega

theorem per_tx_neutral_slope : sixPassSlope 1 3 = 3 :=
  StackRemoveStoreConstsZeroBridge.neutral_six_pass_slope

theorem per_tx_neutral_affine (d_cl d_ws clock : Nat) :
    sixPassAffine d_cl d_ws 0 clock = 3 * clock + (d_cl + d_ws) :=
  StackRemoveStoreConstsZeroBridge.neutral_six_pass_affine d_cl d_ws clock

theorem per_tx_compiled_allowance_zero {width : Nat} [NeZero width] (ctx : Spt Nat)
    (p : HolLoopProg width) (labels : Nat × Nat) :
    StackRemoveStoreConstsZeroBridge.storeConstsAllowance
      (LoopToWord.compHOL ctx p labels).1 = 0 :=
  StackRemoveStoreConstsZeroBridge.compiled_allowance_zero ctx p labels

/-- An actual store-constant payload witnesses that the allowance is not constant zero. -/
theorem per_tx_allowance_tight {α : Type} (a b c d : Nat) (ws : List (Bool × α)) :
    StackRemoveStoreConstsZeroBridge.storeConstsAllowance
      (.storeConsts a b c d ws) = ws.length := rfl

theorem reduced_six_pass_exact : sixPassReducedK = 11029683788 :=
  StackRemoveStoreConstsZeroBridge.neutral_six_pass_budget

/-- Arithmetic does not identify the two distinct target budgets. -/
theorem reduced_strictly_below_per_tx : sixPassReducedK < perTxSixPassTargetK := by
  rw [reduced_six_pass_exact]
  decide

theorem per_tx_target_exact : perTxSixPassTargetK = 122620608536 := by decide

theorem per_tx_target_formula :
    perTxSixPassTargetK = bootstrapSteps + 6 * perTxSourceK := by
  rw [bootstrapSteps_eq]; rfl

/-- Target expansion, including offsets, must fit the explicit factor-six premise. -/
theorem per_tx_target_bound (sourceTicks targetPost : Nat)
    (hs : sourceTicks ≤ perTxSourceK) (ht : targetPost ≤ 6 * sourceTicks) :
    bootstrapSteps + targetPost ≤ perTxSixPassTargetK := by
  rw [per_tx_target_formula]
  exact Nat.add_le_add_left (le_trans ht (Nat.mul_le_mul_left 6 hs)) _

theorem per_tx_target_saturated :
    bootstrapSteps + 6 * perTxSourceK = perTxSixPassTargetK :=
  per_tx_target_formula.symm

/-- Exact rational form of a margin strictly greater than 7.3. -/
theorem per_tx_yukon_margin :
    73 * perTxSixPassTargetK < 10 * 900719925474 ∧
      perTxSixPassTargetK < 900719925474 ∧ 0 < perTxSixPassTargetK := by decide

theorem per_tx_score_representable (minutes : Nat) :
    yukonScore perTxSixPassTargetK minutes < 2 ^ 53 - 1 := by
  apply yukonScore_lt_two_pow_53_sub_one
  have h := per_tx_yukon_margin.2.1
  omega

/-- Certificate bridge at the factor-six target budget; no semantic obligation is dropped. -/
theorem per_tx_finite_certificate
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
        perTxSixPassTargetK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK perTxSixPassTargetK) (.finite perTxSixPassTargetK) := by
  have cert := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (6 * perTxSourceK) hlab compiled depthBound
    (by simpa only [← per_tx_target_formula] using not_timeOut)
  simpa only [← per_tx_target_formula] using cert

theorem per_tx_certificate_literal
    (certificate : InitE.Certificate (baselineWithFiniteK perTxSixPassTargetK)
      (.finite perTxSixPassTargetK)) :
    InitE.Certificate (baselineWithFiniteK 122620608536) (.finite 122620608536) := by
  simpa only [per_tx_target_exact] using certificate

theorem reduced_certificate_literal
    (certificate : InitE.Certificate (baselineWithFiniteK sixPassReducedK)
      (.finite sixPassReducedK)) :
    InitE.Certificate (baselineWithFiniteK 11029683788) (.finite 11029683788) :=
  StackRemoveStoreConstsZeroBridge.reduced_certificate_at_literal certificate

#print axioms per_tx_probes_bridge
#print axioms per_tx_split_bridge
#print axioms per_tx_collision_ticks
#print axioms per_tx_push31_exact
#print axioms per_tx_source_exact
#print axioms per_tx_source_below_imported_ceiling
#print axioms imported_source_ceiling_exact
#print axioms per_tx_source_below_requested_ceiling
#print axioms per_tx_combined_bound
#print axioms per_tx_neutral_slope
#print axioms per_tx_neutral_affine
#print axioms per_tx_compiled_allowance_zero
#print axioms per_tx_allowance_tight
#print axioms reduced_six_pass_exact
#print axioms reduced_strictly_below_per_tx
#print axioms per_tx_target_exact
#print axioms per_tx_target_formula
#print axioms per_tx_target_bound
#print axioms per_tx_target_saturated
#print axioms per_tx_yukon_margin
#print axioms per_tx_score_representable
#print axioms per_tx_finite_certificate
#print axioms per_tx_certificate_literal
#print axioms reduced_certificate_literal

end InitECandidate.Solver.PerTxEip7825TargetMasterK
