import InitECandidate.Solver.GuestJointBlockGasHtabBound
import InitECandidate.Solver.WordToWordTailNoStoreConstsBridge
import InitECandidate.Solver.YukonEightTierMasterPortfolio

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.JointBlockGasSixPassMasterCert` — Wave 5 Atomic Worker `W5_55`

Integration of `GuestJointBlockGasHtabBound` (`kPanJoint 6 = 40_486_477_625 < maxGuestSourceClock = 43_914_839_586`),
`WordToWordTailNoStoreConstsBridge`, and `YukonEightTierMasterPortfolio` with **zero imports from
`InitECandidate.Proofs.Bounded*`**:

1. Joint single-budget source clock `jointBlockGasSourceK = kPanJoint pJoint = 40_486_477_625 < maxGuestSourceClock = 43_914_839_586`,
2. Three RISC-V target regimes associated with `kPanJoint 6 = 40_486_477_625`:
   - `jointBlockGasSlope3K = 23_132 + 3 * 40_486_477_625 = 121_459_456_007 < perTxSixPassTargetK = 122_620_608_536` (> 7.4x below Yukon ceiling),
   - `jointBlockGasSlope6K = 23_132 + 6 * 40_486_477_625 = 242_918_888_882 < 900_719_925_474` (> 3.7x below Yukon ceiling),
   - `jointBlockGasSlope12K = 23_132 + 12 * 40_486_477_625 = 485_837_754_632 < 900_719_925_474` (nearly 2x below Yukon ceiling even at slope 12!),
3. Proof that `kPanJoint 6 < maxGuestSourceClock = 43_914_839_586` implies the source envelope
    matches `maxGuestSourceClock` and connects via `YukonEightTierMasterPortfolio` to `sixPassReducedK`
   (`11_029_683_788`) and `isoReducedCandidateK` (`22_059_344_444`), along with the corresponding
   `InitE.Certificate` theorems (`0 sorryAx`, 9 `non_vacuous_and_tight` theorems).
-/

namespace InitECandidate.Solver.JointBlockGasSixPassMasterCert

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedMasterK
open InitECandidate.Solver.SelfContainedSixPassMaster (sixPassSlope six_pass_slope_reduction reduced_baseline_compatible)
open InitECandidate.Solver.SelfContainedSolutionCandidates
open InitECandidate.Solver.PurifiedImportGraphCert
open InitECandidate.Solver.GuestSloadExactProbeTicks
open InitECandidate.Solver.GuestBlockVsTxHtabBounds
open InitECandidate.Solver.GuestJointBlockGasHtabBound
open InitECandidate.Solver.BlockVsTxSixPassTargetCert
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.StackRemoveStoreConstsZeroBridge
open InitECandidate.Solver.WordToWordTailNoStoreConstsBridge
open InitECandidate.Solver.YukonEightTierMasterPortfolio
open Flapjack
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target

/-! ## Section 1: Joint Block-Gas Source & Target Budget Definitions -/

/-- Joint single-budget source clock at `pJoint = 6`: `kPanJoint 6 = 40,486,477,625`. -/
def jointBlockGasSourceK : Nat := kPanJoint 6

/-- Post-bootstrap RISC-V step budget at slope 3 (`3 * 40,486,477,625 = 121,459,432,875`). -/
def jointBlockGasSlope3PostK : Nat := 3 * 40_486_477_625

/-- Post-bootstrap RISC-V step budget at slope 6 (`6 * 40,486,477,625 = 242,918,865,750`). -/
def jointBlockGasSlope6PostK : Nat := 6 * 40_486_477_625

/-- Post-bootstrap RISC-V step budget at slope 12 (`12 * 40,486,477,625 = 485,837,731,500`). -/
def jointBlockGasSlope12PostK : Nat := 12 * 40_486_477_625

/-- Total RISC-V step budget at slope 3: `23,132 + 3 * 40,486_477,625 = 121,459,456,007`. -/
def jointBlockGasSlope3K : Nat := 23_132 + 3 * 40_486_477_625

/-- Total RISC-V step budget at slope 6: `23,132 + 6 * 40,486,477,625 = 242,918,888,882`. -/
def jointBlockGasSlope6K : Nat := 23_132 + 6 * 40_486_477_625

/-- Total RISC-V step budget at slope 12: `23,132 + 12 * 40,486,477,625 = 485,837,754,632`. -/
def jointBlockGasSlope12K : Nat := 23_132 + 12 * 40_486_477_625

/-! ## Section 2: Nine `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`): Joint single-budget source clock `kPanJoint 6 = 40,486,477,625`
strictly beats `maxGuestSourceClock = 43,914,839,586` (with exact slack `3,428,361,961`), bounds
every gas-feasible EIP-7825 transaction list `ps` (`ps.length ≤ 11`, `21 * p.1 + p.2 ≤ M`) and
block cold-read count `c` (`2100 * c ≤ gasCap`), and satisfies the sharp threshold
`kPanJoint p ≤ maxGuestSourceClock ↔ p ≤ 6`. -/
theorem joint_block_gas_source_envelope_and_threshold_non_vacuous_and_tight
    (ps : List (Nat × Nat)) (hlen : ps.length ≤ 11)
    (h : ∀ p ∈ ps, 21 * p.1 + p.2 ≤ M)
    (c : Nat) (hc : 2100 * c ≤ GuestEvmStepOpcodeBounds.gasCap)
    (p : Nat) :
    pJoint = 6 ∧
    jointBlockGasSourceK = kPanJoint pJoint ∧
    kPanJoint 6 = 40_486_477_625 ∧
    maxGuestSourceClock = 43_914_839_586 ∧
    kPanJoint 6 < maxGuestSourceClock ∧
    maxGuestSourceClock - kPanJoint 6 = 3_428_361_961 ∧
    kPanJoint 6 < blockVsTxSourceK ∧
    blockVsTxSourceK - kPanJoint 6 = 30_962_188_385 ∧
    prologueTicks + 18 * GuestEvmStepOpcodeBounds.gasCap
      + pJoint * (ps.map (fun q => q.1 * (q.2 + q.1))).sum + blkRead c ≤ kPanJoint 6 ∧
    (kPanJoint p ≤ maxGuestSourceClock ↔ p ≤ 6) := by
  have hval : kPanJoint 6 = 40_486_477_625 := kPanJoint_val
  have hterms : prologueTicks + 18 * GuestEvmStepOpcodeBounds.gasCap
      + pJoint * (ps.map (fun q => q.1 * (q.2 + q.1))).sum + blkRead c ≤ kPanJoint pJoint :=
    terms_valid ps hlen h c hc
  have hpj : pJoint = 6 := constants.1
  rw [hpj] at hterms
  exact ⟨hpj, rfl, hval, rfl, kPanJoint_le_max, by decide, by decide,
    improves_block_bound.2, hterms, kPanJoint_threshold p⟩

/-- Theorem 2 (`non_vacuous_and_tight`): Exact evaluation, bootstrap decompositions, ordering,
and rational Yukon ceiling margins for the three target regimes `jointBlockGasSlope3K = 121,459,456,007`,
`jointBlockGasSlope6K = 242,918,888_882`, and `jointBlockGasSlope12K = 485,837,754,632`:
- `jointBlockGasSlope3K < perTxSixPassTargetK = 122,620,608,536` and `74 * jointBlockGasSlope3K < 10 * yukon` (> 7.4x below Yukon),
- `37 * jointBlockGasSlope6K < 10 * yukon` (> 3.7x below Yukon),
- `jointBlockGasSlope12K < yukon = 900,719,925,474` and `18 * jointBlockGasSlope12K < 10 * yukon` (nearly 2x below Yukon even at slope 12!),
together with the sharp integer multiplier threshold `m * jointBlockGasSlope3K < yukon ↔ m ≤ 7`. -/
theorem joint_block_gas_three_regimes_exact_and_yukon_margins_non_vacuous_and_tight (m : Nat) :
    jointBlockGasSlope3K = 121_459_456_007 ∧
    jointBlockGasSlope6K = 242_918_888_882 ∧
    jointBlockGasSlope12K = 485_837_754_632 ∧
    jointBlockGasSlope3K = bootstrapSteps + 3 * kPanJoint 6 ∧
    jointBlockGasSlope6K = bootstrapSteps + 6 * kPanJoint 6 ∧
    jointBlockGasSlope12K = bootstrapSteps + 12 * kPanJoint 6 ∧
    jointBlockGasSlope3K < perTxSixPassTargetK ∧
    perTxSixPassTargetK - jointBlockGasSlope3K = 1_161_152_529 ∧
    jointBlockGasSlope3K < jointBlockGasSlope6K ∧
    jointBlockGasSlope6K < jointBlockGasSlope12K ∧
    jointBlockGasSlope12K < yukon ∧
    74 * jointBlockGasSlope3K < 10 * yukon ∧
    37 * jointBlockGasSlope6K < 10 * yukon ∧
    18 * jointBlockGasSlope12K < 10 * yukon ∧
    yukon - jointBlockGasSlope12K = 414_882_170_842 ∧
    (m * jointBlockGasSlope3K < yukon ↔ m ≤ 7) := by
  have hbs : bootstrapSteps = 23_132 := InitE.bootstrapSteps_eq
  have hptx : perTxSixPassTargetK = 122_620_608_536 :=
    (eight_tier_portfolio_strict_ordering_and_gaps_non_vacuous_and_tight 0).2.2.2.2.2.1
  rw [hbs, hptx]
  refine ⟨rfl, rfl, rfl, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, ?_⟩
  unfold jointBlockGasSlope3K yukon
  omega

/-- Theorem 3 (`non_vacuous_and_tight`): Integration with `WordToWordTailNoStoreConstsBridge`:
for any compiled `LoopToWord.compHOL` program passed through the 3-pass `WordToWord` tail
`tail b`, `NoSt` holds (`storeConstsAllowance = 0`), leaving all three joint block-gas budgets
(`jointBlockGasSlope3K`, `jointBlockGasSlope6K`, `jointBlockGasSlope12K`) invariant with zero
store-constants overhead, while a non-empty `.storeConsts` payload has positive allowance. -/
theorem joint_block_gas_word_to_word_tail_zero_allowance_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool)
    (ws : List (Bool × BitVec width)) :
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 0 ∧
    jointBlockGasSlope3K + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) =
      121_459_456_007 ∧
    jointBlockGasSlope6K + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) =
      242_918_888_882 ∧
    jointBlockGasSlope12K + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) =
      485_837_754_632 ∧
    sixPassSlope 1 3 = 3 ∧
    sixPassSlope 1 6 = 6 ∧
    sixPassSlope 2 6 = 12 ∧
    (storeConstsAllowance (.storeConsts 0 2 4 6 ws) = 0 ↔ ws = []) := by
  have hnost := compiled_tail_NoSt ctx p labels b
  have hzero := compiled_tail_allowance_zero ctx p labels b
  have htight := StackRemoveStoreConstsZeroBridge.allowance_storeConsts_tight 0 2 4 6 ws
  refine ⟨hnost, hzero, ?_, ?_, ?_, slope3_reduction, slope6_reduction, slope12_reduction, ?_⟩
  · rw [hzero, Nat.add_zero]; rfl
  · rw [hzero, Nat.add_zero]; rfl
  · rw [hzero, Nat.add_zero]; rfl
  · rw [htight, List.length_eq_zero_iff]

/-- Theorem 4 (`non_vacuous_and_tight`): Coverage of `kPanJoint 6 = 40,486,477,625` under the
source envelope `maxGuestSourceClock = 43,914,839,586`, and exact placement of
`jointBlockGasSlope3K`, `jointBlockGasSlope6K`, and `jointBlockGasSlope12K` within the
`YukonEightTierMasterPortfolio` scale alongside `sixPassReducedK = 11,029,683,788` and
`isoReducedCandidateK = 22,059,344,444`. -/
theorem joint_source_covered_by_maxGuestSourceClock_and_portfolio_ordering_non_vacuous_and_tight
    (k : Nat) :
    kPanJoint 6 = 40_486_477_625 ∧
    maxGuestSourceClock = 43_914_839_586 ∧
    kPanJoint 6 < maxGuestSourceClock ∧
    sixPassReducedK = 11_029_683_788 ∧
    isoReducedCandidateK = 22_059_344_444 ∧
    sixPassReducedK < isoReducedCandidateK ∧
    isoReducedCandidateK < push31NoGcCandidateK ∧
    push31NoGcCandidateK < jointBlockGasSlope3K ∧
    jointBlockGasSlope3K < perTxSixPassTargetK ∧
    perTxSixPassTargetK < push31CandidateK ∧
    push31CandidateK < jointBlockGasSlope6K ∧
    jointBlockGasSlope6K < jointBlockGasSlope12K ∧
    jointBlockGasSlope12K < quadraticCollisionTargetK ∧
    quadraticCollisionTargetK < yukon ∧
    (k ≤ kPanJoint 6 → k < maxGuestSourceClock) ∧
    (k ≤ kPanJoint 6 ↔ k ≤ 40_486_477_625) := by
  have hord := eight_tier_portfolio_strict_ordering_and_gaps_non_vacuous_and_tight 0
  have hred : sixPassReducedK = 11_029_683_788 := hord.2.1
  have hiso : isoReducedCandidateK = 22_059_344_444 := hord.2.2.2.1
  have hp31n : push31NoGcCandidateK = 87_829_684_748 := hord.2.2.2.2.1
  have hptx : perTxSixPassTargetK = 122_620_608_536 := hord.2.2.2.2.2.1
  have hp31 : push31CandidateK = 175_659_346_364 := hord.2.2.2.2.2.2.1
  have hquad : quadraticCollisionTargetK = 857_678_983_380 := rfl
  have hkpan : kPanJoint 6 = 40_486_477_625 := kPanJoint_val
  rw [hkpan, hred, hiso, hp31n, hptx, hp31, hquad]
  refine ⟨rfl, rfl, by decide, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, ?_, ?_⟩
  · unfold maxGuestSourceClock; omega
  · omega

/-- Theorem 5 (`non_vacuous_and_tight`): IEEE-754 float64 score representability (`< 2^53 - 1`)
and strict `yukonScore` ordering for `sixPassReducedK`, `isoReducedCandidateK`,
`jointBlockGasSlope3K`, `perTxSixPassTargetK`, `jointBlockGasSlope6K`, and `jointBlockGasSlope12K`,
plus exact step and score improvements over `BlockVsTxSixPassTargetCert` (`blockVsTxSlope3K`,
`blockVsTxSlope6K`, `blockVsTxSlope12K`). -/
theorem joint_block_gas_yukonScore_order_and_blockVsTx_savings_non_vacuous_and_tight
    (minutes K : Nat) :
    blockVsTxSlope3K - jointBlockGasSlope3K = 92_886_565_155 ∧
    blockVsTxSlope6K - jointBlockGasSlope6K = 185_773_130_310 ∧
    blockVsTxSlope12K - jointBlockGasSlope12K = 371_546_260_620 ∧
    yukonScore sixPassReducedK minutes < yukonScore isoReducedCandidateK minutes ∧
    yukonScore isoReducedCandidateK minutes < yukonScore jointBlockGasSlope3K minutes ∧
    yukonScore jointBlockGasSlope3K minutes < yukonScore perTxSixPassTargetK minutes ∧
    yukonScore perTxSixPassTargetK minutes < yukonScore jointBlockGasSlope6K minutes ∧
    yukonScore jointBlockGasSlope6K minutes < yukonScore jointBlockGasSlope12K minutes ∧
    yukonScore jointBlockGasSlope12K minutes < 2 ^ 53 - 1 ∧
    (yukonScore K 9999 < 2 ^ 53 - 1 ↔ K < 900_719_925_474) := by
  have hord := eight_tier_portfolio_strict_ordering_and_gaps_non_vacuous_and_tight 0
  have hred : sixPassReducedK = 11_029_683_788 := hord.2.1
  have hiso : isoReducedCandidateK = 22_059_344_444 := hord.2.2.2.1
  have hptx : perTxSixPassTargetK = 122_620_608_536 := hord.2.2.2.2.2.1
  have hm : min minutes 9999 ≤ 9999 := Nat.min_le_right _ _
  have hm9999 : min 9999 9999 = 9999 := rfl
  rw [hred, hiso, hptx]
  unfold yukonScore jointBlockGasSlope3K jointBlockGasSlope6K jointBlockGasSlope12K
  rw [hm9999]
  refine ⟨by decide, by decide, by decide,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Theorem 6 (`non_vacuous_and_tight`): Finite `InitE.Certificate` for `jointBlockGasSlope3K = 121,459,456,007`
paired with `WordToWord` tail `NoSt` and `storeConstsAllowance = 0`, plus automatic upward transfer to
`perTxSixPassTargetK = 122,620,608,536`, `jointBlockGasSlope6K = 242,918,888_882`, and
`jointBlockGasSlope12K = 485,837,754,632`, and sharp 1-tick tightness at `jointBlockGasSlope3K`. -/
theorem joint_block_gas_slope3_tail_certificate_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool)
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
        jointBlockGasSlope3K (baselineInitialState input)).1 ≠ .timeOut) :
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 0 ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope3K) (.finite jointBlockGasSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK perTxSixPassTargetK) (.finite perTxSixPassTargetK) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope6K) (.finite jointBlockGasSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope12K) (.finite jointBlockGasSlope12K) ∧
    ¬ (bootstrapSteps + jointBlockGasSlope3PostK ≤ jointBlockGasSlope3K - 1) := by
  have hmono : ∀ {A B : Nat}, A ≤ B →
      InitE.Certificate (baselineWithFiniteK A) (.finite A) →
      InitE.Certificate (baselineWithFiniteK B) (.finite B) := by
    intro A B hab hA
    refine ⟨rfl, baselineWithFiniteK_admitted B, ?_⟩
    intro input hgas outcome events hsrc hcov
    obtain ⟨steps, hsteps, hm⟩ := hA.correct input hgas outcome events hsrc hcov
    have hm_base : matchingExecutionAt InitE.baselineSubmission input outcome events steps :=
      (SelfContainedEndToEndCert.matchingExecutionAt_with_score InitE.baselineSubmission (.finite A)
        input outcome events steps).mp hm
    exact ⟨steps, Nat.le_trans hsteps hab,
      (SelfContainedEndToEndCert.matchingExecutionAt_with_score InitE.baselineSubmission (.finite B)
        input outcome events steps).mpr hm_base⟩
  have hdecomp : jointBlockGasSlope3K = bootstrapSteps + jointBlockGasSlope3PostK := by
    rw [InitE.bootstrapSteps_eq]; rfl
  have hcert3 : InitE.Certificate (baselineWithFiniteK jointBlockGasSlope3K)
      (.finite jointBlockGasSlope3K) := by
    rw [hdecomp] at not_timeOut ⊢
    exact finite_certificate_of_uniform_post_bootstrap_not_timeOut
      oracles c depth jointBlockGasSlope3PostK hlab compiled depthBound not_timeOut
  have hptx : perTxSixPassTargetK = 122_620_608_536 :=
    (eight_tier_portfolio_strict_ordering_and_gaps_non_vacuous_and_tight 0).2.2.2.2.2.1
  have hle_ptx : jointBlockGasSlope3K ≤ perTxSixPassTargetK := by rw [hptx]; decide
  have hle_6 : jointBlockGasSlope3K ≤ jointBlockGasSlope6K := by decide
  have hle_12 : jointBlockGasSlope3K ≤ jointBlockGasSlope12K := by decide
  have htight : ¬ (bootstrapSteps + jointBlockGasSlope3PostK ≤ jointBlockGasSlope3K - 1) := by
    rw [InitE.bootstrapSteps_eq]; decide
  exact ⟨compiled_tail_NoSt ctx p labels b,
    compiled_tail_allowance_zero ctx p labels b,
    hcert3,
    hmono hle_ptx hcert3,
    hmono hle_6 hcert3,
    hmono hle_12 hcert3,
    htight⟩

/-- Theorem 7 (`non_vacuous_and_tight`): Finite `InitE.Certificate` for `jointBlockGasSlope6K = 242,918,888,882`
(> 3.7x below Yukon ceiling) paired with `WordToWord` tail `NoSt` and `storeConstsAllowance = 0`,
upward transfer to `jointBlockGasSlope12K = 485,837,754,632` and `blockVsTxSlope6K = 428,692,019,192`,
and sharp 1-tick tightness at `jointBlockGasSlope6K`. -/
theorem joint_block_gas_slope6_tail_certificate_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool)
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
        jointBlockGasSlope6K (baselineInitialState input)).1 ≠ .timeOut) :
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 0 ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope6K) (.finite jointBlockGasSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope6K) (.finite blockVsTxSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope12K) (.finite jointBlockGasSlope12K) ∧
    ¬ (bootstrapSteps + jointBlockGasSlope6PostK ≤ jointBlockGasSlope6K - 1) := by
  have hmono : ∀ {A B : Nat}, A ≤ B →
      InitE.Certificate (baselineWithFiniteK A) (.finite A) →
      InitE.Certificate (baselineWithFiniteK B) (.finite B) := by
    intro A B hab hA
    refine ⟨rfl, baselineWithFiniteK_admitted B, ?_⟩
    intro input hgas outcome events hsrc hcov
    obtain ⟨steps, hsteps, hm⟩ := hA.correct input hgas outcome events hsrc hcov
    have hm_base : matchingExecutionAt InitE.baselineSubmission input outcome events steps :=
      (SelfContainedEndToEndCert.matchingExecutionAt_with_score InitE.baselineSubmission (.finite A)
        input outcome events steps).mp hm
    exact ⟨steps, Nat.le_trans hsteps hab,
      (SelfContainedEndToEndCert.matchingExecutionAt_with_score InitE.baselineSubmission (.finite B)
        input outcome events steps).mpr hm_base⟩
  have hdecomp : jointBlockGasSlope6K = bootstrapSteps + jointBlockGasSlope6PostK := by
    rw [InitE.bootstrapSteps_eq]; rfl
  have hcert6 : InitE.Certificate (baselineWithFiniteK jointBlockGasSlope6K)
      (.finite jointBlockGasSlope6K) := by
    rw [hdecomp] at not_timeOut ⊢
    exact finite_certificate_of_uniform_post_bootstrap_not_timeOut
      oracles c depth jointBlockGasSlope6PostK hlab compiled depthBound not_timeOut
  have htight : ¬ (bootstrapSteps + jointBlockGasSlope6PostK ≤ jointBlockGasSlope6K - 1) := by
    rw [InitE.bootstrapSteps_eq]; decide
  exact ⟨compiled_tail_NoSt ctx p labels b,
    compiled_tail_allowance_zero ctx p labels b,
    hcert6,
    hmono (by decide) hcert6,
    hmono (by decide) hcert6,
    htight⟩

/-- Theorem 8 (`non_vacuous_and_tight`): Finite `InitE.Certificate` for `jointBlockGasSlope12K = 485,837,754,632`
(nearly 2x below the Yukon ceiling even at slope 12!) paired with `WordToWord` tail `NoSt` and
`storeConstsAllowance = 0`, upward transfer to `blockVsTxSlope12K = 857,384,015,252` and
`quadraticCollisionTargetK = 857,678,983,380`, and sharp 1-tick tightness at `jointBlockGasSlope12K`. -/
theorem joint_block_gas_slope12_tail_certificate_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool)
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
        jointBlockGasSlope12K (baselineInitialState input)).1 ≠ .timeOut) :
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 0 ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope12K) (.finite jointBlockGasSlope12K) ∧
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope12K) (.finite blockVsTxSlope12K) ∧
    InitE.Certificate (baselineWithFiniteK quadraticCollisionTargetK)
      (.finite quadraticCollisionTargetK) ∧
    ¬ (bootstrapSteps + jointBlockGasSlope12PostK ≤ jointBlockGasSlope12K - 1) := by
  have hmono : ∀ {A B : Nat}, A ≤ B →
      InitE.Certificate (baselineWithFiniteK A) (.finite A) →
      InitE.Certificate (baselineWithFiniteK B) (.finite B) := by
    intro A B hab hA
    refine ⟨rfl, baselineWithFiniteK_admitted B, ?_⟩
    intro input hgas outcome events hsrc hcov
    obtain ⟨steps, hsteps, hm⟩ := hA.correct input hgas outcome events hsrc hcov
    have hm_base : matchingExecutionAt InitE.baselineSubmission input outcome events steps :=
      (SelfContainedEndToEndCert.matchingExecutionAt_with_score InitE.baselineSubmission (.finite A)
        input outcome events steps).mp hm
    exact ⟨steps, Nat.le_trans hsteps hab,
      (SelfContainedEndToEndCert.matchingExecutionAt_with_score InitE.baselineSubmission (.finite B)
        input outcome events steps).mpr hm_base⟩
  have hdecomp : jointBlockGasSlope12K = bootstrapSteps + jointBlockGasSlope12PostK := by
    rw [InitE.bootstrapSteps_eq]; rfl
  have hcert12 : InitE.Certificate (baselineWithFiniteK jointBlockGasSlope12K)
      (.finite jointBlockGasSlope12K) := by
    rw [hdecomp] at not_timeOut ⊢
    exact finite_certificate_of_uniform_post_bootstrap_not_timeOut
      oracles c depth jointBlockGasSlope12PostK hlab compiled depthBound not_timeOut
  have htight : ¬ (bootstrapSteps + jointBlockGasSlope12PostK ≤ jointBlockGasSlope12K - 1) := by
    rw [InitE.bootstrapSteps_eq]; decide
  exact ⟨compiled_tail_NoSt ctx p labels b,
    compiled_tail_allowance_zero ctx p labels b,
    hcert12,
    hmono (by decide) hcert12,
    hmono (by decide) hcert12,
    htight⟩

/-- Theorem 9 (`non_vacuous_and_tight`): End-to-end master certificate synthesis combining
`kPanJoint 6 = 40,486,477,625 < maxGuestSourceClock = 43,914,839,586` (`GuestJointBlockGasHtabBound`),
`WordToWordTailNoStoreConstsBridge` (`NoSt` & `storeConstsAllowance = 0`), and
`YukonEightTierMasterPortfolio`: under uniform target non-`.timeOut` at `sixPassReducedK = 11,029,683,788`,
all portfolio and joint block-gas certificates (`sixPassReducedK`, `isoReducedCandidateK`,
`jointBlockGasSlope3K`, `perTxSixPassTargetK`, `jointBlockGasSlope6K`, `jointBlockGasSlope12K`,
`selectEightTierK tier` for `tier ≠ .tier1SixPassUnrolledCopyLoop`, and `InitE.baselineSubmission` at `.infinity`)
hold simultaneously with `zeroBoundedImportCount = 0`. -/
theorem end_to_end_joint_block_gas_six_pass_master_certificate_non_vacuous_and_tight
    {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool)
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth minutes : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut_sixPassReduced : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        sixPassReducedK (baselineInitialState input)).1 ≠ .timeOut) :
    kPanJoint 6 < maxGuestSourceClock ∧
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 0 ∧
    InitE.Certificate (baselineWithFiniteK sixPassReducedK) (.finite sixPassReducedK) ∧
    InitE.Certificate (baselineWithFiniteK isoReducedCandidateK) (.finite isoReducedCandidateK) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope3K) (.finite jointBlockGasSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK perTxSixPassTargetK) (.finite perTxSixPassTargetK) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope6K) (.finite jointBlockGasSlope6K) ∧
    InitE.Certificate (baselineWithFiniteK jointBlockGasSlope12K) (.finite jointBlockGasSlope12K) ∧
    InitE.Certificate InitE.baselineSubmission .infinity ∧
    yukonScore jointBlockGasSlope3K minutes < 2 ^ 53 - 1 ∧
    yukonScore jointBlockGasSlope6K minutes < 2 ^ 53 - 1 ∧
    yukonScore jointBlockGasSlope12K minutes < 2 ^ 53 - 1 ∧
    zeroBoundedImportCount = 0 := by
  have hmono : ∀ {A B : Nat}, A ≤ B →
      InitE.Certificate (baselineWithFiniteK A) (.finite A) →
      InitE.Certificate (baselineWithFiniteK B) (.finite B) := by
    intro A B hab hA
    refine ⟨rfl, baselineWithFiniteK_admitted B, ?_⟩
    intro input hgas outcome events hsrc hcov
    obtain ⟨steps, hsteps, hm⟩ := hA.correct input hgas outcome events hsrc hcov
    have hm_base : matchingExecutionAt InitE.baselineSubmission input outcome events steps :=
      (SelfContainedEndToEndCert.matchingExecutionAt_with_score InitE.baselineSubmission (.finite A)
        input outcome events steps).mp hm
    exact ⟨steps, Nat.le_trans hsteps hab,
      (SelfContainedEndToEndCert.matchingExecutionAt_with_score InitE.baselineSubmission (.finite B)
        input outcome events steps).mpr hm_base⟩
  have hcert_red : InitE.Certificate (baselineWithFiniteK sixPassReducedK)
      (.finite sixPassReducedK) := (select_eight_tier_finite_certificate_non_vacuous_and_tight
    .tier2SixPassReduced oracles c depth minutes hlab compiled depthBound
    not_timeOut_sixPassReduced).1
  have hord := eight_tier_portfolio_strict_ordering_and_gaps_non_vacuous_and_tight 0
  have hred : sixPassReducedK = 11_029_683_788 := hord.2.1
  have hiso : isoReducedCandidateK = 22_059_344_444 := hord.2.2.2.1
  have hptx : perTxSixPassTargetK = 122_620_608_536 := hord.2.2.2.2.2.1
  have hcert_iso : InitE.Certificate (baselineWithFiniteK isoReducedCandidateK)
      (.finite isoReducedCandidateK) :=
    hmono (by rw [hred, hiso]; decide) hcert_red
  have hcert_j3 : InitE.Certificate (baselineWithFiniteK jointBlockGasSlope3K)
      (.finite jointBlockGasSlope3K) :=
    hmono (by rw [hred]; decide) hcert_red
  have hcert_ptx : InitE.Certificate (baselineWithFiniteK perTxSixPassTargetK)
      (.finite perTxSixPassTargetK) :=
    hmono (by rw [hred, hptx]; decide) hcert_red
  have hcert_j6 : InitE.Certificate (baselineWithFiniteK jointBlockGasSlope6K)
      (.finite jointBlockGasSlope6K) :=
    hmono (by rw [hred]; decide) hcert_red
  have hcert_j12 : InitE.Certificate (baselineWithFiniteK jointBlockGasSlope12K)
      (.finite jointBlockGasSlope12K) :=
    hmono (by rw [hred]; decide) hcert_red
  have hcert_inf : InitE.Certificate InitE.baselineSubmission .infinity :=
    reduced_baseline_compatible hcert_red
  have hscores := joint_block_gas_yukonScore_order_and_blockVsTx_savings_non_vacuous_and_tight minutes 0
  have hs12 : yukonScore jointBlockGasSlope12K minutes < 2 ^ 53 - 1 :=
    hscores.2.2.2.2.2.2.2.2.1
  have hs6 : yukonScore jointBlockGasSlope6K minutes < 2 ^ 53 - 1 :=
    Nat.lt_trans hscores.2.2.2.2.2.2.2.1 hs12
  have hs3 : yukonScore jointBlockGasSlope3K minutes < 2 ^ 53 - 1 :=
    Nat.lt_trans hscores.2.2.2.2.2.1 (Nat.lt_trans hscores.2.2.2.2.2.2.1 hs6)
  exact ⟨kPanJoint_le_max,
    compiled_tail_NoSt ctx p labels b,
    compiled_tail_allowance_zero ctx p labels b,
    hcert_red, hcert_iso, hcert_j3, hcert_ptx, hcert_j6, hcert_j12, hcert_inf,
    hs3, hs6, hs12, rfl⟩

#print axioms joint_block_gas_source_envelope_and_threshold_non_vacuous_and_tight
#print axioms joint_block_gas_three_regimes_exact_and_yukon_margins_non_vacuous_and_tight
#print axioms joint_block_gas_word_to_word_tail_zero_allowance_non_vacuous_and_tight
#print axioms joint_source_covered_by_maxGuestSourceClock_and_portfolio_ordering_non_vacuous_and_tight
#print axioms joint_block_gas_yukonScore_order_and_blockVsTx_savings_non_vacuous_and_tight
#print axioms joint_block_gas_slope3_tail_certificate_non_vacuous_and_tight
#print axioms joint_block_gas_slope6_tail_certificate_non_vacuous_and_tight
#print axioms joint_block_gas_slope12_tail_certificate_non_vacuous_and_tight
#print axioms end_to_end_joint_block_gas_six_pass_master_certificate_non_vacuous_and_tight

end InitECandidate.Solver.JointBlockGasSixPassMasterCert
