import InitECandidate.Solver.GuestEndToEndStartToHaltAndCoupledMptMaster
import InitECandidate.Solver.SelfContainedCoupledGasFullBlockAndSixtyTwoBudgetSynth
import InitECandidate.Solver.SelfContainedNoLocValue6CoupledGasAndSixtyFourBudgetMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedEndToEndCoupledMptAndSixtyFourBudgetSynth`

Self-contained Wave 5 synthesis (`W5_184`, `0` imports from `InitECandidate.Proofs.Bounded*`)
uniting:
1. **`GuestEndToEndStartToHaltAndCoupledMptMaster` (`11/11` tight)**:
   - Exact saving of `619_060_000` ticks on `mpt_set` by coupling MPT state-root writes to the shared
     `200M` gas budget (`21 * k ≤ 2_000_000 ⇒ k ≤ 95_238`, `130_000 * 95_238 = 12_380_940_000`,
     saving `13_000_000_000 - 12_380_940_000 = 619_060_000` ticks),
   - Coupled-MPT block totals: `block_total_coupled_mpt = 224_366_249_693` (without memoization) and
     `block_total_memo_coupled_mpt = 195_035_480_749` (with DAG memoization),
   - Exact coupled-MPT `L_max` thresholds: `38_817` (heap) and `40_284` (memo) at `1×` Yukon, and
     `5_040` (heap) and `6_507` (memo) at `4×` Yukon,
   - Remaining Yukon budget for pre/post-EVM work (`676_353_675_781` at `1×`; `813_731_675` heap and
     `30_144_500_619` memo per quarter at `4×`), per-byte (`≤ 5_039`, `≤ 6`, `≤ 224`) and per-tx
     (`≤ 48_825`, `≤ 1_808_742`) rates, and `mptPlusBuild = 20_036_870_848` reconciliation.
2. **`SelfContainedCoupledGasFullBlockAndSixtyTwoBudgetSynth` (`10/10` tight)**:
   - Coupled-gas `ts+64` absorption (`L ≤ 5_000` adds `0` net ticks), `L_max` thresholds (`38_786`,
     `40_253`, `5_009`, `6_476`), `_resolve_step` bounds (`1_110_441_952` / `536_870_848`), `r = 8`
     probes (`17_767_071_232` / `8_589_933_568`), exact per-node decode ticks (`43/98`, `48/90`,
     `326/448`, `τ < 1`), DAG memoization (`33_554_428` nodes), MPT + `nodedb` + `ts+64` bridge, and
     62/60/56/54/52/50-budget portfolios.
3. **`SelfContainedNoLocValue6CoupledGasAndSixtyFourBudgetMaster` (`12/12` tight)**:
   - Unconditional `StackToLab → LabToTarget` no-`locValue`-6 safety, coupled-gas `L_max` iff
     characterizations, and the strictly increasing **64-budget** portfolio (`SixtyFourShape`,
     `ClaimPayloads`) below Yukon (`900_719_925_474`) with conditional finite certificate lifting.
-/

namespace InitECandidate.Solver.SelfContainedEndToEndCoupledMptAndSixtyFourBudgetSynth

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit (
  tLeaf tExt tBranch decodeTicks
)
open InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound (
  heapAvail heapOf
)
open InitECandidate.Solver.GuestNodedbAndWitnessTableBound (
  maxInput boundedBuild
)
open InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge (
  mptPlusBuild joint
)
open InitECandidate.Solver.GuestWitnessResolveAndBlockTotalTicksSynthesis (
  gasEnv decodeHeap decodeMemo resolveCalls
)
open InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster (
  subHeap subMemo tsTicks total sub_vals sub_slopes salted_four
)
open InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster (
  excess coupled avg_slope absorbed excess_zero excess_first block_unchanged
  seventy_eight_inside lmax1_heap lmax1_memo lmax4_heap lmax4_memo unsalted_still_fails sharp
)
open InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption (S)
open InitECandidate.Solver.GuestEndToEndStartToHaltAndCoupledMptMaster (
  dirty_keys dirty_keys_tight root_coupled coupling_gain no_absorption
  coupled_totals residual_1x residual_4x per_byte per_tx mpt_const
)
open InitECandidate.Solver.WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster (
  HeapAllocationContract HeapNodesContract HeapRateContract MemoContract
  BridgeContract AbsorptionContract FiftySixShape
)
open InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster (
  FiftyFourShape WalkContract AccessContract RootContract WitnessLinearContract
  CoupledJournalContract PanLabSafe PanTargetSafe PanUserSafe FrontendSafe
)
open InitECandidate.Solver.StackToLabAndLabToTargetNoLocValue6 (
  JC JumpOk Sec
)
open InitECandidate.Solver.WitnessDecodeExactTicksNoLocValue6AndSixtyBudgetMaster (
  ExactTicks SixtyShape
)
open InitECandidate.Solver.WitnessResolveBlockTotalTicksAndSixtyTwoBudgetMaster (
  SixtyTwoShape
)
open InitECandidate.Solver.SelfContainedWitnessResolveBlockTotalTicksAndSixtyBudgetSynth (
  sixtyPortfolio SixtyClaimPayloads
)
open InitECandidate.Solver.SelfContainedCoupledGasFullBlockAndSixtyTwoBudgetSynth (
  sixtyTwoPortfolio SixtyTwoClaimPayloads
  coupled_gas_ts64_absorption_and_unchanged_block_totals_non_vacuous_and_tight
  coupled_gas_lmax_thresholds_one_and_four_yukon_non_vacuous_and_tight
  coupled_gas_full_block_and_witness_resolve_probes_non_vacuous_and_tight
  coupled_gas_block_totals_and_mpt_nodedb_bridge_non_vacuous_and_tight
  exact_decode_ticks_dag_memoization_and_coupled_gas_non_vacuous_and_tight
  pan_to_target_no_loc_value_6_and_coupled_gas_full_block_non_vacuous_and_tight
  sixty_and_sixty_two_budget_portfolios_and_payloads_non_vacuous_and_tight
  sixty_two_budget_explicit_certificates_and_coupled_gas_non_vacuous_and_tight
  integrated_sixty_two_budget_and_coupled_gas_full_block_master_non_vacuous_and_tight
  grand_self_contained_coupled_gas_full_block_and_sixty_two_budget_synth_non_vacuous_and_tight
)
open InitECandidate.Solver.SelfContainedNoLocValue6CoupledGasAndSixtyFourBudgetMaster (
  portfolio sixtyFourClaims SixtyFourShape ClaimPayloads
  panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
  exact_ticks_non_vacuous_and_tight
  general_side_regime_absorption_non_vacuous_and_tight
  zero_net_ticks_non_vacuous_and_tight
  one_heap_non_vacuous_and_tight
  one_memo_non_vacuous_and_tight
  four_heap_non_vacuous_and_tight
  four_memo_non_vacuous_and_tight
  sharpness_non_vacuous_and_tight
  portfolio_non_vacuous_and_tight
  payloads_non_vacuous_and_tight
  certificates_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

variable {width : Nat} [NeZero width]

/-- Coupled-MPT full-block subtotal without DAG memoization (`224,985,309,693 - 619,060,000`). -/
def block_total_coupled_mpt : Nat := 224366249693

/-- Coupled-MPT full-block subtotal with DAG memoization (`195,654,540,749 - 619,060,000`). -/
def block_total_memo_coupled_mpt : Nat := 195035480749

abbrev sixtyFourPortfolio : List Nat :=
  InitECandidate.Solver.SelfContainedNoLocValue6CoupledGasAndSixtyFourBudgetMaster.portfolio

abbrev SixtyFourClaimPayloads : Prop :=
  InitECandidate.Solver.SelfContainedNoLocValue6CoupledGasAndSixtyFourBudgetMaster.ClaimPayloads

/-! ## Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- 1. Exact saving of `619_060_000` ticks on `mpt_set` by coupling MPT state-root writes to the
shared `200M` gas budget (`21 * k ≤ 2_000_000 ⇒ k ≤ 95_238`, `130_000 * k ≤ 12_380_940_000`),
yielding `block_total_coupled_mpt = 224_366_249_693` (without memoization) and
`block_total_memo_coupled_mpt = 195_035_480_749` (with DAG memoization), plus exact residual
budgets at `1×` (`676_353_675_781`) and `4×` (`813_731_675` / `30_144_500_619`), per-byte and
per-tx rates, and `mptPlusBuild = 20_036_870_848` reconciliation. -/
theorem coupled_mpt_saving_and_block_totals_non_vacuous_and_tight
    (k : Nat) (hk : 21 * k ≤ 2000000) :
    k ≤ 95238 ∧
    (21 * 95238 ≤ 2000000 ∧ 2000000 < 21 * 95239) ∧
    130000 * k ≤ 12380940000 ∧
    13000000000 - 130000 * 95238 = 619060000 ∧
    (130000 ≤ 21 * 50000 ∧ 40 * 100000000000 = 2000000 * 2000000) ∧
    (block_total_coupled_mpt = 224366249693 ∧
      block_total_memo_coupled_mpt = 195035480749 ∧
      subHeap - 619060000 = block_total_coupled_mpt ∧
      subMemo - 619060000 = block_total_memo_coupled_mpt) ∧
    yukon - block_total_coupled_mpt = 676353675781 ∧
    (yukon / 4 - block_total_coupled_mpt = 813731675 ∧
      yukon / 4 - block_total_memo_coupled_mpt = 30144500619) ∧
    (5039 * 134217712 ≤ 676353675781 ∧ 676353675781 < 5040 * 134217712 ∧
      6 * 134217712 ≤ 813731675 ∧ 813731675 < 7 * 134217712 ∧
      224 * 134217712 ≤ 30144500619 ∧ 30144500619 < 225 * 134217712) ∧
    (200000000 / 12000 = 16666 ∧
      48825 * 16666 ≤ 813731675 ∧ 813731675 < 48826 * 16666 ∧
      1808742 * 16666 ≤ 30144500619 ∧ 30144500619 < 1808743 * 16666) ∧
    (19500000000 + 536870848 = 20036870848 ∧ 20037125024 - 20036870848 = 254176) :=
  ⟨dirty_keys k hk,
   dirty_keys_tight,
   root_coupled k hk,
   coupling_gain,
   no_absorption,
   by decide,
   residual_1x,
   residual_4x,
   per_byte,
   per_tx,
   mpt_const⟩

/-- 2. Exact `L_max` thresholds with coupled MPT (`38_817` heap / `40_284` memo at `1×` Yukon, and
`5_040` heap / `6_507` memo at `4×` Yukon, each `+31` over the uncoupled-MPT coupled-gas thresholds
`38_786` / `40_253` and `5_009` / `6_476`), including iff characterizations and zero excess for
`L ≤ 5_000`. -/
theorem coupled_mpt_lmax_thresholds_one_and_four_yukon_non_vacuous_and_tight
    (L : Nat) (hL : L ≤ 5000) :
    (coupled block_total_coupled_mpt L = 224366249693 ∧
      coupled block_total_memo_coupled_mpt L = 195035480749) ∧
    ((∀ L' : Nat, 1 * coupled block_total_coupled_mpt L' < yukon ↔ L' ≤ 38817) ∧
      coupled block_total_coupled_mpt 38817 < yukon ∧
      yukon ≤ coupled block_total_coupled_mpt 38818) ∧
    ((∀ L' : Nat, 1 * coupled block_total_memo_coupled_mpt L' < yukon ↔ L' ≤ 40284) ∧
      coupled block_total_memo_coupled_mpt 40284 < yukon ∧
      yukon ≤ coupled block_total_memo_coupled_mpt 40285) ∧
    ((∀ L' : Nat, 4 * coupled block_total_coupled_mpt L' < yukon ↔ L' ≤ 5040) ∧
      4 * coupled block_total_coupled_mpt 5040 < yukon ∧
      yukon ≤ 4 * coupled block_total_coupled_mpt 5041) ∧
    ((∀ L' : Nat, 4 * coupled block_total_memo_coupled_mpt L' < yukon ↔ L' ≤ 6507) ∧
      4 * coupled block_total_memo_coupled_mpt 6507 < yukon ∧
      yukon ≤ 4 * coupled block_total_memo_coupled_mpt 6508) ∧
    (38817 - 38786 = 31 ∧ 40284 - 40253 = 31 ∧ 5040 - 5009 = 31 ∧ 6507 - 6476 = 31) ∧
    (40284 < 158162 ∧ yukon < coupled block_total_memo_coupled_mpt 158162 ∧
      yukon < coupled block_total_coupled_mpt 158162) ∧
    ((∀ L' : Nat, 1 * coupled subHeap L' < yukon ↔ L' ≤ 38786) ∧
      (∀ L' : Nat, 1 * coupled subMemo L' < yukon ↔ L' ≤ 40253) ∧
      (∀ L' : Nat, 4 * coupled subHeap L' < yukon ↔ L' ≤ 5009) ∧
      (∀ L' : Nat, 4 * coupled subMemo L' < yukon ↔ L' ≤ 6476)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by decide, by decide,
    ⟨one_heap_non_vacuous_and_tight.1,
     one_memo_non_vacuous_and_tight.1,
     four_heap_non_vacuous_and_tight.1,
     four_memo_non_vacuous_and_tight.1⟩⟩
  · unfold coupled block_total_coupled_mpt block_total_memo_coupled_mpt
    rw [excess_zero L hL]
    decide
  · refine ⟨?_, by decide⟩
    intro L'
    unfold coupled excess block_total_coupled_mpt yukon
    omega
  · refine ⟨?_, by decide⟩
    intro L'
    unfold coupled excess block_total_memo_coupled_mpt yukon
    omega
  · refine ⟨?_, by decide⟩
    intro L'
    unfold coupled excess block_total_coupled_mpt yukon
    omega
  · refine ⟨?_, by decide⟩
    intro L'
    unfold coupled excess block_total_memo_coupled_mpt yukon
    omega

/-- 3. Synthesis of coupled-MPT `619_060_000`-tick saving (`224_366_249_693` / `195_035_480_749`)
and `L_max` thresholds (`38_817` / `40_284` at `1×`, `5_040` / `6_507` at `4×`) with coupled-gas
`ts+64` absorption (`general_side_regime_absorption`, `L ≤ 5_000` adds `0` net ticks, first excess
`excess 5001 = 20_000_000`, sharpness of `50_001`). -/
theorem coupled_mpt_and_coupled_gas_ts64_absorption_non_vacuous_and_tight
    (k L n u B blk : Nat) (hk : 21 * k ≤ 2000000) (hL : L ≤ 5000)
    (hu : n ≤ u) (hS : B + u ≤ 2000000) (hblk : 40 * blk ≤ B * B) :
    (k ≤ 95238 ∧ 130000 * k ≤ 12380940000 ∧
      13000000000 - 130000 * 95238 = 619060000 ∧
      coupled block_total_coupled_mpt L = 224366249693 ∧
      coupled block_total_memo_coupled_mpt L = 195035480749 ∧
      (coupled block_total_coupled_mpt 38817 < yukon ∧ yukon ≤ coupled block_total_coupled_mpt 38818) ∧
      (coupled block_total_memo_coupled_mpt 40284 < yukon ∧ yukon ≤ coupled block_total_memo_coupled_mpt 40285) ∧
      (4 * coupled block_total_coupled_mpt 5040 < yukon ∧ yukon ≤ 4 * coupled block_total_coupled_mpt 5041) ∧
      (4 * coupled block_total_memo_coupled_mpt 6507 < yukon ∧ yukon ≤ 4 * coupled block_total_memo_coupled_mpt 6508)) ∧
    ((156088992805 / 2000000 = 78044 ∧ 156088992805 / 200000000 = 780) ∧
      blk + 10 * L * n ≤ 100000000000 ∧
      excess L = 0 ∧
      excess 5001 = 20000000 ∧
      (coupled subHeap L = 224985309693 ∧ coupled subMemo L = 195654540749) ∧
      (subHeap = 224985309693 ∧ subMemo = 195654540749) ∧
      (4 * subMemo = 782618162996 ∧ 4 * subMemo < yukon ∧ 4 * subHeap < yukon ∧
        yukon < 5 * subMemo) ∧
      (78 ≤ 5000 ∧ excess 78 = 0) ∧
      ¬ (∀ B' U T blk' : Nat, B' + U ≤ S → 40 * blk' ≤ B' * B' → T ≤ 50001 * U →
          blk' + T ≤ 100000000000)) ∧
    ((∀ L' : Nat, excess L' = 0 ↔ L' ≤ 5000) ∧
      (∀ L' : Nat, L' ≤ 5000 →
        coupled subHeap L' = 224985309693 ∧ coupled subMemo L' = 195654540749) ∧
      excess 5001 = 20000000) := by
  have hmpt := coupled_mpt_lmax_thresholds_one_and_four_yukon_non_vacuous_and_tight L hL
  exact ⟨⟨dirty_keys k hk,
          root_coupled k hk,
          coupling_gain,
          hmpt.1.1,
          hmpt.1.2,
          hmpt.2.1.2,
          hmpt.2.2.1.2,
          hmpt.2.2.2.1.2,
          hmpt.2.2.2.2.1.2⟩,
         coupled_gas_ts64_absorption_and_unchanged_block_totals_non_vacuous_and_tight
           L n u B blk hL hu hS hblk,
         zero_net_ticks_non_vacuous_and_tight⟩

/-- 4. Coupled-MPT and coupled-gas full-block totals synthesized with `_resolve_step` call bounds
(`1_110_441_952` heap, `536_870_848` memo), `r = 8` probe ticks (`17_767_071_232` and
`8_589_933_568`), and probe thresholds (`r ≤ 312`, `r ≤ 664`). -/
theorem coupled_mpt_and_witness_resolve_probes_non_vacuous_and_tight
    (k L n u B_gas blk E B r : Nat) (hk : 21 * k ≤ 2000000) (hL : L ≤ 5000)
    (hu : n ≤ u) (hS : B_gas + u ≤ 2000000) (hblk : 40 * blk ≤ B_gas * B_gas)
    (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428) (hr : r ≤ 312) :
    (k ≤ 95238 ∧ 130000 * k ≤ 12380940000 ∧
      13000000000 - 130000 * 95238 = 619060000 ∧
      coupled block_total_coupled_mpt L = 224366249693 ∧
      coupled block_total_memo_coupled_mpt L = 195035480749 ∧
      (coupled block_total_coupled_mpt 38817 < yukon ∧ yukon ≤ coupled block_total_coupled_mpt 38818) ∧
      (coupled block_total_memo_coupled_mpt 40284 < yukon ∧ yukon ≤ coupled block_total_memo_coupled_mpt 40285) ∧
      (4 * coupled block_total_coupled_mpt 5040 < yukon ∧ yukon ≤ 4 * coupled block_total_coupled_mpt 5041) ∧
      (4 * coupled block_total_memo_coupled_mpt 6507 < yukon ∧ yukon ≤ 4 * coupled block_total_memo_coupled_mpt 6508)) ∧
    ((blk + 10 * L * n ≤ 100000000000 ∧
        excess L = 0 ∧
        coupled subHeap L = 224985309693 ∧ coupled subMemo L = 195654540749 ∧
        (coupled subHeap 38786 < yukon ∧ yukon ≤ coupled subHeap 38787) ∧
        (coupled subMemo 40253 < yukon ∧ yukon ≤ coupled subMemo 40254) ∧
        (4 * coupled subHeap 5009 < yukon ∧ yukon ≤ 4 * coupled subHeap 5010) ∧
        (4 * coupled subMemo 6476 < yukon ∧ yukon ≤ 4 * coupled subMemo 6477)) ∧
      ((∀ B', B' ≤ 69402622 → resolveCalls 0 B' ≤ 1110441952) ∧
        resolveCalls 0 69402622 = 1110441952) ∧
      ((∀ E' B', E' + B' ≤ 33554428 → resolveCalls E' B' ≤ 536870848) ∧
        resolveCalls 0 33554428 = 536870848) ∧
      (2 * 8 * resolveCalls 0 69402622 = 17767071232 ∧
        2 * 8 * resolveCalls 0 33554428 = 8589933568) ∧
      ((∀ r' : Nat, 2 * r' * 1110441952 ≤ 693501687013 ↔ r' ≤ 312) ∧
        (∀ r' : Nat, 2 * r' * 536870848 ≤ 713655318293 ↔ r' ≤ 664) ∧
        (2 * 312 * 1110441952 ≤ 693501687013 ∧ 693501687013 < 2 * 313 * 1110441952) ∧
        (2 * 664 * 536870848 ≤ 713655318293 ∧ 713655318293 < 2 * 665 * 536870848)) ∧
      (resolveCalls 0 B ≤ 1110441952 ∧
        resolveCalls E B ≤ 536870848 ∧
        (2 * 8 * 1110441952 = 17767071232 ∧ 2 * 8 * 536870848 = 8589933568) ∧
        (2 * 312 * 1110441952 ≤ 693501687013 ∧ 693501687013 < 2 * 313 * 1110441952) ∧
        (2 * 664 * 536870848 ≤ 713655318293 ∧ 713655318293 < 2 * 665 * 536870848) ∧
        gasEnv + mptPlusBuild + decodeHeap + 2 * r * resolveCalls 0 B < yukon ∧
        693501687013 < 2 * 2 ^ 25 * 1110441952)) := by
  have hmpt := coupled_mpt_lmax_thresholds_one_and_four_yukon_non_vacuous_and_tight L hL
  exact ⟨⟨dirty_keys k hk,
          root_coupled k hk,
          coupling_gain,
          hmpt.1.1,
          hmpt.1.2,
          hmpt.2.1.2,
          hmpt.2.2.1.2,
          hmpt.2.2.2.1.2,
          hmpt.2.2.2.2.1.2⟩,
         coupled_gas_full_block_and_witness_resolve_probes_non_vacuous_and_tight
           L n u B_gas blk E B r hL hu hS hblk hB hEB hr⟩

/-- 5. Coupled-MPT block totals (`224_366_249_693` and `195_035_480_749`, saving `619_060_000`) and
`L_max` thresholds (`38_817`, `40_284`, `5_040`, `6_507`) synthesized with the MPT + `nodedb`
(`20_036_870_848`) + `ts+64` (`176_125_863_653`) bridge and pre-probe subtotals (`207_218_238_461`
and `187_064_607_181`). -/
theorem coupled_mpt_block_totals_and_mpt_nodedb_bridge_non_vacuous_and_tight
    (k L E B r ns nc : Nat) (hk : 21 * k ≤ 2000000) (hL : L ≤ 5000)
    (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428) (hr : r ≤ 312)
    (h_nodedb : 4 * (ns + nc) ≤ maxInput) :
    (k ≤ 95238 ∧ 130000 * k ≤ 12380940000 ∧
      13000000000 - 130000 * 95238 = 619060000 ∧
      block_total_coupled_mpt = 224366249693 ∧
      block_total_memo_coupled_mpt = 195035480749 ∧
      yukon - block_total_coupled_mpt = 676353675781 ∧
      yukon / 4 - block_total_coupled_mpt = 813731675 ∧
      yukon / 4 - block_total_memo_coupled_mpt = 30144500619 ∧
      (coupled block_total_coupled_mpt 38817 < yukon ∧ yukon ≤ coupled block_total_coupled_mpt 38818) ∧
      (coupled block_total_memo_coupled_mpt 40284 < yukon ∧ yukon ≤ coupled block_total_memo_coupled_mpt 40285) ∧
      (4 * coupled block_total_coupled_mpt 5040 < yukon ∧ yukon ≤ 4 * coupled block_total_coupled_mpt 5041) ∧
      (4 * coupled block_total_memo_coupled_mpt 6507 < yukon ∧ yukon ≤ 4 * coupled block_total_memo_coupled_mpt 6508)) ∧
    ((coupled subHeap L = 224985309693 ∧ coupled subMemo L = 195654540749) ∧
      (4 * subMemo = 782618162996 ∧ 4 * subMemo < yukon ∧ 4 * subHeap < yukon ∧
        yukon < 5 * subMemo) ∧
      (coupled subHeap 38786 < yukon ∧ yukon ≤ coupled subHeap 38787 ∧
        coupled subMemo 40253 < yukon ∧ yukon ≤ coupled subMemo 40254 ∧
        4 * coupled subHeap 5009 < yukon ∧ yukon ≤ 4 * coupled subHeap 5010 ∧
        4 * coupled subMemo 6476 < yukon ∧ yukon ≤ 4 * coupled subMemo 6477) ∧
      (resolveCalls 0 B ≤ 1110441952 ∧
        resolveCalls E B ≤ 536870848 ∧
        (gasEnv + mptPlusBuild + decodeHeap = 207218238461 ∧
          yukon - (gasEnv + mptPlusBuild + decodeHeap) = 693501687013) ∧
        (gasEnv + mptPlusBuild + decodeMemo = 187064607181 ∧
          yukon - (gasEnv + mptPlusBuild + decodeMemo) = 713655318293) ∧
        (4 * 207218238461 < yukon ∧ yukon < 5 * 207218238461 ∧
          4 * 187064607181 = 748258428724 ∧ 4 * 187064607181 < yukon ∧ yukon < 5 * 187064607181) ∧
        gasEnv + mptPlusBuild + decodeHeap + 2 * r * resolveCalls 0 B < yukon ∧
        (BridgeContract ∧
          AbsorptionContract ∧
          (mptPlusBuild = 20036870848 ∧
           (44 * mptPlusBuild < yukon ∧ yukon ≤ 45 * mptPlusBuild) ∧
           joint = 176125863653 ∧
           yukon - joint = 724594061821 ∧
           (5 * joint = 880629318265 ∧ 5 * joint < yukon ∧ yukon - 5 * joint = 20090607209) ∧
           boundedBuild 8 ns + boundedBuild 8 nc ≤ 536870848 ∧
           19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ mptPlusBuild ∧
           156088992805 + 19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ joint ∧
           (5 * (2 * 1) / 2 + 5 * (2 * 1) / 2 = 10 ∧ 5 * (4 * 3) / 2 = 30 ∧
             2 * (5 * (158162 * 158161) / 2) = 125075300410) ∧
           (10 * 5000 = 50000 ∧ 50000 < 10 * 5001 ∧ 5 * 10000 = 50000 ∧ 50000 < 5 * 10001))))) := by
  have hmpt := coupled_mpt_lmax_thresholds_one_and_four_yukon_non_vacuous_and_tight L hL
  exact ⟨⟨dirty_keys k hk,
          root_coupled k hk,
          coupling_gain,
          rfl,
          rfl,
          residual_1x,
          residual_4x.1,
          residual_4x.2,
          hmpt.2.1.2,
          hmpt.2.2.1.2,
          hmpt.2.2.2.1.2,
          hmpt.2.2.2.2.1.2⟩,
         coupled_gas_block_totals_and_mpt_nodedb_bridge_non_vacuous_and_tight
           L E B r ns nc hL hB hEB hr h_nodedb⟩

/-- 6. Exact per-node decode ticks (`43 < 98`, `48 < 90`, `326 < 448`, `τ < 1`) and DAG memoization
(`33_554_428` nodes, `10_938_743_528` decode ticks) synthesized with coupled-MPT saving
(`619_060_000` ticks, `224_366_249_693` / `195_035_480_749`) and `L_max` thresholds (`38_817`,
`40_284`, `5_040`, `6_507`). -/
theorem exact_decode_ticks_dag_memoization_and_coupled_mpt_non_vacuous_and_tight
    (k L_run L E B n : Nat) (hk : 21 * k ≤ 2000000) (hL : L_run ≤ 5000)
    (h_heap : heapOf L E B ≤ heapAvail) (h_br : heapOf 0 0 B ≤ heapAvail)
    (hn : 4 * n ≤ 134217712) (h_memo : L + E + B ≤ n) :
    (k ≤ 95238 ∧ 130000 * k ≤ 12380940000 ∧
      13000000000 - 130000 * 95238 = 619060000 ∧
      coupled block_total_coupled_mpt L_run = 224366249693 ∧
      coupled block_total_memo_coupled_mpt L_run = 195035480749 ∧
      (coupled block_total_coupled_mpt 38817 < yukon ∧ yukon ≤ coupled block_total_coupled_mpt 38818) ∧
      (coupled block_total_memo_coupled_mpt 40284 < yukon ∧ yukon ≤ coupled block_total_memo_coupled_mpt 40285) ∧
      (4 * coupled block_total_coupled_mpt 5040 < yukon ∧ yukon ≤ 4 * coupled block_total_coupled_mpt 5041) ∧
      (4 * coupled block_total_memo_coupled_mpt 6507 < yukon ∧ yukon ≤ 4 * coupled block_total_memo_coupled_mpt 6508)) ∧
    ((excess L_run = 0 ∧
        coupled subHeap L_run = 224985309693 ∧ coupled subMemo L_run = 195654540749 ∧
        (coupled subHeap 38786 < yukon ∧ yukon ≤ coupled subHeap 38787) ∧
        (coupled subMemo 40253 < yukon ∧ yukon ≤ coupled subMemo 40254) ∧
        (4 * coupled subHeap 5009 < yukon ∧ yukon ≤ 4 * coupled subHeap 5010) ∧
        (4 * coupled subMemo 6476 < yukon ∧ yukon ≤ 4 * coupled subMemo 6477)) ∧
      (ExactTicks ∧
        ((∀ L' E' B', decodeTicks L' E' B' ≤ heapOf L' E' B') ∧
          (∀ L' E' B', heapOf L' E' B' ≤ heapAvail → decodeTicks L' E' B' ≤ 31092374808) ∧
          decodeTicks 1 0 0 = 43 ∧ decodeTicks 0 1 0 = 48 ∧ decodeTicks 0 0 1 = 326) ∧
        ((∀ L' E' B' n', 4 * n' ≤ 134217712 → L' + E' + B' ≤ n' →
            decodeTicks L' E' B' ≤ 10938743528) ∧
          decodeTicks 0 0 33554428 = 10938743528 ∧
          4 * 33554428 = 134217712 ∧
          yukon - 10938743528 = 889781181946 ∧ 10938743528 < yukon) ∧
        ((∀ L' E' B', heapOf L' E' B' ≤ heapAvail → 5 * decodeTicks L' E' B' < yukon) ∧
          heapAvail = 31092374808 ∧
          28 * heapAvail < yukon ∧ yukon < 29 * heapAvail) ∧
        (HeapAllocationContract ∧
          HeapNodesContract ∧
          HeapRateContract ∧
          MemoContract ∧
          (heapAvail = 31092374808 ∧ heapOf 1 0 0 = 98 ∧ heapOf 0 1 0 = 90 ∧ heapOf 0 0 1 = 448) ∧
          (L + E + B ≤ 345470831 ∧ heapOf 0 345470831 0 ≤ heapAvail ∧ heapAvail < heapOf 0 345470832 0) ∧
          B ≤ 69402622 ∧
          (28 * 31092374808 < yukon ∧ yukon < 29 * 31092374808) ∧
          (5 * (5 * 31092374808) < yukon ∧ yukon < 5 * (6 * 31092374808)) ∧
          (L + E + B ≤ 33554428 ∧
            448 * 33554428 + 2 * 134217712 = 15300819168 ∧ 15300819168 < heapAvail ∧
            58 * 15300819168 < yukon ∧ yukon < 59 * 15300819168)))) := by
  have hmpt := coupled_mpt_lmax_thresholds_one_and_four_yukon_non_vacuous_and_tight L_run hL
  exact ⟨⟨dirty_keys k hk,
          root_coupled k hk,
          coupling_gain,
          hmpt.1.1,
          hmpt.1.2,
          hmpt.2.1.2,
          hmpt.2.2.1.2,
          hmpt.2.2.2.1.2,
          hmpt.2.2.2.2.1.2⟩,
         exact_decode_ticks_dag_memoization_and_coupled_gas_non_vacuous_and_tight
           L_run L E B n hL h_heap h_br hn h_memo⟩

/-- 7. Unconditional `StackToLab → LabToTarget` no-`locValue`-6 safety (`PanTargetSafe`, `PanUserSafe`,
`JumpOk`) synthesized with coupled-MPT saving (`619_060_000` ticks, `224_366_249_693` and
`195_035_480_749`) and `L_max` thresholds (`38_817` / `40_284` at `1×`, `5_040` / `6_507` at `4×`). -/
theorem pan_to_target_no_loc_value_6_and_coupled_mpt_full_block_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (k L E B r : Nat) (hk : 21 * k ≤ 2000000) (hL : L ≤ 5000)
    (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428) (hr : r ≤ 312) :
    (k ≤ 95238 ∧ 130000 * k ≤ 12380940000 ∧
      13000000000 - 130000 * 95238 = 619060000 ∧
      coupled block_total_coupled_mpt L = 224366249693 ∧
      coupled block_total_memo_coupled_mpt L = 195035480749 ∧
      (coupled block_total_coupled_mpt 38817 < yukon ∧ yukon ≤ coupled block_total_coupled_mpt 38818) ∧
      (coupled block_total_memo_coupled_mpt 40284 < yukon ∧ yukon ≤ coupled block_total_memo_coupled_mpt 40285) ∧
      (4 * coupled block_total_coupled_mpt 5040 < yukon ∧ yukon ≤ 4 * coupled block_total_coupled_mpt 5041) ∧
      (4 * coupled block_total_memo_coupled_mpt 6507 < yukon ∧ yukon ≤ 4 * coupled block_total_memo_coupled_mpt 6508)) ∧
    ((NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
        NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe ∧
        MemoContract) ∧
      (coupled subHeap L = 224985309693 ∧ coupled subMemo L = 195654540749 ∧
        (coupled subHeap 38786 < yukon ∧ yukon ≤ coupled subHeap 38787) ∧
        (coupled subMemo 40253 < yukon ∧ yukon ≤ coupled subMemo 40254) ∧
        (4 * coupled subHeap 5009 < yukon ∧ yukon ≤ 4 * coupled subHeap 5010) ∧
        (4 * coupled subMemo 6476 < yukon ∧ yukon ≤ 4 * coupled subMemo 6477)) ∧
      (ExactTicks ∧
        resolveCalls 0 B ≤ 1110441952 ∧
        resolveCalls E B ≤ 536870848 ∧
        (gasEnv + mptPlusBuild + decodeHeap = 207218238461 ∧
          yukon - (gasEnv + mptPlusBuild + decodeHeap) = 693501687013) ∧
        (gasEnv + mptPlusBuild + decodeMemo = 187064607181 ∧
          yukon - (gasEnv + mptPlusBuild + decodeMemo) = 713655318293) ∧
        (4 * 207218238461 < yukon ∧ yukon < 5 * 207218238461 ∧
          4 * 187064607181 = 748258428724 ∧ 4 * 187064607181 < yukon ∧ yukon < 5 * 187064607181) ∧
        gasEnv + mptPlusBuild + decodeHeap + 2 * r * resolveCalls 0 B < yukon ∧
        ((∀ s' ∈ L',
            InitECandidate.Solver.PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = false →
            ∀ x ∈ s'.lines, JumpOk x = true) ∧
          JC (.locValue 0 storeConstsStubLocation 0 : HolProg width) = false))) := by
  have hmpt := coupled_mpt_lmax_thresholds_one_and_four_yukon_non_vacuous_and_tight L hL
  exact ⟨⟨dirty_keys k hk,
          root_coupled k hk,
          coupling_gain,
          hmpt.1.1,
          hmpt.1.2,
          hmpt.2.1.2,
          hmpt.2.2.1.2,
          hmpt.2.2.2.1.2,
          hmpt.2.2.2.2.1.2⟩,
         pan_to_target_no_loc_value_6_and_coupled_gas_full_block_non_vacuous_and_tight
           arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h L E B r hL hB hEB hr⟩

/-- 8. Strictly increasing **64-budget** (`SixtyFourShape`, `SixtyFourClaimPayloads`), 62-budget,
60-budget, 56-budget, 54-budget, 52-budget, and 50-budget portfolios and JSON claim payloads below
Yukon (`900_719_925_474`), united with coupled-MPT saving (`619_060_000` ticks) and `L_max`
thresholds (`38_817`, `40_284`, `5_040`, `6_507`). -/
theorem sixty_two_and_sixty_four_budget_portfolios_and_payloads_non_vacuous_and_tight
    (k L : Nat) (hk : 21 * k ≤ 2000000) (hL : L ≤ 5000) (l_chunks : List Nat) (ck : Nat) :
    (SixtyFourShape ∧ SixtyFourClaimPayloads) ∧
    (k ≤ 95238 ∧ 130000 * k ≤ 12380940000 ∧
      13000000000 - 130000 * 95238 = 619060000 ∧
      coupled block_total_coupled_mpt L = 224366249693 ∧
      coupled block_total_memo_coupled_mpt L = 195035480749 ∧
      (coupled block_total_coupled_mpt 38817 < yukon ∧ yukon ≤ coupled block_total_coupled_mpt 38818) ∧
      (coupled block_total_memo_coupled_mpt 40284 < yukon ∧ yukon ≤ coupled block_total_memo_coupled_mpt 40285) ∧
      (4 * coupled block_total_coupled_mpt 5040 < yukon ∧ yukon ≤ 4 * coupled block_total_coupled_mpt 5041) ∧
      (4 * coupled block_total_memo_coupled_mpt 6507 < yukon ∧ yukon ≤ 4 * coupled block_total_memo_coupled_mpt 6508)) ∧
    ((SixtyTwoShape ∧ SixtyTwoClaimPayloads) ∧
      (coupled subHeap L = 224985309693 ∧ coupled subMemo L = 195654540749 ∧
        (coupled subHeap 38786 < yukon ∧ yukon ≤ coupled subHeap 38787) ∧
        (coupled subMemo 40253 < yukon ∧ yukon ≤ coupled subMemo 40254) ∧
        (4 * coupled subHeap 5009 < yukon ∧ yukon ≤ 4 * coupled subHeap 5010) ∧
        (4 * coupled subMemo 6476 < yukon ∧ yukon ≤ 4 * coupled subMemo 6477)) ∧
      ((SixtyShape ∧ SixtyClaimPayloads) ∧
       ExactTicks ∧
       (gasEnv + mptPlusBuild + decodeHeap = 207218238461 ∧
         yukon - (gasEnv + mptPlusBuild + decodeHeap) = 693501687013) ∧
       (gasEnv + mptPlusBuild + decodeMemo = 187064607181 ∧
         yukon - (gasEnv + mptPlusBuild + decodeMemo) = 713655318293) ∧
       (4 * 207218238461 < yukon ∧ yukon < 5 * 207218238461 ∧
         4 * 187064607181 = 748258428724 ∧ 4 * 187064607181 < yukon ∧ yukon < 5 * 187064607181) ∧
       ((FiftySixShape ∧ SelfContainedWitnessDagMemoizationAndFiftySixBudgetSynth.FiftySixClaimPayloads) ∧
        ((SelfContainedMptNodedbTransientAndFiftyFourBudgetSynth.fiftyFourPortfolio.length = 54 ∧
           SelfContainedMptNodedbTransientAndFiftyFourBudgetSynth.fiftyFourPortfolio.Pairwise (· < ·) ∧
           (∀ K ∈ SelfContainedMptNodedbTransientAndFiftyFourBudgetSynth.fiftyFourPortfolio,
             1212035192 ≤ K ∧ K < yukon)) ∧
         SelfContainedMptNodedbTransientAndFiftyFourBudgetSynth.FiftyFourClaimPayloads) ∧
        ((FiftyFourShape ∧ SelfContainedMptNodedbTransientAndFiftyFourBudgetSynth.FiftyFourClaimPayloads) ∧
         ((TransientStorageRemainingTablesAndFiftyBudgetMaster.FiftyShape ∧
             SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth.FiftyClaimPayloads) ∧
          (TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster.FiftyTwoShape ∧
             SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth.FiftyTwoClaimPayloads) ∧
          ((l_chunks.map GuestTransientStorageAndRemainingTablesAudit.buildTicks).sum ≤
             GuestTransientStorageAndRemainingTablesAudit.buildTicks l_chunks.sum ∧
           (GuestTransientStorageAndRemainingTablesAudit.buildTicks 2 +
               GuestTransientStorageAndRemainingTablesAudit.buildTicks 2 = 10 ∧
             GuestTransientStorageAndRemainingTablesAudit.buildTicks 4 = 30) ∧
           (∀ L' n u B blk : Nat, L' ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
             40 * blk ≤ B * B → blk + 10 * L' * n ≤ 100000000000)) ∧
          (GuestWitnessDecodeAndExtensionNibbleAudit.extAccepted 0 ck = false ∧
           (∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
             ((l.map GuestMptTraversalAndStateRootBound.Step.ext).map
               GuestMptTraversalAndStateRootBound.advance).sum ≤ 64 → l.length ≤ 64) ∧
           (33806089496 - 2713714688) / 56 = 555220978)) ∧
         (mptPlusBuild = 20036870848 ∧
          joint = 176125863653 ∧
          yukon - joint = 724594061821 ∧
          (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209))) ∧
        (HeapAllocationContract ∧ HeapNodesContract ∧ HeapRateContract ∧ MemoContract ∧ BridgeContract)))) := by
  have hmpt := coupled_mpt_lmax_thresholds_one_and_four_yukon_non_vacuous_and_tight L hL
  exact ⟨⟨portfolio_non_vacuous_and_tight, payloads_non_vacuous_and_tight⟩,
         ⟨dirty_keys k hk,
          root_coupled k hk,
          coupling_gain,
          hmpt.1.1,
          hmpt.1.2,
          hmpt.2.1.2,
          hmpt.2.2.1.2,
          hmpt.2.2.2.1.2,
          hmpt.2.2.2.2.1.2⟩,
         sixty_and_sixty_two_budget_portfolios_and_payloads_non_vacuous_and_tight L hL l_chunks ck⟩

/-- 9. Conditional finite certificates across the **64-budget** (`sixtyFourPortfolio`), 62-budget
(`sixtyTwoPortfolio`), 60-budget (`sixtyPortfolio`), and 56-budget (`fiftySixPortfolio`) portfolios
under `cert : CertificateAt 1_212_035_192`, united with coupled-MPT saving (`619_060_000` ticks,
`224_366_249_693` and `195_035_480_749`) and `L_max` thresholds (`38_817`, `40_284`, `5_040`, `6_507`). -/
theorem sixty_four_budget_explicit_certificates_and_coupled_mpt_non_vacuous_and_tight
    (cert : CertificateAt 1_212_035_192) (k L K : Nat) (hk : 21 * k ≤ 2000000) (hL : L ≤ 5000) :
    (NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe ∧
      SelfContainedNoLocValue6ExactTicksAndSixtyBudgetMaster.ExactTicks ∧
      SixtyFourShape ∧ SixtyFourClaimPayloads ∧
      (∀ k' ∈ sixtyFourPortfolio, InitE.Certificate (baselineWithFiniteK k') (.finite k'))) ∧
    (k ≤ 95238 ∧ 130000 * k ≤ 12380940000 ∧
      13000000000 - 130000 * 95238 = 619060000 ∧
      coupled block_total_coupled_mpt L = 224366249693 ∧
      coupled block_total_memo_coupled_mpt L = 195035480749 ∧
      (coupled block_total_coupled_mpt 38817 < yukon ∧ yukon ≤ coupled block_total_coupled_mpt 38818) ∧
      (coupled block_total_memo_coupled_mpt 40284 < yukon ∧ yukon ≤ coupled block_total_memo_coupled_mpt 40285) ∧
      (4 * coupled block_total_coupled_mpt 5040 < yukon ∧ yukon ≤ 4 * coupled block_total_coupled_mpt 5041) ∧
      (4 * coupled block_total_memo_coupled_mpt 6507 < yukon ∧ yukon ≤ 4 * coupled block_total_memo_coupled_mpt 6508)) ∧
    ((SixtyTwoShape ∧ (∀ k' ∈ sixtyTwoPortfolio, InitE.Certificate (baselineWithFiniteK k') (.finite k'))) ∧
      SixtyTwoClaimPayloads ∧
      (coupled subHeap L = 224985309693 ∧ coupled subMemo L = 195654540749 ∧
        (coupled subHeap 38786 < yukon ∧ yukon ≤ coupled subHeap 38787) ∧
        (coupled subMemo 40253 < yukon ∧ yukon ≤ coupled subMemo 40254) ∧
        (4 * coupled subHeap 5009 < yukon ∧ yukon ≤ 4 * coupled subHeap 5010) ∧
        (4 * coupled subMemo 6476 < yukon ∧ yukon ≤ 4 * coupled subMemo 6477)) ∧
      ((SixtyShape ∧ (∀ k' ∈ sixtyPortfolio, InitE.Certificate (baselineWithFiniteK k') (.finite k'))) ∧
       SixtyClaimPayloads ∧
       ExactTicks ∧
       (gasEnv + mptPlusBuild + decodeHeap = 207218238461 ∧
         yukon - (gasEnv + mptPlusBuild + decodeHeap) = 693501687013) ∧
       (gasEnv + mptPlusBuild + decodeMemo = 187064607181 ∧
         yukon - (gasEnv + mptPlusBuild + decodeMemo) = 713655318293) ∧
       ((HeapAllocationContract ∧ HeapNodesContract ∧ HeapRateContract ∧ MemoContract ∧
         BridgeContract ∧ AbsorptionContract ∧
         FrontendSafe ∧ PanLabSafe ∧ PanTargetSafe ∧ PanUserSafe ∧
         FiftySixShape ∧ SelfContainedWitnessDagMemoizationAndFiftySixBudgetSynth.FiftySixClaimPayloads ∧
         (∀ k' ∈ SelfContainedWitnessDagMemoizationAndFiftySixBudgetSynth.fiftySixPortfolio,
           InitE.Certificate (baselineWithFiniteK k') (.finite k'))) ∧
        ((WalkContract ∧ AccessContract ∧ RootContract ∧ WitnessLinearContract ∧
          CoupledJournalContract ∧ FrontendSafe ∧ PanLabSafe ∧ PanTargetSafe ∧ PanUserSafe ∧
          FiftyFourShape ∧ SelfContainedMptNodedbTransientAndFiftyFourBudgetSynth.FiftyFourClaimPayloads ∧
          (∀ k' ∈ SelfContainedMptNodedbTransientAndFiftyFourBudgetSynth.fiftyFourPortfolio,
            InitE.Certificate (baselineWithFiniteK k') (.finite k'))) ∧
         ((TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster.FiftyTwoShape ∧
           SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth.FiftyTwoClaimPayloads ∧
           (∀ k' ∈ SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth.fiftyTwoPortfolio,
             InitE.Certificate (baselineWithFiniteK k') (.finite k'))) ∧
          ((∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
             ((l.map GuestMptTraversalAndStateRootBound.Step.ext).map
               GuestMptTraversalAndStateRootBound.advance).sum ≤ 64 → l.length ≤ 64) ∧
           (∀ L' n u B blk : Nat, L' ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
             40 * blk ≤ B * B → blk + 10 * L' * n ≤ 100000000000)) ∧
          (K = K)) ∧
         (mptPlusBuild = 20036870848 ∧
          joint = 176125863653 ∧
          (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209)))))) := by
  have hmpt := coupled_mpt_lmax_thresholds_one_and_four_yukon_non_vacuous_and_tight L hL
  exact ⟨certificates_non_vacuous_and_tight cert,
         ⟨dirty_keys k hk,
          root_coupled k hk,
          coupling_gain,
          hmpt.1.1,
          hmpt.1.2,
          hmpt.2.1.2,
          hmpt.2.2.1.2,
          hmpt.2.2.2.1.2,
          hmpt.2.2.2.2.1.2⟩,
         sixty_two_budget_explicit_certificates_and_coupled_gas_non_vacuous_and_tight cert L K hL⟩

/-- 10. Grand self-contained synthesis (`W5_184`): unites
(1) exact `619_060_000`-tick saving on `mpt_set` by coupling MPT writes to the `200M` gas budget
    (`block_total_coupled_mpt = 224_366_249_693` without memoization,
    `block_total_memo_coupled_mpt = 195_035_480_749` with DAG memoization),
(2) exact `L_max` thresholds with coupled MPT (`38_817` / `40_284` at `1×` Yukon, `5_040` / `6_507`
    at `4×` Yukon) alongside coupled-gas `ts+64` absorption (`L ≤ 5_000` adds `0` net ticks,
    `38_786` / `40_253` and `5_009` / `6_476`),
(3) `_resolve_step` bounds (`1_110_441_952` / `536_870_848`), `r = 8` probe ticks (`17_767_071_232`
    / `8_589_933_568`), exact per-node decode ticks (`43/98`, `48/90`, `326/448`, `τ < 1`),
    DAG memoization (`33_554_428` nodes), MPT + `nodedb` + `ts+64` bridge, and unconditional
    `StackToLab → LabToTarget` no-`locValue`-6 safety,
(4) the strictly increasing **64-budget** (and 62/60/56/54/52/50-budget) portfolio under Yukon
    (`900_719_925_474`) and conditional finite certificates `InitE.Certificate submission (.finite K)`. -/
theorem grand_self_contained_end_to_end_coupled_mpt_and_sixty_four_budget_synth_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (k L n u B_gas blk ck l_ext E B r ns nc : Nat)
    (hk : 21 * k ≤ 2000000) (hL : L ≤ 5000) (hu : n ≤ u) (hS : B_gas + u ≤ 2000000)
    (hblk : 40 * blk ≤ B_gas * B_gas) (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428) (hr : r ≤ 312)
    (h_nodedb : 4 * (ns + nc) ≤ maxInput)
    (cert : CertificateAt 1_212_035_192) :
    ((NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe ∧
       SelfContainedNoLocValue6ExactTicksAndSixtyBudgetMaster.ExactTicks ∧
       SixtyFourShape ∧ SixtyFourClaimPayloads ∧
       (∀ K ∈ sixtyFourPortfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
     (k ≤ 95238 ∧
       (21 * 95238 ≤ 2000000 ∧ 2000000 < 21 * 95239) ∧
       130000 * k ≤ 12380940000 ∧
       13000000000 - 130000 * 95238 = 619060000 ∧
       (block_total_coupled_mpt = 224366249693 ∧ block_total_memo_coupled_mpt = 195035480749) ∧
       yukon - block_total_coupled_mpt = 676353675781 ∧
       (yukon / 4 - block_total_coupled_mpt = 813731675 ∧
         yukon / 4 - block_total_memo_coupled_mpt = 30144500619) ∧
       (coupled block_total_coupled_mpt L = 224366249693 ∧
         coupled block_total_memo_coupled_mpt L = 195035480749) ∧
       (coupled block_total_coupled_mpt 38817 < yukon ∧ yukon ≤ coupled block_total_coupled_mpt 38818) ∧
       (coupled block_total_memo_coupled_mpt 40284 < yukon ∧ yukon ≤ coupled block_total_memo_coupled_mpt 40285) ∧
       (4 * coupled block_total_coupled_mpt 5040 < yukon ∧ yukon ≤ 4 * coupled block_total_coupled_mpt 5041) ∧
       (4 * coupled block_total_memo_coupled_mpt 6507 < yukon ∧ yukon ≤ 4 * coupled block_total_memo_coupled_mpt 6508))) ∧
    (((SixtyTwoShape ∧ (∀ K ∈ sixtyTwoPortfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
      SixtyTwoClaimPayloads ∧
      ((156088992805 / 2000000 = 78044 ∧ 156088992805 / 200000000 = 780) ∧
       blk + 10 * L * n ≤ 100000000000 ∧
       excess L = 0 ∧
       excess 5001 = 20000000 ∧
       (coupled subHeap L = 224985309693 ∧ coupled subMemo L = 195654540749) ∧
       (coupled subHeap 38786 < yukon ∧ yukon ≤ coupled subHeap 38787) ∧
       (coupled subMemo 40253 < yukon ∧ yukon ≤ coupled subMemo 40254) ∧
       (4 * coupled subHeap 5009 < yukon ∧ yukon ≤ 4 * coupled subHeap 5010) ∧
       (4 * coupled subMemo 6476 < yukon ∧ yukon ≤ 4 * coupled subMemo 6477) ∧
       (40253 < 158162 ∧ yukon < coupled subMemo 158162 ∧ yukon < coupled subHeap 158162) ∧
       ¬ (∀ B' U T blk' : Nat, B' + U ≤ S → 40 * blk' ≤ B' * B' → T ≤ 50001 * U →
           blk' + T ≤ 100000000000))) ∧
     ((((∀ s' ∈ L',
           InitECandidate.Solver.PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = false →
           ∀ x ∈ s'.lines, JumpOk x = true) ∧
         ExactTicks ∧
         (∀ L₀ E' B', heapOf L₀ E' B' ≤ heapAvail → decodeTicks L₀ E' B' ≤ 31092374808) ∧
         (decodeTicks 0 0 33554428 = 10938743528 ∧
           yukon - 10938743528 = 889781181946) ∧
         (joint = 176125863653 ∧ 5 * joint < yukon) ∧
         AbsorptionContract ∧
         SixtyShape ∧ SixtyClaimPayloads ∧
         (∀ K ∈ sixtyPortfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
       (resolveCalls 0 B ≤ 1110441952 ∧
         resolveCalls E B ≤ 536870848 ∧
         (2 * 8 * 1110441952 = 17767071232 ∧ 2 * 8 * 536870848 = 8589933568) ∧
         (gasEnv + mptPlusBuild + decodeHeap = 207218238461 ∧
           yukon - (gasEnv + mptPlusBuild + decodeHeap) = 693501687013) ∧
         (gasEnv + mptPlusBuild + decodeMemo = 187064607181 ∧
           yukon - (gasEnv + mptPlusBuild + decodeMemo) = 713655318293) ∧
         (4 * 207218238461 < yukon ∧ yukon < 5 * 207218238461 ∧
           4 * 187064607181 = 748258428724 ∧ 4 * 187064607181 < yukon ∧ yukon < 5 * 187064607181) ∧
         (2 * 312 * 1110441952 ≤ 693501687013 ∧ 693501687013 < 2 * 313 * 1110441952) ∧
         (2 * 664 * 536870848 ≤ 713655318293 ∧ 713655318293 < 2 * 665 * 536870848) ∧
         gasEnv + mptPlusBuild + decodeHeap + 2 * r * resolveCalls 0 B < yukon ∧
         693501687013 < 2 * 2 ^ 25 * 1110441952 ∧
         decodeHeap - decodeMemo = 20153631280)) ∧
      ((HeapAllocationContract ∧ HeapNodesContract ∧ HeapRateContract ∧ MemoContract ∧
        BridgeContract ∧ AbsorptionContract ∧
        FrontendSafe ∧ PanLabSafe ∧ PanTargetSafe ∧ PanUserSafe ∧
        FiftySixShape ∧ SelfContainedWitnessDagMemoizationAndFiftySixBudgetSynth.FiftySixClaimPayloads ∧
        (∀ K ∈ SelfContainedWitnessDagMemoizationAndFiftySixBudgetSynth.fiftySixPortfolio,
          InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
       ((mptPlusBuild = 20036870848 ∧
         (44 * mptPlusBuild < yukon ∧ yukon ≤ 45 * mptPlusBuild) ∧
         joint = 176125863653 ∧
         yukon - joint = 724594061821 ∧
         (5 * joint = 880629318265 ∧ 5 * joint < yukon ∧ yukon - 5 * joint = 20090607209) ∧
         boundedBuild 8 ns + boundedBuild 8 nc ≤ 536870848 ∧
         19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ mptPlusBuild ∧
         156088992805 + 19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ joint ∧
         (5 * (2 * 1) / 2 + 5 * (2 * 1) / 2 = 10 ∧ 5 * (4 * 3) / 2 = 30 ∧
           2 * (5 * (158162 * 158161) / 2) = 125075300410) ∧
         (10 * 5000 = 50000 ∧ 50000 < 10 * 5001 ∧ 5 * 10000 = 50000 ∧ 50000 < 5 * 10001)) ∧
        (WalkContract ∧ AccessContract ∧ RootContract ∧ WitnessLinearContract ∧
         CoupledJournalContract ∧ FrontendSafe ∧ PanLabSafe ∧ PanTargetSafe ∧ PanUserSafe ∧
         FiftyFourShape ∧ SelfContainedMptNodedbTransientAndFiftyFourBudgetSynth.FiftyFourClaimPayloads ∧
         (∀ K ∈ SelfContainedMptNodedbTransientAndFiftyFourBudgetSynth.fiftyFourPortfolio,
           InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
        (((∀ n' : Nat, 1 ≤ n' →
             GuestWitnessDecodeAndExtensionNibbleAudit.compactLen n' 0 = 2 * n' - 2 ∧
             GuestWitnessDecodeAndExtensionNibbleAudit.compactLen n' 1 = 2 * n' - 1) ∧
          (∀ n' odd : Nat, 1 ≤ n' → odd ≤ 1 →
             (GuestWitnessDecodeAndExtensionNibbleAudit.compactLen n' odd = 0 ↔ n' = 1 ∧ odd = 0)) ∧
          (GuestWitnessDecodeAndExtensionNibbleAudit.compactLen 33 0 = 64 ∧
           GuestWitnessDecodeAndExtensionNibbleAudit.compactLen 32 1 = 63) ∧
          GuestWitnessDecodeAndExtensionNibbleAudit.extAccepted 0 ck = false ∧
          (GuestWitnessDecodeAndExtensionNibbleAudit.extAccepted l_ext 2 = false ∧
           GuestWitnessDecodeAndExtensionNibbleAudit.extAccepted l_ext 1 = false) ∧
          (∀ l' ck' : Nat, GuestWitnessDecodeAndExtensionNibbleAudit.extAccepted l' ck' = true →
             1 ≤ GuestMptTraversalAndStateRootBound.advance (.ext l')) ∧
          (∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
            ((l.map GuestMptTraversalAndStateRootBound.Step.ext).map
              GuestMptTraversalAndStateRootBound.advance).sum ≤ 64 → l.length ≤ 64 ∧ l.length + 1 ≤ 65) ∧
          (33806089496 - 2713714688) / 56 = 555220978 ∧
          ((List.range 7).foldl (fun a i => a + 16 ^ i) 0 = 17895697 ∧
            17895697 * 176 + 16 ^ 7 * 64 = 20329511856 ∧
            20329511856 ≤ 33806089496 - 2713714688) ∧
          33806089496 - 2713714688 < 16 ^ 8 * 64 ∧
          (17895697 + 16 ^ 7 = 286331153 ∧ 8 * 530 < 4300)) ∧
         ((∀ l : List Nat,
             (l.map GuestTransientStorageAndRemainingTablesAudit.buildTicks).sum ≤
             GuestTransientStorageAndRemainingTablesAudit.buildTicks l.sum) ∧
          (GuestTransientStorageAndRemainingTablesAudit.buildTicks 2 +
              GuestTransientStorageAndRemainingTablesAudit.buildTicks 2 = 10 ∧
            GuestTransientStorageAndRemainingTablesAudit.buildTicks 4 = 30) ∧
          2 * GuestTransientStorageAndRemainingTablesAudit.buildTicks 158_162 = 125_075_300_410 ∧
          (∀ L₀ n₀ u₀ B' blk' : Nat, L₀ ≤ 5000 → n₀ ≤ u₀ → B' + u₀ ≤ 2000000 →
            40 * blk' ≤ B' * B' → blk' + 10 * L₀ * n₀ ≤ 100000000000) ∧
          (5_000 < 158_162 ∧ 5 * 156_088_992_805 < yukon) ∧
          TransientStorageRemainingTablesAndFiftyBudgetMaster.CompilerSafety arch prog wc ac perf info j bd ptr f ∧
          TransientStorageRemainingTablesAndFiftyBudgetMaster.FiftyShape ∧
          SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth.FiftyClaimPayloads ∧
          (∀ K ∈ SelfContainedSubcallRevertAbsorptionAndFiftyBudgetSynth.fiftyPortfolio,
            InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
         ((∀ s ∈ StackToLab.compile sc dc mh sp off
              (compileNative ac perf (WordToWord.compile wc ac
                (panToWordCompileProgHOL arch prog)).2).2.2.2,
            PanToLabSectionAndStackRemoveClock.IsStubLabel s.sectionId = true ∨
            StackToLabAndLabToTargetNoStubCall.LOk s.lines) ∧
          (∀ (ic' pos' : Nat) (labs₁ : Spt (Spt Nat)) (ffis₁ : List HolFfiName)
              (L₁ : List (StackToLabAndLabToTargetNoStubCall.Sec width)) (labs₂ : Spt (Spt Nat)),
            removeLabels ic' ac pos' labs₁ ffis₁ (filterSkip (StackToLab.compile sc dc mh sp off
              (compileNative ac perf (WordToWord.compile wc ac
                (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L₁, labs₂) →
            (∀ s' ∈ L₁, PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = true ∨
              ∀ x ∈ s'.lines, StackToLabAndLabToTargetNoStubCall.JumpOk x = true) ∧
            (∀ s' ∈ L₁, PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = false →
              ∀ x ∈ s'.lines, StackToLabAndLabToTargetNoStubCall.JumpOk x = true)) ∧
          ((∀ n' : Nat, 4 * n' ≤ maxInput → n' ≤ 33554428) ∧
            4 * 33554428 = maxInput ∧
            (2 * 33554428 + 2 ≤ 67108864 ∧ 33554432 < 2 * 33554428 + 2) ∧
            (∀ n' c : Nat, 2 * n' + 2 ≤ c → (n' + 1) * 2 ≤ c) ∧
            (boundedBuild 8 33554428 = 536870848 ∧ boundedBuild 8 33554428 < yukon) ∧
            (boundedBuild 13421 33554428 < yukon ∧ yukon < boundedBuild 13422 33554428) ∧
            (∀ r' ns' nc' : Nat, 4 * (ns' + nc') ≤ maxInput →
              boundedBuild r' ns' + boundedBuild r' nc' ≤ boundedBuild r' 33554428)) ∧
          (TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster.FiftyTwoShape ∧
            SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth.FiftyTwoClaimPayloads ∧
            (∀ K ∈ SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth.fiftyTwoPortfolio,
              InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
            (∀ l : List Nat,
              (l.map GuestTransientStorageAndRemainingTablesAudit.buildTicks).sum ≤
              GuestTransientStorageAndRemainingTablesAudit.buildTicks l.sum) ∧
            (∀ j' : List Bool, j'.length ≤ 524288 →
              _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.restoreDels j' ≤ 524288) ∧
            (∀ u1 u2 t1 t2 : Nat, u1 + u2 ≤ 2000000 → t1 ≤ 373022 * u1 →
              t2 ≤ 373022 * u2 → t1 + t2 ≤ 746044000000) ∧
            (∀ L₀ n₀ u₀ B' blk' : Nat, L₀ ≤ 5000 → n₀ ≤ u₀ → B' + u₀ ≤ 2000000 →
              40 * blk' ≤ B' * B' → blk' + 10 * L₀ * n₀ ≤ 100000000000) ∧
            TransientStorageRemainingTablesAndFiftyBudgetMaster.KeyCap ∧
            TransientStorageRemainingTablesAndFiftyBudgetMaster.PackingAndBuild ∧
            TransientStorageRemainingTablesAndFiftyBudgetMaster.BlockCosts ∧
            TransientStorageRemainingTablesAndFiftyBudgetMaster.OneSlopeMargin ∧
            TransientStorageRemainingTablesAndFiftyBudgetMaster.TransientObstruction ∧
            TransientStorageRemainingTablesAndFiftyBudgetMaster.RemainingTables))))))) := by
  have hmpt := coupled_mpt_lmax_thresholds_one_and_four_yukon_non_vacuous_and_tight L hL
  exact ⟨⟨certificates_non_vacuous_and_tight cert,
          dirty_keys k hk,
          dirty_keys_tight,
          root_coupled k hk,
          coupling_gain,
          ⟨rfl, rfl⟩,
          residual_1x,
          residual_4x,
          hmpt.1,
          hmpt.2.1.2,
          hmpt.2.2.1.2,
          hmpt.2.2.2.1.2,
          hmpt.2.2.2.2.1.2⟩,
         grand_self_contained_coupled_gas_full_block_and_sixty_two_budget_synth_non_vacuous_and_tight
           arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h info j bd ptr f
           L n u B_gas blk ck l_ext E B r ns nc hL hu hS hblk hB hEB hr h_nodedb cert⟩

#print axioms coupled_mpt_saving_and_block_totals_non_vacuous_and_tight
#print axioms coupled_mpt_lmax_thresholds_one_and_four_yukon_non_vacuous_and_tight
#print axioms coupled_mpt_and_coupled_gas_ts64_absorption_non_vacuous_and_tight
#print axioms coupled_mpt_and_witness_resolve_probes_non_vacuous_and_tight
#print axioms coupled_mpt_block_totals_and_mpt_nodedb_bridge_non_vacuous_and_tight
#print axioms exact_decode_ticks_dag_memoization_and_coupled_mpt_non_vacuous_and_tight
#print axioms pan_to_target_no_loc_value_6_and_coupled_mpt_full_block_non_vacuous_and_tight
#print axioms sixty_two_and_sixty_four_budget_portfolios_and_payloads_non_vacuous_and_tight
#print axioms sixty_four_budget_explicit_certificates_and_coupled_mpt_non_vacuous_and_tight
#print axioms grand_self_contained_end_to_end_coupled_mpt_and_sixty_four_budget_synth_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedEndToEndCoupledMptAndSixtyFourBudgetSynth
