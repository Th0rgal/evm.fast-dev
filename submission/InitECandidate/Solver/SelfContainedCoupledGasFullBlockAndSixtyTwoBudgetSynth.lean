import InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster
import InitECandidate.Solver.SelfContainedWitnessResolveBlockTotalTicksAndSixtyBudgetSynth
import InitECandidate.Solver.WitnessResolveBlockTotalTicksAndSixtyTwoBudgetMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedCoupledGasFullBlockAndSixtyTwoBudgetSynth`

Self-contained Wave 5 synthesis (`W5_178`, `0` imports from `InitECandidate.Proofs.Bounded*`)
uniting:
1. **`GuestCoupledGasFullBlockWithProbesAndTransientMaster` (`12/12` tight)**:
   - Exact absorption of `ts+64` under the shared `200M` gas budget (`general_side_regime_absorption`:
     every side regime `≤ 50_000` ticks per 100-gas unit is absorbed in the quadratic `10¹¹` term,
     and `50_001` is sharp), so `ts+64` at `10 · L` ticks/unit adds `0` net ticks for all
     `L ≤ 5_000` (`excess L = 0`, `excess 5001 = 20_000_000`), leaving the full block at
     `224_985_309_693` without memoization and `195_654_540_749` with DAG memoization,
   - Exact coupled-gas `L_max` thresholds: `38_786` (heap) and `40_253` (memo) at `1×` Yukon,
     and `5_009` (heap) and `6_476` (memo) at `4×` Yukon, while unsalted `158_162` still exceeds `1×`.
2. **`SelfContainedWitnessResolveBlockTotalTicksAndSixtyBudgetSynth` (`10/10` tight)**:
   - `_resolve_step` call bounds (`≤ 1_110_441_952` heap, `≤ 536_870_848` memo), `r = 8` probe ticks
     (`17_767_071_232` and `8_589_933_568`), probe thresholds `r ≤ 312` and `r ≤ 664`,
     conditional block totals (`207_218_238_461` and `187_064_607_181`), exact per-node decode ticks
     (`43 < 98`, `48 < 90`, `326 < 448`, `τ < 1`), DAG memoization (`33_554_428` nodes),
     MPT + `nodedb` (`20_036_870_848`) + `ts+64` (`176_125_863_653`) bridge, unconditional
     `StackToLab → LabToTarget` no-`locValue`-6 safety, and 50/52/54/56/60-budget portfolios.
3. **`WitnessResolveBlockTotalTicksAndSixtyTwoBudgetMaster` (`12/12` tight)**:
   - Strictly increasing **62-budget** portfolio (`SixtyTwoShape`, `ClaimPayloads`) below Yukon
     (`900_719_925_474`) and conditional finite certificate lifting (`certificates_non_vacuous_and_tight`).
-/

namespace InitECandidate.Solver.SelfContainedCoupledGasFullBlockAndSixtyTwoBudgetSynth

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit (
  tLeaf tExt tBranch decodeTicks ticks_le_heap decode_linear decode_memo decode_memo_val decode_under_5x
)
open InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound (
  heapAvail heapOf branches_by_heap
)
open InitECandidate.Solver.GuestNodedbAndWitnessTableBound (
  maxInput boundedBuild
)
open InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge (
  mptPlusBuild joint
)
open InitECandidate.Solver.GuestWitnessResolveAndBlockTotalTicksSynthesis (
  gasEnv
  decodeHeap
  decodeMemo
  resolveCalls
  resolve_heap
  resolve_memo
  probe_at_8
  block_total
  block_total_memo
  slope_four
  r_threshold_heap
  r_threshold_memo
  total_with_probes
  unsalted_breaks
  memo_saving
)
open InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster (
  subHeap
  subMemo
  tsTicks
  total
  sub_vals
  sub_slopes
  ts_block
  under_cap_memo
  under_cap_memo4
  unsalted_exceeds
  salted_four
)
open InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster (
  excess
  coupled
  avg_slope
  absorbed
  excess_zero
  excess_first
  block_unchanged
  seventy_eight_inside
  lmax1_heap
  lmax1_memo
  lmax4_heap
  lmax4_memo
  unsalted_still_fails
  sharp
)
open InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption (
  general_side_regime_absorption S
)
open InitECandidate.Solver.WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster (
  HeapAllocationContract
  HeapNodesContract
  HeapRateContract
  MemoContract
  BridgeContract
  AbsorptionContract
  FiftySixShape
)
open InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster (
  FiftyFourShape
  WalkContract
  AccessContract
  RootContract
  WitnessLinearContract
  CoupledJournalContract
  PanLabSafe
  PanTargetSafe
  PanUserSafe
  FrontendSafe
)
open InitECandidate.Solver.StackToLabAndLabToTargetNoLocValue6 (
  J JC AOk LOk JumpOk Sec
)
open InitECandidate.Solver.WitnessDecodeExactTicksNoLocValue6AndSixtyBudgetMaster (
  ExactTicks
  SixtyShape
)
open InitECandidate.Solver.SelfContainedWitnessResolveBlockTotalTicksAndSixtyBudgetSynth (
  sixtyPortfolio
  SixtyClaimPayloads
  witness_resolve_step_calls_probes_and_thresholds_non_vacuous_and_tight
  conditional_block_total_and_four_slope_synthesis_non_vacuous_and_tight
  exact_decode_ticks_per_byte_and_dag_memoization_non_vacuous_and_tight
  resolve_block_totals_and_mpt_nodedb_bridge_non_vacuous_and_tight
  pan_to_target_no_stub_jump_or_loc_value_and_compiler_safety_non_vacuous_and_tight
  witness_decode_resolve_block_totals_and_no_loc_value_6_non_vacuous_and_tight
  fifty_six_and_sixty_budget_portfolios_and_payloads_non_vacuous_and_tight
  sixty_budget_explicit_certificates_and_block_totals_non_vacuous_and_tight
  integrated_sixty_budget_and_resolve_block_total_master_non_vacuous_and_tight
  grand_self_contained_witness_resolve_block_total_ticks_and_sixty_budget_synth_non_vacuous_and_tight
)
open InitECandidate.Solver.WitnessResolveBlockTotalTicksAndSixtyTwoBudgetMaster (
  portfolio
  sixtyTwoClaims
  SixtyTwoShape
  ClaimPayloads
  resolve_heap_non_vacuous_and_tight
  resolve_memo_non_vacuous_and_tight
  probes_at_eight_non_vacuous_and_tight
  probe_thresholds_non_vacuous_and_tight
  block_total_non_vacuous_and_tight
  block_total_memo_non_vacuous_and_tight
  slope_four_non_vacuous_and_tight
  no_loc_value_6_non_vacuous_and_tight
  portfolio_non_vacuous_and_tight
  payloads_non_vacuous_and_tight
  certificates_non_vacuous_and_tight
  integrated_master_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

variable {width : Nat} [NeZero width]

abbrev sixtyTwoPortfolio : List Nat :=
  InitECandidate.Solver.WitnessResolveBlockTotalTicksAndSixtyTwoBudgetMaster.portfolio

abbrev SixtyTwoClaimPayloads : Prop :=
  InitECandidate.Solver.WitnessResolveBlockTotalTicksAndSixtyTwoBudgetMaster.ClaimPayloads

/-! ## Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- 1. Exact absorption of `ts+64` under the shared `200M` gas budget (`general_side_regime_absorption`):
every side regime `≤ 50_000` ticks per 100-gas unit is absorbed in the quadratic `10¹¹` term
(`50_001` is sharp), so `ts+64` at `10 · L` ticks/unit adds `0` net ticks for all `L ≤ 5_000`
(`excess L = 0`, `excess 5001 = 20_000_000`), leaving the full block at `224_985_309_693` without
memoization and `195_654_540_749` with DAG memoization. -/
theorem coupled_gas_ts64_absorption_and_unchanged_block_totals_non_vacuous_and_tight
    (L n u B blk : Nat) (hL : L ≤ 5000) (hu : n ≤ u) (hS : B + u ≤ 2000000)
    (hblk : 40 * blk ≤ B * B) :
    (156088992805 / 2000000 = 78044 ∧ 156088992805 / 200000000 = 780) ∧
    blk + 10 * L * n ≤ 100000000000 ∧
    excess L = 0 ∧
    excess 5001 = 20000000 ∧
    (coupled subHeap L = 224985309693 ∧ coupled subMemo L = 195654540749) ∧
    (subHeap = 224985309693 ∧ subMemo = 195654540749) ∧
    (4 * subMemo = 782618162996 ∧ 4 * subMemo < yukon ∧ 4 * subHeap < yukon ∧
      yukon < 5 * subMemo) ∧
    (78 ≤ 5000 ∧ excess 78 = 0) ∧
    ¬ (∀ B' U T blk' : Nat, B' + U ≤ S → 40 * blk' ≤ B' * B' → T ≤ 50001 * U →
        blk' + T ≤ 100000000000) :=
  ⟨avg_slope,
   absorbed L n u B blk hL hu hS hblk,
   excess_zero L hL,
   excess_first,
   block_unchanged L hL,
   sub_vals,
   sub_slopes,
   seventy_eight_inside,
   sharp⟩

/-- 2. Exact coupled-gas `L_max` thresholds (`38_786` heap / `40_253` memo at `1×` Yukon, and
`5_009` heap / `6_476` memo at `4×` Yukon), contrasted with additive thresholds (`33_786` / `35_253`
at `1×`, `9` / `1_476` at `4×`), salted `L = 8` (`4×` under Yukon), and unsalted `158_162` failure. -/
theorem coupled_gas_lmax_thresholds_one_and_four_yukon_non_vacuous_and_tight
    (L : Nat) (hL : L ≤ 5000) :
    (coupled subHeap 38786 < yukon ∧ yukon ≤ coupled subHeap 38787) ∧
    (coupled subMemo 40253 < yukon ∧ yukon ≤ coupled subMemo 40254) ∧
    (4 * coupled subHeap 5009 < yukon ∧ yukon ≤ 4 * coupled subHeap 5010) ∧
    (4 * coupled subMemo 6476 < yukon ∧ yukon ≤ 4 * coupled subMemo 6477) ∧
    (40253 < 158162 ∧ yukon < coupled subMemo 158162 ∧ yukon < coupled subHeap 158162) ∧
    (coupled subHeap L = 224985309693 ∧ coupled subMemo L = 195654540749) ∧
    (total subHeap 33786 < yukon ∧ yukon ≤ total subHeap 33787) ∧
    (total subMemo 35253 < yukon ∧ yukon ≤ total subMemo 35254) ∧
    (4 * total subHeap 9 < yukon ∧ yukon ≤ 4 * total subHeap 10) ∧
    (4 * total subMemo 1476 < yukon ∧ yukon ≤ 4 * total subMemo 1477) ∧
    (4 * total subHeap 8 < yukon ∧ 4 * total subMemo 8 < yukon) :=
  ⟨lmax1_heap,
   lmax1_memo,
   lmax4_heap,
   lmax4_memo,
   unsalted_still_fails,
   block_unchanged L hL,
   GuestFullBlockWithTransientStorageAndProbesMaster.lmax1_heap,
   GuestFullBlockWithTransientStorageAndProbesMaster.lmax1_memo,
   GuestFullBlockWithTransientStorageAndProbesMaster.lmax4_heap,
   GuestFullBlockWithTransientStorageAndProbesMaster.lmax4_memo,
   salted_four⟩

/-- 3. Synthesis of coupled-gas full-block absorption (`224_985_309_693` / `195_654_540_749`) and
`L_max` thresholds (`38_786` / `40_253` at `1×`, `5_009` / `6_476` at `4×`) with `_resolve_step`
call bounds (`1_110_441_952` heap, `536_870_848` memo), `r = 8` probe ticks (`17_767_071_232` and
`8_589_933_568`), and probe thresholds (`r ≤ 312`, `r ≤ 664`). -/
theorem coupled_gas_full_block_and_witness_resolve_probes_non_vacuous_and_tight
    (L n u B_gas blk E B r : Nat) (hL : L ≤ 5000) (hu : n ≤ u) (hS : B_gas + u ≤ 2000000)
    (hblk : 40 * blk ≤ B_gas * B_gas) (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428) (hr : r ≤ 312) :
    (blk + 10 * L * n ≤ 100000000000 ∧
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
      693501687013 < 2 * 2 ^ 25 * 1110441952) :=
  ⟨⟨absorbed L n u B_gas blk hL hu hS hblk,
    excess_zero L hL,
    (block_unchanged L hL).1,
    (block_unchanged L hL).2,
    lmax1_heap,
    lmax1_memo,
    lmax4_heap,
    lmax4_memo⟩,
   resolve_heap_non_vacuous_and_tight,
   resolve_memo_non_vacuous_and_tight,
   probes_at_eight_non_vacuous_and_tight,
   probe_thresholds_non_vacuous_and_tight,
   witness_resolve_step_calls_probes_and_thresholds_non_vacuous_and_tight E B r hB hEB hr⟩

/-- 4. Synthesis of coupled-gas full-block totals (`224_985_309_693` and `195_654_540_749` with
`r = 8` probes and `ts+64` absorbed for `L ≤ 5_000`) and conditional pre-probe subtotals
(`207_218_238_461` and `187_064_607_181`, saving `20_153_631_280`) with the MPT + `nodedb`
(`20_036_870_848`) + `ts+64` (`176_125_863_653`, `5× = 880_629_318_265`) bridge. -/
theorem coupled_gas_block_totals_and_mpt_nodedb_bridge_non_vacuous_and_tight
    (L E B r ns nc : Nat) (hL : L ≤ 5000) (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428)
    (hr : r ≤ 312) (h_nodedb : 4 * (ns + nc) ≤ maxInput) :
    (coupled subHeap L = 224985309693 ∧ coupled subMemo L = 195654540749) ∧
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
         (10 * 5000 = 50000 ∧ 50000 < 10 * 5001 ∧ 5 * 10000 = 50000 ∧ 50000 < 5 * 10001)))) :=
  ⟨block_unchanged L hL,
   sub_slopes,
   ⟨lmax1_heap.1, lmax1_heap.2, lmax1_memo.1, lmax1_memo.2,
    lmax4_heap.1, lmax4_heap.2, lmax4_memo.1, lmax4_memo.2⟩,
   resolve_block_totals_and_mpt_nodedb_bridge_non_vacuous_and_tight E B r ns nc hB hEB hr h_nodedb⟩

/-- 5. Exact per-node decode ticks (`tLeaf = 43 < 98`, `tExt = 48 < 90`, `tBranch = 326 < 448`),
per-byte rate `τ < 1`, and DAG memoization (`33_554_428` nodes, `10_938_743_528` decode ticks)
synthesized with coupled-gas `ts+64` absorption (`L ≤ 5_000`) and `L_max` thresholds (`38_786`,
`40_253`, `5_009`, `6_476`). -/
theorem exact_decode_ticks_dag_memoization_and_coupled_gas_non_vacuous_and_tight
    (L_run L E B n : Nat) (hL : L_run ≤ 5000)
    (h_heap : heapOf L E B ≤ heapAvail) (h_br : heapOf 0 0 B ≤ heapAvail)
    (hn : 4 * n ≤ 134217712) (h_memo : L + E + B ≤ n) :
    (excess L_run = 0 ∧
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
          58 * 15300819168 < yukon ∧ yukon < 59 * 15300819168))) :=
  ⟨⟨excess_zero L_run hL,
    (block_unchanged L_run hL).1,
    (block_unchanged L_run hL).2,
    lmax1_heap,
    lmax1_memo,
    lmax4_heap,
    lmax4_memo⟩,
   exact_decode_ticks_per_byte_and_dag_memoization_non_vacuous_and_tight L E B n h_heap h_br hn h_memo⟩

/-- 6. Unconditional `StackToLab → LabToTarget` absence of `jump`, `jumpCmp`, `call`, and `locValue`
into section 6 (`no_loc_value_6_non_vacuous_and_tight`, `JumpOk`) synthesized with coupled-gas
full-block totals (`224_985_309_693` and `195_654_540_749`) and `L_max` thresholds (`38_786` / `40_253`
at `1×`, `5_009` / `6_476` at `4×`). -/
theorem pan_to_target_no_loc_value_6_and_coupled_gas_full_block_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (L E B r : Nat) (hL : L ≤ 5000) (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428) (hr : r ≤ 312) :
    (NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
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
        JC (.locValue 0 storeConstsStubLocation 0 : HolProg width) = false)) :=
  ⟨no_loc_value_6_non_vacuous_and_tight,
   ⟨(block_unchanged L hL).1, (block_unchanged L hL).2,
    lmax1_heap, lmax1_memo, lmax4_heap, lmax4_memo⟩,
   witness_decode_resolve_block_totals_and_no_loc_value_6_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h E B r hB hEB hr⟩

/-- 7. Strictly increasing **62-budget** (`SixtyTwoShape`, `SixtyTwoClaimPayloads`), 60-budget
(`SixtyShape`, `SixtyClaimPayloads`), 56-budget, 54-budget, 52-budget, and 50-budget portfolios
and JSON claim payloads below Yukon (`900_719_925_474`), coupled with full-block `ts+64` absorption
and `L_max` thresholds (`38_786`, `40_253`, `5_009`, `6_476`). -/
theorem sixty_and_sixty_two_budget_portfolios_and_payloads_non_vacuous_and_tight
    (L : Nat) (hL : L ≤ 5000) (l_chunks : List Nat) (ck : Nat) :
    (SixtyTwoShape ∧ SixtyTwoClaimPayloads) ∧
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
      (HeapAllocationContract ∧ HeapNodesContract ∧ HeapRateContract ∧ MemoContract ∧ BridgeContract))) :=
  ⟨⟨portfolio_non_vacuous_and_tight, payloads_non_vacuous_and_tight⟩,
   ⟨(block_unchanged L hL).1, (block_unchanged L hL).2,
    lmax1_heap, lmax1_memo, lmax4_heap, lmax4_memo⟩,
   fifty_six_and_sixty_budget_portfolios_and_payloads_non_vacuous_and_tight l_chunks ck⟩

/-- 8. Conditional finite certificates across the **62-budget** (`sixtyTwoPortfolio`), 60-budget
(`sixtyPortfolio`), and 56-budget (`fiftySixPortfolio`) portfolios under
`cert : CertificateAt 1_212_035_192`, united with coupled-gas `ts+64` absorption (`L ≤ 5_000`) and
`L_max` thresholds (`38_786`, `40_253`, `5_009`, `6_476`). -/
theorem sixty_two_budget_explicit_certificates_and_coupled_gas_non_vacuous_and_tight
    (cert : CertificateAt 1_212_035_192) (L K : Nat) (hL : L ≤ 5000) :
    (SixtyTwoShape ∧ (∀ k ∈ sixtyTwoPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
    SixtyTwoClaimPayloads ∧
    (coupled subHeap L = 224985309693 ∧ coupled subMemo L = 195654540749 ∧
      (coupled subHeap 38786 < yukon ∧ yukon ≤ coupled subHeap 38787) ∧
      (coupled subMemo 40253 < yukon ∧ yukon ≤ coupled subMemo 40254) ∧
      (4 * coupled subHeap 5009 < yukon ∧ yukon ≤ 4 * coupled subHeap 5010) ∧
      (4 * coupled subMemo 6476 < yukon ∧ yukon ≤ 4 * coupled subMemo 6477)) ∧
    ((SixtyShape ∧ (∀ k ∈ sixtyPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
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
       (∀ k ∈ SelfContainedWitnessDagMemoizationAndFiftySixBudgetSynth.fiftySixPortfolio,
         InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
      ((WalkContract ∧ AccessContract ∧ RootContract ∧ WitnessLinearContract ∧
        CoupledJournalContract ∧ FrontendSafe ∧ PanLabSafe ∧ PanTargetSafe ∧ PanUserSafe ∧
        FiftyFourShape ∧ SelfContainedMptNodedbTransientAndFiftyFourBudgetSynth.FiftyFourClaimPayloads ∧
        (∀ k ∈ SelfContainedMptNodedbTransientAndFiftyFourBudgetSynth.fiftyFourPortfolio,
          InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
       ((TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster.FiftyTwoShape ∧
         SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth.FiftyTwoClaimPayloads ∧
         (∀ k ∈ SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth.fiftyTwoPortfolio,
           InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
        ((∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
           ((l.map GuestMptTraversalAndStateRootBound.Step.ext).map
             GuestMptTraversalAndStateRootBound.advance).sum ≤ 64 → l.length ≤ 64) ∧
         (∀ L' n u B blk : Nat, L' ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
           40 * blk ≤ B * B → blk + 10 * L' * n ≤ 100000000000)) ∧
        (K = K)) ∧
       (mptPlusBuild = 20036870848 ∧
        joint = 176125863653 ∧
        (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209))))) :=
  ⟨certificates_non_vacuous_and_tight cert,
   payloads_non_vacuous_and_tight,
   ⟨(block_unchanged L hL).1, (block_unchanged L hL).2,
    lmax1_heap, lmax1_memo, lmax4_heap, lmax4_memo⟩,
   sixty_budget_explicit_certificates_and_block_totals_non_vacuous_and_tight cert K⟩

/-- 9. Integrated 62-budget and coupled-gas master synthesis uniting
`WitnessResolveBlockTotalTicksAndSixtyTwoBudgetMaster`, `GuestCoupledGasFullBlockWithProbesAndTransientMaster`,
and `SelfContainedWitnessResolveBlockTotalTicksAndSixtyBudgetSynth`. -/
theorem integrated_sixty_two_budget_and_coupled_gas_full_block_master_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (L n u B_gas blk E B r : Nat) (hL : L ≤ 5000) (hu : n ≤ u) (hS : B_gas + u ≤ 2000000)
    (hblk : 40 * blk ≤ B_gas * B_gas) (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428) (hr : r ≤ 312)
    (cert : CertificateAt 1212035192) :
    (NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
      NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe ∧
      MemoContract ∧
      ExactTicks ∧
      (∀ B' r', B' ≤ 69402622 → r' ≤ 312 →
        gasEnv + mptPlusBuild + decodeHeap + 2 * r' * resolveCalls 0 B' < yukon) ∧
      (∀ E' B' r', E' + B' ≤ 33554428 → r' ≤ 664 →
        gasEnv + mptPlusBuild + decodeMemo + 2 * r' * resolveCalls E' B' < yukon) ∧
      (gasEnv + mptPlusBuild + decodeHeap = 207218238461 ∧
        yukon - (gasEnv + mptPlusBuild + decodeHeap) = 693501687013) ∧
      (gasEnv + mptPlusBuild + decodeMemo = 187064607181 ∧
        yukon - (gasEnv + mptPlusBuild + decodeMemo) = 713655318293) ∧
      SixtyTwoShape ∧ SixtyTwoClaimPayloads ∧
      (CertificateAt 1212035192 →
        ∀ K ∈ sixtyTwoPortfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
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
          blk' + T ≤ 100000000000)) ∧
    (((∀ s' ∈ L',
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
       decodeHeap - decodeMemo = 20153631280)) :=
  ⟨integrated_master_non_vacuous_and_tight,
   ⟨avg_slope,
    absorbed L n u B_gas blk hL hu hS hblk,
    excess_zero L hL,
    excess_first,
    block_unchanged L hL,
    lmax1_heap,
    lmax1_memo,
    lmax4_heap,
    lmax4_memo,
    unsalted_still_fails,
    sharp⟩,
   integrated_sixty_budget_and_resolve_block_total_master_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h E B r hB hEB hr cert⟩

/-- 10. Grand self-contained synthesis (`W5_178`): unites
(1) exact `ts+64` absorption under the shared `200M` gas budget (`general_side_regime_absorption`,
    `L ≤ 5_000` adds `0` net ticks, leaving the full block at `224_985_309_693` without memoization
    and `195_654_540_749` with DAG memoization),
(2) exact coupled-gas `L_max` thresholds (`38_786` / `40_253` at `1×` Yukon, `5_009` / `6_476` at
    `4×` Yukon),
(3) `_resolve_step` bounds (`1_110_441_952` / `536_870_848`), `r = 8` probe ticks (`17_767_071_232`
    / `8_589_933_568`), exact per-node decode ticks (`43/98`, `48/90`, `326/448`, `τ < 1`),
    DAG memoization (`33_554_428` nodes), MPT + `nodedb` + `ts+64` bridge, and unconditional
    `StackToLab → LabToTarget` no-`locValue`-6 safety,
(4) the strictly increasing **62-budget** (and 60/56/54/52/50-budget) portfolio under Yukon
    (`900_719_925_474`) and conditional finite certificates `InitE.Certificate submission (.finite K)`. -/
theorem grand_self_contained_coupled_gas_full_block_and_sixty_two_budget_synth_non_vacuous_and_tight
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
    (L n u B_gas blk ck l_ext E B r ns nc : Nat)
    (hL : L ≤ 5000) (hu : n ≤ u) (hS : B_gas + u ≤ 2000000) (hblk : 40 * blk ≤ B_gas * B_gas)
    (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428) (hr : r ≤ 312)
    (h_nodedb : 4 * (ns + nc) ≤ maxInput)
    (cert : CertificateAt 1_212_035_192) :
    ((SixtyTwoShape ∧ (∀ K ∈ sixtyTwoPortfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
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
           TransientStorageRemainingTablesAndFiftyBudgetMaster.RemainingTables)))))) :=
  ⟨⟨certificates_non_vacuous_and_tight cert,
    payloads_non_vacuous_and_tight,
    avg_slope,
    absorbed L n u B_gas blk hL hu hS hblk,
    excess_zero L hL,
    excess_first,
    block_unchanged L hL,
    lmax1_heap,
    lmax1_memo,
    lmax4_heap,
    lmax4_memo,
    unsalted_still_fails,
    sharp⟩,
   grand_self_contained_witness_resolve_block_total_ticks_and_sixty_budget_synth_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h info j bd ptr f ck l_ext E B r ns nc hB hEB hr h_nodedb cert⟩

#print axioms coupled_gas_ts64_absorption_and_unchanged_block_totals_non_vacuous_and_tight
#print axioms coupled_gas_lmax_thresholds_one_and_four_yukon_non_vacuous_and_tight
#print axioms coupled_gas_full_block_and_witness_resolve_probes_non_vacuous_and_tight
#print axioms coupled_gas_block_totals_and_mpt_nodedb_bridge_non_vacuous_and_tight
#print axioms exact_decode_ticks_dag_memoization_and_coupled_gas_non_vacuous_and_tight
#print axioms pan_to_target_no_loc_value_6_and_coupled_gas_full_block_non_vacuous_and_tight
#print axioms sixty_and_sixty_two_budget_portfolios_and_payloads_non_vacuous_and_tight
#print axioms sixty_two_budget_explicit_certificates_and_coupled_gas_non_vacuous_and_tight
#print axioms integrated_sixty_two_budget_and_coupled_gas_full_block_master_non_vacuous_and_tight
#print axioms grand_self_contained_coupled_gas_full_block_and_sixty_two_budget_synth_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedCoupledGasFullBlockAndSixtyTwoBudgetSynth
