import InitECandidate.Solver.GuestPrologueTxDecodeSecp256k1AndIndexedMptBound
import InitECandidate.Solver.SelfContainedEndToEndCoupledMptAndSixtyFourBudgetSynth
import InitECandidate.Solver.SelfContainedCoupledMptStackRemoveZeroAndSixtySixBudgetMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedPrologueSecp256k1AndSixtySixBudgetSynth`

Self-contained Wave 5 synthesis (`W5_190`, `0` imports from `InitECandidate.Proofs.Bounded*`)
uniting:
1. **`GuestPrologueTxDecodeSecp256k1AndIndexedMptBound` (`11/11` tight)**:
   - Transaction count ceiling at `12_000` intrinsic gas (`tx_count : 16_666` user transactions
     + 2 system = `16_668`, vs `9_523` under the `21_000` premise),
   - Post-EVM tick tally `postTerms = 4_859_866_650` (`secp256k1_recover = 500_040_000` at
     `30_000` ticks/tx across `16_668` txs, two tx-indexed tries = `4_333_160_000` at
     `2 · 130_000 · 16_666`, `logs_bloom = 26_666_650` at `50` ticks per `375`-gas log unit),
   - Remaining prologue budgets (`671_493_809_131` ticks at `1×` Yukon i.e. `5_003` ticks/input
     byte; `4×` Yukon without memoization fails since `813_731_675 < 4_859_866_650`;
     `25_284_633_969` ticks at `4×` Yukon with DAG memoization i.e. `188` ticks/input byte).
2. **`SelfContainedEndToEndCoupledMptAndSixtyFourBudgetSynth` (`10/10` tight)**:
   - Exact saving of `619_060_000` ticks on `mpt_set` by coupling MPT state-root writes to the
     shared `200M` gas budget (`block_total_coupled_mpt = 224_366_249_693` and
     `block_total_memo_coupled_mpt = 195_035_480_749`),
   - Coupled-MPT `L_max` thresholds (`38_817`, `40_284`, `5_040`, `6_507`), `_resolve_step` bounds,
     exact per-node decode ticks (`43/98`, `48/90`, `326/448`), DAG memoization, and 64/62/60/56/54/52/50-budget portfolios.
3. **`SelfContainedCoupledMptStackRemoveZeroAndSixtySixBudgetMaster` (`12/12` tight)**:
   - `StackRemove` zero-clock base-case simulations (`skip`, `tick`, `inst`, `stackLoad`,
     `stackStore`, `stackFree`) and bounded-clock `stackAlloc` (`clock ≤ 1`, `result = none → clock = 0`),
   - Strictly increasing **66-budget** portfolio (`SixtySixShape`, `ClaimPayloads`) all
     `< 900_719_925_474` and conditional finite certificates `InitE.Certificate submission (.finite K)`.
-/

namespace InitECandidate.Solver.SelfContainedPrologueSecp256k1AndSixtySixBudgetSynth

open Flapjack
open Flapjack.Compiler
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
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
  excess coupled
)
open InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption (S)
open InitECandidate.Solver.GuestEndToEndStartToHaltAndCoupledMptMaster (
  dirty_keys dirty_keys_tight root_coupled coupling_gain no_absorption
  coupled_totals residual_1x residual_4x per_byte per_tx mpt_const
)
open InitECandidate.Solver.GuestPrologueTxDecodeSecp256k1AndIndexedMptBound (
  tx_count secp_total tries_total bloom_total postTerms post_val
  prologue_1x fourx_heap_fails prologue_4x_memo tries_dominate
  premise_21000 secp_per_tx
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
)
open InitECandidate.Solver.SelfContainedNoLocValue6CoupledGasAndSixtyFourBudgetMaster (
  SixtyFourShape
)
open InitECandidate.Solver.SelfContainedEndToEndCoupledMptAndSixtyFourBudgetSynth (
  block_total_coupled_mpt block_total_memo_coupled_mpt
  sixtyFourPortfolio SixtyFourClaimPayloads
  coupled_mpt_saving_and_block_totals_non_vacuous_and_tight
  coupled_mpt_lmax_thresholds_one_and_four_yukon_non_vacuous_and_tight
  coupled_mpt_and_coupled_gas_ts64_absorption_non_vacuous_and_tight
  coupled_mpt_and_witness_resolve_probes_non_vacuous_and_tight
  coupled_mpt_block_totals_and_mpt_nodedb_bridge_non_vacuous_and_tight
  exact_decode_ticks_dag_memoization_and_coupled_mpt_non_vacuous_and_tight
  pan_to_target_no_loc_value_6_and_coupled_mpt_full_block_non_vacuous_and_tight
  sixty_two_and_sixty_four_budget_portfolios_and_payloads_non_vacuous_and_tight
  sixty_four_budget_explicit_certificates_and_coupled_mpt_non_vacuous_and_tight
  grand_self_contained_end_to_end_coupled_mpt_and_sixty_four_budget_synth_non_vacuous_and_tight
)
open InitECandidate.Solver.SelfContainedCoupledMptStackRemoveZeroAndSixtySixBudgetMaster (
  coupledMpt SixtySixShape
  mpt_coupling_gain_non_vacuous_and_tight
  one_heap_non_vacuous_and_tight
  one_memo_non_vacuous_and_tight
  four_heap_non_vacuous_and_tight
  four_memo_non_vacuous_and_tight
  panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
  skip_tick_inst_zero_clock_non_vacuous_and_tight
  stack_load_store_zero_clock_non_vacuous_and_tight
  stack_free_zero_clock_non_vacuous_and_tight
  stack_alloc_zero_clock_non_vacuous_and_tight
  sixty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  sixty_six_budget_certificates_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

variable {width : Nat} [NeZero width]

abbrev sixtySixPortfolio : List Nat :=
  InitECandidate.Solver.SelfContainedCoupledMptStackRemoveZeroAndSixtySixBudgetMaster.portfolio

abbrev SixtySixClaimPayloads : Prop :=
  InitECandidate.Solver.SelfContainedCoupledMptStackRemoveZeroAndSixtySixBudgetMaster.ClaimPayloads

/-- Combined post-EVM + coupled-MPT block subtotal without DAG memoization
(`224,366,249,693 + 4,859,866,650 = 229,226,116,343`). -/
def block_total_coupled_mpt_with_post : Nat := block_total_coupled_mpt + postTerms

/-- Combined post-EVM + coupled-MPT block subtotal with DAG memoization
(`195,035,480,749 + 4,859,866,650 = 199,895,347,399`). -/
def block_total_memo_coupled_mpt_with_post : Nat := block_total_memo_coupled_mpt + postTerms

/-! ## Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- 1. Transaction count ceiling at `12_000` intrinsic gas (`t_user ≤ 16_666` user transactions +
2 system = `16_668`, vs `9_523` under the `21_000` premise) and exact post-EVM tick tally
`postTerms = 4_859_866_650` (`secp256k1_recover = 500_040_000`, two tx-indexed tries =
`4_333_160_000` dominating `≥ 80%`, `logs_bloom = 26_666_650`, and input-independent per-tx secp
bound `128 * 72 + 3 * 1400 + 1500 ≤ 30_000`). -/
theorem prologue_tx_ceiling_secp256k1_indexed_tries_and_post_terms_non_vacuous_and_tight
    (t_user t_all g : Nat)
    (ht_user : 12000 * t_user ≤ 200000000)
    (ht_all : t_all ≤ 16668)
    (hg : 375 * g ≤ 200000000) :
    (t_user ≤ 16666 ∧ 200000000 / 21000 = 9523) ∧
    (12000 * 16666 ≤ 200000000 ∧ 200000000 < 12000 * 16667 ∧ 16666 + 2 = 16668) ∧
    (30000 * t_all ≤ 500040000 ∧ 30000 * 16668 = 500040000) ∧
    (2 * 130000 * t_user ≤ 4333160000 ∧ 2 * 130000 * 16666 = 4333160000) ∧
    (50 * g ≤ 26666650 ∧ 375 * 533333 ≤ 200000000 ∧ 200000000 < 375 * 533334 ∧
      50 * 533333 = 26666650) ∧
    postTerms = 4859866650 ∧
    (500040000 + 4333160000 + 26666650 = 4859866650) ∧
    10 * 4333160000 ≥ 8 * postTerms ∧
    (30000 * 9525 + 2 * 130000 * 9523 + 26666650 = 2788396650 ∧
      813731675 < 2788396650) ∧
    128 * 72 + 3 * 1400 + 1500 ≤ 30000 := by
  have htx := tx_count t_user ht_user
  exact ⟨htx,
         by decide,
         ⟨secp_total t_all ht_all, by decide⟩,
         ⟨tries_total t_user htx.1, by decide⟩,
         ⟨bloom_total g hg, by decide⟩,
         post_val,
         by decide,
         tries_dominate,
         premise_21000,
         secp_per_tx⟩

/-- 2. Remaining prologue margins after coupled-MPT state-root saving (`619_060_000` ticks) and
post-EVM terms (`postTerms = 4_859_866_650`):
- At `1×` Yukon: `671_493_809_131` ticks remain (`5_003` ticks/input byte over `134_217_712` bytes),
- At `4×` Yukon without memoization: fails (`813_731_675 < 4_859_866_650`),
- At `4×` Yukon with DAG memoization: `25_284_633_969` ticks remain (`188` ticks/input byte),
synthesized with coupled-MPT totals (`224_366_249_693` and `195_035_480_749`) and combined
post-EVM totals (`229_226_116_343` and `199_895_347_399`). -/
theorem prologue_margins_1x_and_4x_memo_with_coupled_mpt_non_vacuous_and_tight
    (k t_user t_all g : Nat)
    (hk : 21 * k ≤ 2000000)
    (ht_user : 12000 * t_user ≤ 200000000)
    (ht_all : t_all ≤ 16668)
    (hg : 375 * g ≤ 200000000) :
    (676353675781 - postTerms = 671493809131 ∧
      5003 * 134217712 ≤ 671493809131 ∧ 671493809131 < 5004 * 134217712) ∧
    813731675 < postTerms ∧
    (30144500619 - postTerms = 25284633969 ∧
      188 * 134217712 ≤ 25284633969 ∧ 25284633969 < 189 * 134217712) ∧
    (block_total_coupled_mpt_with_post = 229226116343 ∧
      block_total_memo_coupled_mpt_with_post = 199895347399 ∧
      yukon - block_total_coupled_mpt_with_post = 671493809131 ∧
      yukon / 4 - block_total_memo_coupled_mpt_with_post = 25284633969 ∧
      yukon / 4 < block_total_coupled_mpt_with_post) ∧
    (t_user ≤ 16666 ∧ 30000 * t_all ≤ 500040000 ∧
      2 * 130000 * t_user ≤ 4333160000 ∧ 50 * g ≤ 26666650 ∧
      30000 * t_all + 2 * 130000 * t_user + 50 * g ≤ postTerms) ∧
    (k ≤ 95238 ∧
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
      (19500000000 + 536870848 = 20036870848 ∧ 20037125024 - 20036870848 = 254176)) := by
  have htx := (tx_count t_user ht_user).1
  have hsecp := secp_total t_all ht_all
  have htries := tries_total t_user htx
  have hbloom := bloom_total g hg
  refine ⟨prologue_1x,
          fourx_heap_fails,
          prologue_4x_memo,
          by decide,
          ⟨htx, hsecp, htries, hbloom, ?_⟩,
          coupled_mpt_saving_and_block_totals_non_vacuous_and_tight k hk⟩
  unfold postTerms
  omega

/-- 3. Coupled-MPT `L_max` collision-run thresholds (`38_817` heap / `40_284` memo at `1×` Yukon,
and `5_040` heap / `6_507` memo at `4×` Yukon, plus `coupledMpt` propagation across all `L`)
synthesized with post-EVM `postTerms = 4_859_866_650` and prologue margins (`671_493_809_131` and
`25_284_633_969`). -/
theorem prologue_and_coupled_mpt_lmax_thresholds_non_vacuous_and_tight
    (L t_user t_all g : Nat) (hL : L ≤ 5000)
    (ht_user : 12000 * t_user ≤ 200000000)
    (ht_all : t_all ≤ 16668)
    (hg : 375 * g ≤ 200000000) :
    ((t_user ≤ 16666 ∧ 200000000 / 21000 = 9523) ∧
      30000 * t_all ≤ 500040000 ∧
      2 * 130000 * t_user ≤ 4333160000 ∧
      50 * g ≤ 26666650 ∧
      postTerms = 4859866650 ∧
      (676353675781 - postTerms = 671493809131 ∧
        5003 * 134217712 ≤ 671493809131 ∧ 671493809131 < 5004 * 134217712) ∧
      813731675 < postTerms ∧
      (30144500619 - postTerms = 25284633969 ∧
        188 * 134217712 ≤ 25284633969 ∧ 25284633969 < 189 * 134217712)) ∧
    ((∀ k : Nat, 21 * k ≤ 2000000 → k ≤ 95238 ∧ 130000 * k ≤ 12380940000) ∧
      (21 * 95238 ≤ 2000000 ∧ 2000000 < 21 * 95239) ∧
      13000000000 - 130000 * 95238 = 619060000 ∧
      SelfContainedCoupledMptStackRemoveZeroAndSixtySixBudgetMaster.block_total_coupled_mpt = 224366249693 ∧
      SelfContainedCoupledMptStackRemoveZeroAndSixtySixBudgetMaster.block_total_memo_coupled_mpt = 195035480749 ∧
      (∀ L' : Nat,
        coupled subHeap L' =
          coupledMpt SelfContainedCoupledMptStackRemoveZeroAndSixtySixBudgetMaster.block_total_coupled_mpt L' + 619060000 ∧
        coupled subMemo L' =
          coupledMpt SelfContainedCoupledMptStackRemoveZeroAndSixtySixBudgetMaster.block_total_memo_coupled_mpt L' + 619060000)) ∧
    ((coupled block_total_coupled_mpt L = 224366249693 ∧
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
        (∀ L' : Nat, 4 * coupled subMemo L' < yukon ↔ L' ≤ 6476))) := by
  have htx := tx_count t_user ht_user
  exact ⟨⟨htx,
          secp_total t_all ht_all,
          tries_total t_user htx.1,
          bloom_total g hg,
          post_val,
          prologue_1x,
          fourx_heap_fails,
          prologue_4x_memo⟩,
         mpt_coupling_gain_non_vacuous_and_tight,
         coupled_mpt_lmax_thresholds_one_and_four_yukon_non_vacuous_and_tight L hL⟩

/-- 4. Prologue margins (`671_493_809_131` at `1×`, `25_284_633_969` at `4×` memo) and post-EVM
bounds (`4_859_866_650`) synthesized with coupled-gas `ts+64` absorption (`L ≤ 5_000` adds `0` net
ticks, `excess 5001 = 20_000_000`) and `_resolve_step` probe bounds (`1_110_441_952` / `536_870_848`,
`r ≤ 312` / `r ≤ 664`). -/
theorem prologue_coupled_gas_ts64_and_witness_resolve_probes_non_vacuous_and_tight
    (t_user t_all g k L n u B_gas blk E B r : Nat)
    (ht_user : 12000 * t_user ≤ 200000000)
    (ht_all : t_all ≤ 16668)
    (hg : 375 * g ≤ 200000000)
    (hk : 21 * k ≤ 2000000) (hL : L ≤ 5000)
    (hu : n ≤ u) (hS : B_gas + u ≤ 2000000) (hblk : 40 * blk ≤ B_gas * B_gas)
    (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428) (hr : r ≤ 312) :
    ((t_user ≤ 16666 ∧ 200000000 / 21000 = 9523) ∧
      30000 * t_all ≤ 500040000 ∧
      2 * 130000 * t_user ≤ 4333160000 ∧
      50 * g ≤ 26666650 ∧
      postTerms = 4859866650 ∧
      (676353675781 - postTerms = 671493809131 ∧
        5003 * 134217712 ≤ 671493809131 ∧ 671493809131 < 5004 * 134217712) ∧
      813731675 < postTerms ∧
      (30144500619 - postTerms = 25284633969 ∧
        188 * 134217712 ≤ 25284633969 ∧ 25284633969 < 189 * 134217712)) ∧
    ((k ≤ 95238 ∧ 130000 * k ≤ 12380940000 ∧
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
          693501687013 < 2 * 2 ^ 25 * 1110441952))) := by
  have htx := tx_count t_user ht_user
  exact ⟨⟨htx,
          secp_total t_all ht_all,
          tries_total t_user htx.1,
          bloom_total g hg,
          post_val,
          prologue_1x,
          fourx_heap_fails,
          prologue_4x_memo⟩,
         coupled_mpt_and_witness_resolve_probes_non_vacuous_and_tight
           k L n u B_gas blk E B r hk hL hu hS hblk hB hEB hr⟩

/-- 5. Prologue and post-EVM bounds (`16_666` user txs, `postTerms = 4_859_866_650`, `671_493_809_131`
at `1×` and `25_284_633_969` at `4×` memo) synthesized with exact per-node decode ticks (`43/98`,
`48/90`, `326/448`), DAG memoization (`33_554_428` nodes), and the MPT + `nodedb` (`20_036_870_848`)
+ `ts+64` (`176_125_863_653`) bridge. -/
theorem prologue_exact_decode_ticks_dag_memo_and_mpt_nodedb_bridge_non_vacuous_and_tight
    (t_user t_all g k L_run L E B n r ns nc : Nat)
    (ht_user : 12000 * t_user ≤ 200000000)
    (ht_all : t_all ≤ 16668)
    (hg : 375 * g ≤ 200000000)
    (hk : 21 * k ≤ 2000000) (hL : L_run ≤ 5000)
    (h_heap : heapOf L E B ≤ heapAvail) (h_br : heapOf 0 0 B ≤ heapAvail)
    (hn : 4 * n ≤ 134217712) (h_memo : L + E + B ≤ n)
    (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428) (hr : r ≤ 312)
    (h_nodedb : 4 * (ns + nc) ≤ maxInput) :
    ((t_user ≤ 16666 ∧ 200000000 / 21000 = 9523) ∧
      30000 * t_all ≤ 500040000 ∧
      2 * 130000 * t_user ≤ 4333160000 ∧
      50 * g ≤ 26666650 ∧
      postTerms = 4859866650 ∧
      (676353675781 - postTerms = 671493809131 ∧
        5003 * 134217712 ≤ 671493809131 ∧ 671493809131 < 5004 * 134217712) ∧
      813731675 < postTerms ∧
      (30144500619 - postTerms = 25284633969 ∧
        188 * 134217712 ≤ 25284633969 ∧ 25284633969 < 189 * 134217712)) ∧
    ((k ≤ 95238 ∧ 130000 * k ≤ 12380940000 ∧
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
              58 * 15300819168 < yukon ∧ yukon < 59 * 15300819168))))) ∧
    (boundedBuild 8 ns + boundedBuild 8 nc ≤ 536870848 ∧
      mptPlusBuild = 20036870848 ∧
      joint = 176125863653 ∧
      gasEnv + mptPlusBuild + decodeHeap + 2 * r * resolveCalls 0 B < yukon) := by
  have htx := tx_count t_user ht_user
  have hbr := (coupled_mpt_block_totals_and_mpt_nodedb_bridge_non_vacuous_and_tight
    k L_run E B r ns nc hk hL hB hEB hr h_nodedb).2.2.2.2
  exact ⟨⟨htx,
          secp_total t_all ht_all,
          tries_total t_user htx.1,
          bloom_total g hg,
          post_val,
          prologue_1x,
          fourx_heap_fails,
          prologue_4x_memo⟩,
         exact_decode_ticks_dag_memoization_and_coupled_mpt_non_vacuous_and_tight
           k L_run L E B n hk hL h_heap h_br hn h_memo,
         ⟨hbr.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hbr.2.2.2.2.2.2.2.2.1,
          hbr.2.2.2.2.2.2.2.2.2.2.1,
          hbr.2.2.2.2.2.1⟩⟩

/-- 6. `StackRemove` zero-clock base-case simulation contracts (`skip`, `tick`, `inst`, `stackLoad`,
`stackStore`, `stackFree`) and bounded-clock `stackAlloc` (`clock ≤ 1`, `result = none → clock = 0`),
synthesized with `PanTargetSafe` / `PanUserSafe` and post-EVM + prologue margins (`postTerms =
4_859_866_650`, `671_493_809_131` at `1×` and `25_284_633_969` at `4×` memo). -/
theorem stack_remove_zero_clock_base_cases_and_prologue_secp256k1_non_vacuous_and_tight
    (t_user t_all g : Nat)
    (ht_user : 12000 * t_user ≤ 200000000)
    (ht_all : t_all ≤ 16668)
    (hg : 375 * g ≤ 200000000) :
    ((t_user ≤ 16666 ∧ 200000000 / 21000 = 9523) ∧
      30000 * t_all ≤ 500040000 ∧
      2 * 130000 * t_user ≤ 4333160000 ∧
      50 * g ≤ 26666650 ∧
      postTerms = 4859866650 ∧
      (676353675781 - postTerms = 671493809131 ∧
        5003 * 134217712 ≤ 671493809131 ∧ 671493809131 < 5004 * 134217712) ∧
      813731675 < postTerms ∧
      (30144500619 - postTerms = 25284633969 ∧
        188 * 134217712 ≤ 25284633969 ∧ 25284633969 < 189 * 134217712)) ∧
    (NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
      NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe) ∧
    ((∀ {width : Nat} [NeZero width] {C F : Type}
        (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
        (_hypothesis : StackSemEvaluate.evaluate (.skip, source) = (result, postSource) ∧
          result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
          StackProps.regBound (.skip : HolProg width) pointer),
        ∃ (postTarget : StackSemStateFiniteExact width C F),
          StackSemEvaluate.evaluate (comp jump bounds pointer .skip, target) = (result, postTarget) ∧
          (match result with
           | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
           | _ => stateRelHOL jump bounds pointer postSource postTarget)) ∧
      (∀ {width : Nat} [NeZero width] {C F : Type}
        (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
        (_hypothesis : StackSemEvaluate.evaluate (.tick, source) = (result, postSource) ∧
          result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
          StackProps.regBound (.tick : HolProg width) pointer),
        ∃ (postTarget : StackSemStateFiniteExact width C F),
          StackSemEvaluate.evaluate (comp jump bounds pointer .tick, target) = (result, postTarget) ∧
          (match result with
           | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
           | _ => stateRelHOL jump bounds pointer postSource postTarget)) ∧
      (∀ {width : Nat} [NeZero width] {C F : Type}
        (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
        (instruction : HolInst width)
        (_hypothesis : StackSemEvaluate.evaluate (.inst instruction, source) = (result, postSource) ∧
          result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
          StackProps.regBound (.inst instruction) pointer),
        ∃ (postTarget : StackSemStateFiniteExact width C F),
          StackSemEvaluate.evaluate (comp jump bounds pointer (.inst instruction), target) = (result, postTarget) ∧
          (match result with
           | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
           | _ => stateRelHOL jump bounds pointer postSource postTarget))) ∧
    ((∀ {width : Nat} [NeZero width] {C F : Type}
        (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F) (register count pointer : Nat)
        (bounds : BitVec width × BitVec width) (jump : Bool)
        (_hypothesis : StackSemEvaluate.evaluate (.stackLoad register count, source) = (result, postSource) ∧
          result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
          StackProps.regBound (.stackLoad register count : HolProg width) pointer),
        ∃ postTarget,
          StackSemEvaluate.evaluate (comp jump bounds pointer (.stackLoad register count), target) = (result, postTarget) ∧
          (match result with
           | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
           | _ => stateRelHOL jump bounds pointer postSource postTarget)) ∧
      (∀ {width : Nat} [NeZero width] {C F : Type}
        (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F) (register count pointer : Nat)
        (bounds : BitVec width × BitVec width) (jump : Bool)
        (_hypothesis : StackSemEvaluate.evaluate (.stackStore register count, source) = (result, postSource) ∧
          result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
          StackProps.regBound (.stackStore register count : HolProg width) pointer),
        ∃ postTarget,
          StackSemEvaluate.evaluate (comp jump bounds pointer (.stackStore register count), target) = (result, postTarget) ∧
          (match result with
           | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
           | _ => stateRelHOL jump bounds pointer postSource postTarget))) ∧
    (∀ {width : Nat} [NeZero width] {C F : Type}
      (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
      (postSource target : StackSemStateFiniteExact width C F)
      (count pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
      (_hypothesis : StackSemEvaluate.evaluate (.stackFree count, source) = (result, postSource) ∧
        result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
        StackProps.regBound (.stackFree count : HolProg width) pointer),
      ∃ (postTarget : StackSemStateFiniteExact width C F),
        StackSemEvaluate.evaluate (comp jump bounds pointer (.stackFree count), target) = (result, postTarget) ∧
        (match result with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
         | _ => stateRelHOL jump bounds pointer postSource postTarget)) ∧
    (∀ {width : Nat} [NeZero width] {C F : Type}
      (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
      (postSource target : StackSemStateFiniteExact width C F)
      (count pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
      (_hypothesis : StackSemEvaluate.evaluate (.stackAlloc count, source) = (result, postSource) ∧
        result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
        StackProps.regBound (.stackAlloc count : HolProg width) pointer),
      ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
        clock ≤ 1 ∧ (result = none → clock = 0) ∧
        StackSemEvaluate.evaluate (comp jump bounds pointer (.stackAlloc count),
          {target with clock := clock + target.clock}) = (result, postTarget) ∧
        (match result with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
         | _ => stateRelHOL jump bounds pointer postSource postTarget)) := by
  have htx := tx_count t_user ht_user
  exact ⟨⟨htx,
          secp_total t_all ht_all,
          tries_total t_user htx.1,
          bloom_total g hg,
          post_val,
          prologue_1x,
          fourx_heap_fails,
          prologue_4x_memo⟩,
         panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight,
         skip_tick_inst_zero_clock_non_vacuous_and_tight,
         stack_load_store_zero_clock_non_vacuous_and_tight,
         stack_free_zero_clock_non_vacuous_and_tight,
         stack_alloc_zero_clock_non_vacuous_and_tight⟩

/-- 7. Unconditional `StackToLab → LabToTarget` no-`locValue`-6 safety (`PanTargetSafe`, `PanUserSafe`,
`JumpOk`) synthesized with `StackRemove` zero-clock base-case contracts, coupled-MPT saving
(`619_060_000` ticks), and prologue + post-EVM bounds (`4_859_866_650` ticks, `671_493_809_131`
at `1×` and `25_284_633_969` at `4×` memo). -/
theorem pan_to_target_no_loc_value_6_stack_remove_and_prologue_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (t_user t_all g k L E B r : Nat)
    (ht_user : 12000 * t_user ≤ 200000000)
    (ht_all : t_all ≤ 16668)
    (hg : 375 * g ≤ 200000000)
    (hk : 21 * k ≤ 2000000) (hL : L ≤ 5000)
    (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428) (hr : r ≤ 312) :
    ((t_user ≤ 16666 ∧ 200000000 / 21000 = 9523) ∧
      30000 * t_all ≤ 500040000 ∧
      2 * 130000 * t_user ≤ 4333160000 ∧
      50 * g ≤ 26666650 ∧
      postTerms = 4859866650 ∧
      (676353675781 - postTerms = 671493809131 ∧
        5003 * 134217712 ≤ 671493809131 ∧ 671493809131 < 5004 * 134217712) ∧
      813731675 < postTerms ∧
      (30144500619 - postTerms = 25284633969 ∧
        188 * 134217712 ≤ 25284633969 ∧ 25284633969 < 189 * 134217712)) ∧
    ((k ≤ 95238 ∧ 130000 * k ≤ 12380940000 ∧
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
            JC (.locValue 0 storeConstsStubLocation 0 : HolProg width) = false)))) ∧
    (∀ {width : Nat} [NeZero width] {C F : Type}
      (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
      (postSource target : StackSemStateFiniteExact width C F)
      (count pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
      (_hypothesis : StackSemEvaluate.evaluate (.stackAlloc count, source) = (result, postSource) ∧
        result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
        StackProps.regBound (.stackAlloc count : HolProg width) pointer),
      ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
        clock ≤ 1 ∧ (result = none → clock = 0) ∧
        StackSemEvaluate.evaluate (comp jump bounds pointer (.stackAlloc count),
          {target with clock := clock + target.clock}) = (result, postTarget) ∧
        (match result with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
         | _ => stateRelHOL jump bounds pointer postSource postTarget)) := by
  have htx := tx_count t_user ht_user
  exact ⟨⟨htx,
          secp_total t_all ht_all,
          tries_total t_user htx.1,
          bloom_total g hg,
          post_val,
          prologue_1x,
          fourx_heap_fails,
          prologue_4x_memo⟩,
         pan_to_target_no_loc_value_6_and_coupled_mpt_full_block_non_vacuous_and_tight
           arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h k L E B r hk hL hB hEB hr,
         stack_alloc_zero_clock_non_vacuous_and_tight⟩

/-- 8. Strictly increasing **66-budget** (`SixtySixShape`), 64-budget (`SixtyFourShape`), 62-budget,
60-budget, 56-budget, 54-budget, 52-budget, and 50-budget portfolios all `< 900_719_925_474`,
united with prologue (`671_493_809_131` / `5_003` per byte at `1×`; `25_284_633_969` / `188` per
byte at `4×` memo) and post-EVM (`4_859_866_650`) bounds. -/
theorem sixty_six_and_sixty_four_budget_portfolios_and_prologue_non_vacuous_and_tight
    (t_user t_all g k L : Nat)
    (ht_user : 12000 * t_user ≤ 200000000)
    (ht_all : t_all ≤ 16668)
    (hg : 375 * g ≤ 200000000)
    (hk : 21 * k ≤ 2000000) (hL : L ≤ 5000)
    (l_chunks : List Nat) (ck : Nat) :
    SixtySixShape ∧
    ((t_user ≤ 16666 ∧ 200000000 / 21000 = 9523) ∧
      30000 * t_all ≤ 500040000 ∧
      2 * 130000 * t_user ≤ 4333160000 ∧
      50 * g ≤ 26666650 ∧
      postTerms = 4859866650 ∧
      (676353675781 - postTerms = 671493809131 ∧
        5003 * 134217712 ≤ 671493809131 ∧ 671493809131 < 5004 * 134217712) ∧
      813731675 < postTerms ∧
      (30144500619 - postTerms = 25284633969 ∧
        188 * 134217712 ≤ 25284633969 ∧ 25284633969 < 189 * 134217712)) ∧
    ((SixtyFourShape ∧ SixtyFourClaimPayloads) ∧
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
          (HeapAllocationContract ∧ HeapNodesContract ∧ HeapRateContract ∧ MemoContract ∧ BridgeContract))))) := by
  have htx := tx_count t_user ht_user
  exact ⟨sixty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
         ⟨htx,
          secp_total t_all ht_all,
          tries_total t_user htx.1,
          bloom_total g hg,
          post_val,
          prologue_1x,
          fourx_heap_fails,
          prologue_4x_memo⟩,
         sixty_two_and_sixty_four_budget_portfolios_and_payloads_non_vacuous_and_tight k L hk hL l_chunks ck⟩

/-- 9. Conditional finite certificates `InitE.Certificate (baselineWithFiniteK K) (.finite K)` across
the **66-budget** (`sixtySixPortfolio`), 64-budget (`sixtyFourPortfolio`), 62-budget
(`sixtyTwoPortfolio`), 60-budget, and 56/54/52-budget portfolios under `cert : CertificateAt 1_212_035_192`,
united with prologue and post-EVM bounds (`4_859_866_650` ticks, `671_493_809_131` at `1×` and
`25_284_633_969` at `4×` memo). -/
theorem sixty_six_budget_explicit_certificates_and_prologue_secp256k1_non_vacuous_and_tight
    (cert : CertificateAt 1_212_035_192)
    (t_user t_all g k L K : Nat)
    (ht_user : 12000 * t_user ≤ 200000000)
    (ht_all : t_all ≤ 16668)
    (hg : 375 * g ≤ 200000000)
    (hk : 21 * k ≤ 2000000) (hL : L ≤ 5000) :
    (NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe ∧
      SixtySixShape ∧ SixtySixClaimPayloads ∧
      (∀ k' ∈ sixtySixPortfolio, InitE.Certificate (baselineWithFiniteK k') (.finite k'))) ∧
    ((t_user ≤ 16666 ∧ 200000000 / 21000 = 9523) ∧
      30000 * t_all ≤ 500040000 ∧
      2 * 130000 * t_user ≤ 4333160000 ∧
      50 * g ≤ 26666650 ∧
      postTerms = 4859866650 ∧
      (676353675781 - postTerms = 671493809131 ∧
        5003 * 134217712 ≤ 671493809131 ∧ 671493809131 < 5004 * 134217712) ∧
      813731675 < postTerms ∧
      (30144500619 - postTerms = 25284633969 ∧
        188 * 134217712 ≤ 25284633969 ∧ 25284633969 < 189 * 134217712)) ∧
    ((NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe ∧
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
            (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209))))))) := by
  have htx := tx_count t_user ht_user
  exact ⟨sixty_six_budget_certificates_non_vacuous_and_tight cert,
         ⟨htx,
          secp_total t_all ht_all,
          tries_total t_user htx.1,
          bloom_total g hg,
          post_val,
          prologue_1x,
          fourx_heap_fails,
          prologue_4x_memo⟩,
         sixty_four_budget_explicit_certificates_and_coupled_mpt_non_vacuous_and_tight cert k L K hk hL⟩

/-- 10. Grand self-contained synthesis (`W5_190`): unites
(1) Transaction ceiling at `12_000` intrinsic gas (`16_666` user txs + 2 system = `16_668`) and
    post-EVM tick tally `postTerms = 4_859_866_650` (`secp256k1_recover = 500_040_000`, two indexed
    tries = `4_333_160_000`, `logs_bloom = 26_666_650`),
(2) Remaining prologue margins (`671_493_809_131` ticks at `1×` Yukon i.e. `5_003` ticks/input byte;
    `25_284_633_969` ticks at `4×` Yukon with DAG memoization i.e. `188` ticks/input byte; failure of
    `4×` without memoization `813_731_675 < 4_859_866_650`),
(3) Coupled-MPT `619_060_000`-tick saving (`224_366_249_693` and `195_035_480_749`), `L_max`
    thresholds (`38_817`, `40_284`, `5_040`, `6_507`), `StackRemove` zero-clock base-case contracts
    and bounded-clock `stackAlloc`, `_resolve_step` bounds, exact decode ticks, DAG memoization,
    and unconditional `StackToLab → LabToTarget` no-`locValue`-6 safety,
(4) The strictly increasing **66-budget** (and 64/62/60/56/54/52/50-budget) portfolio all
    `< 900_719_925_474` and conditional finite certificates `InitE.Certificate submission (.finite K)`. -/
theorem grand_self_contained_prologue_secp256k1_and_sixty_six_budget_synth_non_vacuous_and_tight
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
    (t_user t_all g k L n u B_gas blk ck l_ext E B r ns nc : Nat)
    (ht_user : 12000 * t_user ≤ 200000000)
    (ht_all : t_all ≤ 16668)
    (hg : 375 * g ≤ 200000000)
    (hk : 21 * k ≤ 2000000) (hL : L ≤ 5000) (hu : n ≤ u) (hS : B_gas + u ≤ 2000000)
    (hblk : 40 * blk ≤ B_gas * B_gas) (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428) (hr : r ≤ 312)
    (h_nodedb : 4 * (ns + nc) ≤ maxInput)
    (cert : CertificateAt 1_212_035_192) :
    ((NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe ∧
       SixtySixShape ∧ SixtySixClaimPayloads ∧
       (∀ K ∈ sixtySixPortfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
     ((t_user ≤ 16666 ∧ 200000000 / 21000 = 9523) ∧
       30000 * t_all ≤ 500040000 ∧
       2 * 130000 * t_user ≤ 4333160000 ∧
       50 * g ≤ 26666650 ∧
       postTerms = 4859866650 ∧
       (676353675781 - postTerms = 671493809131 ∧
         5003 * 134217712 ≤ 671493809131 ∧ 671493809131 < 5004 * 134217712) ∧
       813731675 < postTerms ∧
       (30144500619 - postTerms = 25284633969 ∧
         188 * 134217712 ≤ 25284633969 ∧ 25284633969 < 189 * 134217712) ∧
       10 * 4333160000 ≥ 8 * postTerms ∧
       (30000 * 9525 + 2 * 130000 * 9523 + 26666650 = 2788396650 ∧
         813731675 < 2788396650) ∧
       128 * 72 + 3 * 1400 + 1500 ≤ 30000 ∧
       (block_total_coupled_mpt_with_post = 229226116343 ∧
         block_total_memo_coupled_mpt_with_post = 199895347399 ∧
         yukon - block_total_coupled_mpt_with_post = 671493809131 ∧
         yukon / 4 - block_total_memo_coupled_mpt_with_post = 25284633969))) ∧
    ((∀ {width : Nat} [NeZero width] {C F : Type}
        (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (count pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
        (_hypothesis : StackSemEvaluate.evaluate (.stackFree count, source) = (result, postSource) ∧
          result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
          StackProps.regBound (.stackFree count : HolProg width) pointer),
        ∃ (postTarget : StackSemStateFiniteExact width C F),
          StackSemEvaluate.evaluate (comp jump bounds pointer (.stackFree count), target) = (result, postTarget) ∧
          (match result with
           | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
           | _ => stateRelHOL jump bounds pointer postSource postTarget)) ∧
      (∀ {width : Nat} [NeZero width] {C F : Type}
        (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (count pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
        (_hypothesis : StackSemEvaluate.evaluate (.stackAlloc count, source) = (result, postSource) ∧
          result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
          StackProps.regBound (.stackAlloc count : HolProg width) pointer),
        ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
          clock ≤ 1 ∧ (result = none → clock = 0) ∧
          StackSemEvaluate.evaluate (comp jump bounds pointer (.stackAlloc count),
            {target with clock := clock + target.clock}) = (result, postTarget) ∧
          (match result with
           | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
           | _ => stateRelHOL jump bounds pointer postSource postTarget))) ∧
    (((NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe ∧
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
             TransientStorageRemainingTablesAndFiftyBudgetMaster.RemainingTables)))))))) := by
  have htx := tx_count t_user ht_user
  exact ⟨⟨sixty_six_budget_certificates_non_vacuous_and_tight cert,
          htx,
          secp_total t_all ht_all,
          tries_total t_user htx.1,
          bloom_total g hg,
          post_val,
          prologue_1x,
          fourx_heap_fails,
          prologue_4x_memo,
          tries_dominate,
          premise_21000,
          secp_per_tx,
          by decide⟩,
         ⟨stack_free_zero_clock_non_vacuous_and_tight,
          stack_alloc_zero_clock_non_vacuous_and_tight⟩,
         grand_self_contained_end_to_end_coupled_mpt_and_sixty_four_budget_synth_non_vacuous_and_tight
           arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h info j bd ptr f
           k L n u B_gas blk ck l_ext E B r ns nc hk hL hu hS hblk hB hEB hr h_nodedb cert⟩

#print axioms prologue_tx_ceiling_secp256k1_indexed_tries_and_post_terms_non_vacuous_and_tight
#print axioms prologue_margins_1x_and_4x_memo_with_coupled_mpt_non_vacuous_and_tight
#print axioms prologue_and_coupled_mpt_lmax_thresholds_non_vacuous_and_tight
#print axioms prologue_coupled_gas_ts64_and_witness_resolve_probes_non_vacuous_and_tight
#print axioms prologue_exact_decode_ticks_dag_memo_and_mpt_nodedb_bridge_non_vacuous_and_tight
#print axioms stack_remove_zero_clock_base_cases_and_prologue_secp256k1_non_vacuous_and_tight
#print axioms pan_to_target_no_loc_value_6_stack_remove_and_prologue_non_vacuous_and_tight
#print axioms sixty_six_and_sixty_four_budget_portfolios_and_prologue_non_vacuous_and_tight
#print axioms sixty_six_budget_explicit_certificates_and_prologue_secp256k1_non_vacuous_and_tight
#print axioms grand_self_contained_prologue_secp256k1_and_sixty_six_budget_synth_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedPrologueSecp256k1AndSixtySixBudgetSynth
