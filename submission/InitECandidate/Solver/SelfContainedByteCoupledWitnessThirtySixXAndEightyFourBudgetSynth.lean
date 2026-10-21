import InitECandidate.Solver.GuestByteCoupledWitnessResolveAndThirtyFiveXMaster
import InitECandidate.Solver.SelfContainedPrologueSecp256k1AndSixtySixBudgetSynth
import InitECandidate.Solver.SaltedNodedbTwentySevenXAndEightyFourBudgetMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedByteCoupledWitnessThirtySixXAndEightyFourBudgetSynth`

Self-contained Wave 5 synthesis (`W5_230`, `0` imports from `InitECandidate.Proofs.Bounded*`)
uniting:
1. **`GuestByteCoupledWitnessResolveAndThirtyFiveXMaster`**:
   - Byte-coupled `_resolve_step` hash-reference bound (`33 * h ≤ 134_217_712 ⇒ h ≤ 4_067_203`
     disjoint 33-byte `0xa0 ‖ h` references under DAG memoization, attained at `4_067_203`,
     `132×` smaller than `16 * 33_554_428`),
   - Probe tallies `2 * 8 * hashRefs = 65_075_248`, `probes 200_000_000 = 66_675_248`,
     `probes 380_000_000 = 68_115_248`, saving `gain = 8_523_258_320` ticks at `200M` gas,
   - Byte-coupled block totals `main200 = 24_381_873_932` (`36×` Yukon passes with margin
     `22_972_463_922`, `37×` fails) and `main380 = 32_488_958_762` (`27×` Yukon passes with margin
     `23_518_038_900`, `28×` fails), `decodeMemo` dominance (`> 44%` of `main200`), and
     `tree_no_coupling`.
2. **`SelfContainedPrologueSecp256k1AndSixtySixBudgetSynth` (`10/10` tight)**:
   - Transaction count ceiling at `12_000` intrinsic gas (`16_666` user txs + 2 system = `16_668`),
     post-EVM tally `postTerms = 4_859_866_650` (`secp256k1_recover = 500_040_000`, two indexed
     tries = `4_333_160_000`, `logs_bloom = 26_666_650`),
   - Remaining prologue margins (`671_493_809_131` ticks at `1×` Yukon i.e. `5_003` ticks/byte;
     `25_284_633_969` ticks at `4×` Yukon with DAG memoization i.e. `188` ticks/byte),
   - Coupled-MPT `619_060_000`-tick saving, `L_max` thresholds (`38_817`, `40_284`, `5_040`,
     `6_507`), `StackRemove` zero-clock base-case contracts, and 66/64/62/60/56/54/52/50-budget
     portfolios.
3. **`SaltedNodedbTwentySevenXAndEightyFourBudgetMaster` (`12/12` tight)**:
   - Salted `nodedb` + witness + MPT audit (`38_946_487_944` dissect, `663 < 1000` visit cost,
     `witnessMptSalted = 26_801_608_212` / `30_612_453_042`, `postEvmSalted = 681_400_462`,
     salted `main200 = 32_905_132_252` at `27×` and `main380 = 41_010_777_082` at `21×`, `r = 1`
     lever `25_388_940_380` at `35×`),
   - `StackRemove` whole-program `initStubs` / `initCode` / `compileProg` zero-extra-body-clock
     theorems,
   - Strictly increasing **84-budget** portfolio (`EightyFourShape`) all `< 900_719_925_474` and
     conditional finite certificates `InitE.Certificate (baselineWithFiniteK K) (.finite K)`.
-/

namespace InitECandidate.Solver.SelfContainedByteCoupledWitnessThirtySixXAndEightyFourBudgetSynth

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
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock (CodeNoSt ClockOk)
open _root_.InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
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
  subHeap subMemo
)
open InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster (
  excess coupled
)
open InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption (S)
open InitECandidate.Solver.GuestPrologueTxDecodeSecp256k1AndIndexedMptBound (
  tx_count secp_total tries_total bloom_total postTerms post_val
  prologue_1x fourx_heap_fails prologue_4x_memo tries_dominate
  premise_21000 secp_per_tx
)
open InitECandidate.Solver.GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit (
  probesR8 buildNodedb walks rootTicks witnessMptSalted postEvmSalted
)
open InitECandidate.Solver.GuestByteCoupledWitnessResolveAndThirtyFiveXMaster (
  inputBytes hashRefs probes main200 main380
  refs_bound refs_tight ratio probe_vals gain
  main200_slope main380_slope margins decode_dominates tree_no_coupling
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
)
open InitECandidate.Solver.SelfContainedCoupledMptStackRemoveZeroAndSixtySixBudgetMaster (
  coupledMpt SixtySixShape
)
open InitECandidate.Solver.SelfContainedPrologueSecp256k1AndSixtySixBudgetSynth (
  sixtySixPortfolio SixtySixClaimPayloads
  block_total_coupled_mpt_with_post block_total_memo_coupled_mpt_with_post
  prologue_tx_ceiling_secp256k1_indexed_tries_and_post_terms_non_vacuous_and_tight
  prologue_margins_1x_and_4x_memo_with_coupled_mpt_non_vacuous_and_tight
  prologue_and_coupled_mpt_lmax_thresholds_non_vacuous_and_tight
  prologue_coupled_gas_ts64_and_witness_resolve_probes_non_vacuous_and_tight
  prologue_exact_decode_ticks_dag_memo_and_mpt_nodedb_bridge_non_vacuous_and_tight
  stack_remove_zero_clock_base_cases_and_prologue_secp256k1_non_vacuous_and_tight
  pan_to_target_no_loc_value_6_stack_remove_and_prologue_non_vacuous_and_tight
  sixty_six_and_sixty_four_budget_portfolios_and_prologue_non_vacuous_and_tight
  sixty_six_budget_explicit_certificates_and_prologue_secp256k1_non_vacuous_and_tight
  grand_self_contained_prologue_secp256k1_and_sixty_six_budget_synth_non_vacuous_and_tight
)
open InitECandidate.Solver.SaltedNodedbTwentySevenXAndEightyFourBudgetMaster (
  EightyFourShape
  dissect_and_probes_salted_non_vacuous_and_tight
  visit_cost_and_rows_200_non_vacuous_and_tight
  wm_vals_and_post_val_non_vacuous_and_tight
  main200_slope_non_vacuous_and_tight
  main380_slope_and_no_thirty_non_vacuous_and_tight
  dominant_and_r1_lever_non_vacuous_and_tight
  noSt_initStubs_non_vacuous_and_tight
  initCode_clock_preserved_non_vacuous_and_tight
  stackRemoveCompile_sections_noSt_non_vacuous_and_tight
  pancake_stackRemove_compileProg_zeroExtraBodyClock_non_vacuous_and_tight
  eighty_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  eighty_four_budget_certificates_non_vacuous_and_tight
)

variable {width : Nat} [NeZero width]

abbrev eightyFourPortfolio : List Nat :=
  InitECandidate.Solver.SaltedNodedbTwentySevenXAndEightyFourBudgetMaster.portfolio

/-! ## Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- 1. Byte-coupled `_resolve_step` hash-reference bound (`33 * h ≤ inputBytes ⇒ h ≤ 4_067_203`,
attained at `4_067_203` with `33 * 4_067_203 ≤ 134_217_712 < 33 * 4_067_204`), `132×` call-count
reduction (`132 * hashRefs ≤ 16 * 33_554_428 < 133 * hashRefs`), probe tallies (`2 * 8 * hashRefs =
65_075_248`, `probes 200_000_000 = 66_675_248`, `probes 380_000_000 = 68_115_248`), saving
`gain = 8_523_258_320` ticks, `main200 = 24_381_873_932` (`36×` passes with margin `22_972_463_922`,
`37×` fails), `main380 = 32_488_958_762` (`27×` passes with margin `23_518_038_900`, `28×` fails),
`decodeMemo` dominance (`100 * 10_938_743_528 > 44 * main200`), and `tree_no_coupling`. -/
theorem byte_coupled_witness_resolve_thirty_six_x_and_twenty_seven_x_non_vacuous_and_tight
    (h_refs : Nat) (hb : 33 * h_refs ≤ inputBytes) :
    h_refs ≤ 4067203 ∧
    (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) ∧
    (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs) ∧
    (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
      probes 380000000 = 68115248) ∧
    8589933568 - probes 200000000 = 8523258320 ∧
    (main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200) ∧
    (main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380) ∧
    (yukon - 36 * main200 = 22972463922 ∧ yukon - 27 * main380 = 23518038900) ∧
    100 * 10938743528 > 44 * main200 ∧
    2 * 8 * hashRefs < 2 * 8 * 1110441952 :=
  ⟨refs_bound h_refs hb,
   refs_tight,
   ratio,
   probe_vals,
   gain,
   main200_slope,
   main380_slope,
   margins,
   decode_dominates,
   tree_no_coupling⟩

/-- 2. Synthesis of byte-coupled witness resolve (`main200 = 24_381_873_932` at `36×`,
`main380 = 32_488_958_762` at `27×`, `gain = 8_523_258_320`) with the salted `nodedb` + witness +
MPT audit (`38_946_487_944` dissect, `663 < 1000` visit cost, `witnessMptSalted = 26_801_608_212` /
`30_612_453_042`, `postEvmSalted = 681_400_462`, uncoupled salted `32_905_132_252` at `27×` and
`41_010_777_082` at `21×`, `r = 1` lever `25_388_940_380` at `35×`). -/
theorem byte_coupled_witness_and_salted_nodedb_sub_twenty_billion_non_vacuous_and_tight
    (h_refs : Nat) (hb : 33 * h_refs ≤ inputBytes) :
    (h_refs ≤ 4067203 ∧
      (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) ∧
      (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs) ∧
      (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
        probes 380000000 = 68115248) ∧
      8589933568 - probes 200000000 = 8523258320 ∧
      (main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200) ∧
      (main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380) ∧
      (yukon - 36 * main200 = 22972463922 ∧ yukon - 27 * main380 = 23518038900) ∧
      100 * 10938743528 > 44 * main200 ∧
      2 * 8 * hashRefs < 2 * 8 * 1110441952) ∧
    (((decodeMemo + probesR8 + (20036870848 - 619060000) = 38946487944 ∧
        probesR8 = 8589933568) ∧
       probesR8 = 2 * 8 * (16 * 33554428)) ∧
      ((30 + 633 = 663 ∧ 663 < 1000) ∧
        (buildNodedb = 3038649506 ∧ walks 200000000 = 130000000 ∧
          rootTicks 200000000 = 4104281610)) ∧
      ((witnessMptSalted 200000000 = 26801608212 ∧
        witnessMptSalted 380000000 = 30612453042) ∧
       postEvmSalted = 681400462) ∧
      (GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200 = 32905132252 ∧
        27 * GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200 < yukon ∧
        yukon < 28 * GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200) ∧
      ((GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main380 = 41010777082 ∧
        21 * GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main380 < yukon ∧
        yukon < 22 * GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main380) ∧
       (yukon / 30 = 30023997515 ∧
        yukon < 30 * GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200)) ∧
      ((100 * (decodeMemo + probesR8) >
        59 * GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200) ∧
       (GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200 - probesR8 + 2 * 1 * 536870848 = 25388940380 ∧
        35 * 25388940380 < yukon ∧ yukon < 36 * 25388940380))) :=
  ⟨byte_coupled_witness_resolve_thirty_six_x_and_twenty_seven_x_non_vacuous_and_tight h_refs hb,
   dissect_and_probes_salted_non_vacuous_and_tight,
   visit_cost_and_rows_200_non_vacuous_and_tight,
   wm_vals_and_post_val_non_vacuous_and_tight,
   main200_slope_non_vacuous_and_tight,
   main380_slope_and_no_thirty_non_vacuous_and_tight,
   dominant_and_r1_lever_non_vacuous_and_tight⟩

/-- 3. Byte-coupled witness resolve (`refs_bound`, `refs_tight`, `ratio`, `probe_vals`, `gain`,
`main200_slope` at `36×`, `main380_slope` at `27×`, `margins`, `decode_dominates`) synthesized with
the transaction ceiling at `12_000` intrinsic gas (`16_666` user txs + 2 system = `16_668`) and
post-EVM tally `postTerms = 4_859_866_650` (`secp256k1_recover = 500_040_000`, two indexed tries =
`4_333_160_000`, `logs_bloom = 26_666_650`). -/
theorem byte_coupled_witness_and_prologue_tx_secp256k1_post_terms_non_vacuous_and_tight
    (h_refs t_user t_all g : Nat)
    (hb : 33 * h_refs ≤ inputBytes)
    (ht_user : 12000 * t_user ≤ 200000000)
    (ht_all : t_all ≤ 16668)
    (hg : 375 * g ≤ 200000000) :
    (h_refs ≤ 4067203 ∧
      (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) ∧
      (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs) ∧
      (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
        probes 380000000 = 68115248) ∧
      8589933568 - probes 200000000 = 8523258320 ∧
      (main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200) ∧
      (main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380) ∧
      (yukon - 36 * main200 = 22972463922 ∧ yukon - 27 * main380 = 23518038900) ∧
      100 * 10938743528 > 44 * main200 ∧
      2 * 8 * hashRefs < 2 * 8 * 1110441952) ∧
    ((t_user ≤ 16666 ∧ 200000000 / 21000 = 9523) ∧
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
      128 * 72 + 3 * 1400 + 1500 ≤ 30000) :=
  ⟨byte_coupled_witness_resolve_thirty_six_x_and_twenty_seven_x_non_vacuous_and_tight h_refs hb,
   prologue_tx_ceiling_secp256k1_indexed_tries_and_post_terms_non_vacuous_and_tight
     t_user t_all g ht_user ht_all hg⟩

/-- 4. Byte-coupled witness resolve (`main200 = 24_381_873_932` at `36×`, `main380 = 32_488_958_762`
at `27×`, `gain = 8_523_258_320`) synthesized with prologue margins (`671_493_809_131` ticks at
`1×` Yukon i.e. `5_003` ticks/byte; `25_284_633_969` ticks at `4×` Yukon with DAG memoization i.e.
`188` ticks/byte) and coupled-MPT state-root saving (`619_060_000` ticks, `L_max` thresholds
`38_817`, `40_284`, `5_040`, `6_507`). -/
theorem byte_coupled_witness_prologue_margins_and_coupled_mpt_lmax_non_vacuous_and_tight
    (h_refs k L t_user t_all g : Nat)
    (hb : 33 * h_refs ≤ inputBytes)
    (hk : 21 * k ≤ 2000000)
    (hL : L ≤ 5000)
    (ht_user : 12000 * t_user ≤ 200000000)
    (ht_all : t_all ≤ 16668)
    (hg : 375 * g ≤ 200000000) :
    (h_refs ≤ 4067203 ∧
      (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) ∧
      (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs) ∧
      (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
        probes 380000000 = 68115248) ∧
      8589933568 - probes 200000000 = 8523258320 ∧
      (main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200) ∧
      (main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380) ∧
      (yukon - 36 * main200 = 22972463922 ∧ yukon - 27 * main380 = 23518038900) ∧
      100 * 10938743528 > 44 * main200 ∧
      2 * 8 * hashRefs < 2 * 8 * 1110441952) ∧
    ((676353675781 - postTerms = 671493809131 ∧
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
        (19500000000 + 536870848 = 20036870848 ∧ 20037125024 - 20036870848 = 254176))) ∧
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
        yukon ≤ 4 * coupled block_total_memo_coupled_mpt 6508)) := by
  have hlmax := (prologue_and_coupled_mpt_lmax_thresholds_non_vacuous_and_tight
    L t_user t_all g hL ht_user ht_all hg).2.2
  exact ⟨byte_coupled_witness_resolve_thirty_six_x_and_twenty_seven_x_non_vacuous_and_tight h_refs hb,
         prologue_margins_1x_and_4x_memo_with_coupled_mpt_non_vacuous_and_tight
           k t_user t_all g hk ht_user ht_all hg,
         ⟨hlmax.1, hlmax.2.1, hlmax.2.2.1, hlmax.2.2.2.1, hlmax.2.2.2.2.1⟩⟩

/-- 5. Byte-coupled witness resolve (`main200 = 24_381_873_932` at `36×`, `main380 = 32_488_958_762`
at `27×`) synthesized with exact per-node decode ticks (`43/98`, `48/90`, `326/448`), DAG
memoization (`33_554_428` nodes, `10_938_743_528` decode ticks), coupled-gas `ts+64` absorption,
and `_resolve_step` bounds. -/
theorem byte_coupled_witness_exact_decode_ticks_and_mpt_nodedb_bridge_non_vacuous_and_tight
    (h_refs t_user t_all g k L_run L E B n r ns nc : Nat)
    (hb : 33 * h_refs ≤ inputBytes)
    (ht_user : 12000 * t_user ≤ 200000000)
    (ht_all : t_all ≤ 16668)
    (hg : 375 * g ≤ 200000000)
    (hk : 21 * k ≤ 2000000) (hL : L_run ≤ 5000)
    (h_heap : heapOf L E B ≤ heapAvail) (h_br : heapOf 0 0 B ≤ heapAvail)
    (hn : 4 * n ≤ 134217712) (h_memo : L + E + B ≤ n)
    (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428) (hr : r ≤ 312)
    (h_nodedb : 4 * (ns + nc) ≤ maxInput) :
    (h_refs ≤ 4067203 ∧
      (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) ∧
      (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs) ∧
      (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
        probes 380000000 = 68115248) ∧
      8589933568 - probes 200000000 = 8523258320 ∧
      (main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200) ∧
      (main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380) ∧
      (yukon - 36 * main200 = 22972463922 ∧ yukon - 27 * main380 = 23518038900) ∧
      100 * 10938743528 > 44 * main200 ∧
      2 * 8 * hashRefs < 2 * 8 * 1110441952) ∧
    (((t_user ≤ 16666 ∧ 200000000 / 21000 = 9523) ∧
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
      gasEnv + mptPlusBuild + decodeHeap + 2 * r * resolveCalls 0 B < yukon)) :=
  ⟨byte_coupled_witness_resolve_thirty_six_x_and_twenty_seven_x_non_vacuous_and_tight h_refs hb,
   prologue_exact_decode_ticks_dag_memo_and_mpt_nodedb_bridge_non_vacuous_and_tight
     t_user t_all g k L_run L E B n r ns nc ht_user ht_all hg hk hL h_heap h_br hn h_memo hB hEB hr h_nodedb⟩

/-- 6. Whole-program `StackRemove` zero-extra-body-clock compilation (`initStubs` `StackNoSt`,
`initCode` clock preservation, `StackRemove.compileHOL` `StackNoSt`, `progComp` `ClockOk`) and
base-case zero-clock simulations (`skip`, `tick`, `inst`, `stackLoad`, `stackStore`, `stackFree`,
`stackAlloc`) synthesized with byte-coupled witness resolve (`36×` / `27×`) and prologue margins. -/
theorem stack_remove_compile_prog_zero_clock_and_byte_coupled_witness_non_vacuous_and_tight
    {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (jump : Bool) (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maximumHeap pointer start : Nat)
    (h_refs t_user t_all g : Nat)
    (hb : 33 * h_refs ≤ inputBytes)
    (ht_user : 12000 * t_user ≤ 200000000)
    (ht_all : t_all ≤ 16668)
    (hg : 375 * g ≤ 200000000) :
    (h_refs ≤ 4067203 ∧
      (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) ∧
      (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs) ∧
      (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
        probes 380000000 = 68115248) ∧
      8589933568 - probes 200000000 = 8523258320 ∧
      (main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200) ∧
      (main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380) ∧
      (yukon - 36 * main200 = 22972463922 ∧ yukon - 27 * main380 = 23518038900) ∧
      100 * 10938743528 > 44 * main200 ∧
      2 * 8 * hashRefs < 2 * 8 * 1110441952) ∧
    ((∀ e ∈ initStubs (width := width) generateGc maximumHeap pointer start, StackNoSt e.2 = true) ∧
      (∀ (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
        StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, s) = (r, t) →
        t.clock = s.clock) ∧
      (∀ e ∈ StackRemove.compileHOL jump bounds generateGc maximumHeap pointer start
          (StackAlloc.compile dc (StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
            (panToWordCompileProgHOL arch prog)).2).2.2.2)),
        e.1 = storeConstsStubLocation ∨ StackNoSt e.2 = true) ∧
      (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2,
        y.1 = storeConstsStubLocation ∨
        ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
          (postSource target : StackSemStateFiniteExact width C F)
          (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
          CodeNoSt source →
          StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
              (result, postSource) ∧ result ≠ some .error ∧
            StackRemove.stateRelHOL j bd ptr source target ∧
            StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr →
          ∃ clock postTarget, ClockOk clock result ∧
            StackSemEvaluate.evaluate (StackRemove.comp j bd ptr
              (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
              {target with clock := clock + target.clock}) = (result, postTarget))) ∧
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
      NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe) := by
  have hst := stack_remove_zero_clock_base_cases_and_prologue_secp256k1_non_vacuous_and_tight
    t_user t_all g ht_user ht_all hg
  exact ⟨byte_coupled_witness_resolve_thirty_six_x_and_twenty_seven_x_non_vacuous_and_tight h_refs hb,
         pancake_stackRemove_compileProg_zeroExtraBodyClock_non_vacuous_and_tight
           arch prog wc ac perf dc info jump bounds generateGc maximumHeap pointer start,
         hst.1,
         hst.2.1⟩

/-- 7. Unconditional `StackToLab → LabToTarget` no-`locValue`-6 safety (`PanTargetSafe`, `PanUserSafe`,
`JumpOk`), `StackRemove` zero-clock contracts, byte-coupled witness resolve (`main200 = 24_381_873_932`
at `36×`, `main380 = 32_488_958_762` at `27×`), and prologue + post-EVM bounds. -/
theorem pan_to_target_no_loc_value_6_and_byte_coupled_witness_prologue_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (h_refs t_user t_all g k L E B r : Nat)
    (hb : 33 * h_refs ≤ inputBytes)
    (ht_user : 12000 * t_user ≤ 200000000)
    (ht_all : t_all ≤ 16668)
    (hg : 375 * g ≤ 200000000)
    (hk : 21 * k ≤ 2000000) (hL : L ≤ 5000)
    (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428) (hr : r ≤ 312) :
    (h_refs ≤ 4067203 ∧
      (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) ∧
      (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs) ∧
      (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
        probes 380000000 = 68115248) ∧
      8589933568 - probes 200000000 = 8523258320 ∧
      (main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200) ∧
      (main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380) ∧
      (yukon - 36 * main200 = 22972463922 ∧ yukon - 27 * main380 = 23518038900) ∧
      100 * 10938743528 > 44 * main200 ∧
      2 * 8 * hashRefs < 2 * 8 * 1110441952) ∧
    (((t_user ≤ 16666 ∧ 200000000 / 21000 = 9523) ∧
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
         | _ => stateRelHOL jump bounds pointer postSource postTarget))) :=
  ⟨byte_coupled_witness_resolve_thirty_six_x_and_twenty_seven_x_non_vacuous_and_tight h_refs hb,
   pan_to_target_no_loc_value_6_stack_remove_and_prologue_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h
     t_user t_all g k L E B r ht_user ht_all hg hk hL hB hEB hr⟩

/-- 8. Strictly increasing **84-budget** (`EightyFourShape`), **66-budget** (`SixtySixShape`),
64-budget (`SixtyFourShape`), 62-budget, 60-budget, 56-budget, 54-budget, 52-budget, and 50-budget
portfolios all `< 900_719_925_474`, united with byte-coupled witness resolve (`main200 =
24_381_873_932` at `36×`, `main380 = 32_488_958_762` at `27×`) and prologue + post-EVM bounds. -/
theorem eighty_four_and_sixty_six_budget_portfolios_and_byte_coupled_witness_non_vacuous_and_tight
    (h_refs t_user t_all g k L : Nat)
    (hb : 33 * h_refs ≤ inputBytes)
    (ht_user : 12000 * t_user ≤ 200000000)
    (ht_all : t_all ≤ 16668)
    (hg : 375 * g ≤ 200000000)
    (hk : 21 * k ≤ 2000000) (hL : L ≤ 5000)
    (l_chunks : List Nat) (ck : Nat) :
    EightyFourShape ∧
    (h_refs ≤ 4067203 ∧
      (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) ∧
      (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs) ∧
      (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
        probes 380000000 = 68115248) ∧
      8589933568 - probes 200000000 = 8523258320 ∧
      (main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200) ∧
      (main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380) ∧
      (yukon - 36 * main200 = 22972463922 ∧ yukon - 27 * main380 = 23518038900) ∧
      100 * 10938743528 > 44 * main200 ∧
      2 * 8 * hashRefs < 2 * 8 * 1110441952) ∧
    (SixtySixShape ∧
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
            (HeapAllocationContract ∧ HeapNodesContract ∧ HeapRateContract ∧ MemoContract ∧ BridgeContract)))))) :=
  ⟨eighty_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   byte_coupled_witness_resolve_thirty_six_x_and_twenty_seven_x_non_vacuous_and_tight h_refs hb,
   sixty_six_and_sixty_four_budget_portfolios_and_prologue_non_vacuous_and_tight
     t_user t_all g k L ht_user ht_all hg hk hL l_chunks ck⟩

/-- 9. Conditional finite certificates `InitE.Certificate (baselineWithFiniteK K) (.finite K)` across
the **84-budget** (`eightyFourPortfolio`), **66-budget** (`sixtySixPortfolio`), 64-budget
(`sixtyFourPortfolio`), 62-budget, 60-budget, and 56/54/52-budget portfolios under
`cert : CertificateAt 1_212_035_192`, united with byte-coupled witness resolve (`36×` / `27×`)
and prologue + post-EVM bounds. -/
theorem eighty_four_budget_explicit_certificates_and_byte_coupled_witness_non_vacuous_and_tight
    (cert : CertificateAt 1_212_035_192)
    (h_refs t_user t_all g k L K : Nat)
    (hb : 33 * h_refs ≤ inputBytes)
    (ht_user : 12000 * t_user ≤ 200000000)
    (ht_all : t_all ≤ 16668)
    (hg : 375 * g ≤ 200000000)
    (hk : 21 * k ≤ 2000000) (hL : L ≤ 5000) :
    (EightyFourShape ∧
      (∀ k' ∈ eightyFourPortfolio, InitE.Certificate (baselineWithFiniteK k') (.finite k'))) ∧
    (h_refs ≤ 4067203 ∧
      (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) ∧
      (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs) ∧
      (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
        probes 380000000 = 68115248) ∧
      8589933568 - probes 200000000 = 8523258320 ∧
      (main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200) ∧
      (main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380) ∧
      (yukon - 36 * main200 = 22972463922 ∧ yukon - 27 * main380 = 23518038900) ∧
      100 * 10938743528 > 44 * main200 ∧
      2 * 8 * hashRefs < 2 * 8 * 1110441952) ∧
    ((NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe ∧
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
            (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209)))))))) :=
  ⟨eighty_four_budget_certificates_non_vacuous_and_tight cert,
   byte_coupled_witness_resolve_thirty_six_x_and_twenty_seven_x_non_vacuous_and_tight h_refs hb,
   sixty_six_budget_explicit_certificates_and_prologue_secp256k1_non_vacuous_and_tight
     cert t_user t_all g k L K ht_user ht_all hg hk hL⟩

/-- 10. Grand self-contained synthesis (`W5_230`): unites
(1) Byte-coupled `_resolve_step` hash-reference bound (`refs_bound : h ≤ 4_067_203`, `refs_tight`,
    `ratio : 132×`, `probe_vals : 65_075_248 / 66_675_248 / 68_115_248`, `gain = 8_523_258_320`,
    `main200 = 24_381_873_932` passing `36×` Yukon with margin `22_972_463_922`, `main380 =
    32_488_958_762` passing `27×` Yukon with margin `23_518_038_900`, `decode_dominates : > 44%`),
(2) Salted `nodedb` + witness + MPT audit (`38_946_487_944`, `663 < 1000`, `26_801_608_212` /
    `30_612_453_042`, `postEvmSalted = 681_400_462`, `r = 1` lever `25_388_940_380` at `35×`) and
    whole-program `StackRemove` zero-extra-body-clock compilation (`initStubs`, `initCode`,
    `compileHOL`, `progComp`),
(3) Prologue and post-EVM bounds (`16_666` user txs + 2 system = `16_668`, `postTerms = 4_859_866_650`,
    prologue margins `671_493_809_131` at `1×` and `25_284_633_969` at `4×` memo), coupled-MPT
    `619_060_000`-tick saving, `L_max` thresholds (`38_817`, `40_284`, `5_040`, `6_507`), and
    unconditional `StackToLab → LabToTarget` no-`locValue`-6 safety,
(4) The strictly increasing **84-budget** (`EightyFourShape`, plus 66/64/62/60/56/54/52/50-budget)
    portfolio all `< 900_719_925_474` and conditional finite certificates
    `InitE.Certificate (baselineWithFiniteK K) (.finite K)`. -/
theorem grand_self_contained_byte_coupled_witness_thirty_six_x_and_eighty_four_budget_synth_non_vacuous_and_tight
    {C F : Type}
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
    (generateGc : Bool) (start : Nat)
    (h_refs t_user t_all g k L n u B_gas blk ck l_ext E B r ns nc : Nat)
    (hb : 33 * h_refs ≤ inputBytes)
    (ht_user : 12000 * t_user ≤ 200000000)
    (ht_all : t_all ≤ 16668)
    (hg : 375 * g ≤ 200000000)
    (hk : 21 * k ≤ 2000000) (hL : L ≤ 5000) (hu : n ≤ u) (hS : B_gas + u ≤ 2000000)
    (hblk : 40 * blk ≤ B_gas * B_gas) (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428) (hr : r ≤ 312)
    (h_nodedb : 4 * (ns + nc) ≤ maxInput)
    (cert : CertificateAt 1_212_035_192) :
    ((EightyFourShape ∧
       (∀ K ∈ eightyFourPortfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
     (h_refs ≤ 4067203 ∧
       (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) ∧
       (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs) ∧
       (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
         probes 380000000 = 68115248) ∧
       8589933568 - probes 200000000 = 8523258320 ∧
       (main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200) ∧
       (main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380) ∧
       (yukon - 36 * main200 = 22972463922 ∧ yukon - 27 * main380 = 23518038900) ∧
       100 * 10938743528 > 44 * main200 ∧
       2 * 8 * hashRefs < 2 * 8 * 1110441952) ∧
     (((decodeMemo + probesR8 + (20036870848 - 619060000) = 38946487944 ∧
         probesR8 = 8589933568) ∧
        probesR8 = 2 * 8 * (16 * 33554428)) ∧
       ((30 + 633 = 663 ∧ 663 < 1000) ∧
         (buildNodedb = 3038649506 ∧ walks 200000000 = 130000000 ∧
           rootTicks 200000000 = 4104281610)) ∧
       ((witnessMptSalted 200000000 = 26801608212 ∧
         witnessMptSalted 380000000 = 30612453042) ∧
        postEvmSalted = 681400462) ∧
       (GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200 = 32905132252 ∧
         27 * GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200 < yukon ∧
         yukon < 28 * GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200) ∧
       ((GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main380 = 41010777082 ∧
         21 * GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main380 < yukon ∧
         yukon < 22 * GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main380) ∧
        (yukon / 30 = 30023997515 ∧
         yukon < 30 * GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200)) ∧
       ((100 * (decodeMemo + probesR8) >
         59 * GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200) ∧
        (GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200 - probesR8 + 2 * 1 * 536870848 = 25388940380 ∧
         35 * 25388940380 < yukon ∧ yukon < 36 * 25388940380))) ∧
     ((∀ e ∈ initStubs (width := width) generateGc mh sp start, StackNoSt e.2 = true) ∧
       (∀ (s t : StackSemStateFiniteExact width C F) (r_res : Option (StackSemResult width)),
         StackSemEvaluate.evaluate (initCode generateGc mh sp, s) = (r_res, t) →
         t.clock = s.clock) ∧
       (∀ e ∈ StackRemove.compileHOL j bd generateGc mh sp start
           (StackAlloc.compile dc (StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
             (panToWordCompileProgHOL arch prog)).2).2.2.2)),
         e.1 = storeConstsStubLocation ∨ StackNoSt e.2 = true) ∧
       (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
           (panToWordCompileProgHOL arch prog)).2).2.2.2,
         y.1 = storeConstsStubLocation ∨
         ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
           (postSource target : StackSemStateFiniteExact width C F)
           (ptr' : Nat) (bd' : BitVec width × BitVec width) (j' : Bool),
           CodeNoSt source →
           StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
               (result, postSource) ∧ result ≠ some .error ∧
             StackRemove.stateRelHOL j' bd' ptr' source target ∧
             StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr' →
           ∃ clock postTarget, ClockOk clock result ∧
             StackSemEvaluate.evaluate (StackRemove.comp j' bd' ptr'
               (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
               {target with clock := clock + target.clock}) = (result, postTarget)))) ∧
    (((NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe ∧
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
              TransientStorageRemainingTablesAndFiftyBudgetMaster.RemainingTables))))))))) :=
  ⟨⟨eighty_four_budget_certificates_non_vacuous_and_tight cert,
    byte_coupled_witness_resolve_thirty_six_x_and_twenty_seven_x_non_vacuous_and_tight h_refs hb,
    ⟨dissect_and_probes_salted_non_vacuous_and_tight,
     visit_cost_and_rows_200_non_vacuous_and_tight,
     wm_vals_and_post_val_non_vacuous_and_tight,
     main200_slope_non_vacuous_and_tight,
     main380_slope_and_no_thirty_non_vacuous_and_tight,
     dominant_and_r1_lever_non_vacuous_and_tight⟩,
    pancake_stackRemove_compileProg_zeroExtraBodyClock_non_vacuous_and_tight
      arch prog wc ac perf dc info j bd generateGc mh sp start⟩,
   grand_self_contained_prologue_secp256k1_and_sixty_six_budget_synth_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h info j bd ptr f
     t_user t_all g k L n u B_gas blk ck l_ext E B r ns nc
     ht_user ht_all hg hk hL hu hS hblk hB hEB hr h_nodedb cert⟩

#print axioms byte_coupled_witness_resolve_thirty_six_x_and_twenty_seven_x_non_vacuous_and_tight
#print axioms byte_coupled_witness_and_salted_nodedb_sub_twenty_billion_non_vacuous_and_tight
#print axioms byte_coupled_witness_and_prologue_tx_secp256k1_post_terms_non_vacuous_and_tight
#print axioms byte_coupled_witness_prologue_margins_and_coupled_mpt_lmax_non_vacuous_and_tight
#print axioms byte_coupled_witness_exact_decode_ticks_and_mpt_nodedb_bridge_non_vacuous_and_tight
#print axioms stack_remove_compile_prog_zero_clock_and_byte_coupled_witness_non_vacuous_and_tight
#print axioms pan_to_target_no_loc_value_6_and_byte_coupled_witness_prologue_non_vacuous_and_tight
#print axioms eighty_four_and_sixty_six_budget_portfolios_and_byte_coupled_witness_non_vacuous_and_tight
#print axioms eighty_four_budget_explicit_certificates_and_byte_coupled_witness_non_vacuous_and_tight
#print axioms grand_self_contained_byte_coupled_witness_thirty_six_x_and_eighty_four_budget_synth_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedByteCoupledWitnessThirtySixXAndEightyFourBudgetSynth
