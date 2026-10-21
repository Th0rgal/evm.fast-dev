import InitECandidate.Solver.WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster
import InitECandidate.Solver.SelfContainedMptNodedbTransientAndFiftyFourBudgetSynth
import InitECandidate.Solver.WitnessDagMemoizationAndFiftyFourBudgetBridge

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedWitnessDagMemoizationAndFiftySixBudgetSynth`

Self-contained Wave 5 synthesis (`W5_162`, `0` imports from `InitECandidate.Proofs.Bounded*`)
uniting:
1. **`WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster` (`12/12` tight)**:
   - Per-node heap allocation floors (`leaf ≥ 98`, `ext ≥ 90`, `branch ≥ 448` via `HeapAllocationContract`),
     the `345_470_831` node cap under `31_092_374_808` bytes (`HeapNodesContract`), tick-rate thresholds
     `τ ≤ 28` (`1×`) and `τ ≤ 5` (`5×`) (`HeapRateContract`), and DAG memoization (`33_554_428` nodes,
     `15_300_819_168` bytes, `τ ≤ 58` via `MemoContract`),
   - The MPT + `nodedb` (`20_036_870_848` ticks) + `ts+64` (`176_125_863_653` ticks, `5× = 880_629_318_265`,
     margin `20_090_607_209`) bridge (`BridgeContract`) and universal run-cap absorption (`AbsorptionContract`),
   - Unconditional absence of jumps/calls into section 6 (`panToTarget_noStubJump`,
     `panToTarget_user_noStubJump`),
   - Strictly increasing **56-budget** portfolio (`FiftySixShape`, `ClaimPayloads`) below Yukon
     (`900_719_925_474`) and conditional finite certificate lifting (`certificates_non_vacuous_and_tight`).
2. **`SelfContainedMptNodedbTransientAndFiftyFourBudgetSynth` (`10/10` tight)**:
   - Complete synthesis of MPT + `nodedb` + `ts+64` joint bridge, Hex-Prefix zero-length extension
     rejection (`ext_zero_rejected`), `walk_bound_decoded ≤ 64` (`+ 1 ≤ 65`), exponential witness heap
     expansion blocked at `555_220_978` nodes (`heap_nodes`, `expansion_fits`, `expansion_traps`),
   - Unconditional `FrontendSafe`, `PanLabSafe`, `PanTargetSafe`, `PanUserSafe`, `CompilerSafety`, and
     the 50/52/54-budget portfolios.
3. **`WitnessDagMemoizationAndFiftyFourBudgetBridge` (`10/10` tight)**:
   - Direct bridges `heap_floors_non_vacuous_and_tight`, `nodes_cap_non_vacuous_and_tight`,
     `tau_one_non_vacuous_and_tight`, `tau_five_non_vacuous_and_tight`, `memo_non_vacuous_and_tight`,
     `ext_zero_non_vacuous_and_tight`, `walk_decoded_non_vacuous_and_tight`,
     `no_stub_jump_non_vacuous_and_tight`, `portfolio_54_non_vacuous_and_tight`, and
     `payloads_54_non_vacuous_and_tight`.
-/

namespace InitECandidate.Solver.SelfContainedWitnessDagMemoizationAndFiftySixBudgetSynth

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestMptTraversalAndStateRootBound (Step advance)
open InitECandidate.Solver.GuestWitnessDecodeAndExtensionNibbleAudit (
  compactLen
  extAccepted
  ext_zero_rejected
  walk_bound_decoded
)
open InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound (
  heapAvail
  heapOf
  heap_avail_val
  nodes_by_heap
  nodes_by_heap_tight
  branches_by_heap
  decode_heap_bound
  heap_threshold
  heap_threshold_5x
  nodes_memo
  memo_heap
  memo_threshold
  memo_gain
)
open InitECandidate.Solver.GuestNodedbAndWitnessTableBound (
  maxInput
  capOf
  worstBuild
  boundedBuild
)
open InitECandidate.Solver.GuestTransientStorageAndRemainingTablesAudit (
  intrinsic keyGas txCap buildTicks
)
open InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge (
  mptPlusBuild
  joint
  sum_val
  sum_margin
  joint_val
  joint_once
  joint_five
  two_builds_at_8
  mpt_plus_two_builds
  joint_covers
  build_split
  anchors
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
open InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster (
  FiftyShape
  KeyCap
  PackingAndBuild
  BlockCosts
  OneSlopeMargin
  TransientObstruction
  RemainingTables
  CompilerSafety
)
open InitECandidate.Solver.TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster (
  FiftyTwoShape
)
open InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open InitECandidate.Solver.PanToLabSectionAndStackRemoveClock (IsStubLabel)
open InitECandidate.Solver.StackToLabAndLabToTargetNoStubCall (
  J
  JC
  AOk
  LOk
  JumpOk
  Sec
)
open InitECandidate.Solver.WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster (
  portfolio
  fiftySixClaims
  HeapAllocationContract
  HeapNodesContract
  HeapRateContract
  MemoContract
  BridgeContract
  AbsorptionContract
  FiftySixShape
  ClaimPayloads
  heap_allocation_non_vacuous_and_tight
  heap_nodes_non_vacuous_and_tight
  heap_rates_non_vacuous_and_tight
  memo_non_vacuous_and_tight
  bridge_arithmetic_non_vacuous_and_tight
  bridge_absorption_non_vacuous_and_tight
  panToTarget_noStubJump_non_vacuous_and_tight
  panToTarget_user_noStubJump_non_vacuous_and_tight
  portfolio_non_vacuous_and_tight
  payloads_non_vacuous_and_tight
  certificates_non_vacuous_and_tight
  integrated_master_non_vacuous_and_tight
)
open InitECandidate.Solver.SelfContainedMptNodedbTransientAndFiftyFourBudgetSynth (
  fiftyFourPortfolio
  FiftyFourClaimPayloads
  mpt_nodedb_and_transient_storage_joint_bridge_non_vacuous_and_tight
  mpt_contracts_and_decoded_extension_heap_synthesis_non_vacuous_and_tight
  witness_decode_nodedb_and_mpt_bridge_synthesis_non_vacuous_and_tight
  transient_superadditivity_run_cap_and_joint_five_slope_synthesis_non_vacuous_and_tight
  coupled_journal_yukon_headroom_and_mpt_nodedb_bridge_non_vacuous_and_tight
  unconditional_frontend_and_backend_no_stub_jump_and_no_store_consts_non_vacuous_and_tight
  witness_decode_mpt_bridge_and_pan_to_target_no_stub_jump_non_vacuous_and_tight
  fifty_fifty_two_and_fifty_four_budget_portfolios_and_payloads_non_vacuous_and_tight
  fifty_four_budget_explicit_certificates_and_integrated_master_non_vacuous_and_tight
  grand_self_contained_mpt_nodedb_transient_and_fifty_four_budget_synth_non_vacuous_and_tight
)
open InitECandidate.Solver.WitnessDagMemoizationAndFiftyFourBudgetBridge (
  heap_floors_non_vacuous_and_tight
  nodes_cap_non_vacuous_and_tight
  tau_one_non_vacuous_and_tight
  tau_five_non_vacuous_and_tight
  ext_zero_non_vacuous_and_tight
  walk_decoded_non_vacuous_and_tight
  no_stub_jump_non_vacuous_and_tight
  portfolio_54_non_vacuous_and_tight
  payloads_54_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.YukonVerifyScriptAudit (validFiniteClaim)

variable {width : Nat} [NeZero width]

abbrev fiftySixPortfolio : List Nat :=
  InitECandidate.Solver.WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.portfolio

abbrev FiftySixClaimPayloads : Prop :=
  InitECandidate.Solver.WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.ClaimPayloads

/-! ## Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- 1. Per-node heap allocation floors (`leaf ≥ 98`, `ext ≥ 90`, `branch ≥ 448`), the `345_470_831`
node ceiling under `31_092_374_808` bytes (and `69_402_622` branch cap), tick-rate thresholds
`τ ≤ 28` (`1×`) and `τ ≤ 5` (`5×`), and DAG memoization (`33_554_428` nodes, `15_300_819_168` bytes,
`τ ≤ 58`). -/
theorem witness_dag_memoization_and_heap_floors_rates_non_vacuous_and_tight
    (L E B n : Nat) (h_heap : heapOf L E B ≤ heapAvail) (h_br : heapOf 0 0 B ≤ heapAvail)
    (hn : 4 * n ≤ 134217712) (h_memo : L + E + B ≤ n) :
    HeapAllocationContract ∧
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
      58 * 15300819168 < yukon ∧ yukon < 59 * 15300819168) :=
  ⟨heap_allocation_non_vacuous_and_tight,
   heap_nodes_non_vacuous_and_tight,
   heap_rates_non_vacuous_and_tight,
   memo_non_vacuous_and_tight,
   heap_floors_non_vacuous_and_tight,
   nodes_cap_non_vacuous_and_tight L E B h_heap,
   branches_by_heap B h_br,
   tau_one_non_vacuous_and_tight,
   tau_five_non_vacuous_and_tight,
   WitnessDagMemoizationAndFiftyFourBudgetBridge.memo_non_vacuous_and_tight L E B n hn h_memo⟩

/-- 2. Synthesis of the MPT + `nodedb` (`20_036_870_848` ticks) + `ts+64` storage bridge
(`176_125_863_653` ticks at `1×` with margin `724_594_061_821`, `5× = 880_629_318_265 < 900_719_925_474`
with margin `20_090_607_209`), universal run-cap absorption (`AbsorptionContract`), and two-table
state+code coverage at `r = 8`. -/
theorem mpt_nodedb_transient_bridge_and_absorption_synthesis_non_vacuous_and_tight
    (ns nc : Nat) (h : 4 * (ns + nc) ≤ maxInput) :
    BridgeContract ∧
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
     (10 * 5000 = 50000 ∧ 50000 < 10 * 5001 ∧ 5 * 10000 = 50000 ∧ 50000 < 5 * 10001)) :=
  ⟨bridge_arithmetic_non_vacuous_and_tight,
   bridge_absorption_non_vacuous_and_tight,
   mpt_nodedb_and_transient_storage_joint_bridge_non_vacuous_and_tight ns nc h⟩

/-- 3. Synthesis of Hex-Prefix zero-length extension rejection (`ext_zero_rejected`), decoded walk
bound (`walk_bound_decoded ≤ 64`, `+ 1 ≤ 65`), MPT traversal/access/state-root/witness contracts,
and both witness heap bounds (`345_470_831` decoded nodes under `98/90/448` floors, `33_554_428`
DAG-memoized nodes at `15_300_819_168` bytes, and `555_220_978` raw 56-byte extension cap). -/
theorem extension_zero_rejected_walk_bound_and_dag_memoization_non_vacuous_and_tight
    (ck l_ext : Nat) :
    HeapAllocationContract ∧
    HeapNodesContract ∧
    HeapRateContract ∧
    MemoContract ∧
    WalkContract ∧
    (AccessContract ∧ RootContract) ∧
    (WalkContract ∧
     AccessContract ∧
     RootContract ∧
     WitnessLinearContract ∧
     ((∀ n : Nat, 1 ≤ n → compactLen n 0 = 2 * n - 2 ∧ compactLen n 1 = 2 * n - 1) ∧
      (∀ n odd : Nat, 1 ≤ n → odd ≤ 1 → (compactLen n odd = 0 ↔ n = 1 ∧ odd = 0)) ∧
      (compactLen 1 0 = 0 ∧ compactLen 1 1 = 1 ∧ compactLen 33 0 = 64 ∧ compactLen 32 1 = 63) ∧
      extAccepted 0 ck = false ∧
      (extAccepted l_ext 2 = false ∧ extAccepted l_ext 1 = false) ∧
      (∀ l' ck' : Nat, extAccepted l' ck' = true → 1 ≤ advance (.ext l')) ∧
      (extAccepted 1 3 = true ∧ extAccepted 1 0 = true ∧ advance (.ext 1) = 1)) ∧
     ((∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
        ((l.map Step.ext).map advance).sum ≤ 64 → l.length ≤ 64 ∧ l.length + 1 ≤ 65) ∧
      (∀ l ck' : Nat, extAccepted l ck' = true → 1 ≤ advance (.ext l)) ∧
      ((List.replicate 64 1).length = 64 ∧
        (((List.replicate 64 1).map Step.ext).map advance).sum = 64) ∧
      (33806089496 - 2713714688) / 56 = 555220978 ∧
      ((List.range 7).foldl (fun a i => a + 16 ^ i) 0 = 17895697 ∧
        17895697 * 176 + 16 ^ 7 * 64 = 20329511856 ∧
        20329511856 ≤ 33806089496 - 2713714688) ∧
      33806089496 - 2713714688 < 16 ^ 8 * 64 ∧
      (17895697 + 16 ^ 7 = 286331153 ∧ 8 * 530 < 4300))) :=
  ⟨heap_allocation_non_vacuous_and_tight,
   heap_nodes_non_vacuous_and_tight,
   heap_rates_non_vacuous_and_tight,
   memo_non_vacuous_and_tight,
   ext_zero_non_vacuous_and_tight,
   walk_decoded_non_vacuous_and_tight,
   mpt_contracts_and_decoded_extension_heap_synthesis_non_vacuous_and_tight ck l_ext⟩

/-- 4. Synthesis of witness decoding (`ext_zero_rejected`, `walk_bound_decoded`), `nodedb` table
capacity and run-length threshold (`r = 8` vs `r = 13_422`), DAG memoization (`33_554_428` nodes,
`15_300_819_168` bytes, `τ ≤ 58`), and the joint MPT + `nodedb` (`20_036_870_848`) + `ts+64`
(`176_125_863_653`, `5× = 880_629_318_265`, margin `20_090_607_209`) bridge. -/
theorem witness_dag_nodedb_capacity_and_mpt_bridge_synthesis_non_vacuous_and_tight
    (ck l_ext ns nc : Nat) (h : 4 * (ns + nc) ≤ maxInput) :
    HeapAllocationContract ∧
    HeapNodesContract ∧
    HeapRateContract ∧
    MemoContract ∧
    BridgeContract ∧
    ((((∀ n : Nat, 1 ≤ n → compactLen n 0 = 2 * n - 2 ∧ compactLen n 1 = 2 * n - 1) ∧
       (∀ n odd : Nat, 1 ≤ n → odd ≤ 1 → (compactLen n odd = 0 ↔ n = 1 ∧ odd = 0)) ∧
       (compactLen 33 0 = 64 ∧ compactLen 32 1 = 63) ∧
       extAccepted 0 ck = false ∧
       (extAccepted l_ext 2 = false ∧ extAccepted l_ext 1 = false) ∧
       (∀ l' ck' : Nat, extAccepted l' ck' = true → 1 ≤ advance (.ext l')) ∧
       (∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
         ((l.map Step.ext).map advance).sum ≤ 64 → l.length ≤ 64) ∧
       (33806089496 - 2713714688) / 56 = 555220978 ∧
       ((List.range 7).foldl (fun a i => a + 16 ^ i) 0 = 17895697 ∧
         17895697 * 176 + 16 ^ 7 * 64 = 20329511856 ∧
         20329511856 ≤ 33806089496 - 2713714688) ∧
       33806089496 - 2713714688 < 16 ^ 8 * 64 ∧
       (17895697 + 16 ^ 7 = 286331153 ∧ 8 * 530 < 4300)) ∧
      ((∀ n : Nat, 4 * n ≤ maxInput → n ≤ 33554428) ∧
       4 * 33554428 = maxInput ∧
       (2 * 33554428 + 2 ≤ 67108864 ∧ 33554432 < 2 * 33554428 + 2) ∧
       (∀ n c : Nat, 2 * n + 2 ≤ c → (n + 1) * 2 ≤ c) ∧
       (capOf 0 = 4 ∧ capOf 1 = 4 ∧ capOf 2 = 8 ∧ capOf 7 = 16)) ∧
      ((worstBuild 33554428 = 1125899604852756 ∧ yukon < worstBuild 33554428) ∧
       (boundedBuild 8 33554428 = 536870848 ∧ boundedBuild 8 33554428 < yukon) ∧
       (boundedBuild 13421 33554428 < yukon ∧ yukon < boundedBuild 13422 33554428) ∧
       (∀ r a b : Nat, a ≤ b → boundedBuild r a ≤ boundedBuild r b) ∧
       33554428 * 67108864 / 2 = 1125899772624896 ∧
       (∀ r ns' nc' : Nat, 4 * (ns' + nc') ≤ maxInput →
         boundedBuild r ns' + boundedBuild r nc' ≤ boundedBuild r 33554428))) ∧
     (mptPlusBuild = 20036870848 ∧
      joint = 176125863653 ∧
      (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209) ∧
      156088992805 + 19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ joint)) :=
  ⟨heap_allocation_non_vacuous_and_tight,
   heap_nodes_non_vacuous_and_tight,
   heap_rates_non_vacuous_and_tight,
   memo_non_vacuous_and_tight,
   bridge_arithmetic_non_vacuous_and_tight,
   witness_decode_nodedb_and_mpt_bridge_synthesis_non_vacuous_and_tight ck l_ext ns nc h⟩

/-- 5. Synthesis of `buildTicks` superadditivity, EIP-1153 per-tx/block packing, sharp run-cap
thresholds (`L ≤ 5_000` with `REVERT`, `L ≤ 10_000` without), universal run-cap absorption
(`AbsorptionContract`), coupled journal headroom (`CoupledJournalContract`), and the joint
`176_125_863_653` (`5× = 880_629_318_265`, margin `20_090_607_209`) bridge. -/
theorem transient_superadditivity_coupled_journal_and_joint_bridge_non_vacuous_and_tight
    (a b : Nat) (l : List Nat) (L ns nc : Nat) (h : 4 * (ns + nc) ≤ maxInput) :
    BridgeContract ∧
    AbsorptionContract ∧
    ((((a * (a - 1) + b * (b - 1) ≤ (a + b) * (a + b - 1) ∧
          buildTicks a + buildTicks b ≤ buildTicks (a + b) ∧
          (l.map buildTicks).sum ≤ buildTicks l.sum ∧
          (buildTicks 2 + buildTicks 2 = 10 ∧ buildTicks 4 = 30) ∧
          2 * buildTicks 158_162 = 125_075_300_410 ∧
          (2 * buildTicks 79_081 = 31_268_627_400 ∧ buildTicks 158_162 = 62_537_650_205)) ∧
         KeyCap ∧
         PackingAndBuild ∧
         ((∀ k : Nat, intrinsic + keyGas * k ≤ txCap → buildTicks k ≤ 62_537_650_205) ∧
          (intrinsic + keyGas * 158_162 ≤ txCap ∧ buildTicks 158_162 = 62_537_650_205)) ∧
         BlockCosts) ∧
       (((l.map buildTicks).sum ≤ buildTicks l.sum ∧
          buildTicks 2 + buildTicks 2 = 10 ∧ buildTicks 4 = 30 ∧
          buildTicks 2 + buildTicks 2 < buildTicks 4 ∧
          ([158162].map buildTicks).sum = buildTicks ([158162].sum)) ∧
        (2 * buildTicks 158162 = 125075300410 ∧
          2 * buildTicks 79081 = 31268627400 ∧ buildTicks 158162 = 62537650205) ∧
        ((10 * L ≤ 50000 ↔ L ≤ 5000) ∧ (5 * L ≤ 50000 ↔ L ≤ 10000) ∧
          (10 * 5000 = 50000 ∧ 50000 < 10 * 5001 ∧
           5 * 10000 = 50000 ∧ 50000 < 5 * 10001)) ∧
        ((∀ L' n u B blk : Nat, L' ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
            40 * blk ≤ B * B → blk + 10 * L' * n ≤ 100000000000) ∧
          (10 * 5000 * 2000000 = 100000000000) ∧
          100000000000 ≤ 156088992805 ∧
          5 * 156088992805 < yukon ∧ yukon < 6 * 156088992805 ∧ 5000 < 158162))) ∧
     (mptPlusBuild = 20036870848 ∧
      joint = 176125863653 ∧
      yukon - joint = 724594061821 ∧
      (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209) ∧
      156088992805 + 19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ joint)) ∧
    (CoupledJournalContract ∧
     (((∀ l' : List Nat, (∀ x ∈ l', x ≠ 0) →
          ((l'.map Step.ext).map advance).sum ≤ 64 → l'.length ≤ 64) ∧
        ((List.replicate 64 1).length = 64 ∧
          (((List.replicate 64 1).map Step.ext).map advance).sum = 64)) ∧
      (((∀ u1 u2 t1 t2 : Nat, u1 + u2 ≤ 2000000 → t1 ≤ 373022 * u1 →
            t2 ≤ 373022 * u2 → t1 + t2 ≤ 746044000000) ∧
          100 * 2000000 = 200000000 ∧
          373022 * 2000000 + 373022 * 0 = 746044000000 ∧
          11 * buildTicks 158162 + buildTicks 145647 = 740946409660 ∧
          746044000000 - 740946409660 = 5097590340) ∧
        ((746044000000 + 4159564234 < yukon ∧
            yukon - (746044000000 + 4159564234) = 150516361240 ∧
            yukon < 2 * (740946409660 + 4159564234)) ∧
          746044000000 < 740946409660 + 156088992805) ∧
        ((∀ j : List Bool, j.length ≤ 524288 →
            _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.restoreDels j ≤ 524288) ∧
          _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.restoreDels
            (List.replicate 524288 false) = 524288 ∧
          (_root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.restoreDels [false, true, false] = 2 ∧
           _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.restoreDels [true, true] = 0) ∧
          ((1 + 1 : Nat) = 2 ∧ (1 + 1 + 1 : Nat) = 3)) ∧
        ((∀ k : Nat, k ≤ 158162 → 100 * buildTicks k ≤ 373022 * (106 * k)) ∧
          ¬ (250 * (158162 - 1) ≤ 106 * 373021) ∧
          (2000000 / 20 / 2 + 13 * 167772 / 84 + 1 = 75965 ∧ 75965 < 373022)) ∧
        (KeyCap ∧ PackingAndBuild ∧ BlockCosts ∧ OneSlopeMargin ∧ TransientObstruction ∧ RemainingTables))) ∧
     (mptPlusBuild = 20036870848 ∧
      joint = 176125863653 ∧
      (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209))) :=
  ⟨bridge_arithmetic_non_vacuous_and_tight,
   bridge_absorption_non_vacuous_and_tight,
   transient_superadditivity_run_cap_and_joint_five_slope_synthesis_non_vacuous_and_tight a b l L ns nc h,
   coupled_journal_yukon_headroom_and_mpt_nodedb_bridge_non_vacuous_and_tight⟩

/-- 6. Complete unconditional compiler safety synthesis across `FrontendSafe`, `PanLabSafe`,
`PanTargetSafe` (`panToTarget_noStubJump`), `PanUserSafe` (`panToTarget_user_noStubJump`), and
`NoStoreConsts` / `StackNoSt` / `NoStubCall` preservation (`CompilerSafety`). -/
theorem unconditional_pan_to_target_no_stub_jump_and_compiler_safety_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (sid next : Nat) (cs bs : List Nat) :
    (PanTargetSafe ∧ PanUserSafe) ∧
    (FrontendSafe ∧
     PanLabSafe ∧
     PanTargetSafe ∧
     PanUserSafe ∧
     (CompilerSafety arch prog wc ac perf info j bd ptr f ∧
      ((∀ p : HolProg width, JC p = (StackNoSt p && J p)) ∧
       (∀ (info' : Spt Nat) (j' : Bool) (bd' : BitVec width × BitVec width) (ptr' n : Nat) (p : HolProg width),
         JC p = true →
         JC (StackNames.progCompHOL f (StackRemove.comp j' bd' ptr'
           (StackAlloc.progComp (n, StackRawCall.compTop info' p)).2)) = true) ∧
       (∀ (n : Nat) (p : HolProg width), n ≠ storeConstsStubLocation → JC p = true →
         LOk (StackToLab.progToSectionHOL (n, p)).lines) ∧
       StackNoSt (StackNames.progCompHOL f (.storeConsts 0 1 none : HolProg width)) = false ∧
       JC (.rawCall storeConstsStubLocation : HolProg width) = false ∧
       ¬ AOk (StackToLab.flattenHOL false (.rawCall storeConstsStubLocation : HolProg width) sid next cs bs).1 ∧
       JumpOk (.labAsm (.jump (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
       JumpOk (.labAsm (.call (.lab 64 0)) (0 : BitVec width) [] 0) = true) ∧
      (∀ s ∈ StackToLab.compile sc dc mh sp off
          (compileNative ac perf (WordToWord.compile wc ac
            (panToWordCompileProgHOL arch prog)).2).2.2.2,
        IsStubLabel s.sectionId = true ∨ LOk s.lines) ∧
      (∀ (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
          (L' : List (Sec width)) (labs' : Spt (Spt Nat)),
        removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
          (compileNative ac perf (WordToWord.compile wc ac
            (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs') →
        (∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨ ∀ x ∈ s'.lines, JumpOk x = true) ∧
        (∀ s' ∈ L', IsStubLabel s'.sectionId = false → ∀ x ∈ s'.lines, JumpOk x = true)) ∧
      IsStubLabel (storeConstsStubLocation : Nat) = true ∧
      IsStubLabel (64 : Nat) = false)) :=
  ⟨no_stub_jump_non_vacuous_and_tight,
   unconditional_frontend_and_backend_no_stub_jump_and_no_store_consts_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off info j bd ptr f sid next cs bs⟩

/-- 7. Joint synthesis of witness DAG memoization (`33_554_428` nodes, `15_300_819_168` bytes,
`τ ≤ 58`), node heap floors (`98/90/448`, cap `345_470_831`), zero-length extension rejection
(`ext_zero_rejected`), `walk_bound_decoded ≤ 64`, MPT + `nodedb` + `ts+64` joint arithmetic
(`20_036_870_848`, `176_125_863_653`, `5× = 880_629_318_265`), and unconditional `PanSimp → LabToTarget`
section-6 unreachability (`panToTarget_noStubJump`, `panToTarget_user_noStubJump`). -/
theorem witness_dag_decode_mpt_bridge_and_pan_to_target_no_stub_jump_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width) (ck l_ext : Nat) :
    HeapAllocationContract ∧
    HeapNodesContract ∧
    HeapRateContract ∧
    MemoContract ∧
    BridgeContract ∧
    ((((∀ n : Nat, 1 ≤ n → compactLen n 0 = 2 * n - 2 ∧ compactLen n 1 = 2 * n - 1) ∧
       (∀ n odd : Nat, 1 ≤ n → odd ≤ 1 → (compactLen n odd = 0 ↔ n = 1 ∧ odd = 0)) ∧
       (compactLen 33 0 = 64 ∧ compactLen 32 1 = 63) ∧
       extAccepted 0 ck = false ∧
       (extAccepted l_ext 2 = false ∧ extAccepted l_ext 1 = false) ∧
       (∀ l' ck' : Nat, extAccepted l' ck' = true → 1 ≤ advance (.ext l')) ∧
       (∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
         ((l.map Step.ext).map advance).sum ≤ 64 → l.length ≤ 64) ∧
       (33806089496 - 2713714688) / 56 = 555220978 ∧
       ((List.range 7).foldl (fun a i => a + 16 ^ i) 0 = 17895697 ∧
         17895697 * 176 + 16 ^ 7 * 64 = 20329511856 ∧
         20329511856 ≤ 33806089496 - 2713714688) ∧
       33806089496 - 2713714688 < 16 ^ 8 * 64 ∧
       (17895697 + 16 ^ 7 = 286331153 ∧ 8 * 530 < 4300)) ∧
      ((∀ s ∈ StackToLab.compile sc dc mh sp off
          (compileNative ac perf (WordToWord.compile wc ac
            (panToWordCompileProgHOL arch prog)).2).2.2.2,
        IsStubLabel s.sectionId = true ∨ LOk s.lines) ∧
       JumpOk (.labAsm (.jump (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
       JumpOk (.labAsm (.call (.lab 64 0)) (0 : BitVec width) [] 0) = true) ∧
      ((∀ (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
          (L' : List (Sec width)) (labs' : Spt (Spt Nat)),
        removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
          (compileNative ac perf (WordToWord.compile wc ac
            (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs') →
        ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨ ∀ x ∈ s'.lines, JumpOk x = true) ∧
       JumpOk (.labAsm (.jump (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
       JumpOk (.labAsm (.call (.lab 64 0)) (0 : BitVec width) [] 0) = true) ∧
      ((∀ (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
          (L' : List (Sec width)) (labs' : Spt (Spt Nat)),
        removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
          (compileNative ac perf (WordToWord.compile wc ac
            (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs') →
        ∀ s' ∈ L', IsStubLabel s'.sectionId = false → ∀ x ∈ s'.lines, JumpOk x = true) ∧
       IsStubLabel (storeConstsStubLocation : Nat) = true ∧
       IsStubLabel (64 : Nat) = false ∧
       JumpOk (.labAsm (.jump (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
       JumpOk (.labAsm (.call (.lab 64 0)) (0 : BitVec width) [] 0) = true)) ∧
     (WalkContract ∧ AccessContract ∧ RootContract ∧ WitnessLinearContract ∧
      mptPlusBuild = 20036870848 ∧
      joint = 176125863653 ∧
      (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209))) :=
  ⟨heap_allocation_non_vacuous_and_tight,
   heap_nodes_non_vacuous_and_tight,
   heap_rates_non_vacuous_and_tight,
   memo_non_vacuous_and_tight,
   bridge_arithmetic_non_vacuous_and_tight,
   witness_decode_mpt_bridge_and_pan_to_target_no_stub_jump_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off ck l_ext⟩

/-- 8. Strictly increasing 50-budget, 52-budget, 54-budget (`FiftyFourShape`, `FiftyFourClaimPayloads`),
and **56-budget** (`FiftySixShape`, `FiftySixClaimPayloads`) portfolios below the Yukon ceiling
(`900_719_925_474`) coupled with the MPT + `nodedb` + `ts+64` bridge (`20_036_870_848`,
`176_125_863_653`, `5× = 880_629_318_265`) and witness DAG memoization (`33_554_428` nodes,
`15_300_819_168` bytes, `τ ≤ 58`). -/
theorem fifty_four_and_fifty_six_budget_portfolios_and_payloads_non_vacuous_and_tight
    (l_chunks : List Nat) (ck : Nat) :
    (FiftySixShape ∧ FiftySixClaimPayloads) ∧
    ((fiftyFourPortfolio.length = 54 ∧ fiftyFourPortfolio.Pairwise (· < ·) ∧
       (∀ K ∈ fiftyFourPortfolio, 1212035192 ≤ K ∧ K < yukon)) ∧
     FiftyFourClaimPayloads) ∧
    ((FiftyFourShape ∧ FiftyFourClaimPayloads) ∧
     ((FiftyShape ∧ SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth.FiftyClaimPayloads) ∧
      (FiftyTwoShape ∧ SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth.FiftyTwoClaimPayloads) ∧
      ((l_chunks.map buildTicks).sum ≤ buildTicks l_chunks.sum ∧
       (buildTicks 2 + buildTicks 2 = 10 ∧ buildTicks 4 = 30) ∧
       (∀ L n u B blk : Nat, L ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
         40 * blk ≤ B * B → blk + 10 * L * n ≤ 100000000000)) ∧
      (extAccepted 0 ck = false ∧
       (∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
         ((l.map Step.ext).map advance).sum ≤ 64 → l.length ≤ 64) ∧
       (33806089496 - 2713714688) / 56 = 555220978)) ∧
     (mptPlusBuild = 20036870848 ∧
      joint = 176125863653 ∧
      yukon - joint = 724594061821 ∧
      (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209))) ∧
    (HeapAllocationContract ∧ HeapNodesContract ∧ HeapRateContract ∧ MemoContract ∧ BridgeContract) :=
  ⟨⟨portfolio_non_vacuous_and_tight, payloads_non_vacuous_and_tight⟩,
   ⟨portfolio_54_non_vacuous_and_tight, payloads_54_non_vacuous_and_tight⟩,
   fifty_fifty_two_and_fifty_four_budget_portfolios_and_payloads_non_vacuous_and_tight l_chunks ck,
   ⟨heap_allocation_non_vacuous_and_tight, heap_nodes_non_vacuous_and_tight,
    heap_rates_non_vacuous_and_tight, memo_non_vacuous_and_tight,
    bridge_arithmetic_non_vacuous_and_tight⟩⟩

/-- 9. Explicit finite certificates across the 50-budget, 52-budget, 54-budget, and **56-budget**
portfolios under the base certificate hypothesis `cert : CertificateAt 1_212_035_192`, united with
both the 56-budget and 54-budget integrated master theorems. -/
theorem fifty_six_budget_explicit_certificates_and_integrated_master_non_vacuous_and_tight
    (cert : CertificateAt 1_212_035_192) (K : Nat) :
    (HeapAllocationContract ∧ HeapNodesContract ∧ HeapRateContract ∧ MemoContract ∧
     BridgeContract ∧ AbsorptionContract ∧
     FrontendSafe ∧ PanLabSafe ∧ PanTargetSafe ∧ PanUserSafe ∧
     FiftySixShape ∧ FiftySixClaimPayloads ∧
     (∀ k ∈ fiftySixPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
    ((WalkContract ∧ AccessContract ∧ RootContract ∧ WitnessLinearContract ∧
      CoupledJournalContract ∧ FrontendSafe ∧ PanLabSafe ∧ PanTargetSafe ∧ PanUserSafe ∧
      FiftyFourShape ∧ FiftyFourClaimPayloads ∧
      (∀ k ∈ fiftyFourPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
     ((FiftyTwoShape ∧ SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth.FiftyTwoClaimPayloads ∧
       (∀ k ∈ SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth.fiftyTwoPortfolio,
         InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
      ((∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
         ((l.map Step.ext).map advance).sum ≤ 64 → l.length ≤ 64) ∧
       (∀ L n u B blk : Nat, L ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
         40 * blk ≤ B * B → blk + 10 * L * n ≤ 100000000000)) ∧
      (K = K)) ∧
     (mptPlusBuild = 20036870848 ∧
      joint = 176125863653 ∧
      (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209))) :=
  ⟨integrated_master_non_vacuous_and_tight cert,
   fifty_four_budget_explicit_certificates_and_integrated_master_non_vacuous_and_tight cert K⟩

/-- 10. Grand self-contained synthesis (`W5_162`): unites
(1) per-node heap allocation floors (`leaf ≥ 98`, `ext ≥ 90`, `branch ≥ 448`), the `345_470_831`
    node ceiling on `31_092_374_808` bytes, tick-rate thresholds `τ ≤ 28` (`1×`) and `τ ≤ 5` (`5×`),
    and DAG memoization (`33_554_428` nodes, `15_300_819_168` bytes, `τ ≤ 58`),
(2) the MPT + `nodedb` + `ts+64` joint bridge (`20_036_870_848` ticks MPT+nodedb, combined envelope
    `176_125_863_653`, `5× = 880_629_318_265 < 900_719_925_474`, margin `20_090_607_209`, and
    `AbsorptionContract`),
(3) zero-length extension rejection (`ext_zero_rejected`), `walk_bound_decoded ≤ 64` (`+ 1 ≤ 65`),
    and unconditional absence of section-6 jumps/calls (`panToTarget_noStubJump`,
    `panToTarget_user_noStubJump`, `FrontendSafe`, `PanLabSafe`, `PanTargetSafe`, `PanUserSafe`,
    `CompilerSafety`),
(4) the strictly increasing **56-budget** (and 54/52/50-budget) portfolio under Yukon
    (`900_719_925_474`) with conditional finite certificates lifted from `cert : CertificateAt 1_212_035_192`. -/
theorem grand_self_contained_witness_dag_memoization_and_fifty_six_budget_synth_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (ck l_ext ns nc : Nat) (h_nodedb : 4 * (ns + nc) ≤ maxInput)
    (cert : CertificateAt 1_212_035_192) :
    (HeapAllocationContract ∧ HeapNodesContract ∧ HeapRateContract ∧ MemoContract ∧
     BridgeContract ∧ AbsorptionContract ∧
     FrontendSafe ∧ PanLabSafe ∧ PanTargetSafe ∧ PanUserSafe ∧
     FiftySixShape ∧ FiftySixClaimPayloads ∧
     (∀ K ∈ fiftySixPortfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
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
      FiftyFourShape ∧ FiftyFourClaimPayloads ∧
      (∀ K ∈ fiftyFourPortfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
     (((∀ n : Nat, 1 ≤ n → compactLen n 0 = 2 * n - 2 ∧ compactLen n 1 = 2 * n - 1) ∧
       (∀ n odd : Nat, 1 ≤ n → odd ≤ 1 → (compactLen n odd = 0 ↔ n = 1 ∧ odd = 0)) ∧
       (compactLen 33 0 = 64 ∧ compactLen 32 1 = 63) ∧
       extAccepted 0 ck = false ∧
       (extAccepted l_ext 2 = false ∧ extAccepted l_ext 1 = false) ∧
       (∀ l' ck' : Nat, extAccepted l' ck' = true → 1 ≤ advance (.ext l')) ∧
       (∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
         ((l.map Step.ext).map advance).sum ≤ 64 → l.length ≤ 64 ∧ l.length + 1 ≤ 65) ∧
       (33806089496 - 2713714688) / 56 = 555220978 ∧
       ((List.range 7).foldl (fun a i => a + 16 ^ i) 0 = 17895697 ∧
         17895697 * 176 + 16 ^ 7 * 64 = 20329511856 ∧
         20329511856 ≤ 33806089496 - 2713714688) ∧
       33806089496 - 2713714688 < 16 ^ 8 * 64 ∧
       (17895697 + 16 ^ 7 = 286331153 ∧ 8 * 530 < 4300)) ∧
      ((∀ l : List Nat, (l.map buildTicks).sum ≤ buildTicks l.sum) ∧
       (buildTicks 2 + buildTicks 2 = 10 ∧ buildTicks 4 = 30) ∧
       2 * buildTicks 158_162 = 125_075_300_410 ∧
       (∀ L n u B blk : Nat, L ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
         40 * blk ≤ B * B → blk + 10 * L * n ≤ 100000000000) ∧
       (5_000 < 158_162 ∧ 5 * 156_088_992_805 < yukon) ∧
       CompilerSafety arch prog wc ac perf info j bd ptr f ∧
       FiftyShape ∧ SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth.FiftyClaimPayloads ∧
       (∀ K ∈ SelfContainedSubcallRevertAbsorptionAndFiftyBudgetSynth.fiftyPortfolio,
         InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
      ((∀ s ∈ StackToLab.compile sc dc mh sp off
           (compileNative ac perf (WordToWord.compile wc ac
             (panToWordCompileProgHOL arch prog)).2).2.2.2,
         IsStubLabel s.sectionId = true ∨ LOk s.lines) ∧
       (∀ (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
           (L' : List (Sec width)) (labs' : Spt (Spt Nat)),
         removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
           (compileNative ac perf (WordToWord.compile wc ac
             (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs') →
         (∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨ ∀ x ∈ s'.lines, JumpOk x = true) ∧
         (∀ s' ∈ L', IsStubLabel s'.sectionId = false → ∀ x ∈ s'.lines, JumpOk x = true)) ∧
       ((∀ n : Nat, 4 * n ≤ maxInput → n ≤ 33554428) ∧
         4 * 33554428 = maxInput ∧
         (2 * 33554428 + 2 ≤ 67108864 ∧ 33554432 < 2 * 33554428 + 2) ∧
         (∀ n c : Nat, 2 * n + 2 ≤ c → (n + 1) * 2 ≤ c) ∧
         (boundedBuild 8 33554428 = 536870848 ∧ boundedBuild 8 33554428 < yukon) ∧
         (boundedBuild 13421 33554428 < yukon ∧ yukon < boundedBuild 13422 33554428) ∧
         (∀ r ns' nc' : Nat, 4 * (ns' + nc') ≤ maxInput →
           boundedBuild r ns' + boundedBuild r nc' ≤ boundedBuild r 33554428)) ∧
       (FiftyTwoShape ∧ SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth.FiftyTwoClaimPayloads ∧
         (∀ K ∈ SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth.fiftyTwoPortfolio,
           InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
         (∀ l : List Nat, (l.map buildTicks).sum ≤ buildTicks l.sum) ∧
         (∀ j' : List Bool, j'.length ≤ 524288 →
           _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.restoreDels j' ≤ 524288) ∧
         (∀ u1 u2 t1 t2 : Nat, u1 + u2 ≤ 2000000 → t1 ≤ 373022 * u1 →
           t2 ≤ 373022 * u2 → t1 + t2 ≤ 746044000000) ∧
         (∀ L n u B blk : Nat, L ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
           40 * blk ≤ B * B → blk + 10 * L * n ≤ 100000000000) ∧
         KeyCap ∧ PackingAndBuild ∧ BlockCosts ∧ OneSlopeMargin ∧ TransientObstruction ∧ RemainingTables)))) :=
  ⟨integrated_master_non_vacuous_and_tight cert,
   grand_self_contained_mpt_nodedb_transient_and_fifty_four_budget_synth_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off info j bd ptr f ck l_ext ns nc h_nodedb cert⟩

#print axioms witness_dag_memoization_and_heap_floors_rates_non_vacuous_and_tight
#print axioms mpt_nodedb_transient_bridge_and_absorption_synthesis_non_vacuous_and_tight
#print axioms extension_zero_rejected_walk_bound_and_dag_memoization_non_vacuous_and_tight
#print axioms witness_dag_nodedb_capacity_and_mpt_bridge_synthesis_non_vacuous_and_tight
#print axioms transient_superadditivity_coupled_journal_and_joint_bridge_non_vacuous_and_tight
#print axioms unconditional_pan_to_target_no_stub_jump_and_compiler_safety_non_vacuous_and_tight
#print axioms witness_dag_decode_mpt_bridge_and_pan_to_target_no_stub_jump_non_vacuous_and_tight
#print axioms fifty_four_and_fifty_six_budget_portfolios_and_payloads_non_vacuous_and_tight
#print axioms fifty_six_budget_explicit_certificates_and_integrated_master_non_vacuous_and_tight
#print axioms grand_self_contained_witness_dag_memoization_and_fifty_six_budget_synth_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedWitnessDagMemoizationAndFiftySixBudgetSynth
