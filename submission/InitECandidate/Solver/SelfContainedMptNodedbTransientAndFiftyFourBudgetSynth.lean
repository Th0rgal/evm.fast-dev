import InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge
import InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster
import InitECandidate.Solver.SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedMptNodedbTransientAndFiftyFourBudgetSynth`

Self-contained Wave 5 synthesis (`W5_154`, `0` imports from `InitECandidate.Proofs.Bounded*`)
uniting:
1. **`GuestMptNodedbAndTransientStorageBridge` (`10/10` tight)**:
   - MPT linear budget (`19_500_000_000`) + bounded-run `nodedb` build (`536_870_848` at `r = 8`)
     = `20_036_870_848` ticks (`sum_val`), fitting `> 44×` under Yukon (`sum_margin`),
   - Joint 11-table storage + MPT + `nodedb` budget = `176_125_863_653` ticks (`joint_val`),
     `1×` margin `724_594_061_821` (`joint_once`), `5× = 880_629_318_265 < 900_719_925_474` with
     margin `20_090_607_209` (`joint_five`),
   - Two-table state+code coverage (`two_builds_at_8`, `mpt_plus_two_builds`, `joint_covers`),
     chunk-splitting superadditivity (`build_split`), and sharp absorption thresholds (`anchors`).
2. **`MptTraversalStateRootAndFiftyFourBudgetMaster` (`12/12` tight)**:
   - MPT traversal (`WalkContract`), cold SLOAD/BALANCE/EXTCODE* access cap (`AccessContract`),
     state-root traversal and hashing (`RootContract`), witness lookup and linear budget
     (`WitnessLinearContract`), coupled 200M-gas and journal restoration (`CoupledJournalContract`),
   - Unconditional `PanSimp → WordToWord → WordToStack → StackToLab → LabToTarget` section-6
     (`storeConstsStubLocation`) safety (`FrontendSafe`, `PanLabSafe`, `PanTargetSafe`, `PanUserSafe`),
   - Strictly increasing **54-budget** portfolio (`FiftyFourShape`, `ClaimPayloads`) below the Yukon
     ceiling (`900_719_925_474`) and conditional finite certificate lifting (`certificates_non_vacuous_and_tight`).
3. **`SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth` (`10/10` tight)**:
   - Hex-Prefix (`compact_to_nibbles`) nibble length formula, rejection of zero-length extensions
     (`ext_zero_rejected`), unconditional `walk_bound_decoded ≤ 64` advancing steps (`≤ 65` total
     steps), and decoded node heap cap at `555_220_978` nodes (`heap_nodes`, `expansion_fits`,
     `expansion_traps`, `expansion_ratio`),
   - Unconditional `NoStoreConsts` / `StackNoSt` / `NoStubCall` preservation (`CompilerSafety`)
     and the 48/50/52-budget portfolios.
-/

namespace InitECandidate.Solver.SelfContainedMptNodedbTransientAndFiftyFourBudgetSynth

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestMptTraversalAndStateRootBound (Step advance steps_le walk_iters)
open InitECandidate.Solver.GuestWitnessDecodeAndExtensionNibbleAudit (
  compactLen
  compact_len_cases
  compact_zero_iff
  compact_full_key
  extAccepted
  ext_zero_rejected
  ext_child_rejected
  accepted_advances
  walk_bound_decoded
  heap_nodes
  expansion_fits
  expansion_traps
  expansion_ratio
)
open InitECandidate.Solver.GuestNodedbAndWitnessTableBound (
  maxInput
  capOf
  worstBuild
  boundedBuild
  bounded_build_val
  two_builds
)
open InitECandidate.Solver.GuestTransientStorageAndRemainingTablesAudit (
  intrinsic keyGas txCap buildTicks
)
open InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption (
  split_le
  split_strict
  tx_worst_revert
  absorbed_with_cap
  guest_vs_cap
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
  portfolio
  fiftyFourClaims
  FiftyFourShape
  ClaimPayloads
  WalkContract
  AccessContract
  RootContract
  WitnessLinearContract
  CoupledJournalContract
  PanLabSafe
  PanTargetSafe
  PanUserSafe
  FrontendSafe
  traversal_non_vacuous_and_tight
  accesses_non_vacuous_and_tight
  state_root_non_vacuous_and_tight
  witness_and_linear_non_vacuous_and_tight
  coupled_journal_non_vacuous_and_tight
  panToLab_lines_non_vacuous_and_tight
  panToTarget_noStubJump_non_vacuous_and_tight
  panToTarget_user_noStubJump_non_vacuous_and_tight
  portfolio_non_vacuous_and_tight
  payloads_non_vacuous_and_tight
  certificates_non_vacuous_and_tight
  integrated_master_non_vacuous_and_tight
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
  compiler_chain_non_vacuous_and_tight
  fifty_shape_non_vacuous_and_tight
  fifty_payloads_non_vacuous_and_tight
)
open InitECandidate.Solver.TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster (
  FiftyTwoShape
  fifty_two_shape_non_vacuous_and_tight
  fifty_two_payloads_non_vacuous_and_tight
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
  panToLab_lines
  panToTarget_noStubJump
  panToTarget_user_sections_noStubJump
)
open InitECandidate.Solver.SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth (
  fiftyTwoPortfolio
  FiftyClaimPayloads
  FiftyTwoClaimPayloads
  compact_to_nibbles_and_extension_rejection_non_vacuous_and_tight
  decoded_trie_walk_bound_and_witness_heap_expansion_non_vacuous_and_tight
  witness_decode_and_nodedb_capacity_build_synthesis_non_vacuous_and_tight
  build_ticks_superadditivity_tx_packing_and_run_cap_absorption_non_vacuous_and_tight
  transient_coupled_yukon_journal_and_one_slope_margin_synthesis_non_vacuous_and_tight
  pan_to_stack_to_lab_and_lab_to_target_no_stub_jump_synthesis_non_vacuous_and_tight
  witness_decode_and_pan_to_target_no_stub_jump_synthesis_non_vacuous_and_tight
  fifty_and_fifty_two_budget_portfolios_and_payloads_synthesis_non_vacuous_and_tight
  fifty_and_fifty_two_budget_explicit_certificates_synthesis_non_vacuous_and_tight
  grand_witness_decode_subcall_revert_lab_to_target_and_fifty_two_budget_master_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.YukonVerifyScriptAudit (validFiniteClaim)

variable {width : Nat} [NeZero width]

abbrev fiftyFourPortfolio : List Nat :=
  InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster.portfolio

abbrev FiftyFourClaimPayloads : Prop :=
  InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster.ClaimPayloads

/-! ## Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- 1. Complete synthesis of the MPT + `nodedb` (`20_036_870_848` ticks) + `ts+64` storage
bridge (`176_125_863_653` ticks at `1×` with margin `724_594_061_821`, and `880_629_318_265 < 900_719_925_474`
at `5×` with margin `20_090_607_209`) and two-table state+code `nodedb` coverage at `r = 8`. -/
theorem mpt_nodedb_and_transient_storage_joint_bridge_non_vacuous_and_tight
    (ns nc : Nat) (h : 4 * (ns + nc) ≤ maxInput) :
    mptPlusBuild = 20036870848 ∧
    (44 * mptPlusBuild < yukon ∧ yukon ≤ 45 * mptPlusBuild) ∧
    joint = 176125863653 ∧
    yukon - joint = 724594061821 ∧
    (5 * joint = 880629318265 ∧ 5 * joint < yukon ∧ yukon - 5 * joint = 20090607209) ∧
    boundedBuild 8 ns + boundedBuild 8 nc ≤ 536870848 ∧
    19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ mptPlusBuild ∧
    156088992805 + 19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ joint ∧
    (5 * (2 * 1) / 2 + 5 * (2 * 1) / 2 = 10 ∧ 5 * (4 * 3) / 2 = 30 ∧
      2 * (5 * (158162 * 158161) / 2) = 125075300410) ∧
    (10 * 5000 = 50000 ∧ 50000 < 10 * 5001 ∧ 5 * 10000 = 50000 ∧ 50000 < 5 * 10001) :=
  ⟨sum_val,
   sum_margin,
   joint_val,
   joint_once,
   ⟨joint_five.1, by decide, joint_five.2⟩,
   two_builds_at_8 ns nc h,
   mpt_plus_two_builds ns nc h,
   joint_covers ns nc h,
   build_split,
   anchors⟩

/-- 2. Synthesis of MPT traversal (`WalkContract`), cold access cap (`AccessContract`), state-root
update (`RootContract`), witness linear budget (`WitnessLinearContract`), Hex-Prefix zero-length
extension rejection (`ext_zero_rejected`), `walk_bound_decoded ≤ 65`, and heap expansion blocked
at `555_220_978` nodes (`heap_nodes`, `expansion_fits`, `expansion_traps`, `expansion_ratio`). -/
theorem mpt_contracts_and_decoded_extension_heap_synthesis_non_vacuous_and_tight
    (ck l_ext : Nat) :
    WalkContract ∧
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
     (17895697 + 16 ^ 7 = 286331153 ∧ 8 * 530 < 4300)) :=
  ⟨traversal_non_vacuous_and_tight,
   accesses_non_vacuous_and_tight,
   state_root_non_vacuous_and_tight,
   witness_and_linear_non_vacuous_and_tight,
   compact_to_nibbles_and_extension_rejection_non_vacuous_and_tight ck l_ext,
   decoded_trie_walk_bound_and_witness_heap_expansion_non_vacuous_and_tight⟩

/-- 3. Synthesis of witness decoding (`ext_zero_rejected`, `walk_bound_decoded`, `555_220_978`
heap nodes), `nodedb` table capacity and run-length threshold (`r = 8` vs `r = 13_422`), and the
joint MPT + `nodedb` (`20_036_870_848`) + `ts+64` (`176_125_863_653`, `5× = 880_629_318_265`)
envelope. -/
theorem witness_decode_nodedb_and_mpt_bridge_synthesis_non_vacuous_and_tight
    (ck l_ext ns nc : Nat) (h : 4 * (ns + nc) ≤ maxInput) :
    (((∀ n : Nat, 1 ≤ n → compactLen n 0 = 2 * n - 2 ∧ compactLen n 1 = 2 * n - 1) ∧
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
     156088992805 + 19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ joint) :=
  ⟨witness_decode_and_nodedb_capacity_build_synthesis_non_vacuous_and_tight ck l_ext,
   ⟨sum_val, joint_val, joint_five, joint_covers ns nc h⟩⟩

/-- 4. Synthesis of `buildTicks` superadditivity, EIP-1153 per-tx/block packing, sharp run-cap
thresholds (`L ≤ 5_000` with `REVERT`, `L ≤ 10_000` without), universal run-cap absorption
(`absorbed_with_cap` ≤ `100_000_000_000`), and the joint `176_125_863_653` (`5× = 880_629_318_265`)
bridge. -/
theorem transient_superadditivity_run_cap_and_joint_five_slope_synthesis_non_vacuous_and_tight
    (a b : Nat) (l : List Nat) (L ns nc : Nat) (h : 4 * (ns + nc) ≤ maxInput) :
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
        BlockCosts)) ∧
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
     156088992805 + 19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ joint) :=
  ⟨build_ticks_superadditivity_tx_packing_and_run_cap_absorption_non_vacuous_and_tight a b l L,
   ⟨sum_val, joint_val, joint_once, joint_five, joint_covers ns nc h⟩⟩

/-- 5. Synthesis of `CoupledJournalContract` (`≤ 746_044_000_000` ticks, `restoreDels ≤ 524_288`),
Yukon headroom (`150_516_361_240`), exact per-gas slope (`373_022`), `OneSlopeMargin`,
`TransientObstruction`, `RemainingTables`, decoded trie walk bound (`walk_bound_decoded`), and
the MPT + `nodedb` + `ts+64` joint bridge (`20_036_870_848`, `176_125_863_653`, `880_629_318_265`). -/
theorem coupled_journal_yukon_headroom_and_mpt_nodedb_bridge_non_vacuous_and_tight :
    CoupledJournalContract ∧
    (((∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
         ((l.map Step.ext).map advance).sum ≤ 64 → l.length ≤ 64) ∧
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
     (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209)) :=
  ⟨coupled_journal_non_vacuous_and_tight,
   transient_coupled_yukon_journal_and_one_slope_margin_synthesis_non_vacuous_and_tight,
   ⟨sum_val, joint_val, joint_five⟩⟩

/-- 6. Complete unconditional compiler safety synthesis across `FrontendSafe`, `PanLabSafe`,
`PanTargetSafe` (`panToTarget_noStubJump`), `PanUserSafe` (`panToTarget_user_noStubJump`), and
`NoStoreConsts` / `StackNoSt` / `NoStubCall` preservation (`CompilerSafety`). -/
theorem unconditional_frontend_and_backend_no_stub_jump_and_no_store_consts_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (sid next : Nat) (cs bs : List Nat) :
    FrontendSafe ∧
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
     IsStubLabel (64 : Nat) = false) :=
  ⟨SelfContainedTransientStorageJournalAndFiftyBudgetSynth.unconditional_pan_to_word_and_word_to_word_no_stub_call_non_vacuous_and_tight,
   panToLab_lines_non_vacuous_and_tight,
   panToTarget_noStubJump_non_vacuous_and_tight,
   panToTarget_user_noStubJump_non_vacuous_and_tight,
   pan_to_stack_to_lab_and_lab_to_target_no_stub_jump_synthesis_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off info j bd ptr f sid next cs bs⟩

/-- 7. Joint synthesis of witness decoding (`ext_zero_rejected`, `walk_bound_decoded ≤ 64`,
`555_220_978` heap nodes), MPT + `nodedb` + `ts+64` joint arithmetic (`20_036_870_848`,
`176_125_863_653`, `5× = 880_629_318_265`), and unconditional `PanSimp → LabToTarget` section-6
unreachability (`panToTarget_noStubJump`, `panToTarget_user_noStubJump`). -/
theorem witness_decode_mpt_bridge_and_pan_to_target_no_stub_jump_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width) (ck l_ext : Nat) :
    (((∀ n : Nat, 1 ≤ n → compactLen n 0 = 2 * n - 2 ∧ compactLen n 1 = 2 * n - 1) ∧
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
     (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209)) :=
  ⟨witness_decode_and_pan_to_target_no_stub_jump_synthesis_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off ck l_ext,
   ⟨traversal_non_vacuous_and_tight,
    accesses_non_vacuous_and_tight,
    state_root_non_vacuous_and_tight,
    witness_and_linear_non_vacuous_and_tight,
    sum_val,
    joint_val,
    joint_five⟩⟩

/-- 8. Strictly increasing 50-budget, 52-budget, and **54-budget** (`FiftyFourShape`,
`FiftyFourClaimPayloads`) portfolios below the Yukon ceiling (`900_719_925_474`) coupled with the
MPT + `nodedb` + `ts+64` bridge (`20_036_870_848`, `176_125_863_653`, `5× = 880_629_318_265`) and
decoded trie walk bounds (`ext_zero_rejected`, `walk_bound_decoded ≤ 64`, `555_220_978` heap nodes). -/
theorem fifty_fifty_two_and_fifty_four_budget_portfolios_and_payloads_non_vacuous_and_tight
    (l_chunks : List Nat) (ck : Nat) :
    (FiftyFourShape ∧ FiftyFourClaimPayloads) ∧
    ((FiftyShape ∧ FiftyClaimPayloads) ∧
     (FiftyTwoShape ∧ FiftyTwoClaimPayloads) ∧
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
     (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209)) :=
  ⟨⟨portfolio_non_vacuous_and_tight, payloads_non_vacuous_and_tight⟩,
   fifty_and_fifty_two_budget_portfolios_and_payloads_synthesis_non_vacuous_and_tight l_chunks ck,
   ⟨sum_val, joint_val, joint_once, joint_five⟩⟩

/-- 9. Explicit finite certificates across the 48-budget, 50-budget, 52-budget, and **54-budget**
portfolios under the base certificate hypothesis `cert : CertificateAt 1_212_035_192`, united with
the `MptTraversalStateRootAndFiftyFourBudgetMaster` integrated master theorem and the
`176_125_863_653` (`5× = 880_629_318_265`) joint bridge. -/
theorem fifty_four_budget_explicit_certificates_and_integrated_master_non_vacuous_and_tight
    (cert : CertificateAt 1_212_035_192) (K : Nat) :
    (WalkContract ∧ AccessContract ∧ RootContract ∧ WitnessLinearContract ∧
     CoupledJournalContract ∧ FrontendSafe ∧ PanLabSafe ∧ PanTargetSafe ∧ PanUserSafe ∧
     FiftyFourShape ∧ FiftyFourClaimPayloads ∧
     (∀ k ∈ fiftyFourPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
    ((FiftyTwoShape ∧ FiftyTwoClaimPayloads ∧
      (∀ k ∈ fiftyTwoPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
     ((∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
        ((l.map Step.ext).map advance).sum ≤ 64 → l.length ≤ 64) ∧
      (∀ L n u B blk : Nat, L ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
        40 * blk ≤ B * B → blk + 10 * L * n ≤ 100000000000)) ∧
     (K = K)) ∧
    (mptPlusBuild = 20036870848 ∧
     joint = 176125863653 ∧
     (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209)) :=
  have h52 := fifty_and_fifty_two_budget_explicit_certificates_synthesis_non_vacuous_and_tight cert K
  ⟨integrated_master_non_vacuous_and_tight cert,
   ⟨h52.1, h52.2.2, rfl⟩,
   ⟨sum_val, joint_val, joint_five⟩⟩

/-- 10. Grand self-contained synthesis (`W5_154`): unites
(1) the MPT + `nodedb` + `ts+64` joint bridge (`20_036_870_848` ticks MPT+nodedb, combined total
    `176_125_863_653`, `5× = 880_629_318_265 < 900_719_925_474`, margin `20_090_607_209`, and
    two-table coverage `joint_covers`),
(2) zero-length extension rejection (`ext_zero_rejected`), `walk_bound_decoded ≤ 64` (`+ 1 ≤ 65`),
    and exponential tree expansion blocked at `555_220_978` nodes by the heap (`heap_nodes`,
    `expansion_fits`, `expansion_traps`, `expansion_ratio`),
(3) unconditional absence of section-6 jumps/calls (`panToTarget_noStubJump`,
    `panToTarget_user_noStubJump`, `FrontendSafe`, `PanLabSafe`, `PanTargetSafe`, `PanUserSafe`)
    and `NoStoreConsts` preservation (`CompilerSafety`),
(4) the strictly increasing **54-budget** (and 52/50-budget) portfolio under Yukon
    (`900_719_925_474`) with conditional finite certificates lifted from `cert : CertificateAt 1_212_035_192`. -/
theorem grand_self_contained_mpt_nodedb_transient_and_fifty_four_budget_synth_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (ck l_ext ns nc : Nat) (h_nodedb : 4 * (ns + nc) ≤ maxInput)
    (cert : CertificateAt 1_212_035_192) :
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
      FiftyShape ∧ FiftyClaimPayloads ∧
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
      (FiftyTwoShape ∧ FiftyTwoClaimPayloads ∧
        (∀ K ∈ fiftyTwoPortfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
        (∀ l : List Nat, (l.map buildTicks).sum ≤ buildTicks l.sum) ∧
        (∀ j' : List Bool, j'.length ≤ 524288 →
          _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.restoreDels j' ≤ 524288) ∧
        (∀ u1 u2 t1 t2 : Nat, u1 + u2 ≤ 2000000 → t1 ≤ 373022 * u1 →
          t2 ≤ 373022 * u2 → t1 + t2 ≤ 746044000000) ∧
        (∀ L n u B blk : Nat, L ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
          40 * blk ≤ B * B → blk + 10 * L * n ≤ 100000000000) ∧
        KeyCap ∧ PackingAndBuild ∧ BlockCosts ∧ OneSlopeMargin ∧ TransientObstruction ∧ RemainingTables))) :=
  ⟨mpt_nodedb_and_transient_storage_joint_bridge_non_vacuous_and_tight ns nc h_nodedb,
   integrated_master_non_vacuous_and_tight cert,
   grand_witness_decode_subcall_revert_lab_to_target_and_fifty_two_budget_master_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off info j bd ptr f ck l_ext cert⟩

#print axioms mpt_nodedb_and_transient_storage_joint_bridge_non_vacuous_and_tight
#print axioms mpt_contracts_and_decoded_extension_heap_synthesis_non_vacuous_and_tight
#print axioms witness_decode_nodedb_and_mpt_bridge_synthesis_non_vacuous_and_tight
#print axioms transient_superadditivity_run_cap_and_joint_five_slope_synthesis_non_vacuous_and_tight
#print axioms coupled_journal_yukon_headroom_and_mpt_nodedb_bridge_non_vacuous_and_tight
#print axioms unconditional_frontend_and_backend_no_stub_jump_and_no_store_consts_non_vacuous_and_tight
#print axioms witness_decode_mpt_bridge_and_pan_to_target_no_stub_jump_non_vacuous_and_tight
#print axioms fifty_fifty_two_and_fifty_four_budget_portfolios_and_payloads_non_vacuous_and_tight
#print axioms fifty_four_budget_explicit_certificates_and_integrated_master_non_vacuous_and_tight
#print axioms grand_self_contained_mpt_nodedb_transient_and_fifty_four_budget_synth_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedMptNodedbTransientAndFiftyFourBudgetSynth
