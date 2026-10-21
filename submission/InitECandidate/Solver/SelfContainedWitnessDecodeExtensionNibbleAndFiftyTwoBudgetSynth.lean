import InitECandidate.Solver.GuestWitnessDecodeAndExtensionNibbleAudit
import InitECandidate.Solver.SelfContainedSubcallRevertAbsorptionAndFiftyBudgetSynth
import InitECandidate.Solver.SelfContainedLabToTargetNoStubJumpAndFiftyTwoBudgetSynth

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth`

Self-contained Wave 5 synthesis (`W5_151`, `0` imports from `InitECandidate.Proofs.Bounded*`)
uniting:
1. **`GuestWitnessDecodeAndExtensionNibbleAudit` (`11/11` tight)**:
   - Hex-Prefix (`compact_to_nibbles`) nibble length formula and zero-length characterization
     (`compact_len_cases`, `compact_zero_iff`, `compact_full_key`),
   - Rejection of zero-length extensions (`ext_zero_rejected`, `ext_child_rejected`), positive step
     advance (`accepted_advances`), and unconditional `≤ 64` advancing steps (`≤ 65` total steps)
     on any decoded trie (`walk_bound_decoded`),
   - Decoded node heap capacity and tree-expansion bounds (`heap_nodes`, `expansion_fits`,
     `expansion_traps`, `expansion_ratio`).
2. **`SelfContainedSubcallRevertAbsorptionAndFiftyBudgetSynth` (`10/10` tight)**:
   - `buildTicks` superadditivity (`q_super`, `build_super`, `split_le`, `split_strict`), worst-case
     per-transaction revert (`tx_worst_revert`, `half_split`), sharp run-cap thresholds
     (`lmax_revert`, `lmax_norevert`, `lmax_sharp`), and universal run-cap absorption
     (`absorbed_with_cap`, `guest_vs_cap`),
   - Unconditional `PanSimp` → `StackToLab` safety (`CompilerSafety`, `StackNoSt`, `NoStubCall`,
     `FlattenVisitsSt = false`) and the 48-budget / 50-budget portfolios.
3. **`SelfContainedLabToTargetNoStubJumpAndFiftyTwoBudgetSynth` (`10/10` tight)**:
   - Unconditional `PanSimp` → `WordToWord` → `WordToStack` → `StackToLab` → `LabToTarget`
     section-6 (`storeConstsStubLocation`) unreachability (`panToLab_lines`,
     `panToTarget_noStubJump`, `panToTarget_user_noStubJump`),
   - `nodedb` capacity/build thresholds, `ts+64` coupled 200M-gas and journal bounds, and the
     strictly increasing **52-budget** portfolio under the Yukon ceiling (`900_719_925_474`) with
     explicit finite certificates under the base certificate hypothesis.
-/

namespace InitECandidate.Solver.SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestMptTraversalAndStateRootBound (Step advance steps_le)
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
open InitECandidate.Solver.WordToWordNoStubCall (
  NSC
  panToWordToWord_NoStubCall
  panToStackNames_NoSt_and_NoStubCall_unconditional
)
open InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (WordNoStubCall NoStubCall)
open InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts (FlattenVisitsSt)
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
  jumpOk_rejects_stub
  jumpOk_accepts_user
)
open InitECandidate.Solver.GuestNodedbAndWitnessTableBound (
  maxInput
  capOf
  worstBuild
  boundedBuild
  entries_le
  entries_tight
  cap_extreme
  load_half
  cap_small
  worst_build_val
  bounded_build_val
  run_threshold
  bounded_mono
  grind_cost
  two_builds
)
open InitECandidate.Solver.GuestTransientStorageAndRemainingTablesAudit (
  intrinsic keyGas txCap buildTicks
)
open InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption (
  q_super
  build_super
  split_le
  split_strict
  tx_worst_revert
  half_split
  lmax_revert
  lmax_norevert
  lmax_sharp
  absorbed_with_cap
  guest_vs_cap
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
  key_cap_non_vacuous_and_tight
  packing_and_tx_build_non_vacuous_and_tight
  capped_build_non_vacuous_and_tight
  block_and_revert_non_vacuous_and_tight
  one_slope_margin_non_vacuous_and_tight
  transient_obstruction_non_vacuous_and_tight
  compiler_chain_non_vacuous_and_tight
  fifty_shape_non_vacuous_and_tight
  fifty_payloads_non_vacuous_and_tight
  fifty_certificates_non_vacuous_and_tight
)
open InitECandidate.Solver.TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster (
  FiftyTwoShape
  fifty_two_shape_non_vacuous_and_tight
  fifty_two_payloads_non_vacuous_and_tight
  integrated_master_non_vacuous_and_tight
)
open InitECandidate.Solver.SelfContainedSubcallRevertAbsorptionAndFiftyBudgetSynth (
  fiftyPortfolio
  fortyEightPortfolio
  subcall_revert_superadditivity_and_tx_block_packing_synthesis_non_vacuous_and_tight
  exact_absorption_thresholds_run_cap_and_one_slope_margin_synthesis_non_vacuous_and_tight
  unconditional_pan_to_stack_to_lab_no_store_consts_and_no_stub_call_synthesis_non_vacuous_and_tight
  fifty_and_forty_eight_budget_portfolios_certificates_and_claims_synthesis_non_vacuous_and_tight
)
open InitECandidate.Solver.SelfContainedLabToTargetNoStubJumpAndFiftyTwoBudgetSynth (
  stack_and_flatten_invariants_non_vacuous_and_tight
  panToLab_lines_non_vacuous_and_tight
  panToTarget_noStubJump_non_vacuous_and_tight
  panToTarget_user_noStubJump_non_vacuous_and_tight
  nodedb_entries_and_capacity_non_vacuous_and_tight
  nodedb_build_and_two_builds_non_vacuous_and_tight
  transient_split_revert_and_cap_absorption_non_vacuous_and_tight
  transient_coupled_yukon_journal_and_slope_non_vacuous_and_tight
  fifty_two_portfolio_and_payloads_non_vacuous_and_tight
  self_contained_lab_to_target_nodedb_and_fifty_two_budget_master_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.YukonVerifyScriptAudit (validFiniteClaim)
open _root_.InitECandidate.Solver.SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth (fortyEightSharedClaims)
open _root_.InitECandidate.Solver.SelfContainedElevenTablesAndSharedAbsorptionSynth (
  elevenTablesSharedSlope3UnrolledK
  elevenTablesSharedSlope3K
  elevenTablesSharedSlope5UnrolledK
  elevenTablesSharedSlope5K
  elevenTablesSlope3UnrolledK
  elevenTablesSlope3K
  elevenTablesSlope5UnrolledK
  elevenTablesSlope5K
  fortyFourSortedPortfolio
  fortyEightSharedPortfolio
  fortyEightElevenTablesPortfolio
)

variable {width : Nat} [NeZero width]

abbrev fiftyTwoPortfolio : List Nat :=
  InitECandidate.Solver.TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster.portfolio

abbrev FiftyClaimPayloads : Prop :=
  InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.ClaimPayloads

abbrev FiftyTwoClaimPayloads : Prop :=
  InitECandidate.Solver.TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster.ClaimPayloads

/-! ## Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- 1. Hex-Prefix (`compact_to_nibbles`) nibble length characterization (`compact_len_cases`,
`compact_zero_iff`, `compact_full_key`) and decoder extension validation (`ext_zero_rejected`,
`ext_child_rejected`, `accepted_advances`) with tightness witnesses. -/
theorem compact_to_nibbles_and_extension_rejection_non_vacuous_and_tight (ck l : Nat) :
    (∀ n : Nat, 1 ≤ n → compactLen n 0 = 2 * n - 2 ∧ compactLen n 1 = 2 * n - 1) ∧
    (∀ n odd : Nat, 1 ≤ n → odd ≤ 1 → (compactLen n odd = 0 ↔ n = 1 ∧ odd = 0)) ∧
    (compactLen 1 0 = 0 ∧ compactLen 1 1 = 1 ∧ compactLen 33 0 = 64 ∧ compactLen 32 1 = 63) ∧
    extAccepted 0 ck = false ∧
    (extAccepted l 2 = false ∧ extAccepted l 1 = false) ∧
    (∀ l' ck' : Nat, extAccepted l' ck' = true → 1 ≤ advance (.ext l')) ∧
    (extAccepted 1 3 = true ∧ extAccepted 1 0 = true ∧ advance (.ext 1) = 1) :=
  ⟨compact_len_cases,
   compact_zero_iff,
   ⟨by decide, by decide, compact_full_key.1, compact_full_key.2⟩,
   ext_zero_rejected ck,
   ext_child_rejected l,
   accepted_advances,
   by decide⟩

/-- 2. Unconditional `trie_walk` step bound on any decoded trie (`walk_bound_decoded`: `≤ 64`
advancing steps, hence `≤ 65` total iterations including a terminal leaf/miss step) coupled with
decoded node heap capacity and witness expansion bounds (`heap_nodes`, `expansion_fits`,
`expansion_traps`, `expansion_ratio`). -/
theorem decoded_trie_walk_bound_and_witness_heap_expansion_non_vacuous_and_tight :
    (∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
      ((l.map Step.ext).map advance).sum ≤ 64 → l.length ≤ 64 ∧ l.length + 1 ≤ 65) ∧
    (∀ l ck : Nat, extAccepted l ck = true → 1 ≤ advance (.ext l)) ∧
    ((List.replicate 64 1).length = 64 ∧
      (((List.replicate 64 1).map Step.ext).map advance).sum = 64) ∧
    (33806089496 - 2713714688) / 56 = 555220978 ∧
    ((List.range 7).foldl (fun a i => a + 16 ^ i) 0 = 17895697 ∧
      17895697 * 176 + 16 ^ 7 * 64 = 20329511856 ∧
      20329511856 ≤ 33806089496 - 2713714688) ∧
    33806089496 - 2713714688 < 16 ^ 8 * 64 ∧
    (17895697 + 16 ^ 7 = 286331153 ∧ 8 * 530 < 4300) :=
  ⟨fun l hacc hsum =>
     have hlen := walk_bound_decoded l hacc hsum
     ⟨hlen, Nat.add_le_add_right hlen 1⟩,
   accepted_advances,
   by decide,
   heap_nodes,
   expansion_fits,
   expansion_traps,
   expansion_ratio⟩

/-- 3. Complete synthesis of `guest.pp.pnk` witness decoding (`compact_len_cases`,
`compact_zero_iff`, `ext_zero_rejected`, `walk_bound_decoded`, `heap_nodes`, `expansion_fits`,
`expansion_traps`, `expansion_ratio`) and `nodedb` table capacity, run-length threshold, and
two-table state+code build bounds (`nodedb_entries_and_capacity_non_vacuous_and_tight`,
`nodedb_build_and_two_builds_non_vacuous_and_tight`). -/
theorem witness_decode_and_nodedb_capacity_build_synthesis_non_vacuous_and_tight (ck l_ext : Nat) :
    ((∀ n : Nat, 1 ≤ n → compactLen n 0 = 2 * n - 2 ∧ compactLen n 1 = 2 * n - 1) ∧
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
     (∀ r ns nc : Nat, 4 * (ns + nc) ≤ maxInput →
       boundedBuild r ns + boundedBuild r nc ≤ boundedBuild r 33554428)) :=
  ⟨⟨compact_len_cases,
    compact_zero_iff,
    compact_full_key,
    ext_zero_rejected ck,
    ext_child_rejected l_ext,
    accepted_advances,
    walk_bound_decoded,
    heap_nodes,
    expansion_fits,
    expansion_traps,
    expansion_ratio⟩,
   nodedb_entries_and_capacity_non_vacuous_and_tight,
   nodedb_build_and_two_builds_non_vacuous_and_tight⟩

/-- 4. Synthesis of `buildTicks` superadditivity (`q_super`, `build_super`, `split_le`,
`split_strict`), worst-case per-tx revert (`tx_worst_revert`, `half_split`), EIP-1153 key cap and
block packing (`KeyCap`, `PackingAndBuild`, `capped_build_non_vacuous_and_tight`, `BlockCosts`),
sharp run-cap thresholds (`lmax_revert`, `lmax_norevert`, `lmax_sharp`), and universal run-cap
absorption (`absorbed_with_cap` ≤ `100_000_000_000` ticks). -/
theorem build_ticks_superadditivity_tx_packing_and_run_cap_absorption_non_vacuous_and_tight
    (a b : Nat) (l : List Nat) (L : Nat) :
    (((a * (a - 1) + b * (b - 1) ≤ (a + b) * (a + b - 1) ∧
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
       5 * 156088992805 < yukon ∧ yukon < 6 * 156088992805 ∧ 5000 < 158162)) :=
  ⟨subcall_revert_superadditivity_and_tx_block_packing_synthesis_non_vacuous_and_tight a b l,
   transient_split_revert_and_cap_absorption_non_vacuous_and_tight l L⟩

/-- 5. Synthesis of shared 200M-gas convex coupling (`≤ 746_044_000_000` ticks), Yukon headroom
(`150_516_361_240` ticks), journal restoration (`restoreDels` ≤ `524_288`), exact per-gas slope
(`373_022`), `OneSlopeMargin`, `TransientObstruction`, `RemainingTables`, and decoded trie walk
bound (`walk_bound_decoded`). -/
theorem transient_coupled_yukon_journal_and_one_slope_margin_synthesis_non_vacuous_and_tight :
    ((∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
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
     (KeyCap ∧ PackingAndBuild ∧ BlockCosts ∧ OneSlopeMargin ∧ TransientObstruction ∧ RemainingTables)) :=
  ⟨⟨walk_bound_decoded, by decide⟩,
   transient_coupled_yukon_journal_and_slope_non_vacuous_and_tight⟩

/-- 6. Complete unconditional compiler safety synthesis from `PanSimp` through `WordToWord`,
`WordToStack`, `StackToLab`, and `LabToTarget` (`CompilerSafety`, `panToLab_lines`,
`panToTarget_noStubJump`, `panToTarget_user_sections_noStubJump`, and `JC`/`JumpOk` tightness
witnesses). -/
theorem pan_to_stack_to_lab_and_lab_to_target_no_stub_jump_synthesis_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (sid next : Nat) (cs bs : List Nat) :
    CompilerSafety arch prog wc ac perf info j bd ptr f ∧
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
    IsStubLabel (64 : Nat) = false :=
  ⟨compiler_chain_non_vacuous_and_tight arch prog wc ac perf info j bd ptr f,
   stack_and_flatten_invariants_non_vacuous_and_tight f sid next cs bs,
   panToLab_lines arch prog wc ac perf sc dc mh sp off,
   fun ic pos labs ffis L' labs' h =>
     ⟨panToTarget_noStubJump arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h,
      fun s' hs hu =>
        panToTarget_user_sections_noStubJump arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h s' hs hu⟩,
   by decide,
   by decide⟩

/-- 7. Joint synthesis of Hex-Prefix witness decoding (`compact_len_cases`, `compact_zero_iff`,
`ext_zero_rejected`, `accepted_advances`, `walk_bound_decoded`, `heap_nodes`, `expansion_fits`,
`expansion_traps`, `expansion_ratio`) and the unconditional `PanSimp → LabToTarget` section-6
unreachability chain (`panToLab_lines`, `panToTarget_noStubJump`, `panToTarget_user_noStubJump`). -/
theorem witness_decode_and_pan_to_target_no_stub_jump_synthesis_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width) (ck l_ext : Nat) :
    ((∀ n : Nat, 1 ≤ n → compactLen n 0 = 2 * n - 2 ∧ compactLen n 1 = 2 * n - 1) ∧
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
     JumpOk (.labAsm (.call (.lab 64 0)) (0 : BitVec width) [] 0) = true) :=
  ⟨⟨compact_len_cases,
    compact_zero_iff,
    compact_full_key,
    ext_zero_rejected ck,
    ext_child_rejected l_ext,
    accepted_advances,
    walk_bound_decoded,
    heap_nodes,
    expansion_fits,
    expansion_traps,
    expansion_ratio⟩,
   panToLab_lines_non_vacuous_and_tight arch prog wc ac perf sc dc mh sp off,
   panToTarget_noStubJump_non_vacuous_and_tight arch prog wc ac perf sc dc mh sp off,
   panToTarget_user_noStubJump_non_vacuous_and_tight arch prog wc ac perf sc dc mh sp off⟩

/-- 8. Strictly increasing 50-budget (`FiftyShape`, `FiftyClaimPayloads`) and **52-budget**
(`FiftyTwoShape`, `FiftyTwoClaimPayloads`) portfolios below the Yukon ceiling (`900_719_925_474`)
coupled with `buildTicks` superadditivity (`split_le`, `split_strict`, `absorbed_with_cap`) and
decoded trie walk bounds (`walk_bound_decoded`). -/
theorem fifty_and_fifty_two_budget_portfolios_and_payloads_synthesis_non_vacuous_and_tight
    (l_chunks : List Nat) (ck : Nat) :
    (FiftyShape ∧ FiftyClaimPayloads) ∧
    (FiftyTwoShape ∧ FiftyTwoClaimPayloads) ∧
    ((l_chunks.map buildTicks).sum ≤ buildTicks l_chunks.sum ∧
     (buildTicks 2 + buildTicks 2 = 10 ∧ buildTicks 4 = 30) ∧
     (∀ L n u B blk : Nat, L ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
       40 * blk ≤ B * B → blk + 10 * L * n ≤ 100000000000)) ∧
    (extAccepted 0 ck = false ∧
     (∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
       ((l.map Step.ext).map advance).sum ≤ 64 → l.length ≤ 64) ∧
     (33806089496 - 2713714688) / 56 = 555220978) :=
  ⟨⟨fifty_shape_non_vacuous_and_tight, fifty_payloads_non_vacuous_and_tight⟩,
   fifty_two_portfolio_and_payloads_non_vacuous_and_tight,
   ⟨split_le l_chunks, split_strict, absorbed_with_cap⟩,
   ⟨ext_zero_rejected ck, walk_bound_decoded, heap_nodes⟩⟩

/-- 9. Explicit finite certificates across the 48-budget, 50-budget, and **52-budget** portfolios
under the base certificate hypothesis `cert : CertificateAt 1_212_035_192`, united with decoded
trie walk bounds (`walk_bound_decoded`) and run-cap absorption (`absorbed_with_cap`). -/
theorem fifty_and_fifty_two_budget_explicit_certificates_synthesis_non_vacuous_and_tight
    (cert : CertificateAt 1_212_035_192) (K : Nat) :
    (FiftyTwoShape ∧ FiftyTwoClaimPayloads ∧
     (∀ k ∈ fiftyTwoPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
    ((FiftyShape ∧ FiftyClaimPayloads ∧
      (∀ k ∈ fiftyPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
     ((fortyEightPortfolio.length = 48 ∧ fortyEightPortfolio.Pairwise (· < ·) ∧
       ∀ k ∈ fortyEightPortfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474) ∧
      ((fortyEightPortfolio.length = 48 ∧ fortyEightPortfolio.Pairwise (· < ·) ∧
        ∀ k ∈ fortyEightPortfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474) ∧
       (∀ k ∈ fortyEightPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
      (fortyEightSharedClaims.length = 48 ∧
       fortyEightSharedClaims.map Prod.fst = fortyEightPortfolio ∧
       (∀ entry ∈ fortyEightSharedClaims,
         entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true)) ∧
      (((fortyEightPortfolio.length = 48 ∧ fortyEightPortfolio.Pairwise (· < ·) ∧
         ∀ k ∈ fortyEightPortfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474) ∧
        (∀ k ∈ fortyEightPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
        fortyEightSharedClaims.length = 48 ∧
        fortyEightSharedClaims.map Prod.fst = fortyEightPortfolio ∧
        (∀ entry ∈ fortyEightSharedClaims,
          entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true)) ∧
       (fortyEightPortfolio.length = 48 ∧
        fortyEightPortfolio.Pairwise (· < ·) ∧
        (∀ k ∈ fortyEightPortfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474) ∧
        fortyEightSharedPortfolio.length = 48 ∧
        fortyEightSharedPortfolio.Pairwise (· < ·) ∧
        (∀ k ∈ fortyEightSharedPortfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474) ∧
        fortyEightElevenTablesPortfolio.length = 48 ∧
        fortyEightElevenTablesPortfolio.Pairwise (· < ·) ∧
        (∀ k ∈ fortyEightElevenTablesPortfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474) ∧
        fortyFourSortedPortfolio.length = 44 ∧
        fortyFourSortedPortfolio.Pairwise (· < ·) ∧
        elevenTablesSharedSlope3UnrolledK = 468_266_987_647 ∧
        elevenTablesSharedSlope3K = 468_267_001_447 ∧
        elevenTablesSharedSlope5UnrolledK = 780_444_973_257 ∧
        elevenTablesSharedSlope5K = 780_444_987_057 ∧
        elevenTablesSlope3UnrolledK = 502_295_977_246 ∧
        elevenTablesSlope3K = 502_295_991_046 ∧
        elevenTablesSlope5UnrolledK = 837_159_955_922 ∧
        elevenTablesSlope5K = 837_159_969_722 ∧
        elevenTablesSlope3UnrolledK - elevenTablesSharedSlope3UnrolledK = 34_028_989_599 ∧
        elevenTablesSlope5UnrolledK - elevenTablesSharedSlope5UnrolledK = 56_714_982_665 ∧
        yukon - elevenTablesSharedSlope5K = 120_274_938_417 ∧
        (elevenTablesSharedSlope5K ≤ K ↔ 780_444_987_057 ≤ K))))) ∧
    ((∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
       ((l.map Step.ext).map advance).sum ≤ 64 → l.length ≤ 64) ∧
     (∀ L n u B blk : Nat, L ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
       40 * blk ≤ B * B → blk + 10 * L * n ≤ 100000000000)) :=
  ⟨⟨(integrated_master_non_vacuous_and_tight cert).1,
    (integrated_master_non_vacuous_and_tight cert).2.1,
    (integrated_master_non_vacuous_and_tight cert).2.2.1⟩,
   fifty_and_forty_eight_budget_portfolios_certificates_and_claims_synthesis_non_vacuous_and_tight cert K,
   ⟨walk_bound_decoded, absorbed_with_cap⟩⟩

/-- 10. Grand self-contained synthesis (`W5_151`): unites
(1) Hex-Prefix decoding and zero-length extension rejection (`compact_len_cases`,
    `compact_zero_iff`, `ext_zero_rejected`, `accepted_advances`, `walk_bound_decoded` ≤ 64
    advancing steps / 65 total steps unconditionally) and heap bounds (`heap_nodes`,
    `expansion_fits`, `expansion_traps`, `expansion_ratio`),
(2) `buildTicks` superadditivity (`split_le`, `split_strict`, `absorbed_with_cap`) and the
    unconditional `PanSimp → LabToTarget` chain (`CompilerSafety`, `panToLab_lines`,
    `panToTarget_noStubJump`, `panToTarget_user_sections_noStubJump`),
(3) the strictly increasing **52-budget** (and 50-budget) portfolio below the Yukon ceiling
    (`900_719_925_474`) with explicit finite certificates lifted from `cert : CertificateAt 1_212_035_192`. -/
theorem grand_witness_decode_subcall_revert_lab_to_target_and_fifty_two_budget_master_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (ck l_ext : Nat)
    (cert : CertificateAt 1_212_035_192) :
    ((∀ n : Nat, 1 ≤ n → compactLen n 0 = 2 * n - 2 ∧ compactLen n 1 = 2 * n - 1) ∧
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
     (∀ K ∈ fiftyPortfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
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
       (∀ r ns nc : Nat, 4 * (ns + nc) ≤ maxInput →
         boundedBuild r ns + boundedBuild r nc ≤ boundedBuild r 33554428)) ∧
     (FiftyTwoShape ∧ FiftyTwoClaimPayloads ∧
       (∀ K ∈ fiftyTwoPortfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
       (∀ l : List Nat, (l.map buildTicks).sum ≤ buildTicks l.sum) ∧
       (∀ j : List Bool, j.length ≤ 524288 →
         _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.restoreDels j ≤ 524288) ∧
       (∀ u1 u2 t1 t2 : Nat, u1 + u2 ≤ 2000000 → t1 ≤ 373022 * u1 →
         t2 ≤ 373022 * u2 → t1 + t2 ≤ 746044000000) ∧
       (∀ L n u B blk : Nat, L ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
         40 * blk ≤ B * B → blk + 10 * L * n ≤ 100000000000) ∧
       KeyCap ∧ PackingAndBuild ∧ BlockCosts ∧ OneSlopeMargin ∧ TransientObstruction ∧ RemainingTables)) :=
  ⟨⟨compact_len_cases,
    compact_zero_iff,
    compact_full_key,
    ext_zero_rejected ck,
    ext_child_rejected l_ext,
    accepted_advances,
    fun l hacc hsum =>
      have hlen := walk_bound_decoded l hacc hsum
      ⟨hlen, Nat.add_le_add_right hlen 1⟩,
    heap_nodes,
    expansion_fits,
    expansion_traps,
    expansion_ratio⟩,
   ⟨split_le,
    split_strict,
    tx_worst_revert,
    absorbed_with_cap,
    guest_vs_cap,
    compiler_chain_non_vacuous_and_tight arch prog wc ac perf info j bd ptr f,
    fifty_shape_non_vacuous_and_tight,
    fifty_payloads_non_vacuous_and_tight,
    (fifty_certificates_non_vacuous_and_tight cert).2.2⟩,
   self_contained_lab_to_target_nodedb_and_fifty_two_budget_master_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off cert⟩

#print axioms compact_to_nibbles_and_extension_rejection_non_vacuous_and_tight
#print axioms decoded_trie_walk_bound_and_witness_heap_expansion_non_vacuous_and_tight
#print axioms witness_decode_and_nodedb_capacity_build_synthesis_non_vacuous_and_tight
#print axioms build_ticks_superadditivity_tx_packing_and_run_cap_absorption_non_vacuous_and_tight
#print axioms transient_coupled_yukon_journal_and_one_slope_margin_synthesis_non_vacuous_and_tight
#print axioms pan_to_stack_to_lab_and_lab_to_target_no_stub_jump_synthesis_non_vacuous_and_tight
#print axioms witness_decode_and_pan_to_target_no_stub_jump_synthesis_non_vacuous_and_tight
#print axioms fifty_and_fifty_two_budget_portfolios_and_payloads_synthesis_non_vacuous_and_tight
#print axioms fifty_and_fifty_two_budget_explicit_certificates_synthesis_non_vacuous_and_tight
#print axioms grand_witness_decode_subcall_revert_lab_to_target_and_fifty_two_budget_master_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth
