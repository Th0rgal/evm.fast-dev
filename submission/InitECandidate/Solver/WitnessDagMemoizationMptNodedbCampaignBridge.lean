import InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound
import InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge
import InitECandidate.Solver.SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.WitnessDagMemoizationMptNodedbCampaignBridge`

Wave 5 atomic bridge (`W5_155`, `0` imports from `InitECandidate.Proofs.Bounded*`) unifying:
1. **`GuestWitnessDagMemoizationAndHeapBound` (`11/11` tight)**:
   - Per-node decoded heap lower bounds (`leaf ≥ 98`, `ext ≥ 90`, `branch ≥ 448`), available heap
     `heapAvail = 31_092_374_808` (`heap_avail_val`), decoded node cap `L + E + B ≤ 345_470_831`
     (`nodes_by_heap`, `nodes_by_heap_tight`), and branch cap `B ≤ 69_402_622` (`branches_by_heap`),
   - Unmodified heap tick bound `τ * bytes ≤ τ * 31_092_374_808` (`decode_heap_bound`) with Yukon
     thresholds `τ ≤ 28` at `1×` (`heap_threshold`) and `τ ≤ 5` at `5×` (`heap_threshold_5x`),
   - DAG memoization (`nodes_memo` ≤ `33_554_428`, `memo_heap = 15_300_819_168 < heapAvail`,
     `memo_threshold` at `τ ≤ 58`, `memo_gain`: `2 * 15_300_819_168 ≤ heapAvail`).
2. **`GuestMptNodedbAndTransientStorageBridge` (`10/10` tight)**:
   - Combined MPT linear budget and bounded-run `nodedb` build at `r = 8`:
     `mptPlusBuild = 19_500_000_000 + 536_870_848 = 20_036_870_848` (`sum_val`, `sum_margin`,
     `two_builds_at_8`, `mpt_plus_two_builds`),
   - Combined 11-table storage + MPT + `nodedb` envelope:
     `joint = 156_088_992_805 + 20_036_870_848 = 176_125_863_653` (`joint_val`, `joint_once`,
     `joint_five`: `5 * joint = 880_629_318_265`, Yukon margin `20_090_607_209`, `joint_covers`),
   - `buildTicks` superadditivity witnesses and sharp `ts+64` run-cap thresholds (`build_split`,
     `anchors`).
3. **`SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth` (`10/10` tight)**:
   - Zero-length extension rejection (`ext_zero_rejected`), unconditional decoded trie walk bound
     `≤ 64` advancing steps / `≤ 65` total iterations (`walk_bound_decoded`),
   - Unconditional `PanSimp → LabToTarget` section-6 (`storeConstsStubLocation`) unreachability
     (`panToLab_lines`, `panToTarget_noStubJump`, `panToTarget_user_sections_noStubJump`),
   - Strictly increasing 50-budget and **52-budget** portfolios below Yukon (`900_719_925_474`) with
     explicit finite certificates under `cert : CertificateAt 1_212_035_192`.
-/

namespace InitECandidate.Solver.WitnessDagMemoizationMptNodedbCampaignBridge

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
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
  bounded_build_val
  two_builds
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
  jumpOk_rejects_stub
  jumpOk_accepts_user
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
  fifty_certificates_non_vacuous_and_tight
)
open InitECandidate.Solver.TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster (
  FiftyTwoShape
  integrated_master_non_vacuous_and_tight
)
open InitECandidate.Solver.SelfContainedSubcallRevertAbsorptionAndFiftyBudgetSynth (
  fiftyPortfolio
  fortyEightPortfolio
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
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

variable {width : Nat} [NeZero width]

/-! ## Ten `non_vacuous_and_tight` Campaign Bridge Theorems (`0 sorryAx`) -/

/-- 1. Per-node heap lower bounds (`heapOf 1 0 0 = 98`, `heapOf 0 1 0 = 90`, `heapOf 0 0 1 = 448`),
available heap `heapAvail = 31_092_374_808` (`heap_avail_val`), decoded node ceiling
`L + E + B ≤ 345_470_831` (`nodes_by_heap`, `nodes_by_heap_tight`), and branch ceiling
`B ≤ 69_402_622` (`branches_by_heap`). -/
theorem witness_per_node_heap_and_node_ceilings_non_vacuous_and_tight :
    heapAvail = 31092374808 ∧
    (heapOf 1 0 0 = 98 ∧ heapOf 0 1 0 = 90 ∧ heapOf 0 0 1 = 448) ∧
    (∀ L E B : Nat, heapOf L E B ≤ heapAvail → L + E + B ≤ 345470831) ∧
    (heapOf 0 345470831 0 ≤ heapAvail ∧ heapAvail < heapOf 0 345470832 0) ∧
    (∀ B : Nat, heapOf 0 0 B ≤ heapAvail → B ≤ 69402622) ∧
    (heapOf 0 0 69402622 ≤ heapAvail ∧ heapAvail < heapOf 0 0 69402623) :=
  ⟨heap_avail_val,
   by decide,
   nodes_by_heap,
   nodes_by_heap_tight,
   branches_by_heap,
   by decide⟩

/-- 2. Unmodified heap tick bound (`decode_heap_bound`: `τ * bytes ≤ τ * 31_092_374_808`),
Yukon rate thresholds `τ ≤ 28` at `1×` (`heap_threshold`) and `τ ≤ 5` at `5×` (`heap_threshold_5x`),
and DAG memoization bounds (`nodes_memo` ≤ `33_554_428`, `memo_heap = 15_300_819_168 < heapAvail`,
`memo_threshold` at `τ ≤ 58`, and `memo_gain`: `2 * 15_300_819_168 ≤ heapAvail`). -/
theorem witness_heap_thresholds_and_dag_memoization_non_vacuous_and_tight :
    (∀ τ bytes : Nat, bytes ≤ heapAvail → τ * bytes ≤ τ * 31092374808) ∧
    (28 * 31092374808 < yukon ∧ yukon < 29 * 31092374808) ∧
    (5 * (5 * 31092374808) < yukon ∧ yukon < 5 * (6 * 31092374808)) ∧
    (∀ L E B n : Nat, 4 * n ≤ 134217712 → L + E + B ≤ n → L + E + B ≤ 33554428) ∧
    (448 * 33554428 + 2 * 134217712 = 15300819168 ∧ 15300819168 < heapAvail) ∧
    (58 * 15300819168 < yukon ∧ yukon < 59 * 15300819168) ∧
    2 * 15300819168 ≤ heapAvail :=
  ⟨decode_heap_bound,
   heap_threshold,
   heap_threshold_5x,
   nodes_memo,
   memo_heap,
   memo_threshold,
   memo_gain⟩

/-- 3. Combined MPT linear budget and bounded-run `nodedb` build at `r = 8` (`mptPlusBuild =
19_500_000_000 + 536_870_848 = 20_036_870_848`), `44×` Yukon headroom (`sum_margin`), and two-table
state+code coverage (`two_builds_at_8`, `mpt_plus_two_builds`). -/
theorem mpt_and_nodedb_two_builds_bridge_non_vacuous_and_tight :
    mptPlusBuild = 20036870848 ∧
    19500000000 + 536870848 = 20036870848 ∧
    (44 * mptPlusBuild < yukon ∧ yukon ≤ 45 * mptPlusBuild) ∧
    (∀ ns nc : Nat, 4 * (ns + nc) ≤ maxInput →
      boundedBuild 8 ns + boundedBuild 8 nc ≤ 536870848) ∧
    (∀ ns nc : Nat, 4 * (ns + nc) ≤ maxInput →
      19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ mptPlusBuild) ∧
    boundedBuild 8 33554428 + boundedBuild 8 0 = 536870848 :=
  ⟨sum_val,
   by decide,
   sum_margin,
   two_builds_at_8,
   mpt_plus_two_builds,
   by decide⟩

/-- 4. Combined 11-table storage + MPT + `nodedb` envelope (`joint = 156_088_992_805 +
20_036_870_848 = 176_125_863_653`), `1×` Yukon margin (`724_594_061_821`), `5×` Yukon fit
(`880_629_318_265 < 900_719_925_474`, margin `20_090_607_209`), dominance over two `nodedb` builds
(`joint_covers`), and `ts+64` split/revert and sharp run-cap anchors (`build_split`, `anchors`). -/
theorem joint_mpt_nodedb_transient_storage_envelope_non_vacuous_and_tight :
    joint = 176125863653 ∧
    156088992805 + 20036870848 = 176125863653 ∧
    yukon - joint = 724594061821 ∧
    (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209) ∧
    (5 * joint < yukon ∧ yukon < 6 * joint) ∧
    (∀ ns nc : Nat, 4 * (ns + nc) ≤ maxInput →
      156088992805 + 19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ joint) ∧
    (5 * (2 * 1) / 2 + 5 * (2 * 1) / 2 = 10 ∧ 5 * (4 * 3) / 2 = 30 ∧
      2 * (5 * (158162 * 158161) / 2) = 125075300410) ∧
    (10 * 5000 = 50000 ∧ 50000 < 10 * 5001 ∧ 5 * 10000 = 50000 ∧ 50000 < 5 * 10001) :=
  ⟨joint_val,
   by decide,
   joint_once,
   joint_five,
   by decide,
   joint_covers,
   build_split,
   anchors⟩

/-- 5. Unified witness DAG memoization and MPT + `nodedb` + `ts+64` bridge: connects per-node heap
bounds (`98`, `90`, `448`), `nodes_by_heap = 345_470_831`, DAG memoization (`nodes_memo =
33_554_428`, `memo_heap = 15_300_819_168`, `τ ≤ 58`), and the `5×` joint envelope
(`880_629_318_265 < yukon`, margin `20_090_607_209`). -/
theorem witness_dag_memoization_and_joint_mpt_nodedb_bridge_non_vacuous_and_tight :
    (heapAvail = 31092374808 ∧
      (∀ L E B : Nat, heapOf L E B ≤ heapAvail → L + E + B ≤ 345470831) ∧
      (heapOf 0 345470831 0 ≤ heapAvail ∧ heapAvail < heapOf 0 345470832 0) ∧
      (28 * 31092374808 < yukon ∧ yukon < 29 * 31092374808) ∧
      (5 * (5 * 31092374808) < yukon ∧ yukon < 5 * (6 * 31092374808))) ∧
    ((∀ L E B n : Nat, 4 * n ≤ 134217712 → L + E + B ≤ n → L + E + B ≤ 33554428) ∧
      (448 * 33554428 + 2 * 134217712 = 15300819168 ∧ 15300819168 < heapAvail) ∧
      (58 * 15300819168 < yukon ∧ yukon < 59 * 15300819168) ∧
      2 * 15300819168 ≤ heapAvail) ∧
    (mptPlusBuild = 20036870848 ∧
      joint = 176125863653 ∧
      (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209) ∧
      (∀ ns nc : Nat, 4 * (ns + nc) ≤ maxInput →
        156088992805 + 19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ joint)) :=
  ⟨⟨heap_avail_val, nodes_by_heap, nodes_by_heap_tight, heap_threshold, heap_threshold_5x⟩,
   ⟨nodes_memo, memo_heap, memo_threshold, memo_gain⟩,
   ⟨sum_val, joint_val, joint_five, joint_covers⟩⟩

/-- 6. Synthesis of Hex-Prefix witness decoding (`compact_len_cases`, `compact_zero_iff`,
`ext_zero_rejected`, `accepted_advances`, `walk_bound_decoded` ≤ 64 advancing steps / 65 total
steps) with per-node heap lower bounds (`98`, `90`, `448`), `nodes_by_heap = 345_470_831`, and DAG
memoization (`nodes_memo = 33_554_428`, `memo_heap = 15_300_819_168`, `τ ≤ 58`). -/
theorem witness_decode_extension_nibble_and_dag_memoization_non_vacuous_and_tight
    (ck l_ext : Nat) :
    ((∀ n : Nat, 1 ≤ n → compactLen n 0 = 2 * n - 2 ∧ compactLen n 1 = 2 * n - 1) ∧
     (∀ n odd : Nat, 1 ≤ n → odd ≤ 1 → (compactLen n odd = 0 ↔ n = 1 ∧ odd = 0)) ∧
     (compactLen 33 0 = 64 ∧ compactLen 32 1 = 63) ∧
     extAccepted 0 ck = false ∧
     (extAccepted l_ext 2 = false ∧ extAccepted l_ext 1 = false) ∧
     (∀ l' ck' : Nat, extAccepted l' ck' = true → 1 ≤ advance (.ext l')) ∧
     (∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
       ((l.map Step.ext).map advance).sum ≤ 64 → l.length ≤ 64 ∧ l.length + 1 ≤ 65) ∧
     ((List.replicate 64 1).length = 64 ∧
       (((List.replicate 64 1).map Step.ext).map advance).sum = 64)) ∧
    (heapAvail = 31092374808 ∧
     (heapOf 1 0 0 = 98 ∧ heapOf 0 1 0 = 90 ∧ heapOf 0 0 1 = 448) ∧
     (∀ L E B : Nat, heapOf L E B ≤ heapAvail → L + E + B ≤ 345470831) ∧
     (heapOf 0 345470831 0 ≤ heapAvail ∧ heapAvail < heapOf 0 345470832 0) ∧
     (∀ L E B n : Nat, 4 * n ≤ 134217712 → L + E + B ≤ n → L + E + B ≤ 33554428) ∧
     (448 * 33554428 + 2 * 134217712 = 15300819168 ∧ 15300819168 < heapAvail) ∧
     (28 * 31092374808 < yukon ∧ yukon < 29 * 31092374808) ∧
     (5 * (5 * 31092374808) < yukon ∧ yukon < 5 * (6 * 31092374808)) ∧
     (58 * 15300819168 < yukon ∧ yukon < 59 * 15300819168)) :=
  ⟨⟨compact_len_cases,
    compact_zero_iff,
    compact_full_key,
    ext_zero_rejected ck,
    ext_child_rejected l_ext,
    accepted_advances,
    fun l hacc hsum =>
      have hlen := walk_bound_decoded l hacc hsum
      ⟨hlen, Nat.add_le_add_right hlen 1⟩,
    by decide⟩,
   ⟨heap_avail_val,
    by decide,
    nodes_by_heap,
    nodes_by_heap_tight,
    nodes_memo,
    memo_heap,
    heap_threshold,
    heap_threshold_5x,
    memo_threshold⟩⟩

/-- 7. Synthesis of unconditional `PanSimp → LabToTarget` section-6 (`storeConstsStubLocation`)
unreachability (`CompilerSafety`, `panToLab_lines`, `panToTarget_noStubJump`,
`panToTarget_user_sections_noStubJump`), witness decoding (`ext_zero_rejected`,
`walk_bound_decoded`), and the MPT + `nodedb` + `ts+64` joint envelope (`joint = 176_125_863_653`,
`5 * joint = 880_629_318_265`, Yukon margin `20_090_607_209`). -/
theorem pan_to_target_no_stub_jump_and_mpt_nodedb_bridge_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (ck : Nat) :
    CompilerSafety arch prog wc ac perf info j bd ptr f ∧
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
    (JumpOk (.labAsm (.jump (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
     JumpOk (.labAsm (.call (.lab 64 0)) (0 : BitVec width) [] 0) = true) ∧
    (extAccepted 0 ck = false ∧
     (∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
       ((l.map Step.ext).map advance).sum ≤ 64 → l.length ≤ 64 ∧ l.length + 1 ≤ 65)) ∧
    (mptPlusBuild = 20036870848 ∧
     joint = 176125863653 ∧
     (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209) ∧
     (∀ ns nc : Nat, 4 * (ns + nc) ≤ maxInput →
       156088992805 + 19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ joint)) :=
  ⟨compiler_chain_non_vacuous_and_tight arch prog wc ac perf info j bd ptr f,
   panToLab_lines arch prog wc ac perf sc dc mh sp off,
   fun ic pos labs ffis L' labs' h =>
     ⟨panToTarget_noStubJump arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h,
      fun s' hs hu =>
        panToTarget_user_sections_noStubJump arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h s' hs hu⟩,
   ⟨jumpOk_rejects_stub, jumpOk_accepts_user⟩,
   ⟨ext_zero_rejected ck,
    fun l hacc hsum =>
      have hlen := walk_bound_decoded l hacc hsum
      ⟨hlen, Nat.add_le_add_right hlen 1⟩⟩,
   ⟨sum_val, joint_val, joint_five, joint_covers⟩⟩

/-- 8. Synthesis of the strictly increasing 50-budget (`FiftyShape`, `FiftyClaimPayloads`) and
**52-budget** (`FiftyTwoShape`, `FiftyTwoClaimPayloads`) portfolios below Yukon (`900_719_925_474`)
with witness DAG memoization (`nodes_by_heap = 345_470_831`, `nodes_memo = 33_554_428`,
`memo_heap = 15_300_819_168`, `τ ≤ 28` / `τ ≤ 5` / `τ ≤ 58`) and the combined MPT + `nodedb` +
`ts+64` envelope (`joint = 176_125_863_653`, `5 * joint = 880_629_318_265`, margin `20_090_607_209`). -/
theorem fifty_two_budget_portfolio_witness_dag_and_mpt_nodedb_synthesis_non_vacuous_and_tight
    (l_chunks : List Nat) (ck : Nat) :
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
    (heapAvail = 31092374808 ∧
     (∀ L E B : Nat, heapOf L E B ≤ heapAvail → L + E + B ≤ 345470831) ∧
     (∀ L E B n : Nat, 4 * n ≤ 134217712 → L + E + B ≤ n → L + E + B ≤ 33554428) ∧
     (448 * 33554428 + 2 * 134217712 = 15300819168 ∧ 15300819168 < heapAvail) ∧
     (28 * 31092374808 < yukon ∧ yukon < 29 * 31092374808) ∧
     (5 * (5 * 31092374808) < yukon ∧ yukon < 5 * (6 * 31092374808)) ∧
     (58 * 15300819168 < yukon ∧ yukon < 59 * 15300819168)) ∧
    (mptPlusBuild = 20036870848 ∧
     joint = 176125863653 ∧
     (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209) ∧
     (∀ ns nc : Nat, 4 * (ns + nc) ≤ maxInput →
       156088992805 + 19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ joint)) :=
  ⟨fifty_and_fifty_two_budget_portfolios_and_payloads_synthesis_non_vacuous_and_tight l_chunks ck,
   ⟨heap_avail_val, nodes_by_heap, nodes_memo, memo_heap, heap_threshold, heap_threshold_5x, memo_threshold⟩,
   ⟨sum_val, joint_val, joint_five, joint_covers⟩⟩

/-- 9. Explicit finite certificates across the 48-budget, 50-budget, and **52-budget** portfolios
under `cert : CertificateAt 1_212_035_192`, joined with witness DAG memoization (`nodes_by_heap`,
`nodes_memo`, `memo_heap`, `heap_threshold`, `heap_threshold_5x`, `memo_threshold`) and the
combined MPT + `nodedb` + `ts+64` envelope (`sum_val`, `joint_val`, `joint_five`, `joint_covers`). -/
theorem fifty_two_budget_explicit_certificates_and_dag_mpt_nodedb_bridge_non_vacuous_and_tight
    (cert : CertificateAt 1_212_035_192) :
    (FiftyTwoShape ∧ FiftyTwoClaimPayloads ∧
     (∀ k ∈ fiftyTwoPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
    (FiftyShape ∧ FiftyClaimPayloads ∧
     (∀ k ∈ fiftyPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
    (fortyEightPortfolio.length = 48 ∧ fortyEightPortfolio.Pairwise (· < ·) ∧
     (∀ k ∈ fortyEightPortfolio, 1_212_035_192 ≤ k ∧ k < 900_719_925_474) ∧
     (∀ k ∈ fortyEightPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
    (heapAvail = 31092374808 ∧
     (heapOf 1 0 0 = 98 ∧ heapOf 0 1 0 = 90 ∧ heapOf 0 0 1 = 448) ∧
     (∀ L E B : Nat, heapOf L E B ≤ heapAvail → L + E + B ≤ 345470831) ∧
     (heapOf 0 345470831 0 ≤ heapAvail ∧ heapAvail < heapOf 0 345470832 0) ∧
     (∀ L E B n : Nat, 4 * n ≤ 134217712 → L + E + B ≤ n → L + E + B ≤ 33554428) ∧
     (448 * 33554428 + 2 * 134217712 = 15300819168 ∧ 15300819168 < heapAvail) ∧
     (28 * 31092374808 < yukon ∧ yukon < 29 * 31092374808) ∧
     (5 * (5 * 31092374808) < yukon ∧ yukon < 5 * (6 * 31092374808)) ∧
     (58 * 15300819168 < yukon ∧ yukon < 59 * 15300819168)) ∧
    (mptPlusBuild = 20036870848 ∧
     joint = 176125863653 ∧
     yukon - joint = 724594061821 ∧
     (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209) ∧
     (∀ ns nc : Nat, 4 * (ns + nc) ≤ maxInput →
       156088992805 + 19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ joint)) :=
  have hexp := fifty_and_fifty_two_budget_explicit_certificates_synthesis_non_vacuous_and_tight cert 780_444_987_057
  ⟨hexp.1,
   hexp.2.1.1,
   ⟨hexp.2.1.2.1.1, hexp.2.1.2.1.2.1, hexp.2.1.2.1.2.2, hexp.2.1.2.2.1.2⟩,
   ⟨heap_avail_val,
    by decide,
    nodes_by_heap,
    nodes_by_heap_tight,
    nodes_memo,
    memo_heap,
    heap_threshold,
    heap_threshold_5x,
    memo_threshold⟩,
   ⟨sum_val, joint_val, joint_once, joint_five, joint_covers⟩⟩

/-- 10. Grand Wave 5 Campaign Bridge (`W5_155`): unifies
(1) `GuestWitnessDagMemoizationAndHeapBound` (`11/11` tight: per-node heap bounds `98 / 90 / 448`,
    `nodes_by_heap = 345_470_831`, Yukon rate thresholds `τ ≤ 28`, `τ ≤ 5`, and DAG memoization
    `nodes_memo = 33_554_428`, `memo_heap = 15_300_819_168`, `τ ≤ 58`),
(2) `GuestMptNodedbAndTransientStorageBridge` (`10/10` tight: `mptPlusBuild = 20_036_870_848`,
    `joint = 176_125_863_653`, `5 * joint = 880_629_318_265 < yukon`, margin `20_090_607_209`,
    `two_builds_at_8`, `joint_covers`), and
(3) `SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth` (`10/10` tight:
    `ext_zero_rejected`, `walk_bound_decoded ≤ 64` / `≤ 65`, `panToTarget_noStubJump`, and the
    strictly increasing **52-budget** portfolio under Yukon with explicit finite certificates). -/
theorem grand_witness_dag_memoization_mpt_nodedb_and_fifty_two_budget_campaign_bridge_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (ck l_ext : Nat)
    (cert : CertificateAt 1_212_035_192) :
    (heapAvail = 31092374808 ∧
     (heapOf 1 0 0 = 98 ∧ heapOf 0 1 0 = 90 ∧ heapOf 0 0 1 = 448) ∧
     (∀ L E B : Nat, heapOf L E B ≤ heapAvail → L + E + B ≤ 345470831) ∧
     (heapOf 0 345470831 0 ≤ heapAvail ∧ heapAvail < heapOf 0 345470832 0) ∧
     (∀ B : Nat, heapOf 0 0 B ≤ heapAvail → B ≤ 69402622) ∧
     (∀ τ bytes : Nat, bytes ≤ heapAvail → τ * bytes ≤ τ * 31092374808) ∧
     (28 * 31092374808 < yukon ∧ yukon < 29 * 31092374808) ∧
     (5 * (5 * 31092374808) < yukon ∧ yukon < 5 * (6 * 31092374808)) ∧
     (∀ L E B n : Nat, 4 * n ≤ 134217712 → L + E + B ≤ n → L + E + B ≤ 33554428) ∧
     (448 * 33554428 + 2 * 134217712 = 15300819168 ∧ 15300819168 < heapAvail) ∧
     (58 * 15300819168 < yukon ∧ yukon < 59 * 15300819168) ∧
     2 * 15300819168 ≤ heapAvail) ∧
    (mptPlusBuild = 20036870848 ∧
     (44 * mptPlusBuild < yukon ∧ yukon ≤ 45 * mptPlusBuild) ∧
     joint = 176125863653 ∧
     yukon - joint = 724594061821 ∧
     (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209) ∧
     (∀ ns nc : Nat, 4 * (ns + nc) ≤ maxInput →
       boundedBuild 8 ns + boundedBuild 8 nc ≤ 536870848) ∧
     (∀ ns nc : Nat, 4 * (ns + nc) ≤ maxInput →
       19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ mptPlusBuild) ∧
     (∀ ns nc : Nat, 4 * (ns + nc) ≤ maxInput →
       156088992805 + 19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ joint) ∧
     (5 * (2 * 1) / 2 + 5 * (2 * 1) / 2 = 10 ∧ 5 * (4 * 3) / 2 = 30 ∧
       2 * (5 * (158162 * 158161) / 2) = 125075300410) ∧
     (10 * 5000 = 50000 ∧ 50000 < 10 * 5001 ∧ 5 * 10000 = 50000 ∧ 50000 < 5 * 10001)) ∧
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
        KeyCap ∧ PackingAndBuild ∧ BlockCosts ∧ OneSlopeMargin ∧ TransientObstruction ∧ RemainingTables))) :=
  ⟨⟨heap_avail_val,
    by decide,
    nodes_by_heap,
    nodes_by_heap_tight,
    branches_by_heap,
    decode_heap_bound,
    heap_threshold,
    heap_threshold_5x,
    nodes_memo,
    memo_heap,
    memo_threshold,
    memo_gain⟩,
   ⟨sum_val,
    sum_margin,
    joint_val,
    joint_once,
    joint_five,
    two_builds_at_8,
    mpt_plus_two_builds,
    joint_covers,
    build_split,
    anchors⟩,
   grand_witness_decode_subcall_revert_lab_to_target_and_fifty_two_budget_master_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off info j bd ptr f ck l_ext cert⟩

#print axioms witness_per_node_heap_and_node_ceilings_non_vacuous_and_tight
#print axioms witness_heap_thresholds_and_dag_memoization_non_vacuous_and_tight
#print axioms mpt_and_nodedb_two_builds_bridge_non_vacuous_and_tight
#print axioms joint_mpt_nodedb_transient_storage_envelope_non_vacuous_and_tight
#print axioms witness_dag_memoization_and_joint_mpt_nodedb_bridge_non_vacuous_and_tight
#print axioms witness_decode_extension_nibble_and_dag_memoization_non_vacuous_and_tight
#print axioms pan_to_target_no_stub_jump_and_mpt_nodedb_bridge_non_vacuous_and_tight
#print axioms fifty_two_budget_portfolio_witness_dag_and_mpt_nodedb_synthesis_non_vacuous_and_tight
#print axioms fifty_two_budget_explicit_certificates_and_dag_mpt_nodedb_bridge_non_vacuous_and_tight
#print axioms grand_witness_dag_memoization_mpt_nodedb_and_fifty_two_budget_campaign_bridge_non_vacuous_and_tight

end InitECandidate.Solver.WitnessDagMemoizationMptNodedbCampaignBridge
