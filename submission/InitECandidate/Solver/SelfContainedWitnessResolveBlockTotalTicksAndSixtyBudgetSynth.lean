import InitECandidate.Solver.GuestWitnessResolveAndBlockTotalTicksSynthesis
import InitECandidate.Solver.SelfContainedWitnessDagMemoizationAndFiftySixBudgetSynth
import InitECandidate.Solver.WitnessDecodeExactTicksNoLocValue6AndSixtyBudgetMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedWitnessResolveBlockTotalTicksAndSixtyBudgetSynth`

Self-contained Wave 5 synthesis (`W5_169`, `0` imports from `InitECandidate.Proofs.Bounded*`)
uniting:
1. **`GuestWitnessResolveAndBlockTotalTicksSynthesis` (`11/11` tight)**:
   - `_resolve_step` call bounds (`≤ 1_110_441_952` on heap-capped `69_402_622` branches,
     `≤ 536_870_848` on DAG-memoized `33_554_428` nodes), exact probe costs at `r = 8`
     (`17_767_071_232` and `8_589_933_568` ticks), and sharp Yukon margin thresholds `r ≤ 312`
     (heap) and `r ≤ 664` (memo),
   - Conditional block total (assuming `ts+64` quadratic hazard is fixed): `block_total = 207_218_238_461`
     (margin `693_501_687_013` under Yukon `900_719_925_474`) and `block_total_memo = 187_064_607_181`
     (margin `713_655_318_293`, `4× = 748_258_428_724 < 900_719_925_474`, `memo_saving = 20_153_631_280`).
2. **`SelfContainedWitnessDagMemoizationAndFiftySixBudgetSynth` (`10/10` tight)**:
   - Complete synthesis of per-node heap floors (`98/90/448`), `345_470_831` node cap, `τ ≤ 28` (`1×`),
     `τ ≤ 5` (`5×`), DAG memoization (`33_554_428` nodes, `15_300_819_168` bytes, `τ ≤ 58`),
     MPT + `nodedb` (`20_036_870_848`) + `ts+64` (`176_125_863_653`, `5× = 880_629_318_265`) bridge,
     unconditional `PanSimp → LabToTarget` section-6 safety, and 50/52/54/56-budget portfolios.
3. **`WitnessDecodeExactTicksNoLocValue6AndSixtyBudgetMaster` (`12/12` tight)**:
   - Exact per-node decode ticks (`tLeaf = 43 < 98`, `tExt = 48 < 90`, `tBranch = 326 < 448`) and
     per-byte rate `τ < 1` (`decodeTicks L E B ≤ heapOf L E B ≤ 31_092_374_808`, DAG memo cap
     `10_938_743_528`),
   - Unconditional `StackToLab → LabToTarget` absence of `jump`, `jumpCmp`, `call`, and `locValue`
     into section 6 (`StackToLabAndLabToTargetNoLocValue6`),
   - Strictly increasing **60-budget** portfolio (`SixtyShape`, `ClaimPayloads`) below Yukon
     (`900_719_925_474`) and conditional finite certificate lifting (`certificates_non_vacuous_and_tight`).
-/

namespace InitECandidate.Solver.SelfContainedWitnessResolveBlockTotalTicksAndSixtyBudgetSynth

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
open InitECandidate.Solver.SelfContainedWitnessDagMemoizationAndFiftySixBudgetSynth (
  fiftySixPortfolio
  FiftySixClaimPayloads
  witness_dag_memoization_and_heap_floors_rates_non_vacuous_and_tight
  mpt_nodedb_transient_bridge_and_absorption_synthesis_non_vacuous_and_tight
  extension_zero_rejected_walk_bound_and_dag_memoization_non_vacuous_and_tight
  witness_dag_nodedb_capacity_and_mpt_bridge_synthesis_non_vacuous_and_tight
  transient_superadditivity_coupled_journal_and_joint_bridge_non_vacuous_and_tight
  unconditional_pan_to_target_no_stub_jump_and_compiler_safety_non_vacuous_and_tight
  witness_dag_decode_mpt_bridge_and_pan_to_target_no_stub_jump_non_vacuous_and_tight
  fifty_four_and_fifty_six_budget_portfolios_and_payloads_non_vacuous_and_tight
  fifty_six_budget_explicit_certificates_and_integrated_master_non_vacuous_and_tight
  grand_self_contained_witness_dag_memoization_and_fifty_six_budget_synth_non_vacuous_and_tight
)
open InitECandidate.Solver.WitnessDecodeExactTicksNoLocValue6AndSixtyBudgetMaster (
  portfolio
  sixtyClaims
  ExactTicks
  SixtyShape
  ClaimPayloads
  node_ticks_non_vacuous_and_tight
  ticks_le_heap_non_vacuous_and_tight
  decode_memo_non_vacuous_and_tight
  heap_yukon_non_vacuous_and_tight
  panToTarget_noStubJumpOrLocValue_bridge_non_vacuous_and_tight
  panToTarget_user_sections_noStubJumpOrLocValue_bridge_non_vacuous_and_tight
  joint_bridge_non_vacuous_and_tight
  absorption_non_vacuous_and_tight
  portfolio_non_vacuous_and_tight
  payloads_non_vacuous_and_tight
  certificates_non_vacuous_and_tight
  integrated_master_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

variable {width : Nat} [NeZero width]

abbrev sixtyPortfolio : List Nat :=
  InitECandidate.Solver.WitnessDecodeExactTicksNoLocValue6AndSixtyBudgetMaster.portfolio

abbrev SixtyClaimPayloads : Prop :=
  InitECandidate.Solver.WitnessDecodeExactTicksNoLocValue6AndSixtyBudgetMaster.ClaimPayloads

/-! ## Ten `non_vacuous_and_tight` Master Synthesis Theorems (`0 sorryAx`) -/

/-- 1. `_resolve_step` call bounds (`≤ 1_110_441_952` on heap-capped `69_402_622` branches,
`≤ 536_870_848` on DAG-memoized `33_554_428` nodes), exact probe ticks at `r = 8`
(`17_767_071_232` and `8_589_933_568`), sharp Yukon probe-run thresholds `r ≤ 312` (`313` fails)
and `r ≤ 664` (`665` fails), and unsalted collision overflow (`2 * 2^25 * 1_110_441_952 > 693_501_687_013`). -/
theorem witness_resolve_step_calls_probes_and_thresholds_non_vacuous_and_tight
    (E B r : Nat) (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428) (hr : r ≤ 312) :
    resolveCalls 0 B ≤ 1110441952 ∧
    resolveCalls E B ≤ 536870848 ∧
    (2 * 8 * 1110441952 = 17767071232 ∧ 2 * 8 * 536870848 = 8589933568) ∧
    (2 * 312 * 1110441952 ≤ 693501687013 ∧ 693501687013 < 2 * 313 * 1110441952) ∧
    (2 * 664 * 536870848 ≤ 713655318293 ∧ 713655318293 < 2 * 665 * 536870848) ∧
    gasEnv + mptPlusBuild + decodeHeap + 2 * r * resolveCalls 0 B < yukon ∧
    693501687013 < 2 * 2 ^ 25 * 1110441952 :=
  ⟨resolve_heap B hB,
   resolve_memo E B hEB,
   probe_at_8,
   r_threshold_heap,
   r_threshold_memo,
   total_with_probes B r hB hr,
   unsalted_breaks⟩

/-- 2. Conditional global block total (without quadratic `ts+64`): `block_total = 207_218_238_461`
(Yukon margin `693_501_687_013`), `block_total_memo = 187_064_607_181` (Yukon margin
`713_655_318_293`), `memo_saving = 20_153_631_280`, and `4×` vs `5×` slope thresholds
(`4 * 187_064_607_181 = 748_258_428_724 < 900_719_925_474 < 5 * 187_064_607_181`). -/
theorem conditional_block_total_and_four_slope_synthesis_non_vacuous_and_tight
    (B r : Nat) (hB : B ≤ 69402622) (hr : r ≤ 312) :
    (gasEnv + mptPlusBuild + decodeHeap = 207218238461 ∧
      yukon - (gasEnv + mptPlusBuild + decodeHeap) = 693501687013) ∧
    (gasEnv + mptPlusBuild + decodeMemo = 187064607181 ∧
      yukon - (gasEnv + mptPlusBuild + decodeMemo) = 713655318293) ∧
    (4 * 207218238461 < yukon ∧ yukon < 5 * 207218238461 ∧
      4 * 187064607181 = 748258428724 ∧ 4 * 187064607181 < yukon ∧ yukon < 5 * 187064607181) ∧
    decodeHeap - decodeMemo = 20153631280 ∧
    gasEnv + mptPlusBuild + decodeHeap + 2 * r * resolveCalls 0 B < yukon :=
  ⟨block_total,
   block_total_memo,
   slope_four,
   memo_saving,
   total_with_probes B r hB hr⟩

/-- 3. Exact per-node decode ticks (`tLeaf = 43 < 98`, `tExt = 48 < 90`, `tBranch = 326 < 448`),
per-byte rate `τ < 1` (`decodeTicks L E B ≤ heapOf L E B ≤ 31_092_374_808`), DAG memoization
decode cap (`10_938_743_528` ticks, margin `889_781_181_946`), and `5×` Yukon fit combined with
per-node heap floors (`HeapAllocationContract`, `HeapNodesContract`, `HeapRateContract`, `MemoContract`). -/
theorem exact_decode_ticks_per_byte_and_dag_memoization_non_vacuous_and_tight
    (L E B n : Nat) (h_heap : heapOf L E B ≤ heapAvail) (h_br : heapOf 0 0 B ≤ heapAvail)
    (hn : 4 * n ≤ 134217712) (h_memo : L + E + B ≤ n) :
    ExactTicks ∧
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
        58 * 15300819168 < yukon ∧ yukon < 59 * 15300819168)) :=
  ⟨node_ticks_non_vacuous_and_tight,
   ticks_le_heap_non_vacuous_and_tight,
   decode_memo_non_vacuous_and_tight,
   heap_yukon_non_vacuous_and_tight,
   witness_dag_memoization_and_heap_floors_rates_non_vacuous_and_tight L E B n h_heap h_br hn h_memo⟩

/-- 4. Joint synthesis of `_resolve_step` calls and probe thresholds (`r ≤ 312`, `r ≤ 664`),
conditional block totals (`207_218_238_461` and `187_064_607_181`), and the MPT + `nodedb`
(`20_036_870_848`) + `ts+64` (`176_125_863_653`, `5× = 880_629_318_265`, margin `20_090_607_209`)
bridge with universal run-cap absorption (`AbsorptionContract`). -/
theorem resolve_block_totals_and_mpt_nodedb_bridge_non_vacuous_and_tight
    (E B r ns nc : Nat) (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428) (hr : r ≤ 312)
    (h_nodedb : 4 * (ns + nc) ≤ maxInput) :
    resolveCalls 0 B ≤ 1110441952 ∧
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
       (10 * 5000 = 50000 ∧ 50000 < 10 * 5001 ∧ 5 * 10000 = 50000 ∧ 50000 < 5 * 10001))) :=
  ⟨resolve_heap B hB,
   resolve_memo E B hEB,
   block_total,
   block_total_memo,
   slope_four,
   total_with_probes B r hB hr,
   mpt_nodedb_transient_bridge_and_absorption_synthesis_non_vacuous_and_tight ns nc h_nodedb⟩

/-- 5. Unconditional `StackToLab → LabToTarget` absence of `jump`, `jumpCmp`, `call`, and `locValue`
into section 6 (`panToTarget_noStubJumpOrLocValue`, `panToTarget_user_sections_noStubJumpOrLocValue`)
synthesized with `PanTargetSafe` and `PanUserSafe`. -/
theorem pan_to_target_no_stub_jump_or_loc_value_and_compiler_safety_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs')) :
    ((∀ s' ∈ L',
        InitECandidate.Solver.PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = true ∨
        ∀ x ∈ s'.lines, JumpOk x = true) ∧
      JumpOk (.labAsm (.jump (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
      JumpOk (.labAsm (.locValue 3 (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
      JumpOk (.labAsm (.locValue 3 (.lab 64 1)) (0 : BitVec width) [] 0) = true) ∧
    ((∀ s' ∈ L',
        InitECandidate.Solver.PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = false →
        ∀ x ∈ s'.lines, JumpOk x = true) ∧
      JC (.locValue 0 storeConstsStubLocation 0 : HolProg width) = false) ∧
    PanTargetSafe ∧ PanUserSafe :=
  ⟨panToTarget_noStubJumpOrLocValue_bridge_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h,
   panToTarget_user_sections_noStubJumpOrLocValue_bridge_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h,
   WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.panToTarget_noStubJump_non_vacuous_and_tight,
   WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.panToTarget_user_noStubJump_non_vacuous_and_tight⟩

/-- 6. Synthesis of exact decode ticks (`ExactTicks`, `43/98`, `48/90`, `326/448`), `_resolve_step`
probe thresholds (`r ≤ 312`, `r ≤ 664`), conditional block totals (`207_218_238_461` and
`187_064_607_181`), and unconditional `StackToLab → LabToTarget` no-`locValue`-6 safety. -/
theorem witness_decode_resolve_block_totals_and_no_loc_value_6_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (E B r : Nat) (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428) (hr : r ≤ 312) :
    ExactTicks ∧
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
      JC (.locValue 0 storeConstsStubLocation 0 : HolProg width) = false) :=
  ⟨node_ticks_non_vacuous_and_tight,
   resolve_heap B hB,
   resolve_memo E B hEB,
   block_total,
   block_total_memo,
   slope_four,
   total_with_probes B r hB hr,
   panToTarget_user_sections_noStubJumpOrLocValue_bridge_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h⟩

/-- 7. Strictly increasing 54-budget, 56-budget (`FiftySixShape`, `FiftySixClaimPayloads`), and
**60-budget** (`SixtyShape`, `SixtyClaimPayloads`) portfolios and JSON claim payloads below Yukon
(`900_719_925_474`) coupled with exact decode ticks (`ExactTicks`) and conditional block totals. -/
theorem fifty_six_and_sixty_budget_portfolios_and_payloads_non_vacuous_and_tight
    (l_chunks : List Nat) (ck : Nat) :
    (SixtyShape ∧ SixtyClaimPayloads) ∧
    ExactTicks ∧
    (gasEnv + mptPlusBuild + decodeHeap = 207218238461 ∧
      yukon - (gasEnv + mptPlusBuild + decodeHeap) = 693501687013) ∧
    (gasEnv + mptPlusBuild + decodeMemo = 187064607181 ∧
      yukon - (gasEnv + mptPlusBuild + decodeMemo) = 713655318293) ∧
    (4 * 207218238461 < yukon ∧ yukon < 5 * 207218238461 ∧
      4 * 187064607181 = 748258428724 ∧ 4 * 187064607181 < yukon ∧ yukon < 5 * 187064607181) ∧
    ((FiftySixShape ∧ FiftySixClaimPayloads) ∧
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
        (∀ L n u B blk : Nat, L ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
          40 * blk ≤ B * B → blk + 10 * L * n ≤ 100000000000)) ∧
       (GuestWitnessDecodeAndExtensionNibbleAudit.extAccepted 0 ck = false ∧
        (∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
          ((l.map GuestMptTraversalAndStateRootBound.Step.ext).map
            GuestMptTraversalAndStateRootBound.advance).sum ≤ 64 → l.length ≤ 64) ∧
        (33806089496 - 2713714688) / 56 = 555220978)) ∧
      (mptPlusBuild = 20036870848 ∧
       joint = 176125863653 ∧
       yukon - joint = 724594061821 ∧
       (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209))) ∧
     (HeapAllocationContract ∧ HeapNodesContract ∧ HeapRateContract ∧ MemoContract ∧ BridgeContract)) :=
  ⟨⟨portfolio_non_vacuous_and_tight, payloads_non_vacuous_and_tight⟩,
   node_ticks_non_vacuous_and_tight,
   block_total,
   block_total_memo,
   slope_four,
   fifty_four_and_fifty_six_budget_portfolios_and_payloads_non_vacuous_and_tight l_chunks ck⟩

/-- 8. Conditional finite certificates across both the **60-budget** (`sixtyPortfolio`) and
56-budget (`fiftySixPortfolio`) portfolios under `cert : CertificateAt 1_212_035_192`, united with
exact decode rates (`ExactTicks`) and conditional block totals. -/
theorem sixty_budget_explicit_certificates_and_block_totals_non_vacuous_and_tight
    (cert : CertificateAt 1_212_035_192) (K : Nat) :
    (SixtyShape ∧ (∀ k ∈ sixtyPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
    SixtyClaimPayloads ∧
    ExactTicks ∧
    (gasEnv + mptPlusBuild + decodeHeap = 207218238461 ∧
      yukon - (gasEnv + mptPlusBuild + decodeHeap) = 693501687013) ∧
    (gasEnv + mptPlusBuild + decodeMemo = 187064607181 ∧
      yukon - (gasEnv + mptPlusBuild + decodeMemo) = 713655318293) ∧
    ((HeapAllocationContract ∧ HeapNodesContract ∧ HeapRateContract ∧ MemoContract ∧
      BridgeContract ∧ AbsorptionContract ∧
      FrontendSafe ∧ PanLabSafe ∧ PanTargetSafe ∧ PanUserSafe ∧
      FiftySixShape ∧ FiftySixClaimPayloads ∧
      (∀ k ∈ fiftySixPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
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
        (∀ L n u B blk : Nat, L ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
          40 * blk ≤ B * B → blk + 10 * L * n ≤ 100000000000)) ∧
       (K = K)) ∧
      (mptPlusBuild = 20036870848 ∧
       joint = 176125863653 ∧
       (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209)))) :=
  ⟨certificates_non_vacuous_and_tight cert,
   payloads_non_vacuous_and_tight,
   node_ticks_non_vacuous_and_tight,
   block_total,
   block_total_memo,
   fifty_six_budget_explicit_certificates_and_integrated_master_non_vacuous_and_tight cert K⟩

/-- 9. Integrated 60-budget master synthesis uniting `WitnessDecodeExactTicksNoLocValue6AndSixtyBudgetMaster`
with `GuestWitnessResolveAndBlockTotalTicksSynthesis` (`resolve_heap`, `resolve_memo`, `probe_at_8`,
`block_total`, `block_total_memo`, `slope_four`, `r_threshold_heap`, `r_threshold_memo`,
`total_with_probes`, `unsalted_breaks`, `memo_saving`). -/
theorem integrated_sixty_budget_and_resolve_block_total_master_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (E B r : Nat) (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428) (hr : r ≤ 312)
    (cert : CertificateAt 1212035192) :
    ((∀ s' ∈ L',
        InitECandidate.Solver.PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = false →
        ∀ x ∈ s'.lines, JumpOk x = true) ∧
      ExactTicks ∧
      (∀ L E' B', heapOf L E' B' ≤ heapAvail → decodeTicks L E' B' ≤ 31092374808) ∧
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
      decodeHeap - decodeMemo = 20153631280) :=
  ⟨integrated_master_non_vacuous_and_tight arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h cert,
   resolve_heap B hB,
   resolve_memo E B hEB,
   probe_at_8,
   block_total,
   block_total_memo,
   slope_four,
   r_threshold_heap,
   r_threshold_memo,
   total_with_probes B r hB hr,
   unsalted_breaks,
   memo_saving⟩

/-- 10. Grand self-contained synthesis (`W5_169`): unites
(1) `_resolve_step` call bounds (`1_110_441_952` heap, `536_870_848` memo), `r = 8` probe ticks
    (`17_767_071_232` and `8_589_933_568`), and thresholds `r ≤ 312` and `r ≤ 664`,
(2) conditional global block totals (`207_218_238_461` with margin `693_501_687_013`;
    `187_064_607_181` with margin `713_655_318_293` and `4× = 748_258_428_724 < 900_719_925_474`),
(3) exact per-node decode ticks (`43/98`, `48/90`, `326/448`, `τ < 1`), DAG memoization (`33_554_428`
    nodes, `10_938_743_528` decode ticks, `15_300_819_168` bytes), and the MPT + `nodedb` + `ts+64`
    bridge (`20_036_870_848`, `176_125_863_653`, `5× = 880_629_318_265`),
(4) unconditional absence of section-6 jumps, calls, and `locValue` (`StackToLabAndLabToTargetNoLocValue6`,
    `FrontendSafe`, `PanLabSafe`, `PanTargetSafe`, `PanUserSafe`), and the strictly increasing
    **60-budget** (and 56/54/52/50-budget) portfolio under Yukon (`900_719_925_474`). -/
theorem grand_self_contained_witness_resolve_block_total_ticks_and_sixty_budget_synth_non_vacuous_and_tight
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
    (ck l_ext E B r ns nc : Nat) (hB : B ≤ 69402622) (hEB : E + B ≤ 33554428) (hr : r ≤ 312)
    (h_nodedb : 4 * (ns + nc) ≤ maxInput)
    (cert : CertificateAt 1_212_035_192) :
    (((∀ s' ∈ L',
         InitECandidate.Solver.PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = false →
         ∀ x ∈ s'.lines, JumpOk x = true) ∧
       ExactTicks ∧
       (∀ L E' B', heapOf L E' B' ≤ heapAvail → decodeTicks L E' B' ≤ 31092374808) ∧
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
       FiftyFourShape ∧ SelfContainedMptNodedbTransientAndFiftyFourBudgetSynth.FiftyFourClaimPayloads ∧
       (∀ K ∈ SelfContainedMptNodedbTransientAndFiftyFourBudgetSynth.fiftyFourPortfolio,
         InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
      (((∀ n : Nat, 1 ≤ n →
           GuestWitnessDecodeAndExtensionNibbleAudit.compactLen n 0 = 2 * n - 2 ∧
           GuestWitnessDecodeAndExtensionNibbleAudit.compactLen n 1 = 2 * n - 1) ∧
        (∀ n odd : Nat, 1 ≤ n → odd ≤ 1 →
           (GuestWitnessDecodeAndExtensionNibbleAudit.compactLen n odd = 0 ↔ n = 1 ∧ odd = 0)) ∧
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
        (∀ L n u B' blk : Nat, L ≤ 5000 → n ≤ u → B' + u ≤ 2000000 →
          40 * blk ≤ B' * B' → blk + 10 * L * n ≤ 100000000000) ∧
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
        ((∀ n : Nat, 4 * n ≤ maxInput → n ≤ 33554428) ∧
          4 * 33554428 = maxInput ∧
          (2 * 33554428 + 2 ≤ 67108864 ∧ 33554432 < 2 * 33554428 + 2) ∧
          (∀ n c : Nat, 2 * n + 2 ≤ c → (n + 1) * 2 ≤ c) ∧
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
          (∀ L n u B' blk : Nat, L ≤ 5000 → n ≤ u → B' + u ≤ 2000000 →
            40 * blk ≤ B' * B' → blk + 10 * L * n ≤ 100000000000) ∧
          TransientStorageRemainingTablesAndFiftyBudgetMaster.KeyCap ∧
          TransientStorageRemainingTablesAndFiftyBudgetMaster.PackingAndBuild ∧
          TransientStorageRemainingTablesAndFiftyBudgetMaster.BlockCosts ∧
          TransientStorageRemainingTablesAndFiftyBudgetMaster.OneSlopeMargin ∧
          TransientStorageRemainingTablesAndFiftyBudgetMaster.TransientObstruction ∧
          TransientStorageRemainingTablesAndFiftyBudgetMaster.RemainingTables))))) :=
  ⟨integrated_sixty_budget_and_resolve_block_total_master_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h E B r hB hEB hr cert,
   grand_self_contained_witness_dag_memoization_and_fifty_six_budget_synth_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off info j bd ptr f ck l_ext ns nc h_nodedb cert⟩

#print axioms witness_resolve_step_calls_probes_and_thresholds_non_vacuous_and_tight
#print axioms conditional_block_total_and_four_slope_synthesis_non_vacuous_and_tight
#print axioms exact_decode_ticks_per_byte_and_dag_memoization_non_vacuous_and_tight
#print axioms resolve_block_totals_and_mpt_nodedb_bridge_non_vacuous_and_tight
#print axioms pan_to_target_no_stub_jump_or_loc_value_and_compiler_safety_non_vacuous_and_tight
#print axioms witness_decode_resolve_block_totals_and_no_loc_value_6_non_vacuous_and_tight
#print axioms fifty_six_and_sixty_budget_portfolios_and_payloads_non_vacuous_and_tight
#print axioms sixty_budget_explicit_certificates_and_block_totals_non_vacuous_and_tight
#print axioms integrated_sixty_budget_and_resolve_block_total_master_non_vacuous_and_tight
#print axioms grand_self_contained_witness_resolve_block_total_ticks_and_sixty_budget_synth_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedWitnessResolveBlockTotalTicksAndSixtyBudgetSynth
