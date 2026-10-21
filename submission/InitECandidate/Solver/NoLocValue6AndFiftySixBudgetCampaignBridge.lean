import InitECandidate.Solver.StackToLabAndLabToTargetNoLocValue6
import InitECandidate.Solver.WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster
import InitECandidate.Solver.WitnessDagMemoizationMptNodedbCampaignBridge

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.NoLocValue6AndFiftySixBudgetCampaignBridge

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.PanToLabSectionAndStackRemoveClock (IsStubLabel)
open InitECandidate.Solver.StackToLabAndLabToTargetNoLocValue6 (
  NSL
  JC
  LOk
  JumpOk
  Sec
  panToWord_NSL
  panToWordToWord_NSL
  panToLab_lines
  panToTarget_noStubJumpOrLocValue
  panToTarget_user_sections_noStubJumpOrLocValue
  jumpOk_rejects_stub_jump
  jumpOk_rejects_stub_locValue
  jumpOk_accepts_user_locValue
  jc_rejects_locValue_stub
  jc_rejects_return_into_stub
  flatten_locValue_stub_tight
  nsl_rejects_locValue_stub
  nsl_rejects_return_into_stub
  nsl_accepts_user
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
  portfolio_non_vacuous_and_tight
  payloads_non_vacuous_and_tight
  certificates_non_vacuous_and_tight
  integrated_master_non_vacuous_and_tight
)
open InitECandidate.Solver.WitnessDagMemoizationMptNodedbCampaignBridge (
  witness_per_node_heap_and_node_ceilings_non_vacuous_and_tight
  witness_heap_thresholds_and_dag_memoization_non_vacuous_and_tight
  mpt_and_nodedb_two_builds_bridge_non_vacuous_and_tight
  joint_mpt_nodedb_transient_storage_envelope_non_vacuous_and_tight
  witness_dag_memoization_and_joint_mpt_nodedb_bridge_non_vacuous_and_tight
  witness_decode_extension_nibble_and_dag_memoization_non_vacuous_and_tight
  pan_to_target_no_stub_jump_and_mpt_nodedb_bridge_non_vacuous_and_tight
  fifty_two_budget_portfolio_witness_dag_and_mpt_nodedb_synthesis_non_vacuous_and_tight
  fifty_two_budget_explicit_certificates_and_dag_mpt_nodedb_bridge_non_vacuous_and_tight
  grand_witness_dag_memoization_mpt_nodedb_and_fifty_two_budget_campaign_bridge_non_vacuous_and_tight
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
open InitECandidate.Solver.GuestNodedbAndWitnessTableBound (
  maxInput
  boundedBuild
)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.YukonVerifyScriptAudit (validFiniteClaim)

variable {width : Nat} [NeZero width]

theorem pan_to_word_to_word_nsl_and_witnesses_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) :
    (∀ y ∈ panToWordCompileProgHOL arch prog, NSL y.2.2 = true) ∧
    (∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2, NSL y.2.2 = true) ∧
    NSL (WordLangProgHOL.locValue (α := BitVec width) 0 storeConstsStubLocation) = false ∧
    NSL (WordLangProgHOL.call (α := BitVec width)
      (some ([], (.ln, .ln), .skip, storeConstsStubLocation, 0)) (some 64) [] none) = false ∧
    NSL (WordLangProgHOL.call (α := BitVec width)
      (some ([], (.ln, .ln), .locValue 1 64, 64, 0)) (some 64) [] none) = true :=
  ⟨panToWord_NSL arch prog,
   panToWordToWord_NSL arch prog wc ac,
   nsl_rejects_locValue_stub,
   nsl_rejects_return_into_stub,
   nsl_accepts_user⟩

theorem pan_to_lab_and_target_no_stub_jump_or_loc_value_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width) (sid next : Nat) (cs bs : List Nat) :
    (∀ s ∈ StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2,
      IsStubLabel s.sectionId = true ∨ LOk s.lines) ∧
    (∀ (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
        (L' : List (Sec width)) (labs' : Spt (Spt Nat)),
      removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs') →
      ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨ ∀ x ∈ s'.lines, JumpOk x = true) ∧
    JC (.locValue 0 storeConstsStubLocation 0 : HolProg width) = false ∧
    JC (.call (some (.skip, 0, storeConstsStubLocation, 0)) (.inl 64) none : HolProg width) = false ∧
    ¬ StackToLabAndLabToTargetNoLocValue6.AOk
      (StackToLab.flattenHOL false (.locValue 0 storeConstsStubLocation 0 : HolProg width)
        sid next cs bs).1 :=
  ⟨panToLab_lines arch prog wc ac perf sc dc mh sp off,
   fun ic pos labs ffis L' labs' h =>
     panToTarget_noStubJumpOrLocValue arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h,
   jc_rejects_locValue_stub,
   jc_rejects_return_into_stub,
   flatten_locValue_stub_tight sid next cs bs⟩

theorem panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width) :
    (∀ (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
        (L' : List (Sec width)) (labs' : Spt (Spt Nat)),
      removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs') →
      ∀ s' ∈ L', IsStubLabel s'.sectionId = false → ∀ x ∈ s'.lines, JumpOk x = true) ∧
    JumpOk (.labAsm (.jump (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
    JumpOk (.labAsm (.locValue 3 (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
    JumpOk (.labAsm (.locValue 3 (.lab 64 1)) (0 : BitVec width) [] 0) = true :=
  ⟨fun ic pos labs ffis L' labs' h s' hs hu =>
     panToTarget_user_sections_noStubJumpOrLocValue
       arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h s' hs hu,
   jumpOk_rejects_stub_jump,
   jumpOk_rejects_stub_locValue,
   jumpOk_accepts_user_locValue⟩

theorem witness_dag_memoization_and_heap_bounds_non_vacuous_and_tight :
    HeapAllocationContract ∧ HeapNodesContract ∧ HeapRateContract ∧ MemoContract ∧
    (heapAvail = 31092374808 ∧
     (∀ L E B n : Nat, 4 * n ≤ 134217712 → L + E + B ≤ n → L + E + B ≤ 33554428) ∧
     (448 * 33554428 + 2 * 134217712 = 15300819168 ∧ 15300819168 < heapAvail) ∧
     (58 * 15300819168 < yukon ∧ yukon < 59 * 15300819168) ∧
     2 * 15300819168 ≤ heapAvail) :=
  ⟨heap_allocation_non_vacuous_and_tight,
   heap_nodes_non_vacuous_and_tight,
   heap_rates_non_vacuous_and_tight,
   memo_non_vacuous_and_tight,
   ⟨heap_avail_val, nodes_memo, memo_heap, memo_threshold, memo_gain⟩⟩

theorem mpt_nodedb_and_transient_storage_absorption_bridge_non_vacuous_and_tight :
    BridgeContract ∧ AbsorptionContract ∧
    mptPlusBuild = 20036870848 ∧
    joint = 176125863653 ∧
    (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209) ∧
    (44 * mptPlusBuild < yukon ∧ yukon ≤ 45 * mptPlusBuild) ∧
    (∀ ns nc : Nat, 4 * (ns + nc) ≤ maxInput →
      boundedBuild 8 ns + boundedBuild 8 nc ≤ 536870848) ∧
    (∀ ns nc : Nat, 4 * (ns + nc) ≤ maxInput →
      156088992805 + 19500000000 + boundedBuild 8 ns + boundedBuild 8 nc ≤ joint) :=
  ⟨bridge_arithmetic_non_vacuous_and_tight,
   bridge_absorption_non_vacuous_and_tight,
   sum_val,
   joint_val,
   joint_five,
   sum_margin,
   two_builds_at_8,
   joint_covers⟩

theorem no_loc_value_6_and_witness_dag_memoization_bridge_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width) (ck l_ext : Nat) :
    (∀ (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
        (L' : List (Sec width)) (labs' : Spt (Spt Nat)),
      removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs') →
      (∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨ ∀ x ∈ s'.lines, JumpOk x = true) ∧
      (∀ s' ∈ L', IsStubLabel s'.sectionId = false → ∀ x ∈ s'.lines, JumpOk x = true)) ∧
    (JumpOk (.labAsm (.locValue 3 (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
     JumpOk (.labAsm (.locValue 3 (.lab 64 1)) (0 : BitVec width) [] 0) = true) ∧
    MemoContract ∧
    BridgeContract :=
  have _ := witness_decode_extension_nibble_and_dag_memoization_non_vacuous_and_tight ck l_ext
  ⟨fun ic pos labs ffis L' labs' h =>
     ⟨panToTarget_noStubJumpOrLocValue arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h,
      fun s' hs hu =>
        panToTarget_user_sections_noStubJumpOrLocValue
          arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h s' hs hu⟩,
   ⟨jumpOk_rejects_stub_locValue, jumpOk_accepts_user_locValue⟩,
   memo_non_vacuous_and_tight,
   bridge_arithmetic_non_vacuous_and_tight⟩

theorem fifty_six_budget_portfolio_and_claim_payloads_non_vacuous_and_tight :
    FiftySixShape ∧ ClaimPayloads ∧
    portfolio.length = 56 ∧ portfolio.Pairwise (· < ·) ∧
    (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    fiftySixClaims.length = 56 ∧ fiftySixClaims.map Prod.fst = portfolio ∧
    (∀ e ∈ fiftySixClaims, e.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim e.1 e.2 = true) :=
  ⟨portfolio_non_vacuous_and_tight,
   payloads_non_vacuous_and_tight,
   portfolio_non_vacuous_and_tight.1,
   portfolio_non_vacuous_and_tight.2.1,
   portfolio_non_vacuous_and_tight.2.2.1,
   payloads_non_vacuous_and_tight.1,
   payloads_non_vacuous_and_tight.2.1,
   payloads_non_vacuous_and_tight.2.2.1⟩

theorem fifty_six_budget_conditional_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    FiftySixShape ∧ ClaimPayloads ∧
    (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK 880629318265) (.finite 880629318265) ∧
    InitE.Certificate (baselineWithFiniteK 880629318266) (.finite 880629318266) :=
  ⟨portfolio_non_vacuous_and_tight,
   payloads_non_vacuous_and_tight,
   portfolio_non_vacuous_and_tight.2.2.1,
   certificates_non_vacuous_and_tight cert,
   certificates_non_vacuous_and_tight cert 880629318265 (by decide),
   certificates_non_vacuous_and_tight cert 880629318266 (by decide)⟩

theorem fifty_two_and_fifty_six_budget_campaign_synthesis_non_vacuous_and_tight
    (l_chunks : List Nat) (ck : Nat) (cert : CertificateAt 1212035192) :
    FiftySixShape ∧ ClaimPayloads ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    MemoContract ∧ BridgeContract ∧ AbsorptionContract ∧
    (heapAvail = 31092374808 ∧
     (∀ L E B : Nat, heapOf L E B ≤ heapAvail → L + E + B ≤ 345470831) ∧
     (∀ L E B n : Nat, 4 * n ≤ 134217712 → L + E + B ≤ n → L + E + B ≤ 33554428) ∧
     (448 * 33554428 + 2 * 134217712 = 15300819168 ∧ 15300819168 < heapAvail)) :=
  have h52 := fifty_two_budget_portfolio_witness_dag_and_mpt_nodedb_synthesis_non_vacuous_and_tight l_chunks ck
  ⟨portfolio_non_vacuous_and_tight,
   payloads_non_vacuous_and_tight,
   certificates_non_vacuous_and_tight cert,
   memo_non_vacuous_and_tight,
   bridge_arithmetic_non_vacuous_and_tight,
   bridge_absorption_non_vacuous_and_tight,
   ⟨h52.2.1.1, h52.2.1.2.1, h52.2.1.2.2.1, h52.2.1.2.2.2.1⟩⟩

theorem grand_no_loc_value_6_witness_dag_memoization_and_fifty_six_budget_campaign_bridge_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (ck l_ext : Nat)
    (cert : CertificateAt 1212035192) :
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
     JumpOk (.labAsm (.jump (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
     JumpOk (.labAsm (.locValue 3 (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
     JumpOk (.labAsm (.locValue 3 (.lab 64 1)) (0 : BitVec width) [] 0) = true) ∧
    (HeapAllocationContract ∧ HeapNodesContract ∧ HeapRateContract ∧ MemoContract ∧
     BridgeContract ∧ AbsorptionContract ∧
     FiftySixShape ∧ ClaimPayloads ∧
     (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
    ((∀ L E B n : Nat, 4 * n ≤ 134217712 → L + E + B ≤ n → L + E + B ≤ 33554428) ∧
     (448 * 33554428 + 2 * 134217712 = 15300819168 ∧ 15300819168 < heapAvail) ∧
     (58 * 15300819168 < yukon ∧ yukon < 59 * 15300819168) ∧
     2 * 15300819168 ≤ heapAvail ∧
     mptPlusBuild = 20036870848 ∧
     joint = 176125863653 ∧
     (5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209)) :=
  have hm := integrated_master_non_vacuous_and_tight cert
  have hg := grand_witness_dag_memoization_mpt_nodedb_and_fifty_two_budget_campaign_bridge_non_vacuous_and_tight
    arch prog wc ac perf sc dc mh sp off info j bd ptr f ck l_ext cert
  ⟨⟨panToLab_lines arch prog wc ac perf sc dc mh sp off,
    fun ic pos labs ffis L' labs' h =>
      ⟨panToTarget_noStubJumpOrLocValue arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h,
       fun s' hs hu =>
         panToTarget_user_sections_noStubJumpOrLocValue
           arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h s' hs hu⟩,
    jumpOk_rejects_stub_jump,
    jumpOk_rejects_stub_locValue,
    jumpOk_accepts_user_locValue⟩,
   ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1,
    hm.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2⟩,
   ⟨hg.1.2.2.2.2.2.2.2.2.1,
    hg.1.2.2.2.2.2.2.2.2.2.1,
    hg.1.2.2.2.2.2.2.2.2.2.2.1,
    hg.1.2.2.2.2.2.2.2.2.2.2.2,
    hg.2.1.1,
    hg.2.1.2.2.1,
    hg.2.1.2.2.2.2.1⟩⟩

#print axioms pan_to_word_to_word_nsl_and_witnesses_non_vacuous_and_tight
#print axioms pan_to_lab_and_target_no_stub_jump_or_loc_value_non_vacuous_and_tight
#print axioms panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
#print axioms witness_dag_memoization_and_heap_bounds_non_vacuous_and_tight
#print axioms mpt_nodedb_and_transient_storage_absorption_bridge_non_vacuous_and_tight
#print axioms no_loc_value_6_and_witness_dag_memoization_bridge_non_vacuous_and_tight
#print axioms fifty_six_budget_portfolio_and_claim_payloads_non_vacuous_and_tight
#print axioms fifty_six_budget_conditional_certificates_non_vacuous_and_tight
#print axioms fifty_two_and_fifty_six_budget_campaign_synthesis_non_vacuous_and_tight
#print axioms grand_no_loc_value_6_witness_dag_memoization_and_fifty_six_budget_campaign_bridge_non_vacuous_and_tight

end InitECandidate.Solver.NoLocValue6AndFiftySixBudgetCampaignBridge
