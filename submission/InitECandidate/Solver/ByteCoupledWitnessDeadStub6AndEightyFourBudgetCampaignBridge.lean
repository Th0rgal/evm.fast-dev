import InitECandidate.Solver.GuestByteCoupledWitnessResolveAndThirtyFiveXMaster
import InitECandidate.Solver.StackRemoveDeadStub6AndEightyTwoBudgetCampaignBridge
import InitECandidate.Solver.SaltedNodedbTwentySevenXAndEightyFourBudgetMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.ByteCoupledWitnessDeadStub6AndEightyFourBudgetCampaignBridge

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (NoStubCall Clean)
open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock (CodeNoSt ClockOk)
open InitECandidate.Solver.StackRemoveInitMemoryAndCompileProgZeroExtraBodyClock (
  noSt_initStubs
  initCode_clock_preserved
  storeConstsStub_not_noSt
)
open InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt (
  stackAllocSections
  liveSections
  stackAllocSections_clean
  stackAllocSections_noSt_and_noStubCall
  liveTable_lookup_noSt
  codeNoSt_liveTable
  codeNoSt_liveTable_emptyOracle
  liveTable_lookup_six
  panToStackRemove_body_zeroExtraClock_liveTable
  fullTable_has_label6
)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.GuestOpcodeTableCountAndAllTablesSaltedMaster (
  main200AllSalted
  main380AllSalted
)
open InitECandidate.Solver.GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit (
  decodeMemo
  probesR8
  buildNodedb
  walks
  rootTicks
  witnessMptSalted
  postEvmSalted
)
open InitECandidate.Solver.GuestByteCoupledWitnessResolveAndThirtyFiveXMaster (
  inputBytes
  hashRefs
  probes
  main200
  main380
  refs_bound
  refs_tight
  ratio
  probe_vals
  gain
  main200_slope
  main380_slope
  margins
  decode_dominates
  tree_no_coupling
)
open InitECandidate.Solver.SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster (
  clockOk_rejects_non_vacuous_and_tight
)
open InitECandidate.Solver.OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster (
  EightyTwoShape
)
open InitECandidate.Solver.StackRemoveDeadStub6AndEightyTwoBudgetCampaignBridge (
  stack_alloc_sections_clean_and_full_table_label6_non_vacuous_and_tight
  live_table_lookup_six_and_unconditional_code_no_st_non_vacuous_and_tight
  pan_to_stack_remove_body_zero_extra_clock_live_table_non_vacuous_and_tight
  init_memory_zero_clock_and_live_table_body_simulation_bridge_non_vacuous_and_tight
  opcode_table_count_all_salted_main200_and_main380_slopes_non_vacuous_and_tight
  block_salted_vs_all_tables_salted_and_slack_synthesis_non_vacuous_and_tight
  eighty_two_and_eighty_budget_portfolio_hierarchy_non_vacuous_and_tight
  eighty_two_budget_conditional_certificates_and_endpoints_non_vacuous_and_tight
  dead_stub6_live_table_all_salted_slopes_and_eighty_two_budget_certificates_non_vacuous_and_tight
  grand_stack_remove_dead_stub6_all_salted_and_eighty_two_budget_campaign_bridge_non_vacuous_and_tight
)
open InitECandidate.Solver.SaltedNodedbTwentySevenXAndEightyFourBudgetMaster (
  portfolio
  EightyFourShape
  dissect_and_probes_salted_non_vacuous_and_tight
  visit_cost_and_rows_200_non_vacuous_and_tight
  wm_vals_and_post_val_non_vacuous_and_tight
  dominant_and_r1_lever_non_vacuous_and_tight
  eighty_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  eighty_four_budget_certificates_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

variable {width : Nat} [NeZero width]

/-- 1. Byte-coupled 33-byte hash-reference ceiling (`refs_bound`, `refs_tight`), call-count ratio
(`ratio`), and tree-decode comparison (`tree_no_coupling`). -/
theorem byte_coupled_refs_bound_tight_and_ratio_non_vacuous_and_tight
    (h : Nat) (hb : 33 * h ≤ inputBytes) :
    h ≤ 4067203 ∧
    (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) ∧
    (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs) ∧
    (2 * 8 * hashRefs < 2 * 8 * 1110441952) :=
  ⟨refs_bound h hb, refs_tight, ratio, tree_no_coupling⟩

/-- 2. Byte-coupled resolve probe ticks (`probe_vals`), tick savings (`gain`), and `decodeMemo`
share (`decode_dominates`). -/
theorem byte_coupled_probe_vals_gain_and_decode_dominates_non_vacuous_and_tight :
    (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
      probes 380000000 = 68115248) ∧
    (8589933568 - probes 200000000 = 8523258320) ∧
    (100 * 10938743528 > 44 * main200) :=
  ⟨probe_vals, gain, decode_dominates⟩

/-- 3. Byte-coupled `main200 = 24,381,873,932` (`36×` passes, `37×` fails),
`main380 = 32,488,958,762` (`27×` passes, `28×` fails), and exact Yukon `margins`. -/
theorem byte_coupled_main200_36x_and_main380_27x_slopes_and_margins_non_vacuous_and_tight :
    (main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200) ∧
    (main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380) ∧
    (yukon - 36 * main200 = 22972463922 ∧ yukon - 27 * main380 = 23518038900) :=
  ⟨main200_slope, main380_slope, margins⟩

/-- 4. Progression from all-tables salted (`18×` / `16×`), through salted `nodedb`/MPT (`27×` / `21×`),
to byte-coupled witness resolve (`36×` / `27×`). -/
theorem salted_nodedb_to_byte_coupled_witness_progression_non_vacuous_and_tight :
    ((decodeMemo + probesR8 + (20036870848 - 619060000) = 38946487944 ∧
      probesR8 = 8589933568) ∧
     (probesR8 = 2 * 8 * (16 * 33554428))) ∧
    ((witnessMptSalted 200000000 = 26801608212 ∧
      witnessMptSalted 380000000 = 30612453042) ∧
     (postEvmSalted = 681400462)) ∧
    (main200AllSalted = 49228478172 ∧ 18 * main200AllSalted < yukon ∧
      yukon < 19 * main200AllSalted) ∧
    (main380AllSalted = 53523278172 ∧ 16 * main380AllSalted < yukon ∧
      yukon < 17 * main380AllSalted) ∧
    (GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200 = 32905132252 ∧
      27 * GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200 < yukon ∧
      yukon < 28 * GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200) ∧
    (main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200) ∧
    (main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380) :=
  ⟨dissect_and_probes_salted_non_vacuous_and_tight,
   wm_vals_and_post_val_non_vacuous_and_tight,
   opcode_table_count_all_salted_main200_and_main380_slopes_non_vacuous_and_tight.2.2.1,
   opcode_table_count_all_salted_main200_and_main380_slopes_non_vacuous_and_tight.2.2.2,
   SaltedNodedbTwentySevenXAndEightyFourBudgetMaster.main200_slope_non_vacuous_and_tight,
   main200_slope,
   main380_slope⟩

/-- 5. Dead stub 6 (`stackAllocSections_clean`, `liveTable_lookup_six`, `fullTable_has_label6`)
unified with byte-coupled witness resolve bounds (`refs_bound`, `refs_tight`, `main200_slope`,
`main380_slope`). -/
theorem dead_stub6_clean_sections_and_byte_coupled_witness_bridge_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (h k : Nat) (hb : 33 * h ≤ inputBytes) :
    ((∀ e ∈ stackAllocSections arch prog wc ac perf dc,
       e.1 = storeConstsStubLocation ∨ Clean e.2 = true) ∧
     (∀ e ∈ stackAllocSections arch prog wc ac perf dc, e.1 ≠ storeConstsStubLocation →
       StackNoSt e.2 = true ∧ NoStubCall e.2 = true ∧ Clean e.2 = true) ∧
     ((∃ e ∈ stackAllocSections arch prog wc ac perf dc, e.1 = storeConstsStubLocation) ∧
      sptLookup storeConstsStubLocation
        (sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc))) = none) ∧
     StackNoSt (storeConstsStubNative (width := width) k) = false) ∧
    (h ≤ 4067203 ∧ (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204)) ∧
    (main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200) ∧
    (main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380) :=
  ⟨stack_alloc_sections_clean_and_full_table_label6_non_vacuous_and_tight arch prog wc ac perf dc k,
   ⟨refs_bound h hb, refs_tight⟩,
   main200_slope,
   main380_slope⟩

/-- 6. `panToStackRemove_body_zeroExtraClock_liveTable` and `initCode_clock_preserved` unified with
byte-coupled `probe_vals`, `gain`, `margins`, and `decode_dominates`. -/
theorem live_table_zero_extra_clock_and_byte_coupled_margins_bridge_non_vacuous_and_tight {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (generateGc : Bool) (maximumHeap pointer start k : Nat) :
    ((∀ e ∈ initStubs (width := width) generateGc maximumHeap pointer start, StackNoSt e.2 = true) ∧
     (∀ (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
       StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, s) = (r, t) →
       t.clock = s.clock) ∧
     (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
         (panToWordCompileProgHOL arch prog)).2).2.2.2,
       y.1 = storeConstsStubLocation ∨
       ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
         (postSource target : StackSemStateFiniteExact width C F)
         (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
         source.code = sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc)) →
         (∀ i, ∀ e ∈ (source.compileOracle i).2.1, StackNoSt e.2 = true) →
         StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
             (result, postSource) ∧ result ≠ some .error ∧
           StackRemove.stateRelHOL j bd ptr source target ∧
           StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr →
         ∃ clock postTarget, ClockOk clock result ∧
           StackSemEvaluate.evaluate (StackRemove.comp j bd ptr
             (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
             {target with clock := clock + target.clock}) = (result, postTarget)) ∧
     StackNoSt (storeConstsStubNative (width := width) k) = false) ∧
    (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧ probes 380000000 = 68115248) ∧
    (8589933568 - probes 200000000 = 8523258320) ∧
    (yukon - 36 * main200 = 22972463922 ∧ yukon - 27 * main380 = 23518038900) ∧
    (100 * 10938743528 > 44 * main200) :=
  ⟨init_memory_zero_clock_and_live_table_body_simulation_bridge_non_vacuous_and_tight
     arch prog wc ac perf dc info generateGc maximumHeap pointer start k,
   probe_vals,
   gain,
   margins,
   decode_dominates⟩

/-- 7. Strictly increasing 84-budget portfolio (`EightyFourShape`), all `< 900_719_925_474`,
extending the 82-budget campaign hierarchy (`EightyTwoShape`). -/
theorem eighty_four_and_eighty_two_budget_portfolio_hierarchy_non_vacuous_and_tight :
    EightyFourShape ∧
    portfolio.length = 84 ∧
    portfolio.Pairwise (· < ·) ∧
    (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    portfolio.drop 82 = [880629318293, 880629318294] ∧
    portfolio.getLast? = some 880629318294 ∧
    EightyTwoShape :=
  have h84 := eighty_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  have h82 := eighty_two_and_eighty_budget_portfolio_hierarchy_non_vacuous_and_tight
  ⟨h84,
   h84.1,
   h84.2.1,
   h84.2.2.1,
   h84.2.2.2.2.1,
   h84.2.2.2.2.2.1,
   h82.1⟩

/-- 8. Conditional finite certificates `InitE.Certificate (baselineWithFiniteK K) (.finite K)` across
all 84 budgets, with explicit endpoint certificates at `880_629_318_293` and `880_629_318_294`. -/
theorem eighty_four_budget_conditional_certificates_and_endpoints_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    EightyFourShape ∧
    (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK 880629318293) (.finite 880629318293) ∧
    InitE.Certificate (baselineWithFiniteK 880629318294) (.finite 880629318294) :=
  have hcert := eighty_four_budget_certificates_non_vacuous_and_tight cert
  ⟨hcert.1,
   hcert.1.2.2.1,
   hcert.2,
   hcert.2 880629318293 (by decide),
   hcert.2 880629318294 (by decide)⟩

/-- 9. Synthesis of `GuestByteCoupledWitnessResolveAndThirtyFiveXMaster` (`refs_bound`, `refs_tight`,
`ratio`, `probe_vals`, `gain`, `main200_slope`, `main380_slope`, `margins`, `decode_dominates`)
with the 84-budget conditional certificate portfolio. -/
theorem byte_coupled_witness_thirty_five_x_and_eighty_four_budget_certificates_non_vacuous_and_tight
    (h : Nat) (hb : 33 * h ≤ inputBytes) (cert : CertificateAt 1212035192) :
    h ≤ 4067203 ∧
    (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) ∧
    (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs) ∧
    (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
      probes 380000000 = 68115248) ∧
    (8589933568 - probes 200000000 = 8523258320) ∧
    (main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200) ∧
    (main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380) ∧
    (yukon - 36 * main200 = 22972463922 ∧ yukon - 27 * main380 = 23518038900) ∧
    (100 * 10938743528 > 44 * main200) ∧
    (EightyFourShape ∧
      ∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨refs_bound h hb,
   refs_tight,
   ratio,
   probe_vals,
   gain,
   main200_slope,
   main380_slope,
   margins,
   decode_dominates,
   eighty_four_budget_certificates_non_vacuous_and_tight cert⟩

/-- 10. Grand campaign bridge unifying `GuestByteCoupledWitnessResolveAndThirtyFiveXMaster`,
`StackRemoveDeadStub6AndEightyTwoBudgetCampaignBridge`, and
`SaltedNodedbTwentySevenXAndEightyFourBudgetMaster`. -/
theorem grand_byte_coupled_witness_dead_stub6_and_eighty_four_budget_campaign_bridge_non_vacuous_and_tight
    {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (generateGc : Bool) (maximumHeap pointer start k_stub h : Nat)
    (hb : 33 * h ≤ inputBytes)
    (w : WordLocW width) (cert : CertificateAt 1212035192) :
    (h ≤ 4067203 ∧
     (33 * 4067203 ≤ inputBytes ∧ inputBytes < 33 * 4067204) ∧
     (132 * hashRefs ≤ 16 * 33554428 ∧ 16 * 33554428 < 133 * hashRefs) ∧
     (2 * 8 * hashRefs = 65075248 ∧ probes 200000000 = 66675248 ∧
       probes 380000000 = 68115248) ∧
     (8589933568 - probes 200000000 = 8523258320) ∧
     (main200 = 24381873932 ∧ 36 * main200 < yukon ∧ yukon < 37 * main200) ∧
     (main380 = 32488958762 ∧ 27 * main380 < yukon ∧ yukon < 28 * main380) ∧
     (yukon - 36 * main200 = 22972463922 ∧ yukon - 27 * main380 = 23518038900) ∧
     (100 * 10938743528 > 44 * main200)) ∧
    ((∀ e ∈ stackAllocSections arch prog wc ac perf dc,
       e.1 = storeConstsStubLocation ∨ Clean e.2 = true) ∧
     (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
         (panToWordCompileProgHOL arch prog)).2).2.2.2,
       y.1 = storeConstsStubLocation ∨
       ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
         (postSource target : StackSemStateFiniteExact width C F)
         (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
         source.code = sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc)) →
         (∀ i, ∀ e ∈ (source.compileOracle i).2.1, StackNoSt e.2 = true) →
         StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
             (result, postSource) ∧ result ≠ some .error ∧
           StackRemove.stateRelHOL j bd ptr source target ∧
           StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr →
         ∃ clock postTarget, ClockOk clock result ∧
           StackSemEvaluate.evaluate (StackRemove.comp j bd ptr
             (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
             {target with clock := clock + target.clock}) = (result, postTarget)) ∧
     ((∃ e ∈ stackAllocSections arch prog wc ac perf dc, e.1 = storeConstsStubLocation) ∧
      sptLookup storeConstsStubLocation
        (sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc))) = none) ∧
     (∀ e ∈ initStubs (width := width) generateGc maximumHeap pointer start, StackNoSt e.2 = true) ∧
     (∀ (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
       StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, s) = (r, t) →
       t.clock = s.clock) ∧
     StackNoSt (storeConstsStubNative (width := width) k_stub) = false ∧
     (¬ ClockOk (width := width) 1 none ∧ ¬ ClockOk 2 (some (.halt w)))) ∧
    (EightyTwoShape ∧
     EightyFourShape ∧
     portfolio.length = 84 ∧
     portfolio.Pairwise (· < ·) ∧
     (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
     (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) :=
  have hcert84 := eighty_four_budget_certificates_non_vacuous_and_tight cert
  have hg82 := grand_stack_remove_dead_stub6_all_salted_and_eighty_two_budget_campaign_bridge_non_vacuous_and_tight
    (C := C) (F := F) arch prog wc ac perf dc info generateGc maximumHeap pointer start k_stub w cert
  ⟨⟨refs_bound h hb,
    refs_tight,
    ratio,
    probe_vals,
    gain,
    main200_slope,
    main380_slope,
    margins,
    decode_dominates⟩,
   hg82.1,
   ⟨hg82.2.2.2.1,
    hcert84.1,
    hcert84.1.1,
    hcert84.1.2.1,
    hcert84.1.2.2.1,
    hcert84.2⟩⟩

#print axioms byte_coupled_refs_bound_tight_and_ratio_non_vacuous_and_tight
#print axioms byte_coupled_probe_vals_gain_and_decode_dominates_non_vacuous_and_tight
#print axioms byte_coupled_main200_36x_and_main380_27x_slopes_and_margins_non_vacuous_and_tight
#print axioms salted_nodedb_to_byte_coupled_witness_progression_non_vacuous_and_tight
#print axioms dead_stub6_clean_sections_and_byte_coupled_witness_bridge_non_vacuous_and_tight
#print axioms live_table_zero_extra_clock_and_byte_coupled_margins_bridge_non_vacuous_and_tight
#print axioms eighty_four_and_eighty_two_budget_portfolio_hierarchy_non_vacuous_and_tight
#print axioms eighty_four_budget_conditional_certificates_and_endpoints_non_vacuous_and_tight
#print axioms byte_coupled_witness_thirty_five_x_and_eighty_four_budget_certificates_non_vacuous_and_tight
#print axioms grand_byte_coupled_witness_dead_stub6_and_eighty_four_budget_campaign_bridge_non_vacuous_and_tight

end InitECandidate.Solver.ByteCoupledWitnessDeadStub6AndEightyFourBudgetCampaignBridge
