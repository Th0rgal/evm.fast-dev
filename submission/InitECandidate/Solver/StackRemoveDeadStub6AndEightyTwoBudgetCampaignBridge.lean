import InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt
import InitECandidate.Solver.StackRemoveInitMemoryZeroClockAndEightyBudgetCampaignBridge
import InitECandidate.Solver.OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.StackRemoveDeadStub6AndEightyTwoBudgetCampaignBridge

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
  stackRemoveCompile_sections_noSt
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
  liveTable_lookup_eq
  liveTable_lookup_six
  panToStackRemove_body_zeroExtraClock_liveTable
  fullTable_has_label6
)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster (
  salted200
  salted380
  salted200_val
  salted380_val
  slope200
  slope380
)
open InitECandidate.Solver.GuestOpcodeTableCountAndAllTablesSaltedMaster (
  opTicks
  unitTicks
  env200
  env380
  restMain
  main200AllSalted
  main380AllSalted
)
open InitECandidate.Solver.SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster (
  EightyShape
  clockOk_rejects_non_vacuous_and_tight
)
open InitECandidate.Solver.StackRemoveInitMemoryZeroClockAndEightyBudgetCampaignBridge (
  init_stubs_no_store_consts_and_stub6_exception_non_vacuous_and_tight
  init_code_clock_preserved_and_clock_ok_witnesses_non_vacuous_and_tight
  stack_remove_compile_sections_no_st_and_stub6_witness_non_vacuous_and_tight
  pancake_stack_remove_compile_prog_zero_extra_body_clock_master_non_vacuous_and_tight
  salted_linear_gas_200m_8x_and_380m_5x_envelopes_non_vacuous_and_tight
  eighty_and_seventy_eight_budget_portfolio_hierarchy_non_vacuous_and_tight
)
open InitECandidate.Solver.OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster (
  portfolio
  EightyTwoShape
  finds_max_and_unit_val_non_vacuous_and_tight
  env_split_and_vals_non_vacuous_and_tight
  main200_slope_non_vacuous_and_tight
  main380_slope_non_vacuous_and_tight
  unit_slack_non_vacuous_and_tight
  run_slack_non_vacuous_and_tight
  gain_non_vacuous_and_tight
  rest_dominates_non_vacuous_and_tight
  eighty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  eighty_two_budget_certificates_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

variable {width : Nat} [NeZero width]

/-- 1. `stackAllocSections_clean`, `stackAllocSections_noSt_and_noStubCall`, and tightness witness
`fullTable_has_label6` (`∃ e ∈ stackAllocSections …, e.1 = 6` while `liveTable_lookup_six = none`). -/
theorem stack_alloc_sections_clean_and_full_table_label6_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (k : Nat) :
    (∀ e ∈ stackAllocSections arch prog wc ac perf dc,
      e.1 = storeConstsStubLocation ∨ Clean e.2 = true) ∧
    (∀ e ∈ stackAllocSections arch prog wc ac perf dc, e.1 ≠ storeConstsStubLocation →
      StackNoSt e.2 = true ∧ NoStubCall e.2 = true ∧ Clean e.2 = true) ∧
    ((∃ e ∈ stackAllocSections arch prog wc ac perf dc, e.1 = storeConstsStubLocation) ∧
     sptLookup storeConstsStubLocation
       (sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc))) = none) ∧
    StackNoSt (storeConstsStubNative (width := width) k) = false :=
  ⟨stackAllocSections_clean arch prog wc ac perf dc,
   stackAllocSections_noSt_and_noStubCall arch prog wc ac perf dc,
   fullTable_has_label6 arch prog wc ac perf dc,
   storeConstsStub_not_noSt k⟩

/-- 2. `liveTable_lookup_noSt`, `liveTable_lookup_six`, `codeNoSt_liveTable`, and
`codeNoSt_liveTable_emptyOracle` with tightness witness `fullTable_has_label6`. -/
theorem live_table_lookup_six_and_unconditional_code_no_st_non_vacuous_and_tight {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (l : List (Nat × HolProg width)) :
    (∀ k p, sptLookup k (sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc))) = some p →
      StackNoSt p = true ∧ Clean p = true) ∧
    sptLookup storeConstsStubLocation (sptFromAList (liveSections l)) = none ∧
    (∀ (s : StackSemStateFiniteExact width C F),
      s.code = sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc)) →
      (∀ i, ∀ e ∈ (s.compileOracle i).2.1, StackNoSt e.2 = true) →
      CodeNoSt s) ∧
    (∀ (s : StackSemStateFiniteExact width C F),
      s.code = sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc)) →
      (∀ i, (s.compileOracle i).2.1 = []) →
      CodeNoSt s) ∧
    ((∃ e ∈ stackAllocSections arch prog wc ac perf dc, e.1 = storeConstsStubLocation) ∧
     sptLookup storeConstsStubLocation
       (sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc))) = none) :=
  ⟨liveTable_lookup_noSt arch prog wc ac perf dc,
   liveTable_lookup_six l,
   fun s hc ho => codeNoSt_liveTable arch prog wc ac perf dc s hc ho,
   fun s hc ho => codeNoSt_liveTable_emptyOracle arch prog wc ac perf dc s hc ho,
   fullTable_has_label6 arch prog wc ac perf dc⟩

/-- 3. `panToStackRemove_body_zeroExtraClock_liveTable` (no external `CodeNoSt` hypothesis on
the static code table) paired with `fullTable_has_label6` and `ClockOk` tightness witnesses. -/
theorem pan_to_stack_remove_body_zero_extra_clock_live_table_non_vacuous_and_tight {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (w : WordLocW width) :
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
    (¬ ClockOk (width := width) 1 none ∧ ¬ ClockOk 2 (some (.halt w))) :=
  ⟨panToStackRemove_body_zeroExtraClock_liveTable arch prog wc ac perf dc info,
   fullTable_has_label6 arch prog wc ac perf dc,
   clockOk_rejects_non_vacuous_and_tight w⟩

/-- 4. Bridge unifying `initCode_clock_preserved`, `noSt_initStubs`, and
`panToStackRemove_body_zeroExtraClock_liveTable`. -/
theorem init_memory_zero_clock_and_live_table_body_simulation_bridge_non_vacuous_and_tight {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (generateGc : Bool) (maximumHeap pointer start k : Nat) :
    (∀ e ∈ initStubs (width := width) generateGc maximumHeap pointer start, StackNoSt e.2 = true) ∧
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
    StackNoSt (storeConstsStubNative (width := width) k) = false :=
  ⟨noSt_initStubs generateGc maximumHeap pointer start,
   fun s t r h => initCode_clock_preserved generateGc maximumHeap pointer s t r h,
   panToStackRemove_body_zeroExtraClock_liveTable arch prog wc ac perf dc info,
   storeConstsStub_not_noSt k⟩

/-- 5. All-tables salted opcode table count bounds (`finds_max_and_unit_val`, `env_split_and_vals`,
`main200_slope` at `18×/19×` Yukon, and `main380_slope` at `16×/17×` Yukon). -/
theorem opcode_table_count_all_salted_main200_and_main380_slopes_non_vacuous_and_tight :
    ((1 + 2 + 2 + 2 = 7 ∧ 1 ≤ 7 ∧ 3 ≤ 7 ∧ 1 + 5 ≤ 7) ∧
      (opTicks 8 = 28 ∧ unitTicks = 336)) ∧
    ((3659564234 + 500000000 + 151929428571 = 156088992805 ∧
      151929428571 = 100000000000 + 51929428571) ∧
      (env200 = 4831564234 ∧ env380 = 9126364234)) ∧
    (main200AllSalted = 49228478172 ∧ 18 * main200AllSalted < yukon ∧
      yukon < 19 * main200AllSalted) ∧
    (main380AllSalted = 53523278172 ∧ 16 * main380AllSalted < yukon ∧
      yukon < 17 * main380AllSalted) :=
  ⟨finds_max_and_unit_val_non_vacuous_and_tight,
   env_split_and_vals_non_vacuous_and_tight,
   main200_slope_non_vacuous_and_tight,
   main380_slope_non_vacuous_and_tight⟩

/-- 6. Comparison and slack synthesis between block-salted (`salted200` at `8×`, `salted380` at `5×`)
and all-tables salted (`main200AllSalted` at `18×`, `main380AllSalted` at `16×`), including
`unit_slack`, `run_slack`, `gain`, and `rest_dominates`. -/
theorem block_salted_vs_all_tables_salted_and_slack_synthesis_non_vacuous_and_tight :
    (salted200 = 102485906743 ∧ 8 * 102485906743 < yukon ∧ yukon < 9 * 102485906743) ∧
    (salted380 = 154766000267 ∧ 5 * 154766000267 < yukon ∧ yukon < 6 * 154766000267) ∧
    (main200AllSalted = 49228478172 ∧ 18 * main200AllSalted < yukon ∧
      yukon < 19 * main200AllSalted) ∧
    (main380AllSalted = 53523278172 ∧ 16 * main380AllSalted < yukon ∧
      yukon < 17 * main380AllSalted) ∧
    (102485906743 - 49228478172 = 53257428571 ∧
      154766000267 - 53523278172 = 101242722095) ∧
    (12 * opTicks 24 ≤ 741 ∧ 741 < 12 * opTicks 25) ∧
    (restMain = 44396913938 ∧ 10 * restMain > 9 * main200AllSalted) ∧
    (18 * (3659564234 + 500000000 + 741 * 2000000 + restMain) < yukon ∧
      yukon ≤ 18 * (3659564234 + 500000000 + 742 * 2000000 + restMain) ∧
      16 * (59564234 + 18 * 380000000 + 950000000 + 1065 * 3800000 + restMain) < yukon ∧
      yukon ≤ 16 * (59564234 + 18 * 380000000 + 950000000 + 1066 * 3800000 + restMain)) :=
  ⟨⟨salted200_val, slope200.1, slope200.2.2⟩,
   ⟨salted380_val, slope380.1, slope380.2.2⟩,
   main200_slope_non_vacuous_and_tight,
   main380_slope_non_vacuous_and_tight,
   gain_non_vacuous_and_tight,
   run_slack_non_vacuous_and_tight,
   rest_dominates_non_vacuous_and_tight,
   unit_slack_non_vacuous_and_tight⟩

/-- 7. Strictly increasing 82-budget portfolio (`EightyTwoShape`), all `< 900_719_925_474`,
extending the 80-budget campaign hierarchy (`EightyShape`). -/
theorem eighty_two_and_eighty_budget_portfolio_hierarchy_non_vacuous_and_tight :
    EightyTwoShape ∧
    portfolio.length = 82 ∧
    portfolio.Pairwise (· < ·) ∧
    (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    portfolio.drop 80 = [880629318291, 880629318292] ∧
    portfolio.getLast? = some 880629318292 ∧
    EightyShape :=
  have h82 := eighty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  have h80 := eighty_and_seventy_eight_budget_portfolio_hierarchy_non_vacuous_and_tight
  ⟨h82,
   h82.1,
   h82.2.1,
   h82.2.2.1,
   h82.2.2.2.2.1,
   h82.2.2.2.2.2.1,
   h80.1⟩

/-- 8. Conditional finite certificates `InitE.Certificate (baselineWithFiniteK K) (.finite K)` across
all 82 budgets, with explicit endpoint certificates at `880_629_318_291` and `880_629_318_292`. -/
theorem eighty_two_budget_conditional_certificates_and_endpoints_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    EightyTwoShape ∧
    (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK 880629318291) (.finite 880629318291) ∧
    InitE.Certificate (baselineWithFiniteK 880629318292) (.finite 880629318292) :=
  have hcert := eighty_two_budget_certificates_non_vacuous_and_tight cert
  ⟨hcert.1,
   hcert.1.2.2.1,
   hcert.2,
   hcert.2 880629318291 (by decide),
   hcert.2 880629318292 (by decide)⟩

/-- 9. Synthesis of `StackRemoveDeadStub6AndUnconditionalCodeNoSt` with `main200_slope`,
`main380_slope`, and the 82-budget conditional certificate portfolio. -/
theorem dead_stub6_live_table_all_salted_slopes_and_eighty_two_budget_certificates_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (cert : CertificateAt 1212035192) :
    (∀ e ∈ stackAllocSections arch prog wc ac perf dc,
      e.1 = storeConstsStubLocation ∨ Clean e.2 = true) ∧
    ((∃ e ∈ stackAllocSections arch prog wc ac perf dc, e.1 = storeConstsStubLocation) ∧
     sptLookup storeConstsStubLocation
       (sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc))) = none) ∧
    (main200AllSalted = 49228478172 ∧ 18 * main200AllSalted < yukon ∧
      yukon < 19 * main200AllSalted) ∧
    (main380AllSalted = 53523278172 ∧ 16 * main380AllSalted < yukon ∧
      yukon < 17 * main380AllSalted) ∧
    (EightyTwoShape ∧
      ∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨stackAllocSections_clean arch prog wc ac perf dc,
   fullTable_has_label6 arch prog wc ac perf dc,
   main200_slope_non_vacuous_and_tight,
   main380_slope_non_vacuous_and_tight,
   eighty_two_budget_certificates_non_vacuous_and_tight cert⟩

/-- 10. Grand campaign bridge unifying `StackRemoveDeadStub6AndUnconditionalCodeNoSt`,
`StackRemoveInitMemoryZeroClockAndEightyBudgetCampaignBridge`, and
`OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster`. -/
theorem grand_stack_remove_dead_stub6_all_salted_and_eighty_two_budget_campaign_bridge_non_vacuous_and_tight
    {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (generateGc : Bool) (maximumHeap pointer start k_stub : Nat)
    (w : WordLocW width) (cert : CertificateAt 1212035192) :
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
    ((salted200 = 102485906743 ∧ 8 * 102485906743 < yukon ∧ yukon < 9 * 102485906743) ∧
     (salted380 = 154766000267 ∧ 5 * 154766000267 < yukon ∧ yukon < 6 * 154766000267) ∧
     (main200AllSalted = 49228478172 ∧ 18 * main200AllSalted < yukon ∧
       yukon < 19 * main200AllSalted) ∧
     (main380AllSalted = 53523278172 ∧ 16 * main380AllSalted < yukon ∧
       yukon < 17 * main380AllSalted)) ∧
    (EightyShape ∧
     EightyTwoShape ∧
     portfolio.length = 82 ∧
     portfolio.Pairwise (· < ·) ∧
     (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
     (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) :=
  have hcert82 := eighty_two_budget_certificates_non_vacuous_and_tight cert
  ⟨⟨stackAllocSections_clean arch prog wc ac perf dc,
    panToStackRemove_body_zeroExtraClock_liveTable arch prog wc ac perf dc info,
    fullTable_has_label6 arch prog wc ac perf dc,
    noSt_initStubs generateGc maximumHeap pointer start,
    fun s t r h => initCode_clock_preserved generateGc maximumHeap pointer s t r h,
    storeConstsStub_not_noSt k_stub,
    clockOk_rejects_non_vacuous_and_tight w⟩,
   ⟨⟨salted200_val, slope200.1, slope200.2.2⟩,
    ⟨salted380_val, slope380.1, slope380.2.2⟩,
    main200_slope_non_vacuous_and_tight,
    main380_slope_non_vacuous_and_tight⟩,
   ⟨eighty_and_seventy_eight_budget_portfolio_hierarchy_non_vacuous_and_tight.1,
    hcert82.1,
    hcert82.1.1,
    hcert82.1.2.1,
    hcert82.1.2.2.1,
    hcert82.2⟩⟩

#print axioms stack_alloc_sections_clean_and_full_table_label6_non_vacuous_and_tight
#print axioms live_table_lookup_six_and_unconditional_code_no_st_non_vacuous_and_tight
#print axioms pan_to_stack_remove_body_zero_extra_clock_live_table_non_vacuous_and_tight
#print axioms init_memory_zero_clock_and_live_table_body_simulation_bridge_non_vacuous_and_tight
#print axioms opcode_table_count_all_salted_main200_and_main380_slopes_non_vacuous_and_tight
#print axioms block_salted_vs_all_tables_salted_and_slack_synthesis_non_vacuous_and_tight
#print axioms eighty_two_and_eighty_budget_portfolio_hierarchy_non_vacuous_and_tight
#print axioms eighty_two_budget_conditional_certificates_and_endpoints_non_vacuous_and_tight
#print axioms dead_stub6_live_table_all_salted_slopes_and_eighty_two_budget_certificates_non_vacuous_and_tight
#print axioms grand_stack_remove_dead_stub6_all_salted_and_eighty_two_budget_campaign_bridge_non_vacuous_and_tight

end InitECandidate.Solver.StackRemoveDeadStub6AndEightyTwoBudgetCampaignBridge
