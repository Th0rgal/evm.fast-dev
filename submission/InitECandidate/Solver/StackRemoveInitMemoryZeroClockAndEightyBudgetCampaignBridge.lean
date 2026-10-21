import InitECandidate.Solver.StackRemoveInitMemoryAndCompileProgZeroExtraBodyClock
import InitECandidate.Solver.SaltedLinearGasAndSeventyEightBudgetCampaignBridge
import InitECandidate.Solver.SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.StackRemoveInitMemoryZeroClockAndEightyBudgetCampaignBridge

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock (CodeNoSt ClockOk)
open InitECandidate.Solver.StackRemoveInitMemoryAndCompileProgZeroExtraBodyClock (
  noSt_initMemory
  noSt_initCode
  noSt_initStubs
  initStubs_labels
  storeConstsStubLocation_eq
  initCode_clock_preserved
  initCode_clock_independent
  stackRemoveCompile_sections_noSt
  storeConstsStub_not_noSt
  compileNative_has_stub6
  pancake_stackRemove_compileProg_zeroExtraBodyClock
)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster (
  gasEnv200
  witnessMpt
  postEvm
  prologue
  withdrawals16
  balRlp
  requests
  output
  restTerms
  main200
  gasEnv380
  main380
)
open InitECandidate.Solver.GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster (
  saltedTable
  salted200
  salted380
  per_unit
  quad_vs_lin
  salted_env
  salted200_val
  salted380_val
  slope200
  slope380
  salt_gain
  per_unit_slack
  unsalted_cmp
)
open InitECandidate.Solver.CompleteMainAllSubsystemsAndSeventyEightBudgetMaster (
  SeventyEightShape
)
open InitECandidate.Solver.SaltedLinearGasAndSeventyEightBudgetCampaignBridge (
  salted_linear_gas_envelope_and_quad_vs_lin_non_vacuous_and_tight
  salted200_and_salted380_totals_and_slopes_non_vacuous_and_tight
  salted_per_unit_slack_and_salt_gain_non_vacuous_and_tight
  main_subsystem_table_system_gas_bal_and_salted_envelopes_non_vacuous_and_tight
  seventy_eight_and_seventy_six_budget_portfolio_hierarchy_non_vacuous_and_tight
  seventy_eight_budget_conditional_certificates_and_endpoints_non_vacuous_and_tight
  salted_linear_gas_envelopes_and_seventy_eight_budget_certificates_non_vacuous_and_tight
)
open InitECandidate.Solver.SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster (
  portfolio
  EightyShape
  panToStackAlloc_bodies_StackNoSt_non_vacuous_and_tight
  panToStackRemove_body_zeroExtraClock_non_vacuous_and_tight
  clockOk_rejects_non_vacuous_and_tight
  main_subsystem_table_non_vacuous_and_tight
  bal_bound_non_vacuous_and_tight
  eighty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  eighty_budget_certificates_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

variable {width : Nat} [NeZero width]

/-- 1. `noSt_initStubs`, `initStubs_labels`, `storeConstsStubLocation_eq`, and tightness witness
`storeConstsStub_not_noSt`. -/
theorem init_stubs_no_store_consts_and_stub6_exception_non_vacuous_and_tight
    (generateGc : Bool) (maximumHeap pointer start k : Nat)
    (values : List (Sum (BitVec width) Nat)) :
    StackNoSt (initMemory pointer values) = true ∧
    StackNoSt (initCode (width := width) generateGc maximumHeap pointer) = true ∧
    (∀ e ∈ initStubs (width := width) generateGc maximumHeap pointer start, StackNoSt e.2 = true) ∧
    (initStubs (width := width) generateGc maximumHeap pointer start).map Prod.fst = [0, 1, 2] ∧
    storeConstsStubLocation = 6 ∧
    StackNoSt (storeConstsStubNative (width := width) k) = false :=
  ⟨noSt_initMemory pointer values,
   noSt_initCode generateGc maximumHeap pointer,
   noSt_initStubs generateGc maximumHeap pointer start,
   initStubs_labels generateGc maximumHeap pointer start,
   storeConstsStubLocation_eq,
   storeConstsStub_not_noSt k⟩

/-- 2. `initCode_clock_preserved` (`t.clock = s.clock`), `initCode_clock_independent`, and `ClockOk`
tightness witnesses. -/
theorem init_code_clock_preserved_and_clock_ok_witnesses_non_vacuous_and_tight {C F : Type}
    (generateGc : Bool) (maximumHeap pointer clock : Nat)
    (w : WordLocW width) :
    (∀ (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, s) = (r, t) →
      t.clock = s.clock) ∧
    (∀ (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, s) = (r, t) →
      StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, {s with clock := clock}) =
        (r, {t with clock := clock})) ∧
    (¬ ClockOk (width := width) 1 none ∧ ¬ ClockOk 2 (some (.halt w))) :=
  ⟨fun s t r h => initCode_clock_preserved generateGc maximumHeap pointer s t r h,
   fun s t r h => initCode_clock_independent generateGc maximumHeap pointer s t r clock h,
   clockOk_rejects_non_vacuous_and_tight w⟩

/-- 3. `stackRemoveCompile_sections_noSt` on the real `StackToLab` stack pipeline together with
tightness witnesses `storeConstsStub_not_noSt` and `compileNative_has_stub6`. -/
theorem stack_remove_compile_sections_no_st_and_stub6_witness_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (jump : Bool) (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maximumHeap pointer start k : Nat) :
    (∀ e ∈ StackRemove.compileHOL jump bounds generateGc maximumHeap pointer start
        (StackAlloc.compile dc (StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)),
      e.1 = storeConstsStubLocation ∨ StackNoSt e.2 = true) ∧
    StackNoSt (storeConstsStubNative (width := width) k) = false ∧
    (storeConstsStubLocation, storeConstsStubNative (ac.regCount - (5 + ac.avoidRegs.length))) ∈
      (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2 :=
  ⟨stackRemoveCompile_sections_noSt arch prog wc ac perf dc jump bounds generateGc maximumHeap pointer start,
   storeConstsStub_not_noSt k,
   compileNative_has_stub6 ac perf (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2⟩

/-- 4. `pancake_stackRemove_compileProg_zeroExtraBodyClock` unified with `storeConstsStub_not_noSt`
and `clockOk_rejects_non_vacuous_and_tight`. -/
theorem pancake_stack_remove_compile_prog_zero_extra_body_clock_master_non_vacuous_and_tight {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (jump : Bool) (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maximumHeap pointer start k : Nat) (w : WordLocW width) :
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
    StackNoSt (storeConstsStubNative (width := width) k) = false ∧
    (¬ ClockOk (width := width) 1 none ∧ ¬ ClockOk 2 (some (.halt w))) :=
  ⟨pancake_stackRemove_compileProg_zeroExtraBodyClock
     arch prog wc ac perf dc info jump bounds generateGc maximumHeap pointer start,
   storeConstsStub_not_noSt k,
   clockOk_rejects_non_vacuous_and_tight w⟩

/-- 5. Salted linear gas envelopes (`salted200 = 102,485,906,743` passing `8×` Yukon,
`salted380 = 154,766,000,267` passing `5×` Yukon) and `per_unit_slack`. -/
theorem salted_linear_gas_200m_8x_and_380m_5x_envelopes_non_vacuous_and_tight :
    (60 * 8 * 2 ≤ 1000) ∧
    (salted200 = 102485906743 ∧
      8 * 102485906743 < yukon ∧ yukon - 8 * 102485906743 = 80832671530 ∧
      yukon < 9 * 102485906743) ∧
    (salted380 = 154766000267 ∧
      5 * 154766000267 < yukon ∧ yukon - 5 * 154766000267 = 126889924139 ∧
      yukon < 6 * 154766000267) ∧
    (100000000000 - 2000000000 = 98000000000 ∧
      361000000000 - 3800000000 = 357200000000) ∧
    (8 * (200485906743 - 100000000000 + 6052 * 2000000) < yukon ∧
      yukon < 8 * (200485906743 - 100000000000 + 6053 * 2000000) ∧
      5 * (511966000267 - 361000000000 + 7678 * 3800000) < yukon ∧
      yukon < 5 * (511966000267 - 361000000000 + 7679 * 3800000)) :=
  ⟨per_unit,
   ⟨salted200_val, slope200.1, slope200.2.1, slope200.2.2⟩,
   ⟨salted380_val, slope380.1, slope380.2.1, slope380.2.2⟩,
   salt_gain,
   per_unit_slack⟩

/-- 6. Bridge between `StackRemove` initializer/body zero extra clock and the salted linear gas
envelopes (`salted200` at `8×` Yukon, `salted380` at `5×` Yukon). -/
theorem stack_remove_init_memory_zero_clock_and_salted_linear_gas_bridge_non_vacuous_and_tight {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (jump : Bool) (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maximumHeap pointer start k : Nat) :
    (∀ e ∈ initStubs (width := width) generateGc maximumHeap pointer start, StackNoSt e.2 = true) ∧
    (∀ (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, s) = (r, t) →
      t.clock = s.clock) ∧
    (∀ e ∈ StackRemove.compileHOL jump bounds generateGc maximumHeap pointer start
        (StackAlloc.compile dc (StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)),
      e.1 = storeConstsStubLocation ∨ StackNoSt e.2 = true) ∧
    StackNoSt (storeConstsStubNative (width := width) k) = false ∧
    (salted200 = 102485906743 ∧ 8 * 102485906743 < yukon ∧
      yukon - 8 * 102485906743 = 80832671530 ∧ yukon < 9 * 102485906743) ∧
    (salted380 = 154766000267 ∧ 5 * 154766000267 < yukon ∧
      yukon - 5 * 154766000267 = 126889924139 ∧ yukon < 6 * 154766000267) :=
  ⟨noSt_initStubs generateGc maximumHeap pointer start,
   fun s t r h => initCode_clock_preserved generateGc maximumHeap pointer s t r h,
   stackRemoveCompile_sections_noSt arch prog wc ac perf dc jump bounds generateGc maximumHeap pointer start,
   storeConstsStub_not_noSt k,
   ⟨salted200_val, slope200.1, slope200.2.1, slope200.2.2⟩,
   ⟨salted380_val, slope380.1, slope380.2.1, slope380.2.2⟩⟩

/-- 7. Strictly increasing 80-budget portfolio (`EightyShape`), all `< 900_719_925_474`, extending
the 78-budget campaign hierarchy. -/
theorem eighty_and_seventy_eight_budget_portfolio_hierarchy_non_vacuous_and_tight :
    EightyShape ∧
    portfolio.length = 80 ∧
    portfolio.Pairwise (· < ·) ∧
    (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    portfolio.drop 78 = [880629318289, 880629318290] ∧
    portfolio.getLast? = some 880629318290 ∧
    SeventyEightShape :=
  have h80 := eighty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  have h78 := seventy_eight_and_seventy_six_budget_portfolio_hierarchy_non_vacuous_and_tight
  ⟨h80,
   h80.1,
   h80.2.1,
   h80.2.2.1,
   h80.2.2.2.2.1,
   h80.2.2.2.2.2.1,
   h78.1⟩

/-- 8. Conditional finite certificates `InitE.Certificate (baselineWithFiniteK K) (.finite K)` across
all 80 budgets, with explicit endpoint certificates at `880_629_318_289` and `880_629_318_290`. -/
theorem eighty_budget_conditional_certificates_and_endpoints_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    EightyShape ∧
    (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK 880629318289) (.finite 880629318289) ∧
    InitE.Certificate (baselineWithFiniteK 880629318290) (.finite 880629318290) :=
  have hcert := eighty_budget_certificates_non_vacuous_and_tight cert
  ⟨hcert.1,
   hcert.1.2.2.1,
   hcert.2,
   hcert.2 880629318289 (by decide),
   hcert.2 880629318290 (by decide)⟩

/-- 9. Synthesis of salted linear gas envelopes (`salted200`, `salted380`, `slope200`, `slope380`),
complete subsystem table, and the 80-budget conditional certificate portfolio. -/
theorem salted_linear_gas_subsystems_and_eighty_budget_certificates_non_vacuous_and_tight
    (k : Nat) (hk : 2000 * k ≤ 380000000) (cert : CertificateAt 1212035192) :
    (gasEnv200 = 156088992805 ∧ witnessMpt = 38946487944 ∧
      postEvm = 4859866650 ∧ prologue = 268435424 ∧
      withdrawals16 = 2113920 ∧ balRlp = 300000000 ∧ requests = 20000000 ∧
      output = 10000 ∧ restTerms = 5450425994 ∧
      main200 = gasEnv200 + witnessMpt + postEvm + prologue + withdrawals16 +
        balRlp + requests + output) ∧
    (k ≤ 190000 ∧ 2 * 18 * 40 * 190000 ≤ balRlp ∧ balRlp = 300000000) ∧
    (salted200 = 102485906743 ∧ 8 * 102485906743 < yukon ∧
      yukon - 8 * 102485906743 = 80832671530 ∧ yukon < 9 * 102485906743) ∧
    (salted380 = 154766000267 ∧ 5 * 154766000267 < yukon ∧
      yukon - 5 * 154766000267 = 126889924139 ∧ yukon < 6 * 154766000267) ∧
    (EightyShape ∧
      ∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨main_subsystem_table_non_vacuous_and_tight,
   bal_bound_non_vacuous_and_tight k hk,
   ⟨salted200_val, slope200.1, slope200.2.1, slope200.2.2⟩,
   ⟨salted380_val, slope380.1, slope380.2.1, slope380.2.2⟩,
   eighty_budget_certificates_non_vacuous_and_tight cert⟩

/-- 10. Grand campaign bridge unifying `StackRemoveInitMemoryAndCompileProgZeroExtraBodyClock`,
`SaltedLinearGasAndSeventyEightBudgetCampaignBridge`, and
`SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster`. -/
theorem grand_stack_remove_init_memory_zero_clock_salted_linear_gas_and_eighty_budget_campaign_bridge_non_vacuous_and_tight
    {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (jump : Bool) (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maximumHeap pointer start k_stub k_bal : Nat) (hk : 2000 * k_bal ≤ 380000000)
    (w : WordLocW width) (cert : CertificateAt 1212035192) :
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
             {target with clock := clock + target.clock}) = (result, postTarget)) ∧
     StackNoSt (storeConstsStubNative (width := width) k_stub) = false ∧
     (¬ ClockOk (width := width) 1 none ∧ ¬ ClockOk 2 (some (.halt w)))) ∧
    ((60 * 8 * 2 ≤ 1000) ∧
     (salted200 = 102485906743 ∧ 8 * 102485906743 < yukon ∧
       yukon - 8 * 102485906743 = 80832671530 ∧ yukon < 9 * 102485906743) ∧
     (salted380 = 154766000267 ∧ 5 * 154766000267 < yukon ∧
       yukon - 5 * 154766000267 = 126889924139 ∧ yukon < 6 * 154766000267) ∧
     (k_bal ≤ 190000 ∧ 2 * 18 * 40 * 190000 ≤ balRlp ∧ balRlp = 300000000)) ∧
    (SeventyEightShape ∧
     EightyShape ∧
     portfolio.length = 80 ∧
     portfolio.Pairwise (· < ·) ∧
     (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
     (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) :=
  have hcert80 := eighty_budget_certificates_non_vacuous_and_tight cert
  have hm := pancake_stackRemove_compileProg_zeroExtraBodyClock
    (C := C) (F := F) arch prog wc ac perf dc info jump bounds generateGc maximumHeap pointer start
  ⟨⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2,
    storeConstsStub_not_noSt k_stub,
    clockOk_rejects_non_vacuous_and_tight w⟩,
   ⟨per_unit,
    ⟨salted200_val, slope200.1, slope200.2.1, slope200.2.2⟩,
    ⟨salted380_val, slope380.1, slope380.2.1, slope380.2.2⟩,
    bal_bound_non_vacuous_and_tight k_bal hk⟩,
   ⟨seventy_eight_and_seventy_six_budget_portfolio_hierarchy_non_vacuous_and_tight.1,
    hcert80.1,
    hcert80.1.1,
    hcert80.1.2.1,
    hcert80.1.2.2.1,
    hcert80.2⟩⟩

#print axioms init_stubs_no_store_consts_and_stub6_exception_non_vacuous_and_tight
#print axioms init_code_clock_preserved_and_clock_ok_witnesses_non_vacuous_and_tight
#print axioms stack_remove_compile_sections_no_st_and_stub6_witness_non_vacuous_and_tight
#print axioms pancake_stack_remove_compile_prog_zero_extra_body_clock_master_non_vacuous_and_tight
#print axioms salted_linear_gas_200m_8x_and_380m_5x_envelopes_non_vacuous_and_tight
#print axioms stack_remove_init_memory_zero_clock_and_salted_linear_gas_bridge_non_vacuous_and_tight
#print axioms eighty_and_seventy_eight_budget_portfolio_hierarchy_non_vacuous_and_tight
#print axioms eighty_budget_conditional_certificates_and_endpoints_non_vacuous_and_tight
#print axioms salted_linear_gas_subsystems_and_eighty_budget_certificates_non_vacuous_and_tight
#print axioms grand_stack_remove_init_memory_zero_clock_salted_linear_gas_and_eighty_budget_campaign_bridge_non_vacuous_and_tight

end InitECandidate.Solver.StackRemoveInitMemoryZeroClockAndEightyBudgetCampaignBridge
