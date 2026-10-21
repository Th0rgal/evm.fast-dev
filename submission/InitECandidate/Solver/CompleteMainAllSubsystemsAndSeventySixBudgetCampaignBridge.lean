import InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster
import InitECandidate.Solver.NoLocValue6AndFiftySixBudgetCampaignBridge
import InitECandidate.Solver.WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.CompleteMainAllSubsystemsAndSeventySixBudgetCampaignBridge

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
  system_gas
  wd_row
  rest_val
  main_val
  main_slopes
  env380_val
  main380_val
  main380_slopes
  heap_4x_fails
  bal_bound
  env_dominates
)
open InitECandidate.Solver.NoLocValue6AndFiftySixBudgetCampaignBridge (
  pan_to_word_to_word_nsl_and_witnesses_non_vacuous_and_tight
  pan_to_lab_and_target_no_stub_jump_or_loc_value_non_vacuous_and_tight
  witness_dag_memoization_and_heap_bounds_non_vacuous_and_tight
  mpt_nodedb_and_transient_storage_absorption_bridge_non_vacuous_and_tight
  fifty_six_budget_portfolio_and_claim_payloads_non_vacuous_and_tight
  fifty_six_budget_conditional_certificates_non_vacuous_and_tight
)
open InitECandidate.Solver.WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster (
  FiftySixShape
  ClaimPayloads
)
open InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound (nwdMax r1 r4)
open InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit (wdTicks)
open InitECandidate.Solver.WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster (
  portfolio
  SeventySixShape
  ssz_no_cap_non_vacuous_and_tight
  linear_val_non_vacuous_and_tight
  close_1x_salted_non_vacuous_and_tight
  unsalted_thresholds_non_vacuous_and_tight
  nmax_4x_non_vacuous_and_tight
  spec_cap_closes_non_vacuous_and_tight
  seventy_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  seventy_six_budget_certificates_non_vacuous_and_tight
  withdrawals_ssz_limit_main_closure_and_seventy_six_budget_master_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

variable {width : Nat} [NeZero width]

/-- 1. Complete subsystem breakdown and `main200 = 200,485,906,743` under 200M gas budget. -/
theorem complete_main_200m_subsystems_and_margins_non_vacuous_and_tight :
    (132000 * 16 + 8 * (16 * 15) = withdrawals16) ∧
    (restTerms = 5450425994) ∧
    (main200 = 200485906743) ∧
    (yukon - main200 = 700234018731 ∧ 4 * main200 < yukon ∧
      yukon / 4 - main200 = 24694074625 ∧ yukon < 5 * main200) ∧
    (100 * gasEnv200 ≥ 77 * main200) :=
  ⟨wd_row, rest_val, main_val, main_slopes, env_dominates⟩

/-- 2. System calls gas accounting (6 × 30M) and `main380 = 511,966,000,267` under 380M gas budget. -/
theorem complete_main_380m_adversarial_system_code_and_margins_non_vacuous_and_tight :
    (2 + 4 = 6 ∧ 200000000 + 6 * 30000000 = 380000000) ∧
    (gasEnv380 = 467569086329) ∧
    (main380 = 511966000267) ∧
    (yukon - main380 = 388753925207 ∧ yukon < 2 * main380) ∧
    (yukon < 4 * (gasEnv200 + 68277256888 + restTerms)) :=
  ⟨system_gas, env380_val, main380_val, main380_slopes, heap_4x_fails⟩

/-- 3. BAL merge-sort / RLP bound at 380M gas combined with 200M and 380M main totals. -/
theorem bal_rlp_cold_keys_and_dual_main_envelopes_non_vacuous_and_tight
    (k : Nat) (hk : 2000 * k ≤ 380000000) :
    (k ≤ 190000 ∧ 2 * 18 * 40 * 190000 ≤ balRlp) ∧
    (main200 = 200485906743 ∧ yukon - main200 = 700234018731 ∧
      yukon / 4 - main200 = 24694074625) ∧
    (main380 = 511966000267 ∧ yukon - main380 = 388753925207 ∧ yukon < 2 * main380) :=
  ⟨bal_bound k hk,
   ⟨main_val, main_slopes.1, main_slopes.2.2.1⟩,
   ⟨main380_val, main380_slopes.1, main380_slopes.2⟩⟩

/-- 4. Complete safety of user sections after `LabToTarget` (`panToTarget_user_sections_noStubJumpOrLocValue`). -/
theorem panToTarget_user_sections_noStubJumpOrLocValue_complete_bridge_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width) :
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
    JumpOk (.labAsm (.jump (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
    JumpOk (.labAsm (.locValue 3 (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
    JumpOk (.labAsm (.locValue 3 (.lab 64 1)) (0 : BitVec width) [] 0) = true :=
  ⟨panToLab_lines arch prog wc ac perf sc dc mh sp off,
   fun ic pos labs ffis L' labs' h =>
     ⟨panToTarget_noStubJumpOrLocValue arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h,
      fun s' hs hu =>
        panToTarget_user_sections_noStubJumpOrLocValue
          arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h s' hs hu⟩,
   jumpOk_rejects_stub_jump,
   jumpOk_rejects_stub_locValue,
   jumpOk_accepts_user_locValue⟩

/-- 5. User-section `NoLocValue 6` safety unified with 200M/380M main subsystem synthesis. -/
theorem user_sections_no_stub_jump_and_dual_main_synthesis_non_vacuous_and_tight
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
    (JumpOk (.labAsm (.locValue 3 (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
     JumpOk (.labAsm (.locValue 3 (.lab 64 1)) (0 : BitVec width) [] 0) = true) ∧
    (main200 = 200485906743 ∧ yukon - main200 = 700234018731 ∧
      yukon / 4 - main200 = 24694074625) ∧
    (main380 = 511966000267 ∧ yukon - main380 = 388753925207) :=
  ⟨fun ic pos labs ffis L' labs' h s' hs hu =>
     panToTarget_user_sections_noStubJumpOrLocValue
       arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h s' hs hu,
   ⟨jumpOk_rejects_stub_locValue, jumpOk_accepts_user_locValue⟩,
   ⟨main_val, main_slopes.1, main_slopes.2.2.1⟩,
   ⟨main380_val, main380_slopes.1⟩⟩

/-- 6. Withdrawals SSZ limit closure (`n ≤ 16`) unified with `withdrawals16` and `main200` / `main380`. -/
theorem withdrawals_ssz_limit_and_complete_main_closure_non_vacuous_and_tight
    (n : Nat) (hn : n ≤ 16) :
    (nwdMax ≤ 9223372036854775807 ∧ 16 < nwdMax) ∧
    (132000 * nwdMax = 44291808000) ∧
    (wdTicks 0 nwdMax ≤ r1 ∧ r1 - wdTicks 0 nwdMax = 626933565707) ∧
    (wdTicks 0 189516 ≤ r4 ∧ r4 < wdTicks 0 189517) ∧
    (wdTicks 8 n ≤ wdTicks 8 16 ∧ wdTicks 8 16 ≤ r4 ∧ r4 - wdTicks 8 16 = 25014084625) ∧
    (132000 * 16 + 8 * (16 * 15) = withdrawals16 ∧ main200 = 200485906743 ∧ main380 = 511966000267) :=
  ⟨ssz_no_cap_non_vacuous_and_tight,
   linear_val_non_vacuous_and_tight,
   close_1x_salted_non_vacuous_and_tight,
   nmax_4x_non_vacuous_and_tight,
   spec_cap_closes_non_vacuous_and_tight n hn,
   ⟨wd_row, main_val, main380_val⟩⟩

/-- 7. Strictly increasing 76-budget portfolio all `< 900_719_925_474` and 56-budget campaign bridge. -/
theorem seventy_six_and_fifty_six_budget_portfolio_hierarchy_non_vacuous_and_tight :
    SeventySixShape ∧
    portfolio.length = 76 ∧
    portfolio.Pairwise (· < ·) ∧
    (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    FiftySixShape ∧
    ClaimPayloads :=
  ⟨seventy_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   seventy_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.1,
   seventy_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.1,
   seventy_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1,
   fifty_six_budget_portfolio_and_claim_payloads_non_vacuous_and_tight.1,
   fifty_six_budget_portfolio_and_claim_payloads_non_vacuous_and_tight.2.1⟩

/-- 8. Conditional finite certificates `InitE.Certificate (baselineWithFiniteK K) (.finite K)` across all 76 budgets. -/
theorem seventy_six_budget_conditional_certificates_and_anchors_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    SeventySixShape ∧
    (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK 880629318285) (.finite 880629318285) ∧
    InitE.Certificate (baselineWithFiniteK 880629318286) (.finite 880629318286) :=
  have hcert := seventy_six_budget_certificates_non_vacuous_and_tight cert
  ⟨hcert.1,
   hcert.1.2.2.1,
   hcert.2,
   hcert.2 880629318285 (by decide),
   hcert.2 880629318286 (by decide)⟩

/-- 9. Synthesis of 200M/380M `main` envelopes with the 76-budget conditional certificate portfolio. -/
theorem dual_main_envelopes_and_seventy_six_budget_certificates_non_vacuous_and_tight
    (k : Nat) (hk : 2000 * k ≤ 380000000) (cert : CertificateAt 1212035192) :
    (main200 = 200485906743 ∧ yukon - main200 = 700234018731 ∧
      4 * main200 < yukon ∧ yukon / 4 - main200 = 24694074625 ∧ yukon < 5 * main200) ∧
    (main380 = 511966000267 ∧ yukon - main380 = 388753925207 ∧ yukon < 2 * main380) ∧
    (k ≤ 190000 ∧ 2 * 18 * 40 * 190000 ≤ balRlp) ∧
    SeventySixShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  have hcert := seventy_six_budget_certificates_non_vacuous_and_tight cert
  ⟨⟨main_val, main_slopes.1, main_slopes.2.1, main_slopes.2.2.1, main_slopes.2.2.2⟩,
   ⟨main380_val, main380_slopes.1, main380_slopes.2⟩,
   bal_bound k hk,
   hcert.1,
   hcert.2⟩

/-- 10. Grand campaign bridge unifying `GuestCompleteMainAllSubsystemsSynthesisMaster`,
`NoLocValue6AndFiftySixBudgetCampaignBridge`, and
`WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster`. -/
theorem grand_complete_main_all_subsystems_no_loc_value_6_and_seventy_six_budget_campaign_bridge_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (n k : Nat) (hn : n ≤ 16) (hk : 2000 * k ≤ 380000000)
    (cert : CertificateAt 1212035192) :
    ((main200 = 200485906743 ∧ yukon - main200 = 700234018731 ∧
       4 * main200 < yukon ∧ yukon / 4 - main200 = 24694074625 ∧ yukon < 5 * main200) ∧
     (gasEnv380 = 467569086329 ∧ main380 = 511966000267 ∧
       yukon - main380 = 388753925207 ∧ yukon < 2 * main380) ∧
     (k ≤ 190000 ∧ 2 * 18 * 40 * 190000 ≤ balRlp) ∧
     (wdTicks 8 n ≤ wdTicks 8 16 ∧ wdTicks 8 16 ≤ r4 ∧ r4 - wdTicks 8 16 = 25014084625)) ∧
    ((∀ (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
        (L' : List (Sec width)) (labs' : Spt (Spt Nat)),
      removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs') →
      (∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨ ∀ x ∈ s'.lines, JumpOk x = true) ∧
      (∀ s' ∈ L', IsStubLabel s'.sectionId = false → ∀ x ∈ s'.lines, JumpOk x = true)) ∧
     JumpOk (.labAsm (.jump (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
     JumpOk (.labAsm (.locValue 3 (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
     JumpOk (.labAsm (.locValue 3 (.lab 64 1)) (0 : BitVec width) [] 0) = true) ∧
    (SeventySixShape ∧
     portfolio.length = 76 ∧
     portfolio.Pairwise (· < ·) ∧
     (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
     (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) :=
  have hcert := seventy_six_budget_certificates_non_vacuous_and_tight cert
  ⟨⟨⟨main_val, main_slopes.1, main_slopes.2.1, main_slopes.2.2.1, main_slopes.2.2.2⟩,
    ⟨env380_val, main380_val, main380_slopes.1, main380_slopes.2⟩,
    bal_bound k hk,
    spec_cap_closes_non_vacuous_and_tight n hn⟩,
   ⟨fun ic pos labs ffis L' labs' h =>
      ⟨panToTarget_noStubJumpOrLocValue arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h,
       fun s' hs hu =>
         panToTarget_user_sections_noStubJumpOrLocValue
           arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h s' hs hu⟩,
    jumpOk_rejects_stub_jump,
    jumpOk_rejects_stub_locValue,
    jumpOk_accepts_user_locValue⟩,
   ⟨hcert.1,
    hcert.1.1,
    hcert.1.2.1,
    hcert.1.2.2.1,
    hcert.2⟩⟩

#print axioms complete_main_200m_subsystems_and_margins_non_vacuous_and_tight
#print axioms complete_main_380m_adversarial_system_code_and_margins_non_vacuous_and_tight
#print axioms bal_rlp_cold_keys_and_dual_main_envelopes_non_vacuous_and_tight
#print axioms panToTarget_user_sections_noStubJumpOrLocValue_complete_bridge_non_vacuous_and_tight
#print axioms user_sections_no_stub_jump_and_dual_main_synthesis_non_vacuous_and_tight
#print axioms withdrawals_ssz_limit_and_complete_main_closure_non_vacuous_and_tight
#print axioms seventy_six_and_fifty_six_budget_portfolio_hierarchy_non_vacuous_and_tight
#print axioms seventy_six_budget_conditional_certificates_and_anchors_non_vacuous_and_tight
#print axioms dual_main_envelopes_and_seventy_six_budget_certificates_non_vacuous_and_tight
#print axioms grand_complete_main_all_subsystems_no_loc_value_6_and_seventy_six_budget_campaign_bridge_non_vacuous_and_tight

end InitECandidate.Solver.CompleteMainAllSubsystemsAndSeventySixBudgetCampaignBridge
