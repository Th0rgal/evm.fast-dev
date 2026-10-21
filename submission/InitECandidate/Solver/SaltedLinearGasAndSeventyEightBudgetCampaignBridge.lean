import InitECandidate.Solver.GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster
import InitECandidate.Solver.CompleteMainAllSubsystemsAndSeventySixBudgetCampaignBridge
import InitECandidate.Solver.CompleteMainAllSubsystemsAndSeventyEightBudgetMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.SaltedLinearGasAndSeventyEightBudgetCampaignBridge

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
  LOk
  JumpOk
  Sec
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
open InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit (wdTicks)
open InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound (nwdMax r1 r4)
open InitECandidate.Solver.WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster (
  SeventySixShape
)
open InitECandidate.Solver.CompleteMainAllSubsystemsAndSeventySixBudgetCampaignBridge (
  complete_main_200m_subsystems_and_margins_non_vacuous_and_tight
  complete_main_380m_adversarial_system_code_and_margins_non_vacuous_and_tight
  bal_rlp_cold_keys_and_dual_main_envelopes_non_vacuous_and_tight
  panToTarget_user_sections_noStubJumpOrLocValue_complete_bridge_non_vacuous_and_tight
  user_sections_no_stub_jump_and_dual_main_synthesis_non_vacuous_and_tight
  withdrawals_ssz_limit_and_complete_main_closure_non_vacuous_and_tight
  seventy_six_and_fifty_six_budget_portfolio_hierarchy_non_vacuous_and_tight
  seventy_six_budget_conditional_certificates_and_anchors_non_vacuous_and_tight
  dual_main_envelopes_and_seventy_six_budget_certificates_non_vacuous_and_tight
  grand_complete_main_all_subsystems_no_loc_value_6_and_seventy_six_budget_campaign_bridge_non_vacuous_and_tight
)
open InitECandidate.Solver.CompleteMainAllSubsystemsAndSeventyEightBudgetMaster (
  portfolio
  SeventyEightShape
  main_subsystem_table_non_vacuous_and_tight
  system_gas_non_vacuous_and_tight
  main200_non_vacuous_and_tight
  main200_margins_non_vacuous_and_tight
  main380_non_vacuous_and_tight
  main380_margins_non_vacuous_and_tight
  bal_bound_non_vacuous_and_tight
  seventy_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  seventy_eight_budget_certificates_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

variable {width : Nat} [NeZero width]

/-- 1. Per-unit table charge (`60 * 8 * 2 ≤ 1000`), quadratic vs. salted linear terms (`quad_vs_lin`),
and salted gas envelopes (`salted_env`). -/
theorem salted_linear_gas_envelope_and_quad_vs_lin_non_vacuous_and_tight :
    (60 * 8 * 2 ≤ 1000) ∧
    (2000000 * 2000000 / 40 = 100000000000 ∧ saltedTable 2000000 = 2000000000 ∧
      3800000 * 3800000 / 40 = 361000000000 ∧ saltedTable 3800000 = 3800000000) ∧
    (156088992805 - 100000000000 + 2000000000 = 58088992805 ∧
      467569086329 - 361000000000 + 3800000000 = 110369086329) ∧
    (100000000000 - 2000000000 = 98000000000 ∧
      361000000000 - 3800000000 = 357200000000) :=
  ⟨per_unit, quad_vs_lin, salted_env, salt_gain⟩

/-- 2. Salted `main200` and `main380` totals (`salted200_val`, `salted380_val`) with `8×` / `5×`
Yukon slopes (`slope200`, `slope380`) and unsalted comparison (`unsalted_cmp`). -/
theorem salted200_and_salted380_totals_and_slopes_non_vacuous_and_tight :
    (salted200 = 102485906743) ∧
    (salted380 = 154766000267) ∧
    (8 * 102485906743 < yukon ∧ yukon - 8 * 102485906743 = 80832671530 ∧
      yukon < 9 * 102485906743) ∧
    (5 * 154766000267 < yukon ∧ yukon - 5 * 154766000267 = 126889924139 ∧
      yukon < 6 * 154766000267) ∧
    (4 * main200 < yukon ∧ yukon < 5 * main200 ∧ yukon < 2 * main380) :=
  ⟨salted200_val, salted380_val, slope200, slope380, unsalted_cmp⟩

/-- 3. Per-unit slack thresholds (`6052/6053` at `8×` 200M and `7678/7679` at `5×` 380M)
unified with `salt_gain` and `per_unit`. -/
theorem salted_per_unit_slack_and_salt_gain_non_vacuous_and_tight :
    (60 * 8 * 2 ≤ 1000) ∧
    (100000000000 - 2000000000 = 98000000000 ∧
      361000000000 - 3800000000 = 357200000000) ∧
    (8 * (200485906743 - 100000000000 + 6052 * 2000000) < yukon ∧
      yukon < 8 * (200485906743 - 100000000000 + 6053 * 2000000) ∧
      5 * (511966000267 - 361000000000 + 7678 * 3800000) < yukon ∧
      yukon < 5 * (511966000267 - 361000000000 + 7679 * 3800000)) :=
  ⟨per_unit, salt_gain, per_unit_slack⟩

/-- 4. Complete `main_subsystem_table`, `system_gas`, and `bal_bound` unified with salted and unsalted
`main200` / `main380` envelopes. -/
theorem main_subsystem_table_system_gas_bal_and_salted_envelopes_non_vacuous_and_tight
    (k : Nat) (hk : 2000 * k ≤ 380000000) :
    (gasEnv200 = 156088992805 ∧ witnessMpt = 38946487944 ∧
      postEvm = 4859866650 ∧ prologue = 268435424 ∧
      withdrawals16 = 2113920 ∧ balRlp = 300000000 ∧ requests = 20000000 ∧
      output = 10000 ∧ restTerms = 5450425994 ∧
      main200 = gasEnv200 + witnessMpt + postEvm + prologue + withdrawals16 +
        balRlp + requests + output) ∧
    (2 + 4 = 6 ∧ 200000000 + 6 * 30000000 = 380000000) ∧
    (k ≤ 190000 ∧ 2 * 18 * 40 * 190000 ≤ balRlp ∧ balRlp = 300000000) ∧
    (main200 = 200485906743 ∧ salted200 = 102485906743) ∧
    (gasEnv380 = 467569086329 ∧ main380 = 511966000267 ∧ salted380 = 154766000267) :=
  ⟨main_subsystem_table_non_vacuous_and_tight,
   system_gas_non_vacuous_and_tight,
   bal_bound_non_vacuous_and_tight k hk,
   ⟨main200_non_vacuous_and_tight, salted200_val⟩,
   ⟨main380_non_vacuous_and_tight.1, main380_non_vacuous_and_tight.2.1, salted380_val⟩⟩

/-- 5. Unsalted vs. salted 200M and 380M margins and SSZ withdrawal closure (`n ≤ 16`) from the
76-budget campaign bridge. -/
theorem unsalted_vs_salted_margins_and_withdrawals_closure_non_vacuous_and_tight
    (n : Nat) (hn : n ≤ 16) :
    (yukon - main200 = 700234018731 ∧ 4 * main200 < yukon ∧
      yukon / 4 - main200 = 24694074625 ∧ yukon < 5 * main200) ∧
    (main380 < yukon ∧ yukon - main380 = 388753925207 ∧ yukon < 2 * main380) ∧
    (8 * 102485906743 < yukon ∧ yukon - 8 * 102485906743 = 80832671530 ∧
      yukon < 9 * 102485906743) ∧
    (5 * 154766000267 < yukon ∧ yukon - 5 * 154766000267 = 126889924139 ∧
      yukon < 6 * 154766000267) ∧
    ((nwdMax ≤ 9223372036854775807 ∧ 16 < nwdMax) ∧
      (132000 * nwdMax = 44291808000) ∧
      (wdTicks 0 nwdMax ≤ r1 ∧ r1 - wdTicks 0 nwdMax = 626933565707) ∧
      (wdTicks 0 189516 ≤ r4 ∧ r4 < wdTicks 0 189517) ∧
      (wdTicks 8 n ≤ wdTicks 8 16 ∧ wdTicks 8 16 ≤ r4 ∧ r4 - wdTicks 8 16 = 25014084625) ∧
      (132000 * 16 + 8 * (16 * 15) = withdrawals16 ∧ main200 = 200485906743 ∧ main380 = 511966000267)) :=
  ⟨main200_margins_non_vacuous_and_tight,
   main380_margins_non_vacuous_and_tight,
   slope200,
   slope380,
   withdrawals_ssz_limit_and_complete_main_closure_non_vacuous_and_tight n hn⟩

/-- 6. User-section `NoLocValue 6` safety (`panToTarget_user_sections_noStubJumpOrLocValue`) unified
with salted linear gas envelopes (`salted200`, `salted380`, `slope200`, `slope380`). -/
theorem user_sections_no_stub_jump_and_salted_linear_gas_bridge_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width) :
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
    (salted200 = 102485906743 ∧ salted380 = 154766000267) ∧
    (8 * 102485906743 < yukon ∧ yukon - 8 * 102485906743 = 80832671530 ∧
      yukon < 9 * 102485906743) ∧
    (5 * 154766000267 < yukon ∧ yukon - 5 * 154766000267 = 126889924139 ∧
      yukon < 6 * 154766000267) :=
  ⟨panToTarget_user_sections_noStubJumpOrLocValue_complete_bridge_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off,
   ⟨salted200_val, salted380_val⟩,
   slope200,
   slope380⟩

/-- 7. Strictly increasing 78-budget portfolio (`SeventyEightShape`), all `< 900_719_925_474`,
extending the 76-budget and 56-budget campaign hierarchy. -/
theorem seventy_eight_and_seventy_six_budget_portfolio_hierarchy_non_vacuous_and_tight :
    SeventyEightShape ∧
    portfolio.length = 78 ∧
    portfolio.Pairwise (· < ·) ∧
    (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    portfolio.drop 76 = [880629318287, 880629318288] ∧
    portfolio.getLast? = some 880629318288 ∧
    SeventySixShape :=
  have h78 := seventy_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  have h76 := seventy_six_and_fifty_six_budget_portfolio_hierarchy_non_vacuous_and_tight
  ⟨h78,
   h78.1,
   h78.2.1,
   h78.2.2.1,
   h78.2.2.2.2.1,
   h78.2.2.2.2.2.1,
   h76.1⟩

/-- 8. Conditional finite certificates `InitE.Certificate (baselineWithFiniteK K) (.finite K)` across
all 78 budgets, with explicit endpoint certificates at `880_629_318_287` and `880_629_318_288`. -/
theorem seventy_eight_budget_conditional_certificates_and_endpoints_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    SeventyEightShape ∧
    (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK 880629318287) (.finite 880629318287) ∧
    InitE.Certificate (baselineWithFiniteK 880629318288) (.finite 880629318288) :=
  have hcert := seventy_eight_budget_certificates_non_vacuous_and_tight cert
  ⟨hcert.1,
   hcert.1.2.2.1,
   hcert.2,
   hcert.2 880629318287 (by decide),
   hcert.2 880629318288 (by decide)⟩

/-- 9. Synthesis of salted linear gas envelopes (`per_unit`, `quad_vs_lin`, `salted_env`, `salted200_val`,
`salted380_val`, `slope200`, `slope380`, `salt_gain`, `per_unit_slack`) with the 78-budget conditional
certificates. -/
theorem salted_linear_gas_envelopes_and_seventy_eight_budget_certificates_non_vacuous_and_tight
    (k : Nat) (hk : 2000 * k ≤ 380000000) (cert : CertificateAt 1212035192) :
    (60 * 8 * 2 ≤ 1000) ∧
    (2000000 * 2000000 / 40 = 100000000000 ∧ saltedTable 2000000 = 2000000000 ∧
      3800000 * 3800000 / 40 = 361000000000 ∧ saltedTable 3800000 = 3800000000) ∧
    (156088992805 - 100000000000 + 2000000000 = 58088992805 ∧
      467569086329 - 361000000000 + 3800000000 = 110369086329) ∧
    (salted200 = 102485906743 ∧ salted380 = 154766000267) ∧
    (8 * 102485906743 < yukon ∧ yukon - 8 * 102485906743 = 80832671530 ∧
      yukon < 9 * 102485906743) ∧
    (5 * 154766000267 < yukon ∧ yukon - 5 * 154766000267 = 126889924139 ∧
      yukon < 6 * 154766000267) ∧
    (100000000000 - 2000000000 = 98000000000 ∧
      361000000000 - 3800000000 = 357200000000) ∧
    (8 * (200485906743 - 100000000000 + 6052 * 2000000) < yukon ∧
      yukon < 8 * (200485906743 - 100000000000 + 6053 * 2000000) ∧
      5 * (511966000267 - 361000000000 + 7678 * 3800000) < yukon ∧
      yukon < 5 * (511966000267 - 361000000000 + 7679 * 3800000)) ∧
    (k ≤ 190000 ∧ 2 * 18 * 40 * 190000 ≤ balRlp ∧ balRlp = 300000000) ∧
    (SeventyEightShape ∧
      ∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨per_unit,
   quad_vs_lin,
   salted_env,
   ⟨salted200_val, salted380_val⟩,
   slope200,
   slope380,
   salt_gain,
   per_unit_slack,
   bal_bound_non_vacuous_and_tight k hk,
   seventy_eight_budget_certificates_non_vacuous_and_tight cert⟩

/-- 10. Grand campaign bridge unifying `GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster`,
`CompleteMainAllSubsystemsAndSeventySixBudgetCampaignBridge`, and
`CompleteMainAllSubsystemsAndSeventyEightBudgetMaster`. -/
theorem grand_salted_linear_gas_complete_main_all_subsystems_and_seventy_eight_budget_campaign_bridge_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (n k : Nat) (hn : n ≤ 16) (hk : 2000 * k ≤ 380000000)
    (cert : CertificateAt 1212035192) :
    ((60 * 8 * 2 ≤ 1000) ∧
     (2000000 * 2000000 / 40 = 100000000000 ∧ saltedTable 2000000 = 2000000000 ∧
       3800000 * 3800000 / 40 = 361000000000 ∧ saltedTable 3800000 = 3800000000) ∧
     (156088992805 - 100000000000 + 2000000000 = 58088992805 ∧
       467569086329 - 361000000000 + 3800000000 = 110369086329) ∧
     (salted200 = 102485906743 ∧ salted380 = 154766000267) ∧
     (8 * 102485906743 < yukon ∧ yukon - 8 * 102485906743 = 80832671530 ∧
       yukon < 9 * 102485906743) ∧
     (5 * 154766000267 < yukon ∧ yukon - 5 * 154766000267 = 126889924139 ∧
       yukon < 6 * 154766000267) ∧
     (100000000000 - 2000000000 = 98000000000 ∧
       361000000000 - 3800000000 = 357200000000) ∧
     (8 * (200485906743 - 100000000000 + 6052 * 2000000) < yukon ∧
       yukon < 8 * (200485906743 - 100000000000 + 6053 * 2000000) ∧
       5 * (511966000267 - 361000000000 + 7678 * 3800000) < yukon ∧
       yukon < 5 * (511966000267 - 361000000000 + 7679 * 3800000))) ∧
    ((gasEnv200 = 156088992805 ∧ witnessMpt = 38946487944 ∧
       postEvm = 4859866650 ∧ prologue = 268435424 ∧
       withdrawals16 = 2113920 ∧ balRlp = 300000000 ∧ requests = 20000000 ∧
       output = 10000 ∧ restTerms = 5450425994 ∧
       main200 = gasEnv200 + witnessMpt + postEvm + prologue + withdrawals16 +
         balRlp + requests + output) ∧
     (2 + 4 = 6 ∧ 200000000 + 6 * 30000000 = 380000000) ∧
     (k ≤ 190000 ∧ 2 * 18 * 40 * 190000 ≤ balRlp ∧ balRlp = 300000000)) ∧
    (((main200 = 200485906743 ∧ yukon - main200 = 700234018731 ∧
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
      WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster.portfolio.length = 76 ∧
      WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster.portfolio.Pairwise (· < ·) ∧
      (∀ K ∈ WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster.portfolio,
        1212035192 ≤ K ∧ K < 900719925474) ∧
      (∀ K ∈ WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)))) ∧
    (SeventyEightShape ∧
     portfolio.length = 78 ∧
     portfolio.Pairwise (· < ·) ∧
     (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
     (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) :=
  have hcert78 := seventy_eight_budget_certificates_non_vacuous_and_tight cert
  ⟨⟨per_unit, quad_vs_lin, salted_env, ⟨salted200_val, salted380_val⟩,
    slope200, slope380, salt_gain, per_unit_slack⟩,
   ⟨main_subsystem_table_non_vacuous_and_tight,
    system_gas_non_vacuous_and_tight,
    bal_bound_non_vacuous_and_tight k hk⟩,
   grand_complete_main_all_subsystems_no_loc_value_6_and_seventy_six_budget_campaign_bridge_non_vacuous_and_tight
     arch prog wc ac perf sc dc mh sp off n k hn hk cert,
   ⟨hcert78.1, hcert78.1.1, hcert78.1.2.1, hcert78.1.2.2.1, hcert78.2⟩⟩

#print axioms salted_linear_gas_envelope_and_quad_vs_lin_non_vacuous_and_tight
#print axioms salted200_and_salted380_totals_and_slopes_non_vacuous_and_tight
#print axioms salted_per_unit_slack_and_salt_gain_non_vacuous_and_tight
#print axioms main_subsystem_table_system_gas_bal_and_salted_envelopes_non_vacuous_and_tight
#print axioms unsalted_vs_salted_margins_and_withdrawals_closure_non_vacuous_and_tight
#print axioms user_sections_no_stub_jump_and_salted_linear_gas_bridge_non_vacuous_and_tight
#print axioms seventy_eight_and_seventy_six_budget_portfolio_hierarchy_non_vacuous_and_tight
#print axioms seventy_eight_budget_conditional_certificates_and_endpoints_non_vacuous_and_tight
#print axioms salted_linear_gas_envelopes_and_seventy_eight_budget_certificates_non_vacuous_and_tight
#print axioms grand_salted_linear_gas_complete_main_all_subsystems_and_seventy_eight_budget_campaign_bridge_non_vacuous_and_tight

end InitECandidate.Solver.SaltedLinearGasAndSeventyEightBudgetCampaignBridge
