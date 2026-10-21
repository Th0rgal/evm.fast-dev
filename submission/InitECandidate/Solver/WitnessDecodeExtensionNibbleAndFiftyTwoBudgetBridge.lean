import InitECandidate.Solver.GuestWitnessDecodeAndExtensionNibbleAudit
import InitECandidate.Solver.SelfContainedSubcallRevertAbsorptionAndFiftyBudgetSynth
import InitECandidate.Solver.SelfContainedLabToTargetNoStubJumpAndFiftyTwoBudgetSynth

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# WitnessDecodeExtensionNibbleAndFiftyTwoBudgetBridge

Wave 5 atomic bridge (W5_150). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.WitnessDecodeExtensionNibbleAndFiftyTwoBudgetBridge

open InitECandidate.Solver.GuestWitnessDecodeAndExtensionNibbleAudit
open InitECandidate.Solver.GuestMptTraversalAndStateRootBound (Step advance)
open InitECandidate.Solver.SelfContainedLabToTargetNoStubJumpAndFiftyTwoBudgetSynth
open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.PanToStackNoStoreConsts
open InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts
open InitECandidate.Solver.WordToWordNoStubCall
open InitECandidate.Solver.PanToLabSectionAndStackRemoveClock
open InitECandidate.Solver.StackToLabAndLabToTargetNoStubCall
open InitECandidate.Solver.TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster
  (FiftyTwoShape)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev FiftyShape :=
  InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.FiftyShape

abbrev fiftyPortfolio :=
  InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.portfolio

abbrev ClaimPayloads52 :=
  InitECandidate.Solver.TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster.ClaimPayloads

variable {width : Nat} [NeZero width]

theorem compact_len_cases_and_zero_iff_non_vacuous_and_tight (n odd : Nat)
    (hn : 1 ≤ n) (ho : odd ≤ 1) :
    (compactLen n 0 = 2 * n - 2 ∧ compactLen n 1 = 2 * n - 1) ∧
    (compactLen n odd = 0 ↔ n = 1 ∧ odd = 0) ∧
    (compactLen 33 0 = 64 ∧ compactLen 32 1 = 63) :=
  ⟨compact_len_cases n hn, compact_zero_iff n odd hn ho, compact_full_key⟩

theorem ext_zero_and_child_rejected_non_vacuous_and_tight (l ck : Nat) :
    extAccepted 0 ck = false ∧ extAccepted l 2 = false ∧ extAccepted l 1 = false :=
  ⟨ext_zero_rejected ck, (ext_child_rejected l).1, (ext_child_rejected l).2⟩

theorem accepted_advances_and_walk_bound_decoded_non_vacuous_and_tight
    (l ck : Nat) (hacc : extAccepted l ck = true)
    (steps : List Nat) (hsteps : ∀ x ∈ steps, x ≠ 0)
    (hsum : ((steps.map Step.ext).map advance).sum ≤ 64) :
    1 ≤ advance (Step.ext l) ∧ steps.length ≤ 64 ∧ steps.length ≤ 65 :=
  ⟨accepted_advances l ck hacc, walk_bound_decoded steps hsteps hsum,
    Nat.le_trans (walk_bound_decoded steps hsteps hsum) (by decide : 64 ≤ 65)⟩

theorem heap_nodes_expansion_and_ratio_non_vacuous_and_tight :
    (33806089496 - 2713714688) / 56 = 555220978 ∧
    ((List.range 7).foldl (fun a i => a + 16 ^ i) 0 = 17895697 ∧
      17895697 * 176 + 16 ^ 7 * 64 = 20329511856 ∧
      20329511856 ≤ 33806089496 - 2713714688) ∧
    33806089496 - 2713714688 < 16 ^ 8 * 64 ∧
    (17895697 + 16 ^ 7 = 286331153 ∧ 8 * 530 < 4300) :=
  ⟨heap_nodes, expansion_fits, expansion_traps, expansion_ratio⟩

theorem panToTarget_noStubJump_bridge_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width) :
    (∀ (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
        (L' : List (Sec width)) (labs' : Spt (Spt Nat)),
      removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs') →
      ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨ ∀ x ∈ s'.lines, JumpOk x = true) ∧
    JumpOk (.labAsm (.jump (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
    JumpOk (.labAsm (.call (.lab 64 0)) (0 : BitVec width) [] 0) = true :=
  panToTarget_noStubJump_non_vacuous_and_tight arch prog wc ac perf sc dc mh sp off

theorem panToTarget_user_noStubJump_bridge_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width) :
    (∀ (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
        (L' : List (Sec width)) (labs' : Spt (Spt Nat)),
      removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs') →
      ∀ s' ∈ L', IsStubLabel s'.sectionId = false → ∀ x ∈ s'.lines, JumpOk x = true) ∧
    IsStubLabel (storeConstsStubLocation : Nat) = true ∧
    IsStubLabel (64 : Nat) = false ∧
    JumpOk (.labAsm (.jump (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
    JumpOk (.labAsm (.call (.lab 64 0)) (0 : BitVec width) [] 0) = true :=
  panToTarget_user_noStubJump_non_vacuous_and_tight arch prog wc ac perf sc dc mh sp off

theorem fifty_two_budget_portfolio_under_yukon_non_vacuous_and_tight :
    FiftyTwoShape ∧ ClaimPayloads52 ∧ yukon = 900719925474 :=
  ⟨fifty_two_portfolio_and_payloads_non_vacuous_and_tight.1,
   fifty_two_portfolio_and_payloads_non_vacuous_and_tight.2, rfl⟩

theorem fifty_and_fifty_two_budget_portfolios_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    (FiftyShape ∧
      ∀ k ∈ fiftyPortfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (FiftyTwoShape ∧ ClaimPayloads52) :=
  ⟨⟨(InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.fifty_certificates_non_vacuous_and_tight
        cert).1,
     (InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.fifty_certificates_non_vacuous_and_tight
        cert).2.2⟩,
   fifty_two_portfolio_and_payloads_non_vacuous_and_tight⟩

theorem witness_decode_and_pan_to_target_bridge_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width) :
    ((33806089496 - 2713714688) / 56 = 555220978 ∧
      17895697 * 176 + 16 ^ 7 * 64 = 20329511856 ∧
      33806089496 - 2713714688 < 16 ^ 8 * 64 ∧
      17895697 + 16 ^ 7 = 286331153) ∧
    ((∀ (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
        (L' : List (Sec width)) (labs' : Spt (Spt Nat)),
      removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs') →
      ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨ ∀ x ∈ s'.lines, JumpOk x = true) ∧
     (∀ (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
        (L' : List (Sec width)) (labs' : Spt (Spt Nat)),
      removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs') →
      ∀ s' ∈ L', IsStubLabel s'.sectionId = false → ∀ x ∈ s'.lines, JumpOk x = true)) :=
  ⟨⟨heap_nodes, expansion_fits.2.1, expansion_traps, expansion_ratio.1⟩,
   ⟨fun ic pos labs ffis L' labs' h =>
      (panToTarget_noStubJump_non_vacuous_and_tight arch prog wc ac perf sc dc mh sp off).1
        ic pos labs ffis L' labs' h,
    fun ic pos labs ffis L' labs' h s' hs hu =>
      (panToTarget_user_noStubJump_non_vacuous_and_tight arch prog wc ac perf sc dc mh sp off).1
        ic pos labs ffis L' labs' h s' hs hu⟩⟩

theorem witness_decode_extension_nibble_and_fifty_two_budget_bridge_master_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (n odd : Nat) (hn : 1 ≤ n) (ho : odd ≤ 1)
    (l ck : Nat) (hacc : extAccepted l ck = true)
    (steps : List Nat) (hsteps : ∀ x ∈ steps, x ≠ 0)
    (hsum : ((steps.map Step.ext).map advance).sum ≤ 64)
    (cert : CertificateAt 1212035192) :
    (compactLen n 0 = 2 * n - 2 ∧ compactLen n 1 = 2 * n - 1) ∧
    (compactLen n odd = 0 ↔ n = 1 ∧ odd = 0) ∧
    extAccepted 0 ck = false ∧
    1 ≤ advance (Step.ext l) ∧ steps.length ≤ 65 ∧
    (33806089496 - 2713714688) / 56 = 555220978 ∧
    17895697 * 176 + 16 ^ 7 * 64 = 20329511856 ∧
    33806089496 - 2713714688 < 16 ^ 8 * 64 ∧
    17895697 + 16 ^ 7 = 286331153 ∧
    (∀ (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
        (L' : List (Sec width)) (labs' : Spt (Spt Nat)),
      removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs') →
      ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨ ∀ x ∈ s'.lines, JumpOk x = true) ∧
    (∀ (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
        (L' : List (Sec width)) (labs' : Spt (Spt Nat)),
      removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs') →
      ∀ s' ∈ L', IsStubLabel s'.sectionId = false → ∀ x ∈ s'.lines, JumpOk x = true) ∧
    (FiftyShape ∧ ∀ k ∈ fiftyPortfolio,
      InitE.Certificate (baselineWithFiniteK k) (.finite k)) ∧
    (FiftyTwoShape ∧ ClaimPayloads52 ∧ yukon = 900719925474) :=
  ⟨compact_len_cases n hn,
   compact_zero_iff n odd hn ho,
   ext_zero_rejected ck,
   accepted_advances l ck hacc,
   Nat.le_trans (walk_bound_decoded steps hsteps hsum) (by decide : 64 ≤ 65),
   heap_nodes, expansion_fits.2.1, expansion_traps, expansion_ratio.1,
   fun ic pos labs ffis L' labs' h =>
     (panToTarget_noStubJump_non_vacuous_and_tight arch prog wc ac perf sc dc mh sp off).1
       ic pos labs ffis L' labs' h,
   fun ic pos labs ffis L' labs' h s' hs hu =>
     (panToTarget_user_noStubJump_non_vacuous_and_tight arch prog wc ac perf sc dc mh sp off).1
       ic pos labs ffis L' labs' h s' hs hu,
   ⟨(InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.fifty_certificates_non_vacuous_and_tight
        cert).1,
    (InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.fifty_certificates_non_vacuous_and_tight
        cert).2.2⟩,
   And.intro fifty_two_portfolio_and_payloads_non_vacuous_and_tight.1
     (And.intro fifty_two_portfolio_and_payloads_non_vacuous_and_tight.2 rfl)⟩

end InitECandidate.Solver.WitnessDecodeExtensionNibbleAndFiftyTwoBudgetBridge
