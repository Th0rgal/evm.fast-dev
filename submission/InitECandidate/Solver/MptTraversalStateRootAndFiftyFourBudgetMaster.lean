import InitECandidate.Solver.GuestMptTraversalAndStateRootBound
import InitECandidate.Solver.SelfContainedTransientStorageJournalAndFiftyBudgetSynth
import InitECandidate.Solver.LabToTargetNoStubJumpNodedbAndFiftyTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_148. MPT arithmetic, compiler safety and 54 finite tiers.
The advancing-extension and gas premises are explicit model contracts.
Semantic certificates require the base certificate; cost arithmetic does not discharge it.
The two new tiers are one-tick relaxations of the preceding maximum. -/
namespace InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open InitECandidate.Solver
open GuestMptTraversalAndStateRootBound
open StackToLabAndLabToTargetNoStubCall
open _root_.InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (WordNoStubCall)
open _root_.InitECandidate.Solver.PanToWordNoStubCall (TgtGood)
open _root_.InitECandidate.Solver.WordToWordNoStubCall (NSC)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.YukonVerifyScriptAudit (validFiniteClaim)

abbrev Previous := TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster.portfolio

def portfolio : List Nat := Previous ++ [857384015257, 857384015258]

def fiftyFourClaims : List (Nat × String) :=
  TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster.fiftyTwoClaims ++
  [(857384015257, "{\"K\":857384015257}"),
   (857384015258, "{\"K\":857384015258}")]

def FiftyFourShape : Prop :=
  portfolio.length = 54 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
  portfolio.take 52 = Previous

def ClaimPayloads : Prop :=
  fiftyFourClaims.length = 54 ∧ fiftyFourClaims.map Prod.fst = portfolio ∧
  ∀ e ∈ fiftyFourClaims, e.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim e.1 e.2 = true

def WalkContract : Prop :=
  (∀ s : Step, (∀ sl, s = .ext sl → 1 ≤ sl) → 1 ≤ advance s) ∧
  (∀ l : List Step, (∀ s ∈ l, 1 ≤ advance s) → (l.map advance).sum ≤ 64 →
    l.length ≤ 64 ∧ l.length + 1 ≤ 65) ∧
  ((List.replicate 64 Step.branch).map advance).sum = 64 ∧
  (List.replicate 64 Step.branch).length + 1 = 65 ∧ advance (.ext 0) = 0

/-- Advancing walks attain 65 iterations; zero-length extensions stall. -/
theorem traversal_non_vacuous_and_tight : WalkContract :=
  ⟨advance_pos, fun l h hs => ⟨steps_le l h hs, walk_iters l h hs⟩,
    walk_tight, by decide, ext_zero_stalls⟩

def AccessContract : Prop :=
  (∀ c : Nat, 2000 * c ≤ 200000000 → c ≤ 100000 ∧ 65 * c ≤ 6500000) ∧
  2000 * 100000 = 200000000 ∧ 65 * 100000 = 6500000

theorem accesses_non_vacuous_and_tight : AccessContract :=
  ⟨fun c h => access_totals c (cold_le c h), cold_tight, by decide⟩

def RootContract : Prop :=
  (∀ c : Nat, c ≤ 100000 → 2 * 65 * c ≤ 13000000 ∧ 65 * c ≤ 6500000) ∧
  2 * 65 * 100000 = 13000000 ∧ 65 * 100000 = 6500000

theorem state_root_non_vacuous_and_tight : RootContract :=
  ⟨state_root_totals, by decide, by decide⟩

def WitnessLinearContract : Prop :=
  (∀ n : Nat, 4 * n ≤ 134217712 → n ≤ 33554428) ∧
  4 * 33554428 = 134217712 ∧
  13000000 * 1000 + 6500000 * 1000 = 19500000000

theorem witness_and_linear_non_vacuous_and_tight : WitnessLinearContract :=
  ⟨witness_lookups, by decide, linear_budget⟩

def CoupledJournalContract : Prop :=
  (∀ u1 u2 t1 t2 : Nat, u1 + u2 ≤ 2000000 → t1 ≤ 373022 * u1 →
    t2 ≤ 373022 * u2 → t1 + t2 ≤ 746044000000) ∧
  373022 * 1000000 + 373022 * 1000000 = 746044000000 ∧
  (∀ j : List Bool, j.length ≤ 524288 →
    GuestTransientStorageGrowthAndJournalAnalysis.restoreDels j ≤ 524288) ∧
  GuestTransientStorageGrowthAndJournalAnalysis.restoreDels
    (List.replicate 524288 false) = 524288

theorem coupled_journal_non_vacuous_and_tight : CoupledJournalContract := by
  have hj := LabToTargetNoStubJumpNodedbAndFiftyTwoBudgetMaster.journal_non_vacuous_and_tight
  exact ⟨GuestTransientStorageGrowthAndJournalAnalysis.coupled_le,
    by decide, hj.1, hj.2.1⟩

def PanLabSafe : Prop :=
  ∀ {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width),
    ∀ s ∈ StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2,
      PanToLabSectionAndStackRemoveClock.IsStubLabel s.sectionId = true ∨ LOk s.lines

theorem panToLab_lines_non_vacuous_and_tight : PanLabSafe :=
  LabToTargetNoStubJumpNodedbAndFiftyTwoBudgetMaster.panToLab_lines_non_vacuous_and_tight

def PanTargetSafe : Prop :=
  ∀ {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (_h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs')),
    ∀ s' ∈ L', PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = true ∨
      ∀ x ∈ s'.lines, JumpOk x = true

theorem panToTarget_noStubJump_non_vacuous_and_tight : PanTargetSafe :=
  LabToTargetNoStubJumpNodedbAndFiftyTwoBudgetMaster.panToTarget_noStubJump_non_vacuous_and_tight

def PanUserSafe : Prop :=
  ∀ {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (_h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (s' : Sec width) (_hs : s' ∈ L')
    (_hu : PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = false),
    ∀ x ∈ s'.lines, JumpOk x = true

theorem panToTarget_user_noStubJump_non_vacuous_and_tight : PanUserSafe :=
  LabToTargetNoStubJumpNodedbAndFiftyTwoBudgetMaster.panToTarget_user_noStubJump_non_vacuous_and_tight

theorem portfolio_non_vacuous_and_tight : FiftyFourShape := by
  unfold FiftyFourShape
  decide

theorem payloads_non_vacuous_and_tight : ClaimPayloads := by
  unfold ClaimPayloads
  decide

theorem certificates_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    ∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K) := by
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (portfolio_non_vacuous_and_tight.2.2.1 K hK).1 cert

def FrontendSafe : Prop :=
  ∀
    {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width),
    (∀ y ∈ panToWordCompileProgHOL arch prog, WordNoStubCall y.2.2 = true) ∧
    (∀ y ∈ panToWordCompileProgHOL arch prog, 64 ≤ y.1) ∧
    (∀ y ∈ panToWordCompileProgHOL arch prog, WordNoStubCall y.2.2 = true ∧ 64 ≤ y.1) ∧
    (∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      WordNoStubCall y.2.2 = true) ∧
    ¬ TgtGood (some storeConstsStubLocation) ∧
    (TgtGood (some 0) ∧ TgtGood (some 64) ∧ ¬ TgtGood none) ∧
    (WordNoStubCall (WordLangProgHOL.call (α := BitVec width) none (some storeConstsStubLocation) [] none) = false ∧
     WordNoStubCall (WordLangProgHOL.call (α := BitVec width) none (some 64) [] none) = true) ∧
    NSC (WordLangProgHOL.seq (α := BitVec width) .skip
      (.call none (some storeConstsStubLocation) [] none)) = false ∧
    NSC (WordLangProgHOL.call (α := BitVec width) none (some 64) [] none) = true ∧
    NSC (WordLangProgHOL.storeConsts (α := BitVec width) 0 1 2 3 []) = true

/-- All arithmetic contracts and all compiler stages, with semantic lifting
explicitly conditional on the base certificate. No program restriction is used. -/
theorem integrated_master_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    WalkContract ∧ AccessContract ∧ RootContract ∧ WitnessLinearContract ∧
    CoupledJournalContract ∧ FrontendSafe ∧ PanLabSafe ∧ PanTargetSafe ∧ PanUserSafe ∧
    FiftyFourShape ∧ ClaimPayloads ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨traversal_non_vacuous_and_tight, accesses_non_vacuous_and_tight,
   state_root_non_vacuous_and_tight, witness_and_linear_non_vacuous_and_tight,
   coupled_journal_non_vacuous_and_tight,
   SelfContainedTransientStorageJournalAndFiftyBudgetSynth.unconditional_pan_to_word_and_word_to_word_no_stub_call_non_vacuous_and_tight,
   panToLab_lines_non_vacuous_and_tight,
   panToTarget_noStubJump_non_vacuous_and_tight,
   panToTarget_user_noStubJump_non_vacuous_and_tight,
   portfolio_non_vacuous_and_tight, payloads_non_vacuous_and_tight,
   certificates_non_vacuous_and_tight cert⟩

#print axioms traversal_non_vacuous_and_tight
#print axioms accesses_non_vacuous_and_tight
#print axioms state_root_non_vacuous_and_tight
#print axioms witness_and_linear_non_vacuous_and_tight
#print axioms coupled_journal_non_vacuous_and_tight
#print axioms panToLab_lines_non_vacuous_and_tight
#print axioms panToTarget_noStubJump_non_vacuous_and_tight
#print axioms panToTarget_user_noStubJump_non_vacuous_and_tight
#print axioms portfolio_non_vacuous_and_tight
#print axioms payloads_non_vacuous_and_tight
#print axioms certificates_non_vacuous_and_tight
#print axioms integrated_master_non_vacuous_and_tight

end InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster
