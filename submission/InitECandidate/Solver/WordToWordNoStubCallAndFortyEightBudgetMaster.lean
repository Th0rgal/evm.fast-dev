import InitECandidate.Solver.WordToWordNoStubCall
import InitECandidate.Solver.PanToWordNoStubCallAndFortyEightBudgetMaster
import InitECandidate.Solver.SelfContainedElevenTablesAndSharedAbsorptionSynth

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_132: unconditional call safety through all WordToWord passes to StackNames,
shared absorption of the eleven Guest tables, and 48 strictly ordered budgets.
The compiler invariant has no `hcall` premise. Finite semantic certificates
retain the explicit base-certificate premise of the self-contained parents. -/
namespace InitECandidate.Solver.WordToWordNoStubCallAndFortyEightBudgetMaster

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver
open _root_.InitECandidate.Solver.WordToWordNoStubCall (NSC)
open _root_.InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (WordNoStubCall)
open _root_.InitECandidate.Solver.GuestElevenTablesSharedBudgetAbsorption (M S kPanElevenTablesShared)
open _root_.InitECandidate.Solver.GuestElevenTablesAndWarmAddressProbeBound (kPanElevenTables)
open _root_.InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening (feasible witness coupledCost)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster (portfolio)

theorem panToWordToWord_NoStubCall_non_vacuous_and_tight {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) :
    ∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      StackRemoveAndNamesNoStoreConsts.WordNoStubCall y.2.2 = true :=
  WordToWordNoStubCall.panToWordToWord_NoStubCall arch prog wc ac

theorem panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) :
    ∀ y ∈ (WordToStack.Native.compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (PanToStackNoStoreConsts.StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       StackRemoveAndNamesNoStoreConsts.NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true) :=
  WordToWordNoStubCall.panToStackNames_NoSt_and_NoStubCall_unconditional arch prog wc ac perf info j bd ptr f

theorem NSC_rejects_stub_call_non_vacuous_and_tight {α : Type} :
    NSC (WordLangProgHOL.seq (α := α) .skip
      (.call none (some storeConstsStubLocation) [] none)) = false :=
  WordToWordNoStubCall.NSC_rejects_stub_call (α := α)

theorem NSC_accepts_user_call_non_vacuous_and_tight {α : Type} :
    NSC (WordLangProgHOL.call (α := α) none (some 64) [] none) = true :=
  WordToWordNoStubCall.NSC_accepts_user_call (α := α)

theorem NSC_allows_storeConsts_non_vacuous_and_tight {α : Type} :
    NSC (WordLangProgHOL.storeConsts (α := α) 0 1 2 3 []) = true :=
  WordToWordNoStubCall.NSC_allows_storeConsts (α := α)

theorem shared_absorption_non_vacuous_and_tight (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS : B + u2 + u3 + u4 ≤ S) (hb : 40 * blk ≤ B * B) (hl : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7989 * u2) (h3 : 30 * t3 ≤ 5 * 5611 * u3)
    (h4 : 60 * t4 ≤ (M + 2280) * u4) :
    blk + 13 * loc + t2 + t3 + t4 ≤ 151929428571 :=
  PanToWordNoStubCallAndFortyEightBudgetMaster.shared_absorption_non_vacuous_and_tight B u2 u3 u4 blk loc t2 t3 t4 hS hb hl h2 h3 h4

theorem bracket_non_vacuous_and_tight :
    feasible witness ∧ coupledCost witness = 155688931265 ∧
    coupledCost witness ≤ kPanElevenTablesShared ∧
    kPanElevenTablesShared - coupledCost witness = 400061540 ∧
    400061540 * 10000 < 26 * 156088992805 ∧
    400061540 * 10000 < 26 * 155688931265 :=
  PanToWordNoStubCallAndFortyEightBudgetMaster.bracket_non_vacuous_and_tight

theorem five_margin_non_vacuous_and_tight :
    5 * kPanElevenTablesShared < yukon ∧
    yukon - 5 * kPanElevenTablesShared = 120274961449 :=
  PanToWordNoStubCallAndFortyEightBudgetMaster.five_margin_non_vacuous_and_tight

theorem portfolio_shape_non_vacuous_and_tight :
    portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
    ∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474 :=
  PanToWordNoStubCallAndFortyEightBudgetMaster.portfolio_shape_non_vacuous_and_tight

theorem forty_eight_certified_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
    ∀ K ∈ portfolio, K < 900719925474 ∧
      InitE.Certificate (baselineWithFiniteK K) (.finite K) :=
  PanToWordNoStubCallAndFortyEightBudgetMaster.forty_eight_certified_non_vacuous_and_tight cert

theorem eleven_tables_closure_non_vacuous_and_tight
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS : B + u2 + u3 + u4 ≤ S)
    (hblk : 40 * blk ≤ B * B) (hloc : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7_989 * u2)
    (h3 : 30 * t3 ≤ 5 * 5_611 * u3)
    (h4 : 60 * t4 ≤ (M + 2_280) * u4) :
    (5 * 7_989 ≤ 21 * 1_903 ∧ 5 * 5_611 ≤ 30 * 936 ∧ M + 2_280 ≤ 60 * 2_835) ∧
    S * (S - B) ≤ S * S - B * B ∧
    blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571 ∧
    (40 * 100_000_000_000 ≤ S * S ∧ 84 * 3_994_571_428 ≤ M * S ∧
      (21 * S * S + 130 * M * S) / 840 = 151_929_428_571) ∧
    (kPanElevenTablesShared = 156_088_992_805 ∧
      kPanElevenTables - kPanElevenTablesShared = 11_342_996_533) ∧
    (feasible witness ∧ coupledCost witness = 155_688_931_265) ∧
    (coupledCost witness ≤ kPanElevenTablesShared ∧
      kPanElevenTablesShared - coupledCost witness = 400_061_540) ∧
    400_061_540 * 10_000 < 26 * 156_088_992_805 ∧
    (5 * kPanElevenTablesShared < yukon ∧
      yukon - 5 * kPanElevenTablesShared = 120_274_961_449) ∧
    (yukon < 6 * kPanElevenTablesShared ∧ yukon < 6 * coupledCost witness) :=
  SelfContainedElevenTablesAndSharedAbsorptionSynth.guest_eleven_tables_shared_budget_absorption_closure_non_vacuous_and_tight B u2 u3 u4 blk loc t2 t3 t4 hS hblk hloc h2 h3 h4

/-- Safety and arithmetic are unconditional in the source program. Certificate lifting
is a separate implication, so no semantic certificate is needed for call safety. -/
theorem integrated_master_non_vacuous_and_tight {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS : B + u2 + u3 + u4 ≤ S) (hb : 40 * blk ≤ B * B) (hl : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7989 * u2) (h3 : 30 * t3 ≤ 5 * 5611 * u3)
    (h4 : 60 * t4 ≤ (M + 2280) * u4) :
    (∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      WordNoStubCall y.2.2 = true) ∧
    (∀ y ∈ (WordToStack.Native.compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 ≠ storeConstsStubLocation →
      PanToStackNoStoreConsts.StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
      StackRemoveAndNamesNoStoreConsts.NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true) ∧
    blk + 13 * loc + t2 + t3 + t4 ≤ 151929428571 ∧
    kPanElevenTablesShared = 156088992805 ∧
    (feasible witness ∧ coupledCost witness = 155688931265 ∧
      coupledCost witness ≤ kPanElevenTablesShared ∧
      kPanElevenTablesShared - coupledCost witness = 400061540 ∧
      400061540 * 10000 < 26 * 156088992805 ∧
      400061540 * 10000 < 26 * 155688931265) ∧
    (5 * kPanElevenTablesShared < yukon ∧
      yukon - 5 * kPanElevenTablesShared = 120274961449) ∧
    (portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
      ∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    (CertificateAt 1212035192 → ∀ K ∈ portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨panToWordToWord_NoStubCall_non_vacuous_and_tight arch prog wc ac,
    ?_, shared_absorption_non_vacuous_and_tight B u2 u3 u4 blk loc t2 t3 t4 hS hb hl h2 h3 h4,
    ?_, bracket_non_vacuous_and_tight, five_margin_non_vacuous_and_tight,
    portfolio_shape_non_vacuous_and_tight, ?_⟩
  · intro y hy hnonstub
    rcases panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight
      arch prog wc ac perf info j bd ptr f y hy with hstub | hsafe
    · exact False.elim (hnonstub hstub)
    · exact hsafe
  · exact (eleven_tables_closure_non_vacuous_and_tight
      B u2 u3 u4 blk loc t2 t3 t4 hS hb hl h2 h3 h4).2.2.2.2.1.1
  · intro cert K hK
    exact ((forty_eight_certified_non_vacuous_and_tight cert).2.2 K hK).2

#print axioms panToWordToWord_NoStubCall_non_vacuous_and_tight
#print axioms panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight
#print axioms NSC_rejects_stub_call_non_vacuous_and_tight
#print axioms NSC_accepts_user_call_non_vacuous_and_tight
#print axioms NSC_allows_storeConsts_non_vacuous_and_tight
#print axioms shared_absorption_non_vacuous_and_tight
#print axioms bracket_non_vacuous_and_tight
#print axioms five_margin_non_vacuous_and_tight
#print axioms portfolio_shape_non_vacuous_and_tight
#print axioms forty_eight_certified_non_vacuous_and_tight
#print axioms eleven_tables_closure_non_vacuous_and_tight
#print axioms integrated_master_non_vacuous_and_tight

end InitECandidate.Solver.WordToWordNoStubCallAndFortyEightBudgetMaster
