import InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts
import InitECandidate.Solver.ExhaustiveHtabInventoryAndNoStubCallMaster
import InitECandidate.Solver.SelfContainedWordToWordNoStubCallAndSharedAbsorptionSynth

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_136: unconditional compiler invariants, exact side-slope threshold,
shared eleven-table bracket and 48 finite budgets. Finite certificates retain
the base-certificate premise; no bound for arbitrary transient tables is claimed. -/
namespace InitECandidate.Solver.UnconditionalNoStoreConstsNoStubCallAndFortyEightBudgetMaster

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver
open _root_.InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open _root_.InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (NoStubCall)
open _root_.InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts (FlattenVisitsSt)
open _root_.InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption (S)
open _root_.InitECandidate.Solver.GuestElevenTablesSharedBudgetAbsorption (kPanElevenTablesShared)
open _root_.InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening (feasible witness coupledCost M)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster (portfolio)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth (fortyEightSharedClaims)
open _root_.InitECandidate.Solver.YukonVerifyScriptAudit (validFiniteClaim)

variable {width : Nat} [NeZero width]

/-- Both safety invariants and the actual flatten traversal agree, without hcall. -/
theorem unconditional_body_and_flatten_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false) := by
  intro y hy
  rcases WordToWordNoStubCall.panToStackNames_NoSt_and_NoStubCall_unconditional
    arch prog wc ac perf info j bd ptr f y hy with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.1, h.2,
      PanToStackToLabUnconditionalNoStoreConsts.not_visits_of_StackNoSt _ h.1⟩

/-- Section identity is preserved together with both safety invariants. -/
theorem unconditional_section_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
       (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1) := by
  intro y hy
  rcases unconditional_body_and_flatten_non_vacuous_and_tight arch prog wc ac perf info j bd ptr f y hy with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.1, h.2.1, h.2.2, rfl⟩

/-- A real storeConsts is detected and rejected by the invariant, though flatten emits no code. -/
theorem store_consts_discrimination_non_vacuous_and_tight
    (tail : Bool) (sid next : Nat) (cs bs : List Nat) :
    StackNoSt (.seq .skip (.storeConsts 0 1 none) : HolProg width) = false ∧
    FlattenVisitsSt (.seq .skip (.storeConsts 0 1 none) : HolProg width) = true ∧
    StackToLab.flattenHOL tail (.storeConsts 0 1 none : HolProg width) sid next cs bs =
      (.list [], false, next) :=
  ⟨rfl, PanToStackToLabUnconditionalNoStoreConsts.visits_storeConsts_tight,
    PanToStackToLabUnconditionalNoStoreConsts.flatten_storeConsts_empty tail 0 1 none sid next cs bs⟩

/-- General aggregate slope regime with an exact, non-increasable threshold. -/
theorem absorption_and_sharp_threshold_non_vacuous_and_tight
    (l : List (Nat × Nat)) (B blk : Nat)
    (hS : B + (l.map Prod.snd).sum ≤ S) (hblk : 40 * blk ≤ B * B)
    (hslope : (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum) :
    blk + (l.map Prod.fst).sum ≤ 100000000000 ∧
    ¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B →
      T ≤ 50001 * U → blk + T ≤ 100000000000) :=
  ⟨ExhaustiveHtabInventoryAndNoStubCallMaster.general_side_regime_absorption_non_vacuous_and_tight
      l B blk hS hblk hslope,
    ExhaustiveHtabInventoryAndNoStubCallMaster.threshold_sharp_non_vacuous_and_tight⟩

/-- Per-table slope bounds suffice; no individual call-target assumptions occur. -/
theorem pointwise_side_absorption_non_vacuous_and_tight
    (l : List (Nat × Nat)) (B blk : Nat)
    (hS : B + (l.map Prod.snd).sum ≤ S) (hblk : 40 * blk ≤ B * B)
    (hslope : ∀ p ∈ l, p.1 ≤ 50000 * p.2) :
    (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum ∧
    blk + (l.map Prod.fst).sum ≤ 100000000000 := by
  have h := ExhaustiveHtabInventoryAndNoStubCallMaster.slope_sum_non_vacuous_and_tight l hslope
  exact ⟨h, (absorption_and_sharp_threshold_non_vacuous_and_tight l B blk hS hblk h).1⟩

/-- Explicit extremal and failing allocations witness the exact threshold. -/
theorem threshold_endpoint_witnesses_non_vacuous_and_tight :
    40 * 100000000000 = S * S ∧
    0 + 2000000 ≤ S ∧ 100000000000 = 50000 * 2000000 ∧
    50001 * 2000000 > 100000000000 := by decide

/-- Feasible lower witness and the upper budget differ by less than 0.26% on either scale. -/
theorem eleven_table_bracket_non_vacuous_and_tight :
    kPanElevenTablesShared = 156088992805 ∧
    (feasible witness ∧ coupledCost witness = 155688931265 ∧
      coupledCost witness ≤ kPanElevenTablesShared ∧
      kPanElevenTablesShared - coupledCost witness = 400061540 ∧
      400061540 * 10000 < 26 * 156088992805 ∧
      400061540 * 10000 < 26 * 155688931265) :=
  ⟨by decide, WordToWordNoStubCallAndFortyEightBudgetMaster.bracket_non_vacuous_and_tight⟩

open _root_.InitECandidate.Solver.GuestBs32BlockStorageEnvelope (linear)
open _root_.InitECandidate.Solver.GuestElevenTablesAndWarmAddressProbeBound (kPanElevenTables)

theorem shared_eleven_tables_absorption_non_vacuous_and_tight
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS : B + u2 + u3 + u4 ≤ S)
    (hblk : 40 * blk ≤ B * B) (hloc : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7_989 * u2)
    (h3 : 30 * t3 ≤ 5 * 5_611 * u3)
    (h4 : 60 * t4 ≤ (M + 2_280) * u4) :
    blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571 ∧
    (kPanElevenTablesShared = 156_088_992_805 ∧
      kPanElevenTables - kPanElevenTablesShared = 11_342_996_533) ∧
    (feasible witness ∧ coupledCost witness = 155_688_931_265 ∧
      coupledCost witness ≤ kPanElevenTablesShared ∧
      kPanElevenTablesShared - coupledCost witness = 400_061_540 ∧
      400_061_540 * 10_000 < 26 * 156_088_992_805 ∧
      400_061_540 * 10_000 < 26 * 155_688_931_265) ∧
    (5 * kPanElevenTablesShared < yukon ∧
      yukon - 5 * kPanElevenTablesShared = 120_274_961_449) ∧
    (yukon < 6 * kPanElevenTablesShared ∧ yukon < 6 * coupledCost witness) ∧
    (5 * 7_989 ≤ 21 * 1_903 ∧ 5 * 5_611 ≤ 30 * 936 ∧ M + 2_280 ≤ 60 * 2_835) ∧
    S * (S - B) ≤ S * S - B * B ∧
    (40 * 100_000_000_000 ≤ S * S ∧ 84 * 3_994_571_428 ≤ M * S ∧
      (21 * S * S + 130 * M * S) / 840 = 151_929_428_571) :=
  SelfContainedWordToWordNoStubCallAndSharedAbsorptionSynth.shared_absorption_bracket_and_five_margin_synthesis_non_vacuous_and_tight
    B u2 u3 u4 blk loc t2 t3 t4 hS hblk hloc h2 h3 h4

/-- Ordered portfolio shape is unconditional. -/
theorem forty_eight_shape_non_vacuous_and_tight :
    portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
      ∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474 :=
  WordToWordNoStubCallAndFortyEightBudgetMaster.portfolio_shape_non_vacuous_and_tight

/-- Every budget inherits a semantic certificate from the best base certificate. -/
theorem forty_eight_finite_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    (portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
      ∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  have h := ExhaustiveHtabInventoryAndNoStubCallMaster.forty_eight_budget_certificates_non_vacuous_and_tight cert
  exact ⟨h.1, h.2.1⟩

/-- The 48 concrete JSON payloads match the portfolio and satisfy the verifier limit. -/
theorem forty_eight_claim_payloads_non_vacuous_and_tight :
    fortyEightSharedClaims.length = 48 ∧
    fortyEightSharedClaims.map Prod.fst = portfolio ∧
    (∀ entry ∈ fortyEightSharedClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) := by
  have h := SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth.forty_eight_shared_claims_valid_and_within_128_bytes_non_vacuous_and_tight 1
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- Joint compiler, absorption, tightness and finite-certificate contract. -/
theorem integrated_master_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (l : List (Nat × Nat)) (B blk : Nat)
    (hS : B + (l.map Prod.snd).sum ≤ S) (hblk : 40 * blk ≤ B * B)
    (hslope : (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum)
    (cert : CertificateAt 1212035192) :
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
       (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) ∧
    (blk + (l.map Prod.fst).sum ≤ 100000000000 ∧
      ¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B →
        T ≤ 50001 * U → blk + T ≤ 100000000000)) ∧
    (kPanElevenTablesShared = 156088992805 ∧
      (feasible witness ∧ coupledCost witness = 155688931265 ∧
       coupledCost witness ≤ kPanElevenTablesShared ∧
       kPanElevenTablesShared - coupledCost witness = 400061540 ∧
       400061540 * 10000 < 26 * 156088992805 ∧
       400061540 * 10000 < 26 * 155688931265)) ∧
    ((portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
       ∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
      (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
    (fortyEightSharedClaims.length = 48 ∧
      fortyEightSharedClaims.map Prod.fst = portfolio ∧
      (∀ entry ∈ fortyEightSharedClaims,
       entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true)) :=
  ⟨unconditional_section_non_vacuous_and_tight arch prog wc ac perf info j bd ptr f,
    absorption_and_sharp_threshold_non_vacuous_and_tight l B blk hS hblk hslope,
    eleven_table_bracket_non_vacuous_and_tight,
    forty_eight_finite_certificates_non_vacuous_and_tight cert,
    forty_eight_claim_payloads_non_vacuous_and_tight⟩

#print axioms unconditional_body_and_flatten_non_vacuous_and_tight
#print axioms unconditional_section_non_vacuous_and_tight
#print axioms store_consts_discrimination_non_vacuous_and_tight
#print axioms absorption_and_sharp_threshold_non_vacuous_and_tight
#print axioms pointwise_side_absorption_non_vacuous_and_tight
#print axioms threshold_endpoint_witnesses_non_vacuous_and_tight
#print axioms eleven_table_bracket_non_vacuous_and_tight
#print axioms shared_eleven_tables_absorption_non_vacuous_and_tight
#print axioms forty_eight_shape_non_vacuous_and_tight
#print axioms forty_eight_finite_certificates_non_vacuous_and_tight
#print axioms forty_eight_claim_payloads_non_vacuous_and_tight
#print axioms integrated_master_non_vacuous_and_tight

end InitECandidate.Solver.UnconditionalNoStoreConstsNoStubCallAndFortyEightBudgetMaster
