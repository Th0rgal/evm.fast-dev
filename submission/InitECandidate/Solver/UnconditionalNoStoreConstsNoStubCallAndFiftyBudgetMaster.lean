import InitECandidate.Solver.UnconditionalNoStoreConstsNoStubCallAndFortyEightBudgetMaster
import InitECandidate.Solver.SelfContainedExhaustiveHtabInventoryAndNoStubCallSynth

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_139: unconditional compiler invariants, exact side-slope threshold,
shared eleven-table bracket and 50 finite budgets. Finite certificates retain
the base-certificate premise; no bound for arbitrary transient tables is claimed. -/
namespace InitECandidate.Solver.UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster

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

open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

open _root_.InitECandidate.Solver.YukonVerifyScriptAudit (validFiniteClaim)

/-- The original 48 tiers plus two explicit one-tick relaxations of the maximum. -/
def portfolio : List Nat :=
  ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster.portfolio ++
    [857384015253, 857384015254]

/-- Concrete verifier payloads for the same 50 tiers. -/
def fiftyClaims : List (Nat × String) :=
  SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth.fortyEightSharedClaims ++
    [(857384015253, "{\"K\":857384015253}"),
     (857384015254, "{\"K\":857384015254}")]

/-- Core state-table inventory, transcribed from state_init, state_fresh_tx and
frame construction. Auxiliary local tables (BAL, nodedb, authorization scratch,
new_roots) are outside this core inventory and have no inferred clock bound. -/
def coreHtabInventory : List String :=
  ["ws+32", "bs+8", "bs+16", "bs+24", "bs+32", "bs+40", "bs+48", "bs+72",
   "ts+8", "ts+16", "ts+24", "ts+32", "ts+40", "ts+48", "ts+56", "ts+64",
   "ev+136", "ev+168", "ev+176"]

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
theorem inventory_and_threshold_endpoints_non_vacuous_and_tight :
    coreHtabInventory.length = 19 ∧ coreHtabInventory.Nodup ∧
    "ts+64" ∈ coreHtabInventory ∧
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

/-- Strict 50-tier shape and exact preservation of the preceding portfolio. -/
theorem fifty_shape_non_vacuous_and_tight :
    portfolio.length = 50 ∧ portfolio.Pairwise (· < ·) ∧
    (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    portfolio.take 48 = ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster.portfolio := by
  decide

/-- Semantic certificates for every explicit tier, conditional on the base certificate. -/
theorem fifty_finite_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    (portfolio.length = 50 ∧ portfolio.Pairwise (· < ·) ∧
      ∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨⟨fifty_shape_non_vacuous_and_tight.1,
    fifty_shape_non_vacuous_and_tight.2.1,
    fifty_shape_non_vacuous_and_tight.2.2.1⟩, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (fifty_shape_non_vacuous_and_tight.2.2.1 K hK).1 cert

/-- All fifty JSON payloads have the right budget and fit the verifier limit. -/
theorem fifty_claim_payloads_non_vacuous_and_tight :
    fiftyClaims.length = 50 ∧
    fiftyClaims.map Prod.fst = portfolio ∧
    (∀ entry ∈ fiftyClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) := by
  decide

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
    ((portfolio.length = 50 ∧ portfolio.Pairwise (· < ·) ∧
       ∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
      (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
    (fiftyClaims.length = 50 ∧
      fiftyClaims.map Prod.fst = portfolio ∧
      (∀ entry ∈ fiftyClaims,
       entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true)) ∧
    (coreHtabInventory.length = 19 ∧ coreHtabInventory.Nodup) ∧
    (5 * kPanElevenTablesShared < yukon ∧
      yukon - 5 * kPanElevenTablesShared = 120274961449) :=
  ⟨unconditional_section_non_vacuous_and_tight arch prog wc ac perf info j bd ptr f,
    absorption_and_sharp_threshold_non_vacuous_and_tight l B blk hS hblk hslope,
    eleven_table_bracket_non_vacuous_and_tight,
    fifty_finite_certificates_non_vacuous_and_tight cert,
    fifty_claim_payloads_non_vacuous_and_tight,
    ⟨inventory_and_threshold_endpoints_non_vacuous_and_tight.1,
     inventory_and_threshold_endpoints_non_vacuous_and_tight.2.1⟩,
    GuestElevenTablesSharedBudgetAbsorption.five_margin⟩

#print axioms unconditional_body_and_flatten_non_vacuous_and_tight
#print axioms unconditional_section_non_vacuous_and_tight
#print axioms store_consts_discrimination_non_vacuous_and_tight
#print axioms absorption_and_sharp_threshold_non_vacuous_and_tight
#print axioms pointwise_side_absorption_non_vacuous_and_tight
#print axioms inventory_and_threshold_endpoints_non_vacuous_and_tight
#print axioms eleven_table_bracket_non_vacuous_and_tight
#print axioms shared_eleven_tables_absorption_non_vacuous_and_tight
#print axioms fifty_shape_non_vacuous_and_tight
#print axioms fifty_finite_certificates_non_vacuous_and_tight
#print axioms fifty_claim_payloads_non_vacuous_and_tight
#print axioms integrated_master_non_vacuous_and_tight

end InitECandidate.Solver.UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster
