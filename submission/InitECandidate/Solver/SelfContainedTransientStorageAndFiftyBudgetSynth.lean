import InitECandidate.Solver.GuestTransientStorageAndRemainingTablesAudit
import InitECandidate.Solver.UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedTransientStorageAndFiftyBudgetSynth`

Self-contained synthesis of:
1. `GuestTransientStorageAndRemainingTablesAudit` (`ts+64` EIP-1153 per-tx cap `158_162`, block packing,
   `tx_build = 62_537_650_205`, `block_build = 740_946_409_660`, `block_with_revert = 1_481_892_819_320`,
   `one_slope_no_revert` with margin `3_684_523_009`, `tstore_not_absorbable`, and `remaining_absorbed`).
2. Unconditional `PanSimp` to `StackToLab` safety chain without `hcall`
   (`panToStackNames_NoSt_and_NoStubCall_unconditional`, `panToStackToLab_never_visits_StoreConsts`).
3. Strictly increasing 50-budget portfolio under Yukon (`900_719_925_474`) and explicit finite
   certificates conditional on the base certificate.
-/
namespace InitECandidate.Solver.SelfContainedTransientStorageAndFiftyBudgetSynth

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
open _root_.InitECandidate.Solver.GuestTransientStorageAndRemainingTablesAudit
  (txCap blockGas intrinsic keyGas buildTicks)
open _root_.InitECandidate.Solver.UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster
  (portfolio fiftyClaims coreHtabInventory)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.YukonVerifyScriptAudit (validFiniteClaim)

variable {width : Nat} [NeZero width]

/-- 1. EIP-1153 per-tx key cap (`158_162`), monotone build cost, and block packing in `200,000,000` gas. -/
theorem transient_storage_tx_cap_and_packing_non_vacuous_and_tight
    (k a b : Nat) (hk : intrinsic + keyGas * k ≤ txCap) (hab : a ≤ b) :
    k ≤ 158162 ∧
    buildTicks a ≤ buildTicks b ∧
    (intrinsic + keyGas * 158162 ≤ txCap ∧ txCap < intrinsic + keyGas * 158163) ∧
    (11 * txCap + intrinsic + keyGas * 145647 ≤ blockGas ∧
      blockGas < 11 * txCap + intrinsic + keyGas * 145648) :=
  ⟨GuestTransientStorageAndRemainingTablesAudit.keys_le k hk,
   GuestTransientStorageAndRemainingTablesAudit.build_mono a b hab,
   GuestTransientStorageAndRemainingTablesAudit.keys_per_tx,
   GuestTransientStorageAndRemainingTablesAudit.block_packing⟩

/-- 2. Exact `ts+64` per-tx build cost (`62,537,650,205`), block build cost without revert
(`740,946,409,660`), and doubled block cost with revert (`1,481,892,819,320`). -/
theorem transient_storage_build_and_revert_costs_non_vacuous_and_tight :
    buildTicks 158162 = 62537650205 ∧
    11 * buildTicks 158162 + buildTicks 145647 = 740946409660 ∧
    2 * (11 * buildTicks 158162 + buildTicks 145647) = 1481892819320 :=
  ⟨GuestTransientStorageAndRemainingTablesAudit.tx_build,
   GuestTransientStorageAndRemainingTablesAudit.block_build,
   GuestTransientStorageAndRemainingTablesAudit.block_with_revert⟩

/-- 3. `1×` no-revert transient storage plus `kPanElevenTablesShared` (`156,088,992,805`) fits under
Yukon with exact margin `3,684,523,009`, whereas revert or `2×` slope exceeds Yukon. -/
theorem transient_storage_slope_envelope_and_revert_failure_non_vacuous_and_tight :
    (740946409660 < yukon ∧ 156088992805 + 740946409660 < yukon ∧
      yukon - (156088992805 + 740946409660) = 3684523009) ∧
    (yukon < 1481892819320 ∧ yukon < 2 * 740946409660) ∧
    kPanElevenTablesShared + (11 * buildTicks 158162 + buildTicks 145647) < yukon ∧
    yukon - (kPanElevenTablesShared + (11 * buildTicks 158162 + buildTicks 145647)) = 3684523009 :=
  ⟨GuestTransientStorageAndRemainingTablesAudit.one_slope_no_revert,
   GuestTransientStorageAndRemainingTablesAudit.slopes_fail,
   by decide,
   by decide⟩

/-- 4. `ts+64` exceeds the `50,000`-per-unit general absorption slope at the tx cap, while all
remaining auxiliary tables (`bal_accounts`, `ev+136`, `new_roots`, `written`/`set_for`) are absorbed. -/
theorem tstore_non_absorbable_and_remaining_tables_absorbed_non_vacuous_and_tight
    (l : List (Nat × Nat)) (B blk : Nat)
    (hS : B + (l.map Prod.snd).sum ≤ S) (hblk : 40 * blk ≤ B * B)
    (hslope : (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum) :
    50000 * (txCap / 100) < buildTicks 158162 ∧
    (5 * 95238 ≤ 50000 * 20 ∧ 2000 ≤ 2100 ∧ 2000 ≤ 5000 ∧ 2000 ≤ 12500) ∧
    (blk + (l.map Prod.fst).sum ≤ 100000000000 ∧
      ¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B →
        T ≤ 50001 * U → blk + T ≤ 100000000000)) :=
  ⟨GuestTransientStorageAndRemainingTablesAudit.tstore_not_absorbable,
   GuestTransientStorageAndRemainingTablesAudit.remaining_absorbed,
   UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.absorption_and_sharp_threshold_non_vacuous_and_tight
     l B blk hS hblk hslope⟩

/-- 5. Unconditional `PanSimp` to `StackToLab` safety chain without `hcall`: `StackNoSt`, `NoStubCall`,
`FlattenVisitsSt = false`, and `progToSectionHOL` section identity preservation. -/
theorem unconditional_pan_to_stack_to_lab_chain_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) :
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true)) ∧
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
       (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) ∧
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
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)) :=
  ⟨WordToWordNoStubCall.panToStackNames_NoSt_and_NoStubCall_unconditional arch prog wc ac perf info j bd ptr f,
   PanToStackToLabUnconditionalNoStoreConsts.panToLabSection_unconditional arch prog wc ac perf info j bd ptr f,
   UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.unconditional_section_non_vacuous_and_tight
     arch prog wc ac perf info j bd ptr f⟩

/-- 6. Non-vacuity and sharpness of `StackNoSt` / `FlattenVisitsSt` on explicit `.storeConsts`, combined
with the 19-table core inventory including `"ts+64"`. -/
theorem store_consts_discrimination_and_core_inventory_non_vacuous_and_tight
    (tail : Bool) (sid next : Nat) (cs bs : List Nat) :
    (StackNoSt (.seq .skip (.storeConsts 0 1 none) : HolProg width) = false ∧
      FlattenVisitsSt (.seq .skip (.storeConsts 0 1 none) : HolProg width) = true ∧
      StackToLab.flattenHOL tail (.storeConsts 0 1 none : HolProg width) sid next cs bs =
        (.list [], false, next)) ∧
    (coreHtabInventory.length = 19 ∧ coreHtabInventory.Nodup ∧
      "ts+64" ∈ coreHtabInventory ∧
      40 * 100000000000 = S * S ∧
      0 + 2000000 ≤ S ∧ 100000000000 = 50000 * 2000000 ∧
      50001 * 2000000 > 100000000000) :=
  ⟨UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.store_consts_discrimination_non_vacuous_and_tight
     tail sid next cs bs,
   UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.inventory_and_threshold_endpoints_non_vacuous_and_tight⟩

/-- 7. Shared 11-table storage absorption (`156,088,992,805`), `< 0.26%` lower witness bracket, and
combined margin `3,684,523,009` with no-revert `ts+64` block build (`740,946,409,660`). -/
theorem shared_eleven_tables_and_transient_joint_margin_non_vacuous_and_tight
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS : B + u2 + u3 + u4 ≤ S)
    (hblk : 40 * blk ≤ B * B) (hloc : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7_989 * u2)
    (h3 : 30 * t3 ≤ 5 * 5_611 * u3)
    (h4 : 60 * t4 ≤ (M + 2_280) * u4) :
    blk + 13 * loc + t2 + t3 + t4 ≤ 151_929_428_571 ∧
    (kPanElevenTablesShared = 156088992805 ∧
      (feasible witness ∧ coupledCost witness = 155688931265 ∧
       coupledCost witness ≤ kPanElevenTablesShared ∧
       kPanElevenTablesShared - coupledCost witness = 400061540 ∧
       400061540 * 10000 < 26 * 156088992805 ∧
       400061540 * 10000 < 26 * 155688931265)) ∧
    (740946409660 < yukon ∧ 156088992805 + 740946409660 < yukon ∧
      yukon - (156088992805 + 740946409660) = 3684523009) :=
  ⟨(UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.shared_eleven_tables_absorption_non_vacuous_and_tight
      B u2 u3 u4 blk loc t2 t3 t4 hS hblk hloc h2 h3 h4).1,
   UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.eleven_table_bracket_non_vacuous_and_tight,
   GuestTransientStorageAndRemainingTablesAudit.one_slope_no_revert⟩

/-- 8. Strictly increasing 50-budget portfolio under Yukon (`900,719,925,474`) and 50 validated JSON
claim payloads (`≤ 128` bytes). -/
theorem fifty_budget_portfolio_and_payloads_non_vacuous_and_tight :
    (portfolio.length = 50 ∧ portfolio.Pairwise (· < ·) ∧
      (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
      portfolio.take 48 = ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster.portfolio) ∧
    (fiftyClaims.length = 50 ∧
      fiftyClaims.map Prod.fst = portfolio ∧
      (∀ entry ∈ fiftyClaims,
        entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true)) :=
  ⟨UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.fifty_shape_non_vacuous_and_tight,
   UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.fifty_claim_payloads_non_vacuous_and_tight⟩

/-- 9. Explicit finite semantic certificates across all 50 budgets conditional on the base certificate,
paired with `ts+64` no-revert Yukon headroom. -/
theorem fifty_finite_certificates_and_transient_audit_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    ((portfolio.length = 50 ∧ portfolio.Pairwise (· < ·) ∧
       ∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
      (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
    buildTicks 158162 = 62537650205 ∧
    11 * buildTicks 158162 + buildTicks 145647 = 740946409660 ∧
    2 * (11 * buildTicks 158162 + buildTicks 145647) = 1481892819320 ∧
    (740946409660 < yukon ∧ 156088992805 + 740946409660 < yukon ∧
      yukon - (156088992805 + 740946409660) = 3684523009) :=
  ⟨UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.fifty_finite_certificates_non_vacuous_and_tight cert,
   GuestTransientStorageAndRemainingTablesAudit.tx_build,
   GuestTransientStorageAndRemainingTablesAudit.block_build,
   GuestTransientStorageAndRemainingTablesAudit.block_with_revert,
   GuestTransientStorageAndRemainingTablesAudit.one_slope_no_revert⟩

/-- 10. Grand self-contained synthesis combining the `ts+64` transient storage and remaining-tables audit,
the unconditional `PanSimp`-to-`StackToLab` safety chain without `hcall`, and the 50-budget portfolio
and certificates under Yukon. -/
theorem self_contained_transient_storage_and_fifty_budget_master_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (k : Nat) (hk : intrinsic + keyGas * k ≤ txCap)
    (l : List (Nat × Nat)) (B blk : Nat)
    (hS : B + (l.map Prod.snd).sum ≤ S) (hblk : 40 * blk ≤ B * B)
    (hslope : (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum)
    (cert : CertificateAt 1212035192) :
    (k ≤ 158162 ∧
      (intrinsic + keyGas * 158162 ≤ txCap ∧ txCap < intrinsic + keyGas * 158163) ∧
      (11 * txCap + intrinsic + keyGas * 145647 ≤ blockGas ∧
        blockGas < 11 * txCap + intrinsic + keyGas * 145648) ∧
      buildTicks 158162 = 62537650205 ∧
      11 * buildTicks 158162 + buildTicks 145647 = 740946409660 ∧
      2 * (11 * buildTicks 158162 + buildTicks 145647) = 1481892819320 ∧
      (740946409660 < yukon ∧ 156088992805 + 740946409660 < yukon ∧
        yukon - (156088992805 + 740946409660) = 3684523009) ∧
      50000 * (txCap / 100) < buildTicks 158162 ∧
      (5 * 95238 ≤ 50000 * 20 ∧ 2000 ≤ 2100 ∧ 2000 ≤ 5000 ∧ 2000 ≤ 12500)) ∧
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
    ((portfolio.length = 50 ∧ portfolio.Pairwise (· < ·) ∧
       ∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
      (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K))) ∧
    (fiftyClaims.length = 50 ∧
      fiftyClaims.map Prod.fst = portfolio ∧
      (∀ entry ∈ fiftyClaims,
        entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true)) :=
  ⟨⟨GuestTransientStorageAndRemainingTablesAudit.keys_le k hk,
    GuestTransientStorageAndRemainingTablesAudit.keys_per_tx,
    GuestTransientStorageAndRemainingTablesAudit.block_packing,
    GuestTransientStorageAndRemainingTablesAudit.tx_build,
    GuestTransientStorageAndRemainingTablesAudit.block_build,
    GuestTransientStorageAndRemainingTablesAudit.block_with_revert,
    GuestTransientStorageAndRemainingTablesAudit.one_slope_no_revert,
    GuestTransientStorageAndRemainingTablesAudit.tstore_not_absorbable,
    GuestTransientStorageAndRemainingTablesAudit.remaining_absorbed⟩,
   UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.unconditional_section_non_vacuous_and_tight
     arch prog wc ac perf info j bd ptr f,
   UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.absorption_and_sharp_threshold_non_vacuous_and_tight
     l B blk hS hblk hslope,
   UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.fifty_finite_certificates_non_vacuous_and_tight cert,
   UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.fifty_claim_payloads_non_vacuous_and_tight⟩

#print axioms transient_storage_tx_cap_and_packing_non_vacuous_and_tight
#print axioms transient_storage_build_and_revert_costs_non_vacuous_and_tight
#print axioms transient_storage_slope_envelope_and_revert_failure_non_vacuous_and_tight
#print axioms tstore_non_absorbable_and_remaining_tables_absorbed_non_vacuous_and_tight
#print axioms unconditional_pan_to_stack_to_lab_chain_non_vacuous_and_tight
#print axioms store_consts_discrimination_and_core_inventory_non_vacuous_and_tight
#print axioms shared_eleven_tables_and_transient_joint_margin_non_vacuous_and_tight
#print axioms fifty_budget_portfolio_and_payloads_non_vacuous_and_tight
#print axioms fifty_finite_certificates_and_transient_audit_non_vacuous_and_tight
#print axioms self_contained_transient_storage_and_fifty_budget_master_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedTransientStorageAndFiftyBudgetSynth
