import InitECandidate.Solver.GuestTransientStorageAndRemainingTablesAudit
import InitECandidate.Solver.UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_141. Exact transient-storage tick-model arithmetic, remaining-table slope
absorption, unconditional compiler safety, and fifty explicit finite tiers.
The tick model is the hand-transcribed model of the imported audit, not a new
semantic Guest clock bound. Certificates require the base certificate explicitly.
Transient storage is not included in the remaining-table absorption regime. -/
namespace InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestTransientStorageAndRemainingTablesAudit
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption (S)
open _root_.InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open _root_.InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (NoStubCall)
open _root_.InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts (FlattenVisitsSt)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.YukonVerifyScriptAudit (validFiniteClaim)

/-- The very same ordered tiers and JSON payloads as the imported fifty-tier master. -/
abbrev portfolio := UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.portfolio
abbrev fiftyClaims := UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.fiftyClaims

def FiftyShape : Prop :=
  portfolio.length = 50 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
  portfolio.take 48 = ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster.portfolio

def ClaimPayloads : Prop :=
  fiftyClaims.length = 50 ∧ fiftyClaims.map Prod.fst = portfolio ∧
  ∀ entry ∈ fiftyClaims,
    entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true

/-- The exact per-transaction endpoint plus its universally applicable upper bound. -/
def KeyCap : Prop :=
  (intrinsic + keyGas * 158162 ≤ txCap ∧ txCap < intrinsic + keyGas * 158163) ∧
  ∀ k : Nat, intrinsic + keyGas * k ≤ txCap → k ≤ 158162

def PackingAndBuild : Prop :=
  (11 * txCap + intrinsic + keyGas * 145647 ≤ blockGas ∧
    blockGas < 11 * txCap + intrinsic + keyGas * 145648) ∧
  buildTicks 158162 = 62537650205

def BlockCosts : Prop :=
  11 * buildTicks 158162 + buildTicks 145647 = 740946409660 ∧
  2 * (11 * buildTicks 158162 + buildTicks 145647) = 1481892819320

def OneSlopeMargin : Prop :=
  740946409660 < yukon ∧ 156088992805 + 740946409660 < yukon ∧
  yukon - (156088992805 + 740946409660) = 3684523009

def TransientObstruction : Prop :=
  (50000 * (txCap / 100) < buildTicks 158162) ∧
  (yukon < 1481892819320 ∧ yukon < 2 * 740946409660)

/-- BAL, ev+136, new_roots, written/set_for have the imported gas floors.
The witness-sized nodedb is deliberately outside this gas-based statement. -/
def RemainingTables : Prop :=
  5 * 95238 ≤ 50000 * 20 ∧ 2000 ≤ 2100 ∧ 2000 ≤ 5000 ∧ 2000 ≤ 12500

variable {width : Nat} [NeZero width]

/-- All non-stub bodies after the full compiler chain, without any hcall premise. -/
def CompilerSafety (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) : Prop :=
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
        (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1)

/-- 1. Tight EIP-1153 transaction cap, with the next key excluded. -/
theorem key_cap_non_vacuous_and_tight : KeyCap :=
  ⟨keys_per_tx, keys_le⟩

/-- 2. Tight block packing and exact per-transaction construction cost. -/
theorem packing_and_tx_build_non_vacuous_and_tight : PackingAndBuild :=
  ⟨block_packing, tx_build⟩

/-- 3. The cap controls the monotone construction model; the bound is attained. -/
theorem capped_build_non_vacuous_and_tight :
    (∀ k : Nat, intrinsic + keyGas * k ≤ txCap → buildTicks k ≤ 62537650205) ∧
    (intrinsic + keyGas * 158162 ≤ txCap ∧ buildTicks 158162 = 62537650205) := by
  refine ⟨?_, keys_per_tx.1, tx_build⟩
  intro k hk
  rw [← tx_build]
  exact build_mono k 158162 (keys_le k hk)

/-- 4. Exact construction and rollback costs for the packed block. -/
theorem block_and_revert_non_vacuous_and_tight : BlockCosts :=
  ⟨block_build, block_with_revert⟩

/-- 5. One no-revert slope fits alongside the eleven-table storage envelope. -/
theorem one_slope_margin_non_vacuous_and_tight : OneSlopeMargin :=
  one_slope_no_revert

/-- 6. Revert or a second slope exceeds Yukon; TSTORE cannot use side absorption. -/
theorem transient_obstruction_non_vacuous_and_tight : TransientObstruction :=
  ⟨tstore_not_absorbable, slopes_fail⟩

/-- 7. Remaining tables satisfy the side regime, whose 50,000 threshold is sharp. -/
theorem remaining_absorption_non_vacuous_and_tight
    (l : List (Nat × Nat)) (B blk : Nat)
    (hS : B + (l.map Prod.snd).sum ≤ S) (hblk : 40 * blk ≤ B * B)
    (hslope : (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum) :
    RemainingTables ∧ (blk + (l.map Prod.fst).sum ≤ 100000000000 ∧
      ¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B →
        T ≤ 50001 * U → blk + T ≤ 100000000000)) :=
  ⟨remaining_absorbed,
    UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.absorption_and_sharp_threshold_non_vacuous_and_tight
      l B blk hS hblk hslope⟩

/-- 8. Fifty strictly increasing tiers below Yukon, preserving the original 48. -/
theorem fifty_shape_non_vacuous_and_tight : FiftyShape :=
  UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.fifty_shape_non_vacuous_and_tight

/-- 9. Explicit finite JSON payloads agree with every portfolio entry. -/
theorem fifty_payloads_non_vacuous_and_tight : ClaimPayloads :=
  UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.fifty_claim_payloads_non_vacuous_and_tight

/-- 10. PanSimp through StackToLab: both invariants and no StoreConsts visit. -/
theorem compiler_chain_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) :
    CompilerSafety arch prog wc ac perf info j bd ptr f :=
  UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.unconditional_section_non_vacuous_and_tight
    arch prog wc ac perf info j bd ptr f

/-- 11. Finite certificates are conditional only on the stated base certificate. -/
theorem fifty_certificates_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    FiftyShape ∧ ClaimPayloads ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨fifty_shape_non_vacuous_and_tight, fifty_payloads_non_vacuous_and_tight,
    (UnconditionalNoStoreConstsNoStubCallAndFiftyBudgetMaster.fifty_finite_certificates_non_vacuous_and_tight cert).2⟩

/-- 12. Combined contract. The side-regime premises have the explicit zero allocation
as a simultaneous witness; no premise tries to absorb transient storage.
The base certificate remains a separate conditional semantic obligation. -/
theorem integrated_master_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (l : List (Nat × Nat)) (B blk : Nat)
    (hS : B + (l.map Prod.snd).sum ≤ S) (hblk : 40 * blk ≤ B * B)
    (hslope : (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum)
    (cert : CertificateAt 1212035192) :
    KeyCap ∧ PackingAndBuild ∧ BlockCosts ∧ OneSlopeMargin ∧ TransientObstruction ∧
    RemainingTables ∧
    (∀ k : Nat, intrinsic + keyGas * k ≤ txCap → buildTicks k ≤ 62537650205) ∧
    CompilerSafety arch prog wc ac perf info j bd ptr f ∧
    (blk + (l.map Prod.fst).sum ≤ 100000000000 ∧
      ¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B →
        T ≤ 50001 * U → blk + T ≤ 100000000000)) ∧
    FiftyShape ∧ ClaimPayloads ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    (∃ (l : List (Nat × Nat)) (B blk : Nat),
      B + (l.map Prod.snd).sum ≤ S ∧ 40 * blk ≤ B * B ∧
      (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum) := by
  refine ⟨key_cap_non_vacuous_and_tight, packing_and_tx_build_non_vacuous_and_tight,
    block_and_revert_non_vacuous_and_tight, one_slope_margin_non_vacuous_and_tight,
    transient_obstruction_non_vacuous_and_tight, remaining_absorbed,
    capped_build_non_vacuous_and_tight.1,
    compiler_chain_non_vacuous_and_tight arch prog wc ac perf info j bd ptr f,
    (remaining_absorption_non_vacuous_and_tight l B blk hS hblk hslope).2,
    fifty_shape_non_vacuous_and_tight, fifty_payloads_non_vacuous_and_tight,
    (fifty_certificates_non_vacuous_and_tight cert).2.2, ?_⟩
  exact ⟨[], 0, 0, by decide, by decide, by decide⟩

#print axioms key_cap_non_vacuous_and_tight
#print axioms packing_and_tx_build_non_vacuous_and_tight
#print axioms capped_build_non_vacuous_and_tight
#print axioms block_and_revert_non_vacuous_and_tight
#print axioms one_slope_margin_non_vacuous_and_tight
#print axioms transient_obstruction_non_vacuous_and_tight
#print axioms remaining_absorption_non_vacuous_and_tight
#print axioms fifty_shape_non_vacuous_and_tight
#print axioms fifty_payloads_non_vacuous_and_tight
#print axioms compiler_chain_non_vacuous_and_tight
#print axioms fifty_certificates_non_vacuous_and_tight
#print axioms integrated_master_non_vacuous_and_tight

end InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster
