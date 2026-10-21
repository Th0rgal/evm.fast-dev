import InitECandidate.Solver.GuestEndToEndStartToHaltAndCoupledMptMaster
import InitECandidate.Solver.CoupledGasFullBlockAndSixtyFourBudgetBridge
import InitECandidate.Solver.CoupledGasStackRemoveZeroClockAndSixtySixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Exact arithmetic envelope for coupled MPT writes and shared-gas transient
storage, together with the native StackRemove base-case simulations. The collision
run bounds are explicit parameters; this does not bound the remaining end-to-end
pre/post-EVM work. Zero clock is zero *additional* clock (allocation may need one
on an exceptional result). Finite certificates require the semantic base certificate.
No bounded proof-library module is imported here. -/
namespace InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster (coupled excess)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.YukonVerifyScriptAudit (validFiniteClaim)

abbrev Previous := CoupledGasStackRemoveZeroClockAndSixtySixBudgetMaster.portfolio

def block_total_coupled_mpt : Nat :=
  GuestFullBlockWithTransientStorageAndProbesMaster.subHeap - 619060000

def block_total_memo_coupled_mpt : Nat :=
  GuestFullBlockWithTransientStorageAndProbesMaster.subMemo - 619060000

def portfolio : List Nat := Previous ++ [880629318277, 880629318278]

def sixtyEightClaims : List (Nat × String) :=
  CoupledGasStackRemoveZeroClockAndSixtySixBudgetMaster.sixtySixClaims ++
  [(880629318277, "{\"K\":880629318277}"),
   (880629318278, "{\"K\":880629318278}")]

def SixtyEightShape : Prop :=
  portfolio.length = 68 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 66 = Previous ∧
  portfolio.drop 66 = [880629318277, 880629318278] ∧
  portfolio.getLast? = some 880629318278 ∧ yukon = 900719925474

def ClaimPayloads : Prop :=
  sixtyEightClaims.length = 68 ∧ sixtyEightClaims.map Prod.fst = portfolio ∧
  (∀ e ∈ sixtyEightClaims, e.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim e.1 e.2 = true) ∧
  sixtyEightClaims.take 66 =
    CoupledGasStackRemoveZeroClockAndSixtySixBudgetMaster.sixtySixClaims

/-- Shared 200M gas budget: attained written-key bound and exact mpt_set saving. -/
theorem mpt_write_saving_non_vacuous_and_tight :
    (∀ k : Nat, 21 * k ≤ 2000000 → k ≤ 95238 ∧ 130000 * k ≤ 12380940000) ∧
    (21 * 95238 ≤ 2000000 ∧ 2000000 < 21 * 95239) ∧
    130000 * 95238 = 12380940000 ∧
    13000000000 - 130000 * 95238 = 619060000 := by
  refine ⟨?_, GuestEndToEndStartToHaltAndCoupledMptMaster.dirty_keys_tight,
    by decide, GuestEndToEndStartToHaltAndCoupledMptMaster.coupling_gain⟩
  intro k hk
  exact ⟨GuestEndToEndStartToHaltAndCoupledMptMaster.dirty_keys k hk,
    GuestEndToEndStartToHaltAndCoupledMptMaster.root_coupled k hk⟩

/-- Exact reconciled subtotals, fourfold fit and the first rejected integer factor. -/
theorem coupled_mpt_totals_non_vacuous_and_tight :
    block_total_coupled_mpt = 224366249693 ∧
    block_total_memo_coupled_mpt = 195035480749 ∧
    4 * block_total_memo_coupled_mpt = 780141922996 ∧
    4 * block_total_memo_coupled_mpt < yukon ∧
    4 * block_total_coupled_mpt < yukon ∧
    yukon ≤ 5 * block_total_memo_coupled_mpt ∧
    yukon ≤ 5 * block_total_coupled_mpt := by decide

/-- Exact admissible interval, attained endpoint, and first rejected run. -/
theorem one_heap_non_vacuous_and_tight :
    (∀ L : Nat, 1 * coupled block_total_coupled_mpt L < yukon ↔ L ≤ 38817) ∧
    1 * coupled block_total_coupled_mpt 38817 < yukon ∧
    yukon ≤ 1 * coupled block_total_coupled_mpt 38818 := by
  constructor
  · intro L
    unfold coupled excess block_total_coupled_mpt
      GuestFullBlockWithTransientStorageAndProbesMaster.subHeap yukon
    omega
  · decide

/-- Exact admissible interval, attained endpoint, and first rejected run. -/
theorem one_memo_non_vacuous_and_tight :
    (∀ L : Nat, 1 * coupled block_total_memo_coupled_mpt L < yukon ↔ L ≤ 40284) ∧
    1 * coupled block_total_memo_coupled_mpt 40284 < yukon ∧
    yukon ≤ 1 * coupled block_total_memo_coupled_mpt 40285 := by
  constructor
  · intro L
    unfold coupled excess block_total_memo_coupled_mpt
      GuestFullBlockWithTransientStorageAndProbesMaster.subMemo yukon
    omega
  · decide

/-- Exact admissible interval, attained endpoint, and first rejected run. -/
theorem four_heap_non_vacuous_and_tight :
    (∀ L : Nat, 4 * coupled block_total_coupled_mpt L < yukon ↔ L ≤ 5040) ∧
    4 * coupled block_total_coupled_mpt 5040 < yukon ∧
    yukon ≤ 4 * coupled block_total_coupled_mpt 5041 := by
  constructor
  · intro L
    unfold coupled excess block_total_coupled_mpt
      GuestFullBlockWithTransientStorageAndProbesMaster.subHeap yukon
    omega
  · decide

/-- Exact admissible interval, attained endpoint, and first rejected run. -/
theorem four_memo_non_vacuous_and_tight :
    (∀ L : Nat, 4 * coupled block_total_memo_coupled_mpt L < yukon ↔ L ≤ 6507) ∧
    4 * coupled block_total_memo_coupled_mpt 6507 < yukon ∧
    yukon ≤ 4 * coupled block_total_memo_coupled_mpt 6508 := by
  constructor
  · intro L
    unfold coupled excess block_total_memo_coupled_mpt
      GuestFullBlockWithTransientStorageAndProbesMaster.subMemo yukon
    omega
  · decide

open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

/-- Full constructor simulation contracts; zero clock means zero additional clock. -/
theorem skip_tick_inst_zero_clock_non_vacuous_and_tight :
    (∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (_hypothesis : StackSemEvaluate.evaluate (.skip, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.skip : HolProg width) pointer),
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer .skip,
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget)) ∧
    (∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (_hypothesis : StackSemEvaluate.evaluate (.tick, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.tick : HolProg width) pointer),
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer .tick,
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget)) ∧
    (∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (instruction : HolInst width)
    (_hypothesis : StackSemEvaluate.evaluate (.inst instruction, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.inst instruction) pointer),
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.inst instruction),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget)) :=
  ⟨@StackRemoveAllocFreeAndBaseCasesZeroClock.Atoms.compCorrectSkipZ, @StackRemoveAllocFreeAndBaseCasesZeroClock.Control.compCorrectTickZ, @StackRemoveAllocFreeAndBaseCasesZeroClock.Instructions.compCorrectInstZ⟩

/-- Full constructor simulation contracts; zero clock means zero additional clock. -/
theorem stack_load_store_zero_clock_non_vacuous_and_tight :
    (∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register count pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (_hypothesis : StackSemEvaluate.evaluate (.stackLoad register count, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackLoad register count : HolProg width) pointer),
    ∃ postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackLoad register count),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget)) ∧
    (∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register count pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (_hypothesis : StackSemEvaluate.evaluate (.stackStore register count, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackStore register count : HolProg width) pointer),
    ∃ postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackStore register count),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget)) :=
  ⟨@StackRemoveAllocFreeAndBaseCasesZeroClock.StackMemory.compCorrectStackLoadZ, @StackRemoveAllocFreeAndBaseCasesZeroClock.StackMemory.compCorrectStackStoreZ⟩

/-- Full constructor simulation contracts; zero clock means zero additional clock. -/
theorem stack_free_zero_clock_non_vacuous_and_tight :
    (∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (count : Nat)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (_hypothesis : StackSemEvaluate.evaluate ((.stackFree count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.stackFree count) : HolProg width) pointer),
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackFree count),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget)) :=
  @StackRemoveAllocFreeAndBaseCasesZeroClock.StackSpace.compCorrectStackFreeZ

/-- Full constructor simulation contracts; zero clock means zero additional clock. -/
theorem stack_alloc_zero_clock_non_vacuous_and_tight :
    (∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (count : Nat)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (_hypothesis : StackSemEvaluate.evaluate ((.stackAlloc count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.stackAlloc count) : HolProg width) pointer),
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F), clock ≤ 1 ∧ (result = none → clock = 0) ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackAlloc count),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget)) :=
  @StackRemoveAllocFreeAndBaseCasesZeroClock.StackSpace.compCorrectStackAllocZ

/-- Exact 66-budget prefix and two new budgets, strictly increasing below Yukon. -/
theorem sixty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    SixtyEightShape := by
  unfold SixtyEightShape
  decide

/-- Valid claim payloads and conditional finite execution certificates for all 68 budgets. -/
theorem sixty_eight_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    SixtyEightShape ∧ ClaimPayloads ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨sixty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
    ?_, ?_⟩
  · unfold ClaimPayloads
    decide
  · intro K hK
    exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ K (sixty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms mpt_write_saving_non_vacuous_and_tight
#print axioms coupled_mpt_totals_non_vacuous_and_tight
#print axioms one_heap_non_vacuous_and_tight
#print axioms one_memo_non_vacuous_and_tight
#print axioms four_heap_non_vacuous_and_tight
#print axioms four_memo_non_vacuous_and_tight
#print axioms skip_tick_inst_zero_clock_non_vacuous_and_tight
#print axioms stack_load_store_zero_clock_non_vacuous_and_tight
#print axioms stack_free_zero_clock_non_vacuous_and_tight
#print axioms stack_alloc_zero_clock_non_vacuous_and_tight
#print axioms sixty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms sixty_eight_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster
