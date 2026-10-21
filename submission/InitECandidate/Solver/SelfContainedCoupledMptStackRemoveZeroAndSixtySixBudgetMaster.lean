import InitECandidate.Solver.GuestEndToEndStartToHaltAndCoupledMptMaster
import InitECandidate.Solver.SelfContainedNoLocValue6CoupledGasAndSixtyFourBudgetMaster
import InitECandidate.Solver.CoupledGasStackRemoveZeroClockAndSixtySixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_183. Coupled MPT model, sharp collision caps, user-section safety,
StackRemove base-case simulations, and 66 conditional finite certificates.
These model costs leave the documented start-to-halt residual obligations open.
Allocation requires at most one additional tick, zero on a normal return.
No unconditional execution certificate or salted collision bound is asserted. -/
namespace InitECandidate.Solver.SelfContainedCoupledMptStackRemoveZeroAndSixtySixBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster (excess coupled)
open _root_.InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster (subHeap subMemo)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- Replace only the independent MPT-write allowance by the shared-gas cap. -/
def block_total_coupled_mpt : Nat := subHeap - 619060000
def block_total_memo_coupled_mpt : Nat := subMemo - 619060000

def coupledMpt (base L : Nat) : Nat := base + excess L

abbrev portfolio := CoupledGasStackRemoveZeroClockAndSixtySixBudgetMaster.portfolio
abbrev SixtySixShape := CoupledGasStackRemoveZeroClockAndSixtySixBudgetMaster.SixtySixShape
abbrev ClaimPayloads := CoupledGasStackRemoveZeroClockAndSixtySixBudgetMaster.ClaimPayloads

/-- Exact shared 200M-gas dirty-key cap, its attained witness, MPT saving,
and its propagation through both cost models for every collision-run length. -/
theorem mpt_coupling_gain_non_vacuous_and_tight :
    (∀ k : Nat, 21 * k ≤ 2000000 → k ≤ 95238 ∧ 130000 * k ≤ 12380940000) ∧
    (21 * 95238 ≤ 2000000 ∧ 2000000 < 21 * 95239) ∧
    13000000000 - 130000 * 95238 = 619060000 ∧
    block_total_coupled_mpt = 224366249693 ∧
    block_total_memo_coupled_mpt = 195035480749 ∧
    (∀ L : Nat,
      coupled subHeap L = coupledMpt block_total_coupled_mpt L + 619060000 ∧
      coupled subMemo L = coupledMpt block_total_memo_coupled_mpt L + 619060000) := by
  refine ⟨?_, GuestEndToEndStartToHaltAndCoupledMptMaster.dirty_keys_tight,
    GuestEndToEndStartToHaltAndCoupledMptMaster.coupling_gain,
    by decide, by decide, ?_⟩
  · intro k h
    exact ⟨GuestEndToEndStartToHaltAndCoupledMptMaster.dirty_keys k h,
      GuestEndToEndStartToHaltAndCoupledMptMaster.root_coupled k h⟩
  · intro L
    unfold coupled coupledMpt block_total_coupled_mpt block_total_memo_coupled_mpt subHeap subMemo
    omega

/-- Exact admissible interval, including its endpoint and first rejection. -/
theorem one_heap_non_vacuous_and_tight :
    (∀ L : Nat, 1 * coupledMpt block_total_coupled_mpt L < yukon ↔ L ≤ 38817) ∧
    1 * coupledMpt block_total_coupled_mpt 38817 < yukon ∧
    yukon ≤ 1 * coupledMpt block_total_coupled_mpt 38818 := by
  constructor
  · intro L
    unfold coupledMpt block_total_coupled_mpt excess subHeap yukon
    omega
  · decide

/-- Exact admissible interval, including its endpoint and first rejection. -/
theorem one_memo_non_vacuous_and_tight :
    (∀ L : Nat, 1 * coupledMpt block_total_memo_coupled_mpt L < yukon ↔ L ≤ 40284) ∧
    1 * coupledMpt block_total_memo_coupled_mpt 40284 < yukon ∧
    yukon ≤ 1 * coupledMpt block_total_memo_coupled_mpt 40285 := by
  constructor
  · intro L
    unfold coupledMpt block_total_memo_coupled_mpt excess subMemo yukon
    omega
  · decide

/-- Exact admissible interval, including its endpoint and first rejection. -/
theorem four_heap_non_vacuous_and_tight :
    (∀ L : Nat, 4 * coupledMpt block_total_coupled_mpt L < yukon ↔ L ≤ 5040) ∧
    4 * coupledMpt block_total_coupled_mpt 5040 < yukon ∧
    yukon ≤ 4 * coupledMpt block_total_coupled_mpt 5041 := by
  constructor
  · intro L
    unfold coupledMpt block_total_coupled_mpt excess subHeap yukon
    omega
  · decide

/-- Exact admissible interval, including its endpoint and first rejection. -/
theorem four_memo_non_vacuous_and_tight :
    (∀ L : Nat, 4 * coupledMpt block_total_memo_coupled_mpt L < yukon ↔ L ≤ 6507) ∧
    4 * coupledMpt block_total_memo_coupled_mpt 6507 < yukon ∧
    yukon ≤ 4 * coupledMpt block_total_memo_coupled_mpt 6508 := by
  constructor
  · intro L
    unfold coupledMpt block_total_memo_coupled_mpt excess subMemo yukon
    omega
  · decide

/-- All user sections exclude section-6 jumps and location values after LabToTarget. -/
theorem panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  SelfContainedNoLocValue6CoupledGasAndSixtyFourBudgetMaster.panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight

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

/-- Exactly 66 strictly increasing budgets below 900719925474. -/
theorem sixty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    SixtySixShape :=
  CoupledGasStackRemoveZeroClockAndSixtySixBudgetMaster.sixty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight

/-- The base semantic certificate is an explicit premise; payloads and safety
are unconditional. Each certified submission uses the corresponding finite K. -/
theorem sixty_six_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe ∧
    SixtySixShape ∧ ClaimPayloads ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight.2,
   CoupledGasStackRemoveZeroClockAndSixtySixBudgetMaster.sixty_six_budget_certificates_non_vacuous_and_tight cert⟩

#print axioms mpt_coupling_gain_non_vacuous_and_tight
#print axioms one_heap_non_vacuous_and_tight
#print axioms one_memo_non_vacuous_and_tight
#print axioms four_heap_non_vacuous_and_tight
#print axioms four_memo_non_vacuous_and_tight
#print axioms panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
#print axioms skip_tick_inst_zero_clock_non_vacuous_and_tight
#print axioms stack_load_store_zero_clock_non_vacuous_and_tight
#print axioms stack_free_zero_clock_non_vacuous_and_tight
#print axioms stack_alloc_zero_clock_non_vacuous_and_tight
#print axioms sixty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms sixty_six_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedCoupledMptStackRemoveZeroAndSixtySixBudgetMaster
