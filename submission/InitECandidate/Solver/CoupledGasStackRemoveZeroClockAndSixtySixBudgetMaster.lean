import InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster
import InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock
import InitECandidate.Solver.FullBlockTransientProbesAndSixtyFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Shared-gas absorption and exact collision-run caps, native StackRemove
simulations with zero additional clock, and a strictly ordered 66-budget
portfolio. Collision slopes are explicit assumptions, not consequences of
salting. Finite certificates require the semantic base certificate.
The imported StackRemove semantics retains its documented carrier limits. -/
namespace InitECandidate.Solver.CoupledGasStackRemoveZeroClockAndSixtySixBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster
open _root_.InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster (subHeap subMemo)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption (S)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.YukonVerifyScriptAudit (validFiniteClaim)

abbrev Previous := FullBlockTransientProbesAndSixtyFourBudgetMaster.portfolio

def portfolio : List Nat := Previous ++ [880629318275, 880629318276]

def sixtySixClaims : List (Nat × String) :=
  FullBlockTransientProbesAndSixtyFourBudgetMaster.sixtyFourClaims ++
  [(880629318275, "{\"K\":880629318275}"),
   (880629318276, "{\"K\":880629318276}")]

def SixtySixShape : Prop :=
  portfolio.length = 66 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 64 = Previous ∧
  portfolio.drop 64 = [880629318275, 880629318276] ∧
  portfolio.getLast? = some 880629318276 ∧ yukon = 900719925474

def ClaimPayloads : Prop :=
  sixtySixClaims.length = 66 ∧ sixtySixClaims.map Prod.fst = portfolio ∧
  (∀ e ∈ sixtySixClaims, e.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim e.1 e.2 = true) ∧
  sixtySixClaims.take 64 = FullBlockTransientProbesAndSixtyFourBudgetMaster.sixtyFourClaims

/-- The general shared-gas exchange rule, its attained endpoint and sharp slope. -/
theorem general_side_regime_absorption_non_vacuous_and_tight :
    (∀ (l : List (Nat × Nat)) (B blk : Nat),
      B + (l.map Prod.snd).sum ≤ S → 40 * blk ≤ B * B →
      (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum →
      blk + (l.map Prod.fst).sum ≤ 100000000000) ∧
    (40 * 100000000000 = S * S ∧ 100000000000 + 0 = 100000000000) ∧
    ¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B →
      T ≤ 50001 * U → blk + T ≤ 100000000000) :=
  ⟨GuestExhaustiveHtabInventoryAndSlopeAbsorption.general_side_regime_absorption,
   GuestExhaustiveHtabInventoryAndSlopeAbsorption.absorption_tight, sharp⟩

/-- ts+64 has zero net excess through L = 5000; the first excess is explicit. -/
theorem transient_absorption_non_vacuous_and_tight :
    (∀ L n u B blk : Nat, L ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
      40 * blk ≤ B * B → blk + 10 * L * n ≤ 100000000000) ∧
    (∀ L : Nat, L ≤ 5000 → excess L = 0 ∧
      coupled subHeap L = 224985309693 ∧ coupled subMemo L = 195654540749) ∧
    excess 5001 = 20000000 := by
  refine ⟨absorbed, ?_, excess_first⟩
  intro L hL
  exact ⟨excess_zero L hL, block_unchanged L hL⟩

/-- Exact admissible interval and adjacent accepted/rejected witnesses. -/
theorem one_heap_non_vacuous_and_tight :
    (∀ L : Nat, 1 * coupled subHeap L < yukon ↔ L ≤ 38786) ∧
    1 * coupled subHeap 38786 < yukon ∧
    yukon ≤ 1 * coupled subHeap 38787 := by
  constructor
  · intro L
    unfold coupled excess subHeap yukon
    omega
  · simpa using lmax1_heap

/-- Exact admissible interval and adjacent accepted/rejected witnesses. -/
theorem one_memo_non_vacuous_and_tight :
    (∀ L : Nat, 1 * coupled subMemo L < yukon ↔ L ≤ 40253) ∧
    1 * coupled subMemo 40253 < yukon ∧
    yukon ≤ 1 * coupled subMemo 40254 := by
  constructor
  · intro L
    unfold coupled excess subMemo yukon
    omega
  · simpa using lmax1_memo

/-- Exact admissible interval and adjacent accepted/rejected witnesses. -/
theorem four_heap_non_vacuous_and_tight :
    (∀ L : Nat, 4 * coupled subHeap L < yukon ↔ L ≤ 5009) ∧
    4 * coupled subHeap 5009 < yukon ∧
    yukon ≤ 4 * coupled subHeap 5010 := by
  constructor
  · intro L
    unfold coupled excess subHeap yukon
    omega
  · simpa using lmax4_heap

/-- Exact admissible interval and adjacent accepted/rejected witnesses. -/
theorem four_memo_non_vacuous_and_tight :
    (∀ L : Nat, 4 * coupled subMemo L < yukon ↔ L ≤ 6476) ∧
    4 * coupled subMemo 6476 < yukon ∧
    yukon ≤ 4 * coupled subMemo 6477 := by
  constructor
  · intro L
    unfold coupled excess subMemo yukon
    omega
  · simpa using lmax4_memo

open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

/-- Full constructor simulation contracts; zero clock means zero additional clock. -/
theorem skip_tick_inst_zero_clock_non_vacuous_and_tight :
    (∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.skip, source) = (result, postSource) ∧
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
    (hypothesis : StackSemEvaluate.evaluate (.tick, source) = (result, postSource) ∧
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
    (hypothesis : StackSemEvaluate.evaluate (.inst instruction, source) = (result, postSource) ∧
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
    (hypothesis : StackSemEvaluate.evaluate (.stackLoad register count, source) = (result, postSource) ∧
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
    (hypothesis : StackSemEvaluate.evaluate (.stackStore register count, source) = (result, postSource) ∧
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
    (hypothesis : StackSemEvaluate.evaluate ((.stackFree count), source) = (result, postSource) ∧
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
    (hypothesis : StackSemEvaluate.evaluate ((.stackAlloc count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.stackAlloc count) : HolProg width) pointer),
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F), clock ≤ 1 ∧ (result = none → clock = 0) ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackAlloc count),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget)) :=
  @StackRemoveAllocFreeAndBaseCasesZeroClock.StackSpace.compCorrectStackAllocZ

/-- Exact 64-budget prefix, two new budgets, and the strict Yukon ceiling. -/
theorem sixty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    SixtySixShape := by
  unfold SixtySixShape
  decide

/-- Payload validation and finite execution certificates under the base certificate. -/
theorem sixty_six_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    SixtySixShape ∧ ClaimPayloads ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨sixty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
    ?_, ?_⟩
  · unfold ClaimPayloads
    decide
  · intro K hK
    exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ K (sixty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms general_side_regime_absorption_non_vacuous_and_tight
#print axioms transient_absorption_non_vacuous_and_tight
#print axioms one_heap_non_vacuous_and_tight
#print axioms one_memo_non_vacuous_and_tight
#print axioms four_heap_non_vacuous_and_tight
#print axioms four_memo_non_vacuous_and_tight
#print axioms skip_tick_inst_zero_clock_non_vacuous_and_tight
#print axioms stack_load_store_zero_clock_non_vacuous_and_tight
#print axioms stack_free_zero_clock_non_vacuous_and_tight
#print axioms stack_alloc_zero_clock_non_vacuous_and_tight
#print axioms sixty_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms sixty_six_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.CoupledGasStackRemoveZeroClockAndSixtySixBudgetMaster
