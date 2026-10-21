import InitECandidate.Solver.GuestWitnessEmptyItemAndPushExactTicksMaster
import InitECandidate.Solver.SelfContainedWitnessEmptyItemPushOneHundredTwelveBudgetSynth
import InitECandidate.Solver.JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_308: self-contained transaction-gas-coupled LP (`perTx = 40782`,
`trueFixed200 = 711625206`, `mainCached200 = 7334885647` at `122x` Yukon),
witness empty-item (`keccakEmpty = 35`) and exact `PUSH31` (`push31 = 54 = 18 * 3`),
full compiler contracts and 114 conditional finite certificates. Joint bounds
retain every gas, dirty-node and witness-byte hypothesis. The cached model
requires a per-code jumpdest cache. Finite certificates remain conditional on
the base semantic certificate. -/
namespace InitECandidate.Solver.SelfContainedTxGasCoupledOneHundredFourteenBudgetSynth

open InitECandidate.Solver
open _root_.InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt
open _root_.InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (Clean)
open _root_.InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall
open _root_.InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural (NoGcCall NoTailHandler)
open Flapjack.Pancake.PanLang
open _root_.InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open _root_.InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.GuestExactSstoreCallLPAndJumpdestDualBoundMaster
  (callTicks)
open _root_.InitECandidate.Solver.GuestWitnessEmptyItemAndPushExactTicksMaster
  (inputBytes fixed200 fixed380 keccakEmpty push31 costC costU
   mainUncached200 mainUncached380)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native

def perTx : Nat := 40782
def trueFixed200 : Nat := fixed200 - 16666 * perTx
def mainCached200 : Nat := trueFixed200 + inputBytes + (214138410040 + 32) / 33
def mainCached380 : Nat := GuestWitnessEmptyItemAndPushExactTicksMaster.mainCached380

/-- Transaction-gas-coupled cached cost: adds `perTx * T` for `T` user transactions. -/
def costTxC (A K B E n2 n17 md ms P T : Nat) : Nat :=
  costC A K B E n2 n17 md ms P + perTx * T

abbrev oneHundredTwelveExplicitFiniteKBugdetTable :=
  JumpdestDualLPOneHundredTenXAndOneHundredTwelveBudgetMaster.oneHundredTwelveExplicitBudgets

abbrev oneHundredFourteenExplicitFiniteKBugdetTable :=
  JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster.oneHundredFourteenExplicitBudgets

abbrev portfolio := oneHundredFourteenExplicitFiniteKBugdetTable

abbrev OneHundredTwelveShape :=
  JumpdestDualLPOneHundredTenXAndOneHundredTwelveBudgetMaster.OneHundredTwelveShape

abbrev OneHundredFourteenShape :=
  JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster.OneHundredFourteenShape

/-- 1. Exact per-tx and leaf constants (`perTx = 40782`, `trueFixed200 = 711625206`,
`keccakEmpty = 35`, `push31 = 54 = 18 * 3`). -/
theorem per_tx_true_fixed_and_leaf_counts_non_vacuous_and_tight :
    perTx = 40782 ∧ trueFixed200 = 711625206 ∧
    fixed200 - trueFixed200 = 16666 * perTx ∧
    perTx < 18 * 12000 ∧
    keccakEmpty = 35 ∧ push31 = 54 ∧ push31 = 18 * 3 ∧
    callTicks = 67884 ∧ fixed200 = 1391298018 ∧ fixed380 = 1675717026 := by
  decide

/-- 2. Transaction-gas-coupled cached joint LP at 200M gas (`12,000` intrinsic gas per user tx). -/
theorem cached200_tx_coupled_non_vacuous_and_tight (A K B E n2 n17 md ms P T : Nat)
    (hg : 2400 * A + 2100 * K + P + 12000 * T ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    33 * costTxC A K B E n2 n17 md ms P T ≤ 214138410040 := by
  unfold costTxC costC perTx inputBytes at *; omega

/-- 3. Transaction-gas-coupled cached joint LP at 380M gas (`12,000` intrinsic gas per user tx). -/
theorem cached380_tx_coupled_non_vacuous_and_tight (A K B E n2 n17 md ms P T : Nat)
    (hg : 2400 * A + 2100 * K + P + 12000 * T ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    11803 * costTxC A K B E n2 n17 md ms P T ≤ 114947567578464 := by
  unfold costTxC costC perTx inputBytes at *; omega

/-- 4. Uncached full LP at 200M gas. -/
theorem uncached200_non_vacuous_and_tight (A K B E n2 n17 md ms P C T : Nat)
    (hg : 2400 * A + 2100 * K + P + 126 * C + 12000 * T ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K B E n2 n17 md ms P C T ≤ 25461560820280 :=
  SelfContainedWitnessEmptyItemPushOneHundredTwelveBudgetSynth.uncached200_non_vacuous_and_tight
    A K B E n2 n17 md ms P C T hg h1 h2 hb he hw

/-- 5. Uncached full LP at 380M gas. -/
theorem uncached380_non_vacuous_and_tight (A K B E n2 n17 md ms P C T : Nat)
    (hg : 2400 * A + 2100 * K + P + 126 * C + 12000 * T ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K B E n2 n17 md ms P C T ≤ 47863280820280 :=
  SelfContainedWitnessEmptyItemPushOneHundredTwelveBudgetSynth.uncached380_non_vacuous_and_tight
    A K B E n2 n17 md ms P C T hg h1 h2 hb he hw

/-- 6. Cached Guest slopes with tx-gas coupling: `mainCached200 = 7,334,885,647` (`122x` Yukon passes, `123x` fails)
and `mainCached380 = 11,548,778,048` (`77x` Yukon passes, `78x` fails). -/
theorem cached_slopes_non_vacuous_and_tight :
    mainCached200 = 7334885647 ∧ 122 * mainCached200 < yukon ∧
    yukon < 123 * mainCached200 ∧ mainCached380 = 11548778048 ∧
    77 * mainCached380 < yukon ∧ yukon < 78 * mainCached380 := by
  decide

/-- 7. Uncached Guest slopes (`8x` at 200M, `4x` at 380M) and `135x` non-attainment. -/
theorem uncached_slopes_and_no_135_non_vacuous_and_tight :
    (mainUncached200 = 111614505033 ∧ 8 * mainUncached200 < yukon ∧
      yukon < 9 * mainUncached200 ∧ mainUncached380 = 208876066898 ∧ 4 * mainUncached380 < yukon ∧
      yukon < 5 * mainUncached380) ∧
    (yukon / 135 = 6671999447 ∧ yukon < 135 * mainCached200) := by
  decide

/-- 8. Strict progression of cached 200M bounds: `7,334,885,647` (`122x`) < `8,014,558,459` (`112x`)
< `8,145,414,250` (`110x`) < `8,298,113,205` (`108x`). -/
theorem cached_progression_one_hundred_twenty_two_x_non_vacuous_and_tight :
    mainCached200 = 7334885647 ∧
    GuestWitnessEmptyItemAndPushExactTicksMaster.mainCached200 = 8014558459 ∧
    GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached200 = 8145414250 ∧
    GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main200 = 8298113205 ∧
    mainCached200 < GuestWitnessEmptyItemAndPushExactTicksMaster.mainCached200 ∧
    GuestWitnessEmptyItemAndPushExactTicksMaster.mainCached200 - mainCached200 = 679672812 ∧
    112 * GuestWitnessEmptyItemAndPushExactTicksMaster.mainCached200 < yukon ∧
    yukon < 113 * GuestWitnessEmptyItemAndPushExactTicksMaster.mainCached200 := by
  decide

/-- 9. Exact margins below Yukon at `122x` (200M) and `77x` (380M). -/
theorem margins_non_vacuous_and_tight :
    yukon - 122 * mainCached200 = 5863876540 ∧
    yukon - 77 * mainCached380 = 11464015778 ∧
    123 * mainCached200 - yukon = 1471009107 := by
  decide

/-- 10. User sections, base cases and stack-space simulation contracts. -/
theorem user_sections_base_cases_stack_space_non_vacuous_and_tight :
    (NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe) ∧
    (((∀ {width : Nat} [NeZero width] {C F : Type}
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
       | _ => stateRelHOL jump bounds pointer postSource postTarget))) ∧
    ((∀ {width : Nat} [NeZero width] {C F : Type}
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
       | _ => stateRelHOL jump bounds pointer postSource postTarget)))) ∧
    (((∀ {width : Nat} [NeZero width] {C F : Type}
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
       | _ => stateRelHOL jump bounds pointer postSource postTarget))) ∧
    ((∀ {width : Nat} [NeZero width] {C F : Type}
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
       | _ => stateRelHOL jump bounds pointer postSource postTarget)))) :=
  SelfContainedWitnessEmptyItemPushOneHundredTwelveBudgetSynth.user_sections_base_cases_stack_space_non_vacuous_and_tight

/-- 11. Exactly 114 increasing finite budgets below Yukon (`[900710000000, 900715000000]`, margin `4925474`). -/
theorem one_hundred_fourteen_budget_table_non_vacuous_and_tight :
    OneHundredFourteenShape ∧ OneHundredTwelveShape ∧
    oneHundredFourteenExplicitFiniteKBugdetTable.length = 114 ∧
    oneHundredFourteenExplicitFiniteKBugdetTable.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredFourteenExplicitFiniteKBugdetTable, K < 900719925474) ∧
    oneHundredFourteenExplicitFiniteKBugdetTable.drop 112 = [900710000000, 900715000000] ∧
    oneHundredTwelveExplicitFiniteKBugdetTable.getLast? = some 900700000000 ∧
    oneHundredFourteenExplicitFiniteKBugdetTable.getLast? = some 900715000000 ∧
    yukon - 900715000000 = 4925474 := by
  refine ⟨JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster.one_hundred_fourteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
    SelfContainedWitnessEmptyItemPushOneHundredTwelveBudgetSynth.one_hundred_twelve_budget_table_non_vacuous_and_tight.1, ?_⟩
  decide

/-- 12. Conditional finite certificates across all 114 budgets. -/
theorem one_hundred_fourteen_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredFourteenShape ∧
    (∀ K ∈ oneHundredFourteenExplicitFiniteKBugdetTable,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster.one_hundred_fourteen_budget_certificates_non_vacuous_and_tight cert

#print axioms per_tx_true_fixed_and_leaf_counts_non_vacuous_and_tight
#print axioms cached200_tx_coupled_non_vacuous_and_tight
#print axioms cached380_tx_coupled_non_vacuous_and_tight
#print axioms uncached200_non_vacuous_and_tight
#print axioms uncached380_non_vacuous_and_tight
#print axioms cached_slopes_non_vacuous_and_tight
#print axioms uncached_slopes_and_no_135_non_vacuous_and_tight
#print axioms cached_progression_one_hundred_twenty_two_x_non_vacuous_and_tight
#print axioms margins_non_vacuous_and_tight
#print axioms user_sections_base_cases_stack_space_non_vacuous_and_tight
#print axioms one_hundred_fourteen_budget_table_non_vacuous_and_tight
#print axioms one_hundred_fourteen_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedTxGasCoupledOneHundredFourteenBudgetSynth
