import InitECandidate.Solver.Wave8Stage.WordToStackCostCalls
import InitECandidate.Solver.Wave8Stage.WordToStackZeroClock
import InitECandidate.Solver.Wave8Stage.WordToStackSharedClock

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordToStackCostSimulation
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage
open WordToStackBounded WordToStackSourceCost WordToStackZeroClock

/-- Full quantitative native simulation at the actual source execution cost. -/
theorem compCorrect {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) :
    ∀ (program : WordLangProgHOL (BitVec width))
      (source : WordSemStateFiniteExact width (Nat × C) F),
    SimulationB ac program source (sourceCost program source) := by
  apply WordSemStateFiniteExact.evaluate_ind (fun p s => SimulationB ac p s (sourceCost p s))
  refine ⟨?skip, ?alloc, ?storeConsts, ?move, ?inst, ?assign, ?get, ?set, ?opCurrHeap, ?store,
    ?tick, ?mustTerminate, ?seq, ?ret, ?raise, ?brk, ?cont, ?ite, ?loop, ?locValue, ?install,
    ?codeBufferWrite, ?dataBufferWrite, ?ffi, ?shareInst, ?call⟩
  case skip =>
    simp only [sourceCost]
    exact fun s k f frame _ _ _ _ _ _ _ _ _ h => Control.compCorrectSkip ac k f frame s _ _ _ _ _ _ _ _ _ h
  case alloc =>
    simp only [sourceCost]
    exact fun n names s k f frame _ _ _ _ _ _ _ _ _ h =>
    Alloc.compCorrectAlloc ac n names k f frame s _ _ _ _ _ _ _ _ _ h
  case storeConsts =>
    simp only [sourceCost]
    exact fun t1 t2 a o w s => StoreConsts.compCorrectStoreConsts ac t1 t2 a o w s
  case move =>
    simp only [sourceCost]
    exact fun pri moves s => MoveFull.compCorrectMove ac pri moves s
  case inst =>
    simp only [sourceCost]
    exact fun i s => Inst.compCorrectInst ac i s
  case assign =>
    simp only [sourceCost]
    exact fun v e s k f frame _ _ _ _ _ _ _ _ _ h =>
    Flat.compCorrectAssign ac v e k f frame s _ _ _ _ _ _ _ _ _ h
  case get =>
    simp only [sourceCost]
    exact fun v name s => Get.compCorrectGet ac v name s
  case set =>
    simp only [sourceCost]
    exact fun v e s => Set.compCorrectSet ac v e s
  case opCurrHeap =>
    simp only [sourceCost]
    exact fun b d src s => OpCurrHeap.compCorrectOpCurrHeap ac b d src s
  case store =>
    simp only [sourceCost]
    exact fun e v s k f frame _ _ _ _ _ _ _ _ _ h =>
    Flat.compCorrectStore ac e v k f frame s _ _ _ _ _ _ _ _ _ h
  case tick =>
    simp only [sourceCost]
    exact fun s k f frame _ _ _ _ _ _ _ _ _ h => Clock.compCorrectTick ac k f frame s _ _ _ _ _ _ _ _ _ h
  case mustTerminate =>
    simp only [sourceCost]
    exact fun p s _ k f frame _ _ _ _ _ _ _ _ _ h =>
    Clock.compCorrectMustTerminate ac p k f frame s _ _ _ _ _ _ _ _ _ h
  case seq => exact fun c1 c2 s ih => WordToStackCostComposition.compCorrectSeq ac c1 c2 s ih
  case ret =>
    simp only [sourceCost]
    exact fun n ms s => Return.compCorrectReturn ac n ms s
  case raise =>
    simp only [sourceCost]
    exact fun n s => WordToStackBounded.compCorrectRaise ac n s
  case brk =>
    simp only [sourceCost]
    exact fun l s k f frame _ _ _ _ _ _ _ _ _ h => Control.compCorrectBreak ac l k f frame s _ _ _ _ _ _ _ _ _ h
  case cont =>
    simp only [sourceCost]
    exact fun l s k f frame _ _ _ _ _ _ _ _ _ h => Control.compCorrectContinue ac l k f frame s _ _ _ _ _ _ _ _ _ h
  case ite => exact fun cmp r ri c1 c2 s ih => WordToStackCostComposition.compCorrectIf ac cmp r ri c1 c2 s ih
  case loop => exact fun names c exitNames s ih => WordToStackCostComposition.compCorrectLoop ac names exitNames c s ih
  case locValue =>
    simp only [sourceCost]
    exact fun r l s => LocValue.compCorrectLocValue ac r l s
  case install =>
    simp only [sourceCost]
    exact fun p l dp dl names s => Install.compCorrectInstall ac p l dp dl names s
  case codeBufferWrite =>
    simp only [sourceCost]
    exact fun r1 r2 s => CodeBufferWrite.compCorrectCodeBufferWrite ac r1 r2 s
  case dataBufferWrite =>
    simp only [sourceCost]
    exact fun r1 r2 s => DataBufferWrite.compCorrectDataBufferWrite ac r1 r2 s
  case ffi =>
    simp only [sourceCost]
    exact fun i p1 l1 p2 l2 names s k f frame _ _ _ _ _ _ _ _ _ h =>
    FFI.compCorrectFFI ac i p1 l1 p2 l2 names k f frame s _ _ _ _ _ _ _ _ _ h
  case shareInst =>
    simp only [sourceCost]
    exact fun op v e s => WordToStackSharedClock.compCorrectShareInst ac op v e s
  case call => exact fun ret dest args handler s ih => WordToStackCostCalls.compCorrectCall ac ret dest args handler s ih


end InitECandidate.Solver.Wave8Stage.WordToStackCostSimulation
