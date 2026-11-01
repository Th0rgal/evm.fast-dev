import InitECandidate.Solver.Wave8Stage.CrepCostLeaf

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.CrepCostTick
open Flapjack CrepSourceCost
open Pancake.CrepToLoop.Proofs.NCompileCorrect

theorem compCorrectTick {width : Nat} [NeZero width] {σ : Type}
    (v1 : CrepSemHOLState width σ)
    (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
    (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact)
    (live : NumSet)
    (hEval : evalCrepSemHOLProgExact v1 (.tick : CrepProgHOL width) = (res, s1))
    (hNotError : res ≠ some .error)
    (hState : crepToLoopStateRelExact v1 t)
    (hMem : crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs)
    (hGlobals : crepToLoopGlobalsRelHOLExact v1.globals t.globals)
    (hCode : crepToLoopCodeRelExact ctxt v1.code t.code)
    (hLocals : crepToLoopLocalsRelExact ctxt live v1.locals t.locals) :
    ∃ (ck : Nat) (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (t1 : LoopSemStateFiniteExact width σ),
      LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt live .tick)
          { t with clock := t.clock + ck } = (res1, t1) ∧
        crepToLoopStateRelExact s1 t1 ∧
        crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
        crepToLoopCodeRelExact ctxt s1.code t1.code ∧
        res1 = resultToLoop res ∧
        localsResultRel ctxt live res s1 t1 ∧ ck ≤ sourceCost .tick v1 := by
  have hClock : v1.clock = t.clock := hState.2.2.1
  by_cases hZero : v1.clock = 0
  · have hSource : (res, s1) =
        (some .timeOut, CrepSemHOLState.emptyLocals v1) := by
      simpa [evalCrepSemHOLProgExact_tick, hZero] using hEval.symm
    cases hSource
    have hTargetZero : t.clock = 0 := by omega
    refine ⟨0, some .timeOut, { t with locals := .ln }, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp [sourceCost]⟩
    · simp [LoopSemStateFiniteExact.evaluate, compileHOLExact, hTargetZero]
    · simpa [crepToLoopStateRelExact, CrepSemHOLState.emptyLocals,
        LoopSemStateFiniteExact.evaluate, hTargetZero] using hState
    · simpa [CrepSemHOLState.emptyLocals] using hMem
    · simpa [CrepSemHOLState.emptyLocals] using hGlobals
    · simpa [CrepSemHOLState.emptyLocals] using hCode
    · rfl
    · trivial
  · have hSource : (res, s1) = (none, decClockCrepSemHOL v1) := by
      simpa [evalCrepSemHOLProgExact_tick, hZero] using hEval.symm
    cases hSource
    have hTargetNonzero : t.clock ≠ 0 := by omega
    refine ⟨0, none, LoopSemStateFiniteExact.decClock t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp [sourceCost]⟩
    · simp [LoopSemStateFiniteExact.evaluate, compileHOLExact, hTargetNonzero]
    · simpa [crepToLoopStateRelExact, decClockCrepSemHOL,
        LoopSemStateFiniteExact.decClock, hClock] using hState
    · simpa [crepToLoopMemRelHOLExact, decClockCrepSemHOL,
        LoopSemStateFiniteExact.decClock] using hMem
    · simpa [crepToLoopGlobalsRelHOLExact, decClockCrepSemHOL,
        LoopSemStateFiniteExact.decClock] using hGlobals
    · simpa [crepToLoopCodeRelExact, decClockCrepSemHOL,
        LoopSemStateFiniteExact.decClock] using hCode
    · rfl
    · exact hLocals


#print axioms compCorrectTick

end InitECandidate.Solver.Wave8Stage.CrepCostTick
