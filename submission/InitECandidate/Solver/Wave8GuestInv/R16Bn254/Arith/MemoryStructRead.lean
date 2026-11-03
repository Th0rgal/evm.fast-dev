import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryReadTouch

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE

theorem DomainRead.load4 (address : ExpHOL 64) :
    DomainRead address (.load (.comb [.one, .one, .one, .one]) address) := by
  intro F s hg hn
  simp only [arithEval, evalHOLExact, isWfShapeExactHOL, isWfShapesExactHOL, Bool.true_and, ↓reduceIte] at hn
  split at hn
  · rename_i a ha
    by_cases hd : s.memaddrs a
    · rw [hg.memaddrs] at hd
      have hi := ordinaryDomain_interval a hd
      exact ⟨a, ha, hi.1, by omega⟩
    · simp [memLoadHOLExact, memLoadsHOLExact, hd] at hn
  · exact False.elim (hn rfl)

theorem DomainTouch.dec_read (address expression : ExpHOL 64) (name : MlS)
    (shape : ShapeHOL) (body : ProgHOL 64) (hr : DomainRead address expression) :
    DomainTouch address (.dec name shape expression body) := by
  intro F s hg hflow
  apply hr s hg
  intro he
  dsimp only [arithEval] at he
  rw [evaluateHOLFiniteState_dec_total] at hflow
  dsimp only at hflow
  rw [he] at hflow
  simp at hflow

end InitECandidate.Solver.Wave8GuestInv.Arith
