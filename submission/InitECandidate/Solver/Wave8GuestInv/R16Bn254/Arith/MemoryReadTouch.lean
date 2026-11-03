import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryWalk
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ReadFailure

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
open InitECandidate.Solver.PanTerminatingBounded

/-- Successful expression evaluation witnesses a read of this domain address. -/
def DomainRead (address expression : ExpHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), GuestInv s →
    arithEval s expression ≠ none →
    ∃ a : BitVec 64, arithEval s address = some (.val (.word a)) ∧
      sourceBase ≤ a.toNat ∧ a.toNat < heapEnd

theorem DomainRead.load (address : ExpHOL 64) : DomainRead address (.load .one address) := by
  intro F s hg hn
  simp only [arithEval, evalHOLExact, isWfShapeExactHOL, ↓reduceIte] at hn
  split at hn
  · rename_i a ha
    simp only [memLoadHOLExact] at hn
    split at hn
    · rename_i hd
      rw [hg.memaddrs] at hd
      have hi := ordinaryDomain_interval a hd
      exact ⟨a, ha, hi.1, by omega⟩
    · exact False.elim (hn rfl)
  · exact False.elim (hn rfl)

theorem DomainRead.loadByte (address : ExpHOL 64) : DomainRead address (.loadByte address) := by
  intro F s hg hn
  simp only [arithEval, evalHOLExact] at hn
  split at hn
  · rename_i a ha
    cases hm : s.memory (panByteAlignHOL a) with
    | word w =>
      simp only [panMemLoadByteHOL, hm] at hn
      split at hn
      · rename_i hd
        rw [hg.memaddrs] at hd
        exact ⟨a, ha, ordinaryDomain_byte_interval a hd⟩
      · simp at hn
  · exact False.elim (hn rfl)

theorem DomainRead.cmp_left (address left right : ExpHOL 64) (op : Cmp)
    (hr : DomainRead address left) : DomainRead address (.cmp op left right) := by
  intro F s hg hn
  apply hr s hg
  intro he
  apply hn
  simp only [arithEval, evalHOLExact, he]

theorem DomainTouch.ite_read (address condition : ExpHOL 64) (yes no : ProgHOL 64)
    (hr : DomainRead address condition) : DomainTouch address (.ite condition yes no) := by
  intro F s hg hflow
  apply hr s hg
  intro he
  dsimp only [arithEval] at he
  rw [evaluateHOLFiniteState_ite, he] at hflow
  simp at hflow

end InitECandidate.Solver.Wave8GuestInv.Arith
