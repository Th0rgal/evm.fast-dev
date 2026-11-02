import InitECandidate.Solver.Wave8Stage.WordCostEffects

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8Stage.WordCostEffects
open Flapjack WordSemStateFiniteExact WordToStackSourceCost WordCostControl

/-- A zero-cost instruction with normal fallthrough cannot increase the net
cost, since the original evaluator's clock never increases. -/
theorem normal_fits {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (cost : sourceCost p s = 0) (result : (evaluate p s).1 = none) :
    Fits (atom .fall 0) p s := by
  have mono := (evaluate_clock_proj p s).1
  simp only [Fits,netCost,result,classify,atom,if_true,cost,covers_some]
  omega

/-- Every instruction erased to skip has zero extra Stack cost and, on a
non-error run, normal fallthrough. This includes register and memory writes. -/
theorem skip_at {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (erased : erase p = .skip) : At (atom .fall 0) p s := by
  intro ne nt
  apply normal_fits p s
  · cases p <;> (try simp only [erase,reduceCtorEq] at erased)
    case call ret dest args handler =>
      rcases ret with _ | ⟨_,_,_,_,_⟩ <;> rcases handler with _ | ⟨_,_,_,_⟩ <;>
        simp [erase] at erased
    all_goals simp only [sourceCost]
  · cases p <;> (try simp only [erase,reduceCtorEq] at erased)
    case call ret dest args handler =>
      rcases ret with _ | ⟨_,_,_,_,_⟩ <;> rcases handler with _ | ⟨_,_,_,_⟩ <;>
        simp [erase] at erased
    all_goals rw [evaluate] at ne ⊢
    all_goals (repeat' split at ne) <;> simp_all

/-- Indexed control transfers carry no cost or clock credit. -/
theorem break_at {width : Nat} [NeZero width] {C F : Type}
    (label : Nat) (s : WordSemStateFiniteExact width C F) :
    At (atom (.breakTo label) 0) (.break label) s := by
  intro _ _
  simp [Fits,netCost,evaluate,sourceCost,classify,atom]

theorem continue_at {width : Nat} [NeZero width] {C F : Type}
    (label : Nat) (s : WordSemStateFiniteExact width C F) :
    At (atom (.continueTo label) 0) (.continue label) s := by
  intro _ _
  simp [Fits,netCost,evaluate,sourceCost,classify,atom]

/-- A successful return has zero extra cost, including its real flush state. -/
theorem return_at {width : Nat} [NeZero width] {C F : Type}
    (reg : Nat) (regs : List Nat) (s : WordSemStateFiniteExact width C F) :
    At (atom .returned 0) (.return reg regs) s := by
  intro ne nt
  rw [evaluate] at ne
  cases hreg : getVar reg s <;> cases hregs : getVars regs s <;>
    simp only [hreg,hregs] at ne
  all_goals try exact (ne rfl).elim
  rename_i value values
  cases value <;> try exact (ne rfl).elim
  simp [Fits,netCost,evaluate,hreg,hregs,sourceCost,classify,atom,flushState]

/-- Raising contributes precisely one extra Stack tick. -/
theorem raise_at {width : Nat} [NeZero width] {C F : Type}
    (reg : Nat) (s : WordSemStateFiniteExact width C F) :
    At (atom .raised 1) (.raise reg) s := by
  intro ne nt
  have mono := (evaluate_clock_proj (.raise reg) s).1
  rw [evaluate] at ne
  cases hg : getVar reg s with
  | none => simp only [hg] at ne; exact (ne rfl).elim
  | some value =>
    cases hj : jumpExc s with
    | none => simp only [hg,hj] at ne; exact (ne rfl).elim
    | some found =>
      rcases found with ⟨post,l1,l2⟩
      simp only [evaluate,hg,hj] at mono
      simp only [Fits,netCost,evaluate,hg,hj,sourceCost,classify,atom,if_true,covers_some]
      omega

end InitECandidate.Solver.Wave8Stage.WordCostEffects
