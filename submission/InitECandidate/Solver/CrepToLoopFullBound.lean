import InitECandidate.Solver.CrepToLoopStmtBound
import InitECandidate.Solver.CrepToLoopWhileCallBound

set_option autoImplicit false

/-!
Budget composition interface. The factor 2 applies to a *dynamic* charge,
not to the source clock alone: expression comparisons can consume target
clock even when the source consumes none. A whole-program bound still needs
a quantitative evaluation-induction theorem for loops and calls. The existing
while theorem bounds the guard prefix, not the compiled loop execution.
The requested CrepToLoopClockBound and Compiler/CrepToLoop/Proofs/Correctness
source files are absent in this checkout; the actual preservation theorem is
Flapjack.crepToLoopNcompileCorrectOf, imported via BoundedPanToWord.
-/
namespace InitECandidate.Solver.CrepToLoopFullBound

open InitE Flapjack
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Two target control ticks per dynamically charged control step. -/
def M_crep_loop : Nat := 2

/-- Budget from accumulated dynamic expression and control charges.
This definition alone is not a semantic whole-program cost bound. -/
def crepToLoopProgClockBudget (comparisons controlSteps : Nat) : Nat :=
  comparisons + M_crep_loop * controlSteps

theorem budget_zero : crepToLoopProgClockBudget 0 0 = 0 := rfl

theorem budget_add (a b k l : Nat) :
    crepToLoopProgClockBudget (a + b) (k + l) =
      crepToLoopProgClockBudget a k + crepToLoopProgClockBudget b l := by
  simp [crepToLoopProgClockBudget, Nat.mul_add, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

theorem budget_control_step (a k : Nat) :
    crepToLoopProgClockBudget a (k + 1) = crepToLoopProgClockBudget a k + 2 := by
  simp [crepToLoopProgClockBudget, M_crep_loop, Nat.mul_add, Nat.add_assoc]

theorem budget_mono (a b k l : Nat) (ha : a ≤ b) (hk : k ≤ l) :
    crepToLoopProgClockBudget a k ≤ crepToLoopProgClockBudget b l := by
  exact Nat.add_le_add ha (Nat.mul_le_mul_left _ hk)

/-- The while-control estimate has exactly factor two, including final exit. -/
theorem budget_while (comparisons iterations body : Nat) :
    (comparisons + 2) * (iterations + 1) + body =
      crepToLoopProgClockBudget (comparisons * (iterations + 1) + body)
        (iterations + 1) := by
  simp [crepToLoopProgClockBudget, M_crep_loop, Nat.add_mul,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Sharpness in the control charge: decreasing the factor loses two ticks. -/
theorem budget_control_strict (a k : Nat) :
    crepToLoopProgClockBudget a k < crepToLoopProgClockBudget a (k + 1) := by
  rw [budget_control_step]
  omega

/-- Connection to the full preservation theorem: its clock witness is unbounded.
No claim about the dynamic budget follows from this theorem alone. -/
theorem full_preservation {width : Nat} [NeZero width] {F : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width F) :
    PropertyAt p s := crepToLoopNcompileCorrectOf p s

/-- The assignment simulation supplies an actual budgeted execution, with all
preserved relations. It is the quantitatively proved base case. -/
theorem assignment_budget {width : Nat} [NeZero width] {F : Type}
    (n : Nat) (e : CrepExpHOL width) (s sf : CrepSemHOLState width F)
    (r : Option (CrepResultHOLExact width))
    (t : LoopSemStateFiniteExact width F) (ct : CrepToLoopContextExact) (live : NumSet)
    (he : evalCrepSemHOLProgExact s (.assign n e) = (r, sf))
    (hne : r ≠ some .error)
    (hs : crepToLoopStateRelExact s t)
    (hm : crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs)
    (hg : crepToLoopGlobalsRelHOLExact s.globals t.globals)
    (hc : crepToLoopCodeRelExact ct s.code t.code)
    (hl : crepToLoopLocalsRelExact ct live s.locals t.locals) :
    ∃ ck rr tf,
      ck ≤ crepToLoopProgClockBudget (crepProgCmpCount (.assign n e)) 0 ∧
      LoopSemStateFiniteExact.evaluate (compileHOLExact ct live (.assign n e))
        { t with clock := t.clock + ck } = (rr, tf) ∧
      sf.clock = s.clock ∧ tf.clock = t.clock ∧
      crepToLoopStateRelExact sf tf ∧
      crepToLoopMemRelHOLExact sf.memory tf.memory sf.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sf.globals tf.globals ∧
      crepToLoopCodeRelExact ct sf.code tf.code ∧
      rr = resultToLoop r ∧ localsResultRel ct live r sf tf := by
  simpa [crepToLoopProgClockBudget] using
    crepToLoop_compile_assign_clock_bound n e s r sf t ct live he hne hs hm hg hc hl

#print axioms full_preservation
#print axioms assignment_budget
end InitECandidate.Solver.CrepToLoopFullBound
