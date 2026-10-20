import InitECandidate.Proofs.BoundedPanToWord

set_option autoImplicit false

/-!
Static audit of the committed Guest source (SHA256
414d70d031f9e367ad9e5c70bc6dbd523238a3c542fba59a09aed866f3e5f860).

IMPORTANT: the requested unconditional factor four is false in this checkout.
There are 825 functions and 261 while guards (257 nonconstant, four `true`).
The lexical source histogram is 255 guards with one comparison, two with two,
and four with zero. In Guest/Ast.lean:8296,11648 the parser wraps each operand
of && in `cmp notEqual 0`, giving FOUR comparisons in each exceptional guard.
PanToCrep.compileExp preserves these cmp nodes. Thus the structural maximum
is four and its control budget is six, not four. No whole-loop evaluation
bound is asserted here; that still needs the evaluation induction.

The source call graph has 2995 distinct caller/callee edges, is acyclic,
and has maximum depth 39 vertices / 38 edges (not the old asserted 18).

The finite manifest below records the independently extracted histogram.
The kernel checks its arithmetic and the concrete Crep counterexample.
The extraction from the full Guest AST and the full call-graph rank assignment
are script audits, NOT kernel-certified equalities to Guest.guestAst.
The rank theorem below is conditional on a rank-decreasing call-chain witness.
-/
namespace InitECandidate.Solver.GuestAstStaticBounds

open InitE Flapjack
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Exact maximum in the extracted AST histogram, including boolean coercions. -/
def maxGuestWhileCmpCount : Nat := 4

def guestWhileCmpHistogram : List (Nat × Nat) := [(0, 4), (1, 255), (4, 2)]

def guestFunctionCount : Nat := 825

def guestCallDepthVertices : Nat := 39

/-- Control charge per guard evaluation, including the two control ticks. -/
def whileIterationMultiplier {w : Nat} [NeZero w] (e : CrepExpHOL w) : Nat :=
  crepExpCmpCount e + 2

/-- Shape of the lowered `(i < 16) && (found == 0)` guard.
Local variable identifiers are arbitrary; they do not affect the count. -/
def compoundGuestGuard : CrepExpHOL 64 :=
  .op .and [
    .cmp .notEqual (.const 0) (.cmp .less (.var 0) (.const 16)),
    .cmp .notEqual (.const 0) (.cmp .equal (.var 1) (.const 0))]

theorem histogram_population :
    (guestWhileCmpHistogram.map Prod.snd).foldl (· + ·) 0 = 261 := by decide

theorem histogram_maximum :
    (guestWhileCmpHistogram.map Prod.fst).foldl max 0 = maxGuestWhileCmpCount := by decide

theorem histogram_maximum_attained :
    (maxGuestWhileCmpCount, 2) ∈ guestWhileCmpHistogram := by decide

theorem compound_guard_exact_count :
    crepExpCmpCount compoundGuestGuard = 4 := by
  simp [compoundGuestGuard, crepExpCmpCount, crepExpsCmpCount]

theorem compound_guard_exact_multiplier :
    whileIterationMultiplier compoundGuestGuard = 6 := by
  simp [whileIterationMultiplier, compound_guard_exact_count]

/-- Concrete counterexample to a universal factor four for actual guard shapes. -/
theorem factor_four_counterexample :
    crepExpCmpCount compoundGuestGuard ≤ maxGuestWhileCmpCount ∧
      4 < whileIterationMultiplier compoundGuestGuard := by
  simp [compound_guard_exact_count, compound_guard_exact_multiplier, maxGuestWhileCmpCount]

/-- Correct uniform structural control bound for guards conforming to the manifest. -/
theorem conforming_guard_multiplier {w : Nat} [NeZero w] (e : CrepExpHOL w)
    (h : crepExpCmpCount e ≤ maxGuestWhileCmpCount) :
    whileIterationMultiplier e ≤ 6 := by
  unfold whileIterationMultiplier
  unfold maxGuestWhileCmpCount at h
  omega

/-- The requested factor four is valid with the stronger, explicit premise. -/
theorem two_comparison_guard_multiplier {w : Nat} [NeZero w] (e : CrepExpHOL w)
    (h : crepExpCmpCount e ≤ 2) :
    whileIterationMultiplier e ≤ 4 := by
  unfold whileIterationMultiplier
  omega

/-- Includes the final exit check and an accumulated body budget. -/
theorem conforming_loop_control_budget {w : Nat} [NeZero w]
    (e : CrepExpHOL w) (iterations body : Nat)
    (h : crepExpCmpCount e ≤ maxGuestWhileCmpCount) :
    whileIterationMultiplier e * (iterations + 1) + body ≤
      6 * (iterations + 1) + body := by
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_right (iterations + 1) (conforming_guard_multiplier e h)) body

/-- Six is the least uniform multiplier for the exhibited guard, even at zero iterations. -/
theorem uniform_multiplier_lower_bound (m : Nat)
    (h : whileIterationMultiplier compoundGuestGuard ≤ m) : 6 ≤ m := by
  rw [compound_guard_exact_multiplier] at h
  exact h

/-- Strictly descending natural-number ranks certify acyclic call-chain depth.
`ranks` counts functions, so its length minus one counts call edges. -/
def RankedChain : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: tail => b < a ∧ RankedChain (b :: tail)

theorem ranked_chain_length : ∀ (a : Nat) (tail : List Nat),
    RankedChain (a :: tail) → (a :: tail).length ≤ a + 1 := by
  intro a tail
  induction tail generalizing a with
  | nil => intro _; simp
  | cons b tail ih =>
    intro h
    obtain ⟨hlt, hrest⟩ := h
    have hb := ih b hrest
    simp only [List.length_cons] at hb ⊢
    omega

theorem call_depth_from_rank_certificate (a : Nat) (tail : List Nat)
    (hchain : RankedChain (a :: tail)) (hroot : a < guestCallDepthVertices) :
    (a :: tail).length ≤ guestCallDepthVertices := by
  have h := ranked_chain_length a tail hchain
  omega

/-- Tightness of the rank arithmetic; extraction of the named Guest chain is external. -/
theorem rank_depth_attained :
    (List.range guestCallDepthVertices).length = 39 ∧
      guestCallDepthVertices - 1 = 38 := by decide

#print axioms histogram_population
#print axioms histogram_maximum
#print axioms histogram_maximum_attained
#print axioms compound_guard_exact_count
#print axioms compound_guard_exact_multiplier
#print axioms factor_four_counterexample
#print axioms conforming_guard_multiplier
#print axioms two_comparison_guard_multiplier
#print axioms conforming_loop_control_budget
#print axioms uniform_multiplier_lower_bound
#print axioms ranked_chain_length
#print axioms call_depth_from_rank_certificate
#print axioms rank_depth_attained

end InitECandidate.Solver.GuestAstStaticBounds
