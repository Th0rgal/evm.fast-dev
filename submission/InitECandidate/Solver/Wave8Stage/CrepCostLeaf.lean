import InitECandidate.Solver.Wave8Stage.CrepSourceCostBound
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Assembly

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.CrepCostLeaf

open Classical Flapjack CrepExpressionClock CrepSourceCost LoopAcyclicClock
open Pancake.CrepToLoop.Proofs.NCompileCorrect

def PropertyB {width : Nat} [NeZero width] {F : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width F) : Prop :=
  ∀ (r : Option (CrepResultHOLExact width)) (post : CrepSemHOLState width F)
    (t : LoopSemStateFiniteExact width F) (ctx : CrepToLoopContextExact) (live : NumSet),
    evalCrepSemHOLProgExact s p = (r, post) → r ≠ some .error →
    crepToLoopStateRelExact s t →
    crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs →
    crepToLoopGlobalsRelHOLExact s.globals t.globals →
    crepToLoopCodeRelExact ctx s.code t.code →
    crepToLoopLocalsRelExact ctx live s.locals t.locals →
    ∃ extra result final,
      LoopSemStateFiniteExact.evaluate (compileHOLExact ctx live p)
        { t with clock := t.clock + extra } = (result, final) ∧
      crepToLoopStateRelExact post final ∧
      crepToLoopMemRelHOLExact post.memory final.memory post.memaddrs ∧
      crepToLoopGlobalsRelHOLExact post.globals final.globals ∧
      crepToLoopCodeRelExact ctx post.code final.code ∧
      result = resultToLoop r ∧ localsResultRel ctx live r post final ∧
      extra ≤ sourceCost p s

theorem PropertyB.toPropertyAt {width : Nat} [NeZero width] {F : Type}
    {p : CrepProgHOL width} {s : CrepSemHOLState width F} (h : PropertyB p s) :
    PropertyAt p s := by
  intro r post t ctx live he hn hs hm hg hc hl
  obtain ⟨extra, result, final, run, hs', hm', hg', hc', hr, hl', _⟩ :=
    h r post t ctx live he hn hs hm hg hc hl
  exact ⟨extra, result, final, run, hs', hm', hg', hc', hr, hl'⟩

def isLeaf {width : Nat} [NeZero width] : CrepProgHOL width → Bool
  | .dec .. | .seq .. | .ite .. | .while .. | .call .. | .tick => false
  | _ => true

theorem compiledLeaf_cost {width : Nat} [NeZero width] {F : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width F)
    (ctx : CrepToLoopContextExact) (live : NumSet) (hleaf : isLeaf p = true) :
    ∃ b, staticCost (compileHOLExact ctx live p) = some b ∧ b ≤ sourceCost p s := by
  cases p <;> simp only [isLeaf, Bool.false_eq_true] at hleaf
  all_goals try contradiction
  all_goals simp only [compileHOLExact, sourceCost]
  all_goals try exact ⟨0, rfl, Nat.zero_le _⟩
  all_goals try exact ⟨_, compileExps_cost _ _ _ _, Nat.le_refl _⟩
  all_goals try (
    change ∃ b, listCost _ = some b ∧ b ≤ _
    simp [listCost_append, staticCost, compileExp_cost, compileExps_cost, assignments_cost])
  all_goals (repeat' split)
  all_goals try exact ⟨0, rfl, Nat.zero_le _⟩
  all_goals
    change ∃ b, listCost _ = some b ∧ b ≤ _
    simp [listCost_append, staticCost, compileExp_cost, compileExps_cost, assignments_cost]

private theorem shMem_notTimeOut {width : Nat} [NeZero width] {F : Type}
    (op : WordMemOp) (name : Nat) (addr : BitVec width) (s : CrepSemHOLState width F)
    [DecidablePred s.shMemaddrs] :
    (crepShMemOpExactHOL op name addr s).1 ≠ some .timeOut := by
  cases op <;> simp only [crepShMemOpExactHOL, crepShMemLoadExactHOL, crepShMemStoreExactHOL] <;>
    (repeat' split) <;> simp

theorem leaf_notTimeOut {width : Nat} [NeZero width] {F : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width F) (hleaf : isLeaf p = true) :
    (evalCrepSemHOLProgExact s p).1 ≠ some .timeOut := by
  cases p <;> simp only [isLeaf, Bool.false_eq_true] at hleaf
  all_goals try contradiction
  all_goals simp only [evalCrepSemHOLProgExact_skip, evalCrepSemHOLProgExact_break,
    evalCrepSemHOLProgExact_continue, evalCrepSemHOLProgExact_raise,
    evalCrepSemHOLProgExact_primitive_holShape, evalCrepSemHOLProgExact_assign_holShape,
    evalCrepSemHOLProgExact_store_holShape, evalCrepSemHOLProgExact_store32_holShape,
    evalCrepSemHOLProgExact_storeByte_holShape, evalCrepSemHOLProgExact_storeGlob_holShape,
    evalCrepSemHOLProgExact_shMem_holShape, evalCrepSemHOLProgExact_return_holShape,
    evalCrepSemHOLProgExact_extCall_holShape]
  all_goals (repeat' split)
  all_goals first | exact shMem_notTimeOut _ _ _ _ | simp

/-- Every nonrecursive compiler clause is bounded by its expression cost;
all original simulation postconditions are retained. -/
theorem compCorrectLeaf {width : Nat} [NeZero width] {F : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width F) (hleaf : isLeaf p = true) :
    PropertyB p s := by
  intro r post t ctx live he hn hs hm hg hc hl
  obtain ⟨extra, result, final, run, hs', hm', hg', hc', hr, hl'⟩ :=
    crepToLoopNcompileCorrectOf p s r post t ctx live he hn hs hm hg hc hl
  obtain ⟨b, hb, hbound⟩ := compiledLeaf_cost p s ctx live hleaf
  have hnt := leaf_notTimeOut p s hleaf
  rw [he] at hnt
  have targetNT : result ≠ some .timeOut := by
    rw [hr]
    cases r with
    | none => simp [resultToLoop]
    | some r => cases r <;> simp_all [resultToLoop]
  have hcons := consumed_le (compileHOLExact ctx live p)
    { t with clock := t.clock + extra } b hb (by rw [run]; exact targetNT)
  rw [run] at hcons
  have hmono := evalCrepSemHOLProgExact_clock_le s p
  rw [he] at hmono
  have hiClock := hs.2.2.1
  have hfClock := hs'.2.2.1
  refine ⟨extra, result, final, run, hs', hm', hg', hc', hr, hl', ?_⟩
  dsimp only at hcons hmono
  omega


end InitECandidate.Solver.Wave8Stage.CrepCostLeaf
