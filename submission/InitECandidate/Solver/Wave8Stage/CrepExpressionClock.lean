import InitECandidate.Solver.Wave8Stage.LoopAcyclicClock
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpPreservesEval

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.CrepExpressionClock

open Flapjack LoopSemStateFiniteExact LoopAcyclicClock

mutual
  /-- Each materialized comparison consumes one Loop tick. All other
  expression instructions preserve the clock. -/
  def expressionCost {width : Nat} [NeZero width] : CrepExpHOL width → Nat
    | .load e | .load32 e | .loadByte e => expressionCost e
    | .op _ es | .crepOp _ es => expressionsCost es
    | .cmp _ a b => expressionCost a + expressionCost b + 1
    | .shift _ a b => expressionCost a + expressionCost b
    | _ => 0

  def expressionsCost {width : Nat} [NeZero width] : List (CrepExpHOL width) → Nat
    | [] => 0
    | e :: es => expressionCost e + expressionsCost es
end

def listCost {width : Nat} [NeZero width] (ps : List (HolLoopProg width)) : Option Nat :=
  staticCost (loopNestedSeqHOL ps)

@[simp] theorem listCost_nil {width : Nat} [NeZero width] :
    listCost ([] : List (HolLoopProg width)) = some 0 := rfl

@[simp] theorem listCost_cons {width : Nat} [NeZero width]
    (p : HolLoopProg width) (ps : List (HolLoopProg width)) :
    listCost (p :: ps) = (do
      let a ← staticCost p
      let b ← listCost ps
      pure (a + b)) := rfl

theorem listCost_append {width : Nat} [NeZero width]
    (ps qs : List (HolLoopProg width)) :
    listCost (ps ++ qs) = (do
      let a ← listCost ps
      let b ← listCost qs
      pure (a + b)) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.cons_append, listCost_cons, ih]
    cases staticCost p <;> cases listCost ps <;> cases listCost qs <;>
      simp [Nat.add_assoc]

@[simp] theorem assignments_cost {width : Nat} [NeZero width]
    (ns : List Nat) (es : List (HolLoopExp width)) :
    listCost (ns.zipWith HolLoopProg.assign es) = some 0 := by
  induction ns generalizing es with
  | nil => simp
  | cons n ns ih =>
    cases es <;> simp [staticCost, ih]

@[simp] theorem offset_assignments_cost {width : Nat} [NeZero width]
    (offset : Nat) (ns : List Nat) (es : List (HolLoopExp width)) :
    listCost (ns.zipWith (fun n e => HolLoopProg.assign (offset + n) e) es) = some 0 := by
  induction ns generalizing es with
  | nil => simp
  | cons n ns ih =>
    cases es <;> simp [staticCost, ih]

@[simp] theorem compileCrepop_cost {width : Nat} [NeZero width]
    (op : CrepOp) (arch : Compiler.Encoders.Asm.AsmArchitecture)
    (a b tmp : Nat) (live : NumSet) :
    listCost (compileCrepopHOLExact (width := width) op arch a b tmp live).1 = some 0 := by
  cases op
  simp only [compileCrepopHOLExact]
  split <;> simp [staticCost]

@[simp] theorem progIf_cost {width : Nat} [NeZero width]
    (op : Cmp) (ps qs : List (HolLoopProg width)) (a b : HolLoopExp width)
    (reg1 reg2 : Nat) (live : NumSet) :
    listCost (progIfHOLExact op ps qs a b reg1 reg2 live) = (do
      let x ← listCost ps
      let y ← listCost qs
      pure (x + y + 1)) := by
  simp only [progIfHOLExact, listCost_append, listCost_cons, listCost_nil, staticCost]
  cases listCost ps <;> cases listCost qs <;> simp

mutual
  theorem compileExp_cost {width : Nat} [NeZero width]
      (ctx : CrepToLoopContextExact) (tmp : Nat) (live : NumSet)
      (e : CrepExpHOL width) :
      listCost (compileExpHOLExact ctx tmp live e).1 = some (expressionCost e) := by
    cases he : e with
    | load a | load32 a | loadByte a =>
      simpa [compileExpHOLExact, expressionCost, listCost_append, staticCost] using
        compileExp_cost ctx tmp live a
    | op op es =>
      simpa [compileExpHOLExact, expressionCost] using compileExps_cost ctx tmp live es
    | crepOp op es =>
      have hi := compileExps_cost ctx tmp live es
      simp [compileExpHOLExact, expressionCost, listCost_append, hi]
    | cmp op a b | shift op a b =>
      have ha := compileExp_cost ctx tmp live a
      have hb := compileExp_cost ctx (compileExpHOLExact ctx tmp live a).2.2.1
        (compileExpHOLExact ctx tmp live a).2.2.2 b
      simp [compileExpHOLExact, expressionCost, progIf_cost, listCost_append, ha, hb]
    | _ => simp [compileExpHOLExact, expressionCost]
  termination_by sizeOf e
  decreasing_by all_goals (subst e; simp_wf; try omega)

  theorem compileExps_cost {width : Nat} [NeZero width]
      (ctx : CrepToLoopContextExact) (tmp : Nat) (live : NumSet)
      (es : List (CrepExpHOL width)) :
      listCost (compileExpsHOLExact ctx tmp live es).1 = some (expressionsCost es) := by
    cases he : es with
    | nil => simp [compileExpsHOLExact, expressionsCost]
    | cons a rest =>
      have ha := compileExp_cost ctx tmp live a
      have hb := compileExps_cost ctx (compileExpHOLExact ctx tmp live a).2.2.1
        (compileExpHOLExact ctx tmp live a).2.2.2 rest
      simp [compileExpsHOLExact, expressionsCost, listCost_append, ha, hb]
  termination_by sizeOf es
  decreasing_by all_goals (subst es; simp_wf; try omega)
end

/-- Quantitative form of the original expression simulation, retaining all
of its evaluation and state-relation conclusions. -/
theorem compExp_preserves_eval_bounded {width : Nat} [NeZero width] {F : Type}
    (s : CrepSemHOLState width F) (e : CrepExpHOL width)
    (v : HolWordLab width) (t : LoopSemStateFiniteExact width F)
    (ctx : CrepToLoopContextExact) (tmp : Nat) (live : NumSet)
    (ps : List (HolLoopProg width)) (value : HolLoopExp width)
    (next : Nat) (outLive : NumSet)
    (h : evalCrepSemHOLExp s e = some v ∧
      crepToLoopStateRelExact s t ∧
      crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
      crepToLoopCodeRelExact ctx s.code t.code ∧
      crepToLoopLocalsRelExact ctx live s.locals t.locals ∧
      compileExpHOLExact ctx tmp live e = (ps, value, next, outLive) ∧
      ctx.vmax < tmp) :
    ∃ (extra : Nat) (post : LoopSemStateFiniteExact width F),
      evaluate (loopNestedSeqHOL ps) { t with clock := t.clock + extra } = (none, post) ∧
      eval post value = some (wlabWlocExact v) ∧
      crepToLoopStateRelExact s post ∧
      crepToLoopMemRelHOLExact s.memory post.memory s.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s.globals post.globals ∧
      crepToLoopCodeRelExact ctx s.code post.code ∧
      crepToLoopLocalsRelExact ctx outLive s.locals post.locals ∧
      extra ≤ expressionCost e := by
  obtain ⟨extra, post, run, hv, hs, hm, hg, hc, hl⟩ :=
    crepToLoop_comp_exp_preserves_eval s e v t ctx tmp live ps value next outLive h
  have hcost := compileExp_cost ctx tmp live e
  rw [h.2.2.2.2.2.2.1] at hcost
  refine ⟨extra, post, run, hv, hs, hm, hg, hc, hl, ?_⟩
  exact offset_le _ t post _ extra none hcost run (by simp)
    (h.2.1.2.2.1.symm.trans hs.2.2.1)

/-- List-expression counterpart, including the original live-set relation. -/
theorem compExps_preserves_eval_bounded {width : Nat} [NeZero width] {F : Type}
    (es : List (CrepExpHOL width)) (s : CrepSemHOLState width F)
    (vs : List (HolWordLab width)) (t : LoopSemStateFiniteExact width F)
    (ctx : CrepToLoopContextExact) (tmp : Nat) (live : NumSet)
    (ps : List (HolLoopProg width)) (values : List (HolLoopExp width))
    (next : Nat) (outLive : NumSet)
    (h : es.mapM (evalCrepSemHOLExp s) = some vs ∧
      crepToLoopStateRelExact s t ∧
      crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
      crepToLoopCodeRelExact ctx s.code t.code ∧
      crepToLoopLocalsRelExact ctx live s.locals t.locals ∧
      compileExpsHOLExact ctx tmp live es = (ps, values, next, outLive) ∧
      ctx.vmax < tmp) :
    ∃ (extra : Nat) (post : LoopSemStateFiniteExact width F),
      evaluate (loopNestedSeqHOL ps) { t with clock := t.clock + extra } = (none, post) ∧
      values.mapM (eval post) = some (vs.map wlabWlocExact) ∧
      crepToLoopStateRelExact s post ∧
      crepToLoopMemRelHOLExact s.memory post.memory s.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s.globals post.globals ∧
      crepToLoopCodeRelExact ctx s.code post.code ∧
      crepToLoopLocalsRelExact ctx outLive s.locals post.locals ∧
      extra ≤ expressionsCost es := by
  obtain ⟨extra, post, run, hv, hs, hm, hg, hc, hl⟩ :=
    crepToLoop_comp_exps_preserves_eval es s vs t ctx tmp live ps values next outLive h
  have hcost := compileExps_cost ctx tmp live es
  rw [h.2.2.2.2.2.2.1] at hcost
  refine ⟨extra, post, run, hv, hs, hm, hg, hc, hl, ?_⟩
  exact offset_le _ t post _ extra none hcost run (by simp)
    (h.2.1.2.2.1.symm.trans hs.2.2.1)

#print axioms compileExp_cost
#print axioms compileExps_cost
#print axioms compExp_preserves_eval_bounded
#print axioms compExps_preserves_eval_bounded

end InitECandidate.Solver.Wave8Stage.CrepExpressionClock
