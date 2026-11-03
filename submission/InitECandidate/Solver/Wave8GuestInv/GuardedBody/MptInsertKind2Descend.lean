import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2Calls

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def put {F : Type} (s : PanSemStateFiniteExact 64 F) (n : String) (w : BitVec 64) :=
  setVarHOLFinite (ofString n) (.val (.word w)) s

theorem descend_run {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {node level pl : BitVec 64}
    (hn : s.locals.lookup (ofString "node") = some (.val (.word node)))
    (hl : s.locals.lookup (ofString "level") = some (.val (.word level)))
    (hp : s.locals.lookup (ofString "pl") = some (.val (.word pl)))
    (hr : evaluateHOLFiniteState s descend = (none, t)) :
    ∃ child : BitVec 64, child.toNat = memW s (node.toNat + 48) ∧
      t = put (put (put (put (put s "r" node) "next_node" child)
        "next_slot" (node + 48)) "next_level" (level + pl)) "go" 1 := by
  rw [descend_eq] at hr
  obtain ⟨s1, h1, hr1⟩ := seq_none hr
  obtain ⟨v1, hv1, hs1⟩ := assign_none h1
  have hv1' : v1 = .val (.word node) := by
    simpa only [lv, evalAt, evalHOLExact, hn, Option.some.injEq] using hv1.symm
  subst v1
  change s1 = put s "r" node at hs1
  subst s1
  obtain ⟨s2, h2, hr2⟩ := seq_none hr1
  obtain ⟨v2, hv2, hs2⟩ := assign_none h2
  obtain ⟨child, hv2', hchild⟩ := evalAt_loadL (put s "r" node) "node" 48 v2 hv2
  subst v2
  have hchild' : child.toNat = memW s (node.toNat + 48) := by
    simpa +decide [put, locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hn] using hchild
  change s2 = put (put s "r" node) "next_node" child at hs2
  subst s2
  obtain ⟨s3, h3, hr3⟩ := seq_none hr2
  obtain ⟨v3, hv3, hs3⟩ := assign_none h3
  have hv3' : v3 = .val (.word (node + 48)) := by
    simpa +decide [put, lv, constant, evalAt, evalHOLExact, evalListHOLExact,
      setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hn,
      valueIsWord, valueWord, wordOpHOL, wordOp] using hv3.symm
  subst v3
  change s3 = put (put (put s "r" node) "next_node" child) "next_slot" (node + 48) at hs3
  subst s3
  obtain ⟨s4, h4, hr4⟩ := seq_none hr3
  obtain ⟨v4, hv4, hs4⟩ := assign_none h4
  have hv4' : v4 = .val (.word (level + pl)) := by
    simpa +decide [put, lv, evalAt, evalHOLExact, evalListHOLExact,
      setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hl, hp,
      valueIsWord, valueWord, wordOpHOL, wordOp] using hv4.symm
  subst v4
  change s4 = put (put (put (put s "r" node) "next_node" child)
    "next_slot" (node + 48)) "next_level" (level + pl) at hs4
  subst s4
  obtain ⟨v5, hv5, ht⟩ := assign_none hr4
  cases RunFramesRace.evalAt_const _ 1 v5 hv5
  exact ⟨child, hchild', ht⟩

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
