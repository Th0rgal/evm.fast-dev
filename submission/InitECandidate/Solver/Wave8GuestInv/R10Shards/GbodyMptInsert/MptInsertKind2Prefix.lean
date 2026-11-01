import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind2Descend

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem selection_nonnull {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hn : locN s "node" ≠ 0) (hr : evaluateHOLFiniteState s selection = (none, t)) :
    evaluateHOLFiniteState s nonnull = (none, t) := by
  rw [selection_eq] at hr
  rcases ite_none hr with ⟨hcond, _⟩ | ⟨_, hr⟩
  · exact False.elim (hn (by simpa using condTrue_local_eq_const hcond))
  · exact hr

theorem kinds_extension {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hk : locN s "k" = 2) (hr : evaluateHOLFiniteState s kinds = (none, t)) :
    evaluateHOLFiniteState s extension = (none, t) := by
  rw [kinds_eq] at hr
  rcases ite_none hr with ⟨hcond, _⟩ | ⟨_, hr⟩
  · have he : locN s "k" = 1 := by simpa using condTrue_local_eq_const hcond
    omega
  · rcases ite_none hr with ⟨_, hr⟩ | ⟨hcond, _⟩
    · exact hr
    · have he : locN s "k" ≠ 2 := by simpa using condFalse_local_eq_const hcond
      exact False.elim (he hk)

/-- Reduce the non-null kind-2 branch to its extension body after exact invalidation. -/
theorem nonnull_extension (h : MptInsertCallees) {F : Type}
    {s t : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (ha : ArenaReady s) (hn : NodeHeap s Nd) (hroot : RootIn Nd (locN s "node"))
    (htag : memW s (locN s "node") = 2)
    (hr : evaluateHOLFiniteState s nonnull = (none, t)) :
    ∃ cleared u Nd', ArenaReady cleared ∧ NodeHeap cleared Nd' ∧
      (∀ n ∈ Nd, n ∈ Nd') ∧ (∀ p len, KeyIn s Nd p len → KeyIn cleared Nd' p len) ∧
      cleared = { clearCache (put s "k" 2) (locN s "node") with clock := cleared.clock } ∧
      evaluateHOLFiniteState cleared extension = (none, u) ∧
      t = { u with locals := HolFiniteMapExact.resVarEq u.locals (ofString "k", s.locals.lookup (ofString "k")) } := by
  rw [nonnull_eq] at hr
  obtain ⟨v, u, hv, hbody, ht⟩ := dec_none hr
  obtain ⟨w, rfl, hw⟩ := evalAt_loadL s "node" 0 v hv
  have hw2 : w = 2 := by
    apply BitVec.eq_of_toNat_eq
    change w.toNat = 2
    change w.toNat = memW s (locN s "node" + 0) at hw
    simpa only [Nat.add_zero, htag] using hw
  subst w
  obtain ⟨s1, hfail, hrest⟩ := seq_none hbody
  have hk0 : locN (put s "k" 2) "k" = 2 := by
    exact RunFramesRace.locN_setVar_same s "k" 2
  have hs1 : s1 = put s "k" 2 := by
    rcases ite_none hfail with ⟨hcond, _⟩ | ⟨_, hskip⟩
    · have hz := condTrue_local_eq_const hcond
      change locN (put s "k" 2) "k" = 0 at hz
      omega
    · rw [evaluateHOLFiniteState_skip] at hskip
      exact (congrArg Prod.snd hskip).symm
  subst s1
  obtain ⟨cleared, hinv, hkinds⟩ := seq_none hrest
  have hnode : locN (put s "k" 2) "node" = locN s "node" := by
    exact RunFramesRace.locN_setVar_ne s "node" (ofString "k") _ (by decide)
  obtain ⟨Nd', hac, hnc, hsub, hkeys, hclear⟩ := invalidate_call h (s := put s "k" 2) (t := cleared) (Nd := Nd)
    (localsFree_arenaReady s (put s "k" 2).locals s.clock ha) hn (by rw [hnode]; exact hroot) hinv
  have hkc : locN cleared "k" = 2 := by
    rw [hclear]
    exact hk0
  refine ⟨cleared, u, Nd', hac, hnc, hsub, hkeys, ?_, kinds_extension hkc hkinds, ht⟩
  simpa only [hnode] using hclear

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
