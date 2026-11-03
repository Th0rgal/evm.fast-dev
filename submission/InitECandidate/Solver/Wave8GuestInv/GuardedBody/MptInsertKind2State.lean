import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2Finish

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def declared {F : Type} (s : PanSemStateFiniteExact 64 F) :=
  put (put (put (put s "r" 0) "next_node" 0) "next_slot" 0) "next_level" 0

def prepared {F : Type} (s : PanSemStateFiniteExact 64 F) := put (declared s) "go" 0

def cleanup {F : Type} (s t : PanSemStateFiniteExact 64 F) :=
  restore (restore (restore (restore t "next_level" (s.locals.lookup (ofString "next_level")))
    "next_slot" (s.locals.lookup (ofString "next_slot")))
    "next_node" (s.locals.lookup (ofString "next_node"))) "r" (s.locals.lookup (ofString "r"))

def finalState {F : Type} (s : PanSemStateFiniteExact 64 F) (c : Nat)
    (node level sl child : BitVec 64) :=
  finished (put { clearCache s (locN s "node") with clock := c } "go" 1) node level sl child

theorem lookup_restore {F : Type} (s : PanSemStateFiniteExact 64 F) (n : String)
    (old : Option (ValueHOL 64)) (x : MlS) :
    (restore s n old).locals.lookup x = if x = ofString n then old else s.locals.lookup x := by
  cases old <;>
    simp only [restore, HolFiniteMapExact.lookup_resVarEq_none,
      HolFiniteMapExact.lookup_resVarEq_some, FUPDATE_HOL, FDOMSUB_HOL]

theorem locN_clearCache {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) (n : String) :
    locN (clearCache s a) n = locN s n := rfl

theorem prepared_locN {F : Type} (s : PanSemStateFiniteExact 64 F) (n : String)
    (hne : ofString n ∉ ["r", "next_node", "next_slot", "next_level", "go"].map ofString) :
    locN (prepared s) n = locN s n := by
  have hn : ofString n ≠ ofString "r" ∧ ofString n ≠ ofString "next_node" ∧
      ofString n ≠ ofString "next_slot" ∧ ofString n ≠ ofString "next_level" ∧
      ofString n ≠ ofString "go" := by simpa only [List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false, not_or] using hne
  simp only [prepared, declared, locN_put, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2, if_false]

theorem prepared_lookup {F : Type} (s : PanSemStateFiniteExact 64 F) (n : String)
    (hne : ofString n ∉ ["r", "next_node", "next_slot", "next_level", "go"].map ofString) :
    (prepared s).locals.lookup (ofString n) = s.locals.lookup (ofString n) := by
  have hn : ofString n ≠ ofString "r" ∧ ofString n ≠ ofString "next_node" ∧
      ofString n ≠ ofString "next_slot" ∧ ofString n ≠ ofString "next_level" ∧
      ofString n ≠ ofString "go" := by simpa only [List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false, not_or] using hne
  simp only [prepared, declared, lookup_put, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2, if_false]

theorem cleanup_arena {F : Type} (s t : PanSemStateFiniteExact 64 F)
    (ha : ArenaReady t) : ArenaReady (cleanup s t) :=
  restore_arena _ _ (restore_arena _ _ (restore_arena _ _ (restore_arena _ _ ha)))

theorem cleanup_go {F : Type} (s t : PanSemStateFiniteExact 64 F) :
    locN (cleanup s t) "go" = locN t "go" := by
  simp +decide [cleanup, locN, lookup_restore]

theorem dec_zero {F : Type} {s t : PanSemStateFiniteExact 64 F} {n : String} {b : ProgHOL 64}
    (hr : evaluateHOLFiniteState s (.dec (ofString n) .one (constant 0) b) = (none, t)) :
    ∃ u, evaluateHOLFiniteState (put s n 0) b = (none, u) ∧
      t = restore u n (s.locals.lookup (ofString n)) := by
  obtain ⟨v, u, hv, he, ht⟩ := dec_none hr
  cases RunFramesRace.evalAt_const s 0 v hv
  exact ⟨u, he, ht⟩

theorem body_unwrap {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hr : evaluateHOLFiniteState s mptInsertBody = (none, t)) :
    ∃ u, evaluateHOLFiniteState (declared s) core = (none, u) ∧ t = cleanup s u := by
  rw [body_eq] at hr
  obtain ⟨u1, h1, ht⟩ := dec_zero hr
  obtain ⟨u2, h2, hu1⟩ := dec_zero h1
  obtain ⟨u3, h3, hu2⟩ := dec_zero h2
  obtain ⟨u4, h4, hu3⟩ := dec_zero h3
  refine ⟨u4, h4, ?_⟩
  rw [ht, hu1, hu2, hu3]
  simp +decide [lookup_put, cleanup]

theorem cleanup_finished {F : Type} (s : PanSemStateFiniteExact 64 F) (c : Nat)
    (node level sl child : BitVec 64) :
    cleanup s (finished (descended
      { clearCache (prepared s) (locN s "node") with clock := c } node level sl child)
      node level sl child) = finalState s c node level sl child := by
  have hslot : locN (descended { clearCache (prepared s) (locN s "node") with clock := c }
      node level sl child) "slot" = locN s "slot" := by
    simp +decide [descended, locN_put, locN_clock, locN_clearCache, prepared, declared]
  have hslot' : locN (put { clearCache s (locN s "node") with clock := c } "go" 1) "slot" =
      locN s "slot" := by simp +decide [locN_put, locN_clock, locN_clearCache]
  unfold finalState finished
  rw [hslot, hslot']
  by_cases hz : locN s "slot" = 0 <;> simp only [hz, if_true, if_false]
  all_goals
    have hl : (cleanup s (put (put (put
        (if locN s "slot" = 0 then put (descended
          { clearCache (prepared s) (locN s "node") with clock := c } node level sl child)
          "result" node else descended { clearCache (prepared s) (locN s "node") with clock := c }
          node level sl child) "node" child) "slot" (node + 48)) "level" (level + sl))).locals =
        (put (put (put (if locN s "slot" = 0 then
          put (put { clearCache s (locN s "node") with clock := c } "go" 1) "result" node
          else put { clearCache s (locN s "node") with clock := c } "go" 1)
          "node" child) "slot" (node + 48)) "level" (level + sl)).locals := by
      apply HolFiniteMapExact.ext
      funext x
      by_cases hr : x = ofString "r"
      · subst x
        simp +decide [cleanup, lookup_restore, lookup_put, hz, descended, prepared, declared, clearCache]
      by_cases hn : x = ofString "next_node"
      · subst x
        simp +decide [cleanup, lookup_restore, lookup_put, hz, descended, prepared, declared, clearCache]
      by_cases hs : x = ofString "next_slot"
      · subst x
        simp +decide [cleanup, lookup_restore, lookup_put, hz, descended, prepared, declared, clearCache]
      by_cases hl : x = ofString "next_level"
      · subst x
        simp +decide [cleanup, lookup_restore, lookup_put, hz, descended, prepared, declared, clearCache]
      simp only [cleanup, lookup_restore, lookup_put, hz, if_true, if_false, hr, hn, hs, hl,
        descended, prepared, declared, clearCache]
      split <;> simp_all only [lookup_put, if_true, if_false]
    simp only [hz, if_true, if_false] at hl
    dsimp only [cleanup, restore, put, setVarHOLFinite, descended, prepared, declared, clearCache] at hl ⊢
    congr 1

theorem finalState_shape {F : Type} (s : PanSemStateFiniteExact 64 F) (c : Nat)
    (node level sl child : BitVec 64) :
    finalState s c node level sl child =
      { clearCache s (locN s "node") with
        locals := (finalState s c node level sl child).locals, clock := c } := by
  unfold finalState finished
  split <;> rfl

theorem finalState_lookup {F : Type} (s : PanSemStateFiniteExact 64 F) (c : Nat)
    (node level sl child : BitVec 64) (x : MlS) :
    (finalState s c node level sl child).locals.lookup x =
      if x = ofString "level" then some (.val (.word (level + sl)))
      else if x = ofString "slot" then some (.val (.word (node + 48)))
      else if x = ofString "node" then some (.val (.word child))
      else if locN s "slot" = 0 ∧ x = ofString "result" then some (.val (.word node))
      else if x = ofString "go" then some (.val (.word 1)) else s.locals.lookup x := by
  have hslot : locN (put { clearCache s (locN s "node") with clock := c } "go" 1) "slot" =
      locN s "slot" := by simp +decide [locN_put, locN_clock, locN_clearCache]
  unfold finalState finished
  rw [hslot]
  by_cases hz : locN s "slot" = 0 <;>
    simp only [hz, if_true, if_false, lookup_put, true_and, false_and]
  all_goals rfl

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
