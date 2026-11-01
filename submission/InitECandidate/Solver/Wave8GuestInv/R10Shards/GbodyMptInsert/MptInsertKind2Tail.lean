import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind2Descend

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem store_arena {F : Type} {s t : PanSemStateFiniteExact 64 F} {a v : ExpHOL 64}
    (ha : ArenaReady s) (hr : evaluateHOLFiniteState s (.store a v) = (none, t)) :
    ArenaReady t ∧ t.locals = s.locals := by
  rw [evaluateHOLFiniteState_store] at hr
  split at hr
  · split at hr
    · split at hr
      · have ht := (congrArg Prod.snd hr).symm
        dsimp only at ht
        subst t
        exact ⟨⟨guestInv_congr (s := s) rfl rfl rfl rfl ha.1, ha.2⟩, rfl⟩
      · cases hr
    · cases hr
  · cases hr

theorem assign_arena_go {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {name : String} {e : ExpHOL 64} (ha : ArenaReady s) (hne : ofString "go" ≠ ofString name)
    (hr : evaluateHOLFiniteState s (assign name e) = (none, t)) :
    ArenaReady t ∧ locN t "go" = locN s "go" := by
  obtain ⟨v, _, ht⟩ := assign_none hr
  subst t
  exact ⟨localsFree_arenaReady s _ s.clock ha,
    RunFramesRace.locN_setVar_ne s "go" (ofString name) v hne⟩

/-- The common tail preserves arena ownership and the loop-control word. -/
theorem tail_arena_go {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (ha : ArenaReady s) (hr : evaluateHOLFiniteState s tail = (none, t)) :
    ArenaReady t ∧ locN t "go" = locN s "go" := by
  rw [tail_eq] at hr
  obtain ⟨s1, h1, hr1⟩ := seq_none hr
  have hmid : ArenaReady s1 ∧ locN s1 "go" = locN s "go" := by
    rcases ite_none h1 with ⟨_, hresult⟩ | ⟨_, hstore⟩
    · exact assign_arena_go ha (by decide) hresult
    · obtain ⟨ha1, hl⟩ := store_arena ha hstore
      exact ⟨ha1, by simp only [locN, hl]⟩
  obtain ⟨s2, h2, hr2⟩ := seq_none hr1
  obtain ⟨ha2, hg2⟩ := assign_arena_go hmid.1 (by decide) h2
  obtain ⟨s3, h3, hr3⟩ := seq_none hr2
  obtain ⟨ha3, hg3⟩ := assign_arena_go ha2 (by decide) h3
  obtain ⟨hat, hgt⟩ := assign_arena_go ha3 (by decide) hr3
  exact ⟨hat, hgt.trans (hg3.trans (hg2.trans hmid.2))⟩

theorem tail_stopped {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (ha : ArenaReady s) (hz : locN s "go" = 0)
    (hr : evaluateHOLFiniteState s tail = (none, t)) :
    MptInsertHead t ∧ MptInsertEffect s t := by
  obtain ⟨hat, hgt⟩ := tail_arena_go ha hr
  have ht0 := hgt.trans hz
  exact ⟨⟨hat, fun hn => False.elim (hn ht0)⟩, Or.inl ht0⟩

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
