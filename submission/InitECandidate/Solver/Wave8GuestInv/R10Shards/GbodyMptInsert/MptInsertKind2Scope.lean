import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind2Descend

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def restore {F : Type} (s : PanSemStateFiniteExact 64 F) (n : String)
    (old : Option (ValueHOL 64)) :=
  { s with locals := HolFiniteMapExact.resVarEq s.locals (ofString n, old) }

theorem restore_put_same {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n : String) (w : BitVec 64) :
    restore (put s n w) n (s.locals.lookup (ofString n)) = s := by
  have hm : HolFiniteMapExact.resVarEq (s.locals.update (ofString n, .val (.word w)))
      (ofString n, s.locals.lookup (ofString n)) = s.locals := by
    apply HolFiniteMapExact.ext
    funext key
    cases hl : s.locals.lookup (ofString n) with
    | none =>
      simp only [HolFiniteMapExact.resVarEq, HolFiniteMapExact.lookup_eraseEq,
        HolFiniteMapExact.lookup_update_pointwise, FDOMSUB_HOL]
      by_cases hk : key = ofString n <;> simp [hk, hl]
    | some old =>
      simp only [HolFiniteMapExact.resVarEq, HolFiniteMapExact.lookup_updateEq,
        HolFiniteMapExact.lookup_update_pointwise, FUPDATE_HOL]
      by_cases hk : key = ofString n <;> simp [hk, hl]
  dsimp only [restore, put, setVarHOLFinite]
  rw [hm]

theorem restore_put_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n changed : String) (old : Option (ValueHOL 64)) (w : BitVec 64)
    (hne : ofString changed ≠ ofString n) :
    restore (put s changed w) n old = put (restore s n old) changed w := by
  have hm : HolFiniteMapExact.resVarEq (s.locals.update (ofString changed, .val (.word w)))
      (ofString n, old) = (HolFiniteMapExact.resVarEq s.locals (ofString n, old)).update
        (ofString changed, .val (.word w)) := by
    apply HolFiniteMapExact.ext
    funext key
    cases old <;> by_cases ha : key = ofString changed <;> by_cases hb : key = ofString n <;>
      simp_all [HolFiniteMapExact.lookup_resVarEq_none, HolFiniteMapExact.lookup_resVarEq_some,
        HolFiniteMapExact.lookup_update_pointwise, FUPDATE, FUPDATE_HOL, FDOMSUB_HOL]
  dsimp only [restore, put, setVarHOLFinite]
  rw [hm]

theorem restore_go {F : Type} (s : PanSemStateFiniteExact 64 F) (n : String)
    (old : Option (ValueHOL 64)) (hne : ofString "go" ≠ ofString n) :
    locN (restore s n old) "go" = locN s "go" := by
  simp only [restore, locN]
  rw [resVarEq_lookup_ne _ _ _ _ hne]

theorem restore_arena {F : Type} {s : PanSemStateFiniteExact 64 F}
    (n : String) (old : Option (ValueHOL 64)) (ha : ArenaReady s) : ArenaReady (restore s n old) :=
  localsFree_arenaReady s (restore s n old).locals s.clock ha

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
