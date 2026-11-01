import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

/-! The exact memory update in rev9 `InvalidatesCache` is idempotent.
This is a supporting lemma, not a proof of any `GBody` target. -/

set_option autoImplicit false
namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The update at nd+8, nd+16, nd+24 specified by `InvalidatesCache`. -/
def clearCache {F : Type} (s : PanSemStateFiniteExact 64 F) (nd : Nat) :
    PanSemStateFiniteExact 64 F :=
  { s with memory := fun a =>
      if a = BitVec.ofNat 64 (nd + 8) ∨ a = BitVec.ofNat 64 (nd + 16) ∨
          a = BitVec.ofNat 64 (nd + 24)
      then HolWordLab.word 0 else s.memory a }

theorem clearCache_idempotent {F : Type} (s : PanSemStateFiniteExact 64 F) (nd : Nat) :
    clearCache (clearCache s nd) nd = clearCache s nd := by
  unfold clearCache
  congr 1
  funext a
  split <;> simp_all

/-- Once the cache is warm, a second invalidation changes only locals and clock.
The surrounding caller still has to prove that its own locals and stores repeat. -/
theorem clearCache_warm_effect {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (nd : Nat)
    (heffect : post = { clearCache (clearCache s nd) nd with
        locals := post.locals, clock := post.clock }) :
    post = { clearCache s nd with locals := post.locals, clock := post.clock } := by
  simpa only [clearCache_idempotent] using heffect

/-- Cache invalidation followed by the caller's pointer store. -/
def clearCacheAndStore {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nd slot : Nat) : PanSemStateFiniteExact 64 F :=
  let z := clearCache s nd
  { z with memory := fun a => if a = BitVec.ofNat 64 slot
      then HolWordLab.word (BitVec.ofNat 64 nd) else z.memory a }

/-- Repeating both writes is idempotent, even without an aliasing assumption. -/
theorem clearCacheAndStore_idempotent {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nd slot : Nat) :
    clearCacheAndStore (clearCacheAndStore s nd slot) nd slot =
      clearCacheAndStore s nd slot := by
  dsimp only [clearCacheAndStore, clearCache]
  congr 1
  funext a
  by_cases hs : a = BitVec.ofNat 64 slot
  · simp only [hs, if_true]
  · simp only [hs, if_false]
    split <;> simp_all

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
