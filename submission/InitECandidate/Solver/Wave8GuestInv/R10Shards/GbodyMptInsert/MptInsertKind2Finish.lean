import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind2Extension

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem assign_local_word {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {dst src : String} {w : BitVec 64}
    (hv : s.locals.lookup (ofString src) = some (.val (.word w)))
    (hr : evaluateHOLFiniteState s (assign dst (lv src)) = (none, t)) :
    t = put s dst w := by
  obtain ⟨v, he, ht⟩ := assign_none hr
  change s.locals.lookup (ofString src) = some v at he
  rw [hv] at he
  cases Option.some.inj he
  exact ht

theorem store_local_redundant {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {dst src : String} {w : BitVec 64}
    (hv : s.locals.lookup (ofString src) = some (.val (.word w)))
    (hm : s.memory (BitVec.ofNat 64 (locN s dst)) = .word w)
    (hr : evaluateHOLFiniteState s (.store (lv dst) (lv src)) = (none, t)) : t = s := by
  rw [evaluateHOLFiniteState_store] at hr
  split at hr
  · rename_i a ha
    have haN := RunFramesRace.evalAt_local s dst a ha
    have haw : a = BitVec.ofNat 64 (locN s dst) := by
      simp only [← haN, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hsrc : evalAt s (lv src) = some (.val (.word w)) := hv
    dsimp only [evalAt] at hsrc
    rw [hsrc] at hr
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hr
    split at hr
    · rename_i memory hstore
      have hmemory : (fun b => if b = a then .word w else s.memory b) = s.memory := by
        funext b
        split
        · rename_i hb
          subst b
          exact (haw ▸ hm).symm
        · rfl
      have hm' : memory = s.memory := by
        by_cases hd : s.memaddrs a
        · simpa only [if_pos hd, hmemory, Option.some.injEq] using hstore.symm
        · simp only [if_neg hd] at hstore
          cases hstore
      rw [hm'] at hr
      exact (congrArg Prod.snd hr).symm
    · cases hr
  · cases hr

def finished {F : Type} (s : PanSemStateFiniteExact 64 F)
    (node level sl child : BitVec 64) :=
  put (put (put (if locN s "slot" = 0 then put s "result" node else s)
    "node" child) "slot" (node + 48)) "level" (level + sl)

/-- The shared tail links the current extension and installs the saved descent cursor. -/
theorem tail_descended {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (node level sl child : BitVec 64)
    (hm : locN s "slot" ≠ 0 → s.memory (BitVec.ofNat 64 (locN s "slot")) = .word node)
    (hr : evaluateHOLFiniteState (descended s node level sl child) tail = (none, t)) :
    t = finished (descended s node level sl child) node level sl child := by
  let d := descended s node level sl child
  have hdslot : locN d "slot" = locN s "slot" := by
    simp +decide [d, descended, locN_put]
  have hdr : d.locals.lookup (ofString "r") = some (.val (.word node)) := by
    simp +decide [d, descended, lookup_put]
  rw [tail_eq] at hr
  obtain ⟨u1, hfirst, hrest⟩ := seq_none hr
  have hu1 : u1 = if locN d "slot" = 0 then put d "result" node else d := by
    rcases ite_none hfirst with ⟨hc, ha⟩ | ⟨hc, hs⟩
    · have hz : locN d "slot" = 0 := by simpa using condTrue_local_eq_const hc
      rw [if_pos hz]
      exact assign_local_word hdr ha
    · have hz : locN d "slot" ≠ 0 := by simpa using condFalse_local_eq_const hc
      rw [if_neg hz]
      apply store_local_redundant hdr _ hs
      change s.memory (BitVec.ofNat 64 (locN d "slot")) = .word node
      rw [hdslot]
      exact hm (hdslot ▸ hz)
  let u := if locN d "slot" = 0 then put d "result" node else d
  change u1 = u at hu1
  subst u1
  have hu (n : String) (hne : ofString n ≠ ofString "result") :
      u.locals.lookup (ofString n) = d.locals.lookup (ofString n) := by
    dsimp only [u]
    split <;> simp only [lookup_put, hne, if_false]
  obtain ⟨u2, hn, hrest2⟩ := seq_none hrest
  have hu2 : u2 = put u "node" child := assign_local_word
    (by rw [hu "next_node" (by decide)]; simp +decide [d, descended, lookup_put]) hn
  subst u2
  obtain ⟨u3, hs, hl⟩ := seq_none hrest2
  have hu3 : u3 = put (put u "node" child) "slot" (node + 48) := assign_local_word
    (by simp +decide only [lookup_put, hu "next_slot" (by decide)]
        simp +decide [d, descended, lookup_put]) hs
  subst u3
  have ht : t = put (put (put u "node" child) "slot" (node + 48)) "level" (level + sl) :=
    assign_local_word
      (by simp +decide only [lookup_put, hu "next_level" (by decide)]
          simp +decide [d, descended, lookup_put]) hl
  exact ht

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
