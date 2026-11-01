import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertCountLocals

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.InsertCount
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Leaves.Rlp

def Normal {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.locals.lookup (ofString "go") = some (.val (.word 1)) ∧
    WordLocal (ofString "node") s ∧ WordLocal (ofString "slot") s ∧
    WordLocal (ofString "level") s ∧ locN s "slot" ≠ 0

theorem normal_active {F : Type} {s : PanSemStateFiniteExact 64 F} (h : Normal s) :
    locN s "go" ≠ 0 := by simp only [locN, h.1]; decide

theorem loc_lt {F : Type} (s : PanSemStateFiniteExact 64 F) (n : String) : locN s n < 2 ^ 64 := by
  unfold locN
  split
  · exact BitVec.isLt _
  · decide

theorem slot_info {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hh : MptInsertHead s) (ha : locN s "go" ≠ 0) (hs : locN s "slot" ≠ 0) :
    sourceBase ≤ locN s "slot" ∧ locN s "slot" - sourceBase < 2 ^ 28 ∧
      memW s (locN s "slot") = locN s "node" := by
  obtain ⟨_, Nd, hn, _, _, hslot, _, _⟩ := hh.2 ha
  obtain ⟨p, hp, hk, hv⟩ := hslot.resolve_left hs
  have hlo := (hn.1 p hp).2.2.1.1
  have hi := (hn.1 p hp).2.2.1.2
  change sourceBase ≤ p at hlo
  change p + nodeSize (memW s p) ≤ heapLimit at hi
  suffices sourceBase ≤ locN s "slot" ∧ locN s "slot" - sourceBase < 2 ^ 28 from
    ⟨this.1, this.2, hv⟩
  rcases hk with ⟨hk, hslot⟩ | ⟨hk, i, hi', hslot⟩
  · rw [hk] at hi
    norm_num [nodeSize, heapLimit, scratchStart, sourceBase] at hi hlo ⊢
    omega
  · rw [hk] at hi
    norm_num [nodeSize, heapLimit, scratchStart, sourceBase] at hi hlo ⊢
    omega

/-- Parent slots determine the current node through `MptSlotOK`. This needs only
one 28-bit heap-offset key, even for a cycle containing many nodes. -/
def key {F : Type} (s : PanSemStateFiniteExact 64 F) : Fin (2 ^ 28) :=
  ⟨(locN s "slot" - sourceBase) % 2 ^ 28, Nat.mod_lt _ (by decide)⟩

structure Frame {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop where
  head_s : MptInsertHead s
  head_t : MptInsertHead t
  normal_s : Normal s
  normal_t : Normal t
  state : t = {s with locals := t.locals, clock := t.clock}
  level : locN t "level" = locN s "level"
  result : t.locals.lookup (ofString "result") = s.locals.lookup (ofString "result")
  other : ∀ x, x ∉ observed → t.locals.lookup x = s.locals.lookup x

theorem frame_trans {F : Type} (s t u : PanSemStateFiniteExact 64 F)
    (a : Frame s t) (b : Frame t u) : Frame s u := by
  refine ⟨a.head_s, b.head_t, a.normal_s, b.normal_t, ?_,
    b.level.trans a.level, b.result.trans a.result, fun x hx => (b.other x hx).trans (a.other x hx)⟩
  calc u = {t with locals := u.locals, clock := u.clock} := b.state
       _ = {s with locals := u.locals, clock := u.clock} := by rw [a.state]

theorem word_lookup_eq {F : Type} {s t : PanSemStateFiniteExact 64 F} (n : String)
    (hs : WordLocal (ofString n) s) (ht : WordLocal (ofString n) t)
    (h : locN t n = locN s n) : t.locals.lookup (ofString n) = s.locals.lookup (ofString n) := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := ht
  simp only [locN, ha, hb] at h
  rw [ha, hb, BitVec.eq_of_toNat_eq h]

theorem frame_key {F : Type} (s t : PanSemStateFiniteExact 64 F)
    (h : Frame s t) (hk : key s = key t) : t = {s with clock := t.clock} := by
  obtain ⟨hsl, hss, hsn⟩ := slot_info h.head_s (normal_active h.normal_s) h.normal_s.2.2.2.2
  obtain ⟨htl, hts, htn⟩ := slot_info h.head_t (normal_active h.normal_t) h.normal_t.2.2.2.2
  have hslot : locN t "slot" = locN s "slot" := by
    have h' := congrArg Fin.val hk
    simp only [key, Nat.mod_eq_of_lt hss, Nat.mod_eq_of_lt hts] at h'
    omega
  have hm : t.memory = s.memory := by rw [h.state]
  have hnode : locN t "node" = locN s "node" := by
    rw [← htn, hslot, ← hsn]
    simp only [memW, hm]
  have hl : t.locals = s.locals := by
    apply HolFiniteMapExact.ext_lookup
    intro x
    by_cases hg : x = ofString "go"
    · subst hg; rw [h.normal_s.1, h.normal_t.1]
    by_cases hn : x = ofString "node"
    · subst hn; exact word_lookup_eq _ h.normal_s.2.1 h.normal_t.2.1 hnode
    by_cases hs : x = ofString "slot"
    · subst hs; exact word_lookup_eq _ h.normal_s.2.2.1 h.normal_t.2.2.1 hslot
    by_cases hv : x = ofString "level"
    · subst hv; exact word_lookup_eq _ h.normal_s.2.2.2.1 h.normal_t.2.2.2.1 h.level
    by_cases hr : x = ofString "result"
    · subst hr; exact h.result
    exact h.other x (by simp [observed, hg, hn, hs, hv, hr])
  calc t = {s with locals := t.locals, clock := t.clock} := h.state
       _ = {s with clock := t.clock} := by rw [hl]

/-- Each level has at most `heapLimit - sourceBase` cache warmups and one normalization step.
Between them, no active parent slot can repeat on a terminating run. -/
noncomputable def phase {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat := by
  classical
  exact if locN s "go" = 0 then 0 else
    (65 - locN s "level") * (2 * (heapLimit - sourceBase + 1)) +
      2 * (dirty s).card + if Normal s then 0 else 1

theorem phase_le {F : Type} (s : PanSemStateFiniteExact 64 F) : phase s ≤ 2 ^ 36 := by
  classical
  have hd := dirty_le s
  have hl : 65 - locN s "level" ≤ 65 := Nat.sub_le _ _
  unfold phase
  split
  · omega
  · split <;> norm_num [heapLimit, scratchStart, sourceBase] at hd ⊢ <;> omega

theorem level_le {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : MptInsertHead s) (ha : locN s "go" ≠ 0) : locN s "level" ≤ 64 := by
  obtain ⟨hl, _, _, _, _, _, _, hk⟩ := hs.2 ha
  omega

theorem phase_pos {F : Type} {s : PanSemStateFiniteExact 64 F} (hs : MptInsertActive s) :
    0 < phase s := by
  classical
  have hl := level_le hs.1 hs.2
  have hd := dirty_le s
  simp only [phase, if_neg hs.2]
  split <;> norm_num [heapLimit, scratchStart, sourceBase] <;> omega

theorem phase_strict {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hs : MptInsertActive s) (ht : MptInsertActive t)
    (hl : locN s "level" < locN t "level") : phase t < phase s := by
  classical
  have ls := level_le hs.1 hs.2
  have lt := level_le ht.1 ht.2
  have ds := dirty_le s
  have dt := dirty_le t
  simp only [phase, if_neg hs.2, if_neg ht.2]
  split <;> split <;> norm_num [heapLimit, scratchStart, sourceBase] at ds dt ⊢ <;> omega


/-- A step either starts a smaller phase or stays in the exact finite-key frame.
All semantic effects come from the supplied one-iteration interface. -/
theorem step_phase {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hs : MptInsertActive s) (ht : MptInsertHead t) (he : MptInsertEffect s t)
    (hr : evaluateHOLFiniteState s mptInsertBody = (none, t)) :
    (phase t = phase s ∧ Frame s t) ∨ phase t < phase s := by
  classical
  by_cases htgo : locN t "go" = 0
  · right
    have hp := phase_pos hs
    simpa only [phase, if_pos htgo] using hp
  obtain ⟨_, _, _, _, hprogress⟩ := he.resolve_left htgo
  rcases hprogress with hl | hz
  · exact Or.inr (phase_strict hs ⟨ht, htgo⟩ hl)
  obtain ⟨hn0, hkind, hlen, hlevel, hnode, hslot, hresult, hstate, hother⟩ := hz
  obtain ⟨hg, wn, ws, wl, hresultRaw⟩ := body_locals hr
  have hg1 : t.locals.lookup (ofString "go") = some (.val (.word 1)) := by
    rcases hg with hg | hg
    · exact False.elim (htgo (by simp only [locN, hg]; rfl))
    · exact hg
  have hnormal : Normal t := ⟨hg1, wn, ws, wl, by omega⟩
  obtain ⟨_, Nd, hheap, hroot, _, _⟩ := hs.1.2 hs.2
  have hnmem : locN s "node" ∈ Nd := hroot.resolve_left hn0
  have hlo := (hheap.1 _ hnmem).2.2.1.1
  have hi := (hheap.1 _ hnmem).2.2.1.2
  change sourceBase ≤ locN s "node" at hlo
  change locN s "node" + nodeSize (memW s (locN s "node")) ≤ heapLimit at hi
  rw [hkind] at hi
  have hbound : locN s "node" + 24 < heapLimit := by
    norm_num [nodeSize] at hi
    omega
  have hdirty : dirty t = dirty (clearCache s (locN s "node")) := by rw [hstate]; rfl
  have hdle : (dirty t).card ≤ (dirty s).card := by
    rw [hdirty]
    exact Finset.card_le_card (dirty_clear_subset _ _)
  by_cases hdeq : (dirty t).card = (dirty s).card
  · have hclear : clearCache s (locN s "node") = s :=
      clear_eq_of_dirty_eq _ _ hlo hbound (by simpa only [hdirty] using hdeq)
    by_cases hns : Normal s
    · left
      refine ⟨?_, hs.1, ht, hns, hnormal, ?_, hlevel,
        hresultRaw hns.2.2.2.2, hother⟩
      · simp only [phase, if_neg hs.2, if_neg htgo, if_pos hns, if_pos hnormal, hlevel, hdeq]
      · simpa only [hclear] using hstate
    · right
      simp only [phase, if_neg hs.2, if_neg htgo, if_neg hns, if_pos hnormal, hlevel, hdeq]
      omega
  · right
    have hdlt : (dirty t).card < (dirty s).card := by omega
    simp only [phase, if_neg hs.2, if_neg htgo, if_pos hnormal, hlevel]
    split <;> omega

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.InsertCount
