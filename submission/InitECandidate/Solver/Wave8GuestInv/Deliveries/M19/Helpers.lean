import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Multiset.AddSub

/-! Abstract crit-bit tree invariants (the list part of `HtabWF`, over a node-field function
`nd` and an order function `ord`) and their preservation by the deletion of a leaf. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8M19.Htab

def FreeChainF (nd : Nat → Nat → Nat) : Nat → List Nat → Prop
  | head, [] => head = 0
  | head, f :: rest => head = f ∧ FreeChainF nd (nd f 0) rest

def TreeWF (L I Fr : List Nat) (next klen cnt root free : Nat) (nd : Nat → Nat → Nat)
    (ord : Nat → Nat) : Prop :=
  L.length = cnt ∧ (L ++ I ++ Fr).Nodup ∧ (∀ n, n ∈ L ++ I ++ Fr ↔ 1 ≤ n ∧ n < next) ∧
  ((cnt = 0 ∧ I = []) ∨ I.length + 1 = cnt) ∧
  (∀ (i : Nat) (h : i < L.length), ord i = L[i] ∧ nd L[i] 24 = 8 * klen ∧ nd L[i] 16 = i) ∧
  (∀ n ∈ I, nd n 24 < 8 * klen ∧ nd n 8 ∈ L ++ I ∧ nd n 16 ∈ L ++ I ∧ nd n 8 ≠ nd n 16 ∧
    nd (nd n 8) 0 = n ∧ nd (nd n 16) 0 = n) ∧
  (cnt = 0 → root = 0) ∧ (0 < cnt → root ∈ L ++ I ∧ nd root 0 = 0) ∧
  (∀ n ∈ I, nd n 8 ≠ root ∧ nd n 16 ≠ root) ∧
  (∀ n ∈ L ++ I, n ≠ root → nd n 0 ∈ I) ∧
  (∃ dep : Nat → Nat, ∀ n ∈ L ++ I, n ≠ root →
    (nd (nd n 0) 8 = n ∨ nd (nd n 0) 16 = n) ∧ dep (nd n 0) < dep n) ∧
  FreeChainF nd free Fr

theorem FreeChainF.congr {nd nd' : Nat → Nat → Nat} :
    ∀ (Fr : List Nat) (head : Nat), (∀ f ∈ Fr, nd' f 0 = nd f 0) →
      FreeChainF nd head Fr → FreeChainF nd' head Fr
  | [], _, _, h => h
  | f :: rest, head, hc, ⟨h1, h2⟩ => by
    refine ⟨h1, ?_⟩
    rw [hc f (List.mem_cons_self)]
    exact FreeChainF.congr rest _ (fun x hx => hc x (List.mem_cons_of_mem _ hx)) h2

theorem set_dropLast_perm : ∀ (L : List Nat) (pos : Nat) (hpos : pos < L.length), L.Nodup →
    ((L.set pos (L[L.length - 1]'(by omega))).dropLast).Perm (L.erase (L[pos]))
  | [], pos, hpos, _ => by simp at hpos
  | [a], pos, hpos, _ => by
    have : pos = 0 := by simp at hpos; omega
    subst this; simp
  | a :: b :: t, 0, _, hnd => by
    simp only [List.set_cons_zero, List.getElem_cons_zero, List.erase_cons_head]
    rw [List.dropLast_cons_of_ne_nil (by simp)]
    have hl : (a :: b :: t)[(a :: b :: t).length - 1] = (b :: t).getLast (by simp) := by
      simp [List.getLast_eq_getElem]
    rw [hl]
    have := List.dropLast_append_getLast (l := b :: t) (by simp)
    conv_rhs => rw [← this]
    exact (List.perm_append_singleton _ _).symm
  | a :: b :: t, k + 1, hpos, hnd => by
    have hpos' : k < (b :: t).length := by simp at hpos ⊢; omega
    have ih := set_dropLast_perm (b :: t) k hpos' (List.nodup_cons.mp hnd).2
    have hl : (a :: b :: t)[(a :: b :: t).length - 1] = (b :: t)[(b :: t).length - 1] := by
      simp
    have hne : a ≠ (b :: t)[k] := by
      intro h
      exact (List.nodup_cons.mp hnd).1 (h ▸ List.getElem_mem _)
    simp only [List.set_cons_succ, List.getElem_cons_succ]
    rw [hl, List.dropLast_cons_of_ne_nil (by simp), List.erase_cons_tail (by simpa using hne)]
    exact ih.cons a

/-- In a rooted tree, a nonempty set of internal nodes contains the root. -/
theorem root_mem_I {L I : List Nat} {root : Nat} {nd : Nat → Nat → Nat} (dep : Nat → Nat)
    (hpar : ∀ n ∈ L ++ I, n ≠ root → nd n 0 ∈ I)
    (hdep : ∀ n ∈ L ++ I, n ≠ root → dep (nd n 0) < dep n) :
    ∀ n ∈ I, root ∈ I := by
  intro n hn
  induction h : dep n using Nat.strong_induction_on generalizing n with
  | _ k ih =>
    by_cases hr : n = root
    · subst hr; exact hn
    · have hnLI : n ∈ L ++ I := List.mem_append_right _ hn
      exact ih (dep (nd n 0)) (h ▸ hdep n hnLI hr) (nd n 0) (hpar n hnLI hr) rfl

/-- Deleting the root leaf: the table becomes empty and the leaf heads the free list. -/
theorem treeWF_del_root {L I Fr : List Nat} {next klen cnt root free : Nat}
    {nd nd' : Nat → Nat → Nat} {ord ord' : Nat → Nat} (leaf : Nat)
    (h : TreeWF L I Fr next klen cnt root free nd ord) (hleaf : leaf ∈ L) (hroot : leaf = root)
    (hnd0 : nd' leaf 0 = free) (hfr : ∀ f ∈ Fr, nd' f 0 = nd f 0) :
    cnt = 1 ∧ L = [leaf] ∧ I = [] ∧ TreeWF [] [] (leaf :: Fr) next klen 0 0 leaf nd' ord' := by
  obtain ⟨hlen, hnodup, hmem, hcI, hord, hint, hr0, hr1, hrc, hpar, ⟨dep, hdep⟩, hfc⟩ := h
  have hI : I = [] := by
    rcases I with _ | ⟨n, rest⟩
    · rfl
    · exfalso
      have hrI := root_mem_I (L := L) (I := n :: rest) (root := root) (nd := nd) dep hpar
        (fun x hx hxr => (hdep x hx hxr).2) n (List.mem_cons_self)
      have hnd2 := (List.nodup_append.mp hnodup).1
      exact (List.nodup_append.mp hnd2).2.2 leaf hleaf root hrI hroot
  subst hI
  have hcnt : cnt = 1 := by
    rcases hcI with ⟨hc0, _⟩ | hc1
    · subst hc0
      rw [List.length_eq_zero_iff] at hlen
      subst hlen
      simp at hleaf
    · simpa using hc1.symm
  subst hcnt
  have hL : L = [leaf] := by
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
    subst ha
    simp at hleaf
    subst hleaf
    rfl
  subst hL
  refine ⟨rfl, rfl, rfl, rfl, by simpa using hnodup, fun n => by simpa using hmem n, Or.inl ⟨rfl, rfl⟩,
    fun i hi => by simp at hi, fun n hn => by simp at hn, fun _ => rfl, fun h => by omega,
    fun n hn => by simp at hn, fun n hn => by simp at hn, ⟨dep, fun n hn => by simp at hn⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  rw [hnd0]
  exact FreeChainF.congr Fr free hfr hfc

theorem perm_del (L I Fr L' : List Nat) (leaf p : Nat) (hl : leaf ∈ L) (hp : p ∈ I) (hL' : L'.Perm (L.erase leaf)) :
    (L' ++ I.erase p ++ leaf :: p :: Fr).Perm (L ++ I ++ Fr) := by
  rw [← Multiset.coe_eq_coe]
  have h1 : (L' : Multiset Nat) = (L : Multiset Nat).erase leaf := by
    rw [Multiset.coe_erase]; exact Multiset.coe_eq_coe.mpr hL'
  simp only [← Multiset.coe_add, ← Multiset.cons_coe, h1, ← Multiset.coe_erase]
  rw [Multiset.add_cons, Multiset.add_cons, ← Multiset.cons_add, ← Multiset.cons_add]
  have hL := Multiset.cons_erase (Multiset.mem_coe.mpr hl)
  have hI := Multiset.cons_erase (Multiset.mem_coe.mpr hp)
  conv_rhs => rw [← hL, ← hI]
  rw [Multiset.cons_add, Multiset.add_cons, Multiset.cons_add, Multiset.cons_add, Multiset.cons_swap, Multiset.cons_add, Multiset.cons_add]

/-- Deleting a non-root leaf: its parent `p` and the leaf go to the free list, the sibling `s`
takes `p`'s place under the grandparent `g` (or becomes the root), and the last leaf `mv` moves
into the vacated order slot. -/
theorem treeWF_del_inner {L I Fr : List Nat} {next klen cnt root free : Nat}
    {nd nd' : Nat → Nat → Nat} {ord ord' : Nat → Nat} (leaf : Nat)
    (h : TreeWF L I Fr next klen cnt root free nd ord) (hleaf : leaf ∈ L) (hnr : leaf ≠ root)
    (hL0 : 0 < L.length)
    (h0 : ∀ n ∈ L ++ I ++ Fr, nd' n 0 =
      if n = (if nd (nd leaf 0) 8 = leaf then nd (nd leaf 0) 16 else nd (nd leaf 0) 8) then
        nd (nd leaf 0) 0
      else if n = nd leaf 0 then free else if n = leaf then nd leaf 0 else nd n 0)
    (h8 : ∀ n ∈ L ++ I ++ Fr, nd' n 8 =
      if n = nd (nd leaf 0) 0 ∧ nd (nd (nd leaf 0) 0) 8 = nd leaf 0 then
        (if nd (nd leaf 0) 8 = leaf then nd (nd leaf 0) 16 else nd (nd leaf 0) 8)
      else nd n 8)
    (h16 : ∀ n ∈ L ++ I ++ Fr, nd' n 16 =
      if n = L[L.length - 1]'(by omega) then nd leaf 16
      else if n = nd (nd leaf 0) 0 ∧ nd (nd (nd leaf 0) 0) 8 ≠ nd leaf 0 then
        (if nd (nd leaf 0) 8 = leaf then nd (nd leaf 0) 16 else nd (nd leaf 0) 8)
      else nd n 16)
    (h24 : ∀ n ∈ L ++ I ++ Fr, nd' n 24 = nd n 24)
    (hord : ∀ i < cnt - 1, ord' i =
      if i = nd leaf 16 then L[L.length - 1]'(by omega) else ord i) :
    TreeWF ((L.set (nd leaf 16) (L[L.length - 1]'(by omega))).dropLast) (I.erase (nd leaf 0))
      (leaf :: nd leaf 0 :: Fr) next klen (cnt - 1)
      (if nd (nd leaf 0) 0 = 0 then
        (if nd (nd leaf 0) 8 = leaf then nd (nd leaf 0) 16 else nd (nd leaf 0) 8) else root)
      leaf nd' ord' := by
  obtain ⟨hlen, hnodup, hmem, hcI, hordL, hint, hr0, hr1, hrc, hpar, ⟨dep, hdep⟩, hfc⟩ := h
  -- names
  set p := nd leaf 0 with hpdef
  set g := nd p 0 with hgdef
  set s := (if nd p 8 = leaf then nd p 16 else nd p 8) with hsdef
  set pos := nd leaf 16 with hposdef
  set mv := L[L.length - 1]'(by omega) with hmvdef
  -- list facts
  have hnd12 := List.nodup_append.mp hnodup
  have hndLI := List.nodup_append.mp hnd12.1
  have hLnd : L.Nodup := hndLI.1
  have hInd : I.Nodup := hndLI.2.1
  have hLI : ∀ a ∈ L, a ∉ I := fun a ha hai => hndLI.2.2 a ha a hai rfl
  have hLIF : ∀ a ∈ L ++ I, a ∉ Fr := fun a ha haf => hnd12.2.2 a ha a haf rfl
  have hpos1 : ∀ n ∈ L ++ I ++ Fr, 1 ≤ n := fun n hn => ((hmem n).1 hn).1
  have hleafLI : leaf ∈ L ++ I := List.mem_append_left _ hleaf
  have hpI : p ∈ I := hpar leaf hleafLI hnr
  have hpLI : p ∈ L ++ I := List.mem_append_right _ hpI
  have hLIa : ∀ a ∈ L ++ I, a ∈ L ++ I ++ Fr := fun a ha => List.mem_append_left _ ha
  -- `pos` is the index of `leaf`
  obtain ⟨i0, hi0, hli0⟩ := List.getElem_of_mem hleaf
  have hpos : pos = i0 := by rw [hposdef, ← hli0]; exact (hordL i0 hi0).2.2
  -- count
  have hcnt : I.length + 1 = cnt := by
    rcases hcI with ⟨_, hI0⟩ | h1
    · rw [hI0] at hpI; simp at hpI
    · exact h1
  have hIpos : 0 < I.length := List.length_pos_of_mem hpI
  -- children of `p`
  obtain ⟨hpcrit, hp8, hp16, hp816, hp8p, hp16p⟩ := hint p hpI
  have hleafchild : nd p 8 = leaf ∨ nd p 16 = leaf := (hdep leaf hleafLI hnr).1
  have hsLI : s ∈ L ++ I := by rw [hsdef]; split <;> assumption
  have hsp : nd s 0 = p := by rw [hsdef]; split <;> assumption
  have hsleaf : s ≠ leaf := by
    rw [hsdef]; split
    · rename_i h; rw [← h]; exact Ne.symm hp816
    · rename_i h; exact h
  have hother : nd p 8 = leaf ∧ nd p 16 = s ∨ nd p 8 = s ∧ nd p 16 = leaf := by
    rw [hsdef]; split
    · rename_i h; exact Or.inl ⟨h, rfl⟩
    · rename_i h; exact Or.inr ⟨rfl, hleafchild.resolve_left h⟩
  have hcnt2 : 2 ≤ cnt := by omega
  have hrootLI : root ∈ L ++ I := (hr1 (by omega)).1
  have hroot0 : nd root 0 = 0 := (hr1 (by omega)).2
  have hpleaf : p ≠ leaf := fun h => hLI leaf hleaf (h ▸ hpI)
  have hp1 : 1 ≤ p := hpos1 p (hLIa p hpLI)
  have hs1 : 1 ≤ s := hpos1 s (hLIa s hsLI)
  have hleaf1 : 1 ≤ leaf := hpos1 leaf (hLIa leaf hleafLI)
  have hsroot : s ≠ root := fun h => by rw [h, hroot0] at hsp; omega
  have hsp' : s ≠ p := by
    intro h
    by_cases hpr : p = root
    · rw [← hpr] at hroot0; rw [h] at hsp; rw [hsp] at hroot0; omega
    · have := (hdep p hpLI hpr).2; rw [← h, hsp, h] at this; omega
  -- the grandparent
  have hgroot : p = root → g = 0 := fun h => by rw [hgdef, h]; exact hroot0
  have hgI : p ≠ root → g ∈ I := fun h => hpar p hpLI h
  have hg0 : g = 0 ↔ p = root := by
    constructor
    · intro hg; by_contra hpr
      have := hpos1 g (hLIa g (List.mem_append_right _ (hgI hpr))); omega
    · exact hgroot
  have hgp : g ≠ p := by
    by_cases hpr : p = root
    · rw [hgroot hpr]; omega
    · intro h; have := (hdep p hpLI hpr).2; rw [← hgdef, h] at this; omega
  have hsg : s ≠ g := by
    by_cases hpr : p = root
    · rw [hgroot hpr]; omega
    · intro h
      have h1 := (hdep p hpLI hpr).2
      have h2 := (hdep s hsLI hsroot).2
      rw [hsp] at h2
      rw [← hgdef, ← h] at h1
      omega
  have hleafg : leaf ≠ g := by
    by_cases hpr : p = root
    · rw [hgroot hpr]; omega
    · exact fun h => hLI leaf hleaf (h ▸ hgI hpr)
  have hgchild : p ≠ root → nd g 8 = p ∨ nd g 16 = p := fun h => (hdep p hpLI h).1
  -- children of `p` are exactly `leaf` and `s`
  have hchildp : ∀ n ∈ L ++ I, n ≠ root → nd n 0 = p → n = leaf ∨ n = s := by
    intro n hn hnr' hnp
    have := (hdep n hn hnr').1
    rw [hnp] at this
    rcases hother with ⟨h8, h16⟩ | ⟨h8, h16⟩ <;> rcases this with e | e
    · left; rw [← e, h8]
    · right; rw [← e, h16]
    · right; rw [← e, h8]
    · left; rw [← e, h16]
  -- the moved leaf
  have hmvL : mv ∈ L := List.getElem_mem _
  have hmvI : ∀ n ∈ I, n ≠ mv := fun n hn e => hLI mv hmvL (e ▸ hn)
  -- membership in the new live set
  have hpi0 : pos < L.length := by rw [hpos]; exact hi0
  have hL'perm := set_dropLast_perm L pos hpi0 hLnd
  have hLpos : L[pos] = leaf := by simp only [hpos]; exact hli0
  rw [hLpos] at hL'perm
  set L' := (L.set pos mv).dropLast with hL'def
  have hmemL' : ∀ x, x ∈ L' ↔ x ∈ L ∧ x ≠ leaf := fun x => by
    rw [hL'perm.mem_iff, hLnd.mem_erase_iff]; exact and_comm
  have hmemI' : ∀ x, x ∈ I.erase p ↔ x ∈ I ∧ x ≠ p := fun x => by
    rw [hInd.mem_erase_iff]; exact and_comm
  have hmemLI' : ∀ x, x ∈ L' ++ I.erase p ↔ x ∈ L ++ I ∧ x ≠ leaf ∧ x ≠ p := by
    intro x
    simp only [List.mem_append, hmemL', hmemI']
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨Or.inl h1, h2, fun e => hLI x h1 (e ▸ hpI)⟩
      · exact ⟨Or.inr h1, fun e => hLI x (e ▸ hleaf) h1, h2⟩
    · rintro ⟨h1 | h1, h2, h3⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h3⟩
  have hperm := perm_del L I Fr L' leaf p hleaf hpI hL'perm
  -- unchanged fields
  have hu0 : ∀ n ∈ L ++ I ++ Fr, n ≠ s → n ≠ p → n ≠ leaf → nd' n 0 = nd n 0 := by
    intro n hn h1 h2 h3; rw [h0 n hn, if_neg h1, if_neg h2, if_neg h3]
  have hs0 : nd' s 0 = g := by rw [h0 s (hLIa s hsLI), if_pos rfl]
  have hp0 : nd' p 0 = free := by rw [h0 p (hLIa p hpLI), if_neg (Ne.symm hsp'), if_pos rfl]
  have hl0 : nd' leaf 0 = p := by
    rw [h0 leaf (hLIa leaf hleafLI), if_neg (Ne.symm hsleaf), if_neg (Ne.symm hpleaf), if_pos rfl]
  have hu8 : ∀ n ∈ L ++ I ++ Fr, n ≠ g → nd' n 8 = nd n 8 := by
    intro n hn h1; rw [h8 n hn, if_neg (fun h => h1 h.1)]
  have hu16 : ∀ n ∈ L ++ I ++ Fr, n ≠ mv → n ≠ g → nd' n 16 = nd n 16 := by
    intro n hn h1 h2; rw [h16 n hn, if_neg h1, if_neg (fun h => h2 h.1)]
  -- the new tree
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hL'def, List.length_dropLast, List.length_set, hlen]
  · exact hperm.nodup_iff.mpr hnodup
  · intro n; rw [hperm.mem_iff]; exact hmem n
  · right
    rw [List.length_erase_of_mem hpI]
    omega
  · intro i hi
    have hi' : i < L.length - 1 := by
      have : L'.length = L.length - 1 := by rw [hL'def, List.length_dropLast, List.length_set]
      omega
    have hgi : L'[i] = if pos = i then mv else L[i]'(by omega) := by
      simp only [hL'def, List.getElem_dropLast, List.getElem_set]
    rw [hgi]
    have hord' := hord i (by omega)
    by_cases hpi : pos = i
    · subst hpi
      simp only [if_true] at hord' ⊢
      refine ⟨hord', ?_, ?_⟩
      · rw [h24 mv (hLIa mv (List.mem_append_left _ hmvL))]
        have := (hordL (L.length - 1) (by omega)).2.1
        exact this
      · rw [h16 mv (hLIa mv (List.mem_append_left _ hmvL)), if_pos rfl]
    · have hipos : ¬ i = pos := fun e => hpi e.symm
      simp only [hpi, hipos, if_false] at hord' ⊢
      have hLi : L[i]'(by omega) ∈ L := List.getElem_mem _
      have hLiI : L[i]'(by omega) ∈ L ++ I ++ Fr := hLIa _ (List.mem_append_left _ hLi)
      have hne_mv : L[i]'(by omega) ≠ mv := by
        intro e
        have := (List.Nodup.getElem_inj_iff hLnd).mp e
        omega
      have hne_g : L[i]'(by omega) ≠ g := by
        by_cases hpr : p = root
        · rw [hgroot hpr]; have := hpos1 _ hLiI; omega
        · exact fun e => hLI _ hLi (e ▸ hgI hpr)
      refine ⟨by rw [hord']; exact (hordL i (by omega)).1, ?_, ?_⟩
      · rw [h24 _ hLiI]; exact (hordL i (by omega)).2.1
      · rw [hu16 _ hLiI hne_mv hne_g]; exact (hordL i (by omega)).2.2
  · intro n hn
    obtain ⟨hnI, hnp⟩ := (hmemI' n).mp hn
    have hnLI : n ∈ L ++ I := List.mem_append_right _ hnI
    have hnA := hLIa n hnLI
    obtain ⟨hc24, hc8, hc16, hc816, hc8p, hc16p⟩ := hint n hnI
    have hnmv := hmvI n hnI
    rw [h24 n hnA]
    by_cases hng : n = g
    · -- the grandparent: its child `p` is replaced by `s`
      have hpr : p ≠ root := fun e => by rw [hg0.mpr e] at hng; have := hpos1 n hnA; omega
      subst hng
      have hsA : s ∈ L' ++ I.erase p := (hmemLI' s).mpr ⟨hsLI, hsleaf, hsp'⟩
      by_cases h8p : nd g 8 = p
      · have hc : nd g 16 ≠ p := fun e => hc816 (h8p.trans e.symm)
        have hcLI := hc16
        have hcleaf : nd g 16 ≠ leaf := fun e => by
          have := hc16p; rw [e] at this; exact hgp (this.symm.trans rfl) |>.elim
        rw [h8 g hnA, if_pos ⟨rfl, h8p⟩, h16 g hnA, if_neg (fun e => hnmv e),
          if_neg (fun h => h.2 h8p)]
        have hcs : nd g 16 ≠ s := fun e => by
          have := hc16p; rw [e, hsp] at this; exact hgp this.symm
        refine ⟨hc24, hsA, (hmemLI' _).mpr ⟨hc16, hcleaf, hc⟩, fun e => hcs e.symm, hs0, ?_⟩
        rw [hu0 _ (hLIa _ hc16) hcs hc hcleaf]; exact hc16p
      · have h16p : nd g 16 = p := (hgchild hpr).resolve_left h8p
        have hcleaf : nd g 8 ≠ leaf := fun e => by
          have := hc8p; rw [e] at this; exact hgp (this.symm.trans rfl) |>.elim
        rw [h8 g hnA, if_neg (fun h => h8p h.2), h16 g hnA, if_neg (fun e => hnmv e),
          if_pos ⟨rfl, h8p⟩]
        have hcs : nd g 8 ≠ s := fun e => by
          have := hc8p; rw [e, hsp] at this; exact hgp this.symm
        refine ⟨hc24, (hmemLI' _).mpr ⟨hc8, hcleaf, h8p⟩, hsA, hcs, ?_, hs0⟩
        rw [hu0 _ (hLIa _ hc8) hcs h8p hcleaf]; exact hc8p
    · -- any other internal node keeps its children
      rw [hu8 n hnA hng, hu16 n hnA hnmv hng]
      have hok : ∀ c, c ∈ L ++ I → nd c 0 = n →
          c ∈ L' ++ I.erase p ∧ nd' c 0 = n := by
        intro c hc hcn
        have hcp : c ≠ p := fun e => hng (by rw [← hcn, e])
        have hcl : c ≠ leaf := fun e => hnp (by rw [← hcn, e])
        have hcs : c ≠ s := fun e => hnp (by rw [← hcn, e, hsp])
        exact ⟨(hmemLI' c).mpr ⟨hc, hcl, hcp⟩, by rw [hu0 c (hLIa c hc) hcs hcp hcl]; exact hcn⟩
      obtain ⟨m8, e8⟩ := hok _ hc8 hc8p
      obtain ⟨m16, e16⟩ := hok _ hc16 hc16p
      exact ⟨hc24, m8, m16, hc816, e8, e16⟩
  · intro h; omega
  · intro _
    by_cases hg : g = 0
    · rw [if_pos hg]
      exact ⟨(hmemLI' s).mpr ⟨hsLI, hsleaf, hsp'⟩, by rw [hs0, hg]⟩
    · rw [if_neg hg]
      have hpr : p ≠ root := fun e => hg (hgroot e)
      refine ⟨(hmemLI' root).mpr ⟨hrootLI, fun e => hnr e.symm, fun e => hpr e.symm⟩, ?_⟩
      rw [hu0 root (hLIa root hrootLI) (fun e => hsroot e.symm) (fun e => hpr e.symm)
        (fun e => hnr e.symm)]
      exact hroot0
  · intro n hn
    obtain ⟨hnI, hnp⟩ := (hmemI' n).mp hn
    have hnLI : n ∈ L ++ I := List.mem_append_right _ hnI
    have hnA := hLIa n hnLI
    obtain ⟨_, hc8, hc16, _, hc8p, hc16p⟩ := hint n hnI
    have hnmv := hmvI n hnI
    by_cases hg : g = 0
    · rw [if_pos hg]
      have hng : n ≠ g := by rw [hg]; have := hpos1 n hnA; omega
      rw [hu8 n hnA hng, hu16 n hnA hnmv hng]
      constructor
      · intro e; rw [e, hsp] at hc8p; exact hnp hc8p.symm
      · intro e; rw [e, hsp] at hc16p; exact hnp hc16p.symm
    · rw [if_neg hg]
      obtain ⟨hr8, hr16⟩ := hrc n hnI
      by_cases hng : n = g
      · subst hng
        rw [h8 g hnA, h16 g hnA, if_neg (fun e => hnmv e)]
        by_cases h8p : nd g 8 = p
        · rw [if_pos ⟨rfl, h8p⟩, if_neg (fun h => h.2 h8p)]
          exact ⟨hsroot, hr16⟩
        · rw [if_neg (fun h => h8p h.2), if_pos ⟨rfl, h8p⟩]
          exact ⟨hr8, hsroot⟩
      · rw [hu8 n hnA hng, hu16 n hnA hnmv hng]
        exact ⟨hr8, hr16⟩
  · intro n hn hnr'
    obtain ⟨hnLI, hnl, hnp⟩ := (hmemLI' n).mp hn
    by_cases hns : n = s
    · rw [hns] at hnr' ⊢
      have hg : g ≠ 0 := fun hg => hnr' (by rw [if_pos hg])
      have hpr : p ≠ root := fun e => hg (hgroot e)
      rw [hs0]
      exact (hmemI' g).mpr ⟨hgI hpr, hgp⟩
    · rw [hu0 n (hLIa n hnLI) hns hnp hnl]
      have hnroot : n ≠ root := by
        by_cases hg : g = 0
        · intro e; exact hnp (e.trans ((hg0.mp hg).symm))
        · rw [if_neg hg] at hnr'; exact hnr'
      have hq := hpar n hnLI hnroot
      refine (hmemI' _).mpr ⟨hq, fun e => ?_⟩
      rcases hchildp n hnLI hnroot e with h | h
      · exact hnl h
      · exact hns h
  · refine ⟨dep, ?_⟩
    intro n hn hnr'
    obtain ⟨hnLI, hnl, hnp⟩ := (hmemLI' n).mp hn
    by_cases hns : n = s
    · rw [hns] at hnr' ⊢
      have hg : g ≠ 0 := fun hg => hnr' (by rw [if_pos hg])
      have hpr : p ≠ root := fun e => hg (hgroot e)
      have hgA : g ∈ L ++ I ++ Fr := hLIa g (List.mem_append_right _ (hgI hpr))
      rw [hs0]
      refine ⟨?_, ?_⟩
      · by_cases h8p : nd g 8 = p
        · left; rw [h8 g hgA, if_pos ⟨rfl, h8p⟩]
        · right; rw [h16 g hgA, if_neg (fun e => hmvI g (hgI hpr) e), if_pos ⟨rfl, h8p⟩]
      · have h1 := (hdep p hpLI hpr).2
        have h2 := (hdep s hsLI hsroot).2
        rw [hsp] at h2
        rw [← hgdef] at h1
        omega
    · rw [hu0 n (hLIa n hnLI) hns hnp hnl]
      have hnroot : n ≠ root := by
        by_cases hg : g = 0
        · intro e; exact hnp (e.trans ((hg0.mp hg).symm))
        · rw [if_neg hg] at hnr'; exact hnr'
      obtain ⟨hch, hdp⟩ := hdep n hnLI hnroot
      refine ⟨?_, hdp⟩
      have hqI := hpar n hnLI hnroot
      have hqA : nd n 0 ∈ L ++ I ++ Fr := hLIa _ (List.mem_append_right _ hqI)
      have hqmv := hmvI _ hqI
      have hqp : nd n 0 ≠ p := fun e => by
        rcases hchildp n hnLI hnroot e with h | h
        · exact hnl h
        · exact hns h
      by_cases hqg : nd n 0 = g
      · rw [h8 _ hqA, h16 _ hqA, if_neg hqmv]
        by_cases h8p : nd g 8 = p
        · rw [if_pos ⟨hqg, h8p⟩, if_neg (fun h => h.2 h8p)]
          right
          rcases hch with e | e
          · rw [hqg, h8p] at e; exact absurd e.symm hnp
          · exact e
        · rw [if_neg (fun h => h8p h.2), if_pos ⟨hqg, h8p⟩]
          left
          rcases hch with e | e
          · exact e
          · have hpr : p ≠ root := fun e' => by
              have := hg0.mpr e'; rw [← hqg] at this
              have := hpos1 _ hqA; omega
            have h16p := (hgchild hpr).resolve_left h8p
            rw [hqg, h16p] at e; exact absurd e.symm hnp
      · rw [hu8 _ hqA hqg, hu16 _ hqA hqmv hqg]
        exact hch
  · refine ⟨rfl, hl0, ?_⟩
    rw [hp0]
    refine FreeChainF.congr Fr free (fun f hf => ?_) hfc
    have hfA : f ∈ L ++ I ++ Fr := List.mem_append_right _ hf
    have hfLI : f ∉ L ++ I := fun h => hLIF f h hf
    refine hu0 f hfA (fun e => hfLI (e ▸ hsLI)) (fun e => hfLI (e ▸ hpLI)) (fun e => hfLI (e ▸ hleafLI))

end InitECandidate.Solver.Wave8M19.Htab

/-! Generic field-level effect of unlinking an internal node. Both child positions use the
same lemma. The memory realization will instantiate `fields` after the order-slot move. -/

set_option autoImplicit false
namespace InitECandidate.Solver.Wave8M19.Htab

def fieldWrite (fields : Nat → Nat → Nat) (node offset value : Nat) : Nat → Nat → Nat :=
  fun n k => if n = node ∧ k = offset then value else fields n k

def unlinkFields (fields : Nat → Nat → Nat) (leaf parent grand sibling free : Nat)
    (left : Bool) : Nat → Nat → Nat :=
  let f := fieldWrite fields sibling 0 grand
  let f := if grand = 0 then f else fieldWrite f grand (if left then 8 else 16) sibling
  fieldWrite (fieldWrite f parent 0 free) leaf 0 parent

/-- Removing `parent`, replacing it by `sibling` at either grandparent child slot, and
prepending `leaf,parent` to the free list has this uniform field effect. A zero grandparent
means that the header's root is changed instead, so every live node's child slots are untouched. -/
theorem unlinkFields_spec (fields : Nat → Nat → Nat) (leaf parent grand sibling free n : Nat)
    (left : Bool) (hlp : leaf ≠ parent) (hsp : sibling ≠ parent) (hsl : sibling ≠ leaf)
    (hn : 0 < n) :
    unlinkFields fields leaf parent grand sibling free left n 0 =
      (if n = sibling then grand else if n = parent then free else if n = leaf then parent else fields n 0) ∧
    unlinkFields fields leaf parent grand sibling free left n 8 =
      (if n = grand ∧ left = true then sibling else fields n 8) ∧
    unlinkFields fields leaf parent grand sibling free left n 16 =
      (if n = grand ∧ left = false then sibling else fields n 16) ∧
    unlinkFields fields leaf parent grand sibling free left n 24 = fields n 24 := by
  cases left <;> by_cases hg : grand = 0 <;>
    simp only [unlinkFields, fieldWrite, hg, ↓reduceIte, Bool.false_eq_true,
      Bool.true_eq_false, and_false, and_true, and_self, Nat.reduceEqDiff] <;>
    split_ifs <;> simp_all <;> omega

end InitECandidate.Solver.Wave8M19.Htab
