import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Invariant

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE InitECandidate.Solver.Wave8GuestInv

def normIvl (i : Ivl) : Ivl := if i.2 = 0 then (0, 0) else i

@[simp] theorem disj_norm (i j : Ivl) : Disj (normIvl i) (normIvl j) ↔ Disj i j := by
  unfold normIvl
  split_ifs <;> simp_all [Disj]

theorem pairwise_disj_mem {xs : List Ivl} (h : xs.Pairwise Disj)
    {i j : Ivl} (hi : i ∈ xs) (hj : j ∈ xs) (hne : i ≠ j) : Disj i j := by
  induction xs with
  | nil => simp at hi
  | cons a xs ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp hi with hia | hi'
    · rcases List.mem_cons.mp hj with hja | hj'
      · exact (hne (hia.trans hja.symm)).elim
      · rw [hia]; exact ha j hj'
    · rcases List.mem_cons.mp hj with hja | hj'
      · rw [hja]; exact disj_symm (ha i hi')
      · exact ih ht hi' hj'

def bufferIvls {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)

def fixedRaw {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  bufferIvls s ++ [(globN s "journal", 32 * globN s "journal_cap")] ++ blockOutObjects s ++ balObjects s

theorem fixed_pairwise_raw {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : FixedTyped s) : (fixedRaw s).Pairwise Disj := by
  have hp : ((fixedRaw s).map normIvl).Pairwise Disj := h.2
  simpa only [List.pairwise_map, disj_norm] using hp

theorem fixed_mem_raw {F : Type} {s : PanSemStateFiniteExact 64 F} {i : Ivl}
    (hi : i ∈ fixedRaw s) (hn : i.2 ≠ 0) : i ∈ fixedObjects s := by
  apply mem_normalized hi
  exact fun hz => (hn hz).elim

theorem fixed_disj_raw {F : Type} {s : PanSemStateFiniteExact 64 F} {i j : Ivl}
    (h : ∀ k ∈ fixedObjects s, Disj i k) (hj : j ∈ fixedRaw s) : Disj i j := by
  by_cases hz : j.2 = 0
  · exact Or.inr (Or.inl hz)
  · exact h j (fixed_mem_raw hj hz)

theorem buffer_mem_raw {F : Type} (s : PanSemStateFiniteExact 64 F)
    {gn : String × Nat} (h : gn ∈ globalBuffers) :
    (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2) ∈ fixedRaw s := by
  apply List.mem_append.mpr; left
  apply List.mem_append.mpr; left
  apply List.mem_append.mpr; left
  exact List.mem_map.mpr ⟨gn, h, rfl⟩

theorem buffer_pair_disj {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : FixedTyped s) {a b : String × Nat}
    (ha : a ∈ globalBuffers) (hb : b ∈ globalBuffers) (hne : a ≠ b) :
    Disj (globN s a.1, if globN s a.1 = 0 then 0 else a.2)
      (globN s b.1, if globN s b.1 = 0 then 0 else b.2) := by
  have hp := fixed_pairwise_raw h
  simp only [fixedRaw, List.pairwise_append] at hp
  have hbfs := hp.1.1.1
  rw [bufferIvls, List.pairwise_map] at hbfs
  obtain ⟨ia, hia, eqa⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨ib, hib, eqb⟩ := List.mem_iff_getElem.mp hb
  have hn : ia ≠ ib := by intro he; subst he; exact hne (eqa.symm.trans eqb)
  rcases Nat.lt_or_gt_of_ne hn with hlt | hgt
  · have hr := (List.pairwise_iff_getElem.mp hbfs) ia ib hia hib hlt
    simpa only [eqa, eqb] using hr
  · have hr := (List.pairwise_iff_getElem.mp hbfs) ib ia hib hia hgt
    exact disj_symm (by simpa only [eqa, eqb] using hr)

theorem buffer_disj_rest {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : FixedTyped s) {a : String × Nat} (ha : a ∈ globalBuffers)
    {j : Ivl} (hj : j ∈ [(globN s "journal", 32 * globN s "journal_cap")] ++
      blockOutObjects s ++ balObjects s) :
    Disj (globN s a.1, if globN s a.1 = 0 then 0 else a.2) j := by
  have hp := fixed_pairwise_raw h
  rw [fixedRaw, List.append_assoc, List.append_assoc, List.pairwise_append] at hp
  apply hp.2.2 _ (List.mem_map.mpr ⟨a, ha, rfl⟩) j
  simpa only [List.append_assoc] using hj

theorem block_mem_raw {F : Type} {s : PanSemStateFiniteExact 64 F} {i : Ivl}
    (hi : i ∈ blockOutObjects s) : i ∈ fixedRaw s := by
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hi)))

theorem bal_mem_raw {F : Type} {s : PanSemStateFiniteExact 64 F} {i : Ivl}
    (hi : i ∈ balObjects s) : i ∈ fixedRaw s := List.mem_append.mpr (Or.inr hi)

theorem allocated_lower {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {i : Ivl} (h : Allocated s i) : sourceBase ≤ i.1 := by
  rcases h with h | h
  · exact h.1
  · have hsb : sourceBase ≤ scratchStart := by decide
    exact hsb.trans (hA.2.2.1.trans (hA.2.2.2.1.trans h.1))

theorem nodeExtents_lower {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (h : NodeHeap s Nd) {i : Ivl} (hi : i ∈ nodeExtents s Nd) :
    i.2 = 0 ∨ sourceBase ≤ i.1 := by
  obtain ⟨n, hn, hi⟩ := List.mem_flatMap.mp hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact Or.inr (h.1 n hn).2.2.2.2.1.1
  · unfold nodePath
    split_ifs with hc
    · have hk := (h.1 n hn).2.2.2.2.2.2.2.2 hc.1
      exact Or.inr ((hk.resolve_left hc.2).2.2.1.1)
    · exact Or.inl rfl

theorem worldOwned_lower {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {i : Ivl} (hi : i ∈ worldOwned s S Nd) : i.2 = 0 ∨ sourceBase ≤ i.1 := by
  rcases List.mem_append.mp hi with hi | hi
  · rcases List.mem_append.mp hi with hi | hi
    · obtain ⟨t, ht, hi⟩ := List.mem_flatMap.mp hi
      exact Or.inr (((hW.1.2.1 t ht).1.1 i hi).1.1)
    · rcases hW.2.2.1.1 i hi with hz | ⟨hal, _⟩
      · exact Or.inl hz
      · exact Or.inr (allocated_lower hA hal)
  · exact nodeExtents_lower hW.2.2.2.1 hi

theorem worldTypedIvls_mem {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {i : Ivl} (hi : i ∈ worldTypedIvls s S Nd) :
    i = (0, 0) ∨ i ∈ worldOwned s S Nd := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  split_ifs with hz
  · exact Or.inl rfl
  · right
    simp only [List.mem_append] at hj
    rcases hj with ((((ht | hr) | hjr) | hb) | hbal) | hnd
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ht)))
    · obtain ⟨r, hrec, rfl⟩ := List.mem_map.mp hr
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
        (Or.inr (typedRecord_mem_fixedObjects s hrec))))
    · apply List.mem_append.mpr; left; apply List.mem_append.mpr; right
      apply fixed_mem_raw (hn := hz)
      simp only [fixedRaw, List.mem_append]; exact Or.inl (Or.inl (Or.inr hjr))
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (fixed_mem_raw (block_mem_raw hb) hz))))
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (fixed_mem_raw (bal_mem_raw hbal) hz))))
    · exact List.mem_append.mpr (Or.inr hnd)

theorem typed_disj_of_owned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {i : Ivl} (h : ∀ j ∈ worldOwned s S Nd, Disj i j) :
    ∀ j ∈ worldTypedIvls s S Nd, Disj i j := by
  intro j hj
  rcases worldTypedIvls_mem hj with rfl | hj
  · exact disj_zero_right i
  · exact h j hj

theorem buffer_disj_typed {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {gn : String × Nat} (hgn : gn ∈ globalBuffers) (hnot : gn ∉ typedRecords)
    (hn : 0 < gn.2) (hsmall : gn.2 ≤ sourceBase) :
    ∀ j ∈ worldTypedIvls s S Nd, Disj (globN s gn.1, gn.2) j := by
  by_cases hz : globN s gn.1 = 0
  · intro j hj
    rcases worldTypedIvls_mem hj with rfl | hj
    · exact disj_zero_right _
    · rcases worldOwned_lower hA hW hj with hj | hj
      · exact Or.inr (Or.inl hj)
      · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
  · have hm : (globN s gn.1, gn.2) ∈ fixedObjects s := by
      apply fixed_mem_raw (hn := by dsimp; omega)
      simpa only [hz, if_false] using buffer_mem_raw s hgn
    intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    split_ifs with hiz
    · exact disj_zero_right _
    · simp only [List.mem_append] at hi
      rcases hi with ((((ht | hr) | hjr) | hb) | hbal) | hnd
      · obtain ⟨t, ht, hi⟩ := List.mem_flatMap.mp ht
        exact disj_symm (((hW.1.2.1 t ht).2 i hi).2 _ hm)
      · obtain ⟨r, hrec, rfl⟩ := List.mem_map.mp hr
        have hne : gn ≠ r := by intro he; exact hnot (he ▸ hrec)
        simpa only [hz, if_false] using buffer_pair_disj hW.2.2.1 hgn
          (typedRecord_mem_globalBuffers hrec) hne
      · simpa only [hz, if_false] using buffer_disj_rest hW.2.2.1 hgn
          (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hjr))))
      · simpa only [hz, if_false] using buffer_disj_rest hW.2.2.1 hgn
          (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hb))))
      · simpa only [hz, if_false] using buffer_disj_rest hW.2.2.1 hgn
          (List.mem_append.mpr (Or.inr hbal))
      · exact disj_symm ((hW.2.2.2.2.1 i hnd).2 _ hm)

theorem input_disj_buffer {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {i : Ivl} (hlo : sourceBase ≤ i.1)
    (hd : ∀ j ∈ worldOwned s S Nd, Disj i j)
    {gn : String × Nat} (hgn : gn ∈ globalBuffers)
    (hn : 0 < gn.2) (hsmall : gn.2 ≤ sourceBase) : Disj i (globN s gn.1, gn.2) := by
  by_cases hz : globN s gn.1 = 0
  · exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))
  · apply hd
    apply List.mem_append.mpr; left; apply List.mem_append.mpr; right
    apply fixed_mem_raw (hn := by dsimp; omega)
    simpa only [hz, if_false] using buffer_mem_raw s hgn

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
