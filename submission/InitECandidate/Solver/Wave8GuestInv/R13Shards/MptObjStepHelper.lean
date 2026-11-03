import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_C08WkShard03

/-! Master relational lifting lemma `MptEff.to_mptObjStep` for `mk_mpt_root` and `mk_mpt_set`
(`R13-M4b-MptKeepsTwin`). -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv.R13MptKeepsTwin

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03

/-- Execution effect of a trie-object operation (`mpt_root` or `mpt_set`) on `m = locN s "m"`:
1. `arena`, `grows`, `gw_kept`, `dom_wr`: preserves arenas, grows allocator (`heap_ptr` grows,
   `scratch_ptr ≤` entry `scratch_ptr`), keeps globals outside `gw ⊆ ["heap_ptr", "scratch_ptr"]`,
   and only modifies in-domain cells.
2. `write_frame`: for ANY entry node-set `Nm` of `m` (without assuming `R s` avoids `Nm`, so
   `RecordsKept` holds unconditionally from `MptObjReady s`), every modified cell/byte lies in
   `R s`, untyped global buffers `B`, `mptObjIvls s Nm (locN s "m")`, `freeGap s`, or `heapFree s`.
3. `obj_pres`: for ANY entry node-set `Nm` of `m` from which `R s` is disjoint (`IvlsDisj (R s) (mptObjIvls s Nm m)`),
   `Nm` extends to a typed node-set `Nm'` at `post` rooting `memW post m`, whose node extents lie inside
   `nodeExtents s Nm` or fresh heap `[heap_ptr s, heap_ptr post)`. -/
structure MptEff {F : Type}
    (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl)
    (B : List (String × Nat))
    (gw : List String)
    (s post : PanSemStateFiniteExact 64 F) : Prop where
  arena   : ArenaReady post
  grows   : AllocatorGrows s post
  gw_kept : GlobalsKept gw s post
  dom_wr  : ∀ a : BitVec 64, post.memory a ≠ s.memory a → s.memaddrs a
  write_frame : ∀ Nm : List Nat,
    Allocated s (locN s "m", 16) →
    WordsOK s (locN s "m", 16) →
    NodeHeap s Nm →
    RootIn Nm (memW s (locN s "m")) →
    (∀ o ∈ nodeExtents s Nm, Disj o (locN s "m", 16) ∧ ∀ gs ∈ B, Disj o (bufferRegion s gs)) →
    (∀ gs ∈ B, Disj (locN s "m", 16) (bufferRegion s gs)) →
    (∀ a : BitVec 64, post.memory a ≠ s.memory a →
      (∃ ivl ∈ R s, CellHitsPos a.toNat ivl) ∨
      (∃ gs ∈ B, CellHitsPos a.toNat (bufferRegion s gs)) ∨
      (∃ o ∈ mptObjIvls s Nm (locN s "m"), CellHitsPos a.toNat o) ∨
      CellHitsPos a.toNat (freeGap s) ∨
      CellHitsPos a.toNat (heapFree s)) ∧
    (∀ b : Nat, b < 2 ^ 64 → memB post b ≠ memB s b →
      (∃ ivl ∈ R s, InIvl b ivl) ∨
      (∃ gs ∈ B, InIvl b (bufferRegion s gs)) ∨
      (∃ o ∈ mptObjIvls s Nm (locN s "m"), InIvl b o) ∨
      InIvl b (freeGap s) ∨
      InIvl b (heapFree s))
  obj_pres : ∀ Nm : List Nat,
    Allocated s (locN s "m", 16) →
    WordsOK s (locN s "m", 16) →
    NodeHeap s Nm →
    RootIn Nm (memW s (locN s "m")) →
    (∀ o ∈ nodeExtents s Nm, Disj o (locN s "m", 16) ∧ ∀ gs ∈ B, Disj o (bufferRegion s gs)) →
    (∀ gs ∈ B, Disj (locN s "m", 16) (bufferRegion s gs)) →
    IvlsDisj (R s) (mptObjIvls s Nm (locN s "m")) →
    ∃ Nm' : List Nat,
      NodeHeap post Nm' ∧
      RootIn Nm' (memW post (locN s "m")) ∧
      (∀ o ∈ nodeExtents post Nm',
        o = (0, 0) ∨
        (∃ j ∈ nodeExtents s Nm, Inside o j.1 (j.1 + j.2)) ∨
        Inside o (globN s "heap_ptr") (globN post "heap_ptr"))

theorem freshBufsOK_of_gw_alloc {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {gw : List String} (hgw : GlobalsKept gw s post)
    (hsub : ∀ g ∈ gw, ofString g = ofString "heap_ptr" ∨ ofString g = ofString "scratch_ptr") :
    FreshBufsOK s post := by
  have hg_eq : ∀ gn ∈ globalBuffers, globN post gn.1 = globN s gn.1 := by
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" ∧ ofString gn.1 ≠ ofString "scratch_ptr" := by
      revert gn hgn; decide
    apply globN_eq_of_lookup
    apply hgw
    intro hm
    obtain ⟨g, hg_mem, hg_eq'⟩ := List.mem_map.1 hm
    rcases hsub g hg_mem with h1 | h2
    · exact hne.1 (hg_eq'.symm.trans h1)
    · exact hne.2 (hg_eq'.symm.trans h2)
  refine ⟨fun gn hgn => Or.inl (hg_eq gn hgn), ?_⟩
  rw [List.pairwise_iff_getElem]
  intro i j hi _ _ h1 _
  exact absurd (hg_eq _ (List.getElem_mem hi)) h1.1

theorem disj_fresh_heap_allocated {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) {o j : Ivl}
    (ho : Inside o (globN s "heap_ptr") (globN post "heap_ptr"))
    (hj : j.2 = 0 ∨ Allocated s j) :
    Disj o j := by
  rcases hj with hj0 | hal
  · exact Or.inr (Or.inl hj0)
  · rcases hal with ⟨_, hj2⟩ | ⟨hj1, _⟩
    · exact Or.inr (Or.inr (Or.inr (Nat.le_trans hj2 ho.1)))
    · have hsep : heapLimit ≤ scratchStart := by decide
      have := hAp.2.1; have := hAs.2.2.1; have := hAs.2.2.2.1
      obtain ⟨ho1, ho2⟩ := ho
      exact Or.inr (Or.inr (Or.inl (by omega)))

theorem disj_inside_left {o j k : Ivl}
    (hin : Inside o j.1 (j.1 + j.2)) (hdj : Disj j k) : Disj o k := by
  obtain ⟨h1, h2⟩ := hin
  rcases hdj with h0 | h0 | hd | hd
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl h0)
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

theorem disj_inside_both {o1 j1 o2 j2 : Ivl}
    (h1 : Inside o1 j1.1 (j1.1 + j1.2))
    (h2 : Inside o2 j2.1 (j2.1 + j2.2))
    (hdj : Disj j1 j2) : Disj o1 o2 :=
  Disj.flip (disj_inside_left h2 (Disj.flip (disj_inside_left h1 hdj)))

private theorem bufferRegion_in_fixedObjects {F : Type} (s : PanSemStateFiniteExact 64 F)
    (gs : String × Nat) (hgb : gs ∈ globalBuffers) :
    bufferRegion s gs ∈ fixedObjects s := by
  unfold fixedObjects
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_map.2 ⟨gs, hgb, rfl⟩

private theorem mptObjIvl_disj_worldTypedIvls {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd Nm : List Nat}
    (hWT : WorldTypedWith s S Nd)
    (hm : MptObjInWith s S Nm (locN s "m"))
    (hdisj_nd : IvlsDisj ((locN s "m", 16) :: nodeExtents s Nm) (nodeExtents s Nd))
    {o i : Ivl} (ho : o ∈ mptObjIvls s Nm (locN s "m")) (hi : i ∈ worldTypedIvls s S Nd) :
    Disj o i := by
  obtain ⟨_, hJ, _, _⟩ := hWT
  unfold worldTypedIvls at hi
  simp only [List.mem_append] at hi
  have ho_fix_tab : (∀ t ∈ S, ∀ j ∈ htabFootprint s t, Disj o j) ∧ ∀ j ∈ fixedObjects s, Disj o j := by
    rcases List.mem_cons.1 ho with rfl | ho_ne
    · exact ⟨hm.2.2.1, hm.2.2.2.1⟩
    · exact (hm.2.2.2.2.2.2 o ho_ne).2
  rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
  · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
    exact ho_fix_tab.1 t ht i hfp
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
    exact ho_fix_tab.2 _ (typedRecord_mem_fixedObjects s hr)
  · simp only [List.mem_singleton] at h3; subst h3
    have hj_fo : (if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap") ∈
        fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
      exact List.mem_singleton.2 rfl
    exact ho_fix_tab.2 _ hj_fo
  · have hfo : i ∈ fixedObjects s := by
      unfold fixedObjects; apply List.mem_append_left; apply List.mem_append_right; exact h4
    exact ho_fix_tab.2 i hfo
  · have hfo : i ∈ fixedObjects s := by
      unfold fixedObjects; exact List.mem_append_right _ h5
    exact ho_fix_tab.2 i hfo
  · exact hdisj_nd o ho i h6

theorem MptEff.to_mptObjStep {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {B : List (String × Nat)} {gw : List String}
    {s post : PanSemStateFiniteExact 64 F}
    (hMpt : MptObjReady s)
    (hB_ok : ∀ gs ∈ B, gs ∈ globalBuffers ∧ gs.1 ∉ typedRecords.map Prod.fst)
    (hgw_sub : ∀ g ∈ gw, ofString g = ofString "heap_ptr" ∨ ofString g = ofString "scratch_ptr")
    (heff : MptEff R B gw s post) :
    MptObjStep R gw stdKeep s post := by
  have hAs : ArenaReady s := hMpt.1
  have hAp : ArenaReady post := heff.arena
  have hag : AllocatorGrows s post := heff.grows
  obtain ⟨S0, hWT0, ⟨Nm0, hm0⟩, _⟩ := hMpt.2
  obtain ⟨Nd0, hWTW0⟩ := (worldTyped_iff_with s S0).1 hWT0
  have hcore_out : ∀ g ∈ coreWorldGlobals, ofString g ∉ gw.map ofString := by
    intro g hg
    have hne : ofString g ≠ ofString "heap_ptr" ∧ ofString g ≠ ofString "scratch_ptr" := by
      revert g hg; decide
    intro hm
    obtain ⟨g', hg', heq⟩ := List.mem_map.1 hm
    rcases hgw_sub g' hg' with h1 | h2
    · exact hne.1 (heq.symm.trans h1)
    · exact hne.2 (heq.symm.trans h2)
  have hcore : ∀ g ∈ coreWorldGlobals, globN post g = globN s g :=
    fun g hg => globN_eq_of_lookup (heff.gw_kept (ofString g) (hcore_out g hg))
  have hbuf : FreshBufsOK s post := freshBufsOK_of_gw_alloc heff.gw_kept hgw_sub
  have hlow : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 :=
    ⟨mem_low_eq_of_domain_writes heff.dom_wr hAs.1 (by rw [sourceBase_val]; omega),
     mem_low_eq_of_domain_writes heff.dom_wr hAs.1 (by rw [sourceBase_val]; omega)⟩
  -- 1. `RecordsKept` using `(S0, Nd0, Nm0)` from `hMpt : MptObjReady s`:
  have hRecKept : RecordsKept R stdKeep s post := by
    have hF0 := hWTW0.2.2.1
    obtain ⟨hm0_al, hm0_w, hm0_tab, hm0_fix, hm0_nh, hm0_root, hm0_ext⟩ := hm0
    obtain ⟨hcell0, _⟩ := heff.write_frame Nm0 hm0_al hm0_w hm0_nh hm0_root
      (fun o ho => ⟨(hm0_ext o ho).1, fun gs hgs => (hm0_ext o ho).2.2 _ (bufferRegion_in_fixedObjects s gs (hB_ok gs hgs).1)⟩)
      (fun gs hgs => hm0_fix _ (bufferRegion_in_fixedObjects s gs (hB_ok gs hgs).1))
    intro rec hrec hgnz k hk hnoR
    have hrec_sz : ∃ sz, (rec.1, sz) ∈ typedRecords ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by simp [typedRecords], ?_⟩; simp at hk; omega
      · refine ⟨80, by simp [typedRecords], ?_⟩; simp at hk; omega
      · refine ⟨72, by simp [typedRecords], ?_⟩; simp at hk; omega
      · refine ⟨88, by simp [typedRecords], ?_⟩; simp at hk; omega
    obtain ⟨sz, htr, hk8, hksz⟩ := hrec_sz
    have hmf := typedRecord_mem_fixedObjects s htr
    have hmf_nz : (globN s rec.1, sz) ∈ fixedObjects s := by simpa [hgnz] using hmf
    have hwti_rec : (globN s rec.1, sz) ∈ worldTypedIvls s S0 Nd0 := by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨(rec.1, sz), htr, by simp [hgnz]⟩
    rcases hF0.1 _ hmf_nz with h0 | ⟨hal, hwords⟩
    · omega
    · have hhi := (ivl_allocated_bound hAs.2 hal).2
      have ha_lt : globN s rec.1 + k < 2 ^ 64 := by dsimp at hhi; omega
      unfold memW
      have hmem_eq : post.memory (BitVec.ofNat 64 (globN s rec.1 + k)) =
          s.memory (BitVec.ofNat 64 (globN s rec.1 + k)) := by
        by_contra hne
        have hcases := hcell0 _ hne
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at hcases
        have hin_rec : globN s rec.1 + k ≥ globN s rec.1 ∧ globN s rec.1 + k + 8 ≤ globN s rec.1 + sz :=
          ⟨by omega, by omega⟩
        rcases hcases with ⟨ivl, hivl, _, hhit⟩ | ⟨gs, hgs, hhit⟩ | ⟨o, ho, hhit⟩ | hfg | hhf
        · exact hnoR ivl hivl hhit
        · obtain ⟨hgs_gb, hgs_nt⟩ := hB_ok gs hgs
          have hdj := Disj.flip (untypedBuf_disj_worldTypedIvls hWTW0 gs hgs_gb hgs_nt _ hwti_rec)
          exact not_cellHitsPos_of_disj hin_rec hdj hhit
        · have hdj_o : Disj (globN s rec.1, sz) o := by
            rcases List.mem_cons.1 ho with rfl | ho_ne
            · exact Disj.flip (hm0_fix _ hmf_nz)
            · exact Disj.flip ((hm0_ext o ho_ne).2.2 _ hmf_nz)
          exact not_cellHitsPos_of_disj hin_rec hdj_o hhit
        · exact not_cellHitsPos_of_disj hin_rec (disj_allocated_freeGap hAs.2 hal) hfg
        · exact not_cellHitsPos_of_disj hin_rec (disj_allocated_heapFree hAs.2 hal) hhf
      rw [hmem_eq]
  -- 2. Main relational clause `∀ S Nd Nm, ...`:
  refine ⟨hAp, hag.1, heff.gw_kept, hRecKept, fun S Nd Nm hWT hMptIn hDisjRNmNd hDisjRAll => ?_⟩
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  obtain ⟨hm_al, hm_w, hm_tab, hm_fix, hm_nh, hm_root, hm_ext⟩ := hMptIn
  have hDisjR_wti : IvlsDisj (R s) (worldTypedIvls s S Nd) :=
    fun r hr j hj => hDisjRAll r hr j (List.mem_append_left _ hj)
  have hDisjR_obj : IvlsDisj (R s) (mptObjIvls s Nm (locN s "m")) :=
    fun r hr j hj => hDisjRAll r hr j (List.mem_append_right _ hj)
  have hDisjObj_Nd : IvlsDisj ((locN s "m", 16) :: nodeExtents s Nm) (nodeExtents s Nd) := by
    intro o ho j hj
    rcases List.mem_cons.1 ho with rfl | ho_ne
    · exact hDisjRNmNd (locN s "m", 16) (List.mem_cons_self) j hj
    · exact hDisjRNmNd o (List.mem_cons_of_mem _ (List.mem_append_right _ ho_ne)) j hj
  have hNm_B : ∀ o ∈ nodeExtents s Nm, Disj o (locN s "m", 16) ∧ ∀ gs ∈ B, Disj o (bufferRegion s gs) :=
    fun o ho => ⟨(hm_ext o ho).1,
      fun gs hgs => (hm_ext o ho).2.2 _ (bufferRegion_in_fixedObjects s gs (hB_ok gs hgs).1)⟩
  have hm_B : ∀ gs ∈ B, Disj (locN s "m", 16) (bufferRegion s gs) :=
    fun gs hgs => hm_fix _ (bufferRegion_in_fixedObjects s gs (hB_ok gs hgs).1)
  obtain ⟨hcell, hbyte⟩ := heff.write_frame Nm hm_al hm_w hm_nh hm_root hNm_B hm_B
  obtain ⟨Nm', hNH_Nm', hRoot_Nm', hExt_Nm'⟩ :=
    heff.obj_pres Nm hm_al hm_w hm_nh hm_root hNm_B hm_B hDisjR_obj
  -- Prove `WorldTypedWith post S Nd`:
  let keep0 : List Ivl := R s ++ B.map (bufferRegion s) ++ mptObjIvls s Nm (locN s "m") ++ [freeGap s]
  have hfr_pos : ∀ a : BitVec 64, post.memory a ≠ s.memory a →
      (∃ j ∈ keep0, CellHitsPos a.toNat j) ∨ CellHitsPos a.toNat (heapFree s) := by
    intro a hne
    rcases hcell a hne with ⟨ivl, hivl, hhit⟩ | ⟨gs, hgs, hhit⟩ | ⟨o, ho, hhit⟩ | hfg | hhf
    · left; refine ⟨ivl, ?_, hhit⟩
      simp only [keep0, List.mem_append]; exact Or.inl (Or.inl (Or.inl hivl))
    · left; refine ⟨bufferRegion s gs, ?_, hhit⟩
      simp only [keep0, List.mem_append]; exact Or.inl (Or.inl (Or.inr (List.mem_map.2 ⟨gs, hgs, rfl⟩)))
    · left; refine ⟨o, ?_, hhit⟩
      simp only [keep0, List.mem_append]; exact Or.inl (Or.inr ho)
    · left; refine ⟨freeGap s, ?_, hfg⟩
      simp only [keep0, List.mem_append, List.mem_singleton]; exact Or.inr trivial
    · exact Or.inr hhf
  have hu_wti_aligned : ∀ i ∈ worldTypedIvls s S Nd, Allocated s i → i.1 % 8 = 0 → i.2 % 8 = 0 →
      IvlUnhit s post i := by
    intro i hi hal hi1 hi2
    refine ivlUnhit_of_cellHitsPos hi1 hi2 hfr_pos (fun j hj => ?_) (disj_allocated_heapFree hAs.2 hal)
    simp only [keep0, List.mem_append, List.mem_singleton] at hj
    rcases hj with ((hjR | hjB) | hjM) | rfl
    · exact Disj.flip (hDisjR_wti j hjR i hi)
    · obtain ⟨gs, hgs, rfl⟩ := List.mem_map.1 hjB
      obtain ⟨hgs_gb, hgs_nt⟩ := hB_ok gs hgs
      exact Disj.flip (untypedBuf_disj_worldTypedIvls ⟨hT, hJ, hF, hTr⟩ gs hgs_gb hgs_nt i hi)
    · exact Disj.flip (mptObjIvl_disj_worldTypedIvls ⟨hT, hJ, hF, hTr⟩ ⟨hm_al, hm_w, hm_tab, hm_fix, hm_nh, hm_root, hm_ext⟩ hDisjObj_Nd hjM hi)
    · exact disj_allocated_freeGap hAs.2 hal
  have hu_fix_wti : ∀ i ∈ worldTypedIvls s S Nd, i ∈ fixedObjects s → i.2 ≠ 0 → IvlUnhit s post i := by
    intro i hwti hfi hpos
    rcases hF.1 i hfi with h0 | ⟨hal, hw⟩
    · exact absurd h0 hpos
    · exact hu_wti_aligned i hwti hal hw.1 hw.2.1
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i := by
    intro t ht i hi
    have hal := ((hT.2.1 t ht).2 i hi).1
    have hw := ((hT.2.1 t ht).1.1 i hi).2
    refine hu_wti_aligned i ?_ hal hw.1 hw.2.1
    unfold worldTypedIvls
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
    apply List.mem_append.2; left; apply List.mem_append.2; left
    exact List.mem_flatMap.2 ⟨t, ht, hi⟩
  have hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("ws", 40), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by simp [typedRecords]))
      (by simp)
  have hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("bs", 80), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by simp [typedRecords]))
      (by simp)
  have hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("ts", 72), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by simp [typedRecords]))
      (by simp)
  have hu_bo : globN s "bo" ≠ 0 → IvlUnhit s post (globN s "bo", 88) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("bo", 88), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by simp [typedRecords]))
      (by simp)
  have hu_jr : globN s "journal_cap" ≠ 0 → IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := fun hcnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; right; simp [hcnz])
      (by unfold fixedObjects; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; right; simp [hcnz])
      (by dsimp only; omega)
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → IvlUnhit s post i := fun i hi h24 =>
    hu_fix_wti i
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; right; exact hi)
      (by unfold fixedObjects; apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
      (by omega)
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i := fun i hi hpos =>
    hu_fix_wti i
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
      (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi))
      hpos
  have hu_nd_rec : ∀ n ∈ Nd, IvlUnhit s post (nodeIvl s n) := fun n hn => by
    have hal := (hTr.1.1 n hn).2.1
    have hw := (hTr.1.1 n hn).2.2.2.1
    refine hu_wti_aligned _ ?_ hal hw.1 hw.2.1
    unfold worldTypedIvls; refine List.mem_append.2 (Or.inr ?_)
    unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    have h264 : heapLimit ≤ 2 ^ 64 := by decide
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, hin_p, _⟩
    · exact absurd h0 hlen0
    · have hp_ne : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
      have hp_wti : (memW s (n + 32), memW s (n + 40)) ∈ worldTypedIvls s S Nd := by
        unfold worldTypedIvls; exact List.mem_append.2 (Or.inr hp_ne)
      by_contra hne_b
      have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by have := hin_p.2; dsimp at this; omega
      rcases hbyte _ ha_lt hne_b with ⟨ivl, hivl, hin_ivl⟩ | ⟨gs, hgs, hin_gs⟩ | ⟨o, ho, hin_o⟩ | hfg | hhf
      · have hdj := hDisjR_wti ivl hivl _ hp_wti
        unfold InIvl at hin_ivl; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
      · obtain ⟨hgs_gb, hgs_nt⟩ := hB_ok gs hgs
        have hdj := untypedBuf_disj_worldTypedIvls ⟨hT, hJ, hF, hTr⟩ gs hgs_gb hgs_nt _ hp_wti
        unfold InIvl at hin_gs; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
      · have hdj := hDisjObj_Nd o ho _ hp_ne
        unfold InIvl at hin_o; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
      · have hdj := disj_allocated_freeGap hAs.2 hal_p
        unfold InIvl at hfg; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
      · have hdj := disj_allocated_heapFree hAs.2 hal_p
        unfold InIvl at hhf; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
  have hbo_eq := (blockOutObjects_eq_of_bo_unhit hAs.2 hF (hcore "bo" (by decide))
    hT.2.2.2.2.2.2.2.2.2.2.1 hu_bo hu_bo_lst).1
  have hbal_eq := (balObjects_eq_of_unhit hAs.2 hT hF (hcore "bal_accounts" (by decide))
    hu_tab hu_bal hlow).1
  obtain ⟨hF_post, hfix_new⟩ := fixedTyped_of_freshBufsOK hAs hAp hag hF
    (hcore "journal" (by decide)) (hcore "journal_cap" (by decide)) hbo_eq hbal_eq hbuf
  obtain ⟨hWT_post, hOG_world, hne_eq, hfp_eq⟩ := worldTypedWith_congr_w1 hAs hAp hag hcore
    ⟨hT, hJ, hF, hTr⟩ hu_tab hu_ws hu_bs hu_ts hu_bo hu_jr hu_bo_lst hu_bal hu_nd_rec hu_nd_byte
    hlow hF_post hfix_new
  have hfix_eq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [hbo_eq, hbal_eq, hcore "journal" (by decide), hcore "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" ∧ ofString gn.1 ≠ ofString "scratch_ptr" := by
      revert gn hgn; decide
    have heq : globN post gn.1 = globN s gn.1 := by
      apply globN_eq_of_lookup
      apply heff.gw_kept
      intro hm
      obtain ⟨g, hg_mem, hg_eq'⟩ := List.mem_map.1 hm
      rcases hgw_sub g hg_mem with h1 | h2
      · exact hne.1 (hg_eq'.symm.trans h1)
      · exact hne.2 (hg_eq'.symm.trans h2)
    rw [heq]
  -- Prove `MptObjInWith post S Nm' (locN s "m")`:
  have hMptIn_post : MptObjInWith post S Nm' (locN s "m") := by
    refine ⟨hag.allocated hm_al, wordsOK_transfer hAs.1 hAp.1 hm_w, ?_, ?_, hNH_Nm', hRoot_Nm', ?_⟩
    · intro t ht i hi
      rw [hfp_eq t ht] at hi
      exact hm_tab t ht i hi
    · rw [hfix_eq]; exact hm_fix
    · intro o ho
      rcases hExt_Nm' o ho with rfl | ⟨j, hj, hin_j⟩ | hin_fr
      · exact ⟨Or.inl rfl, fun _ _ _ _ => Or.inl rfl, fun _ _ => Or.inl rfl⟩
      · refine ⟨disj_inside_left hin_j (hm_ext j hj).1, ?_, ?_⟩
        · intro t ht i hi
          rw [hfp_eq t ht] at hi
          exact disj_inside_left hin_j ((hm_ext j hj).2.1 t ht i hi)
        · rw [hfix_eq]
          intro f hf
          exact disj_inside_left hin_j ((hm_ext j hj).2.2 f hf)
      · refine ⟨disj_fresh_heap_allocated hAs.2 hAp.2 hin_fr (Or.inr hm_al), ?_, ?_⟩
        · intro t ht i hi
          rw [hfp_eq t ht] at hi
          exact disj_fresh_heap_allocated hAs.2 hAp.2 hin_fr (Or.inr (((hT.2.1 t ht).2 i hi).1))
        · rw [hfix_eq]
          intro f hf
          exact disj_fresh_heap_allocated hAs.2 hAp.2 hin_fr
            ((hF.1 f hf).elim Or.inl (fun h => Or.inr h.1))
  -- Prove `IvlsDisj ((locN s "m", 16) :: nodeExtents post Nm') (nodeExtents post Nd)`:
  have hDisjPost : IvlsDisj ((locN s "m", 16) :: nodeExtents post Nm') (nodeExtents post Nd) := by
    rw [hne_eq]
    intro o ho p hp
    have hp_al : p.2 = 0 ∨ Allocated s p := by
      unfold nodeExtents at hp
      obtain ⟨n, hn, hnp⟩ := List.mem_flatMap.1 hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hnp
      rcases hnp with rfl | rfl
      · exact Or.inr (hTr.1.1 n hn).2.1
      · unfold nodePath
        split
        · rename_i hcond
          rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hcond.1 with h0 | ⟨_, hal, _⟩
          · exact absurd h0 hcond.2
          · exact Or.inr hal
        · exact Or.inl rfl
    rcases List.mem_cons.1 ho with rfl | ho_ne
    · exact hDisjObj_Nd (locN s "m", 16) List.mem_cons_self p hp
    · rcases hExt_Nm' o ho_ne with rfl | ⟨j, hj, hin_j⟩ | hin_fr
      · exact Or.inl rfl
      · exact disj_inside_left hin_j (hDisjObj_Nd j (List.mem_cons_of_mem _ hj) p hp)
      · exact disj_fresh_heap_allocated hAs.2 hAp.2 hin_fr hp_al
  -- Prove `OwnedGrows`:
  have hOG_all : OwnedGrows s post
      (worldOwned s S Nd ++ mptObjIvls s Nm (locN s "m"))
      (worldOwned post S Nd ++ mptObjIvls post Nm' (locN s "m")) := by
    intro o ho
    rcases List.mem_append.1 ho with ho_w | ho_m
    · rcases hOG_world o ho_w with rfl | ⟨j, hj, hin⟩ | hfr
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨j, List.mem_append_left _ hj, hin⟩)
      · exact Or.inr (Or.inr hfr)
    · rcases List.mem_cons.1 ho_m with rfl | ho_ne
      · exact Or.inr (Or.inl ⟨(locN s "m", 16), List.mem_append_right _ List.mem_cons_self,
          Nat.le_refl _, Nat.le_refl _⟩)
      · rcases hExt_Nm' o ho_ne with rfl | ⟨j, hj, hin_j⟩ | hfr
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨j, List.mem_append_right _ (List.mem_cons_of_mem _ hj), hin_j⟩)
        · exact Or.inr (Or.inr hfr)
  -- Prove `FrameOutside`:
  refine ⟨S, Nd, Nm', fun _ ht => ht, hWT_post, hMptIn_post, hDisjPost, hOG_all, ?_⟩
  intro a hkeep hfresh
  by_contra hne
  rcases hcell a hne with ⟨ivl, hivl, _, hhit⟩ | ⟨gs, hgs, _, hhit⟩ | ⟨o, ho, _, hhit⟩ | ⟨_, hfg⟩ | ⟨_, hhf⟩
  · exact hkeep ivl (List.mem_append_left _ (List.mem_append_right _ hivl)) hhit
  · have hfo_gs := bufferRegion_in_fixedObjects s gs (hB_ok gs hgs).1
    have hwo_gs : bufferRegion s gs ∈ worldOwned s S Nd := by
      unfold worldOwned; exact List.mem_append_left _ (List.mem_append_right _ hfo_gs)
    exact hkeep _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hwo_gs))) hhit
  · exact hkeep o (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ho))) hhit
  · exact hkeep (freeGap s) (List.mem_append_right _ List.mem_cons_self) hfg
  · exact hfresh hhf

end InitECandidate.Solver.Wave8GuestInv.R13MptKeepsTwin
