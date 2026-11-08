import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2Strong

/-!
# `htab_new` exit transports (phase-2 `aa` region, spine 77..85)

The five helpers `phase2_htab_new_txEnv`, `phase2_htab_new_txBacking`,
`phase2_htab_new_live_buffer`, `phase2_htab_new_world_disj` and
`phase2_p4Shapes_htab_new_aa` consumed by `PtxPhase2StrongTail.lean`
(both the store-ready region and its second copy further down that file).

The `htab_new` exit frame is *fine*: it writes only inside the scratch gap
(the sole keep entry) and the fresh heap gap, so every old-heap cell is
preserved verbatim.  All transports are derived from
`R16Shards.GbodyC17ToC21Common.worldTypedWith_congr_bo` (the old world
survives with `worldOwned` unchanged) and the frame lemmas of the same
module; no alignment of list headers is ever required.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.PanTerminatingBounded InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.Wave8GuestInv

/-- Every world-owned interval is unhit between `s` and `post` under the fine
`htab_new` exit frame. -/
private theorem unhit_worldOwned_of_htab_new {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hA_s : ArenaReady s) (hAp : ArenaReady post) (hag : AllocatorGrows s post)
    (hw : WorldTypedWith s S Nd)
    (hfr : FrameOutside s post
      [(globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr")]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    ∀ j ∈ worldOwned s S Nd, R16Shards.GbodyC17ToC21Common.IvlUnhit s post j := by
  intro j hj
  exact R16Shards.GbodyC17ToC21Common.ivl_unhit_free_of_zero_or_allocated hA_s.2 hAp.2 hag hfr
    (fun k hk => List.mem_singleton.1 hk) rfl
    (R16Shards.GbodyC17ToC21Common.worldOwned_zero_or_allocated hw j hj)

/-- A cell of an allocated interval is preserved by the fine `htab_new` frame;
no alignment requirement on the cell. -/
private theorem memW_eq_of_htab_new_ivl {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hA_s : ArenaReady s) (hAp : ArenaReady post) (hag : AllocatorGrows s post)
    (hfr : FrameOutside s post
      [(globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr")]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    {i : Ivl} (hal : Allocated s i) {a : Nat}
    (hlo : i.1 ≤ a) (hhi : a + 8 ≤ i.1 + i.2) : memW post a = memW s a := by
  obtain ⟨hs_lo, hs_hp, hs_fm, hs_sc, hs_end, hs_hp8, hs_fm8, hs_sc8, _⟩ := hA_s.2
  obtain ⟨hp_lo, hp_hp, hp_fm, hp_sc, hp_end, hp_hp8, hp_fm8, hp_sc8, _⟩ := hAp.2
  have hg_hp := hag.1; have hg_sc := hag.2
  have harena : heapLimit ≤ scratchStart := by decide
  have ha_lt : a < 2 ^ 64 := by
    have hi_end : i.1 + i.2 < 2 ^ 64 := by
      rcases hal with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact Nat.lt_of_le_of_lt (Nat.le_trans h2 hs_hp) (by decide)
      · exact Nat.lt_of_le_of_lt h2 (by decide)
    omega
  have hm := hfr (BitVec.ofNat 64 a)
    (fun j hj hcj => by
      simp only [List.mem_singleton] at hj; subst hj
      obtain ⟨h1, h2⟩ := hcj
      dsimp at h1
      dsimp at h2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h2
      rcases hal with ⟨hheap, hheap2⟩ | ⟨hsc, hsc2⟩
      · omega
      · omega)
    (fun hcf => by
      obtain ⟨h1, h2⟩ := hcf
      dsimp at h1
      dsimp at h2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h2
      rcases hal with ⟨hheap, hheap2⟩ | ⟨hsc, hsc2⟩
      · omega
      · omega)
  unfold memW
  rw [hm]

/-- The block-output record words preserved by the fine `htab_new` frame. -/
private theorem htab_new_bo_facts {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S0 Nd0 : List Nat}
    (hA_s : ArenaReady s) (hAp : ArenaReady post) (hw0 : WorldTypedWith s S0 Nd0)
    (hbo_nz : globN s "bo" ≠ 0) (hag : AllocatorGrows s post)
    (hgs : R16Shards.GbodyC17ToC21Common.WorldGlobalsSame s post)
    (hfr : FrameOutside s post
      [(globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr")]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    globN post "bo" = globN s "bo" ∧
    (∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      memW post (globN post "bo" + k) = memW s (globN s "bo" + k)) := by
  have hunhit_owned : ∀ j ∈ worldOwned s S0 Nd0, R16Shards.GbodyC17ToC21Common.IvlUnhit s post j :=
    fun j hj =>
      R16Shards.GbodyC17ToC21Common.ivl_unhit_free_of_zero_or_allocated hA_s.2 hAp.2 hag hfr
        (fun k hk => List.mem_singleton.1 hk) rfl
        (R16Shards.GbodyC17ToC21Common.worldOwned_zero_or_allocated hw0 j hj)
  have hunhit : ∀ i ∈ worldTypedIvls s S0 Nd0, R16Shards.GbodyC17ToC21Common.IvlUnhit s post i :=
    fun i hi =>
      hunhit_owned i (R16Shards.GbodyC17ToC21Common.worldTypedIvls_sub_worldOwned s S0 Nd0 i hi)
  have hbo_u : globN s "bo" ≠ 0 → R16Shards.GbodyC17ToC21Common.IvlUnhit s post (globN s "bo", 88) :=
    fun hnz =>
      hunhit _ (by
        unfold worldTypedIvls
        apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
        apply List.mem_append.2; left; apply List.mem_append.2; right
        exact List.mem_map.2 ⟨("bo", 88), by simp [typedRecords], by simp [hnz]⟩)
  have hbo_g : globN post "bo" = globN s "bo" := hgs.1 ("bo", 88) (by simp [globalBuffers])
  refine ⟨hbo_g, ?_⟩
  intro k hk
  have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
  exact R16Shards.GbodyC17ToC21Common.rec_word_eq_of_unhit hA_s.2 hw0.2.2.1 "bo" 88
    (by simp [typedRecords]) hbo_g hbo_nz (hbo_u hbo_nz) hk_in.1 hk_in.2

/-- Core world-disjointness transport: any interval `b` inside the old heap
that was disjoint from the old world stays disjoint from the extended world
after `htab_new`. -/
private theorem phase2_htab_new_ivl_disj {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {t : Nat}
    (hA_s : ArenaReady s) (hw : WorldTypedWith s S Nd) (hAp : ArenaReady post)
    (hag : AllocatorGrows s post)
    (hfp_t : ∀ i ∈ htabFootprint post t, Allocated post i ∧
      (Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∨
        Inside i (globN post "scratch_ptr") (globN s "scratch_ptr")))
    (hfr : FrameOutside s post
      [(globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr")]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hbe : post.be = s.be) (hgs : R16Shards.GbodyC17ToC21Common.WorldGlobalsSame s post)
    {b : Ivl} (hbin : Inside b InitE.sourceBase (globN s "heap_ptr"))
    (hsep : ∀ j ∈ worldOwned s S Nd, Disj b j)
    {j : Ivl} (hj : j ∈ worldOwned post (S ++ [t]) Nd) :
    Disj b j := by
  have hsb : 24 < InitE.sourceBase := by decide
  have hsb264 : InitE.sourceBase < 2 ^ 64 := by decide
  have harena : heapLimit ≤ scratchStart := by decide
  obtain ⟨hs_lo, hs_hp, hs_fm, hs_sc, hs_end, hs_hp8, hs_fm8, hs_sc8, _⟩ := hA_s.2
  obtain ⟨hp_lo, hp_hp, hp_fm, hp_sc, hp_end, hp_hp8, hp_fm8, hp_sc8, _⟩ := hAp.2
  have hg_hp := hag.1; have hg_sc := hag.2
  have hm_low : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    have hlow : ∀ a : Nat, a + 8 ≤ InitE.sourceBase → memW post a = memW s a := fun a ha => by
      have ha_lt : a < 2 ^ 64 := by omega
      have hm := hfr (BitVec.ofNat 64 a)
        (fun j hj hcj => by
          simp only [List.mem_singleton] at hj; subst hj
          obtain ⟨h1, _⟩ := hcj
          dsimp at h1
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          omega)
        (fun hcf => by
          obtain ⟨h1, _⟩ := hcf
          dsimp at h1
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          omega)
      unfold memW; rw [hm]
    exact ⟨hlow 8 (by omega), hlow 16 (by omega)⟩
  have hunhit_owned : ∀ j ∈ worldOwned s S Nd, R16Shards.GbodyC17ToC21Common.IvlUnhit s post j :=
    fun j hj =>
      R16Shards.GbodyC17ToC21Common.ivl_unhit_free_of_zero_or_allocated hA_s.2 hAp.2 hag hfr
        (fun k hk => List.mem_singleton.1 hk) rfl
        (R16Shards.GbodyC17ToC21Common.worldOwned_zero_or_allocated hw j hj)
  have hunhit : ∀ i ∈ worldTypedIvls s S Nd, R16Shards.GbodyC17ToC21Common.IvlUnhit s post i :=
    fun i hi =>
      hunhit_owned i (R16Shards.GbodyC17ToC21Common.worldTypedIvls_sub_worldOwned s S Nd i hi)
  have hbo_u : globN s "bo" ≠ 0 → R16Shards.GbodyC17ToC21Common.IvlUnhit s post (globN s "bo", 88) :=
    fun hnz =>
      hunhit _ (by
        unfold worldTypedIvls
        apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
        apply List.mem_append.2; left; apply List.mem_append.2; right
        exact List.mem_map.2 ⟨("bo", 88), by simp [typedRecords], by simp [hnz]⟩)
  have hbase := R16Shards.GbodyC17ToC21Common.worldTypedWith_congr_bo hA_s hAp hbe hag hgs hw
    (fun u hu i hi => hunhit i (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; left
      exact List.mem_flatMap.2 ⟨u, hu, hi⟩))
    (fun hnz => hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("ws", 40), by simp [typedRecords], by simp [hnz]⟩))
    (fun hnz => hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("bs", 80), by simp [typedRecords], by simp [hnz]⟩))
    (fun hnz => hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact List.mem_map.2 ⟨("ts", 72), by simp [typedRecords], by simp [hnz]⟩))
    (fun hnz => hunhit _ (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; right; simp [hnz]))
    (fun i hi _ => hunhit i (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
      exact hi))
    (fun i hi => hunhit i (by
      unfold worldTypedIvls
      apply List.mem_append.2; left; apply List.mem_append.2; right
      exact hi))
    (fun o ho => hunhit o (by
      unfold worldTypedIvls
      exact List.mem_append.2 (Or.inr ho)))
    (fun hnz k hk => by
      have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      have hbo_g : globN post "bo" = globN s "bo" := hgs.1 ("bo", 88) (by simp [globalBuffers])
      simpa [hbo_g] using
        R16Shards.GbodyC17ToC21Common.rec_word_eq_of_unhit hA_s.2 hw.2.2.1 "bo" 88
          (by simp [typedRecords]) hbo_g hnz (hbo_u hnz) hk_in.1 hk_in.2)
    hm_low
  obtain ⟨hW_S, howned_S, hwrs_eq, hjr_eq, hhdr_S⟩ := hbase
  unfold worldOwned at hj
  rw [List.flatMap_append] at hj
  rcases List.mem_append.1 hj with hj1 | hjNE
  · rcases List.mem_append.1 hj1 with hjT | hjF
    · rcases List.mem_append.1 hjT with hjS | hjt
      · exact hsep j (by
          have hmem : j ∈ worldOwned post S Nd :=
            List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hjS)))
          rw [howned_S] at hmem
          exact hmem)
      · rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hjt
        obtain ⟨_, hin⟩ := hfp_t j hjt
        rcases hin with hin_hp | hin_sc
        · refine Or.inr (Or.inr (Or.inl ?_))
          obtain ⟨_, hb2⟩ := hbin
          obtain ⟨hj1, _⟩ := hin_hp
          omega
        · refine Or.inr (Or.inr (Or.inl ?_))
          obtain ⟨_, hb2⟩ := hbin
          obtain ⟨hj1, _⟩ := hin_sc
          omega
    · exact hsep j (by
        have hmem : j ∈ worldOwned post S Nd :=
          List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hjF)))
        rw [howned_S] at hmem
        exact hmem)
  · exact hsep j (by
      have hmem : j ∈ worldOwned post S Nd :=
        List.mem_append.2 (Or.inr hjNE)
      rw [howned_S] at hmem
      exact hmem)

/- The five public `htab_new` exit transports that this module
- originally declared are now provided by the patched
- `PtxPhase2Strong` (`phase2_htab_new_txEnv`, `phase2_htab_new_txBacking`,
- `phase2_htab_new_live_buffer`, `phase2_htab_new_world_disj`,
- `phase2_p4Shapes_htab_new_aa`); they are not redeclared here to
- avoid duplicate-declaration errors. The private helpers above remain
- the reference implementation of the frame reasoning. -/

end InitECandidate.Solver.Wave8GuestInv.R13Shards
