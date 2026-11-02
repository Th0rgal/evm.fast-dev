import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1World
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

theorem freeChain_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k nodes : Nat) :
    ∀ (Fr : List Nat) (head : Nat),
      FreeChain { s with locals := locals, clock := k } nodes head Fr ↔ FreeChain s nodes head Fr
  | [], _ => Iff.rfl
  | f :: rest, head => by
    simp only [FreeChain]
    exact and_congr Iff.rfl (freeChain_with_locals s locals k nodes rest _)

theorem htabWF_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k t : Nat) :
    HtabWF { s with locals := locals, clock := k } t ↔ HtabWF s t := by
  simp only [HtabWF, freeChain_with_locals]
  exact Iff.rfl

theorem tablesTyped_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S : List Nat) :
    TablesTyped { s with locals := locals, clock := k } S ↔ TablesTyped s S := by
  simp only [TablesTyped, htabWF_with_locals]
  exact Iff.rfl

theorem worldTyped_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S : List Nat) :
    WorldTyped { s with locals := locals, clock := k } S ↔ WorldTyped s S := by
  simp only [WorldTyped, tablesTyped_with_locals]
  exact Iff.rfl

theorem arenaReady_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ArenaReady { s with locals := locals, clock := k } ↔ ArenaReady s :=
  ⟨fun h => ⟨guestInv_congr (s := { s with locals := locals, clock := k }) rfl rfl rfl rfl h.1, h.2⟩,
   fun h => ⟨guestInv_with_locals_clock s locals k h.1, h.2⟩⟩

theorem locN_congr {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (name : String)
    (h : locals.lookup (ofString name) = s.locals.lookup (ofString name)) :
    locN { s with locals := locals, clock := k } name = locN s name := by
  simp only [locN, h]

theorem worldOK_of_parts {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd) : WorldOK s :=
  ⟨hA, S, hW.1, hW.2.1, hW.2.2.1, Nd, hW.2.2.2⟩

theorem txEnv_of_ready {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxReadyStrong s) : TxEnv s :=
  ⟨h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.1.2.2.2.2, h.2.2.1⟩

theorem txEnv_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hidx : locals.lookup (ofString "index") = s.locals.lookup (ofString "index"))
    (h : TxEnv s) : TxEnv { s with locals := locals, clock := k } := by
  have hi := locN_congr s locals k "index" hidx
  exact ⟨h.bo_nz, h.bo24, h.bo32, h.bo40, h.bo72, by rw [hi]; exact h.idx_lt, h.jcap_nz⟩

theorem worldTypedWith_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nd : List Nat) :
    WorldTypedWith { s with locals := locals, clock := k } S Nd ↔ WorldTypedWith s S Nd := by
  simp only [WorldTypedWith, tablesTyped_with_locals]
  exact Iff.rfl


/-- Empty intervals in the R10 world footprint cannot straddle an aligned cell. -/
theorem worldOwned_zero_aligned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd) :
    ∀ i ∈ worldOwned s S Nd, i.2 = 0 → i.1 % 8 = 0 := by
  intro i hi hz
  unfold worldOwned at hi
  rcases List.mem_append.mp hi with hi | hi
  · rcases List.mem_append.mp hi with hi | hi
    · obtain ⟨t, ht, hi⟩ := List.mem_flatMap.mp hi
      exact ((hW.1.2.1 t ht).1.1 i hi).2.1
    · have hbase := normalized_mem_zero hi hz
      simp [hbase]
  · obtain ⟨n, _, hi⟩ := List.mem_flatMap.mp hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · unfold nodeIvl nodeSize at hz
      split_ifs at hz
    · unfold nodePath at hz ⊢
      split_ifs at hz ⊢ with h
      · exact False.elim (h.2 hz)
      · rfl

theorem not_cellHits_of_disj {a : Nat} {i j : Ivl}
    (ha8 : a % 8 = 0) (hj0 : j.2 = 0 → j.1 % 8 = 0)
    (ha : i.1 ≤ a ∧ a + 8 ≤ i.1 + i.2) (hd : Disj i j) :
    ¬ CellHits a j := by
  unfold Disj at hd
  unfold CellHits
  rcases hd with h | h | h | h
  · omega
  · have hj8 := hj0 h
    omega
  · omega
  · omega

theorem heap_ivl_survives_step {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {old new R : List Ivl}
    (hold0 : ∀ j ∈ old, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post old new)
    (hfr : FrameOutside s post (old ++ R ++ [freeGap s]) (heapFree s))
    {b : Ivl} (hb1 : b.1 % 8 = 0) (hb2 : b.2 % 8 = 0)
    (hb_in : Inside b sourceBase (globN s "heap_ptr"))
    (hb_old : ∀ j ∈ old, Disj b j)
    (hb_R : ∀ j ∈ R, Disj b j) :
    Inside b sourceBase (globN post "heap_ptr") ∧
    (∀ o ∈ new, Disj b o) ∧
    IvlUnhit s post b := by
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs
  refine ⟨⟨hb_in.1, Nat.le_trans hb_in.2 hhp⟩, ?_, ?_⟩
  · intro o ho
    rcases hog o ho with rfl | ⟨j, hj, hin⟩ | hfresh
    · exact disj_zero_right b
    · exact disj_of_inside_right hin (hb_old j hj)
    · exact Or.inr (Or.inr (Or.inl (Nat.le_trans hb_in.2 hfresh.1)))
  · intro a ha8 hhit
    obtain ⟨hc1, hc2⟩ := hhit
    have ha_in : b.1 ≤ a.toNat ∧ a.toNat + 8 ≤ b.1 + b.2 := by omega
    apply hfr a
    · intro j hj hcj
      obtain ⟨hj1, hj2⟩ := hcj
      rcases List.mem_append.1 hj with hj12 | hfg
      · rcases List.mem_append.1 hj12 with hj_old | hj_R
        · exact not_cellHits_of_disj ha8 (hold0 j hj_old) ha_in (hb_old j hj_old) ⟨hj1, hj2⟩
        · exact not_cellHits_of_disj ha8 (hR0 j hj_R) ha_in (hb_R j hj_R) ⟨hj1, hj2⟩
      · simp only [List.mem_singleton] at hfg; subst hfg
        unfold freeGap at hj1 hj2
        unfold Inside at hb_in
        dsimp at hj1 hj2
        omega
    · intro hcf
      obtain ⟨hf1, hf2⟩ := hcf
      unfold heapFree at hf1 hf2
      unfold Inside at hb_in
      dsimp at hf1 hf2
      omega

theorem txEnv_preserved_by_worldStep {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)} {boKeep : List Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hstep : WorldStep R gw keep Q s r post)
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hjcap_gw : ofString "journal_cap" ∉ gw.map ofString)
    (hbo_keep : ("bo", boKeep) ∈ keep)
    (hoffs : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat), k ∈ boKeep)
    (hR_bo : ∀ i ∈ R s, Disj i (globN s "bo", 88))
    (hbo8 : globN s "bo" % 8 = 0)
    (hR_zero : ∀ i ∈ R s, i.2 = 0 → i.1 % 8 = 0)
    (henv : TxEnv s)
    {locals : HolFiniteMapExact MlS (ValueHOL 64)}
    (hidx : locals.lookup (ofString "index") = s.locals.lookup (ofString "index")) :
    TxEnv { post with locals := locals } := by
  obtain ⟨_, _, hg_kept, hrec_kept, _⟩ := hstep
  have hbo_eq : globN post "bo" = globN s "bo" := globN_eq_of_lookup (hg_kept (ofString "bo") hbo_gw)
  have hjcap_eq : globN post "journal_cap" = globN s "journal_cap" :=
    globN_eq_of_lookup (hg_kept (ofString "journal_cap") hjcap_gw)
  have hkw : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := by
    intro k hk
    apply hrec_kept ("bo", boKeep) hbo_keep henv.bo_nz k (hoffs k hk)
    intro i hi hch
    dsimp only at hch
    have hk_in : k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    have hbase : (globN s "bo" + k) % 8 = (globN s "bo") % 8 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    rcases hR_bo i hi with hz | hz | hd | hd
    · have hnorm := hR_zero i hi hz
      unfold CellHits at hch
      dsimp only at *
      omega
    · simp at hz
    · unfold CellHits at hch; dsimp only at hd; omega
    · unfold CellHits at hch; dsimp only at hd; omega
  have hi := locN_congr s locals post.clock "index" hidx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show globN post "bo" ≠ 0; rw [hbo_eq]; exact henv.bo_nz
  · show memW post (globN post "bo" + 24) ≠ 0
    rw [hbo_eq, hkw 24 (by simp)]; exact henv.bo24
  · show memW post (globN post "bo" + 32) ≠ 0
    rw [hbo_eq, hkw 32 (by simp)]; exact henv.bo32
  · show memW post (globN post "bo" + 40) ≠ 0
    rw [hbo_eq, hkw 40 (by simp)]; exact henv.bo40
  · show memW post (globN post "bo" + 72) ≠ 0
    rw [hbo_eq, hkw 72 (by simp)]; exact henv.bo72
  · show locN { post with locals := locals } "index" < memW post (globN post "bo" + 80)
    change locN { s with locals := locals, clock := post.clock } "index" < _
    rw [hi, hbo_eq, hkw 80 (by simp)]; exact henv.idx_lt
  · show globN post "journal_cap" ≠ 0; rw [hjcap_eq]; exact henv.jcap_nz

theorem txAccessListOK_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) {S Nd : List Nat}
    (htx_lu : locals.lookup (ofString "tx") = s.locals.lookup (ofString "tx"))
    (h : TxAccessListOK s S Nd) :
    TxAccessListOK { s with locals := locals, clock := k } S Nd := by
  have ht := locN_congr s locals k "tx" htx_lu
  unfold TxAccessListOK at h ⊢
  dsimp only at h ⊢
  rw [ht]
  exact h

theorem txAccessListOK_survives_step {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {S Nd S' Nd' : List Nat} {R : List Ivl}
    (hW : WorldTypedWith s S Nd)
    (hR0 : ∀ i ∈ R, i.2 = 0 → i.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd'))
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (htx : TxAccessListOK s S Nd)
    (htx_R : ∀ r ∈ R, Disj (locN s "tx", 384) r)
    (hrecs_R : memW s (locN s "tx") ≠ 0 → 0 < memW s (locN s "tx" + 216) →
      ∀ r ∈ R, Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) r)
    {locals : HolFiniteMapExact MlS (ValueHOL 64)}
    (htx_lu : locals.lookup (ofString "tx") = s.locals.lookup (ofString "tx")) :
    TxAccessListOK { post with locals := locals } S' Nd' := by
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  obtain ⟨htx8, htx_in, htx_ow, hrest⟩ := htx
  have htx_hi : locN s "tx" + 384 ≤ 2 ^ 64 := by
    have := (ivl_allocated_bound hAs (Or.inl htx_in)).2; dsimp at this; omega
  obtain ⟨htx_in', htx_ow', htx_u⟩ :=
    heap_ivl_survives_step hAs hhp (worldOwned_zero_aligned hW) hR0 hog hfr htx8 (by omega) htx_in htx_ow htx_R
  have hm0 : memW post (locN s "tx") = memW s (locN s "tx") :=
    memW_eq_of_ivlUnhit htx_u htx8 htx_hi ⟨le_rfl, by omega⟩
  have hm208 : memW post (locN s "tx" + 208) = memW s (locN s "tx" + 208) :=
    memW_eq_of_ivlUnhit htx_u (by omega) htx_hi ⟨by omega, by omega⟩
  have hm216 : memW post (locN s "tx" + 216) = memW s (locN s "tx" + 216) :=
    memW_eq_of_ivlUnhit htx_u (by omega) htx_hi ⟨by omega, by omega⟩
  have ht_loc : locN { post with locals := locals } "tx" = locN s "tx" :=
    locN_congr s locals post.clock "tx" htx_lu
  unfold TxAccessListOK
  dsimp only
  rw [ht_loc]
  change (locN s "tx") % 8 = 0 ∧
    Inside (locN s "tx", 384) sourceBase (globN post "heap_ptr") ∧
    (∀ o ∈ worldOwned post S' Nd', Disj (locN s "tx", 384) o) ∧
    (memW post (locN s "tx") ≠ 0 →
      memW post (locN s "tx" + 216) < 2 ^ 32 ∧
      (0 < memW post (locN s "tx" + 216) →
        (memW post (locN s "tx" + 208)) % 8 = 0 ∧
        Inside (memW post (locN s "tx" + 208), 24 * memW post (locN s "tx" + 216)) sourceBase (globN post "heap_ptr") ∧
        ∀ o ∈ worldOwned post S' Nd', Disj (memW post (locN s "tx" + 208), 24 * memW post (locN s "tx" + 216)) o) ∧
      ((List.range (memW post (locN s "tx" + 216))).map
        (fun i => memW post (memW post (locN s "tx" + 208) + 24 * i + 16))).sum < 2 ^ 32)
  rw [hm0, hm208, hm216]
  refine ⟨htx8, htx_in', htx_ow', fun hnz => ?_⟩
  obtain ⟨hnal, hrecs_fn, hsum⟩ := hrest hnz
  refine ⟨hnal, fun hpos => ?_, ?_⟩
  · obtain ⟨hr8, hr_in, hr_ow⟩ := hrecs_fn hpos
    obtain ⟨hr_in', hr_ow', _⟩ :=
      heap_ivl_survives_step hAs hhp (worldOwned_zero_aligned hW) hR0 hog hfr hr8 (by omega) hr_in hr_ow (hrecs_R hnz hpos)
    exact ⟨hr8, hr_in', hr_ow'⟩
  · by_cases hpos : 0 < memW s (locN s "tx" + 216)
    · obtain ⟨hr8, hr_in, hr_ow⟩ := hrecs_fn hpos
      have hr_hi := (ivl_allocated_bound hAs (Or.inl hr_in)).2
      obtain ⟨_, _, hr_u⟩ :=
        heap_ivl_survives_step hAs hhp (worldOwned_zero_aligned hW) hR0 hog hfr hr8 (by omega) hr_in hr_ow (hrecs_R hnz hpos)
      have hmap_eq : (List.range (memW s (locN s "tx" + 216))).map
          (fun i => memW post (memW s (locN s "tx" + 208) + 24 * i + 16)) =
          (List.range (memW s (locN s "tx" + 216))).map
          (fun i => memW s (memW s (locN s "tx" + 208) + 24 * i + 16)) := by
        apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        exact memW_eq_of_ivlUnhit hr_u (by omega) hr_hi ⟨by dsimp; omega, by dsimp; omega⟩
      rw [hmap_eq]; exact hsum
    · have hz : memW s (locN s "tx" + 216) = 0 := by omega
      simp [hz]


theorem worldStep_with_locals {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (h : WorldStep R gw keep Q s r post)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    WorldStep (fun _ => R s) gw keep NoExtra {s with locals := locals, clock := k} r post := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  intro S Nd hW hR
  have hWs := (worldTypedWith_with_locals s locals k S Nd).mp hW
  obtain ⟨S', Nd', hsub, hW', hgrow, hframe, _⟩ := h.2.2.2.2 S Nd hWs hR
  exact ⟨S', Nd', hsub, hW', hgrow, hframe, trivial⟩

theorem txValid_of_header_preserved {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hg : GuestInv s) (hg' : GuestInv post) (h : TxValid s)
    (htx : locN post "tx" = locN s "tx")
    (hm : ∀ k, k < 48 → memW post (locN s "tx" + 8 * k) = memW s (locN s "tx" + 8 * k)) :
    TxValid post := by
  unfold TxValid at h ⊢
  dsimp only at h ⊢
  rw [htx]
  obtain ⟨hw, htype, h200, h264, h280, hin⟩ := h
  have hm0 := hm 0 (by omega)
  have hm24 := hm 24 (by omega)
  have hm25 := hm 25 (by omega)
  have hm33 := hm 33 (by omega)
  have hm35 := hm 35 (by omega)
  norm_num only at hm0 hm24 hm25 hm33 hm35
  simp only [Nat.add_zero] at hm0
  rw [hm0, hm24, hm25, hm33, hm35]
  exact ⟨wordsOK_transfer hg hg' hw, htype, h200, h264, h280, hin⟩

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
