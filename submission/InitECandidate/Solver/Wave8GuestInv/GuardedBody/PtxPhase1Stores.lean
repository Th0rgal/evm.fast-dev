import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Geometry
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Semantics
import InitECandidate.Solver.Wave8GuestInv.Expressions
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

theorem txAccessListOK_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (htx_loc : locN post "tx" = locN s "tx")
    {S Nd : List Nat} (how_eq : worldOwned post S Nd = worldOwned s S Nd)
    (htx : TxAccessListOK s S Nd)
    (htx_u : IvlUnhit s post (locN s "tx", 384))
    (hrecs_u : memW s (locN s "tx") ≠ 0 → 0 < memW s (locN s "tx" + 216) →
      IvlUnhit s post (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))) :
    TxAccessListOK post S Nd := by
  obtain ⟨htx8, htx_in, htx_ow, hrest⟩ := htx
  have htx_hi : locN s "tx" + 384 ≤ 2 ^ 64 := by
    have := (ivl_allocated_bound hAs (Or.inl htx_in)).2; dsimp at this; omega
  have hm0 : memW post (locN s "tx") = memW s (locN s "tx") :=
    memW_eq_of_ivlUnhit htx_u htx8 htx_hi ⟨le_rfl, by omega⟩
  have hm208 : memW post (locN s "tx" + 208) = memW s (locN s "tx" + 208) :=
    memW_eq_of_ivlUnhit htx_u (by omega) htx_hi ⟨by omega, by omega⟩
  have hm216 : memW post (locN s "tx" + 216) = memW s (locN s "tx" + 216) :=
    memW_eq_of_ivlUnhit htx_u (by omega) htx_hi ⟨by omega, by omega⟩
  unfold TxAccessListOK
  dsimp only
  rw [htx_loc, how_eq, hm0, hm208, hm216]
  refine ⟨htx8, ⟨htx_in.1, Nat.le_trans htx_in.2 hhp⟩, htx_ow, fun hnz => ?_⟩
  obtain ⟨hnal, hrecs_fn, hsum⟩ := hrest hnz
  refine ⟨hnal, fun hpos => ?_, ?_⟩
  · obtain ⟨hr8, hr_in, hr_ow⟩ := hrecs_fn hpos
    exact ⟨hr8, ⟨hr_in.1, Nat.le_trans hr_in.2 hhp⟩, hr_ow⟩
  · by_cases hpos : 0 < memW s (locN s "tx" + 216)
    · obtain ⟨hr8, hr_in, _⟩ := hrecs_fn hpos
      have hr_hi := (ivl_allocated_bound hAs (Or.inl hr_in)).2
      have hr_u := hrecs_u hnz hpos
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

def encArray {F : Type} (s : PanSemStateFiniteExact 64 F) : Ivl :=
  (memW s (globN s "bo" + 24), 16 * memW s (globN s "bo" + 80) + 16)

theorem encArray_mem_block {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hE : TxEnv s) : encArray s ∈ blockOutObjects s := by
  simp [encArray, blockOutObjects, hE.bo_nz, hE.bo24]

theorem encArray_mem_fixed {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hE : TxEnv s) : encArray s ∈ fixedObjects s :=
  fixed_mem_raw (block_mem_raw (encArray_mem_block hE)) (by simp [encArray])

theorem encArray_words {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hF : FixedTyped s) (hE : TxEnv s) : Allocated s (encArray s) ∧ WordsOK s (encArray s) :=
  (hF.1 _ (encArray_mem_fixed hE)).resolve_left (by simp [encArray])

theorem ivlUnhit_single {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {x : BitVec 64} {i : Ivl}
    (hm : ∀ a, a ≠ x → post.memory a = s.memory a)
    (hi0 : i.2 = 0 → i.1 % 8 = 0) (hd : Disj i (x.toNat, 8)) : IvlUnhit s post i := by
  intro a ha hh
  apply hm
  intro he
  subst a
  exact not_cellHits_of_disj ha hi0 ⟨le_rfl, le_rfl⟩ (disj_symm hd) hh

theorem store_encArray_world {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) (hE : TxEnv s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (encArray s).1 ((encArray s).1 + (encArray s).2))
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    WorldTypedWith {s with memory := mem'} S Nd ∧
    worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd ∧
    TxEnv {s with memory := mem'} := by
  let post : PanSemStateFiniteExact 64 F := {s with memory := mem'}
  have hAp : ArenaReady post := ⟨guestInv_congr (s := s) rfl rfl rfl rfl hA.1, hA.2⟩
  have hb := encArray_mem_block hE
  have hfix := encArray_mem_fixed hE
  have hp := fixed_pairwise_raw hW.2.2.1
  rw [fixedRaw, List.pairwise_append] at hp
  obtain ⟨hp0, _, hbal⟩ := hp
  rw [List.pairwise_append] at hp0
  obtain ⟨_, hblock, hbefore⟩ := hp0
  have before (r : String × Nat) (hr : r ∈ globalBuffers) (hn : globN s r.1 ≠ 0) :
      Disj (globN s r.1, r.2) (encArray s) := by
    apply hbefore _ ?_ _ hb
    apply List.mem_append.mpr; left
    exact List.mem_map.mpr ⟨r, hr, by simp only [hn, if_false]⟩
  have unhit (i : Ivl) (hi : i ∈ worldOwned s S Nd) (hd : Disj i (encArray s)) :
      IvlUnhit s post i :=
    ivlUnhit_single hm (worldOwned_zero_aligned hW i hi) (disj_of_inside_right hin hd)
  have fixedOwned (i : Ivl) (hi : i ∈ fixedObjects s) : i ∈ worldOwned s S Nd :=
    List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hi)))
  have recUnhit (r : String × Nat) (hr : r ∈ typedRecords) (hn : globN s r.1 ≠ 0) :
      IvlUnhit s post (globN s r.1, r.2) := by
    apply unhit
    · apply fixedOwned
      simpa only [hn, if_false] using typedRecord_mem_fixedObjects s hr
    · exact before r (typedRecord_mem_globalBuffers hr) hn
  have hboU := recUnhit ("bo", 88) (by simp [typedRecords]) hE.bo_nz
  have hboW : ∀ k, k % 8 = 0 → k + 8 ≤ 88 →
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := by
    intro k hk hkle
    have hw := bo_words hW.2.2.1 hE.bo_nz
    have hhi := (ivl_allocated_bound hA.2 hw.1).2
    exact memW_eq_of_ivlUnhit hboU (by have := hw.2.1; omega) hhi ⟨by dsimp; omega, by dsimp; omega⟩
  have hm0 : memW post 0 = memW s 0 ∧ memW post 16 = memW s 16 := by
    have hlo : sourceBase ≤ x.toNat := ((ordinaryDomain_iff x).mp (hA.1.memaddrs ▸ hx)).2.1
    have hsb : 16 < sourceBase := by decide
    constructor
    · unfold memW
      rw [show post.memory (BitVec.ofNat 64 0) = s.memory (BitVec.ofNat 64 0) from hm _ (by
        intro he; have := congrArg BitVec.toNat he; norm_num at this; omega)]
    · unfold memW
      rw [show post.memory (BitVec.ofNat 64 16) = s.memory (BitVec.ofNat 64 16) from hm _ (by
        intro he; have := congrArg BitVec.toNat he; norm_num at this; omega)]
  have hw := worldTypedWith_congr_bo hA hAp rfl ⟨le_rfl, le_rfl⟩
    (worldGlobalsSame_of_globals_eq (s := s) (post := post) rfl) hW
    (fun t ht i hi => unhit i
      (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨t, ht, hi⟩)))))
      (((hW.1.2.1 t ht).2 i hi).2 _ hfix))
    (recUnhit ("ws", 40) (by simp [typedRecords]))
    (recUnhit ("bs", 80) (by simp [typedRecords]))
    (recUnhit ("ts", 72) (by simp [typedRecords]))
    (fun hn => by
      apply unhit
      · apply fixedOwned; apply fixed_mem_raw (hn := by dsimp; omega)
        simp only [fixedRaw, List.mem_append]; exact Or.inl (Or.inl (Or.inr (by simp)))
      · exact hbefore _ (List.mem_append.mpr (Or.inr (by simp))) _ hb)
    (fun i hi h24 => by
      apply unhit
      · exact fixedOwned i (fixed_mem_raw (block_mem_raw hi) (by omega))
      · apply pairwise_disj_mem hblock hi hb
        intro he; have := congrArg Prod.snd he
        simp only [encArray] at this; omega)
    (fun i hi => by
      apply ivlUnhit_single hm
      · intro hz
        have hbase := normalized_mem_zero hi hz
        simp [hbase]
      · apply disj_of_inside_right hin
        exact disj_symm (hbal _ (List.mem_append.mpr (Or.inr hb)) i hi))
    (fun i hi => unhit i (List.mem_append.mpr (Or.inr hi)) ((hW.2.2.2.2.1 i hi).2 _ hfix))
    (fun _ k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hboW _ (by omega) (by omega)) hm0
  refine ⟨hw.1, hw.2.1, ?_⟩
  refine ⟨hE.bo_nz, ?_, ?_, ?_, ?_, ?_, hE.jcap_nz⟩
  · change memW post (globN s "bo" + 24) ≠ 0
    rw [hboW 24 (by omega) (by omega)]; exact hE.bo24
  · change memW post (globN s "bo" + 32) ≠ 0
    rw [hboW 32 (by omega) (by omega)]; exact hE.bo32
  · change memW post (globN s "bo" + 40) ≠ 0
    rw [hboW 40 (by omega) (by omega)]; exact hE.bo40
  · change memW post (globN s "bo" + 72) ≠ 0
    rw [hboW 72 (by omega) (by omega)]; exact hE.bo72
  · change locN s "index" < memW post (globN s "bo" + 80)
    rw [hboW 80 (by omega) (by omega)]; exact hE.idx_lt

theorem txReadyStrong_store_encArray {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxReadyStrong s) {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (encArray s).1 ((encArray s).1 + (encArray s).2))
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    TxReadyStrong {s with memory := mem'} := by
  let post : PanSemStateFiniteExact 64 F := {s with memory := mem'}
  have hA := h.1.1.1
  obtain ⟨S, Nd, hW, hT⟩ := h.2.2.2.2.2
  obtain ⟨hW', how, hE'⟩ := store_encArray_world hA (txEnv_of_ready h) hW hx hin hm
  have hAp : ArenaReady post := ⟨guestInv_congr (s := s) rfl rfl rfl rfl hA.1, hA.2⟩
  have harr : encArray s ∈ worldOwned s S Nd :=
    List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (encArray_mem_fixed (txEnv_of_ready h)))))
  have hu : IvlUnhit s post (locN s "tx", 384) :=
    ivlUnhit_single hm (by simp) (disj_of_inside_right hin (hT.2.2.1 _ harr))
  have hur : memW s (locN s "tx") ≠ 0 → 0 < memW s (locN s "tx" + 216) →
      IvlUnhit s post (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) := by
    intro ht hn
    have hr := (hT.2.2.2 ht).2.1 hn
    exact ivlUnhit_single hm (by dsimp; omega) (disj_of_inside_right hin (hr.2.2 _ harr))
  have hT' := txAccessListOK_congr_unhit hA.2 (post := post) le_rfl rfl how hT hu hur
  have hV' : TxValid post := by
    apply txValid_of_header_preserved hA.1 hAp.1 h.2.1 rfl
    intro k hk
    have hhi := (ivl_allocated_bound hA.2 (Or.inl hT.2.1)).2
    exact memW_eq_of_ivlUnhit hu (by have := hT.1; omega) hhi
      ⟨by dsimp; omega, by dsimp; omega⟩
  exact txReadyStrong_of_parts hAp hE' hV' hW' hT'

theorem txReadyStrong_assign_bal_index {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxReadyStrong s) (v : ValueHOL 64) :
    TxReadyStrong (setKvarHOLFinite .global (ofString "bal_index") v s) := by
  let post := setKvarHOLFinite .global (ofString "bal_index") v s
  obtain ⟨S, Nd, hW, hT⟩ := h.2.2.2.2.2
  obtain ⟨hA', hW', how, _, _, hhp, _, hbo, hm⟩ := worldTypedWith_assign_bal_index h.1.1.1 (v := v) hW
  have hT' : TxAccessListOK post S Nd := by
    unfold TxAccessListOK
    change (locN s "tx") % 8 = 0 ∧
      Inside (locN s "tx", 384) sourceBase (globN post "heap_ptr") ∧
      (∀ o ∈ worldOwned post S Nd, Disj (locN s "tx", 384) o) ∧ _
    rw [hhp, how]
    exact hT
  have hE := txEnv_of_ready h
  have hE' : TxEnv post := by
    have hj : globN post "journal_cap" = globN s "journal_cap" := by
      simp [post, globN, setKvarHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "bal_index" ≠ ofString "journal_cap" from by decide]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hbo]; exact hE.bo_nz
    · rw [hbo]; exact hE.bo24
    · rw [hbo]; exact hE.bo32
    · rw [hbo]; exact hE.bo40
    · rw [hbo]; exact hE.bo72
    · rw [hbo]; exact hE.idx_lt
    · rw [hj]; exact hE.jcap_nz
  exact txReadyStrong_of_parts hA' hE' h.2.1 hW' hT'

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
