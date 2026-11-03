import InitECandidate.Solver.Wave8GuestInv.MemoryViews
import InitECandidate.Solver.GuestTrapOutcomes
import Guest.SoftwareAst

/-! R11 EVM-frame preservation lemma for head-frame status/gas updates. -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R11Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

theorem scratchEnd_val : scratchEnd = 2965299200 := rfl
theorem scratchStart_val : scratchStart = 2952790016 := rfl
theorem sourceBase_val : sourceBase = 2701131776 := rfl
theorem heapLimit_val : heapLimit = 2952790016 := rfl
theorem heapEnd_val : heapEnd = 33806089704 := by decide

theorem Disj.symm {i j : Ivl} (h : Disj i j) : Disj j i := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

theorem triesTypedWith_inter {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd1 Nd2 : List Nat}
    (h1 : TriesTypedWith s S Nd1) (h2 : TriesTypedWith s S Nd2) :
    let Nd := Nd1.filter (fun n => decide (n ∈ Nd2))
    TriesTypedWith s S Nd ∧
    (∀ x ∈ nodeExtents s Nd, x ∈ nodeExtents s Nd1 ∧ x ∈ nodeExtents s Nd2) := by
  dsimp only
  set Nd := Nd1.filter (fun n => decide (n ∈ Nd2))
  have hmem_iff : ∀ n, n ∈ Nd ↔ n ∈ Nd1 ∧ n ∈ Nd2 := fun n => by simp [Nd, List.mem_filter]
  have hroot_iff : ∀ v, RootIn Nd1 v → RootIn Nd2 v → RootIn Nd v := by
    intro v r1 r2
    rcases r1 with rfl | hm1
    · exact Or.inl rfl
    · rcases r2 with rfl | hm2
      · exact Or.inl rfl
      · exact Or.inr ((hmem_iff v).2 ⟨hm1, hm2⟩)
  have hne_sub : ∀ x ∈ nodeExtents s Nd, x ∈ nodeExtents s Nd1 ∧ x ∈ nodeExtents s Nd2 := by
    intro x hx
    unfold nodeExtents at hx ⊢
    obtain ⟨n, hn, hnx⟩ := List.mem_flatMap.1 hx
    obtain ⟨hn1, hn2⟩ := (hmem_iff n).1 hn
    exact ⟨List.mem_flatMap.2 ⟨n, hn1, hnx⟩, List.mem_flatMap.2 ⟨n, hn2, hnx⟩⟩
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, hne_sub⟩
  · intro n hn
    obtain ⟨hn1, hn2⟩ := (hmem_iff n).1 hn
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := h1.1.1 n hn1
    obtain ⟨_, _, _, _, d5, d6, _⟩ := h2.1.1 n hn2
    refine ⟨c1, c2, c3, c4, fun hk2 => hroot_iff _ (c5 hk2) (d5 hk2),
      fun hk3 i hi => hroot_iff _ (c6 hk3 i hi) (d6 hk3 i hi), fun h12 => ?_, c8, c9, c10⟩
    rcases c7 h12 with hz | ⟨hnib, hal, hin, hdj⟩
    · exact Or.inl hz
    · exact Or.inr ⟨hnib, hal, hin, fun m hm => hdj m ((hmem_iff m).1 hm).1⟩
  · intro n hn m hm hne
    exact h1.1.2 n ((hmem_iff n).1 hn).1 m ((hmem_iff m).1 hm).1 hne
  · intro o ho
    exact h1.2.1 o (hne_sub o ho).1
  · intro hws
    obtain ⟨r1_24, r1_32⟩ := h1.2.2 hws
    obtain ⟨r2_24, r2_32⟩ := h2.2.2 hws
    exact ⟨hroot_iff _ r1_24 r2_24, fun htS i hi => hroot_iff _ (r1_32 htS i hi) (r2_32 htS i hi)⟩

def headAllowedOffsets (e0 c0 : Nat) : List Nat :=
  [e0 + 64, e0 + 72, e0 + 96, e0 + 104, e0 + 120, e0 + 128, e0 + 160, e0 + 184, e0 + 192, e0 + 200,
   c0 + 32]

def allowedFrameOffs : List Nat :=
  [64, 72, 96, 104, 120, 128, 160, 184, 192, 200]

theorem evmInv_of_head_status_gas_update {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hE : EvmInv s)
    (hGp : GuestInv post)
    (hglob : post.globals = s.globals)
    (hbe : post.be = s.be)
    (hmem_out : ∀ x : BitVec 64,
      (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
      post.memory x = s.memory x)
    (hgas_le : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192)) :
    EvmInv post ∧ evmChain post = evmChain s ∧
    ((evmChain post).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum ≤
      ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum := by
  obtain ⟨hAR, S, hWT, hrest⟩ := hE
  dsimp only at hrest
  obtain ⟨hch_ne, hch_len, hlast, hFWF, hFRoom, hRetW, hPair, hDisj, hTries, hMarks, hRoles, hGasSum⟩ := hrest
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  have hec0_mem : (e0, c0) ∈ evmChain s := by simp [evmChain, evmChainFrom, e0, c0]
  have hF0 := hFWF (e0, c0) hec0_mem
  have he0_blk := hF0.1 (e0, 280) (by simp)
  have hc0_blk := hF0.1 (c0, 104) (by simp)
  have he0_in : Inside (e0, 280) (globN s "scratch_ptr") scratchEnd := he0_blk.1
  have hc0_in : Inside (c0, 104) (globN s "scratch_ptr") scratchEnd := hc0_blk.1
  have he0_words : WordsOK s (e0, 280) := he0_blk.2
  have hc0_words : WordsOK s (c0, 104) := hc0_blk.2
  have he0_lt : e0 + 280 < 2 ^ 64 := by have := he0_in.2; rw [scratchEnd_val] at this; omega
  have hc0_lt : c0 + 104 < 2 ^ 64 := by have := hc0_in.2; rw [scratchEnd_val] at this; omega
  have he0_ge32 : 32 ≤ e0 := by
    have h1 := hAR.2.2.2.1; have h2 := hAR.2.2.2.2.1; rw [scratchStart_val] at h1
    have := he0_in.1; omega
  have hc0_ge32 : 32 ≤ c0 := by
    have h1 := hAR.2.2.2.1; have h2 := hAR.2.2.2.2.1; rw [scratchStart_val] at h1
    have := hc0_in.1; omega
  have he0_pos : 0 < e0 := by omega
  have hc0_pos : 0 < c0 := by omega
  have hall_lt : ∀ addr ∈ headAllowedOffsets e0 c0, addr < 2 ^ 64 := by
    intro addr haddr
    simp only [headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
    rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hall_align : ∀ addr ∈ headAllowedOffsets e0 c0, addr % 8 = 0 := by
    intro addr haddr
    have he8 := he0_words.1; have hc8 := hc0_words.1
    simp only [headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
    rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hall_in_ec0 : ∀ addr ∈ headAllowedOffsets e0 c0,
      (e0 ≤ addr ∧ addr + 8 ≤ e0 + 280) ∨ (c0 ≤ addr ∧ addr + 8 ≤ c0 + 104) := by
    intro addr haddr
    simp only [headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
    rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (first | exact Or.inl ⟨by omega, by omega⟩ | exact Or.inr ⟨by omega, by omega⟩)
  have hmemW_ne : ∀ a : Nat, a < 2 ^ 64 →
      (∀ addr ∈ headAllowedOffsets e0 c0, a ≠ addr) → memW post a = memW s a := by
    intro a hlt hne
    unfold memW
    rw [hmem_out (BitVec.ofNat 64 a)]
    intro addr haddr heq
    have := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (hall_lt addr haddr)] at this
    exact hne addr haddr this
  have hmemW_disj : ∀ (o : Ivl), Disj (e0, 280) o → Disj (c0, 104) o →
      ∀ a : Nat, InIvl a o → a < 2 ^ 64 → memW post a = memW s a := by
    intro o hde hdc a ⟨hlo, hhi⟩ halt
    apply hmemW_ne a halt
    intro addr haddr heq
    unfold Disj at hde hdc; dsimp only at hde hdc hlo hhi
    rcases hall_in_ec0 addr haddr with ⟨he1, he2⟩ | ⟨hc1, hc2⟩
    · rcases hde with h | h | h | h <;> omega
    · rcases hdc with h | h | h | h <;> omega
  have hmemB_disj : ∀ (o : Ivl), Disj (e0, 280) o → Disj (c0, 104) o →
      ∀ a : Nat, InIvl a o → a < 2 ^ 64 → memB post a = memB s a := by
    intro o hde hdc a ⟨hlo, hhi⟩ halt
    unfold memB
    have h8 : (panByteAlignHOL (BitVec.ofNat 64 a)).toNat = a / 8 * 8 := by
      have hh : 2 ^ Nat.log2 (64 / 8) = 8 := by decide
      simp only [panByteAlignHOL, hh, BitVec.toNat_ofNat, Nat.mod_eq_of_lt halt]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmem_out (panByteAlignHOL (BitVec.ofNat 64 a)), hbe]
    intro addr haddr heq
    have htonat := congrArg BitVec.toNat heq
    rw [h8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hall_lt addr haddr)] at htonat
    have hal := hall_align addr haddr
    unfold Disj at hde hdc; dsimp only at hde hdc hlo hhi
    rcases hall_in_ec0 addr haddr with ⟨he1, he2⟩ | ⟨hc1, hc2⟩
    · rcases hde with h | h | h | h <;> omega
    · rcases hdc with h | h | h | h <;> omega
  have hdom_eq : post.memaddrs = s.memaddrs := hGp.memaddrs.trans hAR.1.memaddrs.symm
  have hWordAt_eq : ∀ a, WordAt post a ↔ WordAt s a := by
    intro a
    unfold WordAt; rw [hdom_eq]
    constructor
    · rintro ⟨_, hd, _⟩
      cases hm : s.memory (BitVec.ofNat 64 a) with
      | word w => exact ⟨w, hd, rfl⟩
    · rintro ⟨_, hd, _⟩
      cases hm : post.memory (BitVec.ofNat 64 a) with
      | word w => exact ⟨w, hd, rfl⟩
  have hWordsOK_eq : ∀ o, WordsOK post o ↔ WordsOK s o := by
    intro o; unfold WordsOK
    exact and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun k => imp_congr_right fun _ => hWordAt_eq _))
  have hglobN : ∀ g, globN post g = globN s g := fun g => by simp [globN, hglob]
  have hAlloc_eq : ∀ o, Allocated post o ↔ Allocated s o := fun o => by simp [Allocated, hglobN]
  have hAR_post : ArenaReady post := ⟨hGp, arenaOK_congr hglob hAR.2⟩
  have halloc_bound : ∀ o, Allocated s o → o.1 + o.2 < 2 ^ 64 := by
    intro o ho
    rcases ho with ⟨_, h⟩ | ⟨_, h⟩
    · have := hAR.2.2.1; have hhl : heapLimit < 2 ^ 64 := by decide
      omega
    · rw [scratchEnd_val] at h; omega
  have hlow_ne : ∀ a : Nat, a < 32 → ∀ addr ∈ headAllowedOffsets e0 c0, a ≠ addr := by
    intro a ha addr haddr
    rcases hall_in_ec0 addr haddr with ⟨he1, _⟩ | ⟨hc1, _⟩ <;> omega
  have hzero0 : memW post 0 = memW s 0 := hmemW_ne 0 (by decide) (hlow_ne 0 (by omega))
  have hzero8 : memW post 8 = memW s 8 := hmemW_ne 8 (by decide) (hlow_ne 8 (by omega))
  have hzero16 : memW post 16 = memW s 16 := hmemW_ne 16 (by decide) (hlow_ne 16 (by omega))
  have he0_fo : (e0, 280) ∈ frameObjects s (e0, c0) := by simp [frameObjects]
  have hc0_fo : (c0, 104) ∈ frameObjects s (e0, c0) := by simp [frameObjects]
  have hd_tab_e : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (e0, 280) i :=
    (hDisj (e0, c0) hec0_mem (e0, 280) he0_fo).1
  have hd_tab_c : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (c0, 104) i :=
    (hDisj (e0, c0) hec0_mem (c0, 104) hc0_fo).1
  have hd_fix_e : ∀ j ∈ fixedObjects s, Disj (e0, 280) j :=
    (hDisj (e0, c0) hec0_mem (e0, 280) he0_fo).2
  have hd_fix_c : ∀ j ∈ fixedObjects s, Disj (c0, 104) j :=
    (hDisj (e0, c0) hec0_mem (c0, 104) hc0_fo).2
  obtain ⟨hTab, hJrn, hFix, Nd, hTriesW⟩ := hWT
  -- 1. Every table `t ∈ S` keeps `hdr`, `htabFootprint`, `htabValues`, `HtabWF`
  have htab_kept : ∀ t ∈ S,
      (∀ k < 11, hdr post t k = hdr s t k) ∧
      htabFootprint post t = htabFootprint s t ∧
      htabValues post t = htabValues s t ∧
      HtabWF post t := by
    intro t ht
    obtain ⟨hwf, hfp_al⟩ := hTab.2.1 t ht
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, L, I, Fr,
      c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, hfr⟩ := hwf
    have hhdr_in : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
    have ht_lt := halloc_bound _ (hfp_al _ hhdr_in).1
    have hhdr : ∀ k < 11, hdr post t k = hdr s t k := fun k hk =>
      hmemW_disj (t, 88) (hd_tab_e t ht _ hhdr_in) (hd_tab_c t ht _ hhdr_in)
        (t + 8 * k) ⟨by omega, by omega⟩ (by omega)
    have hfp : htabFootprint post t = htabFootprint s t := by
      simp only [htabFootprint, hhdr 1 (by omega), hhdr 4 (by omega), hhdr 5 (by omega),
        hhdr 6 (by omega), hhdr 10 (by omega)]
    have hnd_in : (hdr s t 5, (hdr s t 10 + 1) * 32) ∈ htabFootprint s t := by simp [htabFootprint]
    have hnd_lt := halloc_bound _ (hfp_al _ hnd_in).1
    have hnodeF : ∀ n < hdr s t 10 + 1, ∀ off < 32,
        nodeF post (hdr s t 5) n off = nodeF s (hdr s t 5) n off := fun n hn off hoff =>
      hmemW_disj _ (hd_tab_e t ht _ hnd_in) (hd_tab_c t ht _ hnd_in)
        (hdr s t 5 + 32 * n + off) ⟨by omega, by omega⟩ (by omega)
    have hord_in : (hdr s t 6, (hdr s t 10 + 1) * 8) ∈ htabFootprint s t := by simp [htabFootprint]
    have hord_lt := halloc_bound _ (hfp_al _ hord_in).1
    have hordW : ∀ i < hdr s t 10 + 1, memW post (hdr s t 6 + 8 * i) = memW s (hdr s t 6 + 8 * i) :=
      fun i hi => hmemW_disj _ (hd_tab_e t ht _ hord_in) (hd_tab_c t ht _ hord_in)
        (hdr s t 6 + 8 * i) ⟨by omega, by omega⟩ (by omega)
    have hcnt_le : hdr s t 3 ≤ hdr s t 10 := by
      by_cases hc0' : hdr s t 3 = 0
      · omega
      · have hsub : (L ++ I).toFinset ⊆ Finset.Ico 1 (hdr s t 8) := by
          intro x hx; rw [List.mem_toFinset] at hx; rw [Finset.mem_Ico]
          exact (c11 x).1 (List.mem_append_left _ hx)
        have hcard := Finset.card_le_card hsub
        rw [List.toFinset_card_of_nodup (List.nodup_append.mp c10).1, Nat.card_Ico, List.length_append] at hcard
        rcases c12 with ⟨h0, _⟩ | _ <;> omega
    have hvals : htabValues post t = htabValues s t := by
      unfold htabValues
      rw [hhdr 3 (by omega), hhdr 5 (by omega), hhdr 6 (by omega)]
      apply List.map_congr_left
      intro i hi; rw [List.mem_range] at hi
      rw [hordW i (by omega), (c13 i (by omega)).1]
      have hLmem : L[i]'(by omega) ∈ L ++ I ++ Fr :=
        List.mem_append_left _ (List.mem_append_left _ (List.getElem_mem _))
      have hLlt : L[i]'(by omega) < hdr s t 8 := ((c11 _).1 hLmem).2
      exact hnodeF _ (by omega) 8 (by omega)
    have hfr' : ∀ (Fr' : List Nat) (hd : Nat), (∀ f ∈ Fr', f < hdr s t 10 + 1) →
        FreeChain s (hdr s t 5) hd Fr' → FreeChain post (hdr s t 5) hd Fr' := by
      intro Fr'; induction Fr' with
      | nil => intro _ _ h; exact h
      | cons f rest ih =>
        intro hd hlt ⟨rfl, hr⟩
        refine ⟨rfl, ?_⟩
        rw [hnodeF hd (hlt hd List.mem_cons_self) 0 (by omega)]
        exact ih _ (fun x hx => hlt x (List.mem_cons_of_mem _ hx)) hr
    refine ⟨hhdr, hfp, hvals, ?_⟩
    unfold HtabWF
    rw [hfp, hhdr 0 (by omega), hhdr 1 (by omega), hhdr 3 (by omega), hhdr 5 (by omega),
      hhdr 6 (by omega), hhdr 7 (by omega), hhdr 8 (by omega), hhdr 9 (by omega), hhdr 10 (by omega)]
    refine ⟨fun i hi => ⟨(c1 i hi).1, (hWordsOK_eq i).mpr (c1 i hi).2⟩,
      c2, c3, c4, c5, c6, c7, c8, L, I, Fr, c9, c10, c11, c12, ?_, ?_, c15, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have hLm : L[i] ∈ L ++ I ++ Fr := List.mem_append_left _ (List.mem_append_left _ (List.getElem_mem _))
      have hLl : L[i] < hdr s t 10 + 1 := by have := ((c11 L[i]).1 hLm).2; omega
      rw [hordW i (by omega), hnodeF L[i] hLl 24 (by omega), hnodeF L[i] hLl 16 (by omega)]
      exact c13 i hi
    · intro n hn
      have hnl : n < hdr s t 10 + 1 := by
        have := ((c11 n).1 (List.mem_append_left _ (List.mem_append_right _ hn))).2; omega
      obtain ⟨b1, d1, d2, dne, p1, p2⟩ := c14 n hn
      have hd1l : nodeF s (hdr s t 5) n 8 < hdr s t 10 + 1 := by
        have := ((c11 _).1 (List.mem_append_left _ d1)).2; omega
      have hd2l : nodeF s (hdr s t 5) n 16 < hdr s t 10 + 1 := by
        have := ((c11 _).1 (List.mem_append_left _ d2)).2; omega
      rw [hnodeF n hnl 24 (by omega), hnodeF n hnl 8 (by omega), hnodeF n hnl 16 (by omega),
        hnodeF _ hd1l 0 (by omega), hnodeF _ hd2l 0 (by omega)]
      exact ⟨b1, d1, d2, dne, p1, p2⟩
    · intro hpos
      obtain ⟨r1, r2⟩ := c16 hpos
      have hrl : hdr s t 7 < hdr s t 10 + 1 := by have := ((c11 _).1 (List.mem_append_left _ r1)).2; omega
      rw [hnodeF _ hrl 0 (by omega)]; exact ⟨r1, r2⟩
    · intro n hn
      have hnl : n < hdr s t 10 + 1 := by
        have := ((c11 n).1 (List.mem_append_left _ (List.mem_append_right _ hn))).2; omega
      rw [hnodeF n hnl 8 (by omega), hnodeF n hnl 16 (by omega)]; exact c17 n hn
    · intro n hn hnr
      have hnl : n < hdr s t 10 + 1 := by have := ((c11 n).1 (List.mem_append_left _ hn)).2; omega
      rw [hnodeF n hnl 0 (by omega)]; exact c18 n hn hnr
    · obtain ⟨dep, hdep⟩ := c19
      refine ⟨dep, fun n hn hnr => ?_⟩
      have hnl : n < hdr s t 10 + 1 := by have := ((c11 n).1 (List.mem_append_left _ hn)).2; omega
      have hpm : nodeF s (hdr s t 5) n 0 ∈ I := c18 n hn hnr
      have hpl : nodeF s (hdr s t 5) n 0 < hdr s t 10 + 1 := by
        have := ((c11 _).1 (List.mem_append_left _ (List.mem_append_right _ hpm))).2; omega
      rw [hnodeF n hnl 0 (by omega), hnodeF _ hpl 8 (by omega), hnodeF _ hpl 16 (by omega)]
      exact hdep n hn hnr
    · refine hfr' Fr (hdr s t 9) (fun f hf => ?_) hfr
      have := ((c11 f).1 (List.mem_append_right _ hf)).2; omega
  -- 2. Fixed objects
  have hfixW : ∀ o ∈ fixedObjects s, o.2 ≠ 0 → ∀ a, InIvl a o → memW post a = memW s a := by
    intro o ho hnz a ha
    rcases hFix.1 o ho with hz | ⟨hal, _⟩
    · exact absurd hz hnz
    · have hb := halloc_bound o hal
      have hal_lt : a < 2 ^ 64 := by obtain ⟨_, ha2⟩ := ha; omega
      exact hmemW_disj o (hd_fix_e o ho) (hd_fix_c o ho) a ha hal_lt
  have hrec_fix : ∀ (g : String) (sz : Nat), (g, sz) ∈ globalBuffers → globN s g ≠ 0 →
      (globN s g, sz) ∈ fixedObjects s := by
    intro g sz hgb hnz
    have : (globN s g, if globN s g = 0 then 0 else sz) ∈ fixedObjects s := by
      unfold fixedObjects
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map_of_mem hgb)))
    simpa [hnz] using this
  have hrecW : ∀ (g : String) (sz : Nat), (g, sz) ∈ globalBuffers → 0 < sz → globN s g ≠ 0 →
      ∀ k < sz, memW post (globN s g + k) = memW s (globN s g + k) := by
    intro g sz hgb hsz hnz k hk
    exact hfixW (globN s g, sz) (hrec_fix g sz hgb hnz) (by omega) (globN s g + k) ⟨by omega, by omega⟩
  have hbo_kept : blockOutObjects post = blockOutObjects s ∧
      (globN s "bo" ≠ 0 → ∀ k ∈ [40, 72], memW post (globN s "bo" + k) = memW s (globN s "bo" + k) ∧
        (memW s (globN s "bo" + k) ≠ 0 → LstOK post (memW post (globN s "bo" + k)))) := by
    by_cases hbo0 : globN s "bo" = 0
    · exact ⟨by simp [blockOutObjects, hglobN, hbo0], fun h => absurd hbo0 h⟩
    · have hboW := hrecW "bo" 88 (by decide) (by decide) hbo0
      have hlstHdr : ∀ k ∈ [40, 72], memW s (globN s "bo" + k) ≠ 0 →
          memW post (memW s (globN s "bo" + k)) = memW s (memW s (globN s "bo" + k)) ∧
          memW post (memW s (globN s "bo" + k) + 8) = memW s (memW s (globN s "bo" + k) + 8) ∧
          memW post (memW s (globN s "bo" + k) + 16) = memW s (memW s (globN s "bo" + k) + 16) := by
        intro k hk hkz
        have hl_bo : (memW s (globN s "bo" + k), 24) ∈ blockOutObjects s := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl <;> simp [blockOutObjects, hbo0, hkz]
        have hl_fix : (memW s (globN s "bo" + k), 24) ∈ fixedObjects s :=
          List.mem_append_left _ (List.mem_append_right _ hl_bo)
        exact ⟨hfixW _ hl_fix (by simp) _ ⟨by omega, by omega⟩,
          hfixW _ hl_fix (by simp) _ ⟨by omega, by omega⟩,
          hfixW _ hl_fix (by simp) _ ⟨by omega, by omega⟩⟩
      refine ⟨?_, ?_⟩
      · unfold blockOutObjects
        simp only [hglobN]
        rw [hboW 24 (by omega), hboW 32 (by omega), hboW 56 (by omega), hboW 80 (by omega),
            hboW 40 (by omega), hboW 72 (by omega)]
        by_cases h40z : memW s (globN s "bo" + 40) = 0 <;> by_cases h72z : memW s (globN s "bo" + 72) = 0
        · simp [hbo0, h40z, h72z]
        · obtain ⟨e0_72, _, e16_72⟩ := hlstHdr 72 (by simp) h72z
          simp [hbo0, h40z, h72z, e0_72, e16_72]
        · obtain ⟨e0_40, _, e16_40⟩ := hlstHdr 40 (by simp) h40z
          simp [hbo0, h40z, h72z, e0_40, e16_40]
        · obtain ⟨e0_40, _, e16_40⟩ := hlstHdr 40 (by simp) h40z
          obtain ⟨e0_72, _, e16_72⟩ := hlstHdr 72 (by simp) h72z
          simp [hbo0, h40z, h72z, e0_40, e16_40, e0_72, e16_72]
      · intro _ k hk
        have heqk := hboW k (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> omega)
        refine ⟨heqk, fun hkz => ?_⟩
        rw [heqk]
        obtain ⟨_, e8', e16'⟩ := hlstHdr k hk hkz
        have hLok := hTab.2.2.2.2.2.2.2.2.2.2.1 hbo0 k hk hkz
        unfold LstOK at hLok ⊢
        rw [e8', e16']; exact hLok
  have hbal_rec_eq : balRecords post = balRecords s := by
    unfold balRecords; rw [hglobN]
    by_cases hb0 : globN s "bal_accounts" = 0
    · simp [hb0]
    · simp only [hb0, ↓reduceIte]
      rcases hTab.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hmS
      · exact absurd h0 hb0
      · exact (htab_kept _ hmS).2.2.1
  have hbal_kept : balObjects post = balObjects s ∧
      (∀ ad ∈ balRecords s, memW post ad = memW s ad ∧ memW post (ad + 8) = memW s (ad + 8) ∧
        (∀ k ∈ [16, 24, 32], LstOK post (memW post (ad + k))) ∧
        ∀ l ∈ htabValues post (memW post ad), LstOK post l) := by
    have had_all : ∀ ad ∈ balRecords s,
        memW post ad = memW s ad ∧ memW post (ad + 8) = memW s (ad + 8) ∧
        memW post (ad + 16) = memW s (ad + 16) ∧ memW post (ad + 24) = memW s (ad + 24) ∧
        memW post (ad + 32) = memW s (ad + 32) ∧
        lstObjects post (memW s (ad + 16)) 40 = lstObjects s (memW s (ad + 16)) 40 ∧
        lstObjects post (memW s (ad + 24)) 16 = lstObjects s (memW s (ad + 24)) 16 ∧
        lstObjects post (memW s (ad + 32)) 24 = lstObjects s (memW s (ad + 32)) 24 ∧
        (∀ k ∈ [16, 24, 32], LstOK post (memW s (ad + k))) ∧
        htabValues post (memW s ad) = htabValues s (memW s ad) ∧
        (∀ l ∈ htabValues s (memW s ad), lstObjects post l 40 = lstObjects s l 40 ∧ LstOK post l) := by
      intro ad had
      have had_bal : (ad, 40) ∈ balObjects s :=
        List.mem_flatMap.mpr ⟨ad, had, List.mem_cons_self⟩
      have had_fix : (ad, 40) ∈ fixedObjects s := List.mem_append_right _ had_bal
      have e0' := hfixW _ had_fix (by simp) ad ⟨by omega, by omega⟩
      have e8' := hfixW _ had_fix (by simp) (ad + 8) ⟨by omega, by omega⟩
      have e16' := hfixW _ had_fix (by simp) (ad + 16) ⟨by omega, by omega⟩
      have e24' := hfixW _ had_fix (by simp) (ad + 24) ⟨by omega, by omega⟩
      have e32' := hfixW _ had_fix (by simp) (ad + 32) ⟨by omega, by omega⟩
      have hlstH : ∀ (l esz : Nat), (l = 0 ∨ (l, 24) ∈ balObjects s) → LstOK s l →
          lstObjects post l esz = lstObjects s l esz ∧ LstOK post l := by
        intro l esz hlb hLok
        by_cases hl0 : l = 0
        · subst hl0
          refine ⟨by simp [lstObjects], ?_⟩
          unfold LstOK at hLok ⊢
          simp only [Nat.zero_add] at hLok ⊢
          rw [hzero8, hzero16]; exact hLok
        · rcases hlb with rfl | hl_b
          · contradiction
          · have hl_f : (l, 24) ∈ fixedObjects s := List.mem_append_right _ hl_b
            have el0 := hfixW _ hl_f (by simp) l ⟨by omega, by omega⟩
            have el8 := hfixW _ hl_f (by simp) (l + 8) ⟨by omega, by omega⟩
            have el16 := hfixW _ hl_f (by simp) (l + 16) ⟨by omega, by omega⟩
            refine ⟨by simp [lstObjects, hl0, el0, el16], ?_⟩
            unfold LstOK at hLok ⊢; rw [el8, el16]; exact hLok
      have had_tab := hTab.2.2.2.2.2.2.2.2.2.1 ad had
      have hl16_b : memW s (ad + 16) = 0 ∨ (memW s (ad + 16), 24) ∈ balObjects s := by
        by_cases hz : memW s (ad + 16) = 0
        · exact Or.inl hz
        · exact Or.inr (List.mem_flatMap.mpr ⟨ad, had, List.mem_cons_of_mem _
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (by simp [lstObjects, hz]))))⟩)
      have hl24_b : memW s (ad + 24) = 0 ∨ (memW s (ad + 24), 24) ∈ balObjects s := by
        by_cases hz : memW s (ad + 24) = 0
        · exact Or.inl hz
        · exact Or.inr (List.mem_flatMap.mpr ⟨ad, had, List.mem_cons_of_mem _
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp [lstObjects, hz]))))⟩)
      have hl32_b : memW s (ad + 32) = 0 ∨ (memW s (ad + 32), 24) ∈ balObjects s := by
        by_cases hz : memW s (ad + 32) = 0
        · exact Or.inl hz
        · exact Or.inr (List.mem_flatMap.mpr ⟨ad, had, List.mem_cons_of_mem _
            (List.mem_append_left _ (List.mem_append_right _ (by simp [lstObjects, hz])))⟩)
      obtain ⟨o16, k16⟩ := hlstH _ 40 hl16_b (had_tab.2.2.1 16 (by simp))
      obtain ⟨o24, k24⟩ := hlstH _ 16 hl24_b (had_tab.2.2.1 24 (by simp))
      obtain ⟨o32, k32⟩ := hlstH _ 24 hl32_b (had_tab.2.2.1 32 (by simp))
      have hv := (htab_kept _ had_tab.1).2.2.1
      refine ⟨e0', e8', e16', e24', e32', o16, o24, o32, ?_, hv, ?_⟩
      · intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl
        · exact k16
        · exact k24
        · exact k32
      · intro l hl
        have hl_b : l = 0 ∨ (l, 24) ∈ balObjects s := by
          by_cases hz : l = 0
          · exact Or.inl hz
          · exact Or.inr (List.mem_flatMap.mpr ⟨ad, had, List.mem_cons_of_mem _
              (List.mem_append_right _ (List.mem_flatMap.mpr ⟨l, hl, by simp [lstObjects, hz]⟩))⟩)
        exact hlstH l 40 hl_b (had_tab.2.2.2 l hl)
    refine ⟨?_, ?_⟩
    · unfold balObjects; rw [hbal_rec_eq]
      apply List.flatMap_congr; intro ad had
      obtain ⟨e0', _, e16', e24', e32', o16, o24, o32, _, hv, hlv⟩ := had_all ad had
      rw [e0', e16', e24', e32', o16, o24, o32, hv]
      have htail : (htabValues s (memW s ad)).flatMap (fun l => lstObjects post l 40) =
          (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40) :=
        List.flatMap_congr fun l hl => (hlv l hl).1
      rw [htail]
    · intro ad had
      obtain ⟨e0', e8', e16', e24', e32', _, _, _, hkl, hv, hlv⟩ := had_all ad had
      refine ⟨e0', e8', ?_, ?_⟩
      · intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl
        · rw [e16']; exact hkl 16 (by simp)
        · rw [e24']; exact hkl 24 (by simp)
        · rw [e32']; exact hkl 32 (by simp)
      · rw [e0', hv]; exact fun l hl => (hlv l hl).2
  have hfix_eq : fixedObjects post = fixedObjects s := by
    simp only [fixedObjects, hglobN, hbo_kept.1, hbal_kept.1]
  have hjrn_words : ∀ i < globN s "journal_n", ∀ off ∈ [0, 8, 16, 24],
      memW post (globN s "journal" + 32 * i + off) = memW s (globN s "journal" + 32 * i + off) := by
    intro i hi off hoff
    have hjc_pos : 0 < globN s "journal_cap" := by have := hJrn.1; omega
    have hjc_nz : globN s "journal_cap" ≠ 0 := by omega
    have hj_fix : (globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
      have : (if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
      simpa [hjc_nz] using this
    have hoff_lt : off < 32 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl <;> omega
    exact hfixW _ hj_fix (by omega) _ ⟨by omega, by have := hJrn.1; omega⟩
  have hwroles_eq : worldRoleSlots post = worldRoleSlots s := by
    have hrecR : ∀ (g : String) (sz : Nat) (ks : List (Nat × String)),
        (g, sz) ∈ globalBuffers → 0 < sz → (∀ p ∈ ks, p.1 < sz) →
        recRoles post g ks = recRoles s g ks := by
      intro g sz ks hgb hsz hks
      unfold recRoles; rw [hglobN]
      by_cases hg0 : globN s g = 0
      · simp [hg0]
      · simp only [hg0, ↓reduceIte]
        exact List.map_congr_left fun p hp => by rw [hrecW g sz hgb hsz hg0 p.1 (hks p hp)]
    have hnestR : ∀ (g r : String) (sz : Nat),
        (g, sz) ∈ globalBuffers → 32 < sz →
        (globN s g ≠ 0 → RootIn S (memW s (globN s g + 32))) →
        nestRoles post g r = nestRoles s g r := by
      intro g r sz hgb hsz hroot
      unfold nestRoles; rw [hglobN]
      by_cases hg0 : globN s g = 0
      · simp [hg0]
      · have heq32 := hrecW g sz hgb (by omega) hg0 32 hsz
        simp only [hg0, ↓reduceIte, heq32]
        rcases hroot hg0 with hz | hmS
        · simp [hz]
        · by_cases hz : memW s (globN s g + 32) = 0
          · simp [hz]
          · simp [hz, (htab_kept _ hmS).2.2.1]
    unfold worldRoleSlots
    rw [hrecR "ws" 40 _ (by decide) (by decide) (by decide),
        hrecR "bs" 80 _ (by decide) (by decide) (by decide),
        hrecR "ts" 72 _ (by decide) (by decide) (by decide),
        hnestR "bs" "bs.inner" 80 (by decide) (by decide) (fun hg0 => hTab.2.2.2.2.1 32 (by simp [bsTableSlots]) hg0),
        hnestR "ts" "ts.inner" 72 (by decide) (by decide) (fun hg0 => hTab.2.2.2.2.2.1 32 (by simp [tsTableSlots]) hg0),
        hbal_rec_eq]
    simp only [hglobN]
    have hbf : (balRecords s).flatMap (fun ad => [(memW post ad, "bal.stor"), (memW post (ad + 8), "bal.reads")]) =
        (balRecords s).flatMap (fun ad => [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")]) := by
      apply List.flatMap_congr; intro ad had
      obtain ⟨e0', e8', _, _⟩ := hbal_kept.2 ad had
      rw [e0', e8']
    rw [hbf]
  have hjrole_eq : ∀ t, journalRole post t = journalRole s t := by
    intro t; unfold journalRole; simp only [hglobN]
    by_cases hts0 : globN s "ts" = 0
    · simp [hts0]
    · have htsW := hrecW "ts" 72 (by decide) (by decide) hts0
      rw [htsW 16 (by omega), htsW 32 (by omega), htsW 48 (by omega), htsW 64 (by omega)]
  have hjroles_eq : journalRoleSlots post = journalRoleSlots s := by
    unfold journalRoleSlots; simp only [hglobN]
    apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi
    have e0' := hjrn_words i hi 0 (by simp)
    have e16' := hjrn_words i hi 16 (by simp)
    have e24' := hjrn_words i hi 24 (by simp)
    simp only [Nat.add_zero] at e0'
    rw [e0', e16', e24', hjrole_eq]
  -- 3. Persistent tries (`TriesTypedWith`)
  have htries_preserved : ∀ (Nset : List Nat), TriesTypedWith s S Nset →
      (∀ o ∈ nodeExtents s Nset, Disj (e0, 280) o ∧ Disj (c0, 104) o) →
      TriesTypedWith post S Nset ∧ nodeExtents post Nset = nodeExtents s Nset := by
    intro Nset ⟨hNH, hTd, hTws⟩ hdN
    have hn_ivl_m : ∀ n ∈ Nset, nodeIvl s n ∈ nodeExtents s Nset := fun n hn =>
      List.mem_flatMap.mpr ⟨n, hn, List.mem_cons_self⟩
    have hn_path_m : ∀ n ∈ Nset, nodePath s n ∈ nodeExtents s Nset := fun n hn =>
      List.mem_flatMap.mpr ⟨n, hn, List.mem_cons_of_mem _ List.mem_cons_self⟩
    have hn_sz_ge : ∀ n ∈ Nset, 32 ≤ (nodeIvl s n).2 := by
      intro n _; unfold nodeIvl nodeSize; dsimp only
      by_cases h0 : memW s n = 0
      · simp [h0]
      · by_cases h1 : memW s n = 1
        · simp [h1]
        · by_cases h2 : memW s n = 2 <;> simp [h0, h1, h2]
    have hnW : ∀ n ∈ Nset, ∀ a, InIvl a (nodeIvl s n) → memW post a = memW s a := by
      intro n hn a ha
      have hb := halloc_bound _ (hNH.1 n hn).2.1
      have halt : a < 2 ^ 64 := by obtain ⟨_, ha2⟩ := ha; omega
      obtain ⟨hde, hdc⟩ := hdN _ (hn_ivl_m n hn)
      exact hmemW_disj _ hde hdc a ha halt
    have hn0 : ∀ n ∈ Nset, memW post n = memW s n := fun n hn =>
      hnW n hn n ⟨by simp [nodeIvl], by have := hn_sz_ge n hn; simp [nodeIvl] at this ⊢; omega⟩
    have hn_ivl : ∀ n ∈ Nset, nodeIvl post n = nodeIvl s n := fun n hn => by simp [nodeIvl, hn0 n hn]
    have hn_pw : ∀ n ∈ Nset, (memW s n = 1 ∨ memW s n = 2) →
        memW post (n + 32) = memW s (n + 32) ∧ memW post (n + 40) = memW s (n + 40) := by
      intro n hn hk12
      have hsz : 56 ≤ (nodeIvl s n).2 := by
        rcases hk12 with h | h <;> simp [nodeIvl, nodeSize, h]
      exact ⟨hnW n hn (n + 32) ⟨by simp [nodeIvl], by simp [nodeIvl] at hsz ⊢; omega⟩,
        hnW n hn (n + 40) ⟨by simp [nodeIvl], by simp [nodeIvl] at hsz ⊢; omega⟩⟩
    have hn_path : ∀ n ∈ Nset, nodePath post n = nodePath s n := by
      intro n hn; unfold nodePath; rw [hn0 n hn]
      by_cases hk12 : memW s n = 1 ∨ memW s n = 2
      · obtain ⟨p32, p40⟩ := hn_pw n hn hk12; simp [hk12, p32, p40]
      · simp [hk12]
    have hext : nodeExtents post Nset = nodeExtents s Nset :=
      List.flatMap_congr fun n hn => by rw [hn_ivl n hn, hn_path n hn]
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, hext⟩
    · intro n hn
      have hnd := hNH.1 n hn
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hnd
      rw [hn0 n hn, hn_ivl n hn]
      have hsz32 := hn_sz_ge n hn
      have heq16 : memW post (n + 16) = memW s (n + 16) :=
        hnW n hn (n + 16) ⟨by simp [nodeIvl], by simp [nodeIvl] at hsz32 ⊢; omega⟩
      refine ⟨c1, (hAlloc_eq _).mpr c2, c3, (hWordsOK_eq _).mpr c4, ?_, ?_, ?_,
        by rw [heq16]; exact c8, ?_, ?_⟩
      · intro hk2
        have hsz : (nodeIvl s n).2 = 56 := by simp [nodeIvl, nodeSize, hk2]
        rw [hnW n hn (n + 48) ⟨by simp [nodeIvl], by simp [nodeIvl] at hsz ⊢; omega⟩]
        exact c5 hk2
      · intro hk3 i hi
        have hsz : (nodeIvl s n).2 = 176 := by simp [nodeIvl, nodeSize, hk3]
        rw [hnW n hn (n + 32 + 8 * i) ⟨by simp [nodeIvl]; omega, by simp [nodeIvl] at hsz ⊢; omega⟩]
        exact c6 hk3 i hi
      · intro hk12
        obtain ⟨p32, p40⟩ := hn_pw n hn hk12; rw [p32, p40]
        rcases c7 hk12 with hz | ⟨hnib, hpal, hpins, hpdisj⟩
        · exact Or.inl hz
        · right
          refine ⟨?_, (hAlloc_eq _).mpr hpal, hpins, fun m hm => by rw [hn_ivl m hm]; exact hpdisj m hm⟩
          by_cases hl0 : memW s (n + 40) = 0
          · intro k hk; omega
          · have hp_m : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nset := by
              have hpeq : nodePath s n = (memW s (n + 32), memW s (n + 40)) := by
                unfold nodePath; simp [hk12, hl0]
              rw [← hpeq]; exact hn_path_m n hn
            obtain ⟨hde_p, hdc_p⟩ := hdN _ hp_m
            have hpb := halloc_bound _ hpal
            intro k hk
            rw [hmemB_disj _ hde_p hdc_p (memW s (n + 32) + k) ⟨by omega, by omega⟩ (by omega)]
            exact hnib k hk
      · intro hk1
        have hsz : (nodeIvl s n).2 = 64 := by simp [nodeIvl, nodeSize, hk1]
        rw [hnW n hn (n + 56) ⟨by simp [nodeIvl], by simp [nodeIvl] at hsz ⊢; omega⟩]
        exact c9 hk1
      · intro hk3
        have hsz : (nodeIvl s n).2 = 176 := by simp [nodeIvl, nodeSize, hk3]
        rw [hnW n hn (n + 168) ⟨by simp [nodeIvl], by simp [nodeIvl] at hsz ⊢; omega⟩]
        exact c10 hk3
    · intro n hn m hm hne; rw [hn_ivl n hn, hn_ivl m hm]; exact hNH.2 n hn m hm hne
    · intro o ho; rw [hext] at ho; rw [hfix_eq]
      exact ⟨fun t ht i hi => by rw [(htab_kept t ht).2.1] at hi; exact (hTd o ho).1 t ht i hi,
        (hTd o ho).2⟩
    · rw [hglobN]; intro hws0
      have hwsW := hrecW "ws" 40 (by decide) (by decide) hws0
      rw [hwsW 24 (by omega), hwsW 32 (by omega)]
      obtain ⟨h24, h32⟩ := hTws hws0
      refine ⟨h24, fun hmS => ?_⟩
      obtain ⟨hhdr, _, _, _⟩ := htab_kept _ hmS
      rw [hhdr 3 (by omega), hhdr 5 (by omega), hhdr 6 (by omega)]
      intro i hi
      have hres := h32 hmS i hi
      have hord_in : (hdr s (memW s (globN s "ws" + 32)) 6,
          (hdr s (memW s (globN s "ws" + 32)) 10 + 1) * 8) ∈ htabFootprint s (memW s (globN s "ws" + 32)) := by
        simp [htabFootprint]
      have hnd_in : (hdr s (memW s (globN s "ws" + 32)) 5,
          (hdr s (memW s (globN s "ws" + 32)) 10 + 1) * 32) ∈ htabFootprint s (memW s (globN s "ws" + 32)) := by
        simp [htabFootprint]
      obtain ⟨_, _, _, _, _, _, _, _, L, I, Fr, c9, c10, c11, c12, c13, _⟩ := (hTab.2.1 _ hmS).1
      have hcnt_le : hdr s (memW s (globN s "ws" + 32)) 3 ≤ hdr s (memW s (globN s "ws" + 32)) 10 := by
        have hsub : (L ++ I).toFinset ⊆ Finset.Ico 1 (hdr s (memW s (globN s "ws" + 32)) 8) := by
          intro x hx; rw [List.mem_toFinset] at hx; rw [Finset.mem_Ico]
          exact (c11 x).1 (List.mem_append_left _ hx)
        have hcard := Finset.card_le_card hsub
        rw [List.toFinset_card_of_nodup (List.nodup_append.mp c10).1, Nat.card_Ico, List.length_append] at hcard
        rcases c12 with ⟨h0, _⟩ | _ <;> omega
      have hord_b := halloc_bound _ ((hTab.2.1 _ hmS).2 _ hord_in).1
      have hnd_b := halloc_bound _ ((hTab.2.1 _ hmS).2 _ hnd_in).1
      have heq_ord := hmemW_disj _ (hd_tab_e _ hmS _ hord_in) (hd_tab_c _ hmS _ hord_in)
        (hdr s (memW s (globN s "ws" + 32)) 6 + 8 * i) ⟨by omega, by omega⟩ (by omega)
      rw [heq_ord]
      have hLi : memW s (hdr s (memW s (globN s "ws" + 32)) 6 + 8 * i) = L[i]'(by omega) := (c13 i (by omega)).1
      have hLm : L[i]'(by omega) ∈ L ++ I ++ Fr :=
        List.mem_append_left _ (List.mem_append_left _ (List.getElem_mem _))
      have hLl : L[i]'(by omega) < hdr s (memW s (globN s "ws" + 32)) 8 := ((c11 _).1 hLm).2
      have heq_nf : nodeF post (hdr s (memW s (globN s "ws" + 32)) 5)
          (memW s (hdr s (memW s (globN s "ws" + 32)) 6 + 8 * i)) 8 =
          nodeF s (hdr s (memW s (globN s "ws" + 32)) 5)
          (memW s (hdr s (memW s (globN s "ws" + 32)) 6 + 8 * i)) 8 := by
        rw [hLi]; unfold nodeF
        exact hmemW_disj _ (hd_tab_e _ hmS _ hnd_in) (hd_tab_c _ hmS _ hnd_in)
          _ ⟨by omega, by omega⟩ (by omega)
      rw [heq_nf]; exact hres
  obtain ⟨Nd_av, hTriesAv, hDisjAv⟩ := hTries
  have hd_triesAv : ∀ o ∈ nodeExtents s Nd_av, Disj (e0, 280) o ∧ Disj (c0, 104) o := fun o ho =>
    ⟨hDisjAv (e0, 280) (List.mem_flatten.mpr ⟨frameObjects s (e0, c0), List.mem_map_of_mem hec0_mem, he0_fo⟩) o ho,
     hDisjAv (c0, 104) (List.mem_flatten.mpr ⟨frameObjects s (e0, c0), List.mem_map_of_mem hec0_mem, hc0_fo⟩) o ho⟩
  obtain ⟨hTriesAv_post, hextAv_eq⟩ := htries_preserved Nd_av hTriesAv hd_triesAv
  -- 4. `WorldTyped post S`
  have hTab_post : TablesTyped post S := by
    obtain ⟨hSnodup, hShtab, hSdisj, hSws, hSbs, hSts, hSg, hSnbs, hSnts, hSbal, hSbo, hSroles⟩ := hTab
    refine ⟨hSnodup, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      obtain ⟨_, hfp, _, hwf_p⟩ := htab_kept t ht
      refine ⟨hwf_p, fun i hi => ?_⟩
      rw [hfp] at hi; rw [hfix_eq]
      exact ⟨(hAlloc_eq i).mpr ((hShtab t ht).2 i hi).1, ((hShtab t ht).2 i hi).2⟩
    · intro t ht u hu hne i hi j hj
      rw [(htab_kept t ht).2.1] at hi; rw [(htab_kept u hu).2.1] at hj
      exact hSdisj t ht u hu hne i hi j hj
    · intro k hk; rw [hglobN]; intro hws0
      have hklt : k < 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [hrecW "ws" 40 (by decide) (by decide) hws0 k hklt]
      exact hSws k hk hws0
    · intro k hk; rw [hglobN]; intro hbs0
      have hklt : k < 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [hrecW "bs" 80 (by decide) (by decide) hbs0 k hklt]
      exact hSbs k hk hbs0
    · intro k hk; rw [hglobN]; intro hts0
      have hklt : k < 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [hrecW "ts" 72 (by decide) (by decide) hts0 k hklt]
      exact hSts k hk hts0
    · intro g hg; rw [hglobN]; exact hSg g hg
    · rw [hglobN]; intro hbs0
      rw [hrecW "bs" 80 (by decide) (by decide) hbs0 32 (by omega)]
      intro hmS; have hvals := (htab_kept _ hmS).2.2.1
      unfold HtabValuesIn; intro i hi
      have hmemv : nodeF post (hdr post (memW s (globN s "bs" + 32)) 5)
          (memW post (hdr post (memW s (globN s "bs" + 32)) 6 + 8 * i)) 8 ∈
            htabValues post (memW s (globN s "bs" + 32)) :=
        List.mem_map_of_mem (List.mem_range.mpr hi)
      rw [hvals] at hmemv; unfold htabValues at hmemv
      obtain ⟨j, hj, heq⟩ := List.mem_map.mp hmemv; rw [← heq]
      exact hSnbs hbs0 hmS j (List.mem_range.mp hj)
    · rw [hglobN]; intro hts0
      rw [hrecW "ts" 72 (by decide) (by decide) hts0 32 (by omega)]
      intro hmS; have hvals := (htab_kept _ hmS).2.2.1
      unfold HtabValuesIn; intro i hi
      have hmemv : nodeF post (hdr post (memW s (globN s "ts" + 32)) 5)
          (memW post (hdr post (memW s (globN s "ts" + 32)) 6 + 8 * i)) 8 ∈
            htabValues post (memW s (globN s "ts" + 32)) :=
        List.mem_map_of_mem (List.mem_range.mpr hi)
      rw [hvals] at hmemv; unfold htabValues at hmemv
      obtain ⟨j, hj, heq⟩ := List.mem_map.mp hmemv; rw [← heq]
      exact hSnts hts0 hmS j (List.mem_range.mp hj)
    · rw [hbal_rec_eq]; intro ad had
      obtain ⟨e0', e8', hkl, hlv⟩ := hbal_kept.2 ad had
      have hb_old := hSbal ad had
      exact ⟨e0' ▸ hb_old.1, e8' ▸ hb_old.2.1, hkl, hlv⟩
    · rw [hglobN]; intro hbo0 k hk hkz
      have ⟨heqk, hlk⟩ := hbo_kept.2 hbo0 k hk
      rw [heqk] at hkz; exact hlk hkz
    · rw [hwroles_eq, hjroles_eq]
      obtain ⟨r1, r2, r3⟩ := hSroles
      exact ⟨fun a ha => ⟨(r1 a ha).1, by rw [(htab_kept a.1 (r1 a ha).1).1 0 (by omega)]; exact (r1 a ha).2⟩,
        r2, r3⟩
  have hJrn_post : JournalTyped post S := by
    obtain ⟨j1, j2, j3, j4⟩ := hJrn
    unfold JournalTyped; simp only [hglobN]
    refine ⟨j1, j2, ?_, fun i hi => ?_⟩
    · rcases j3 with hz | ⟨hal, hw⟩
      · exact Or.inl hz
      · exact Or.inr ⟨(hAlloc_eq _).mpr hal, (hWordsOK_eq _).mpr hw⟩
    · have e0' := hjrn_words i hi 0 (by simp)
      simp only [Nat.add_zero] at e0'; rw [e0']; exact j4 i hi
  have hFix_post : FixedTyped post := by
    unfold FixedTyped; rw [hfix_eq]
    refine ⟨fun o ho => ?_, hFix.2⟩
    rcases hFix.1 o ho with hz | ⟨hal, hw⟩
    · exact Or.inl hz
    · exact Or.inr ⟨(hAlloc_eq o).mpr hal, (hWordsOK_eq o).mpr hw⟩
  have hWT_post : WorldTyped post S := ⟨hTab_post, hJrn_post, hFix_post, ⟨Nd_av, hTriesAv_post⟩⟩
  -- 5. Separation of `(e0, 280)` and `(c0, 104)` from other frame objects in `evmChain s`
  have hflat := List.pairwise_flatten.mp hPair
  have hmap_len : ((evmChain s).map (frameObjects s)).length = (evmChain s).length := List.length_map _
  have hhead : (evmChain s)[0]'(List.length_pos_iff.mpr hch_ne) = (e0, c0) := by
    simp [evmChain, evmChainFrom, e0, c0]
  have hp0 : (frameObjects s (e0, c0)).Pairwise Disj := by
    have hfo_mem : frameObjects s (e0, c0) ∈ (evmChain s).map (frameObjects s) :=
      List.mem_map_of_mem hec0_mem
    exact hflat.1 _ hfo_mem
  have hp0_split := List.pairwise_append.mp hp0
  -- `hp0_split.1` is pairwise Disj on the 7-element prefix of `frameObjects s (e0, c0)`!
  have hp0_7 := hp0_split.1
  have hdisj_e0_c0 : Disj (e0, 280) (c0, 104) :=
    (List.pairwise_cons.mp hp0_7).1 (c0, 104) (by simp)
  have hother_frame_disj : ∀ (idx : Nat) (hidx : idx < (evmChain s).length), 0 < idx →
      ∀ o ∈ frameObjects s (evmChain s)[idx], Disj (e0, 280) o ∧ Disj (c0, 104) o := by
    intro idx hidx hpos o ho
    have h0_lt : 0 < (evmChain s).length := by omega
    have hrel := List.pairwise_iff_getElem.mp hflat.2 0 idx
      (by rw [hmap_len]; exact h0_lt) (by rw [hmap_len]; exact hidx) hpos
    simp only [List.getElem_map, hhead] at hrel
    exact ⟨hrel (e0, 280) he0_fo o ho, hrel (c0, 104) hc0_fo o ho⟩
  have hcont_field_eq : ∀ ec ∈ evmChain s, ∀ off < 104, off ≠ 32 →
      memW post (ec.2 + off) = memW s (ec.2 + off) := by
    intro ec hec off hoff hne32
    have hc_in : Inside (ec.2, 104) (globN s "scratch_ptr") scratchEnd :=
      (hFWF ec hec).1 (ec.2, 104) (by simp) |>.1
    have hc_lt' : ec.2 + 104 < 2 ^ 64 := by have := hc_in.2; rw [scratchEnd_val] at this; omega
    obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hec
    by_cases h0 : idx = 0
    · subst h0; rw [hhead]
      apply hmemW_ne (c0 + off) (by omega)
      intro addr haddr heq
      rcases hall_in_ec0 addr haddr with ⟨he1, he2⟩ | ⟨_, _⟩
      · unfold Disj at hdisj_e0_c0; dsimp only at hdisj_e0_c0
        rcases hdisj_e0_c0 with h | h | h | h <;> omega
      · simp only [headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
        unfold Disj at hdisj_e0_c0; dsimp only at hdisj_e0_c0
        rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rcases hdisj_e0_c0 with h | h | h | h <;> omega
        · rcases hdisj_e0_c0 with h | h | h | h <;> omega
        · rcases hdisj_e0_c0 with h | h | h | h <;> omega
        · rcases hdisj_e0_c0 with h | h | h | h <;> omega
        · rcases hdisj_e0_c0 with h | h | h | h <;> omega
        · rcases hdisj_e0_c0 with h | h | h | h <;> omega
        · rcases hdisj_e0_c0 with h | h | h | h <;> omega
        · rcases hdisj_e0_c0 with h | h | h | h <;> omega
        · rcases hdisj_e0_c0 with h | h | h | h <;> omega
        · rcases hdisj_e0_c0 with h | h | h | h <;> omega
        · omega
    · obtain ⟨hde, hdc⟩ := hother_frame_disj idx hidx (by omega)
        ((evmChain s)[idx].2, 104) (by simp [frameObjects])
      exact hmemW_disj _ hde hdc _ ⟨by omega, by omega⟩ (by omega)
  have hchain_eq : evmChain post = evmChain s := by
    suffices haux : ∀ (fuel e c : Nat),
        (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
        evmChainFrom post fuel e c = evmChainFrom s fuel e c by
      unfold evmChain; rw [hglobN, hglobN]
      exact haux _ _ _ (fun _ h => h)
    intro fuel; induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec_in : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      have hc0_eq := hcont_field_eq (e, c) hec_in 0 (by omega) (by omega)
      have hc8_eq := hcont_field_eq (e, c) hec_in 8 (by omega) (by omega)
      have hc16_eq := hcont_field_eq (e, c) hec_in 16 (by omega) (by omega)
      simp only [Nat.add_zero] at hc0_eq
      simp only [evmChainFrom, hc16_eq, hc0_eq, hc8_eq]
      by_cases h16 : memW s (c + 16) = 0
      · simp [h16]
      · simp only [h16, ↓reduceIte]
        congr 1; apply ih
        intro ec hec; apply hsub; simp [evmChainFrom, h16, hec]
  have hframe_field_eq : ∀ ec ∈ evmChain s, ∀ off < 280, off ∉ allowedFrameOffs →
      memW post (ec.1 + off) = memW s (ec.1 + off) := by
    intro ec hec off hoff hnot
    have he_in : Inside (ec.1, 280) (globN s "scratch_ptr") scratchEnd :=
      (hFWF ec hec).1 (ec.1, 280) (by simp) |>.1
    have he_lt' : ec.1 + 280 < 2 ^ 64 := by have := he_in.2; rw [scratchEnd_val] at this; omega
    obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hec
    by_cases h0 : idx = 0
    · subst h0; rw [hhead]
      apply hmemW_ne (e0 + off) (by omega)
      intro addr haddr heq
      simp only [headAllowedOffsets, List.mem_cons, List.not_mem_nil, or_false] at haddr
      rcases haddr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have ho : off = 64 := by omega
        exact hnot (ho ▸ (by decide : 64 ∈ allowedFrameOffs))
      · have ho : off = 72 := by omega
        exact hnot (ho ▸ (by decide : 72 ∈ allowedFrameOffs))
      · have ho : off = 96 := by omega
        exact hnot (ho ▸ (by decide : 96 ∈ allowedFrameOffs))
      · have ho : off = 104 := by omega
        exact hnot (ho ▸ (by decide : 104 ∈ allowedFrameOffs))
      · have ho : off = 120 := by omega
        exact hnot (ho ▸ (by decide : 120 ∈ allowedFrameOffs))
      · have ho : off = 128 := by omega
        exact hnot (ho ▸ (by decide : 128 ∈ allowedFrameOffs))
      · have ho : off = 160 := by omega
        exact hnot (ho ▸ (by decide : 160 ∈ allowedFrameOffs))
      · have ho : off = 184 := by omega
        exact hnot (ho ▸ (by decide : 184 ∈ allowedFrameOffs))
      · have ho : off = 192 := by omega
        exact hnot (ho ▸ (by decide : 192 ∈ allowedFrameOffs))
      · have ho : off = 200 := by omega
        exact hnot (ho ▸ (by decide : 200 ∈ allowedFrameOffs))
      · unfold Disj at hdisj_e0_c0; dsimp only at hdisj_e0_c0
        rcases hdisj_e0_c0 with h | h | h | h <;> omega
    · obtain ⟨hde, hdc⟩ := hother_frame_disj idx hidx (by omega)
        ((evmChain s)[idx].1, 280) (by simp [frameObjects])
      exact hmemW_disj _ hde hdc _ ⟨by omega, by omega⟩ (by omega)
  have hlogs_hdr_disj : ∀ ec ∈ evmChain s,
      Disj (e0, 280) (memW s (ec.1 + 88), 24) ∧ Disj (c0, 104) (memW s (ec.1 + 88), 24) := by
    intro ec hec
    obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hec
    by_cases h0 : idx = 0
    · subst h0; rw [hhead]
      have p1 := List.pairwise_cons.mp hp0_7
      have p2 := List.pairwise_cons.mp p1.2
      exact ⟨p1.1 (memW s (e0 + 88), 24) (by simp), p2.1 (memW s (e0 + 88), 24) (by simp)⟩
    · exact hother_frame_disj idx hidx (by omega) _ (by simp [frameObjects])
  have hlogs_hdr_eq : ∀ ec ∈ evmChain s, ∀ off < 24,
      memW post (memW s (ec.1 + 88) + off) = memW s (memW s (ec.1 + 88) + off) := by
    intro ec hec off hoff
    have hl_in := (hFWF ec hec).1 (memW s (ec.1 + 88), 24) (by simp) |>.1
    have hl_lt : memW s (ec.1 + 88) + 24 < 2 ^ 64 := by have := hl_in.2; rw [scratchEnd_val] at this; omega
    obtain ⟨hde, hdc⟩ := hlogs_hdr_disj ec hec
    exact hmemW_disj _ hde hdc _ ⟨by omega, by omega⟩ (by omega)
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec; unfold frameLogs
    rw [hframe_field_eq ec hec 88 (by omega) (by decide)]
    have e0' := hlogs_hdr_eq ec hec 0 (by omega)
    have e16' := hlogs_hdr_eq ec hec 16 (by omega)
    simp only [Nat.add_zero] at e0'; rw [e0', e16']
  have hlogs_arr_disj : ∀ ec ∈ evmChain s,
      Disj (e0, 280) (frameLogs s ec) ∧ Disj (c0, 104) (frameLogs s ec) := by
    intro ec hec
    obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hec
    by_cases h0 : idx = 0
    · subst h0; rw [hhead]
      have p1 := List.pairwise_cons.mp hp0_7
      have p2 := List.pairwise_cons.mp p1.2
      exact ⟨p1.1 (frameLogs s (e0, c0)) (by simp), p2.1 (frameLogs s (e0, c0)) (by simp)⟩
    · exact hother_frame_disj idx hidx (by omega) _ (by simp [frameObjects])
  -- R11: live log pointer array entries & live log records `(log, 40)` are unchanged!
  have hlog_ptr_eq : ∀ ec ∈ evmChain s, ∀ i < memW s (memW s (ec.1 + 88) + 8),
      memW post (memW s (memW s (ec.1 + 88)) + 8 * i) =
      memW s (memW s (memW s (ec.1 + 88)) + 8 * i) := by
    intro ec hec i hi
    have hF := hFWF ec hec
    have hcap_ge : memW s (memW s (ec.1 + 88) + 8) ≤ memW s (memW s (ec.1 + 88) + 16) :=
      hF.2.2.2.2.2.2.2.2.2.2.2.1
    have hfl_al : Allocated s (frameLogs s ec) := by
      rcases hF.2.2.2.2.2.2.2.2.2.2.2.2.1 with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hfl_bnd := halloc_bound _ hfl_al
    unfold frameLogs at hfl_bnd; dsimp only at hfl_bnd
    obtain ⟨hde, hdc⟩ := hlogs_arr_disj ec hec
    exact hmemW_disj (frameLogs s ec) hde hdc _
      ⟨by unfold frameLogs; dsimp only; omega, by unfold frameLogs; dsimp only; omega⟩ (by omega)
  have hlog_rec_disj : ∀ ec ∈ evmChain s, ∀ i < memW s (memW s (ec.1 + 88) + 8),
      let log := memW s (memW s (memW s (ec.1 + 88)) + 8 * i)
      Disj (e0, 280) (log, 40) ∧ Disj (c0, 104) (log, 40) := by
    intro ec hec i hi log
    have howned : (log, 40) ∈ logOwnedIvls s log := by simp [logOwnedIvls, logRecordIvls]
    have hin_flo : (log, 40) ∈ frameLogObjects s ec :=
      List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, howned⟩
    have hin_fo : (log, 40) ∈ frameObjects s ec := List.mem_append_right _ hin_flo
    obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hec
    by_cases h0 : idx = 0
    · subst h0; rw [hhead] at hin_flo
      exact ⟨hp0_split.2.2 (e0, 280) (by simp) (log, 40) hin_flo,
             hp0_split.2.2 (c0, 104) (by simp) (log, 40) hin_flo⟩
    · exact hother_frame_disj idx hidx (by omega) (log, 40) hin_fo
  have hlog_rec_words : ∀ ec ∈ evmChain s, ∀ i < memW s (memW s (ec.1 + 88) + 8),
      let log := memW s (memW s (memW s (ec.1 + 88)) + 8 * i)
      ∀ off < 40, memW post (log + off) = memW s (log + off) := by
    intro ec hec i hi log off hoff
    have hF := hFWF ec hec
    have hllok : LogsListOK s (memW s (ec.1 + 88)) :=
      hF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hlog_ok : LogEntryOK s log := by
      rcases hllok with hz | ⟨_, _, _, _, hentries⟩
      · have hf := (hF.1 (memW s (ec.1 + 88), 24) (by simp)).1.1
        have h1 := hAR.2.2.2.1; have h2 := hAR.2.2.2.2.1; rw [scratchStart_val] at h1
        dsimp only at hf; omega
      · exact (hentries i hi).2
    have hlog_lt := halloc_bound (log, 40) (Or.inl hlog_ok.2.1)
    dsimp only at hlog_lt
    obtain ⟨hde, hdc⟩ := hlog_rec_disj ec hec i hi
    exact hmemW_disj (log, 40) hde hdc (log + off) ⟨by omega, by omega⟩ (by omega)
  have hframeLogObjects_eq : ∀ ec ∈ evmChain s, frameLogObjects post ec = frameLogObjects s ec := by
    intro ec hec; unfold frameLogObjects; dsimp only
    rw [hframe_field_eq ec hec 88 (by omega) (by decide),
        hlogs_hdr_eq ec hec 8 (by omega)]
    have he0_88 := hlogs_hdr_eq ec hec 0 (by omega)
    simp only [Nat.add_zero] at he0_88
    apply List.flatMap_congr; intro i hi
    rw [List.mem_range] at hi
    rw [he0_88, hlog_ptr_eq ec hec i hi]
    set log := memW s (memW s (memW s (ec.1 + 88)) + 8 * i)
    have w0 := hlog_rec_words ec hec i hi 0 (by omega)
    have w8 := hlog_rec_words ec hec i hi 8 (by omega)
    have w16 := hlog_rec_words ec hec i hi 16 (by omega)
    have w24 := hlog_rec_words ec hec i hi 24 (by omega)
    have w32 := hlog_rec_words ec hec i hi 32 (by omega)
    simp only [Nat.add_zero] at w0
    change logOwnedIvls post log = logOwnedIvls s log
    unfold logOwnedIvls logRecordIvls
    rw [hglobN, w0, w8, w16, w24, w32]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec; unfold frameRet
    rw [hframe_field_eq ec hec 216 (by omega) (by decide),
        hframe_field_eq ec hec 144 (by omega) (by decide)]
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec; unfold frameObjects
    rw [hframe_field_eq ec hec 8 (by omega) (by decide),
        hframe_field_eq ec hec 232 (by omega) (by decide),
        hframe_field_eq ec hec 24 (by omega) (by decide),
        hframe_field_eq ec hec 40 (by omega) (by decide),
        hframe_field_eq ec hec 88 (by omega) (by decide),
        hframeLogs_eq ec hec, hframeRet_eq ec hec, hframeLogObjects_eq ec hec]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec; unfold frameScratch
    rw [hframe_field_eq ec hec 8 (by omega) (by decide),
        hframe_field_eq ec hec 232 (by omega) (by decide),
        hframe_field_eq ec hec 88 (by omega) (by decide)]
  have hmap_fo_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hframeRoles_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots; apply List.flatMap_congr; intro ec hec
    rw [hframe_field_eq ec hec 136 (by omega) (by decide),
        hframe_field_eq ec hec 168 (by omega) (by decide),
        hframe_field_eq ec hec 176 (by omega) (by decide)]
  have hworldRefs_eq : worldTableRefs post S = worldTableRefs s S := by
    have hrs : ∀ (g : String) (sz : Nat) (ks : List Nat),
        (g, sz) ∈ globalBuffers → 0 < sz → (∀ k ∈ ks, k < sz) →
        recordSlots post g ks = recordSlots s g ks := by
      intro g sz ks hgb hsz hks
      unfold recordSlots; rw [hglobN]
      by_cases hg0 : globN s g = 0
      · simp [hg0]
      · simp only [hg0, ↓reduceIte]
        exact List.map_congr_left fun k hk => hrecW g sz hgb hsz hg0 k (hks k hk)
    unfold worldTableRefs; dsimp only
    rw [hrs "ws" 40 wsTableSlots (by decide) (by decide) (by decide),
        hrs "bs" 80 bsTableSlots (by decide) (by decide) (by decide),
        hrs "ts" 72 tsTableSlots (by decide) (by decide) (by decide),
        hbal_rec_eq]
    have hgmap : globalTableRoots.map (globN post) = globalTableRoots.map (globN s) :=
      List.map_congr_left fun g _ => hglobN g
    have hnest_eq : ∀ (g : String) (sz : Nat), (g, sz) ∈ globalBuffers → 32 < sz →
        (if globN post g ≠ 0 ∧ memW post (globN post g + 32) ∈ S then htabValues post (memW post (globN post g + 32)) else []) =
        (if globN s g ≠ 0 ∧ memW s (globN s g + 32) ∈ S then htabValues s (memW s (globN s g + 32)) else []) := by
      intro g sz hgb hsz; rw [hglobN]
      by_cases hg0 : globN s g = 0
      · simp [hg0]
      · rw [hrecW g sz hgb (by omega) hg0 32 hsz]
        by_cases hmS : memW s (globN s g + 32) ∈ S
        · simp [hg0, hmS, (htab_kept _ hmS).2.2.1]
        · simp [hg0, hmS]
    have hbal_fm : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
        (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) :=
      List.flatMap_congr fun ad had => by
        obtain ⟨e0', e8', _, _⟩ := hbal_kept.2 ad had; rw [e0', e8']
    have hjrn_map : (List.range (globN post "journal_n")).map (fun k => memW post (globN post "journal" + 32 * k)) =
        (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
      simp only [hglobN]
      apply List.map_congr_left; intro k hk; rw [List.mem_range] at hk
      have e0' := hjrn_words k hk 0 (by simp)
      simp only [Nat.add_zero] at e0'; exact e0'
    rw [hgmap, hnest_eq "bs" 80 (by decide) (by decide), hnest_eq "ts" 72 (by decide) (by decide),
        hbal_fm, hjrn_map]
  -- Gas sum bound:
  have hsum_le : ((evmChain s).map (fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192))).sum ≤
      ((evmChain s).map (fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192))).sum := by
    have hterm_le : ∀ ec ∈ evmChain s,
        memW post (ec.1 + 64) + memW post (ec.1 + 192) ≤ memW s (ec.1 + 64) + memW s (ec.1 + 192) := by
      intro ec hec
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hec
      by_cases h0 : idx = 0
      · subst h0; rw [hhead]; exact hgas_le
      · have he_in : Inside ((evmChain s)[idx].1, 280) (globN s "scratch_ptr") scratchEnd :=
          (hFWF _ hec).1 (_, 280) (by simp) |>.1
        have he_lt' : (evmChain s)[idx].1 + 280 < 2 ^ 64 := by have := he_in.2; rw [scratchEnd_val] at this; omega
        obtain ⟨hde, hdc⟩ := hother_frame_disj idx hidx (by omega)
          ((evmChain s)[idx].1, 280) (by simp [frameObjects])
        rw [hmemW_disj _ hde hdc _ ⟨by omega, by omega⟩ (by omega),
            hmemW_disj _ hde hdc _ ⟨by omega, by omega⟩ (by omega)]
    have hlist_le : ∀ (L : List Ivl),
        (∀ ec ∈ L, memW post (ec.1 + 64) + memW post (ec.1 + 192) ≤ memW s (ec.1 + 64) + memW s (ec.1 + 192)) →
        (L.map (fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192))).sum ≤
          (L.map (fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192))).sum := by
      intro L; induction L with
      | nil => intro _; simp
      | cons hd tl ih =>
        intro hL; simp only [List.map_cons, List.sum_cons]
        have h1 := hL hd List.mem_cons_self
        have h2 := ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
        omega
    exact hlist_le (evmChain s) hterm_le
  -- 6. Assemble `EvmInv post`!
  refine ⟨⟨hAR_post, S, hWT_post, ?_⟩, hchain_eq, by rw [hchain_eq]; exact hsum_le⟩
  dsimp only; rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
  · obtain ⟨ec, hec, hk0⟩ := hlast
    have hec_mem : ec ∈ evmChain s := List.mem_of_getLast? hec
    exact ⟨ec, hec, by rw [hcont_field_eq ec hec_mem 16 (by omega) (by omega)]; exact hk0⟩
  · intro ec hec
    have hF := hFWF ec hec
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, hllok, hmsg_own⟩ := hF
    unfold FrameWF; dsimp only
    rw [hframe_field_eq ec hec 8 (by omega) (by decide),
        hframe_field_eq ec hec 232 (by omega) (by decide),
        hframe_field_eq ec hec 88 (by omega) (by decide),
        hframe_field_eq ec hec 24 (by omega) (by decide),
        hframe_field_eq ec hec 40 (by omega) (by decide),
        hframe_field_eq ec hec 16 (by omega) (by decide),
        hframe_field_eq ec hec 32 (by omega) (by decide),
        hframe_field_eq ec hec 136 (by omega) (by decide),
        hframe_field_eq ec hec 168 (by omega) (by decide),
        hframe_field_eq ec hec 176 (by omega) (by decide),
        hframe_field_eq ec hec 216 (by omega) (by decide),
        hframe_field_eq ec hec 144 (by omega) (by decide),
        hframe_field_eq ec hec 112 (by omega) (by decide),
        hlogs_hdr_eq ec hec 16 (by omega),
        hlogs_hdr_eq ec hec 8 (by omega),
        hframeLogs_eq ec hec,
        hframeRet_eq ec hec]
    simp only [hglobN, hWordsOK_eq]
    refine ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, ?_, ?_⟩
    · -- `LogsListOK post (memW s (ec.1 + 88))`
      rcases hllok with hz | ⟨lw, lal, llt, lle, lentries⟩
      · exact Or.inl hz
      · right
        rw [hlogs_hdr_eq ec hec 8 (by omega), hlogs_hdr_eq ec hec 16 (by omega)]
        have he0_88 := hlogs_hdr_eq ec hec 0 (by omega)
        simp only [Nat.add_zero] at he0_88
        refine ⟨(hWordsOK_eq _).mpr lw, (hAlloc_eq _).mpr lal, llt, lle, fun i hi => ?_⟩
        rw [he0_88, hlog_ptr_eq ec hec i hi]
        obtain ⟨hwa, hlok⟩ := lentries i hi
        refine ⟨(hWordAt_eq _).mpr hwa, ?_⟩
        unfold LogEntryOK at hlok ⊢
        have w0 := hlog_rec_words ec hec i hi 0 (by omega)
        have w8 := hlog_rec_words ec hec i hi 8 (by omega)
        have w16 := hlog_rec_words ec hec i hi 16 (by omega)
        have w24 := hlog_rec_words ec hec i hi 24 (by omega)
        have w32 := hlog_rec_words ec hec i hi 32 (by omega)
        simp only [Nat.add_zero] at w0
        rw [w0, w8, w16, w24, w32]
        simp only [hglobN, hWordsOK_eq]
        exact hlok
    · -- `MsgOwned post S (memW s (ec.1 + 112))`
      obtain ⟨mal, mw, md_tab, md_fix, md_fo, Nd_m, hTr_m, hd_m⟩ := hmsg_own
      obtain ⟨hTr_int, hsub_int⟩ := triesTypedWith_inter hTr_m hTriesAv
      have hd_int : ∀ o ∈ nodeExtents s (Nd_m.filter (fun n => decide (n ∈ Nd_av))),
          Disj (e0, 280) o ∧ Disj (c0, 104) o := fun o ho =>
        hd_triesAv o (hsub_int o ho).2
      obtain ⟨hTr_int_post, hext_int_eq⟩ := htries_preserved _ hTr_int hd_int
      refine ⟨(hAlloc_eq _).mpr mal, (hWordsOK_eq _).mpr mw, ?_, ?_, ?_, ?_⟩
      · intro t ht i hi; rw [(htab_kept t ht).2.1] at hi; exact md_tab t ht i hi
      · rw [hfix_eq]; exact md_fix
      · intro ec' hec' o ho
        rw [hchain_eq] at hec'
        rw [hframeObjects_eq ec' hec'] at ho
        exact md_fo ec' hec' o ho
      · refine ⟨Nd_m.filter (fun n => decide (n ∈ Nd_av)), hTr_int_post, fun o ho j hj => ?_⟩
        rw [hext_int_eq] at hj
        exact hd_m o ho j (hsub_int j hj).1
  · intro ec hec
    have hec_m : ec ∈ evmChain s := List.mem_of_mem_tail hec
    unfold FrameRoom
    rw [hframe_field_eq ec hec_m 16 (by omega) (by decide),
        hframe_field_eq ec hec_m 232 (by omega) (by decide)]
    exact hFRoom ec hec
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
    rw [hcont_field_eq _ hi0 80 (by omega) (by omega), hcont_field_eq _ hi0 72 (by omega) (by omega),
        hframe_field_eq _ hi1 40 (by omega) (by decide)]
    exact hRetW i hi
  · rw [hmap_fo_eq]; exact hPair
  · intro ec hec o ho
    rw [hframeObjects_eq ec hec] at ho; rw [hfix_eq]
    exact ⟨fun t ht i hi => by rw [(htab_kept t ht).2.1] at hi; exact (hDisj ec hec o ho).1 t ht i hi,
      (hDisj ec hec o ho).2⟩
  · rw [hmap_fo_eq]
    exact ⟨Nd_av, hTriesAv_post, fun o ho j hj => by rw [hextAv_eq] at hj; exact hDisjAv o ho j hj⟩
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hm_i := hMarks i hi; dsimp only at hm_i ⊢
    rw [hcont_field_eq _ hi0 48 (by omega) (by omega),
        hcont_field_eq _ hi0 56 (by omega) (by omega),
        hframeScratch_eq _ hi0,
        hframe_field_eq _ hi0 24 (by omega) (by decide),
        hfix_eq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hm_i
    refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
    · intro j hj hij
      have hj_m : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      rw [hframeScratch_eq _ hj_m, hframeObjects_eq _ hj_m, hframeLogs_eq _ hj_m,
          hframe_field_eq _ hj_m 112 (by omega) (by decide)]
      exact m5 j hj hij
    · intro t ht
      have htk_fp := (htab_kept t ht).2.1
      have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
          ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) :=
        List.map_congr_left fun ec hec =>
          hframe_field_eq ec (List.mem_of_mem_take hec) 136 (by omega) (by decide)
      have hdelEx_eq : DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
        unfold DelExclusive; rw [hworldRefs_eq]
        refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
          forall_congr' fun k => forall_congr' fun hk => ?_)
        have hj_m : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
        have hk_ok : k < 280 ∧ k ∉ allowedFrameOffs := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by decide⟩
        rw [hframe_field_eq _ hj_m k hk_ok.1 hk_ok.2]
      rw [htake_eq, hdelEx_eq, htk_fp]
      exact m8 t ht
  · rw [hwroles_eq, hframeRoles_eq, hjroles_eq]
    obtain ⟨r1, r2, r3⟩ := hRoles
    exact ⟨fun a ha => ⟨(r1 a ha).1, by rw [(htab_kept a.1 (r1 a ha).1).1 0 (by omega)]; exact (r1 a ha).2⟩,
      r2, r3⟩

end InitECandidate.Solver.Wave8GuestInv.R11Shards
