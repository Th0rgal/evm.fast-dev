import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.MptSetRootKeeps

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12

/-! ## 1. Scratch buffers and fresh-trie invariant for `build_mpt_indexed` -/

theorem not_resumes_timeout_bmi : ¬ Resumes (some (.timeOut : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

theorem not_resumes_finalFfi_bmi {ev} : ¬ Resumes (some (.finalFfi ev : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

abbrev bmiScratch : List (String × Nat) :=
  [("keccak_pad", 136), ("keccak_st", 200), ("mpt_hash_scratch", 40), ("mpt_key_scratch", 16)]

theorem bmiScratch_ok :
    ∀ gs ∈ bmiScratch, gs ∈ globalBuffers ∧ gs.1 ∉ typedRecords.map Prod.fst := by
  decide

def BmiScratchOK {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ gs ∈ bmiScratch, globN s gs.1 ≠ 0 →
    Allocated s (globN s gs.1, gs.2) ∧ WordsOK s (globN s gs.1, gs.2)

theorem bmiScratchOK_of_fixedTyped {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hF : FixedTyped s) : BmiScratchOK s := by
  intro gs hgs hnz
  have hgb : gs ∈ globalBuffers := (bmiScratch_ok gs hgs).1
  have hfix := P3MptSet.buf_in_fixedObjects s gs.1 gs.2 hgb hnz
  rcases hF.1 _ hfix with h0 | ⟨hal, hw⟩
  · exfalso
    simp only [bmiScratch, List.mem_cons, List.not_mem_nil, or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl <;> simp at h0
  · exact ⟨hal, hw⟩

theorem bmiScratchOK_of_heapByteEff {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl}
    (heff : HeapByteEff s post Rl ["heap_ptr", "scratch_ptr"])
    (hB : BmiScratchOK s) : BmiScratchOK post := by
  intro gs hgs hnz_post
  have hg_eq : globN post gs.1 = globN s gs.1 := by
    have hnot : ofString gs.1 ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString := by
      simp only [bmiScratch, List.mem_cons, List.not_mem_nil, or_false] at hgs
      rcases hgs with rfl | rfl | rfl | rfl <;> decide
    simp [globN, ← heff.globals (ofString gs.1) hnot]
  rw [hg_eq] at hnz_post ⊢
  obtain ⟨hal, hw⟩ := hB gs hgs hnz_post
  have hal_post : Allocated post (globN s gs.1, gs.2) := by
    rcases hal with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, Nat.le_trans h2 heff.hp_le⟩
    · exact Or.inr ⟨Nat.le_trans heff.sp_le h1, h2⟩
  have hw_post : WordsOK post (globN s gs.1, gs.2) := by
    refine ⟨hw.1, hw.2.1, fun k hk => ?_⟩
    obtain ⟨_, hdom, _⟩ := hw.2.2 k hk
    rcases hm : post.memory (BitVec.ofNat 64 ((globN s gs.1, gs.2).1 + 8 * k)) with ⟨w⟩
    exact ⟨w, heff.memaddrs ▸ hdom, hm⟩
  exact ⟨hal_post, hw_post⟩

theorem bmiScratch_disj_fresh {F : Type} {s : PanSemStateFiniteExact 64 F}
    {mark : Nat} (hAR : ArenaReady s) (hB : BmiScratchOK s)
    (hmark_lo : sourceBase ≤ mark)
    (hB_pre : ∀ gs ∈ bmiScratch, globN s gs.1 ≠ 0 →
      globN s gs.1 + gs.2 ≤ mark ∨ globN s "scratch_ptr" ≤ globN s gs.1)
    {o : Ivl} (ho : o = (0, 0) ∨ Inside o mark (globN s "heap_ptr")) :
    ∀ gs ∈ bmiScratch, Disj o (bufferRegion s gs) := by
  intro gs hgs
  rcases ho with rfl | ⟨ho1, ho2⟩
  · exact Or.inl rfl
  · by_cases hz : globN s gs.1 = 0
    · simp [bufferRegion, hz, Disj]
    · have hhl_ss : heapLimit ≤ scratchStart := by decide
      have hhp_hl := hAR.2.2.1
      have hss_fm := hAR.2.2.2.1
      have hfm_sp := hAR.2.2.2.2.1
      rcases hB_pre gs hgs hz with hlo | hhi
      · simp only [bufferRegion, hz, ↓reduceIte, Disj]
        exact Or.inr (Or.inr (Or.inr (by omega)))
      · simp only [bufferRegion, hz, ↓reduceIte, Disj]
        exact Or.inr (Or.inr (Or.inl (by omega)))

def FreshTrie {F : Type} (s : PanSemStateFiniteExact 64 F)
    (mark : Nat) (wm : BitVec 64) (Nm : List Nat) : Prop :=
  mark + 16 ≤ globN s "heap_ptr" ∧
  sourceBase ≤ mark ∧
  mark % 8 = 0 ∧
  wm.toNat = mark ∧
  WordsOK s (mark, 16) ∧
  NodeHeap s Nm ∧
  NodeHeapValuePtrOK s Nm ∧
  RootIn Nm (memW s mark) ∧
  (∀ o ∈ nodeExtents s Nm, o = (0, 0) ∨ Inside o (mark + 16) (globN s "heap_ptr"))

theorem FreshTrie.with_locals_clock {F : Type} {s : PanSemStateFiniteExact 64 F}
    {mark : Nat} {wm : BitVec 64} {Nm : List Nat}
    (h : FreshTrie s mark wm Nm) (locs : HolFiniteMapExact MlS (ValueHOL 64)) (clk : Nat) :
    FreshTrie { s with locals := locs, clock := clk } mark wm Nm :=
  h

theorem lookup_mpt_new_bmi :
    originalRuntimeCode.lookup (ofString "mpt_new") =
      some ([(ofString "root_node", .one), (ofString "secured", .one)],
        sourceFnBody Guest.Software.guestFn_mpt_new, .one) :=
  lookup_of_guestAst_getElem 268 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_new) rfl

theorem lookup_mpt_root_bmi :
    originalRuntimeCode.lookup (ofString "mpt_root") =
      some ([(ofString "m", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_mpt_root, .one) :=
  lookup_of_guestAst_getElem 291 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_root) rfl

/-! ## 2. Local frame/alignment helpers for `mpt_set` on a `FreshTrie` -/

private theorem freeGap_aligned_bmi {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) : (freeGap s).1 % 8 = 0 ∧ (freeGap s).2 % 8 = 0 := by
  have hfm := hA.2.2.2.2.2.2.2.1
  have hsp := hA.2.2.2.2.2.2.2.2
  dsimp [freeGap]; exact ⟨hfm, by omega⟩

private theorem heapFree_aligned_bmi {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) : (heapFree s).1 % 8 = 0 ∧ (heapFree s).2 % 8 = 0 := by
  have hhp := hA.2.2.2.2.2.2.1
  have hhl : heapLimit % 8 = 0 := by decide
  dsimp [heapFree]; exact ⟨hhp, by omega⟩

private theorem ordinaryDomain_bounds_bmi {a : BitVec 64} (h : ordinaryDomain a) :
    a.toNat % 8 = 0 ∧ sourceBase ≤ a.toNat ∧ a.toNat < heapEnd := by
  rw [Wave8Contracts.M26.ordinaryDomain_iff] at h
  exact ⟨h.2.2, h.1, h.2.1⟩

private theorem cellHits_buf_to_pos_bmi {F : Type} {s : PanSemStateFiniteExact 64 F}
    {a : Nat} (ha_lo : sourceBase ≤ a) {name : String} {sz : Nat}
    (hsz_pos : 0 < sz) (hsz_hi : sz ≤ 200)
    (hhit : CellHits a (globN s name, sz)) :
    Fast_C08WkShard03.CellHitsPos a (bufferRegion s (name, sz)) := by
  have hsb : 208 < sourceBase := by decide
  by_cases hz : globN s name = 0
  · rw [hz] at hhit; dsimp [CellHits] at hhit; omega
  · refine ⟨by simp [bufferRegion, hz, hsz_pos], ?_⟩
    simpa [bufferRegion, hz] using hhit

private theorem cellHits_aligned_to_pos_bmi {a : Nat} (ha8 : a % 8 = 0) {ivl : Ivl}
    (hivl8 : ivl.1 % 8 = 0 ∧ ivl.2 % 8 = 0)
    (hhit : CellHits a ivl) :
    Fast_C08WkShard03.CellHitsPos a ivl := by
  obtain ⟨h1, h2⟩ := hhit
  obtain ⟨hi1, hi2⟩ := hivl8
  exact ⟨by omega, h1, h2⟩

private theorem inIvl_of_cellHitsPos_aligned_bmi {b : Nat} {ivl : Ivl}
    (hivl8 : ivl.1 % 8 = 0 ∧ ivl.2 % 8 = 0)
    (hhit : Fast_C08WkShard03.CellHitsPos (b / 8 * 8) ivl) :
    InIvl b ivl := by
  obtain ⟨_, hc1, hc2⟩ := hhit
  obtain ⟨hi1, hi2⟩ := hivl8
  unfold InIvl; omega

private theorem buf_keep_cond_of_disj_bmi {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hB : BmiScratchOK s) {ivl : Ivl} (hivl_lo : sourceBase ≤ ivl.1)
    (name : String) (sz : Nat) (hgs : (name, sz) ∈ bmiScratch)
    (hsz8 : sz % 8 = 0) (hsz_hi : sz + 8 ≤ sourceBase)
    (hdisj : Disj ivl (bufferRegion s (name, sz))) :
    (globN s name % 8 = 0 ∧ sz % 8 = 0 ∧ Disj ivl (globN s name, sz)) ∨
      globN s name + sz + 8 ≤ ivl.1 := by
  by_cases hz : globN s name = 0
  · right; rw [hz]; omega
  · left
    obtain ⟨_, hw⟩ := hB (name, sz) hgs hz
    refine ⟨hw.1, hsz8, ?_⟩
    simpa [bufferRegion, hz] using hdisj

private theorem nodeExtents_allocated_bmi {F : Type} {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (hN : NodeHeap s Nd) {o : Ivl} (ho : o ∈ nodeExtents s Nd) (ho0 : o.2 ≠ 0) :
    Allocated s o ∧ sourceBase ≤ o.1 := by
  unfold nodeExtents at ho
  rcases List.mem_flatMap.mp ho with ⟨n, hn, hmem⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  obtain ⟨_, hal_n, hin_n, _, _, _, hkey_n, _⟩ := hN.1 n hn
  rcases hmem with rfl | rfl
  · exact ⟨hal_n, hin_n.1⟩
  · unfold nodePath at ho0 ⊢
    split_ifs at ho0 ⊢ with hp
    · rcases hkey_n hp.1 with h0 | ⟨_, hal_p, hin_p, _⟩
      · exact absurd h0 hp.2
      · exact ⟨hal_p, hin_p.1⟩
    · exact absurd rfl ho0

private theorem nodeExtents_eq_of_unhit_bmi {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) {Nm : List Nat} (hN : NodeHeap s Nm)
    (hu : ∀ o ∈ nodeExtents s Nm, o.2 ≠ 0 → P3MptSet.IvlUnhit s post o) :
    nodeExtents post Nm = nodeExtents s Nm := by
  unfold nodeExtents
  apply List.flatMap_congr
  intro n hn
  obtain ⟨_, hal_n, _, hw_n, _⟩ := hN.1 n hn
  have hhi_n : n + nodeSize (memW s n) ≤ 2 ^ 64 := P3MptSet.ivl_allocated_bound hA.2 hal_n
  have hsz32 : 32 ≤ nodeSize (memW s n) := (R16Shards.nodeSize_bounds (memW s n)).1
  have hu_n : P3MptSet.IvlUnhit s post (n, nodeSize (memW s n)) :=
    hu _ (List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩) (by dsimp only; omega)
  have hw0 : memW post n = memW s n :=
    P3MptSet.memW_eq_of_ivlUnhit hu_n hw_n.1 hhi_n ⟨by omega, by omega⟩
  have hni : nodeIvl post n = nodeIvl s n := by simp [nodeIvl, hw0]
  have hnp : nodePath post n = nodePath s n := by
    unfold nodePath; rw [hw0]
    by_cases hk12 : memW s n = 1 ∨ memW s n = 2
    · have hsz56 : 56 ≤ nodeSize (memW s n) := by
        rcases hk12 with h1 | h2 <;> simp [nodeSize, *]
      have hn8 : n % 8 = 0 := hw_n.1
      have hw32 : memW post (n + 32) = memW s (n + 32) :=
        P3MptSet.memW_eq_of_ivlUnhit hu_n (by omega) hhi_n ⟨by omega, by omega⟩
      have hw40 : memW post (n + 40) = memW s (n + 40) :=
        P3MptSet.memW_eq_of_ivlUnhit hu_n (by omega) hhi_n ⟨by omega, by omega⟩
      rw [hw32, hw40]
    · simp only [hk12, false_and, ite_false]
  rw [hni, hnp]

private theorem nodeHeapValuePtrOK_congr_unhit_bmi {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    (hA : ArenaReady s) (hN : NodeHeap s Nd)
    (hglob : post.globals = s.globals)
    (hu : ∀ o ∈ nodeExtents s Nd, o.2 ≠ 0 → P3MptSet.IvlUnhit s post o)
    (hvs : NodeHeapValuePtrOK s Nd) :
    NodeHeapValuePtrOK post Nd := by
  have hw_node : ∀ n ∈ Nd, ∀ off : Nat, off % 8 = 0 → off + 8 ≤ nodeSize (memW s n) →
      memW post (n + off) = memW s (n + off) := by
    intro n hn off hoff8 hoff_lt
    obtain ⟨_, hal_n, _, hw_n, _⟩ := hN.1 n hn
    have hhi_n : n + nodeSize (memW s n) ≤ 2 ^ 64 := P3MptSet.ivl_allocated_bound hA.2 hal_n
    have hn8 : n % 8 = 0 := hw_n.1
    have hu_n : P3MptSet.IvlUnhit s post (n, nodeSize (memW s n)) :=
      hu _ (List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩)
        (by have := (R16Shards.nodeSize_bounds (memW s n)).1; dsimp only; omega)
    exact P3MptSet.memW_eq_of_ivlUnhit hu_n (by omega) hhi_n ⟨by omega, by omega⟩
  have hfg_eq : freeGapTo (globN post "scratch_ptr") post = freeGapTo (globN s "scratch_ptr") s := by
    unfold freeGapTo globN; rw [hglob]
  have hhf_eq : heapFree post = heapFree s := by unfold heapFree globN; rw [hglob]
  have hkc_eq : keccakBufIvls post = keccakBufIvls s := by
    unfold keccakBufIvls bufferRegion globN; rw [hglob]
  intro n hn
  obtain ⟨h1_s, h3_s⟩ := hvs n hn
  have h0_eq : memW post n = memW s n := by
    have hsz32 := (R16Shards.nodeSize_bounds (memW s n)).1
    simpa using hw_node n hn 0 (by simp) (by omega)
  refine ⟨fun hk1 hvl1 hdom => ?_, fun hk3 hvl3 hdom => ?_⟩
  · rw [h0_eq] at hk1
    have h48 := hw_node n hn 48 (by decide) (by rw [hk1]; decide)
    have h56 := hw_node n hn 56 (by decide) (by rw [hk1]; decide)
    rw [h48] at hdom ⊢; rw [h56] at hvl1
    obtain ⟨hc, hkc, hfg, hhf⟩ := h1_s hk1 hvl1 hdom
    exact ⟨hc, hkc_eq ▸ hkc, hfg_eq ▸ hfg, hhf_eq ▸ hhf⟩
  · rw [h0_eq] at hk3
    have h160 := hw_node n hn 160 (by decide) (by rw [hk3]; decide)
    have h168 := hw_node n hn 168 (by decide) (by rw [hk3]; decide)
    rw [h160] at hdom ⊢; rw [h168] at hvl3
    obtain ⟨hc, hkc, hfg, hhf⟩ := h3_s hk3 hvl3 hdom
    exact ⟨hc, hkc_eq ▸ hkc, hfg_eq ▸ hfg, hhf_eq ▸ hhf⟩

private theorem nk_preserves_fresh_bmi {F : Type} {s post_nk : PanSemStateFiniteExact 64 F}
    {mark : Nat} {Nm : List Nat}
    (hA : ArenaReady s) (hA_nk : ArenaReady post_nk)
    (hB : BmiScratchOK s)
    (hbe : post_nk.be = s.be)
    (hag : AllocatorGrows s post_nk)
    (hsp_eq : globN post_nk "scratch_ptr" = globN s "scratch_ptr")
    (hfm_eq : globN post_nk "frame_mem_ptr" = globN s "frame_mem_ptr")
    (hkc_eq : keccakBufIvls post_nk = keccakBufIvls s)
    (hfr : FrameOutside s post_nk
      ([(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_hash_scratch", 40)] ++
        [freeGap s])
      (heapFree s))
    (hm_al : Allocated s (mark, 16))
    (hm_w : WordsOK s (mark, 16))
    (hN : NodeHeap s Nm)
    (hN_vs : NodeHeapValuePtrOK s Nm)
    (hext_buf : ∀ o ∈ nodeExtents s Nm, ∀ gs ∈ bmiScratch, Disj o (bufferRegion s gs))
    (hm_buf : ∀ gs ∈ bmiScratch, Disj (mark, 16) (bufferRegion s gs)) :
    memW post_nk mark = memW s mark ∧
    NodeHeap post_nk Nm ∧
    NodeHeapValuePtrOK post_nk Nm ∧
    nodeExtents post_nk Nm = nodeExtents s Nm ∧
    (∀ n ∈ Nm, nodeIvl post_nk n = nodeIvl s n) := by
  have hgap_al := freeGap_aligned_bmi hA
  have hhf_al := heapFree_aligned_bmi hA
  have hm_lo : sourceBase ≤ mark := by
    rcases hm_al with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · have : sourceBase ≤ scratchStart := by decide
      have := hA.2.2.2.1; have := hA.2.2.2.2.1; omega
  have hm_unhit : P3MptSet.IvlUnhit s post_nk (mark, 16) := by
    apply P3MptSet.ivlUnhit_of_frameOutside hfr ?_ hhf_al
      (P3MptSet.disj_allocated_heapFree hA.2 hm_al) (by simp)
    intro j hj
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with (rfl | rfl | rfl) | rfl
    · exact buf_keep_cond_of_disj_bmi hB hm_lo "keccak_pad" 136 (by simp [bmiScratch]) (by decide) (by decide)
        (hm_buf ("keccak_pad", 136) (by simp [bmiScratch]))
    · exact buf_keep_cond_of_disj_bmi hB hm_lo "keccak_st" 200 (by simp [bmiScratch]) (by decide) (by decide)
        (hm_buf ("keccak_st", 200) (by simp [bmiScratch]))
    · exact buf_keep_cond_of_disj_bmi hB hm_lo "mpt_hash_scratch" 40 (by simp [bmiScratch]) (by decide) (by decide)
        (hm_buf ("mpt_hash_scratch", 40) (by simp [bmiScratch]))
    · exact Or.inl ⟨hgap_al.1, hgap_al.2, P3MptSet.disj_allocated_freeGap hA.2 hm_al⟩
  have hm_memW : memW post_nk mark = memW s mark :=
    P3MptSet.memW_eq_of_ivlUnhit hm_unhit hm_w.1 (P3MptSet.ivl_allocated_bound hA.2 hm_al) ⟨by omega, by omega⟩
  have hext_unhit : ∀ o ∈ nodeExtents s Nm, o.2 ≠ 0 → P3MptSet.IvlUnhit s post_nk o := by
    intro o ho ho0
    obtain ⟨hal_o, ho_lo⟩ := nodeExtents_allocated_bmi hN ho ho0
    have ho_buf := hext_buf o ho
    apply P3MptSet.ivlUnhit_of_frameOutside hfr ?_ hhf_al
      (P3MptSet.disj_allocated_heapFree hA.2 hal_o) ho0
    intro j hj
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with (rfl | rfl | rfl) | rfl
    · exact buf_keep_cond_of_disj_bmi hB ho_lo "keccak_pad" 136 (by simp [bmiScratch]) (by decide) (by decide)
        (ho_buf ("keccak_pad", 136) (by simp [bmiScratch]))
    · exact buf_keep_cond_of_disj_bmi hB ho_lo "keccak_st" 200 (by simp [bmiScratch]) (by decide) (by decide)
        (ho_buf ("keccak_st", 200) (by simp [bmiScratch]))
    · exact buf_keep_cond_of_disj_bmi hB ho_lo "mpt_hash_scratch" 40 (by simp [bmiScratch]) (by decide) (by decide)
        (ho_buf ("mpt_hash_scratch", 40) (by simp [bmiScratch]))
    · exact Or.inl ⟨hgap_al.1, hgap_al.2, P3MptSet.disj_allocated_freeGap hA.2 hal_o⟩
  have hNm_nk : NodeHeap post_nk Nm :=
    P3MptSet.nodeHeap_congr_unhit hA.1 hA_nk.1 hbe hag hN hext_unhit
  have hext_eq : nodeExtents post_nk Nm = nodeExtents s Nm :=
    nodeExtents_eq_of_unhit_bmi hA hN hext_unhit
  have hw_node : ∀ n ∈ Nm, ∀ off : Nat, off % 8 = 0 → off + 8 ≤ nodeSize (memW s n) →
      memW post_nk (n + off) = memW s (n + off) := by
    intro n hn off hoff8 hoff_lt
    obtain ⟨_, hal_n, _, hw_n, _⟩ := hN.1 n hn
    have hhi_n : n + nodeSize (memW s n) ≤ 2 ^ 64 := P3MptSet.ivl_allocated_bound hA.2 hal_n
    have hn8 : n % 8 = 0 := hw_n.1
    have hu_n : P3MptSet.IvlUnhit s post_nk (n, nodeSize (memW s n)) :=
      hext_unhit _ (List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩)
        (by have := (R16Shards.nodeSize_bounds (memW s n)).1; dsimp only; omega)
    exact P3MptSet.memW_eq_of_ivlUnhit hu_n (by omega) hhi_n ⟨by omega, by omega⟩
  have hni_eq : ∀ n ∈ Nm, nodeIvl post_nk n = nodeIvl s n := by
    intro n hn
    have hsz32 := (R16Shards.nodeSize_bounds (memW s n)).1
    have hw0 : memW post_nk n = memW s n := by simpa using hw_node n hn 0 (by simp) (by omega)
    simp [nodeIvl, hw0]
  have hfg_eq : freeGapTo (globN post_nk "scratch_ptr") post_nk = freeGapTo (globN s "scratch_ptr") s := by
    simp [freeGapTo, hfm_eq, hsp_eq]
  have hhf_sub : ∀ b, InIvl b (heapFree post_nk) → InIvl b (heapFree s) := by
    intro b ⟨h1, h2⟩; have := hag.1; dsimp [heapFree] at h1 h2 ⊢; exact ⟨by omega, by omega⟩
  have hvs_nk : NodeHeapValuePtrOK post_nk Nm := by
    intro n hn
    obtain ⟨h1_s, h3_s⟩ := hN_vs n hn
    have h0_eq : memW post_nk n = memW s n := by
      have hsz32 := (R16Shards.nodeSize_bounds (memW s n)).1
      simpa using hw_node n hn 0 (by simp) (by omega)
    refine ⟨fun hk1 hvl1 hdom => ?_, fun hk3 hvl3 hdom => ?_⟩
    · rw [h0_eq] at hk1
      have h48 := hw_node n hn 48 (by decide) (by rw [hk1]; decide)
      have h56 := hw_node n hn 56 (by decide) (by rw [hk1]; decide)
      rw [h48] at hdom ⊢; rw [h56] at hvl1
      obtain ⟨hc, hkc, hfg, hhf⟩ := h1_s hk1 hvl1 hdom
      exact ⟨hc, hkc_eq ▸ hkc, hfg_eq ▸ hfg, fun h => hhf (hhf_sub _ h)⟩
    · rw [h0_eq] at hk3
      have h160 := hw_node n hn 160 (by decide) (by rw [hk3]; decide)
      have h168 := hw_node n hn 168 (by decide) (by rw [hk3]; decide)
      rw [h160] at hdom ⊢; rw [h168] at hvl3
      obtain ⟨hc, hkc, hfg, hhf⟩ := h3_s hk3 hvl3 hdom
      exact ⟨hc, hkc_eq ▸ hkc, hfg_eq ▸ hfg, fun h => hhf (hhf_sub _ h)⟩
  exact ⟨hm_memW, hNm_nk, hvs_nk, hext_eq, hni_eq⟩

private theorem nk_cell_frame_bmi {F : Type} {s post_nk : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s)
    (hfr : FrameOutside s post_nk
      ([(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_hash_scratch", 40)] ++
        [freeGap s])
      (heapFree s))
    (hdom : ∀ a : BitVec 64, post_nk.memory a ≠ s.memory a → s.memaddrs a)
    {a : BitVec 64} (hne : post_nk.memory a ≠ s.memory a) :
    (∃ gs ∈ bmiScratch, Fast_C08WkShard03.CellHitsPos a.toNat (bufferRegion s gs)) ∨
    Fast_C08WkShard03.CellHitsPos a.toNat (freeGap s) ∨
    Fast_C08WkShard03.CellHitsPos a.toNat (heapFree s) := by
  have hord : ordinaryDomain a := by
    have hm := hdom a hne; rwa [hA.1.memaddrs] at hm
  obtain ⟨ha8, ha_lo, _⟩ := ordinaryDomain_bounds_bmi hord
  by_contra hnone
  have hnoB : ∀ gs ∈ bmiScratch, ¬ Fast_C08WkShard03.CellHitsPos a.toNat (bufferRegion s gs) :=
    fun gs hgs h => hnone (Or.inl ⟨gs, hgs, h⟩)
  have hnoFg : ¬ Fast_C08WkShard03.CellHitsPos a.toNat (freeGap s) :=
    fun h => hnone (Or.inr (Or.inl h))
  have hnoHf : ¬ Fast_C08WkShard03.CellHitsPos a.toNat (heapFree s) :=
    fun h => hnone (Or.inr (Or.inr h))
  apply hne
  apply hfr a
  · intro j hj hcj
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with (rfl | rfl | rfl) | rfl
    · exact hnoB ("keccak_pad", 136) (by simp [bmiScratch])
        (cellHits_buf_to_pos_bmi ha_lo (by decide) (by decide) hcj)
    · exact hnoB ("keccak_st", 200) (by simp [bmiScratch])
        (cellHits_buf_to_pos_bmi ha_lo (by decide) (by decide) hcj)
    · exact hnoB ("mpt_hash_scratch", 40) (by simp [bmiScratch])
        (cellHits_buf_to_pos_bmi ha_lo (by decide) (by decide) hcj)
    · exact hnoFg (cellHits_aligned_to_pos_bmi ha8 (freeGap_aligned_bmi hA) hcj)
  · intro hcf
    exact hnoHf (cellHits_aligned_to_pos_bmi ha8 (heapFree_aligned_bmi hA) hcf)

private theorem nodeStep_cell_frame_bmi {F : Type} {s s_nk s_call : PanSemStateFiniteExact 64 F}
    {Nm Nm' : List Nat}
    (hA : ArenaReady s) (hA_nk : ArenaReady s_nk)
    (hhp_nk : globN s "heap_ptr" ≤ globN s_nk "heap_ptr")
    (hfg_eq : freeGap s_nk = freeGap s)
    (hni_eq : ∀ n ∈ Nm, nodeIvl s_nk n = nodeIvl s n)
    (hN : NodeHeap s Nm)
    (hstep : R16Shards.NodeStep s_nk s_call Nm Nm')
    {a : BitVec 64} (ha8 : a.toNat % 8 = 0)
    (hne : s_call.memory a ≠ s_nk.memory a) :
    (∃ n ∈ Nm, Fast_C08WkShard03.CellHitsPos a.toNat (nodeIvl s n)) ∨
    Fast_C08WkShard03.CellHitsPos a.toNat (freeGap s) ∨
    Fast_C08WkShard03.CellHitsPos a.toNat (heapFree s) := by
  by_contra hnone
  have hnoN : ∀ n ∈ Nm, ¬ Fast_C08WkShard03.CellHitsPos a.toNat (nodeIvl s n) :=
    fun n hn h => hnone (Or.inl ⟨n, hn, h⟩)
  have hnoFg : ¬ Fast_C08WkShard03.CellHitsPos a.toNat (freeGap s) :=
    fun h => hnone (Or.inr (Or.inl h))
  have hnoHf : ¬ Fast_C08WkShard03.CellHitsPos a.toNat (heapFree s) :=
    fun h => hnone (Or.inr (Or.inr h))
  apply hne
  apply hstep.frame a
  · intro j hj hcj
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hj
    rcases hj with ⟨n, hn, rfl⟩ | hjfg
    · rw [hni_eq n hn] at hcj
      obtain ⟨_, _, _, hw_n, _⟩ := hN.1 n hn
      have hni8 : (nodeIvl s n).1 % 8 = 0 ∧ (nodeIvl s n).2 % 8 = 0 :=
        ⟨hw_n.1, (R16Shards.nodeSize_bounds (memW s n)).2.2⟩
      exact hnoN n hn (cellHits_aligned_to_pos_bmi ha8 hni8 hcj)
    · change j = freeGap s_nk at hjfg
      rw [hjfg, hfg_eq] at hcj
      exact hnoFg (cellHits_aligned_to_pos_bmi ha8 (freeGap_aligned_bmi hA) hcj)
  · intro hcf
    have hhp_hi_nk : globN s_nk "heap_ptr" ≤ heapLimit := hA_nk.2.2.1
    have hhp8_nk : globN s_nk "heap_ptr" % 8 = 0 := hA_nk.2.2.2.2.2.2.1
    have hhl8 : heapLimit % 8 = 0 := by decide
    have hhf_sub : CellHits a.toNat (heapFree s) := by
      dsimp [heapFree, CellHits] at hcf ⊢; omega
    exact hnoHf (cellHits_aligned_to_pos_bmi ha8 (heapFree_aligned_bmi hA) hhf_sub)

private theorem nk_keyIn_nm_bmi {F : Type} {s post_nk : PanSemStateFiniteExact 64 F}
    {Nm : List Nat} {p l : BitVec 64}
    (hA : ArenaReady s) (hA_nk : ArenaReady post_nk)
    (hnib : NibblesOK post_nk p.toNat l.toNat)
    (hin_fresh : Inside (p.toNat, l.toNat) (globN s "heap_ptr") (globN post_nk "heap_ptr"))
    (hN : NodeHeap s Nm)
    (hni_eq : ∀ n ∈ Nm, nodeIvl post_nk n = nodeIvl s n) :
    KeyIn post_nk Nm p.toNat l.toNat := by
  by_cases hl0 : l.toNat = 0
  · exact Or.inl hl0
  · right
    have hin_hp : Inside (p.toNat, l.toNat) sourceBase (globN post_nk "heap_ptr") :=
      ⟨Nat.le_trans hA.2.1 hin_fresh.1, hin_fresh.2⟩
    have hin_lim : Inside (p.toNat, l.toNat) sourceBase heapLimit :=
      ⟨hin_hp.1, Nat.le_trans hin_fresh.2 hA_nk.2.2.1⟩
    refine ⟨hnib, Or.inl hin_hp, hin_lim, ?_⟩
    intro n hn
    obtain ⟨_, hal_n, _, _⟩ := hN.1 n hn
    have hn_old_in : Inside (nodeIvl s n) sourceBase (globN s "heap_ptr") := by
      rcases hal_n with h1 | h2
      · exact h1
      · have : heapLimit ≤ scratchStart := by decide
        have := hA.2.2.2.1; have := hA.2.2.2.2.1
        have hsz := (R16Shards.nodeSize_bounds (memW s n)).1
        dsimp [Inside, nodeIvl] at *; omega
    rw [hni_eq n hn]
    exact Or.inr (Or.inr (Or.inr (Nat.le_trans hn_old_in.2 hin_fresh.1)))

private theorem ext_extents_combine_bmi {F : Type} {s s_nk s_call : PanSemStateFiniteExact 64 F}
    {Nm Nm' : List Nat} {p l : BitVec 64}
    (hhp_nk : globN s "heap_ptr" ≤ globN s_nk "heap_ptr")
    (hhp_call : globN s_nk "heap_ptr" ≤ globN s_call "heap_ptr")
    (hin_pl : Inside (p.toNat, l.toNat) (globN s "heap_ptr") (globN s_nk "heap_ptr"))
    (hext_eq : nodeExtents s_nk Nm = nodeExtents s Nm)
    (hext : ExtNodeStep [(p.toNat, l.toNat)] s_nk s_call Nm Nm') :
    ∀ o ∈ nodeExtents s_call Nm',
      o = (0, 0) ∨
      (∃ j ∈ nodeExtents s Nm, Inside o j.1 (j.1 + j.2)) ∨
      Inside o (globN s "heap_ptr") (globN s_call "heap_ptr") := by
  intro o ho
  rcases hext.2 o ho with hz | ⟨j, hj, hin⟩ | hf
  · exact Or.inl hz
  · simp only [List.singleton_append, List.mem_cons] at hj
    rcases hj with rfl | hjN
    · right; right; dsimp [Inside] at hin hin_pl ⊢; omega
    · rw [hext_eq] at hjN
      exact Or.inr (Or.inl ⟨j, hjN, hin⟩)
  · right; right; dsimp [Inside] at hf ⊢; omega

private theorem m_unhit_across_nodeStep_bmi {F : Type} {s s_nk s_call : PanSemStateFiniteExact 64 F}
    {mark : Nat} {Nm Nm' : List Nat}
    (hA : ArenaReady s) (hA_nk : ArenaReady s_nk)
    (hhp_nk : globN s "heap_ptr" ≤ globN s_nk "heap_ptr")
    (hfg_eq : freeGap s_nk = freeGap s)
    (hni_eq : ∀ n ∈ Nm, nodeIvl s_nk n = nodeIvl s n)
    (hm_al : Allocated s (mark, 16))
    (hm_w : WordsOK s (mark, 16))
    (hN : NodeHeap s Nm)
    (hext_disj : ∀ o ∈ nodeExtents s Nm, Disj o (mark, 16))
    (hstep : R16Shards.NodeStep s_nk s_call Nm Nm') :
    memW s_call mark = memW s_nk mark := by
  have hm_hi := P3MptSet.ivl_allocated_bound hA.2 hm_al
  have hm8 : mark % 8 = 0 := hm_w.1
  have hu : P3MptSet.IvlUnhit s_nk s_call (mark, 16) := by
    intro a ha8 hhit
    by_contra hne
    rcases nodeStep_cell_frame_bmi hA hA_nk hhp_nk hfg_eq hni_eq hN hstep ha8 hne with
      ⟨n, hn, hcp⟩ | hcp | hcp
    · have hdm : Disj (nodeIvl s n) (mark, 16) :=
        hext_disj _ (List.mem_flatMap.2 ⟨n, hn, by simp⟩)
      obtain ⟨_, hc1, hc2⟩ := hcp; obtain ⟨hh1, hh2⟩ := hhit
      rcases hdm with hd | hd | hd | hd <;> omega
    · have hdfg := P3MptSet.disj_allocated_freeGap hA.2 hm_al
      obtain ⟨_, hc1, hc2⟩ := hcp; obtain ⟨hh1, hh2⟩ := hhit
      change Disj (mark, 16) (freeGap s) at hdfg
      rcases hdfg with hd | hd | hd | hd <;> omega
    · have hdhf := P3MptSet.disj_allocated_heapFree hA.2 hm_al
      obtain ⟨_, hc1, hc2⟩ := hcp; obtain ⟨hh1, hh2⟩ := hhit
      change Disj (mark, 16) (heapFree s) at hdhf
      rcases hdhf with hd | hd | hd | hd <;> omega
  exact P3MptSet.memW_eq_of_ivlUnhit hu hm8 hm_hi ⟨by omega, by omega⟩

private theorem dec_resumes_inv_bmi {F : Type}
    {s : PanSemStateFiniteExact 64 F} {x : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {b : ProgHOL 64}
    (hres : Resumes (evaluateHOLFiniteState s (.dec x sh e b)).1) :
    ∃ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v ∧
      shapeEqHOL sh (shapeOfHOLExact v) = true ∧
      Resumes (evaluateHOLFiniteState (setVarHOLFinite x v s) b).1 ∧
      (evaluateHOLFiniteState s (.dec x sh e b)).1 =
        (evaluateHOLFiniteState (setVarHOLFinite x v s) b).1 ∧
      (evaluateHOLFiniteState s (.dec x sh e b)).2 =
        { (evaluateHOLFiniteState (setVarHOLFinite x v s) b).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState (setVarHOLFinite x v s) b).2.locals
            (x, s.locals.lookup x) } := by
  have hd := evaluateHOLFiniteState_dec_total s x sh e b
  dsimp only at hd
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | v
  · rw [hd, hev] at hres; exact absurd hres R16Shards.not_resumes_error
  · rw [hev] at hd; dsimp only at hd
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact v) = true
    · rw [if_pos hsh] at hd; rw [hd] at hres ⊢; exact ⟨v, rfl, hsh, hres, rfl, rfl⟩
    · rw [if_neg hsh] at hd; rw [hd] at hres; exact absurd hres R16Shards.not_resumes_error

private theorem seq_flow_or_resumes_bmi {F : Type}
    {s : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (hres : Resumes (evaluateHOLFiniteState s (.seq a b)).1) :
    ((evaluateHOLFiniteState s a).1 = none ∧
      Resumes (evaluateHOLFiniteState (evaluateHOLFiniteState s a).2 b).1 ∧
      evaluateHOLFiniteState s (.seq a b) = evaluateHOLFiniteState (evaluateHOLFiniteState s a).2 b) ∨
    (Resumes (evaluateHOLFiniteState s a).1 ∧
      evaluateHOLFiniteState s (.seq a b) = evaluateHOLFiniteState s a) := by
  have hs := evaluateHOLFiniteState_seq_line780 s a b
  dsimp only at hs
  rcases ha : evaluateHOLFiniteState s a with ⟨ra, sa⟩
  rw [ha] at hs
  cases ra with
  | none =>
    dsimp only at hs
    exact Or.inl ⟨rfl, hs ▸ hres, hs⟩
  | some r0 =>
    dsimp only at hs
    exact Or.inr ⟨hs ▸ hres, hs⟩

private theorem ite_flow_or_exn_bmi {F : Type}
    {s : PanSemStateFiniteExact 64 F} {cond : ExpHOL 64} {tb eb : ProgHOL 64}
    (h : (evaluateHOLFiniteState s (.ite cond tb eb)).1 = none ∨
         Resumes (evaluateHOLFiniteState s (.ite cond tb eb)).1) :
    ∃ cw : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word cw)) ∧
      ((cw ≠ 0 ∧ evaluateHOLFiniteState s (.ite cond tb eb) = evaluateHOLFiniteState s tb) ∨
       (cw = 0 ∧ evaluateHOLFiniteState s (.ite cond tb eb) = evaluateHOLFiniteState s eb)) := by
  have hite := evaluateHOLFiniteState_ite s cond tb eb
  have hnot_err : (evaluateHOLFiniteState s (.ite cond tb eb)).1 ≠ some .error := by
    intro herr; rcases h with hn | hr
    · rw [herr] at hn; cases hn
    · rw [herr] at hr; exact R16Shards.not_resumes_error hr
  rcases hcv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | cv
  · exfalso; apply hnot_err; rw [hite, hcv]
  · rcases cv with x | fs | ⟨nm, fs⟩
    · cases x with
      | word cw =>
        rw [hcv] at hite; dsimp only at hite
        refine ⟨cw, rfl, ?_⟩
        by_cases h0 : cw = 0
        · rw [if_pos h0] at hite; exact Or.inr ⟨h0, hite⟩
        · rw [if_neg h0] at hite; exact Or.inl ⟨h0, hite⟩
    · exfalso; apply hnot_err; rw [hite, hcv]
    · exfalso; apply hnot_err; rw [hite, hcv]

private theorem store_return_zero_resumes_bmi {F : Type}
    {s : PanSemStateFiniteExact 64 F} {wm wroot : BitVec 64}
    (hlk_m : s.locals.lookup (ofString "m") = some (.val (.word wm)))
    (hlk_root : s.locals.lookup (ofString "root") = some (.val (.word wroot)))
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local (ofString "m"), .const 0]) (.var .local (ofString "root")))
            (.return (.const 0)))).1) :
    s.memaddrs wm ∧
    (evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local (ofString "m"), .const 0]) (.var .local (ofString "root")))
            (.return (.const 0)))).2 =
      { s with memory := fun a => if a = wm then .word wroot else s.memory a, locals := HolFiniteMapExact.empty } := by
  obtain ⟨mid, hst, hseq⟩ := R16Shards.seq_store_resumes hres
  rw [evaluateHOLFiniteState_store] at hst
  have hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "m"), .const 0]) = some (.val (.word wm)) := by
    simp [evalHOLExact, evalListHOLExact, hlk_m, valueIsWord, valueWord, wordOpHOL, wordOp]
  have hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "root")) = some (.val (.word wroot)) := by
    simp [evalHOLExact, hlk_root]
  rw [hdst, hsrc] at hst
  simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hst
  by_cases hdom : s.memaddrs wm
  · simp only [hdom, ↓reduceIte, Prod.mk.injEq, reduceCtorEq, false_and] at hst
    rcases hst with ⟨-, hmid_eq⟩
    subst hmid_eq
    refine ⟨hdom, ?_⟩
    rw [hseq, evaluateHOLFiniteState_return]
    simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, ↓reduceIte]
    rfl
  · simp [hdom] at hst

private theorem nodeHeap_preserve_single_store_bmi {F : Type}
    {s : PanSemStateFiniteExact 64 F} {Nd : List Nat} {wm wval : BitVec 64}
    (hA : ArenaReady s) (hNd : NodeHeap s Nd) (hvs : NodeHeapValuePtrOK s Nd)
    (hdisj : ∀ o ∈ nodeExtents s Nd, Disj o (wm.toNat, 16)) :
    let post : PanSemStateFiniteExact 64 F :=
      { s with memory := fun a => if a = wm then .word wval else s.memory a,
               locals := HolFiniteMapExact.empty }
    ArenaReady post ∧ NodeHeap post Nd ∧ NodeHeapValuePtrOK post Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  intro post
  have hmem_ar : ArenaReady { s with memory := fun a => if a = wm then .word wval else s.memory a } :=
    ⟨guestInv_congr (s := s) rfl rfl rfl rfl hA.1, hA.2⟩
  have hApost : ArenaReady post :=
    R16Shards.localsFree_arenaReady _ HolFiniteMapExact.empty s.clock hmem_ar
  have hag : AllocatorGrows s post := ⟨le_rfl, le_rfl⟩
  have hu : ∀ o ∈ nodeExtents s Nd, o.2 ≠ 0 → P3MptSet.IvlUnhit s post o := by
    intro o ho ho0 a ha8 hhit
    have hdo := hdisj o ho
    have hne : a ≠ wm := by
      intro heq; subst heq
      obtain ⟨hc1, hc2⟩ := hhit
      rcases hdo with hd | hd | hd | hd <;> omega
    dsimp [post]; rw [if_neg hne]
  exact ⟨hApost, P3MptSet.nodeHeap_congr_unhit hA.1 hApost.1 rfl hag hNd hu,
         nodeHeapValuePtrOK_congr_unhit_bmi hA hNd rfl hu hvs,
         nodeExtents_eq_of_unhit_bmi hA hNd hu⟩

private theorem globN_eq_of_lookup_bmi {F : Type} {s post : PanSemStateFiniteExact 64 F} {g : String}
    (h : post.globals.lookup (ofString g) = s.globals.lookup (ofString g)) :
    globN post g = globN s g := by
  simp [globN, h]

/-! ## 3. `mpt_set_body_fresh` and `eval_call_mpt_set_fresh` -/

theorem mpt_set_body_fresh {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (mark : Nat) (wm wkey wklen wvptr wvlen : BitVec 64) (Nm : List Nat)
    (hcode : s.code = originalRuntimeCode)
    (hA : ArenaReady s)
    (hB : BmiScratchOK s)
    (hB_pre : ∀ gs ∈ bmiScratch, globN s gs.1 ≠ 0 →
      globN s gs.1 + gs.2 ≤ mark ∨ globN s "scratch_ptr" ≤ globN s gs.1)
    (hFT : FreshTrie s mark wm Nm)
    (hlk_m : s.locals.lookup (ofString "m") = some (.val (.word wm)))
    (hlk_key : s.locals.lookup (ofString "key") = some (.val (.word wkey)))
    (hlk_klen : s.locals.lookup (ofString "klen") = some (.val (.word wklen)))
    (hlk_vptr : s.locals.lookup (ofString "vptr") = some (.val (.word wvptr)))
    (hlk_vlen : s.locals.lookup (ofString "vlen") = some (.val (.word wvlen)))
    (hklen_le : wklen.toNat ≤ 32)
    (hvlen_lt : wvlen.toNat < 2 ^ 40)
    (hv_safe : ValuePtrSafe s Nm wvptr.toNat wvlen.toNat)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mpt_set)).1) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mpt_set)).2
    ∃ Nm',
      HeapByteEff s post
        ([(mark, 16)] ++ Nm.map (nodeIvl s) ++ bmiScratch.map (bufferRegion s))
        ["heap_ptr", "scratch_ptr"] ∧
      FreshTrie post mark wm Nm' := by
  intro post
  set body := sourceFnBody Guest.Software.guestFn_mpt_set
  obtain ⟨hmark_hp, hmark_lo, hmark8, hwm_nat, hm_w, hN, hvs, hm_root, hext_in⟩ := hFT
  have hwm_loc : locN s "m" = mark := by simp [locN, hlk_m, hwm_nat]
  have hm_al : Allocated s (mark, 16) := Or.inl ⟨hmark_lo, hmark_hp⟩
  have hm_buf : ∀ gs ∈ bmiScratch, Disj (mark, 16) (bufferRegion s gs) :=
    bmiScratch_disj_fresh hA hB hmark_lo hB_pre (Or.inr ⟨le_rfl, hmark_hp⟩)
  have hext_buf : ∀ o ∈ nodeExtents s Nm, ∀ gs ∈ bmiScratch, Disj o (bufferRegion s gs) := by
    intro o ho
    apply bmiScratch_disj_fresh hA hB hmark_lo hB_pre
    rcases hext_in o ho with rfl | ⟨h1, h2⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨by omega, h2⟩
  have hext_disj_m : ∀ o ∈ nodeExtents s Nm, Disj o (mark, 16) := by
    intro o ho
    rcases hext_in o ho with rfl | ⟨h1, _⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr h1))
  have hB_al : ∀ gs ∈ bmiScratch, (bufferRegion s gs).2 = 0 ∨
      ((bufferRegion s gs).1 % 8 = 0 ∧ (bufferRegion s gs).2 % 8 = 0) := by
    intro gs hgs
    by_cases hz : globN s gs.1 = 0
    · exact Or.inl (by simp [bufferRegion, hz])
    · obtain ⟨_, hw⟩ := hB gs hgs hz
      have hsz8 : gs.2 % 8 = 0 := by
        simp only [bmiScratch, List.mem_cons, List.not_mem_nil, or_false] at hgs
        rcases hgs with rfl | rfl | rfl | rfl <;> decide
      exact Or.inr (by simpa [bufferRegion, hz] using And.intro hw.1 hsz8)
  have hdom_wr : ∀ a : BitVec 64, post.memory a ≠ s.memory a → s.memaddrs a := by
    intro a hne; by_contra hna
    exact hne (evaluate_memory_eq_of_not_memaddrs s body a hna)
  have hbe_post : post.be = s.be :=
    (PanRunBounded.evaluateHOLFiniteState_metadata s body).2.2.1
  have hmemaddrs_post : post.memaddrs = s.memaddrs :=
    (PanRunBounded.evaluateHOLFiniteState_metadata s body).2.1
  set Rl := [(mark, 16)] ++ Nm.map (nodeIvl s) ++ bmiScratch.map (bufferRegion s)
  have hcell_to_byte :
      (∀ a : BitVec 64, post.memory a ≠ s.memory a →
        (∃ i ∈ Rl, Fast_C08WkShard03.CellHitsPos a.toNat i) ∨
        Fast_C08WkShard03.CellHitsPos a.toNat (freeGap s) ∨
        Fast_C08WkShard03.CellHitsPos a.toNat (heapFree s)) →
      ∀ b : Nat, b < 2 ^ 64 → memB post b ≠ memB s b →
        (∃ i ∈ Rl, InIvl b i) ∨ InIvl b (freeGap s) ∨ InIvl b (heapFree s) := by
    intro hcell b hb hne_b
    let ca : BitVec 64 := BitVec.ofNat 64 (b / 8 * 8)
    have hca_lt : b / 8 * 8 < 2 ^ 64 := lt_of_le_of_lt (Nat.div_mul_le_self b 8) hb
    have hca_nat : ca.toNat = b / 8 * 8 := by
      dsimp [ca]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hca_lt]
    have hne_c : post.memory ca ≠ s.memory ca :=
      fun heq => hne_b (memB_eq_of_align_cell_eq hb heq hbe_post)
    rcases hcell ca hne_c with ⟨iv, hiv, hcp⟩ | hcp | hcp
    · rw [hca_nat] at hcp
      have hiv' : iv = (mark, 16) ∨ (∃ n ∈ Nm, nodeIvl s n = iv) ∨ (∃ gs ∈ bmiScratch, bufferRegion s gs = iv) := by
        simpa only [Rl, List.singleton_append, List.mem_cons, List.mem_append, List.mem_map, or_assoc] using hiv
      rcases hiv' with rfl | ⟨n, hn, rfl⟩ | ⟨gs, hgs, rfl⟩
      · exact Or.inl ⟨(mark, 16), by simp [Rl],
          inIvl_of_cellHitsPos_aligned_bmi ⟨hmark8, show (16 : Nat) % 8 = 0 by decide⟩ hcp⟩
      · obtain ⟨_, _, _, hw_n, _⟩ := hN.1 n hn
        have hni8 : (nodeIvl s n).1 % 8 = 0 ∧ (nodeIvl s n).2 % 8 = 0 :=
          ⟨hw_n.1, (R16Shards.nodeSize_bounds (memW s n)).2.2⟩
        have hmem_n : nodeIvl s n ∈ Rl := List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2 ⟨n, hn, rfl⟩))
        exact Or.inl ⟨nodeIvl s n, hmem_n, inIvl_of_cellHitsPos_aligned_bmi hni8 hcp⟩
      · rcases hB_al gs hgs with hz | hal
        · exact absurd hcp.1 (by omega)
        · have hmem_gs : bufferRegion s gs ∈ Rl := List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨gs, hgs, rfl⟩))
          exact Or.inl ⟨bufferRegion s gs, hmem_gs, inIvl_of_cellHitsPos_aligned_bmi hal hcp⟩
    · rw [hca_nat] at hcp
      exact Or.inr (Or.inl (inIvl_of_cellHitsPos_aligned_bmi (freeGap_aligned_bmi hA) hcp))
    · rw [hca_nat] at hcp
      exact Or.inr (Or.inr (inIvl_of_cellHitsPos_aligned_bmi (heapFree_aligned_bmi hA) hcp))
  set nk_args : List (ExpHOL 64) :=
    [.var .local (ofString "m"), .var .local (ofString "key"), .var .local (ofString "klen")]
  set root_init : ExpHOL 64 := .load .one (.op .add [.var .local (ofString "m"), .const 0])
  set del_call : ProgHOL 64 :=
    .call (some (some (.local, ofString "root"), none)) (ofString "_mpt_delete_node")
      [.var .local (ofString "root"),
       .rfield 0 (.var .local (ofString "nk")),
       .rfield 1 (.var .local (ofString "nk")),
       .const 0]
  set ins_call : ProgHOL 64 :=
    .call (some (some (.local, ofString "root"), none)) (ofString "_mpt_insert_node")
      [.var .local (ofString "root"),
       .rfield 0 (.var .local (ofString "nk")),
       .rfield 1 (.var .local (ofString "nk")),
       .const 0,
       .var .local (ofString "vptr"),
       .var .local (ofString "vlen")]
  set ite_cond : ExpHOL 64 :=
    .cmp .notEqual (.const 0)
      (.op .or [.cmp .equal (.var .local (ofString "vptr")) (.const 0),
                .cmp .equal (.var .local (ofString "vlen")) (.const 0)])
  set st_ret : ProgHOL 64 :=
    .seq (.store (.op .add [.var .local (ofString "m"), .const 0]) (.var .local (ofString "root")))
         (.return (.const 0))
  set cont_nk : ProgHOL 64 :=
    .dec (ofString "root") .one root_init (.seq (.ite ite_cond del_call ins_call) st_ret)
  have hbody_eq : body = .decCall (ofString "nk") (.comb [.one, .one]) (ofString "mpt_nibble_key")
      nk_args cont_nk := rfl
  have hres_dc : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString "nk") (.comb [.one, .one]) (ofString "mpt_nibble_key") nk_args cont_nk)).1 := by
    rwa [← hbody_eq]
  obtain ⟨nk_vals, nk_body, nk_callee, nk_ret, _, hnk_args, hnk_lk, hnk_exn | hnk_ok⟩ :=
    R16Shards.decCall_resumes_inv hres_dc
  · obtain ⟨eid, ev, hnk_run, _, hnk_out⟩ := hnk_exn
    set post_nk := (evaluateHOLFiniteState (callEntryStateHOLFinite s nk_callee) nk_body).2
    have hpost_eq : post = emptyLocalsHOLFinite post_nk := by
      change (evaluateHOLFiniteState s body).2 = _
      rw [hbody_eq, hnk_out]
    have hAe_nk : ArenaReady (callEntryStateHOLFinite s nk_callee) :=
      R16Shards.localsFree_arenaReady s nk_callee (s.clock - 1) hA
    have hnt_nk : (evaluateHOLFiniteState (callEntryStateHOLFinite s nk_callee) nk_body).1 ≠ some .timeOut := by
      rw [hnk_run]; simp
    have hww_nk := FunSpec.at_lookup R16Shards.ww_mpt_nibble_key s hcode nk_vals nk_body nk_callee nk_ret
      hnk_lk hAe_nk hnt_nk
    obtain ⟨hA_nk, hhp_nk, hsp_nk, hfr_nk, hgw_nk⟩ :=
      hww_nk (by rw [hnk_run]; exact Or.inr ⟨eid, ev, rfl, ‹_›⟩)
    have hA_post : ArenaReady post := by
      rw [hpost_eq]; exact R16Shards.localsFree_arenaReady post_nk _ _ hA_nk
    have hag_nk : AllocatorGrows s post_nk := ⟨hhp_nk, hsp_nk⟩
    have hbe_nk : post_nk.be = s.be := by
      have hm := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s nk_callee) nk_body).2.2.1
      rwa [hnk_run] at hm
    have hgw_post : GlobalsKept ["heap_ptr", "scratch_ptr"] s post := by
      intro g hg; rw [hpost_eq]
      exact hgw_nk g (fun hm => hg (by
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
        exact Or.inl hm))
    have hfm_post : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" :=
      globN_eq_of_lookup_bmi (hgw_post (ofString "frame_mem_ptr") (by decide)).symm
    have hsp_eq_nk : globN post_nk "scratch_ptr" = globN s "scratch_ptr" :=
      globN_eq_of_lookup_bmi (hgw_nk (ofString "scratch_ptr") (by decide)).symm
    have hfm_eq_nk : globN post_nk "frame_mem_ptr" = globN s "frame_mem_ptr" :=
      globN_eq_of_lookup_bmi (hgw_nk (ofString "frame_mem_ptr") (by decide)).symm
    have hkp_eq_nk : globN post_nk "keccak_pad" = globN s "keccak_pad" :=
      globN_eq_of_lookup_bmi (hgw_nk (ofString "keccak_pad") (by decide)).symm
    have hks_eq_nk : globN post_nk "keccak_st" = globN s "keccak_st" :=
      globN_eq_of_lookup_bmi (hgw_nk (ofString "keccak_st") (by decide)).symm
    have hkc_eq_nk : keccakBufIvls post_nk = keccakBufIvls s := by
      simp [keccakBufIvls, bufferRegion, hkp_eq_nk, hks_eq_nk]
    obtain ⟨hm_memW, hNm_nk, hvs_nk, hext_eq, _⟩ :=
      nk_preserves_fresh_bmi hA hA_nk hB hbe_nk hag_nk hsp_eq_nk hfm_eq_nk hkc_eq_nk hfr_nk
        hm_al hm_w hN hvs hext_buf hm_buf
    have hcell : ∀ a : BitVec 64, post.memory a ≠ s.memory a →
        (∃ i ∈ Rl, Fast_C08WkShard03.CellHitsPos a.toNat i) ∨
        Fast_C08WkShard03.CellHitsPos a.toNat (freeGap s) ∨
        Fast_C08WkShard03.CellHitsPos a.toNat (heapFree s) := by
      intro a hne
      have hne_nk : post_nk.memory a ≠ s.memory a := by rwa [hpost_eq] at hne
      have hdom_nk : ∀ x : BitVec 64, post_nk.memory x ≠ s.memory x → s.memaddrs x :=
        fun x hx => hdom_wr x (by rwa [hpost_eq])
      rcases nk_cell_frame_bmi hA hfr_nk hdom_nk hne_nk with ⟨gs, hgs, hcp⟩ | hFg | hHf
      · exact Or.inl ⟨bufferRegion s gs,
          List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨gs, hgs, rfl⟩)), hcp⟩
      · exact Or.inr (Or.inl hFg)
      · exact Or.inr (Or.inr hHf)
    have hhp_post : globN s "heap_ptr" ≤ globN post "heap_ptr" := by
      rw [hpost_eq]; exact hhp_nk
    have hsp_post : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by
      rw [hpost_eq]; exact hsp_nk
    have heff : HeapByteEff s post Rl ["heap_ptr", "scratch_ptr"] :=
      ⟨hA_post, hmemaddrs_post, hhp_post, hfm_post, hsp_post, hbe_post, hgw_post,
       hdom_wr, hcell, hcell_to_byte hcell⟩
    refine ⟨Nm, heff, Nat.le_trans hmark_hp hhp_post, hmark_lo, hmark8, hwm_nat,
      P3MptSet.wordsOK_transfer hA.1 hA_post.1 hm_w,
      by rw [hpost_eq]; exact hNm_nk,
      by rw [hpost_eq]; exact hvs_nk,
      by rw [hpost_eq]; change RootIn Nm (memW post_nk mark); rw [hm_memW]; exact hm_root,
      fun o ho => ?_⟩
    rw [hpost_eq] at ho; change o ∈ nodeExtents post_nk Nm at ho; rw [hext_eq] at ho
    rcases hext_in o ho with rfl | ⟨h1, h2⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨h1, Nat.le_trans h2 hhp_post⟩
  · obtain ⟨rv, post_nk, hnk_run, _, hcont_res, _, hpost_dc⟩ := hnk_ok
    have hAe_nk : ArenaReady (callEntryStateHOLFinite s nk_callee) :=
      R16Shards.localsFree_arenaReady s nk_callee (s.clock - 1) hA
    have hnt_nk : (evaluateHOLFiniteState (callEntryStateHOLFinite s nk_callee) nk_body).1 ≠ some .timeOut := by
      rw [hnk_run]; simp
    have hww_nk := FunSpec.at_lookup R16Shards.ww_mpt_nibble_key s hcode nk_vals nk_body nk_callee nk_ret
      hnk_lk hAe_nk hnt_nk
    have hret_nk := FunSpec.at_lookup R13MptKeepsTwin.nk_mpt_nibble_key_proof s hcode nk_vals nk_body nk_callee nk_ret
      hnk_lk hAe_nk hnt_nk
    rw [hnk_run] at hww_nk hret_nk
    obtain ⟨hA_nk, hhp_nk, hsp_nk, hfr_nk, hgw_nk⟩ := hww_nk (Or.inl ⟨rv, rfl⟩)
    obtain ⟨p, l, rfl, hnib_nk, hl_le, hin_pl⟩ := hret_nk rv rfl
    have hp3 := P3MptSet.callee_param_three_exp s (ofString "mpt_nibble_key")
      (ofString "m") (ofString "key") (ofString "klen") .one .one .one _ _
      (by rw [hcode]; exact P3MptSet.lookup_mpt_nibble_key) _ _ _ nk_vals nk_body nk_callee nk_ret
      hnk_args hnk_lk
    obtain ⟨_, _, vklen, _, _, he_klen, _, _, hc_klen⟩ := hp3
    have hklen_eq : locN (callEntryStateHOLFinite s nk_callee) "klen" = wklen.toNat := by
      simp only [evalAt, evalHOLExact, hlk_klen] at he_klen
      injection he_klen with hv; subst hv
      simp [locN, callEntryStateHOLFinite, hc_klen]
    have hl64 : l.toNat ≤ 64 := hl_le (by rw [hklen_eq]; exact hklen_le)
    have hbe_nk : post_nk.be = s.be := by
      have hm := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s nk_callee) nk_body).2.2.1
      rwa [hnk_run] at hm
    have hdom_nk : ∀ a : BitVec 64, post_nk.memory a ≠ s.memory a → s.memaddrs a := by
      intro a hne; by_contra hna
      have heq := evaluate_memory_eq_of_not_memaddrs (callEntryStateHOLFinite s nk_callee) nk_body a hna
      rw [hnk_run] at heq; exact hne heq
    have hsp_eq_nk : globN post_nk "scratch_ptr" = globN s "scratch_ptr" :=
      globN_eq_of_lookup_bmi (hgw_nk (ofString "scratch_ptr") (by decide)).symm
    have hfm_eq_nk : globN post_nk "frame_mem_ptr" = globN s "frame_mem_ptr" :=
      globN_eq_of_lookup_bmi (hgw_nk (ofString "frame_mem_ptr") (by decide)).symm
    have hkp_eq_nk : globN post_nk "keccak_pad" = globN s "keccak_pad" :=
      globN_eq_of_lookup_bmi (hgw_nk (ofString "keccak_pad") (by decide)).symm
    have hks_eq_nk : globN post_nk "keccak_st" = globN s "keccak_st" :=
      globN_eq_of_lookup_bmi (hgw_nk (ofString "keccak_st") (by decide)).symm
    have hkc_eq_nk : keccakBufIvls post_nk = keccakBufIvls s := by
      simp [keccakBufIvls, bufferRegion, hkp_eq_nk, hks_eq_nk]
    have hfg_eq_nk : freeGap post_nk = freeGap s := by
      simp [freeGap, hsp_eq_nk, hfm_eq_nk]
    have hag_nk : AllocatorGrows s post_nk := ⟨hhp_nk, hsp_nk⟩
    obtain ⟨hm_memW, hNm_nk, hvs_nk, hext_eq, hni_eq⟩ :=
      nk_preserves_fresh_bmi hA hA_nk hB hbe_nk hag_nk hsp_eq_nk hfm_eq_nk hkc_eq_nk hfr_nk
        hm_al hm_w hN hvs hext_buf hm_buf
    have hv_nk : ValuePtrSafe post_nk Nm wvptr.toNat wvlen.toNat := by
      intro hvl1 hord
      obtain ⟨hc, hkc, hfg, hhf⟩ := hv_safe hvl1 hord
      have hhf_sub : ∀ b, InIvl b (heapFree post_nk) → InIvl b (heapFree s) := by
        have hhp_hl_s : globN s "heap_ptr" ≤ heapLimit := hA.2.2.1
        have hhp_hl_nk : globN post_nk "heap_ptr" ≤ heapLimit := hA_nk.2.2.1
        have hhp_grow : globN s "heap_ptr" ≤ globN post_nk "heap_ptr" := hhp_nk
        intro b ⟨h1, h2⟩
        simp only [InIvl, heapFree] at h1 h2 ⊢
        omega
      exact ⟨hc, hkc_eq_nk ▸ hkc, hfg_eq_nk ▸ hfg, fun h => hhf (hhf_sub _ h)⟩
    set s_nk := setVarHOLFinite (ofString "nk") (.rStruct [.val (.word p), .val (.word l)])
      { post_nk with locals := s.locals }
    have hA_snk : ArenaReady s_nk := R16Shards.localsFree_arenaReady post_nk _ _ hA_nk
    obtain ⟨vroot, hev_root, _, hseq_res, _, hpost_dec⟩ := dec_resumes_inv_bmi hcont_res
    have hvroot_word : ∃ wroot : BitVec 64, vroot = .val (.word wroot) ∧
        wroot.toNat = memW post_nk mark := by
      have hsnk_m : locN s_nk "m" = mark := by
        simp [s_nk, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_m, hwm_nat,
          show ofString "nk" ≠ ofString "m" by decide]
      obtain ⟨wroot, rfl, hwroot⟩ := P3MptSet.evalAt_loadL s_nk "m" 0 vroot hev_root
      rw [hsnk_m] at hwroot
      exact ⟨wroot, rfl, hwroot⟩
    obtain ⟨wroot, rfl, hwroot_nat⟩ := hvroot_word
    set s_root := setVarHOLFinite (ofString "root") (.val (.word wroot)) s_nk
    have hA_sroot : ArenaReady s_root := R16Shards.localsFree_arenaReady s_nk _ _ hA_snk
    have hcode_sroot : s_root.code = originalRuntimeCode := hA_sroot.1.code
    have hlk_sroot_m : s_root.locals.lookup (ofString "m") = some (.val (.word wm)) := by
      simp [s_root, s_nk, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_m,
        show ofString "root" ≠ ofString "m" by decide,
        show ofString "nk" ≠ ofString "m" by decide]
    have hlk_sroot_root : s_root.locals.lookup (ofString "root") = some (.val (.word wroot)) := by
      simp [s_root, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hlk_sroot_nk : s_root.locals.lookup (ofString "nk") =
        some (.rStruct [.val (.word p), .val (.word l)]) := by
      simp [s_root, s_nk, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "root" ≠ ofString "nk" by decide]
    have hlk_sroot_vptr : s_root.locals.lookup (ofString "vptr") = some (.val (.word wvptr)) := by
      simp [s_root, s_nk, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_vptr,
        show ofString "root" ≠ ofString "vptr" by decide,
        show ofString "nk" ≠ ofString "vptr" by decide]
    have hlk_sroot_vlen : s_root.locals.lookup (ofString "vlen") = some (.val (.word wvlen)) := by
      simp [s_root, s_nk, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_vlen,
        show ofString "root" ≠ ofString "vlen" by decide,
        show ofString "nk" ≠ ofString "vlen" by decide]
    have hseq_cases := seq_flow_or_resumes_bmi hseq_res
    have hite_or : (evaluateHOLFiniteState s_root (.ite ite_cond del_call ins_call)).1 = none ∨
        Resumes (evaluateHOLFiniteState s_root (.ite ite_cond del_call ins_call)).1 := by
      rcases hseq_cases with ⟨hn, _, _⟩ | ⟨hr, _⟩
      · exact Or.inl hn
      · exact Or.inr hr
    obtain ⟨cw, _, hite_br⟩ := ite_flow_or_exn_bmi hite_or
    have hdel_args : evalListHOLFinite s_root (h := fun a => Classical.propDecidable (s_root.memaddrs a))
        [.var .local (ofString "root"),
         .rfield 0 (.var .local (ofString "nk")),
         .rfield 1 (.var .local (ofString "nk")),
         .const 0] =
        some [.val (.word wroot), .val (.word p), .val (.word l), .val (.word 0)] := by
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact, evalHOLExact, hlk_sroot_root, hlk_sroot_nk]
    have hins_args : evalListHOLFinite s_root (h := fun a => Classical.propDecidable (s_root.memaddrs a))
        [.var .local (ofString "root"),
         .rfield 0 (.var .local (ofString "nk")),
         .rfield 1 (.var .local (ofString "nk")),
         .const 0,
         .var .local (ofString "vptr"),
         .var .local (ofString "vlen")] =
        some [.val (.word wroot), .val (.word p), .val (.word l), .val (.word 0),
              .val (.word wvptr), .val (.word wvlen)] := by
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact, evalHOLExact, hlk_sroot_root, hlk_sroot_nk, hlk_sroot_vptr, hlk_sroot_vlen]
    set ite_out := evaluateHOLFiniteState s_root (.ite ite_cond del_call ins_call)
    have hsroot_eq : s_root = { post_nk with locals := s_root.locals, clock := post_nk.clock } := rfl
    have hkey_nk : KeyIn post_nk Nm p.toNat l.toNat :=
      nk_keyIn_nm_bmi hA hA_nk hnib_nk hin_pl hN hni_eq
    have hroot_sr : RootIn Nm wroot.toNat := by
      rw [hwroot_nat, hm_memW]; exact hm_root
    have hite_spec : ∃ Nm',
        ValExtNodeStep [(p.toNat, l.toNat)] [(wvptr.toNat, wvlen.toNat)] post_nk ite_out.2 Nm Nm' ∧
        ((ite_out.1 = none ∧ ∃ wnew : BitVec 64,
            RootIn Nm' wnew.toNat ∧
            ite_out.2.code = originalRuntimeCode ∧
            ite_out.2.locals.lookup (ofString "root") = some (.val (.word wnew)) ∧
            (∀ y : MlS, y ≠ ofString "root" → ite_out.2.locals.lookup y = s_root.locals.lookup y)) ∨
         (∃ eid ev, ite_out.1 = some (.exception eid ev) ∧ eid ≠ ofString "TrapErr")) := by
      have hNd_sr' : NodeHeap s_root Nm := hNm_nk
      have hkey_sr' : KeyIn s_root Nm p.toNat l.toNat := hkey_nk
      rcases hite_br with ⟨_, htb⟩ | ⟨_, heb⟩
      · have hdel_or : (evaluateHOLFiniteState s_root del_call).1 = none ∨
            Resumes (evaluateHOLFiniteState s_root del_call).1 := by rwa [← htb]
        have hsp := call_assign_mpt_delete_node_valExt (K := [(p.toNat, l.toNat)])
          (V := [(wvptr.toNat, wvlen.toNat)]) s_root Nm (ofString "root") _ wroot p l 0
          hcode_sroot hA_sroot hNd_sr' hdel_args hroot_sr (by simp)
          (by simpa using hkey_sr') hdel_or
        dsimp only at hsp; rw [← htb] at hsp
        obtain ⟨Nm', hst, hrest⟩ := hsp
        rw [hsroot_eq] at hst
        exact ⟨Nm', hst.from_locals_clock, hrest⟩
      · have hins_or : (evaluateHOLFiniteState s_root ins_call).1 = none ∨
            Resumes (evaluateHOLFiniteState s_root ins_call).1 := by rwa [← heb]
        have hprov : l.toNat = 0 ∨ ∃ j ∈ [(p.toNat, l.toNat)],
            Inside (p.toNat, l.toNat) j.1 (j.1 + j.2) :=
          Or.inr ⟨(p.toNat, l.toNat), List.mem_singleton_self _, le_rfl, le_rfl⟩
        have hsp := call_assign_mpt_insert_node_valExt (K := [(p.toNat, l.toNat)])
          (V := [(wvptr.toNat, wvlen.toNat)]) s_root Nm (ofString "root") _ wroot p l 0 wvptr wvlen
          hcode_sroot hA_sroot hNd_sr' hins_args hroot_sr (by simp) hl64 hvlen_lt
          (List.mem_singleton_self _)
          (by simpa using hkey_sr') hprov hins_or
        dsimp only at hsp; rw [← heb] at hsp
        obtain ⟨Nm', hst, hrest⟩ := hsp
        rw [hsroot_eq] at hst
        exact ⟨Nm', hst.from_locals_clock, hrest⟩
    obtain ⟨Nm', hstep_nm, hcases_nm⟩ := hite_spec
    have hvs_ite : NodeHeapValuePtrOK ite_out.2 Nm' :=
      ValExtNodeStep.to_nodeHeapValuePtrOK hA_nk hstep_nm hvs_nk
        (fun pv hpv => by simp only [List.mem_singleton] at hpv; subst hpv; exact hv_nk)
    have hpost_rel : ∀ {st_fin : PanSemStateFiniteExact 64 F},
        (evaluateHOLFiniteState s_root (.seq (.ite ite_cond del_call ins_call) st_ret)).2 = st_fin →
        post.memory = st_fin.memory ∧ post.globals = st_fin.globals ∧
        (ArenaReady st_fin → ArenaReady post) := by
      intro st_fin hfin
      have hp1 : post = { st_fin with
          locals := HolFiniteMapExact.resVarEq
            (HolFiniteMapExact.resVarEq st_fin.locals (ofString "root", s_nk.locals.lookup (ofString "root")))
            (ofString "nk", s.locals.lookup (ofString "nk")) } := by
        change (evaluateHOLFiniteState s body).2 = _
        rw [hbody_eq, hpost_dc, hpost_dec, hfin]
      rw [hp1]
      exact ⟨rfl, rfl, fun hAst => R16Shards.localsFree_arenaReady st_fin _ st_fin.clock hAst⟩
    have hag_ite : AllocatorGrows s ite_out.2 :=
      ⟨Nat.le_trans hhp_nk hstep_nm.1.1.hp_le, Nat.le_trans hstep_nm.1.1.sp_le hsp_nk⟩
    have hgw_ite : GlobalsKept ["heap_ptr", "scratch_ptr"] s ite_out.2 := by
      intro g hg
      have hg_nk : s.globals.lookup g = post_nk.globals.lookup g := hgw_nk g (fun hm => hg (by
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
        exact Or.inl hm))
      exact hg_nk.trans (hstep_nm.1.1.globals g hg)
    have hext_comb := ext_extents_combine_bmi hhp_nk hstep_nm.1.1.hp_le hin_pl hext_eq hstep_nm.1
    rcases hseq_cases with ⟨hite_none, hst_res, hseq_eq⟩ | ⟨_, hseq_eq⟩
    · rcases hcases_nm with ⟨_, wnew, hwnew_root, _, hlk_ite_root, hother⟩ | ⟨eid, ev, hex, _⟩
      · have hlk_ite_m : ite_out.2.locals.lookup (ofString "m") = some (.val (.word wm)) := by
          rw [hother (ofString "m") (by decide), hlk_sroot_m]
        obtain ⟨_, hst_post⟩ := store_return_zero_resumes_bmi hlk_ite_m hlk_ite_root hst_res
        set st_fin : PanSemStateFiniteExact 64 F :=
          { ite_out.2 with memory := fun a => if a = wm then .word wnew else ite_out.2.memory a,
                           locals := HolFiniteMapExact.empty }
        have hseq_post : (evaluateHOLFiniteState s_root (.seq (.ite ite_cond del_call ins_call) st_ret)).2 = st_fin := by
          rw [hseq_eq]; exact hst_post
        obtain ⟨hpost_mem, hpost_glob, hpost_ar_fn⟩ := hpost_rel hseq_post
        have hdisj_store : ∀ o ∈ nodeExtents ite_out.2 Nm', Disj o (wm.toNat, 16) := by
          intro o ho; rw [hwm_nat]
          rcases hext_comb o ho with rfl | ⟨j, hj, hin_j⟩ | hin_fr
          · exact Or.inl rfl
          · exact R13MptKeepsTwin.disj_inside_left hin_j (hext_disj_m j hj)
          · exact R13MptKeepsTwin.disj_fresh_heap_allocated hA.2 hstep_nm.1.1.arena.2 hin_fr (Or.inr hm_al)
        obtain ⟨hAst_fin, hNm'_st, hvs_st, hext_st⟩ :=
          nodeHeap_preserve_single_store_bmi hstep_nm.1.1.arena hstep_nm.1.1.heap hvs_ite hdisj_store (wval := wnew)
        have hA_post : ArenaReady post := hpost_ar_fn hAst_fin
        have hhp_post : globN s "heap_ptr" ≤ globN post "heap_ptr" := by
          dsimp [globN]; rw [hpost_glob]; exact hag_ite.1
        have hsp_post : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by
          dsimp [globN]; rw [hpost_glob]; exact hag_ite.2
        have hgw_post : GlobalsKept ["heap_ptr", "scratch_ptr"] s post := by
          intro g hg; rw [hpost_glob]; exact hgw_ite g hg
        have hfm_post : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" :=
          globN_eq_of_lookup_bmi (hgw_post (ofString "frame_mem_ptr") (by decide)).symm
        have hcell : ∀ a : BitVec 64, post.memory a ≠ s.memory a →
            (∃ i ∈ Rl, Fast_C08WkShard03.CellHitsPos a.toNat i) ∨
            Fast_C08WkShard03.CellHitsPos a.toNat (freeGap s) ∨
            Fast_C08WkShard03.CellHitsPos a.toNat (heapFree s) := by
          intro a hne
          have hord : ordinaryDomain a := by
            have hm := hdom_wr a hne; rwa [hA.1.memaddrs] at hm
          obtain ⟨ha8, _, _⟩ := ordinaryDomain_bounds_bmi hord
          rw [hpost_mem] at hne; dsimp [st_fin] at hne
          by_cases hawm : a = wm
          · subst hawm
            exact Or.inl ⟨(mark, 16), by simp [Rl], by rw [hwm_nat]; exact ⟨by omega, by omega, by omega⟩⟩
          · rw [if_neg hawm] at hne
            by_cases hne_ite : ite_out.2.memory a ≠ post_nk.memory a
            · rcases nodeStep_cell_frame_bmi hA hA_nk hhp_nk hfg_eq_nk hni_eq hN hstep_nm.1.1 ha8 hne_ite with
                ⟨n, hn, hcp⟩ | hFg | hHf
              · exact Or.inl ⟨nodeIvl s n,
                  List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2 ⟨n, hn, rfl⟩)), hcp⟩
              · exact Or.inr (Or.inl hFg)
              · exact Or.inr (Or.inr hHf)
            · push Not at hne_ite
              have hne_nk : post_nk.memory a ≠ s.memory a := by rwa [← hne_ite]
              rcases nk_cell_frame_bmi hA hfr_nk hdom_nk hne_nk with ⟨gs, hgs, hcp⟩ | hFg | hHf
              · exact Or.inl ⟨bufferRegion s gs,
                  List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨gs, hgs, rfl⟩)), hcp⟩
              · exact Or.inr (Or.inl hFg)
              · exact Or.inr (Or.inr hHf)
        have heff : HeapByteEff s post Rl ["heap_ptr", "scratch_ptr"] :=
          ⟨hA_post, hmemaddrs_post, hhp_post, hfm_post, hsp_post, hbe_post, hgw_post,
           hdom_wr, hcell, hcell_to_byte hcell⟩
        have hNm'_post : NodeHeap post Nm' :=
          P3MptSet.nodeHeap_congr_unhit hAst_fin.1 hA_post.1
            (by rw [hbe_post]; exact ((PanRunBounded.evaluateHOLFiniteState_metadata s_root (.ite ite_cond del_call ins_call)).2.2.1.trans hbe_nk).symm)
            (by dsimp [AllocatorGrows, globN]; rw [hpost_glob]; exact ⟨le_rfl, le_rfl⟩)
            hNm'_st (fun o _ _ a _ _ => by rw [hpost_mem])
        have hvs_post : NodeHeapValuePtrOK post Nm' :=
          nodeHeapValuePtrOK_congr_unhit_bmi hAst_fin hNm'_st hpost_glob
            (fun o _ _ a _ _ => by rw [hpost_mem]) hvs_st
        have hext_post : nodeExtents post Nm' = nodeExtents st_fin Nm' :=
          nodeExtents_eq_of_unhit_bmi hAst_fin hNm'_st (fun o _ _ a _ _ => by rw [hpost_mem])
        have hroot_post : RootIn Nm' (memW post mark) := by
          have hmw : memW post mark = wnew.toNat := by
            have hm_lt : mark < 2 ^ 64 := by
              have hb := P3MptSet.ivl_allocated_bound hA.2 hm_al; omega
            have hbv : (BitVec.ofNat 64 mark : BitVec 64) = wm := by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt, hwm_nat]
            simp only [memW, hpost_mem, st_fin, hbv, ↓reduceIte]
          rw [hmw]; exact hwnew_root
        refine ⟨Nm', heff, Nat.le_trans hmark_hp hhp_post, hmark_lo, hmark8, hwm_nat,
          P3MptSet.wordsOK_transfer hA.1 hA_post.1 hm_w, hNm'_post, hvs_post, hroot_post, ?_⟩
        intro o ho
        rw [hext_post, hext_st] at ho
        have hhp_post_eq : globN post "heap_ptr" = globN ite_out.2 "heap_ptr" := by
          simp [globN, hpost_glob, st_fin]
        rw [hhp_post_eq]
        rcases hext_comb o ho with rfl | ⟨j, hj, hin_j⟩ | hin_fr
        · exact Or.inl rfl
        · rcases hext_in j hj with rfl | ⟨hj1, hj2⟩
          · dsimp [Inside] at hin_j; exact Or.inl (Prod.ext (by omega) (by omega))
          · exact Or.inr ⟨by dsimp [Inside] at hin_j ⊢; omega,
              by dsimp [Inside] at hin_j ⊢; have := hag_ite.1; omega⟩
        · exact Or.inr ⟨Nat.le_trans hmark_hp hin_fr.1, hin_fr.2⟩
      · rw [hite_none] at hex; cases hex
    · have hseq_post : (evaluateHOLFiniteState s_root (.seq (.ite ite_cond del_call ins_call) st_ret)).2 = ite_out.2 := by
        rw [hseq_eq]
      obtain ⟨hpost_mem, hpost_glob, hpost_ar_fn⟩ := hpost_rel hseq_post
      have hA_post : ArenaReady post := hpost_ar_fn hstep_nm.1.1.arena
      have hhp_post : globN s "heap_ptr" ≤ globN post "heap_ptr" := by
        dsimp [globN]; rw [hpost_glob]; exact hag_ite.1
      have hsp_post : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by
        dsimp [globN]; rw [hpost_glob]; exact hag_ite.2
      have hgw_post : GlobalsKept ["heap_ptr", "scratch_ptr"] s post := by
        intro g hg; rw [hpost_glob]; exact hgw_ite g hg
      have hfm_post : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" :=
        globN_eq_of_lookup_bmi (hgw_post (ofString "frame_mem_ptr") (by decide)).symm
      have hcell : ∀ a : BitVec 64, post.memory a ≠ s.memory a →
          (∃ i ∈ Rl, Fast_C08WkShard03.CellHitsPos a.toNat i) ∨
          Fast_C08WkShard03.CellHitsPos a.toNat (freeGap s) ∨
          Fast_C08WkShard03.CellHitsPos a.toNat (heapFree s) := by
        intro a hne
        have hord : ordinaryDomain a := by
          have hm := hdom_wr a hne; rwa [hA.1.memaddrs] at hm
        obtain ⟨ha8, _, _⟩ := ordinaryDomain_bounds_bmi hord
        rw [hpost_mem] at hne
        by_cases hne_ite : ite_out.2.memory a ≠ post_nk.memory a
        · rcases nodeStep_cell_frame_bmi hA hA_nk hhp_nk hfg_eq_nk hni_eq hN hstep_nm.1.1 ha8 hne_ite with
            ⟨n, hn, hcp⟩ | hFg | hHf
          · exact Or.inl ⟨nodeIvl s n,
              List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2 ⟨n, hn, rfl⟩)), hcp⟩
          · exact Or.inr (Or.inl hFg)
          · exact Or.inr (Or.inr hHf)
        · push Not at hne_ite
          have hne_nk : post_nk.memory a ≠ s.memory a := by rwa [← hne_ite]
          rcases nk_cell_frame_bmi hA hfr_nk hdom_nk hne_nk with ⟨gs, hgs, hcp⟩ | hFg | hHf
          · exact Or.inl ⟨bufferRegion s gs,
              List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨gs, hgs, rfl⟩)), hcp⟩
          · exact Or.inr (Or.inl hFg)
          · exact Or.inr (Or.inr hHf)
      have heff : HeapByteEff s post Rl ["heap_ptr", "scratch_ptr"] :=
        ⟨hA_post, hmemaddrs_post, hhp_post, hfm_post, hsp_post, hbe_post, hgw_post,
         hdom_wr, hcell, hcell_to_byte hcell⟩
      have hm_ite := m_unhit_across_nodeStep_bmi hA hA_nk hhp_nk hfg_eq_nk hni_eq hm_al hm_w hN hext_disj_m hstep_nm.1.1
      have hNm'_post : NodeHeap post Nm' :=
        P3MptSet.nodeHeap_congr_unhit hstep_nm.1.1.arena.1 hA_post.1
          (by rw [hbe_post]; exact ((PanRunBounded.evaluateHOLFiniteState_metadata s_root (.ite ite_cond del_call ins_call)).2.2.1.trans hbe_nk).symm)
          (by dsimp [AllocatorGrows, globN]; rw [hpost_glob]; exact ⟨le_rfl, le_rfl⟩)
          hstep_nm.1.1.heap (fun o _ _ a _ _ => by rw [hpost_mem])
      have hvs_post : NodeHeapValuePtrOK post Nm' :=
        nodeHeapValuePtrOK_congr_unhit_bmi hstep_nm.1.1.arena hstep_nm.1.1.heap hpost_glob
          (fun o _ _ a _ _ => by rw [hpost_mem]) hvs_ite
      have hext_post : nodeExtents post Nm' = nodeExtents ite_out.2 Nm' :=
        nodeExtents_eq_of_unhit_bmi hstep_nm.1.1.arena hstep_nm.1.1.heap (fun o _ _ a _ _ => by rw [hpost_mem])
      have hroot_post : RootIn Nm' (memW post mark) := by
        have hmw : memW post mark = memW s mark := by
          have hp : memW post mark = memW ite_out.2 mark := by simp [memW, hpost_mem]
          rw [hp, hm_ite, hm_memW]
        rw [hmw]
        rcases hm_root with h0 | hm_in
        · exact Or.inl h0
        · exact Or.inr (hstep_nm.1.1.sub _ hm_in)
      refine ⟨Nm', heff, Nat.le_trans hmark_hp hhp_post, hmark_lo, hmark8, hwm_nat,
        P3MptSet.wordsOK_transfer hA.1 hA_post.1 hm_w, hNm'_post, hvs_post, hroot_post, ?_⟩
      intro o ho
      rw [hext_post] at ho
      have hhp_post_eq : globN post "heap_ptr" = globN ite_out.2 "heap_ptr" := by
        simp [globN, hpost_glob]
      rw [hhp_post_eq]
      rcases hext_comb o ho with rfl | ⟨j, hj, hin_j⟩ | hin_fr
      · exact Or.inl rfl
      · rcases hext_in j hj with rfl | ⟨hj1, hj2⟩
        · dsimp [Inside] at hin_j; exact Or.inl (Prod.ext (by omega) (by omega))
        · exact Or.inr ⟨by dsimp [Inside] at hin_j ⊢; omega,
            by dsimp [Inside] at hin_j ⊢; have := hag_ite.1; omega⟩
      · exact Or.inr ⟨Nat.le_trans hmark_hp hin_fr.1, hin_fr.2⟩

/-! ## 3b. Finite code-lookup helpers for `mpt_set` and `mpt_root` -/

theorem lookupCodeHOLFinite_two_words_bmi
    {code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    {name p1 p2 : MlS} {body : ProgHOL 64} {rs : ShapeHOL}
    {w1 w2 : BitVec 64}
    (hd : List.Pairwise (· ≠ ·) [p1, p2])
    (lookup : code name = some ([(p1, .one), (p2, .one)], body, rs)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name [.val (.word w1), .val (.word w2)] =
      some (body, (HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2)), rs) := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
    and_true] at hd
  have hsh : ∀ w : BitVec 64, shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true := by
    intro w; simp [shapeOfHOLExact, shapeEqHOL]
  have raw : lookupCodeHOLExact code name [.val (.word w1), .val (.word w2)] =
      some (body, (fun key =>
        if key = p2 then some (.val (.word w2))
        else if key = p1 then some (.val (.word w1))
        else none), rs) := by
    simp [lookupCodeHOLExact, lookup, hsh, hd]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing; rw [raw] at missing; cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, foundShape))
    apply HolFiniteMapExact.ext
    funext key
    by_cases c2 : key = p2
    · subst c2; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
    · have b2 : p2 ≠ key := Ne.symm c2
      by_cases c1 : key = p1
      · subst c1; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, c2, b2]
      · have b1 : p1 ≠ key := Ne.symm c1
        simp [c1, c2, b1, b2, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]

private theorem lookupCodeHOLFinite_five_words_bmi
    {code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    {name p1 p2 p3 p4 p5 : MlS} {body : ProgHOL 64} {rs : ShapeHOL}
    {w1 w2 w3 w4 w5 : BitVec 64}
    (hd : List.Pairwise (· ≠ ·) [p1, p2, p3, p4, p5])
    (lookup : code name = some ([(p1, .one), (p2, .one), (p3, .one), (p4, .one), (p5, .one)], body, rs)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name
      [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4), .val (.word w5)] =
      some (body, (((((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update
        (p2, .val (.word w2))).update (p3, .val (.word w3))).update (p4, .val (.word w4))).update
        (p5, .val (.word w5))), rs) := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true] at hd
  obtain ⟨⟨h12, h13, h14, h15⟩, ⟨h23, h24, h25⟩, ⟨h34, h35⟩, h45⟩ := hd
  have hsh : ∀ w : BitVec 64, shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true := by
    intro w; simp [shapeOfHOLExact, shapeEqHOL]
  have raw : lookupCodeHOLExact code name
      [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4), .val (.word w5)] =
      some (body, (fun key =>
        if key = p5 then some (.val (.word w5))
        else if key = p4 then some (.val (.word w4))
        else if key = p3 then some (.val (.word w3))
        else if key = p2 then some (.val (.word w2))
        else if key = p1 then some (.val (.word w1))
        else none), rs) := by
    simp [lookupCodeHOLExact, lookup, hsh, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing; rw [raw] at missing; cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, foundShape))
    apply HolFiniteMapExact.ext
    funext key
    by_cases c5 : key = p5
    · subst c5; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
    · have b5 : p5 ≠ key := Ne.symm c5
      by_cases c4 : key = p4
      · subst c4; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, c5, b5]
      · have b4 : p4 ≠ key := Ne.symm c4
        by_cases c3 : key = p3
        · subst c3; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, c5, b5, c4, b4]
        · have b3 : p3 ≠ key := Ne.symm c3
          by_cases c2 : key = p2
          · subst c2; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, c5, b5, c4, b4, c3, b3]
          · have b2 : p2 ≠ key := Ne.symm c2
            by_cases c1 : key = p1
            · subst c1; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, c5, b5, c4, b4, c3, b3, c2, b2]
            · have b1 : p1 ≠ key := Ne.symm c1
              simp [c1, c2, c3, c4, c5, b1, b2, b3, b4, b5,
                HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]

theorem eval_call_mpt_set_fresh {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (mark : Nat) (wm wkey wklen wvptr wvlen : BitVec 64) (Nm : List Nat)
    (mExp keyExp klenExp vptrExp vlenExp : ExpHOL 64)
    (hcode : s.code = originalRuntimeCode)
    (hA : ArenaReady s)
    (hB : BmiScratchOK s)
    (hB_pre : ∀ gs ∈ bmiScratch, globN s gs.1 ≠ 0 →
      globN s gs.1 + gs.2 ≤ mark ∨ globN s "scratch_ptr" ≤ globN s gs.1)
    (hFT : FreshTrie s mark wm Nm)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [mExp, keyExp, klenExp, vptrExp, vlenExp] =
      some [.val (.word wm), .val (.word wkey), .val (.word wklen), .val (.word wvptr), .val (.word wvlen)])
    (hklen_le : wklen.toNat ≤ 32)
    (hvlen_lt : wvlen.toNat < 2 ^ 40)
    (hv_safe : ValuePtrSafe s Nm wvptr.toNat wvlen.toNat)
    (hor : (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "mpt_set") [mExp, keyExp, klenExp, vptrExp, vlenExp])).1 = none ∨
      Resumes (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "mpt_set") [mExp, keyExp, klenExp, vptrExp, vlenExp])).1) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "mpt_set") [mExp, keyExp, klenExp, vptrExp, vlenExp])
    ∃ Nm',
      HeapByteEff s out.2
        ([(mark, 16)] ++ Nm.map (nodeIvl s) ++ bmiScratch.map (bufferRegion s))
        ["heap_ptr", "scratch_ptr"] ∧
      FreshTrie out.2 mark wm Nm' ∧
      ((out.1 = none ∧ out.2.locals = s.locals) ∨
       (∃ eid ev, out.1 = some (.exception eid ev) ∧ eid ≠ ofString "TrapErr")) := by
  intro out; dsimp only [out]
  rw [evaluateHOLFiniteState_call] at hor ⊢
  rw [hargs] at hor ⊢; dsimp only at hor ⊢
  set callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (((((HolFiniteMapExact.empty : HolFiniteMapExact MlS (ValueHOL 64)).update
      (ofString "m", .val (.word wm))).update
      (ofString "key", .val (.word wkey))).update
      (ofString "klen", .val (.word wklen))).update
      (ofString "vptr", .val (.word wvptr))).update
      (ofString "vlen", .val (.word wvlen))
  have hl : lookupCodeHOLFinite s.code.lookup (ofString "mpt_set")
      [.val (.word wm), .val (.word wkey), .val (.word wklen), .val (.word wvptr), .val (.word wvlen)] =
      some (sourceFnBody Guest.Software.guestFn_mpt_set, callee, .one) := by
    rw [hcode]
    exact lookupCodeHOLFinite_five_words_bmi (by decide) P3MptSet.lookup_mpt_set
  rw [hl] at hor ⊢; dsimp only at hor ⊢
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at hor
    rcases hor with hn | hr <;> [cases hn; exact absurd hr not_resumes_timeout_bmi]
  · rw [if_neg hcz] at hor ⊢
    let ent := callEntryStateHOLFinite s callee
    have hent_m : ent.locals.lookup (ofString "m") = some (.val (.word wm)) := by
      simp [ent, callee, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "vlen" ≠ ofString "m" by decide,
        show ofString "vptr" ≠ ofString "m" by decide,
        show ofString "klen" ≠ ofString "m" by decide,
        show ofString "key" ≠ ofString "m" by decide]
    have hent_key : ent.locals.lookup (ofString "key") = some (.val (.word wkey)) := by
      simp [ent, callee, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "vlen" ≠ ofString "key" by decide,
        show ofString "vptr" ≠ ofString "key" by decide,
        show ofString "klen" ≠ ofString "key" by decide]
    have hent_klen : ent.locals.lookup (ofString "klen") = some (.val (.word wklen)) := by
      simp [ent, callee, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "vlen" ≠ ofString "klen" by decide,
        show ofString "vptr" ≠ ofString "klen" by decide]
    have hent_vptr : ent.locals.lookup (ofString "vptr") = some (.val (.word wvptr)) := by
      simp [ent, callee, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "vlen" ≠ ofString "vptr" by decide]
    have hent_vlen : ent.locals.lookup (ofString "vlen") = some (.val (.word wvlen)) := by
      simp [ent, callee, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hrun : evaluateHOLFiniteState (s.callEntryStateHOLFinite callee) (sourceFnBody Guest.Software.guestFn_mpt_set) with ⟨res, cpost⟩
    have hres_ent : Resumes res := by
      cases res with
      | none =>
        rw [hrun] at hor; dsimp only at hor
        rcases hor with hn | hr <;> [cases hn; exact absurd hr R16Shards.not_resumes_error]
      | some r0 =>
        cases r0 with
        | returned v => exact Or.inl ⟨v, rfl⟩
        | exception eid ev =>
          rw [hrun] at hor; dsimp only at hor
          rcases hor with hn | hr
          · cases hn
          · rcases hr with ⟨_, hrv⟩ | ⟨e', v', hex, hne⟩
            · cases hrv
            · injection hex with hex'; cases hex'; exact Or.inr ⟨eid, ev, rfl, hne⟩
        | timeOut =>
          rw [hrun] at hor; dsimp only at hor
          rcases hor with hn | hr <;> [cases hn; exact absurd hr not_resumes_timeout_bmi]
        | error =>
          rw [hrun] at hor; dsimp only at hor
          rcases hor with hn | hr <;> [cases hn; exact absurd hr R16Shards.not_resumes_error]
        | «break» =>
          rw [hrun] at hor; dsimp only at hor
          rcases hor with hn | hr <;> [cases hn; exact absurd hr R16Shards.not_resumes_error]
        | «continue» =>
          rw [hrun] at hor; dsimp only at hor
          rcases hor with hn | hr <;> [cases hn; exact absurd hr R16Shards.not_resumes_error]
        | finalFfi _ =>
          rw [hrun] at hor; dsimp only at hor
          rcases hor with hn | hr <;> [cases hn; exact absurd hr not_resumes_finalFfi_bmi]
    have hspec := mpt_set_body_fresh ent mark wm wkey wklen wvptr wvlen Nm
      hcode (R16Shards.localsFree_arenaReady s _ _ hA) hB hB_pre hFT
      hent_m hent_key hent_klen hent_vptr hent_vlen hklen_le hvlen_lt hv_safe
      (by dsimp only [ent]; rw [hrun]; exact hres_ent)
    dsimp only [ent] at hspec; rw [hrun] at hspec; dsimp only at hspec
    obtain ⟨Nm', heff_ent, hFT_post⟩ := hspec
    have heff_s_cpost : HeapByteEff s cpost
        ([(mark, 16)] ++ Nm.map (nodeIvl s) ++ bmiScratch.map (bufferRegion s))
        ["heap_ptr", "scratch_ptr"] :=
      ((HeapByteEff.refl hA _ _).locals_clock ent.locals ent.clock).trans heff_ent
    rcases hres_ent with ⟨v, rfl⟩ | ⟨eid, ev, rfl, hne⟩
    · rw [hrun] at hor; dsimp only at hor ⊢
      by_cases hsh : shapeEqHOL (shapeOfHOLExact v) .one = true
      · rw [if_pos hsh]
        exact ⟨Nm', heff_s_cpost.locals_clock s.locals cpost.clock,
          hFT_post.with_locals_clock s.locals cpost.clock, Or.inl ⟨rfl, rfl⟩⟩
      · rw [if_neg hsh] at hor
        rcases hor with hn | hr <;> [cases hn; exact absurd hr R16Shards.not_resumes_error]
    · dsimp only
      exact ⟨Nm', heff_s_cpost.locals_clock HolFiniteMapExact.empty cpost.clock,
        hFT_post.with_locals_clock HolFiniteMapExact.empty cpost.clock, Or.inr ⟨eid, ev, rfl, hne⟩⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
