import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01AllocMpt
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01Memcpy

/-! Proofs of `rt_htab_copy` and `wk_htab_copy` for `WkShard01.lean`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Contracts.M12
open InitECandidate.Solver.Wave8Contracts.M26

theorem lookup_htab_copy_r13 :
    originalRuntimeCode.lookup (ofString "htab_copy") =
      some ([(ofString "t", .one)], sourceFnBody Guest.Software.guestFn_htab_copy, .one) :=
  lookup_of_guestAst_getElem 145 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_copy) rfl

/-! ## 1. `MemOnlyFrame`: globals-agnostic byte & cell write-frame -/

structure MemOnlyFrame {F : Type} (s0 s : PanSemStateFiniteExact 64 F) (ivl : Ivl) : Prop where
  code       : s.code = s0.code
  memaddrs   : s.memaddrs = s0.memaddrs
  shMemaddrs : s.shMemaddrs = s0.shMemaddrs
  baseAddr   : s.baseAddr = s0.baseAddr
  be         : s.be = s0.be
  cell_frame : FrameOutside s0 s [ivl] (0, 0)
  byte_frame : ∀ a : Nat, a < 2 ^ 64 → ¬ InIvl a ivl → memB s a = memB s0 a
  dom_writes : ∀ a : BitVec 64, s.memory a ≠ s0.memory a → s0.memaddrs a

theorem MemOnlyFrame.refl {F : Type} (s0 : PanSemStateFiniteExact 64 F) (ivl : Ivl) :
    MemOnlyFrame s0 s0 ivl :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ h => absurd rfl h⟩

theorem MemOnlyFrame.of_mwf {F : Type} {s0 s : PanSemStateFiniteExact 64 F} {ivl : Ivl}
    (h : MemWriteFrame s0 s ivl) : MemOnlyFrame s0 s ivl :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
   h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem MemOnlyFrame.with_locals_clock {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {ivl : Ivl} (h : MemOnlyFrame s0 s ivl)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    MemOnlyFrame s0 { s with locals := L, clock := k } ivl :=
  ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be,
   h.cell_frame, h.byte_frame, h.dom_writes⟩

theorem MemOnlyFrame.trans {F : Type} {s0 s1 s2 : PanSemStateFiniteExact 64 F}
    {ivl1 ivl2 ivl : Ivl}
    (h1 : MemOnlyFrame s0 s1 ivl1) (h2 : MemOnlyFrame s1 s2 ivl2)
    (hsub1 : ivl1 = (0, 0) ∨ (ivl.1 ≤ ivl1.1 ∧ ivl1.1 + ivl1.2 ≤ ivl.1 + ivl.2))
    (hsub2 : ivl2 = (0, 0) ∨ (ivl.1 ≤ ivl2.1 ∧ ivl2.1 + ivl2.2 ≤ ivl.1 + ivl.2)) :
    MemOnlyFrame s0 s2 ivl := by
  refine ⟨h2.code.trans h1.code, h2.memaddrs.trans h1.memaddrs,
    h2.shMemaddrs.trans h1.shMemaddrs, h2.baseAddr.trans h1.baseAddr,
    h2.be.trans h1.be, ?_, ?_, ?_⟩
  · intro a hk hf
    have hn2 : ¬ CellHits a.toNat ivl2 := by
      intro hch
      rcases hsub2 with rfl | ⟨hl, hr⟩
      · unfold CellHits at hch; omega
      · exact hk ivl (List.mem_singleton.2 rfl) ⟨by unfold CellHits at hch; omega, by unfold CellHits at hch; omega⟩
    have hn1 : ¬ CellHits a.toNat ivl1 := by
      intro hch
      rcases hsub1 with rfl | ⟨hl, hr⟩
      · unfold CellHits at hch; omega
      · exact hk ivl (List.mem_singleton.2 rfl) ⟨by unfold CellHits at hch; omega, by unfold CellHits at hch; omega⟩
    rw [h2.cell_frame a (fun j hj => by rw [List.mem_singleton.1 hj]; exact hn2) hf]
    exact h1.cell_frame a (fun j hj => by rw [List.mem_singleton.1 hj]; exact hn1) hf
  · intro a ha hni
    have hnb2 : ¬ InIvl a ivl2 := by
      intro hin
      rcases hsub2 with rfl | ⟨hl, hr⟩
      · unfold InIvl at hin; omega
      · exact hni ⟨by unfold InIvl at hin; omega, by unfold InIvl at hin; omega⟩
    have hnb1 : ¬ InIvl a ivl1 := by
      intro hin
      rcases hsub1 with rfl | ⟨hl, hr⟩
      · unfold InIvl at hin; omega
      · exact hni ⟨by unfold InIvl at hin; omega, by unfold InIvl at hin; omega⟩
    rw [h2.byte_frame a ha hnb2, h1.byte_frame a ha hnb1]
  · intro a hne
    by_cases heq2 : s2.memory a = s1.memory a
    · rw [heq2] at hne; exact h1.dom_writes a hne
    · rw [← h1.memaddrs]; exact h2.dom_writes a heq2

theorem MemOnlyFrame.updW_step {F : Type} {s0 s1 : PanSemStateFiniteExact 64 F}
    {ivl : Ivl} (h1 : MemOnlyFrame s0 s1 ivl)
    (addr val : BitVec 64) (hdom : s1.memaddrs addr)
    (ha8 : addr.toNat % 8 = 0)
    (hin : ivl.1 ≤ addr.toNat ∧ addr.toNat + 8 ≤ ivl.1 + ivl.2) :
    MemOnlyFrame s0 { s1 with memory := updW s1.memory addr val } ivl := by
  refine ⟨h1.code, h1.memaddrs, h1.shMemaddrs, h1.baseAddr, h1.be, ?_, ?_, ?_⟩
  · intro a hk hf
    have hne : a ≠ addr := by
      rintro rfl
      exact hk ivl (List.mem_singleton.2 rfl) ⟨by omega, by omega⟩
    dsimp only; rw [updW, if_neg hne]
    exact h1.cell_frame a hk hf
  · intro b hb hni
    unfold memB
    dsimp only
    have hal_nat : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
      rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
    have hne : panByteAlignHOL (BitVec.ofNat 64 b) ≠ addr := by
      intro heq
      have ht := congrArg BitVec.toNat heq
      rw [hal_nat] at ht
      exact hni ⟨by omega, by omega⟩
    simp only [updW, if_neg hne]
    exact h1.byte_frame b hb hni
  · intro a hne
    dsimp only at hne
    by_cases ha : a = addr
    · subst ha; rw [← h1.memaddrs]; exact hdom
    · simp only [updW, if_neg ha] at hne; exact h1.dom_writes a hne

theorem MemOnlyFrame.mem_eq_of_disj_cell {F : Type} {s0 s1 : PanSemStateFiniteExact 64 F}
    {ivl : Ivl} (hmof : MemOnlyFrame s0 s1 ivl)
    (a : BitVec 64) (hnh : ¬ CellHits a.toNat ivl) :
    s1.memory a = s0.memory a :=
  hmof.cell_frame a (fun j hj => by rw [List.mem_singleton.1 hj]; exact hnh)
    (by unfold CellHits; omega)

theorem memW_eq_of_mem_eq {F : Type} {s1 s2 : PanSemStateFiniteExact 64 F}
    (addr : Nat) (h : s1.memory (BitVec.ofNat 64 addr) = s2.memory (BitVec.ofNat 64 addr)) :
    memW s1 addr = memW s2 addr := by
  unfold memW; rw [h]

theorem memW_updW_self {F : Type} (s : PanSemStateFiniteExact 64 F)
    (addr val : BitVec 64) :
    memW { s with memory := updW s.memory addr val } addr.toNat = val.toNat := by
  simp [memW, BitVec.ofNat_toNat, updW]

/-! ## 2. `HtabWF` isomorphism lemma for a freshly copied table -/

theorem freeChain_congr_eq {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {nodes_s nodes_p ncap : Nat}
    (hnd : ∀ n, 1 ≤ n → n ≤ ncap → nodeF post nodes_p n 0 = nodeF s nodes_s n 0) :
    ∀ (Fr : List Nat) (head : Nat),
      (∀ f ∈ Fr, 1 ≤ f ∧ f ≤ ncap) →
      FreeChain s nodes_s head Fr → FreeChain post nodes_p head Fr
  | [], head, _, h => h
  | f :: rest, head, hFr, ⟨h1, h2⟩ => by
    have hf := hFr f List.mem_cons_self
    refine ⟨h1, ?_⟩
    rw [hnd f hf.1 hf.2]
    exact freeChain_congr_eq hnd rest _ (fun x hx => hFr x (List.mem_cons_of_mem _ hx)) h2

theorem htabWF_of_copied {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {t n b_keys b_nodes b_order : Nat}
    (hW : HtabWF s t)
    (hG_post : GuestInv post)
    (hhdr0 : hdr post n 0 = hdr s t 0)
    (hhdr1 : hdr post n 1 = hdr s t 1)
    (hhdr3 : hdr post n 3 = hdr s t 3)
    (hhdr4 : hdr post n 4 = b_keys)
    (hhdr5 : hdr post n 5 = b_nodes)
    (hhdr6 : hdr post n 6 = b_order)
    (hhdr7 : hdr post n 7 = hdr s t 7)
    (hhdr8 : hdr post n 8 = hdr s t 8)
    (hhdr9 : hdr post n 9 = hdr s t 9)
    (hhdr10 : hdr post n 10 = hdr s t 10)
    (hn8 : n % 8 = 0) (hk8 : b_keys % 8 = 0) (hnd8 : b_nodes % 8 = 0) (ho8 : b_order % 8 = 0)
    (hn_in : sourceBase ≤ n ∧ n + 88 ≤ heapLimit)
    (hk_in : n + 88 ≤ b_keys ∧ b_keys + (hdr s t 10 + 1) * hdr s t 1 ≤ heapLimit)
    (hnd_in : b_keys + (hdr s t 10 + 1) * hdr s t 1 ≤ b_nodes ∧ b_nodes + (hdr s t 10 + 1) * 32 ≤ heapLimit)
    (ho_in : b_nodes + (hdr s t 10 + 1) * 32 ≤ b_order ∧ b_order + (hdr s t 10 + 1) * 8 ≤ heapLimit)
    (hnodeF_eq : ∀ idx, 1 ≤ idx → idx ≤ hdr s t 10 → ∀ off ∈ ([0, 8, 16, 24] : List Nat),
      nodeF post b_nodes idx off = nodeF s (hdr s t 5) idx off)
    (hord_eq : ∀ idx, idx < hdr s t 3 →
      memW post (b_order + 8 * idx) = memW s (hdr s t 6 + 8 * idx)) :
    HtabWF post n := by
  have hhl_he : heapLimit ≤ heapEnd := by decide
  obtain ⟨_, _, hk1, hk2, hst, hnc, hnx1, hnx2,
    L, I, Fr, hLlen, hnd, hmem, hcntI, hL, hI, hr0, hrpos, hnroot, hpI, hdep, hfc⟩ := hW
  have hst8 : hdr s t 1 % 8 = 0 := by omega
  have hks_len8 : ((hdr s t 10 + 1) * hdr s t 1) % 8 = 0 := by rw [Nat.mul_mod, hst8]; simp
  have hnd_len8 : ((hdr s t 10 + 1) * 32) % 8 = 0 := by omega
  have ho_len8 : ((hdr s t 10 + 1) * 8) % 8 = 0 := by omega
  have hLI_bound : ∀ idx ∈ L ++ I, 1 ≤ idx ∧ idx ≤ hdr s t 10 := fun idx hidx => by
    have := (hmem idx).1 (List.mem_append_left Fr hidx); omega
  have hFr_bound : ∀ f ∈ Fr, 1 ≤ f ∧ f ≤ hdr s t 10 := fun f hf => by
    have := (hmem f).1 (List.mem_append_right (L ++ I) hf); omega
  unfold HtabWF htabFootprint
  simp only [hhdr0, hhdr1, hhdr3, hhdr4, hhdr5, hhdr6, hhdr7, hhdr8, hhdr9, hhdr10]
  refine ⟨?_, ?_, hk1, hk2, hst, hnc, hnx1, hnx2, L, I, Fr, hLlen, hnd, hmem, hcntI,
    ?_, ?_, hr0, ?_, ?_, ?_, ?_, ?_⟩
  · intro ivl hivl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hivl
    rcases hivl with rfl | rfl | rfl | rfl
    · exact ⟨⟨hn_in.1, le_trans hn_in.2 hhl_he⟩,
        wordsOK_of_guestInv post hG_post n 88 hn8 (by decide) hn_in.1 (le_trans hn_in.2 hhl_he)⟩
    · exact ⟨⟨by omega, le_trans hk_in.2 hhl_he⟩,
        wordsOK_of_guestInv post hG_post b_keys _ hk8 hks_len8 (by omega) (le_trans hk_in.2 hhl_he)⟩
    · exact ⟨⟨by omega, le_trans hnd_in.2 hhl_he⟩,
        wordsOK_of_guestInv post hG_post b_nodes _ hnd8 hnd_len8 (by omega) (le_trans hnd_in.2 hhl_he)⟩
    · exact ⟨⟨by omega, le_trans ho_in.2 hhl_he⟩,
        wordsOK_of_guestInv post hG_post b_order _ ho8 ho_len8 (by omega) (le_trans ho_in.2 hhl_he)⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, Disj]
    exact ⟨⟨Or.inr (Or.inr (Or.inl (by omega))),
            Or.inr (Or.inr (Or.inl (by omega))),
            Or.inr (Or.inr (Or.inl (by omega)))⟩,
           ⟨Or.inr (Or.inr (Or.inl (by omega))),
            Or.inr (Or.inr (Or.inl (by omega)))⟩,
           Or.inr (Or.inr (Or.inl (by omega))),
           fun _ h => h.elim⟩
  · intro idx hidx
    have hLi : L[idx] ∈ L ++ I := List.mem_append_left I (List.getElem_mem hidx)
    obtain ⟨hb1, hb2⟩ := hLI_bound L[idx] hLi
    rw [hord_eq idx (by omega), hnodeF_eq L[idx] hb1 hb2 24 (by simp), hnodeF_eq L[idx] hb1 hb2 16 (by simp)]
    exact hL idx hidx
  · intro m hm
    have hmLI : m ∈ L ++ I := List.mem_append_right L hm
    obtain ⟨hb1, hb2⟩ := hLI_bound m hmLI
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hI m hm
    obtain ⟨h8_1, h8_2⟩ := hLI_bound _ c2
    obtain ⟨h16_1, h16_2⟩ := hLI_bound _ c3
    rw [hnodeF_eq m hb1 hb2 24 (by simp), hnodeF_eq m hb1 hb2 8 (by simp), hnodeF_eq m hb1 hb2 16 (by simp),
        hnodeF_eq _ h8_1 h8_2 0 (by simp), hnodeF_eq _ h16_1 h16_2 0 (by simp)]
    exact ⟨c1, c2, c3, c4, c5, c6⟩
  · intro hpos
    obtain ⟨hrm, hrp⟩ := hrpos hpos
    obtain ⟨hb1, hb2⟩ := hLI_bound _ hrm
    rw [hnodeF_eq _ hb1 hb2 0 (by simp)]
    exact ⟨hrm, hrp⟩
  · intro m hm
    have hmLI : m ∈ L ++ I := List.mem_append_right L hm
    obtain ⟨hb1, hb2⟩ := hLI_bound m hmLI
    rw [hnodeF_eq m hb1 hb2 8 (by simp), hnodeF_eq m hb1 hb2 16 (by simp)]
    exact hnroot m hm
  · intro m hm hnr
    obtain ⟨hb1, hb2⟩ := hLI_bound m hm
    rw [hnodeF_eq m hb1 hb2 0 (by simp)]
    exact hpI m hm hnr
  · obtain ⟨dep, hdep⟩ := hdep
    refine ⟨dep, fun m hm hnr => ?_⟩
    obtain ⟨hb1, hb2⟩ := hLI_bound m hm
    have hp_mem : nodeF s (hdr s t 5) m 0 ∈ L ++ I := List.mem_append_right L (hpI m hm hnr)
    obtain ⟨hpb1, hpb2⟩ := hLI_bound _ hp_mem
    rw [hnodeF_eq m hb1 hb2 0 (by simp), hnodeF_eq _ hpb1 hpb2 8 (by simp), hnodeF_eq _ hpb1 hpb2 16 (by simp)]
    exact hdep m hm hnr
  · exact freeChain_congr_eq (fun m h1 h2 => hnodeF_eq m h1 h2 0 (by simp)) Fr _ hFr_bound hfc

/-! ## 3. Symbolic execution helpers for `htab_copy` -/

theorem step_decCall_alloc_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS) (arg : ExpHOL 64) (cont : ProgHOL 64)
    (nv hp : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hA : ArenaReady s)
    (hhp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)))
    (harg : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) arg =
      some (.val (.word nv)))
    (hres : Wave8Contracts.M12.Resumes
      (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [arg] cont)).1) :
    let q := (hp + (nv + 7)) &&& ((0 : BitVec 64) - 8)
    ∃ clk1 : Nat,
      let next : PanSemStateFiniteExact 64 F :=
        { s with
          locals := s.locals.update (x, .val (.word hp))
          globals := s.globals.update (ofString "heap_ptr", .val (.word q))
          clock := clk1 }
      q.toNat = hp.toNat + (nv.toNat + 7) / 8 * 8 ∧
      q.toNat ≤ heapLimit ∧
      q.toNat % 8 = 0 ∧
      hp.toNat ≤ q.toNat ∧
      ArenaReady next ∧
      (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [arg] cont)).1 =
        (evaluateHOLFiniteState next cont).1 ∧
      (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [arg] cont)).2 =
        { (evaluateHOLFiniteState next cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState next cont).2.locals
            (x, s.locals.lookup x) } := by
  dsimp only
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hres ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [arg] =
      some [.val (.word nv)] := by
    simp [evalListHOLFinite, evalListHOLExact, harg]
  have hl := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) nv (by rw [hcode]; exact lookup_alloc_r13)
  rw [hargs] at hres ⊢; dsimp only at hres ⊢; rw [hl] at hres ⊢; dsimp only at hres ⊢
  by_cases hz : s.clock = 0
  · rw [if_pos hz] at hres; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
  · rw [if_neg hz] at hres ⊢
    let centry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv)))
    have hA_ce : ArenaReady centry := ⟨guestInv_callEntry s _ hA.1, hA.2⟩
    have hn_ce : centry.locals.lookup (ofString "n") = some (.val (.word nv)) := by
      simp [centry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hres_ce : Wave8Contracts.M12.Resumes
        (evaluateHOLFiniteState centry (sourceFnBody Guest.Software.guestFn_alloc)).1 := by
      rcases hb : evaluateHOLFiniteState centry (sourceFnBody Guest.Software.guestFn_alloc) with ⟨rb, pb⟩
      dsimp only [centry] at hb; rw [hb] at hres
      cases rb with
      | none => rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | some rb' =>
        cases rb' with
        | returned rv => exact Or.inl ⟨rv, rfl⟩
        | exception eid ev_v =>
          rcases hres with ⟨_, h⟩ | ⟨e', v', h, hntrap⟩
          · simp at h
          · injection h with h1; injection h1 with h2 h3; subst h2 h3
            exact Or.inr ⟨eid, ev_v, rfl, hntrap⟩
        | _ => rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    obtain ⟨p', q', hret_ce, hp'_eq, hq'_eq, hq'_hi, hq'_al, hp'_le, hg_ce, hm_ce, hbe_ce, hma_ce, hA_pb, _, _⟩ :=
      alloc_body_resumes_props centry hcode hA_ce hres_ce
    have hp_ce_eq : p' = hp := by
      apply BitVec.eq_of_toNat_eq
      rw [hp'_eq]; simp [centry, callEntryStateHOLFinite, globN, hhp]
    subst p'
    have hn_ce_nat : locN centry "n" = nv.toNat := by simp [locN, hn_ce]
    rw [hn_ce_nat] at hq'_eq
    rcases hb : evaluateHOLFiniteState
      (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv))))
      (sourceFnBody Guest.Software.guestFn_alloc) with ⟨rb, pb⟩
    have hret_ce' : (evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv))))
        (sourceFnBody Guest.Software.guestFn_alloc)).1 = some (.returned (.val (.word hp))) := hret_ce
    have hg_ce' : (evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv))))
        (sourceFnBody Guest.Software.guestFn_alloc)).2.globals =
        s.globals.update (ofString "heap_ptr", .val (.word q')) := hg_ce
    have hA_pb' : ArenaReady (evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv))))
        (sourceFnBody Guest.Software.guestFn_alloc)).2 := hA_pb
    rw [hb] at hret_ce' hg_ce' hA_pb'
    dsimp only at hret_ce' hg_ce' hA_pb'
    subst hret_ce'
    dsimp only
    have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word hp) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word hp) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh]
    have hrun_exact := alloc_body_run centry hp nv hcode hhp hn_ce (.val (.word hp))
      (by dsimp only [centry]; rw [hb])
    have hpb_struct : pb = { centry with
        globals := centry.globals.update (ofString "heap_ptr", .val (.word ((hp + (nv + 7)) &&& ((0 : BitVec 64) - 8))))
        locals := pb.locals } := by
      have hre := hrun_exact
      dsimp only [centry] at hre; rw [hb] at hre; exact hre.2.2.2
    let q := (hp + (nv + 7)) &&& ((0 : BitVec 64) - 8)
    have hq'_is_q : q' = q := by
      have hg1 : pb.globals.lookup (ofString "heap_ptr") = some (.val (.word q')) := by
        rw [hg_ce']; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hg2 : pb.globals.lookup (ofString "heap_ptr") = some (.val (.word q)) := by
        rw [hpb_struct]; simp [centry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]; rfl
      rw [hg1] at hg2; simp at hg2; exact hg2
    subst hq'_is_q
    have hst_eq : setVarHOLFinite x (.val (.word hp)) { pb with locals := s.locals } =
        { s with
          locals := s.locals.update (x, .val (.word hp))
          globals := s.globals.update (ofString "heap_ptr", .val (.word q))
          clock := pb.clock } := by
      dsimp only [setVarHOLFinite]; rw [hpb_struct]; rfl
    refine ⟨pb.clock, hq'_eq, hq'_hi, hq'_al, hp'_le, ?_, by rw [hst_eq], by rw [hst_eq]⟩
    exact ⟨by rw [← hst_eq]; exact guestInv_setVar _ _ _ (guestInv_with_locals_clock pb s.locals pb.clock hA_pb'.1),
      by rw [← hst_eq]; exact hA_pb'.2⟩

private def noExnProg : ProgHOL 64 → Bool
  | .dec _ _ _ b => noExnProg b
  | .seq a b => noExnProg a && noExnProg b
  | .ite _ a b => noExnProg a && noExnProg b
  | .while _ b => noExnProg b
  | .assign _ _ _ | .store _ _ | .storeByte _ _ | .skip | .return _ => true
  | _ => false

private theorem evaluate_noExnProg {F : Type} (p : ProgHOL 64) (hp : noExnProg p = true)
    (st : PanSemStateFiniteExact 64 F) (e1 : MlS) (v1 : ValueHOL 64) :
    (evaluateHOLFiniteState st p).1 ≠ some (.exception e1 v1) := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; simp
  | assign _ _ _ =>
    rw [evaluateHOLFiniteState_assign]
    split <;> [simp; (split <;> simp)]
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split <;> [ (split <;> [ (split <;> simp) ; simp ]) ; simp ]
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split <;> [ (split <;> [ (split <;> simp) ; simp ]) ; simp ]
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split <;> [simp; (split <;> simp)]
  | dec x _ _ b =>
    have hb : noExnProg b = true := by simpa [shape, noExnProg] using hp
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · simp
    · split
      · rename_i val _ _
        have mclk : (setVarHOLFinite x val st).clock ≤ st.clock := le_rfl
        exact evaluate_noExnProg b hb (setVarHOLFinite x val st) e1 v1
      · simp
  | seq a b =>
    obtain ⟨ha, hb⟩ : noExnProg a = true ∧ noExnProg b = true := by simpa [shape, noExnProg] using hp
    have rem := evaluateHOLFiniteState_clock_le st a
    rw [evaluateHOLFiniteState_seq_line780]
    have iha := evaluate_noExnProg a ha st e1 v1
    rcases hra : evaluateHOLFiniteState st a with ⟨r1, m⟩
    rw [hra] at iha rem
    cases r1 with
    | none =>
      have mclk : m.clock ≤ st.clock := rem
      exact evaluate_noExnProg b hb m e1 v1
    | some _ => exact iha
  | ite _ a b =>
    obtain ⟨ha, hb⟩ : noExnProg a = true ∧ noExnProg b = true := by simpa [shape, noExnProg] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noExnProg b hb st e1 v1
      · exact evaluate_noExnProg a ha st e1 v1
    · simp
  | «while» cond body =>
    have hb : noExnProg body = true := by simpa [shape, noExnProg] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · rename_i nonzero
          have dec_lt : (decClockHOLFinite st).clock < st.clock := by
            simp only [decClockHOLFinite]; omega
          dsimp only; rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noExnProg body hb (decClockHOLFinite st) e1 v1
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < st.clock := by
            change mid.clock ≤ st.clock - 1 at rem; omega
          cases r1 with
          | none =>
            exact evaluate_noExnProg (.while cond body) (by simpa [noExnProg] using hb) mid e1 v1
          | some r1 =>
            cases r1 with
            | «continue» =>
              exact evaluate_noExnProg (.while cond body) (by simpa [noExnProg] using hb) mid e1 v1
            | «break» | returned _ | timeOut | error | finalFfi _ => simp
            | exception _ _ => exact ih1
      · simp
    · simp
  | _ => simp [shape, noExnProg] at hp
termination_by (st.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

theorem step_call_memcpy_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (dstExp srcExp nExp : ExpHOL 64) (cont : ProgHOL 64)
    (dst0 src0 n0 : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hA : ArenaReady s)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp =
      some (.val (.word src0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hres : Wave8Contracts.M12.Resumes
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) cont)).1) :
    ∃ t : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) = (none, t) ∧
      t.locals = s.locals ∧
      t.globals = s.globals ∧
      ArenaReady t ∧
      MemWriteFrame s t (dst0.toNat, n0.toNat) ∧
      BytesCopiedUpTo s t dst0 src0 n0.toNat n0.toNat ∧
      (0 < n0.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapEnd) ∧
      evaluateHOLFiniteState s (.seq (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) cont) =
        evaluateHOLFiniteState t cont := by
  rw [evaluateHOLFiniteState_seq_line780] at hres
  rcases hcall : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) with ⟨rc, t⟩
  rw [hcall] at hres
  cases rc with
  | none =>
    obtain ⟨hloc, hmwf, hcp, hdom⟩ := call_memcpy_step s dstExp srcExp nExp dst0 src0 n0 hcode hA.1 hdst hsrc hn t hcall
    have hGt : GuestInv t := guestInv_congr hmwf.1 hmwf.2.1 hmwf.2.2.1 hmwf.2.2.2.1 hA.1
    have hAt : ArenaReady t := ⟨hGt, arenaOK_congr hmwf.2.2.2.2.2.1 hA.2⟩
    refine ⟨t, rfl, hloc, hmwf.2.2.2.2.2.1, hAt, hmwf, hcp, hdom, ?_⟩
    rw [evaluateHOLFiniteState_seq_line780, hcall]
  | some rc' =>
    exfalso
    dsimp only at hres
    rw [evaluateHOLFiniteState_call] at hcall
    have hevargs : @evalListHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        [dstExp, srcExp, nExp] = some [.val (.word dst0), .val (.word src0), .val (.word n0)] := by
      rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, hdst, hsrc, hn]
    have hlook := pan_three_word_lookup s.code.lookup (ofString "memcpy")
      (ofString "dst") (ofString "src") (ofString "n") (sourceFnBody Guest.Software.guestFn_memcpy)
      dst0 src0 n0 (by decide) (by decide) (by decide) (by rw [hcode]; exact lookup_memcpy)
    rw [hevargs] at hcall; dsimp only at hcall; rw [hlook] at hcall; dsimp only at hcall
    split at hcall
    · injection hcall with hr _; injection hr with hr'; subst hr'
      rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    · let cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
        ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word dst0))).update
          (ofString "src", .val (.word src0))).update (ofString "n", .val (.word n0))
      let entry := callEntryStateHOLFinite s cmap
      rcases hran : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_memcpy) with ⟨res, post⟩
      dsimp only [entry] at hran; rw [hran] at hcall
      cases res with
      | none => injection hcall with hr _; injection hr with hr'; subst hr'; exact not_resumes_error hres
      | some r =>
        cases r with
        | returned rv =>
          dsimp only at hcall
          split at hcall
          · simp at hcall
          · injection hcall with hr _; injection hr with hr'; subst hr'; exact not_resumes_error hres
        | exception eid ev_v =>
          exact evaluate_noExnProg (sourceFnBody Guest.Software.guestFn_memcpy) rfl entry eid ev_v
            (by dsimp only [entry]; rw [hran])
        | _ =>
          dsimp only at hcall
          injection hcall with hr _; injection hr with hr'; subst hr'
          rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

theorem step_call_memcpy_load_t_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (dstExp nExp : ExpHOL 64) (off : BitVec 64) (cont : ProgHOL 64)
    (dst0 tw n0 : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hA : ArenaReady s)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (ht : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hres : Wave8Contracts.M12.Resumes
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) (ofString "memcpy")
        [dstExp, .load .one (.op .add [.var .local (ofString "t"), .const off]), nExp]) cont)).1) :
    ∃ (src0 : BitVec 64) (t : PanSemStateFiniteExact 64 F),
      s.memaddrs (tw + off) ∧
      s.memory (tw + off) = .word src0 ∧
      t.locals = s.locals ∧
      t.globals = s.globals ∧
      ArenaReady t ∧
      MemWriteFrame s t (dst0.toNat, n0.toNat) ∧
      BytesCopiedUpTo s t dst0 src0 n0.toNat n0.toNat ∧
      evaluateHOLFiniteState s (.seq (.call (some (none, none)) (ofString "memcpy")
        [dstExp, .load .one (.op .add [.var .local (ofString "t"), .const off]), nExp]) cont) =
        evaluateHOLFiniteState t cont := by
  have hdom : s.memaddrs (tw + off) := by
    by_contra hndom
    have hnone_ld : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "t"), .const off])) = none := by
      simp [evalHOLExact, evalListHOLExact, isWfShapeExactHOL, ht, valueIsWord, valueWord,
        wordOpHOL, wordOp, memLoadHOLExact, panMemLoadHOL, hndom]
    have hnone_args : @evalListHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        [dstExp, .load .one (.op .add [.var .local (ofString "t"), .const off]), nExp] = none := by
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact, hdst, hnone_ld]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call, hnone_args] at hres
    exact not_resumes_error hres
  have hex_w : ∃ src0, s.memory (tw + off) = .word src0 := by
    rcases hm : s.memory (tw + off) with ⟨src0⟩; exact ⟨src0, rfl⟩
  obtain ⟨src0, hm⟩ := hex_w
  have hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "t"), .const off])) = some (.val (.word src0)) := by
    simp [evalHOLExact, evalListHOLExact, isWfShapeExactHOL, ht, valueIsWord, valueWord,
      wordOpHOL, wordOp, memLoadHOLExact, panMemLoadHOL, hdom, hm]
  obtain ⟨t, _, hloc, hglob, hAt, hmwf, hcp, _, hseq⟩ :=
    step_call_memcpy_resumes s dstExp _ nExp cont dst0 src0 n0 hcode hA hdst hsrc hn hres
  exact ⟨src0, t, hdom, hm, hloc, hglob, hAt, hmwf, hcp, hseq⟩

theorem step_store_word_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp valExp : ExpHOL 64) (cont : ProgHOL 64)
    (addr val : BitVec 64)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word addr)))
    (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some (.val (.word val)))
    (hres : Wave8Contracts.M12.Resumes
      (evaluateHOLFiniteState s (.seq (.store dstExp valExp) cont)).1) :
    s.memaddrs addr ∧
    evaluateHOLFiniteState s (.seq (.store dstExp valExp) cont) =
      evaluateHOLFiniteState { s with memory := updW s.memory addr val } cont := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store, hdst, hval] at hres ⊢
  dsimp only at hres ⊢
  rcases hst : @panMemStoresHOL 64 _ addr (flattenHOL (.val (.word val))) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory with _ | m'
  · rw [hst] at hres; exact False.elim (not_resumes_error hres)
  · obtain ⟨hdom, rfl⟩ := stores_word (fun a => Classical.propDecidable (s.memaddrs a)) hst
    exact ⟨hdom, rfl⟩

theorem disj_fresh_of_allocated {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {ivl dst : Ivl}
    (hal : Allocated s ivl)
    (hdst : Inside dst (globN s "heap_ptr") heapLimit) :
    Disj dst ivl := by
  rcases hal with ⟨_, hhi⟩ | ⟨hlo, _⟩
  · exact Or.inr (Or.inr (Or.inr (by unfold Inside at hdst; omega)))
  · have hss : heapLimit = scratchStart := rfl
    have hfmp := hA.2.2.1
    have hsp := hA.2.2.2.1
    exact Or.inr (Or.inr (Or.inl (by unfold Inside at hdst; omega)))

theorem not_cellHits_heapFree_of_allocated_word {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {base len off : Nat}
    (hal : Allocated s (base, len)) (hoff : off + 8 ≤ len) :
    ¬ CellHits (base + off) (Wave8Contracts.M12.heapFree s) := by
  intro ⟨hc1, hc2⟩
  unfold Wave8Contracts.M12.heapFree at hc1 hc2
  have hhp_hi := hA.2.1
  rcases hal with ⟨_, hhi⟩ | ⟨hlo, _⟩
  · omega
  · have hss : heapLimit = scratchStart := rfl
    have hfmp := hA.2.2.1
    have hsp := hA.2.2.2.1
    omega

/-! ## 4. Main symbolic execution theorem for `htab_copy` -/

theorem htab_copy_resumes_props {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hA : ArenaReady s)
    (ht : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hres : Wave8Contracts.M12.Resumes
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_copy)).1) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_copy)
    ∃ (p1 q4 : BitVec 64),
      out.1 = some (.returned (.val (.word p1))) ∧
      locN s "t" ≠ 0 ∧
      p1.toNat = globN s "heap_ptr" ∧
      q4.toNat = globN out.2 "heap_ptr" ∧
      p1.toNat ≤ q4.toNat ∧
      q4.toNat ≤ heapLimit ∧
      ArenaReady out.2 ∧
      AllocatorGrows s out.2 ∧
      Wave8Contracts.M12.GlobalsKept ["heap_ptr"] s out.2 ∧
      MemOnlyFrame s out.2 (Wave8Contracts.M12.heapFree s) ∧
      (HtabWF s (locN s "t") → (∀ i ∈ htabFootprint s (locN s "t"), Allocated s i) →
        HtabWF out.2 p1.toNat ∧
        hdr out.2 p1.toNat 3 = hdr s (locN s "t") 3 ∧
        (∀ i ∈ htabFootprint out.2 p1.toNat,
          Inside i (globN s "heap_ptr") (globN out.2 "heap_ptr"))) := by
  dsimp only
  have ht_loc : locN s "t" = tw.toNat := by simp [locN, ht]
  have hb : sourceFnBody Guest.Software.guestFn_htab_copy =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_htab_copy).body := rfl
  rw [hb] at hres
  dsimp only [extractFn, Guest.Software.guestFn_htab_copy,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map] at hres
  -- 1. `dec "nodecap" (load (t + 80))`
  rw [evaluateHOLFiniteState_dec_total] at hres; dsimp only at hres
  have hdom_t80 : s.memaddrs (tw + 80#64) := by
    by_contra hndom
    have hnone_ld : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "t"), .const 80#64])) = none := by
      simp [evalHOLExact, evalListHOLExact, isWfShapeExactHOL, ht, valueIsWord, valueWord,
        wordOpHOL, wordOp, memLoadHOLExact, panMemLoadHOL, hndom]
    rw [hnone_ld] at hres
    exact not_resumes_error hres
  have ht_ne0 : locN s "t" ≠ 0 := by
    rw [ht_loc]
    intro h0
    have htw0 : tw = 0 := BitVec.eq_of_toNat_eq h0
    subst htw0
    have hd := hA.1.memaddrs ▸ hdom_t80
    rw [Wave8Contracts.M12.ordinaryDomain_iff] at hd
    have h80 : ((0 : BitVec 64) + 80#64).toNat = 80 := rfl
    rw [h80] at hd; omega
  have hex_ncap : ∃ w_ncap, s.memory (tw + 80#64) = .word w_ncap := by
    rcases s.memory (tw + 80#64) with ⟨w_ncap⟩; exact ⟨w_ncap, rfl⟩
  obtain ⟨w_ncap, hm_t80⟩ := hex_ncap
  have hev_t80 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "t"), .const 80#64])) =
      some (.val (.word w_ncap)) := by
    simp [evalHOLExact, evalListHOLExact, isWfShapeExactHOL, ht, valueIsWord, valueWord,
      wordOpHOL, wordOp, memLoadHOLExact, panMemLoadHOL, hdom_t80, hm_t80]
  have hsh_ncap : shapeEqHOL .one (shapeOfHOLExact (.val (.word w_ncap) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  have hdec1_eq :
      evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_copy) =
      let s_nc := setVarHOLFinite (ofString "nodecap") (.val (.word w_ncap)) s
      let r := evaluateHOLFiniteState s_nc
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
          (match (extractFn Guest.Software.guestFn_htab_copy).body with
           | .dec _ _ _ b => b
           | _ => .skip))
      (r.1, { r.2 with locals := HolFiniteMapExact.resVarEq r.2.locals (ofString "nodecap", s.locals.lookup (ofString "nodecap")) }) := by
    conv_lhs =>
      rw [hb]
      dsimp only [extractFn, Guest.Software.guestFn_htab_copy,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
      rw [evaluateHOLFiniteState_dec_total]
      dsimp only
    rw [hev_t80]; dsimp only; rw [if_pos hsh_ncap]; rfl
  rw [hev_t80] at hres; dsimp only at hres; rw [if_pos hsh_ncap] at hres; dsimp only at hres
  set s_nc := setVarHOLFinite (ofString "nodecap") (.val (.word w_ncap)) s
  -- 2. `dec "stride" (load (t + 8))`
  rw [evaluateHOLFiniteState_dec_total] at hres; dsimp only at hres
  have ht_nc : s_nc.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [s_nc, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht,
      show ofString "nodecap" ≠ ofString "t" by decide]
  have hdom_t8 : s.memaddrs (tw + 8#64) := by
    by_contra hndom
    have hd_nc : ¬ s_nc.memaddrs (tw + 8#64) := hndom
    have hnone_ld : @evalHOLExact 64 F _ s_nc.toExact (fun a => Classical.propDecidable (s_nc.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "t"), .const 8#64])) = none := by
      simp [evalHOLExact, evalListHOLExact, isWfShapeExactHOL, ht_nc, valueIsWord, valueWord,
        wordOpHOL, wordOp, memLoadHOLExact, panMemLoadHOL, hd_nc]
    rw [hnone_ld] at hres
    exact not_resumes_error hres
  have hex_stride : ∃ w_stride, s.memory (tw + 8#64) = .word w_stride := by
    rcases s.memory (tw + 8#64) with ⟨w_stride⟩; exact ⟨w_stride, rfl⟩
  obtain ⟨w_stride, hm_t8⟩ := hex_stride
  have hev_t8 : @evalHOLExact 64 F _ s_nc.toExact (fun a => Classical.propDecidable (s_nc.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "t"), .const 8#64])) =
      some (.val (.word w_stride)) := by
    have hd_nc : s_nc.memaddrs (tw + 8#64) := hdom_t8
    have hm_nc : s_nc.memory (tw + 8#64) = .word w_stride := hm_t8
    simp [evalHOLExact, evalListHOLExact, isWfShapeExactHOL, ht_nc, valueIsWord, valueWord,
      wordOpHOL, wordOp, memLoadHOLExact, panMemLoadHOL, hd_nc, hm_nc]
  have hsh_stride : shapeEqHOL .one (shapeOfHOLExact (.val (.word w_stride) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  rw [hev_t8] at hres; dsimp only at hres; rw [if_pos hsh_stride] at hres; dsimp only at hres
  set s0 := setVarHOLFinite (ofString "stride") (.val (.word w_stride)) s_nc
  let bodyRest : ProgHOL 64 :=
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (match (extractFn Guest.Software.guestFn_htab_copy).body with
       | .dec _ _ _ (.dec _ _ _ b) => b
       | _ => .skip)
  have hdec2_eq :
      evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_copy) =
      let r := evaluateHOLFiniteState s0 bodyRest
      (r.1, { r.2 with
        locals :=
          HolFiniteMapExact.resVarEq
            (HolFiniteMapExact.resVarEq r.2.locals (ofString "stride", s_nc.locals.lookup (ofString "stride")))
            (ofString "nodecap", s.locals.lookup (ofString "nodecap")) }) := by
    rw [hdec1_eq]; dsimp only
    conv_lhs =>
      dsimp only [extractFn, Guest.Software.guestFn_htab_copy,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
      rw [evaluateHOLFiniteState_dec_total]; dsimp only
    rw [hev_t8]; dsimp only; rw [if_pos hsh_stride]; rfl
  have hA0 : ArenaReady s0 := ⟨guestInv_setVar _ _ _ (guestInv_setVar _ _ _ hA.1), hA.2⟩
  obtain ⟨p1, _, _, hhp1_s, hhp1_eq, _, _, _, _⟩ := arenaOK_globals s hA.2
  rcases hA.2 with ⟨hsb_s, _, _, _, _, hhp_al_s, _, _⟩
  have hp1_al : p1.toNat % 8 = 0 := by rw [hhp1_eq]; exact hhp_al_s
  have hp1_sb : sourceBase ≤ p1.toNat := by rw [hhp1_eq]; exact hsb_s
  have hhp0 : s0.globals.lookup (ofString "heap_ptr") = some (.val (.word p1)) := hhp1_s
  set hf_s : Ivl := Wave8Contracts.M12.heapFree s
  have hhl_val : heapLimit = 2952790016 := rfl
  -- Phase 1: `decCall "n" .one "alloc" [88]`
  obtain ⟨clk1, hq1_eq, hq1_hi, hq1_al, hp1_le_q1, hA1, hr_eq1, hp_eq1⟩ :=
    step_decCall_alloc_resumes s0 (ofString "n") (.const 88#64) _ 88#64 p1 hcode hA0 hhp0 rfl hres
  rw [hr_eq1] at hres
  set p2 := (p1 + (88#64 + 7)) &&& ((0 : BitVec 64) - 8)
  have h88_r : ((88#64 : BitVec 64).toNat + 7) / 8 * 8 = 88 := by decide
  rw [h88_r] at hq1_eq
  set s1 : PanSemStateFiniteExact 64 F :=
    { s0 with
      locals := s0.locals.update (ofString "n", .val (.word p1))
      globals := s0.globals.update (ofString "heap_ptr", .val (.word p2))
      clock := clk1 }
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word p1)) := by
    simp [s1, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_t : s1.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [s1, s0, s_nc, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht,
      show ofString "n" ≠ ofString "t" by decide,
      show ofString "stride" ≠ ofString "t" by decide,
      show ofString "nodecap" ≠ ofString "t" by decide]
  have hs1_nc : s1.locals.lookup (ofString "nodecap") = some (.val (.word w_ncap)) := by
    simp [s1, s0, s_nc, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "nodecap" by decide,
      show ofString "stride" ≠ ofString "nodecap" by decide]
  have hs1_st : s1.locals.lookup (ofString "stride") = some (.val (.word w_stride)) := by
    simp [s1, s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "stride" by decide]
  -- `memcpy(n, t, 88)`
  obtain ⟨s2, _, hs2_loc, hs2_glob, hA2, hmwf1, hcp1, _, hseq1_eq⟩ :=
    step_call_memcpy_resumes s1 (.var .local (ofString "n")) (.var .local (ofString "t")) (.const 88#64) _
      p1 tw 88#64 hcode hA1
      (by simp [evalHOLExact, hs1_n]) (by simp [evalHOLExact, hs1_t]) rfl hres
  rw [hseq1_eq] at hres
  have hmof_s_s2 : MemOnlyFrame s s2 hf_s := by
    have h88_nat : (88#64 : BitVec 64).toNat = 88 := rfl
    exact MemOnlyFrame.trans (s1 := s1)
      ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ h => absurd rfl h⟩
      (MemOnlyFrame.of_mwf hmwf1) (Or.inl rfl)
      (Or.inr ⟨by unfold hf_s Wave8Contracts.M12.heapFree; omega,
               by unfold hf_s Wave8Contracts.M12.heapFree; rw [h88_nat]; omega⟩)
  -- Phase 2: `decCall "keys" .one "alloc" [(nodecap + 1) * stride]`
  let w_klen_alloc : BitVec 64 := (w_ncap + 1#64) * w_stride
  have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word p1)) := hs2_loc ▸ hs1_n
  have hs2_t : s2.locals.lookup (ofString "t") = some (.val (.word tw)) := hs2_loc ▸ hs1_t
  have hs2_nc : s2.locals.lookup (ofString "nodecap") = some (.val (.word w_ncap)) := hs2_loc ▸ hs1_nc
  have hs2_st : s2.locals.lookup (ofString "stride") = some (.val (.word w_stride)) := hs2_loc ▸ hs1_st
  have hs2_code : s2.code = originalRuntimeCode := hmof_s_s2.code.trans hcode
  have hev_klen2 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
      (.panop .mul [.op .add [.var .local (ofString "nodecap"), .const 1#64], .var .local (ofString "stride")]) =
      some (.val (.word w_klen_alloc)) := by
    simp [evalHOLExact, evalListHOLExact, hs2_nc, hs2_st, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, w_klen_alloc]
  have hs2_hp : s2.globals.lookup (ofString "heap_ptr") = some (.val (.word p2)) := by
    rw [hs2_glob]; simp [s1, HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨clk3, hq2_eq, hq2_hi, hq2_al, hp2_le_q2, hA3, hr_eq2, hp_eq2⟩ :=
    step_decCall_alloc_resumes s2 (ofString "keys") _ _ w_klen_alloc p2 hs2_code hA2 hs2_hp hev_klen2 hres
  rw [hr_eq2] at hres
  set p3 := (p2 + (w_klen_alloc + 7)) &&& ((0 : BitVec 64) - 8)
  set s3 : PanSemStateFiniteExact 64 F :=
    { s2 with
      locals := s2.locals.update (ofString "keys", .val (.word p2))
      globals := s2.globals.update (ofString "heap_ptr", .val (.word p3))
      clock := clk3 }
  have hs3_keys : s3.locals.lookup (ofString "keys") = some (.val (.word p2)) := by
    simp [s3, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs3_n : s3.locals.lookup (ofString "n") = some (.val (.word p1)) := by
    simp [s3, HolFiniteMapExact.lookup_update, FUPDATE, hs2_n, show ofString "keys" ≠ ofString "n" by decide]
  have hs3_t : s3.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [s3, HolFiniteMapExact.lookup_update, FUPDATE, hs2_t, show ofString "keys" ≠ ofString "t" by decide]
  have hs3_nc : s3.locals.lookup (ofString "nodecap") = some (.val (.word w_ncap)) := by
    simp [s3, HolFiniteMapExact.lookup_update, FUPDATE, hs2_nc, show ofString "keys" ≠ ofString "nodecap" by decide]
  have hs3_st : s3.locals.lookup (ofString "stride") = some (.val (.word w_stride)) := by
    simp [s3, HolFiniteMapExact.lookup_update, FUPDATE, hs2_st, show ofString "keys" ≠ ofString "stride" by decide]
  have hev_klen3 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
      (.panop .mul [.op .add [.var .local (ofString "nodecap"), .const 1#64], .var .local (ofString "stride")]) =
      some (.val (.word w_klen_alloc)) := by
    simp [evalHOLExact, evalListHOLExact, hs3_nc, hs3_st, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, w_klen_alloc]
  -- `memcpy(keys, load(t + 32), (nodecap + 1) * stride)`
  obtain ⟨src_keys, s4, _, hm_t32_s3, hs4_loc, hs4_glob, hA4, hmwf2, hcp2, hseq2_eq⟩ :=
    step_call_memcpy_load_t_resumes s3 (.var .local (ofString "keys")) _ 32#64 _
      p2 tw w_klen_alloc hs2_code hA3 (by simp [evalHOLExact, hs3_keys]) hs3_t hev_klen3 hres
  rw [hseq2_eq] at hres
  have hmof_s2_s4 : MemOnlyFrame s2 s4 (p2.toNat, w_klen_alloc.toNat) :=
    MemOnlyFrame.trans (s1 := s3)
      ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ h => absurd rfl h⟩
      (MemOnlyFrame.of_mwf hmwf2) (Or.inl rfl) (Or.inr ⟨le_rfl, le_rfl⟩)
  -- `store (n + 32) keys`
  have hs4_n : s4.locals.lookup (ofString "n") = some (.val (.word p1)) := hs4_loc ▸ hs3_n
  have hs4_keys : s4.locals.lookup (ofString "keys") = some (.val (.word p2)) := hs4_loc ▸ hs3_keys
  obtain ⟨hdom_p1_32, hst32_eq⟩ := step_store_word_resumes s4
    (.op .add [.var .local (ofString "n"), .const 32#64]) (.var .local (ofString "keys")) _
    (p1 + 32#64) p2
    (by simp [evalHOLExact, evalListHOLExact, hs4_n, valueIsWord, valueWord, wordOpHOL, wordOp])
    (by simp [evalHOLExact, hs4_keys]) hres
  rw [hst32_eq] at hres
  set s5 : PanSemStateFiniteExact 64 F := { s4 with memory := updW s4.memory (p1 + 32#64) p2 }
  have hp1_32_nat : (p1 + 32#64).toNat = p1.toNat + 32 :=
    BitVec.toNat_add_of_lt (by change p1.toNat + 32 < 2 ^ 64; omega)
  have hmof_s_s5 : MemOnlyFrame s s5 hf_s := by
    have hmof_s_s4 : MemOnlyFrame s s4 hf_s :=
      MemOnlyFrame.trans hmof_s_s2 hmof_s2_s4
        (Or.inr ⟨le_rfl, le_rfl⟩)
        (Or.inr ⟨by unfold hf_s Wave8Contracts.M12.heapFree; omega,
                 by unfold hf_s Wave8Contracts.M12.heapFree; omega⟩)
    exact MemOnlyFrame.updW_step hmof_s_s4 (p1 + 32#64) p2 hdom_p1_32
      (by rw [hp1_32_nat]; omega)
      ⟨by unfold hf_s Wave8Contracts.M12.heapFree; rw [hp1_32_nat]; omega,
       by unfold hf_s Wave8Contracts.M12.heapFree; rw [hp1_32_nat]; omega⟩
  have hA5 : ArenaReady s5 := ⟨⟨hA4.1.code, hA4.1.memaddrs, hA4.1.shMemaddrs, hA4.1.baseAddr⟩, hA4.2⟩
  -- Phase 3: `decCall "nodes" .one "alloc" [(nodecap + 1) * 32]`
  let w_nlen_alloc : BitVec 64 := (w_ncap + 1#64) * 32#64
  have hs5_n : s5.locals.lookup (ofString "n") = some (.val (.word p1)) := hs4_n
  have hs5_t : s5.locals.lookup (ofString "t") = some (.val (.word tw)) := hs4_loc ▸ hs3_t
  have hs5_nc : s5.locals.lookup (ofString "nodecap") = some (.val (.word w_ncap)) := hs4_loc ▸ hs3_nc
  have hs5_code : s5.code = originalRuntimeCode := hmof_s_s5.code.trans hcode
  have hev_nlen5 : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
      (.panop .mul [.op .add [.var .local (ofString "nodecap"), .const 1#64], .const 32#64]) =
      some (.val (.word w_nlen_alloc)) := by
    simp [evalHOLExact, evalListHOLExact, hs5_nc, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, w_nlen_alloc]
  have hs5_hp : s5.globals.lookup (ofString "heap_ptr") = some (.val (.word p3)) := by
    change s4.globals.lookup (ofString "heap_ptr") = _; rw [hs4_glob]
    simp [s3, HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨clk6, hq3_eq, hq3_hi, hq3_al, hp3_le_q3, hA6, hr_eq3, hp_eq3⟩ :=
    step_decCall_alloc_resumes s5 (ofString "nodes") _ _ w_nlen_alloc p3 hs5_code hA5 hs5_hp hev_nlen5 hres
  rw [hr_eq3] at hres
  set p4 := (p3 + (w_nlen_alloc + 7)) &&& ((0 : BitVec 64) - 8)
  set s6 : PanSemStateFiniteExact 64 F :=
    { s5 with
      locals := s5.locals.update (ofString "nodes", .val (.word p3))
      globals := s5.globals.update (ofString "heap_ptr", .val (.word p4))
      clock := clk6 }
  have hs6_nodes : s6.locals.lookup (ofString "nodes") = some (.val (.word p3)) := by
    simp [s6, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs6_n : s6.locals.lookup (ofString "n") = some (.val (.word p1)) := by
    simp [s6, HolFiniteMapExact.lookup_update, FUPDATE, hs5_n, show ofString "nodes" ≠ ofString "n" by decide]
  have hs6_t : s6.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [s6, HolFiniteMapExact.lookup_update, FUPDATE, hs5_t, show ofString "nodes" ≠ ofString "t" by decide]
  have hs6_nc : s6.locals.lookup (ofString "nodecap") = some (.val (.word w_ncap)) := by
    simp [s6, HolFiniteMapExact.lookup_update, FUPDATE, hs5_nc, show ofString "nodes" ≠ ofString "nodecap" by decide]
  have hev_nlen6 : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a))
      (.panop .mul [.op .add [.var .local (ofString "nodecap"), .const 1#64], .const 32#64]) =
      some (.val (.word w_nlen_alloc)) := by
    simp [evalHOLExact, evalListHOLExact, hs6_nc, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, w_nlen_alloc]
  -- `memcpy(nodes, load(t + 40), (nodecap + 1) * 32)`
  obtain ⟨src_nodes, s7, _, hm_t40_s6, hs7_loc, hs7_glob, hA7, hmwf3, hcp3, hseq3_eq⟩ :=
    step_call_memcpy_load_t_resumes s6 (.var .local (ofString "nodes")) _ 40#64 _
      p3 tw w_nlen_alloc hs5_code hA6 (by simp [evalHOLExact, hs6_nodes]) hs6_t hev_nlen6 hres
  rw [hseq3_eq] at hres
  have hmof_s5_s7 : MemOnlyFrame s5 s7 (p3.toNat, w_nlen_alloc.toNat) :=
    MemOnlyFrame.trans (s1 := s6)
      ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ h => absurd rfl h⟩
      (MemOnlyFrame.of_mwf hmwf3) (Or.inl rfl) (Or.inr ⟨le_rfl, le_rfl⟩)
  -- `store (n + 40) nodes`
  have hs7_n : s7.locals.lookup (ofString "n") = some (.val (.word p1)) := hs7_loc ▸ hs6_n
  have hs7_nodes : s7.locals.lookup (ofString "nodes") = some (.val (.word p3)) := hs7_loc ▸ hs6_nodes
  obtain ⟨hdom_p1_40, hst40_eq⟩ := step_store_word_resumes s7
    (.op .add [.var .local (ofString "n"), .const 40#64]) (.var .local (ofString "nodes")) _
    (p1 + 40#64) p3
    (by simp [evalHOLExact, evalListHOLExact, hs7_n, valueIsWord, valueWord, wordOpHOL, wordOp])
    (by simp [evalHOLExact, hs7_nodes]) hres
  rw [hst40_eq] at hres
  set s8 : PanSemStateFiniteExact 64 F := { s7 with memory := updW s7.memory (p1 + 40#64) p3 }
  have hp1_40_nat : (p1 + 40#64).toNat = p1.toNat + 40 :=
    BitVec.toNat_add_of_lt (by change p1.toNat + 40 < 2 ^ 64; omega)
  have hmof_s_s8 : MemOnlyFrame s s8 hf_s := by
    have hmof_s_s7 : MemOnlyFrame s s7 hf_s :=
      MemOnlyFrame.trans hmof_s_s5 hmof_s5_s7
        (Or.inr ⟨le_rfl, le_rfl⟩)
        (Or.inr ⟨by unfold hf_s Wave8Contracts.M12.heapFree; omega,
                 by unfold hf_s Wave8Contracts.M12.heapFree; omega⟩)
    exact MemOnlyFrame.updW_step hmof_s_s7 (p1 + 40#64) p3 hdom_p1_40
      (by rw [hp1_40_nat]; omega)
      ⟨by unfold hf_s Wave8Contracts.M12.heapFree; rw [hp1_40_nat]; omega,
       by unfold hf_s Wave8Contracts.M12.heapFree; rw [hp1_40_nat]; omega⟩
  have hA8 : ArenaReady s8 := ⟨⟨hA7.1.code, hA7.1.memaddrs, hA7.1.shMemaddrs, hA7.1.baseAddr⟩, hA7.2⟩
  -- Phase 4: `decCall "order" .one "alloc" [(nodecap + 1) * 8]`
  let w_olen_alloc : BitVec 64 := (w_ncap + 1#64) * 8#64
  have hs8_n : s8.locals.lookup (ofString "n") = some (.val (.word p1)) := hs7_n
  have hs8_t : s8.locals.lookup (ofString "t") = some (.val (.word tw)) := hs7_loc ▸ hs6_t
  have hs8_nc : s8.locals.lookup (ofString "nodecap") = some (.val (.word w_ncap)) := hs7_loc ▸ hs6_nc
  have hs8_code : s8.code = originalRuntimeCode := hmof_s_s8.code.trans hcode
  have hev_olen8 : @evalHOLExact 64 F _ s8.toExact (fun a => Classical.propDecidable (s8.memaddrs a))
      (.panop .mul [.op .add [.var .local (ofString "nodecap"), .const 1#64], .const 8#64]) =
      some (.val (.word w_olen_alloc)) := by
    simp [evalHOLExact, evalListHOLExact, hs8_nc, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, w_olen_alloc]
  have hs8_hp : s8.globals.lookup (ofString "heap_ptr") = some (.val (.word p4)) := by
    change s7.globals.lookup (ofString "heap_ptr") = _; rw [hs7_glob]
    simp [s6, HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨clk9, hq4_eq, hq4_hi, hq4_al, hp4_le_q4, hA9, hr_eq4, hp_eq4⟩ :=
    step_decCall_alloc_resumes s8 (ofString "order") _ _ w_olen_alloc p4 hs8_code hA8 hs8_hp hev_olen8 hres
  rw [hr_eq4] at hres
  set q4 := (p4 + (w_olen_alloc + 7)) &&& ((0 : BitVec 64) - 8)
  set s9 : PanSemStateFiniteExact 64 F :=
    { s8 with
      locals := s8.locals.update (ofString "order", .val (.word p4))
      globals := s8.globals.update (ofString "heap_ptr", .val (.word q4))
      clock := clk9 }
  have hs9_order : s9.locals.lookup (ofString "order") = some (.val (.word p4)) := by
    simp [s9, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs9_n : s9.locals.lookup (ofString "n") = some (.val (.word p1)) := by
    simp [s9, HolFiniteMapExact.lookup_update, FUPDATE, hs8_n, show ofString "order" ≠ ofString "n" by decide]
  have hs9_t : s9.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [s9, HolFiniteMapExact.lookup_update, FUPDATE, hs8_t, show ofString "order" ≠ ofString "t" by decide]
  have hs9_nc : s9.locals.lookup (ofString "nodecap") = some (.val (.word w_ncap)) := by
    simp [s9, HolFiniteMapExact.lookup_update, FUPDATE, hs8_nc, show ofString "order" ≠ ofString "nodecap" by decide]
  have hev_olen9 : @evalHOLExact 64 F _ s9.toExact (fun a => Classical.propDecidable (s9.memaddrs a))
      (.panop .mul [.op .add [.var .local (ofString "nodecap"), .const 1#64], .const 8#64]) =
      some (.val (.word w_olen_alloc)) := by
    simp [evalHOLExact, evalListHOLExact, hs9_nc, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, w_olen_alloc]
  -- `memcpy(order, load(t + 48), (nodecap + 1) * 8)`
  obtain ⟨src_order, s10, _, hm_t48_s9, hs10_loc, hs10_glob, hA10, hmwf4, hcp4, hseq4_eq⟩ :=
    step_call_memcpy_load_t_resumes s9 (.var .local (ofString "order")) _ 48#64 _
      p4 tw w_olen_alloc hs8_code hA9 (by simp [evalHOLExact, hs9_order]) hs9_t hev_olen9 hres
  rw [hseq4_eq] at hres
  have hmof_s8_s10 : MemOnlyFrame s8 s10 (p4.toNat, w_olen_alloc.toNat) :=
    MemOnlyFrame.trans (s1 := s9)
      ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ h => absurd rfl h⟩
      (MemOnlyFrame.of_mwf hmwf4) (Or.inl rfl) (Or.inr ⟨le_rfl, le_rfl⟩)
  -- `store (n + 48) order`
  have hs10_n : s10.locals.lookup (ofString "n") = some (.val (.word p1)) := hs10_loc ▸ hs9_n
  have hs10_order : s10.locals.lookup (ofString "order") = some (.val (.word p4)) := hs10_loc ▸ hs9_order
  obtain ⟨hdom_p1_48, hst48_eq⟩ := step_store_word_resumes s10
    (.op .add [.var .local (ofString "n"), .const 48#64]) (.var .local (ofString "order")) _
    (p1 + 48#64) p4
    (by simp [evalHOLExact, evalListHOLExact, hs10_n, valueIsWord, valueWord, wordOpHOL, wordOp])
    (by simp [evalHOLExact, hs10_order]) hres
  rw [hst48_eq] at hres
  set s11 : PanSemStateFiniteExact 64 F := { s10 with memory := updW s10.memory (p1 + 48#64) p4 }
  have hp1_48_nat : (p1 + 48#64).toNat = p1.toNat + 48 :=
    BitVec.toNat_add_of_lt (by change p1.toNat + 48 < 2 ^ 64; omega)
  have hmof_s_s11 : MemOnlyFrame s s11 hf_s := by
    have hmof_s_s10 : MemOnlyFrame s s10 hf_s :=
      MemOnlyFrame.trans hmof_s_s8 hmof_s8_s10
        (Or.inr ⟨le_rfl, le_rfl⟩)
        (Or.inr ⟨by unfold hf_s Wave8Contracts.M12.heapFree; omega,
                 by unfold hf_s Wave8Contracts.M12.heapFree; omega⟩)
    exact MemOnlyFrame.updW_step hmof_s_s10 (p1 + 48#64) p4 hdom_p1_48
      (by rw [hp1_48_nat]; omega)
      ⟨by unfold hf_s Wave8Contracts.M12.heapFree; rw [hp1_48_nat]; omega,
       by unfold hf_s Wave8Contracts.M12.heapFree; rw [hp1_48_nat]; omega⟩
  have hA11 : ArenaReady s11 := ⟨⟨hA10.1.code, hA10.1.memaddrs, hA10.1.shMemaddrs, hA10.1.baseAddr⟩, hA10.2⟩
  -- `return n`
  have hs11_n : s11.locals.lookup (ofString "n") = some (.val (.word p1)) := hs10_n
  have hret11 : evaluateHOLFiniteState s11 (.return (.var .local (ofString "n"))) =
      (some (.returned (.val (.word p1))), emptyLocalsHOLFinite s11) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, hs11_n, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  -- Assemble the full result & post-state of `sourceFnBody Guest.Software.guestFn_htab_copy`:
  set out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_copy)
  have hout_body : evaluateHOLFiniteState s0 bodyRest =
      (some (.returned (.val (.word p1))),
        { (emptyLocalsHOLFinite s11) with
          locals :=
            HolFiniteMapExact.resVarEq
              (HolFiniteMapExact.resVarEq
                (HolFiniteMapExact.resVarEq
                  (HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite s11).locals
                    (ofString "order", s8.locals.lookup (ofString "order")))
                  (ofString "nodes", s5.locals.lookup (ofString "nodes")))
                (ofString "keys", s2.locals.lookup (ofString "keys")))
              (ofString "n", s0.locals.lookup (ofString "n")) }) := by
    dsimp only [bodyRest, extractFn, Guest.Software.guestFn_htab_copy,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
    apply Prod.ext
    · rw [hr_eq1, hseq1_eq, hr_eq2, hseq2_eq, hst32_eq, hr_eq3, hseq3_eq, hst40_eq, hr_eq4, hseq4_eq, hst48_eq, hret11]
    · rw [hp_eq1]; dsimp only
      rw [hseq1_eq, hp_eq2]; dsimp only
      rw [hseq2_eq, hst32_eq, hp_eq3]; dsimp only
      rw [hseq3_eq, hst40_eq, hp_eq4]; dsimp only
      rw [hseq4_eq, hst48_eq, hret11]
  have hout_1 : out.1 = some (.returned (.val (.word p1))) := by
    rw [hdec2_eq]; dsimp only; rw [hout_body]
  have hout_2_core :
      out.2.globals = s11.globals ∧
      out.2.memory = s11.memory ∧
      out.2.code = s11.code ∧
      out.2.memaddrs = s11.memaddrs ∧
      out.2.shMemaddrs = s11.shMemaddrs ∧
      out.2.baseAddr = s11.baseAddr ∧
      out.2.be = s11.be ∧
      out.2.clock = s11.clock := by
    rw [hdec2_eq]; dsimp only; rw [hout_body]; dsimp only [emptyLocalsHOLFinite]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hg_out, hm_out, hc_out, hma_out, hsh_out, hba_out, hbe_out, _⟩ := hout_2_core
  have hs11_globals_eq : s11.globals =
      (((s.globals.update (ofString "heap_ptr", .val (.word p2))).update
        (ofString "heap_ptr", .val (.word p3))).update
        (ofString "heap_ptr", .val (.word p4))).update
        (ofString "heap_ptr", .val (.word q4)) := by
    change s10.globals = _; rw [hs10_glob]
    dsimp only [s9, s8]; change s7.globals.update _ = _
    rw [hs7_glob]; dsimp only [s6, s5]; change (s4.globals.update _).update _ = _
    rw [hs4_glob]; dsimp only [s3]; rw [hs2_glob]; rfl
  have hout_hp : globN out.2 "heap_ptr" = q4.toNat := by
    unfold globN; rw [hg_out, hs11_globals_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hout_sp : globN out.2 "scratch_ptr" = globN s "scratch_ptr" := by
    unfold globN; rw [hg_out, hs11_globals_eq]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
  have hgkept : Wave8Contracts.M12.GlobalsKept ["heap_ptr"] s out.2 := by
    intro k hk
    have hne : ofString "heap_ptr" ≠ k := fun h => hk (by simp [h])
    rw [hg_out, hs11_globals_eq]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have hG_out : GuestInv out.2 := guestInv_congr hc_out hma_out hsh_out hba_out hA11.1
  have hA_out : ArenaReady out.2 := ⟨hG_out, arenaOK_congr hg_out hA11.2⟩
  have hmof_out : MemOnlyFrame s out.2 hf_s :=
    ⟨hc_out.trans hmof_s_s11.code,
     hma_out.trans hmof_s_s11.memaddrs,
     hsh_out.trans hmof_s_s11.shMemaddrs,
     hba_out.trans hmof_s_s11.baseAddr,
     hbe_out.trans hmof_s_s11.be,
     fun a hk hf => (congrFun hm_out a).trans (hmof_s_s11.cell_frame a hk hf),
     fun b hb hni => by unfold memB; rw [hm_out, hbe_out]; exact hmof_s_s11.byte_frame b hb hni,
     fun a hne => hmof_s_s11.dom_writes a (by rwa [← hm_out])⟩
  have hp1_le_q4 : p1.toNat ≤ q4.toNat := by omega
  have hAG : AllocatorGrows s out.2 := ⟨by rw [← hhp1_eq, hout_hp]; exact hp1_le_q4, by rw [hout_sp]⟩
  refine ⟨p1, q4, hout_1, ht_ne0, hhp1_eq, hout_hp.symm, hp1_le_q4, hq4_hi, hA_out, hAG, hgkept, hmof_out, ?_⟩
  -- Now prove the `HtabWF` preservation obligation when `HtabWF s (locN s "t")` and `Allocated s`!
  intro hW halloc
  rw [ht_loc] at hW halloc
  have hhe_264 : heapEnd < 2 ^ 64 := by decide
  have hfp_hdr : (tw.toNat, 88) ∈ htabFootprint s tw.toNat := by simp [htabFootprint]
  have hfp_keys : (hdr s tw.toNat 4, (hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1) ∈ htabFootprint s tw.toNat := by
    simp [htabFootprint]
  have hfp_nodes : (hdr s tw.toNat 5, (hdr s tw.toNat 10 + 1) * 32) ∈ htabFootprint s tw.toNat := by
    simp [htabFootprint]
  have hfp_order : (hdr s tw.toNat 6, (hdr s tw.toNat 10 + 1) * 8) ∈ htabFootprint s tw.toNat := by
    simp [htabFootprint]
  obtain ⟨ht_in, ht_wok⟩ := hW.1 _ hfp_hdr
  obtain ⟨hk_src_in, hk_src_wok⟩ := hW.1 _ hfp_keys
  obtain ⟨hnd_src_in, hnd_src_wok⟩ := hW.1 _ hfp_nodes
  obtain ⟨ho_src_in, ho_src_wok⟩ := hW.1 _ hfp_order
  have hal_hdr : Allocated s (tw.toNat, 88) := halloc _ hfp_hdr
  have hal_keys : Allocated s (hdr s tw.toNat 4, (hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1) := halloc _ hfp_keys
  have hal_nodes : Allocated s (hdr s tw.toNat 5, (hdr s tw.toNat 10 + 1) * 32) := halloc _ hfp_nodes
  have hal_order : Allocated s (hdr s tw.toNat 6, (hdr s tw.toNat 10 + 1) * 8) := halloc _ hfp_order
  have htw_off_eq : ∀ off : Nat, off ≤ 80 →
      tw + BitVec.ofNat 64 off = BitVec.ofNat 64 (tw.toNat + off) := by
    intro off hoff
    apply BitVec.eq_of_toNat_eq
    have hlt1 : tw.toNat + off < 2 ^ 64 := by unfold Inside at ht_in; omega
    have hlt0 : off < 2 ^ 64 := by omega
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt0,
        Nat.mod_eq_of_lt hlt1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt1]
  -- Identify `w_ncap` and `w_stride`:
  have hw_ncap_nat : w_ncap.toNat = hdr s tw.toNat 10 := by
    unfold hdr memW
    have heq := htw_off_eq 80 (by omega)
    change w_ncap.toNat = (match s.memory (BitVec.ofNat 64 (tw.toNat + 80)) with | .word w => w.toNat)
    rw [← heq, hm_t80]
  have hw_stride_nat : w_stride.toNat = hdr s tw.toNat 1 := by
    unfold hdr memW
    have heq := htw_off_eq 8 (by omega)
    change w_stride.toNat = (match s.memory (BitVec.ofNat 64 (tw.toNat + 8)) with | .word w => w.toNat)
    rw [← heq, hm_t8]
  -- Non-wrapping of `(w_ncap + 1) * w_stride`, `(w_ncap + 1) * 32`, `(w_ncap + 1) * 8`:
  have hnc1_lt : hdr s tw.toNat 10 + 1 < 2 ^ 64 := by unfold Inside at hnd_src_in; omega
  have hw_nc1_nat : (w_ncap + 1#64).toNat = hdr s tw.toNat 10 + 1 := by
    rw [BitVec.toNat_add, hw_ncap_nat]; change (hdr s tw.toNat 10 + 1) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt hnc1_lt
  have hst8 : hdr s tw.toNat 1 % 8 = 0 := by have := hW.2.2.2.2.1; omega
  have hw_klen_nat : w_klen_alloc.toNat = (hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1 := by
    change ((w_ncap + 1#64) * w_stride).toNat = _
    rw [BitVec.toNat_mul, hw_nc1_nat, hw_stride_nat]
    exact Nat.mod_eq_of_lt (by unfold Inside at hk_src_in; omega)
  have hw_nlen_nat : w_nlen_alloc.toNat = (hdr s tw.toNat 10 + 1) * 32 := by
    change ((w_ncap + 1#64) * 32#64).toNat = _
    rw [BitVec.toNat_mul, hw_nc1_nat]
    change ((hdr s tw.toNat 10 + 1) * 32) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by unfold Inside at hnd_src_in; omega)
  have hw_olen_nat : w_olen_alloc.toNat = (hdr s tw.toNat 10 + 1) * 8 := by
    change ((w_ncap + 1#64) * 8#64).toNat = _
    rw [BitVec.toNat_mul, hw_nc1_nat]
    change ((hdr s tw.toNat 10 + 1) * 8) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by unfold Inside at hnd_src_in; omega)
  have hp3_eq : p3.toNat = p2.toNat + (hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1 := by
    rw [hq2_eq, hw_klen_nat]
    have hm8 : ((hdr s tw.toNat 10 + 1) * hdr s tw.toNat 1) % 8 = 0 := by rw [Nat.mul_mod, hst8]; simp
    omega
  have hp4_eq : p4.toNat = p3.toNat + (hdr s tw.toNat 10 + 1) * 32 := by
    rw [hq3_eq, hw_nlen_nat]; omega
  have hq4_exact : q4.toNat = p4.toNat + (hdr s tw.toNat 10 + 1) * 8 := by
    rw [hq4_eq, hw_olen_nat]; omega
  -- Identify `src_nodes` and `src_order` from `s6` and `s9` via `MemOnlyFrame s s5 hf_s` and `MemOnlyFrame s s8 hf_s`:
  have hsrc_nodes_nat : src_nodes.toNat = hdr s tw.toNat 5 := by
    have heq40 := htw_off_eq 40 (by omega)
    have hnh40 : ¬ CellHits (tw + 40#64).toNat hf_s := by
      rw [heq40, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold Inside at ht_in; omega)]
      exact not_cellHits_heapFree_of_allocated_word hA.2 hal_hdr (by omega)
    have hm_s5_s : s5.memory (tw + 40#64) = s.memory (tw + 40#64) :=
      hmof_s_s5.mem_eq_of_disj_cell (tw + 40#64) hnh40
    have hm_s6 : s5.memory (tw + 40#64) = .word src_nodes := hm_t40_s6
    rw [hm_s5_s] at hm_s6
    unfold hdr memW
    change src_nodes.toNat = (match s.memory (BitVec.ofNat 64 (tw.toNat + 40)) with | .word w => w.toNat)
    rw [← heq40, hm_s6]
  have hsrc_order_nat : src_order.toNat = hdr s tw.toNat 6 := by
    have heq48 := htw_off_eq 48 (by omega)
    have hnh48 : ¬ CellHits (tw + 48#64).toNat hf_s := by
      rw [heq48, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold Inside at ht_in; omega)]
      exact not_cellHits_heapFree_of_allocated_word hA.2 hal_hdr (by omega)
    have hm_s8_s : s8.memory (tw + 48#64) = s.memory (tw + 48#64) :=
      hmof_s_s8.mem_eq_of_disj_cell (tw + 48#64) hnh48
    have hm_s9 : s8.memory (tw + 48#64) = .word src_order := hm_t48_s9
    rw [hm_s8_s] at hm_s9
    unfold hdr memW
    change src_order.toNat = (match s.memory (BitVec.ofNat 64 (tw.toNat + 48)) with | .word w => w.toNat)
    rw [← heq48, hm_s9]
  -- Header fields of `p1` in `out.2`:
  -- First, for `k ∈ {0, 1, 3, 7, 8, 9, 10}`, cell `p1 + 8*k` in `s2` equals `hdr s tw k`,
  -- and is untouched from `s2` to `s11`!
  have hhdr_kept : ∀ k ∈ ([0, 1, 3, 7, 8, 9, 10] : List Nat),
      hdr out.2 p1.toNat k = hdr s tw.toNat k := by
    intro k hk
    have hk_le : 8 * k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    -- 1) `memW s2 (p1.toNat + 8*k) = memW s (tw.toNat + 8*k)` via `hcp1`:
    have hs2_eq_s : memW s2 (p1.toNat + 8 * k) = memW s (tw.toNat + 8 * k) := by
      apply memW_eq_of_memB_eq s2 s (p1.toNat + 8 * k) (tw.toNat + 8 * k) hmof_s_s2.be
        (by omega) (by have := ht_wok.1; omega)
        (by omega) (by unfold Inside at ht_in; omega)
      intro r hr
      have hd1 : Disj (p1.toNat, (88#64 : BitVec 64).toNat) (tw.toNat, (88#64 : BitVec 64).toNat) :=
        disj_fresh_of_allocated hA.2 hal_hdr ⟨by omega, by change p1.toNat + 88 ≤ heapLimit; omega⟩
      have hsrc_bnd1 : tw.toNat + (88#64 : BitVec 64).toNat ≤ 2 ^ 64 := by
        change tw.toNat + 88 ≤ 2 ^ 64; unfold Inside at ht_in; omega
      have hbyte := hcp1 hd1 hsrc_bnd1 (8 * k + r) (by change 8 * k + r < 88; omega)
      rw [← Nat.add_assoc, ← Nat.add_assoc] at hbyte
      exact hbyte
    -- 2) Cell `a := BitVec.ofNat 64 (p1.toNat + 8*k)` is unchanged from `s2` to `s11`:
    let ak := BitVec.ofNat 64 (p1.toNat + 8 * k)
    have hak_nat : ak.toNat = p1.toNat + 8 * k := by
      change (BitVec.ofNat 64 (p1.toNat + 8 * k)).toNat = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have h4_2 : s4.memory ak = s2.memory ak :=
      hmof_s2_s4.mem_eq_of_disj_cell ak (by rw [hak_nat]; unfold CellHits; omega)
    have h5_4 : s5.memory ak = s4.memory ak := by
      dsimp [s5]; rw [updW, if_neg]
      intro heq; have ht_a := congrArg BitVec.toNat heq
      rw [hak_nat, hp1_32_nat] at ht_a
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have h7_5 : s7.memory ak = s5.memory ak :=
      hmof_s5_s7.mem_eq_of_disj_cell ak (by rw [hak_nat]; unfold CellHits; omega)
    have h8_7 : s8.memory ak = s7.memory ak := by
      dsimp [s8]; rw [updW, if_neg]
      intro heq; have ht_a := congrArg BitVec.toNat heq
      rw [hak_nat, hp1_40_nat] at ht_a
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have h10_8 : s10.memory ak = s8.memory ak :=
      hmof_s8_s10.mem_eq_of_disj_cell ak (by rw [hak_nat]; unfold CellHits; omega)
    have h11_10 : s11.memory ak = s10.memory ak := by
      dsimp [s11]; rw [updW, if_neg]
      intro heq; have ht_a := congrArg BitVec.toNat heq
      rw [hak_nat, hp1_48_nat] at ht_a
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    unfold hdr
    rw [memW_eq_of_mem_eq (p1.toNat + 8 * k)
      ((congrFun hm_out ak).trans (h11_10.trans (h10_8.trans (h8_7.trans (h7_5.trans (h5_4.trans h4_2))))))]
    exact hs2_eq_s
  -- Pointer fields `hdr out.2 p1 4 = p2`, `hdr out.2 p1 5 = p3`, `hdr out.2 p1 6 = p4`:
  have hhdr4 : hdr out.2 p1.toNat 4 = p2.toNat := by
    unfold hdr
    let a32 := BitVec.ofNat 64 (p1.toNat + 32)
    have ha32_eq : a32 = p1 + 32#64 := by
      apply BitVec.eq_of_toNat_eq
      change (BitVec.ofNat 64 (p1.toNat + 32)).toNat = (p1 + 32#64).toNat
      rw [BitVec.toNat_ofNat, hp1_32_nat, Nat.mod_eq_of_lt (by omega)]
    have h7_5 : s7.memory a32 = s5.memory a32 :=
      hmof_s5_s7.mem_eq_of_disj_cell a32 (by rw [ha32_eq, hp1_32_nat]; unfold CellHits; omega)
    have h8_7 : s8.memory a32 = s7.memory a32 := by
      dsimp [s8]; rw [updW, if_neg]
      intro heq; have := congrArg BitVec.toNat heq; rw [ha32_eq, hp1_32_nat, hp1_40_nat] at this; omega
    have h10_8 : s10.memory a32 = s8.memory a32 :=
      hmof_s8_s10.mem_eq_of_disj_cell a32 (by rw [ha32_eq, hp1_32_nat]; unfold CellHits; omega)
    have h11_10 : s11.memory a32 = s10.memory a32 := by
      dsimp [s11]; rw [updW, if_neg]
      intro heq; have := congrArg BitVec.toNat heq; rw [ha32_eq, hp1_32_nat, hp1_48_nat] at this; omega
    change memW out.2 (p1.toNat + 32) = p2.toNat
    rw [memW_eq_of_mem_eq (p1.toNat + 32)
      ((congrFun hm_out a32).trans (h11_10.trans (h10_8.trans (h8_7.trans h7_5))))]
    rw [← hp1_32_nat]; exact memW_updW_self s4 (p1 + 32#64) p2
  have hhdr5 : hdr out.2 p1.toNat 5 = p3.toNat := by
    unfold hdr
    let a40 := BitVec.ofNat 64 (p1.toNat + 40)
    have ha40_eq : a40 = p1 + 40#64 := by
      apply BitVec.eq_of_toNat_eq
      change (BitVec.ofNat 64 (p1.toNat + 40)).toNat = (p1 + 40#64).toNat
      rw [BitVec.toNat_ofNat, hp1_40_nat, Nat.mod_eq_of_lt (by omega)]
    have h10_8 : s10.memory a40 = s8.memory a40 :=
      hmof_s8_s10.mem_eq_of_disj_cell a40 (by rw [ha40_eq, hp1_40_nat]; unfold CellHits; omega)
    have h11_10 : s11.memory a40 = s10.memory a40 := by
      dsimp [s11]; rw [updW, if_neg]
      intro heq; have := congrArg BitVec.toNat heq; rw [ha40_eq, hp1_40_nat, hp1_48_nat] at this; omega
    change memW out.2 (p1.toNat + 40) = p3.toNat
    rw [memW_eq_of_mem_eq (p1.toNat + 40) ((congrFun hm_out a40).trans (h11_10.trans h10_8))]
    rw [← hp1_40_nat]; exact memW_updW_self s7 (p1 + 40#64) p3
  have hhdr6 : hdr out.2 p1.toNat 6 = p4.toNat := by
    unfold hdr
    change memW out.2 (p1.toNat + 48) = p4.toNat
    rw [memW_eq_of_mem_eq (p1.toNat + 48) (congrFun hm_out _), ← hp1_48_nat]
    exact memW_updW_self s10 (p1 + 48#64) p4
  -- `nodeF out.2 p3 idx off = nodeF s (hdr s tw 5) idx off` for `1 ≤ idx ≤ ncap`:
  have hnodeF_eq : ∀ idx, 1 ≤ idx → idx ≤ hdr s tw.toNat 10 → ∀ off ∈ ([0, 8, 16, 24] : List Nat),
      nodeF out.2 p3.toNat idx off = nodeF s (hdr s tw.toNat 5) idx off := by
    intro idx hidx1 hidx2 off hoff
    have hoff_8 : off % 8 = 0 ∧ off + 8 ≤ 32 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl <;> omega
    have hpos_lt : 32 * idx + off + 8 ≤ (hdr s tw.toNat 10 + 1) * 32 := by omega
    unfold nodeF
    -- Show `out.2` has same cell as `s7` at `p3 + 32*idx + off`:
    let an := BitVec.ofNat 64 (p3.toNat + 32 * idx + off)
    have han_nat : an.toNat = p3.toNat + 32 * idx + off := by
      change (BitVec.ofNat 64 (p3.toNat + 32 * idx + off)).toNat = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have h8_7 : s8.memory an = s7.memory an := by
      dsimp [s8]; rw [updW, if_neg]
      intro heq; have := congrArg BitVec.toNat heq; rw [han_nat, hp1_40_nat] at this; omega
    have h10_8 : s10.memory an = s8.memory an :=
      hmof_s8_s10.mem_eq_of_disj_cell an (by rw [han_nat]; unfold CellHits; omega)
    have h11_10 : s11.memory an = s10.memory an := by
      dsimp [s11]; rw [updW, if_neg]
      intro heq; have := congrArg BitVec.toNat heq; rw [han_nat, hp1_48_nat] at this; omega
    rw [memW_eq_of_mem_eq (p3.toNat + 32 * idx + off)
      ((congrFun hm_out an).trans (h11_10.trans (h10_8.trans h8_7)))]
    -- Now compare `memW s7 (p3 + 32*idx + off)` with `memW s (hdr s tw 5 + 32*idx + off)` via `hcp3`:
    have hs7_be : s7.be = s.be := hmof_s5_s7.be.trans hmof_s_s5.be
    apply memW_eq_of_memB_eq s7 s (p3.toNat + 32 * idx + off) (hdr s tw.toNat 5 + 32 * idx + off)
      hs7_be (by omega) (by have := hnd_src_wok.1; omega)
      (by omega) (by unfold Inside at hnd_src_in; omega)
    intro r hr
    have hd3 : Disj (p3.toNat, w_nlen_alloc.toNat) (src_nodes.toNat, w_nlen_alloc.toNat) := by
      rw [hw_nlen_nat, hsrc_nodes_nat]
      exact disj_fresh_of_allocated hA.2 hal_nodes ⟨by omega, by omega⟩
    have hsb3 : src_nodes.toNat + w_nlen_alloc.toNat ≤ 2 ^ 64 := by
      rw [hsrc_nodes_nat, hw_nlen_nat]; unfold Inside at hnd_src_in; omega
    have hbyte := hcp3 hd3 hsb3 (32 * idx + off + r) (by rw [hw_nlen_nat]; omega)
    have hs6_s_byte : memB s6 (src_nodes.toNat + (32 * idx + off + r)) =
        memB s (src_nodes.toNat + (32 * idx + off + r)) := by
      change memB s5 _ = memB s _
      apply hmof_s_s5.byte_frame _ (by omega)
      intro hin
      have hdisj_hf := disj_fresh_of_allocated hA.2 hal_nodes
        (dst := hf_s) ⟨by unfold hf_s Wave8Contracts.M12.heapFree; omega,
                       by unfold hf_s Wave8Contracts.M12.heapFree; omega⟩
      unfold InIvl at hin
      rw [hsrc_nodes_nat] at hin
      rcases hdisj_hf with h0 | h0 | h | h <;> omega
    rw [hs6_s_byte, hsrc_nodes_nat] at hbyte
    have ha1 : p3.toNat + 32 * idx + off + r = p3.toNat + (32 * idx + off + r) := by omega
    have ha2 : hdr s tw.toNat 5 + 32 * idx + off + r = hdr s tw.toNat 5 + (32 * idx + off + r) := by omega
    rw [ha1, ha2]; exact hbyte
  -- `memW out.2 (p4 + 8*idx) = memW s (hdr s tw 6 + 8*idx)` for `idx < hdr s tw 3`:
  have hord_eq : ∀ idx, idx < hdr s tw.toNat 3 →
      memW out.2 (p4.toNat + 8 * idx) = memW s (hdr s tw.toNat 6 + 8 * idx) := by
    intro idx hidx
    have hcnt_le := Wave8Contracts.M12.htabCount_le_ncap hW
    have hpos_lt : 8 * idx + 8 ≤ (hdr s tw.toNat 10 + 1) * 8 := by omega
    let ao := BitVec.ofNat 64 (p4.toNat + 8 * idx)
    have hao_nat : ao.toNat = p4.toNat + 8 * idx := by
      change (BitVec.ofNat 64 (p4.toNat + 8 * idx)).toNat = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have h11_10 : s11.memory ao = s10.memory ao := by
      dsimp [s11]; rw [updW, if_neg]
      intro heq; have := congrArg BitVec.toNat heq; rw [hao_nat, hp1_48_nat] at this; omega
    rw [memW_eq_of_mem_eq (p4.toNat + 8 * idx) ((congrFun hm_out ao).trans h11_10)]
    have hs10_be : s10.be = s.be := hmof_s8_s10.be.trans hmof_s_s8.be
    apply memW_eq_of_memB_eq s10 s (p4.toNat + 8 * idx) (hdr s tw.toNat 6 + 8 * idx)
      hs10_be (by omega) (by have := ho_src_wok.1; omega)
      (by omega) (by unfold Inside at ho_src_in; omega)
    intro r hr
    have hd4 : Disj (p4.toNat, w_olen_alloc.toNat) (src_order.toNat, w_olen_alloc.toNat) := by
      rw [hw_olen_nat, hsrc_order_nat]
      exact disj_fresh_of_allocated hA.2 hal_order ⟨by omega, by omega⟩
    have hsb4 : src_order.toNat + w_olen_alloc.toNat ≤ 2 ^ 64 := by
      rw [hsrc_order_nat, hw_olen_nat]; unfold Inside at ho_src_in; omega
    have hbyte := hcp4 hd4 hsb4 (8 * idx + r) (by rw [hw_olen_nat]; omega)
    have hs9_s_byte : memB s9 (src_order.toNat + (8 * idx + r)) =
        memB s (src_order.toNat + (8 * idx + r)) := by
      change memB s8 _ = memB s _
      apply hmof_s_s8.byte_frame _ (by omega)
      intro hin
      have hdisj_hf := disj_fresh_of_allocated hA.2 hal_order
        (dst := hf_s) ⟨by unfold hf_s Wave8Contracts.M12.heapFree; omega,
                       by unfold hf_s Wave8Contracts.M12.heapFree; omega⟩
      unfold InIvl at hin
      rw [hsrc_order_nat] at hin
      rcases hdisj_hf with h0 | h0 | h | h <;> omega
    rw [hs9_s_byte, hsrc_order_nat] at hbyte
    have ha1 : p4.toNat + 8 * idx + r = p4.toNat + (8 * idx + r) := by omega
    have ha2 : hdr s tw.toNat 6 + 8 * idx + r = hdr s tw.toNat 6 + (8 * idx + r) := by omega
    rw [ha1, ha2]; exact hbyte
  have hWF_out : HtabWF out.2 p1.toNat :=
    htabWF_of_copied hW hG_out
      (hhdr_kept 0 (by simp)) (hhdr_kept 1 (by simp)) (hhdr_kept 3 (by simp))
      hhdr4 hhdr5 hhdr6
      (hhdr_kept 7 (by simp)) (hhdr_kept 8 (by simp)) (hhdr_kept 9 (by simp)) (hhdr_kept 10 (by simp))
      hp1_al hq1_al hq2_al hq3_al
      ⟨hp1_sb, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      hnodeF_eq hord_eq
  refine ⟨hWF_out, by rw [ht_loc]; exact hhdr_kept 3 (by simp), ?_⟩
  intro ivl hivl
  unfold htabFootprint at hivl
  rw [hhdr4, hhdr5, hhdr6, hhdr_kept 1 (by simp), hhdr_kept 10 (by simp)] at hivl
  rw [← hhp1_eq, hout_hp]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hivl
  rcases hivl with rfl | rfl | rfl | rfl
  · exact ⟨le_rfl, by omega⟩
  · exact ⟨by omega, by omega⟩
  · exact ⟨by omega, by omega⟩
  · exact ⟨by omega, by omega⟩

/-! ## 5. Exported contracts `rt_htab_copy_impl` and `wk_htab_copy_impl` -/

theorem rt_htab_copy_impl :
    Wave8Contracts.M26.Returns ArenaReady (fun s post n => locN s "t" ≠ 0 ∧
      (HtabWF s (locN s "t") → (∀ i ∈ htabFootprint s (locN s "t"), Allocated s i) →
        HtabWF post n ∧ hdr post n 3 = hdr s (locN s "t") 3 ∧
        ∀ i ∈ htabFootprint post n, Inside i (globN s "heap_ptr") (globN post "heap_ptr")))
    (ofString "htab_copy") := by
  refine ⟨_, _, _, lookup_htab_copy_r13, ?_⟩
  intro F s hcode hAR ⟨vals, hl⟩ _ v hret
  obtain ⟨tw, _, ht⟩ := lookupCode_one_word lookup_htab_copy_r13 hl
  obtain ⟨p1, _, hrv, ht_ne0, _, _, _, _, hA_post, hAG, _, _, hWF_imp⟩ :=
    htab_copy_resumes_props s tw hcode hAR ht (Or.inl ⟨v, hret⟩)
  rw [hrv] at hret
  injection hret with h1; injection h1 with h2; subst h2
  exact ⟨p1, rfl, hA_post, hAG, ht_ne0, hWF_imp⟩

theorem wk_htab_copy_impl :
    Wave8Contracts.M12.WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (Wave8Contracts.M12.RetAvoidsIf (fun s => HtabWF s (locN s "t") ∧
        ∀ i ∈ htabFootprint s (locN s "t"), Allocated s i)
      (fun _ post w => htabFootprint post w)) (ofString "htab_copy") := by
  refine ⟨_, _, _, lookup_htab_copy_r13, ?_⟩
  intro F s hcode hW ⟨vals, hl⟩ _ hres
  obtain ⟨tw, _, ht⟩ := lookupCode_one_word lookup_htab_copy_r13 hl
  obtain ⟨p1, _, hrv, _, _, _, _, _, hA_post, hAG, hgkept, hmof, hWF_imp⟩ :=
    htab_copy_resumes_props s tw hcode hW.1 ht hres
  set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_copy)).2
  have heff : WorldFrameEff s post ([] ++ ([] : List Ivl)) ["heap_ptr"] := by
    refine ⟨hA_post, hAG.1, hAG.2, hgkept, hmof.be, ?_, ?_, ?_⟩
    · intro a hna
      by_contra hne
      exact hna (hmof.dom_writes a hne)
    · intro a _ hnhf
      exact hmof.mem_eq_of_disj_cell a hnhf
    · intro b hb _ hnhf
      exact hmof.byte_frame b hb hnhf
  refine heff.to_worldStep (extra := fun _ => []) hW
    (fun g hg => Or.inl (by simpa using hg))
    (fun _ h => by simp at h)
    (fun S Nd hWT _ _ hno_new ⟨hW_t, halloc_t⟩ v hv => ?_)
  rw [hrv] at hv
  injection hv with hv'; injection hv' with hv''; subst hv''
  obtain ⟨_, _, hfp_in⟩ := hWF_imp hW_t halloc_t
  refine ⟨p1, rfl, ?_⟩
  intro blk hblk o ho
  exact disj_fresh_heap_of_worldOwned hW.1 hA_post hWT
    (fun x hx => by rcases hno_new x hx with rfl | h; exact Or.inl rfl; exact Or.inr (Or.inl h))
    hno_new (hfp_in blk hblk) blk (List.mem_singleton.2 rfl) o ho

end InitECandidate.Solver.Wave8GuestInv.R13Shards
