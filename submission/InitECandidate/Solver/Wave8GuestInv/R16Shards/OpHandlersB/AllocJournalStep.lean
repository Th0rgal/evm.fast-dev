import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M23.EvmLemmas
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmHtabStep

/-! # Heap-allocation and journal-push `EvmInvAt` preservation lemmas -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8Contracts.M23

private theorem mem_eq_of_byte_eq {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hbe : post.be = s.be)
    {a : BitVec 64} (ha_dom : ordinaryDomain a)
    (hb : ∀ k : Nat, k < 8 → memB post (a.toNat + k) = memB s (a.toNat + k)) :
    post.memory a = s.memory a := by
  have hdom' := (ordinaryDomain_iff a).mp ha_dom
  have ha_ord : a.toNat % 8 = 0 ∧ sourceBase ≤ a.toNat ∧ a.toNat < heapEnd := by
    rw [R11Shards.sourceBase_val, R11Shards.heapEnd_val]; omega
  have hhe_lt : heapEnd ≤ 2 ^ 64 := by rw [R11Shards.heapEnd_val]; decide
  have hhe_8 : heapEnd % 8 = 0 := by decide
  have ha_hi : a.toNat + 8 ≤ 2 ^ 64 := by omega
  rcases hp_m : post.memory a with ⟨wp⟩
  rcases hs_m : s.memory a with ⟨ws⟩
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hbyte_val : ∀ k : Nat, k < 8 →
      (panGetByteHOL (BitVec.ofNat 64 (a.toNat + k)) wp s.be).toNat =
      (panGetByteHOL (BitVec.ofNat 64 (a.toNat + k)) ws s.be).toNat := by
    intro k hk
    have hal_eq : panByteAlignHOL (BitVec.ofNat 64 (a.toNat + k)) = a := by
      apply BitVec.eq_of_toNat_eq
      rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hbk := hb k hk
    unfold memB at hbk
    rw [hal_eq, hp_m, hs_m, hbe] at hbk
    exact hbk
  have hshift : ∀ (w : BitVec 64) (idx : Nat), idx < 8 →
      w.toNat / 256 ^ idx % 256 =
      (panGetByteHOL (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))) w s.be).toNat := by
    intro w idx hidx
    unfold panGetByteHOL
    change w.toNat / 256 ^ idx % 256 =
      (UInt8.ofNat (w.toNat / 256 ^
        (if s.be then 8 - 1 - (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8
          else (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8) % 256)).toNat
    have hexp :
        (if s.be then 8 - 1 - (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8
          else (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8) = idx := by
      have hmod_lt : (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat =
          a.toNat + (if s.be then 7 - idx else idx) :=
        Nat.mod_eq_of_lt (by cases s.be <;> simp <;> omega)
      rw [hmod_lt]
      cases s.be <;> simp <;> omega
    rw [hexp, UInt8.toNat_ofNat']
    have h256 : (2 ^ 8 : Nat) = 256 := by decide
    rw [h256, Nat.mod_mod]
  have hpow_eq : ∀ idx : Nat, idx < 8 → wp.toNat / 256 ^ idx % 256 = ws.toNat / 256 ^ idx % 256 := by
    intro idx hidx
    rw [hshift wp idx hidx, hshift ws idx hidx]
    exact hbyte_val (if s.be then 7 - idx else idx) (by cases s.be <;> simp <;> omega)
  have hdecomp : ∀ n : Nat, n < 2 ^ 64 →
      n = (n / 256 ^ 0 % 256) +
          (n / 256 ^ 1 % 256) * 256 ^ 1 +
          (n / 256 ^ 2 % 256) * 256 ^ 2 +
          (n / 256 ^ 3 % 256) * 256 ^ 3 +
          (n / 256 ^ 4 % 256) * 256 ^ 4 +
          (n / 256 ^ 5 % 256) * 256 ^ 5 +
          (n / 256 ^ 6 % 256) * 256 ^ 6 +
          (n / 256 ^ 7 % 256) * 256 ^ 7 := by
    intro n hn; omega
  rw [hdecomp wp.toNat wp.isLt, hdecomp ws.toNat ws.isLt]
  rw [hpow_eq 0 (by omega), hpow_eq 1 (by omega), hpow_eq 2 (by omega), hpow_eq 3 (by omega),
      hpow_eq 4 (by omega), hpow_eq 5 (by omega), hpow_eq 6 (by omega), hpow_eq 7 (by omega)]

private theorem memW_eq_of_outside_range {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {lo hi : Nat}
    (hma_s : s.memaddrs = ordinaryDomain)
    (hbe : post.be = s.be)
    (hout_dom : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 → ¬ (lo ≤ b ∧ b < hi) → memB post b = memB s b)
    {base sz k : Nat}
    (hbnd : base + sz ≤ 2 ^ 64) (_hb8 : base % 8 = 0) (_hk8 : k % 8 = 0)
    (hk : k + 8 ≤ sz)
    (hdj : sz = 0 ∨ hi ≤ base ∨ base + sz ≤ lo) :
    memW post (base + k) = memW s (base + k) := by
  have ha : base + k < 2 ^ 64 := by omega
  have hbit : (BitVec.ofNat 64 (base + k)).toNat = base + k := Nat.mod_eq_of_lt ha
  unfold memW
  by_cases hdom : ordinaryDomain (BitVec.ofNat 64 (base + k))
  · rw [mem_eq_of_byte_eq hbe hdom]
    intro idx hidx
    rw [hbit]
    apply hbyte (base + k + idx) (by omega)
    intro ⟨h1, h2⟩
    rcases hdj with h0 | h | h <;> omega
  · rw [hout_dom _ (by rwa [hma_s])]

private theorem frameObject_disj_fresh_heap {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat} {ec o : Ivl} {hp_post : Nat}
    (hA : ArenaOK s) (hhp_lim : hp_post ≤ heapLimit)
    (hFW : FrameWF s S ec) (ho : o ∈ frameObjects s ec) :
    o.2 = 0 ∨ hp_post ≤ o.1 ∨ o.1 + o.2 ≤ globN s "heap_ptr" := by
  have hhl_ss : heapLimit ≤ scratchStart := by
    rw [R11Shards.heapLimit_val, R11Shards.scratchStart_val]
  have hfm_ge : scratchStart ≤ globN s "frame_mem_ptr" := hA.2.2.1
  have hsp_ge : scratchStart ≤ globN s "scratch_ptr" := le_trans hfm_ge hA.2.2.2.1
  obtain ⟨hscr, hmem_in, _, _, _, _, _, _, _, _, _, _, hlogs_in, _, hret_in, hll_ok, _⟩ := hFW
  unfold frameObjects at ho
  rcases List.mem_append.1 ho with ho7 | holog
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
    rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h := (hscr (ec.1, 280) (by simp)).1.1
      dsimp only at h ⊢; exact Or.inr (Or.inl (by omega))
    · have h := (hscr (ec.2, 104) (by simp)).1.1
      dsimp only at h ⊢; exact Or.inr (Or.inl (by omega))
    · have h := (hscr (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)) (by simp)).1.1
      dsimp only at h ⊢; exact Or.inr (Or.inl (by omega))
    · have h := hmem_in.1
      dsimp only at h ⊢; exact Or.inr (Or.inl (by omega))
    · have h := (hscr (memW s (ec.1 + 88), 24) (by simp)).1.1
      dsimp only at h ⊢; exact Or.inr (Or.inl (by omega))
    · rcases hlogs_in with h | h
      · exact Or.inr (Or.inr h.2)
      · exact Or.inr (Or.inl (by have := h.1; omega))
    · rcases hret_in with ⟨hz, _⟩ | ⟨h, _⟩
      · unfold frameRet; exact Or.inl (by simp [hz])
      · exact Or.inr (Or.inr h.2)
  · unfold frameLogObjects at holog
    dsimp only at holog
    obtain ⟨idx, hidx_mem, ho_own⟩ := List.mem_flatMap.1 holog
    rw [List.mem_range] at hidx_mem
    rcases hll_ok with hz | ⟨_, _, _, _, hent⟩
    · exfalso
      have hlo := (hscr (memW s (ec.1 + 88), 24) (by simp)).1.1
      dsimp only at hlo
      have hss : 0 < scratchStart := by rw [R11Shards.scratchStart_val]; decide
      omega
    · have hle := (hent idx hidx_mem).2
      have ho_rec : o ∈ logRecordIvls s (memW s (memW s (memW s (ec.1 + 88)) + 8 * idx)) :=
        (List.mem_filter.1 ho_own).1
      simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at ho_rec
      rcases ho_rec with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr hle.2.1.2)
      · exact Or.inr (Or.inr hle.2.2.2.2.1.2)
      · exact Or.inr (Or.inr hle.2.2.2.2.2.1.2)
      · exact Or.inr (Or.inr hle.2.2.2.2.2.2.2)

/-- Any step that bumps `heap_ptr`, keeps all non-`heap_ptr` globals unchanged, and writes only inside
`[globN s "heap_ptr", globN post "heap_ptr")` preserves `EvmInvAt`, `evmChain`, and `evmR`. -/
theorem evmInvAt_of_fresh_heap_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hAs : ArenaReady s) (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hAp : ArenaReady post) (hbe : post.be = s.be)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hg_kept : GlobalsKept ["heap_ptr"] s post)
    (hout_dom : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b) :
    InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt post S ∧
    evmChain post = evmChain s ∧
    evmR post = evmR s := by
  obtain ⟨hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInv
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT
  have hWT : WorldTypedWith s S Nd_at := ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
  have hdom_eq : post.memaddrs = s.memaddrs := hAp.1.memaddrs.trans hAs.1.memaddrs.symm
  have hglob_nonHeap : ∀ nm : String, ofString nm ≠ ofString "heap_ptr" → globN post nm = globN s nm := by
    intro nm hne
    exact (globN_eq_of_lookup_eq (hg_kept (ofString nm) (by simp [hne]))).symm
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by
    rw [hglob_nonHeap "scratch_ptr" (by decide)]
  have hcg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := by
    intro g hg
    have hne : ofString g ≠ ofString "heap_ptr" := by revert g hg; decide
    exact hglob_nonHeap g hne
  have hcell : SameTypedCells s post S Nd_at := by
    have hwti_disj : ∀ i ∈ worldTypedIvls s S Nd_at,
        i.2 = 0 ∨ globN post "heap_ptr" ≤ i.1 ∨ i.1 + i.2 ≤ globN s "heap_ptr" := by
      intro i hi
      rcases worldTypedIvls_allocated hWT hi with h0 | hal
      · exact Or.inl h0
      · rcases hal with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact Or.inr (Or.inr h2)
        · have hp_lim := hAp.2.2.1
          have hs_fr := hAs.2.2.2.1
          have hs_gap := hAs.2.2.2.2.1
          rw [R11Shards.heapLimit_val] at hp_lim
          rw [R11Shards.scratchStart_val] at hs_fr
          exact Or.inr (Or.inl (by omega))
    refine ⟨hbe, hdom_eq, hAs.1.memaddrs, ?_, ?_, ?_⟩
    · intro a hna
      apply hout_dom a
      rwa [hAs.1.memaddrs]
    · intro a ha ha8 ⟨i, hi, ha1, ha2⟩
      by_cases hdom : ordinaryDomain (BitVec.ofNat 64 a)
      · have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
        apply mem_eq_of_byte_eq hbe hdom
        intro k hk
        rw [hbit]
        apply hbyte (a + k) (by omega)
        intro ⟨hb1, hb2⟩
        rcases hwti_disj i hi with h0 | h | h <;> omega
      · apply hout_dom _ (by rwa [hAs.1.memaddrs])
    · intro b hb ⟨i, hi, hb1, hb2⟩
      apply hbyte b hb
      intro ⟨h1, h2⟩
      rcases hwti_disj i hi with h0 | h | h <;> omega
  have hfeq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [blockOutObjects_eq hAs.2 hWT.2.2.1 hcell (hglob_nonHeap "bo" (by decide)),
        balObjects_eq hAs.2 hWT.1 hWT.2.2.1 hcell (hglob_nonHeap "bal_accounts" (by decide)),
        hglob_nonHeap "journal" (by decide),
        hglob_nonHeap "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" := by revert gn hgn; decide
    rw [hglob_nonHeap gn.1 hne]
  have hFT_post := fixedTyped_of_eq hAp hWT.2.2.1 hhp hsc hfeq
  obtain ⟨hWT_post, _⟩ := worldTypedWith_congr_w1 hAs hAp hhp hsc hcg hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd_at, hWT_post.2.2.2⟩
  have hdj_fo : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec,
      o.2 = 0 ∨ globN post "heap_ptr" ≤ o.1 ∨ o.1 + o.2 ≤ globN s "heap_ptr" :=
    fun ec hec o ho => frameObject_disj_fresh_heap hAs.2 hAp.2.2.1 (hFW_all ec hec) ho
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨hb1, hb2, hb88, _⟩ := frameWF_bounds hAs.2 hFW
    have he1_8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    have he2_8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have he88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    refine ⟨fun k hk hk8 => memW_eq_of_outside_range hAs.1.memaddrs hbe hout_dom hbyte hb1 he1_8 hk8 hk
              (hdj_fo ec hec (ec.1, 280) (by simp [frameObjects])),
            fun k hk hk8 => memW_eq_of_outside_range hAs.1.memaddrs hbe hout_dom hbyte hb2 he2_8 hk8 hk
              (hdj_fo ec hec (ec.2, 104) (by simp [frameObjects])),
            fun k hk hk8 => memW_eq_of_outside_range hAs.1.memaddrs hbe hout_dom hbyte hb88 he88_8 hk8 hk
              (hdj_fo ec hec (memW s (ec.1 + 88), 24) (by simp [frameObjects]))⟩
  have hchain_aux : ∀ (fuel e c : Nat),
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel; induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      obtain ⟨_, hc_eq, _⟩ := hrec_eq (e, c) hec
      have hc16 := hc_eq 16 (by omega) (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega) (by omega)
      have hc8 := hc_eq 8 (by omega) (by omega)
      simp only [evmChainFrom, hc16, hc0, hc8]
      split
      · rfl
      · rename_i hne16
        rw [ih]; intro ec' hec'; exact hsub ec' (by simp [evmChainFrom, hne16, hec'])
  have hchain_eq : evmChain post = evmChain s := by
    unfold evmChain
    rw [hglob_nonHeap "ev" (by decide), hglob_nonHeap "cur_cont" (by decide)]
    exact hchain_aux _ _ _ (fun _ h => h)
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega)]
  have hlogs_congr : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := frameWF_bounds hAs.2 hFW
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    have hl0 : memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) := by
      simpa using h88_eq 0 (by omega) (by omega)
    have hl8 : memW post (memW s (ec.1 + 88) + 8) = memW s (memW s (ec.1 + 88) + 8) :=
      h88_eq 8 (by omega) (by omega)
    have hl16 : memW post (memW s (ec.1 + 88) + 16) = memW s (memW s (ec.1 + 88) + 16) :=
      h88_eq 16 (by omega) (by omega)
    have harr_eq : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
        memW post (memW s (memW s (ec.1 + 88)) + 8 * i) = memW s (memW s (memW s (ec.1 + 88)) + 8 * i) := by
      intro i hi
      have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
      have hlen_le : memW s (memW s (ec.1 + 88) + 8) ≤ memW s (memW s (ec.1 + 88) + 16) :=
        hFW.2.2.2.2.2.2.2.2.2.2.2.1
      have hfl_b : (frameLogs s ec).1 + (frameLogs s ec).2 ≤ 2 ^ 64 := by
        rcases hfob _ hfl_in with h0 | hb
        · unfold frameLogs at h0; dsimp only at h0; omega
        · exact hb
      have hfl_8 : (memW s (memW s (ec.1 + 88))) % 8 = 0 := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      exact memW_eq_of_outside_range hAs.1.memaddrs hbe hout_dom hbyte hfl_b hfl_8 (by omega)
        (by unfold frameLogs; dsimp only; omega) (hdj_fo ec hec _ hfl_in)
    have hlr_eq : ∀ i (hi : i < memW s (memW s (ec.1 + 88) + 8)) off, off + 8 ≤ 40 → off % 8 = 0 →
        memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) =
          memW s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) := by
      intro i hi off hoff hoff8
      have hlr_in : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameObjects s ec := by
        unfold frameObjects; apply List.mem_append_right
        unfold frameLogObjects; dsimp only
        exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
          by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
      have hlr_b : memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + 40 ≤ 2 ^ 64 := by
        rcases hfob _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_8 : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) % 8 = 0 := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · have he88_in := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1.1
          have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
          rw [R11Shards.scratchStart_val] at h1; dsimp only at he88_in; omega
        · exact (hent i hi).2.1.1
      exact memW_eq_of_outside_range hAs.1.memaddrs hbe hout_dom hbyte hlr_b hlr_8 hoff8 hoff
        (hdj_fo ec hec _ hlr_in)
    refine ⟨?_, ?_⟩
    · unfold frameLogObjects; dsimp only
      rw [he_eq 88 (by omega) (by omega), hl8]
      apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi
      rw [hl0, harr_eq i hi]
      have r0 := hlr_eq i hi 0 (by omega) (by omega)
      have r8 := hlr_eq i hi 8 (by omega) (by omega)
      have r16 := hlr_eq i hi 16 (by omega) (by omega)
      have r24 := hlr_eq i hi 24 (by omega) (by omega)
      have r32 := hlr_eq i hi 32 (by omega) (by omega)
      simp only [Nat.add_zero] at r0
      unfold logOwnedIvls logRecordIvls
      rw [r0, r8, r16, r24, r32, hglob_nonHeap "vm_system_address" (by decide)]
    · rw [he_eq 88 (by omega) (by omega)]
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
      · exact Or.inl hz
      · right
        refine ⟨(wordsOK_congr_dom hdom_eq).2 hw_l, allocated_mono hhp hsc hal_l,
          by rw [hl8]; exact hlt28, by rw [hl8, hl16]; exact hle_cap, fun i hi => ?_⟩
        rw [hl8] at hi; rw [hl0]
        obtain ⟨hwa, hle⟩ := hent i hi
        refine ⟨(wordAt_congr_dom hdom_eq).2 hwa, ?_⟩
        rw [harr_eq i hi]
        have r0 := hlr_eq i hi 0 (by omega) (by omega)
        have r8 := hlr_eq i hi 8 (by omega) (by omega)
        have r16 := hlr_eq i hi 16 (by omega) (by omega)
        have r24 := hlr_eq i hi 24 (by omega) (by omega)
        have r32 := hlr_eq i hi 32 (by omega) (by omega)
        simp only [Nat.add_zero] at r0
        unfold LogEntryOK at hle ⊢
        rw [r0, r8, r16, r24, r32]
        exact ⟨(wordsOK_congr_dom hdom_eq).2 hle.1,
          ⟨hle.2.1.1, le_trans hle.2.1.2 hhp⟩,
          hle.2.2.1, hle.2.2.2.1,
          ⟨hle.2.2.2.2.1.1, le_trans hle.2.2.2.2.1.2 hhp⟩,
          ⟨hle.2.2.2.2.2.1.1, le_trans hle.2.2.2.2.2.1.2 hhp⟩,
          ⟨hle.2.2.2.2.2.2.1, le_trans hle.2.2.2.2.2.2.2 hhp⟩⟩
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 24 (by omega) (by omega), he_eq 40 (by omega) (by omega),
        he_eq 88 (by omega) (by omega),
        hframeLogs_eq ec hec, hframeRet_eq ec hec, (hlogs_congr ec hec).1]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 88 (by omega) (by omega)]
  have hmap_fo_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots; apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega) (by omega), he_eq 168 (by omega) (by omega),
        he_eq 176 (by omega) (by omega)]
  have hfp_eq_all : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  have hR_eq : evmR post = evmR s :=
    evmR_eq_of_chain_and_words hchain_eq (fun ec hec =>
      ⟨(hrec_eq ec hec).1 64 (by omega) (by omega),
       (hrec_eq ec hec).1 192 (by omega) (by omega)⟩)
  refine ⟨⟨hW_post, ?_⟩, hchain_eq, hR_eq⟩
  dsimp only; rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    have hec_mem := List.mem_of_mem_getLast? hec
    exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2.1 16 (by omega) (by omega)]; exact hk0⟩
  · intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
    have hlo_ok := (hlogs_congr ec hec).2
    have hmsg_ok : MsgOwned post S (memW post (ec.1 + 112)) := by
      rw [he_eq 112 (by omega) (by omega)]
      obtain ⟨hal_m, hw_m, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := c17
      obtain ⟨hTr_int, hsub_int⟩ := R11Shards.triesTypedWith_inter hTr_at hTr_m
      set Ndi := Nd_at.filter (fun n => decide (n ∈ Nd_m))
      have hcell_i : SameTypedCells s post S Ndi := by
        have hwti_sub : ∀ i ∈ worldTypedIvls s S Ndi, i ∈ worldTypedIvls s S Nd_at := by
          intro i hi; unfold worldTypedIvls at hi ⊢
          rcases List.mem_append.1 hi with hpre | hne
          · exact List.mem_append_left _ hpre
          · apply List.mem_append_right; unfold nodeExtents at hne ⊢
            obtain ⟨n, hn, hnx⟩ := List.mem_flatMap.1 hne
            exact List.mem_flatMap.2 ⟨n, (List.mem_filter.1 hn).1, hnx⟩
        refine ⟨hcell.1, hcell.2.1, hcell.2.2.1, hcell.2.2.2.1,
          fun a ha ha8 ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.1 a ha ha8 ⟨i, hwti_sub i hi, h1, h2⟩,
          fun b hb ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.2 b hb ⟨i, hwti_sub i hi, h1, h2⟩⟩
      obtain ⟨hWT_i_post, _⟩ := worldTypedWith_congr_w1 hAs hAp hhp hsc hcg hcell_i
        ⟨hWT.1, hWT.2.1, hWT.2.2.1, hTr_int⟩
        ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
      refine ⟨allocated_mono hhp hsc hal_m, (wordsOK_congr_dom hdom_eq).2 hw_m,
        fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact hdt t ht i hi,
        by rw [hfeq]; exact hdf,
        by rw [hchain_eq]; intro ec' hec' o ho; rw [hframeObjects_eq ec' hec'] at ho; exact hdfo ec' hec' o ho,
        Ndi, hWT_i_post.2.2.2, fun o ho j hj => ?_⟩
      rw [nodeExtents_eq hTr_int.1 hcell_i] at hj
      exact hdj_m o ho j (hsub_int j hj).2
    unfold FrameWF; dsimp only
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 88 (by omega) (by omega), he_eq 24 (by omega) (by omega),
        he_eq 40 (by omega) (by omega), he_eq 16 (by omega) (by omega),
        he_eq 32 (by omega) (by omega), he_eq 136 (by omega) (by omega),
        he_eq 168 (by omega) (by omega), he_eq 176 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
        hframeLogs_eq ec hec,
        he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega),
        hframeRet_eq ec hec,
        hglob_nonHeap "scratch_ptr" (by decide),
        hglob_nonHeap "frame_mem_ptr" (by decide),
        hglob_nonHeap "evm_empty" (by decide)]
    rw [he_eq 88 (by omega) (by omega)] at hlo_ok
    refine ⟨fun i hi => ⟨(c1 i hi).1, (wordsOK_congr_dom hdom_eq).2 (c1 i hi).2⟩,
      c2, (wordsOK_congr_dom hdom_eq).2 c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
      ?_, (wordsOK_congr_dom hdom_eq).2 c14, ?_, hlo_ok, hmsg_ok⟩
    · rcases c13 with hl | hr
      · exact Or.inl ⟨hl.1, le_trans hl.2 hhp⟩
      · exact Or.inr hr
    · rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨⟨hin.1, le_trans hin.2 hhp⟩, (wordsOK_congr_dom hdom_eq).2 hw⟩
  · intro ec hec
    have hec_mem := List.mem_of_mem_tail hec
    unfold FrameRoom
    rw [(hrec_eq ec hec_mem).1 16 (by omega) (by omega),
        (hrec_eq ec hec_mem).1 232 (by omega) (by omega)]
    exact hFR_all ec hec
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
    rw [(hrec_eq _ hi0).2.1 80 (by omega) (by omega),
        (hrec_eq _ hi0).2.1 72 (by omega) (by omega),
        (hrec_eq _ hi1).1 40 (by omega) (by omega)]
    exact hRW i hi
  · rw [hmap_fo_eq]; exact hFO_pw
  · intro ec hec o ho
    rw [hframeObjects_eq ec hec] at ho; rw [hfeq]
    exact ⟨fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact (hFO_disj ec hec o ho).1 t ht i hi,
      (hFO_disj ec hec o ho).2⟩
  · rw [hmap_fo_eq]
    refine ⟨Nd_at, hWT_post.2.2.2, fun o ho j hj => ?_⟩
    rw [nodeExtents_eq hTr_at.1 hcell] at hj
    exact hAT_at o ho j hj
  · have hworldRefs_eq : worldTableRefs post S = worldTableRefs s S := by
      unfold worldTableRefs recordSlots
      rw [hglob_nonHeap "ws" (by decide), hglob_nonHeap "bs" (by decide), hglob_nonHeap "ts" (by decide),
          show globalTableRoots.map (globN post) = globalTableRoots.map (globN s) by
            simp only [globalTableRoots, List.map,
              hglob_nonHeap "bal_accounts" (by decide),
              hglob_nonHeap "bal_idx_accts" (by decide),
              hglob_nonHeap "bal_idx_stor" (by decide)],
          balRecords_eq hWT.1 hcell (hglob_nonHeap "bal_accounts" (by decide)),
          hglob_nonHeap "journal_n" (by decide), hglob_nonHeap "journal" (by decide)]
      have hws_sl : (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW post (globN s "ws" + k)) =
          (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW s (globN s "ws" + k)) := by
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 40) (by decide) hnz
          (by simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> omega)
      have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
          (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz
          (by simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
          (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz
          (by simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      have hnest_bs : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
          (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
        by_cases hnz : globN s "bs" = 0
        · simp [hnz]
        · rw [memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz (by omega)]
          by_cases hmS : memW s (globN s "bs" + 32) ∈ S
          · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
          · simp [hnz, hmS]
      have hnest_ts : (if globN s "ts" ≠ 0 ∧ memW post (globN s "ts" + 32) ∈ S then htabValues post (memW post (globN s "ts" + 32)) else []) =
          (if globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S then htabValues s (memW s (globN s "ts" + 32)) else []) := by
        by_cases hnz : globN s "ts" = 0
        · simp [hnz]
        · rw [memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz (by omega)]
          by_cases hmS : memW s (globN s "ts" + 32) ∈ S
          · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
          · simp [hnz, hmS]
      have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
          (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
        apply List.flatMap_congr; intro ad had
        have had_mem := balRecord_ivl_mem had
        rcases fixedObject_le_2pow64 hAs.2 hWT.2.2.1 (bal_in_fixedObjects had_mem) with h0 | had_bnd
        · dsimp only at h0; omega
        · dsimp only at had_bnd
          have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd_at) had_mem
          rw [memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩,
              memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩]
      have hjrn_mp : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
          (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
        apply List.map_congr_left; intro k hk; rw [List.mem_range] at hk
        have hjc_le := hWT.2.1.1
        have hjc_ne : globN s "journal_cap" ≠ 0 := by omega
        rcases hWT.2.1.2.2.1 with h0 | ⟨hal, _⟩
        · exact absurd h0 hjc_ne
        · have hbnd := allocated_le_2pow64 hAs.2 hal; dsimp only at hbnd
          have hkle : 32 * k + 8 ≤ 32 * globN s "journal_cap" := by omega
          exact memW_eq_of_cellHits hcell (by omega) (mem_worldTypedIvls_journal (S := S) (Nd := Nd_at) hjc_ne)
            ⟨by dsimp only; omega, by dsimp only; omega⟩
      dsimp only
      rw [hglob_nonHeap "bs" (by decide), hglob_nonHeap "ts" (by decide),
          hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]
    have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
      intro i t; unfold DelExclusive; rw [hworldRefs_eq]
      refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
        forall_congr' fun k => imp_congr_right fun hk => ?_)
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      have hk_ok : k + 8 ≤ 280 ∧ k % 8 = 0 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
      rw [(hrec_eq _ hj_mem).1 k hk_ok.1 hk_ok.2]
    intro i hi
    have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hm_eq := (hrec_eq _ hi_mem).2.1 48 (by omega) (by omega)
    have hmm_eq := (hrec_eq _ hi_mem).2.1 56 (by omega) (by omega)
    have he24_eq := (hrec_eq _ hi_mem).1 24 (by omega) (by omega)
    have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
        ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
      apply List.map_congr_left; intro ec hec
      exact (hrec_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by omega)
    have hM := hMarks i hi; dsimp only at hM ⊢
    rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfeq, htake_eq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
    · intro j hj hij
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem,
          (hrec_eq _ hj_mem).1 112 (by omega) (by omega)]
      exact m5 j hj hij
    · intro t ht
      rw [hfp_eq_all t ht, hdelEx_iff i t]; exact m8 t ht
  · rw [worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hcg,
        hframeRoleSlots_eq,
        journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hcell hcg]
    unfold RolesOK at hRoles ⊢
    refine ⟨fun a ha => ?_, hRoles.2⟩
    obtain ⟨haS, hkl⟩ := hRoles.1 a ha
    have htb := ((hWT.1.2.1 a.1 haS).1.1 (a.1, 88) (by simp [htabFootprint])).1
    rw [htab_hdr_eq hcell haS htb 0 (by omega)]; exact ⟨haS, hkl⟩
  · have sum_eq : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum =
        ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum := by
      unfold evmR at hR_eq; rw [hchain_eq] at hR_eq; exact hR_eq
    rw [sum_eq]; exact hGas

/-- Appending one journal record `(t0, kc, pres, oldv)` at index `jn = globN s "journal_n" < globN s "journal_cap"`
and bumping `journal_n := jn + 1` preserves `EvmInvAt`, `evmChain`, and `evmR` when `t0` is a
non-`ts+32` world-role table in `S`. -/
theorem evmInvAt_of_journal_push {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {t0 : Nat}
    (hAs : ArenaReady s) (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S)
    (hAp : ArenaReady post) (hbe : post.be = s.be)
    (hjn_lt : globN s "journal_n" < globN s "journal_cap")
    (hjn_post : globN post "journal_n" = globN s "journal_n" + 1)
    (hg_kept : GlobalsKept ["journal_n"] s post)
    (hcell_out : ∀ a : BitVec 64,
      ¬ (globN s "journal" + 32 * globN s "journal_n" ≤ a.toNat ∧
          a.toNat + 8 ≤ globN s "journal" + 32 * globN s "journal_n" + 32) →
      post.memory a = s.memory a)
    (ht0_post : memW post (globN s "journal" + 32 * globN s "journal_n") = t0)
    (ht0_S : t0 ∈ S)
    (ht0_wref : t0 ∈ worldTableRefs s S)
    (ht0_wrs : (t0, journalRole s t0) ∈ worldRoleSlots s)
    (ht0_not_ts32 : journalRole s t0 ≠ "ts+32") :
    InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt post S ∧
    evmChain post = evmChain s ∧
    evmR post = evmR s := by
  obtain ⟨hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInv
  obtain ⟨hT, hJ, hF, _⟩ := hW
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT
  have hdom_eq : post.memaddrs = s.memaddrs := hAp.1.memaddrs.trans hAs.1.memaddrs.symm
  have hg_nonJn : ∀ name : String, ofString name ≠ ofString "journal_n" → globN post name = globN s name := by
    intro name hne
    exact (globN_eq_of_lookup_eq (hg_kept (ofString name) (by simp [hne]))).symm
  have hhp_eq : globN post "heap_ptr" = globN s "heap_ptr" := hg_nonJn "heap_ptr" (by decide)
  have hsc_eq : globN post "scratch_ptr" = globN s "scratch_ptr" := hg_nonJn "scratch_ptr" (by decide)
  have hfm_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := hg_nonJn "frame_mem_ptr" (by decide)
  have hev_eq : globN post "ev" = globN s "ev" := hg_nonJn "ev" (by decide)
  have hcc_eq : globN post "cur_cont" = globN s "cur_cont" := hg_nonJn "cur_cont" (by decide)
  have hevm_empty_eq : globN post "evm_empty" = globN s "evm_empty" := hg_nonJn "evm_empty" (by decide)
  have hvmsa_eq : globN post "vm_system_address" = globN s "vm_system_address" := hg_nonJn "vm_system_address" (by decide)
  have hws_g : globN post "ws" = globN s "ws" := hg_nonJn "ws" (by decide)
  have hbs_g : globN post "bs" = globN s "bs" := hg_nonJn "bs" (by decide)
  have hts_g : globN post "ts" = globN s "ts" := hg_nonJn "ts" (by decide)
  have hbo_g : globN post "bo" = globN s "bo" := hg_nonJn "bo" (by decide)
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" := hg_nonJn "bal_accounts" (by decide)
  have hbia_g : globN post "bal_idx_accts" = globN s "bal_idx_accts" := hg_nonJn "bal_idx_accts" (by decide)
  have hbis_g : globN post "bal_idx_stor" = globN s "bal_idx_stor" := hg_nonJn "bal_idx_stor" (by decide)
  have hj_g : globN post "journal" = globN s "journal" := hg_nonJn "journal" (by decide)
  have hjc_g : globN post "journal_cap" = globN s "journal_cap" := hg_nonJn "journal_cap" (by decide)
  have hag : AllocatorGrows s post := ⟨by rw [hhp_eq], by rw [hsc_eq]⟩
  have hjc_nz : globN s "journal_cap" ≠ 0 := by omega
  have hjr_mem_fix : (globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right; simp [hjc_nz]
  obtain ⟨hal_jr, hwords_jr⟩ : Allocated s (globN s "journal", 32 * globN s "journal_cap") ∧
      WordsOK s (globN s "journal", 32 * globN s "journal_cap") := by
    rcases hJ.2.2.1 with h0 | h
    · exact absurd h0 hjc_nz
    · exact h
  have hjr_hi : globN s "journal" + 32 * globN s "journal_cap" ≤ 2 ^ 64 :=
    (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_jr).2
  set slotIvl : Ivl := (globN s "journal" + 32 * globN s "journal_n", 32)
  have hslot_in_jr : Inside slotIvl (globN s "journal") (globN s "journal" + 32 * globN s "journal_cap") := by
    dsimp [slotIvl, Inside]; omega
  have hunhit_of_disj_jr : ∀ i : Ivl, Disj i (globN s "journal", 32 * globN s "journal_cap") →
      InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post i := by
    intro i hdj a ha8 h1 h2
    apply hcell_out a
    intro ⟨hs1, hs2⟩
    rcases hdj with d | d | d | d <;> omega
  have hfix_pw : ((globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++
      [(globN s "journal", 32 * globN s "journal_cap")] ++ blockOutObjects s ++ balObjects s).Pairwise Disj := by
    have hp := hF.2; unfold fixedObjects at hp; simpa [hjc_nz] using hp
  obtain ⟨hpw_gb_jr_bo, hpw_bal, hdisj_left_bal⟩ := List.pairwise_append.1 hfix_pw
  obtain ⟨hpw_gb_jr, hpw_bo, hdisj_left_bo⟩ := List.pairwise_append.1 hpw_gb_jr_bo
  obtain ⟨_, _, hdisj_gb_jr⟩ := List.pairwise_append.1 hpw_gb_jr
  have hdisj_sym : ∀ {x y : Ivl}, Disj x y → Disj y x := fun h => by
    unfold Disj at h ⊢; omega
  have hu_gb : ∀ gn ∈ globalBuffers, globN s gn.1 ≠ 0 →
      InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (globN s gn.1, gn.2) := by
    intro gn hgn hnz
    have hmem : (globN s gn.1, gn.2) ∈ globalBuffers.map (fun g => (globN s g.1, if globN s g.1 = 0 then 0 else g.2)) := by
      rw [List.mem_map]; exact ⟨gn, hgn, by simp [hnz]⟩
    exact hunhit_of_disj_jr _ (hdisj_gb_jr _ hmem _ (List.mem_singleton.2 rfl))
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 →
      InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post i := by
    intro i hi _
    exact hunhit_of_disj_jr _ (hdisj_sym (hdisj_left_bo _ (List.mem_append_right _ (List.mem_singleton.2 rfl)) _ hi))
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 →
      InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post i := by
    intro i hi _
    exact hunhit_of_disj_jr _ (hdisj_sym (hdisj_left_bal _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.2 rfl))) _ hi))
  have hu_tab : ∀ u ∈ S, ∀ i ∈ htabFootprint s u,
      InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post i := fun u hu i hi =>
    hunhit_of_disj_jr i (((hT.2.1 u hu).2 i hi).2 _ hjr_mem_fix)
  have hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    have hlow : ∀ a : Nat, a + 8 ≤ sourceBase → memW post a = memW s a := fun a ha => by
      have hsb_lt : sourceBase < 2 ^ 64 := by decide
      have ha_lt : a < 2 ^ 64 := lt_of_le_of_lt (by omega) hsb_lt
      have hjr_lo : sourceBase ≤ globN s "journal" := by
        rcases hal_jr with ⟨hl, _⟩ | ⟨hl, _⟩
        · exact hl
        · have := hAs.2.2.2.1; have := hAs.2.2.2.2.1
          rw [R11Shards.sourceBase_val]; rw [R11Shards.scratchStart_val] at *; dsimp at hl ⊢; omega
      have hm := hcell_out (BitVec.ofNat 64 a) (fun ⟨h1, _⟩ => by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1; omega)
      unfold memW; rw [hm]
    exact ⟨hlow 0 (by decide), hlow 8 (by decide), hlow 16 (by decide)⟩
  have hu_ws : globN s "ws" ≠ 0 → InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (globN s "ws", 40) :=
    hu_gb ("ws", 40) (by simp [globalBuffers])
  have hu_bs : globN s "bs" ≠ 0 → InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (globN s "bs", 80) :=
    hu_gb ("bs", 80) (by simp [globalBuffers])
  have hu_ts : globN s "ts" ≠ 0 → InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (globN s "ts", 72) :=
    hu_gb ("ts", 72) (by simp [globalBuffers])
  have hu_bo : globN s "bo" ≠ 0 → InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (globN s "bo", 88) :=
    hu_gb ("bo", 88) (by simp [globalBuffers])
  have hbo_words : globN s "bo" ≠ 0 → ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := fun hnz k hk => by
    have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    simpa [hbo_g] using InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
      hAs.2 hF "bo" 88 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hbo_g hnz (hu_bo hnz) hk_in.1 hk_in.2
  have hbo_eq := InitECandidate.Solver.Wave8Contracts.M08.blockOutObjects_eq_of_bo_unhit hAs.2 hF hbo_g
    hT.2.2.2.2.2.2.2.2.2.2.1
    (fun h => hbo_words h 24 (by simp))
    (fun h => hbo_words h 32 (by simp))
    (fun h => hbo_words h 40 (by simp))
    (fun h => hbo_words h 56 (by simp))
    (fun h => hbo_words h 72 (by simp))
    (fun h => hbo_words h 80 (by simp))
    (fun _ _ => by simp [hm0.1, hm0.2.2])
    (fun _ _ => by simp [hm0.1, hm0.2.2])
    (fun h h40 => hu_bo_lst (memW s (globN s "bo" + 40), 24) (by simp [blockOutObjects, h, h40]) rfl)
    (fun h h72 => hu_bo_lst (memW s (globN s "bo" + 72), 24) (by simp [blockOutObjects, h, h72]) rfl)
  have hbal_eq := InitECandidate.Solver.Wave8Contracts.M08.balObjects_eq_of_unhit hAs.2 hT hF hba_g hu_tab hu_bal hm0
  have hfix_eq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [hbo_eq.1, hbal_eq.1, hj_g, hjc_g]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "journal_n" := by revert gn hgn; decide
    rw [hg_nonJn gn.1 hne]
  have hF_post := InitECandidate.Solver.Wave8Contracts.M08.fixedTyped_transfer hAs.1 hAp.1 hag hF hfix_eq
  have hrole_eq : ∀ t, journalRole post t = journalRole s t := fun t => by
    unfold journalRole
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · have hw16 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hts_g h (hu_ts h) (k := 16) (by omega) (by omega)
      have hw32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
      have hw48 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hts_g h (hu_ts h) (k := 48) (by omega) (by omega)
      have hw64 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hts_g h (hu_ts h) (k := 64) (by omega) (by omega)
      simp only [hts_g] at hw16 hw32 hw48 hw64 ⊢
      rw [hw16, hw32, hw48, hw64]
  have hj_cells : ∀ i, i < globN s "journal_n" →
      memW post (globN s "journal" + 32 * i) = memW s (globN s "journal" + 32 * i) ∧
      memW post (globN s "journal" + 32 * i + 16) = memW s (globN s "journal" + 32 * i + 16) ∧
      memW post (globN s "journal" + 32 * i + 24) = memW s (globN s "journal" + 32 * i + 24) := by
    intro i hi
    have hj8 : (globN s "journal") % 8 = 0 := hwords_jr.1
    have hcell_i : ∀ off : Nat, off % 8 = 0 → off + 8 ≤ 32 →
        memW post (globN s "journal" + 32 * i + off) = memW s (globN s "journal" + 32 * i + off) := by
      intro off hoff8 hoff32
      have ha_lt : globN s "journal" + 32 * i + off < 2 ^ 64 := by omega
      have hm := hcell_out (BitVec.ofNat 64 (globN s "journal" + 32 * i + off)) (fun ⟨h1, h2⟩ => by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1 h2; omega)
      unfold memW; rw [hm]
    exact ⟨by simpa using hcell_i 0 (by omega) (by omega),
           hcell_i 16 (by omega) (by omega),
           hcell_i 24 (by omega) (by omega)⟩
  have hJ_post : JournalTyped post S := by
    unfold JournalTyped
    rw [hjn_post, hjc_g, hj_g]
    refine ⟨by omega, hJ.2.1,
      Or.inr ⟨hag.allocated hal_jr, InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 hwords_jr⟩,
      fun i hi => ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hilt | rfl
    · rw [(hj_cells i hilt).1]; exact hJ.2.2.2 i hilt
    · rw [ht0_post]; exact ht0_S
  have hjrs_eq : journalRoleSlots post = journalRoleSlots s ++ [(t0, journalRole s t0)] := by
    unfold journalRoleSlots
    rw [hjn_post, hj_g, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    congr 1
    · apply List.flatMap_congr; intro i hi
      rw [List.mem_range] at hi
      obtain ⟨c0, c16, c24⟩ := hj_cells i hi
      dsimp only; rw [c0, c16, c24, hrole_eq]
    · dsimp only
      rw [ht0_post, hrole_eq, if_neg (fun h => ht0_not_ts32 h.2)]
  have hwrs_eq : worldRoleSlots post = worldRoleSlots s := by
    have hrec_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] = recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
      unfold recRoles
      by_cases h : globN s "ws" = 0
      · simp [hws_g, h]
      · have hw16 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hws_g h (hu_ws h) (k := 16) (by omega) (by omega)
        have hw32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hws_g h (hu_ws h) (k := 32) (by omega) (by omega)
        simp only [hws_g] at hw16 hw32 ⊢; simp [h, hw16, hw32]
    have hrec_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
        (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
        recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
        (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
      unfold recRoles
      by_cases h : globN s "bs" = 0
      · simp [hbs_g, h]
      · simp only [hbs_g, h, ↓reduceIte]; apply List.map_congr_left
        intro ⟨k, r⟩ hkr
        have hk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
          rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        have hw := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hbs_g h (hu_bs h) hk.1 hk.2
        simp only [hbs_g] at hw; simp [hw]
    have hrec_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
        recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
      unfold recRoles
      by_cases h : globN s "ts" = 0
      · simp [hts_g, h]
      · simp only [hts_g, h, ↓reduceIte]; apply List.map_congr_left
        intro ⟨k, r⟩ hkr
        have hk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
          rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        have hw := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hts_g h (hu_ts h) hk.1 hk.2
        simp only [hts_g] at hw; simp [hw]
    have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
      unfold nestRoles
      by_cases h : globN s "bs" = 0
      · simp [hbs_g, h]
      · have hw32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hbs_g h (hu_bs h) (k := 32) (by omega) (by omega)
        simp only [hbs_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
        by_cases h32 : memW s (globN s "bs" + 32) = 0
        · simp [h32]
        · simp only [h32, ↓reduceIte]
          have hmS : memW s (globN s "bs" + 32) ∈ S := by
            rcases hT.2.2.2.2.1 32 (by simp [bsTableSlots]) h with h0 | hm
            · exact absurd h0 h32
            · exact hm
          rw [InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
    have hnest_ts : nestRoles post "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
      unfold nestRoles
      by_cases h : globN s "ts" = 0
      · simp [hts_g, h]
      · have hw32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
        simp only [hts_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
        by_cases h32 : memW s (globN s "ts" + 32) = 0
        · simp [h32]
        · simp only [h32, ↓reduceIte]
          have hmS : memW s (globN s "ts" + 32) ∈ S := by
            rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) h with h0 | hm
            · exact absurd h0 h32
            · exact hm
          rw [InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
    have hrecs_bal := InitECandidate.Solver.Wave8Contracts.M08.balRecords_eq_of_unhit hT hba_g (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_tab _ hm)
    unfold worldRoleSlots
    rw [hrec_ws, hrec_bs, hrec_ts, hba_g, hbia_g, hbis_g, hnest_bs, hnest_ts, hrecs_bal]
    congr 1; congr 1
    apply List.flatMap_congr; intro ad had
    rw [← hrecs_bal] at had
    obtain ⟨e0, e8, _⟩ := hbal_eq.2 ad had
    rw [e0, e8]
  have htab_fp_hdr : ∀ u ∈ S,
      (∀ k, k < 11 → hdr post u k = hdr s u k) ∧ htabFootprint post u = htabFootprint s u := by
    intro u hu
    have hfp := (hT.2.1 u hu).1.1
    have ht_fp : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
    have h264 : heapEnd ≤ 2 ^ 64 := by decide
    exact InitECandidate.Solver.Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit
      ((hfp _ ht_fp).2.1) (by have := (hfp _ ht_fp).1.2; dsimp at this; omega) (hu_tab u hu _ ht_fp)
  have transfer_tries : ∀ Nd, TriesTypedWith s S Nd →
      TriesTypedWith post S Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
    intro Nd hTr
    have hu_nd_rec : ∀ n ∈ Nd, InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (nodeIvl s n) := fun n hn => by
      have hmem : nodeIvl s n ∈ nodeExtents s Nd := by
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
      exact hunhit_of_disj_jr _ ((hTr.2.1 _ hmem).2 _ hjr_mem_fix)
    have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
        ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
      intro n hn h12 hlen0 k hk
      have h264 : heapLimit ≤ 2 ^ 64 := by decide
      rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, _, hin_p, _⟩
      · exact absurd h0 hlen0
      · have hp_ne : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
          unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
        have hdj := (hTr.2.1 _ hp_ne).2 _ hjr_mem_fix
        have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by have := hin_p.2; omega
        let c := panByteAlignHOL (BitVec.ofNat 64 (memW s (n + 32) + k))
        have hc_nat : c.toNat = (memW s (n + 32) + k) / 8 * 8 := by
          rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
        have hj8 : (globN s "journal") % 8 = 0 := hwords_jr.1
        have hmem := hcell_out c (fun ⟨h1, h2⟩ => by
          rw [hc_nat] at h1 h2
          rcases hdj with d | d | d | d <;> dsimp at d <;> omega)
        unfold memB
        change (match post.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v post.be).toNat) =
               (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v s.be).toNat)
        rw [hmem, hbe]
    obtain ⟨hNH_post, hne_eq⟩ := InitECandidate.Solver.Wave8Contracts.M08.nodeHeap_congr_bytes
      hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_byte
    refine ⟨⟨hNH_post, ?_, ?_⟩, hne_eq⟩
    · rw [hne_eq, hfix_eq]
      intro o ho
      exact ⟨fun u hu i hi => by rw [(htab_fp_hdr u hu).2] at hi; exact (hTr.2.1 o ho).1 u hu i hi,
             (hTr.2.1 o ho).2⟩
    · intro hws_nz
      rw [hws_g] at hws_nz
      have e24 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hws_g hws_nz (hu_ws hws_nz) (k := 24) (by omega) (by omega)
      have e32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hws_g hws_nz (hu_ws hws_nz) (k := 32) (by omega) (by omega)
      rw [e24, e32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hws_nz
      refine ⟨hr24, fun htS i hi => ?_⟩
      have hu32 := hu_tab _ htS
      have hwf32 := (hT.2.1 _ htS).1
      have hvals_eq := InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit hwf32 hu32
      obtain ⟨hhdr32, _⟩ := htab_fp_hdr _ htS
      rw [hhdr32 3 (by omega)] at hi
      have hget : (htabValues post (memW s (globN s "ws" + 32)))[i]? =
          (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals_eq]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hhdr32 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]; exact hr32 htS i hi
  obtain ⟨hTr_at_post, hne_at_eq⟩ := transfer_tries Nd_at hTr_at
  have hu_fo_m08 : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec,
      InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post o :=
    fun ec hec o ho => hunhit_of_disj_jr o ((hFO_disj ec hec o ho).2 _ hjr_mem_fix)
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨hb1, hb2, hb88, _⟩ := frameWF_bounds hAs.2 hFW
    have he1_8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    have he2_8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have he88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    refine ⟨fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hu_fo_m08 ec hec (ec.1, 280) (by simp [frameObjects])) (by omega) hb1 ⟨by omega, by omega⟩,
            fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hu_fo_m08 ec hec (ec.2, 104) (by simp [frameObjects])) (by omega) hb2 ⟨by omega, by omega⟩,
            fun k hk hk8 => InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
              (hu_fo_m08 ec hec (memW s (ec.1 + 88), 24) (by simp [frameObjects])) (by omega) hb88 ⟨by omega, by omega⟩⟩
  have hchain_aux : ∀ (fuel e c : Nat),
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel; induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      obtain ⟨_, hc_eq, _⟩ := hrec_eq (e, c) hec
      have hc16 := hc_eq 16 (by omega) (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega) (by omega)
      have hc8 := hc_eq 8 (by omega) (by omega)
      simp only [evmChainFrom, hc16, hc0, hc8]
      split
      · rfl
      · rename_i hne16
        rw [ih]; intro ec' hec'; exact hsub ec' (by simp [evmChainFrom, hne16, hec'])
  have hchain_eq : evmChain post = evmChain s := by
    unfold evmChain; rw [hev_eq, hcc_eq]
    exact hchain_aux _ _ _ (fun _ h => h)
  have hfrs_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots; apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega) (by omega), he_eq 168 (by omega) (by omega),
        he_eq 176 (by omega) (by omega)]
  have hRoles_evm_post : RolesOK post S (worldRoleSlots post ++ frameRoleSlots post (evmChain s))
      (journalRoleSlots post) := by
    rw [hwrs_eq, hfrs_eq, hjrs_eq]
    have ht0_in_old : (t0, journalRole s t0) ∈ (worldRoleSlots s ++ frameRoleSlots s (evmChain s)) ++ journalRoleSlots s :=
      List.mem_append_left _ (List.mem_append_left _ ht0_wrs)
    refine ⟨?_, hRoles.2.1, ?_⟩
    · intro a ha
      have ha_old : a ∈ (worldRoleSlots s ++ frameRoleSlots s (evmChain s)) ++ journalRoleSlots s := by
        rcases List.mem_append.1 ha with hsl | hjr
        · exact List.mem_append_left _ hsl
        · rcases List.mem_append.1 hjr with hjr_old | hjr_new
          · exact List.mem_append_right _ hjr_old
          · rw [List.mem_singleton.1 hjr_new]; exact ht0_in_old
      obtain ⟨haS, hkl⟩ := hRoles.1 a ha_old
      rw [(htab_fp_hdr a.1 haS).1 0 (by omega)]
      exact ⟨haS, hkl⟩
    · intro a ha b hb heq
      have hb_old : b ∈ (worldRoleSlots s ++ frameRoleSlots s (evmChain s)) ++ journalRoleSlots s := by
        rcases List.mem_append.1 hb with hbsl | hbjr
        · exact List.mem_append_left _ hbsl
        · rcases List.mem_append.1 hbjr with hb_o | hb_n
          · exact List.mem_append_right _ hb_o
          · rw [List.mem_singleton.1 hb_n]; exact ht0_in_old
      rcases List.mem_append.1 ha with ha_old | ha_new
      · exact hRoles.2.2 a ha_old b hb_old heq
      · rw [List.mem_singleton.1 ha_new] at heq ⊢
        rcases List.mem_append.1 hb_old with hb_sl | hb_jr
        · have hsl_eq : ∀ {L : List (Nat × String)},
              L.Pairwise (fun x y => x.1 = y.1 → x.2 = y.2 ∧ x.2 ∈ sharedRoles) →
              ∀ {x y}, x ∈ L → y ∈ L → x.1 = y.1 → x.2 = y.2 := by
            intro L hpw x y hx hy hxy
            obtain ⟨ix, hix, rfl⟩ := List.getElem_of_mem hx
            obtain ⟨iy, hiy, rfl⟩ := List.getElem_of_mem hy
            rcases Nat.lt_trichotomy ix iy with hlt | rfl | hgt
            · exact (List.pairwise_iff_getElem.1 hpw ix iy hix hiy hlt hxy).1
            · rfl
            · exact (List.pairwise_iff_getElem.1 hpw iy ix hiy hix hgt hxy.symm).1.symm
          exact hsl_eq hRoles.2.1 (List.mem_append_left _ ht0_wrs) hb_sl heq
        · exact (hRoles.2.2 b hb_jr (t0, journalRole s t0)
            (List.mem_append_left _ (List.mem_append_left _ ht0_wrs)) heq.symm).symm
  have hRoles_world_post : RolesOK post S (worldRoleSlots post) (journalRoleSlots post) :=
    ⟨fun a ha => hRoles_evm_post.1 a (by
       rcases List.mem_append.1 ha with h1 | h2
       · exact List.mem_append_left _ (List.mem_append_left _ h1)
       · exact List.mem_append_right _ h2),
     (List.pairwise_append.1 hRoles_evm_post.2.1).1,
     fun a ha b hb => hRoles_evm_post.2.2 a ha b (by
       rcases List.mem_append.1 hb with h1 | h2
       · exact List.mem_append_left _ (List.mem_append_left _ h1)
       · exact List.mem_append_right _ h2)⟩
  have hrecs_bal := InitECandidate.Solver.Wave8Contracts.M08.balRecords_eq_of_unhit hT hba_g (fun hnz => by
    rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
    · exact absurd h0 hnz
    · exact hu_tab _ hm)
  have hT_post : TablesTyped post S := by
    obtain ⟨hnd, htwf, htpw, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, _⟩ := hT
    refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_eq.2, hRoles_world_post⟩
    · intro u hu
      rw [(htab_fp_hdr u hu).2, hfix_eq]
      exact ⟨InitECandidate.Solver.Wave8Contracts.M08.htabWF_congr_unhit hAs.1 hAp.1 (htwf u hu).1 (hu_tab u hu),
        fun i hi => ⟨hag.allocated ((htwf u hu).2 i hi).1, ((htwf u hu).2 i hi).2⟩⟩
    · intro u hu v hv hne i hi j hj
      rw [(htab_fp_hdr u hu).2] at hi; rw [(htab_fp_hdr v hv).2] at hj
      exact htpw u hu v hv hne i hi j hj
    · intro k hk hnz
      rw [hws_g] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hws_g hnz (hu_ws hnz) hk8.1 hk8.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [hbs_g] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hbs_g hnz (hu_bs hnz) hk8.1 hk8.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [hts_g] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hts_g hnz (hu_ts hnz) hk8.1 hk8.2]
      exact htsR k hk hnz
    · intro g hg_mem
      have hne : ofString g ≠ ofString "journal_n" := by
        simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg_mem
        rcases hg_mem with rfl | rfl | rfl <;> decide
      rw [hg_nonJn g hne]; exact hgR g hg_mem
    · intro hnz hmem
      rw [hbs_g] at hnz
      have ew := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hbs_g hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact InitECandidate.Solver.Wave8Contracts.M08.htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_tab _ hmem) (fun _ hx => hx) (hbsN hnz hmem)
    · intro hnz hmem
      rw [hts_g] at hnz
      have ew := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hts_g hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact InitECandidate.Solver.Wave8Contracts.M08.htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_tab _ hmem) (fun _ hx => hx) (htsN hnz hmem)
    · intro ad had
      have had_s : ad ∈ balRecords s := by rwa [← hrecs_bal]
      obtain ⟨e0, e8, _, hkl, hll⟩ := hbal_eq.2 ad had
      exact ⟨e0 ▸ (hbalT ad had_s).1, e8 ▸ (hbalT ad had_s).2.1, hkl, hll⟩
  have hW_post : WorldTyped post S := ⟨hT_post, hJ_post, hF_post, Nd_at, hTr_at_post⟩
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega)]
  have hlogs_congr : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := frameWF_bounds hAs.2 hFW
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    set logs := memW s (ec.1 + 88)
    have hl0 : memW post logs = memW s logs := by simpa [logs] using h88_eq 0 (by omega) (by omega)
    have hl8 : memW post (logs + 8) = memW s (logs + 8) := h88_eq 8 (by omega) (by omega)
    have hl16 : memW post (logs + 16) = memW s (logs + 16) := h88_eq 16 (by omega) (by omega)
    have harr_eq : ∀ i, i < memW s (logs + 8) →
        memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i) := by
      intro i hi
      have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
      have hlen_le : memW s (logs + 8) ≤ memW s (logs + 16) := hFW.2.2.2.2.2.2.2.2.2.2.2.1
      have hfl_b : memW s logs + 8 * memW s (logs + 16) ≤ 2 ^ 64 := by
        rcases hfob _ hfl_in with h0 | hb
        · unfold frameLogs at h0; dsimp only [logs] at h0 hi hlen_le; omega
        · simpa [frameLogs, logs] using hb
      have hfl_8 : (memW s logs) % 8 = 0 := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      have hfl_u : InitECandidate.Solver.Wave8Contracts.M08.IvlUnhit s post (memW s logs, 8 * memW s (logs + 16)) :=
        hu_fo_m08 ec hec (frameLogs s ec) hfl_in
      exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
        hfl_u (by omega) hfl_b ⟨by omega, by omega⟩
    have hlr_eq : ∀ i (hi : i < memW s (logs + 8)) off, off + 8 ≤ 40 → off % 8 = 0 →
        memW post (memW s (memW s logs + 8 * i) + off) = memW s (memW s (memW s logs + 8 * i) + off) := by
      intro i hi off hoff hoff8
      have hlr_in : (memW s (memW s logs + 8 * i), 40) ∈ frameObjects s ec := by
        unfold frameObjects; apply List.mem_append_right
        unfold frameLogObjects; dsimp only [logs]
        refine List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, ?_⟩
        unfold logOwnedIvls logRecordIvls
        exact List.mem_filter.2 ⟨by simp, by simp⟩
      have hlr_b : memW s (memW s logs + 8 * i) + 40 ≤ 2 ^ 64 := by
        rcases hfob _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_8 : (memW s (memW s logs + 8 * i)) % 8 = 0 := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · have he88_in := (hFW.1 (logs, 24) (by simp [logs])).1.1
          have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
          rw [R11Shards.scratchStart_val] at h1; dsimp only at he88_in; omega
        · exact (hent i hi).2.1.1
      exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
        (hu_fo_m08 ec hec _ hlr_in) (by omega) hlr_b ⟨by omega, by omega⟩
    refine ⟨?_, ?_⟩
    · unfold frameLogObjects; dsimp only
      rw [he_eq 88 (by omega) (by omega), hl8]
      apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi
      rw [hl0, harr_eq i hi]
      have r0 := hlr_eq i hi 0 (by omega) (by omega)
      have r8 := hlr_eq i hi 8 (by omega) (by omega)
      have r16 := hlr_eq i hi 16 (by omega) (by omega)
      have r24 := hlr_eq i hi 24 (by omega) (by omega)
      have r32 := hlr_eq i hi 32 (by omega) (by omega)
      simp only [Nat.add_zero] at r0
      unfold logOwnedIvls logRecordIvls
      rw [r0, r8, r16, r24, r32, hvmsa_eq]
    · rw [he_eq 88 (by omega) (by omega)]
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
      · exact Or.inl hz
      · right
        refine ⟨InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 hw_l, hag.allocated hal_l,
          by rw [hl8]; exact hlt28, by rw [hl8, hl16]; exact hle_cap, fun i hi => ?_⟩
        rw [hl8] at hi; rw [hl0]
        obtain ⟨hwa, hle⟩ := hent i hi
        refine ⟨(wordAt_congr_dom hdom_eq).2 hwa, ?_⟩
        rw [harr_eq i hi]
        have r0 := hlr_eq i hi 0 (by omega) (by omega)
        have r8 := hlr_eq i hi 8 (by omega) (by omega)
        have r16 := hlr_eq i hi 16 (by omega) (by omega)
        have r24 := hlr_eq i hi 24 (by omega) (by omega)
        have r32 := hlr_eq i hi 32 (by omega) (by omega)
        simp only [Nat.add_zero] at r0
        unfold LogEntryOK at hle ⊢
        rw [r0, r8, r16, r24, r32, hhp_eq]
        exact ⟨InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 hle.1, hle.2⟩
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 24 (by omega) (by omega), he_eq 40 (by omega) (by omega),
        he_eq 88 (by omega) (by omega), hframeLogs_eq ec hec, hframeRet_eq ec hec,
        (hlogs_congr ec hec).1]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega), he_eq 88 (by omega) (by omega)]
  have hmap_fo_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hwref_iff : ∀ u, u ∈ worldTableRefs post S ↔ u ∈ worldTableRefs s S := by
    intro u
    unfold worldTableRefs recordSlots
    rw [hws_g, hbs_g, hts_g,
        show globalTableRoots.map (globN post) = globalTableRoots.map (globN s) by
          simp only [globalTableRoots, List.map, hba_g, hbia_g, hbis_g],
        hrecs_bal, hj_g, hjn_post, List.range_succ, List.map_append, List.map_singleton, ht0_post]
    have hws_sl : (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW post (globN s "ws" + k)) =
        (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW s (globN s "ws" + k)) := by
      split; · rfl
      rename_i hnz; apply List.map_congr_left; intro k hk
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> omega
      simpa [hws_g] using InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hws_g hnz (hu_ws hnz) hk8.1 hk8.2
    have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
        (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
      split; · rfl
      rename_i hnz; apply List.map_congr_left; intro k hk
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      simpa [hbs_g] using InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hbs_g hnz (hu_bs hnz) hk8.1 hk8.2
    have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
        (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
      split; · rfl
      rename_i hnz; apply List.map_congr_left; intro k hk
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      simpa [hts_g] using InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hts_g hnz (hu_ts hnz) hk8.1 hk8.2
    have hnest_bs_w : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
        (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
      by_cases hnz : globN s "bs" = 0
      · simp [hnz]
      · have ew := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hbs_g hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
        simp only [hbs_g] at ew; rw [ew]
        by_cases hmS : memW s (globN s "bs" + 32) ∈ S
        · simp [hnz, hmS, InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
        · simp [hnz, hmS]
    have hnest_ts_w : (if globN s "ts" ≠ 0 ∧ memW post (globN s "ts" + 32) ∈ S then htabValues post (memW post (globN s "ts" + 32)) else []) =
        (if globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S then htabValues s (memW s (globN s "ts" + 32)) else []) := by
      by_cases hnz : globN s "ts" = 0
      · simp [hnz]
      · have ew := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [InitECandidate.Solver.Wave8Contracts.M08.typedRecords]) hts_g hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
        simp only [hts_g] at ew; rw [ew]
        by_cases hmS : memW s (globN s "ts" + 32) ∈ S
        · simp [hnz, hmS, InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
        · simp [hnz, hmS]
    have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
        (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
      apply List.flatMap_congr; intro ad had
      have had_p : ad ∈ balRecords post := by rwa [hrecs_bal]
      obtain ⟨e0, e8, _⟩ := hbal_eq.2 ad had_p
      rw [e0, e8]
    have hjrn_mp : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
        (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
      apply List.map_congr_left; intro k hk; rw [List.mem_range] at hk
      exact (hj_cells k hk).1
    dsimp only
    rw [hbs_g, hts_g, hws_sl, hbs_sl, hts_sl, hnest_bs_w, hnest_ts_w, hbal_fl, hjrn_mp, ← List.append_assoc]
    constructor
    · intro hmem
      rcases List.mem_append.1 hmem with hold | hnew
      · exact hold
      · rw [List.mem_singleton.1 hnew]
        exact ht0_wref
    · intro hold
      exact List.mem_append_left _ hold
  have hdelEx_iff : ∀ i u, DelExclusive post S (evmChain s) i u ↔ DelExclusive s S (evmChain s) i u := by
    intro i u; unfold DelExclusive
    refine and_congr (not_congr (hwref_iff u)) (forall_congr' fun j => forall_congr' fun hj =>
      forall_congr' fun k => imp_congr_right fun hk => ?_)
    have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
    have hk_le : k + 8 ≤ 280 ∧ k % 8 = 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    rw [(hrec_eq _ hj_mem).1 k hk_le.1 hk_le.2]
  have hR_eq : evmR post = evmR s :=
    evmR_eq_of_chain_and_words hchain_eq (fun ec hec =>
      ⟨(hrec_eq ec hec).1 64 (by omega) (by omega),
       (hrec_eq ec hec).1 192 (by omega) (by omega)⟩)
  have hmap_gas : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
        ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
    apply List.map_congr_left; intro ec hec
    rw [(hrec_eq ec hec).1 64 (by decide) (by decide), (hrec_eq ec hec).1 192 (by decide) (by decide)]
  refine ⟨⟨hW_post, ?_⟩, hchain_eq, hR_eq⟩
  dsimp only; rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, hmap_fo_eq ▸ hFO_pw, ?_, ?_, ?_, hRoles_evm_post, hmap_gas ▸ hGas⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    have hec_mem := List.mem_of_mem_getLast? hec
    exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2.1 16 (by omega) (by omega)]; exact hk0⟩
  · intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
    have hlo_ok := (hlogs_congr ec hec).2
    have hmsg_ok : MsgOwned post S (memW post (ec.1 + 112)) := by
      rw [he_eq 112 (by omega) (by omega)]
      obtain ⟨hal_m, hw_m, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := c17
      obtain ⟨hTr_m_post, hne_m_eq⟩ := transfer_tries Nd_m hTr_m
      refine ⟨hag.allocated hal_m, InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 hw_m,
        fun u hu i hi => by rw [(htab_fp_hdr u hu).2] at hi; exact hdt u hu i hi,
        by rw [hfix_eq]; exact hdf,
        by rw [hchain_eq]; intro ec' hec' o ho; rw [hframeObjects_eq ec' hec'] at ho; exact hdfo ec' hec' o ho,
        Nd_m, hTr_m_post, fun o ho j hj => by rw [hne_m_eq] at hj; exact hdj_m o ho j hj⟩
    unfold FrameWF; dsimp only
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 88 (by omega) (by omega), he_eq 24 (by omega) (by omega),
        he_eq 40 (by omega) (by omega), he_eq 16 (by omega) (by omega),
        he_eq 32 (by omega) (by omega), he_eq 136 (by omega) (by omega),
        he_eq 168 (by omega) (by omega), he_eq 176 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
        hframeLogs_eq ec hec, he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega),
        hframeRet_eq ec hec, hsc_eq, hfm_eq, hevm_empty_eq, hhp_eq]
    rw [he_eq 88 (by omega) (by omega)] at hlo_ok
    exact ⟨fun i hi => ⟨(c1 i hi).1, InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 (c1 i hi).2⟩,
      c2, InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 c3,
      c4, c5, c6, c7, c8, c9, c10, c11, c12,
      c13, InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 c14,
      (by rcases c15 with h0 | ⟨hin, hw⟩
          · exact Or.inl h0
          · exact Or.inr ⟨hin, InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 hw⟩),
      hlo_ok, hmsg_ok⟩
  · intro ec hec
    have hec_mem := List.mem_of_mem_tail hec
    unfold FrameRoom
    rw [(hrec_eq ec hec_mem).1 16 (by omega) (by omega), (hrec_eq ec hec_mem).1 232 (by omega) (by omega)]
    exact hFR_all ec hec
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
    rw [(hrec_eq _ hi0).2.1 80 (by decide) (by decide),
        (hrec_eq _ hi0).2.1 72 (by decide) (by decide),
        (hrec_eq _ hi1).1 40 (by decide) (by decide)]
    exact hRW i hi
  · intro ec hec o ho
    rw [hframeObjects_eq ec hec] at ho; rw [hfix_eq]
    exact ⟨fun u hu i hi => by rw [(htab_fp_hdr u hu).2] at hi; exact (hFO_disj ec hec o ho).1 u hu i hi,
           (hFO_disj ec hec o ho).2⟩
  · rw [hmap_fo_eq]
    refine ⟨Nd_at, hTr_at_post, fun o ho j hj => ?_⟩
    rw [hne_at_eq] at hj; exact hAT_at o ho j hj
  · intro i hi
    have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hm_eq := (hrec_eq _ hi_mem).2.1 48 (by omega) (by omega)
    have hmm_eq := (hrec_eq _ hi_mem).2.1 56 (by omega) (by omega)
    have he24_eq := (hrec_eq _ hi_mem).1 24 (by omega) (by omega)
    have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
        ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
      apply List.map_congr_left; intro ec hec
      exact (hrec_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by omega)
    have hM := hMarks i hi
    dsimp only at hM ⊢
    rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfix_eq, htake_eq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
    · intro j hj hij
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem,
          (hrec_eq _ hj_mem).1 112 (by omega) (by omega)]
      exact m5 j hj hij
    · intro u hu
      rw [(htab_fp_hdr u hu).2, hdelEx_iff i u]
      exact m8 u hu

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
