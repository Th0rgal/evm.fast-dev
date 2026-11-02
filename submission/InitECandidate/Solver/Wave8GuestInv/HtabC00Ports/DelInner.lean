import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.Reads

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

namespace InitECandidate.Solver.Wave8M19.Htab
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE InitECandidate.Solver.Wave8M19

theorem del_core_inner {F : Type} (s post : PanSemStateFiniteExact 64 F) (tw nd ow lw cw : BitVec 64)
    (M' : BitVec 64 → HolWordLab 64) (L I Fr : List Nat) (mvN : Nat)
    (hA : ArenaReady s) (hal : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i)
    (hB : HtabBlocks s tw.toNat)
    (hT : TreeWF L I Fr (hdr s tw.toNat 8) (hdr s tw.toNat 0) (hdr s tw.toNat 3) (hdr s tw.toNat 7)
      (hdr s tw.toNat 9) (nodeF s (hdr s tw.toNat 5)) (fun i => memW s (hdr s tw.toNat 6 + 8 * i)))
    (h5 : hdr s tw.toNat 5 = nd.toNat) (h6 : hdr s tw.toNat 6 = ow.toNat)
    (hcw : cw.toNat + 1 = hdr s tw.toNat 3)
    (hleaf : lw.toNat ∈ L)
    (hmvN : ∀ h : L.length - 1 < L.length, L[L.length - 1]'h = mvN) (hmvL : mvN ∈ L)
    (hMn : ∀ n off, n < hdr s tw.toNat 10 + 1 → off < 32 →
      rdN M' (nd.toNat + 32 * n + off) =
        if n = mvN ∧ off = 16 then nodeF s nd.toNat lw.toNat 16
        else rdN s.memory (nd.toNat + 32 * n + off))
    (hMo : ∀ i, i < hdr s tw.toNat 10 + 1 →
      rdN M' (ow.toNat + 8 * i) =
        if i = nodeF s nd.toNat lw.toNat 16 then mvN else rdN s.memory (ow.toNat + 8 * i))
    (hMh : ∀ c, c < 88 → rdN M' (tw.toNat + c) = rdN s.memory (tw.toNat + c))
    (hMf : ∀ a : BitVec 64, (∀ i ∈ htabFootprint s tw.toNat, ¬ InIvl a.toNat i) → M' a = s.memory a)
    (hpost : DelPostR s M' tw nd lw cw post) (hbranch : ¬ (wv (updW M' (tw + 24) cw (tw + 56)) = lw)) :
    ExitR9 tw.toNat s post := by
  rw [h5, h6] at hT
  obtain ⟨hlen, hnodup, hmem, hcI, hordL, hint, hr0, hr1, hrc, hpar, ⟨dep, hdep⟩, hfc⟩ := id hT
  obtain ⟨hfpB, hdisj, hk1, hk60, hstr, hnc2, hnx1, hnx⟩ := id hB
  simp only [htabFootprint, h5, h6] at hfpB hdisj
  have hfp0 := (hfpB (tw.toNat, 88) (by simp)).1
  have hfp2 := (hfpB (nd.toNat, (hdr s tw.toNat 10 + 1) * 32) (by simp)).1
  have hfp3 := (hfpB (ow.toNat, (hdr s tw.toNat 10 + 1) * 8) (by simp)).1
  simp only [Inside] at hfp0 hfp2 hfp3
  have hhe : heapEnd < 2 ^ 64 := by decide
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Disj] at hdisj
  have hdA := hdisj.1.2.1
  have hdB := hdisj.1.2.2
  have hdC := hdisj.2.2.1
  have hLIF : ∀ n ∈ L ++ I ++ Fr, 1 ≤ n ∧ n < hdr s tw.toNat 10 + 1 := fun n hn => by
    have := (hmem n).1 hn; omega
  have hnd12 := List.nodup_append.mp hnodup
  have hndLI := List.nodup_append.mp hnd12.1
  have hLI : ∀ a ∈ L, a ∉ I := fun a ha hai => hndLI.2.2 a ha a hai rfl
  have hLIr : ∀ a ∈ L ++ I, a ∉ Fr := fun a ha haf => hnd12.2.2 a ha a haf rfl
  have mL : ∀ a ∈ L, a ∈ L ++ I ++ Fr := fun a ha => by simp [ha]
  have mI : ∀ a ∈ I, a ∈ L ++ I ++ Fr := fun a ha => by simp [ha]
  have mF : ∀ a ∈ Fr, a ∈ L ++ I ++ Fr := fun a ha => by simp [ha]
  have mLI : ∀ a ∈ L ++ I, a ∈ L ++ I ++ Fr := fun a ha => List.mem_append_left _ ha
  have hlwB := hLIF _ (mL _ hleaf)
  have hmvB := hLIF _ (mL _ hmvL)
  have hlwl := lw.isLt
  have e7 : rdN s.memory (tw.toNat + 56) = hdr s tw.toNat 7 := by rw [hdr, memW_rdN]
  have e9 : rdN s.memory (tw.toNat + 72) = hdr s tw.toNat 9 := by rw [hdr, memW_rdN]
  have hMn0 := hMn
  simp only [nodeF, memW_rdN] at hMn hMo
  -- the frame (every store is inside the old blocks)
  have hframe : ∀ a : BitVec 64, (∀ i ∈ htabFootprint s tw.toNat, ¬ InIvl a.toNat i) →
      ¬ (tw.toNat ≤ a.toNat ∧ a.toNat < tw.toNat + 88) ∧
      ¬ (nd.toNat ≤ a.toNat ∧ a.toNat < nd.toNat + (hdr s tw.toNat 10 + 1) * 32) ∧
      ¬ (ow.toNat ≤ a.toNat ∧ a.toNat < ow.toNat + (hdr s tw.toNat 10 + 1) * 8) := by
    intro a ha
    have h0 := ha (tw.toNat, 88) (by simp [htabFootprint])
    have h2 := ha (nd.toNat, (hdr s tw.toNat 10 + 1) * 32) (by simp [htabFootprint, h5])
    have h3 := ha (ow.toNat, (hdr s tw.toNat 10 + 1) * 8) (by simp [htabFootprint, h6])
    simp only [InIvl] at h0 h2 h3
    exact ⟨h0, h2, h3⟩
  rcases hpost with ⟨hrt, hP⟩ | ⟨hrt, hP⟩
  · exact False.elim (hbranch hrt)
  · -- an inner leaf
    have hnr : lw.toNat ≠ hdr s tw.toNat 7 := by
      intro h; apply hrt; apply BitVec.eq_of_toNat_eq
      rdsimp [hMh, e7]; exact h.symm
    set nf := nodeF s nd.toNat with hnf
    have hlwLI : lw.toNat ∈ L ++ I := List.mem_append_left _ hleaf
    have hpI := hpar _ hlwLI hnr
    have hpB := hLIF _ (mI _ hpI)
    obtain ⟨hpcrit, hp8, hp16, hp816, hp8p, hp16p⟩ := hint _ hpI
    have hc8B := hLIF _ (mLI _ hp8)
    have hc16B := hLIF _ (mLI _ hp16)
    have hcl := (hdep _ hlwLI hnr).1
    have hlp : lw.toNat ≠ nf lw.toNat 0 := fun h => hLI _ hleaf (h ▸ hpI)
    have hmvp : mvN ≠ nf lw.toNat 0 := fun h => hLI _ hmvL (h ▸ hpI)
    have hcnt1 : 0 < hdr s tw.toNat 3 := by rw [← hlen]; exact List.length_pos_of_mem hleaf
    have hroot0 := (hr1 hcnt1).2
    have hgB : nf (nf lw.toNat 0) 0 = 0 ∨ nf (nf lw.toNat 0) 0 ∈ I := by
      by_cases hpr : nf lw.toNat 0 = hdr s tw.toNat 7
      · left; rw [hpr]; exact hroot0
      · right; exact hpar _ (List.mem_append_right _ hpI) hpr
    have hgN : nf (nf lw.toNat 0) 0 < hdr s tw.toNat 10 + 1 := by
      rcases hgB with h | h
      · omega
      · exact (hLIF _ (mI _ h)).2
    have hgp : nf (nf lw.toNat 0) 0 ≠ nf lw.toNat 0 := by
      by_cases hpr : nf lw.toNat 0 = hdr s tw.toNat 7
      · rw [hpr, hroot0]; omega
      · intro h
        have := (hdep _ (List.mem_append_right _ hpI) hpr).2
        rw [h] at this; omega
    have hmvg : mvN ≠ nf (nf lw.toNat 0) 0 := by
      rcases hgB with h | h
      · rw [h]; omega
      · exact fun e => hLI _ hmvL (e ▸ h)
    have hc8p : nf (nf lw.toNat 0) 8 ≠ nf lw.toNat 0 := by
      intro h; apply hgp; have := hp8p; rw [h] at this; exact this
    have hc16p : nf (nf lw.toNat 0) 16 ≠ nf lw.toNat 0 := by
      intro h; apply hgp; have := hp16p; rw [h] at this; exact this
    have hLlen : L.length ≤ hdr s tw.toNat 8 - 1 :=
      nodup_len_le L _ hndLI.1 (fun x hx => (hmem x).1 (mL x hx))
    have hL0 : 0 < L.length := List.length_pos_of_mem hleaf
    obtain ⟨Lp, C, hpe⟩ := hP
    -- name the words the deletion reads
    rcases hp0 : s.memory (nd + lw * 32 + 0) with ⟨p0⟩
    have ep0 : nf lw.toNat 0 = p0.toNat := nodeF_of s nd lw p0 0 hp0
    simp only [ep0] at hpB hp816 hp8p hp16p hc8B hc16B hcl hlp hmvp hgN hgp hmvg hc8p hc16p
    rcases hg0 : s.memory (nd + p0 * 32 + 0) with ⟨g0⟩
    have eg0 : nf p0.toNat 0 = g0.toNat := nodeF_of s nd p0 g0 0 hg0
    rcases hc8 : s.memory (nd + p0 * 32 + 8) with ⟨c8⟩
    have ec8 : nf p0.toNat 8 = c8.toNat := nodeF_of s nd p0 c8 8 hc8
    rcases hc16 : s.memory (nd + p0 * 32 + 16) with ⟨c16⟩
    have ec16 : nf p0.toNat 16 = c16.toNat := nodeF_of s nd p0 c16 16 hc16
    simp only [eg0, ec8, ec16] at hpB hp816 hp8p hp16p hc8B hc16B hcl hlp hmvp hgN hgp hmvg hc8p hc16p
    rcases hg8 : s.memory (nd + g0 * 32 + 8) with ⟨g8⟩
    have eg8 : nf g0.toNat 8 = g8.toNat := nodeF_of s nd g0 g8 8 hg8
    rcases hfr : s.memory (tw + 72) with ⟨fr⟩
    have efr : hdr s tw.toNat 9 = fr.toNat := hdr_of s tw fr 9 hfr
    have hc8n := hp8p
    have hc16n := hp16p
    have rp0 : rdN s.memory (nd.toNat + 32 * lw.toNat + 0) = p0.toNat := by rw [← memW_rdN]; exact ep0
    have rg0 : rdN s.memory (nd.toNat + 32 * p0.toNat + 0) = g0.toNat := by rw [← memW_rdN]; exact eg0
    have rc8 : rdN s.memory (nd.toNat + 32 * p0.toNat + 8) = c8.toNat := by rw [← memW_rdN]; exact ec8
    have rc16 : rdN s.memory (nd.toNat + 32 * p0.toNat + 16) = c16.toNat := by
      rw [← memW_rdN]; exact ec16
    have rg8 : rdN s.memory (nd.toNat + 32 * g0.toNat + 8) = g8.toNat := by rw [← memW_rdN]; exact eg8
    have rfr : rdN s.memory (tw.toNat + 72) = fr.toNat := by rw [← memW_rdN]; exact efr
    -- the sibling
    have esv : (if c8.toNat = lw.toNat then c16.toNat else c8.toNat) =
        (if c8 = lw then c16 else c8).toNat := by
      by_cases h : c8 = lw
      · rw [if_pos (congrArg BitVec.toNat h), if_pos h]
      · rw [if_neg (fun e => h (BitVec.eq_of_toNat_eq e)), if_neg h]
    generalize hsvd : (if c8 = lw then c16 else c8) = sv at esv
    have hsvB : 1 ≤ sv.toNat ∧ sv.toNat < hdr s tw.toNat 10 + 1 ∧ sv.toNat ≠ p0.toNat ∧
        sv.toNat ≠ lw.toNat := by
      clear * - esv hc8B hc16B hp816 hcl hc8p hc16p
      rw [← esv]; split_ifs <;> omega
    -- flatten the final memory
    have v1 : wv (updW M' (tw + 24) cw (nd + lw * 32 + 0)) = p0 := by
      clear * - hfp0 hfp2 hdA hhe hlwB hMn rp0
      apply BitVec.eq_of_toNat_eq
      rdsimp [hMn, rp0]
    have v2 : wv (updW M' (tw + 24) cw (nd + p0 * 32 + 0)) = g0 := by
      clear * - hfp0 hfp2 hdA hhe hpB hMn rg0
      apply BitVec.eq_of_toNat_eq
      rdsimp [hMn, rg0]
    have v3 : wv (updW M' (tw + 24) cw (nd + p0 * 32 + 8)) = c8 := by
      clear * - hfp0 hfp2 hdA hhe hpB hMn rc8
      apply BitVec.eq_of_toNat_eq
      rdsimp [hMn, rc8]
    have v4 : wv (updW M' (tw + 24) cw (nd + p0 * 32 + 16)) = c16 := by
      clear * - hfp0 hfp2 hdA hhe hpB hmvp hMn rc16
      apply BitVec.eq_of_toNat_eq
      rdsimp [hMn, rc16]
    rw [v1] at hpe
    simp only [delSib] at hpe
    rw [v2, v3, v4, hsvd] at hpe
    simp only [delSplice] at hpe
    have v5 : wv (updW (updW M' (tw + 24) cw) (nd + sv * 32 + 0) g0 (nd + g0 * 32 + 8)) = g8 := by
      clear * - hfp0 hfp2 hdA hhe hsvB hgN hmvg hMn rg8
      apply BitVec.eq_of_toNat_eq
      rdsimp [hMn, rg8]
    rw [v5] at hpe
    have v6a : wv (updW (updW (updW M' (tw + 24) cw) (nd + sv * 32 + 0) g0) (tw + 56) sv (tw + 72))
        = fr := by
      clear * - hfp0 hfp2 hdA hhe hsvB hgN hMh rfr
      apply BitVec.eq_of_toNat_eq
      rdsimp [hMh, rfr]
    have v6b : wv (updW (updW (updW M' (tw + 24) cw) (nd + sv * 32 + 0) g0) (nd + g0 * 32 + 8) sv
        (tw + 72)) = fr := by
      clear * - hfp0 hfp2 hdA hhe hsvB hgN hMh rfr
      apply BitVec.eq_of_toNat_eq
      rdsimp [hMh, rfr]
    have v6c : wv (updW (updW (updW M' (tw + 24) cw) (nd + sv * 32 + 0) g0) (nd + g0 * 32 + 16) sv
        (tw + 72)) = fr := by
      clear * - hfp0 hfp2 hdA hhe hsvB hgN hMh rfr
      apply BitVec.eq_of_toNat_eq
      rdsimp [hMh, rfr]
    simp only [fn_ite_apply, wv_ite, v6a, v6b, v6c, ite_self] at hpe
    -- Separate address arithmetic from the generic unlink operation.
    let initialFields : Nat → Nat → Nat := fun n off => rdN M' (nd.toNat + 32 * n + off)
    have hfields : ∀ n off, n ∈ L ++ I ++ Fr → off < 32 →
        nodeF post nd.toNat n off =
          unlinkFields initialFields lw.toNat p0.toNat g0.toNat sv.toNat fr.toNat
            (decide (g8 = p0)) n off := by
      intro n off hn hoff
      have hnB := hLIF n hn
      clear * - hpe initialFields hnB hoff hfp0 hfp2 hdA hhe hgN hpB hlwB hsvB
      have hnaddr : ∀ m k, m < hdr s tw.toNat 10 + 1 → k < 32 →
          nd.toNat + 32 * m + k < 2 ^ 64 := by
        clear * - hfp2 hhe
        intro m k hm hk
        omega
      have hhaddr : ∀ c, c < 88 → tw.toNat + c < 2 ^ 64 := by
        clear * - hfp0 hhe
        intro c hc
        omega
      have hsep : ∀ c, c < 88 → nd.toNat + 32 * n + off ≠ tw.toNat + c := by
        clear * - hnB hoff hdA
        intro c hc
        omega
      by_cases hg : g0.toNat = 0 <;> by_cases hl : g8.toNat = p0.toNat
      all_goals
        simp only [← BitVec.toNat_inj, bv0_toNat, hg, hl, if_true, if_false] at hpe
        simp only [nodeF, memW_rdN, hpe, NS_memory, unlinkFields, fieldWrite, initialFields]
        simp only [← BitVec.toNat_inj, hg, hl, decide_true, decide_false, if_true, if_false, fieldWrite]
        clear * - hnaddr hhaddr hsep hnB hoff hgN hpB hlwB hsvB hg hl
        simp only [an0, an8, an16, ah24, ah56, ah72, rdN_upd]
        simp only [Nat.mod_eq_of_lt (hnaddr n off hnB.2 hoff),
          Nat.mod_eq_of_lt (hnaddr lw.toNat 0 hlwB.2 (by decide)),
          Nat.mod_eq_of_lt (hnaddr p0.toNat 0 hpB.2 (by decide)),
          Nat.mod_eq_of_lt (hnaddr sv.toNat 0 hsvB.2.1 (by decide)),
          Nat.mod_eq_of_lt (hnaddr g0.toNat 8 hgN (by decide)),
          Nat.mod_eq_of_lt (hnaddr g0.toNat 16 hgN (by decide)),
          Nat.mod_eq_of_lt (hhaddr 24 (by decide)),
          Nat.mod_eq_of_lt (hhaddr 56 (by decide)),
          Nat.mod_eq_of_lt (hhaddr 72 (by decide))]
        simp only [if_neg (hsep 24 (by decide)), if_neg (hsep 56 (by decide)),
          if_neg (hsep 72 (by decide)),
          node_addr_eq_iff nd.toNat n lw.toNat off 0 hoff (by decide),
          node_addr_eq_iff nd.toNat n p0.toNat off 0 hoff (by decide),
          node_addr_eq_iff nd.toNat n sv.toNat off 0 hoff (by decide),
          node_addr_eq_iff nd.toNat n g0.toNat off 8 hoff (by decide),
          node_addr_eq_iff nd.toNat n g0.toNat off 16 hoff (by decide), hg,
          Bool.false_eq_true, if_false, if_true]
    have hu : ∀ n, n ∈ L ++ I ++ Fr →
        let f := unlinkFields initialFields lw.toNat p0.toNat g0.toNat sv.toNat fr.toNat
          (decide (g8 = p0))
        f n 0 = (if n = sv.toNat then g0.toNat else if n = p0.toNat then fr.toNat
          else if n = lw.toNat then p0.toNat else initialFields n 0) ∧
        f n 8 = (if n = g0.toNat ∧ decide (g8 = p0) = true then sv.toNat else initialFields n 8) ∧
        f n 16 = (if n = g0.toNat ∧ decide (g8 = p0) = false then sv.toNat else initialFields n 16) ∧
        f n 24 = initialFields n 24 := by
      intro n hn
      exact unlinkFields_spec initialFields lw.toNat p0.toNat g0.toNat sv.toNat fr.toNat n
        (decide (g8 = p0)) hlp hsvB.2.2.1 hsvB.2.2.2 (hLIF n hn).1
    have hTW := treeWF_del_inner (nd' := nodeF post nd.toNat)
      (ord' := fun i => memW post (ow.toNat + 8 * i)) lw.toNat hT hleaf hnr hL0
      (by
        intro n hn
        have hnB := hLIF n hn
        simp only [ep0, eg0, ec8, ec16, eg8, efr]
        rw [hfields n 0 hn (by decide), (hu n hn).1]
        simp only [initialFields, hnf, nodeF, memW_rdN]
        clear * - hnB hMn esv hmvg
        rdsimp [hMn, esv])
      (by
        intro n hn
        have hnB := hLIF n hn
        simp only [ep0, eg0, ec8, ec16, eg8, efr]
        rw [hfields n 8 hn (by decide), (hu n hn).2.1]
        simp only [initialFields, hnf, nodeF, memW_rdN, decide_eq_true_eq]
        clear * - hnB hMn esv hmvg
        rdsimp [hMn, esv])
      (by
        intro n hn
        have hnB := hLIF n hn
        simp only [ep0, eg0, ec8, ec16, eg8, efr, hmvN]
        rw [hfields n 16 hn (by decide), (hu n hn).2.2.1]
        simp only [initialFields, hnf, nodeF, memW_rdN, decide_eq_false_iff_not]
        clear * - hnB hMn esv hmvg
        rdsimp [hMn, esv]
        split_ifs <;> simp_all <;> omega)
      (by
        intro n hn
        have hnB := hLIF n hn
        rw [hfields n 24 hn (by decide), (hu n hn).2.2.2]
        simp only [initialFields, hnf, nodeF, memW_rdN]
        clear * - hnB hMn
        rdsimp [hMn])
      (by
        intro i hi
        have hiN : i < hdr s tw.toNat 10 + 1 := by
          clear * - hi hlen hLlen hnx
          omega
        have hread : ow.toNat + 8 * i < 2 ^ 64 := by
          clear * - hfp3 hhe hiN
          omega
        have hnaddr : ∀ m k, m < hdr s tw.toNat 10 + 1 → k < 32 →
            nd.toNat + 32 * m + k < 2 ^ 64 := by
          clear * - hfp2 hhe
          intro m k hm hk
          omega
        have hhaddr : ∀ c, c < 88 → tw.toNat + c < 2 ^ 64 := by
          clear * - hfp0 hhe
          intro c hc
          omega
        have hsepN : ∀ m k, m < hdr s tw.toNat 10 + 1 → k < 32 →
            ow.toNat + 8 * i ≠ nd.toNat + 32 * m + k := by
          clear * - hdC hiN
          intro m k hm hk
          omega
        have hsepH : ∀ c, c < 88 → ow.toNat + 8 * i ≠ tw.toNat + c := by
          clear * - hdB hiN
          intro c hc
          omega
        simp only [hmvN]
        by_cases hg : g0.toNat = 0 <;> by_cases hl : g8.toNat = p0.toNat
        all_goals
          simp only [← BitVec.toNat_inj, bv0_toNat, hg, hl, if_true, if_false] at hpe
          simp only [hnf, nodeF, memW_rdN, hpe, NS_memory]
          clear * - hread hnaddr hhaddr hsepN hsepH hiN hgN hpB hlwB hsvB hMo
          simp only [an0, an8, an16, ah24, ah56, ah72, rdN_upd]
          simp only [Nat.mod_eq_of_lt hread,
            Nat.mod_eq_of_lt (hnaddr lw.toNat 0 hlwB.2 (by decide)),
            Nat.mod_eq_of_lt (hnaddr p0.toNat 0 hpB.2 (by decide)),
            Nat.mod_eq_of_lt (hnaddr sv.toNat 0 hsvB.2.1 (by decide)),
            Nat.mod_eq_of_lt (hnaddr g0.toNat 8 hgN (by decide)),
            Nat.mod_eq_of_lt (hnaddr g0.toNat 16 hgN (by decide)),
            Nat.mod_eq_of_lt (hhaddr 24 (by decide)),
            Nat.mod_eq_of_lt (hhaddr 56 (by decide)),
            Nat.mod_eq_of_lt (hhaddr 72 (by decide))]
          simp only [if_neg (hsepH 24 (by decide)), if_neg (hsepH 56 (by decide)),
            if_neg (hsepH 72 (by decide)),
            if_neg (hsepN lw.toNat 0 hlwB.2 (by decide)),
            if_neg (hsepN p0.toNat 0 hpB.2 (by decide)),
            if_neg (hsepN sv.toNat 0 hsvB.2.1 (by decide)),
            if_neg (hsepN g0.toNat 8 hgN (by decide)),
            if_neg (hsepN g0.toNat 16 hgN (by decide))]
          exact hMo i hiN)
    have headers : ∀ k, k < 11 → hdr post tw.toNat k =
        if k = 9 then lw.toNat else if g0.toNat = 0 ∧ k = 7 then sv.toNat
        else if k = 3 then cw.toNat else hdr s tw.toNat k := by
      intro k hk
      have hc : 8 * k < 88 := by omega
      have hread : tw.toNat + 8 * k < 2 ^ 64 := by
        clear * - hfp0 hhe hc
        omega
      have hnaddr : ∀ m j, m < hdr s tw.toNat 10 + 1 → j < 32 →
          nd.toNat + 32 * m + j < 2 ^ 64 := by
        clear * - hfp2 hhe
        intro m j hm hj
        omega
      have hhaddr : ∀ c, c < 88 → tw.toNat + c < 2 ^ 64 := by
        clear * - hfp0 hhe
        intro c hc
        omega
      have hsepN : ∀ m j, m < hdr s tw.toNat 10 + 1 → j < 32 →
          tw.toNat + 8 * k ≠ nd.toNat + 32 * m + j := by
        clear * - hdA hc
        intro m j hm hj
        omega
      have he3 : tw.toNat + 8 * k = tw.toNat + 24 ↔ k = 3 := by omega
      have he7 : tw.toNat + 8 * k = tw.toNat + 56 ↔ k = 7 := by omega
      have he9 : tw.toNat + 8 * k = tw.toNat + 72 ↔ k = 9 := by omega
      by_cases hg : g0.toNat = 0 <;> by_cases hl : g8.toNat = p0.toNat
      all_goals
        simp only [← BitVec.toNat_inj, bv0_toNat, hg, hl, if_true, if_false] at hpe
        simp only [hdr, memW_rdN, hpe, NS_memory]
        clear * - hread hnaddr hhaddr hsepN he3 he7 he9 hc hgN hpB hlwB hsvB hMh hg
        simp only [an0, an8, an16, ah24, ah56, ah72, rdN_upd]
        simp only [Nat.mod_eq_of_lt hread,
          Nat.mod_eq_of_lt (hnaddr lw.toNat 0 hlwB.2 (by decide)),
          Nat.mod_eq_of_lt (hnaddr p0.toNat 0 hpB.2 (by decide)),
          Nat.mod_eq_of_lt (hnaddr sv.toNat 0 hsvB.2.1 (by decide)),
          Nat.mod_eq_of_lt (hnaddr g0.toNat 8 hgN (by decide)),
          Nat.mod_eq_of_lt (hnaddr g0.toNat 16 hgN (by decide)),
          Nat.mod_eq_of_lt (hhaddr 24 (by decide)),
          Nat.mod_eq_of_lt (hhaddr 56 (by decide)),
          Nat.mod_eq_of_lt (hhaddr 72 (by decide))]
        simp only [if_neg (hsepN lw.toNat 0 hlwB.2 (by decide)),
          if_neg (hsepN p0.toNat 0 hpB.2 (by decide)),
          if_neg (hsepN sv.toNat 0 hsvB.2.1 (by decide)),
          if_neg (hsepN g0.toNat 8 hgN (by decide)),
          if_neg (hsepN g0.toNat 16 hgN (by decide)), he3, he7, he9,
          hMh (8 * k) hc, hg, true_and, false_and, if_true, if_false]
        by_cases h9 : k = 9 <;> simp only [h9, if_true, if_false]
    have q : ∀ k, k ≠ 3 → k ≠ 7 → k ≠ 9 → k < 11 → hdr post tw.toNat k = hdr s tw.toNat k := by
      intro k h3 h7 h9 hk
      rw [headers k hk]
      simp only [h3, h7, h9, and_false, if_false]
    have q3 : hdr post tw.toNat 3 = cw.toNat := by
      rw [headers 3 (by decide)]
      simp
    have q9 : hdr post tw.toNat 9 = lw.toNat := by
      rw [headers 9 (by decide)]
      simp
    have q7 : hdr post tw.toNat 7 = if nf (nf lw.toNat 0) 0 = 0 then
        (if nf (nf lw.toNat 0) 8 = lw.toNat then nf (nf lw.toNat 0) 16 else nf (nf lw.toNat 0) 8)
        else hdr s tw.toNat 7 := by
      simp only [ep0, eg0, ec8, ec16, esv]
      rw [headers 7 (by decide)]
      simp
    have hW' : HtabWF post tw.toNat := by
      refine (htabWF_iff post tw.toNat).2 ⟨blocks_transfer s post tw.toNat (by rw [hpe]; rfl)
        (q 0 (by decide) (by decide) (by decide) (by decide)) (q 1 (by decide) (by decide) (by decide) (by decide)) (q 4 (by decide) (by decide) (by decide) (by decide)) (q 5 (by decide) (by decide) (by decide) (by decide)) (q 6 (by decide) (by decide) (by decide) (by decide)) (q 8 (by decide) (by decide) (by decide) (by decide)) (q 10 (by decide) (by decide) (by decide) (by decide)) hB, (L.set (nf lw.toNat 16) mvN).dropLast,
        I.erase (nf lw.toNat 0), lw.toNat :: nf lw.toNat 0 :: Fr, ?_⟩
      rw [q 8 (by decide) (by decide) (by decide) (by decide), q 0 (by decide) (by decide) (by decide) (by decide), q3, q7, q9, q 5 (by decide) (by decide) (by decide) (by decide), q 6 (by decide) (by decide) (by decide) (by decide), h5, h6]
      have : cw.toNat = hdr s tw.toNat 3 - 1 := by
        clear * - hcw
        omega
      rw [this]
      simpa only [hmvN] using hTW
    have hfp : htabFootprint post tw.toNat = htabFootprint s tw.toNat := by
      simp only [htabFootprint, q 1 (by decide) (by decide) (by decide) (by decide), q 4 (by decide) (by decide) (by decide) (by decide), q 5 (by decide) (by decide) (by decide) (by decide), q 6 (by decide) (by decide) (by decide) (by decide), q 10 (by decide) (by decide) (by decide) (by decide)]
    refine ⟨?_, q 0 (by decide) (by decide) (by decide) (by decide),
      q 1 (by decide) (by decide) (by decide) (by decide)⟩
    refine exitR_memPost _ s post _ ⟨Lp, C, hpe⟩ hA hal hW' hfp ?_
    intro a ha
    obtain ⟨ha0, ha2, ha3⟩ := hframe a ha
    have hal' := a.isLt
    clear * - ha0 ha2 hMf ha hfp0 hfp2 hhe hgN hpB hlwB hsvB hal'
    rdsimp []
    exact hMf a ha

end InitECandidate.Solver.Wave8M19.Htab
