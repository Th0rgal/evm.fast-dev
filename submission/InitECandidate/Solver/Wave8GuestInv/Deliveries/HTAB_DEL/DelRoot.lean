import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_DEL.Reads

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace InitECandidate.Solver.Wave8HtabAstra.Htab
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE InitECandidate.Solver.Wave8HtabAstra

theorem del_core_root {F : Type} (s post : PanSemStateFiniteExact 64 F) (tw nd ow lw cw : BitVec 64)
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
    (hpost : DelPostR s M' tw nd lw cw post) (hbranch : wv (updW M' (tw + 24) cw (tw + 56)) = lw) :
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
  · -- the leaf was the root
    have hrt' := congrArg BitVec.toNat hrt
    rdsimp [hMh, e7] at hrt'
    obtain ⟨Lp, C, hpe⟩ := hP
    have hnd0 : nodeF post nd.toNat lw.toNat 0 = hdr s tw.toNat 9 := by
      simp only [nodeF, memW_rdN, hpe, NS_memory]
      rdsimp [hMn, hMh, e9]
    obtain ⟨hc1, hL1, hI0, hTW⟩ := treeWF_del_root (nd' := nodeF post nd.toNat)
      (ord' := fun i => memW post (ow.toNat + 8 * i)) lw.toNat hT hleaf hrt'.symm hnd0 (by
        intro f hf
        have hfB := hLIF f (mF f hf)
        have hfl : f ≠ lw.toNat := fun h => hLIr _ (List.mem_append_left _ hleaf) (h ▸ hf)
        simp only [nodeF, memW_rdN, hpe, NS_memory]
        rdsimp [hMn, hMh])
    have q : ∀ k, k ≠ 3 → k ≠ 7 → k ≠ 9 → k < 11 → hdr post tw.toNat k = hdr s tw.toNat k := by
      intro k h3 h7 h9 hk
      simp only [hdr, memW_rdN, hpe, NS_memory]
      rdsimp [hMh]
    have q3 : hdr post tw.toNat 3 = cw.toNat := by
      simp only [hdr, memW_rdN, hpe, NS_memory]
      rdsimp []
    have q7 : hdr post tw.toNat 7 = 0 := by
      simp only [hdr, memW_rdN, hpe, NS_memory]
      rdsimp []
    have q9 : hdr post tw.toNat 9 = lw.toNat := by
      simp only [hdr, memW_rdN, hpe, NS_memory]
      rdsimp []
    have hW' : HtabWF post tw.toNat := by
      refine (htabWF_iff post _).2 ⟨blocks_transfer s post _ (by rw [hpe]; rfl)
        (q 0 (by decide) (by decide) (by decide) (by decide))
        (q 1 (by decide) (by decide) (by decide) (by decide))
        (q 4 (by decide) (by decide) (by decide) (by decide))
        (q 5 (by decide) (by decide) (by decide) (by decide))
        (q 6 (by decide) (by decide) (by decide) (by decide))
        (q 8 (by decide) (by decide) (by decide) (by decide))
        (q 10 (by decide) (by decide) (by decide) (by decide)) hB, [], [], lw.toNat :: Fr, ?_⟩
      rw [q 8 (by decide) (by decide) (by decide) (by decide),
        q 0 (by decide) (by decide) (by decide) (by decide), q3, q7, q9,
        q 5 (by decide) (by decide) (by decide) (by decide),
        q 6 (by decide) (by decide) (by decide) (by decide), h5, h6]
      have : cw.toNat = 0 := by omega
      rw [this]; exact hTW
    have hfp : htabFootprint post tw.toNat = htabFootprint s tw.toNat := by
      simp only [htabFootprint, q 1 (by decide) (by decide) (by decide) (by decide),
        q 4 (by decide) (by decide) (by decide) (by decide),
        q 5 (by decide) (by decide) (by decide) (by decide),
        q 6 (by decide) (by decide) (by decide) (by decide),
        q 10 (by decide) (by decide) (by decide) (by decide)]
    refine ⟨?_, q 0 (by decide) (by decide) (by decide) (by decide),
      q 1 (by decide) (by decide) (by decide) (by decide)⟩
    refine exitR_memPost _ s post _ ⟨Lp, C, hpe⟩ hA hal hW' hfp ?_
    intro a ha
    obtain ⟨ha0, ha2, ha3⟩ := hframe a ha
    have hal' := a.isLt
    rdsimp [hMn, hMh]
    exact hMf a ha
  · exact False.elim (hrt hbranch)

end InitECandidate.Solver.Wave8HtabAstra.Htab
