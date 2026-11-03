import InitECandidate.Solver.Wave8GuestInv.ContractParts.C00Defs
import InitECandidate.Solver.Wave8GuestInv.R10Shards.SoloHtabSetFinal
import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.TruncateSpec

/-! `HtabValuesSub`: proves `htabValues` inclusion properties for `htab_set` and `htab_del`
(pre-`C00`, cycle-free for both `ContractParts/C00.lean` and `ContractParts/C08.lean`). -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

theorem evaluate_be_eq {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) :
    (evaluateHOLFiniteState s p).2.be = s.be := by
  have inv := evaluateInvariantsHOLFinite p
    (PanPropsEvalStateFiniteExact.ofPanSemFinite s)
    (evaluateHOLFiniteState s p).1
    (PanPropsEvalStateFiniteExact.ofPanSemFinite (evaluateHOLFiniteState s p).2)
    (by simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
          PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite])
  exact inv.2.2.1

/-! ## 1. `htabValues` inclusion for `htab_del` -/

section HtabDelValues

open InitECandidate.Solver.Wave8M19.Htab
open InitECandidate.Solver.Wave8GuestInv.HtabC00Ports (arg_to_light exit_from_light)

private theorem del_inner_values_sub {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (tw nd ow lw cw : BitVec 64)
    (M' : BitVec 64 → HolWordLab 64) (L I Fr : List Nat) (mvN : Nat)
    (hB : HtabBlocks s tw.toNat)
    (hT : TreeWF L I Fr (Wave8M19.hdr s tw.toNat 8) (Wave8M19.hdr s tw.toNat 0)
      (Wave8M19.hdr s tw.toNat 3) (Wave8M19.hdr s tw.toNat 7)
      (Wave8M19.hdr s tw.toNat 9) (Wave8M19.nodeF s (Wave8M19.hdr s tw.toNat 5))
      (fun i => Wave8M19.memW s (Wave8M19.hdr s tw.toNat 6 + 8 * i)))
    (h5 : Wave8M19.hdr s tw.toNat 5 = nd.toNat) (h6 : Wave8M19.hdr s tw.toNat 6 = ow.toNat)
    (hcw : cw.toNat + 1 = Wave8M19.hdr s tw.toNat 3)
    (hleaf : lw.toNat ∈ L) (hmvL : mvN ∈ L)
    (hMn : ∀ n off, n < Wave8M19.hdr s tw.toNat 10 + 1 → off < 32 →
      rdN M' (nd.toNat + 32 * n + off) =
        if n = mvN ∧ off = 16 then Wave8M19.nodeF s nd.toNat lw.toNat 16
        else rdN s.memory (nd.toNat + 32 * n + off))
    (hMo : ∀ i, i < cw.toNat →
      ∃ j < Wave8M19.hdr s tw.toNat 3,
        rdN M' (ow.toNat + 8 * i) = rdN s.memory (ow.toNat + 8 * j) ∧
        rdN s.memory (ow.toNat + 8 * j) ∈ L)
    (hMh : ∀ c, c < 88 → rdN M' (tw.toNat + c) = rdN s.memory (tw.toNat + c))
    (hpost : DelPostR s M' tw nd lw cw post) :
    ∀ x ∈ htabValues post tw.toNat, x ∈ htabValues s tw.toNat := by
  rw [h5, h6] at hT
  obtain ⟨hlen, hnodup, hmem, hcI, hordL, hint, hr0, hr1, hrc, hpar, ⟨dep, hdep⟩, hfc⟩ := id hT
  obtain ⟨hfpB, hdisj, hk1, hk60, hstr, hnc2, hnx1, hnx⟩ := id hB
  simp only [Wave8M19.htabFootprint, h5, h6] at hfpB hdisj
  have hfp0 := (hfpB (tw.toNat, 88) (by simp)).1
  have hfp2 := (hfpB (nd.toNat, (Wave8M19.hdr s tw.toNat 10 + 1) * 32) (by simp)).1
  have hfp3 := (hfpB (ow.toNat, (Wave8M19.hdr s tw.toNat 10 + 1) * 8) (by simp)).1
  simp only [Wave8M19.Inside] at hfp0 hfp2 hfp3
  have hhe : heapEnd < 2 ^ 64 := by decide
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Wave8M19.Disj] at hdisj
  have hdA := hdisj.1.2.1
  have hdB := hdisj.1.2.2
  have hdC := hdisj.2.2.1
  have hLIF : ∀ n ∈ L ++ I ++ Fr, 1 ≤ n ∧ n < Wave8M19.hdr s tw.toNat 10 + 1 := fun n hn => by
    have := (hmem n).1 hn; omega
  have hnd12 := List.nodup_append.mp hnodup
  have hndLI := List.nodup_append.mp hnd12.1
  have hLI : ∀ a ∈ L, a ∉ I := fun a ha hai => hndLI.2.2 a ha a hai rfl
  have mL : ∀ a ∈ L, a ∈ L ++ I ++ Fr := fun a ha => by simp [ha]
  have mI : ∀ a ∈ I, a ∈ L ++ I ++ Fr := fun a ha => by simp [ha]
  have mLI : ∀ a ∈ L ++ I, a ∈ L ++ I ++ Fr := fun a ha => List.mem_append_left _ ha
  have hlwB := hLIF _ (mL _ hleaf)
  have hmvB := hLIF _ (mL _ hmvL)
  have e5_rd : rdN s.memory (tw.toNat + 40) = nd.toNat := by
    rw [← memW_rdN]; exact h5
  have e6_rd : rdN s.memory (tw.toNat + 48) = ow.toNat := by
    rw [← memW_rdN]; exact h6
  have e7 : rdN s.memory (tw.toNat + 56) = Wave8M19.hdr s tw.toNat 7 := by
    rw [Wave8M19.hdr, memW_rdN]
  have hLlen : L.length ≤ Wave8M19.hdr s tw.toNat 8 - 1 :=
    nodup_len_le L _ hndLI.1 (fun x hx => (hmem x).1 (mL x hx))
  simp only [Wave8M19.nodeF, memW_rdN] at hMn
  have hpost_reads :
      hdr post tw.toNat 3 = cw.toNat ∧
      hdr post tw.toNat 5 = nd.toNat ∧
      hdr post tw.toNat 6 = ow.toNat ∧
      (∀ i < cw.toNat, memW post (ow.toNat + 8 * i) = rdN M' (ow.toNat + 8 * i)) ∧
      (∀ z ∈ L, nodeF post nd.toNat z 8 = rdN M' (nd.toNat + 32 * z + 8)) := by
    rcases hpost with ⟨_, Lp, Cp, hpe⟩ | ⟨hrt, Lp, Cp, hpe⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · change Wave8M19.memW post (tw.toNat + 8 * 3) = _; rw [memW_rdN, hpe, NS_memory]; rdsimp []
      · change Wave8M19.memW post (tw.toNat + 8 * 5) = _; rw [memW_rdN, hpe, NS_memory]; rdsimp [hMh, e5_rd]
      · change Wave8M19.memW post (tw.toNat + 8 * 6) = _; rw [memW_rdN, hpe, NS_memory]; rdsimp [hMh, e6_rd]
      · intro i hi
        have hiB : i < Wave8M19.hdr s tw.toNat 10 + 1 := by omega
        change Wave8M19.memW post (ow.toNat + 8 * i) = _; rw [memW_rdN, hpe, NS_memory]; rdsimp []
      · intro z hz
        have hzB := hLIF z (mL z hz)
        change Wave8M19.memW post (nd.toNat + 32 * z + 8) = _; rw [memW_rdN, hpe, NS_memory]; rdsimp []
    · have hnr : lw.toNat ≠ Wave8M19.hdr s tw.toNat 7 := by
        intro h; apply hrt; apply BitVec.eq_of_toNat_eq
        rdsimp [hMh, e7]; exact h.symm
      set nf := Wave8M19.nodeF s nd.toNat with hnf
      have hlwLI : lw.toNat ∈ L ++ I := List.mem_append_left _ hleaf
      have hpI := hpar _ hlwLI hnr
      have hpB := hLIF _ (mI _ hpI)
      obtain ⟨_, hp8, hp16, hp816, hp8p, hp16p⟩ := hint _ hpI
      have hc8B := hLIF _ (mLI _ hp8)
      have hc16B := hLIF _ (mLI _ hp16)
      have hcl := (hdep _ hlwLI hnr).1
      have hlp : lw.toNat ≠ nf lw.toNat 0 := fun h => hLI _ hleaf (h ▸ hpI)
      have hmvp : mvN ≠ nf lw.toNat 0 := fun h => hLI _ hmvL (h ▸ hpI)
      have hcnt1 : 0 < Wave8M19.hdr s tw.toNat 3 := by rw [← hlen]; exact List.length_pos_of_mem hleaf
      have hroot0 := (hr1 hcnt1).2
      have hgB : nf (nf lw.toNat 0) 0 = 0 ∨ nf (nf lw.toNat 0) 0 ∈ I := by
        by_cases hpr : nf lw.toNat 0 = Wave8M19.hdr s tw.toNat 7
        · left; rw [hpr]; exact hroot0
        · right; exact hpar _ (List.mem_append_right _ hpI) hpr
      have hgN : nf (nf lw.toNat 0) 0 < Wave8M19.hdr s tw.toNat 10 + 1 := by
        rcases hgB with h | h
        · omega
        · exact (hLIF _ (mI _ h)).2
      have hgp : nf (nf lw.toNat 0) 0 ≠ nf lw.toNat 0 := by
        by_cases hpr : nf lw.toNat 0 = Wave8M19.hdr s tw.toNat 7
        · rw [hpr, hroot0]; omega
        · intro h
          have := (hdep _ (List.mem_append_right _ hpI) hpr).2
          rw [h] at this; omega
      have hmvg : mvN ≠ nf (nf lw.toNat 0) 0 := by
        rcases hgB with h | h
        · rw [h]; omega
        · exact fun e => hLI _ hmvL (e ▸ h)
      have hc8p : nf (nf lw.toNat 0) 8 ≠ nf lw.toNat 0 := fun h => hgp (by rw [← h]; exact hp8p)
      have hc16p : nf (nf lw.toNat 0) 16 ≠ nf lw.toNat 0 := fun h => hgp (by rw [← h]; exact hp16p)
      rcases hp0 : s.memory (nd + lw * 32 + 0) with ⟨p0⟩
      have ep0 : nf lw.toNat 0 = p0.toNat := nodeF_of s nd lw p0 0 hp0
      simp only [ep0] at hpB hp816 hp8p hp16p hc8B hc16B hcl hlp hmvp hgN hgp hmvg hc8p hc16p hgB
      rcases hg0 : s.memory (nd + p0 * 32 + 0) with ⟨g0⟩
      have eg0 : nf p0.toNat 0 = g0.toNat := nodeF_of s nd p0 g0 0 hg0
      rcases hc8 : s.memory (nd + p0 * 32 + 8) with ⟨c8⟩
      have ec8 : nf p0.toNat 8 = c8.toNat := nodeF_of s nd p0 c8 8 hc8
      rcases hc16 : s.memory (nd + p0 * 32 + 16) with ⟨c16⟩
      have ec16 : nf p0.toNat 16 = c16.toNat := nodeF_of s nd p0 c16 16 hc16
      simp only [eg0, ec8, ec16] at hpB hp816 hp8p hp16p hc8B hc16B hcl hlp hmvp hgN hgp hmvg hc8p hc16p hgB
      rcases hg8 : s.memory (nd + g0 * 32 + 8) with ⟨g8⟩
      have eg8 : nf g0.toNat 8 = g8.toNat := nodeF_of s nd g0 g8 8 hg8
      rcases hfr : s.memory (tw + 72) with ⟨fr⟩
      have efr : Wave8M19.hdr s tw.toNat 9 = fr.toNat := hdr_of s tw fr 9 hfr
      have rp0 : rdN s.memory (nd.toNat + 32 * lw.toNat + 0) = p0.toNat := by rw [← memW_rdN]; exact ep0
      have rg0 : rdN s.memory (nd.toNat + 32 * p0.toNat + 0) = g0.toNat := by rw [← memW_rdN]; exact eg0
      have rc8 : rdN s.memory (nd.toNat + 32 * p0.toNat + 8) = c8.toNat := by rw [← memW_rdN]; exact ec8
      have rc16 : rdN s.memory (nd.toNat + 32 * p0.toNat + 16) = c16.toNat := by rw [← memW_rdN]; exact ec16
      have rg8 : rdN s.memory (nd.toNat + 32 * g0.toNat + 8) = g8.toNat := by rw [← memW_rdN]; exact eg8
      have rfr : rdN s.memory (tw.toNat + 72) = fr.toNat := by rw [← memW_rdN]; exact efr
      have esv : (if c8.toNat = lw.toNat then c16.toNat else c8.toNat) =
          (if c8 = lw then c16 else c8).toNat := by
        by_cases h : c8 = lw
        · rw [if_pos (congrArg BitVec.toNat h), if_pos h]
        · rw [if_neg (fun e => h (BitVec.eq_of_toNat_eq e)), if_neg h]
      generalize hsvd : (if c8 = lw then c16 else c8) = sv at esv
      have hsvB : 1 ≤ sv.toNat ∧ sv.toNat < Wave8M19.hdr s tw.toNat 10 + 1 ∧ sv.toNat ≠ p0.toNat ∧
          sv.toNat ≠ lw.toNat := by
        clear * - esv hc8B hc16B hp816 hcl hc8p hc16p
        rw [← esv]; split_ifs <;> omega
      have v1 : wv (updW M' (tw + 24) cw (nd + lw * 32 + 0)) = p0 := by
        clear * - hfp0 hfp2 hdA hhe hlwB hMn rp0
        apply BitVec.eq_of_toNat_eq; rdsimp [hMn, rp0]
      have v2 : wv (updW M' (tw + 24) cw (nd + p0 * 32 + 0)) = g0 := by
        clear * - hfp0 hfp2 hdA hhe hpB hMn rg0
        apply BitVec.eq_of_toNat_eq; rdsimp [hMn, rg0]
      have v3 : wv (updW M' (tw + 24) cw (nd + p0 * 32 + 8)) = c8 := by
        clear * - hfp0 hfp2 hdA hhe hpB hMn rc8
        apply BitVec.eq_of_toNat_eq; rdsimp [hMn, rc8]
      have v4 : wv (updW M' (tw + 24) cw (nd + p0 * 32 + 16)) = c16 := by
        clear * - hfp0 hfp2 hdA hhe hpB hmvp hMn rc16
        apply BitVec.eq_of_toNat_eq; rdsimp [hMn, rc16]
      rw [v1] at hpe
      simp only [delSib] at hpe
      rw [v2, v3, v4, hsvd] at hpe
      simp only [delSplice] at hpe
      have v5 : wv (updW (updW M' (tw + 24) cw) (nd + sv * 32 + 0) g0 (nd + g0 * 32 + 8)) = g8 := by
        clear * - hfp0 hfp2 hdA hhe hsvB hgN hmvg hMn rg8
        apply BitVec.eq_of_toNat_eq; rdsimp [hMn, rg8]
      rw [v5] at hpe
      have v6a : wv (updW (updW (updW M' (tw + 24) cw) (nd + sv * 32 + 0) g0) (tw + 56) sv (tw + 72)) = fr := by
        clear * - hfp0 hfp2 hdA hhe hsvB hgN hMh rfr
        apply BitVec.eq_of_toNat_eq; rdsimp [hMh, rfr]
      have v6b : wv (updW (updW (updW M' (tw + 24) cw) (nd + sv * 32 + 0) g0) (nd + g0 * 32 + 8) sv (tw + 72)) = fr := by
        clear * - hfp0 hfp2 hdA hhe hsvB hgN hMh rfr
        apply BitVec.eq_of_toNat_eq; rdsimp [hMh, rfr]
      have v6c : wv (updW (updW (updW M' (tw + 24) cw) (nd + sv * 32 + 0) g0) (nd + g0 * 32 + 16) sv (tw + 72)) = fr := by
        clear * - hfp0 hfp2 hdA hhe hsvB hgN hMh rfr
        apply BitVec.eq_of_toNat_eq; rdsimp [hMh, rfr]
      simp only [fn_ite_apply, wv_ite, v6a, v6b, v6c, ite_self] at hpe
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · change Wave8M19.memW post (tw.toNat + 8 * 3) = _
        rw [memW_rdN, hpe, NS_memory]
        by_cases hg : g0 = 0 <;> by_cases hl : g8 = p0 <;>
          simp only [hg, hl, if_true, if_false] <;> rdsimp []
      · change Wave8M19.memW post (tw.toNat + 8 * 5) = _
        rw [memW_rdN, hpe, NS_memory]
        by_cases hg : g0 = 0 <;> by_cases hl : g8 = p0 <;>
          simp only [hg, hl, if_true, if_false] <;> rdsimp [hMh, e5_rd]
      · change Wave8M19.memW post (tw.toNat + 8 * 6) = _
        rw [memW_rdN, hpe, NS_memory]
        by_cases hg : g0 = 0 <;> by_cases hl : g8 = p0 <;>
          simp only [hg, hl, if_true, if_false] <;> rdsimp [hMh, e6_rd]
      · intro i hi
        have hiB : i < Wave8M19.hdr s tw.toNat 10 + 1 := by omega
        change Wave8M19.memW post (ow.toNat + 8 * i) = _
        rw [memW_rdN, hpe, NS_memory]
        by_cases hg : g0 = 0 <;> by_cases hl : g8 = p0 <;>
          simp only [hg, hl, if_true, if_false] <;> rdsimp []
      · intro z hz
        have hzB := hLIF z (mL z hz)
        have hzg : z ≠ g0.toNat := by
          rcases hgB with h0 | hI
          · omega
          · exact fun e => hLI z hz (e ▸ hI)
        change Wave8M19.memW post (nd.toNat + 32 * z + 8) = _
        rw [memW_rdN, hpe, NS_memory]
        by_cases hg : g0 = 0 <;> by_cases hl : g8 = p0 <;>
          simp only [hg, hl, if_true, if_false] <;> rdsimp []
  obtain ⟨hh3_p, hh5_p, hh6_p, hord_p, hnd8_p⟩ := hpost_reads
  intro x hx
  unfold htabValues at hx ⊢
  rw [hh3_p, hh5_p, hh6_p] at hx
  obtain ⟨i, hi_mem, hxi⟩ := List.mem_map.mp hx
  have hi_lt : i < cw.toNat := List.mem_range.mp hi_mem
  dsimp only at hxi
  obtain ⟨j, hj_lt, hMo_ij, hj_L⟩ := hMo i hi_lt
  have hord_eq : memW post (ow.toNat + 8 * i) = memW s (ow.toNat + 8 * j) := by
    rw [hord_p i hi_lt, hMo_ij]
    change _ = Wave8M19.memW s (ow.toNat + 8 * j)
    rw [memW_rdN]
  set z := memW s (ow.toNat + 8 * j)
  have hz_L : z ∈ L := by
    change Wave8M19.memW s (ow.toNat + 8 * j) ∈ L
    rwa [memW_rdN]
  have hz_B := hLIF z (mL z hz_L)
  have hnd_eq : nodeF post nd.toNat z 8 = nodeF s nd.toNat z 8 := by
    rw [hnd8_p z hz_L, hMn z 8 hz_B.2 (by decide)]
    simp only [show ¬(z = mvN ∧ (8 : Nat) = 16) by omega, ↓reduceIte]
    change _ = Wave8M19.nodeF s nd.toNat z 8
    rw [Wave8M19.nodeF, memW_rdN]
  rw [← hxi, hord_eq, hnd_eq]
  change nodeF s (Wave8M19.hdr s tw.toNat 5) (memW s (Wave8M19.hdr s tw.toNat 6 + 8 * j)) 8 ∈ _
  rw [h5, h6]
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj_lt, rfl⟩

theorem htab_del_values_sub {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hP : HtabArgWF s)
    (v : ValueHOL 64)
    (hv : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_del)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_del)).2
    HtabExit s post ∧ post.be = s.be ∧
    ∀ x ∈ htabValues post (locN s "t"), x ∈ htabValues s (locN s "t") := by
  dsimp only
  have hbe : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_del)).2.be = s.be :=
    evaluate_be_eq s _
  have hExit : HtabExit s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_del)).2 := by
    rcases htab_del_spec_proof with ⟨ps, body, ret, hl, hrun⟩
    have hbody_eq : body = sourceFnBody Guest.Software.guestFn_htab_del := by
      have h1 : originalRuntimeCode.lookup (ofString "htab_del") =
          some (List.map FrontendCodecComputation.paramToHOLStructural (extractFn Guest.Software.guestFn_htab_del).params,
            sourceFnBody Guest.Software.guestFn_htab_del,
            FrontendCodecComputation.shapeToHOLStructural (extractFn Guest.Software.guestFn_htab_del).returnShape) :=
        lookup_of_guestAst_getElem 139 (by rw [guestAst_len]; decide)
          (extractFn Guest.Software.guestFn_htab_del) rfl
      rw [hl] at h1; injection h1 with h1; injection h1 with _ h2; injection h2 with hb _; exact hb
    subst hbody_eq
    have hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_del)).1 ≠ some .timeOut := by
      rw [hv]; simp
    exact exit_from_light s _ (hrun s hcode (arg_to_light s hP) hnt v hv) hP.1.2.2.2.2.2.2.2.2.2
  refine ⟨hExit, hbe, ?_⟩
  have hP' := arg_to_light s hP
  obtain ⟨hAR, hWF, hal⟩ := hP'
  have htpos : 0 < Wave8M19.locN s "t" := by
    have := (hWF.1 _ (List.mem_cons_self)).1.1
    simp only [Wave8M19.htabFootprint] at this
    have hsb : sourceBase = 2701131776 := rfl
    omega
  obtain ⟨tw, ht, htn⟩ : ∃ w : BitVec 64, s.locals.lookup (ofString "t") = some (.val (.word w)) ∧
      locN s "t" = w.toNat := by
    change 0 < locN s "t" at htpos
    unfold locN at htpos ⊢
    split at htpos
    · rename_i w hw; exact ⟨w, hw, rfl⟩
    · omega
  rw [htn]
  change Wave8M19.HtabWF s (locN s "t") at hWF
  rw [htn] at hWF
  obtain ⟨hB, L, I, Fr, hT⟩ := (htabWF_iff s _).1 hWF
  obtain ⟨hLlen, hnodup, hmemr, hcntI, hord, hint, hroot0, hroot1, _, hpar, _, _⟩ := id hT
  obtain ⟨hfp, hdisj, hk1, hk60, hst, hnc, hnx1, hnx⟩ := id hB
  rcases hk : s.memory (tw + 0) with ⟨k⟩
  rcases hnd : s.memory (tw + 40) with ⟨nd⟩
  rcases how : s.memory (tw + 48) with ⟨ow⟩
  rcases hcnt : s.memory (tw + 24) with ⟨cntw⟩
  rcases hrt : s.memory (tw + 56) with ⟨rt⟩
  have e0 : Wave8M19.hdr s tw.toNat 0 = k.toNat := hdr_of s tw k 0 hk
  have e3 : Wave8M19.hdr s tw.toNat 3 = cntw.toNat := hdr_of s tw cntw 3 hcnt
  have e5 : Wave8M19.hdr s tw.toNat 5 = nd.toNat := hdr_of s tw nd 5 hnd
  have e6 : Wave8M19.hdr s tw.toNat 6 = ow.toNat := hdr_of s tw ow 6 how
  have e7 : Wave8M19.hdr s tw.toNat 7 = rt.toNat := hdr_of s tw rt 7 hrt
  have hB0 := hB
  have hT0 := hT
  simp only [e0, e3, e5, e6, e7] at hLlen hcntI hord hint hroot0 hroot1 hpar hk1 hk60
  simp only [Wave8M19.htabFootprint, e5, e6] at hfp hdisj
  have hfp2 := (hfp (nd.toNat, (Wave8M19.hdr s tw.toNat 10 + 1) * 32) (by simp)).1
  have hfp3 := (hfp (ow.toNat, (Wave8M19.hdr s tw.toNat 10 + 1) * 8) (by simp)).1
  simp only [Wave8M19.Inside] at hfp2 hfp3
  have hhe : heapEnd < 2 ^ 64 := by decide
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, Wave8M19.Disj] at hdisj
  have hdA := hdisj.1.2.1
  have hdB := hdisj.1.2.2
  have hdC := hdisj.2.2.1
  have hfp0 := (hfp (tw.toNat, 88) (by simp)).1
  simp only [Wave8M19.Inside] at hfp0
  have hLIb : ∀ n ∈ L ++ I ++ Fr, 1 ≤ n ∧ n < Wave8M19.hdr s tw.toNat 10 + 1 := fun n hn => by
    have := (hmemr n).1 hn; omega
  have hres := (del_walk2 s hcode tw ht (0 :: (L ++ I))
    (fun u hu => by
      rw [hrt] at hu; simp only [HolWordLab.word.injEq] at hu; subst hu
      by_cases hc : cntw.toNat = 0
      · simp [hroot0 hc]
      · exact List.mem_cons_of_mem _ (hroot1 (by omega)).1)
    (fun nd' k' hnd' hk' w hwS hw0 hne => by
      rw [hnd] at hnd'; rw [hk] at hk'
      simp only [HolWordLab.word.injEq] at hnd' hk'; subst hnd' hk'
      have hwLI : w.toNat ∈ L ++ I := by
        rcases List.mem_cons.mp hwS with h | h
        · exact absurd (word_eq_zero_of_toNat h) hw0
        · exact h
      rcases List.mem_append.mp hwLI with hwL | hwI
      · exfalso
        obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hwL
        have := (hord i hi).2.1
        rw [hiw] at this
        apply hne
        have hmk : maxKeyLen = 60 := rfl
        have h8 : (k * 8).toNat = k.toNat * 8 := by rw [BitVec.toNat_mul]; simp; omega
        rw [h8]; unfold Wave8M19.nodeF at this; omega
      · obtain ⟨_, h8, h16, _⟩ := hint _ hwI
        unfold Wave8M19.nodeF at h8 h16
        exact ⟨List.mem_cons_of_mem _ h8, List.mem_cons_of_mem _ h16⟩)
    nd ow cntw hnd how hcnt).run v hv
  rcases hres with heq | ⟨lw, pw, mv, hlwS, hlw0, hcrit, hpw, hmv0, hcase⟩
  · intro x hx
    have hmem_eq : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_del)).2.memory = s.memory :=
      congrArg PanSemStateFiniteExact.memory heq
    have hveq : htabValues (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_del)).2 tw.toNat =
        htabValues s tw.toNat := by
      simp [htabValues, hdr, nodeF, memW, hmem_eq]
    rwa [← hveq]
  · have hlwLI : lw.toNat ∈ L ++ I := by
      rcases List.mem_cons.mp hlwS with h | h
      · exact absurd (word_eq_zero_of_toNat h) hlw0
      · exact h
    have hleaf : lw.toNat ∈ L := by
      rcases List.mem_append.mp hlwLI with h | h
      · exact h
      · exfalso
        have hc := hcrit nd k hnd hk
        have h24 := (hint _ h).1
        have hmk : maxKeyLen = 60 := rfl
        have h8 : (k * 8).toNat = k.toNat * 8 := by rw [BitVec.toNat_mul]; simp; omega
        rw [h8] at hc; unfold Wave8M19.nodeF at h24; omega
    have hL0 : 0 < L.length := List.length_pos_of_mem hleaf
    have hlwB := hLIb lw.toNat (by simp [hleaf])
    obtain ⟨i0, hi0, hli0⟩ := List.getElem_of_mem hleaf
    have hpos : Wave8M19.nodeF s nd.toNat lw.toNat 16 = i0 := by rw [← hli0]; exact (hord i0 hi0).2.2
    have hpw' : pw.toNat = i0 := by rw [← hpos]; exact (nodeF_of s nd lw pw 16 hpw).symm
    have hlast := hord (L.length - 1) (by omega)
    set mvN := L[L.length - 1]'(by omega) with hmvN
    have hmvL : mvN ∈ L := List.getElem_mem _
    have hmvB := hLIb mvN (by simp [hmvL])
    have hcw1 : (cntw - 1).toNat = cntw.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
    have hcw : (cntw - 1).toNat + 1 = Wave8M19.hdr s tw.toNat 3 := by rw [e3, hcw1]; omega
    have hmv' : mv.toNat = mvN := by
      have h1 := hlast.1
      have haddr : ow + (cntw - 1) * 8 = BitVec.ofNat 64 (ow.toNat + 8 * (L.length - 1)) := by
        rw [ao8, hcw1, hLlen]
      rw [haddr] at hmv0; unfold Wave8M19.memW at h1; rw [hmv0] at h1; exact h1
    rcases hcase with ⟨heq_p, hpost⟩ | ⟨hne_p, hpost⟩
    · have hi0' : i0 = L.length - 1 := by
        have := congrArg BitVec.toNat heq_p; rw [hcw1] at this; omega
      have hmvlw : mvN = lw.toNat := by rw [hmvN, ← hli0]; simp only [hi0']
      refine del_inner_values_sub s _ tw nd ow lw (cntw - 1) s.memory L I Fr mvN hB0 hT0 e5 e6 hcw hleaf hmvL ?_ ?_ (fun _ _ => rfl) hpost
      · intro n off _ _
        split_ifs with h
        · rw [h.1, h.2, hmvlw, ← memW_rdN]; rfl
        · rfl
      · intro i hi
        have hiL : i < L.length := by omega
        refine ⟨i, by rw [e3]; omega, rfl, ?_⟩
        rw [← memW_rdN, (hord i hiL).1]; exact List.getElem_mem hiL
    · have hpwB : pw.toNat < Wave8M19.hdr s tw.toNat 10 + 1 := by omega
      have hmvB' : mv.toNat < Wave8M19.hdr s tw.toNat 10 + 1 := by omega
      have hposR : rdN s.memory (nd.toNat + 32 * lw.toNat + 16) = pw.toNat := by
        rw [← memW_rdN, hpw']; exact hpos
      refine del_inner_values_sub s _ tw nd ow lw (cntw - 1) _ L I Fr mvN hB0 hT0 e5 e6 hcw hleaf hmvL ?_ ?_ ?_ hpost
      · intro n off hn hoff
        simp only [Wave8M19.nodeF, memW_rdN]
        rdsimp [hposR]
        split_ifs <;> omega
      · intro i hi
        have hiB : i < Wave8M19.hdr s tw.toNat 10 + 1 := by omega
        by_cases hip : i = pw.toNat
        · refine ⟨L.length - 1, by rw [e3]; omega, ?_, ?_⟩
          · have h1 := hlast.1
            rw [← memW_rdN, h1, ← hmv']
            rdsimp [hip]
          · rw [← memW_rdN, hlast.1]; exact List.getElem_mem _
        · have hiL : i < L.length := by omega
          refine ⟨i, by rw [e3]; omega, ?_, ?_⟩
          · rdsimp []
          · rw [← memW_rdN, (hord i hiL).1]; exact List.getElem_mem hiL
      · intro c hc
        rdsimp []

end HtabDelValues
end InitECandidate.Solver.Wave8GuestInv.R16Shards
