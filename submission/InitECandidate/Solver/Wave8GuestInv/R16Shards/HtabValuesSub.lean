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

/-! ## 2. `htabValues` inclusion for `htab_set` -/

section HtabSetValues

open InitECandidate.Solver.Wave8GuestInv.SoloHtabSet

private theorem locFree_valuesSub {F : Type} (s0 : PanSemStateFiniteExact 64 F) (t val : Nat) :
    LocFreePost (fun (_ : ValueHOL 64) (post : PanSemStateFiniteExact 64 F) =>
      ∀ x ∈ htabValues post t, x = val ∨ x ∈ htabValues s0 t) := by
  intro _ post L' h x hx
  exact h x hx

private theorem set_branch_empty_values {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F)
    (tw keyw valw : BitVec 64)
    (hs_fr : LocFrame s0 s)
    (hA0 : ArenaReady s0)
    (hW0 : HtabWF s0 tw.toNat)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i)
    (hcnt0 : hdr s0 tw.toNat 3 = 0)
    (ht_s : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hkey_s : s.locals.lookup (ofString "key") = some (.val (.word keyw)))
    (hval_s : s.locals.lookup (ofString "value") = some (.val (.word valw))) :
    Ret s
      (.decCall (ofString "nl") .one (ofString "htab_new_leaf")
        [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")]
        (.seq
          (.store (.op .add [.var .local (ofString "t"), .const 56#64]) (.var .local (ofString "nl")))
          (.return (.const 0#64))))
      (fun _ post => ∀ x ∈ htabValues post tw.toNat, x = valw.toNat ∨ x ∈ htabValues s0 tw.toNat) := by
  set t := tw.toNat
  have hLF := locFree_valuesSub s0 t valw.toNat
  have hmem_s : s.memory = s0.memory := hs_fr.memory
  obtain ⟨hB0, L0, I0, Fr0, hT0⟩ := (htabWF_iff s0 t).mp hW0
  have hL0_nil : L0 = [] := List.eq_nil_of_length_eq_zero (hT0.1.trans hcnt0)
  have hI0_nil : I0 = [] := by
    rcases hT0.2.2.2.1 with ⟨_, hI⟩ | hlen
    · exact hI
    · omega
  subst hL0_nil hI0_nil
  have hNS_s : NodeState s t [] Fr0 := by
    have hNS0 : NodeState s0 t [] Fr0 :=
      ⟨hB0, by simpa using hT0.2.1, by simpa using hT0.2.2.1, hT0.2.2.2.2.2.2.2.2.2.2.2⟩
    unfold LocFrame at hs_fr; rw [hs_fr]; exact hNS0
  have hA_s : ArenaReady s := by unfold LocFrame at hs_fr; rw [hs_fr]; exact (arenaReady_locals s0 _ _).mpr hA0
  have hal_s : ∀ i ∈ htabFootprint s t, Allocated s i := by
    unfold LocFrame at hs_fr; rw [hs_fr]; exact hal0
  have hh3_s : hdr s t 3 = 0 := by unfold hdr memW; rw [hmem_s]; exact hcnt0
  have hcnt_s : hdr s t 3 ≤ ([] : List Nat).length := by omega
  refine Ret.decCall_new_leaf_lf hLF tw keyw valw [] Fr0
    (by simp [evalAt, evalHOLExact, ht_s])
    (by simp [evalAt, evalHOLExact, hkey_s])
    (by simp [evalAt, evalHOLExact, hval_s])
    hA_s hNS_s hcnt_s hal_s ?_
  intro nlw Fr1 s1 _ hNS1 _ _ hh3_1 _ _ n8_1 _ _ ordc_1 _ _ _ _ _ _ hloc_1
  obtain ⟨hB1, _, hmem1, _⟩ := hNS1
  obtain ⟨hnc1_lt, _, _, _, ht_lo, ht_hi, _⟩ := htabBlocks_bounds hB1
  have hhe : heapEnd = 33806089704 := rfl
  let L_nl := s.locals.update (ofString "nl", .val (.word nlw))
  have ht_nl : L_nl.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [L_nl, HolFiniteMapExact.lookup_update, FUPDATE, ht_s, show ofString "nl" ≠ ofString "t" by decide]
  have hnl_lk : L_nl.lookup (ofString "nl") = some (.val (.word nlw)) := by
    simp [L_nl, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_nl_eq : setVarHOLFinite (ofString "nl") (.val (.word nlw)) s1 = NS s1 L_nl s1.globals s1.memory s1.clock := by
    simp [setVarHOLFinite, NS, hloc_1, L_nl]
  rw [hs1_nl_eq]
  refine Ret.ns_storeW (tw + 56#64) nlw
    (by
      have h560 : 56#64 + (0 : BitVec 64) = 56#64 := rfl
      simp only [NS_locals, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
        ht_nl, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
        valueIsWord, valueWord, wordOpHOL, wordOp, h560])
    (by simp [evalAt, evalHOLExact, hnl_lk]) ?_
  intro _
  apply Ret.ns_ret; intro _ _
  let s_end := NS s1 HolFiniteMapExact.empty s1.globals (updW s1.memory (tw + 56#64) nlw) s1.clock
  have htw56_eq : BitVec.ofNat 64 (t + 8 * 7) = tw + 56#64 := ofNat_add_toNat tw 56
  have hne_hdr : ∀ k < 11, k ≠ 7 → BitVec.ofNat 64 (t + 8 * k) ≠ tw + 56#64 := by
    intro k hk hne; rw [← htw56_eq]; exact ofNat64_ne_of_ne_of_lt (by omega) (by omega) (by omega)
  have hsep1 := htabBlocks_cell_sep hB1
  have hh3_end : hdr s_end t 3 = 1 := by
    have h1 : hdr s_end t 3 = hdr s1 t 3 := memW_updW_other s1 _ _ _ (hne_hdr 3 (by omega) (by omega))
    omega
  have hh5_end : hdr s_end t 5 = hdr s1 t 5 := memW_updW_other s1 _ _ _ (hne_hdr 5 (by omega) (by omega))
  have hh6_end : hdr s_end t 6 = hdr s1 t 6 := memW_updW_other s1 _ _ _ (hne_hdr 6 (by omega) (by omega))
  have hnl_rng : 1 ≤ nlw.toNat ∧ nlw.toNat < hdr s1 t 8 :=
    (hmem1 nlw.toNat).mp (List.mem_append_left _ (by simp))
  have hnl_lt_nc1 : nlw.toNat < hdr s1 t 10 + 1 := by have := hB1.2.2.2.2.2.2.2; omega
  have h0_lt_nc1 : 0 < hdr s1 t 10 + 1 := by omega
  have hord0_end : memW s_end (hdr s_end t 6 + 8 * 0) = nlw.toNat := by
    rw [hh6_end]
    have h1 : memW s_end (hdr s1 t 6 + 8 * 0) = memW s1 (hdr s1 t 6 + 8 * 0) := by
      apply memW_updW_other s1; rw [← htw56_eq]; exact (hsep1.2.1 7 (by omega) 0 h0_lt_nc1).symm
    have h2 : memW s1 (hdr s1 t 6 + 8 * 0) = nlw.toNat := by
      have hc0 : hdr s tw.toNat 3 = 0 := hh3_s
      rw [hc0] at ordc_1; exact ordc_1
    exact h1.trans h2
  have hn8_end : nodeF s_end (hdr s_end t 5) nlw.toNat 8 = valw.toNat := by
    rw [hh5_end]
    have h1 : nodeF s_end (hdr s1 t 5) nlw.toNat 8 = nodeF s1 (hdr s1 t 5) nlw.toNat 8 := by
      unfold nodeF; apply memW_updW_other s1; rw [← htw56_eq]
      exact (hsep1.1 7 (by omega) nlw.toNat hnl_lt_nc1 8 (Or.inr (Or.inl rfl))).symm
    exact h1.trans n8_1
  intro x hx
  unfold htabValues at hx
  change x ∈ List.map (fun i => nodeF s_end (hdr s_end t 5) (memW s_end (hdr s_end t 6 + 8 * i)) 8)
    (List.range (hdr s_end t 3)) at hx
  rw [hh3_end] at hx
  simp only [List.range_one, List.map_cons, List.map_nil, List.mem_singleton] at hx
  left
  rw [hx, hord0_end, hn8_end]

private theorem set_branch_overwrite_values {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F)
    (tw leafw valw : BitVec 64)
    (hs_fr : LocFrame s0 s)
    (hA0 : ArenaReady s0)
    (hW0 : HtabWF s0 tw.toNat)
    (hleaf_mem : ∀ L I Fr, TreeWF L I Fr (hdr s0 tw.toNat 8) (hdr s0 tw.toNat 0) (hdr s0 tw.toNat 3)
      (hdr s0 tw.toNat 7) (hdr s0 tw.toNat 9) (nodeF s0 (hdr s0 tw.toNat 5))
      (fun i => memW s0 (hdr s0 tw.toNat 6 + 8 * i)) → leafw.toNat ∈ L)
    (ht_s : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hleaf_s : s.locals.lookup (ofString "leaf") = some (.val (.word leafw)))
    (hval_s : s.locals.lookup (ofString "value") = some (.val (.word valw))) :
    Ret s
      (.seq
        (.store (.op .add [
            .load .one (.op .add [.var .local (ofString "t"), .const 40#64]),
            .panop .mul [.var .local (ofString "leaf"), .const 32#64],
            .const 8#64])
          (.var .local (ofString "value")))
        (.return (.const 0#64)))
      (fun _ post => ∀ x ∈ htabValues post tw.toNat, x = valw.toNat ∨ x ∈ htabValues s0 tw.toNat) := by
  set t := tw.toNat
  have hmem_s : s.memory = s0.memory := hs_fr.memory
  have hma_s : s.memaddrs = s0.memaddrs := by unfold LocFrame at hs_fr; rw [hs_fr]
  obtain ⟨hB0, L0, I0, Fr0, hT0⟩ := (htabWF_iff s0 t).mp hW0
  have hleaf_L0 : leafw.toNat ∈ L0 := hleaf_mem L0 I0 Fr0 hT0
  have hleaf_rng := (hT0.2.2.1 leafw.toNat).mp (List.mem_append_left _ (List.mem_append_left _ hleaf_L0))
  have hleaf_lt_nc0 : leafw.toNat < hdr s0 t 10 + 1 := by have := hB0.2.2.2.2.2.2.2; omega
  obtain ⟨hnc0_lt, _, _, _, ht_lo, ht_hi, _⟩ := htabBlocks_bounds hB0
  have hhe : heapEnd = 33806089704 := rfl
  obtain ⟨hdom0_t5, hm0_t5⟩ := word_of_hdr s0 tw 5 (by omega) hB0
  set ndw := BitVec.ofNat 64 (hdr s0 t 5)
  have hndw_nat : ndw.toNat = hdr s0 t 5 := by
    have hnd0_in := (hB0.1 (hdr s0 t 5, (hdr s0 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hnd0_in; rw [BitVec.toNat_ofNat]; omega
  have hed : evalAt s (.op .add [
      .load .one (.op .add [.var .local (ofString "t"), .const 40#64]),
      .panop .mul [.var .local (ofString "leaf"), .const 32#64],
      .const 8#64]) =
      some (.val (.word (ndw + leafw * 32#64 + 8#64))) := by
    have hdom40 : s.memaddrs (tw + 40#64) := by rw [hma_s]; exact hdom0_t5
    have hm40 : s.memory (tw + 40#64) = .word ndw := by rw [hmem_s]; exact hm0_t5
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
      ht_s, hleaf_s, isWfShapeExactHOL, memLoadHOLExact,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL]
    have h400 : 40#64 + (0 : BitVec 64) = 40#64 := rfl
    rw [h400]
    simp only [hdom40, hm40, ↓reduceIte, List.all, List.map, Bool.and_self, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    have hz : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
    rw [hz, BitVec.add_assoc]
  have hs_ns : s = NS s0 s.locals s0.globals s0.memory s.clock := hs_fr
  rw [hs_ns]
  refine Ret.ns_storeW (ndw + leafw * 32#64 + 8#64) valw
    (by rw [← hs_ns]; exact hed)
    (by simp [evalAt, evalHOLExact, hval_s]) ?_
  intro _
  apply Ret.ns_ret; intro _ _
  set addr := ndw + leafw * 32#64 + 8#64
  have haddr_eq : addr = BitVec.ofNat 64 (hdr s0 t 5 + 32 * leafw.toNat + 8) := by
    dsimp [addr]; rw [← hndw_nat]; exact (ofNat_node_addr ndw leafw 8).symm
  let s_end := NS s0 HolFiniteMapExact.empty s0.globals (updW s0.memory addr valw) s.clock
  have hsep0 := htabBlocks_cell_sep hB0
  have hne_hdr : ∀ k < 11, BitVec.ofNat 64 (t + 8 * k) ≠ addr := by
    intro k hk; rw [haddr_eq]; exact hsep0.1 k hk leafw.toNat hleaf_lt_nc0 8 (Or.inr (Or.inl rfl))
  have hh3_end : hdr s_end t 3 = hdr s0 t 3 := memW_updW_other s0 _ _ _ (hne_hdr 3 (by omega))
  have hh5_end : hdr s_end t 5 = hdr s0 t 5 := memW_updW_other s0 _ _ _ (hne_hdr 5 (by omega))
  have hh6_end : hdr s_end t 6 = hdr s0 t 6 := memW_updW_other s0 _ _ _ (hne_hdr 6 (by omega))
  have hnd_L0_I0 : (L0 ++ I0).Nodup := (List.nodup_append.mp hT0.2.1).1
  have hLlen : L0.length ≤ hdr s0 t 10 := by
    have hle := nodup_len_le_range (List.nodup_append.mp hnd_L0_I0).1
      (fun x hx => (hT0.2.2.1 x).mp (List.mem_append_left _ (List.mem_append_left _ hx)))
    have := hB0.2.2.2.2.2.2.2; omega
  intro x hx
  unfold htabValues at hx
  change x ∈ List.map (fun i => nodeF s_end (hdr s_end t 5) (memW s_end (hdr s_end t 6 + 8 * i)) 8)
    (List.range (hdr s_end t 3)) at hx
  rw [hh3_end, hh5_end, hh6_end] at hx
  obtain ⟨i, hi_mem, hxi⟩ := List.mem_map.mp hx
  have hi_lt : i < hdr s0 t 3 := List.mem_range.mp hi_mem
  have hi_L0 : i < L0.length := by rw [hT0.1]; exact hi_lt
  have hord_i : memW s_end (hdr s0 t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i) := by
    apply memW_updW_other s0; rw [haddr_eq]
    exact hsep0.2.2.1 leafw.toNat hleaf_lt_nc0 8 (Or.inr (Or.inl rfl)) i (by omega)
  dsimp only at hxi
  rw [hord_i] at hxi
  set z := memW s0 (hdr s0 t 6 + 8 * i)
  have hz_eq : z = L0[i] := (hT0.2.2.2.2.1 i hi_L0).1
  have hz_L0 : z ∈ L0 := by rw [hz_eq]; exact List.getElem_mem hi_L0
  have hz_rng := (hT0.2.2.1 z).mp (List.mem_append_left _ (List.mem_append_left _ hz_L0))
  have hz_lt_nc0 : z < hdr s0 t 10 + 1 := by have := hB0.2.2.2.2.2.2.2; omega
  by_cases hzl : z = leafw.toNat
  · left
    rw [← hxi, hzl]
    change memW s_end (hdr s0 t 5 + 32 * leafw.toNat + 8) = valw.toNat
    unfold memW
    rw [← haddr_eq]
    simp [s_end, NS_memory, updW]
  · right
    have hnd_z : nodeF s_end (hdr s0 t 5) z 8 = nodeF s0 (hdr s0 t 5) z 8 := by
      unfold nodeF; apply memW_updW_other s0; rw [haddr_eq]
      exact hsep0.2.2.2.1 z hz_lt_nc0 8 (Or.inr (Or.inl rfl)) leafw.toNat hleaf_lt_nc0 8 (Or.inr (Or.inl rfl)) (Or.inl hzl)
    rw [← hxi, hnd_z]
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi_lt, rfl⟩

private theorem set_splice_values {F : Type}
    (s0 s2 : PanSemStateFiniteExact 64 F)
    (tw dw pw nw nlw niw valw : BitVec 64)
    (L0 I0 Fr0 Fr2 : List Nat)
    (L_cur : HolFiniteMapExact MlS (ValueHOL 64))
    (ht_cur : L_cur.lookup (ofString "t") = some (.val (.word tw)))
    (hp_cur : L_cur.lookup (ofString "p") = some (.val (.word pw)))
    (hn_cur : L_cur.lookup (ofString "n") = some (.val (.word nw)))
    (hnl_cur : L_cur.lookup (ofString "nl") = some (.val (.word nlw)))
    (hni_cur : L_cur.lookup (ofString "ni") = some (.val (.word niw)))
    (hA2 : ArenaReady s2)
    (hNS2 : NodeState s2 tw.toNat (((L0 ++ I0) ++ [nlw.toNat]) ++ [niw.toNat]) Fr2)
    (hT0 : TreeWF L0 I0 Fr0
      (hdr s0 tw.toNat 8) (hdr s0 tw.toNat 0) (hdr s0 tw.toNat 3) (hdr s0 tw.toNat 7) (hdr s0 tw.toNat 9)
      (nodeF s0 (hdr s0 tw.toNat 5)) (fun i => memW s0 (hdr s0 tw.toNat 6 + 8 * i)))
    (hnw_LI : nw.toNat ∈ L0 ++ I0)
    (hpw_spec : (pw.toNat = 0 ∧ nw.toNat = hdr s0 tw.toNat 7) ∨
      (pw.toNat ∈ I0 ∧ nw.toNat ≠ hdr s0 tw.toNat 7 ∧ pw.toNat = nodeF s0 (hdr s0 tw.toNat 5) nw.toNat 0))
    (hh3_2 : hdr s2 tw.toNat 3 = hdr s0 tw.toNat 3 + 1)
    (hnl_8_2 : nodeF s2 (hdr s2 tw.toNat 5) nlw.toNat 8 = valw.toNat)
    (hord_cnt_2 : memW s2 (hdr s2 tw.toNat 6 + 8 * hdr s0 tw.toNat 3) = nlw.toNat)
    (hord_old_2 : ∀ i, i < hdr s0 tw.toNat 3 →
      memW s2 (hdr s2 tw.toNat 6 + 8 * i) = memW s0 (hdr s0 tw.toNat 6 + 8 * i))
    (hnd_old_2 : ∀ z ∈ L0 ++ I0, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF s2 (hdr s2 tw.toNat 5) z off = nodeF s0 (hdr s0 tw.toNat 5) z off) :
    Ret (NS s2 L_cur s2.globals s2.memory s2.clock)
      (.seq
        (.assign .local (ofString "nodes") (.load .one (.op .add [.var .local (ofString "t"), .const 40#64])))
        (.seq
          (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "ni"), .const 32#64], .const 0#64]) (.var .local (ofString "p")))
          (.seq
            (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "nl"), .const 32#64], .const 0#64]) (.var .local (ofString "ni")))
            (.seq
              (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "n"), .const 32#64], .const 0#64]) (.var .local (ofString "ni")))
              (.seq
                (.ite (.cmp .equal (.op .and [.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"), .shift .lsr (.var .local (ofString "d")) (.const 3#64)])) (.op .sub [.const 7#64, .op .and [.var .local (ofString "d"), .const 7#64]]), .const 1#64]) (.const 0#64))
                  (.seq
                    (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "ni"), .const 32#64], .const 8#64]) (.var .local (ofString "nl")))
                    (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "ni"), .const 32#64], .const 16#64]) (.var .local (ofString "n"))))
                  (.seq
                    (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "ni"), .const 32#64], .const 8#64]) (.var .local (ofString "n")))
                    (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "ni"), .const 32#64], .const 16#64]) (.var .local (ofString "nl")))))
                (.seq
                  (.ite (.cmp .equal (.var .local (ofString "p")) (.const 0#64))
                    (.store (.op .add [.var .local (ofString "t"), .const 56#64]) (.var .local (ofString "ni")))
                    (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "p"), .const 32#64], .const 8#64])) (.var .local (ofString "n")))
                      (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "p"), .const 32#64], .const 8#64]) (.var .local (ofString "ni")))
                      (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "p"), .const 32#64], .const 16#64]) (.var .local (ofString "ni")))))
                  (.return (.const 0#64))))))))
      (fun _ post => ∀ x ∈ htabValues post tw.toNat, x = valw.toNat ∨ x ∈ htabValues s0 tw.toNat) := by
  set t := tw.toNat
  have hB2 := hNS2.1
  have hnodup2 := hNS2.2.1
  have hmem2 := hNS2.2.2.1
  obtain ⟨hnc2_lt, _, _, _, ht_lo, ht_hi, _⟩ := htabBlocks_bounds hB2
  have hhe : heapEnd = 33806089704 := rfl
  obtain ⟨hdom2_t5, hm2_t5⟩ := word_of_hdr s2 tw 5 (by omega) hB2
  set ndw := BitVec.ofNat 64 (hdr s2 t 5)
  have hndw_nat : ndw.toNat = hdr s2 t 5 := by
    have hnd2_in := (hB2.1 (hdr s2 t 5, (hdr s2 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hnd2_in; rw [BitVec.toNat_ofNat]; omega
  have hsep2 := htabBlocks_cell_sep hB2
  have haddr_nd : ∀ (xw : BitVec 64) (off : Nat),
      ndw + xw * 32#64 + BitVec.ofNat 64 off = BitVec.ofNat 64 (hdr s2 t 5 + 32 * xw.toNat + off) := by
    intro xw off; rw [← hndw_nat]; exact (ofNat_node_addr ndw xw off).symm
  have hnd_all := (List.nodup_append.mp hnodup2).1
  have hnd_A1 := (List.nodup_append.mp hnd_all).1
  have hLI_lt_nc2 : ∀ z ∈ L0 ++ I0, z < hdr s2 t 10 + 1 := by
    intro z hz
    have := (hmem2 z).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hz)))
    omega
  have hni_lt_nc2 : niw.toNat < hdr s2 t 10 + 1 := by
    have := (hmem2 niw.toNat).mp (List.mem_append_left _ (List.mem_append_right _ (by simp))); omega
  have hnl_lt_nc2 : nlw.toNat < hdr s2 t 10 + 1 := by
    have := (hmem2 nlw.toNat).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))); omega
  have hnw_lt_nc2 : nw.toNat < hdr s2 t 10 + 1 := hLI_lt_nc2 nw.toNat hnw_LI
  have hnl_ne_ni : nlw.toNat ≠ niw.toNat := fun h =>
    (List.nodup_append.mp hnd_all).2.2 niw.toNat (List.mem_append_right _ (by simp [h])) niw.toNat (by simp) rfl
  have hLI_ne_ni : ∀ z ∈ L0 ++ I0, z ≠ niw.toNat := fun z hz h =>
    (List.nodup_append.mp hnd_all).2.2 niw.toNat (List.mem_append_left _ (h ▸ hz)) niw.toNat (by simp) rfl
  have hLI_ne_nl : ∀ z ∈ L0 ++ I0, z ≠ nlw.toNat := fun z hz h =>
    (List.nodup_append.mp hnd_A1).2.2 nlw.toNat (h ▸ hz) nlw.toNat (by simp) rfl
  have hnd_L0_I0 := (List.nodup_append.mp hT0.2.1).1
  have hL0_not_I0 : ∀ z ∈ L0, z ∉ I0 := fun z hz hI =>
    (List.nodup_append.mp hnd_L0_I0).2.2 z hz z hI rfl
  -- Prove the pure memory property for `m_final` once, just like `htab_set_splice_memory_wf`!
  have splice_mem_values : ∀ (ch_left : Bool) (m_final : BitVec 64 → HolWordLab 64),
      let m3 := updW (updW (updW s2.memory (ndw + niw * 32#64 + 0#64) pw)
                  (ndw + nlw * 32#64 + 0#64) niw) (ndw + nw * 32#64 + 0#64) niw
      let m5 := if ch_left then
                  updW (updW m3 (ndw + niw * 32#64 + 8#64) nlw) (ndw + niw * 32#64 + 16#64) nw
                else
                  updW (updW m3 (ndw + niw * 32#64 + 8#64) nw) (ndw + niw * 32#64 + 16#64) nlw
      m_final = (if pw.toNat = 0 then
                  updW m5 (tw + 56#64) niw
                else if nodeF s0 (hdr s0 t 5) pw.toNat 8 = nw.toNat then
                  updW m5 (ndw + pw * 32#64 + 8#64) niw
                else
                  updW m5 (ndw + pw * 32#64 + 16#64) niw) →
      let s_end := NS s2 HolFiniteMapExact.empty s2.globals m_final s2.clock
      ∀ x ∈ htabValues s_end t, x = valw.toNat ∨ x ∈ htabValues s0 t := by
    intro ch_left m_final m3 m5 hm_eq s_end
    have htw56_eq : tw + 56#64 = BitVec.ofNat 64 (t + 8 * 7) := (ofNat_add_toNat tw 56).symm
    have hm5_hdr : ∀ k < 11, m5 (BitVec.ofNat 64 (t + 8 * k)) = s2.memory (BitVec.ofNat 64 (t + 8 * k)) := by
      intro k hk
      have h1 := hsep2.1 k hk niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl)))
      have h2 := hsep2.1 k hk niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl))
      have h3 := hsep2.1 k hk nw.toNat hnw_lt_nc2 0 (Or.inl rfl)
      have h4 := hsep2.1 k hk nlw.toNat hnl_lt_nc2 0 (Or.inl rfl)
      have h5 := hsep2.1 k hk niw.toNat hni_lt_nc2 0 (Or.inl rfl)
      rw [← haddr_nd] at h1 h2 h3 h4 h5
      cases ch_left <;> simp only [m5, m3, updW, Bool.false_eq_true, ↓reduceIte, h1, h2, h3, h4, h5]
    have hm5_ord : ∀ i < hdr s2 t 10 + 1, m5 (BitVec.ofNat 64 (hdr s2 t 6 + 8 * i)) = s2.memory (BitVec.ofNat 64 (hdr s2 t 6 + 8 * i)) := by
      intro i hi
      have h1 := hsep2.2.2.1 niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) i hi
      have h2 := hsep2.2.2.1 niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl)) i hi
      have h3 := hsep2.2.2.1 nw.toNat hnw_lt_nc2 0 (Or.inl rfl) i hi
      have h4 := hsep2.2.2.1 nlw.toNat hnl_lt_nc2 0 (Or.inl rfl) i hi
      have h5 := hsep2.2.2.1 niw.toNat hni_lt_nc2 0 (Or.inl rfl) i hi
      rw [← haddr_nd] at h1 h2 h3 h4 h5
      cases ch_left <;> simp only [m5, m3, updW, Bool.false_eq_true, ↓reduceIte, h1, h2, h3, h4, h5]
    have hp_lt_nc2 : pw.toNat ≠ 0 → pw.toNat < hdr s2 t 10 + 1 := by
      intro hpz
      rcases hpw_spec with ⟨h0, _⟩ | ⟨hpI, _, _⟩
      · exact absurd h0 hpz
      · exact hLI_lt_nc2 pw.toNat (List.mem_append_right _ hpI)
    have hdr_end_other : ∀ k < 11, k ≠ 7 → hdr s_end t k = hdr s2 t k := by
      intro k hk hk7
      unfold hdr memW
      simp only [s_end, NS_memory, hm_eq]
      by_cases hpz : pw.toNat = 0
      · have hne7 : BitVec.ofNat 64 (t + 8 * k) ≠ tw + 56#64 := by
          rw [htw56_eq]; exact ofNat64_ne_of_ne_of_lt (by omega) (by omega) (by omega)
        simp only [hpz, ↓reduceIte, updW, hne7, hm5_hdr k hk]
      · simp only [hpz, ↓reduceIte]
        have hp_lt := hp_lt_nc2 hpz
        have hne8 : BitVec.ofNat 64 (t + 8 * k) ≠ ndw + pw * 32#64 + 8#64 := by
          rw [haddr_nd]; exact hsep2.1 k hk pw.toNat hp_lt 8 (Or.inr (Or.inl rfl))
        have hne16 : BitVec.ofNat 64 (t + 8 * k) ≠ ndw + pw * 32#64 + 16#64 := by
          rw [haddr_nd]; exact hsep2.1 k hk pw.toNat hp_lt 16 (Or.inr (Or.inr (Or.inl rfl)))
        split <;> simp only [updW, hne8, hne16, ↓reduceIte, hm5_hdr k hk]
    have hh3_end : hdr s_end t 3 = hdr s0 t 3 + 1 := (hdr_end_other 3 (by omega) (by omega)).trans hh3_2
    have hh5_end : hdr s_end t 5 = hdr s2 t 5 := hdr_end_other 5 (by omega) (by omega)
    have hh6_end : hdr s_end t 6 = hdr s2 t 6 := hdr_end_other 6 (by omega) (by omega)
    have hord_end : ∀ i < hdr s2 t 10 + 1, memW s_end (hdr s2 t 6 + 8 * i) = memW s2 (hdr s2 t 6 + 8 * i) := by
      intro i hi
      unfold memW
      simp only [s_end, NS_memory, hm_eq]
      by_cases hpz : pw.toNat = 0
      · have hne7 : BitVec.ofNat 64 (hdr s2 t 6 + 8 * i) ≠ tw + 56#64 := by
          rw [htw56_eq]; exact (hsep2.2.1 7 (by omega) i hi).symm
        simp only [hpz, ↓reduceIte, updW, hne7, hm5_ord i hi]
      · simp only [hpz, ↓reduceIte]
        have hp_lt := hp_lt_nc2 hpz
        have hne8 : BitVec.ofNat 64 (hdr s2 t 6 + 8 * i) ≠ ndw + pw * 32#64 + 8#64 := by
          rw [haddr_nd]; exact hsep2.2.2.1 pw.toNat hp_lt 8 (Or.inr (Or.inl rfl)) i hi
        have hne16 : BitVec.ofNat 64 (hdr s2 t 6 + 8 * i) ≠ ndw + pw * 32#64 + 16#64 := by
          rw [haddr_nd]; exact hsep2.2.2.1 pw.toNat hp_lt 16 (Or.inr (Or.inr (Or.inl rfl))) i hi
        split <;> simp only [updW, hne8, hne16, ↓reduceIte, hm5_ord i hi]
    -- Any leaf `z` (`z < ncap2 + 1`, `z ≠ niw.toNat`, `z ≠ pw.toNat`) has `nodeF s_end (hdr s2 t 5) z 8 = nodeF s2 (hdr s2 t 5) z 8`:
    have hnd8_end_keep : ∀ z < hdr s2 t 10 + 1, z ≠ niw.toNat → (pw.toNat ≠ 0 → z ≠ pw.toNat) →
        nodeF s_end (hdr s2 t 5) z 8 = nodeF s2 (hdr s2 t 5) z 8 := by
      intro z hz hzni hzp
      unfold nodeF memW
      simp only [s_end, NS_memory, hm_eq]
      have hm5_z8 : m5 (BitVec.ofNat 64 (hdr s2 t 5 + 32 * z + 8)) = s2.memory (BitVec.ofNat 64 (hdr s2 t 5 + 32 * z + 8)) := by
        have h1 := hsep2.2.2.2.1 z hz 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inl hzni)
        have h2 := hsep2.2.2.2.1 z hz 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl)) (Or.inl hzni)
        have h3 := hsep2.2.2.2.1 z hz 8 (Or.inr (Or.inl rfl)) nw.toNat hnw_lt_nc2 0 (Or.inl rfl) (Or.inr (by omega))
        have h4 := hsep2.2.2.2.1 z hz 8 (Or.inr (Or.inl rfl)) nlw.toNat hnl_lt_nc2 0 (Or.inl rfl) (Or.inr (by omega))
        have h5 := hsep2.2.2.2.1 z hz 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc2 0 (Or.inl rfl) (Or.inl hzni)
        rw [← haddr_nd] at h1 h2 h3 h4 h5
        cases ch_left <;> simp only [m5, m3, updW, Bool.false_eq_true, ↓reduceIte, h1, h2, h3, h4, h5]
      by_cases hpz : pw.toNat = 0
      · have hne7 : BitVec.ofNat 64 (hdr s2 t 5 + 32 * z + 8) ≠ tw + 56#64 := by
          rw [htw56_eq]; exact (hsep2.1 7 (by omega) z hz 8 (Or.inr (Or.inl rfl))).symm
        simp only [hpz, ↓reduceIte, updW, hne7, hm5_z8]
      · simp only [hpz, ↓reduceIte]
        have hp_lt := hp_lt_nc2 hpz
        have hne8 : BitVec.ofNat 64 (hdr s2 t 5 + 32 * z + 8) ≠ ndw + pw * 32#64 + 8#64 := by
          rw [haddr_nd]; exact hsep2.2.2.2.1 z hz 8 (Or.inr (Or.inl rfl)) pw.toNat hp_lt 8 (Or.inr (Or.inl rfl)) (Or.inl (hzp hpz))
        have hne16 : BitVec.ofNat 64 (hdr s2 t 5 + 32 * z + 8) ≠ ndw + pw * 32#64 + 16#64 := by
          rw [haddr_nd]; exact hsep2.2.2.2.1 z hz 8 (Or.inr (Or.inl rfl)) pw.toNat hp_lt 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inl (hzp hpz))
        split <;> simp only [updW, hne8, hne16, ↓reduceIte, hm5_z8]
    have hcnt_lt_nc2 : hdr s0 t 3 < hdr s2 t 10 + 1 := by
      have hnx2_le : hdr s2 t 8 ≤ hdr s2 t 10 + 1 := hB2.2.2.2.2.2.2.2
      have hr2 : ∀ y ∈ ((L0 ++ I0) ++ [nlw.toNat]) ++ [niw.toNat], 1 ≤ y ∧ y < hdr s2 t 8 := fun y hy =>
        (hmem2 y).mp (List.mem_append_left _ hy)
      have hlen_le := nodup_len_le_range hnd_all hr2
      have hL0_len : L0.length = hdr s0 t 3 := hT0.1
      have hni_rng := hr2 niw.toNat (List.mem_append_right _ (by simp))
      simp only [List.length_append, List.length_singleton] at hlen_le
      omega
    intro x hx
    unfold htabValues at hx
    change x ∈ List.map (fun i => nodeF s_end (hdr s_end t 5) (memW s_end (hdr s_end t 6 + 8 * i)) 8)
      (List.range (hdr s_end t 3)) at hx
    rw [hh3_end, hh5_end, hh6_end] at hx
    obtain ⟨i, hi_mem, hxi⟩ := List.mem_map.mp hx
    have hi_lt : i < hdr s0 t 3 + 1 := List.mem_range.mp hi_mem
    dsimp only at hxi
    by_cases hi_eq : i = hdr s0 t 3
    · left
      subst hi_eq
      rw [hord_end (hdr s0 t 3) hcnt_lt_nc2, hord_cnt_2] at hxi
      have hnl_ne_p : pw.toNat ≠ 0 → nlw.toNat ≠ pw.toNat := by
        intro hpz
        rcases hpw_spec with ⟨h0, _⟩ | ⟨hpI, _, _⟩
        · exact absurd h0 hpz
        · exact fun h => hLI_ne_nl pw.toNat (List.mem_append_right _ hpI) h.symm
      rw [← hxi, hnd8_end_keep nlw.toNat hnl_lt_nc2 hnl_ne_ni hnl_ne_p, hnl_8_2]
    · right
      have hi_old : i < hdr s0 t 3 := by omega
      have hi_L0 : i < L0.length := by rw [hT0.1]; exact hi_old
      rw [hord_end i (lt_trans hi_old hcnt_lt_nc2), hord_old_2 i hi_old] at hxi
      set z := memW s0 (hdr s0 t 6 + 8 * i)
      have hz_eq : z = L0[i] := (hT0.2.2.2.2.1 i hi_L0).1
      have hz_L0 : z ∈ L0 := by rw [hz_eq]; exact List.getElem_mem hi_L0
      have hz_LI : z ∈ L0 ++ I0 := List.mem_append_left _ hz_L0
      have hz_ne_p : pw.toNat ≠ 0 → z ≠ pw.toNat := by
        intro hpz
        rcases hpw_spec with ⟨h0, _⟩ | ⟨hpI, _, _⟩
        · exact absurd h0 hpz
        · exact fun h => hL0_not_I0 z hz_L0 (h ▸ hpI)
      rw [← hxi, hnd8_end_keep z (hLI_lt_nc2 z hz_LI) (hLI_ne_ni z hz_LI) hz_ne_p,
          hnd_old_2 z hz_LI 8 (Or.inr (Or.inl rfl))]
      exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi_old, rfl⟩
  -- Execute the splice AST identically to `htab_set_splice_exec`:
  have hev_nd : evalAt (NS s2 L_cur s2.globals s2.memory s2.clock)
      (.load .one (.op .add [.var .local (ofString "t"), .const 40#64])) =
      some (.val (.word ndw)) :=
    eval_field_load_word _ tw 40#64 ndw ht_cur hdom2_t5 hm2_t5
  refine Ret.ns_assign ndw hev_nd ?_
  let L_nd := L_cur.update (ofString "nodes", .val (.word ndw))
  have hl_nd : L_nd.lookup (ofString "nodes") = some (.val (.word ndw)) := by
    simp [L_nd, HolFiniteMapExact.lookup_update, FUPDATE]
  have hl_t : L_nd.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [L_nd, HolFiniteMapExact.lookup_update, FUPDATE, ht_cur, show ofString "nodes" ≠ ofString "t" by decide]
  have hl_p : L_nd.lookup (ofString "p") = some (.val (.word pw)) := by
    simp [L_nd, HolFiniteMapExact.lookup_update, FUPDATE, hp_cur, show ofString "nodes" ≠ ofString "p" by decide]
  have hl_n : L_nd.lookup (ofString "n") = some (.val (.word nw)) := by
    simp [L_nd, HolFiniteMapExact.lookup_update, FUPDATE, hn_cur, show ofString "nodes" ≠ ofString "n" by decide]
  have hl_nl : L_nd.lookup (ofString "nl") = some (.val (.word nlw)) := by
    simp [L_nd, HolFiniteMapExact.lookup_update, FUPDATE, hnl_cur, show ofString "nodes" ≠ ofString "nl" by decide]
  have hl_ni : L_nd.lookup (ofString "ni") = some (.val (.word niw)) := by
    simp [L_nd, HolFiniteMapExact.lookup_update, FUPDATE, hni_cur, show ofString "nodes" ≠ ofString "ni" by decide]
  refine Ret.ns_storeW (ndw + niw * 32#64 + 0#64) pw
    (eval_node_field_expr _ (ofString "ni") ndw niw 0 hl_nd hl_ni)
    (by simp [evalAt, evalHOLExact]; exact hl_p) ?_
  intro _
  refine Ret.ns_storeW (ndw + nlw * 32#64 + 0#64) niw
    (eval_node_field_expr _ (ofString "nl") ndw nlw 0 hl_nd hl_nl)
    (by simp [evalAt, evalHOLExact]; exact hl_ni) ?_
  intro _
  refine Ret.ns_storeW (ndw + nw * 32#64 + 0#64) niw
    (eval_node_field_expr _ (ofString "n") ndw nw 0 hl_nd hl_n)
    (by simp [evalAt, evalHOLExact]; exact hl_ni) ?_
  intro _
  set m3 := updW (updW (updW s2.memory
              (ndw + niw * 32#64 + 0#64) pw)
              (ndw + nlw * 32#64 + 0#64) niw)
              (ndw + nw * 32#64 + 0#64) niw
  have exec_parent_link : ∀ (ch_left : Bool) (m5_val : BitVec 64 → HolWordLab 64),
      m5_val = (if ch_left then
                  updW (updW m3 (ndw + niw * 32#64 + 8#64) nlw) (ndw + niw * 32#64 + 16#64) nw
                else
                  updW (updW m3 (ndw + niw * 32#64 + 8#64) nw) (ndw + niw * 32#64 + 16#64) nlw) →
      Ret (NS s2 L_nd s2.globals m5_val s2.clock)
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "p")) (.const 0#64))
            (.store (.op .add [.var .local (ofString "t"), .const 56#64]) (.var .local (ofString "ni")))
            (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "p"), .const 32#64], .const 8#64])) (.var .local (ofString "n")))
              (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "p"), .const 32#64], .const 8#64]) (.var .local (ofString "ni")))
              (.store (.op .add [.var .local (ofString "nodes"), .panop .mul [.var .local (ofString "p"), .const 32#64], .const 16#64]) (.var .local (ofString "ni")))))
          (.return (.const 0#64)))
        (fun _ post => ∀ x ∈ htabValues post t, x = valw.toNat ∨ x ∈ htabValues s0 t) := by
    intro ch_left m5_val hm5_eq
    apply Ret.seq_ite
    intro cwp hcwp
    have hcwp_spec : (cwp ≠ 0 → pw.toNat = 0) ∧ (cwp = 0 → pw.toNat ≠ 0) := by
      obtain ⟨va, vb, hva, hvb, hcw_eq⟩ := evalAt_cmp _ .equal _ _ cwp hcwp
      simp only [NS_locals, evalAt, evalHOLExact, hl_p, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hva hvb
      subst hva hvb
      have hz0 : (0#64 : BitVec 64).toNat = 0 := rfl
      constructor
      · intro hnz; by_contra hne
        have hp_ne : pw ≠ 0#64 := fun h => hne (by rw [h]; exact hz0)
        simp [Compiler.Encoders.Asm.wordCmpHOL, hp_ne] at hcw_eq
        exact hnz hcw_eq
      · intro hz hp0
        have hp_eq : pw = 0#64 := BitVec.eq_of_toNat_eq (by rw [hp0, hz0])
        simp [Compiler.Encoders.Asm.wordCmpHOL, hp_eq] at hcw_eq
        rw [hz] at hcw_eq; exact absurd hcw_eq (by decide)
    refine ⟨fun hcwp_nz => ?_, fun hcwp_z => ?_⟩
    · have hpz := hcwp_spec.1 hcwp_nz
      refine Ret.ns_storeW (tw + 56#64) niw
        (by
          have h560 : 56#64 + (0 : BitVec 64) = 56#64 := rfl
          simp only [NS_locals, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
            hl_t, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
            valueIsWord, valueWord, wordOpHOL, wordOp, h560])
        (by simp [evalAt, evalHOLExact]; exact hl_ni) ?_
      intro _
      apply Ret.ns_ret; intro _ _
      exact splice_mem_values ch_left (updW m5_val (tw + 56#64) niw)
        (by dsimp only; rw [if_pos hpz, hm5_eq])
    · have hpnz := hcwp_spec.2 hcwp_z
      have hpI : pw.toNat ∈ I0 := by
        rcases hpw_spec with ⟨h0, _⟩ | ⟨hI, _, _⟩
        · exact absurd h0 hpnz
        · exact hI
      have hpLI : pw.toNat ∈ L0 ++ I0 := List.mem_append_right _ hpI
      have hp_lt_nc2 := hLI_lt_nc2 pw.toNat hpLI
      have hp_ne_ni := hLI_ne_ni pw.toNat hpLI
      obtain ⟨_, hm2_p8⟩ := word_of_node s2 tw ndw pw 8 hndw_nat.symm hp_lt_nc2 (Or.inr (Or.inl rfl)) hB2
      have hm5_p8 : m5_val (ndw + pw * 32#64 + 8#64) = .word (BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) pw.toNat 8)) := by
        have h1 := hsep2.2.2.2.1 pw.toNat hp_lt_nc2 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inl hp_ne_ni)
        have h2 := hsep2.2.2.2.1 pw.toNat hp_lt_nc2 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl)) (Or.inl hp_ne_ni)
        have h3 := hsep2.2.2.2.1 pw.toNat hp_lt_nc2 8 (Or.inr (Or.inl rfl)) nw.toNat hnw_lt_nc2 0 (Or.inl rfl) (Or.inr (by omega))
        have h4 := hsep2.2.2.2.1 pw.toNat hp_lt_nc2 8 (Or.inr (Or.inl rfl)) nlw.toNat hnl_lt_nc2 0 (Or.inl rfl) (Or.inr (by omega))
        have h5 := hsep2.2.2.2.1 pw.toNat hp_lt_nc2 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc2 0 (Or.inl rfl) (Or.inl hp_ne_ni)
        rw [hm5_eq]
        have hm5_s2 : (if ch_left = true then updW (updW m3 (ndw + niw * 32#64 + 8#64) nlw) (ndw + niw * 32#64 + 16#64) nw
            else updW (updW m3 (ndw + niw * 32#64 + 8#64) nw) (ndw + niw * 32#64 + 16#64) nlw) (ndw + pw * 32#64 + 8#64) =
            s2.memory (ndw + pw * 32#64 + 8#64) := by
          cases ch_left <;> simp only [m3, updW, Bool.false_eq_true, ↓reduceIte,
            haddr_nd pw 8, haddr_nd niw 16, haddr_nd niw 8, haddr_nd nw 0, haddr_nd nlw 0, haddr_nd niw 0,
            h1, h2, h3, h4, h5]
        rw [hm5_s2]
        have hm2_p8' : s2.memory (ndw + pw * 32#64 + 8#64) = .word (BitVec.ofNat 64 (nodeF s2 (hdr s2 t 5) pw.toNat 8)) := by
          rw [← hndw_nat]; exact hm2_p8
        rw [hm2_p8', hnd_old_2 pw.toNat hpLI 8 (Or.inr (Or.inl rfl))]
      have hp8_lt_264 : nodeF s0 (hdr s0 t 5) pw.toNat 8 < 2 ^ 64 := by
        unfold nodeF memW; rcases s0.memory _ with ⟨w⟩; exact w.isLt
      apply Ret.seq_ite
      intro cw8 hcw8
      have hcw8_spec : (cw8 ≠ 0 → nodeF s0 (hdr s0 t 5) pw.toNat 8 = nw.toNat) ∧
          (cw8 = 0 → nodeF s0 (hdr s0 t 5) pw.toNat 8 ≠ nw.toNat) := by
        obtain ⟨va, vb, hva, hvb, hcw_eq⟩ := evalAt_cmp _ .equal _ _ cw8 hcw8
        obtain ⟨_, hva_mem⟩ := ev_var_node_load (NS s2 L_nd s2.globals m5_val s2.clock) (ofString "p") ndw pw 8#64 hl_nd hl_p (.val (.word va)) hva
        have hm5_p8' : m5_val (ndw + pw * 32 + 8#64) = .word (BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) pw.toNat 8)) := hm5_p8
        simp only [NS_memory, hm5_p8', ValueHOL.val.injEq, HolWordLab.word.injEq] at hva_mem
        subst hva_mem
        simp only [NS_locals, evalAt, evalHOLExact, hl_n, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hvb
        subst hvb
        have hva_nat : (BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) pw.toNat 8)).toNat = nodeF s0 (hdr s0 t 5) pw.toNat 8 := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp8_lt_264]
        constructor
        · intro hnz; by_contra hne
          have hbne : BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) pw.toNat 8) ≠ nw := fun h =>
            hne (by have := congrArg BitVec.toNat h; rw [hva_nat] at this; exact this)
          simp [Compiler.Encoders.Asm.wordCmpHOL, hbne] at hcw_eq
          exact hnz hcw_eq
        · intro hz heq
          have hbeq : BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) pw.toNat 8) = nw :=
            BitVec.eq_of_toNat_eq (by rw [hva_nat, heq])
          simp [Compiler.Encoders.Asm.wordCmpHOL, hbeq] at hcw_eq
          rw [hz] at hcw_eq; exact absurd hcw_eq (by decide)
      refine ⟨fun hcw8_nz => ?_, fun hcw8_z => ?_⟩
      · have hp8_eq := hcw8_spec.1 hcw8_nz
        refine Ret.ns_storeW (ndw + pw * 32#64 + 8#64) niw
          (eval_node_field_expr _ (ofString "p") ndw pw 8 hl_nd hl_p)
          (by simp [evalAt, evalHOLExact]; exact hl_ni) ?_
        intro _
        apply Ret.ns_ret; intro _ _
        exact splice_mem_values ch_left (updW m5_val (ndw + pw * 32#64 + 8#64) niw)
          (by dsimp only; rw [if_neg hpnz, if_pos hp8_eq, hm5_eq])
      · have hp8_ne := hcw8_spec.2 hcw8_z
        refine Ret.ns_storeW (ndw + pw * 32#64 + 16#64) niw
          (eval_node_field_expr _ (ofString "p") ndw pw 16 hl_nd hl_p)
          (by simp [evalAt, evalHOLExact]; exact hl_ni) ?_
        intro _
        apply Ret.ns_ret; intro _ _
        exact splice_mem_values ch_left (updW m5_val (ndw + pw * 32#64 + 16#64) niw)
          (by dsimp only; rw [if_neg hpnz, if_neg hp8_ne, hm5_eq])
  apply Ret.seq_ite
  intro cw_bit _
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · refine Ret.ns_seq_storeW2
      (ndw + niw * 32#64 + 8#64) nlw
      (ndw + niw * 32#64 + 16#64) nw
      (eval_node_field_expr _ (ofString "ni") ndw niw 8 hl_nd hl_ni)
      (by simp [evalAt, evalHOLExact]; exact hl_nl)
      (eval_node_field_expr _ (ofString "ni") ndw niw 16 hl_nd hl_ni)
      (by simp [evalAt, evalHOLExact]; exact hl_n) ?_
    intro _ _
    exact exec_parent_link true _ rfl
  · refine Ret.ns_seq_storeW2
      (ndw + niw * 32#64 + 8#64) nw
      (ndw + niw * 32#64 + 16#64) nlw
      (eval_node_field_expr _ (ofString "ni") ndw niw 8 hl_nd hl_ni)
      (by simp [evalAt, evalHOLExact]; exact hl_n)
      (eval_node_field_expr _ (ofString "ni") ndw niw 16 hl_nd hl_ni)
      (by simp [evalAt, evalHOLExact]; exact hl_nl) ?_
    intro _ _
    exact exec_parent_link false _ rfl

private theorem htab_set_body_values {F : Type}
    (s0 : PanSemStateFiniteExact 64 F)
    (tw keyw valw : BitVec 64)
    (ht0 : s0.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hkey0 : s0.locals.lookup (ofString "key") = some (.val (.word keyw)))
    (hval0 : s0.locals.lookup (ofString "value") = some (.val (.word valw)))
    (hA0 : ArenaReady s0)
    (hW0 : HtabWF s0 tw.toNat)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i) :
    Ret s0 (sourceFnBody Guest.Software.guestFn_htab_set)
      (fun _ post => ∀ x ∈ htabValues post tw.toNat, x = valw.toNat ∨ x ∈ htabValues s0 tw.toNat) := by
  set t := tw.toNat
  have hLF := locFree_valuesSub s0 t valw.toNat
  obtain ⟨hB0, L0, I0, Fr0, hT0⟩ := (htabWF_iff s0 t).mp hW0
  obtain ⟨hnc0_lt, hst0_ge8, hst0_le64, hst0_al, ht_lo, ht_hi, ht_al⟩ := htabBlocks_bounds hB0
  have hnx0_le : hdr s0 t 8 ≤ hdr s0 t 10 + 1 := hB0.2.2.2.2.2.2.2
  have hklen_le60 : hdr s0 t 0 ≤ 60 := hB0.2.2.2.1
  have hklen_le_st : hdr s0 t 0 ≤ hdr s0 t 1 := by have := hB0.2.2.2.2.1; omega
  have hhe : heapEnd = 33806089704 := rfl
  obtain ⟨_, hm0_t0⟩ := word_of_hdr s0 tw 0 (by omega) hB0
  obtain ⟨_, hm0_t1⟩ := word_of_hdr s0 tw 1 (by omega) hB0
  obtain ⟨_, hm0_t4⟩ := word_of_hdr s0 tw 4 (by omega) hB0
  obtain ⟨_, hm0_t5⟩ := word_of_hdr s0 tw 5 (by omega) hB0
  obtain ⟨_, hm0_t7⟩ := word_of_hdr s0 tw 7 (by omega) hB0
  set klenw := BitVec.ofNat 64 (hdr s0 t 0)
  set stridew := BitVec.ofNat 64 (hdr s0 t 1)
  set keysw := BitVec.ofNat 64 (hdr s0 t 4)
  set nodesw0 := BitVec.ofNat 64 (hdr s0 t 5)
  set rootw0 := BitVec.ofNat 64 (hdr s0 t 7)
  have hklenw_nat : klenw.toNat = hdr s0 t 0 := by rw [BitVec.toNat_ofNat]; omega
  have hstridew_nat : stridew.toNat = hdr s0 t 1 := by rw [BitVec.toNat_ofNat]; omega
  have hkeysw_nat : keysw.toNat = hdr s0 t 4 := by
    have hk_in := (hB0.1 (hdr s0 t 4, (hdr s0 t 10 + 1) * hdr s0 t 1) (by simp [htabFootprint])).1
    unfold Inside at hk_in; rw [BitVec.toNat_ofNat]; omega
  have hnodesw0_nat : nodesw0.toNat = hdr s0 t 5 := by
    have hn_in := (hB0.1 (hdr s0 t 5, (hdr s0 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hn_in; rw [BitVec.toNat_ofNat]; omega
  htab_unfold Guest.Software.guestFn_htab_set
  apply Ret.dec_lf hLF; intro vkl hvkl
  obtain ⟨_, rfl⟩ := ev_field_load s0 (ofString "t") tw 0#64 ht0 vkl hvkl
  have hm0 : s0.memory (tw + 0#64) = .word klenw := hm0_t0
  rw [hm0]
  apply Ret.dec_lf hLF; intro vst hvst
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 8#64
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht0, show ofString "klen" ≠ ofString "t" by decide]) vst hvst
  have hm8 : (setVarHOLFinite (ofString "klen") (.val (.word klenw)) s0).memory (tw + 8#64) = .word stridew := hm0_t1
  rw [hm8]
  let s_fl_pre := setVarHOLFinite (ofString "stride") (.val (.word stridew))
    (setVarHOLFinite (ofString "klen") (.val (.word klenw)) s0)
  have ht_fl_pre : s_fl_pre.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht0,
      show ofString "stride" ≠ ofString "t" by decide, show ofString "klen" ≠ ofString "t" by decide]
  have hkey_fl_pre : s_fl_pre.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
    simp [s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkey0,
      show ofString "stride" ≠ ofString "key" by decide, show ofString "klen" ≠ ofString "key" by decide]
  refine Ret.decCall2_lf hLF hA0.1.code (by decide) lookup_htab_find_leaf tw keyw
    (by simp [evalAt, evalHOLExact]; exact ht_fl_pre)
    (by simp [evalAt, evalHOLExact]; exact hkey_fl_pre) ?_
  intro leafw post_fl hrun_fl
  let entry_fl := callEntryStateHOLFinite s_fl_pre
    ((HolFiniteMapExact.empty.update (ofString "t", .val (.word tw))).update (ofString "key", .val (.word keyw)))
  have hW_entry_fl : HtabWF entry_fl t := (htabWF_locals s0 _ _ t).mpr hW0
  have hfl_spec := find_leaf_spec_wf entry_fl tw
    (by simp [entry_fl, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "key" ≠ ofString "t" by decide])
    hW_entry_fl (.val (.word leafw)) (by rw [hrun_fl])
  rw [hrun_fl] at hfl_spec
  obtain ⟨lw', hlw_eq, hfr_fl, hleaf_cases⟩ := hfl_spec
  dsimp only at hfr_fl
  injection hlw_eq with h1; injection h1 with h2; subst h2
  have hs_lf_fr : LocFrame s0 (setVarHOLFinite (ofString "leaf") (.val (.word leafw)) { post_fl with locals := s_fl_pre.locals }) := by
    unfold LocFrame at hfr_fl ⊢; dsimp [setVarHOLFinite]; rw [hfr_fl]; rfl
  apply Ret.dec_lf hLF; intro vks hvks
  obtain ⟨_, hvks_eq⟩ := ev_field_load _ (ofString "t") tw 32#64
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "leaf" ≠ ofString "t" by decide]; exact ht_fl_pre) vks hvks
  have hm32_lf : (setVarHOLFinite (ofString "leaf") (.val (.word leafw)) { post_fl with locals := s_fl_pre.locals }).memory (tw + 32#64) = .word keysw := by
    rw [hs_lf_fr.memory]; exact hm0_t4
  rw [hm32_lf] at hvks_eq; subst hvks_eq
  let s_k := setVarHOLFinite (ofString "keys") (.val (.word keysw))
    (setVarHOLFinite (ofString "leaf") (.val (.word leafw)) { post_fl with locals := s_fl_pre.locals })
  have hs_k_fr : LocFrame s0 s_k := hs_lf_fr.setVar _ _
  have hcode_sk : s_k.code = originalRuntimeCode := by unfold LocFrame at hs_k_fr; rw [hs_k_fr]; exact hA0.1.code
  have ht_sk : s_k.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [s_k, s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht0,
      show ofString "keys" ≠ ofString "t" by decide, show ofString "leaf" ≠ ofString "t" by decide,
      show ofString "stride" ≠ ofString "t" by decide, show ofString "klen" ≠ ofString "t" by decide]
  have hkey_sk : s_k.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
    simp [s_k, s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkey0,
      show ofString "keys" ≠ ofString "key" by decide, show ofString "leaf" ≠ ofString "key" by decide,
      show ofString "stride" ≠ ofString "key" by decide, show ofString "klen" ≠ ofString "key" by decide]
  have hval_sk : s_k.locals.lookup (ofString "value") = some (.val (.word valw)) := by
    simp [s_k, s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hval0,
      show ofString "keys" ≠ ofString "value" by decide, show ofString "leaf" ≠ ofString "value" by decide,
      show ofString "stride" ≠ ofString "value" by decide, show ofString "klen" ≠ ofString "value" by decide]
  have hleaf_sk : s_k.locals.lookup (ofString "leaf") = some (.val (.word leafw)) := by
    simp [s_k, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "keys" ≠ ofString "leaf" by decide]
  have hkeys_sk : s_k.locals.lookup (ofString "keys") = some (.val (.word keysw)) := by
    simp [s_k, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hkl_sk : s_k.locals.lookup (ofString "klen") = some (.val (.word klenw)) := by
    simp [s_k, s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "keys" ≠ ofString "klen" by decide, show ofString "leaf" ≠ ofString "klen" by decide,
      show ofString "stride" ≠ ofString "klen" by decide]
  have hst_sk : s_k.locals.lookup (ofString "stride") = some (.val (.word stridew)) := by
    simp [s_k, s_fl_pre, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "keys" ≠ ofString "stride" by decide, show ofString "leaf" ≠ ofString "stride" by decide]
  refine Ret.ite_ret
    (fun _ => by
      rw [evaluateHOLFiniteState_decCall_total]
      split
      · simp
      · split
        · simp
        · split
          · simp
          · dsimp only
            rw [fixClockHOLFinite_evaluateState]
            rcases evaluateHOLFiniteState _ _ with ⟨r, _⟩
            cases r with
            | none => simp
            | some r =>
              cases r with
              | returned _ =>
                dsimp only; split
                · exact noFlow_seq_right fun _ => noFlow_ret
                · simp
              | _ => simp)
    ?_
  intro cw_lf hcw_lf
  have hcw_lf_spec : (cw_lf ≠ 0 → leafw = 0) ∧ (cw_lf = 0 → leafw ≠ 0) := by
    obtain ⟨va, vb, hva, hvb, hcw_eq⟩ := evalAt_cmp s_k .equal _ _ cw_lf hcw_lf
    simp [evalAt, evalHOLExact, hleaf_sk] at hva hvb
    subst hva hvb
    constructor
    · intro hnz; by_contra hne
      have hne' : leafw ≠ 0#64 := hne
      simp [Compiler.Encoders.Asm.wordCmpHOL, hne'] at hcw_eq
      exact hnz hcw_eq
    · intro hz heq
      have heq' : leafw = 0#64 := heq
      simp [Compiler.Encoders.Asm.wordCmpHOL, heq'] at hcw_eq
      rw [hz] at hcw_eq; exact absurd hcw_eq (by decide)
  refine ⟨fun hcw_nz => ?_, fun hcw_z => ?_⟩
  · have hlf0 := hcw_lf_spec.1 hcw_nz
    have hcnt0 : hdr s0 t 3 = 0 := by
      rcases hleaf_cases with ⟨_, hc⟩ | ⟨hnz, _⟩
      · exact hc
      · exact absurd hlf0 hnz
    exact set_branch_empty_values s0 s_k tw keyw valw hs_k_fr hA0 hW0 hal0 hcnt0 ht_sk hkey_sk hval_sk
  · have hlf_nz := hcw_lf_spec.2 hcw_z
    obtain ⟨_, hcnt_pos, hleaf_mem⟩ := hleaf_cases.resolve_left (fun h => hlf_nz h.1)
    have hleaf_L0 : leafw.toNat ∈ L0 := hleaf_mem L0 I0 Fr0 hT0
    have hleaf_rng := (hT0.2.2.1 leafw.toNat).mp (List.mem_append_left _ (List.mem_append_left _ hleaf_L0))
    have hleaf_lt_nc0 : leafw.toNat < hdr s0 t 10 + 1 := by omega
    have hkeys0_in := (hB0.1 (hdr s0 t 4, (hdr s0 t 10 + 1) * hdr s0 t 1) (by simp [htabFootprint])).1
    change hdr s0 t 4 ≥ sourceBase ∧ hdr s0 t 4 + (hdr s0 t 10 + 1) * hdr s0 t 1 ≤ heapEnd at hkeys0_in
    have hmul_lf_le : leafw.toNat * hdr s0 t 1 + hdr s0 t 1 ≤ (hdr s0 t 10 + 1) * hdr s0 t 1 := by
      have h1 : (leafw.toNat + 1) * hdr s0 t 1 ≤ (hdr s0 t 10 + 1) * hdr s0 t 1 := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at h1; exact h1
    set lkeyw := keysw + leafw * stridew
    have hlkeyw_nat : lkeyw.toNat = hdr s0 t 4 + leafw.toNat * hdr s0 t 1 := by
      have hmul_nat : (leafw * stridew).toNat = leafw.toNat * hdr s0 t 1 := by
        rw [BitVec.toNat_mul, hstridew_nat, Nat.mod_eq_of_lt (by omega)]
      change (keysw + leafw * stridew).toNat = _
      rw [BitVec.toNat_add, hkeysw_nat, hmul_nat, Nat.mod_eq_of_lt (by omega)]
    have hev_lkey : evalAt s_k (.op .add [.var .local (ofString "keys"),
        .panop .mul [.var .local (ofString "leaf"), .var .local (ofString "stride")]]) =
        some (.val (.word lkeyw)) := by
      simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
        hkeys_sk, hleaf_sk, hst_sk, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
        valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
      rw [BitVec.add_zero]
    refine Ret.decCall3_lf hLF hcode_sk (by decide) (by decide) (by decide)
      lookup_memeq_fn lkeyw keyw klenw hev_lkey
      (by simp [evalAt, evalHOLExact]; exact hkey_sk)
      (by simp [evalAt, evalHOLExact]; exact hkl_sk) ?_
    intro eqw post_meq hrun_meq
    let entry_meq := callEntryStateHOLFinite s_k
      (((HolFiniteMapExact.empty.update (ofString "a", .val (.word lkeyw))).update
        (ofString "b", .val (.word keyw))).update (ofString "n", .val (.word klenw)))
    have hfr_meq_eval := locFrameW_eval (sourceFnBody Guest.Software.guestFn_memeq) (by rfl) entry_meq
    rw [hrun_meq] at hfr_meq_eval; dsimp only at hfr_meq_eval
    let s_eq := setVarHOLFinite (ofString "eq") (.val (.word eqw)) { post_meq with locals := s_k.locals }
    have hs_eq_fr : LocFrame s0 s_eq := by
      unfold LocFrame at hs_k_fr hfr_meq_eval ⊢
      dsimp [s_eq, setVarHOLFinite]; rw [hfr_meq_eval]
      dsimp [entry_meq, callEntryStateHOLFinite, decClockHOLFinite]; rw [hs_k_fr]
    have hcode_seq : s_eq.code = originalRuntimeCode := by unfold LocFrame at hs_eq_fr; rw [hs_eq_fr]; exact hA0.1.code
    have ht_seq : s_eq.locals.lookup (ofString "t") = some (.val (.word tw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_sk, show ofString "eq" ≠ ofString "t" by decide]
    have hkey_seq : s_eq.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkey_sk, show ofString "eq" ≠ ofString "key" by decide]
    have hval_seq : s_eq.locals.lookup (ofString "value") = some (.val (.word valw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hval_sk, show ofString "eq" ≠ ofString "value" by decide]
    have hleaf_seq : s_eq.locals.lookup (ofString "leaf") = some (.val (.word leafw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hleaf_sk, show ofString "eq" ≠ ofString "leaf" by decide]
    have hkeys_seq : s_eq.locals.lookup (ofString "keys") = some (.val (.word keysw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkeys_sk, show ofString "eq" ≠ ofString "keys" by decide]
    have hkl_seq : s_eq.locals.lookup (ofString "klen") = some (.val (.word klenw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkl_sk, show ofString "eq" ≠ ofString "klen" by decide]
    have hst_seq : s_eq.locals.lookup (ofString "stride") = some (.val (.word stridew)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_sk, show ofString "eq" ≠ ofString "stride" by decide]
    have heq_seq : s_eq.locals.lookup (ofString "eq") = some (.val (.word eqw)) := by
      simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    refine Ret.ite_ret (fun _ => noFlow_seq_right fun _ => noFlow_ret) ?_
    intro cw_eq hcw_eq
    have hcw_eq_spec : (cw_eq ≠ 0 → eqw ≠ 0) ∧ (cw_eq = 0 → eqw = 0) := by
      obtain ⟨va, vb, hva, hvb, hcwe⟩ := evalAt_cmp s_eq .notEqual _ _ cw_eq hcw_eq
      simp [evalAt, evalHOLExact, heq_seq] at hva hvb
      subst hva hvb
      constructor
      · intro hnz heq0
        have heq0' : eqw = 0#64 := heq0
        simp [Compiler.Encoders.Asm.wordCmpHOL, heq0'] at hcwe
        exact hnz hcwe
      · intro hz; by_contra hne
        have hne' : eqw ≠ 0#64 := hne
        simp [Compiler.Encoders.Asm.wordCmpHOL, hne'] at hcwe
        rw [hz] at hcwe; exact absurd hcwe (by decide)
    refine ⟨fun _ => ?_, fun hcw_eq_z => ?_⟩
    · exact set_branch_overwrite_values s0 s_eq tw leafw valw hs_eq_fr hA0 hW0 hleaf_mem ht_seq hleaf_seq hval_seq
    · have heqw0 : eqw = 0 := hcw_eq_spec.2 hcw_eq_z
      have hG_entry_meq : GuestInv entry_meq := by
        have hfr_em : LocFrame s0 entry_meq := by
          unfold LocFrame at hs_k_fr ⊢
          dsimp [entry_meq, callEntryStateHOLFinite, decClockHOLFinite]; rw [hs_k_fr]
        unfold LocFrame at hfr_em; rw [hfr_em]
        exact guestInv_with_locals_clock s0 _ _ hA0.1
      have ha_meq : entry_meq.locals.lookup (ofString "a") = some (.val (.word lkeyw)) := by
        simp [entry_meq, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "a" by decide, show ofString "b" ≠ ofString "a" by decide]
      have hb_meq : entry_meq.locals.lookup (ofString "b") = some (.val (.word keyw)) := by
        simp [entry_meq, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "b" by decide]
      have hn_meq : entry_meq.locals.lookup (ofString "n") = some (.val (.word klenw)) := by
        simp [entry_meq, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hklen_ge1 : 1 ≤ klenw.toNat := by rw [hklenw_nat]; exact hB0.2.2.1
      have hklen_le60_w : klenw.toNat ≤ 60 := by rw [hklenw_nat]; exact hklen_le60
      have hlkey_nw : lkeyw.toNat + klenw.toNat < 2 ^ 64 := by rw [hlkeyw_nat, hklenw_nat]; omega
      have hrun_meq0 : (evaluateHOLFiniteState entry_meq (sourceFnBody Guest.Software.guestFn_memeq)).1 =
          some (.returned (.val (.word 0))) := by rw [hrun_meq, heqw0]
      have hkey_nw : keyw.toNat + klenw.toNat < 2 ^ 64 :=
        memeq_ret_key_no_wrap entry_meq hG_entry_meq lkeyw keyw klenw
          hklen_ge1 hklen_le60_w ha_meq hb_meq hn_meq (.val (.word 0)) hrun_meq0
      have hdiff_meq := memeq_body_ret0_exists_diff entry_meq hG_entry_meq lkeyw keyw klenw
        hklen_le60_w hlkey_nw hkey_nw ha_meq hb_meq hn_meq hrun_meq0
      have hmemB_em_s0 : ∀ addr : Nat, memB entry_meq addr = memB s0 addr := by
        intro addr
        have hmem_em : entry_meq.memory = s0.memory := by
          dsimp [entry_meq, callEntryStateHOLFinite, decClockHOLFinite]; exact hs_k_fr.memory
        have hbe_em : entry_meq.be = s0.be := by
          dsimp [entry_meq, callEntryStateHOLFinite, decClockHOLFinite]
          unfold LocFrame at hs_k_fr; rw [hs_k_fr]
        simp [memB, hmem_em, hbe_em]
      have hdiff_s0 : ∃ k < klenw.toNat,
          memB s0 ((keyw + BitVec.ofNat 64 k).toNat) ≠ memB s0 ((lkeyw + BitVec.ofNat 64 k).toNat) := by
        obtain ⟨k, hk, hne⟩ := hdiff_meq
        rw [hmemB_em_s0, hmemB_em_s0] at hne
        exact ⟨k, hk, hne.symm⟩
      have hev_lkey_seq : evalAt s_eq (.op .add [.var .local (ofString "keys"),
          .panop .mul [.var .local (ofString "leaf"), .var .local (ofString "stride")]]) =
          some (.val (.word lkeyw)) := by
        simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
          hkeys_seq, hleaf_seq, hst_seq, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
          valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
        rw [BitVec.add_zero]
      refine Ret.decCall3_lf hLF hcode_seq (by decide) (by decide) (by decide)
        lookup_htab_first_diff keyw lkeyw klenw
        (by simp [evalAt, evalHOLExact]; exact hkey_seq)
        hev_lkey_seq
        (by simp [evalAt, evalHOLExact]; exact hkl_seq) ?_
      intro dw post_fd hrun_fd
      let entry_fd := callEntryStateHOLFinite s_eq
        (((HolFiniteMapExact.empty.update (ofString "a", .val (.word keyw))).update
          (ofString "b", .val (.word lkeyw))).update (ofString "key_len", .val (.word klenw)))
      have hfr_fd_eval := locFrameW_eval (sourceFnBody Guest.Software.guestFn_htab_first_diff) (by rfl) entry_fd
      rw [hrun_fd] at hfr_fd_eval; dsimp only at hfr_fd_eval
      have hdiff_fd : ∃ k < klenw.toNat,
          memB entry_fd ((keyw + BitVec.ofNat 64 k).toNat) ≠ memB entry_fd ((lkeyw + BitVec.ofNat 64 k).toNat) := by
        have hmem_fd : entry_fd.memory = s0.memory := by
          dsimp [entry_fd, callEntryStateHOLFinite, decClockHOLFinite]; exact hs_eq_fr.memory
        have hbe_fd : entry_fd.be = s0.be := by
          dsimp [entry_fd, callEntryStateHOLFinite, decClockHOLFinite]
          unfold LocFrame at hs_eq_fr; rw [hs_eq_fr]
        obtain ⟨k, hk, hne⟩ := hdiff_s0
        refine ⟨k, hk, ?_⟩
        simpa [memB, hmem_fd, hbe_fd] using hne
      obtain ⟨dw', hdw_eq, hd_lt_w⟩ := htab_first_diff_ret_lt entry_fd keyw lkeyw klenw hklen_le60_w hdiff_fd
        (by simp [entry_fd, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "key_len" ≠ ofString "a" by decide, show ofString "b" ≠ ofString "a" by decide])
        (by simp [entry_fd, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "key_len" ≠ ofString "b" by decide])
        (by simp [entry_fd, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        (.val (.word dw)) (by rw [hrun_fd])
      injection hdw_eq with h1; injection h1 with h2; subst h2
      have hd_lt : dw.toNat < 8 * hdr s0 t 0 := by rw [← hklenw_nat]; exact hd_lt_w
      let s_d := setVarHOLFinite (ofString "d") (.val (.word dw)) { post_fd with locals := s_eq.locals }
      have hs_d_fr : LocFrame s0 s_d := by
        unfold LocFrame at hs_eq_fr hfr_fd_eval ⊢
        dsimp [s_d, setVarHOLFinite]; rw [hfr_fd_eval]
        dsimp [entry_fd, callEntryStateHOLFinite, decClockHOLFinite]; rw [hs_eq_fr]
      have ht_sd : s_d.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        simp [s_d, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_seq, show ofString "d" ≠ ofString "t" by decide]
      have hkey_sd : s_d.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
        simp [s_d, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkey_seq, show ofString "d" ≠ ofString "key" by decide]
      have hval_sd : s_d.locals.lookup (ofString "value") = some (.val (.word valw)) := by
        simp [s_d, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hval_seq, show ofString "d" ≠ ofString "value" by decide]
      apply Ret.dec_lf hLF; intro vnd hvnd
      obtain ⟨_, hvnd_eq⟩ := ev_field_load s_d (ofString "t") tw 40#64 ht_sd vnd hvnd
      rw [hs_d_fr.memory, hm0_t5] at hvnd_eq; subst hvnd_eq
      apply Ret.dec_lf hLF; intro vp0 hvp0
      have hvp0_eq : vp0 = .val (.word 0#64) := by simp [evalAt, evalHOLExact] at hvp0; exact hvp0.symm
      subst hvp0_eq
      apply Ret.dec_lf hLF; intro vr0 hvr0
      obtain ⟨_, hvr0_eq⟩ := ev_field_load _ (ofString "t") tw 56#64
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "p" ≠ ofString "t" by decide, show ofString "nodes" ≠ ofString "t" by decide]; exact ht_sd) vr0 hvr0
      have hm56_sd : (setVarHOLFinite (ofString "p") (.val (.word 0#64))
          (setVarHOLFinite (ofString "nodes") (.val (.word nodesw0)) s_d)).memory (tw + 56#64) = .word rootw0 := by
        dsimp [setVarHOLFinite]; rw [hs_d_fr.memory]; exact hm0_t7
      rw [hm56_sd] at hvr0_eq; subst hvr0_eq
      let s_lp := setVarHOLFinite (ofString "n") (.val (.word rootw0))
        (setVarHOLFinite (ofString "p") (.val (.word 0#64))
          (setVarHOLFinite (ofString "nodes") (.val (.word nodesw0)) s_d))
      have hs_lp_fr : LocFrame s0 s_lp := ((hs_d_fr.setVar _ _).setVar _ _).setVar _ _
      have hrootw0_nat : rootw0.toNat = hdr s0 t 7 := by
        have hr_mem : hdr s0 t 7 ∈ L0 ++ I0 := (hT0.2.2.2.2.2.2.2.1 hcnt_pos).1
        have hr_rng := (hT0.2.2.1 (hdr s0 t 7)).mp (List.mem_append_left _ hr_mem)
        rw [BitVec.toNat_ofNat]; omega
      apply Ret.seq
      · intro v hv
        refine False.elim (while_noRet _ _ (fun st v' => ?_) s_lp.clock s_lp le_rfl v hv)
        exact NoRet.dec' (NoRet.seq (NoRet.ite NoRet.brk NoRet.skip)
          (NoRet.seq NoRet.assign (NoRet.ite NoRet.assign NoRet.assign))) st v'
      intro u_lp hu_lp
      have hT_slp : TreeWF L0 I0 Fr0 (hdr s0 t 8) (hdr s0 t 0) (hdr s0 t 3) (hdr s0 t 7) (hdr s0 t 9)
          (nodeF s_lp nodesw0.toNat) (fun i => memW s0 (hdr s0 t 6 + 8 * i)) := by
        have hnf_eq : nodeF s_lp nodesw0.toNat = nodeF s0 (hdr s0 t 5) := by
          funext z off; simp [nodeF, memW, hs_lp_fr.memory, hnodesw0_nat]
        rw [hnf_eq]; exact hT0
      obtain ⟨hu_fr_lp, hu_keep, pw, nw, hp_ulp, hn_ulp, hnw_LI, hpw_spec⟩ :=
        set_descent_loop s_lp u_lp nodesw0 dw rootw0 L0 I0 Fr0
          (hdr s0 t 8) (hdr s0 t 0) (hdr s0 t 3) (hdr s0 t 7) (hdr s0 t 9)
          (fun i => memW s0 (hdr s0 t 6 + 8 * i))
          hcnt_pos hd_lt (by omega) hrootw0_nat hT_slp
          (by simp [s_lp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "n" ≠ ofString "nodes" by decide, show ofString "p" ≠ ofString "nodes" by decide])
          (by simp [s_lp, s_d, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "n" ≠ ofString "d" by decide, show ofString "p" ≠ ofString "d" by decide,
            show ofString "nodes" ≠ ofString "d" by decide])
          (by simp [s_lp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "n" ≠ ofString "p" by decide])
          (by simp [s_lp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
          _ rfl hu_lp
      have hu_fr : LocFrame s0 u_lp := hs_lp_fr.trans hu_fr_lp
      have hpw_spec0 : (pw.toNat = 0 ∧ nw.toNat = hdr s0 t 7) ∨
          (pw.toNat ∈ I0 ∧ nw.toNat ≠ hdr s0 t 7 ∧ pw.toNat = nodeF s0 (hdr s0 t 5) nw.toNat 0) := by
        have hnf_eq : nodeF s_lp nodesw0.toNat nw.toNat 0 = nodeF s0 (hdr s0 t 5) nw.toNat 0 := by
          simp [nodeF, memW, hs_lp_fr.memory, hnodesw0_nat]
        rw [hnf_eq] at hpw_spec; exact hpw_spec
      have ht_ulp : u_lp.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        rw [hu_keep (ofString "t") (by decide) (by decide)]
        simp [s_lp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_sd,
          show ofString "n" ≠ ofString "t" by decide, show ofString "p" ≠ ofString "t" by decide,
          show ofString "nodes" ≠ ofString "t" by decide]
      have hkey_ulp : u_lp.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
        rw [hu_keep (ofString "key") (by decide) (by decide)]
        simp [s_lp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkey_sd,
          show ofString "n" ≠ ofString "key" by decide, show ofString "p" ≠ ofString "key" by decide,
          show ofString "nodes" ≠ ofString "key" by decide]
      have hval_ulp : u_lp.locals.lookup (ofString "value") = some (.val (.word valw)) := by
        rw [hu_keep (ofString "value") (by decide) (by decide)]
        simp [s_lp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hval_sd,
          show ofString "n" ≠ ofString "value" by decide, show ofString "p" ≠ ofString "value" by decide,
          show ofString "nodes" ≠ ofString "value" by decide]
      have hd_ulp : u_lp.locals.lookup (ofString "d") = some (.val (.word dw)) := by
        rw [hu_keep (ofString "d") (by decide) (by decide)]
        simp [s_lp, s_d, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "d" by decide, show ofString "p" ≠ ofString "d" by decide,
          show ofString "nodes" ≠ ofString "d" by decide]
      have hmem_u : u_lp.memory = s0.memory := hu_fr.memory
      have hA_ulp : ArenaReady u_lp := by
        unfold LocFrame at hu_fr; rw [hu_fr]; exact (arenaReady_locals s0 _ _).mpr hA0
      have hNS_ulp : NodeState u_lp t (L0 ++ I0) Fr0 := by
        have hNS0 : NodeState s0 t (L0 ++ I0) Fr0 := ⟨hB0, hT0.2.1, hT0.2.2.1, hT0.2.2.2.2.2.2.2.2.2.2.2⟩
        unfold LocFrame at hu_fr; rw [hu_fr]; exact hNS0
      have hcnt_le_ulp : hdr u_lp t 3 ≤ (L0 ++ I0).length := by
        have hh3_u : hdr u_lp t 3 = hdr s0 t 3 := by unfold hdr memW; rw [hmem_u]
        have hlen := hT0.1; rw [hh3_u, List.length_append]; omega
      have hal_ulp : ∀ i ∈ htabFootprint u_lp t, Allocated u_lp i := by
        unfold LocFrame at hu_fr; rw [hu_fr]; exact hal0
      refine Ret.decCall_new_leaf_lf hLF tw keyw valw (L0 ++ I0) Fr0
        (by simp [evalAt, evalHOLExact]; exact ht_ulp)
        (by simp [evalAt, evalHOLExact]; exact hkey_ulp)
        (by simp [evalAt, evalHOLExact]; exact hval_ulp)
        hA_ulp hNS_ulp hcnt_le_ulp hal_ulp ?_
      intro nlw Fr1 s1 hA1 hNS1 _ _ hh3_1 _ _ n8_1 _ _ ordc_1 hnd_1 hord_1 _ hfp_1 _ _ hloc_1
      let s1_nl := setVarHOLFinite (ofString "nl") (.val (.word nlw)) s1
      have hA1_nl : ArenaReady s1_nl := (arenaReady_locals s1 _ s1.clock).mpr hA1
      have hNS1_nl : NodeState s1_nl t ((L0 ++ I0) ++ [nlw.toNat]) Fr1 := hNS1
      have hal1_nl : ∀ i ∈ htabFootprint s1_nl t, Allocated s1_nl i := fun i hi => (hfp_1 i hi).1
      have ht_s1nl : s1_nl.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        simp [s1_nl, setVarHOLFinite, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, ht_ulp,
          show ofString "nl" ≠ ofString "t" by decide]
      have hd_s1nl : s1_nl.locals.lookup (ofString "d") = some (.val (.word dw)) := by
        simp [s1_nl, setVarHOLFinite, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, hd_ulp,
          show ofString "nl" ≠ ofString "d" by decide]
      refine Ret.decCall_new_internal_lf hLF tw dw ((L0 ++ I0) ++ [nlw.toNat]) Fr1
        (by simp [evalAt, evalHOLExact]; exact ht_s1nl)
        (by simp [evalAt, evalHOLExact]; exact hd_s1nl)
        hA1_nl hNS1_nl hal1_nl ?_
      intro niw Fr2 s2 hA2 hNS2 _ _ hh3_2 _ _ _ _ _ _ hnd_2 hord_2 _ _ _ _ hloc_2
      let L_cur := (u_lp.locals.update (ofString "nl", .val (.word nlw))).update (ofString "ni", .val (.word niw))
      have hs2_ni_eq : setVarHOLFinite (ofString "ni") (.val (.word niw)) s2 =
          NS s2 L_cur s2.globals s2.memory s2.clock := by
        simp [setVarHOLFinite, NS, hloc_2, hloc_1, L_cur]
      rw [hs2_ni_eq]
      have hh_u : ∀ k, hdr u_lp t k = hdr s0 t k := fun k => by unfold hdr memW; rw [hmem_u]
      have hh3_20 : hdr s2 t 3 = hdr s0 t 3 + 1 := hh3_2.trans (hh3_1.trans (by rw [hh_u 3]))
      have hnl_mem_A1 : nlw.toNat ∈ (L0 ++ I0) ++ [nlw.toNat] := List.mem_append_right _ (by simp)
      have hnl8_20 : nodeF s2 (hdr s2 t 5) nlw.toNat 8 = valw.toNat :=
        (hnd_2 nlw.toNat hnl_mem_A1 8 (Or.inr (Or.inl rfl))).trans n8_1
      have hcnt_lt_nc1 : hdr s0 t 3 < hdr s1 tw.toNat 10 + 1 := by
        have hB1 : HtabBlocks s1 tw.toNat := hNS1.1
        have hnx1_le : hdr s1 tw.toNat 8 ≤ hdr s1 tw.toNat 10 + 1 := hB1.2.2.2.2.2.2.2
        have hnd1 := (List.nodup_append.mp hNS1.2.1).1
        have hr1 : ∀ x ∈ (L0 ++ I0) ++ [nlw.toNat], 1 ≤ x ∧ x < hdr s1 tw.toNat 8 := fun x hx =>
          (hNS1.2.2.1 x).mp (List.mem_append_left _ hx)
        have hlen_le := nodup_len_le_range hnd1 hr1
        have hL0_len : L0.length = hdr s0 t 3 := hT0.1
        have hnl_rng := hr1 nlw.toNat (List.mem_append_right _ (by simp))
        simp only [List.length_append, List.length_singleton] at hlen_le
        omega
      have hord_cnt_20 : memW s2 (hdr s2 t 6 + 8 * hdr s0 t 3) = nlw.toNat := by
        have h1 := hord_2 (hdr s0 t 3) hcnt_lt_nc1
        have h2 : memW s1 (hdr s1 t 6 + 8 * hdr s0 t 3) = nlw.toNat := by rw [← hh_u 3]; exact ordc_1
        exact h1.trans h2
      have hord_old_20 : ∀ i, i < hdr s0 t 3 →
          memW s2 (hdr s2 t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i) := by
        intro i hi
        have h1 := hord_2 i (lt_trans hi hcnt_lt_nc1)
        have h2 : memW s1 (hdr s1 t 6 + 8 * i) = memW u_lp (hdr u_lp t 6 + 8 * i) :=
          hord_1 i (by rw [hh_u 3]; exact hi)
        have h3 : memW u_lp (hdr u_lp t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i) := by
          rw [hh_u 6]; unfold memW; rw [hmem_u]
        exact (h1.trans h2).trans h3
      have hnd_old_20 : ∀ z ∈ L0 ++ I0, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
          nodeF s2 (hdr s2 t 5) z off = nodeF s0 (hdr s0 t 5) z off := by
        intro z hz off hoff
        have h1 := hnd_2 z (List.mem_append_left _ hz) off hoff
        have h2 : nodeF s1 (hdr s1 t 5) z off = nodeF u_lp (hdr u_lp t 5) z off := hnd_1 z hz off hoff
        have h3 : nodeF u_lp (hdr u_lp t 5) z off = nodeF s0 (hdr s0 t 5) z off := by
          rw [hh_u 5]; unfold nodeF memW; rw [hmem_u]
        exact (h1.trans h2).trans h3
      exact set_splice_values s0 s2 tw dw pw nw nlw niw valw L0 I0 Fr0 Fr2 L_cur
        (by simp [L_cur, HolFiniteMapExact.lookup_update, FUPDATE, ht_ulp,
          show ofString "ni" ≠ ofString "t" by decide, show ofString "nl" ≠ ofString "t" by decide])
        (by simp [L_cur, HolFiniteMapExact.lookup_update, FUPDATE, hp_ulp,
          show ofString "ni" ≠ ofString "p" by decide, show ofString "nl" ≠ ofString "p" by decide])
        (by simp [L_cur, HolFiniteMapExact.lookup_update, FUPDATE, hn_ulp,
          show ofString "ni" ≠ ofString "n" by decide, show ofString "nl" ≠ ofString "n" by decide])
        (by simp [L_cur, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "ni" ≠ ofString "nl" by decide])
        (by simp [L_cur, HolFiniteMapExact.lookup_update, FUPDATE])
        hA2 hNS2 hT0 hnw_LI hpw_spec0 hh3_20 hnl8_20 hord_cnt_20 hord_old_20 hnd_old_20

theorem htab_set_values_sub {F : Type} (s : PanSemStateFiniteExact 64 F)
    (tw keyw valw : BitVec 64)
    (ht : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hkey : s.locals.lookup (ofString "key") = some (.val (.word keyw)))
    (hval : s.locals.lookup (ofString "value") = some (.val (.word valw)))
    (hP : HtabArgWF s)
    (v : ValueHOL 64)
    (hv : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_set)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_set)).2
    HtabExit s post ∧ post.be = s.be ∧
    ∀ x ∈ htabValues post (locN s "t"), x = locN s "value" ∨ x ∈ htabValues s (locN s "t") := by
  dsimp only
  have hlt : locN s "t" = tw.toNat := by simp [locN, ht]
  have hlv : locN s "value" = valw.toNat := by simp [locN, hval]
  obtain ⟨hA0, hW0, hal0⟩ := hP
  rw [hlt] at hW0 hal0
  have hexitAt := htab_set_body_spec s tw keyw valw ht hkey hval hA0 hW0 hal0 v hv
  have hExit : HtabExit s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_set)).2 := by
    rw [htabExit_iff_at, hlt]; exact hexitAt
  have hbe : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_set)).2.be = s.be :=
    evaluate_be_eq s _
  have hvals := htab_set_body_values s tw keyw valw ht hkey hval hA0 hW0 hal0 v hv
  rw [hlt, hlv]
  exact ⟨hExit, hbe, hvals⟩

end HtabSetValues

end InitECandidate.Solver.Wave8GuestInv.R16Shards

end InitECandidate.Solver.Wave8GuestInv.R16Shards
