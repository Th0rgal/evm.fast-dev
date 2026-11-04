import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalBase

/-! Zero-sorry proofs of `wk_bal_remove_change` and `wk_remove_storage_write` (`ContractParts/C08.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBal

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Contracts.M08
open InitECandidate.Solver.Wave8GuestInv.M11

/-! ## 1. Function lookups and catchable-exception absence -/

theorem lookup_htab_del :
    originalRuntimeCode.lookup (ofString "htab_del") =
      some ([(ofString "t", .one), (ofString "key", .one)],
        sourceFnBody Guest.Software.guestFn_htab_del, .one) :=
  lookup_of_guestAst_getElem 139 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_del) rfl

theorem lookup_bal_list_remove_idx :
    originalRuntimeCode.lookup (ofString "bal_list_remove_idx") =
      some ([(ofString "l", .one), (ofString "esz", .one), (ofString "idx", .one)],
        sourceFnBody Guest.Software.guestFn_bal_list_remove_idx, .one) :=
  lookup_of_guestAst_getElem 424 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bal_list_remove_idx) rfl

theorem lookup_bal_remove_change :
    originalRuntimeCode.lookup (ofString "bal_remove_change") =
      some ([(ofString "addr", .one), (ofString "which", .one), (ofString "esz", .one),
             (ofString "idx", .one)],
        sourceFnBody Guest.Software.guestFn_bal_remove_change, .one) :=
  lookup_of_guestAst_getElem 425 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bal_remove_change) rfl

theorem lookup_remove_storage_write :
    originalRuntimeCode.lookup (ofString "remove_storage_write") =
      some ([(ofString "addr", .one), (ofString "slot", .one), (ofString "idx", .one)],
        sourceFnBody Guest.Software.guestFn_remove_storage_write, .one) :=
  lookup_of_guestAst_getElem 426 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_remove_storage_write) rfl

theorem htab_del_no_catchable_exn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (e : MlS) (v : ValueHOL 64)
    (hne : e ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_del)).1 ≠
      some (.exception e v) := by
  refine evaluate_noCatchableRaise
    InitECandidate.Solver.Wave8Contracts.M15.htabGetCallees
    ?_ (sourceFnBody Guest.Software.guestFn_htab_del) rfl s hcode e v hne
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ :=
    InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  simp only [InitECandidate.Solver.Wave8Contracts.M15.htabGetCallees,
    Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with rfl | rfl
  · rw [lookup_htab_find_leaf] at hinst
    have hbody := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← hbody]; rfl
  · rw [lookup_memeq] at hinst
    have hbody := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← hbody]; rfl

def memcpyOnlyCallees (f : MlS) : Bool :=
  f == ofString "memcpy"

theorem bal_list_remove_idx_no_catchable_exn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (e : MlS) (v : ValueHOL 64)
    (hne : e ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx)).1 ≠
      some (.exception e v) := by
  refine evaluate_noCatchableRaise memcpyOnlyCallees ?_
    (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx) rfl s hcode e v hne
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ :=
    InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
  simp only [memcpyOnlyCallees, beq_iff_eq] at hf
  subst hf
  rw [InitECandidate.Solver.Wave8GuestInv.M11.lookup_memcpy] at hinst
  have hbody := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
  rw [← hbody]; rfl

theorem evaluate_be_eq {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) :
    (evaluateHOLFiniteState s p).2.be = s.be := by
  have inv := evaluateInvariantsHOLFinite p
    (PanPropsEvalStateFiniteExact.ofPanSemFinite s)
    (evaluateHOLFiniteState s p).1
    (PanPropsEvalStateFiniteExact.ofPanSemFinite (evaluateHOLFiniteState s p).2)
    (by simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
          PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite])
  exact inv.2.2.1

/-! ## 2. `htabValues` inclusion for `htab_del` -/

section HtabDelValues

open Wave8M19.Htab
open InitECandidate.Solver.Wave8GuestInv.HtabC00Ports (arg_to_light exit_from_light)

theorem del_inner_values_subperm {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
    (hMo : ∃ f : Nat → Nat,
      (∀ i < cw.toNat, f i < Wave8M19.hdr s tw.toNat 3 ∧
        rdN M' (ow.toNat + 8 * i) = rdN s.memory (ow.toNat + 8 * f i) ∧
        rdN s.memory (ow.toNat + 8 * f i) ∈ L) ∧
      (∀ i1 < cw.toNat, ∀ i2 < cw.toNat, i1 ≠ i2 → f i1 ≠ f i2))
    (hMh : ∀ c, c < 88 → rdN M' (tw.toNat + c) = rdN s.memory (tw.toNat + c))
    (hpost : DelPostR s M' tw nd lw cw post) :
    ∃ f : Nat → Nat,
      (∀ i (hi : i < (htabValues post tw.toNat).length),
        ∃ hj : f i < (htabValues s tw.toNat).length,
          (htabValues post tw.toNat)[i] = (htabValues s tw.toNat)[f i]'hj) ∧
      (∀ i1 < (htabValues post tw.toNat).length,
        ∀ i2 < (htabValues post tw.toNat).length, i1 ≠ i2 → f i1 ≠ f i2) := by
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
    Wave8M19.Htab.nodup_len_le L _ hndLI.1 (fun x hx => (hmem x).1 (mL x hx))
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
      have hc8p : nf (nf lw.toNat 0) 8 ≠ nf lw.toNat 0 := fun h => hgp (by nth_rw 1 [← h]; exact hp8p)
      have hc16p : nf (nf lw.toNat 0) 16 ≠ nf lw.toNat 0 := fun h => hgp (by nth_rw 1 [← h]; exact hp16p)
      rcases hp0 : s.memory (nd + lw * 32 + 0) with ⟨p0⟩
      have ep0 : nf lw.toNat 0 = p0.toNat := nodeF_of s nd lw p0 0 hp0
      simp only [ep0] at hpB hp816 hc8B hc16B hcl hlp hmvp hgN hgp hmvg hc8p hc16p hgB
      rcases hg0 : s.memory (nd + p0 * 32 + 0) with ⟨g0⟩
      have eg0 : nf p0.toNat 0 = g0.toNat := nodeF_of s nd p0 g0 0 hg0
      rcases hc8 : s.memory (nd + p0 * 32 + 8) with ⟨c8⟩
      have ec8 : nf p0.toNat 8 = c8.toNat := nodeF_of s nd p0 c8 8 hc8
      rcases hc16 : s.memory (nd + p0 * 32 + 16) with ⟨c16⟩
      have ec16 : nf p0.toNat 16 = c16.toNat := nodeF_of s nd p0 c16 16 hc16
      simp only [eg0, ec8, ec16] at hpB hp816 hc8B hc16B hcl hlp hmvp hgN hgp hmvg hc8p hc16p hgB
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
      have hnaddr : ∀ m j, m < Wave8M19.hdr s tw.toNat 10 + 1 → j < 32 →
          nd.toNat + 32 * m + j < 2 ^ 64 := by
        clear * - hfp2 hhe; intro m j hm hj; omega
      have hhaddr : ∀ c, c < 88 → tw.toNat + c < 2 ^ 64 := by
        clear * - hfp0 hhe; intro c hc; omega
      have hsepHN : ∀ c m j, c < 88 → m < Wave8M19.hdr s tw.toNat 10 + 1 → j < 32 →
          tw.toNat + c ≠ nd.toNat + 32 * m + j := by
        clear * - hdA; intro c m j hc hm hj; omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · change Wave8M19.memW post (tw.toNat + 8 * 3) = _
        have hsepN := fun m j hm hj => hsepHN 24 m j (by decide) hm hj
        by_cases hg : g0.toNat = 0 <;> by_cases hl : g8.toNat = p0.toNat
        all_goals
          simp only [← BitVec.toNat_inj, bv0_toNat, hg, hl, if_true, if_false] at hpe
          rw [memW_rdN, hpe, NS_memory]
          clear * - hnaddr hhaddr hsepN hgN hpB hlwB hsvB
          simp only [an0, an8, an16, ah24, ah56, ah72, rdN_upd,
            Nat.mod_eq_of_lt (hhaddr 24 (by decide)),
            Nat.mod_eq_of_lt (hhaddr 56 (by decide)),
            Nat.mod_eq_of_lt (hhaddr 72 (by decide)),
            Nat.mod_eq_of_lt (hnaddr lw.toNat 0 hlwB.2 (by decide)),
            Nat.mod_eq_of_lt (hnaddr p0.toNat 0 hpB.2 (by decide)),
            Nat.mod_eq_of_lt (hnaddr sv.toNat 0 hsvB.2.1 (by decide)),
            Nat.mod_eq_of_lt (hnaddr g0.toNat 8 hgN (by decide)),
            Nat.mod_eq_of_lt (hnaddr g0.toNat 16 hgN (by decide)),
            if_neg (hsepN lw.toNat 0 hlwB.2 (by decide)),
            if_neg (hsepN p0.toNat 0 hpB.2 (by decide)),
            if_neg (hsepN sv.toNat 0 hsvB.2.1 (by decide)),
            if_neg (hsepN g0.toNat 8 hgN (by decide)),
            if_neg (hsepN g0.toNat 16 hgN (by decide))]
          split_ifs <;> omega
      · change Wave8M19.memW post (tw.toNat + 40) = _
        have hsepN := fun m j hm hj => hsepHN 40 m j (by decide) hm hj
        have h40 := hMh 40 (by decide)
        by_cases hg : g0.toNat = 0 <;> by_cases hl : g8.toNat = p0.toNat
        all_goals
          simp only [← BitVec.toNat_inj, bv0_toNat, hg, hl, if_true, if_false] at hpe
          rw [memW_rdN, hpe, NS_memory]
          clear * - hnaddr hhaddr hsepN hgN hpB hlwB hsvB h40 e5_rd
          simp only [an0, an8, an16, ah24, ah56, ah72, rdN_upd,
            Nat.mod_eq_of_lt (hhaddr 40 (by decide)),
            Nat.mod_eq_of_lt (hhaddr 24 (by decide)),
            Nat.mod_eq_of_lt (hhaddr 56 (by decide)),
            Nat.mod_eq_of_lt (hhaddr 72 (by decide)),
            Nat.mod_eq_of_lt (hnaddr lw.toNat 0 hlwB.2 (by decide)),
            Nat.mod_eq_of_lt (hnaddr p0.toNat 0 hpB.2 (by decide)),
            Nat.mod_eq_of_lt (hnaddr sv.toNat 0 hsvB.2.1 (by decide)),
            Nat.mod_eq_of_lt (hnaddr g0.toNat 8 hgN (by decide)),
            Nat.mod_eq_of_lt (hnaddr g0.toNat 16 hgN (by decide)),
            if_neg (hsepN lw.toNat 0 hlwB.2 (by decide)),
            if_neg (hsepN p0.toNat 0 hpB.2 (by decide)),
            if_neg (hsepN sv.toNat 0 hsvB.2.1 (by decide)),
            if_neg (hsepN g0.toNat 8 hgN (by decide)),
            if_neg (hsepN g0.toNat 16 hgN (by decide))]
          split_ifs <;> omega
      · change Wave8M19.memW post (tw.toNat + 48) = _
        have hsepN := fun m j hm hj => hsepHN 48 m j (by decide) hm hj
        have h48 := hMh 48 (by decide)
        by_cases hg : g0.toNat = 0 <;> by_cases hl : g8.toNat = p0.toNat
        all_goals
          simp only [← BitVec.toNat_inj, bv0_toNat, hg, hl, if_true, if_false] at hpe
          rw [memW_rdN, hpe, NS_memory]
          clear * - hnaddr hhaddr hsepN hgN hpB hlwB hsvB h48 e6_rd
          simp only [an0, an8, an16, ah24, ah56, ah72, rdN_upd,
            Nat.mod_eq_of_lt (hhaddr 48 (by decide)),
            Nat.mod_eq_of_lt (hhaddr 24 (by decide)),
            Nat.mod_eq_of_lt (hhaddr 56 (by decide)),
            Nat.mod_eq_of_lt (hhaddr 72 (by decide)),
            Nat.mod_eq_of_lt (hnaddr lw.toNat 0 hlwB.2 (by decide)),
            Nat.mod_eq_of_lt (hnaddr p0.toNat 0 hpB.2 (by decide)),
            Nat.mod_eq_of_lt (hnaddr sv.toNat 0 hsvB.2.1 (by decide)),
            Nat.mod_eq_of_lt (hnaddr g0.toNat 8 hgN (by decide)),
            Nat.mod_eq_of_lt (hnaddr g0.toNat 16 hgN (by decide)),
            if_neg (hsepN lw.toNat 0 hlwB.2 (by decide)),
            if_neg (hsepN p0.toNat 0 hpB.2 (by decide)),
            if_neg (hsepN sv.toNat 0 hsvB.2.1 (by decide)),
            if_neg (hsepN g0.toNat 8 hgN (by decide)),
            if_neg (hsepN g0.toNat 16 hgN (by decide))]
          split_ifs <;> omega
      · intro i hi
        have hiB : i < Wave8M19.hdr s tw.toNat 10 + 1 := by omega
        have hread : ow.toNat + 8 * i < 2 ^ 64 := by clear * - hfp3 hhe hiB; omega
        have hsepN : ∀ m j, m < Wave8M19.hdr s tw.toNat 10 + 1 → j < 32 →
            ow.toNat + 8 * i ≠ nd.toNat + 32 * m + j := by
          clear * - hdC hiB; intro m j hm hj; omega
        have hsepH : ∀ c, c < 88 → ow.toNat + 8 * i ≠ tw.toNat + c := by
          clear * - hdB hiB; intro c hc; omega
        change Wave8M19.memW post (ow.toNat + 8 * i) = _
        by_cases hg : g0.toNat = 0 <;> by_cases hl : g8.toNat = p0.toNat
        all_goals
          simp only [← BitVec.toNat_inj, bv0_toNat, hg, hl, if_true, if_false] at hpe
          rw [memW_rdN, hpe, NS_memory]
          clear * - hread hnaddr hhaddr hsepN hsepH hgN hpB hlwB hsvB
          simp only [an0, an8, an16, ah24, ah56, ah72, rdN_upd,
            Nat.mod_eq_of_lt hread,
            Nat.mod_eq_of_lt (hhaddr 24 (by decide)),
            Nat.mod_eq_of_lt (hhaddr 56 (by decide)),
            Nat.mod_eq_of_lt (hhaddr 72 (by decide)),
            Nat.mod_eq_of_lt (hnaddr lw.toNat 0 hlwB.2 (by decide)),
            Nat.mod_eq_of_lt (hnaddr p0.toNat 0 hpB.2 (by decide)),
            Nat.mod_eq_of_lt (hnaddr sv.toNat 0 hsvB.2.1 (by decide)),
            Nat.mod_eq_of_lt (hnaddr g0.toNat 8 hgN (by decide)),
            Nat.mod_eq_of_lt (hnaddr g0.toNat 16 hgN (by decide)),
            if_neg (hsepH 24 (by decide)),
            if_neg (hsepH 56 (by decide)),
            if_neg (hsepH 72 (by decide)),
            if_neg (hsepN lw.toNat 0 hlwB.2 (by decide)),
            if_neg (hsepN p0.toNat 0 hpB.2 (by decide)),
            if_neg (hsepN sv.toNat 0 hsvB.2.1 (by decide)),
            if_neg (hsepN g0.toNat 8 hgN (by decide)),
            if_neg (hsepN g0.toNat 16 hgN (by decide))]
      · intro z hz
        have hzB := hLIF z (mL z hz)
        have hzg : z ≠ g0.toNat := by
          rcases hgB with h0 | hI
          · omega
          · exact fun e => hLI z hz (e ▸ hI)
        have hsepH : ∀ c, c < 88 → nd.toNat + 32 * z + 8 ≠ tw.toNat + c := by
          clear * - hzB hdA; intro c hc; omega
        change Wave8M19.memW post (nd.toNat + 32 * z + 8) = _
        by_cases hg : g0.toNat = 0 <;> by_cases hl : g8.toNat = p0.toNat
        all_goals
          simp only [← BitVec.toNat_inj, bv0_toNat, hg, hl, if_true, if_false] at hpe
          rw [memW_rdN, hpe, NS_memory]
          clear * - hnaddr hhaddr hsepH hzB hzg hgN hpB hlwB hsvB
          simp only [an0, an8, an16, ah24, ah56, ah72, rdN_upd,
            Nat.mod_eq_of_lt (hnaddr z 8 hzB.2 (by decide)),
            Nat.mod_eq_of_lt (hhaddr 24 (by decide)),
            Nat.mod_eq_of_lt (hhaddr 56 (by decide)),
            Nat.mod_eq_of_lt (hhaddr 72 (by decide)),
            Nat.mod_eq_of_lt (hnaddr lw.toNat 0 hlwB.2 (by decide)),
            Nat.mod_eq_of_lt (hnaddr p0.toNat 0 hpB.2 (by decide)),
            Nat.mod_eq_of_lt (hnaddr sv.toNat 0 hsvB.2.1 (by decide)),
            Nat.mod_eq_of_lt (hnaddr g0.toNat 8 hgN (by decide)),
            Nat.mod_eq_of_lt (hnaddr g0.toNat 16 hgN (by decide)),
            if_neg (hsepH 24 (by decide)),
            if_neg (hsepH 56 (by decide)),
            if_neg (hsepH 72 (by decide)),
            node_addr_eq_iff nd.toNat z lw.toNat 8 0 (by decide) (by decide),
            node_addr_eq_iff nd.toNat z p0.toNat 8 0 (by decide) (by decide),
            node_addr_eq_iff nd.toNat z sv.toNat 8 0 (by decide) (by decide),
            node_addr_eq_iff nd.toNat z g0.toNat 8 8 (by decide) (by decide),
            node_addr_eq_iff nd.toNat z g0.toNat 8 16 (by decide) (by decide)]
          simp only [show ¬(8 = 0) by decide, and_false, show (8 = 8) by decide, and_true,
            show ¬(8 = 16) by decide, hzg, if_false]
  obtain ⟨hh3_p, hh5_p, hh6_p, hord_p, hnd8_p⟩ := hpost_reads
  obtain ⟨f, hf_val, hf_inj⟩ := hMo
  refine ⟨f, ?_, ?_⟩
  · intro i hi
    have hlen_post : (htabValues post tw.toNat).length = cw.toNat := by
      simp [htabValues, hh3_p]
    have hlen_pre : (htabValues s tw.toNat).length = Wave8M19.hdr s tw.toNat 3 := by
      simp only [htabValues, List.length_map, List.length_range]; rfl
    have hi_lt : i < cw.toNat := hlen_post ▸ hi
    obtain ⟨hj_lt, hMo_ij, hj_L⟩ := hf_val i hi_lt
    refine ⟨hlen_pre.symm ▸ hj_lt, ?_⟩
    have hord_eq : memW post (ow.toNat + 8 * i) = memW s (ow.toNat + 8 * f i) := by
      rw [hord_p i hi_lt, hMo_ij]
      change _ = Wave8M19.memW s (ow.toNat + 8 * f i)
      rw [memW_rdN]
    set z := memW s (ow.toNat + 8 * f i)
    have hz_L : z ∈ L := by
      change Wave8M19.memW s (ow.toNat + 8 * f i) ∈ L
      rwa [memW_rdN]
    have hz_B := hLIF z (mL z hz_L)
    have hnd_eq : nodeF post nd.toNat z 8 = nodeF s nd.toNat z 8 := by
      rw [hnd8_p z hz_L, hMn z 8 hz_B.2 (by decide)]
      simp only [show ¬(z = mvN ∧ (8 : Nat) = 16) by omega, ↓reduceIte]
      change _ = Wave8M19.nodeF s nd.toNat z 8
      rw [Wave8M19.nodeF, memW_rdN]
    simp only [htabValues, List.getElem_map, List.getElem_range]
    rw [hh5_p, hh6_p, hord_eq, hnd_eq]
    change _ = nodeF s (Wave8M19.hdr s tw.toNat 5) (memW s (Wave8M19.hdr s tw.toNat 6 + 8 * f i)) 8
    rw [h5, h6]
  · intro i1 hi1 i2 hi2 hne
    have hlen_post : (htabValues post tw.toNat).length = cw.toNat := by
      simp [htabValues, hh3_p]
    exact hf_inj i1 (hlen_post ▸ hi1) i2 (hlen_post ▸ hi2) hne

theorem htab_del_values_subperm {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hP : HtabArgWF s)
    (v : ValueHOL 64)
    (hv : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_del)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_del)).2
    HtabExit s post ∧ post.be = s.be ∧ post.globals = s.globals ∧
    ∃ f : Nat → Nat,
      (∀ i (hi : i < (htabValues post (locN s "t")).length),
        ∃ hj : f i < (htabValues s (locN s "t")).length,
          (htabValues post (locN s "t"))[i] = (htabValues s (locN s "t"))[f i]'hj) ∧
      (∀ i1 < (htabValues post (locN s "t")).length,
        ∀ i2 < (htabValues post (locN s "t")).length, i1 ≠ i2 → f i1 ≠ f i2) := by
  dsimp only
  have hbe : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_del)).2.be = s.be :=
    evaluate_be_eq s _
  have hExit : HtabExit s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_del)).2 := by
    rcases htab_del_spec_proof with ⟨ps, body, ret, hl, hrun⟩
    have hbody_eq : body = sourceFnBody Guest.Software.guestFn_htab_del := by
      have h1 := lookup_htab_del
      rw [hl] at h1
      exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj h1)).2).1
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
  have hndLI := List.nodup_append.mp (List.nodup_append.mp hnodup).1
  have hLlen' : L.length ≤ Wave8M19.hdr s tw.toNat 8 - 1 :=
    Wave8M19.Htab.nodup_len_le L _ hndLI.1 (fun x hx => (hmemr x).1 (by simp [hx]))
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
        have hmk : Wave8M19.maxKeyLen = 60 := rfl
        have h8 : (k * 8).toNat = k.toNat * 8 := by rw [BitVec.toNat_mul]; simp; omega
        rw [h8]; unfold Wave8M19.nodeF at this; omega
      · obtain ⟨_, h8, h16, _⟩ := hint _ hwI
        unfold Wave8M19.nodeF at h8 h16
        exact ⟨List.mem_cons_of_mem _ h8, List.mem_cons_of_mem _ h16⟩)
    nd ow cntw hnd how hcnt).run v hv
  rcases hres with heq | ⟨lw, pw, mv, hlwS, hlw0, hcrit, hpw, hmv0, hcase⟩
  · have hmem_eq : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_del)).2.memory = s.memory := by
      have := congrArg PanSemStateFiniteExact.memory heq; exact this
    have hg_eq : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_del)).2.globals = s.globals := by
      have := congrArg PanSemStateFiniteExact.globals heq; exact this
    have hveq : htabValues (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_del)).2 tw.toNat =
        htabValues s tw.toNat := by
      simp [htabValues, hdr, nodeF, memW, hmem_eq]
    exact ⟨hg_eq, id, fun i hi => ⟨by rwa [hveq] at hi, by simp [hveq]⟩, fun _ _ _ _ hne => hne⟩
  · have hg_eq : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_del)).2.globals = s.globals := by
      rcases hcase with ⟨_, ⟨_, _, _, hpe⟩ | ⟨_, _, _, hpe⟩⟩ | ⟨_, ⟨_, _, _, hpe⟩ | ⟨_, _, _, hpe⟩⟩ <;>
        (have := congrArg PanSemStateFiniteExact.globals hpe; rw [NS_globals] at this; exact this)
    refine ⟨hg_eq, ?_⟩
    have hlwLI : lw.toNat ∈ L ++ I := by
      rcases List.mem_cons.mp hlwS with h | h
      · exact absurd (word_eq_zero_of_toNat h) hlw0
      · exact h
    have hleaf : lw.toNat ∈ L := by
      rcases List.mem_append.mp hlwLI with h | h
      · exact h
      · exfalso
        have hc := hcrit nd k hnd hk
        have h24 := (hint _ h).1
        have hmk : Wave8M19.maxKeyLen = 60 := rfl
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
      refine del_inner_values_subperm s _ tw nd ow lw (cntw - 1) s.memory L I Fr mvN hB0 hT0 e5 e6 hcw hleaf hmvL ?_ ?_ (fun _ _ => rfl) hpost
      · intro n off _ _
        split_ifs with h
        · rw [h.1, h.2, hmvlw, ← memW_rdN]; rfl
        · rfl
      · refine ⟨fun i => i, fun i hi => ?_, fun _ _ _ _ hne => hne⟩
        dsimp only
        have hiL : i < L.length := by omega
        refine ⟨by rw [e3]; omega, rfl, ?_⟩
        rw [← memW_rdN, (hord i hiL).1]; exact List.getElem_mem hiL
    · have hi0' : i0 ≠ L.length - 1 := by
        intro h; apply hne_p; apply BitVec.eq_of_toNat_eq; rw [hcw1]; omega
      have hpwB : pw.toNat < Wave8M19.hdr s tw.toNat 10 + 1 := by omega
      have hmvB' : mv.toNat < Wave8M19.hdr s tw.toNat 10 + 1 := by omega
      have hposR : rdN s.memory (nd.toNat + 32 * lw.toNat + 16) = pw.toNat := by
        rw [← memW_rdN, hpw']; exact hpos
      refine del_inner_values_subperm s _ tw nd ow lw (cntw - 1) _ L I Fr mvN hB0 hT0 e5 e6 hcw hleaf hmvL ?_ ?_ ?_ hpost
      · intro n off hn hoff
        simp only [Wave8M19.nodeF, memW_rdN]
        rdsimp [hposR]
        split_ifs <;> omega
      · refine ⟨fun i => if i = pw.toNat then L.length - 1 else i, fun i hi => ?_, fun i1 hi1 i2 hi2 hne => ?_⟩
        · have hiB : i < Wave8M19.hdr s tw.toNat 10 + 1 := by omega
          by_cases hip : i = pw.toNat
          · simp only [hip, ↓reduceIte]
            refine ⟨by rw [e3]; omega, ?_, ?_⟩
            · have h1 := hlast.1
              rw [← memW_rdN, h1, ← hmv']
              rdsimp [hip]
            · rw [← memW_rdN, hlast.1]; exact List.getElem_mem _
          · simp only [hip, ↓reduceIte]
            have hiL : i < L.length := by omega
            refine ⟨by rw [e3]; omega, ?_, ?_⟩
            · rdsimp []
            · rw [← memW_rdN, (hord i hiL).1]; exact List.getElem_mem hiL
        · dsimp only
          split_ifs <;> omega
      · intro c hc
        rdsimp []

end HtabDelValues

/-! ## 3. `bal_list_remove_idx` execution and `WorldStep` -/

theorem pairwise_disj_outside_slice {L1 mid L2 : List Ivl}
    (hpw : (L1 ++ mid ++ L2).Pairwise Disj)
    {x y : Ivl} (hx : x ∈ L1 ∨ x ∈ L2) (hy : y ∈ mid) :
    Disj x y := by
  have h12 := List.pairwise_append.1 hpw
  have h1 := List.pairwise_append.1 h12.1
  rcases hx with hx1 | hx2
  · exact h1.2.2 x hx1 y hy
  · exact disj_flip (h12.2.2 y (List.mem_append_right _ hy) x hx2)

/-- A BAL list `(l, esz)` embedded in `balObjects s = L1 ++ lstObjects s l esz ++ L2`
such that every BAL account record `(ad, 40)` and every OTHER BAL list header `(l', 24)` (`l' ≠ l`)
lies in `L1` or `L2`. -/
def BalListSlice {F : Type} (s : PanSemStateFiniteExact 64 F) (l esz : Nat) : Prop :=
  ∃ L1 L2,
    balObjects s = L1 ++ lstObjects s l esz ++ L2 ∧
    (∀ ad ∈ balRecords s, (ad, 40) ∈ L1 ∨ (ad, 40) ∈ L2) ∧
    (∀ ad ∈ balRecords s, ∀ k ∈ ([16, 24, 32] : List Nat),
      memW s (ad + k) ≠ 0 → memW s (ad + k) ≠ l →
      (memW s (ad + k), 24) ∈ L1 ∨ (memW s (ad + k), 24) ∈ L2) ∧
    (∀ ad ∈ balRecords s, ∀ l' ∈ htabValues s (memW s ad),
      l' ≠ 0 → l' ≠ l → (l', 24) ∈ L1 ∨ (l', 24) ∈ L2)

theorem lstObjects_head_mem {F : Type} (s : PanSemStateFiniteExact 64 F)
    {m esz : Nat} (hm : m ≠ 0) :
    (m, 24) ∈ lstObjects s m esz := by
  simp [lstObjects, hm]

theorem bal_chunk_mem_of_record {F : Type} (s : PanSemStateFiniteExact 64 F)
    {R : List Nat} {ad : Nat} (had : ad ∈ R) :
    let f := fun a : Nat => (a, 40) :: lstObjects s (memW s (a + 16)) 40 ++
      lstObjects s (memW s (a + 24)) 16 ++ lstObjects s (memW s (a + 32)) 24 ++
      (htabValues s (memW s a)).flatMap (fun x => lstObjects s x 40)
    (ad, 40) ∈ R.flatMap f ∧
    (∀ k ∈ ([16, 24, 32] : List Nat), memW s (ad + k) ≠ 0 →
      (memW s (ad + k), 24) ∈ R.flatMap f) ∧
    (∀ l' ∈ htabValues s (memW s ad), l' ≠ 0 → (l', 24) ∈ R.flatMap f) := by
  dsimp only
  refine ⟨List.mem_flatMap.2 ⟨ad, had, by simp⟩, ?_, ?_⟩
  · intro k hk hnz
    refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (lstObjects_head_mem s hnz))))
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (lstObjects_head_mem s hnz)))
    · exact List.mem_append_left _ (List.mem_append_right _ (lstObjects_head_mem s hnz))
  · intro l' hl' hnz
    exact List.mem_flatMap.2 ⟨ad, had, List.mem_append_right _
      (List.mem_flatMap.2 ⟨l', hl', lstObjects_head_mem s hnz⟩)⟩

theorem bal_list_slice_of_ad_field {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ad which esz : Nat} (had : ad ∈ balRecords s)
    (hwe : (which = 16 ∧ esz = 40) ∨ (which = 24 ∧ esz = 16) ∨ (which = 32 ∧ esz = 24)) :
    BalListSlice s (memW s (ad + which)) esz := by
  obtain ⟨R1, R2, hrec⟩ := List.append_of_mem had
  let f := fun a : Nat => (a, 40) :: lstObjects s (memW s (a + 16)) 40 ++
    lstObjects s (memW s (a + 24)) 16 ++ lstObjects s (memW s (a + 32)) 24 ++
    (htabValues s (memW s a)).flatMap (fun x => lstObjects s x 40)
  have hbal : balObjects s = R1.flatMap f ++ f ad ++ R2.flatMap f := by
    change (balRecords s).flatMap f = _
    rw [hrec]; simp [List.flatMap_append, List.flatMap_cons, List.append_assoc]
  have hmem_rec : ∀ a ∈ balRecords s, a ∈ R1 ∨ a = ad ∨ a ∈ R2 := by
    intro a ha; rw [hrec] at ha; simpa [or_assoc] using ha
  rcases hwe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨R1.flatMap f ++ [(ad, 40)],
      lstObjects s (memW s (ad + 24)) 16 ++ lstObjects s (memW s (ad + 32)) 24 ++
        (htabValues s (memW s ad)).flatMap (fun x => lstObjects s x 40) ++ R2.flatMap f,
      by rw [hbal]; simp [f, List.append_assoc], ?_, ?_, ?_⟩
    · intro a ha
      rcases hmem_rec a ha with h1 | rfl | h2
      · exact Or.inl (List.mem_append_left _ (bal_chunk_mem_of_record s h1).1)
      · exact Or.inl (List.mem_append_right _ (by simp))
      · exact Or.inr (List.mem_append_right _ (bal_chunk_mem_of_record s h2).1)
    · intro a ha k hk hnz hne
      rcases hmem_rec a ha with h1 | rfl | h2
      · exact Or.inl (List.mem_append_left _ ((bal_chunk_mem_of_record s h1).2.1 k hk hnz))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl
        · exact absurd rfl hne
        · exact Or.inr (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (lstObjects_head_mem s hnz))))
        · exact Or.inr (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_right _ (lstObjects_head_mem s hnz))))
      · exact Or.inr (List.mem_append_right _ ((bal_chunk_mem_of_record s h2).2.1 k hk hnz))
    · intro a ha l' hl' hnz _
      rcases hmem_rec a ha with h1 | rfl | h2
      · exact Or.inl (List.mem_append_left _ ((bal_chunk_mem_of_record s h1).2.2 l' hl' hnz))
      · exact Or.inr (List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.2 ⟨l', hl', lstObjects_head_mem s hnz⟩)))
      · exact Or.inr (List.mem_append_right _ ((bal_chunk_mem_of_record s h2).2.2 l' hl' hnz))
  · refine ⟨R1.flatMap f ++ [(ad, 40)] ++ lstObjects s (memW s (ad + 16)) 40,
      lstObjects s (memW s (ad + 32)) 24 ++
        (htabValues s (memW s ad)).flatMap (fun x => lstObjects s x 40) ++ R2.flatMap f,
      by rw [hbal]; simp [f, List.append_assoc], ?_, ?_, ?_⟩
    · intro a ha
      rcases hmem_rec a ha with h1 | rfl | h2
      · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ (bal_chunk_mem_of_record s h1).1))
      · exact Or.inl (List.mem_append_left _ (List.mem_append_right _ (by simp)))
      · exact Or.inr (List.mem_append_right _ (bal_chunk_mem_of_record s h2).1)
    · intro a ha k hk hnz hne
      rcases hmem_rec a ha with h1 | rfl | h2
      · exact Or.inl (List.mem_append_left _ (List.mem_append_left _
          ((bal_chunk_mem_of_record s h1).2.1 k hk hnz)))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl
        · exact Or.inl (List.mem_append_right _ (lstObjects_head_mem s hnz))
        · exact absurd rfl hne
        · exact Or.inr (List.mem_append_left _ (List.mem_append_left _ (lstObjects_head_mem s hnz)))
      · exact Or.inr (List.mem_append_right _ ((bal_chunk_mem_of_record s h2).2.1 k hk hnz))
    · intro a ha l' hl' hnz _
      rcases hmem_rec a ha with h1 | rfl | h2
      · exact Or.inl (List.mem_append_left _ (List.mem_append_left _
          ((bal_chunk_mem_of_record s h1).2.2 l' hl' hnz)))
      · exact Or.inr (List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.2 ⟨l', hl', lstObjects_head_mem s hnz⟩)))
      · exact Or.inr (List.mem_append_right _ ((bal_chunk_mem_of_record s h2).2.2 l' hl' hnz))
  · refine ⟨R1.flatMap f ++ [(ad, 40)] ++ lstObjects s (memW s (ad + 16)) 40 ++
      lstObjects s (memW s (ad + 24)) 16,
      (htabValues s (memW s ad)).flatMap (fun x => lstObjects s x 40) ++ R2.flatMap f,
      by rw [hbal]; simp [f, List.append_assoc], ?_, ?_, ?_⟩
    · intro a ha
      rcases hmem_rec a ha with h1 | rfl | h2
      · exact Or.inl (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (bal_chunk_mem_of_record s h1).1)))
      · exact Or.inl (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (by simp))))
      · exact Or.inr (List.mem_append_right _ (bal_chunk_mem_of_record s h2).1)
    · intro a ha k hk hnz hne
      rcases hmem_rec a ha with h1 | rfl | h2
      · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          ((bal_chunk_mem_of_record s h1).2.1 k hk hnz))))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl
        · exact Or.inl (List.mem_append_left _ (List.mem_append_right _ (lstObjects_head_mem s hnz)))
        · exact Or.inl (List.mem_append_right _ (lstObjects_head_mem s hnz))
        · exact absurd rfl hne
      · exact Or.inr (List.mem_append_right _ ((bal_chunk_mem_of_record s h2).2.1 k hk hnz))
    · intro a ha l' hl' hnz _
      rcases hmem_rec a ha with h1 | rfl | h2
      · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          ((bal_chunk_mem_of_record s h1).2.2 l' hl' hnz))))
      · exact Or.inr (List.mem_append_left _
          (List.mem_flatMap.2 ⟨l', hl', lstObjects_head_mem s hnz⟩))
      · exact Or.inr (List.mem_append_right _ ((bal_chunk_mem_of_record s h2).2.2 l' hl' hnz))

theorem bal_list_slice_of_stor_val {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ad l : Nat} (had : ad ∈ balRecords s) (hl : l ∈ htabValues s (memW s ad)) :
    BalListSlice s l 40 := by
  obtain ⟨R1, R2, hrec⟩ := List.append_of_mem had
  obtain ⟨V1, V2, hval⟩ := List.append_of_mem hl
  let f := fun a : Nat => (a, 40) :: lstObjects s (memW s (a + 16)) 40 ++
    lstObjects s (memW s (a + 24)) 16 ++ lstObjects s (memW s (a + 32)) 24 ++
    (htabValues s (memW s a)).flatMap (fun x => lstObjects s x 40)
  have hbal : balObjects s = R1.flatMap f ++ f ad ++ R2.flatMap f := by
    change (balRecords s).flatMap f = _
    rw [hrec]; simp [List.flatMap_append, List.flatMap_cons, List.append_assoc]
  have hmem_rec : ∀ a ∈ balRecords s, a ∈ R1 ∨ a = ad ∨ a ∈ R2 := by
    intro a ha; rw [hrec] at ha; simpa [or_assoc] using ha
  refine ⟨R1.flatMap f ++ [(ad, 40)] ++ lstObjects s (memW s (ad + 16)) 40 ++
      lstObjects s (memW s (ad + 24)) 16 ++ lstObjects s (memW s (ad + 32)) 24 ++
      V1.flatMap (fun x => lstObjects s x 40),
    V2.flatMap (fun x => lstObjects s x 40) ++ R2.flatMap f,
    by rw [hbal]; dsimp only [f]; rw [hval]
       simp [List.flatMap_append, List.flatMap_cons, List.append_assoc], ?_, ?_, ?_⟩
  · intro a ha
    rcases hmem_rec a ha with h1 | rfl | h2
    · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (bal_chunk_mem_of_record s h1).1)))))
    · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_right _ (by simp))))))
    · exact Or.inr (List.mem_append_right _ (bal_chunk_mem_of_record s h2).1)
  · intro a ha k hk hnz _
    rcases hmem_rec a ha with h1 | rfl | h2
    · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _
          ((bal_chunk_mem_of_record s h1).2.1 k hk hnz))))))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (lstObjects_head_mem s hnz)))))
      · exact Or.inl (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (lstObjects_head_mem s hnz))))
      · exact Or.inl (List.mem_append_left _
          (List.mem_append_right _ (lstObjects_head_mem s hnz)))
    · exact Or.inr (List.mem_append_right _ ((bal_chunk_mem_of_record s h2).2.1 k hk hnz))
  · intro a ha l' hl' hnz hne
    rcases hmem_rec a ha with h1 | rfl | h2
    · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _
          ((bal_chunk_mem_of_record s h1).2.2 l' hl' hnz))))))
    · rw [hval] at hl'
      rcases List.mem_append.1 hl' with hv1 | hv2
      · exact Or.inl (List.mem_append_right _
          (List.mem_flatMap.2 ⟨l', hv1, lstObjects_head_mem s hnz⟩))
      · rcases List.mem_cons.1 hv2 with rfl | hv2'
        · exact absurd rfl hne
        · exact Or.inr (List.mem_append_left _
            (List.mem_flatMap.2 ⟨l', hv2', lstObjects_head_mem s hnz⟩))
    · exact Or.inr (List.mem_append_right _ ((bal_chunk_mem_of_record s h2).2.2 l' hl' hnz))

theorem bal_list_slice_props {F : Type} {s : PanSemStateFiniteExact 64 F}
    {l esz : Nat} (hF : FixedTyped s)
    (hl_nz : l ≠ 0) (hesz : esz = 16 ∨ esz = 24 ∨ esz = 40) (hlst : LstOK s l)
    (hslice : BalListSlice s l esz) :
    (l, 24) ∈ fixedObjects s ∧
    (memW s l, esz * memW s (l + 16)) ∈ fixedObjects s ∧
    Disj (l, 24) (memW s l, esz * memW s (l + 16)) ∧
    (∀ ad ∈ balRecords s,
      Disj (ad, 40) (l, 24) ∧ Disj (ad, 40) (memW s l, esz * memW s (l + 16))) ∧
    (∀ ad ∈ balRecords s, ∀ k ∈ ([16, 24, 32] : List Nat),
      memW s (ad + k) ≠ 0 → memW s (ad + k) ≠ l →
      Disj (memW s (ad + k), 24) (l, 24) ∧
      Disj (memW s (ad + k), 24) (memW s l, esz * memW s (l + 16))) ∧
    (∀ ad ∈ balRecords s, ∀ l' ∈ htabValues s (memW s ad),
      l' ≠ 0 → l' ≠ l →
      Disj (l', 24) (l, 24) ∧ Disj (l', 24) (memW s l, esz * memW s (l + 16))) := by
  have hesz_pos : 0 < esz := by rcases hesz with rfl | rfl | rfl <;> decide
  have hpos : esz * memW s (l + 16) ≠ 0 :=
    ne_of_gt (Nat.mul_pos hesz_pos (by have := hlst.1; omega))
  have hlst_eq : lstObjects s l esz = [(l, 24), (memW s l, esz * memW s (l + 16))] := by
    simp [lstObjects, hl_nz, hpos]
  obtain ⟨L1, L2, hbal_eq, had_lr, hfk_lr, hst_lr⟩ := hslice
  have hl_bal : (l, 24) ∈ balObjects s := by rw [hbal_eq, hlst_eq]; simp
  have hp_bal : (memW s l, esz * memW s (l + 16)) ∈ balObjects s := by rw [hbal_eq, hlst_eq]; simp
  have hpw_bal : (balObjects s).Pairwise Disj := by
    have hpw := hF.2
    unfold fixedObjects at hpw
    exact (List.pairwise_append.1 hpw).2.1
  rw [hbal_eq, hlst_eq] at hpw_bal
  have hpw_mid : ([(l, 24), (memW s l, esz * memW s (l + 16))]).Pairwise Disj :=
    (List.pairwise_append.1 (List.pairwise_append.1 hpw_bal).1).2.1
  refine ⟨List.mem_append.2 (Or.inr hl_bal), List.mem_append.2 (Or.inr hp_bal),
    (List.pairwise_cons.1 hpw_mid).1 _ (List.mem_singleton.2 rfl), ?_, ?_, ?_⟩
  · intro ad had
    exact ⟨pairwise_disj_outside_slice hpw_bal (had_lr ad had) (by simp),
           pairwise_disj_outside_slice hpw_bal (had_lr ad had) (by simp)⟩
  · intro ad had k hk hnz hne
    exact ⟨pairwise_disj_outside_slice hpw_bal (hfk_lr ad had k hk hnz hne) (by simp),
           pairwise_disj_outside_slice hpw_bal (hfk_lr ad had k hk hnz hne) (by simp)⟩
  · intro ad had l' hl' hnz hne
    exact ⟨pairwise_disj_outside_slice hpw_bal (hst_lr ad had l' hl' hnz hne) (by simp),
           pairwise_disj_outside_slice hpw_bal (hst_lr ad had l' hl' hnz hne) (by simp)⟩

theorem bal_list_store_len_and_arr_worldStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {l esz n' : Nat}
    (hW : WorldOK s)
    (hl_nz : l ≠ 0) (hesz : esz = 16 ∨ esz = 24 ∨ esz = 40)
    (hslice_all : ∀ S Nd, WorldTypedWith s S Nd → LstOK s l ∧ BalListSlice s l esz)
    (heff : M11.ByteRegionEffect s post
      [(l + 8, 8), (memW s l, esz * memW s (l + 16))])
    (hn'_le : n' ≤ memW s (l + 16))
    (hl8_post : memW post (l + 8) = n') :
    WorldStep (fun _ => []) [] stdKeep NoExtra s r post := by
  have hAs := hW.1
  have hinv_post : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAs.1
  have hAp : ArenaReady post := ⟨hinv_post, arenaOK_congr heff.globals hAs.2⟩
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  have hhp : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hag : AllocatorGrows s post := ⟨hhp, hsp⟩
  have hG : GlobalsKept [] s post := fun _ _ => by rw [heff.globals]
  have hgs : InitECandidate.Solver.Wave8Contracts.M08.WorldGlobalsSame s post :=
    InitECandidate.Solver.Wave8Contracts.M08.worldGlobalsSame_of_kept hG (by simp)
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  obtain ⟨hlst0, hslice0⟩ := hslice_all S0 Nd0 hWT0
  obtain ⟨hl_fix0, hp_fix0, hdj_lp0, _, _, _⟩ :=
    bal_list_slice_props hWT0.2.2.1 hl_nz hesz hlst0 hslice0
  have hesz_pos : 0 < esz := by rcases hesz with rfl | rfl | rfl <;> decide
  have hpos_arr : esz * memW s (l + 16) ≠ 0 :=
    ne_of_gt (Nat.mul_pos hesz_pos (by have := hlst0.1; omega))
  rcases hWT0.2.2.1.1 _ hl_fix0 with h0 | ⟨hal_l, hw_l⟩
  · simp at h0
  rcases hWT0.2.2.1.1 _ hp_fix0 with h0 | ⟨hal_p, _⟩
  · exact absurd h0 hpos_arr
  have hl_hi : l + 24 ≤ 2 ^ 64 :=
    (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_l).2
  have hunhit_of_disj : ∀ i : Ivl, Disj i (l, 24) → Disj i (memW s l, esz * memW s (l + 16)) →
      M08IvlUnhit s post i := by
    intro i hdj1 hdj2 a ha8 hi1 hi2
    apply heff.cell_frame a
    intro x hx hch
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain ⟨hc1, hc2⟩ := hch
    rcases hx with rfl | rfl
    · dsimp only at hc1 hc2
      rcases hdj1 with d | d | d | d <;> omega
    · dsimp only at hc1 hc2
      rcases hdj2 with d | d | d | d <;> omega
  have hRK : RecordsKept (fun _ => []) stdKeep s post := by
    intro ⟨rec_nm, rec_ks⟩ hrec hgnz k hk _
    have hrec_sz : ∃ sz, (rec_nm, sz) ∈ typedRecords ∧ sz ≠ 0 ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [stdKeep, M13.stdKeep, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrec
      rcases hrec with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨40, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨80, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨72, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨88, by decide, by decide, ?_⟩; simp at hk; omega
    obtain ⟨sz, htr, hsz_nz, hk8, hksz⟩ := hrec_sz
    have hmf := M11.typedRec_in_fixedObjects s htr
    simp only [hgnz, ↓reduceIte] at hmf
    have hgb_mem : (globN s rec_nm, sz) ∈
        (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++
        [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
        blockOutObjects s := by
      apply List.mem_append_left; apply List.mem_append_left
      have hr_gb : (rec_nm, sz) ∈ globalBuffers :=
        InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_globalBuffers htr
      have hm : (globN s rec_nm, if globN s rec_nm = 0 then 0 else sz) ∈
          globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2) :=
        List.mem_map.2 ⟨(rec_nm, sz), hr_gb, rfl⟩
      rwa [if_neg hgnz] at hm
    have hpw_top := List.pairwise_append.1 hWT0.2.2.1.2
    have hl_bal0 : (l, 24) ∈ balObjects s := by
      obtain ⟨L1, L2, hb, _⟩ := hslice0; rw [hb]; simp [lstObjects, hl_nz]
    have hp_bal0 : (memW s l, esz * memW s (l + 16)) ∈ balObjects s := by
      obtain ⟨L1, L2, hb, _⟩ := hslice0; rw [hb]; simp [lstObjects, hl_nz, hpos_arr]
    have hdj_l : Disj (globN s rec_nm, sz) (l, 24) := hpw_top.2.2 _ hgb_mem _ hl_bal0
    have hdj_p : Disj (globN s rec_nm, sz) (memW s l, esz * memW s (l + 16)) :=
      hpw_top.2.2 _ hgb_mem _ hp_bal0
    rcases hWT0.2.2.1.1 _ hmf with h0 | ⟨hal_r, hw_r⟩
    · exact absurd h0 hsz_nz
    have hhi_r := (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_r).2
    have hg8 : (globN s rec_nm) % 8 = 0 := hw_r.1
    change memW post (globN s rec_nm + k) = memW s (globN s rec_nm + k)
    exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit
      (hunhit_of_disj _ hdj_l hdj_p) (by omega) hhi_r ⟨by omega, by omega⟩
  refine ⟨hAp, hhp, hG, hRK, fun S Nd hWT _ => ?_⟩
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  obtain ⟨hlst, hslice⟩ := hslice_all S Nd ⟨hT, hJ, hF, hTr⟩
  obtain ⟨hl_fix, hp_fix, hdj_lp, had_dj, hfk_dj, hst_dj⟩ :=
    bal_list_slice_props hF hl_nz hesz hlst hslice
  have hl_bal : (l, 24) ∈ balObjects s := by
    obtain ⟨L1, L2, hb, _⟩ := hslice; rw [hb]; simp [lstObjects, hl_nz]
  have hp_bal : (memW s l, esz * memW s (l + 16)) ∈ balObjects s := by
    obtain ⟨L1, L2, hb, _⟩ := hslice; rw [hb]; simp [lstObjects, hl_nz, hpos_arr]
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, M08IvlUnhit s post i := fun t ht i hi =>
    hunhit_of_disj i (((hT.2.1 t ht).2 i hi).2 _ hl_fix) (((hT.2.1 t ht).2 i hi).2 _ hp_fix)
  have hu_prefix : ∀ i ∈
      (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++
      [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
      blockOutObjects s, M08IvlUnhit s post i := fun i hi =>
    hunhit_of_disj i ((List.pairwise_append.1 hF.2).2.2 i hi _ hl_bal)
      ((List.pairwise_append.1 hF.2).2.2 i hi _ hp_bal)
  have hmem_gb_prefix : ∀ (nm : String) (sz : Nat), (nm, sz) ∈ globalBuffers → globN s nm ≠ 0 →
      (globN s nm, sz) ∈
        (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++
        [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
        blockOutObjects s := fun nm sz hgb hnz => by
    apply List.mem_append_left; apply List.mem_append_left
    have hm : (globN s nm, if globN s nm = 0 then 0 else sz) ∈
        globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2) :=
      List.mem_map.2 ⟨(nm, sz), hgb, rfl⟩
    rwa [if_neg hnz] at hm
  have hu_ws : globN s "ws" ≠ 0 → M08IvlUnhit s post (globN s "ws", 40) := fun hnz =>
    hu_prefix _ (hmem_gb_prefix "ws" 40 (by decide) hnz)
  have hu_bs : globN s "bs" ≠ 0 → M08IvlUnhit s post (globN s "bs", 80) := fun hnz =>
    hu_prefix _ (hmem_gb_prefix "bs" 80 (by decide) hnz)
  have hu_ts : globN s "ts" ≠ 0 → M08IvlUnhit s post (globN s "ts", 72) := fun hnz =>
    hu_prefix _ (hmem_gb_prefix "ts" 72 (by decide) hnz)
  have hu_bo : globN s "bo" ≠ 0 → M08IvlUnhit s post (globN s "bo", 88) := fun hnz =>
    hu_prefix _ (hmem_gb_prefix "bo" 88 (by decide) hnz)
  have hu_jr : globN s "journal_cap" ≠ 0 →
      M08IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := fun hnz =>
    hu_prefix _ (List.mem_append_left _ (List.mem_append_right _ (by simp [hnz])))
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → M08IvlUnhit s post i := fun i hi _ =>
    hu_prefix _ (List.mem_append_right _ hi)
  have hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 :=
    InitECandidate.Solver.Wave8Contracts.M08.mem0_8_16_eq_of_domain_writes
      (fun a hne => Classical.byContradiction fun hna => hne (heff.out_dom a hna)) hAs.1
  have hl_w0 : memW post l = memW s l := by
    have hl8 : l % 8 = 0 := hw_l.1
    have hl_lt : l < 2 ^ 64 := by omega
    have hm := heff.cell_frame (BitVec.ofNat 64 l) (fun x hx hch => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨hc1, hc2⟩ := hch
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl_lt] at hc1 hc2
      rcases hx with rfl | rfl
      · dsimp only at hc1 hc2; omega
      · dsimp only at hc1 hc2; rcases hdj_lp with d | d | d | d <;> omega)
    unfold memW; rw [hm]
  have hl_w16 : memW post (l + 16) = memW s (l + 16) := by
    have hl8 : l % 8 = 0 := hw_l.1
    have hl_lt : l + 16 < 2 ^ 64 := by omega
    have hm := heff.cell_frame (BitVec.ofNat 64 (l + 16)) (fun x hx hch => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨hc1, hc2⟩ := hch
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl_lt] at hc1 hc2
      rcases hx with rfl | rfl
      · dsimp only at hc1 hc2; omega
      · dsimp only at hc1 hc2; rcases hdj_lp with d | d | d | d <;> omega)
    unfold memW; rw [hm]
  have hlst_l_post : LstOK post l := by
    unfold LstOK
    rw [hl8_post, hl_w16]
    exact ⟨hlst.1, hn'_le⟩
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" :=
    hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  have hrecs_bal : balRecords post = balRecords s :=
    InitECandidate.Solver.Wave8Contracts.M08.balRecords_eq_of_unhit hT hba_g (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_tab _ hm)
  have hlst_hdr_unhit_eq : ∀ (m esz_m : Nat), m ≠ 0 → (m, 24) ∈ fixedObjects s →
      Disj (m, 24) (l, 24) → Disj (m, 24) (memW s l, esz * memW s (l + 16)) →
      lstObjects post m esz_m = lstObjects s m esz_m ∧ (LstOK s m → LstOK post m) := by
    intro m esz_m hm_nz hm_fix hdj1 hdj2
    rcases hF.1 _ hm_fix with h0 | ⟨hal_m, hw_m⟩
    · simp at h0
    have hhi_m := (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_m).2
    have hm8 : m % 8 = 0 := hw_m.1
    have hum := hunhit_of_disj _ hdj1 hdj2
    have hw0 : memW post m = memW s m := by
      simpa using InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hum (by omega) hhi_m ⟨by omega, by omega⟩
    have hw8 : memW post (m + 8) = memW s (m + 8) :=
      InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hum (by omega) hhi_m ⟨by omega, by omega⟩
    have hw16 : memW post (m + 16) = memW s (m + 16) :=
      InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hum (by omega) hhi_m ⟨by omega, by omega⟩
    refine ⟨by simp [lstObjects, hm_nz, hw0, hw16], fun hm_ok => ?_⟩
    unfold LstOK at hm_ok ⊢; rw [hw8, hw16]; exact hm_ok
  have hlst_any_eq : ∀ (m esz_m : Nat),
      (m ≠ 0 → m ≠ l → (m, 24) ∈ fixedObjects s ∧
        Disj (m, 24) (l, 24) ∧ Disj (m, 24) (memW s l, esz * memW s (l + 16))) →
      lstObjects post m esz_m = lstObjects s m esz_m ∧ (LstOK s m → LstOK post m) := by
    intro m esz_m hcond
    by_cases hm0_z : m = 0
    · subst hm0_z
      refine ⟨by simp [lstObjects], fun hm_ok => ?_⟩
      unfold LstOK at hm_ok ⊢; rw [hm0.2.1, hm0.2.2]; exact hm_ok
    · by_cases hml : m = l
      · subst hml
        exact ⟨by simp [lstObjects, hl_nz, hl_w0, hl_w16], fun _ => hlst_l_post⟩
      · obtain ⟨hm_fix, hdj1, hdj2⟩ := hcond hm0_z hml
        exact hlst_hdr_unhit_eq m esz_m hm0_z hm_fix hdj1 hdj2
  have had_all : ∀ ad ∈ balRecords s,
      (∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off)) ∧
      htabValues post (memW s ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW s (ad + k))) ∧
      (∀ l' ∈ htabValues s (memW s ad), LstOK post l') ∧
      (ad, 40) :: lstObjects post (memW post (ad + 16)) 40 ++
        lstObjects post (memW post (ad + 24)) 16 ++ lstObjects post (memW post (ad + 32)) 24 ++
        (htabValues post (memW post ad)).flatMap (fun x => lstObjects post x 40) =
      (ad, 40) :: lstObjects s (memW s (ad + 16)) 40 ++
        lstObjects s (memW s (ad + 24)) 16 ++ lstObjects s (memW s (ad + 32)) 24 ++
        (htabValues s (memW s ad)).flatMap (fun x => lstObjects s x 40) := by
    intro ad had
    have had_fix : (ad, 40) ∈ fixedObjects s :=
      List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨ad, had, by simp⟩))
    rcases hF.1 _ had_fix with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_ad).2
    have had8 : ad % 8 = 0 := hw_ad.1
    have hu_ad := hunhit_of_disj _ (had_dj ad had).1 (had_dj ad had).2
    have hoff : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off) := by
      intro off hoff_m
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff_m
      rcases hoff_m with rfl | rfl | rfl | rfl | rfl <;>
        exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_ad (by omega) hhi_ad ⟨by omega, by omega⟩
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have hvals_ad : htabValues post (memW s ad) = htabValues s (memW s ad) :=
      InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ had_T.1).1 (hu_tab _ had_T.1)
    have hfk_eq : ∀ k ∈ ([16, 24, 32] : List Nat), ∀ esz_k,
        lstObjects post (memW s (ad + k)) esz_k = lstObjects s (memW s (ad + k)) esz_k ∧
        LstOK post (memW s (ad + k)) := by
      intro k hk esz_k
      have hp := hlst_any_eq (memW s (ad + k)) esz_k (fun hnz hne => by
        have hmem_bal : (memW s (ad + k), 24) ∈ balObjects s :=
          (bal_chunk_mem_of_record s had).2.1 k hk hnz
        exact ⟨List.mem_append.2 (Or.inr hmem_bal), (hfk_dj ad had k hk hnz hne).1,
          (hfk_dj ad had k hk hnz hne).2⟩)
      exact ⟨hp.1, hp.2 (had_T.2.2.1 k hk)⟩
    have hst_eq : ∀ l' ∈ htabValues s (memW s ad),
        lstObjects post l' 40 = lstObjects s l' 40 ∧ LstOK post l' := by
      intro l' hl'
      have hp := hlst_any_eq l' 40 (fun hnz hne => by
        have hmem_bal : (l', 24) ∈ balObjects s :=
          (bal_chunk_mem_of_record s had).2.2 l' hl' hnz
        exact ⟨List.mem_append.2 (Or.inr hmem_bal), (hst_dj ad had l' hl' hnz hne).1,
          (hst_dj ad had l' hl' hnz hne).2⟩)
      exact ⟨hp.1, hp.2 (had_T.2.2.2 l' hl')⟩
    have hw0_ad : memW post ad = memW s ad := by simpa using hoff 0 (by simp)
    have hw16_ad := hoff 16 (by simp)
    have hw24_ad := hoff 24 (by simp)
    have hw32_ad := hoff 32 (by simp)
    refine ⟨hoff, hvals_ad, fun k hk => (hfk_eq k hk 40).2, fun l' hl' => (hst_eq l' hl').2, ?_⟩
    rw [hw0_ad, hw16_ad, hw24_ad, hw32_ad, hvals_ad,
      (hfk_eq 16 (by simp) 40).1, (hfk_eq 24 (by simp) 16).1, (hfk_eq 32 (by simp) 24).1]
    congr 1
    exact List.flatMap_congr fun x hx => (hst_eq x hx).1
  have hbal_eq : balObjects post = balObjects s := by
    unfold balObjects
    rw [hrecs_bal]
    exact List.flatMap_congr fun ad had => (had_all ad had).2.2.2.2
  have hbo_g : globN post "bo" = globN s "bo" := hgs.1 ("bo", 88) (by simp [globalBuffers])
  have hws_g : globN post "ws" = globN s "ws" := hgs.1 ("ws", 40) (by simp [globalBuffers])
  have hbs_g : globN post "bs" = globN s "bs" := hgs.1 ("bs", 80) (by simp [globalBuffers])
  have hts_g : globN post "ts" = globN s "ts" := hgs.1 ("ts", 72) (by simp [globalBuffers])
  have hbia_g : globN post "bal_idx_accts" = globN s "bal_idx_accts" :=
    hgs.2.1 "bal_idx_accts" (by simp [globalTableRoots])
  have hbis_g : globN post "bal_idx_stor" = globN s "bal_idx_stor" :=
    hgs.2.1 "bal_idx_stor" (by simp [globalTableRoots])
  have htr_ws : ("ws", 40) ∈ InitECandidate.Solver.Wave8Contracts.M08.typedRecords := by decide
  have htr_bs : ("bs", 80) ∈ InitECandidate.Solver.Wave8Contracts.M08.typedRecords := by decide
  have htr_ts : ("ts", 72) ∈ InitECandidate.Solver.Wave8Contracts.M08.typedRecords := by decide
  have htr_bo : ("bo", 88) ∈ InitECandidate.Solver.Wave8Contracts.M08.typedRecords := by decide
  have hbo_words : globN s "bo" ≠ 0 → ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := fun hnz k hk => by
    have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    simpa [hbo_g] using InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
      hAs.2 hF "bo" 88 htr_bo hbo_g hnz (hu_bo hnz) hk_in.1 hk_in.2
  have hbo_part := InitECandidate.Solver.Wave8Contracts.M08.blockOutObjects_eq_of_bo_unhit
    hAs.2 hF hbo_g hT.2.2.2.2.2.2.2.2.2.2.1
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
  have hfix_eq := InitECandidate.Solver.Wave8Contracts.M08.fixedObjects_eq_of_parts
    hgs hbo_part.1 hbal_eq
  have hF_post := InitECandidate.Solver.Wave8Contracts.M08.fixedTyped_transfer
    hAs.1 hAp.1 hag hF hfix_eq
  have hjr_part := InitECandidate.Solver.Wave8Contracts.M08.journalRoleSlots_eq_of_unhit
    hAs.1 hAp.1 hAs.2 hag (fun _ hx => hx) hJ hF hgs hu_ts hu_jr
  have hwrs_eq : worldRoleSlots post = worldRoleSlots s := by
    have hrec_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] =
        recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
      unfold recRoles
      by_cases h : globN s "ws" = 0
      · simp [hws_g, h]
      · have hw16 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ws" 40 htr_ws hws_g h (hu_ws h) (k := 16) (by omega) (by omega)
        have hw32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ws" 40 htr_ws hws_g h (hu_ws h) (k := 32) (by omega) (by omega)
        simp only [hws_g] at hw16 hw32 ⊢
        simp [h, hw16, hw32]
    have hrec_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
        (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
        recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
        (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
      unfold recRoles
      by_cases h : globN s "bs" = 0
      · simp [hbs_g, h]
      · simp only [hbs_g, h, ↓reduceIte]
        apply List.map_congr_left
        intro ⟨k, r0⟩ hkr
        have hk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
          rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        have hw := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "bs" 80 htr_bs hbs_g h (hu_bs h) hk.1 hk.2
        simp only [hbs_g] at hw; simp [hw]
    have hrec_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
        recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
      unfold recRoles
      by_cases h : globN s "ts" = 0
      · simp [hts_g, h]
      · simp only [hts_g, h, ↓reduceIte]
        apply List.map_congr_left
        intro ⟨k, r0⟩ hkr
        have hk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
          rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        have hw := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ts" 72 htr_ts hts_g h (hu_ts h) hk.1 hk.2
        simp only [hts_g] at hw; simp [hw]
    have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
      unfold nestRoles
      by_cases h : globN s "bs" = 0
      · simp [hbs_g, h]
      · have hw32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "bs" 80 htr_bs hbs_g h (hu_bs h) (k := 32) (by omega) (by omega)
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
      · have hw32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ts" 72 htr_ts hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
        simp only [hts_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
        by_cases h32 : memW s (globN s "ts" + 32) = 0
        · simp [h32]
        · simp only [h32, ↓reduceIte]
          have hmS : memW s (globN s "ts" + 32) ∈ S := by
            rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) h with h0 | hm
            · exact absurd h0 h32
            · exact hm
          rw [InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
    unfold worldRoleSlots
    rw [hrec_ws, hrec_bs, hrec_ts, hba_g, hbia_g, hbis_g, hnest_bs, hnest_ts, hrecs_bal]
    congr 1; congr 1
    apply List.flatMap_congr
    intro ad had
    have had0 : memW post ad = memW s ad := by simpa using (had_all ad had).1 0 (by simp)
    have had8 : memW post (ad + 8) = memW s (ad + 8) := (had_all ad had).1 8 (by simp)
    rw [had0, had8]
  have hu_nd_rec : ∀ n ∈ Nd, M08IvlUnhit s post (nodeIvl s n) := fun n hn => by
    have hne_mem : nodeIvl s n ∈ nodeExtents s Nd :=
      List.mem_flatMap.2 ⟨n, hn, List.mem_cons_self⟩
    exact hunhit_of_disj _ ((hTr.2.1 _ hne_mem).2 _ hl_fix) ((hTr.2.1 _ hne_mem).2 _ hp_fix)
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    have hnp_mem : nodePath s n ∈ nodeExtents s Nd :=
      List.mem_flatMap.2 ⟨n, hn, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)⟩
    have hnp_eq : nodePath s n = (memW s (n + 32), memW s (n + 40)) := by
      simp [nodePath, h12, hlen0]
    have hdj_l : Disj (memW s (n + 32), memW s (n + 40)) (l, 24) := by
      rw [← hnp_eq]; exact (hTr.2.1 _ hnp_mem).2 _ hl_fix
    have hdj_p : Disj (memW s (n + 32), memW s (n + 40)) (memW s l, esz * memW s (l + 16)) := by
      rw [← hnp_eq]; exact (hTr.2.1 _ hnp_mem).2 _ hp_fix
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, _, hin_p, _⟩
    · exact absurd h0 hlen0
    have hlim264 : heapLimit ≤ 2 ^ 64 := by decide
    have hbk_lt : memW s (n + 32) + k < 2 ^ 64 := by
      have := hin_p.2; dsimp at this; omega
    exact heff.byte_frame (memW s (n + 32) + k) hbk_lt (fun x hx hbi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨hb1, hb2⟩ := hbi
      rcases hx with rfl | rfl
      · dsimp only at hb1 hb2; rcases hdj_l with d | d | d | d <;> omega
      · dsimp only at hb1 hb2; rcases hdj_p with d | d | d | d <;> omega)
  have hnd_part := InitECandidate.Solver.Wave8Contracts.M08.nodeHeap_congr_bytes
    hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_byte
  have htab_fp_hdr : ∀ t ∈ S, (∀ k, k < 11 → hdr post t k = hdr s t k) ∧
      htabFootprint post t = htabFootprint s t := by
    have h264_he : heapEnd ≤ 2 ^ 64 := by decide
    intro t ht
    have hwf := (hT.2.1 t ht).1
    have ht_fp : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have hhi : t + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; dsimp at this; omega
    exact InitECandidate.Solver.Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit
      ht8 hhi (hu_tab t ht _ ht_fp)
  have hflat_fp : S.flatMap (htabFootprint post) = S.flatMap (htabFootprint s) :=
    List.flatMap_congr fun t ht => (htab_fp_hdr t ht).2
  have howned_eq : M13.worldOwned post S Nd = M13.worldOwned s S Nd := by
    change S.flatMap (htabFootprint post) ++ fixedObjects post ++ nodeExtents post Nd =
      S.flatMap (htabFootprint s) ++ fixedObjects s ++ nodeExtents s Nd
    rw [hflat_fp, hfix_eq, hnd_part.2]
  have hT_post : TablesTyped post S := by
    obtain ⟨hndS, hTt, hTp, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, hboT, hroles⟩ := hT
    refine ⟨hndS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_part.2, ?_⟩
    · intro t ht
      rw [(htab_fp_hdr t ht).2, hfix_eq]
      exact ⟨InitECandidate.Solver.Wave8Contracts.M08.htabWF_congr_unhit
          hAs.1 hAp.1 (hTt t ht).1 (hu_tab t ht),
        fun i hi => ⟨hag.allocated ((hTt t ht).2 i hi).1, ((hTt t ht).2 i hi).2⟩⟩
    · intro t ht u hu_mem hne
      rw [(htab_fp_hdr t ht).2, (htab_fp_hdr u hu_mem).2]
      exact hTp t ht u hu_mem hne
    · intro k hk hnz
      rw [hws_g] at hnz
      have hwk : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ws" 40 htr_ws hws_g hnz (hu_ws hnz) hwk.1 hwk.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [hbs_g] at hnz
      have hbk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "bs" 80 htr_bs hbs_g hnz (hu_bs hnz) hbk.1 hbk.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [hts_g] at hnz
      have htk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ts" 72 htr_ts hts_g hnz (hu_ts hnz) htk.1 htk.2]
      exact htsR k hk hnz
    · intro g hg; rw [hgs.2.1 g hg]; exact hgR g hg
    · intro hnz hm
      rw [hbs_g] at hnz
      have hw32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "bs" 80 htr_bs hbs_g hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact InitECandidate.Solver.Wave8Contracts.M08.htabValuesIn_congr_unhit
        (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (hbsN hnz hm)
    · intro hnz hm
      rw [hts_g] at hnz
      have hw32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "ts" 72 htr_ts hts_g hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact InitECandidate.Solver.Wave8Contracts.M08.htabValuesIn_congr_unhit
        (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (htsN hnz hm)
    · intro ad had
      rw [hrecs_bal] at had
      have hp := had_all ad had
      have h0 : memW post ad = memW s ad := by simpa using hp.1 0 (by simp)
      have h8 : memW post (ad + 8) = memW s (ad + 8) := hp.1 8 (by simp)
      have had_old := hbalT ad had
      refine ⟨by rw [h0]; exact had_old.1, by rw [h8]; exact had_old.2.1, ?_, ?_⟩
      · intro k hk
        have hk5 : k ∈ ([0, 8, 16, 24, 32] : List Nat) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
          rcases hk with rfl | rfl | rfl <;> simp
        rw [hp.1 k hk5]; exact hp.2.2.1 k hk
      · intro l' hl'; rw [h0, hp.2.1] at hl'; exact hp.2.2.2.1 l' hl'
    · unfold RolesOK at hroles ⊢
      rw [hwrs_eq, hjr_part.1]
      refine ⟨fun a ha => ?_, hroles.2.1, hroles.2.2⟩
      obtain ⟨haS, hak⟩ := hroles.1 a ha
      rw [(htab_fp_hdr a.1 haS).1 0 (by omega)]
      exact ⟨haS, hak⟩
  have hTr_post : TriesTypedWith post S Nd := by
    refine ⟨hnd_part.1, ?_, ?_⟩
    · intro o ho
      rw [hnd_part.2] at ho; rw [hfix_eq]
      refine ⟨fun t ht i hi => ?_, (hTr.2.1 o ho).2⟩
      rw [(htab_fp_hdr t ht).2] at hi
      exact (hTr.2.1 o ho).1 t ht i hi
    · intro hnz
      rw [hws_g] at hnz
      have hw24 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "ws" 40 htr_ws hws_g hnz (hu_ws hnz) (k := 24) (by omega) (by omega)
      have hw32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "ws" 40 htr_ws hws_g hnz (hu_ws hnz) (k := 32) (by omega) (by omega)
      rw [hw24, hw32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hnz
      refine ⟨hr24, fun hm i hi => ?_⟩
      have hwf32 := (hT.2.1 _ hm).1
      have hu32 := hu_tab _ hm
      have hh32 := htab_fp_hdr _ hm
      rw [hh32.1 3 (by omega)] at hi
      have hvals := InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit hwf32 hu32
      have hget : (htabValues post (memW s (globN s "ws" + 32)))[i]? =
          (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hh32.1 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]
      exact hr32 hm i hi
  have hfr : FrameOutside s post (worldOwned s S Nd ++ ([] : List Ivl) ++ [freeGap s]) (heapFree s) := by
    intro a ha _
    apply heff.cell_frame a
    intro x hx hch
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain ⟨hc1, hc2⟩ := hch
    have hl_ow : (l, 24) ∈ worldOwned s S Nd ++ ([] : List Ivl) ++ [freeGap s] := by
      apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_append_left _ (List.mem_append_right _ hl_fix)
    have hp_ow : (memW s l, esz * memW s (l + 16)) ∈
        worldOwned s S Nd ++ ([] : List Ivl) ++ [freeGap s] := by
      apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_append_left _ (List.mem_append_right _ hp_fix)
    rcases hx with rfl | rfl
    · exact ha (l, 24) hl_ow ⟨by dsimp only at hc1 ⊢; omega, by dsimp only at hc2 ⊢; omega⟩
    · exact ha _ hp_ow ⟨hc1, hc2⟩
  refine ⟨S, Nd, fun _ hx => hx, ⟨hT_post, hjr_part.2, hF_post, hTr_post⟩, ?_, hfr, trivial⟩
  rw [howned_eq]
  exact fun o ho => Or.inr (Or.inl ⟨o, ho, le_rfl, le_rfl⟩)

/-! ## 4. `bal_list_remove_idx` execution & `wk_bal_remove_change` -/

abbrev balRemoveLoopBody : ProgHOL 64 :=
  .seq
    (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "p"),
        .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
        (.var .local (ofString "idx")))
      (.seq
        (.ite (.cmp .notEqual (.var .local (ofString "i"))
            (.op .sub [.var .local (ofString "n"), .const 1#64]))
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "p"),
               .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]],
             .op .add [.var .local (ofString "p"),
               .panop .mul [.op .sub [.var .local (ofString "n"), .const 1#64],
                 .var .local (ofString "esz")]],
             .var .local (ofString "esz")])
          .skip)
        (.seq
          (.store (.op .add [.var .local (ofString "l"), .const 8#64])
            (.op .sub [.var .local (ofString "n"), .const 1#64]))
          (.return (.const 0#64))))
      .skip)
    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))

abbrev balRemoveLoop : ProgHOL 64 :=
  .while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n")))
    balRemoveLoopBody

theorem bal_remove_loop_eval {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (lw nw pw eszw idxw : BitVec 64)
    (hcode0 : s0.code = originalRuntimeCode)
    (hma0 : s0.memaddrs = ordinaryDomain)
    (hl_al : lw.toNat % 8 = 0 ∧ sourceBase ≤ lw.toNat ∧ lw.toNat + 24 ≤ heapEnd)
    (hp_al : pw.toNat % 8 = 0 ∧ sourceBase ≤ pw.toNat ∧
      pw.toNat + eszw.toNat * memW s0 (lw.toNat + 16) ≤ heapEnd)
    (hesz : eszw.toNat = 16 ∨ eszw.toNat = 24 ∨ eszw.toNat = 40)
    (hp_eq : pw.toNat = memW s0 lw.toNat)
    (hn_le : nw.toNat ≤ memW s0 (lw.toNat + 16)) :
    ∀ (k : Nat) (t : PanSemStateFiniteExact 64 F) (iw : BitVec 64),
      t.clock = k →
      t = { s0 with locals := t.locals, clock := k } →
      iw.toNat ≤ nw.toNat →
      t.locals.lookup (ofString "l") = some (.val (.word lw)) →
      t.locals.lookup (ofString "n") = some (.val (.word nw)) →
      t.locals.lookup (ofString "p") = some (.val (.word pw)) →
      t.locals.lookup (ofString "esz") = some (.val (.word eszw)) →
      t.locals.lookup (ofString "idx") = some (.val (.word idxw)) →
      t.locals.lookup (ofString "i") = some (.val (.word iw)) →
      (evaluateHOLFiniteState t balRemoveLoop).1 ≠ some .timeOut →
        ((evaluateHOLFiniteState t balRemoveLoop).1 = none →
          (evaluateHOLFiniteState t balRemoveLoop).2 =
            { s0 with
              locals := (evaluateHOLFiniteState t balRemoveLoop).2.locals,
              clock := (evaluateHOLFiniteState t balRemoveLoop).2.clock }) ∧
        (∀ rv, (evaluateHOLFiniteState t balRemoveLoop).1 = some (.returned rv) →
          rv = .val (.word 0) ∧ 1 ≤ nw.toNat ∧
          M11.ByteRegionEffect s0 (evaluateHOLFiniteState t balRemoveLoop).2
            [(lw.toNat + 8, 8), (memW s0 lw.toNat, eszw.toNat * memW s0 (lw.toNat + 16))] ∧
          memW (evaluateHOLFiniteState t balRemoveLoop).2 (lw.toNat + 8) = nw.toNat - 1) ∧
        (∀ r, (evaluateHOLFiniteState t balRemoveLoop).1 = some r →
          (∀ rv, r ≠ .returned rv) → ¬ Resumes (some r)) := by
  have hhe_263 : heapEnd < 2 ^ 63 := by decide
  have hhe_264 : heapEnd ≤ 2 ^ 64 := by decide
  have h338 : heapEnd = 33806089704 := by decide
  have hesz_pos : 0 < eszw.toNat := by rcases hesz with h | h | h <;> omega
  have hcap_lt : memW s0 (lw.toNat + 16) < 2 ^ 63 := by
    have : 1 * memW s0 (lw.toNat + 16) ≤ eszw.toNat * memW s0 (lw.toNat + 16) :=
      Nat.mul_le_mul_right _ hesz_pos
    omega
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro t iw hclk ht_eq hi_le_n h_l h_n h_p h_esz h_idx h_i hnt
    have ht_code : t.code = originalRuntimeCode := by rw [ht_eq]; exact hcode0
    have ht_ma : t.memaddrs = ordinaryDomain := by rw [ht_eq]; exact hma0
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    have hcond : @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      rw [evalHOLFinite_eq_toExact]
      simp only [evalHOLExact, h_i, h_n, Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small iw nw (by omega) (by omega), decide_eq_true_eq]
      by_cases hlt : iw.toNat < nw.toNat <;> simp [hlt]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hi_lt_n : iw.toNat < nw.toNat
    · rw [if_pos hi_lt_n] at hnt ⊢
      have h1nz : (1#64 : BitVec 64) ≠ 0 := by decide
      rw [if_pos h1nz] at hnt ⊢
      by_cases hk0 : t.clock = 0
      · rw [if_pos hk0] at hnt; exact absurd rfl hnt
      · rw [if_neg hk0] at hnt ⊢
        have hn_pos : 1 ≤ nw.toNat := by omega
        let td := decClockHOLFinite t
        have htd_eq : td = { s0 with locals := t.locals, clock := k - 1 } := by
          change decClockHOLFinite t = _
          rw [ht_eq]; rfl
        have htd_ma : td.memaddrs = ordinaryDomain := by rw [htd_eq]; exact hma0
        have htd_code : td.code = originalRuntimeCode := by rw [htd_eq]; exact hcode0
        have hmul_ie : (iw * eszw).toNat = iw.toNat * eszw.toNat := by
          rw [BitVec.toNat_mul]
          have : iw.toNat * eszw.toNat ≤ eszw.toNat * memW s0 (lw.toNat + 16) := by
            rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
          exact Nat.mod_eq_of_lt (by omega)
        have haddr_i : (pw + iw * eszw).toNat = pw.toNat + iw.toNat * eszw.toNat := by
          rw [BitVec.toNat_add, hmul_ie]
          have : iw.toNat * eszw.toNat ≤ eszw.toNat * memW s0 (lw.toNat + 16) := by
            rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
          exact Nat.mod_eq_of_lt (by omega)
        have hdom_i : td.memaddrs (pw + iw * eszw) := by
          rw [htd_ma, InitECandidate.Solver.Wave8Contracts.M08.ordinaryDomain_iff]
          have hmul8 : (iw.toNat * eszw.toNat) % 8 = 0 := by
            rcases hesz with h | h | h
            · rw [h, Nat.mul_mod]; simp
            · rw [h, Nat.mul_mod]; simp
            · rw [h, Nat.mul_mod]; simp
          have hal_i : (pw + iw * eszw).toNat % 8 = 0 := by
            rw [haddr_i, Nat.add_mod, hp_al.1, hmul8]
          have h1 : (iw.toNat + 1) * eszw.toNat ≤ memW s0 (lw.toNat + 16) * eszw.toNat :=
            Nat.mul_le_mul_right _ (by omega)
          have h2 : memW s0 (lw.toNat + 16) * eszw.toNat = eszw.toNat * memW s0 (lw.toNat + 16) :=
            Nat.mul_comm _ _
          have h3 : iw.toNat * eszw.toNat + eszw.toNat = (iw.toNat + 1) * eszw.toNat := by ring
          exact ⟨hal_i, by rw [haddr_i]; omega, by rw [haddr_i]; omega⟩
        have hcell_i : ∃ cw, td.memory (pw + iw * eszw) = .word cw := by
          cases td.memory (pw + iw * eszw) with | word cw => exact ⟨cw, rfl⟩
        obtain ⟨cw, hcw⟩ := hcell_i
        have hev_cmp : @evalHOLExact 64 F _ td.toExact (fun a => Classical.propDecidable (td.memaddrs a))
            (.cmp .equal (.load .one (.op .add [.var .local (ofString "p"),
              .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
              (.var .local (ofString "idx"))) =
            some (.val (.word (if cw = idxw then 1#64 else 0#64))) := by
          have hl_p : td.locals.lookup (ofString "p") = some (.val (.word pw)) := h_p
          have hl_i : td.locals.lookup (ofString "i") = some (.val (.word iw)) := h_i
          have hl_e : td.locals.lookup (ofString "esz") = some (.val (.word eszw)) := h_esz
          have hl_x : td.locals.lookup (ofString "idx") = some (.val (.word idxw)) := h_idx
          have hz_ie : iw * eszw + 0 = iw * eszw := BitVec.add_zero _
          simp only [evalHOLExact, evalListHOLExact, hl_p, hl_i, hl_e, hl_x,
            valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
            memLoadHOLExact, isWfShapeExactHOL, List.all, List.map, Option.map,
            Bool.and_self, List.foldr, hz_ie, hdom_i, hcw, ↓reduceIte,
            Compiler.Encoders.Asm.wordCmpHOL, decide_eq_true_eq]
          by_cases hci : cw = idxw <;> simp [hci]
        have hbody_unfold := evaluateHOLFiniteState_seq_line780 td
          (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "p"),
              .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
              (.var .local (ofString "idx")))
            (.seq
              (.ite (.cmp .notEqual (.var .local (ofString "i"))
                  (.op .sub [.var .local (ofString "n"), .const 1#64]))
                (.call (some (none, none)) (ofString "memcpy")
                  [.op .add [.var .local (ofString "p"),
                     .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]],
                   .op .add [.var .local (ofString "p"),
                     .panop .mul [.op .sub [.var .local (ofString "n"), .const 1#64],
                       .var .local (ofString "esz")]],
                   .var .local (ofString "esz")])
                .skip)
              (.seq
                (.store (.op .add [.var .local (ofString "l"), .const 8#64])
                  (.op .sub [.var .local (ofString "n"), .const 1#64]))
                (.return (.const 0#64))))
            .skip)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))
        by_cases hmatch : cw = idxw
        · -- Matching branch: executes optional memcpy, then store (l+8) (n-1), then return 0
          have hite1 : evaluateHOLFiniteState td
              (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "p"),
                  .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
                  (.var .local (ofString "idx")))
                (.seq
                  (.ite (.cmp .notEqual (.var .local (ofString "i"))
                      (.op .sub [.var .local (ofString "n"), .const 1#64]))
                    (.call (some (none, none)) (ofString "memcpy")
                      [.op .add [.var .local (ofString "p"),
                         .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]],
                       .op .add [.var .local (ofString "p"),
                         .panop .mul [.op .sub [.var .local (ofString "n"), .const 1#64],
                           .var .local (ofString "esz")]],
                       .var .local (ofString "esz")])
                    .skip)
                  (.seq
                    (.store (.op .add [.var .local (ofString "l"), .const 8#64])
                      (.op .sub [.var .local (ofString "n"), .const 1#64]))
                    (.return (.const 0#64))))
                .skip) =
              evaluateHOLFiniteState td
                (.seq
                  (.ite (.cmp .notEqual (.var .local (ofString "i"))
                      (.op .sub [.var .local (ofString "n"), .const 1#64]))
                    (.call (some (none, none)) (ofString "memcpy")
                      [.op .add [.var .local (ofString "p"),
                         .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]],
                       .op .add [.var .local (ofString "p"),
                         .panop .mul [.op .sub [.var .local (ofString "n"), .const 1#64],
                           .var .local (ofString "esz")]],
                       .var .local (ofString "esz")])
                    .skip)
                  (.seq
                    (.store (.op .add [.var .local (ofString "l"), .const 8#64])
                      (.op .sub [.var .local (ofString "n"), .const 1#64]))
                    (.return (.const 0#64)))) := by
            rw [evaluateHOLFiniteState_ite, hev_cmp, if_pos hmatch]
            try dsimp only
            rw [if_neg (by decide)]
          let Rl : List Ivl := [(lw.toNat + 8, 8), (memW s0 lw.toNat, eszw.toNat * memW s0 (lw.toNat + 16))]
          let step1Prog : ProgHOL 64 :=
            .ite (.cmp .notEqual (.var .local (ofString "i"))
                (.op .sub [.var .local (ofString "n"), .const 1#64]))
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "p"),
                   .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]],
                 .op .add [.var .local (ofString "p"),
                   .panop .mul [.op .sub [.var .local (ofString "n"), .const 1#64],
                     .var .local (ofString "esz")]],
                 .var .local (ofString "esz")])
              .skip
          let step2Prog : ProgHOL 64 :=
            .seq
              (.store (.op .add [.var .local (ofString "l"), .const 8#64])
                (.op .sub [.var .local (ofString "n"), .const 1#64]))
              (.return (.const 0#64))
          have hseq1 := evaluateHOLFiniteState_seq_line780 td step1Prog step2Prog
          have hstep1_nt : (evaluateHOLFiniteState td step1Prog).1 ≠ some .timeOut := by
            intro hto
            have hseq1_to : evaluateHOLFiniteState td (.seq step1Prog step2Prog) =
                evaluateHOLFiniteState td step1Prog := by
              rw [hseq1]; simp only [hto]
            have hbody_to : evaluateHOLFiniteState td balRemoveLoopBody =
                evaluateHOLFiniteState td step1Prog := by
              rw [hbody_unfold, hite1]
              change (have firstOutput := evaluateHOLFiniteState td (.seq step1Prog step2Prog); _) = _
              rw [hseq1_to]; simp only [hto]
            rw [show t.decClockHOLFinite = td from rfl, hbody_to, hto] at hnt
            exact hnt rfl
          have hstep1_spec :
              ((evaluateHOLFiniteState td step1Prog).1 = none →
                M11.ByteRegionEffect s0 (evaluateHOLFiniteState td step1Prog).2 Rl ∧
                (evaluateHOLFiniteState td step1Prog).2.locals = td.locals) ∧
              ((evaluateHOLFiniteState td step1Prog).1 ≠ none →
                ¬ Resumes (evaluateHOLFiniteState td step1Prog).1) := by
            have hev_ne : @evalHOLExact 64 F _ td.toExact (fun a => Classical.propDecidable (td.memaddrs a))
                (.cmp .notEqual (.var .local (ofString "i"))
                  (.op .sub [.var .local (ofString "n"), .const 1#64])) =
                some (.val (.word (if iw ≠ nw - 1#64 then 1#64 else 0#64))) := by
              have hl_i : td.locals.lookup (ofString "i") = some (.val (.word iw)) := h_i
              have hl_n : td.locals.lookup (ofString "n") = some (.val (.word nw)) := h_n
              simp only [evalHOLExact, evalListHOLExact, hl_i, hl_n,
                valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map,
                Bool.and_self, ↓reduceIte, Compiler.Encoders.Asm.wordCmpHOL]
              by_cases hne_in : iw = nw - 1#64 <;> simp [hne_in]
            dsimp only [step1Prog] at hstep1_nt ⊢
            rw [evaluateHOLFiniteState_ite, hev_ne] at hstep1_nt ⊢
            dsimp only at hstep1_nt ⊢
            by_cases hne_in : iw ≠ nw - 1#64
            · rw [if_pos hne_in, if_neg (by decide)] at hstep1_nt ⊢
              have hl_p : td.locals.lookup (ofString "p") = some (.val (.word pw)) := h_p
              have hl_i : td.locals.lookup (ofString "i") = some (.val (.word iw)) := h_i
              have hl_n : td.locals.lookup (ofString "n") = some (.val (.word nw)) := h_n
              have hl_e : td.locals.lookup (ofString "esz") = some (.val (.word eszw)) := h_esz
              have hz_ie : iw * eszw + 0 = iw * eszw := BitVec.add_zero _
              have hz_ne : (nw - 1#64) * eszw + 0 = (nw - 1#64) * eszw := BitVec.add_zero _
              have hdst_ev : @evalHOLExact 64 F _ td.toExact (fun a => Classical.propDecidable (td.memaddrs a))
                  (.op .add [.var .local (ofString "p"),
                    .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]) =
                  some (.val (.word (pw + iw * eszw))) := by
                simp only [evalHOLExact, evalListHOLExact, hl_p, hl_i, hl_e,
                  valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
                  List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, hz_ie]
              have hsrc_ev : @evalHOLExact 64 F _ td.toExact (fun a => Classical.propDecidable (td.memaddrs a))
                  (.op .add [.var .local (ofString "p"),
                    .panop .mul [.op .sub [.var .local (ofString "n"), .const 1#64],
                      .var .local (ofString "esz")]]) =
                  some (.val (.word (pw + (nw - 1#64) * eszw))) := by
                simp only [evalHOLExact, evalListHOLExact, hl_p, hl_n, hl_e,
                  valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
                  List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, hz_ne]
              have hn_ev : @evalHOLExact 64 F _ td.toExact (fun a => Classical.propDecidable (td.memaddrs a))
                  (.var .local (ofString "esz")) = some (.val (.word eszw)) := by
                simp [evalHOLExact, hl_e]
              have hmc := M11.eval_call_memcpy_bre td _ _ _ (pw + iw * eszw) (pw + (nw - 1#64) * eszw) eszw Rl
                htd_code htd_ma hdst_ev hsrc_ev hn_ev
                (fun _ => ⟨(memW s0 lw.toNat, eszw.toNat * memW s0 (lw.toNat + 16)),
                  by simp [Rl], by
                    dsimp only; rw [haddr_i, hp_eq]; omega, by
                    dsimp only; rw [haddr_i, hp_eq]
                    have h1 : (iw.toNat + 1) * eszw.toNat ≤ memW s0 (lw.toNat + 16) * eszw.toNat :=
                      Nat.mul_le_mul_right eszw.toNat (by omega)
                    have h2 : memW s0 (lw.toNat + 16) * eszw.toNat = eszw.toNat * memW s0 (lw.toNat + 16) :=
                      Nat.mul_comm _ _
                    have h3 : iw.toNat * eszw.toNat + eszw.toNat = (iw.toNat + 1) * eszw.toNat := by ring
                    omega⟩)
                hstep1_nt
              have hs0_td : M11.ByteRegionEffect s0 td Rl := by
                rw [htd_eq]
                exact (M11.ByteRegionEffect.refl s0 Rl).with_locals_clock t.locals (k - 1)
              exact ⟨fun h0 => ⟨hs0_td.trans (hmc.1 h0).1, (hmc.1 h0).2⟩, hmc.2⟩
            · rw [if_neg hne_in]
              have h0eq : (0#64 : BitVec 64) = 0 := rfl
              rw [if_pos h0eq, evaluateHOLFiniteState_skip]
              have hs0_td : M11.ByteRegionEffect s0 td Rl := by
                rw [htd_eq]
                exact (M11.ByteRegionEffect.refl s0 Rl).with_locals_clock t.locals (k - 1)
              exact ⟨fun _ => ⟨hs0_td, rfl⟩, fun h => False.elim (h rfl)⟩
          by_cases hs1 : (evaluateHOLFiniteState td step1Prog).1 = none
          · obtain ⟨heff1, hloc1⟩ := hstep1_spec.1 hs1
            let m1 := (evaluateHOLFiniteState td step1Prog).2
            have hm1_ma : m1.memaddrs = ordinaryDomain := by rw [heff1.memaddrs]; exact hma0
            have hm1_l : m1.locals.lookup (ofString "l") = some (.val (.word lw)) := by
              rw [hloc1]; exact h_l
            have hm1_n : m1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
              rw [hloc1]; exact h_n
            have hl8_toNat : (lw + 8#64).toNat = lw.toNat + 8 := by
              rw [BitVec.toNat_add]; change (lw.toNat + 8) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
            have hdom_l8 : m1.memaddrs (lw + 8#64) := by
              rw [hm1_ma, InitECandidate.Solver.Wave8Contracts.M08.ordinaryDomain_iff]
              exact ⟨by rw [hl8_toNat]; omega, by rw [hl8_toNat]; omega, by rw [hl8_toNat]; omega⟩
            have hnm1_toNat : (nw - 1#64).toNat = nw.toNat - 1 := by
              rw [BitVec.toNat_sub_of_le (by
                rw [BitVec.le_def]; change 1 ≤ nw.toNat; exact hn_pos)]
              rfl
            have hz_8 : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
            have hev_d : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
                (.op .add [.var .local (ofString "l"), .const 8#64]) =
                some (.val (.word (lw + 8#64))) := by
              simp only [evalHOLExact, evalListHOLExact, hm1_l, valueIsWord, valueWord,
                wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte,
                List.foldr, hz_8]
            have hev_v : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
                (.op .sub [.var .local (ofString "n"), .const 1#64]) =
                some (.val (.word (nw - 1#64))) := by
              simp only [evalHOLExact, evalListHOLExact, hm1_n, valueIsWord, valueWord,
                wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte]
            have hstore_eq : evaluateHOLFiniteState m1
                (.store (.op .add [.var .local (ofString "l"), .const 8#64])
                  (.op .sub [.var .local (ofString "n"), .const 1#64])) =
                (none, { m1 with memory := fun a => if a = lw + 8#64 then .word (nw - 1#64) else m1.memory a }) := by
              rw [evaluateHOLFiniteState_store, hev_d, hev_v]; dsimp only
              simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom_l8, FUPDATE]
            obtain ⟨heff2, _⟩ := M11.ByteRegionEffect.of_store_word (Rl := Rl) hm1_ma hstore_eq
              (fun v hv => by
                rw [hev_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
              (fun addr hdst _ => by
                rw [hev_d] at hdst; injection hdst with hd'; injection hd' with hd''; injection hd'' with hd3
                subst hd3
                exact ⟨(lw.toNat + 8, 8), by simp [Rl], by dsimp only; omega, by dsimp only; omega⟩)
            let m2 : PanSemStateFiniteExact 64 F :=
              { m1 with memory := fun a => if a = lw + 8#64 then .word (nw - 1#64) else m1.memory a }
            have hret_eq : evaluateHOLFiniteState m2 (.return (.const 0#64)) =
                (some (.returned (.val (.word 0))), emptyLocalsHOLFinite m2) := by
              rw [evaluateHOLFiniteState_return]
              simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
            have hseq2 : evaluateHOLFiniteState m1 step2Prog =
                (some (.returned (.val (.word 0))), emptyLocalsHOLFinite m2) := by
              dsimp only [step2Prog]
              rw [evaluateHOLFiniteState_seq_line780]; simp only [hstore_eq]; exact hret_eq
            have hseq1_ok : evaluateHOLFiniteState td (.seq step1Prog step2Prog) =
                (some (.returned (.val (.word 0))), emptyLocalsHOLFinite m2) := by
              rw [hseq1]; simp only [hs1]; exact hseq2
            have hbody_all : evaluateHOLFiniteState td balRemoveLoopBody =
                (some (.returned (.val (.word 0))), emptyLocalsHOLFinite m2) := by
              rw [hbody_unfold, hite1]; dsimp only [step1Prog, step2Prog] at hseq1_ok; simp only [hseq1_ok]
            simp only [show t.decClockHOLFinite = td from rfl, hbody_all]
            have heff_tot : M11.ByteRegionEffect s0 (emptyLocalsHOLFinite m2) Rl :=
              (heff1.trans heff2).with_locals_clock HolFiniteMapExact.empty m2.clock
            have hmemW_l8 : memW (emptyLocalsHOLFinite m2) (lw.toNat + 8) = nw.toNat - 1 := by
              unfold memW emptyLocalsHOLFinite
              dsimp only [m2]
              have hbv_eq : BitVec.ofNat 64 (lw.toNat + 8) = lw + 8#64 := by
                apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hl8_toNat]
              rw [if_pos hbv_eq]; exact hnm1_toNat
            refine ⟨fun h => by simp at h, fun rv hrv => ?_, fun r hr hnr => ?_⟩
            · injection hrv with hrv'; injection hrv' with hrv''
              exact ⟨hrv''.symm, hn_pos, heff_tot, hmemW_l8⟩
            · injection hr with hr'
              exact False.elim (hnr _ hr'.symm)
          · have hnr1 := hstep1_spec.2 hs1
            rcases hst1 : evaluateHOLFiniteState td step1Prog with ⟨r1, m1⟩
            have hst1_val : evaluateHOLFiniteState td step1Prog = (r1, m1) := hst1
            have hseq1_err : evaluateHOLFiniteState td (.seq step1Prog step2Prog) = (r1, m1) := by
              rw [hseq1]; simp only [hst1]
              cases r1 with
              | none => exact absurd (by rw [hst1]) hs1
              | some _ => rfl
            have hbody_err : evaluateHOLFiniteState td balRemoveLoopBody = (r1, m1) := by
              rw [hbody_unfold, hite1]
              change (have firstOutput := evaluateHOLFiniteState td (.seq step1Prog step2Prog); _) = (r1, m1)
              rw [hseq1_err]
              cases r1 with
              | none => exact absurd (by rw [hst1]) hs1
              | some _ => rfl
            rw [show t.decClockHOLFinite = td from rfl, hbody_err]
            rw [hst1] at hs1 hstep1_nt hnr1
            have hs1' : r1 ≠ none := hs1
            have hstep1_nt' : r1 ≠ some .timeOut := hstep1_nt
            have hnr1' : ¬ Resumes r1 := hnr1
            have hno_bc : r1 ≠ some .break ∧ r1 ≠ some .continue := by
              dsimp only [step1Prog] at hst1_val
              rw [evaluateHOLFiniteState_ite] at hst1_val
              split at hst1_val
              · split at hst1_val
                · rw [evaluateHOLFiniteState_skip] at hst1_val
                  injection hst1_val with hr _; subst hr; exact ⟨by simp, by simp⟩
                · rw [evaluateHOLFiniteState_call] at hst1_val
                  split at hst1_val
                  · injection hst1_val with hr _; subst hr; exact ⟨by simp, by simp⟩
                  · split at hst1_val
                    · injection hst1_val with hr _; subst hr; exact ⟨by simp, by simp⟩
                    · split at hst1_val
                      · injection hst1_val with hr _; subst hr; exact ⟨by simp, by simp⟩
                      · split at hst1_val
                        · injection hst1_val with hr _; subst hr; exact ⟨by simp, by simp⟩
                        · injection hst1_val with hr _; subst hr; exact ⟨by simp, by simp⟩
                        · injection hst1_val with hr _; subst hr; exact ⟨by simp, by simp⟩
                        · split at hst1_val <;> (injection hst1_val with hr _; subst hr; exact ⟨by simp, by simp⟩)
                        · injection hst1_val with hr _; subst hr; exact ⟨by simp, by simp⟩
                        · next _ _ xb xc _ _ _ =>
                          injection hst1_val with hr _; subst hr
                          exact ⟨by intro h; injection h with h'; exact xb h',
                                 by intro h; injection h with h'; exact xc h'⟩
              · injection hst1_val with hr _; subst hr; exact ⟨by simp, by simp⟩
            cases r1 with
            | none => exact absurd rfl hs1
            | some r1' =>
              cases r1' with
              | timeOut => exact absurd rfl hstep1_nt
              | «break» => exact absurd rfl hno_bc.1
              | «continue» => exact absurd rfl hno_bc.2
              | returned rv => exact absurd (Or.inl ⟨rv, rfl⟩) hnr1
              | error =>
                exact ⟨fun h => by simp at h, fun _ h => by simp at h, fun r hr _ => by
                  injection hr with hr'; subst hr'; exact not_resumes_error⟩
              | exception eid ev =>
                exact ⟨fun h => by simp at h, fun _ h => by simp at h, fun r hr _ => by
                  injection hr with hr'; subst hr'; exact hnr1⟩
              | finalFfi _ =>
                exact ⟨fun h => by simp at h, fun _ h => by simp at h, fun r hr _ => by
                  injection hr with hr'; subst hr'; exact hnr1⟩
        · -- Non-matching branch: skip, then i := i + 1, then recurse
          have hite0 : evaluateHOLFiniteState td
              (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "p"),
                  .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
                  (.var .local (ofString "idx")))
                (.seq
                  (.ite (.cmp .notEqual (.var .local (ofString "i"))
                      (.op .sub [.var .local (ofString "n"), .const 1#64]))
                    (.call (some (none, none)) (ofString "memcpy")
                      [.op .add [.var .local (ofString "p"),
                         .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]],
                       .op .add [.var .local (ofString "p"),
                         .panop .mul [.op .sub [.var .local (ofString "n"), .const 1#64],
                           .var .local (ofString "esz")]],
                       .var .local (ofString "esz")])
                    .skip)
                  (.seq
                    (.store (.op .add [.var .local (ofString "l"), .const 8#64])
                      (.op .sub [.var .local (ofString "n"), .const 1#64]))
                    (.return (.const 0#64))))
                .skip) = (none, td) := by
            rw [evaluateHOLFiniteState_ite, hev_cmp, if_neg hmatch]
            try dsimp only
            have h0eq : (0#64 : BitVec 64) = 0 := rfl
            rw [if_pos h0eq]; exact evaluateHOLFiniteState_skip td
          have hasgn : evaluateHOLFiniteState td
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])) =
              (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) td) := by
            rw [evaluateHOLFiniteState_assign]
            have hl_i : td.locals.lookup (ofString "i") = some (.val (.word iw)) := h_i
            have hz_1 : (1#64 : BitVec 64) + 0 = 1#64 := BitVec.add_zero _
            have hev_add : @evalHOLExact 64 F _ td.toExact (fun a => Classical.propDecidable (td.memaddrs a))
                (.op .add [.var .local (ofString "i"), .const 1#64]) =
                some (.val (.word (iw + 1#64))) := by
              simp only [evalHOLExact, evalListHOLExact, hl_i, valueIsWord, valueWord,
                wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte,
                List.foldr, hz_1]
            rw [hev_add]; dsimp only
            have hval_i : isValidValueHOLFinite td .local (ofString "i") (.val (.word (iw + 1#64))) = true := by
              simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hl_i, shapeEqHOL, shapeOfHOLExact]
            rw [if_pos hval_i]; rfl
          have hbody_step : evaluateHOLFiniteState td balRemoveLoopBody =
              (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) td) := by
            rw [hbody_unfold]; simp only [hite0]; exact hasgn
          rw [show t.decClockHOLFinite = td from rfl, hbody_step] at hnt ⊢; try dsimp only at hnt ⊢
          let t' : PanSemStateFiniteExact 64 F :=
            setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) td
          have ht'_clk : t'.clock < k := by
            simp [t', setVarHOLFinite, td, decClockHOLFinite, hclk]
            have : t.clock ≠ 0 := hk0
            omega
          have ht'_eq : t' = { s0 with locals := t'.locals, clock := t'.clock } := by
            simp [t', setVarHOLFinite, htd_eq]
          have hiw1_le : (iw + 1#64).toNat ≤ nw.toNat := by
            rw [BitVec.toNat_add]; change (iw.toNat + 1) % 2 ^ 64 ≤ nw.toNat
            rw [Nat.mod_eq_of_lt (by omega)]; omega
          have hne_il : ofString "i" ≠ ofString "l" := by decide
          have hne_in : ofString "i" ≠ ofString "n" := by decide
          have hne_ip : ofString "i" ≠ ofString "p" := by decide
          have hne_ie : ofString "i" ≠ ofString "esz" := by decide
          have hne_ix : ofString "i" ≠ ofString "idx" := by decide
          exact ih t'.clock ht'_clk t' (iw + 1#64) rfl ht'_eq hiw1_le
            (by simp [t', setVarHOLFinite, td, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_il, h_l])
            (by simp [t', setVarHOLFinite, td, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_in, h_n])
            (by simp [t', setVarHOLFinite, td, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_ip, h_p])
            (by simp [t', setVarHOLFinite, td, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_ie, h_esz])
            (by simp [t', setVarHOLFinite, td, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_ix, h_idx])
            (by simp [t', setVarHOLFinite, td, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
            hnt
    · rw [if_neg hi_lt_n] at hnt ⊢
      rw [if_neg (by decide)] at hnt ⊢
      exact ⟨fun _ => by rw [← hclk] at ht_eq; exact ht_eq,
        fun _ h => by simp at h, fun _ h => by simp at h⟩

theorem call_bal_list_remove_idx_eval {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (lExp eszExp idxExp : ExpHOL 64)
    (lw eszw idxw : BitVec 64)
    (hW : WorldOK s)
    (hev_l : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) lExp =
      some (.val (.word lw)))
    (hev_e : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) eszExp =
      some (.val (.word eszw)))
    (hev_x : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) idxExp =
      some (.val (.word idxw)))
    (hesz : eszw.toNat = 16 ∨ eszw.toNat = 24 ∨ eszw.toNat = 40)
    (hslice_nz : lw ≠ 0 → ∀ S Nd, WorldTypedWith s S Nd →
      LstOK s lw.toNat ∧ BalListSlice s lw.toNat eszw.toNat)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "bal_list_remove_idx") [lExp, eszExp, idxExp])).1 ≠
        some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "bal_list_remove_idx") [lExp, eszExp, idxExp])
    (out.1 = none →
      lw ≠ 0 ∧ WorldStep (fun _ => []) [] stdKeep NoExtra s out.1 out.2 ∧
      out.2.locals = s.locals ∧
      M11.ByteRegionEffect s out.2
        [(lw.toNat + 8, 8), (memW s lw.toNat, eszw.toNat * memW s (lw.toNat + 16))]) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  dsimp only
  have hG := hW.1.1
  have hAs := hW.1
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [lExp, eszExp, idxExp] = some [.val (.word lw), .val (.word eszw), .val (.word idxw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hev_l, hev_e, hev_x]
  rw [hargs] at hnt ⊢; dsimp only at hnt ⊢
  have hlook : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup (ofString "bal_list_remove_idx")
      [.val (.word lw), .val (.word eszw), .val (.word idxw)] =
      some (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx,
        (((HolFiniteMapExact.empty.update (ofString "l", ValueHOL.val (.word lw))).update
          (ofString "esz", ValueHOL.val (.word eszw))).update
          (ofString "idx", ValueHOL.val (.word idxw))),
        .one) := by
    rw [hG.code]
    exact InitECandidate.Solver.GuestTrapAndLookup.pan_three_word_lookup
      originalRuntimeCode.lookup (ofString "bal_list_remove_idx")
      (ofString "l") (ofString "esz") (ofString "idx")
      (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx)
      lw eszw idxw (by decide) (by decide) (by decide) lookup_bal_list_remove_idx
  rw [hlook] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at hnt; exact absurd rfl hnt
  · rw [if_neg hcz] at hnt ⊢
    let cmap := (((HolFiniteMapExact.empty.update (ofString "l", ValueHOL.val (.word lw))).update
      (ofString "esz", ValueHOL.val (.word eszw))).update
      (ofString "idx", ValueHOL.val (.word idxw)))
    set ent := callEntryStateHOLFinite s (((HolFiniteMapExact.empty.update (ofString "l", ValueHOL.val (.word lw))).update
      (ofString "esz", ValueHOL.val (.word eszw))).update
      (ofString "idx", ValueHOL.val (.word idxw))) with hent_def
    have hent_eq : ent = { s with locals := cmap, clock := s.clock - 1 } := rfl
    have hent_code : ent.code = originalRuntimeCode := hG.code
    have hent_ma : ent.memaddrs = ordinaryDomain := hG.memaddrs
    have hent_l : ent.locals.lookup (ofString "l") = some (.val (.word lw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "idx" ≠ ofString "l" by decide,
        show ofString "esz" ≠ ofString "l" by decide]
    have hent_e : ent.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "idx" ≠ ofString "esz" by decide]
    have hent_x : ent.locals.lookup (ofString "idx") = some (.val (.word idxw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    by_cases hlw0 : lw = 0
    · -- Null list pointer: load (0 + 8) faults immediately with error
      have hnot8 : ¬ ent.memaddrs 8#64 := by
        rw [hent_ma, InitECandidate.Solver.Wave8Contracts.M08.ordinaryDomain_iff]
        have hsb : sourceBase = 2701131776 := rfl
        simp [hsb]
      have hbody_err : (evaluateHOLFiniteState ent
          (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx)).1 = some .error := by
        dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_bal_list_remove_idx,
          InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
        rw [evaluateHOLFiniteState_dec_total]; dsimp only
        have hz_8 : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
        have hl0 : ent.locals.lookup (ofString "l") = some (.val (.word 0#64)) := by
          subst hlw0; exact hent_l
        have hev8 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "l"), .const 8#64])) = none := by
          simp [evalHOLExact, evalListHOLExact, hl0, valueIsWord, valueWord, wordOpHOL, wordOp,
            List.foldr, hz_8, memLoadHOLExact, hnot8]
        rw [hev8]
      rcases hrun : evaluateHOLFiniteState ent
          (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx) with ⟨rb, sb⟩
      rw [hrun] at hbody_err; dsimp only at hbody_err ⊢; subst hbody_err
      exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
    · -- Non-null list pointer: slice is allocated in fixedObjects s
      have hlw_nz_nat : lw.toNat ≠ 0 := fun h => hlw0 (BitVec.eq_of_toNat_eq (by simpa using h))
      obtain ⟨S0, hWT0_ex⟩ := hW.2
      obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
      obtain ⟨hlst0, hslice0⟩ := hslice_nz hlw0 S0 Nd0 hWT0
      obtain ⟨hl_fix0, hp_fix0, _, _, _, _⟩ :=
        bal_list_slice_props hWT0.2.2.1 hlw_nz_nat hesz hlst0 hslice0
      have hesz_pos : 0 < eszw.toNat := by rcases hesz with h | h | h <;> omega
      have hpos_arr : eszw.toNat * memW s (lw.toNat + 16) ≠ 0 :=
        ne_of_gt (Nat.mul_pos hesz_pos (by have := hlst0.1; omega))
      rcases hWT0.2.2.1.1 _ hl_fix0 with h0 | ⟨hal_l, hw_l⟩
      · simp at h0
      rcases hWT0.2.2.1.1 _ hp_fix0 with h0 | ⟨hal_p, hw_p⟩
      · exact absurd h0 hpos_arr
      have hhe_264 : heapEnd < 2 ^ 64 := by decide
      have hsb_ss : sourceBase ≤ scratchStart := by decide
      have hl_bnd : sourceBase ≤ lw.toNat ∧ lw.toNat + 24 ≤ heapEnd := by
        have hup := (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_l).1
        rcases hal_l with h | h
        · exact ⟨h.1, hup⟩
        · exact ⟨le_trans hsb_ss (le_trans hAs.2.2.2.1 (le_trans hAs.2.2.2.2.1 h.1)), hup⟩
      have hp_bnd : sourceBase ≤ memW s lw.toNat ∧
          memW s lw.toNat + eszw.toNat * memW s (lw.toNat + 16) ≤ heapEnd := by
        have hup := (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_p).1
        rcases hal_p with h | h
        · exact ⟨h.1, hup⟩
        · exact ⟨le_trans hsb_ss (le_trans hAs.2.2.2.1 (le_trans hAs.2.2.2.2.1 h.1)), hup⟩
      let pw : BitVec 64 := BitVec.ofNat 64 (memW s lw.toNat)
      let nw : BitVec 64 := BitVec.ofNat 64 (memW s (lw.toNat + 8))
      have hpw_toNat : pw.toNat = memW s lw.toNat := by
        dsimp [pw]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hnw_toNat : nw.toNat = memW s (lw.toNat + 8) := by
        dsimp [nw]; rw [BitVec.toNat_ofNat]
        have : memW s (lw.toNat + 8) ≤ memW s (lw.toNat + 16) := hlst0.2
        have : 1 * memW s (lw.toNat + 16) ≤ eszw.toNat * memW s (lw.toNat + 16) :=
          Nat.mul_le_mul_right _ hesz_pos
        exact Nat.mod_eq_of_lt (by omega)
      have hl8_bv : lw + 8#64 = BitVec.ofNat 64 (lw.toNat + 8) := by
        apply BitVec.eq_of_toNat_eq
        have hlt_l8 : lw.toNat + 8 < 2 ^ 64 := by omega
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        change (lw.toNat + 8) % 2 ^ 64 = (lw.toNat + 8) % 2 ^ 64
        rfl
      have hl0_bv : lw + 0#64 = BitVec.ofNat 64 lw.toNat := by simp
      have hdom_l8 : ent.memaddrs (lw + 8#64) := by
        rw [hent_ma, InitECandidate.Solver.Wave8Contracts.M08.ordinaryDomain_iff, hl8_bv]
        have hl8_mod : lw.toNat % 8 = 0 := hw_l.1
        have hlt_l8 : lw.toNat + 8 < 2 ^ 64 := lt_of_le_of_lt (by omega) hhe_264
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt_l8]
        exact ⟨by omega, by omega, by omega⟩
      have hdom_l0 : ent.memaddrs (lw + 0#64) := by
        rw [hent_ma, InitECandidate.Solver.Wave8Contracts.M08.ordinaryDomain_iff]
        have : (lw + 0#64).toNat = lw.toNat := by simp
        rw [this]
        exact ⟨hw_l.1, by omega, by omega⟩
      have hm_l8 : ent.memory (lw + 8#64) = .word nw := by
        change s.memory (lw + 8#64) = .word nw
        rw [hl8_bv]; dsimp [nw]; unfold memW
        rcases s.memory (BitVec.ofNat 64 (lw.toNat + 8)) with ⟨w⟩
        simp
      have hm_l0 : ent.memory (lw + 0#64) = .word pw := by
        change s.memory (lw + 0#64) = .word pw
        rw [hl0_bv]; dsimp [pw]; unfold memW
        rcases s.memory (BitVec.ofNat 64 lw.toNat) with ⟨w⟩
        simp
      -- Evaluate the three `dec` headers of `bal_list_remove_idx`
      have hz_8 : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
      have hz_0 : (0#64 : BitVec 64) + 0 = 0#64 := BitVec.add_zero _
      let e1 := setVarHOLFinite (ofString "n") (.val (.word nw)) ent
      let e2 := setVarHOLFinite (ofString "p") (.val (.word pw)) e1
      let e3 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) e2
      have hbody_eq_e3 : evaluateHOLFiniteState ent
          (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx) =
          (let out := evaluateHOLFiniteState e3 (.seq balRemoveLoop (.return (.const 0#64)));
           (out.1, { out.2 with
             locals := HolFiniteMapExact.resVarEq
               (HolFiniteMapExact.resVarEq
                 (HolFiniteMapExact.resVarEq out.2.locals (ofString "i", e2.locals.lookup (ofString "i")))
                 (ofString "p", e1.locals.lookup (ofString "p")))
               (ofString "n", ent.locals.lookup (ofString "n")) })) := by
        dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_bal_list_remove_idx,
          InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
        rw [evaluateHOLFiniteState_dec_total]; dsimp only
        have hev1 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "l"), .const 8#64])) =
            some (.val (.word nw)) := by
          simp only [evalHOLExact, evalListHOLExact, hent_l, valueIsWord, valueWord,
            wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_8,
            memLoadHOLExact, isWfShapeExactHOL, hdom_l8, hm_l8, ↓reduceIte]
        rw [hev1]; dsimp only
        rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
        have he1_def : setVarHOLFinite (ofString "n") (.val (.word nw)) ent = e1 := rfl
        rw [he1_def, evaluateHOLFiniteState_dec_total]; dsimp only
        have he1_l : e1.locals.lookup (ofString "l") = some (.val (.word lw)) := by
          simp [e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "n" ≠ ofString "l" by decide, hent_l]
        have he1_dom_l0 : e1.memaddrs (lw + 0#64) := hdom_l0
        have he1_m_l0 : e1.memory (lw + 0#64) = .word pw := hm_l0
        have hev2 : @evalHOLExact 64 F _ e1.toExact (fun a => Classical.propDecidable (e1.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "l"), .const 0#64])) =
            some (.val (.word pw)) := by
          simp only [evalHOLExact, evalListHOLExact, he1_l, valueIsWord, valueWord,
            wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_0,
            memLoadHOLExact, isWfShapeExactHOL, he1_dom_l0, he1_m_l0, ↓reduceIte]
        rw [hev2]; dsimp only
        rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
        have he2_def : setVarHOLFinite (ofString "p") (.val (.word pw)) e1 = e2 := rfl
        rw [he2_def, evaluateHOLFiniteState_dec_total]; dsimp only
        have hev3 : @evalHOLExact 64 F _ e2.toExact (fun a => Classical.propDecidable (e2.memaddrs a))
            (.const 0#64) = some (.val (.word 0#64)) := rfl
        rw [hev3]; dsimp only
        rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
      have he3_eq : e3 = { s with locals := e3.locals, clock := s.clock - 1 } := by
        simp [e3, e2, e1, setVarHOLFinite, hent_eq]
      have he3_l : e3.locals.lookup (ofString "l") = some (.val (.word lw)) := by
        simp [e3, e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "l" by decide,
          show ofString "p" ≠ ofString "l" by decide,
          show ofString "n" ≠ ofString "l" by decide, hent_l]
      have he3_n : e3.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        simp [e3, e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "n" by decide,
          show ofString "p" ≠ ofString "n" by decide]
      have he3_p : e3.locals.lookup (ofString "p") = some (.val (.word pw)) := by
        simp [e3, e2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "p" by decide]
      have he3_e : e3.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
        simp [e3, e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "esz" by decide,
          show ofString "p" ≠ ofString "esz" by decide,
          show ofString "n" ≠ ofString "esz" by decide, hent_e]
      have he3_x : e3.locals.lookup (ofString "idx") = some (.val (.word idxw)) := by
        simp [e3, e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "idx" by decide,
          show ofString "p" ≠ ofString "idx" by decide,
          show ofString "n" ≠ ofString "idx" by decide, hent_x]
      have he3_i : e3.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
        simp [e3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hseq_loop := evaluateHOLFiniteState_seq_line780 e3 balRemoveLoop (.return (.const 0#64))
      have hloop_nt : (evaluateHOLFiniteState e3 balRemoveLoop).1 ≠ some .timeOut := by
        intro hto
        have hseq_to : (evaluateHOLFiniteState e3 (.seq balRemoveLoop (.return (.const 0#64)))).1 =
            some .timeOut := by
          rw [hseq_loop]; simp only [hto]
        have hb_to : (evaluateHOLFiniteState ent
            (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx)).1 = some .timeOut := by
          rw [hbody_eq_e3]; dsimp only; exact hseq_to
        rcases hcal : evaluateHOLFiniteState ent
            (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx) with ⟨rc, sc⟩
        rw [hcal] at hb_to hnt; dsimp only at hb_to; subst hb_to
        exact hnt rfl
      have hloop_spec := bal_remove_loop_eval s lw nw pw eszw idxw
        hG.code hG.memaddrs
        ⟨hw_l.1, hl_bnd.1, hl_bnd.2⟩
        ⟨by rw [hpw_toNat]; exact hw_p.1, by rw [hpw_toNat]; exact hp_bnd.1,
         by rw [hpw_toNat]; exact hp_bnd.2⟩
        hesz hpw_toNat (by rw [hnw_toNat]; exact hlst0.2)
        (s.clock - 1) e3 0#64 rfl he3_eq (by simp)
        he3_l he3_n he3_p he3_e he3_x he3_i hloop_nt
      rcases hlp : evaluateHOLFiniteState e3 balRemoveLoop with ⟨rl, sl⟩
      cases rl with
      | none =>
        have hsl_eq := hloop_spec.1 (by rw [hlp])
        rw [hlp] at hsl_eq; dsimp only at hsl_eq
        have hret0 : evaluateHOLFiniteState sl (.return (.const 0#64)) =
            (some (.returned (.val (.word 0))), emptyLocalsHOLFinite sl) := by
          rw [evaluateHOLFiniteState_return]
          simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
        have hseq_val : evaluateHOLFiniteState e3 (.seq balRemoveLoop (.return (.const 0#64))) =
            (some (.returned (.val (.word 0))), emptyLocalsHOLFinite sl) := by
          rw [hseq_loop]; simp only [hlp]; exact hret0
        have hb_val : evaluateHOLFiniteState ent
            (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx) =
            (some (.returned (.val (.word 0))),
              { sl with
                locals := HolFiniteMapExact.resVarEq
                  (HolFiniteMapExact.resVarEq
                    (HolFiniteMapExact.resVarEq HolFiniteMapExact.empty
                      (ofString "i", e2.locals.lookup (ofString "i")))
                    (ofString "p", e1.locals.lookup (ofString "p")))
                  (ofString "n", ent.locals.lookup (ofString "n")) }) := by
          rw [hbody_eq_e3, hseq_val]; rfl
        rw [hb_val]; dsimp only
        rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
        have hpost_eq : { sl with locals := s.locals } = { s with clock := sl.clock } := by
          cases sl; cases s; cases hsl_eq; rfl
        have hws : WorldStep (fun _ => []) [] stdKeep NoExtra s none { sl with locals := s.locals } :=
          worldStep_refl (fun _ => []) [] hAs hpost_eq
        have hbre : M11.ByteRegionEffect s { sl with locals := s.locals }
            [(lw.toNat + 8, 8), (memW s lw.toNat, eszw.toNat * memW s (lw.toNat + 16))] := by
          rw [hpost_eq]
          exact (M11.ByteRegionEffect.refl s _).with_locals_clock s.locals sl.clock
        exact ⟨fun _ => ⟨hlw0, hws, rfl, hbre⟩, fun h => False.elim (h rfl)⟩
      | some rl' =>
        cases rl' with
        | returned rv =>
          obtain ⟨rfl, hn_pos, hbre_sl, hmemW_sl⟩ := hloop_spec.2.1 rv (by rw [hlp])
          rw [hlp] at hbre_sl hmemW_sl; dsimp only at hbre_sl hmemW_sl
          have hseq_val : evaluateHOLFiniteState e3 (.seq balRemoveLoop (.return (.const 0#64))) =
              (some (.returned (.val (.word 0))), sl) := by
            rw [hseq_loop]; simp only [hlp]
          have hb_val : evaluateHOLFiniteState ent
              (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx) =
              (some (.returned (.val (.word 0))),
                { sl with
                  locals := HolFiniteMapExact.resVarEq
                    (HolFiniteMapExact.resVarEq
                      (HolFiniteMapExact.resVarEq sl.locals
                        (ofString "i", e2.locals.lookup (ofString "i")))
                      (ofString "p", e1.locals.lookup (ofString "p")))
                    (ofString "n", ent.locals.lookup (ofString "n")) }) := by
            rw [hbody_eq_e3, hseq_val]
          rw [hb_val]; dsimp only
          rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
          have hbre_post : M11.ByteRegionEffect s { sl with locals := s.locals }
              [(lw.toNat + 8, 8), (memW s lw.toNat, eszw.toNat * memW s (lw.toNat + 16))] :=
            hbre_sl.with_locals_clock s.locals sl.clock
          have hmemW_post : memW { sl with locals := s.locals } (lw.toNat + 8) = nw.toNat - 1 := hmemW_sl
          have hn'_le : nw.toNat - 1 ≤ memW s (lw.toNat + 16) := by
            rw [hnw_toNat]; have := hlst0.2; omega
          have hws : WorldStep (fun _ => []) [] stdKeep NoExtra s none { sl with locals := s.locals } :=
            bal_list_store_len_and_arr_worldStep hW hlw_nz_nat hesz (hslice_nz hlw0)
              hbre_post hn'_le hmemW_post
          exact ⟨fun _ => ⟨hlw0, hws, rfl, hbre_post⟩, fun h => False.elim (h rfl)⟩
        | timeOut => exact absurd (by rw [hlp]) hloop_nt
        | «break» =>
          have hseq_val : evaluateHOLFiniteState e3 (.seq balRemoveLoop (.return (.const 0#64))) =
              (some .break, sl) := by rw [hseq_loop]; simp only [hlp]
          have hb_val : (evaluateHOLFiniteState ent
              (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx)).1 = some .break := by
            rw [hbody_eq_e3, hseq_val]
          rcases hcal : evaluateHOLFiniteState ent
              (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx) with ⟨rc, sc⟩
          rw [hcal] at hb_val; dsimp only at hb_val ⊢; subst hb_val
          exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
        | «continue» =>
          have hseq_val : evaluateHOLFiniteState e3 (.seq balRemoveLoop (.return (.const 0#64))) =
              (some .continue, sl) := by rw [hseq_loop]; simp only [hlp]
          have hb_val : (evaluateHOLFiniteState ent
              (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx)).1 = some .continue := by
            rw [hbody_eq_e3, hseq_val]
          rcases hcal : evaluateHOLFiniteState ent
              (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx) with ⟨rc, sc⟩
          rw [hcal] at hb_val; dsimp only at hb_val ⊢; subst hb_val
          exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
        | error =>
          have hseq_val : evaluateHOLFiniteState e3 (.seq balRemoveLoop (.return (.const 0#64))) =
              (some .error, sl) := by rw [hseq_loop]; simp only [hlp]
          have hb_val : (evaluateHOLFiniteState ent
              (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx)).1 = some .error := by
            rw [hbody_eq_e3, hseq_val]
          rcases hcal : evaluateHOLFiniteState ent
              (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx) with ⟨rc, sc⟩
          rw [hcal] at hb_val; dsimp only at hb_val ⊢; subst hb_val
          exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
        | exception eid ev =>
          have hnr := hloop_spec.2.2 (.exception eid ev) (by rw [hlp]) (by simp)
          have hseq_val : evaluateHOLFiniteState e3 (.seq balRemoveLoop (.return (.const 0#64))) =
              (some (.exception eid ev), sl) := by rw [hseq_loop]; simp only [hlp]
          have hb_val : (evaluateHOLFiniteState ent
              (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx)).1 =
              some (.exception eid ev) := by
            rw [hbody_eq_e3, hseq_val]
          rcases hcal : evaluateHOLFiniteState ent
              (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx) with ⟨rc, sc⟩
          rw [hcal] at hb_val; dsimp only at hb_val ⊢; subst hb_val
          exact ⟨fun h => by simp at h, fun _ => hnr⟩
        | finalFfi f =>
          have hnr := hloop_spec.2.2 (.finalFfi f) (by rw [hlp]) (by simp)
          have hseq_val : evaluateHOLFiniteState e3 (.seq balRemoveLoop (.return (.const 0#64))) =
              (some (.finalFfi f), sl) := by rw [hseq_loop]; simp only [hlp]
          have hb_val : (evaluateHOLFiniteState ent
              (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx)).1 =
              some (.finalFfi f) := by
            rw [hbody_eq_e3, hseq_val]
          rcases hcal : evaluateHOLFiniteState ent
              (sourceFnBody Guest.Software.guestFn_bal_list_remove_idx) with ⟨rc, sc⟩
          rw [hcal] at hb_val; dsimp only at hb_val ⊢; subst hb_val
          exact ⟨fun h => by simp at h, fun _ => hnr⟩

/-! ## 4. `wk_bal_remove_change` -/

theorem bal_remove_change_f0_nz_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (f0 f1 whichw eszw idxw : BitVec 64) (ck : Nat)
    (hW : WorldOK s)
    (hwh : (whichw.toNat = 16 ∧ eszw.toNat = 40) ∨
           (whichw.toNat = 24 ∧ eszw.toNat = 16) ∨
           (whichw.toNat = 32 ∧ eszw.toNat = 24))
    (hs1_bal : ∀ S Nd, WorldTypedWith s S Nd → f1.toNat ∈ balRecords s) :
    let s1 := setVarHOLFinite (ofString "m") (.rStruct [.val (.word f0), .val (.word f1)])
      { s with clock := ck }
    let prog : ProgHOL 64 :=
      .seq (.call (some (none, none)) (ofString "bal_list_remove_idx")
              [.load .one (.op .add [.rfield 1 (.var .local (ofString "m")), .var .local (ofString "which")]),
               .var .local (ofString "esz"), .var .local (ofString "idx")])
            (.return (.const 0#64))
    s1.locals.lookup (ofString "which") = some (.val (.word whichw)) →
    s1.locals.lookup (ofString "esz") = some (.val (.word eszw)) →
    s1.locals.lookup (ofString "idx") = some (.val (.word idxw)) →
    (evaluateHOLFiniteState s1 prog).1 ≠ some .timeOut →
    Resumes (evaluateHOLFiniteState s1 prog).1 →
    WorldStep (fun _ => []) [] stdKeep NoExtra s
      (evaluateHOLFiniteState s1 prog).1
      { (evaluateHOLFiniteState s1 prog).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 prog).2.locals
            (ofString "m", s.locals.lookup (ofString "m")) } := by
  dsimp only
  intro hs1_which hs1_esz hs1_idx hnt1 hres1
  set s1 := setVarHOLFinite (ofString "m") (.rStruct [.val (.word f0), .val (.word f1)])
    { s with clock := ck }
  have hs1_eq : s1 = { s with locals := s1.locals, clock := ck } := rfl
  have hs1_m : s1.locals.lookup (ofString "m") = some (.rStruct [.val (.word f0), .val (.word f1)]) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hAR0 : ArenaReady s := hW.1
  have hG : GuestInv s := hAR0.1
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  have had0 : f1.toNat ∈ balRecords s := hs1_bal S0 Nd0 hWT0
  have had_fix : (f1.toNat, 40) ∈ fixedObjects s := by
    unfold fixedObjects; apply List.mem_append_right; unfold balObjects
    exact List.mem_flatMap.2 ⟨f1.toNat, had0, List.mem_cons_self⟩
  rcases hWT0.2.2.1.1 _ had_fix with h0 | ⟨hal_ad, hw_ad⟩
  · cases h0
  have had_bnd : f1.toNat + 40 ≤ heapEnd ∧ f1.toNat + 40 ≤ 2 ^ 64 :=
    ivl_allocated_bound hAR0.2 hal_ad
  have had_lo : sourceBase ≤ f1.toNat := by
    rcases hal_ad with h | h
    · exact h.1
    · have h1 := hAR0.2.2.2.1; have h2 := hAR0.2.2.2.2.1
      have h3 : sourceBase ≤ scratchStart := by decide
      exact le_trans h3 (le_trans h1 (le_trans h2 h.1))
  have hwh_bound : whichw.toNat % 8 = 0 ∧ whichw.toNat + 8 ≤ 40 := by
    rcases hwh with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  have had_add_lt : f1.toNat + whichw.toNat < 2 ^ 64 := by
    have := had_bnd.2; have := hwh_bound.2; omega
  have hf1_lt : f1.toNat < 2 ^ 64 := f1.isLt
  have had_add_bv : f1 + whichw = BitVec.ofNat 64 (f1.toNat + whichw.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have had_align : f1.toNat % 8 = 0 := hw_ad.1
  have had_wh_align : (f1.toNat + whichw.toNat) % 8 = 0 := by omega
  have had_wh_lo : sourceBase ≤ f1.toNat + whichw.toNat := by omega
  have had_wh_hi : f1.toNat + whichw.toNat < heapEnd := by omega
  have hdom_ad : s1.memaddrs (f1 + whichw) := by
    change s.memaddrs (f1 + whichw)
    rw [hG.memaddrs, InitECandidate.Solver.Wave8Contracts.M08.ordinaryDomain_iff, had_add_bv,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt had_add_lt]
    exact ⟨had_wh_align, had_wh_lo, had_wh_hi⟩
  have hword_ad : WordAt s (f1.toNat + 8 * (whichw.toNat / 8)) :=
    hw_ad.2.2 (whichw.toNat / 8) (by
      have h2 := hwh_bound.2
      exact Nat.div_lt_of_lt_mul (by omega))
  obtain ⟨lw, _, hlw_mem0⟩ := hword_ad
  have hlw_mem_s : s.memory (f1 + whichw) = .word lw := by
    have heq_addr : BitVec.ofNat 64 (f1.toNat + 8 * (whichw.toNat / 8)) = f1 + whichw := by
      rw [had_add_bv]; apply congrArg (BitVec.ofNat 64)
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hwh_bound.1)]
    rw [← heq_addr]; exact hlw_mem0
  have hlw_mem : s1.memory (f1 + whichw) = .word lw := hlw_mem_s
  have hlw_toNat : lw.toNat = memW s (f1.toNat + whichw.toNat) := by
    change lw.toNat = (match s.memory (BitVec.ofNat 64 (f1.toNat + whichw.toNat)) with | .word w => w.toNat)
    rw [← had_add_bv, hlw_mem_s]
  have hz_wh : whichw + 0 = whichw := BitVec.add_zero _
  have hev_l : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.load .one (.op .add [.rfield 1 (.var .local (ofString "m")), .var .local (ofString "which")])) =
      some (.val (.word lw)) := by
    simp [evalHOLExact, evalListHOLExact, hs1_m, hs1_which,
      valueIsWord, valueWord, wordOpHOL, wordOp, hz_wh,
      memLoadHOLExact, isWfShapeExactHOL, hdom_ad, hlw_mem]
  have hev_e : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.var .local (ofString "esz")) = some (.val (.word eszw)) := by
    simp [evalHOLExact, hs1_esz]
  have hev_x : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.var .local (ofString "idx")) = some (.val (.word idxw)) := by
    simp [evalHOLExact, hs1_idx]
  have hW_s1 : WorldOK s1 := by
    rw [hs1_eq]; exact (worldOK_with_locals s s1.locals ck).2 hW
  have hwh_mem : whichw.toNat ∈ ([16, 24, 32] : List Nat) := by
    rcases hwh with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]; exact List.mem_cons_self
    · rw [h1]; exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [h1]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hesz_disj : eszw.toNat = 16 ∨ eszw.toNat = 24 ∨ eszw.toNat = 40 := by
    rcases hwh with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
    · exact Or.inr (Or.inr h2)
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)
  have hslice_s1 : lw ≠ 0 → ∀ S Nd, WorldTypedWith s1 S Nd →
      LstOK s1 lw.toNat ∧ BalListSlice s1 lw.toNat eszw.toNat := by
    intro _ S Nd hWT_s1
    have hWT_s : WorldTypedWith s S Nd :=
      (worldTypedWith_with_locals s s1.locals ck S Nd).1 (hs1_eq ▸ hWT_s1)
    have had_s : f1.toNat ∈ balRecords s := hs1_bal S Nd hWT_s
    have hsl : BalListSlice s (memW s (f1.toNat + whichw.toNat)) eszw.toNat :=
      bal_list_slice_of_ad_field had_s hwh
    rw [← hlw_toNat] at hsl
    have hlst_s : LstOK s lw.toNat := by
      rw [hlw_toNat]
      exact (hWT_s.1.2.2.2.2.2.2.2.2.2.1 f1.toNat had_s).2.2.1 whichw.toNat hwh_mem
    have hlst_s1 : LstOK s1 lw.toNat := by rw [hs1_eq]; exact hlst_s
    have hsl_s1 : BalListSlice s1 lw.toNat eszw.toNat := by rw [hs1_eq]; exact hsl
    exact ⟨hlst_s1, hsl_s1⟩
  let callProg : ProgHOL 64 :=
    .call (some (none, none)) (ofString "bal_list_remove_idx")
      [.load .one (.op .add [.rfield 1 (.var .local (ofString "m")), .var .local (ofString "which")]),
       .var .local (ofString "esz"), .var .local (ofString "idx")]
  have hseq2 := evaluateHOLFiniteState_seq_line780 s1 callProg (.return (.const 0#64))
  rcases hcall_out : evaluateHOLFiniteState s1 callProg with ⟨rc, sc⟩
  have hcall_nt : rc ≠ some .timeOut := by
    intro hto; subst hto
    rw [hseq2, hcall_out] at hnt1
    exact hnt1 rfl
  have hcall_spec := call_bal_list_remove_idx_eval s1 _ _ _ lw eszw idxw
    hW_s1 hev_l hev_e hev_x hesz_disj hslice_s1 (by rw [hcall_out]; exact hcall_nt)
  rw [hcall_out] at hcall_spec hseq2
  cases rc with
  | none =>
    obtain ⟨_, hws_sc, _, _⟩ := hcall_spec.1 rfl
    have hret_sc : evaluateHOLFiniteState sc (.return (.const 0#64)) =
        (some (PanSemResultExact.returned (.val (.word 0#64))), emptyLocalsHOLFinite sc) := by
      rw [evaluateHOLFiniteState_return]
      simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
      rw [if_pos (by decide)]
    have hseq_ret : evaluateHOLFiniteState s1 (callProg.seq (.return (.const 0#64))) =
        (some (PanSemResultExact.returned (.val (.word 0#64))), emptyLocalsHOLFinite sc) := by
      rw [hseq2]; exact hret_sc
    rw [hseq_ret]; dsimp only
    have hws_s_sc : WorldStep (fun _ => []) [] stdKeep NoExtra s none sc :=
      worldStep_with_locals_left hs1_eq rfl (fun _ _ _ => trivial) hws_sc
    have hws_ret : WorldStep (fun _ => []) [] stdKeep NoExtra s
        (some (PanSemResultExact.returned (.val (.word 0#64)))) sc := by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hws_s_sc
      exact ⟨h1, h2, h3, h4, fun S Nd hWT hD =>
        let ⟨S', Nd', ha, hb, hc, hd, _⟩ := h5 S Nd hWT hD
        ⟨S', Nd', ha, hb, hc, hd, trivial⟩⟩
    have hsc_emp : { emptyLocalsHOLFinite sc with
          locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite sc).locals
            (ofString "m", s.locals.lookup (ofString "m")) } =
        { sc with
          locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite sc).locals
            (ofString "m", s.locals.lookup (ofString "m"))
          clock := sc.clock } := rfl
    rw [hsc_emp]
    exact worldStep_with_locals_right _ sc.clock (fun _ _ _ => trivial) hws_ret
  | some rc' =>
    have hnr : ¬ Resumes (some rc') := hcall_spec.2 (Option.some_ne_none rc')
    have hres_rc : Resumes (some rc') := by rw [hseq2] at hres1; exact hres1
    exact absurd hres_rc hnr

theorem wk_bal_remove_change :
    WorldKeeps BalChangeArg (fun _ => []) []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
     ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "bal_remove_change") := by
  refine ⟨_, _, _, lookup_bal_remove_change, ?_⟩
  intro F s hcode hArg hvalid hnt hres
  obtain ⟨hW, hwh⟩ := hArg
  have hAR0 : ArenaReady s := hW.1
  have hG : GuestInv s := hAR0.1
  obtain ⟨values, hlook_fn⟩ := hvalid
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "bal_remove_change")
    values _ s.locals _ hlook_fn
  simp only [lookupCodeHOLExact, lookup_bal_remove_change] at hx
  rcases values with _ | ⟨va, _ | ⟨vw, _ | ⟨ve, _ | ⟨vx, _ | ⟨_, _⟩⟩⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · simp at hx
  · rcases va with ⟨⟨addrw⟩⟩ | _ | _; swap; · simp [shapeOfHOLExact, shapeEqHOL] at hx
    swap; · simp [shapeOfHOLExact, shapeEqHOL] at hx
    rcases vw with ⟨⟨whichw⟩⟩ | _ | _; swap; · simp [shapeOfHOLExact, shapeEqHOL] at hx
    swap; · simp [shapeOfHOLExact, shapeEqHOL] at hx
    rcases ve with ⟨⟨eszw⟩⟩ | _ | _; swap; · simp [shapeOfHOLExact, shapeEqHOL] at hx
    swap; · simp [shapeOfHOLExact, shapeEqHOL] at hx
    rcases vx with ⟨⟨idxw⟩⟩ | _ | _; swap; · simp [shapeOfHOLExact, shapeEqHOL] at hx
    swap; · simp [shapeOfHOLExact, shapeEqHOL] at hx
    simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hs_locals_eq⟩ := hx
    have hs_addr : s.locals.lookup (ofString "addr") = some (.val (.word addrw)) := by
      have := congrFun hs_locals_eq (ofString "addr")
      simpa [FUPDATE, show ofString "idx" ≠ ofString "addr" by decide,
        show ofString "esz" ≠ ofString "addr" by decide,
        show ofString "which" ≠ ofString "addr" by decide,
        show ofString "addr" ≠ ofString "idx" by decide,
        show ofString "addr" ≠ ofString "esz" by decide,
        show ofString "addr" ≠ ofString "which" by decide] using this.symm
    have hs_which : s.locals.lookup (ofString "which") = some (.val (.word whichw)) := by
      have := congrFun hs_locals_eq (ofString "which")
      simpa [FUPDATE, show ofString "idx" ≠ ofString "which" by decide,
        show ofString "esz" ≠ ofString "which" by decide,
        show ofString "which" ≠ ofString "idx" by decide,
        show ofString "which" ≠ ofString "esz" by decide] using this.symm
    have hs_esz : s.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
      have := congrFun hs_locals_eq (ofString "esz")
      simpa [FUPDATE, show ofString "idx" ≠ ofString "esz" by decide,
        show ofString "esz" ≠ ofString "idx" by decide] using this.symm
    have hs_idx : s.locals.lookup (ofString "idx") = some (.val (.word idxw)) := by
      have := congrFun hs_locals_eq (ofString "idx")
      simpa [FUPDATE] using this.symm
    have hwh_nat : locN s "which" = whichw.toNat := by simp [locN, hs_which]
    have hesz_nat : locN s "esz" = eszw.toNat := by simp [locN, hs_esz]
    rw [hwh_nat, hesz_nat] at hwh
    set cont1 : ProgHOL 64 :=
      .seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
              (.return (.const 0#64)) .skip)
        (.seq (.call (some (none, none)) (ofString "bal_list_remove_idx")
                [.load .one (.op .add [.rfield 1 (.var .local (ofString "m")), .var .local (ofString "which")]),
                 .var .local (ofString "esz"), .var .local (ofString "idx")])
              (.return (.const 0#64)))
    have hbody_eq : sourceFnBody Guest.Software.guestFn_bal_remove_change =
        .decCall (ofString "m") (.comb [.one, .one]) (ofString "htab_get")
          [.var .global (ofString "bal_accounts"), .var .local (ofString "addr")] cont1 := rfl
    rw [hbody_eq] at hnt hres ⊢
    obtain ⟨tw, kw, f0, f1, ck, hev_t, hev_k, htw_nz, hf1_in, hnt1, hres1, heq1_r, heq1_s⟩ :=
      decCall_htab_get_resumes s (ofString "m")
        (.var .global (ofString "bal_accounts")) (.var .local (ofString "addr")) cont1 hG hnt hres
    set s1 := setVarHOLFinite (ofString "m") (.rStruct [.val (.word f0), .val (.word f1)])
      { s with clock := ck }
    have hs1_eq : s1 = { s with locals := s1.locals, clock := ck } := rfl
    have hba_word : ∃ baw : BitVec 64, s.globals.lookup (ofString "bal_accounts") = some (.val (.word baw)) :=
      hAR0.2.2.2.2.2.2.2.2.2 "bal_accounts" (by decide)
    obtain ⟨baw, hbaw⟩ := hba_word
    have htw_eq : tw = baw := by
      simp [evalHOLExact, hbaw] at hev_t; exact hev_t.symm
    have hba_nat : globN s "bal_accounts" = tw.toNat := by
      subst htw_eq; simp [globN, hbaw]
    have hba_nz : globN s "bal_accounts" ≠ 0 := by
      rw [hba_nat]; exact fun h => htw_nz (BitVec.eq_of_toNat_eq (by simpa using h))
    have hs1_m : s1.locals.lookup (ofString "m") = some (.rStruct [.val (.word f0), .val (.word f1)]) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs1_which : s1.locals.lookup (ofString "which") = some (.val (.word whichw)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "m" ≠ ofString "which" by decide, hs_which]
    have hs1_esz : s1.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "m" ≠ ofString "esz" by decide, hs_esz]
    have hs1_idx : s1.locals.lookup (ofString "idx") = some (.val (.word idxw)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "m" ≠ ofString "idx" by decide, hs_idx]
    have hseq1 := evaluateHOLFiniteState_seq_line780 s1
      (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
          (.return (.const 0#64)) .skip)
      (.seq (.call (some (none, none)) (ofString "bal_list_remove_idx")
              [.load .one (.op .add [.rfield 1 (.var .local (ofString "m")), .var .local (ofString "which")]),
               .var .local (ofString "esz"), .var .local (ofString "idx")])
            (.return (.const 0#64)))
    by_cases hf0 : f0 = 0
    · have hite_ret : evaluateHOLFiniteState s1
          (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
              (.return (.const 0#64)) .skip) =
          (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite s1) := by
        rw [evaluateHOLFiniteState_ite]
        have hcmp : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
            (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64)) =
            some (.val (.word 1#64)) := by
          subst hf0; simp [evalHOLExact, hs1_m, Compiler.Encoders.Asm.wordCmpHOL]
        rw [hcmp]; dsimp only
        rw [if_neg (by decide), evaluateHOLFiniteState_return]
        simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
        rw [if_pos (by decide)]
      have hcont1_eq : evaluateHOLFiniteState s1 cont1 =
          (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite s1) := by
        dsimp only [cont1]; rw [hseq1]; simp only [hite_ret]
      have hpost_eq : (evaluateHOLFiniteState s
          (.decCall (ofString "m") (.comb [.one, .one]) (ofString "htab_get")
            [.var .global (ofString "bal_accounts"), .var .local (ofString "addr")] cont1)).2 =
          { s with
              locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite s1).locals (ofString "m", s.locals.lookup (ofString "m"))
              clock := ck } := by
        rw [heq1_s, hcont1_eq]; rfl
      rw [hpost_eq]
      exact worldStep_with_locals_right _ ck (fun _ _ _ => trivial)
        (worldStep_refl (fun _ => []) [] hAR0 rfl)
    · have hf0_64 : f0 ≠ 0#64 := hf0
      have hite_skip : evaluateHOLFiniteState s1
          (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
              (.return (.const 0#64)) .skip) = (none, s1) := by
        rw [evaluateHOLFiniteState_ite]
        have hcmp : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
            (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64)) =
            some (.val (.word 0#64)) := by
          simp [evalHOLExact, hs1_m, Compiler.Encoders.Asm.wordCmpHOL, hf0_64]
        rw [hcmp]; dsimp only
        rw [if_pos (by decide), evaluateHOLFiniteState_skip]
      have hcont1_eq2 : evaluateHOLFiniteState s1 cont1 =
          evaluateHOLFiniteState s1
            (.seq (.call (some (none, none)) (ofString "bal_list_remove_idx")
                    [.load .one (.op .add [.rfield 1 (.var .local (ofString "m")), .var .local (ofString "which")]),
                     .var .local (ofString "esz"), .var .local (ofString "idx")])
                  (.return (.const 0#64))) := by
        dsimp only [cont1]; rw [hseq1]; simp only [hite_skip]
      rw [hcont1_eq2] at hnt1 hres1 heq1_r heq1_s
      have hf1_bal : ∀ S Nd, WorldTypedWith s S Nd → f1.toNat ∈ balRecords s := by
        intro S Nd hWT
        have hba_S : globN s "bal_accounts" ∈ S := by
          rcases hWT.1.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
          · exact absurd h0 hba_nz
          · exact hm
        have hwf_ba : HtabWF s tw.toNat := by rw [← hba_nat]; exact (hWT.1.2.1 _ hba_S).1
        have hin_vals := hf1_in hwf_ba hf0
        unfold balRecords
        rw [if_neg hba_nz, hba_nat]
        exact hin_vals
      rw [heq1_r, heq1_s]
      exact bal_remove_change_f0_nz_step s f0 f1 whichw eszw idxw ck hW hwh hf1_bal
        hs1_which hs1_esz hs1_idx hnt1 hres1
  · simp at hx

/-! ## 5. `bal_stor_htab_del_worldStep` and `wk_remove_storage_write` -/

theorem htab_del_values_subperm_full {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hP : HtabArgWF s)
    (v : ValueHOL 64)
    (hv : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_del)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_del)).2
    HtabExit s post ∧ post.be = s.be ∧ post.globals = s.globals ∧
    ∃ f : Nat → Nat,
      (∀ i (hi : i < (htabValues post (locN s "t")).length),
        ∃ hj : f i < (htabValues s (locN s "t")).length,
          (htabValues post (locN s "t"))[i] = (htabValues s (locN s "t"))[f i]'hj) ∧
      (∀ i1 < (htabValues post (locN s "t")).length,
        ∀ i2 < (htabValues post (locN s "t")).length, i1 ≠ i2 → f i1 ≠ f i2) := by
  dsimp only
  exact htab_del_values_subperm s hcode hP v hv

theorem htabFootprint_len_pos_r16 {F : Type} {s : PanSemStateFiniteExact 64 F} {t : Nat}
    (hwf : HtabWF s t) {i : Ivl} (hi : i ∈ htabFootprint s t) : i.2 ≠ 0 := by
  have hk1 : 1 ≤ hdr s t 0 := hwf.2.2.1
  have hst : hdr s t 1 = (hdr s t 0 + 7) / 8 * 8 := hwf.2.2.2.2.1
  have hnc : 2 ≤ hdr s t 10 := hwf.2.2.2.2.2.1
  simp only [htabFootprint, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · dsimp only; omega
  · dsimp only; rw [hst]
    have h1 : 8 ≤ (hdr s t 0 + 7) / 8 * 8 := by omega
    have h2 : 3 ≤ hdr s t 10 + 1 := by omega
    exact ne_of_gt (Nat.mul_pos (by omega) (by omega))
  · dsimp only; omega
  · dsimp only; omega

theorem ivlUnhit_of_frameOutside_zero_fresh {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {W : List Ivl} {i : Ivl}
    (hhp8 : globN s "heap_ptr" % 8 = 0)
    (hipos : i.2 ≠ 0)
    (hfr : FrameOutside s post W (globN s "heap_ptr", 0))
    (hW_al : ∀ j ∈ W, j.1 % 8 = 0 ∧ j.2 % 8 = 0)
    (hdj : ∀ j ∈ W, Disj i j) :
    M08IvlUnhit s post i := by
  intro a ha8 hlo hhi
  apply hfr a
  · intro j hj hcj
    obtain ⟨hc1, hc2⟩ := hcj
    have ⟨hj1, hj2⟩ := hW_al j hj
    rcases hdj j hj with d | d | d | d <;> omega
  · intro ⟨hc1, hc2⟩
    have hc1' : globN s "heap_ptr" < a.toNat + 8 := hc1
    have hc2' : a.toNat < globN s "heap_ptr" + 0 := hc2
    omega

theorem pairwise_flatMap_subperm_symm {α β : Type} {R : β → β → Prop}
    (hsym : ∀ x y, R x y → R y x)
    {xs ys : List α} (g : α → List β) (f : Nat → Nat)
    (hf_map : ∀ i (hi : i < xs.length), ∃ hj : f i < ys.length, xs[i] = ys[f i]'hj)
    (hf_inj : ∀ i1 < xs.length, ∀ i2 < xs.length, i1 ≠ i2 → f i1 ≠ f i2)
    (hpw : (ys.flatMap g).Pairwise R) :
    (xs.flatMap g).Pairwise R := by
  rw [List.pairwise_flatMap] at hpw ⊢
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
    obtain ⟨hj, heq⟩ := hf_map i hi
    rw [heq]
    exact hpw.1 _ (List.getElem_mem hj)
  · rw [List.pairwise_iff_getElem] at *
    intro i1 i2 hi1 hi2 hlt b hb c hc
    obtain ⟨hj1, heq1⟩ := hf_map i1 hi1
    obtain ⟨hj2, heq2⟩ := hf_map i2 hi2
    rw [heq1] at hb; rw [heq2] at hc
    have hne : f i1 ≠ f i2 := hf_inj i1 hi1 i2 hi2 (by omega)
    rcases Nat.lt_or_gt_of_ne hne with h12 | h21
    · exact hpw.2 (f i1) (f i2) hj1 hj2 h12 b hb c hc
    · exact hsym c b (hpw.2 (f i2) (f i1) hj2 hj1 h21 c hc b hb)

theorem bal_stor_slot_distinct {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hT : TablesTyped s S) {ad0 : Nat} (had0 : ad0 ∈ balRecords s)
    (ht0_nz : memW s ad0 ≠ 0) :
    let t0 := memW s ad0
    t0 ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) := by
  dsimp only
  have ht0_S : memW s ad0 ∈ S := (hT.2.2.2.2.2.2.2.2.2.1 ad0 had0).1
  have ht0_wrs : (memW s ad0, "bal.stor") ∈ worldRoleSlots s := by
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [ht0_nz]⟩
    apply List.mem_append.2; right
    exact List.mem_flatMap.2 ⟨ad0, had0, by simp⟩
  have hslot_ne : ∀ u r, (u, r) ∈ worldRoleSlots s → r ≠ "bal.stor" → u ≠ memW s ad0 := by
    intro u r hur hner heq
    subst heq
    obtain ⟨i1, hi1, heq1⟩ := List.mem_iff_getElem.1 hur
    obtain ⟨i2, hi2, heq2⟩ := List.mem_iff_getElem.1 ht0_wrs
    have hroles := hT.2.2.2.2.2.2.2.2.2.2.2
    rcases Nat.lt_trichotomy i1 i2 with hlt | rfl | hgt
    · have hp := List.pairwise_iff_getElem.1 hroles.2.1 i1 i2 hi1 hi2 hlt
      rw [heq1, heq2] at hp
      exact hner (hp rfl).1
    · rw [heq1] at heq2; exact hner (Prod.mk.inj heq2).2
    · have hp := List.pairwise_iff_getElem.1 hroles.2.1 i2 i1 hi2 hi1 hgt
      rw [heq1, heq2] at hp
      exact hner (hp rfl).1.symm
  refine ⟨ht0_S, ?_, ?_, ?_, ?_⟩
  · intro hbs h32
    apply hslot_ne (memW s (globN s "bs" + 32)) "bs+32" _ (by decide) h32
    have h32_nz : memW s (globN s "bs" + 32) ≠ 0 := by rw [h32]; exact ht0_nz
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [h32_nz]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    simp [recRoles, hbs]
  · intro hts h32
    apply hslot_ne (memW s (globN s "ts" + 32)) "ts+32" _ (by decide) h32
    have h32_nz : memW s (globN s "ts" + 32) ≠ 0 := by rw [h32]; exact ht0_nz
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [h32_nz]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_right
    simp [recRoles, hts]
  · intro hba
    apply hslot_ne (globN s "bal_accounts") "bal_accounts" _ (by decide) hba
    have hba_nz : globN s "bal_accounts" ≠ 0 := by rw [hba]; exact ht0_nz
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [hba_nz]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_right; simp
  · intro hws h32
    apply hslot_ne (memW s (globN s "ws" + 32)) "ws+32" _ (by decide) h32
    have h32_nz : memW s (globN s "ws" + 32) ≠ 0 := by rw [h32]; exact ht0_nz
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [h32_nz]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    simp [recRoles, hws]

theorem pairwise_flatMap_outer_subperm_symm {α β : Type} {R : β → β → Prop}
    (hsym : ∀ x y, R x y → R y x)
    {xs : List α} {F1 F2 : α → List β}
    (hsub : ∀ a ∈ xs, ∀ b ∈ F1 a, b ∈ F2 a)
    (hpw_in : ∀ a ∈ xs, (F2 a).Pairwise R → (F1 a).Pairwise R)
    (hpw : (xs.flatMap F2).Pairwise R) :
    (xs.flatMap F1).Pairwise R := by
  rw [List.pairwise_flatMap] at hpw ⊢
  refine ⟨fun a ha => hpw_in a ha (hpw.1 a ha), ?_⟩
  rw [List.pairwise_iff_getElem] at *
  intro i1 i2 hi1 hi2 hlt b hb c hc
  exact hpw.2 i1 i2 hi1 hi2 hlt b (hsub _ (List.getElem_mem hi1) b hb)
    c (hsub _ (List.getElem_mem hi2) c hc)

theorem balObjects_subperm_of_stor_del {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {S : List Nat} (hT : TablesTyped s S) (hF : FixedTyped s)
    (hba_eq : globN post "bal_accounts" = globN s "bal_accounts")
    {t0 : Nat}
    (hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint s u, M08IvlUnhit s post i)
    (hno_ba : globN s "bal_accounts" ≠ t0)
    (hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → M08IvlUnhit s post i)
    (hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16)
    (f : Nat → Nat)
    (hf_map : ∀ i (hi : i < (htabValues post t0).length),
      ∃ hj : f i < (htabValues s t0).length,
        (htabValues post t0)[i] = (htabValues s t0)[f i]'hj)
    (hf_inj : ∀ i1 < (htabValues post t0).length,
      ∀ i2 < (htabValues post t0).length, i1 ≠ i2 → f i1 ≠ f i2) :
    balRecords post = balRecords s ∧
    (∀ i ∈ balObjects post, i ∈ balObjects s) ∧
    (balObjects post).Pairwise Disj ∧
    (∀ ad ∈ balRecords post,
      memW post ad = memW s ad ∧ memW post (ad + 8) = memW s (ad + 8) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW post (ad + k))) ∧
      (∀ l ∈ htabValues post (memW post ad), LstOK post l)) := by
  have hrecs : balRecords post = balRecords s :=
    InitECandidate.Solver.Wave8Contracts.M08.balRecords_eq_of_unhit hT hba_eq (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_other _ hm hno_ba)
  have hmem_fix_of_bal : ∀ i ∈ balObjects s, i ∈ fixedObjects s := fun i hi =>
    List.mem_append.2 (Or.inr hi)
  have hlst_eq_bal : ∀ l, (l, 24) ∈ balObjects s →
      memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧
      memW post (l + 16) = memW s (l + 16) := by
    intro l hl_bal
    rcases hF.1 _ (hmem_fix_of_bal _ hl_bal) with h0 | ⟨hal_l, hw_l⟩
    · simp at h0
    have hhi_l := (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hA hal_l).2
    have hl8 : l % 8 = 0 := hw_l.1
    have hul := hu_bal _ hl_bal (by simp)
    refine ⟨?_, ?_, ?_⟩
    · simpa using InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
    · exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
    · exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
  have hvals_t0_sub : ∀ l ∈ htabValues post t0, l ∈ htabValues s t0 := by
    intro l hl
    obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.1 hl
    obtain ⟨hj, heq⟩ := hf_map idx hidx
    rw [heq]; exact List.getElem_mem hj
  have had_props : ∀ ad ∈ balRecords s,
      (∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off)) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), ∀ esz,
        lstObjects post (memW s (ad + k)) esz = lstObjects s (memW s (ad + k)) esz ∧
        LstOK post (memW s (ad + k))) ∧
      (∀ l ∈ htabValues s (memW s ad),
        lstObjects post l 40 = lstObjects s l 40 ∧ LstOK post l) ∧
      (∀ l ∈ htabValues post (memW s ad), l ∈ htabValues s (memW s ad)) := by
    intro ad had
    have had_bal : (ad, 40) ∈ balObjects s :=
      List.mem_flatMap.2 ⟨ad, had, by simp⟩
    rcases hF.1 _ (hmem_fix_of_bal _ had_bal) with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hA hal_ad).2
    have had8 : ad % 8 = 0 := hw_ad.1
    have hoff_eq : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off) := by
      intro off hoff
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
        exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit (hu_bal _ had_bal (by simp)) (by omega) hhi_ad ⟨by omega, by omega⟩
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have hfk : ∀ k ∈ ([16, 24, 32] : List Nat), ∀ esz,
        lstObjects post (memW s (ad + k)) esz = lstObjects s (memW s (ad + k)) esz ∧
        LstOK post (memW s (ad + k)) := by
      intro k hk esz
      by_cases hk0 : memW s (ad + k) = 0
      · refine ⟨by simp [lstObjects, hk0], ?_⟩
        have hok := had_T.2.2.1 k hk
        unfold LstOK at hok ⊢; rw [hk0] at hok ⊢; rw [hm0.2.1, hm0.2.2]; exact hok
      · have hmem_b := (bal_chunk_mem_of_record s had).2.1 k hk hk0
        obtain ⟨e0, e8, e16⟩ := hlst_eq_bal _ hmem_b
        refine ⟨by simp [lstObjects, hk0, e0, e16], ?_⟩
        have hok := had_T.2.2.1 k hk
        unfold LstOK at hok ⊢; rw [e8, e16]; exact hok
    have hll : ∀ l ∈ htabValues s (memW s ad),
        lstObjects post l 40 = lstObjects s l 40 ∧ LstOK post l := by
      intro l hl
      by_cases hl0 : l = 0
      · subst hl0
        refine ⟨by simp [lstObjects], ?_⟩
        have hok := had_T.2.2.2 0 hl
        unfold LstOK at hok ⊢; rw [hm0.2.1, hm0.2.2]; exact hok
      · have hmem_b := (bal_chunk_mem_of_record s had).2.2 l hl hl0
        obtain ⟨e0, e8, e16⟩ := hlst_eq_bal l hmem_b
        refine ⟨by simp [lstObjects, hl0, e0, e16], ?_⟩
        have hok := had_T.2.2.2 l hl
        unfold LstOK at hok ⊢; rw [e8, e16]; exact hok
    have hsub_ad : ∀ l ∈ htabValues post (memW s ad), l ∈ htabValues s (memW s ad) := by
      by_cases heq_t : memW s ad = t0
      · rw [heq_t]; exact hvals_t0_sub
      · have hveq := InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit
          (hT.2.1 _ had_T.1).1 (hu_other _ had_T.1 heq_t)
        rw [hveq]; exact fun _ h => h
    exact ⟨hoff_eq, hfk, hll, hsub_ad⟩
  let F_post : Nat → List Ivl := fun ad =>
    (ad, 40) :: lstObjects post (memW post (ad + 16)) 40 ++
      lstObjects post (memW post (ad + 24)) 16 ++ lstObjects post (memW post (ad + 32)) 24 ++
      (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40)
  let F_pre : Nat → List Ivl := fun ad =>
    (ad, 40) :: lstObjects s (memW s (ad + 16)) 40 ++
      lstObjects s (memW s (ad + 24)) 16 ++ lstObjects s (memW s (ad + 32)) 24 ++
      (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40)
  have hF_post_eq_s : ∀ ad ∈ balRecords s,
      F_post ad = (ad, 40) :: lstObjects s (memW s (ad + 16)) 40 ++
        lstObjects s (memW s (ad + 24)) 16 ++ lstObjects s (memW s (ad + 32)) 24 ++
        (htabValues post (memW s ad)).flatMap (fun l => lstObjects s l 40) := by
    intro ad had
    obtain ⟨hoff_eq, hfk, hll, hsub_ad⟩ := had_props ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h16 := hoff_eq 16 (by simp)
    have h24 := hoff_eq 24 (by simp)
    have h32 := hoff_eq 32 (by simp)
    dsimp only [F_post]
    rw [h0, h16, h24, h32, (hfk 16 (by simp) 40).1, (hfk 24 (by simp) 16).1, (hfk 32 (by simp) 24).1]
    congr 1
    exact List.flatMap_congr fun l hl => (hll l (hsub_ad l hl)).1
  have hF_sub : ∀ ad ∈ balRecords s, ∀ b ∈ F_post ad, b ∈ F_pre ad := by
    intro ad had b hb
    rw [hF_post_eq_s ad had] at hb
    dsimp only [F_pre]
    simp only [List.mem_cons, List.mem_append, List.mem_flatMap] at hb ⊢
    rcases hb with (((rfl | h1) | h2) | h3) | ⟨l, hl, hbl⟩
    · exact Or.inl (Or.inl (Or.inl (Or.inl rfl)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h1)))
    · exact Or.inl (Or.inl (Or.inr h2))
    · exact Or.inl (Or.inr h3)
    · exact Or.inr ⟨l, (had_props ad had).2.2.2 l hl, hbl⟩
  have hF_pw_in : ∀ ad ∈ balRecords s, (F_pre ad).Pairwise Disj → (F_post ad).Pairwise Disj := by
    intro ad had hpw_pre
    rw [hF_post_eq_s ad had]
    dsimp only [F_pre] at hpw_pre
    -- F_pre ad = pref ++ (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40)
    -- note: in Lean, `a :: l1 ++ l2 ++ l3 ++ l4` parses as `(((a :: l1) ++ l2) ++ l3) ++ l4`
    have hpw_split := List.pairwise_append.1 hpw_pre
    refine List.pairwise_append.2 ⟨hpw_split.1, ?_, ?_⟩
    · by_cases heq_t : memW s ad = t0
      · rw [heq_t] at hpw_split ⊢
        exact pairwise_flatMap_subperm_symm (fun _ _ h => disj_flip h)
          (fun l => lstObjects s l 40) f hf_map hf_inj hpw_split.2.1
      · have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
        have hveq := InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit
          (hT.2.1 _ had_T.1).1 (hu_other _ had_T.1 heq_t)
        rw [hveq]; exact hpw_split.2.1
    · intro x hx y hy
      obtain ⟨l, hl, hyl⟩ := List.mem_flatMap.1 hy
      exact hpw_split.2.2 x hx y (List.mem_flatMap.2 ⟨l, (had_props ad had).2.2.2 l hl, hyl⟩)
  have hbal_pw_s : (balObjects s).Pairwise Disj := (List.pairwise_append.1 hF.2).2.1
  refine ⟨hrecs, ?_, ?_, ?_⟩
  · intro i hi
    unfold balObjects at hi ⊢
    rw [hrecs] at hi
    obtain ⟨ad, had, hi_ad⟩ := List.mem_flatMap.1 hi
    exact List.mem_flatMap.2 ⟨ad, had, hF_sub ad had i hi_ad⟩
  · change ((balRecords post).flatMap F_post).Pairwise Disj
    rw [hrecs]
    exact pairwise_flatMap_outer_subperm_symm (fun _ _ h => disj_flip h) hF_sub hF_pw_in hbal_pw_s
  · intro ad had
    rw [hrecs] at had
    obtain ⟨hoff_eq, hfk, hll, hsub_ad⟩ := had_props ad had
    have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
    have h8 := hoff_eq 8 (by simp)
    refine ⟨h0, h8, ?_, ?_⟩
    · intro k hk
      have hk_in : k ∈ ([0, 8, 16, 24, 32] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl <;> simp
      rw [hoff_eq k hk_in]
      exact (hfk k hk 40).2
    · intro l hl
      rw [h0] at hl
      exact (hll l (hsub_ad l hl)).2

theorem stor_del_exit_worldStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hW0 : WorldOK s)
    (hbe : post.be = s.be) (hglob : post.globals = s.globals)
    {t0 : Nat}
    (ht0_nz : t0 ≠ 0)
    (ht0_bal : ∀ S Nd, WorldTypedWith s S Nd → ∃ ad ∈ balRecords s, memW s ad = t0)
    (hAp : ArenaReady post) (hwf_t0 : HtabWF post t0)
    (hhdr0_t0 : hdr post t0 0 = hdr s t0 0)
    (hfp_t0 : ∀ i ∈ htabFootprint post t0, Allocated post i ∧
      ((∃ j ∈ htabFootprint s t0, Inside i j.1 (j.1 + j.2)) ∨
        Inside i (globN s "heap_ptr") (globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr"))))
    (hfr : FrameOutside s post (htabFootprint s t0)
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (f : Nat → Nat)
    (hf_map : ∀ i (hi : i < (htabValues post t0).length),
      ∃ hj : f i < (htabValues s t0).length,
        (htabValues post t0)[i] = (htabValues s t0)[f i]'hj)
    (hf_inj : ∀ i1 < (htabValues post t0).length,
      ∀ i2 < (htabValues post t0).length, i1 ≠ i2 → f i1 ≠ f i2) :
    WorldStep (fun _ => []) [] stdKeep NoExtra s r post := by
  have hAs := hW0.1
  have hhp_eq : globN post "heap_ptr" = globN s "heap_ptr" :=
    InitECandidate.Solver.Wave8Contracts.M08.globN_congr hglob "heap_ptr"
  have hsp_eq : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    InitECandidate.Solver.Wave8Contracts.M08.globN_congr hglob "scratch_ptr"
  have hhp : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hhp_eq]
  have hag : AllocatorGrows s post := ⟨hhp, by rw [hsp_eq]⟩
  have hG : GlobalsKept [] s post := fun k _ => by rw [hglob]
  have hgs : InitECandidate.Solver.Wave8Contracts.M08.WorldGlobalsSame s post :=
    InitECandidate.Solver.Wave8Contracts.M08.worldGlobalsSame_of_kept hG (fun _ h => nomatch h)
  have hfr0 : FrameOutside s post (htabFootprint s t0) (globN s "heap_ptr", 0) := by
    intro a h1 h2
    apply hfr a h1
    simpa only [hhp_eq, Nat.sub_self] using h2
  have hfp_t0_in : ∀ i ∈ htabFootprint post t0, Allocated post i ∧
      ∃ j ∈ htabFootprint s t0, Inside i j.1 (j.1 + j.2) := by
    intro i hi
    obtain ⟨hal_i, hcase⟩ := hfp_t0 i hi
    refine ⟨hal_i, ?_⟩
    rcases hcase with hj | hfresh
    · exact hj
    · rw [hhp_eq] at hfresh
      have hipos := htabFootprint_len_pos_r16 hwf_t0 hi
      obtain ⟨h1, h2⟩ := hfresh; omega
  obtain ⟨S0, hWT0_ex⟩ := hW0.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  obtain ⟨ad0_0, had0_0, rfl_t0_0⟩ := ht0_bal S0 Nd0 hWT0
  have ht0_S0 : t0 ∈ S0 := by rw [← rfl_t0_0]; exact (hWT0.1.2.2.2.2.2.2.2.2.2.1 ad0_0 had0_0).1
  have ht0_al0 : ∀ j ∈ htabFootprint s t0, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
    have hw := ((hWT0.1.2.1 t0 ht0_S0).1.1 j hj).2
    exact ⟨hw.1, hw.2.1⟩
  have hrk : RecordsKept (fun _ => []) stdKeep s post := by
    intro ⟨rec_nm, rec_ks⟩ hrec hgnz k hk _
    dsimp only at hgnz hk ⊢
    have hrec_sz : ∃ sz, (rec_nm, sz) ∈ InitECandidate.Solver.Wave8Contracts.M08.typedRecords ∧
        sz ≠ 0 ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [stdKeep, M13.stdKeep, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrec
      rcases hrec with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨40, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨80, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨72, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨88, by decide, by decide, ?_⟩; simp at hk; omega
    obtain ⟨sz, htr, hsz_nz, hk8, hksz⟩ := hrec_sz
    have hmf := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects s htr
    simp only [hgnz, ↓reduceIte] at hmf
    rcases hWT0.2.2.1.1 _ hmf with h0 | ⟨hal, hwords⟩
    · exact absurd h0 hsz_nz
    · have hhi := (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal).2
      have hg8 : (globN s rec_nm) % 8 = 0 := hwords.1
      have hu_rec : M08IvlUnhit s post (globN s rec_nm, sz) :=
        ivlUnhit_of_frameOutside_zero_fresh hAs.2.2.2.2.2.2.1 hsz_nz hfr0 ht0_al0
          (fun j hj => disj_flip (((hWT0.1.2.1 t0 ht0_S0).2 j hj).2 _ hmf))
      exact InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_rec (by omega) hhi ⟨by omega, by omega⟩
  refine ⟨hAp, hhp, hG, hrk, fun S Nd hWT _ => ?_⟩
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  obtain ⟨ad0, had0, had0_eq⟩ := ht0_bal S Nd ⟨hT, hJ, hF, hTr⟩
  have had0_nz : memW s ad0 ≠ 0 := by rw [had0_eq]; exact ht0_nz
  obtain ⟨ht0_S, hno_bs32, hno_ts32, hno_ba, hno_ws32⟩ := by
    have hd := bal_stor_slot_distinct hT had0 had0_nz
    change memW s ad0 ∈ S ∧ _ at hd
    rw [had0_eq] at hd
    exact hd
  have ht0_al : ∀ j ∈ htabFootprint s t0, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
    have hw := ((hT.2.1 t0 ht0_S).1.1 j hj).2
    exact ⟨hw.1, hw.2.1⟩
  have hunhit_disj : ∀ i : Ivl, i.2 ≠ 0 → (∀ j ∈ htabFootprint s t0, Disj i j) →
      M08IvlUnhit s post i := fun i hipos hdi =>
    ivlUnhit_of_frameOutside_zero_fresh hAs.2.2.2.2.2.2.1 hipos hfr0 ht0_al hdi
  have hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint s u, M08IvlUnhit s post i := fun u hu hne i hi =>
    hunhit_disj i (htabFootprint_len_pos_r16 (hT.2.1 u hu).1 hi)
      (fun j hj => hT.2.2.1 u hu t0 ht0_S hne i hi j hj)
  have hu_fix : ∀ i ∈ fixedObjects s, i.2 ≠ 0 → M08IvlUnhit s post i := fun i hi hipos =>
    hunhit_disj i hipos (fun j hj => disj_flip (((hT.2.1 t0 ht0_S).2 j hj).2 i hi))
  have hu_nd_rec : ∀ n ∈ Nd, M08IvlUnhit s post (nodeIvl s n) := fun n hn => by
    have hmem : nodeIvl s n ∈ nodeExtents s Nd :=
      List.mem_flatMap.2 ⟨n, hn, by simp⟩
    have hpos : (nodeIvl s n).2 ≠ 0 := by
      change nodeSize (memW s n) ≠ 0; unfold nodeSize; split_ifs <;> decide
    exact hunhit_disj _ hpos (fun j hj => (hTr.2.1 _ hmem).1 t0 ht0_S j hj)
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    have h264 : heapLimit ≤ 2 ^ 64 := by decide
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, _, hin_p, _⟩
    · exact absurd h0 hlen0
    · have hp_ne : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
      have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by have := hin_p.2; omega
      let c := panByteAlignHOL (BitVec.ofNat 64 (memW s (n + 32) + k))
      have hc_nat : c.toNat = (memW s (n + 32) + k) / 8 * 8 := by
        have hal8 : 2 ^ ((64 : Nat) / 8).log2 = 8 := by decide
        change (BitVec.ofNat 64 ((BitVec.ofNat 64 (memW s (n + 32) + k)).toNat /
          2 ^ ((64 : Nat) / 8).log2 * 2 ^ ((64 : Nat) / 8).log2)).toNat =
          (memW s (n + 32) + k) / 8 * 8
        rw [hal8, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt,
          Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self _ 8) ha_lt)]
      have hmem := hfr0 c
        (fun j hj hcj => by
          obtain ⟨h1, h2⟩ := hcj
          rw [hc_nat] at h1 h2
          have ⟨hj1, hj2⟩ := ht0_al j hj
          have hdj := (hTr.2.1 _ hp_ne).1 t0 ht0_S j hj
          rcases hdj with d | d | d | d
          · change (memW s (n + 32), memW s (n + 40)).2 = 0 at d; dsimp only at d; omega
          · change j.2 = 0 at d; omega
          · change memW s (n + 32) + memW s (n + 40) ≤ j.1 at d
            change j.1 < (memW s (n + 32) + k) / 8 * 8 + 8 at h1; omega
          · change j.1 + j.2 ≤ memW s (n + 32) at d
            change (memW s (n + 32) + k) / 8 * 8 < j.1 + j.2 at h2; omega)
        (InitECandidate.Solver.Wave8Contracts.M08.not_cellHits_of_disj (i := (c.toNat, 8))
          (by rw [hc_nat]; omega) hAs.2.2.2.2.2.2.1 ⟨le_rfl, le_rfl⟩ (Or.inr (Or.inl rfl)))
      unfold memB
      change (match post.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v post.be).toNat) =
             (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v s.be).toNat)
      rw [hmem, hbe]
  have hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    have hlow : ∀ a : Nat, a + 8 ≤ sourceBase → a % 8 = 0 → memW post a = memW s a := fun a ha ha8 => by
      have hsb_lt : sourceBase < 2 ^ 64 := by decide
      have ha_lt : a < 2 ^ 64 := lt_of_le_of_lt (by omega) hsb_lt
      have hbva : (BitVec.ofNat 64 a).toNat = a := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
      have hm := hfr0 (BitVec.ofNat 64 a)
        (fun j hj hcj => by
          obtain ⟨h1, _⟩ := hcj
          rw [hbva] at h1
          have hlo := ((hT.2.1 t0 ht0_S).1.1 j hj).1.1
          omega)
        (InitECandidate.Solver.Wave8Contracts.M08.not_cellHits_of_disj (i := (a, 8))
          (by rw [hbva]; exact ha8) hAs.2.2.2.2.2.2.1 (by rw [hbva]; exact ⟨le_rfl, le_rfl⟩)
          (Or.inr (Or.inl rfl)))
      unfold memW; rw [hm]
    exact ⟨hlow 0 (by decide) (by decide), hlow 8 (by decide) (by decide), hlow 16 (by decide) (by decide)⟩
  have hu_ws : globN s "ws" ≠ 0 → M08IvlUnhit s post (globN s "ws", 40) := fun hnz => by
    have hm := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects s
      (r := ("ws", 40)) (by decide)
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by simp)
  have hu_bs : globN s "bs" ≠ 0 → M08IvlUnhit s post (globN s "bs", 80) := fun hnz => by
    have hm := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects s
      (r := ("bs", 80)) (by decide)
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by simp)
  have hu_ts : globN s "ts" ≠ 0 → M08IvlUnhit s post (globN s "ts", 72) := fun hnz => by
    have hm := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects s
      (r := ("ts", 72)) (by decide)
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by simp)
  have hu_bo : globN s "bo" ≠ 0 → M08IvlUnhit s post (globN s "bo", 88) := fun hnz => by
    have hm := InitECandidate.Solver.Wave8Contracts.M08.typedRecord_mem_fixedObjects s
      (r := ("bo", 88)) (by decide)
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by simp)
  have hu_jr : globN s "journal_cap" ≠ 0 →
      M08IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := fun hnz => by
    apply hu_fix _ _ (by change 32 * globN s "journal_cap" ≠ 0; omega)
    unfold fixedObjects
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    simp [hnz]
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → M08IvlUnhit s post i := fun i hi h24 =>
    hu_fix i (List.mem_append_left _ (List.mem_append_right _ hi)) (by omega)
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → M08IvlUnhit s post i := fun i hi hipos =>
    hu_fix i (List.mem_append_right _ hi) hipos
  have hbo_g : globN post "bo" = globN s "bo" :=
    InitECandidate.Solver.Wave8Contracts.M08.globN_congr hglob "bo"
  have hws_g : globN post "ws" = globN s "ws" :=
    InitECandidate.Solver.Wave8Contracts.M08.globN_congr hglob "ws"
  have hbs_g : globN post "bs" = globN s "bs" :=
    InitECandidate.Solver.Wave8Contracts.M08.globN_congr hglob "bs"
  have hts_g : globN post "ts" = globN s "ts" :=
    InitECandidate.Solver.Wave8Contracts.M08.globN_congr hglob "ts"
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" :=
    InitECandidate.Solver.Wave8Contracts.M08.globN_congr hglob "bal_accounts"
  have hbia_g : globN post "bal_idx_accts" = globN s "bal_idx_accts" :=
    InitECandidate.Solver.Wave8Contracts.M08.globN_congr hglob "bal_idx_accts"
  have hbis_g : globN post "bal_idx_stor" = globN s "bal_idx_stor" :=
    InitECandidate.Solver.Wave8Contracts.M08.globN_congr hglob "bal_idx_stor"
  have htr_ws : ("ws", 40) ∈ InitECandidate.Solver.Wave8Contracts.M08.typedRecords := by decide
  have htr_bs : ("bs", 80) ∈ InitECandidate.Solver.Wave8Contracts.M08.typedRecords := by decide
  have htr_ts : ("ts", 72) ∈ InitECandidate.Solver.Wave8Contracts.M08.typedRecords := by decide
  have htr_bo : ("bo", 88) ∈ InitECandidate.Solver.Wave8Contracts.M08.typedRecords := by decide
  have hbo_words : globN s "bo" ≠ 0 → ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := fun hnz k hk => by
    have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    simpa [hbo_g] using InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
      hAs.2 hF "bo" 88 htr_bo hbo_g hnz (hu_bo hnz) hk_in.1 hk_in.2
  have hbo_part := InitECandidate.Solver.Wave8Contracts.M08.blockOutObjects_eq_of_bo_unhit
    hAs.2 hF hbo_g hT.2.2.2.2.2.2.2.2.2.2.1
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
  obtain ⟨hrecs_bal, hbal_sub, hbal_pw, hbal_ad⟩ := balObjects_subperm_of_stor_del
    hAs.2 hT hF hba_g hu_other hno_ba hu_bal hm0 f hf_map hf_inj
  have hfix_pref_eq :
      (globalBuffers.map fun gn => (globN post gn.1, if globN post gn.1 = 0 then 0 else gn.2)) ++
        [(if globN post "journal_cap" = 0 then 0 else globN post "journal", 32 * globN post "journal_cap")] ++
        blockOutObjects post =
      (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++
        [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
        blockOutObjects s := by
    rw [hbo_part.1, hgs.2.2.1, hgs.2.2.2.1]
    congr 2
    apply List.map_congr_left
    intro gn hgn; rw [hgs.1 gn hgn]
  have hfix_sub : ∀ i ∈ fixedObjects post, i ∈ fixedObjects s := by
    intro i hi
    unfold fixedObjects at hi ⊢
    rw [hfix_pref_eq] at hi
    rcases List.mem_append.1 hi with h1 | h2
    · exact List.mem_append_left _ h1
    · exact List.mem_append_right _ (hbal_sub i h2)
  have hF_post : FixedTyped post := by
    refine ⟨fun i hi => ?_, ?_⟩
    · rcases hF.1 i (hfix_sub i hi) with h0 | ⟨hal_i, hw_i⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hag.allocated hal_i,
          InitECandidate.Solver.Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 hw_i⟩
    · unfold fixedObjects
      rw [hfix_pref_eq]
      have hpw_s := List.pairwise_append.1 hF.2
      exact List.pairwise_append.2 ⟨hpw_s.1, hbal_pw, fun x hx y hy => hpw_s.2.2 x hx y (hbal_sub y hy)⟩
  obtain ⟨hjr_eq, hJ_post⟩ := InitECandidate.Solver.Wave8Contracts.M08.journalRoleSlots_eq_of_unhit
    hAs.1 hAp.1 hAs.2 hag (fun _ hx => hx) hJ hF hgs hu_ts hu_jr
  have hwrs_eq : worldRoleSlots post = worldRoleSlots s := by
    have hrec_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] =
        recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
      unfold recRoles
      by_cases h : globN s "ws" = 0
      · simp [hws_g, h]
      · have hw16 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ws" 40 htr_ws hws_g h (hu_ws h) (k := 16) (by omega) (by omega)
        have hw32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ws" 40 htr_ws hws_g h (hu_ws h) (k := 32) (by omega) (by omega)
        simp only [hws_g] at hw16 hw32 ⊢; simp [h, hw16, hw32]
    have hrec_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
        (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
        recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
        (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
      unfold recRoles
      by_cases h : globN s "bs" = 0
      · simp [hbs_g, h]
      · simp only [hbs_g, h, ↓reduceIte]
        apply List.map_congr_left
        intro ⟨k, r0⟩ hkr
        have hk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
          rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        have hw := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "bs" 80 htr_bs hbs_g h (hu_bs h) hk.1 hk.2
        simp only [hbs_g] at hw; simp [hw]
    have hrec_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
        recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
      unfold recRoles
      by_cases h : globN s "ts" = 0
      · simp [hts_g, h]
      · simp only [hts_g, h, ↓reduceIte]
        apply List.map_congr_left
        intro ⟨k, r0⟩ hkr
        have hk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
          rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        have hw := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ts" 72 htr_ts hts_g h (hu_ts h) hk.1 hk.2
        simp only [hts_g] at hw; simp [hw]
    have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
      unfold nestRoles
      by_cases h : globN s "bs" = 0
      · simp [hbs_g, h]
      · have hw32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "bs" 80 htr_bs hbs_g h (hu_bs h) (k := 32) (by omega) (by omega)
        simp only [hbs_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
        by_cases h32 : memW s (globN s "bs" + 32) = 0
        · simp [h32]
        · simp only [h32, ↓reduceIte]
          have hmS : memW s (globN s "bs" + 32) ∈ S := by
            rcases hT.2.2.2.2.1 32 (by simp [bsTableSlots]) h with h0 | hm
            · exact absurd h0 h32
            · exact hm
          rw [InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit
            (hT.2.1 _ hmS).1 (hu_other _ hmS (hno_bs32 h))]
    have hnest_ts : nestRoles post "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
      unfold nestRoles
      by_cases h : globN s "ts" = 0
      · simp [hts_g, h]
      · have hw32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ts" 72 htr_ts hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
        simp only [hts_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
        by_cases h32 : memW s (globN s "ts" + 32) = 0
        · simp [h32]
        · simp only [h32, ↓reduceIte]
          have hmS : memW s (globN s "ts" + 32) ∈ S := by
            rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) h with h0 | hm
            · exact absurd h0 h32
            · exact hm
          rw [InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit
            (hT.2.1 _ hmS).1 (hu_other _ hmS (hno_ts32 h))]
    unfold worldRoleSlots
    rw [hrec_ws, hrec_bs, hrec_ts, hba_g, hbia_g, hbis_g, hnest_bs, hnest_ts, hrecs_bal]
    congr 1; congr 1
    apply List.flatMap_congr
    intro ad had
    have had_p : ad ∈ balRecords post := by rwa [hrecs_bal]
    obtain ⟨e0, e8, _⟩ := hbal_ad ad had_p
    rw [e0, e8]
  obtain ⟨hNH_post, hne_eq⟩ := InitECandidate.Solver.Wave8Contracts.M08.nodeHeap_congr_bytes
    hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_byte
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hother_fp : ∀ u ∈ S, u ≠ t0 →
      (∀ k, k < 11 → hdr post u k = hdr s u k) ∧ htabFootprint post u = htabFootprint s u := by
    intro u hu hne
    have hfp := (hT.2.1 u hu).1.1
    have ht_fp : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
    exact InitECandidate.Solver.Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit
      ((hfp _ ht_fp).2.1) (by have := (hfp _ ht_fp).1.2; dsimp at this; omega)
      (hu_other u hu hne _ ht_fp)
  have ht0_disj_other : ∀ i ∈ htabFootprint post t0,
      (∀ u ∈ S, u ≠ t0 → ∀ j ∈ htabFootprint s u, Disj i j) ∧
      (∀ j ∈ fixedObjects s, Disj i j) ∧
      (∀ o ∈ nodeExtents s Nd, Disj i o) := by
    intro i hi
    obtain ⟨_, k, hk, hin⟩ := hfp_t0_in i hi
    refine ⟨fun u hu hne j hj => InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_left hin
              (hT.2.2.1 t0 ht0_S u hu hne.symm k hk j hj),
            fun j hj => InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_left hin
              (((hT.2.1 t0 ht0_S).2 k hk).2 j hj),
            fun o ho => InitECandidate.Solver.Wave8Contracts.M08.disj_of_inside_left hin
              (disj_flip ((hTr.2.1 o ho).1 t0 ht0_S k hk))⟩
  have hT_post : TablesTyped post S := by
    obtain ⟨hnd, htwf, htpw, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, _, hroles⟩ := hT
    refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_part.2, ?_⟩
    · intro u hu
      by_cases heq : u = t0
      · subst heq
        exact ⟨hwf_t0, fun i hi => ⟨(hfp_t0_in i hi).1, fun j hj => (ht0_disj_other i hi).2.1 j (hfix_sub j hj)⟩⟩
      · rw [(hother_fp u hu heq).2]
        exact ⟨InitECandidate.Solver.Wave8Contracts.M08.htabWF_congr_unhit hAs.1 hAp.1 (htwf u hu).1 (hu_other u hu heq),
          fun i hi => ⟨hag.allocated ((htwf u hu).2 i hi).1, fun j hj => ((htwf u hu).2 i hi).2 j (hfix_sub j hj)⟩⟩
    · intro u hu v hv hne i hi j hj
      by_cases hu0 : u = t0
      · subst hu0; rw [(hother_fp v hv hne.symm).2] at hj
        exact (ht0_disj_other i hi).1 v hv hne.symm j hj
      · by_cases hv0 : v = t0
        · subst hv0; rw [(hother_fp u hu hu0).2] at hi
          exact disj_flip ((ht0_disj_other j hj).1 u hu hu0 i hi)
        · rw [(hother_fp u hu hu0).2] at hi; rw [(hother_fp v hv hv0).2] at hj
          exact htpw u hu v hv hne i hi j hj
    · intro k hk hnz
      rw [hws_g] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ws" 40 htr_ws hws_g hnz (hu_ws hnz) hk8.1 hk8.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [hbs_g] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "bs" 80 htr_bs hbs_g hnz (hu_bs hnz) hk8.1 hk8.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [hts_g] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ts" 72 htr_ts hts_g hnz (hu_ts hnz) hk8.1 hk8.2]
      exact htsR k hk hnz
    · intro g hg_mem; rw [hgs.2.1 g hg_mem]; exact hgR g hg_mem
    · intro hnz hmem
      rw [hbs_g] at hnz
      have ew := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "bs" 80 htr_bs hbs_g hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact InitECandidate.Solver.Wave8Contracts.M08.htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_other _ hmem (hno_bs32 hnz)) (fun _ hx => hx) (hbsN hnz hmem)
    · intro hnz hmem
      rw [hts_g] at hnz
      have ew := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ts" 72 htr_ts hts_g hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact InitECandidate.Solver.Wave8Contracts.M08.htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_other _ hmem (hno_ts32 hnz)) (fun _ hx => hx) (htsN hnz hmem)
    · intro ad had
      have had_s : ad ∈ balRecords s := by rwa [← hrecs_bal]
      obtain ⟨e0, e8, hkl, hll⟩ := hbal_ad ad had
      exact ⟨e0 ▸ (hbalT ad had_s).1, e8 ▸ (hbalT ad had_s).2.1, hkl, hll⟩
    · unfold RolesOK at hroles ⊢
      rw [hwrs_eq, hjr_eq]
      refine ⟨fun a ha => ?_, hroles.2⟩
      obtain ⟨haS, hkl⟩ := hroles.1 a ha
      by_cases ha0 : a.1 = t0
      · rw [ha0] at hkl ⊢; exact ⟨ht0_S, hhdr0_t0.trans hkl⟩
      · exact ⟨haS, ((hother_fp a.1 haS ha0).1 0 (by omega)).trans hkl⟩
  have hTr_post : TriesTypedWith post S Nd := by
    refine ⟨hNH_post, ?_, ?_⟩
    · rw [hne_eq]
      intro o ho
      refine ⟨fun u hu i hi => ?_, fun j hj => (hTr.2.1 o ho).2 j (hfix_sub j hj)⟩
      by_cases hu0 : u = t0
      · subst hu0; exact disj_flip ((ht0_disj_other i hi).2.2 o ho)
      · rw [(hother_fp u hu hu0).2] at hi; exact (hTr.2.1 o ho).1 u hu i hi
    · intro hws_nz
      rw [hws_g] at hws_nz
      have e24 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ws" 40 htr_ws hws_g hws_nz (hu_ws hws_nz) (k := 24) (by omega) (by omega)
      have e32 := InitECandidate.Solver.Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ws" 40 htr_ws hws_g hws_nz (hu_ws hws_nz) (k := 32) (by omega) (by omega)
      rw [e24, e32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hws_nz
      refine ⟨hr24, fun htS i hi => ?_⟩
      have hne32 := hno_ws32 hws_nz
      have hu32 := hu_other _ htS hne32
      have hwf32 := (hT.2.1 _ htS).1
      have hvals_eq := InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit hwf32 hu32
      obtain ⟨hhdr32, _⟩ := hother_fp _ htS hne32
      rw [hhdr32 3 (by omega)] at hi
      have hget : (htabValues post (memW s (globN s "ws" + 32)))[i]? =
          (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals_eq]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hhdr32 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]; exact hr32 htS i hi
  refine ⟨S, Nd, fun _ h => h, ⟨hT_post, hJ_post, hF_post, hTr_post⟩, ?_, ?_, trivial⟩
  · intro o ho
    change o ∈ S.flatMap (htabFootprint post) ++ fixedObjects post ++ nodeExtents post Nd at ho
    rcases List.mem_append.1 ho with ho12 | ho_nd
    · rcases List.mem_append.1 ho12 with ho_tab | ho_fix
      · obtain ⟨u, hu, hi⟩ := List.mem_flatMap.1 ho_tab
        by_cases hu0 : u = t0
        · subst hu0
          obtain ⟨_, j, hj, hin⟩ := hfp_t0_in o hi
          refine Or.inr (Or.inl ⟨j, ?_, hin⟩)
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u, hu, hj⟩))
        · rw [(hother_fp u hu hu0).2] at hi
          refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u, hu, hi⟩))
      · refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
        exact List.mem_append_left _ (List.mem_append_right _ (hfix_sub o ho_fix))
    · rw [hne_eq] at ho_nd
      refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
      exact List.mem_append_right _ ho_nd
  · intro a hkeep hnf
    apply hfr0 a
    · intro j hj
      apply hkeep j
      apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t0, ht0_S, hj⟩))
    · intro hc
      apply hnf
      exact ⟨hc.1, Nat.lt_of_lt_of_le hc.2 (Nat.le_add_right (globN s "heap_ptr") _)⟩

theorem call_bal_stor_htab_del_eval {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tExp keyExp : ExpHOL 64) (tw kw : BitVec 64)
    (hW : WorldOK s)
    (hev_t : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) tExp =
      some (.val (.word tw)))
    (hev_k : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) keyExp =
      some (.val (.word kw)))
    (htw_nz : tw ≠ 0)
    (htw_bal : ∀ S Nd, WorldTypedWith s S Nd → ∃ ad ∈ balRecords s, memW s ad = tw.toNat)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_del") [tExp, keyExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_del") [tExp, keyExp])
    (out.1 = none →
      WorldStep (fun _ => []) [] stdKeep NoExtra s out.1 out.2 ∧
      out.2.locals = s.locals) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  dsimp only
  have hG := hW.1.1
  have hAs := hW.1
  have htw_nz_nat : tw.toNat ≠ 0 := fun h => htw_nz (BitVec.eq_of_toNat_eq (by simpa using h))
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [tExp, keyExp] = some [.val (.word tw), .val (.word kw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hev_t, hev_k]
  rw [hargs] at hnt ⊢; dsimp only at hnt ⊢
  have hlook : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup (ofString "htab_del")
      [.val (.word tw), .val (.word kw)] =
      some (sourceFnBody Guest.Software.guestFn_htab_del,
        (HolFiniteMapExact.empty.update (ofString "t", ValueHOL.val (.word tw))).update
          (ofString "key", ValueHOL.val (.word kw)),
        .one) := by
    rw [hG.code]
    exact InitECandidate.Solver.GuestTrapAndLookup.pan_two_word_lookup
      originalRuntimeCode.lookup (ofString "htab_del")
      (ofString "t") (ofString "key") (sourceFnBody Guest.Software.guestFn_htab_del)
      tw kw (by decide) lookup_htab_del
  rw [hlook] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at hnt; exact absurd rfl hnt
  · rw [if_neg hcz] at hnt ⊢
    let cmap := (HolFiniteMapExact.empty.update (ofString "t", ValueHOL.val (.word tw))).update
      (ofString "key", ValueHOL.val (.word kw))
    let ent := callEntryStateHOLFinite s cmap
    have hent_eq : ent = { s with locals := cmap, clock := s.clock - 1 } := rfl
    have hent_code : ent.code = originalRuntimeCode := hG.code
    have hent_t : locN ent "t" = tw.toNat := by
      simp [locN, ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "key" ≠ ofString "t" by decide]
    obtain ⟨S0, hWT0_ex⟩ := hW.2
    obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
    obtain ⟨ad0, had0, had0_eq⟩ := htw_bal S0 Nd0 hWT0
    have htw_S0 : tw.toNat ∈ S0 := by
      rw [← had0_eq]; exact (hWT0.1.2.2.2.2.2.2.2.2.2.1 ad0 had0).1
    have hP_ent : HtabArgWF ent := by
      refine ⟨(arenaReady_with_locals s cmap (s.clock - 1)).2 hAs, ?_, ?_⟩
      · rw [hent_t, hent_eq, htabWF_with_locals]; exact (hWT0.1.2.1 _ htw_S0).1
      · rw [hent_t]; intro i hi
        change Allocated s i
        exact ((hWT0.1.2.1 _ htw_S0).2 i hi).1
    have hcal_spec := htab_del_values_subperm_full ent hent_code hP_ent
    have hnc_ent := htab_del_no_catchable_exn ent hent_code
    dsimp only [ent] at hcal_spec hnc_ent
    rcases hcal : evaluateHOLFiniteState
        (callEntryStateHOLFinite s
          ((HolFiniteMapExact.empty.update (ofString "t", ValueHOL.val (.word tw))).update
            (ofString "key", ValueHOL.val (.word kw))))
        (sourceFnBody Guest.Software.guestFn_htab_del) with ⟨rc, sc⟩
    have hcal_cmap : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_htab_del) = (rc, sc) := hcal
    rw [hcal_cmap] at hcal_spec hnc_ent
    dsimp only at hnt hcal_spec hnc_ent ⊢
    cases rc with
    | none => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
    | some r =>
      cases r with
      | timeOut =>
        exfalso; apply hnt; rw [hcal]
      | «break» => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
      | «continue» => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
      | error => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
      | finalFfi f =>
        exact ⟨fun h => by simp at h, fun _ => by
          rintro (⟨v, hv⟩ | ⟨e, v, hv, _⟩) <;> cases hv⟩
      | exception eid ev =>
        exact ⟨fun h => by simp at h, fun _ => by
          rintro (⟨v, hv⟩ | ⟨e, v, hv, hne⟩)
          · cases hv
          · injection hv with h1; injection h1 with he1 hv1
            subst he1; subst hv1
            exact hnc_ent eid ev hne rfl⟩
      | returned v =>
        dsimp only at hnt ⊢
        by_cases hsh : shapeEqHOL (shapeOfHOLExact v) .one = true
        · rw [if_pos hsh]
          obtain ⟨hExit, hbe_sc, hg_sc, f, hf_map, hf_inj⟩ := hcal_spec v rfl
          have hent_t' : locN (callEntryStateHOLFinite s cmap) "t" = tw.toNat := hent_t
          rw [hent_t'] at hf_map hf_inj
          obtain ⟨hAp_sc, hwf_sc, hhdr0_sc, _, _, hfp_sc, hfr_sc, _⟩ := hExit
          rw [hent_t'] at hwf_sc hhdr0_sc hfp_sc hfr_sc
          let post := { sc with locals := s.locals }
          have hAp_post : ArenaReady post :=
            (arenaReady_with_locals sc s.locals sc.clock).2 hAp_sc
          have hbe_post : post.be = s.be := hbe_sc
          have hg_post : post.globals = s.globals := hg_sc
          have hwf_post : HtabWF post tw.toNat :=
            (htabWF_with_locals sc s.locals sc.clock tw.toNat).2 hwf_sc
          have hhdr0_post : hdr post tw.toNat 0 = hdr s tw.toNat 0 := hhdr0_sc
          have hfp_post : ∀ i ∈ htabFootprint post tw.toNat, Allocated post i ∧
              ((∃ j ∈ htabFootprint s tw.toNat, Inside i j.1 (j.1 + j.2)) ∨
                Inside i (globN s "heap_ptr") (globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr"))) :=
            hfp_sc
          have hfr_post : FrameOutside s post (htabFootprint s tw.toNat)
              (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := hfr_sc
          have hws : WorldStep (fun _ => []) [] stdKeep NoExtra s none post :=
            stor_del_exit_worldStep hW hbe_post hg_post htw_nz_nat htw_bal hAp_post hwf_post
              hhdr0_post hfp_post hfr_post f hf_map hf_inj
          exact ⟨fun _ => ⟨hws, rfl⟩, fun h => False.elim (h rfl)⟩
        · rw [if_neg hsh]
          exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩

theorem worldStep_nil_trans {F : Type}
    {s m post : PanSemStateFiniteExact 64 F}
    {r1 r2 : Option (PanSemResultExact 64)}
    (hAs : ArenaOK s)
    (h1 : WorldStep (fun _ => []) [] stdKeep NoExtra s r1 m)
    (h2 : WorldStep (fun _ => []) [] stdKeep NoExtra m r2 post) :
    WorldStep (fun _ => []) [] stdKeep NoExtra s r2 post := by
  have hsp_eq : globN m "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (h1.2.2.1 (ofString "scratch_ptr") (by simp))
  exact worldStep_trans_bufs hAs h1 h2 (by rw [hsp_eq]) rfl
    (fun _ _ _ x hx => nomatch hx) (fun _ _ => by simp) (fun _ _ _ _ _ _ => trivial)

theorem bal_stor_list_remove_preserves_ad_t {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {ad l : Nat}
    (hW : WorldOK s)
    (had : ad ∈ balRecords s)
    (hl : l ∈ htabValues s (memW s ad))
    (hl_nz : l ≠ 0)
    (heff : M11.ByteRegionEffect s post
      [(l + 8, 8), (memW s l, 40 * memW s (l + 16))]) :
    balRecords post = balRecords s ∧
    memW post ad = memW s ad ∧
    htabValues post (memW s ad) = htabValues s (memW s ad) := by
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hT, hJ, hF, hTr⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  have hAs := hW.1
  have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
  have hlst : LstOK s l := had_T.2.2.2 l hl
  have hslice : BalListSlice s l 40 := bal_list_slice_of_stor_val had hl
  obtain ⟨hl_fix, hp_fix, _, had_dj, _, _⟩ :=
    bal_list_slice_props hF hl_nz (Or.inr (Or.inr rfl)) hlst hslice
  have hunhit_of_disj : ∀ (j : Ivl), Disj j (l, 24) → Disj j (memW s l, 40 * memW s (l + 16)) →
      M08IvlUnhit s post j := by
    intro j hdj1 hdj2 a ha8 hj1 hj2
    apply heff.cell_frame a
    intro x hx hcx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain ⟨hc1, hc2⟩ := hcx
    rcases hx with rfl | rfl
    · change l + 8 < a.toNat + 8 at hc1
      change a.toNat < l + 8 + 8 at hc2
      rcases hdj1 with d | d | d | d
      · change j.2 = 0 at d; omega
      · change (24 : Nat) = 0 at d; omega
      · change j.1 + j.2 ≤ l at d; omega
      · change l + 24 ≤ j.1 at d; omega
    · change memW s l < a.toNat + 8 at hc1
      change a.toNat < memW s l + 40 * memW s (l + 16) at hc2
      have hpos_arr : 40 * memW s (l + 16) ≠ 0 := by have := hlst.1; omega
      rcases hdj2 with d | d | d | d
      · change j.2 = 0 at d; omega
      · exact absurd d hpos_arr
      · change j.1 + j.2 ≤ memW s l at d; omega
      · change memW s l + 40 * memW s (l + 16) ≤ j.1 at d; omega
  have hu_tab : ∀ t ∈ S0, ∀ i ∈ htabFootprint s t, M08IvlUnhit s post i := fun t ht i hi =>
    hunhit_of_disj i (((hT.2.1 t ht).2 i hi).2 _ hl_fix) (((hT.2.1 t ht).2 i hi).2 _ hp_fix)
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" := by
    simp [globN, heff.globals]
  have hrecs : balRecords post = balRecords s :=
    InitECandidate.Solver.Wave8Contracts.M08.balRecords_eq_of_unhit hT hba_g (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_tab _ hm)
  have had_fix : (ad, 40) ∈ fixedObjects s :=
    List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨ad, had, by simp⟩))
  rcases hF.1 _ had_fix with h0 | ⟨hal_ad, hw_ad⟩
  · simp at h0
  have hhi_ad := (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_ad).2
  have hu_ad := hunhit_of_disj _ (had_dj ad had).1 (had_dj ad had).2
  have had_w0 : memW post ad = memW s ad := by
    have h0 := InitECandidate.Solver.Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_ad
      (a := ad + 0) (by have := hw_ad.1; omega) hhi_ad ⟨by omega, by omega⟩
    simpa using h0
  have hvals : htabValues post (memW s ad) = htabValues s (memW s ad) :=
    InitECandidate.Solver.Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ had_T.1).1 (hu_tab _ had_T.1)
  exact ⟨hrecs, had_w0, hvals⟩

def removeStorAfterListProg : ProgHOL 64 :=
  .seq
    (.ite (.cmp .equal (.load .one (.op .add [.rfield 1 (.var .local (ofString "sl")), .const 8#64])) (.const 0#64))
      (.call (some (none, none)) (ofString "htab_del")
        [.var .local (ofString "t"), .var .local (ofString "slot")])
      .skip)
    (.return (.const 0#64))

def removeStorSlFoundProg : ProgHOL 64 :=
  .seq
    (.call (some (none, none)) (ofString "bal_list_remove_idx")
      [.rfield 1 (.var .local (ofString "sl")), .const 40#64, .var .local (ofString "idx")])
    removeStorAfterListProg

theorem remove_storage_write_after_list_step {F : Type}
    (s m : PanSemStateFiniteExact 64 F) (sl0 lw tw slotw : BitVec 64)
    (hW_s : WorldOK s)
    (hws_sm : WorldStep (fun _ => []) [] stdKeep NoExtra s none m)
    (hlw_nz : lw ≠ 0)
    (htw_nz : tw ≠ 0)
    (hm_sl : m.locals.lookup (ofString "sl") = some (.rStruct [.val (.word sl0), .val (.word lw)]))
    (hm_t : m.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hm_slot : m.locals.lookup (ofString "slot") = some (.val (.word slotw)))
    (had_m : ∃ ad ∈ balRecords m, memW m ad = tw.toNat ∧ lw.toNat ∈ htabValues m tw.toNat)
    (hnt : (evaluateHOLFiniteState m removeStorAfterListProg).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState m removeStorAfterListProg).1) :
    WorldStep (fun _ => []) [] stdKeep NoExtra s
      (evaluateHOLFiniteState m removeStorAfterListProg).1
      (evaluateHOLFiniteState m removeStorAfterListProg).2 ∧
    (∃ v, (evaluateHOLFiniteState m removeStorAfterListProg).1 = some (.returned v)) := by
  have hAR_s := hW_s.1
  have hAR_m := hws_sm.1
  have hG_m := hAR_m.1
  obtain ⟨S0, hWT0_ex⟩ := hW_s.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  obtain ⟨Sm, Ndm, _, hWT_m, _, _, _⟩ := hws_sm.2.2.2.2 S0 Nd0 hWT0 (fun x hx => nomatch hx)
  have hW_m : WorldOK m := ⟨hAR_m, ⟨Sm, (worldTyped_iff_with m Sm).2 ⟨Ndm, hWT_m⟩⟩⟩
  obtain ⟨adm, hadm, hadm_t, hlw_in_m⟩ := had_m
  have hlw_nz_nat : lw.toNat ≠ 0 := fun h => hlw_nz (BitVec.eq_of_toNat_eq (by simpa using h))
  have hl_fix_m : (lw.toNat, 24) ∈ fixedObjects m := by
    unfold fixedObjects; apply List.mem_append_right; unfold balObjects
    rw [← hadm_t] at hlw_in_m
    exact (bal_chunk_mem_of_record m hadm).2.2 lw.toNat hlw_in_m hlw_nz_nat
  rcases hWT_m.2.2.1.1 _ hl_fix_m with h0 | ⟨hal_lm, hw_lm⟩
  · cases h0
  have hl_bnd := ivl_allocated_bound hAR_m.2 hal_lm
  have hl_lo : sourceBase ≤ lw.toNat := by
    rcases hal_lm with h | h
    · exact h.1
    · have h1 := hAR_m.2.2.2.1; have h2 := hAR_m.2.2.2.2.1
      have h3 : sourceBase ≤ scratchStart := by decide
      exact le_trans h3 (le_trans h1 (le_trans h2 h.1))
  have hl8_lt : lw.toNat + 8 < 2 ^ 64 := by have := hl_bnd.2; omega
  have hl8_bv : lw + 8#64 = BitVec.ofNat 64 (lw.toNat + 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    change (lw.toNat + 8) % 2 ^ 64 = (lw.toNat + 8) % 2 ^ 64; rfl
  have hl8_align : (lw.toNat + 8) % 8 = 0 := by have := hw_lm.1; omega
  have hdom_l8 : m.memaddrs (lw + 8#64) := by
    rw [hG_m.memaddrs, InitECandidate.Solver.Wave8Contracts.M08.ordinaryDomain_iff, hl8_bv,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl8_lt]
    exact ⟨hl8_align, by omega, by have := hl_bnd.1; omega⟩
  obtain ⟨nw, _, hnw_mem0⟩ := hw_lm.2.2 1 (by change 1 < 24 / 8; omega)
  have hnw_mem : m.memory (lw + 8#64) = .word nw := by
    rw [hl8_bv]; simpa using hnw_mem0
  have hz8 : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
  have hev_load8 : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
      (.load .one (.op .add [.rfield 1 (.var .local (ofString "sl")), .const 8#64])) =
      some (.val (.word nw)) := by
    simp [evalHOLExact, evalListHOLExact, hm_sl, valueIsWord, valueWord, wordOpHOL, wordOp, hz8,
      memLoadHOLExact, isWfShapeExactHOL, hdom_l8, hnw_mem]
  let iteProg : ProgHOL 64 :=
    .ite (.cmp .equal (.load .one (.op .add [.rfield 1 (.var .local (ofString "sl")), .const 8#64])) (.const 0#64))
      (.call (some (none, none)) (ofString "htab_del")
        [.var .local (ofString "t"), .var .local (ofString "slot")])
      .skip
  have hseq_ite := evaluateHOLFiniteState_seq_line780 m iteProg (.return (.const 0#64))
  dsimp only [removeStorAfterListProg] at hnt hres ⊢
  by_cases hnw0 : nw = 0#64
  · have hcmp1 : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
        (.cmp .equal (.load .one (.op .add [.rfield 1 (.var .local (ofString "sl")), .const 8#64])) (.const 0#64)) =
        some (.val (.word 1#64)) := by
      unfold evalHOLExact
      rw [hev_load8]
      simp [evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL, hnw0]
    have hite_del : evaluateHOLFiniteState m iteProg =
        evaluateHOLFiniteState m
          (.call (some (none, none)) (ofString "htab_del")
            [.var .local (ofString "t"), .var .local (ofString "slot")]) := by
      dsimp only [iteProg]
      rw [evaluateHOLFiniteState_ite, hcmp1]; dsimp only
      rw [if_neg (by decide)]
    have hev_t_m : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
        (.var .local (ofString "t")) = some (.val (.word tw)) := by
      simp [evalHOLExact, hm_t]
    have hev_slot_m : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
        (.var .local (ofString "slot")) = some (.val (.word slotw)) := by
      simp [evalHOLExact, hm_slot]
    let delCall : ProgHOL 64 :=
      .call (some (none, none)) (ofString "htab_del")
        [.var .local (ofString "t"), .var .local (ofString "slot")]
    rcases hdel_out : evaluateHOLFiniteState m delCall with ⟨rd, sd⟩
    have hdel_nt : rd ≠ some .timeOut := by
      intro hto; subst hto
      rw [hseq_ite, hite_del, hdel_out] at hnt
      exact hnt rfl
    have hdel_spec := call_bal_stor_htab_del_eval m _ _ tw slotw hW_m hev_t_m hev_slot_m htw_nz
      (fun _ _ _ => ⟨adm, hadm, hadm_t⟩) (by rw [hdel_out]; exact hdel_nt)
    rw [hdel_out] at hdel_spec
    cases rd with
    | none =>
      obtain ⟨hws_md, _⟩ := hdel_spec.1 rfl
      have hret_sd : evaluateHOLFiniteState sd (.return (.const 0#64)) =
          (some (PanSemResultExact.returned (.val (.word 0#64))), emptyLocalsHOLFinite sd) := by
        rw [evaluateHOLFiniteState_return]
        simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
        rw [if_pos (by decide)]
      have htot : evaluateHOLFiniteState m (iteProg.seq (.return (.const 0#64))) =
          (some (PanSemResultExact.returned (.val (.word 0#64))), emptyLocalsHOLFinite sd) := by
        rw [hseq_ite, hite_del, hdel_out]; exact hret_sd
      rw [htot]; dsimp only
      have hws_sd : WorldStep (fun _ => []) [] stdKeep NoExtra s none sd :=
        worldStep_nil_trans hAR_s.2 hws_sm hws_md
      have hws_ret : WorldStep (fun _ => []) [] stdKeep NoExtra s
          (some (PanSemResultExact.returned (.val (.word 0#64)))) sd := by
        obtain ⟨h1, h2, h3, h4, h5⟩ := hws_sd
        exact ⟨h1, h2, h3, h4, fun S Nd hWT hD =>
          let ⟨S', Nd', ha, hb, hc, hd, _⟩ := h5 S Nd hWT hD
          ⟨S', Nd', ha, hb, hc, hd, trivial⟩⟩
      have hsd_emp : emptyLocalsHOLFinite sd = { sd with locals := (emptyLocalsHOLFinite sd).locals, clock := sd.clock } := rfl
      rw [hsd_emp]
      exact ⟨worldStep_with_locals_right _ sd.clock (fun _ _ _ => trivial) hws_ret,
        ⟨.val (.word 0#64), rfl⟩⟩
    | some rd' =>
      have hnr : ¬ Resumes (some rd') := hdel_spec.2 (Option.some_ne_none rd')
      have hres_rd : Resumes (some rd') := by
        rw [hseq_ite, hite_del, hdel_out] at hres; exact hres
      exact absurd hres_rd hnr
  · have hcmp0 : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
        (.cmp .equal (.load .one (.op .add [.rfield 1 (.var .local (ofString "sl")), .const 8#64])) (.const 0#64)) =
        some (.val (.word 0#64)) := by
      unfold evalHOLExact
      rw [hev_load8]
      simp [evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL, hnw0]
    have hite_skip : evaluateHOLFiniteState m iteProg = (none, m) := by
      dsimp only [iteProg]
      rw [evaluateHOLFiniteState_ite, hcmp0]; dsimp only
      rw [if_pos (by decide), evaluateHOLFiniteState_skip]
    have hret_m : evaluateHOLFiniteState m (.return (.const 0#64)) =
        (some (PanSemResultExact.returned (.val (.word 0#64))), emptyLocalsHOLFinite m) := by
      rw [evaluateHOLFiniteState_return]
      simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
      rw [if_pos (by decide)]
    have htot : evaluateHOLFiniteState m (iteProg.seq (.return (.const 0#64))) =
        (some (PanSemResultExact.returned (.val (.word 0#64))), emptyLocalsHOLFinite m) := by
      rw [hseq_ite, hite_skip]; exact hret_m
    rw [htot]; dsimp only
    have hws_ret : WorldStep (fun _ => []) [] stdKeep NoExtra s
        (some (PanSemResultExact.returned (.val (.word 0#64)))) m := by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hws_sm
      exact ⟨h1, h2, h3, h4, fun S Nd hWT hD =>
        let ⟨S', Nd', ha, hb, hc, hd, _⟩ := h5 S Nd hWT hD
        ⟨S', Nd', ha, hb, hc, hd, trivial⟩⟩
    have hm_emp : emptyLocalsHOLFinite m = { m with locals := (emptyLocalsHOLFinite m).locals, clock := m.clock } := rfl
    rw [hm_emp]
    exact ⟨worldStep_with_locals_right _ m.clock (fun _ _ _ => trivial) hws_ret,
      ⟨.val (.word 0#64), rfl⟩⟩

theorem remove_storage_write_sl_nz_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (sl0 lw tw slotw idxw : BitVec 64)
    (l3 : HolFiniteMapExact MlS (ValueHOL 64)) (ck : Nat)
    (hW : WorldOK s)
    (htw_nz : tw ≠ 0)
    (had_s : ∃ ad ∈ balRecords s, memW s ad = tw.toNat)
    (hlw_in_s : lw.toNat ∈ htabValues s tw.toNat)
    (hs3_sl : l3.lookup (ofString "sl") = some (.rStruct [.val (.word sl0), .val (.word lw)]))
    (hs3_t : l3.lookup (ofString "t") = some (.val (.word tw)))
    (hs3_slot : l3.lookup (ofString "slot") = some (.val (.word slotw)))
    (hs3_idx : l3.lookup (ofString "idx") = some (.val (.word idxw))) :
    let s3 := { s with locals := l3, clock := ck }
    (evaluateHOLFiniteState s3 removeStorSlFoundProg).1 ≠ some .timeOut →
    Resumes (evaluateHOLFiniteState s3 removeStorSlFoundProg).1 →
    WorldStep (fun _ => []) [] stdKeep NoExtra s
      (evaluateHOLFiniteState s3 removeStorSlFoundProg).1
      (evaluateHOLFiniteState s3 removeStorSlFoundProg).2 := by
  dsimp only
  intro hnt hres
  set s3 : PanSemStateFiniteExact 64 F := { s with locals := l3, clock := ck }
  have hs3_eq : s3 = { s with locals := l3, clock := ck } := rfl
  have hW_s3 : WorldOK s3 := (worldOK_with_locals s l3 ck).2 hW
  obtain ⟨ad, had, had_t⟩ := had_s
  have hs3_sl' : s3.locals.lookup (ofString "sl") = some (.rStruct [.val (.word sl0), .val (.word lw)]) := hs3_sl
  have hs3_idx' : s3.locals.lookup (ofString "idx") = some (.val (.word idxw)) := hs3_idx
  have hev_sl1 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
      (.rfield 1 (.var .local (ofString "sl"))) = some (.val (.word lw)) := by
    simp [evalHOLExact, hs3_sl']
  have hev_40 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
      (.const 40#64) = some (.val (.word 40#64)) := rfl
  have hev_idx : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
      (.var .local (ofString "idx")) = some (.val (.word idxw)) := by
    simp [evalHOLExact, hs3_idx']
  have hslice_s3 : lw ≠ 0 → ∀ S Nd, WorldTypedWith s3 S Nd →
      LstOK s3 lw.toNat ∧ BalListSlice s3 lw.toNat (40#64 : BitVec 64).toNat := by
    intro _ S Nd hWT_s3
    have hWT_s : WorldTypedWith s S Nd := (worldTypedWith_with_locals s l3 ck S Nd).1 hWT_s3
    have hlw_in' : lw.toNat ∈ htabValues s (memW s ad) := by rwa [had_t]
    have hlst_s : LstOK s lw.toNat := (hWT_s.1.2.2.2.2.2.2.2.2.2.1 ad had).2.2.2 lw.toNat hlw_in'
    have hsl_s : BalListSlice s lw.toNat 40 := bal_list_slice_of_stor_val had hlw_in'
    exact ⟨hlst_s, hsl_s⟩
  let callProg : ProgHOL 64 :=
    .call (some (none, none)) (ofString "bal_list_remove_idx")
      [.rfield 1 (.var .local (ofString "sl")), .const 40#64, .var .local (ofString "idx")]
  have hseq := evaluateHOLFiniteState_seq_line780 s3 callProg removeStorAfterListProg
  dsimp only [removeStorSlFoundProg] at hnt hres ⊢
  rcases hcall_out : evaluateHOLFiniteState s3 callProg with ⟨rc, m⟩
  have hcall_nt : rc ≠ some .timeOut := by
    intro hto; subst hto
    rw [hseq, hcall_out] at hnt; exact hnt rfl
  have hcall_spec := call_bal_list_remove_idx_eval s3 _ _ _ lw 40#64 idxw
    hW_s3 hev_sl1 hev_40 hev_idx (Or.inr (Or.inr rfl)) hslice_s3
    (by rw [hcall_out]; exact hcall_nt)
  rw [hcall_out] at hcall_spec hseq
  cases rc with
  | none =>
    obtain ⟨hlw_nz, hws_s3_m, hm_loc, hbre_s3_m⟩ := hcall_spec.1 rfl
    have hws_sm : WorldStep (fun _ => []) [] stdKeep NoExtra s none m :=
      worldStep_with_locals_left hs3_eq rfl (fun _ _ _ => trivial) hws_s3_m
    have hbre_sm : M11.ByteRegionEffect s m
        [(lw.toNat + 8, 8), (memW s lw.toNat, 40 * memW s (lw.toNat + 16))] :=
      ⟨hbre_s3_m.code, hbre_s3_m.memaddrs, hbre_s3_m.shMemaddrs,
        hbre_s3_m.baseAddr, hbre_s3_m.be, hbre_s3_m.globals,
        hbre_s3_m.out_dom, hbre_s3_m.cell_frame, hbre_s3_m.byte_frame⟩
    have hlw_nz_nat : lw.toNat ≠ 0 := fun h => hlw_nz (BitVec.eq_of_toNat_eq (by simpa using h))
    have hlw_in_ad : lw.toNat ∈ htabValues s (memW s ad) := by rwa [had_t]
    obtain ⟨hrecs_m, had_w0_m, hvals_m⟩ :=
      bal_stor_list_remove_preserves_ad_t hW had hlw_in_ad hlw_nz_nat hbre_sm
    have had_m : ∃ ad' ∈ balRecords m, memW m ad' = tw.toNat ∧ lw.toNat ∈ htabValues m tw.toNat := by
      refine ⟨ad, ?_, ?_, ?_⟩
      · rw [hrecs_m]; exact had
      · rw [had_w0_m]; exact had_t
      · rw [← had_t, hvals_m]; exact hlw_in_ad
    have hm_sl : m.locals.lookup (ofString "sl") = some (.rStruct [.val (.word sl0), .val (.word lw)]) := by
      rw [hm_loc]; exact hs3_sl
    have hm_t : m.locals.lookup (ofString "t") = some (.val (.word tw)) := by
      rw [hm_loc]; exact hs3_t
    have hm_slot : m.locals.lookup (ofString "slot") = some (.val (.word slotw)) := by
      rw [hm_loc]; exact hs3_slot
    rw [hseq] at hnt hres ⊢
    exact (remove_storage_write_after_list_step s m sl0 lw tw slotw hW hws_sm hlw_nz htw_nz
      hm_sl hm_t hm_slot had_m hnt hres).1
  | some rc' =>
    have hnr : ¬ Resumes (some rc') := hcall_spec.2 (Option.some_ne_none rc')
    have hres_rc : Resumes (some rc') := by rw [hseq] at hres; exact hres
    exact absurd hres_rc hnr

def removeStorDecTProg : ProgHOL 64 :=
  .dec (ofString "t") .one (.load .one (.op .add [.rfield 1 (.var .local (ofString "m")), .const 0#64]))
    (.decCall (ofString "sl") (.comb [.one, .one]) (ofString "htab_get")
      [.var .local (ofString "t"), .var .local (ofString "slot")]
      (.seq
        (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "sl"))) (.const 0#64))
          (.return (.const 0#64))
          .skip)
        removeStorSlFoundProg))

theorem remove_storage_write_m_nz_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (f0 f1 slotw idxw : BitVec 64)
    (l1 : HolFiniteMapExact MlS (ValueHOL 64)) (ck : Nat)
    (hW : WorldOK s)
    (hf1_bal : ∀ S Nd, WorldTypedWith s S Nd → f1.toNat ∈ balRecords s)
    (hs1_m : l1.lookup (ofString "m") = some (.rStruct [.val (.word f0), .val (.word f1)]))
    (hs1_slot : l1.lookup (ofString "slot") = some (.val (.word slotw)))
    (hs1_idx : l1.lookup (ofString "idx") = some (.val (.word idxw))) :
    let s1 := { s with locals := l1, clock := ck }
    (evaluateHOLFiniteState s1 removeStorDecTProg).1 ≠ some .timeOut →
    Resumes (evaluateHOLFiniteState s1 removeStorDecTProg).1 →
    WorldStep (fun _ => []) [] stdKeep NoExtra s
      (evaluateHOLFiniteState s1 removeStorDecTProg).1
      (evaluateHOLFiniteState s1 removeStorDecTProg).2 := by
  dsimp only
  intro hnt hres
  set s1 : PanSemStateFiniteExact 64 F := { s with locals := l1, clock := ck }
  have hAR0 := hW.1
  have hG0 := hAR0.1
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  have had0 : f1.toNat ∈ balRecords s := hf1_bal S0 Nd0 hWT0
  have had_fix : (f1.toNat, 40) ∈ fixedObjects s := by
    unfold fixedObjects; apply List.mem_append_right; unfold balObjects
    exact List.mem_flatMap.2 ⟨f1.toNat, had0, List.mem_cons_self⟩
  rcases hWT0.2.2.1.1 _ had_fix with h0 | ⟨hal_ad, hw_ad⟩
  · cases h0
  have had_bnd := ivl_allocated_bound hAR0.2 hal_ad
  have had_lo : sourceBase ≤ f1.toNat := by
    rcases hal_ad with h | h
    · exact h.1
    · have h1 := hAR0.2.2.2.1; have h2 := hAR0.2.2.2.2.1
      have h3 : sourceBase ≤ scratchStart := by decide
      exact le_trans h3 (le_trans h1 (le_trans h2 h.1))
  have hf1_bv : f1 + 0#64 = BitVec.ofNat 64 f1.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.add_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt f1.isLt]
  have hdom_f1 : s1.memaddrs (f1 + 0#64) := by
    change s.memaddrs (f1 + 0#64)
    rw [hG0.memaddrs, InitECandidate.Solver.Wave8Contracts.M08.ordinaryDomain_iff, hf1_bv,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt f1.isLt]
    exact ⟨hw_ad.1, had_lo, by have := had_bnd.1; omega⟩
  obtain ⟨tw0, _, htw_mem0⟩ := hw_ad.2.2 0 (by change 0 < 40 / 8; omega)
  have htw_mem_s : s.memory (f1 + 0#64) = .word tw0 := by
    rw [hf1_bv]; simpa using htw_mem0
  have htw_mem : s1.memory (f1 + 0#64) = .word tw0 := htw_mem_s
  have htw0_toNat : tw0.toNat = memW s f1.toNat := by
    change tw0.toNat = (match s.memory (BitVec.ofNat 64 f1.toNat) with | .word w => w.toNat)
    rw [← hf1_bv, htw_mem_s]
  have hs1_m' : s1.locals.lookup (ofString "m") = some (.rStruct [.val (.word f0), .val (.word f1)]) := hs1_m
  have hz_0 : (0#64 : BitVec 64) + 0 = 0#64 := BitVec.add_zero _
  have hev_t_load : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.load .one (.op .add [.rfield 1 (.var .local (ofString "m")), .const 0#64])) =
      some (.val (.word tw0)) := by
    simp only [evalHOLExact, evalListHOLExact, hs1_m', List.getElem?_cons_succ, List.getElem?_cons_zero,
      valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self,
      List.foldr, hz_0, memLoadHOLExact, isWfShapeExactHOL, hdom_f1, htw_mem, ↓reduceIte]
  dsimp only [removeStorDecTProg] at hnt hres ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢; dsimp only at hnt hres ⊢
  rw [hev_t_load] at hnt hres ⊢; dsimp only at hnt hres ⊢
  rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt hres ⊢
  set s2 := setVarHOLFinite (ofString "t") (.val (.word tw0)) s1
  have hs2_eq : s2 = { s with locals := s2.locals, clock := ck } := rfl
  have hG_s2 : GuestInv s2 := guestInv_with_locals_clock s s2.locals ck hG0
  have hs2_t : s2.locals.lookup (ofString "t") = some (.val (.word tw0)) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs2_slot : s2.locals.lookup (ofString "slot") = some (.val (.word slotw)) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "t" ≠ ofString "slot" by decide]
    exact hs1_slot
  have hs2_idx : s2.locals.lookup (ofString "idx") = some (.val (.word idxw)) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "t" ≠ ofString "idx" by decide]
    exact hs1_idx
  let contSl : ProgHOL 64 :=
    .seq
      (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "sl"))) (.const 0#64))
        (.return (.const 0#64))
        .skip)
      removeStorSlFoundProg
  obtain ⟨tw, kw, sl0, lw, ck2, hev_t2, _, htw_nz, hlw_in, hnt3, hres3, heq3_r, heq3_s⟩ :=
    decCall_htab_get_resumes s2 (ofString "sl")
      (.var .local (ofString "t")) (.var .local (ofString "slot")) contSl hG_s2 hnt hres
  have htw_eq : tw = tw0 := by
    simp [evalHOLExact, hs2_t] at hev_t2; exact hev_t2.symm
  subst htw_eq
  set s3 := setVarHOLFinite (ofString "sl") (.rStruct [.val (.word sl0), .val (.word lw)])
    { s2 with clock := ck2 }
  have hs3_eq : s3 = { s with locals := s3.locals, clock := ck2 } := rfl
  have hs3_sl : s3.locals.lookup (ofString "sl") = some (.rStruct [.val (.word sl0), .val (.word lw)]) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs3_t : s3.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "sl" ≠ ofString "t" by decide, hs2_t]
  have hs3_slot : s3.locals.lookup (ofString "slot") = some (.val (.word slotw)) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "sl" ≠ ofString "slot" by decide, hs2_slot]
  have hs3_idx : s3.locals.lookup (ofString "idx") = some (.val (.word idxw)) := by
    simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "sl" ≠ ofString "idx" by decide, hs2_idx]
  have hseq_sl := evaluateHOLFiniteState_seq_line780 s3
    (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "sl"))) (.const 0#64))
      (.return (.const 0#64)) .skip)
    removeStorSlFoundProg
  by_cases hsl0 : sl0 = 0
  · have hite_ret : evaluateHOLFiniteState s3
        (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "sl"))) (.const 0#64))
          (.return (.const 0#64)) .skip) =
        (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite s3) := by
      rw [evaluateHOLFiniteState_ite]
      have hcmp : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
          (.cmp .equal (.rfield 0 (.var .local (ofString "sl"))) (.const 0#64)) =
          some (.val (.word 1#64)) := by
        subst hsl0; simp [evalHOLExact, hs3_sl, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hcmp]; dsimp only
      rw [if_neg (by decide), evaluateHOLFiniteState_return]
      simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
      rw [if_pos (by decide)]
    have hcontSl_eq : evaluateHOLFiniteState s3 contSl =
        (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite s3) := by
      dsimp only [contSl]; rw [hseq_sl]; simp only [hite_ret]
    have hdecCall_s : (evaluateHOLFiniteState s2
        (.decCall (ofString "sl") (.comb [.one, .one]) (ofString "htab_get")
          [.var .local (ofString "t"), .var .local (ofString "slot")] contSl)).2 =
        { s with
          locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite s3).locals (ofString "sl", s2.locals.lookup (ofString "sl"))
          clock := ck2 } := by
      rw [heq3_s, hcontSl_eq]; rfl
    let out2 := evaluateHOLFiniteState s2
      (.decCall (ofString "sl") (.comb [.one, .one]) (ofString "htab_get")
        [.var .local (ofString "t"), .var .local (ofString "slot")] contSl)
    have hout_tot : { out2.2 with locals := HolFiniteMapExact.resVarEq out2.2.locals (ofString "t", l1.lookup (ofString "t")) } =
        { s with
          locals := HolFiniteMapExact.resVarEq
            (HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite s3).locals (ofString "sl", s2.locals.lookup (ofString "sl")))
            (ofString "t", l1.lookup (ofString "t"))
          clock := ck2 } := by
      dsimp only [out2]; rw [hdecCall_s]
    change WorldStep (fun _ => []) [] stdKeep NoExtra s out2.1
      { out2.2 with locals := HolFiniteMapExact.resVarEq out2.2.locals (ofString "t", s1.locals.lookup (ofString "t")) }
    rw [show s1.locals.lookup (ofString "t") = l1.lookup (ofString "t") from rfl, hout_tot]
    exact worldStep_with_locals_right _ ck2 (fun _ _ _ => trivial)
      (worldStep_refl (fun _ => []) [] hAR0 rfl)
  · have hsl0_64 : sl0 ≠ 0#64 := hsl0
    have hite_skip : evaluateHOLFiniteState s3
        (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "sl"))) (.const 0#64))
          (.return (.const 0#64)) .skip) = (none, s3) := by
      rw [evaluateHOLFiniteState_ite]
      have hcmp : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
          (.cmp .equal (.rfield 0 (.var .local (ofString "sl"))) (.const 0#64)) =
          some (.val (.word 0#64)) := by
        simp [evalHOLExact, hs3_sl, Compiler.Encoders.Asm.wordCmpHOL, hsl0_64]
      rw [hcmp]; dsimp only
      rw [if_pos (by decide), evaluateHOLFiniteState_skip]
    have hcontSl_eq : evaluateHOLFiniteState s3 contSl =
        evaluateHOLFiniteState s3 removeStorSlFoundProg := by
      dsimp only [contSl]; rw [hseq_sl]; simp only [hite_skip]
    rw [hcontSl_eq] at hnt3 hres3 heq3_r heq3_s
    have htw_S0 : tw.toNat ∈ S0 := by
      rw [htw0_toNat]; exact (hWT0.1.2.2.2.2.2.2.2.2.2.1 f1.toNat had0).1
    have hwf_tw_s2 : HtabWF s2 tw.toNat := by
      rw [hs2_eq, htabWF_with_locals]; exact (hWT0.1.2.1 _ htw_S0).1
    have hlw_in_s : lw.toNat ∈ htabValues s tw.toNat := hlw_in hwf_tw_s2 hsl0
    have hws_inner : WorldStep (fun _ => []) [] stdKeep NoExtra s
        (evaluateHOLFiniteState s3 removeStorSlFoundProg).1
        (evaluateHOLFiniteState s3 removeStorSlFoundProg).2 := by
      have hstep := remove_storage_write_sl_nz_step s sl0 lw tw slotw idxw s3.locals ck2
        hW htw_nz ⟨f1.toNat, had0, htw0_toNat.symm⟩ hlw_in_s hs3_sl hs3_t hs3_slot hs3_idx
      rw [← hs3_eq] at hstep
      exact hstep hnt3 hres3
    let out2 := evaluateHOLFiniteState s2
      (.decCall (ofString "sl") (.comb [.one, .one]) (ofString "htab_get")
        [.var .local (ofString "t"), .var .local (ofString "slot")] contSl)
    change WorldStep (fun _ => []) [] stdKeep NoExtra s out2.1
      { out2.2 with locals := HolFiniteMapExact.resVarEq out2.2.locals (ofString "t", s1.locals.lookup (ofString "t")) }
    dsimp only [out2]
    rw [heq3_r, heq3_s]
    let p3 := (evaluateHOLFiniteState s3 removeStorSlFoundProg).2
    have hupd : { { p3 with locals := HolFiniteMapExact.resVarEq p3.locals (ofString "sl", s2.locals.lookup (ofString "sl")) } with
          locals := HolFiniteMapExact.resVarEq
            (HolFiniteMapExact.resVarEq p3.locals (ofString "sl", s2.locals.lookup (ofString "sl")))
            (ofString "t", s1.locals.lookup (ofString "t")) } =
        { p3 with
          locals := HolFiniteMapExact.resVarEq
            (HolFiniteMapExact.resVarEq p3.locals (ofString "sl", s2.locals.lookup (ofString "sl")))
            (ofString "t", s1.locals.lookup (ofString "t"))
          clock := p3.clock } := rfl
    dsimp only [p3] at hupd
    rw [hupd]
    exact worldStep_with_locals_right _ (evaluateHOLFiniteState s3 removeStorSlFoundProg).2.clock
      (fun _ _ _ => trivial) hws_inner

theorem wk_remove_storage_write :
    WorldKeeps WorldOK (fun _ => [])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
     ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "remove_storage_write") := by
  refine ⟨_, _, _, lookup_remove_storage_write, ?_⟩
  intro F s hcode hW hvalid hnt hres
  have hAR0 : ArenaReady s := hW.1
  have hG : GuestInv s := hAR0.1
  obtain ⟨values, hlook_fn⟩ := hvalid
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "remove_storage_write")
    values _ s.locals _ hlook_fn
  simp only [lookupCodeHOLExact, lookup_remove_storage_write] at hx
  rcases values with _ | ⟨va, _ | ⟨vs, _ | ⟨vx, _ | ⟨_, _⟩⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · rcases va with ⟨⟨addrw⟩⟩ | _ | _; swap; · simp [shapeOfHOLExact, shapeEqHOL] at hx
    swap; · simp [shapeOfHOLExact, shapeEqHOL] at hx
    rcases vs with ⟨⟨slotw⟩⟩ | _ | _; swap; · simp [shapeOfHOLExact, shapeEqHOL] at hx
    swap; · simp [shapeOfHOLExact, shapeEqHOL] at hx
    rcases vx with ⟨⟨idxw⟩⟩ | _ | _; swap; · simp [shapeOfHOLExact, shapeEqHOL] at hx
    swap; · simp [shapeOfHOLExact, shapeEqHOL] at hx
    simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hs_locals_eq⟩ := hx
    have hs_addr : s.locals.lookup (ofString "addr") = some (.val (.word addrw)) := by
      have := congrFun hs_locals_eq (ofString "addr")
      simpa [FUPDATE, show ofString "idx" ≠ ofString "addr" by decide,
        show ofString "slot" ≠ ofString "addr" by decide,
        show ofString "addr" ≠ ofString "idx" by decide,
        show ofString "addr" ≠ ofString "slot" by decide] using this.symm
    have hs_slot : s.locals.lookup (ofString "slot") = some (.val (.word slotw)) := by
      have := congrFun hs_locals_eq (ofString "slot")
      simpa [FUPDATE, show ofString "idx" ≠ ofString "slot" by decide,
        show ofString "slot" ≠ ofString "idx" by decide] using this.symm
    have hs_idx : s.locals.lookup (ofString "idx") = some (.val (.word idxw)) := by
      have := congrFun hs_locals_eq (ofString "idx")
      simpa [FUPDATE] using this.symm
    set cont1 : ProgHOL 64 :=
      .seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
              (.return (.const 0#64)) .skip)
        removeStorDecTProg
    have hbody_eq : sourceFnBody Guest.Software.guestFn_remove_storage_write =
        .decCall (ofString "m") (.comb [.one, .one]) (ofString "htab_get")
          [.var .global (ofString "bal_accounts"), .var .local (ofString "addr")] cont1 := rfl
    rw [hbody_eq] at hnt hres ⊢
    obtain ⟨tw, kw, f0, f1, ck, hev_t, hev_k, htw_nz, hf1_in, hnt1, hres1, heq1_r, heq1_s⟩ :=
      decCall_htab_get_resumes s (ofString "m")
        (.var .global (ofString "bal_accounts")) (.var .local (ofString "addr")) cont1 hG hnt hres
    set s1 := setVarHOLFinite (ofString "m") (.rStruct [.val (.word f0), .val (.word f1)])
      { s with clock := ck }
    have hs1_eq : s1 = { s with locals := s1.locals, clock := ck } := rfl
    have hba_word : ∃ baw : BitVec 64, s.globals.lookup (ofString "bal_accounts") = some (.val (.word baw)) :=
      hAR0.2.2.2.2.2.2.2.2.2 "bal_accounts" (by decide)
    obtain ⟨baw, hbaw⟩ := hba_word
    have htw_eq : tw = baw := by
      simp [evalHOLExact, hbaw] at hev_t; exact hev_t.symm
    have hba_nat : globN s "bal_accounts" = tw.toNat := by
      subst htw_eq; simp [globN, hbaw]
    have hba_nz : globN s "bal_accounts" ≠ 0 := by
      rw [hba_nat]; exact fun h => htw_nz (BitVec.eq_of_toNat_eq (by simpa using h))
    have hs1_m : s1.locals.lookup (ofString "m") = some (.rStruct [.val (.word f0), .val (.word f1)]) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs1_slot : s1.locals.lookup (ofString "slot") = some (.val (.word slotw)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "m" ≠ ofString "slot" by decide, hs_slot]
    have hs1_idx : s1.locals.lookup (ofString "idx") = some (.val (.word idxw)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "m" ≠ ofString "idx" by decide, hs_idx]
    have hseq1 := evaluateHOLFiniteState_seq_line780 s1
      (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
          (.return (.const 0#64)) .skip)
      removeStorDecTProg
    by_cases hf0 : f0 = 0
    · have hite_ret : evaluateHOLFiniteState s1
          (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
              (.return (.const 0#64)) .skip) =
          (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite s1) := by
        rw [evaluateHOLFiniteState_ite]
        have hcmp : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
            (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64)) =
            some (.val (.word 1#64)) := by
          subst hf0; simp [evalHOLExact, hs1_m, Compiler.Encoders.Asm.wordCmpHOL]
        rw [hcmp]; dsimp only
        rw [if_neg (by decide), evaluateHOLFiniteState_return]
        simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
        rw [if_pos (by decide)]
      have hcont1_eq : evaluateHOLFiniteState s1 cont1 =
          (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite s1) := by
        dsimp only [cont1]; rw [hseq1]; simp only [hite_ret]
      have hpost_eq : (evaluateHOLFiniteState s
          (.decCall (ofString "m") (.comb [.one, .one]) (ofString "htab_get")
            [.var .global (ofString "bal_accounts"), .var .local (ofString "addr")] cont1)).2 =
          { s with
              locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite s1).locals (ofString "m", s.locals.lookup (ofString "m"))
              clock := ck } := by
        rw [heq1_s, hcont1_eq]; rfl
      rw [hpost_eq]
      exact worldStep_with_locals_right _ ck (fun _ _ _ => trivial)
        (worldStep_refl (fun _ => []) [] hAR0 rfl)
    · have hf0_64 : f0 ≠ 0#64 := hf0
      have hite_skip : evaluateHOLFiniteState s1
          (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
              (.return (.const 0#64)) .skip) = (none, s1) := by
        rw [evaluateHOLFiniteState_ite]
        have hcmp : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
            (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64)) =
            some (.val (.word 0#64)) := by
          simp [evalHOLExact, hs1_m, Compiler.Encoders.Asm.wordCmpHOL, hf0_64]
        rw [hcmp]; dsimp only
        rw [if_pos (by decide), evaluateHOLFiniteState_skip]
      have hcont1_eq2 : evaluateHOLFiniteState s1 cont1 =
          evaluateHOLFiniteState s1 removeStorDecTProg := by
        dsimp only [cont1]; rw [hseq1]; simp only [hite_skip]
      rw [hcont1_eq2] at hnt1 hres1 heq1_r heq1_s
      have hf1_bal : ∀ S Nd, WorldTypedWith s S Nd → f1.toNat ∈ balRecords s := by
        intro S Nd hWT
        have hba_S : globN s "bal_accounts" ∈ S := by
          rcases hWT.1.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
          · exact absurd h0 hba_nz
          · exact hm
        have hwf_ba : HtabWF s tw.toNat := by rw [← hba_nat]; exact (hWT.1.2.1 _ hba_S).1
        have hin_vals := hf1_in hwf_ba hf0
        unfold balRecords
        rw [if_neg hba_nz, hba_nat]
        exact hin_vals
      have hws_inner : WorldStep (fun _ => []) [] stdKeep NoExtra s
          (evaluateHOLFiniteState s1 removeStorDecTProg).1
          (evaluateHOLFiniteState s1 removeStorDecTProg).2 := by
        have hstep := remove_storage_write_m_nz_step s f0 f1 slotw idxw s1.locals ck
          hW hf1_bal hs1_m hs1_slot hs1_idx
        rw [← hs1_eq] at hstep
        exact hstep hnt1 hres1
      rw [heq1_r, heq1_s]
      exact worldStep_with_locals_right _ (evaluateHOLFiniteState s1 removeStorDecTProg).2.clock
        (fun _ _ _ => trivial) hws_inner
  · simp at hx

end InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBal
