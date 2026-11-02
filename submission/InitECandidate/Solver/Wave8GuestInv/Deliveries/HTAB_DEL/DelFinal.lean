import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_DEL.DelCore

/-! `htab_del_spec`: `htab_del` keeps its table well formed, writes only inside the table blocks
and allocates nothing. -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace InitECandidate.Solver.Wave8HtabAstra.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8HtabAstra

theorem htab_del_spec_proof : FunSpec HtabArgWF
    (OnReturn (fun s post => ExitR9 (locN s "t") s post)) (ofString "htab_del") := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem 139 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_del) rfl, ?_⟩
  intro F s hcode hP _ v hv
  obtain ⟨hAR, hWF, hal⟩ := hP
  have htpos : 0 < locN s "t" := by
    have := (hWF.1 _ (List.mem_cons_self)).1.1
    simp only [htabFootprint] at this
    have hsb : sourceBase = 2701131776 := rfl
    omega
  obtain ⟨tw, ht, htn⟩ := (fun h => by
    unfold locN at h ⊢
    split at h
    · rename_i w hw; exact ⟨w, hw, rfl⟩
    · omega : 0 < locN s "t" → ∃ w : BitVec 64, s.locals.lookup (ofString "t") = some (.val (.word w)) ∧
        locN s "t" = w.toNat) htpos
  show ExitR9 (locN s "t") s _
  rw [htn] at hWF hal ⊢
  obtain ⟨hB, L, I, Fr, hT⟩ := (htabWF_iff s _).1 hWF
  obtain ⟨hLlen, hnodup, hmemr, hcntI, hord, hint, hroot0, hroot1, _, hpar, _, _⟩ := id hT
  obtain ⟨hfp, hdisj, hk1, hk60, hst, hnc, hnx1, hnx⟩ := id hB
  -- header words
  rcases hk : s.memory (tw + 0) with ⟨k⟩
  rcases hnd : s.memory (tw + 40) with ⟨nd⟩
  rcases how : s.memory (tw + 48) with ⟨ow⟩
  rcases hcnt : s.memory (tw + 24) with ⟨cntw⟩
  rcases hrt : s.memory (tw + 56) with ⟨rt⟩
  have e0 : hdr s tw.toNat 0 = k.toNat := hdr_of s tw k 0 hk
  have e3 : hdr s tw.toNat 3 = cntw.toNat := hdr_of s tw cntw 3 hcnt
  have e5 : hdr s tw.toNat 5 = nd.toNat := hdr_of s tw nd 5 hnd
  have e6 : hdr s tw.toNat 6 = ow.toNat := hdr_of s tw ow 6 how
  have e7 : hdr s tw.toNat 7 = rt.toNat := hdr_of s tw rt 7 hrt
  simp only [e0, e3, e5, e6, e7] at hLlen hcntI hord hint hroot0 hroot1 hpar hk1 hk60
  simp only [htabFootprint, e5, e6] at hfp hdisj
  have hfp2 := (hfp (nd.toNat, (hdr s tw.toNat 10 + 1) * 32) (by simp)).1
  have hfp3 := (hfp (ow.toNat, (hdr s tw.toNat 10 + 1) * 8) (by simp)).1
  simp only [Inside] at hfp2 hfp3
  have hhe : heapEnd < 2 ^ 64 := by decide
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, Disj] at hdisj
  have hdA := hdisj.1.2.1
  have hdB := hdisj.1.2.2
  have hdC := hdisj.2.2.1
  have hfp0 := (hfp (tw.toNat, 88) (by simp)).1
  simp only [Inside] at hfp0
  have hLIb : ∀ n ∈ L ++ I ++ Fr, 1 ≤ n ∧ n < hdr s tw.toNat 10 + 1 := fun n hn => by
    have := (hmemr n).1 hn; omega
  have hndLI := List.nodup_append.mp (List.nodup_append.mp hnodup).1
  have hLI : ∀ x ∈ L, x ∉ I := fun x hx hxi => hndLI.2.2 x hx x hxi rfl
  have hLlen' : L.length ≤ hdr s tw.toNat 8 - 1 :=
    nodup_len_le L _ hndLI.1 (fun x hx => (hmemr x).1 (by simp [hx]))
  have hres := (del_walk2 s hcode tw ht (0 :: (L ++ I)) ?_ ?_ nd ow cntw hnd how hcnt).run v hv
  · rcases hres with heq | ⟨lw, pw, mv, hlwS, hlw0, hcrit, hpw, hmv0, hcase⟩
    · rw [heq]
      refine ⟨?_, rfl, rfl⟩
      exact (exitR_locals _ s s s.locals _ s.clock _).2 (ExitR.refl _ s hAR hWF hal)
    -- the deleted leaf is live
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
        have hmk : maxKeyLen = 60 := rfl
        have h8 : (k * 8).toNat = k.toNat * 8 := by
          rw [BitVec.toNat_mul]; simp; omega
        rw [h8] at hc
        unfold nodeF at h24
        omega
    have hL0 : 0 < L.length := List.length_pos_of_mem hleaf
    have hlwB := hLIb lw.toNat (by simp [hleaf])
    obtain ⟨i0, hi0, hli0⟩ := List.getElem_of_mem hleaf
    have hpos : nodeF s nd.toNat lw.toNat 16 = i0 := by rw [← hli0]; exact (hord i0 hi0).2.2
    have hpw' : pw.toNat = i0 := by rw [← hpos]; exact (nodeF_of s nd lw pw 16 hpw).symm
    have hlast := hord (L.length - 1) (by omega)
    set mvN := L[L.length - 1]'(by omega) with hmvN
    have hmvL : mvN ∈ L := List.getElem_mem _
    have hmvB := hLIb mvN (by simp [hmvL])
    have hcw1 : (cntw - 1).toNat = cntw.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
      simp
    have hcw : (cntw - 1).toNat + 1 = hdr s tw.toNat 3 := by rw [e3, hcw1]; omega
    have hmv' : mv.toNat = mvN := by
      have h1 := hlast.1
      have haddr : ow + (cntw - 1) * 8 = BitVec.ofNat 64 (ow.toNat + 8 * (L.length - 1)) := by
        rw [ao8, hcw1, hLlen]
      rw [haddr] at hmv0
      unfold memW at h1
      rw [hmv0] at h1
      exact h1
    -- the memory after the order-slot move
    rcases hcase with ⟨heq, hpost⟩ | ⟨hne, hpost⟩
    · -- the leaf is the last one: nothing moves
      have hi0' : i0 = L.length - 1 := by
        have := congrArg BitVec.toNat heq
        rw [hcw1] at this
        omega
      have hmvlw : mvN = lw.toNat := by rw [hmvN, ← hli0]; simp only [hi0']
      refine del_core s _ tw nd ow lw (cntw - 1) s.memory L I Fr mvN hAR hal hB hT e5 e6 hcw hleaf
        (fun _ => rfl) hmvL ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) hpost
      · intro n off _ _
        split_ifs with h
        · rw [h.1, h.2, hmvlw, ← memW_rdN]; rfl
        · rfl
      · intro i _
        split_ifs with h
        · rw [h, hpos, hi0', ← memW_rdN]; exact hlast.1
        · rfl
    · -- move the last leaf into the vacated slot
      have hi0' : i0 ≠ L.length - 1 := by
        intro h; apply hne
        apply BitVec.eq_of_toNat_eq
        rw [hcw1]
        omega
      have hpwB : pw.toNat < hdr s tw.toNat 10 + 1 := by omega
      have hmvB' : mv.toNat < hdr s tw.toNat 10 + 1 := by omega
      have hposR : rdN s.memory (nd.toNat + 32 * lw.toNat + 16) = pw.toNat := by
        rw [← memW_rdN, hpw']
        exact hpos
      refine del_core s _ tw nd ow lw (cntw - 1) _ L I Fr mvN hAR hal hB hT e5 e6 hcw hleaf
        (fun _ => rfl) hmvL ?_ ?_ ?_ ?_ hpost
      · intro n off hn hoff
        simp only [nodeF, memW_rdN]
        rdsimp [hposR]
        split_ifs <;> omega
      · intro i hi
        simp only [nodeF, memW_rdN]
        rdsimp [hposR]
        split_ifs <;> omega
      · intro c hc
        rdsimp []
      · intro a ha
        have h0 := ha (tw.toNat, 88) (by simp [htabFootprint])
        have h2 := ha (nd.toNat, (hdr s tw.toNat 10 + 1) * 32) (by simp [htabFootprint, e5])
        have h3 := ha (ow.toNat, (hdr s tw.toNat 10 + 1) * 8) (by simp [htabFootprint, e6])
        simp only [InIvl] at h0 h2 h3
        have := a.isLt
        rdsimp []
  · intro u hu
    rw [hrt] at hu
    simp only [HolWordLab.word.injEq] at hu
    subst hu
    by_cases hc : cntw.toNat = 0
    · simp [hroot0 hc]
    · exact List.mem_cons_of_mem _ (hroot1 (by omega)).1
  · intro nd' k' hnd' hk' w hwS hw0 hne
    rw [hnd] at hnd'; rw [hk] at hk'
    simp only [HolWordLab.word.injEq] at hnd' hk'
    subst hnd' hk'
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
      have h8 : (k * 8).toNat = k.toNat * 8 := by
        rw [BitVec.toNat_mul]; simp; omega
      rw [h8]
      unfold nodeF at this
      omega
    · obtain ⟨_, h8, h16, _⟩ := hint _ hwI
      unfold nodeF at h8 h16
      exact ⟨List.mem_cons_of_mem _ h8, List.mem_cons_of_mem _ h16⟩

end InitECandidate.Solver.Wave8HtabAstra.Htab
