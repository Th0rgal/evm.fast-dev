import InitECandidate.Solver.Wave8GuestInv.R10Shards.SoloHtabSetMain

/-! Final composition of `htab_set_body_spec` and `htab_set_spec_proof` (`FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_set")`). -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.SoloHtabSet

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Execution of the Post-Allocation Splice Program -/

theorem eval_field_load_word {F : Type} (st : PanSemStateFiniteExact 64 F)
    (tw off w : BitVec 64)
    (ht : st.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hdom : st.memaddrs (tw + off))
    (hm : st.memory (tw + off) = .word w) :
    evalAt st (.load .one (.op .add [.var .local (ofString "t"), .const off])) =
      some (.val (.word w)) := by
  simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, ht,
    isWfShapeExactHOL, memLoadHOLExact, hdom, hm, valueIsWord, valueWord, wordOpHOL, wordOp]

theorem htab_set_splice_exec {F : Type}
    (s0 s2 : PanSemStateFiniteExact 64 F)
    (tw dw pw nw nlw niw : BitVec 64)
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
    (hcnt_pos : 0 < hdr s0 tw.toNat 3)
    (hd_lt : dw.toNat < 8 * hdr s0 tw.toNat 0)
    (hnw_LI : nw.toNat ∈ L0 ++ I0)
    (hpw_spec : (pw.toNat = 0 ∧ nw.toNat = hdr s0 tw.toNat 7) ∨
      (pw.toNat ∈ I0 ∧ nw.toNat ≠ hdr s0 tw.toNat 7 ∧ pw.toNat = nodeF s0 (hdr s0 tw.toNat 5) nw.toNat 0))
    (hh0_2 : hdr s2 tw.toNat 0 = hdr s0 tw.toNat 0)
    (hh1_2 : hdr s2 tw.toNat 1 = hdr s0 tw.toNat 1)
    (hh3_2 : hdr s2 tw.toNat 3 = hdr s0 tw.toNat 3 + 1)
    (hh7_2 : hdr s2 tw.toNat 7 = hdr s0 tw.toNat 7)
    (hnl_16_2 : nodeF s2 (hdr s2 tw.toNat 5) nlw.toNat 16 = hdr s0 tw.toNat 3)
    (hnl_24_2 : nodeF s2 (hdr s2 tw.toNat 5) nlw.toNat 24 = 8 * hdr s0 tw.toNat 0)
    (hni_24_2 : nodeF s2 (hdr s2 tw.toNat 5) niw.toNat 24 = dw.toNat)
    (hord_cnt_2 : memW s2 (hdr s2 tw.toNat 6 + 8 * hdr s0 tw.toNat 3) = nlw.toNat)
    (hord_old_2 : ∀ i, i < hdr s0 tw.toNat 3 →
      memW s2 (hdr s2 tw.toNat 6 + 8 * i) = memW s0 (hdr s0 tw.toNat 6 + 8 * i))
    (hnd_old_2 : ∀ z ∈ L0 ++ I0, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF s2 (hdr s2 tw.toNat 5) z off = nodeF s0 (hdr s0 tw.toNat 5) z off)
    (hhp_2 : globN s0 "heap_ptr" ≤ globN s2 "heap_ptr")
    (hfp_2 : ∀ i ∈ htabFootprint s2 tw.toNat, Allocated s2 i ∧
      ((∃ j ∈ htabFootprint s0 tw.toNat, Inside i j.1 (j.1 + j.2)) ∨
        Inside i (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (globN s2 "heap_ptr" - globN s0 "heap_ptr"))))
    (hfr_2 : FrameOutside s0 s2 (htabFootprint s0 tw.toNat) (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr"))
    (hg_2 : ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s0.globals.lookup k = s2.globals.lookup k) :
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
      (fun _ post => HtabExitAt tw.toNat s0 post) := by
  set t := tw.toNat
  have hB2 := hNS2.1
  have hnodup2 := hNS2.2.1
  have hmem2 := hNS2.2.2.1
  have hfc2 := hNS2.2.2.2
  obtain ⟨hnc2_lt, _, _, _, ht_lo, ht_hi, _⟩ := htabBlocks_bounds hB2
  have hnx2_le : hdr s2 t 8 ≤ hdr s2 t 10 + 1 := hB2.2.2.2.2.2.2.2
  have hhe : heapEnd = 33806089704 := rfl
  obtain ⟨hdom2_t5, hm2_t5⟩ := word_of_hdr s2 tw 5 (by omega) hB2
  set ndw := BitVec.ofNat 64 (hdr s2 t 5)
  have hndw_nat : ndw.toNat = hdr s2 t 5 := by
    have hnd2_in := (hB2.1 (hdr s2 t 5, (hdr s2 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hnd2_in; rw [BitVec.toNat_ofNat]; omega
  -- 1. `nodes := load(t + 40)`
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
  -- 2. Three parent stores: `ni.+0 := p`, `nl.+0 := ni`, `n.+0 := ni`
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
  -- Helper: from `NS s2 L_nd s2.globals m5_val s2.clock` where `m5_val` corresponds to `ch_left : Bool`,
  -- execute the final `ite (p == 0)` and `return 0`!
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
        (fun _ post => HtabExitAt t s0 post) := by
    intro ch_left m5_val hm5_eq
    apply Ret.seq_ite
    intro cwp hcwp
    have hp_lt_264 : pw.toNat < 2 ^ 64 := pw.isLt
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
    · -- `pw.toNat = 0`: `store(t + 56, ni); return 0`
      have hpz := hcwp_spec.1 hcwp_nz
      refine Ret.ns_storeW (tw + 56#64) niw
        (by
          have h560 : 56#64 + (0 : BitVec 64) = 56#64 := rfl
          simp only [NS_locals, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
            hl_t, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
            valueIsWord, valueWord, wordOpHOL, wordOp, h560])
        (by simp [evalAt, evalHOLExact]; exact hl_ni) ?_
      intro _
      apply Ret.ns_ret; intro _ _
      exact htab_set_splice_memory_wf s0 s2 tw dw pw nw nlw niw L0 I0 Fr0 Fr2 ch_left
        (updW m5_val (tw + 56#64) niw)
        (by dsimp only; rw [if_pos hpz, hm5_eq])
        hA2 hNS2 hT0 hcnt_pos hd_lt hnw_LI hpw_spec hh0_2 hh1_2 hh3_2 hh7_2
        hnl_16_2 hnl_24_2 hni_24_2 hord_cnt_2 hord_old_2 hnd_old_2 hhp_2 hfp_2 hfr_2 hg_2
    · -- `pw.toNat ≠ 0`: `ite (load(nodes + p*32 + 8) == n)`
      have hpnz := hcwp_spec.2 hcwp_z
      have hpI : pw.toNat ∈ I0 := by
        rcases hpw_spec with ⟨h0, _⟩ | ⟨hI, _, _⟩
        · exact absurd h0 hpnz
        · exact hI
      have hpLI : pw.toNat ∈ L0 ++ I0 := List.mem_append_right _ hpI
      have hp_lt_nc2 : pw.toNat < hdr s2 t 10 + 1 := by
        have := (hmem2 pw.toNat).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hpLI)))
        omega
      -- Show `m5_val (ndw + pw * 32 + 8) = .word (BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) pw.toNat 8))`!
      have hsep2 := htabBlocks_cell_sep hB2
      have haddr_nd : ∀ (xw : BitVec 64) (off : Nat),
          ndw + xw * 32#64 + BitVec.ofNat 64 off = BitVec.ofNat 64 (hdr s2 t 5 + 32 * xw.toNat + off) := by
        intro xw off; rw [← hndw_nat]; exact (ofNat_node_addr ndw xw off).symm
      have hnd_all := (List.nodup_append.mp hnodup2).1
      have hp_ne_ni : pw.toNat ≠ niw.toNat := fun h =>
        (List.nodup_append.mp hnd_all).2.2 niw.toNat (List.mem_append_left _ (h ▸ hpLI)) niw.toNat (by simp) rfl
      have hni_lt_nc2 : niw.toNat < hdr s2 t 10 + 1 := by
        have := (hmem2 niw.toNat).mp (List.mem_append_left _ (List.mem_append_right _ (by simp))); omega
      have hnl_lt_nc2 : nlw.toNat < hdr s2 t 10 + 1 := by
        have := (hmem2 nlw.toNat).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))); omega
      have hnw_lt_nc2 : nw.toNat < hdr s2 t 10 + 1 := by
        have := (hmem2 nw.toNat).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hnw_LI))); omega
      obtain ⟨hdom_p8, hm2_p8⟩ := word_of_node s2 tw ndw pw 8 hndw_nat.symm hp_lt_nc2 (Or.inr (Or.inl rfl)) hB2
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
        exact htab_set_splice_memory_wf s0 s2 tw dw pw nw nlw niw L0 I0 Fr0 Fr2 ch_left
          (updW m5_val (ndw + pw * 32#64 + 8#64) niw)
          (by dsimp only; rw [if_neg hpnz, if_pos hp8_eq, hm5_eq])
          hA2 hNS2 hT0 hcnt_pos hd_lt hnw_LI hpw_spec hh0_2 hh1_2 hh3_2 hh7_2
          hnl_16_2 hnl_24_2 hni_24_2 hord_cnt_2 hord_old_2 hnd_old_2 hhp_2 hfp_2 hfr_2 hg_2
      · have hp8_ne := hcw8_spec.2 hcw8_z
        refine Ret.ns_storeW (ndw + pw * 32#64 + 16#64) niw
          (eval_node_field_expr _ (ofString "p") ndw pw 16 hl_nd hl_p)
          (by simp [evalAt, evalHOLExact]; exact hl_ni) ?_
        intro _
        apply Ret.ns_ret; intro _ _
        exact htab_set_splice_memory_wf s0 s2 tw dw pw nw nlw niw L0 I0 Fr0 Fr2 ch_left
          (updW m5_val (ndw + pw * 32#64 + 16#64) niw)
          (by dsimp only; rw [if_neg hpnz, if_neg hp8_ne, hm5_eq])
          hA2 hNS2 hT0 hcnt_pos hd_lt hnw_LI hpw_spec hh0_2 hh1_2 hh3_2 hh7_2
          hnl_16_2 hnl_24_2 hni_24_2 hord_cnt_2 hord_old_2 hnd_old_2 hhp_2 hfp_2 hfr_2 hg_2
  -- 3. Dispatch the `ite (bit_at_d == 0)` child-ordering test!
  apply Ret.seq_ite
  intro cw_bit _
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · -- `ch_left = true`: `ni.+8 := nl`, `ni.+16 := n`
    refine Ret.ns_seq_storeW2
      (ndw + niw * 32#64 + 8#64) nlw
      (ndw + niw * 32#64 + 16#64) nw
      (eval_node_field_expr _ (ofString "ni") ndw niw 8 hl_nd hl_ni)
      (by simp [evalAt, evalHOLExact]; exact hl_nl)
      (eval_node_field_expr _ (ofString "ni") ndw niw 16 hl_nd hl_ni)
      (by simp [evalAt, evalHOLExact]; exact hl_n) ?_
    intro _ _
    exact exec_parent_link true _ rfl
  · -- `ch_left = false`: `ni.+8 := n`, `ni.+16 := nl`
    refine Ret.ns_seq_storeW2
      (ndw + niw * 32#64 + 8#64) nw
      (ndw + niw * 32#64 + 16#64) nlw
      (eval_node_field_expr _ (ofString "ni") ndw niw 8 hl_nd hl_ni)
      (by simp [evalAt, evalHOLExact]; exact hl_n)
      (eval_node_field_expr _ (ofString "ni") ndw niw 16 hl_nd hl_ni)
      (by simp [evalAt, evalHOLExact]; exact hl_nl) ?_
    intro _ _
    exact exec_parent_link false _ rfl

/-! ## 2. `memeq` Address Bound When Returning Normally on `1 ≤ n ≤ 60` -/

theorem memeq_ret_key_no_wrap {F : Type}
    (s0 : PanSemStateFiniteExact 64 F)
    (hG0 : GuestInv s0) (a b n : BitVec 64)
    (hn_ge1 : 1 ≤ n.toNat) (hn_le60 : n.toNat ≤ 60)
    (ha_loc : s0.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb_loc : s0.locals.lookup (ofString "b") = some (.val (.word b)))
    (hn_loc : s0.locals.lookup (ofString "n") = some (.val (.word n)))
    (rv : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memeq)).1 =
      some (.returned rv)) :
    b.toNat + n.toNat < 2 ^ 64 := by
  have hb_of_dom_word : ∀ {st : PanSemStateFiniteExact 64 F},
      st.memaddrs = ordinaryDomain → st.memaddrs b → b.toNat + n.toNat < 2 ^ 64 := by
    intro st hma hdom
    rw [hma, ordinaryDomain_iff] at hdom
    have h264 : 2701131776 + 8 * 3888119741 + 60 < 2 ^ 64 := by decide
    omega
  have hb_of_dom_byte : ∀ {st : PanSemStateFiniteExact 64 F},
      st.memaddrs = ordinaryDomain → st.memaddrs (panByteAlignHOL b) → b.toNat + n.toNat < 2 ^ 64 := by
    intro st hma hdom
    rw [hma, ordinaryDomain_iff] at hdom
    have hp := panByteAlign_toNat64 b
    have h264 : 2701131776 + 8 * 3888119741 + 8 + 60 < 2 ^ 64 := by decide
    omega
  have hma0 : s0.memaddrs = ordinaryDomain := hG0.memaddrs
  have first_word_b : ∀ {st : PanSemStateFiniteExact 64 F} {ea eb : ExpHOL 64} {rest : ProgHOL 64},
      st.memaddrs = ordinaryDomain →
      evalAt st eb = some (.val (.word b)) →
      (evaluateHOLFiniteState st
        (.seq (.ite (.cmp .notEqual (.load .one ea) (.load .one eb)) (.return (.const 0#64)) .skip) rest)).1 ≠ some .error →
      b.toNat + n.toNat < 2 ^ 64 := by
    intro st ea eb rest hma heb hev
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hev
    split at hev
    · rename_i cw hcmp
      obtain ⟨_, wb, _, hldb, _⟩ := evalAt_cmp st .notEqual _ _ cw hcmp
      obtain ⟨hdomb, _⟩ := memW_of_eval_load st eb b (.val (.word wb)) heb hldb
      exact hb_of_dom_word hma hdomb
    · exfalso; exact hev rfl
  have first_byte_b : ∀ {st : PanSemStateFiniteExact 64 F} {ea eb : ExpHOL 64} {rest : ProgHOL 64},
      st.memaddrs = ordinaryDomain →
      evalAt st eb = some (.val (.word b)) →
      (evaluateHOLFiniteState st
        (.seq (.ite (.cmp .notEqual (.loadByte ea) (.loadByte eb)) (.return (.const 0#64)) .skip) rest)).1 ≠ some .error →
      b.toNat + n.toNat < 2 ^ 64 := by
    intro st ea eb rest hma heb hev
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hev
    split at hev
    · rename_i cw hcmp
      obtain ⟨_, wb, _, hlbb, _⟩ := evalAt_cmp st .notEqual _ _ cw hcmp
      obtain ⟨hdomb, _⟩ := memB_of_eval_loadByte st eb b (.val (.word wb)) heb hlbb
      exact hb_of_dom_byte hma hdomb
    · exfalso; exact hev rfl
  have while_first_iter : ∀ {st : PanSemStateFiniteExact 64 F} {cond : ExpHOL 64} {body : ProgHOL 64} {r0 : Option (PanSemResultExact 64)},
      (∃ cw, evalAt st cond = some (.val (.word cw)) ∧ cw ≠ 0) →
      r0 = none ∨ (∃ u, r0 = some (.returned u)) →
      ((evaluateHOLFiniteState (decClockHOLFinite st) body).1 ≠ some .error → b.toNat + n.toNat < 2 ^ 64) →
      (evaluateHOLFiniteState st (.while cond body)).1 = r0 →
      b.toNat + n.toNat < 2 ^ 64 := by
    intro st cond body r0 ⟨cw, hcond, hnz⟩ hr0 hbody hw
    rw [evaluateHOLFiniteState_while_total] at hw
    rw [evalHOLFinite_eq_toExact] at hw
    unfold evalAt at hcond
    rw [hcond] at hw
    dsimp only at hw
    rw [if_pos hnz] at hw
    split at hw
    · rcases hr0 with rfl | ⟨_, rfl⟩ <;> simp at hw
    · rw [fixClockHOLFinite_evaluateState] at hw
      apply hbody
      intro herr
      rw [herr] at hw
      rcases hr0 with rfl | ⟨_, rfl⟩ <;> simp at hw
  have while_skip_false : ∀ {st u : PanSemStateFiniteExact 64 F} {cond : ExpHOL 64} {body : ProgHOL 64},
      evalAt st cond = some (.val (.word 0#64)) →
      evaluateHOLFiniteState st (.while cond body) = (none, u) →
      u = st := by
    intro st u cond body hcond hw
    rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hw
    unfold evalAt at hcond
    rw [hcond] at hw
    dsimp only at hw
    rw [if_neg (by decide : ¬ (0#64 : BitVec 64) ≠ 0)] at hw
    injection hw with _ e; exact e.symm
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memeq,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hret
  rw [evaluateHOLFiniteState_dec_total] at hret
  dsimp only at hret
  have hev0 : @evalHOLExact 64 F _ s0.toExact (fun x => Classical.propDecidable (s0.memaddrs x)) (.const 0#64) =
      some (.val (.word 0#64)) := rfl
  rw [hev0] at hret
  dsimp only at hret
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh0] at hret
  dsimp only at hret
  set s1 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s0
  have hs1_ma : s1.memaddrs = ordinaryDomain := hma0
  have hs1_b : s1.locals.lookup (ofString "b") = some (.val (.word b)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hb_loc, show ofString "i" ≠ ofString "b" by decide]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_loc, show ofString "i" ≠ ofString "n" by decide]
  have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have heb_var : ∀ {st : PanSemStateFiniteExact 64 F},
      st.locals.lookup (ofString "b") = some (.val (.word b)) →
      evalAt st (.var .local (ofString "b")) = some (.val (.word b)) := by
    intro st hb; simp [evalAt, evalHOLExact, hb]
  have heb_i0 : ∀ {st : PanSemStateFiniteExact 64 F},
      st.locals.lookup (ofString "b") = some (.val (.word b)) →
      st.locals.lookup (ofString "i") = some (.val (.word 0#64)) →
      evalAt st (.op .add [.var .local (ofString "b"), .var .local (ofString "i")]) = some (.val (.word b)) := by
    intro st hb hi
    simp [evalAt, evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, valueWord, wordOpHOL, wordOp]
  have fast_ite_err_or_skip : ∀ {st : PanSemStateFiniteExact 64 F} {cval : BitVec 64} {ea eb : ExpHOL 64} {rest : ProgHOL 64} {r0 : Option (PanSemResultExact 64)},
      st.memaddrs = ordinaryDomain →
      st.locals.lookup (ofString "n") = some (.val (.word n)) →
      evalAt st eb = some (.val (.word b)) →
      r0 = none ∨ (∃ u, r0 = some (.returned u)) →
      (evaluateHOLFiniteState st
        (.ite (.cmp .equal (.var .local (ofString "n")) (.const cval))
          (.seq (.ite (.cmp .notEqual (.load .one ea) (.load .one eb)) (.return (.const 0#64)) .skip) rest)
          .skip)).1 = r0 →
      b.toNat + n.toNat < 2 ^ 64 ∨
      evaluateHOLFiniteState st
        (.ite (.cmp .equal (.var .local (ofString "n")) (.const cval))
          (.seq (.ite (.cmp .notEqual (.load .one ea) (.load .one eb)) (.return (.const 0#64)) .skip) rest)
          .skip) = (none, st) := by
    intro st cval ea eb rest r0 hma hn_st heb hr0 hev
    rw [evaluateHOLFiniteState_ite] at hev ⊢
    have hc : @evalHOLExact 64 F _ st.toExact (fun addr => Classical.propDecidable (st.memaddrs addr))
        (.cmp .equal (.var .local (ofString "n")) (.const cval)) =
        some (.val (.word (if Compiler.Encoders.Asm.wordCmpHOL .equal n cval then 1#64 else 0#64))) := by
      simp [evalHOLExact, hn_st]
    rw [hc] at hev ⊢
    dsimp only at hev ⊢
    by_cases hcz : (if Compiler.Encoders.Asm.wordCmpHOL .equal n cval then (1#64 : BitVec 64) else 0#64) = 0
    · rw [if_pos hcz]; right; exact evaluateHOLFiniteState_skip st
    · rw [if_neg hcz] at hev
      left; apply first_word_b hma heb; intro herr; rw [herr] at hev
      rcases hr0 with rfl | ⟨_, rfl⟩ <;> simp at hev
  have seq_step : ∀ {st : PanSemStateFiniteExact 64 F} {p1 p2 : ProgHOL 64} {r0 : Option (PanSemResultExact 64)},
      r0 = none ∨ (∃ u, r0 = some (.returned u)) →
      (evaluateHOLFiniteState st (.seq p1 p2)).1 = r0 →
      (∃ u, (evaluateHOLFiniteState st p1).1 = some (.returned u)) ∨
      ∃ m, evaluateHOLFiniteState st p1 = (none, m) ∧ (evaluateHOLFiniteState m p2).1 = r0 := by
    intro st p1 p2 r0 hr0 h
    rw [evaluateHOLFiniteState_seq_line780] at h
    rcases hp1 : evaluateHOLFiniteState st p1 with ⟨r1, m⟩
    rw [hp1] at h
    cases r1 with
    | none => exact Or.inr ⟨m, rfl, h⟩
    | some x =>
      cases x with
      | returned u => exact Or.inl ⟨u, rfl⟩
      | _ => rcases hr0 with rfl | ⟨_, rfl⟩ <;> simp at h
  -- Helper for `s2` (after the aligned `ite`): if aligned `ite` exited with `(none, s2)`, either `b` was already checked (so `< 2^64`) or `s2 = s1` (when `n < 8` or unaligned)!
  rcases seq_step (Or.inr ⟨rv, rfl⟩) hret with ⟨u1, hu1⟩ | ⟨s2, hs2, hret2⟩
  · -- Aligned `ite` returned `u1`!
    rw [evaluateHOLFiniteState_ite] at hu1
    split at hu1
    · split at hu1
      · simp [evaluateHOLFiniteState_skip] at hu1
      · -- Inside aligned fast block!
        rcases seq_step (Or.inr ⟨u1, rfl⟩) hu1 with ⟨ua, hua⟩ | ⟨m20, hm20, h2⟩
        · rcases fast_ite_err_or_skip hs1_ma hs1_n (heb_var hs1_b) (Or.inr ⟨ua, rfl⟩) hua with hlt | heq
          · exact hlt
          · rw [heq] at hua; simp at hua
        rcases fast_ite_err_or_skip hs1_ma hs1_n (heb_var hs1_b) (Or.inl rfl) (congrArg Prod.fst hm20) with hlt | heq20
        · exact hlt
        rw [hm20] at heq20; injection heq20 with _ eq_m20; subst eq_m20
        rcases seq_step (Or.inr ⟨u1, rfl⟩) h2 with ⟨ub, hub⟩ | ⟨m32, hm32, h3⟩
        · rcases fast_ite_err_or_skip hs1_ma hs1_n (heb_var hs1_b) (Or.inr ⟨ub, rfl⟩) hub with hlt | heq
          · exact hlt
          · rw [heq] at hub; simp at hub
        rcases fast_ite_err_or_skip hs1_ma hs1_n (heb_var hs1_b) (Or.inl rfl) (congrArg Prod.fst hm32) with hlt | heq32
        · exact hlt
        rw [hm32] at heq32; injection heq32 with _ eq_m32; subst eq_m32
        rcases seq_step (Or.inr ⟨u1, rfl⟩) h3 with ⟨uc, huc⟩ | ⟨m52, hm52, h4⟩
        · rcases fast_ite_err_or_skip hs1_ma hs1_n (heb_var hs1_b) (Or.inr ⟨uc, rfl⟩) huc with hlt | heq
          · exact hlt
          · rw [heq] at huc; simp at huc
        rcases fast_ite_err_or_skip hs1_ma hs1_n (heb_var hs1_b) (Or.inl rfl) (congrArg Prod.fst hm52) with hlt | heq52
        · exact hlt
        rw [hm52] at heq52; injection heq52 with _ eq_m52; subst eq_m52
        -- Now `h4` is `(seq while32 while8w).1 = some (.returned u1)` from `s1`!
        -- Notice `while32` and `while8w` only return `0`, and CANNOT return anything if `n < 8`!
        by_cases hn32 : 32 ≤ n.toNat
        · have hcond32 : evalAt s1 (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32#64])) =
              some (.val (.word 1#64)) := by
            have hle_bv : 32#64 ≤ n := by rw [BitVec.le_def]; exact hn32
            simp [evalAt, evalHOLExact, evalListHOLExact, hs1_n, hs1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
              Compiler.Encoders.Asm.wordCmpHOL, hle_bv]
          rcases seq_step (Or.inr ⟨u1, rfl⟩) h4 with ⟨ud, hud⟩ | ⟨ml32, hml32, _⟩
          · exact while_first_iter ⟨1#64, hcond32, by decide⟩ (Or.inr ⟨ud, rfl⟩)
              (fun herr => first_word_b (st := decClockHOLFinite s1) hs1_ma (heb_i0 hs1_b hs1_i) herr) hud
          · exact while_first_iter ⟨1#64, hcond32, by decide⟩ (Or.inl rfl)
              (fun herr => first_word_b (st := decClockHOLFinite s1) hs1_ma (heb_i0 hs1_b hs1_i) herr) (congrArg Prod.fst hml32)
        · have hcond32_f : evalAt s1 (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32#64])) =
              some (.val (.word 0#64)) := by
            have hlt_bv : n < 32#64 := by rw [BitVec.lt_def]; change n.toNat < 32; omega
            have hnle_bv : ¬ (32#64 ≤ n) := by rw [BitVec.le_def]; change ¬ (32 ≤ n.toNat); omega
            simp [evalAt, evalHOLExact, evalListHOLExact, hs1_n, hs1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
              Compiler.Encoders.Asm.wordCmpHOL, hnle_bv, hlt_bv]
          rcases seq_step (Or.inr ⟨u1, rfl⟩) h4 with ⟨ud, hud⟩ | ⟨ml32, hml32, hl8w⟩
          · rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hud
            unfold evalAt at hcond32_f; rw [hcond32_f] at hud; simp at hud
          have hml32_eq := while_skip_false hcond32_f hml32; subst hml32_eq
          by_cases hn8 : 8 ≤ n.toNat
          · have hcond8 : evalAt s1 (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8#64])) =
                some (.val (.word 1#64)) := by
              have hle_bv : 8#64 ≤ n := by rw [BitVec.le_def]; exact hn8
              simp [evalAt, evalHOLExact, evalListHOLExact, hs1_n, hs1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
                Compiler.Encoders.Asm.wordCmpHOL, hle_bv]
            exact while_first_iter ⟨1#64, hcond8, by decide⟩ (Or.inr ⟨u1, rfl⟩)
              (fun herr => first_word_b (st := decClockHOLFinite s1) hs1_ma (heb_i0 hs1_b hs1_i) herr) hl8w
          · have hcond8_f : evalAt s1 (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8#64])) =
                some (.val (.word 0#64)) := by
              have hlt_bv : n < 8#64 := by rw [BitVec.lt_def]; change n.toNat < 8; omega
              have hnle_bv : ¬ (8#64 ≤ n) := by rw [BitVec.le_def]; change ¬ (8 ≤ n.toNat); omega
              simp [evalAt, evalHOLExact, evalListHOLExact, hs1_n, hs1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
                Compiler.Encoders.Asm.wordCmpHOL, hnle_bv, hlt_bv]
            rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hl8w
            unfold evalAt at hcond8_f; rw [hcond8_f] at hl8w; simp at hl8w
    · simp at hu1
  · -- Aligned `ite` exited with `(none, s2)`!
    have seq_none_pair : ∀ {st u : PanSemStateFiniteExact 64 F} {p1 p2 : ProgHOL 64},
        evaluateHOLFiniteState st (.seq p1 p2) = (none, u) →
        ∃ m, evaluateHOLFiniteState st p1 = (none, m) ∧ evaluateHOLFiniteState m p2 = (none, u) := by
      intro st u p1 p2 h
      rw [evaluateHOLFiniteState_seq_line780] at h
      rcases hp1 : evaluateHOLFiniteState st p1 with ⟨r1, m⟩
      rw [hp1] at h
      cases r1 with
      | none => exact ⟨m, rfl, h⟩
      | some _ => simp at h
    -- Either `b.toNat + n.toNat < 2 ^ 64` ALREADY holds (if `8 ≤ n` and aligned branch ran), OR `s2 = s1`!
    have hs2_or : b.toNat + n.toNat < 2 ^ 64 ∨ s2 = s1 := by
      rw [evaluateHOLFiniteState_ite] at hs2
      split at hs2
      · split at hs2
        · rw [evaluateHOLFiniteState_skip] at hs2; injection hs2 with _ e; exact Or.inr e.symm
        · obtain ⟨m20, hm20, hs2'⟩ := seq_none_pair hs2
          rcases fast_ite_err_or_skip hs1_ma hs1_n (heb_var hs1_b) (Or.inl rfl) (congrArg Prod.fst hm20) with hlt | heq20
          · exact Or.inl hlt
          rw [hm20] at heq20; injection heq20 with _ eq_m20; subst eq_m20
          obtain ⟨m32, hm32, hs2'⟩ := seq_none_pair hs2'
          rcases fast_ite_err_or_skip hs1_ma hs1_n (heb_var hs1_b) (Or.inl rfl) (congrArg Prod.fst hm32) with hlt | heq32
          · exact Or.inl hlt
          rw [hm32] at heq32; injection heq32 with _ eq_m32; subst eq_m32
          obtain ⟨m52, hm52, hs2'⟩ := seq_none_pair hs2'
          rcases fast_ite_err_or_skip hs1_ma hs1_n (heb_var hs1_b) (Or.inl rfl) (congrArg Prod.fst hm52) with hlt | heq52
          · exact Or.inl hlt
          rw [hm52] at heq52; injection heq52 with _ eq_m52; subst eq_m52
          obtain ⟨ml32, hml32, hs2'⟩ := seq_none_pair hs2'
          by_cases hn32 : 32 ≤ n.toNat
          · left
            have hcond32 : evalAt s1 (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32#64])) =
                some (.val (.word 1#64)) := by
              have hle_bv : 32#64 ≤ n := by rw [BitVec.le_def]; exact hn32
              simp [evalAt, evalHOLExact, evalListHOLExact, hs1_n, hs1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
                Compiler.Encoders.Asm.wordCmpHOL, hle_bv]
            exact while_first_iter ⟨1#64, hcond32, by decide⟩ (Or.inl rfl)
              (fun herr => first_word_b (st := decClockHOLFinite s1) hs1_ma (heb_i0 hs1_b hs1_i) herr) (congrArg Prod.fst hml32)
          · have hcond32_f : evalAt s1 (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32#64])) =
                some (.val (.word 0#64)) := by
              have hlt_bv : n < 32#64 := by rw [BitVec.lt_def]; change n.toNat < 32; omega
              have hnle_bv : ¬ (32#64 ≤ n) := by rw [BitVec.le_def]; change ¬ (32 ≤ n.toNat); omega
              simp [evalAt, evalHOLExact, evalListHOLExact, hs1_n, hs1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
                Compiler.Encoders.Asm.wordCmpHOL, hnle_bv, hlt_bv]
            have hml32_eq := while_skip_false hcond32_f hml32; subst hml32_eq
            by_cases hn8 : 8 ≤ n.toNat
            · left
              have hcond8 : evalAt s1 (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8#64])) =
                  some (.val (.word 1#64)) := by
                have hle_bv : 8#64 ≤ n := by rw [BitVec.le_def]; exact hn8
                simp [evalAt, evalHOLExact, evalListHOLExact, hs1_n, hs1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
                  Compiler.Encoders.Asm.wordCmpHOL, hle_bv]
              exact while_first_iter ⟨1#64, hcond8, by decide⟩ (Or.inl rfl)
                (fun herr => first_word_b (st := decClockHOLFinite s1) hs1_ma (heb_i0 hs1_b hs1_i) herr) (congrArg Prod.fst hs2')
            · right
              have hcond8_f : evalAt s1 (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8#64])) =
                  some (.val (.word 0#64)) := by
                have hlt_bv : n < 8#64 := by rw [BitVec.lt_def]; change n.toNat < 8; omega
                have hnle_bv : ¬ (8#64 ≤ n) := by rw [BitVec.le_def]; change ¬ (8 ≤ n.toNat); omega
                simp [evalAt, evalHOLExact, evalListHOLExact, hs1_n, hs1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
                  Compiler.Encoders.Asm.wordCmpHOL, hnle_bv, hlt_bv]
              exact while_skip_false hcond8_f hs2'
      · simp at hs2
    rcases hs2_or with hlt | rfl
    · exact hlt
    -- Now `s2 = s1`! Next in `hret2` is `seq while8b (seq while1b (return 1))`!
    by_cases hn8 : 8 ≤ n.toNat
    · have hcond8b : evalAt s1 (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8#64])) =
          some (.val (.word 1#64)) := by
        have hle_bv : 8#64 ≤ n := by rw [BitVec.le_def]; exact hn8
        simp [evalAt, evalHOLExact, evalListHOLExact, hs1_n, hs1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
          Compiler.Encoders.Asm.wordCmpHOL, hle_bv]
      rcases seq_step (Or.inr ⟨rv, rfl⟩) hret2 with ⟨ue, hue⟩ | ⟨s3, hs3, _⟩
      · exact while_first_iter ⟨1#64, hcond8b, by decide⟩ (Or.inr ⟨ue, rfl⟩)
          (fun herr => first_byte_b (st := decClockHOLFinite s1) hs1_ma (heb_i0 hs1_b hs1_i) herr) hue
      · exact while_first_iter ⟨1#64, hcond8b, by decide⟩ (Or.inl rfl)
          (fun herr => first_byte_b (st := decClockHOLFinite s1) hs1_ma (heb_i0 hs1_b hs1_i) herr) (congrArg Prod.fst hs3)
    · have hcond8b_f : evalAt s1 (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8#64])) =
          some (.val (.word 0#64)) := by
        have hlt_bv : n < 8#64 := by rw [BitVec.lt_def]; change n.toNat < 8; omega
        have hnle_bv : ¬ (8#64 ≤ n) := by rw [BitVec.le_def]; change ¬ (8 ≤ n.toNat); omega
        simp [evalAt, evalHOLExact, evalListHOLExact, hs1_n, hs1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
          Compiler.Encoders.Asm.wordCmpHOL, hnle_bv, hlt_bv]
      rcases seq_step (Or.inr ⟨rv, rfl⟩) hret2 with ⟨ue, hue⟩ | ⟨s3, hs3, hret3⟩
      · rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hue
        unfold evalAt at hcond8b_f; rw [hcond8b_f] at hue; simp at hue
      have hs3_eq := while_skip_false hcond8b_f hs3; subst hs3_eq
      -- Now `s3 = s1`, and `1 ≤ n.toNat`, so `0 < n` (`while1b` condition `i < n` is TRUE)!
      have hcond1b : evalAt s1 (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
          some (.val (.word 1#64)) := by
        have hlt_bv : (0#64 : BitVec 64) < n := by rw [BitVec.lt_def]; change 0 < n.toNat; omega
        simp [evalAt, evalHOLExact, hs1_n, hs1_i, Compiler.Encoders.Asm.wordCmpHOL, hlt_bv]
      rcases seq_step (Or.inr ⟨rv, rfl⟩) hret3 with ⟨uf, huf⟩ | ⟨s4, hs4, _⟩
      · exact while_first_iter ⟨1#64, hcond1b, by decide⟩ (Or.inr ⟨uf, rfl⟩)
          (fun herr => first_byte_b (st := decClockHOLFinite s1) hs1_ma (heb_i0 hs1_b hs1_i) herr) huf
      · exact while_first_iter ⟨1#64, hcond1b, by decide⟩ (Or.inl rfl)
          (fun herr => first_byte_b (st := decClockHOLFinite s1) hs1_ma (heb_i0 hs1_b hs1_i) herr) (congrArg Prod.fst hs4)

/-! ## 3. Full `htab_set` Body Spec and `htab_set_spec_proof` -/

theorem htab_set_body_spec {F : Type}
    (s0 : PanSemStateFiniteExact 64 F)
    (tw keyw valw : BitVec 64)
    (ht0 : s0.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hkey0 : s0.locals.lookup (ofString "key") = some (.val (.word keyw)))
    (hval0 : s0.locals.lookup (ofString "value") = some (.val (.word valw)))
    (hA0 : ArenaReady s0)
    (hW0 : HtabWF s0 tw.toNat)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i) :
    Ret s0 (sourceFnBody Guest.Software.guestFn_htab_set)
      (fun _ post => HtabExitAt tw.toNat s0 post) := by
  set t := tw.toNat
  have hLF := locFree_htabExitAt s0 t
  obtain ⟨hB0, L0, I0, Fr0, hT0⟩ := (htabWF_iff s0 t).mp hW0
  obtain ⟨hnc0_lt, hst0_ge8, hst0_le64, hst0_al, ht_lo, ht_hi, ht_al⟩ := htabBlocks_bounds hB0
  have hnx0_le : hdr s0 t 8 ≤ hdr s0 t 10 + 1 := hB0.2.2.2.2.2.2.2
  have hklen_le60 : hdr s0 t 0 ≤ 60 := hB0.2.2.2.1
  have hklen_le_st : hdr s0 t 0 ≤ hdr s0 t 1 := by have := hB0.2.2.2.2.1; omega
  have hhe : heapEnd = 33806089704 := rfl
  obtain ⟨hdom0_t0, hm0_t0⟩ := word_of_hdr s0 tw 0 (by omega) hB0
  obtain ⟨hdom0_t1, hm0_t1⟩ := word_of_hdr s0 tw 1 (by omega) hB0
  obtain ⟨hdom0_t4, hm0_t4⟩ := word_of_hdr s0 tw 4 (by omega) hB0
  obtain ⟨hdom0_t5, hm0_t5⟩ := word_of_hdr s0 tw 5 (by omega) hB0
  obtain ⟨hdom0_t7, hm0_t7⟩ := word_of_hdr s0 tw 7 (by omega) hB0
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
  -- 1. dec klen := load(t + 0)
  apply Ret.dec_lf hLF; intro vkl hvkl
  obtain ⟨_, rfl⟩ := ev_field_load s0 (ofString "t") tw 0#64 ht0 vkl hvkl
  have hm0 : s0.memory (tw + 0#64) = .word klenw := hm0_t0
  rw [hm0]
  -- 2. dec stride := load(t + 8)
  apply Ret.dec_lf hLF; intro vst hvst
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 8#64
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht0, show ofString "klen" ≠ ofString "t" by decide]) vst hvst
  have hm8 : (setVarHOLFinite (ofString "klen") (.val (.word klenw)) s0).memory (tw + 8#64) = .word stridew := hm0_t1
  rw [hm8]
  -- 3. decCall leaf := htab_find_leaf(t, key)
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
  -- Notice `LocFrame entry_fl post_fl` gives `LocFrame s0 { post_fl with locals := s_fl_pre.locals }`!
  have hs_lf_fr : LocFrame s0 (setVarHOLFinite (ofString "leaf") (.val (.word leafw)) { post_fl with locals := s_fl_pre.locals }) := by
    unfold LocFrame at hfr_fl ⊢
    dsimp [setVarHOLFinite]
    rw [hfr_fl]; rfl
  -- 4. dec keys := load(t + 32)
  apply Ret.dec_lf hLF; intro vks hvks
  obtain ⟨_, hvks_eq⟩ := ev_field_load _ (ofString "t") tw 32#64
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "leaf" ≠ ofString "t" by decide]; exact ht_fl_pre) vks hvks
  have hm32_lf : (setVarHOLFinite (ofString "leaf") (.val (.word leafw)) { post_fl with locals := s_fl_pre.locals }).memory (tw + 32#64) = .word keysw := by
    rw [hs_lf_fr.memory]; exact hm0_t4
  rw [hm32_lf] at hvks_eq
  subst hvks_eq
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
  -- 5. `ite (leaf == 0)`
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
  · -- Branch A: `leaf == 0` (`cnt = 0`)!
    have hlf0 := hcw_lf_spec.1 hcw_nz
    have hcnt0 : hdr s0 t 3 = 0 := by
      rcases hleaf_cases with ⟨_, hc⟩ | ⟨hnz, _⟩
      · exact hc
      · exact absurd hlf0 hnz
    exact htab_set_branch_empty s0 s_k tw keyw valw hLF hs_k_fr hA0 hW0 hal0 hcnt0 ht_sk hkey_sk hval_sk
  · -- `leaf != 0` (`0 < cnt`, `leafw.toNat ∈ L0`)!
    have hlf_nz := hcw_lf_spec.2 hcw_z
    obtain ⟨_, hcnt_pos_efl, hleaf_mem_efl⟩ := hleaf_cases.resolve_left (fun h => hlf_nz h.1)
    have hcnt_pos : 0 < hdr s0 t 3 := hcnt_pos_efl
    have hleaf_mem : ∀ L I Fr,
        TreeWF L I Fr (hdr s0 t 8) (hdr s0 t 0) (hdr s0 t 3) (hdr s0 t 7) (hdr s0 t 9)
          (nodeF s0 (hdr s0 t 5)) (fun i => memW s0 (hdr s0 t 6 + 8 * i)) →
        leafw.toNat ∈ L := hleaf_mem_efl
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
      have hz : leafw * stridew + (0 : BitVec 64) = leafw * stridew := BitVec.add_zero _
      rw [hz]
    -- 6. `decCall eq := memeq(keys + leaf * stride, key, klen)`
    refine Ret.decCall3_lf hLF hcode_sk (by decide) (by decide) (by decide)
      lookup_memeq_fn lkeyw keyw klenw hev_lkey
      (by simp [evalAt, evalHOLExact]; exact hkey_sk)
      (by simp [evalAt, evalHOLExact]; exact hkl_sk) ?_
    intro eqw post_meq hrun_meq
    let entry_meq := callEntryStateHOLFinite s_k
      (((HolFiniteMapExact.empty.update (ofString "a", .val (.word lkeyw))).update
        (ofString "b", .val (.word keyw))).update (ofString "n", .val (.word klenw)))
    have hfr_meq_eval := locFrameW_eval (sourceFnBody Guest.Software.guestFn_memeq) (by rfl) entry_meq
    rw [hrun_meq] at hfr_meq_eval
    dsimp only at hfr_meq_eval
    let s_eq := setVarHOLFinite (ofString "eq") (.val (.word eqw)) { post_meq with locals := s_k.locals }
    have hs_eq_fr : LocFrame s0 s_eq := by
      unfold LocFrame at hs_k_fr hfr_meq_eval ⊢
      dsimp [s_eq, setVarHOLFinite]
      rw [hfr_meq_eval]
      dsimp [entry_meq, callEntryStateHOLFinite, decClockHOLFinite]
      rw [hs_k_fr]
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
    -- 7. `ite (eq != 0)`
    refine Ret.ite_ret
      (fun _ => noFlow_seq_right fun _ => noFlow_ret) ?_
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
    refine ⟨fun hcw_eq_nz => ?_, fun hcw_eq_z => ?_⟩
    · -- Branch B: `eq != 0` -> key match overwrite!
      exact htab_set_branch_overwrite s0 s_eq tw leafw valw hs_eq_fr hA0 hW0 hal0 hleaf_mem ht_seq hleaf_seq hval_seq
    · -- Branch C: `eq == 0` -> key mismatch -> crit-bit splice!
      have heqw0 : eqw = 0 := hcw_eq_spec.2 hcw_eq_z
      have hG_entry_meq : GuestInv entry_meq := by
        have hfr_em : LocFrame s0 entry_meq := by
          unfold LocFrame at hs_k_fr ⊢
          dsimp [entry_meq, callEntryStateHOLFinite, decClockHOLFinite]
          rw [hs_k_fr]
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
      have hlkey_nw : lkeyw.toNat + klenw.toNat < 2 ^ 64 := by
        rw [hlkeyw_nat, hklenw_nat]; omega
      have hrun_meq0 : (evaluateHOLFiniteState entry_meq (sourceFnBody Guest.Software.guestFn_memeq)).1 =
          some (.returned (.val (.word 0))) := by
        rw [hrun_meq, heqw0]
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
      -- 8. `decCall d := htab_first_diff(key, keys + leaf * stride, klen)`
      have hev_lkey_seq : evalAt s_eq (.op .add [.var .local (ofString "keys"),
          .panop .mul [.var .local (ofString "leaf"), .var .local (ofString "stride")]]) =
          some (.val (.word lkeyw)) := by
        simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
          hkeys_seq, hleaf_seq, hst_seq, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
          valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
        have hz : leafw * stridew + (0 : BitVec 64) = leafw * stridew := BitVec.add_zero _
        rw [hz]
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
      rw [hrun_fd] at hfr_fd_eval
      dsimp only at hfr_fd_eval
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
        dsimp [s_d, setVarHOLFinite]
        rw [hfr_fd_eval]
        dsimp [entry_fd, callEntryStateHOLFinite, decClockHOLFinite]
        rw [hs_eq_fr]
      have ht_sd : s_d.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        simp [s_d, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_seq, show ofString "d" ≠ ofString "t" by decide]
      have hkey_sd : s_d.locals.lookup (ofString "key") = some (.val (.word keyw)) := by
        simp [s_d, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hkey_seq, show ofString "d" ≠ ofString "key" by decide]
      have hval_sd : s_d.locals.lookup (ofString "value") = some (.val (.word valw)) := by
        simp [s_d, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hval_seq, show ofString "d" ≠ ofString "value" by decide]
      -- 9. `dec nodes := load(t + 40); dec p := 0; dec n := load(t + 56)`
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
      -- 10. Descent `while (n != 0)` loop!
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
      -- 11. `decCall nl := htab_new_leaf(t, key, value)`
      have hmem_u : u_lp.memory = s0.memory := hu_fr.memory
      have hg_u : u_lp.globals = s0.globals := by unfold LocFrame at hu_fr; rw [hu_fr]
      have hA_ulp : ArenaReady u_lp := by
        unfold LocFrame at hu_fr; rw [hu_fr]; exact (arenaReady_locals s0 _ _).mpr hA0
      have hNS_ulp : NodeState u_lp t (L0 ++ I0) Fr0 := by
        have hNS0 : NodeState s0 t (L0 ++ I0) Fr0 := ⟨hB0, hT0.2.1, hT0.2.2.1, hT0.2.2.2.2.2.2.2.2.2.2.2⟩
        unfold LocFrame at hu_fr; rw [hu_fr]; exact hNS0
      have hcnt_le_ulp : hdr u_lp t 3 ≤ (L0 ++ I0).length := by
        have hh3_u : hdr u_lp t 3 = hdr s0 t 3 := by unfold hdr memW; rw [hmem_u]
        have hlen := hT0.1
        rw [hh3_u, List.length_append]; omega
      have hal_ulp : ∀ i ∈ htabFootprint u_lp t, Allocated u_lp i := by
        unfold LocFrame at hu_fr; rw [hu_fr]; exact hal0
      refine Ret.decCall_new_leaf_lf hLF tw keyw valw (L0 ++ I0) Fr0
        (by simp [evalAt, evalHOLExact]; exact ht_ulp)
        (by simp [evalAt, evalHOLExact]; exact hkey_ulp)
        (by simp [evalAt, evalHOLExact]; exact hval_ulp)
        hA_ulp hNS_ulp hcnt_le_ulp hal_ulp ?_
      intro nlw Fr1 s1 hA1 hNS1 hh0_1 hh1_1 hh3_1 hh7_1 _ _ n16_1 n24_1 ordc_1 hnd_1 hord_1 hhp_1 hfp_1 hfr_1 hg_1 hloc_1
      let s1_nl := setVarHOLFinite (ofString "nl") (.val (.word nlw)) s1
      have hA1_nl : ArenaReady s1_nl := (arenaReady_locals s1 _ s1.clock).mpr hA1
      have hNS1_nl : NodeState s1_nl t ((L0 ++ I0) ++ [nlw.toNat]) Fr1 := hNS1
      have hal1_nl : ∀ i ∈ htabFootprint s1_nl t, Allocated s1_nl i := fun i hi => (hfp_1 i hi).1
      have ht_s1nl : (setVarHOLFinite (ofString "nl") (.val (.word nlw)) s1).locals.lookup (ofString "t") = some (.val (.word tw)) := by
        simp [setVarHOLFinite, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, ht_ulp,
          show ofString "nl" ≠ ofString "t" by decide]
      have hd_s1nl : (setVarHOLFinite (ofString "nl") (.val (.word nlw)) s1).locals.lookup (ofString "d") = some (.val (.word dw)) := by
        simp [setVarHOLFinite, hloc_1, HolFiniteMapExact.lookup_update, FUPDATE, hd_ulp,
          show ofString "nl" ≠ ofString "d" by decide]
      -- 12. `decCall ni := htab_new_internal(t, d)`
      refine Ret.decCall_new_internal_lf hLF tw dw ((L0 ++ I0) ++ [nlw.toNat]) Fr1
        (by simp [evalAt, evalHOLExact]; exact ht_s1nl)
        (by simp [evalAt, evalHOLExact]; exact hd_s1nl)
        hA1_nl hNS1_nl hal1_nl ?_
      intro niw Fr2 s2 hA2 hNS2 hh0_2 hh1_2 hh3_2 hh7_2 _ _ _ _ ni24_2 hnd_2 hord_2 hhp_2 hfp_2 hfr_2 hg_2 hloc_2
      -- Normalize `setVarHOLFinite "ni" niw s2` into `NS s2 L_cur s2.globals s2.memory s2.clock`!
      let L_cur := (u_lp.locals.update (ofString "nl", .val (.word nlw))).update (ofString "ni", .val (.word niw))
      have hs2_ni_eq : setVarHOLFinite (ofString "ni") (.val (.word niw)) s2 =
          NS s2 L_cur s2.globals s2.memory s2.clock := by
        simp [setVarHOLFinite, NS, hloc_2, hloc_1, L_cur]
      rw [hs2_ni_eq]
      -- Assemble all hypotheses of `htab_set_splice_exec`!
      have hh_u : ∀ k, hdr u_lp t k = hdr s0 t k := fun k => by unfold hdr memW; rw [hmem_u]
      have hfp_u : htabFootprint u_lp t = htabFootprint s0 t := by simp [htabFootprint, hdr, memW, hmem_u]
      have hgn_u : globN u_lp "heap_ptr" = globN s0 "heap_ptr" := by unfold globN; rw [hg_u]
      have hh0_20 : hdr s2 t 0 = hdr s0 t 0 := hh0_2.trans (hh0_1.trans (hh_u 0))
      have hh1_20 : hdr s2 t 1 = hdr s0 t 1 := hh1_2.trans (hh1_1.trans (hh_u 1))
      have hh3_20 : hdr s2 t 3 = hdr s0 t 3 + 1 := hh3_2.trans (hh3_1.trans (by rw [hh_u 3]))
      have hh7_20 : hdr s2 t 7 = hdr s0 t 7 := hh7_2.trans (hh7_1.trans (hh_u 7))
      have hnl_mem_A1 : nlw.toNat ∈ (L0 ++ I0) ++ [nlw.toNat] := List.mem_append_right _ (by simp)
      have hnl16_20 : nodeF s2 (hdr s2 t 5) nlw.toNat 16 = hdr s0 t 3 :=
        (hnd_2 nlw.toNat hnl_mem_A1 16 (Or.inr (Or.inr (Or.inl rfl)))).trans (n16_1.trans (hh_u 3))
      have hnl24_20 : nodeF s2 (hdr s2 t 5) nlw.toNat 24 = 8 * hdr s0 t 0 :=
        (hnd_2 nlw.toNat hnl_mem_A1 24 (Or.inr (Or.inr (Or.inr rfl)))).trans (n24_1.trans (by rw [hh_u 0]))
      have hcnt_lt_nc1 : hdr s0 t 3 < hdr s1 tw.toNat 10 + 1 := by
        have hB1 : HtabBlocks s1 tw.toNat := hNS1.1
        have hnx1_le : hdr s1 tw.toNat 8 ≤ hdr s1 tw.toNat 10 + 1 := hB1.2.2.2.2.2.2.2
        have hnd1 := (List.nodup_append.mp hNS1.2.1).1
        have hr1 : ∀ x ∈ (L0 ++ I0) ++ [nlw.toNat], 1 ≤ x ∧ x < hdr s1 tw.toNat 8 := fun x hx =>
          (hNS1.2.2.1 x).mp (List.mem_append_left _ hx)
        have hlen_le := nodup_len_le_range hnd1 hr1
        have hL0_len : L0.length = hdr s0 t 3 := hT0.1
        have hnl_rng := hr1 nlw.toNat (List.mem_append_right _ (by simp))
        have hnx1_ge1 : 1 ≤ hdr s1 tw.toNat 8 := by omega
        simp only [List.length_append, List.length_singleton] at hlen_le
        omega
      have hord_cnt_20 : memW s2 (hdr s2 t 6 + 8 * hdr s0 t 3) = nlw.toNat := by
        have h1 := hord_2 (hdr s0 t 3) hcnt_lt_nc1
        have h2 : memW s1 (hdr s1 t 6 + 8 * hdr s0 t 3) = nlw.toNat := by
          rw [← hh_u 3]; exact ordc_1
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
        have h2 : nodeF s1 (hdr s1 t 5) z off = nodeF u_lp (hdr u_lp t 5) z off :=
          hnd_1 z hz off hoff
        have h3 : nodeF u_lp (hdr u_lp t 5) z off = nodeF s0 (hdr s0 t 5) z off := by
          rw [hh_u 5]; unfold nodeF memW; rw [hmem_u]
        exact (h1.trans h2).trans h3
      have hhp_01 : globN s0 "heap_ptr" ≤ globN s1 "heap_ptr" := by rw [← hgn_u]; exact hhp_1
      have hhp_12 : globN s1 "heap_ptr" ≤ globN s2 "heap_ptr" := hhp_2
      have hhp_20 : globN s0 "heap_ptr" ≤ globN s2 "heap_ptr" := le_trans hhp_01 hhp_12
      have hfp_10 : ∀ i ∈ htabFootprint s1 t, Allocated s1 i ∧
          ((∃ j ∈ htabFootprint s0 t, Inside i j.1 (j.1 + j.2)) ∨
            Inside i (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (globN s1 "heap_ptr" - globN s0 "heap_ptr"))) := by
        intro i hi
        obtain ⟨hal, hprov⟩ := hfp_1 i hi
        rw [hfp_u, hgn_u] at hprov
        exact ⟨hal, hprov⟩
      have hfp_20 : ∀ i ∈ htabFootprint s2 t, Allocated s2 i ∧
          ((∃ j ∈ htabFootprint s0 t, Inside i j.1 (j.1 + j.2)) ∨
            Inside i (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (globN s2 "heap_ptr" - globN s0 "heap_ptr"))) := by
        intro i hi
        obtain ⟨hal2, hprov2⟩ := hfp_2 i hi
        refine ⟨hal2, ?_⟩
        rcases hprov2 with ⟨j, hj, hij⟩ | hfr2
        · rcases (hfp_10 j hj).2 with ⟨k, hk, hjk⟩ | hjf
          · exact Or.inl ⟨k, hk, ⟨le_trans hjk.1 hij.1, le_trans hij.2 hjk.2⟩⟩
          · exact Or.inr ⟨le_trans hjf.1 hij.1, by have := hij.2; have := hjf.2; omega⟩
        · change Inside i (globN s1 "heap_ptr") (globN s1 "heap_ptr" + (globN s2 "heap_ptr" - globN s1 "heap_ptr")) at hfr2
          exact Or.inr ⟨by have := hfr2.1; omega, by have := hfr2.2; omega⟩
      have hfr_10 : FrameOutside s0 s1 (htabFootprint s0 t)
          (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
        intro x hxk hxf
        rw [hfr_1 x (by rw [hfp_u]; exact hxk) (by rw [hgn_u]; exact hxf), hmem_u]
      have hfr_10_wide : FrameOutside s0 s1 (htabFootprint s0 t)
          (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr") :=
        frameOutside_mono hfr_10 (fun i hi => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) ⟨le_rfl, by dsimp; omega⟩
      have hfr_12_wide : FrameOutside s1 s2 (htabFootprint s0 t)
          (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr") :=
        frameOutside_mono (a := s1) (b := s2) hfr_2
          (fun i hi => (hfp_10 i hi).2.elim Or.inl (fun h => Or.inr ⟨h.1, le_trans h.2 (by dsimp; omega)⟩))
          ⟨hhp_01, by change globN s1 "heap_ptr" + (globN s2 "heap_ptr" - globN s1 "heap_ptr") ≤ globN s0 "heap_ptr" + (globN s2 "heap_ptr" - globN s0 "heap_ptr"); omega⟩
      have hfr_20 : FrameOutside s0 s2 (htabFootprint s0 t)
          (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr") :=
        fun x hxk hxf => (hfr_12_wide x hxk hxf).trans (hfr_10_wide x hxk hxf)
      have hg_20 : ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
          s0.globals.lookup k = s2.globals.lookup k := by
        intro k hk
        rw [← hg_u, hg_1 k hk]
        exact hg_2 k hk
      exact htab_set_splice_exec s0 s2 tw dw pw nw nlw niw L0 I0 Fr0 Fr2 L_cur
        (by simp [L_cur, HolFiniteMapExact.lookup_update, FUPDATE, ht_ulp,
          show ofString "ni" ≠ ofString "t" by decide, show ofString "nl" ≠ ofString "t" by decide])
        (by simp [L_cur, HolFiniteMapExact.lookup_update, FUPDATE, hp_ulp,
          show ofString "ni" ≠ ofString "p" by decide, show ofString "nl" ≠ ofString "p" by decide])
        (by simp [L_cur, HolFiniteMapExact.lookup_update, FUPDATE, hn_ulp,
          show ofString "ni" ≠ ofString "n" by decide, show ofString "nl" ≠ ofString "n" by decide])
        (by simp [L_cur, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "ni" ≠ ofString "nl" by decide])
        (by simp [L_cur, HolFiniteMapExact.lookup_update, FUPDATE])
        hA2 hNS2 hT0 hcnt_pos hd_lt hnw_LI hpw_spec0
        hh0_20 hh1_20 hh3_20 hh7_20 hnl16_20 hnl24_20 ni24_2
        hord_cnt_20 hord_old_20 hnd_old_20 hhp_20 hfp_20 hfr_20 hg_20

theorem htab_set_spec_proof :
    ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
      originalRuntimeCode.lookup (ofString "htab_set") = some (params, body, retShape) ∧
      ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → HtabArgWF s →
        (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_set") values =
          some (body, s.locals, retShape)) →
        (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
        ∀ v, (evaluateHOLFiniteState s body).1 = some (.returned v) →
          HtabExit s (evaluateHOLFiniteState s body).2 := by
  refine ⟨[(ofString "t", .one), (ofString "key", .one), (ofString "value", .one)],
    sourceFnBody Guest.Software.guestFn_htab_set, .one, lookup_htab_set, ?_⟩
  intro F s _ hP ⟨values, hl⟩ _ v hv
  obtain ⟨tw, keyw, valw, ht, hkey, hval⟩ :=
    three_word_params_of_lookupCode s (ofString "htab_set")
      (ofString "t") (ofString "key") (ofString "value")
      (by decide) (by decide) (by decide) _ _ lookup_htab_set values hl
  have hloc_t : locN s "t" = tw.toNat := by simp [locN, ht]
  obtain ⟨hA0, hW0, hal0⟩ := hP
  rw [hloc_t] at hW0 hal0
  rw [htabExit_iff_at, hloc_t]
  exact htab_set_body_spec s tw keyw valw ht hkey hval hA0 hW0 hal0 v hv

end InitECandidate.Solver.Wave8GuestInv.SoloHtabSet

