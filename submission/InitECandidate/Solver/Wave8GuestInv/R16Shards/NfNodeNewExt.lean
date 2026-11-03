import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptSpecBase

/-! `nf_node_new_ext`: `node_new_ext(nib, nlen, child)` preserves typed node heaps (`NodeFn ["child"]`).
Allocates a fresh 56-byte heap block `nd = globN s "heap_ptr"`, stores kind `2`, zeroes cache words
`+8/+16/+24`, stores `nib/+32`, `nlen/+40`, `child/+48`, and returns `nd`. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

private theorem updW_ne {m : BitVec 64 → HolWordLab 64} {a b w : BitVec 64} (h : b ≠ a) :
    Wave8Contracts.M26.updW m a w b = m b := by
  simp [Wave8Contracts.M26.updW, h]

private theorem updW_eq {m : BitVec 64 → HolWordLab 64} {a w : BitVec 64} :
    Wave8Contracts.M26.updW m a w a = .word w := by
  simp [Wave8Contracts.M26.updW]

/-- `node_new_ext` (AST line 10021): typed nodes in, typed nodes out (MPT tier);
requirement: `KeyIn s Nd (locN s "nib") (locN s "nlen")`. -/
theorem «nf_node_new_ext» :
    NodeFn ["child"]
    (fun s Nd =>
      KeyIn s Nd (locN s "nib") (locN s "nlen"))
    (ofString "node_new_ext") := by
  refine ⟨_, _, _, lookup_node_new_ext, ?_⟩
  intro F s hcode hP ⟨callVals, hcallL⟩ _hnt hres
  have hAR : ArenaReady s := hP.1
  have hG : GuestInv s := hAR.1
  have hA : ArenaOK s := hAR.2
  obtain ⟨hp, fp, sp, hhp, hhp_eq, hfp, hfp_eq, hsp, hsp_eq⟩ :=
    Wave8Contracts.M26.arenaOK_globals s hA
  obtain ⟨wnib, hlk_nib, hloc_nib⟩ := lookup_param_word lookup_node_new_ext hcallL
    [] "nib" [(ofString "nlen", .one), (ofString "child", .one)] rfl (by decide)
  obtain ⟨wnlen, hlk_nlen, hloc_nlen⟩ := lookup_param_word lookup_node_new_ext hcallL
    [(ofString "nib", .one)] "nlen" [(ofString "child", .one)] rfl (by decide)
  obtain ⟨wchild, hlk_child, hloc_child⟩ := lookup_param_word lookup_node_new_ext hcallL
    [(ofString "nib", .one), (ofString "nlen", .one)] "child" [] rfl (by decide)
  have hbody : sourceFnBody Guest.Software.guestFn_node_new_ext =
      .decCall (ofString "nd") .one (ofString "alloc") [.const 56]
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 0)]) (.const (BitVec.ofNat 64 2)))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 8)]) (.const (BitVec.ofNat 64 0)))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 16)]) (.const (BitVec.ofNat 64 0)))
              (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 24)]) (.const (BitVec.ofNat 64 0)))
                (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 32)]) (.var .local (ofString "nib")))
                  (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 40)]) (.var .local (ofString "nlen")))
                    (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 48)]) (.var .local (ofString "child")))
                      (.return (.var .local (ofString "nd")))))))))) := rfl
  set res := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_new_ext)).1
  set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_new_ext)).2
  have hres' : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_new_ext)).1 := hres
  rw [hbody] at hres'
  obtain ⟨values, abody, acallee, aret, hcz, hargs, hl, hexn | ⟨rv, apost, harun, _, hcont_res, hr_eq, hp_eq⟩⟩ :=
    decCall_resumes_inv hres'
  · obtain ⟨eid, ev, ha_exn, hne_trap, _⟩ := hexn
    have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "alloc")
      _ _ _ _ _ values acallee (by rw [hcode]; exact lookup_alloc) hl
    subst hsame
    obtain ⟨_, hret_a⟩ := alloc_body_resumes_eq_returned (callEntryStateHOLFinite s acallee) hcode
      (by rw [ha_exn]; exact Or.inr ⟨eid, ev, rfl, hne_trap⟩)
    rw [ha_exn] at hret_a; cases hret_a
  · have hvals : values = [.val (.word 56)] := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      simpa [evalListHOLExact, evalHOLExact] using hargs.symm
    subst hvals
    have hl_exact := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_alloc) 56 (by rw [hcode]; exact lookup_alloc)
    rw [hl_exact] at hl
    obtain ⟨hbody_a, hrest_a⟩ := Prod.mk.inj (Option.some.inj hl.symm)
    obtain ⟨hcal_a, hret_a⟩ := Prod.mk.inj hrest_a
    subst hbody_a hcal_a hret_a
    have hn_ent : (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word 56)))).locals.lookup
        (ofString "n") = some (.val (.word 56)) := by
      simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have harun_info := Wave8Contracts.M26.alloc_body_run
      (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word 56))))
      hp 56 hcode hhp hn_ent rv (by rw [harun])
    rw [harun] at harun_info
    obtain ⟨rfl, hcmp1, hcmp2, hapost_eq⟩ := harun_info
    dsimp only at hapost_eq
    set q : BitVec 64 := (hp + (56 + 7)) &&& ((0 : BitVec 64) - 8)
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hA.2.1
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
    obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q⟩ := Wave8Contracts.M26.alloc_arith hp 56 hhp_hi hhp_al hcmp1 hcmp2
    change q.toNat = hp.toNat + ((56 : BitVec 64).toNat + 7) / 8 * 8 at hq_eq
    change q.toNat ≤ heapLimit at hq_hi
    have h56 : ((56 : BitVec 64).toNat + 7) / 8 * 8 = 56 := by decide
    rw [h56] at hq_eq
    have hhl_lt : heapLimit < 2 ^ 64 := by decide
    have hhp_add : ∀ k : Nat, k ≤ 56 →
        hp + BitVec.ofNat 64 k = BitVec.ofNat 64 (hp.toNat + k) ∧
        (hp + BitVec.ofNat 64 k).toNat = hp.toNat + k := by
      intro k hk
      have hlt : hp.toNat + k < 2 ^ 64 := by omega
      have heq : hp + BitVec.ofNat 64 k = BitVec.ofNat 64 (hp.toNat + k) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      exact ⟨heq, by rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]⟩
    set s0 := setVarHOLFinite (ofString "nd") (.val (.word hp)) { apost with locals := s.locals }
    have hs0_nd : s0.locals.lookup (ofString "nd") = some (.val (.word hp)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs0_nib : s0.locals.lookup (ofString "nib") = some (.val (.word wnib)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_nib,
        show ofString "nd" ≠ ofString "nib" by decide]
    have hs0_nlen : s0.locals.lookup (ofString "nlen") = some (.val (.word wnlen)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_nlen,
        show ofString "nd" ≠ ofString "nlen" by decide]
    have hs0_child : s0.locals.lookup (ofString "child") = some (.val (.word wchild)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_child,
        show ofString "nd" ≠ ofString "child" by decide]
    have hs0_dom : ∀ k : Nat, k < 56 → k % 8 = 0 → s0.memaddrs (hp + BitVec.ofNat 64 k) := by
      intro k hk hk8
      have hma : s0.memaddrs = ordinaryDomain := by
        simp [s0, setVarHOLFinite]; rw [hapost_eq]; exact hG.memaddrs
      rw [hma, (hhp_add k (by omega)).1]
      have hhe_ge : heapLimit ≤ heapEnd := by decide
      exact Wave8Contracts.M26.ordinaryDomain_of_nat (hp.toNat + k)
        (by rw [hhp_eq]; have := hA.1; omega)
        (by omega)
        (by omega)
    have step_store_const : ∀ (st : PanSemStateFiniteExact 64 F) (k c : Nat),
        st.locals = s0.locals → st.memaddrs = s0.memaddrs → k < 56 → k % 8 = 0 →
        evaluateHOLFiniteState st
          (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 k)])
            (.const (BitVec.ofNat 64 c))) =
          (none, { st with memory := Wave8Contracts.M26.updW st.memory (hp + BitVec.ofNat 64 k) (BitVec.ofNat 64 c) }) := by
      intro st k c hloc hma hk hk8
      have hnd : st.locals.lookup (ofString "nd") = some (.val (.word hp)) := by rw [hloc]; exact hs0_nd
      have hdom : st.memaddrs (hp + BitVec.ofNat 64 k) := by rw [hma]; exact hs0_dom k hk hk8
      rw [evaluateHOLFiniteState_store]
      have hd : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
          (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 k)]) =
          some (.val (.word (hp + BitVec.ofNat 64 k))) := by
        simp [evalHOLExact, evalListHOLExact, hnd, valueIsWord, valueWord, wordOpHOL, wordOp]
      have he : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
          (.const (BitVec.ofNat 64 c)) = some (.val (.word (BitVec.ofNat 64 c))) := rfl
      rw [hd, he]
      simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom]
      rfl
    have step_store_var : ∀ (st : PanSemStateFiniteExact 64 F) (k : Nat) (nm : String) (w : BitVec 64),
        st.locals = s0.locals → st.memaddrs = s0.memaddrs → k < 56 → k % 8 = 0 →
        s0.locals.lookup (ofString nm) = some (.val (.word w)) →
        evaluateHOLFiniteState st
          (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 k)])
            (.var .local (ofString nm))) =
          (none, { st with memory := Wave8Contracts.M26.updW st.memory (hp + BitVec.ofNat 64 k) w }) := by
      intro st k nm w hloc hma hk hk8 hnm
      have hnd : st.locals.lookup (ofString "nd") = some (.val (.word hp)) := by rw [hloc]; exact hs0_nd
      have hnm' : st.locals.lookup (ofString nm) = some (.val (.word w)) := by rw [hloc]; exact hnm
      have hdom : st.memaddrs (hp + BitVec.ofNat 64 k) := by rw [hma]; exact hs0_dom k hk hk8
      rw [evaluateHOLFiniteState_store]
      have hd : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
          (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 k)]) =
          some (.val (.word (hp + BitVec.ofNat 64 k))) := by
        simp [evalHOLExact, evalListHOLExact, hnd, valueIsWord, valueWord, wordOpHOL, wordOp]
      have he : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
          (.var .local (ofString nm)) = some (.val (.word w)) := hnm'
      rw [hd, he]
      simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom]
      rfl
    set M7 :=
      Wave8Contracts.M26.updW
        (Wave8Contracts.M26.updW
          (Wave8Contracts.M26.updW
            (Wave8Contracts.M26.updW
              (Wave8Contracts.M26.updW
                (Wave8Contracts.M26.updW
                  (Wave8Contracts.M26.updW s.memory (hp + BitVec.ofNat 64 0) (BitVec.ofNat 64 2))
                  (hp + BitVec.ofNat 64 8) (BitVec.ofNat 64 0))
                (hp + BitVec.ofNat 64 16) (BitVec.ofNat 64 0))
              (hp + BitVec.ofNat 64 24) (BitVec.ofNat 64 0))
            (hp + BitVec.ofNat 64 32) wnib)
          (hp + BitVec.ofNat 64 40) wnlen)
        (hp + BitVec.ofNat 64 48) wchild
    have hs0_mem_eq : s0.memory = s.memory := by simp [s0, setVarHOLFinite]; rw [hapost_eq]; rfl
    have hcont_eval : evaluateHOLFiniteState s0
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 0)]) (.const (BitVec.ofNat 64 2)))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 8)]) (.const (BitVec.ofNat 64 0)))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 16)]) (.const (BitVec.ofNat 64 0)))
              (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 24)]) (.const (BitVec.ofNat 64 0)))
                (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 32)]) (.var .local (ofString "nib")))
                  (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 40)]) (.var .local (ofString "nlen")))
                    (.seq (.store (.op .add [.var .local (ofString "nd"), .const (BitVec.ofNat 64 48)]) (.var .local (ofString "child")))
                      (.return (.var .local (ofString "nd")))))))))) =
        (some (.returned (.val (.word hp))), emptyLocalsHOLFinite { s0 with memory := M7 }) := by
      rw [evaluateHOLFiniteState_seq_line780, step_store_const s0 0 2 rfl rfl (by decide) (by decide)]
      dsimp only
      set m1 := { s0 with memory := Wave8Contracts.M26.updW s0.memory (hp + BitVec.ofNat 64 0) (BitVec.ofNat 64 2) }
      rw [evaluateHOLFiniteState_seq_line780, step_store_const m1 8 0 rfl rfl (by decide) (by decide)]
      dsimp only
      set m2 := { m1 with memory := Wave8Contracts.M26.updW m1.memory (hp + BitVec.ofNat 64 8) (BitVec.ofNat 64 0) }
      rw [evaluateHOLFiniteState_seq_line780, step_store_const m2 16 0 rfl rfl (by decide) (by decide)]
      dsimp only
      set m3 := { m2 with memory := Wave8Contracts.M26.updW m2.memory (hp + BitVec.ofNat 64 16) (BitVec.ofNat 64 0) }
      rw [evaluateHOLFiniteState_seq_line780, step_store_const m3 24 0 rfl rfl (by decide) (by decide)]
      dsimp only
      set m4 := { m3 with memory := Wave8Contracts.M26.updW m3.memory (hp + BitVec.ofNat 64 24) (BitVec.ofNat 64 0) }
      rw [evaluateHOLFiniteState_seq_line780, step_store_var m4 32 "nib" wnib rfl rfl (by decide) (by decide) hs0_nib]
      dsimp only
      set m5 := { m4 with memory := Wave8Contracts.M26.updW m4.memory (hp + BitVec.ofNat 64 32) wnib }
      rw [evaluateHOLFiniteState_seq_line780, step_store_var m5 40 "nlen" wnlen rfl rfl (by decide) (by decide) hs0_nlen]
      dsimp only
      set m6 := { m5 with memory := Wave8Contracts.M26.updW m5.memory (hp + BitVec.ofNat 64 40) wnlen }
      rw [evaluateHOLFiniteState_seq_line780, step_store_var m6 48 "child" wchild rfl rfl (by decide) (by decide) hs0_child]
      dsimp only
      set m7 := { m6 with memory := Wave8Contracts.M26.updW m6.memory (hp + BitVec.ofNat 64 48) wchild }
      have hm7_eq : m7 = { s0 with memory := M7 } := by
        dsimp only [m7, m6, m5, m4, m3, m2, m1, M7]
        rw [hs0_mem_eq]
      rw [hm7_eq, evaluateHOLFiniteState_return]
      simp [evalHOLExact, hs0_nd, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    have hres_final : res = some (.returned (.val (.word hp))) := by
      change (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_new_ext)).1 = _
      rw [hbody, hr_eq, hcont_eval]
    have hpost_mem : post.memory = M7 := by
      change (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_new_ext)).2.memory = M7
      rw [hbody, hp_eq, hcont_eval]; rfl
    have hpost_glob : post.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) := by
      change (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_new_ext)).2.globals = _
      rw [hbody, hp_eq, hcont_eval]
      simp [emptyLocalsHOLFinite, s0, setVarHOLFinite]; rw [hapost_eq]; rfl
    have hpost_be : post.be = s.be :=
      (evaluateHOLFiniteState_metadata s (sourceFnBody Guest.Software.guestFn_node_new_ext)).2.2.1
    have hG_post : GuestInv post := guestInv_evaluate s _ hG
    have hpost_hp : globN post "heap_ptr" = q.toNat := by
      unfold globN; rw [hpost_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hpost_fp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
      unfold globN; rw [hpost_glob]
      simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
    have hpost_sp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
      unfold globN; rw [hpost_glob]
      simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
    have hA_post : ArenaOK post :=
      arenaOK_update_heap hpost_glob (by have := hA.1; omega) hq_hi hq_al hA
    have hAR_post : ArenaReady post := ⟨hG_post, hA_post⟩
    have hgrow : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [← hhp_eq, hpost_hp]; exact hp_le_q
    have hsp_le : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hpost_sp]
    have hmem_outside : ∀ a : BitVec 64,
        (a.toNat < hp.toNat ∨ hp.toNat + 56 ≤ a.toNat) → post.memory a = s.memory a := by
      intro a hout
      have hne : ∀ k : Nat, k < 56 → a ≠ hp + BitVec.ofNat 64 k := by
        intro k hk heq
        have := (hhp_add k (by omega)).2
        rw [heq] at hout
        omega
      rw [hpost_mem]
      dsimp only [M7]
      rw [updW_ne (hne 48 (by decide)),
          updW_ne (hne 40 (by decide)), updW_ne (hne 32 (by decide)),
          updW_ne (hne 24 (by decide)), updW_ne (hne 16 (by decide)),
          updW_ne (hne 8 (by decide)), updW_ne (hne 0 (by decide))]
    have hmem_lt : ∀ a : BitVec 64, a.toNat < globN s "heap_ptr" → post.memory a = s.memory a := by
      intro a hlt; rw [← hhp_eq] at hlt; exact hmem_outside a (Or.inl hlt)
    have hne_off : ∀ j k : Nat, j ≤ 48 → k ≤ 48 → j ≠ k → hp + BitVec.ofNat 64 j ≠ hp + BitVec.ofNat 64 k := by
      intro j k hj hk hjk heq
      have h1 := (hhp_add j (by omega)).2
      have h2 := (hhp_add k (by omega)).2
      rw [heq] at h1; omega
    have hmw_0 : memW post hp.toNat = 2 := by
      have ha0 : BitVec.ofNat 64 hp.toNat = hp + BitVec.ofNat 64 0 := by simp
      unfold memW; rw [ha0, hpost_mem]
      dsimp only [M7]
      rw [updW_ne (hne_off 0 48 (by decide) (by decide) (by decide)),
          updW_ne (hne_off 0 40 (by decide) (by decide) (by decide)),
          updW_ne (hne_off 0 32 (by decide) (by decide) (by decide)),
          updW_ne (hne_off 0 24 (by decide) (by decide) (by decide)),
          updW_ne (hne_off 0 16 (by decide) (by decide) (by decide)),
          updW_ne (hne_off 0 8 (by decide) (by decide) (by decide)),
          updW_eq]
      decide
    have hmw_16 : memW post (hp.toNat + 16) = 0 := by
      have ha : BitVec.ofNat 64 (hp.toNat + 16) = hp + BitVec.ofNat 64 16 := (hhp_add 16 (by decide)).1.symm
      unfold memW; rw [ha, hpost_mem]
      dsimp only [M7]
      rw [updW_ne (hne_off 16 48 (by decide) (by decide) (by decide)),
          updW_ne (hne_off 16 40 (by decide) (by decide) (by decide)),
          updW_ne (hne_off 16 32 (by decide) (by decide) (by decide)),
          updW_ne (hne_off 16 24 (by decide) (by decide) (by decide)),
          updW_eq]
      decide
    have hmw_32 : memW post (hp.toNat + 32) = locN s "nib" := by
      have ha : BitVec.ofNat 64 (hp.toNat + 32) = hp + BitVec.ofNat 64 32 := (hhp_add 32 (by decide)).1.symm
      unfold memW; rw [ha, hloc_nib s rfl, hpost_mem]
      dsimp only [M7]
      rw [updW_ne (hne_off 32 48 (by decide) (by decide) (by decide)),
          updW_ne (hne_off 32 40 (by decide) (by decide) (by decide)),
          updW_eq]
    have hmw_40 : memW post (hp.toNat + 40) = locN s "nlen" := by
      have ha : BitVec.ofNat 64 (hp.toNat + 40) = hp + BitVec.ofNat 64 40 := (hhp_add 40 (by decide)).1.symm
      unfold memW; rw [ha, hloc_nlen s rfl, hpost_mem]
      dsimp only [M7]
      rw [updW_ne (hne_off 40 48 (by decide) (by decide) (by decide)),
          updW_eq]
    have hmw_48 : memW post (hp.toNat + 48) = locN s "child" := by
      have ha : BitVec.ofNat 64 (hp.toNat + 48) = hp + BitVec.ofNat 64 48 := (hhp_add 48 (by decide)).1.symm
      unfold memW; rw [ha, hloc_child s rfl, hpost_mem]
      dsimp only [M7]
      rw [updW_eq]
    refine ⟨hAR_post, hgrow, hsp_le, ?_⟩
    intro Nd hNd hroots hKey
    have hchild_root : RootIn Nd (locN s "child") := hroots "child" (by simp)
    have hchild_cons : RootIn (hp.toNat :: Nd) (locN s "child") := by
      rcases hchild_root with h0 | hm
      · exact Or.inl h0
      · exact Or.inr (List.mem_cons_of_mem _ hm)
    have hnd_fresh : Inside (nodeIvl post hp.toNat) (globN s "heap_ptr") (globN post "heap_ptr") := by
      dsimp [nodeIvl, Inside]
      rw [hmw_0, show nodeSize 2 = 56 by decide, ← hhp_eq, hpost_hp]
      omega
    have hkinds_pre : ∀ n ∈ Nd, memW post n = memW s n := by
      intro n hn
      have hp_n := hNd.1 n hn
      have hn_in : Inside (nodeIvl s n) sourceBase (globN s "heap_ptr") := by
        rcases hp_n.2.1 with h1 | h2
        · exact h1
        · have := hp_n.2.2.1.2; have := hA.2.2.1; have := hA.2.2.2.1
          have hsep : heapLimit ≤ scratchStart := by decide
          obtain ⟨hsz, _, _⟩ := nodeSize_bounds (memW s n)
          dsimp [nodeIvl, Inside] at *; omega
      obtain ⟨hsz, _, _⟩ := nodeSize_bounds (memW s n)
      dsimp [nodeIvl, Inside] at hn_in
      have hlt64 : n < 2 ^ 64 := by omega
      unfold memW
      rw [hmem_lt (BitVec.ofNat 64 n) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]; omega)]
    have hKey_post := keyIn_unchanged_below_hp hAR hgrow hpost_be hmem_lt hkinds_pre hKey
    have hKey_cons : KeyIn post (hp.toNat :: Nd) (locN s "nib") (locN s "nlen") := by
      refine keyIn_cons_fresh hKey_post (fun hz => ?_)
      obtain ⟨_, hplen, _⟩ := keyIn_heap hAR hKey hz
      rw [← hhp_eq] at hplen
      exact Or.inr (Or.inr (Or.inl hplen))
    obtain ⟨hNd', hkinds⟩ := nodeHeap_cons_fresh hAR hAR_post hgrow hpost_be hmem_lt hNd hnd_fresh hhp_al
      (by rw [hmw_0]; decide)
      (by intro _; rw [hmw_48]; exact hchild_cons)
      (by rw [hmw_0]; intro h; cases h)
      (by intro _; rw [hmw_32, hmw_40]; exact hKey_cons)
      (by rw [hmw_16]; decide)
      (by rw [hmw_0]; intro h; cases h)
      (by rw [hmw_0]; intro h; cases h)
    refine ⟨hp.toNat :: Nd, hNd',
      fun n hn => List.mem_cons_of_mem _ hn, hkinds, ?_, ?_, ?_, ?_⟩
    · intro n hn
      rcases List.mem_cons.mp hn with rfl | hold
      · exact Or.inr hnd_fresh
      · exact Or.inl hold
    · apply frameOutside_of_mem_lt_hp hAR
      intro a ha_out
      apply hmem_outside a
      rcases ha_out with h1 | h2
      · rw [← hhp_eq] at h1; exact Or.inl h1
      · exact Or.inr (by omega)
    · intro k hk
      rw [hpost_glob]
      have hne : ofString "heap_ptr" ≠ k := by
        rintro rfl; exact hk (by simp)
      simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]
    · intro v hv
      rw [hres_final] at hv
      injection hv with hv1; injection hv1 with hv2
      subst hv2
      exact ⟨hp, rfl, Or.inr (List.mem_cons_self ..)⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards
