import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.Common

/-! Return-typing contract `rt_lst_new` for micro-shard `m26` (`wave8/contracts-m26`),
checked against frozen revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

`lst_new` (AST line 13804, index 408): returns a fresh empty list (`LstOK`): header and backing
array fresh and disjoint.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8Contracts.M26

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

private theorem lookup_lst_new :
    originalRuntimeCode.lookup (ofString "lst_new") =
      some ([(ofString "esz", .one), (ofString "cap", .one)],
        sourceFnBody Guest.Software.guestFn_lst_new, .one) :=
  lookup_of_guestAst_getElem 408 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_lst_new) rfl

private theorem eval_panop_mul_words {F : Type}
    (s : PanSemStateFiniteExact 64 F) (e1 e2 : ExpHOL 64)
    (hret_or_some : ∃ vals, evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [.panop .mul [e1, e2]] = some vals) :
    ∃ w1 w2 : BitVec 64,
      ev s e1 = some (.val (.word w1)) ∧
      ev s e2 = some (.val (.word w2)) ∧
      ev s (.panop .mul [e1, e2]) = some (.val (.word (w1 * w2))) := by
  obtain ⟨vals, hvals⟩ := hret_or_some
  rw [evalListHOLFinite_eq_toExact] at hvals
  simp only [evalListHOLExact] at hvals
  rcases hev : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) (.panop .mul [e1, e2]) with _ | mv
  · rw [hev] at hvals; cases hvals
  · simp only [evalHOLExact, evalListHOLExact] at hev
    rcases he1 : @evalHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
    · rw [he1] at hev; cases hev
    · rcases he2 : @evalHOLExact 64 F _ s.toExact
          (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
      · rw [he1, he2] at hev; cases hev
      · rw [he1, he2] at hev
        rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _
        · refine ⟨w1, w2, he1, he2, ?_⟩
          simp [ev, evalHOLExact, evalListHOLExact, he1, he2, valueIsWord, valueWord, panOpHOL]
        all_goals (simp [List.all, valueIsWord] at hev)

private theorem decCall_arg_some {F : Type} (s : PanSemStateFiniteExact 64 F)
    (x fname : MlS) (arg : ExpHOL 64) (cont : ProgHOL 64) (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (.decCall x .one fname [arg] cont)).1 = some (.returned v)) :
    ∃ vals, evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [arg] =
      some vals := by
  rw [evaluateHOLFiniteState_decCall_total] at hret
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [arg] with
    _ | vals
  · rw [ha] at hret; simp at hret
  · exact ⟨vals, rfl⟩

/-- `lst_new` (AST line 13804): returns a fresh empty list (`LstOK`): header and backing array
fresh and disjoint. -/
theorem rt_lst_new :
    Returns ArenaReady (fun s post l =>
      locN s "esz" * locN s "cap" < 2 ^ 64 → 1 ≤ locN s "cap" →
        FreshBlock s post l 24 ∧ FreshBlock s post (memW post l) (locN s "esz" * locN s "cap") ∧
        Disj (l, 24) (memW post l, locN s "esz" * locN s "cap") ∧
        memW post (l + 8) = 0 ∧ memW post (l + 16) = locN s "cap")
    (ofString "lst_new") := by
  refine ⟨_, _, _, lookup_lst_new, ?_⟩
  intro F s hcode hAR _ _hnt v hret
  obtain ⟨hG, hA⟩ := hAR
  obtain ⟨hp, fp, sp, hhp, hhp_eq, hfp, hfp_eq, hsp, hsp_eq⟩ := arenaOK_globals s hA
  have hbody : sourceFnBody Guest.Software.guestFn_lst_new =
      .decCall (ofString "l") .one (ofString "alloc") [.const 24]
        (.decCall (ofString "p") .one (ofString "alloc")
          [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")]]
          (.seq (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "p")))
            (.seq (.store (.op .add [.var .local (ofString "l"), .const 8]) (.const 0))
              (.seq (.store (.op .add [.var .local (ofString "l"), .const 16]) (.var .local (ofString "cap")))
                (.return (.var .local (ofString "l"))))))) := rfl
  have hrun : Ret s (sourceFnBody Guest.Software.guestFn_lst_new)
      (fun rv post => ∃ w : BitVec 64, rv = .val (.word w) ∧
        ArenaReady post ∧ AllocatorGrows s post ∧
        (locN s "esz" * locN s "cap" < 2 ^ 64 → 1 ≤ locN s "cap" →
          FreshBlock s post w.toNat 24 ∧
          FreshBlock s post (memW post w.toNat) (locN s "esz" * locN s "cap") ∧
          Disj (w.toNat, 24) (memW post w.toNat, locN s "esz" * locN s "cap") ∧
          memW post (w.toNat + 8) = 0 ∧ memW post (w.toNat + 16) = locN s "cap")) := by
    rw [hbody]
    apply Ret.of_NS
    refine Ret.ns_alloc hcode 24 rfl hp hhp ?_
    intro hcmp1_1 hcmp2_1
    set q1 : BitVec 64 := (hp + (24 + 7)) &&& ((0 : BitVec 64) - 8)
    set L1 := s.locals.update (ofString "l", .val (.word hp))
    set G1 := s.globals.update (ofString "heap_ptr", .val (.word q1))
    show Ret (NS s L1 G1 s.memory (s.clock - 1)) _ _
    intro v1 hv1
    obtain ⟨w_esz, w_cap, hesz1, hcap1, hmul1⟩ :=
      eval_panop_mul_words (NS s L1 G1 s.memory (s.clock - 1))
        (.var .local (ofString "esz")) (.var .local (ofString "cap"))
        (decCall_arg_some _ _ _ _ _ v1 hv1)
    have hesz_s : s.locals.lookup (ofString "esz") = some (.val (.word w_esz)) := by
      simp [ev, evalHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "l" ≠ ofString "esz" by decide] at hesz1
      exact hesz1
    have hcap_s : s.locals.lookup (ofString "cap") = some (.val (.word w_cap)) := by
      simp [ev, evalHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "l" ≠ ofString "cap" by decide] at hcap1
      exact hcap1
    have hq1_g : G1.lookup (ofString "heap_ptr") = some (.val (.word q1)) := by
      simp [G1, HolFiniteMapExact.lookup_update, FUPDATE]
    refine (Ret.ns_alloc (s := s) (L := L1) (G := G1) (M := s.memory) (C := s.clock - 1)
      (Φ := fun rv t =>
        let post := { t with locals := HolFiniteMapExact.resVarEq t.locals (ofString "l", s.locals.lookup (ofString "l")) }
        ∃ w : BitVec 64, rv = .val (.word w) ∧
          ArenaReady post ∧ AllocatorGrows s post ∧
          (locN s "esz" * locN s "cap" < 2 ^ 64 → 1 ≤ locN s "cap" →
            FreshBlock s post w.toNat 24 ∧
            FreshBlock s post (memW post w.toNat) (locN s "esz" * locN s "cap") ∧
            Disj (w.toNat, 24) (memW post w.toNat, locN s "esz" * locN s "cap") ∧
            memW post (w.toNat + 8) = 0 ∧ memW post (w.toNat + 16) = locN s "cap"))
      hcode (w_esz * w_cap) hmul1 q1 hq1_g ?_) v1 hv1
    intro hcmp1_2 hcmp2_2
    set q2 : BitVec 64 := (q1 + (w_esz * w_cap + 7)) &&& ((0 : BitVec 64) - 8)
    set L2 := L1.update (ofString "p", .val (.word q1))
    set G2 := G1.update (ofString "heap_ptr", .val (.word q2))
    show Ret (NS s L2 G2 s.memory (s.clock - 1 - 1)) _ _
    have hev_l0 : ev (NS s L2 G2 s.memory (s.clock - 1 - 1))
        (.op .add [.var .local (ofString "l"), .const 0]) = some (.val (.word (hp + 0))) := by
      simp [ev, evalHOLExact, evalListHOLExact, L2, L1, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "l" by decide, valueIsWord, valueWord, wordOpHOL, wordOp]
    have hev_p : ev (NS s L2 G2 s.memory (s.clock - 1 - 1))
        (.var .local (ofString "p")) = some (.val (.word q1)) := by
      simp [ev, evalHOLExact, L2, HolFiniteMapExact.lookup_update, FUPDATE]
    refine Ret.ns_storeW (hp + 0) q1 hev_l0 hev_p ?_
    intro _hdom0
    set M1 := updW s.memory (hp + 0) q1
    have hev_l8 : ev (NS s L2 G2 M1 (s.clock - 1 - 1))
        (.op .add [.var .local (ofString "l"), .const 8]) = some (.val (.word (hp + 8))) := by
      simp [ev, evalHOLExact, evalListHOLExact, L2, L1, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "l" by decide, valueIsWord, valueWord, wordOpHOL, wordOp]
    refine Ret.ns_storeW (hp + 8) 0 hev_l8 rfl ?_
    intro _hdom8
    set M2 := updW M1 (hp + 8) 0
    have hev_l16 : ev (NS s L2 G2 M2 (s.clock - 1 - 1))
        (.op .add [.var .local (ofString "l"), .const 16]) = some (.val (.word (hp + 16))) := by
      simp [ev, evalHOLExact, evalListHOLExact, L2, L1, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "l" by decide, valueIsWord, valueWord, wordOpHOL, wordOp]
    have hev_cap : ev (NS s L2 G2 M2 (s.clock - 1 - 1))
        (.var .local (ofString "cap")) = some (.val (.word w_cap)) := by
      simp [ev, evalHOLExact, L2, L1, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "cap" by decide,
        show ofString "l" ≠ ofString "cap" by decide, hcap_s]
    refine Ret.ns_storeW (hp + 16) w_cap hev_l16 hev_cap ?_
    intro _hdom16
    set M3 := updW M2 (hp + 16) w_cap
    refine Ret.ns_ret ?_
    intro val hval
    have hval_eq : val = .val (.word hp) := by
      simp [ev, evalHOLExact, L2, L1, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "l" by decide] at hval
      exact hval.symm
    subst hval_eq
    dsimp only
    refine ⟨hp, rfl, ?_⟩
    set post : PanSemStateFiniteExact 64 F :=
      { locals := HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq
            (emptyLocalsHOLFinite (NS s L2 G2 M3 (s.clock - 1 - 1))).locals
            (ofString "p", L1.lookup (ofString "p")))
          (ofString "l", s.locals.lookup (ofString "l")),
        globals := G2,
        structs := s.structs,
        code := s.code,
        eshapes := s.eshapes,
        memory := M3,
        memaddrs := s.memaddrs,
        shMemaddrs := s.shMemaddrs,
        clock := s.clock - 1 - 1,
        be := s.be,
        ffi := s.ffi,
        baseAddr := s.baseAddr,
        topAddr := s.topAddr }
    change ArenaReady post ∧ AllocatorGrows s post ∧
      (locN s "esz" * locN s "cap" < 2 ^ 64 → 1 ≤ locN s "cap" →
        FreshBlock s post hp.toNat 24 ∧
        FreshBlock s post (memW post hp.toNat) (locN s "esz" * locN s "cap") ∧
        Disj (hp.toNat, 24) (memW post hp.toNat, locN s "esz" * locN s "cap") ∧
        memW post (hp.toNat + 8) = 0 ∧ memW post (hp.toNat + 16) = locN s "cap")
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hA.2.1
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
    obtain ⟨hq1_eq, hq1_hi, hq1_al, hp_le_q1⟩ := alloc_arith hp 24 hhp_hi hhp_al hcmp1_1 hcmp2_1
    change q1.toNat = _ at hq1_eq
    change q1.toNat ≤ heapLimit at hq1_hi
    change q1.toNat % 8 = 0 at hq1_al
    change hp.toNat ≤ q1.toNat at hp_le_q1
    have h24 : ((24 : BitVec 64).toNat + 7) / 8 * 8 = 24 := by decide
    rw [h24] at hq1_eq
    obtain ⟨hq2_eq, hq2_hi, hq2_al, hq1_le_q2⟩ :=
      alloc_arith q1 (w_esz * w_cap) hq1_hi hq1_al hcmp1_2 hcmp2_2
    change q2.toNat = _ at hq2_eq
    change q2.toNat ≤ heapLimit at hq2_hi
    change q2.toNat % 8 = 0 at hq2_al
    change q1.toNat ≤ q2.toNat at hq1_le_q2
    have hpost_hp : globN post "heap_ptr" = q2.toNat := by
      simp [post, G2, globN, HolFiniteMapExact.lookup_update, FUPDATE]
    have hpost_fp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
      simp [post, G2, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
    have hpost_sp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
      simp [post, G2, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
    have hG_post : GuestInv post := ⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩
    have hsb_le : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hA.1
    have hA_post : ArenaOK post := by
      unfold ArenaOK
      rw [hpost_hp, hpost_fp, hpost_sp]
      refine ⟨by omega, hq2_hi, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hq2_al, hA.2.2.2.2.2.2.1,
        hA.2.2.2.2.2.2.2.1,
        globalsWord_update (s := { s with globals := G1 }) (t := post) (ofString "heap_ptr") q2 rfl
          (globalsWord_update (s := s) (t := { s with globals := G1 }) (ofString "heap_ptr") q1 rfl
            hA.2.2.2.2.2.2.2.2)⟩
    have hAG : AllocatorGrows s post := by
      refine ⟨?_, by rw [hpost_sp]⟩
      rw [hpost_hp, ← hhp_eq]
      omega
    have hlim_le_he : heapLimit ≤ heapEnd := by decide
    have hloc_esz : locN s "esz" = w_esz.toNat := by simp [locN, hesz_s]
    have hloc_cap : locN s "cap" = w_cap.toNat := by simp [locN, hcap_s]
    -- Read back the three stored words at `hp + 0`, `hp + 8`, `hp + 16`:
    have hp0_ne_8 : hp + 0 ≠ hp + 8 := by
      intro h
      have h1 := congrArg BitVec.toNat h
      simp [BitVec.toNat_add] at h1
      omega
    have hp0_ne_16 : hp + 0 ≠ hp + 16 := by
      intro h
      have h1 := congrArg BitVec.toNat h
      simp [BitVec.toNat_add] at h1
      omega
    have hp_eq_0 : BitVec.ofNat 64 hp.toNat = hp + 0 := by
      simp [BitVec.ofNat_toNat]
    have hp8_ne_16 : hp + 8 ≠ hp + 16 := by
      intro h
      have h1 := congrArg BitVec.toNat h
      simp [BitVec.toNat_add] at h1
      omega
    have hp8_eq : BitVec.ofNat 64 (hp.toNat + 8) = hp + 8 := ofNat_add_toNat_eq hp 8
    have hp16_eq : BitVec.ofNat 64 (hp.toNat + 16) = hp + 16 := ofNat_add_toNat_eq hp 16
    have hmem0 : memW post hp.toNat = q1.toNat := by
      unfold memW
      change (match M3 (BitVec.ofNat 64 hp.toNat) with | .word w => w.toNat) = q1.toNat
      rw [show M3 (BitVec.ofNat 64 hp.toNat) = .word q1 by
        rw [hp_eq_0]; simp only [M3, M2, M1, updW, hp0_ne_16, hp0_ne_8, ↓reduceIte]]
    have hmem8 : memW post (hp.toNat + 8) = 0 := by
      unfold memW
      change (match M3 (BitVec.ofNat 64 (hp.toNat + 8)) with | .word w => w.toNat) = 0
      rw [show M3 (BitVec.ofNat 64 (hp.toNat + 8)) = .word 0 by
        rw [hp8_eq]; simp only [M3, M2, updW, hp8_ne_16, ↓reduceIte]]
      rfl
    have hmem16 : memW post (hp.toNat + 16) = w_cap.toNat := by
      unfold memW
      change (match M3 (BitVec.ofNat 64 (hp.toNat + 16)) with | .word w => w.toNat) = w_cap.toNat
      rw [show M3 (BitVec.ofNat 64 (hp.toNat + 16)) = .word w_cap by
        rw [hp16_eq]; simp only [M3, updW, ↓reduceIte]]
    refine ⟨⟨hG_post, hA_post⟩, hAG, ?_⟩
    intro hmul_lt _hcap_ge
    rw [hloc_esz, hloc_cap] at hmul_lt ⊢
    rw [hmem0]
    have hmul_toNat : (w_esz * w_cap).toNat = w_esz.toNat * w_cap.toNat := by
      rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hmul_lt]
    rw [hmul_toNat] at hq2_eq
    have hFB_hdr : FreshBlock s post hp.toNat 24 := by
      refine ⟨hhp_al, ?_, ?_⟩
      · change Inside (hp.toNat, 24) (globN s "heap_ptr") (globN post "heap_ptr")
        rw [← hhp_eq, hpost_hp]
        exact ⟨le_rfl, by omega⟩
      · change WordsOK post (hp.toNat, 24)
        exact wordsOK_of_guestInv post hG_post hp.toNat 24 hhp_al (by decide) hsb_le (by omega)
    have hFB_arr : FreshBlock s post q1.toNat (w_esz.toNat * w_cap.toNat) := by
      refine ⟨hq1_al, ?_, ?_⟩
      · rw [← hhp_eq, hpost_hp]
        exact ⟨hp_le_q1, le_of_eq hq2_eq.symm⟩
      · exact wordsOK_of_guestInv post hG_post q1.toNat
          ((w_esz.toNat * w_cap.toNat + 7) / 8 * 8) hq1_al (by omega) (by omega) (by omega)
    have hDisj : Disj (hp.toNat, 24) (q1.toNat, w_esz.toNat * w_cap.toNat) :=
      Or.inr (Or.inr (Or.inl (le_of_eq hq1_eq.symm)))
    exact ⟨hFB_hdr, hFB_arr, hDisj, hmem8, hmem16⟩
  exact hrun v hret

end InitECandidate.Solver.Wave8Contracts.M26
