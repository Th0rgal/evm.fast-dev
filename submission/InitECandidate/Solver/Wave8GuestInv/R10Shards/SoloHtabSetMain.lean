import InitECandidate.Solver.Wave8GuestInv.R10Shards.SoloHtabSetLeafInt

/-! Proof of `htab_set_body_spec` and `htab_set_spec_proof` (`FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_set")`). -/

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

/-! ## 1. Entry Parameter Extraction and Postcondition Local-Insensitivity -/

theorem three_word_params_of_lookupCode {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fname p1 p2 p3 : MlS)
    (hne12 : p1 ≠ p2) (hne13 : p1 ≠ p3) (hne23 : p2 ≠ p3)
    (body : ProgHOL 64) (retShape : ShapeHOL)
    (hc : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one), (p3, .one)], body, retShape))
    (values : List (ValueHOL 64))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, s.locals, retShape)) :
    ∃ w1 w2 w3 : BitVec 64,
      s.locals.lookup p1 = some (.val (.word w1)) ∧
      s.locals.lookup p2 = some (.val (.word w2)) ∧
      s.locals.lookup p3 = some (.val (.word w3)) := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup fname values body s.locals retShape hl
  unfold lookupCodeHOLExact at hx
  rw [hc] at hx
  dsimp only at hx
  split at hx
  · rename_i hcond
    injection hx with hx_eq
    have hmap := congrArg (fun x => x.2.1) hx_eq
    rcases values with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩
    · simp at hcond
    · simp at hcond
    · simp at hcond
    · have hall := hcond.2.2
      simp only [List.zip, List.all, Bool.and_true, Bool.and_eq_true] at hall
      have h1w : ∃ w1, v1 = .val (.word w1) := by
        rcases v1 with ⟨⟨w1⟩⟩ | _ | _
        · exact ⟨w1, rfl⟩
        · simp [shapeOfHOLExact, shapeEqHOL] at hall
        · simp [shapeOfHOLExact, shapeEqHOL] at hall
      have h2w : ∃ w2, v2 = .val (.word w2) := by
        rcases v2 with ⟨⟨w2⟩⟩ | _ | _
        · exact ⟨w2, rfl⟩
        · simp [shapeOfHOLExact, shapeEqHOL] at hall
        · simp [shapeOfHOLExact, shapeEqHOL] at hall
      have h3w : ∃ w3, v3 = .val (.word w3) := by
        rcases v3 with ⟨⟨w3⟩⟩ | _ | _
        · exact ⟨w3, rfl⟩
        · simp [shapeOfHOLExact, shapeEqHOL] at hall
        · simp [shapeOfHOLExact, shapeEqHOL] at hall
      obtain ⟨w1, rfl⟩ := h1w
      obtain ⟨w2, rfl⟩ := h2w
      obtain ⟨w3, rfl⟩ := h3w
      refine ⟨w1, w2, w3, ?_, ?_, ?_⟩
      · have := congrFun hmap.symm p1
        simpa [List.map, List.zip, List.foldl, hne13, hne12] using this
      · have := congrFun hmap.symm p2
        simpa [List.map, List.zip, List.foldl, hne23] using this
      · have := congrFun hmap.symm p3
        simpa [List.map, List.zip, List.foldl] using this
    · simp at hcond
  · cases hx

theorem locFree_htabExitAt {F : Type} (s0 : PanSemStateFiniteExact 64 F) (t : Nat) :
    LocFreePost (fun _ post => HtabExitAt t s0 post) := by
  intro _ post L' h
  have hs0 : { s0 with locals := s0.locals, clock := s0.clock } = s0 := by cases s0; rfl
  have hp : { post with locals := post.locals, clock := post.clock } = post := by cases post; rfl
  have h1 := (htabExitAt_locals t s0 post s0.locals L' s0.clock post.clock).mp (by rw [hs0]; exact h)
  have h2 := (htabExitAt_locals t s0 post s0.locals post.locals s0.clock post.clock).mpr h1
  rw [hs0, hp] at h2
  exact h2

theorem storeW_mem {F : Type} {s u : PanSemStateFiniteExact 64 F}
    {ed ee : ExpHOL 64} (a w : BitVec 64)
    (hed : evalAt s ed = some (.val (.word a)))
    (hee : evalAt s ee = some (.val (.word w)))
    (hu : evaluateHOLFiniteState s (.store ed ee) = (none, u)) :
    s.memaddrs a ∧ u = { s with memory := updW s.memory a w } := by
  rw [evaluateHOLFiniteState_store] at hu
  unfold evalAt at hed hee
  rw [hed] at hu; dsimp only at hu
  rw [hee] at hu; dsimp only at hu
  rcases hm : @panMemStoresHOL 64 _ a (flattenHOL (.val (.word w))) s.memaddrs
    (fun addr => Classical.propDecidable (s.memaddrs addr)) s.memory with _ | m
  · rw [hm] at hu; simp at hu
  · rw [hm] at hu
    injection hu with _ hteq
    obtain ⟨hdom, rfl⟩ := stores_word _ hm
    exact ⟨hdom, hteq.symm⟩

/-! ## 2. Sub-proof A: Empty Table Insertion (`leaf == 0`) -/

theorem htab_set_branch_empty {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F)
    (tw keyw valw : BitVec 64)
    (hLF : LocFreePost (fun _ post => HtabExitAt tw.toNat s0 post))
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
      (fun _ post => HtabExitAt tw.toNat s0 post) := by
  set t := tw.toNat
  have hmem_s : s.memory = s0.memory := hs_fr.memory
  have hg_s : s.globals = s0.globals := by unfold LocFrame at hs_fr; rw [hs_fr]
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
  have hcnt_s : hdr s t 3 ≤ ([] : List Nat).length := by
    have : hdr s t 3 = 0 := by unfold hdr memW; rw [hmem_s]; exact hcnt0
    omega
  refine Ret.decCall_new_leaf_lf hLF tw keyw valw [] Fr0
    (by simp [evalAt, evalHOLExact, ht_s])
    (by simp [evalAt, evalHOLExact, hkey_s])
    (by simp [evalAt, evalHOLExact, hval_s])
    hA_s hNS_s hcnt_s hal_s ?_
  intro nlw Fr1 s1 hA1 hNS1 hh0_1 hh1_1 hh3_1 _ n0_1 _ n16_1 n24_1 ordc_1 _ _ hhp_1 hfp_1 hfr_1 hg_1 hloc_1
  change NodeState s1 t [nlw.toNat] Fr1 at hNS1
  have hh0_s : hdr s t 0 = hdr s0 t 0 := by unfold hdr memW; rw [hmem_s]
  have hh1_s : hdr s t 1 = hdr s0 t 1 := by unfold hdr memW; rw [hmem_s]
  have hh3_s : hdr s t 3 = 0 := by unfold hdr memW; rw [hmem_s]; exact hcnt0
  have hfp_s : htabFootprint s t = htabFootprint s0 t := by
    simp [htabFootprint, hdr, memW, hmem_s]
  have hgn_s : globN s "heap_ptr" = globN s0 "heap_ptr" := by unfold globN; rw [hg_s]
  obtain ⟨hB1, hnodup1, hmem1, hfc1⟩ := hNS1
  obtain ⟨hnc1_lt, _, _, _, ht_lo, ht_hi, _⟩ := htabBlocks_bounds hB1
  have hhe : heapEnd = 33806089704 := rfl
  -- Now execute `store(t + 56, nl); return 0` via `NS`!
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
  obtain ⟨hB_end, hfp_end⟩ := htabBlocks_updW_nonlayout (tw + 56#64) nlw hB1
    (hne_hdr 0 (by omega) (by omega)) (hne_hdr 1 (by omega) (by omega))
    (hne_hdr 4 (by omega) (by omega)) (hne_hdr 5 (by omega) (by omega))
    (hne_hdr 6 (by omega) (by omega)) (hne_hdr 10 (by omega) (by omega))
    (fun h8 => absurd h8 (hne_hdr 8 (by omega) (by omega)))
  have hsep1 := htabBlocks_cell_sep hB1
  have hh0_end : hdr s_end t 0 = hdr s0 t 0 :=
    (memW_updW_other s1 _ _ _ (hne_hdr 0 (by omega) (by omega))).trans (hh0_1.trans hh0_s)
  have hh1_end : hdr s_end t 1 = hdr s0 t 1 :=
    (memW_updW_other s1 _ _ _ (hne_hdr 1 (by omega) (by omega))).trans (hh1_1.trans hh1_s)
  have hh3_end : hdr s_end t 3 = 1 := by
    have h1 : hdr s_end t 3 = hdr s1 t 3 := memW_updW_other s1 _ _ _ (hne_hdr 3 (by omega) (by omega))
    have h2 : hdr s1 t 3 = hdr s t 3 + 1 := hh3_1
    omega
  have hh5_end : hdr s_end t 5 = hdr s1 t 5 := memW_updW_other s1 _ _ _ (hne_hdr 5 (by omega) (by omega))
  have hh6_end : hdr s_end t 6 = hdr s1 t 6 := memW_updW_other s1 _ _ _ (hne_hdr 6 (by omega) (by omega))
  have hh7_end : hdr s_end t 7 = nlw.toNat := by
    change memW { s1 with memory := updW s1.memory (tw + 56#64) nlw } (t + 8 * 7) = nlw.toNat
    unfold memW; rw [htw56_eq]; simp [updW]
  have hh8_end : hdr s_end t 8 = hdr s1 t 8 := memW_updW_other s1 _ _ _ (hne_hdr 8 (by omega) (by omega))
  have hh9_end : hdr s_end t 9 = hdr s1 t 9 := memW_updW_other s1 _ _ _ (hne_hdr 9 (by omega) (by omega))
  have hnd_end : ∀ x < hdr s1 t 10 + 1, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF s_end (hdr s1 t 5) x off = nodeF s1 (hdr s1 t 5) x off := by
    intro x hx off hoff
    unfold nodeF
    apply memW_updW_other s1
    rw [← htw56_eq]
    exact (hsep1.1 7 (by omega) x hx off hoff).symm
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
  have hfc_end : FreeChainF (nodeF s_end (hdr s_end t 5)) (hdr s_end t 9) Fr1 := by
    rw [hh5_end, hh9_end]
    refine FreeChainF.congr Fr1 _ ?_ hfc1
    intro f hf
    have hf_rng := (hmem1 f).mp (List.mem_append_right _ hf)
    have := hB1.2.2.2.2.2.2.2
    exact hnd_end f (by omega) 0 (Or.inl rfl)
  have hT_end : TreeWF [nlw.toNat] [] Fr1 (hdr s_end t 8) (hdr s_end t 0) (hdr s_end t 3)
      (hdr s_end t 7) (hdr s_end t 9) (nodeF s_end (hdr s_end t 5))
      (fun i => memW s_end (hdr s_end t 6 + 8 * i)) := by
    rw [hh3_end, hh7_end, hh0_end]
    apply TreeWF.insert_empty
    · simpa using hnodup1
    · intro x; rw [hh8_end]; simpa using hmem1 x
    · exact hfc_end
    · exact hord0_end
    · rw [hh5_end, hnd_end nlw.toNat hnl_lt_nc1 0 (Or.inl rfl)]; exact n0_1
    · rw [hh5_end, hnd_end nlw.toNat hnl_lt_nc1 16 (Or.inr (Or.inr (Or.inl rfl)))]
      exact n16_1.trans hh3_s
    · rw [hh5_end, hnd_end nlw.toNat hnl_lt_nc1 24 (Or.inr (Or.inr (Or.inr rfl)))]
      exact n24_1.trans (congrArg (8 * ·) hh0_s)
  have hW_end : HtabWF s_end t := (htabWF_iff s_end t).mpr ⟨hB_end, [nlw.toNat], [], Fr1, hT_end⟩
  have hfr_s0_s1 : FrameOutside s0 s1 (htabFootprint s0 t) (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
    intro x hxk hxf
    have hm1 := hfr_1 x (by rw [hfp_s]; exact hxk) (by rw [hgn_s]; exact hxf)
    rw [hm1, hmem_s]
  have htw56_hit : (∃ j ∈ htabFootprint s0 t, CellHits (tw + 56#64).toNat j) ∨
      CellHits (tw + 56#64).toNat (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") := by
    have htw56_nat : (tw + 56#64).toNat = t + 56 := by rw [BitVec.toNat_add, show (56#64).toNat = 56 from rfl]; omega
    exact Or.inl ⟨(t, 88), by simp [htabFootprint], by rw [htw56_nat]; exact ⟨by omega, by omega⟩⟩
  have hfr_end : FrameOutside s0 s_end (htabFootprint s0 t) (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") :=
    frameOutside_updW_mem s0 s1 s1.memory rfl (tw + 56#64) nlw _ _ hfr_s0_s1 htw56_hit s_end rfl
  refine ⟨⟨guestInv_congr (s := s1) rfl rfl rfl rfl hA1.1, hA1.2⟩,
    hW_end, hh0_end, hh1_end,
    by change globN s0 "heap_ptr" ≤ globN s1 "heap_ptr"; rw [← hgn_s]; exact hhp_1,
    ?_, hfr_end,
    fun k hk => by rw [← hg_s]; exact hg_1 k hk⟩
  · change ∀ iv ∈ htabFootprint { s1 with memory := updW s1.memory (tw + 56#64) nlw } t, Allocated s1 iv ∧ _
    rw [hfp_end]
    intro iv hiv
    obtain ⟨hal_iv, hprov⟩ := hfp_1 iv hiv
    rw [hfp_s, hgn_s] at hprov
    exact ⟨hal_iv, hprov⟩

/-! ## 3. Sub-proof B: Key Match Overwrite (`eq != 0`) -/

theorem htab_set_branch_overwrite {F : Type}
    (s0 s : PanSemStateFiniteExact 64 F)
    (tw leafw valw : BitVec 64)
    (hs_fr : LocFrame s0 s)
    (hA0 : ArenaReady s0)
    (hW0 : HtabWF s0 tw.toNat)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i)
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
      (fun _ post => HtabExitAt tw.toNat s0 post) := by
  set t := tw.toNat
  have hmem_s : s.memory = s0.memory := hs_fr.memory
  have hma_s : s.memaddrs = s0.memaddrs := by unfold LocFrame at hs_fr; rw [hs_fr]
  have hg_s : s.globals = s0.globals := by unfold LocFrame at hs_fr; rw [hs_fr]
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
  have hs_ns : s = NS s0 s.locals s0.globals s0.memory s.clock := by
    unfold LocFrame at hs_fr
    exact hs_fr
  rw [hs_ns]
  refine Ret.ns_storeW (ndw + leafw * 32#64 + 8#64) valw
    (by rw [← hs_ns]; exact hed)
    (by simp [evalAt, evalHOLExact, hval_s]) ?_
  intro _
  apply Ret.ns_ret; intro _ _
  -- State returned is `NS s0 HolFiniteMapExact.empty s0.globals (updW s0.memory addr valw) s.clock`!
  set addr := ndw + leafw * 32#64 + 8#64
  have haddr_eq : addr = BitVec.ofNat 64 (hdr s0 t 5 + 32 * leafw.toNat + 8) := by
    dsimp [addr]; rw [← hndw_nat]; exact (ofNat_node_addr ndw leafw 8).symm
  let s_end := NS s0 HolFiniteMapExact.empty s0.globals (updW s0.memory addr valw) s.clock
  have hsep0 := htabBlocks_cell_sep hB0
  have hne_hdr : ∀ k < 11, BitVec.ofNat 64 (t + 8 * k) ≠ addr := by
    intro k hk; rw [haddr_eq]; exact hsep0.1 k hk leafw.toNat hleaf_lt_nc0 8 (Or.inr (Or.inl rfl))
  obtain ⟨hB_end, hfp_end⟩ := htabBlocks_updW_nonlayout addr valw hB0
    (hne_hdr 0 (by omega)) (hne_hdr 1 (by omega))
    (hne_hdr 4 (by omega)) (hne_hdr 5 (by omega))
    (hne_hdr 6 (by omega)) (hne_hdr 10 (by omega))
    (fun h8 => absurd h8 (hne_hdr 8 (by omega)))
  have hh0_end : hdr s_end t 0 = hdr s0 t 0 := memW_updW_other s0 _ _ _ (hne_hdr 0 (by omega))
  have hh1_end : hdr s_end t 1 = hdr s0 t 1 := memW_updW_other s0 _ _ _ (hne_hdr 1 (by omega))
  have hh3_end : hdr s_end t 3 = hdr s0 t 3 := memW_updW_other s0 _ _ _ (hne_hdr 3 (by omega))
  have hh5_end : hdr s_end t 5 = hdr s0 t 5 := memW_updW_other s0 _ _ _ (hne_hdr 5 (by omega))
  have hh6_end : hdr s_end t 6 = hdr s0 t 6 := memW_updW_other s0 _ _ _ (hne_hdr 6 (by omega))
  have hh7_end : hdr s_end t 7 = hdr s0 t 7 := memW_updW_other s0 _ _ _ (hne_hdr 7 (by omega))
  have hh8_end : hdr s_end t 8 = hdr s0 t 8 := memW_updW_other s0 _ _ _ (hne_hdr 8 (by omega))
  have hh9_end : hdr s_end t 9 = hdr s0 t 9 := memW_updW_other s0 _ _ _ (hne_hdr 9 (by omega))
  have hnd_L0_I0 : (L0 ++ I0).Nodup := (List.nodup_append.mp hT0.2.1).1
  have hleaf_not_I0 : leafw.toNat ∉ I0 := fun hI =>
    (List.nodup_append.mp hnd_L0_I0).2.2 leafw.toNat hleaf_L0 leafw.toNat hI rfl
  have hT_end : TreeWF L0 I0 Fr0 (hdr s_end t 8) (hdr s_end t 0) (hdr s_end t 3)
      (hdr s_end t 7) (hdr s_end t 9) (nodeF s_end (hdr s_end t 5))
      (fun i => memW s_end (hdr s_end t 6 + 8 * i)) := by
    rw [hh8_end, hh0_end, hh3_end, hh7_end, hh9_end, hh5_end, hh6_end]
    apply TreeWF.overwrite_leaf_value hT0
    · intro x hx
      have hx_rng := (hT0.2.2.1 x).mp hx
      have := hB0.2.2.2.2.2.2.2
      unfold nodeF; apply memW_updW_other s0; rw [haddr_eq]
      exact hsep0.2.2.2.1 x (by omega) 0 (Or.inl rfl) leafw.toNat hleaf_lt_nc0 8 (Or.inr (Or.inl rfl)) (Or.inr (by omega))
    · intro x hx
      have hx_rng := (hT0.2.2.1 x).mp (List.mem_append_left _ hx)
      have := hB0.2.2.2.2.2.2.2
      unfold nodeF; apply memW_updW_other s0; rw [haddr_eq]
      exact hsep0.2.2.2.1 x (by omega) 16 (Or.inr (Or.inr (Or.inl rfl))) leafw.toNat hleaf_lt_nc0 8 (Or.inr (Or.inl rfl)) (Or.inr (by omega))
    · intro x hx
      have hx_rng := (hT0.2.2.1 x).mp (List.mem_append_left _ hx)
      have := hB0.2.2.2.2.2.2.2
      unfold nodeF; apply memW_updW_other s0; rw [haddr_eq]
      exact hsep0.2.2.2.1 x (by omega) 24 (Or.inr (Or.inr (Or.inr rfl))) leafw.toNat hleaf_lt_nc0 8 (Or.inr (Or.inl rfl)) (Or.inr (by omega))
    · intro x hxI
      have hx_ne : x ≠ leafw.toNat := fun h => hleaf_not_I0 (h ▸ hxI)
      have hx_rng := (hT0.2.2.1 x).mp (List.mem_append_left _ (List.mem_append_right _ hxI))
      have := hB0.2.2.2.2.2.2.2
      unfold nodeF; apply memW_updW_other s0; rw [haddr_eq]
      exact hsep0.2.2.2.1 x (by omega) 8 (Or.inr (Or.inl rfl)) leafw.toNat hleaf_lt_nc0 8 (Or.inr (Or.inl rfl)) (Or.inl hx_ne)
    · intro i hi
      have hLlen : L0.length ≤ hdr s0 t 10 := by
        have hle := nodup_len_le_range (List.nodup_append.mp hnd_L0_I0).1
          (fun x hx => (hT0.2.2.1 x).mp (List.mem_append_left _ (List.mem_append_left _ hx)))
        have := hB0.2.2.2.2.2.2.2
        omega
      apply memW_updW_other s0; rw [haddr_eq]
      exact hsep0.2.2.1 leafw.toNat hleaf_lt_nc0 8 (Or.inr (Or.inl rfl)) i (by omega)
  have hW_end : HtabWF s_end t := (htabWF_iff s_end t).mpr ⟨hB_end, L0, I0, Fr0, hT_end⟩
  have hhit_addr : (∃ j ∈ htabFootprint s0 t, CellHits addr.toNat j) ∨ CellHits addr.toNat (globN s0 "heap_ptr", 0) := by
    have hnd0_in := (hB0.1 (hdr s0 t 5, (hdr s0 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hnd0_in
    have ha_nat : addr.toNat = hdr s0 t 5 + 32 * leafw.toNat + 8 := by
      rw [haddr_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact Or.inl ⟨(hdr s0 t 5, (hdr s0 t 10 + 1) * 32), by simp [htabFootprint], by rw [ha_nat]; exact ⟨by omega, by omega⟩⟩
  have hfr_end : FrameOutside s0 s_end (htabFootprint s0 t) (globN s0 "heap_ptr", 0) :=
    frameOutside_updW_mem s0 s0 s0.memory rfl addr valw _ _ (fun _ _ _ => rfl) hhit_addr s_end rfl
  refine ⟨⟨guestInv_congr (s := s0) rfl rfl rfl rfl hA0.1, hA0.2⟩,
    hW_end, hh0_end, hh1_end, le_rfl,
    ?_,
    by change FrameOutside s0 s_end (htabFootprint s0 t) (globN s0 "heap_ptr", globN s0 "heap_ptr" - globN s0 "heap_ptr")
       rw [Nat.sub_self]; exact hfr_end,
    fun _ _ => rfl⟩
  · change ∀ iv ∈ htabFootprint { s0 with memory := updW s0.memory addr valw } t, Allocated s0 iv ∧ _
    rw [hfp_end]
    intro iv hiv
    exact ⟨hal0 iv hiv, Or.inl ⟨iv, hiv, le_rfl, le_rfl⟩⟩

/-! ## 4. Sub-proof C: Crit-Bit Splice Tail (after `htab_new_leaf` and `htab_new_internal`) -/

theorem Ret.ns_seq_storeW2 {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C}
    {d1 e1 d2 e2 : ExpHOL 64} {b : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (a1 w1 a2 w2 : BitVec 64)
    (hd1 : evalAt (NS s L G M C) d1 = some (.val (.word a1)))
    (he1 : evalAt (NS s L G M C) e1 = some (.val (.word w1)))
    (hd2 : evalAt (NS s L G (updW M a1 w1) C) d2 = some (.val (.word a2)))
    (he2 : evalAt (NS s L G (updW M a1 w1) C) e2 = some (.val (.word w2)))
    (hb : s.memaddrs a1 → s.memaddrs a2 → Ret (NS s L G (updW (updW M a1 w1) a2 w2) C) b Φ) :
    Ret (NS s L G M C) (.seq (.seq (.store d1 e1) (.store d2 e2)) b) Φ := by
  refine Ret.seq ?_ ?_
  · intro v hv
    rw [evaluateHOLFiniteState_seq_line780] at hv
    rcases hr1 : evaluateHOLFiniteState (NS s L G M C) (.store d1 e1) with ⟨r1, m1⟩
    rw [hr1] at hv
    cases r1 with
    | none =>
      have := (evaluate_store_control_frame m1 d2 e2).1
      rcases this with h | h <;> rw [h] at hv <;> simp at hv
    | some _ =>
      have := (evaluate_store_control_frame (NS s L G M C) d1 e1).1
      rw [hr1] at this
      rcases this with h | h <;> simp at h <;> subst h <;> simp at hv
  · intro t2 ht2
    obtain ⟨m1, hm1, hm2⟩ := (by
      rw [evaluateHOLFiniteState_seq_line780] at ht2
      rcases hr : evaluateHOLFiniteState (NS s L G M C) (.store d1 e1) with ⟨r1, m⟩
      rw [hr] at ht2
      cases r1 with
      | none => exact ⟨m, rfl, ht2⟩
      | some _ => simp at ht2 : ∃ m1, evaluateHOLFiniteState (NS s L G M C) (.store d1 e1) = (none, m1) ∧
          evaluateHOLFiniteState m1 (.store d2 e2) = (none, t2))
    obtain ⟨ha1, hm1_eq⟩ := storeW_mem a1 w1 hd1 he1 hm1
    have hd2' : evalAt m1 d2 = some (.val (.word a2)) := by rw [hm1_eq]; exact hd2
    have he2' : evalAt m1 e2 = some (.val (.word w2)) := by rw [hm1_eq]; exact he2
    obtain ⟨ha2, hm2_eq⟩ := storeW_mem a2 w2 hd2' he2' hm2
    have ha2' : s.memaddrs a2 := by rw [hm1_eq] at ha2; exact ha2
    have ht2_eq : t2 = NS s L G (updW (updW M a1 w1) a2 w2) C := by
      rw [hm2_eq, hm1_eq]; rfl
    rw [ht2_eq]
    exact hb ha1 ha2'

theorem eval_node_field_expr {F : Type} (st : PanSemStateFiniteExact 64 F)
    (x : MlS) (ndw xw : BitVec 64) (off : Nat)
    (hnd : st.locals.lookup (ofString "nodes") = some (.val (.word ndw)))
    (hx : st.locals.lookup x = some (.val (.word xw))) :
    evalAt st (.op .add [.var .local (ofString "nodes"),
      .panop .mul [.var .local x, .const 32#64],
      .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (ndw + xw * 32#64 + BitVec.ofNat 64 off))) := by
  simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hnd, hx,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
    valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
    Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
  have hz : BitVec.ofNat 64 off + (0 : BitVec 64) = BitVec.ofNat 64 off := BitVec.add_zero _
  rw [hz, BitVec.add_assoc]

theorem htab_set_splice_memory_wf {F : Type}
    (s0 s2 : PanSemStateFiniteExact 64 F)
    (tw dw pw nw nlw niw : BitVec 64)
    (L0 I0 Fr0 Fr2 : List Nat)
    (ch_left : Bool)
    (m_final : BitVec 64 → HolWordLab 64)
    (hm_final :
      let ndw := BitVec.ofNat 64 (hdr s2 tw.toNat 5)
      let m3 := updW (updW (updW s2.memory
                  (ndw + niw * 32#64 + 0#64) pw)
                  (ndw + nlw * 32#64 + 0#64) niw)
                  (ndw + nw * 32#64 + 0#64) niw
      let m5 := if ch_left then
                  updW (updW m3 (ndw + niw * 32#64 + 8#64) nlw) (ndw + niw * 32#64 + 16#64) nw
                else
                  updW (updW m3 (ndw + niw * 32#64 + 8#64) nw) (ndw + niw * 32#64 + 16#64) nlw
      m_final = if pw.toNat = 0 then
                  updW m5 (tw + 56#64) niw
                else if nodeF s0 (hdr s0 tw.toNat 5) pw.toNat 8 = nw.toNat then
                  updW m5 (ndw + pw * 32#64 + 8#64) niw
                else
                  updW m5 (ndw + pw * 32#64 + 16#64) niw)
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
    HtabExitAt tw.toNat s0 (NS s2 HolFiniteMapExact.empty s2.globals m_final s2.clock) := by
  set t := tw.toNat
  obtain ⟨hB2, hnodup2, hmem2, hfc2⟩ := hNS2
  obtain ⟨hnc2_lt, _, _, _, ht_lo, ht_hi, _⟩ := htabBlocks_bounds hB2
  have hnx2_le : hdr s2 t 8 ≤ hdr s2 t 10 + 1 := hB2.2.2.2.2.2.2.2
  have hhe : heapEnd = 33806089704 := rfl
  have hsep2 := htabBlocks_cell_sep hB2
  set ndw := BitVec.ofNat 64 (hdr s2 t 5)
  have hndw_nat : ndw.toNat = hdr s2 t 5 := by
    have hnd2_in := (hB2.1 (hdr s2 t 5, (hdr s2 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hnd2_in; rw [BitVec.toNat_ofNat]; omega
  have haddr_nd : ∀ (xw : BitVec 64) (off : Nat),
      ndw + xw * 32#64 + BitVec.ofNat 64 off = BitVec.ofNat 64 (hdr s2 t 5 + 32 * xw.toNat + off) := by
    intro xw off; rw [← hndw_nat]; exact (ofNat_node_addr ndw xw off).symm
  -- Distinctness & bounds of `niw`, `nlw`, `nw`, `pw` from `hnodup2` and `hmem2`:
  have hperm_new : List.Perm ((L0 ++ [nlw.toNat]) ++ (I0 ++ [niw.toNat]) ++ Fr2)
      ((((L0 ++ I0) ++ [nlw.toNat]) ++ [niw.toNat]) ++ Fr2) := by
    have p0 : List.Perm ([nlw.toNat] ++ I0) (I0 ++ [nlw.toNat]) := List.perm_append_comm
    have p1 : List.Perm (L0 ++ ([nlw.toNat] ++ I0)) (L0 ++ (I0 ++ [nlw.toNat])) := p0.append_left L0
    have p2 : List.Perm ((L0 ++ ([nlw.toNat] ++ I0)) ++ [niw.toNat]) ((L0 ++ (I0 ++ [nlw.toNat])) ++ [niw.toNat]) := p1.append_right [niw.toNat]
    have p3 := p2.append_right Fr2
    simpa only [List.append_assoc] using p3
  have hnodup_new : ((L0 ++ [nlw.toNat]) ++ (I0 ++ [niw.toNat]) ++ Fr2).Nodup :=
    hperm_new.nodup_iff.mpr hnodup2
  have hmem_new : ∀ x, x ∈ (L0 ++ [nlw.toNat]) ++ (I0 ++ [niw.toNat]) ++ Fr2 ↔ 1 ≤ x ∧ x < hdr s2 t 8 := by
    intro x; rw [hperm_new.mem_iff]; exact hmem2 x
  have hnd_all := (List.nodup_append.mp hnodup2).1
  have hnd_Anl := (List.nodup_append.mp hnd_all).1
  have hni_not_Anl : niw.toNat ∉ (L0 ++ I0) ++ [nlw.toNat] := fun h =>
    (List.nodup_append.mp hnd_all).2.2 niw.toNat h niw.toNat (by simp) rfl
  have hnl_not_LI : nlw.toNat ∉ L0 ++ I0 := fun h =>
    (List.nodup_append.mp hnd_Anl).2.2 nlw.toNat h nlw.toNat (by simp) rfl
  have hnl_ne_ni : nlw.toNat ≠ niw.toNat := fun h =>
    hni_not_Anl (List.mem_append_right _ (by simp [h]))
  have hnw_ne_nl : nw.toNat ≠ nlw.toNat := fun h => hnl_not_LI (h ▸ hnw_LI)
  have hnw_ne_ni : nw.toNat ≠ niw.toNat := fun h => hni_not_Anl (List.mem_append_left _ (h ▸ hnw_LI))
  have hnl_lt_nc2 : nlw.toNat < hdr s2 t 10 + 1 := by
    have := (hmem2 nlw.toNat).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp))))
    omega
  have hni_lt_nc2 : niw.toNat < hdr s2 t 10 + 1 := by
    have := (hmem2 niw.toNat).mp (List.mem_append_left _ (List.mem_append_right _ (by simp)))
    omega
  have hnw_lt_nc2 : nw.toNat < hdr s2 t 10 + 1 := by
    have := (hmem2 nw.toNat).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hnw_LI)))
    omega
  have hLI_lt_nc2 : ∀ z ∈ L0 ++ I0, z < hdr s2 t 10 + 1 := by
    intro z hz
    have := (hmem2 z).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hz)))
    omega
  set m3 := updW (updW (updW s2.memory
              (ndw + niw * 32#64 + 0#64) pw)
              (ndw + nlw * 32#64 + 0#64) niw)
              (ndw + nw * 32#64 + 0#64) niw
  set m5 := if ch_left then
              updW (updW m3 (ndw + niw * 32#64 + 8#64) nlw) (ndw + niw * 32#64 + 16#64) nw
            else
              updW (updW m3 (ndw + niw * 32#64 + 8#64) nw) (ndw + niw * 32#64 + 16#64) nlw
  have hm_eq : m_final = if pw.toNat = 0 then
                  updW m5 (tw + 56#64) niw
                else if nodeF s0 (hdr s0 t 5) pw.toNat 8 = nw.toNat then
                  updW m5 (ndw + pw * 32#64 + 8#64) niw
                else
                  updW m5 (ndw + pw * 32#64 + 16#64) niw := hm_final
  let s_end := NS s2 HolFiniteMapExact.empty s2.globals m_final s2.clock
  have htw56_eq : tw + 56#64 = BitVec.ofNat 64 (t + 8 * 7) := (ofNat_add_toNat tw 56).symm
  -- Helper: `m5` agrees with `s2.memory` on all header cells `t + 8 * k` (`k < 11`) and all order cells!
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
  have hh0_end : hdr s_end t 0 = hdr s0 t 0 := (hdr_end_other 0 (by omega) (by omega)).trans hh0_2
  have hh1_end : hdr s_end t 1 = hdr s0 t 1 := (hdr_end_other 1 (by omega) (by omega)).trans hh1_2
  have hh3_end : hdr s_end t 3 = hdr s0 t 3 + 1 := (hdr_end_other 3 (by omega) (by omega)).trans hh3_2
  have hh4_end : hdr s_end t 4 = hdr s2 t 4 := hdr_end_other 4 (by omega) (by omega)
  have hh5_end : hdr s_end t 5 = hdr s2 t 5 := hdr_end_other 5 (by omega) (by omega)
  have hh6_end : hdr s_end t 6 = hdr s2 t 6 := hdr_end_other 6 (by omega) (by omega)
  have hh8_end : hdr s_end t 8 = hdr s2 t 8 := hdr_end_other 8 (by omega) (by omega)
  have hh9_end : hdr s_end t 9 = hdr s2 t 9 := hdr_end_other 9 (by omega) (by omega)
  have hh10_end : hdr s_end t 10 = hdr s2 t 10 := hdr_end_other 10 (by omega) (by omega)
  have hh7_end : hdr s_end t 7 = if pw.toNat = 0 then niw.toNat else hdr s0 t 7 := by
    unfold hdr memW
    simp only [s_end, NS_memory, hm_eq]
    by_cases hpz : pw.toNat = 0
    · rw [← htw56_eq]; simp [hpz, updW]
    · simp only [hpz, ↓reduceIte]
      have hp_lt := hp_lt_nc2 hpz
      have hne8 : BitVec.ofNat 64 (t + 8 * 7) ≠ ndw + pw * 32#64 + 8#64 := by
        rw [haddr_nd]; exact hsep2.1 7 (by omega) pw.toNat hp_lt 8 (Or.inr (Or.inl rfl))
      have hne16 : BitVec.ofNat 64 (t + 8 * 7) ≠ ndw + pw * 32#64 + 16#64 := by
        rw [haddr_nd]; exact hsep2.1 7 (by omega) pw.toNat hp_lt 16 (Or.inr (Or.inr (Or.inl rfl)))
      split
      · simp only [updW, hne8, ↓reduceIte, hm5_hdr 7 (by omega)]; exact hh7_2
      · simp only [updW, hne16, ↓reduceIte, hm5_hdr 7 (by omega)]; exact hh7_2
  have hfp_end : htabFootprint s_end t = htabFootprint s2 t := by
    simp [htabFootprint, hdr_end_other 1 (by omega) (by omega), hh4_end, hh5_end, hh6_end, hh10_end]
  have hB_end : HtabBlocks s_end t := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro iv hiv; rw [hfp_end] at hiv; obtain ⟨hin, hwok⟩ := hB2.1 iv hiv
      exact ⟨hin, wordsOK_block s_end hA2.1.memaddrs iv.1 iv.2 hwok.1 hwok.2.1 hin.1 hin.2⟩
    · rw [hfp_end]; exact hB2.2.1
    · rw [hdr_end_other 0 (by omega) (by omega)]; exact hB2.2.2.1
    · rw [hdr_end_other 0 (by omega) (by omega)]; exact hB2.2.2.2.1
    · rw [hdr_end_other 1 (by omega) (by omega), hdr_end_other 0 (by omega) (by omega)]; exact hB2.2.2.2.2.1
    · rw [hh10_end]; exact hB2.2.2.2.2.2.1
    · rw [hh8_end]; exact hB2.2.2.2.2.2.2.1
    · rw [hh8_end, hh10_end]; exact hB2.2.2.2.2.2.2.2
  -- Order entries in `s_end` equal those in `s2`:
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
  -- Helper: any node field `(x, off)` with `off = 0` or `off = 24` (or `x ≠ pw.toNat`) is unaffected by the final `if pw = 0 ...` write!
  have hm_final_non_p_ch : ∀ x < hdr s2 t 10 + 1, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      (x ≠ pw.toNat ∨ off = 0 ∨ off = 24) →
      m_final (BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off)) = m5 (BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off)) := by
    intro x hx off hoff hcond
    rw [hm_eq]
    by_cases hpz : pw.toNat = 0
    · have hne7 : BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off) ≠ tw + 56#64 := by
        rw [htw56_eq]; exact (hsep2.1 7 (by omega) x hx off hoff).symm
      simp only [hpz, ↓reduceIte, updW, hne7]
    · simp only [hpz, ↓reduceIte]
      have hp_lt := hp_lt_nc2 hpz
      have hne8 : BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off) ≠ ndw + pw * 32#64 + 8#64 := by
        rw [haddr_nd]
        apply hsep2.2.2.2.1 x hx off hoff pw.toNat hp_lt 8 (Or.inr (Or.inl rfl))
        rcases hcond with hne | rfl | rfl
        · exact Or.inl hne
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
      have hne16 : BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off) ≠ ndw + pw * 32#64 + 16#64 := by
        rw [haddr_nd]
        apply hsep2.2.2.2.1 x hx off hoff pw.toNat hp_lt 16 (Or.inr (Or.inr (Or.inl rfl)))
        rcases hcond with hne | rfl | rfl
        · exact Or.inl hne
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
      split <;> simp only [updW, hne8, hne16, ↓reduceIte]
  -- Helper: any node field `(x, off)` with `off ≠ 0` and `(x ≠ niw.toNat ∨ off = 24)` has `m5` = `s2.memory`!
  have hm5_keep : ∀ x < hdr s2 t 10 + 1, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      (x ≠ niw.toNat → x ≠ nlw.toNat → x ≠ nw.toNat → m5 (BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off)) = s2.memory (BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off))) ∧
      ((off = 8 ∨ off = 16 ∨ off = 24) → x ≠ niw.toNat → m5 (BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off)) = s2.memory (BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off))) ∧
      (off = 24 → m5 (BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off)) = s2.memory (BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + off))) := by
    intro x hx off hoff
    refine ⟨?_, ?_, ?_⟩
    · intro hx_ni hx_nl hx_nw
      have h1 := hsep2.2.2.2.1 x hx off hoff niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inl hx_ni)
      have h2 := hsep2.2.2.2.1 x hx off hoff niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl)) (Or.inl hx_ni)
      have h3 := hsep2.2.2.2.1 x hx off hoff nw.toNat hnw_lt_nc2 0 (Or.inl rfl) (Or.inl hx_nw)
      have h4 := hsep2.2.2.2.1 x hx off hoff nlw.toNat hnl_lt_nc2 0 (Or.inl rfl) (Or.inl hx_nl)
      have h5 := hsep2.2.2.2.1 x hx off hoff niw.toNat hni_lt_nc2 0 (Or.inl rfl) (Or.inl hx_ni)
      rw [← haddr_nd] at h1 h2 h3 h4 h5
      cases ch_left <;> simp only [m5, m3, updW, Bool.false_eq_true, ↓reduceIte, h1, h2, h3, h4, h5]
    · intro hoff_nz hx_ni
      have h0 : off ≠ 0 := by rcases hoff_nz with rfl | rfl | rfl <;> omega
      have h1 := hsep2.2.2.2.1 x hx off hoff niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inl hx_ni)
      have h2 := hsep2.2.2.2.1 x hx off hoff niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl)) (Or.inl hx_ni)
      have h3 := hsep2.2.2.2.1 x hx off hoff nw.toNat hnw_lt_nc2 0 (Or.inl rfl) (Or.inr h0)
      have h4 := hsep2.2.2.2.1 x hx off hoff nlw.toNat hnl_lt_nc2 0 (Or.inl rfl) (Or.inr h0)
      have h5 := hsep2.2.2.2.1 x hx off hoff niw.toNat hni_lt_nc2 0 (Or.inl rfl) (Or.inl hx_ni)
      rw [← haddr_nd] at h1 h2 h3 h4 h5
      cases ch_left <;> simp only [m5, m3, updW, Bool.false_eq_true, ↓reduceIte, h1, h2, h3, h4, h5]
    · rintro rfl
      have h1 := hsep2.2.2.2.1 x hx 24 (Or.inr (Or.inr (Or.inr rfl))) niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (by omega))
      have h2 := hsep2.2.2.2.1 x hx 24 (Or.inr (Or.inr (Or.inr rfl))) niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl)) (Or.inr (by omega))
      have h3 := hsep2.2.2.2.1 x hx 24 (Or.inr (Or.inr (Or.inr rfl))) nw.toNat hnw_lt_nc2 0 (Or.inl rfl) (Or.inr (by omega))
      have h4 := hsep2.2.2.2.1 x hx 24 (Or.inr (Or.inr (Or.inr rfl))) nlw.toNat hnl_lt_nc2 0 (Or.inl rfl) (Or.inr (by omega))
      have h5 := hsep2.2.2.2.1 x hx 24 (Or.inr (Or.inr (Or.inr rfl))) niw.toNat hni_lt_nc2 0 (Or.inl rfl) (Or.inr (by omega))
      rw [← haddr_nd] at h1 h2 h3 h4 h5
      cases ch_left <;> simp only [m5, m3, updW, Bool.false_eq_true, ↓reduceIte, h1, h2, h3, h4, h5]
  -- Specific node field values in `s_end`:
  have hm5_at_0 : ∀ x < hdr s2 t 10 + 1,
      m5 (BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + 0)) = m3 (BitVec.ofNat 64 (hdr s2 t 5 + 32 * x + 0)) := by
    intro x hx
    have h1 := hsep2.2.2.2.1 x hx 0 (Or.inl rfl) niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (by omega))
    have h2 := hsep2.2.2.2.1 x hx 0 (Or.inl rfl) niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl)) (Or.inr (by omega))
    rw [← haddr_nd] at h1 h2
    cases ch_left <;> simp only [m5, updW, Bool.false_eq_true, ↓reduceIte, h1, h2]
  have hnl_0_end : nodeF s_end (hdr s2 t 5) nlw.toNat 0 = niw.toNat := by
    unfold nodeF memW
    simp only [s_end, NS_memory]
    rw [hm_final_non_p_ch nlw.toNat hnl_lt_nc2 0 (Or.inl rfl) (Or.inr (Or.inl rfl)),
      hm5_at_0 nlw.toNat hnl_lt_nc2]
    have hne_nw := hsep2.2.2.2.1 nlw.toNat hnl_lt_nc2 0 (Or.inl rfl) nw.toNat hnw_lt_nc2 0 (Or.inl rfl) (Or.inl hnw_ne_nl.symm)
    simp only [m3, updW, haddr_nd nw 0, haddr_nd nlw 0, hne_nw, ↓reduceIte]
  have hni_0_end : nodeF s_end (hdr s2 t 5) niw.toNat 0 = pw.toNat := by
    unfold nodeF memW
    simp only [s_end, NS_memory]
    rw [hm_final_non_p_ch niw.toNat hni_lt_nc2 0 (Or.inl rfl) (Or.inr (Or.inl rfl)),
      hm5_at_0 niw.toNat hni_lt_nc2]
    have hne_nw := hsep2.2.2.2.1 niw.toNat hni_lt_nc2 0 (Or.inl rfl) nw.toNat hnw_lt_nc2 0 (Or.inl rfl) (Or.inl hnw_ne_ni.symm)
    have hne_nl := hsep2.2.2.2.1 niw.toNat hni_lt_nc2 0 (Or.inl rfl) nlw.toNat hnl_lt_nc2 0 (Or.inl rfl) (Or.inl hnl_ne_ni.symm)
    simp only [m3, updW, haddr_nd nw 0, haddr_nd nlw 0, haddr_nd niw 0, hne_nw, hne_nl, ↓reduceIte]
  have hnw_0_end : nodeF s_end (hdr s2 t 5) nw.toNat 0 = niw.toNat := by
    unfold nodeF memW
    simp only [s_end, NS_memory]
    rw [hm_final_non_p_ch nw.toNat hnw_lt_nc2 0 (Or.inl rfl) (Or.inr (Or.inl rfl)),
      hm5_at_0 nw.toNat hnw_lt_nc2]
    simp only [m3, updW, haddr_nd nw 0, ↓reduceIte]
  have hnl_16_end : nodeF s_end (hdr s2 t 5) nlw.toNat 16 = hdr s0 t 3 := by
    have hnl_ne_pw : nlw.toNat ≠ pw.toNat := by
      intro h; rcases hpw_spec with ⟨hpz, _⟩ | ⟨hpI, _, _⟩
      · have := (hmem2 nlw.toNat).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))); omega
      · exact hnl_not_LI (h ▸ List.mem_append_right _ hpI)
    unfold nodeF memW
    simp only [s_end, NS_memory]
    rw [hm_final_non_p_ch nlw.toNat hnl_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inl hnl_ne_pw),
      (hm5_keep nlw.toNat hnl_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl)))).2.1 (Or.inr (Or.inl rfl)) hnl_ne_ni]
    exact hnl_16_2
  have hnl_24_end : nodeF s_end (hdr s2 t 5) nlw.toNat 24 = 8 * hdr s0 t 0 := by
    unfold nodeF memW
    simp only [s_end, NS_memory]
    rw [hm_final_non_p_ch nlw.toNat hnl_lt_nc2 24 (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr rfl)),
      (hm5_keep nlw.toNat hnl_lt_nc2 24 (Or.inr (Or.inr (Or.inr rfl)))).2.2 rfl]
    exact hnl_24_2
  have hni_24_end : nodeF s_end (hdr s2 t 5) niw.toNat 24 = dw.toNat := by
    unfold nodeF memW
    simp only [s_end, NS_memory]
    rw [hm_final_non_p_ch niw.toNat hni_lt_nc2 24 (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr rfl)),
      (hm5_keep niw.toNat hni_lt_nc2 24 (Or.inr (Or.inr (Or.inr rfl)))).2.2 rfl]
    exact hni_24_2
  have hni_ne_pw : niw.toNat ≠ pw.toNat := by
    intro h; rcases hpw_spec with ⟨hpz, _⟩ | ⟨hpI, _, _⟩
    · have := (hmem2 niw.toNat).mp (List.mem_append_left _ (List.mem_append_right _ (by simp))); omega
    · exact hni_not_Anl (List.mem_append_left _ (List.mem_append_right _ (h ▸ hpI)))
  have hni_ch_end : (nodeF s_end (hdr s2 t 5) niw.toNat 8 = nlw.toNat ∧ nodeF s_end (hdr s2 t 5) niw.toNat 16 = nw.toNat) ∨
      (nodeF s_end (hdr s2 t 5) niw.toNat 8 = nw.toNat ∧ nodeF s_end (hdr s2 t 5) niw.toNat 16 = nlw.toNat) := by
    have h8_m5 := hm_final_non_p_ch niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl)) (Or.inl hni_ne_pw)
    have h16_m5 := hm_final_non_p_ch niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inl hni_ne_pw)
    have hne8_16 := hsep2.2.2.2.1 niw.toNat hni_lt_nc2 8 (Or.inr (Or.inl rfl)) niw.toNat hni_lt_nc2 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (by omega))
    unfold nodeF memW
    simp only [s_end, NS_memory, h8_m5, h16_m5]
    cases hcl : ch_left
    · right
      have hm5_f : m5 = updW (updW m3 (ndw + niw * 32#64 + 8#64) nw) (ndw + niw * 32#64 + 16#64) nlw := by simp [m5, hcl]
      rw [hm5_f]
      simp [updW, haddr_nd niw 16, haddr_nd niw 8, hne8_16]
    · left
      have hm5_t : m5 = updW (updW m3 (ndw + niw * 32#64 + 8#64) nlw) (ndw + niw * 32#64 + 16#64) nw := by simp [m5, hcl]
      rw [hm5_t]
      simp [updW, haddr_nd niw 16, haddr_nd niw 8, hne8_16]
  -- FreeChain in `s_end`:
  have hfc_end : FreeChainF (nodeF s_end (hdr s2 t 5)) (hdr s2 t 9) Fr2 := by
    refine FreeChainF.congr Fr2 _ ?_ hfc2
    intro f hf
    have hf_lt : f < hdr s2 t 10 + 1 := by
      have := (hmem2 f).mp (List.mem_append_right _ hf); omega
    have hf_not_all : f ∉ (((L0 ++ I0) ++ [nlw.toNat]) ++ [niw.toNat]) := fun h =>
      (List.nodup_append.mp hnodup2).2.2 f h f hf rfl
    have hf_ni : f ≠ niw.toNat := fun h => hf_not_all (List.mem_append_right _ (by simp [h]))
    have hf_nl : f ≠ nlw.toNat := fun h => hf_not_all (List.mem_append_left _ (List.mem_append_right _ (by simp [h])))
    have hf_nw : f ≠ nw.toNat := fun h => hf_not_all (List.mem_append_left _ (List.mem_append_left _ (h ▸ hnw_LI)))
    unfold nodeF memW
    simp only [s_end, NS_memory]
    rw [hm_final_non_p_ch f hf_lt 0 (Or.inl rfl) (Or.inr (Or.inl rfl)),
      (hm5_keep f hf_lt 0 (Or.inl rfl)).1 hf_ni hf_nl hf_nw]
  -- Assemble `TreeWF.insert_splice`!
  have hT_end : TreeWF (L0 ++ [nlw.toNat]) (I0 ++ [niw.toNat]) Fr2
      (hdr s_end t 8) (hdr s_end t 0) (hdr s_end t 3) (hdr s_end t 7) (hdr s_end t 9)
      (nodeF s_end (hdr s_end t 5)) (fun i => memW s_end (hdr s_end t 6 + 8 * i)) := by
    rw [hh8_end, hh0_end, hh3_end, hh7_end, hh9_end, hh5_end, hh6_end]
    have hcnt_lt_nc2 : hdr s0 t 3 < hdr s2 t 10 + 1 := by
      have hlen_le := nodup_len_le_range hnd_all (fun x hx => (hmem2 x).mp (List.mem_append_left _ hx))
      have hLlen0 := hT0.1
      simp only [List.length_append, List.length_singleton] at hlen_le
      omega
    apply TreeWF.insert_splice (nd := nodeF s0 (hdr s0 t 5)) (ord := fun i => memW s0 (hdr s0 t 6 + 8 * i))
      hT0.1 hcnt_pos hnodup_new hmem_new hT0.2.2.2.1 hT0.2.2.2.2.1 hT0.2.2.2.2.2.1
      hT0.2.2.2.2.2.2.2.1 hT0.2.2.2.2.2.2.2.2.1 hT0.2.2.2.2.2.2.2.2.2.1 hT0.2.2.2.2.2.2.2.2.2.2.1
      hfc_end hd_lt hnw_LI hpw_spec
    · intro i hi
      rw [hT0.1] at hi
      exact (hord_end i (by omega)).trans (hord_old_2 i hi)
    · exact (hord_end (hdr s0 t 3) hcnt_lt_nc2).trans hord_cnt_2
    · exact hnl_0_end
    · exact hnl_16_end
    · exact hnl_24_end
    · exact hni_0_end
    · exact hni_24_end
    · exact hni_ch_end
    · exact hnw_0_end
    · intro x hxLI hx_nw
      have hx_lt := hLI_lt_nc2 x hxLI
      have hx_ni : x ≠ niw.toNat := fun h => hni_not_Anl (List.mem_append_left _ (h ▸ hxLI))
      have hx_nl : x ≠ nlw.toNat := fun h => hnl_not_LI (h ▸ hxLI)
      have h1 : nodeF s_end (hdr s2 t 5) x 0 = nodeF s2 (hdr s2 t 5) x 0 := by
        unfold nodeF memW; simp only [s_end, NS_memory]
        rw [hm_final_non_p_ch x hx_lt 0 (Or.inl rfl) (Or.inr (Or.inl rfl)),
          (hm5_keep x hx_lt 0 (Or.inl rfl)).1 hx_ni hx_nl hx_nw]
      exact h1.trans (hnd_old_2 x hxLI 0 (Or.inl rfl))
    · intro x hxLI
      have hx_lt := hLI_lt_nc2 x hxLI
      have h1 : nodeF s_end (hdr s2 t 5) x 24 = nodeF s2 (hdr s2 t 5) x 24 := by
        unfold nodeF memW; simp only [s_end, NS_memory]
        rw [hm_final_non_p_ch x hx_lt 24 (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr rfl)),
          (hm5_keep x hx_lt 24 (Or.inr (Or.inr (Or.inr rfl)))).2.2 rfl]
      exact h1.trans (hnd_old_2 x hxLI 24 (Or.inr (Or.inr (Or.inr rfl))))
    · intro x hxL
      have hxLI : x ∈ L0 ++ I0 := List.mem_append_left _ hxL
      have hx_lt := hLI_lt_nc2 x hxLI
      have hx_ni : x ≠ niw.toNat := fun h => hni_not_Anl (List.mem_append_left _ (h ▸ hxLI))
      have hx_pw : x ≠ pw.toNat := by
        intro h; rcases hpw_spec with ⟨hpz, _⟩ | ⟨hpI, _, _⟩
        · have := (hT0.2.2.1 x).mp (List.mem_append_left _ hxLI); omega
        · have hndLI0 := (List.nodup_append.mp hT0.2.1).1
          exact (List.nodup_append.mp hndLI0).2.2 x hxL x (h ▸ hpI) rfl
      have h1 : nodeF s_end (hdr s2 t 5) x 16 = nodeF s2 (hdr s2 t 5) x 16 := by
        unfold nodeF memW; simp only [s_end, NS_memory]
        rw [hm_final_non_p_ch x hx_lt 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inl hx_pw),
          (hm5_keep x hx_lt 16 (Or.inr (Or.inr (Or.inl rfl)))).2.1 (Or.inr (Or.inl rfl)) hx_ni]
      exact h1.trans (hnd_old_2 x hxLI 16 (Or.inr (Or.inr (Or.inl rfl))))
    · intro x hxI hx_pw
      have hxLI : x ∈ L0 ++ I0 := List.mem_append_right _ hxI
      have hx_lt := hLI_lt_nc2 x hxLI
      have hx_ni : x ≠ niw.toNat := fun h => hni_not_Anl (List.mem_append_left _ (h ▸ hxLI))
      have h8 : nodeF s_end (hdr s2 t 5) x 8 = nodeF s2 (hdr s2 t 5) x 8 := by
        unfold nodeF memW; simp only [s_end, NS_memory]
        rw [hm_final_non_p_ch x hx_lt 8 (Or.inr (Or.inl rfl)) (Or.inl hx_pw),
          (hm5_keep x hx_lt 8 (Or.inr (Or.inl rfl))).2.1 (Or.inl rfl) hx_ni]
      have h16 : nodeF s_end (hdr s2 t 5) x 16 = nodeF s2 (hdr s2 t 5) x 16 := by
        unfold nodeF memW; simp only [s_end, NS_memory]
        rw [hm_final_non_p_ch x hx_lt 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inl hx_pw),
          (hm5_keep x hx_lt 16 (Or.inr (Or.inr (Or.inl rfl)))).2.1 (Or.inr (Or.inl rfl)) hx_ni]
      exact ⟨h8.trans (hnd_old_2 x hxLI 8 (Or.inr (Or.inl rfl))),
             h16.trans (hnd_old_2 x hxLI 16 (Or.inr (Or.inr (Or.inl rfl))))⟩
    · intro hpz
      have hpI : pw.toNat ∈ I0 := by
        rcases hpw_spec with ⟨h0, _⟩ | ⟨hI, _, _⟩
        · exact absurd h0 hpz
        · exact hI
      have hpLI : pw.toNat ∈ L0 ++ I0 := List.mem_append_right _ hpI
      have hp_lt := hp_lt_nc2 hpz
      have hp_ni : pw.toNat ≠ niw.toNat := hni_ne_pw.symm
      have hne8_16 := hsep2.2.2.2.1 pw.toNat hp_lt 8 (Or.inr (Or.inl rfl)) pw.toNat hp_lt 16 (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (by omega))
      have hm5_p8 := (hm5_keep pw.toNat hp_lt 8 (Or.inr (Or.inl rfl))).2.1 (Or.inl rfl) hp_ni
      have hm5_p16 := (hm5_keep pw.toNat hp_lt 16 (Or.inr (Or.inr (Or.inl rfl)))).2.1 (Or.inr (Or.inl rfl)) hp_ni
      constructor
      · intro hp8_eq
        refine ⟨?_, ?_⟩
        · unfold nodeF memW; simp only [s_end, NS_memory, hm_eq, hpz, hp8_eq, ↓reduceIte, updW, haddr_nd pw 8]
        · have h1 : nodeF s_end (hdr s2 t 5) pw.toNat 16 = nodeF s2 (hdr s2 t 5) pw.toNat 16 := by
            unfold nodeF memW
            simp only [s_end, NS_memory, hm_eq, hpz, hp8_eq, ↓reduceIte, updW, haddr_nd pw 8, hne8_16.symm, hm5_p16]
          exact h1.trans (hnd_old_2 pw.toNat hpLI 16 (Or.inr (Or.inr (Or.inl rfl))))
      · intro hp8_ne
        refine ⟨?_, ?_⟩
        · have h1 : nodeF s_end (hdr s2 t 5) pw.toNat 8 = nodeF s2 (hdr s2 t 5) pw.toNat 8 := by
            unfold nodeF memW
            simp only [s_end, NS_memory, hm_eq, hpz, hp8_ne, ↓reduceIte, updW, haddr_nd pw 16, hne8_16, hm5_p8]
          exact h1.trans (hnd_old_2 pw.toNat hpLI 8 (Or.inr (Or.inl rfl)))
        · unfold nodeF memW; simp only [s_end, NS_memory, hm_eq, hpz, hp8_ne, ↓reduceIte, updW, haddr_nd pw 16]
  have hW_end : HtabWF s_end t := (htabWF_iff s_end t).mpr ⟨hB_end, L0 ++ [nlw.toNat], I0 ++ [niw.toNat], Fr2, hT_end⟩
  -- Finally, `FrameOutside s0 s_end (htabFootprint s0 t) (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr")`!
  have hit_nd2 : ∀ (xw : BitVec 64) (off : Nat),
      xw.toNat < hdr s2 t 10 + 1 → (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      (∃ j ∈ htabFootprint s0 t, CellHits (ndw + xw * 32#64 + BitVec.ofNat 64 off).toNat j) ∨
        CellHits (ndw + xw * 32#64 + BitVec.ofNat 64 off).toNat (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr") := by
    intro xw off hxw hoff
    have hnd2_in := (hB2.1 (hdr s2 t 5, (hdr s2 t 10 + 1) * 32) (by simp [htabFootprint])).1
    unfold Inside at hnd2_in
    have hhit_blk : CellHits (ndw + xw * 32#64 + BitVec.ofNat 64 off).toNat (hdr s2 t 5, (hdr s2 t 10 + 1) * 32) := by
      rw [haddr_nd xw off, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rcases hoff with rfl | rfl | rfl | rfl <;> omega)]
      unfold CellHits
      rcases hoff with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    rcases (hfp_2 (hdr s2 t 5, (hdr s2 t 10 + 1) * 32) (by simp [htabFootprint])).2 with ⟨j, hj, hij⟩ | hfr
    · exact Or.inl ⟨j, hj, cellHits_of_inside hhit_blk hij⟩
    · exact Or.inr (cellHits_of_inside hhit_blk hfr)
  have hit_t56 : (∃ j ∈ htabFootprint s0 t, CellHits (tw + 56#64).toNat j) ∨
      CellHits (tw + 56#64).toNat (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr") := by
    have htw56_nat : (tw + 56#64).toNat = t + 56 := by rw [BitVec.toNat_add, show (56#64).toNat = 56 from rfl]; omega
    exact Or.inl ⟨(t, 88), by simp [htabFootprint], by rw [htw56_nat]; exact ⟨by omega, by omega⟩⟩
  have hfr_m3 : FrameOutside s0 (NS s2 HolFiniteMapExact.empty s2.globals m3 s2.clock)
      (htabFootprint s0 t) (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr") := by
    have f1 := frameOutside_updW_mem s0 s2 s2.memory rfl _ pw _ _ hfr_2 (hit_nd2 niw 0 hni_lt_nc2 (Or.inl rfl))
      (NS s2 HolFiniteMapExact.empty s2.globals (updW s2.memory (ndw + niw * 32#64 + 0#64) pw) s2.clock) rfl
    have f2 := frameOutside_updW_mem s0 _ _ rfl _ niw _ _ f1 (hit_nd2 nlw 0 hnl_lt_nc2 (Or.inl rfl))
      (NS s2 HolFiniteMapExact.empty s2.globals (updW (updW s2.memory (ndw + niw * 32#64 + 0#64) pw) (ndw + nlw * 32#64 + 0#64) niw) s2.clock) rfl
    exact frameOutside_updW_mem s0 _ _ rfl _ niw _ _ f2 (hit_nd2 nw 0 hnw_lt_nc2 (Or.inl rfl))
      (NS s2 HolFiniteMapExact.empty s2.globals m3 s2.clock) rfl
  have hfr_m5 : FrameOutside s0 (NS s2 HolFiniteMapExact.empty s2.globals m5 s2.clock)
      (htabFootprint s0 t) (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr") := by
    cases hcl : ch_left
    · have hm5_f : m5 = updW (updW m3 (ndw + niw * 32#64 + 8#64) nw) (ndw + niw * 32#64 + 16#64) nlw := by simp [m5, hcl]
      have f4 := frameOutside_updW_mem s0 _ _ rfl _ nw _ _ hfr_m3 (hit_nd2 niw 8 hni_lt_nc2 (Or.inr (Or.inl rfl)))
        (NS s2 HolFiniteMapExact.empty s2.globals (updW m3 (ndw + niw * 32#64 + 8#64) nw) s2.clock) rfl
      exact frameOutside_updW_mem s0 _ _ rfl _ nlw _ _ f4 (hit_nd2 niw 16 hni_lt_nc2 (Or.inr (Or.inr (Or.inl rfl))))
        (NS s2 HolFiniteMapExact.empty s2.globals m5 s2.clock) hm5_f
    · have hm5_t : m5 = updW (updW m3 (ndw + niw * 32#64 + 8#64) nlw) (ndw + niw * 32#64 + 16#64) nw := by simp [m5, hcl]
      have f4 := frameOutside_updW_mem s0 _ _ rfl _ nlw _ _ hfr_m3 (hit_nd2 niw 8 hni_lt_nc2 (Or.inr (Or.inl rfl)))
        (NS s2 HolFiniteMapExact.empty s2.globals (updW m3 (ndw + niw * 32#64 + 8#64) nlw) s2.clock) rfl
      exact frameOutside_updW_mem s0 _ _ rfl _ nw _ _ f4 (hit_nd2 niw 16 hni_lt_nc2 (Or.inr (Or.inr (Or.inl rfl))))
        (NS s2 HolFiniteMapExact.empty s2.globals m5 s2.clock) hm5_t
  have hfr_end : FrameOutside s0 s_end (htabFootprint s0 t) (globN s0 "heap_ptr", globN s2 "heap_ptr" - globN s0 "heap_ptr") := by
    by_cases hpz : pw.toNat = 0
    · have hm_p0 : s_end.memory = updW m5 (tw + 56#64) niw := by simp [s_end, hm_eq, hpz]
      exact frameOutside_updW_mem s0 _ _ rfl _ niw _ _ hfr_m5 hit_t56 s_end hm_p0
    · have hp_lt := hp_lt_nc2 hpz
      by_cases hp8 : nodeF s0 (hdr s0 t 5) pw.toNat 8 = nw.toNat
      · have hm_p8 : s_end.memory = updW m5 (ndw + pw * 32#64 + 8#64) niw := by simp [s_end, hm_eq, hpz, hp8]
        exact frameOutside_updW_mem s0 _ _ rfl _ niw _ _ hfr_m5 (hit_nd2 pw 8 hp_lt (Or.inr (Or.inl rfl))) s_end hm_p8
      · have hm_p16 : s_end.memory = updW m5 (ndw + pw * 32#64 + 16#64) niw := by simp [s_end, hm_eq, hpz, hp8]
        exact frameOutside_updW_mem s0 _ _ rfl _ niw _ _ hfr_m5 (hit_nd2 pw 16 hp_lt (Or.inr (Or.inr (Or.inl rfl)))) s_end hm_p16
  refine ⟨⟨guestInv_congr (s := s2) rfl rfl rfl rfl hA2.1, hA2.2⟩,
    hW_end, hh0_end, hh1_end, hhp_2,
    ?_, hfr_end, hg_2⟩
  · change ∀ iv ∈ htabFootprint s_end t, Allocated s2 iv ∧ _
    rw [hfp_end]; exact hfp_2

end InitECandidate.Solver.Wave8GuestInv.SoloHtabSet
