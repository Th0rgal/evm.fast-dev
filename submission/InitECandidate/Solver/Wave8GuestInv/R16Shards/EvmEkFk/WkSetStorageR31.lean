import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.WkSetStorageJsetR31

/-!
# R31 `set_storage` World-Preserving Closure (`wkSc_set_storage`)

Proves `wkSc_set_storage : WorldKeepsSc WorldOK (bufRegions wsAcctBufs)
  ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra (ofString "set_storage")`
by composing:
1. `wkSc_get_account_optional` + `if a == 1 then raise StateErr 3 else skip`
2. `outer := load(ts + 32)` + `m := htab_get(outer, addr)`
3. Miss branch (`m.0 == 0`): `inner := htab_new(32, 8); jset(outer, addr, inner)` via
   `merge_new_call_worldStep`, `merge_new_call_bound_owned`, `jset_ts32_fresh_inner_step_r31`,
   and `worldStepSc_trans_owned_r31`
4. Hit branch (`m.0 != 0`): `inner := m.1` with `(inner, "ts.inner") ∈ worldRoleSlots`
5. `v := alloc(32); store(v, value)` preserving `worldRoleSlots`, followed by
   `jset(inner, key, v)` (`jset_tsInner_step_r31`) and `return 0`.
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

theorem lookup_set_storage :
    originalRuntimeCode.lookup (ofString "set_storage") =
      some ([(ofString "addr", .one), (ofString "key", .one),
             (ofString "value", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_set_storage, .one) :=
  lookup_of_guestAst_getElem 388 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_set_storage) rfl

private theorem worldEff_preserves_wrs_r31 {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hW0 : WorldOK s)
    (heff : WorldEff s post [] [] ["heap_ptr"]) :
    worldRoleSlots post = worldRoleSlots s := by
  obtain ⟨hAs, S, hWT⟩ := hW0
  obtain ⟨Nd, hWTN⟩ := (worldTyped_iff_with s S).1 hWT
  obtain ⟨hT, hJ, hF, _⟩ := hWTN
  have hcore : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := fun g hg => by
    have hne : ofString g ∉ (["heap_ptr"] : List String).map ofString := by revert g hg; decide
    exact globN_eq_of_lookup (heff.gw_kept (ofString g) hne)
  have hfr_pos : ∀ a : BitVec 64, post.memory a ≠ s.memory a →
      (∃ j ∈ ([freeGap s] : List Ivl), CellHitsPos a.toNat j) ∨ CellHitsPos a.toNat (heapFree s) := by
    intro a hne
    rcases heff.cell_frame a hne with ⟨_, h, _⟩ | ⟨_, h, _⟩ | hfg | hhf
    · cases h
    · cases h
    · exact Or.inl ⟨freeGap s, List.mem_singleton.2 rfl, hfg⟩
    · exact Or.inr hhf
  have hu_aligned : ∀ i : Ivl, Allocated s i → i.1 % 8 = 0 → i.2 % 8 = 0 → IvlUnhit s post i := by
    intro i hal hi1 hi2
    refine ivlUnhit_of_cellHitsPos hi1 hi2 hfr_pos (fun j hj => ?_) (disj_allocated_heapFree hAs.2 hal)
    simp only [List.mem_singleton] at hj
    subst hj
    exact disj_allocated_freeGap hAs.2 hal
  have hu_fix : ∀ i ∈ fixedObjects s, i.2 ≠ 0 → IvlUnhit s post i := by
    intro i hfi hpos
    rcases hF.1 i hfi with h0 | ⟨hal, hw⟩
    · exact absurd h0 hpos
    · exact hu_aligned i hal hw.1 hw.2.1
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i := by
    intro t ht i hi
    exact hu_aligned i ((hT.2.1 t ht).2 i hi).1 ((hT.2.1 t ht).1.1 i hi).2.1 ((hT.2.1 t ht).1.1 i hi).2.2.1
  have hu_ws : globN s "ws" ≠ 0 → IvlUnhit s post (globN s "ws", 40) := fun hnz =>
    hu_fix _ (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by simp [typedRecords])) (by simp)
  have hu_bs : globN s "bs" ≠ 0 → IvlUnhit s post (globN s "bs", 80) := fun hnz =>
    hu_fix _ (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by simp [typedRecords])) (by simp)
  have hu_ts : globN s "ts" ≠ 0 → IvlUnhit s post (globN s "ts", 72) := fun hnz =>
    hu_fix _ (by simpa [hnz] using typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by simp [typedRecords])) (by simp)
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → IvlUnhit s post i := fun i hi hpos =>
    hu_fix i (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)) hpos
  have hlow : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 :=
    ⟨mem_low_eq_of_domain_writes heff.out_dom hAs.1 (by rw [sourceBase_val]; omega),
     mem_low_eq_of_domain_writes heff.out_dom hAs.1 (by rw [sourceBase_val]; omega)⟩
  exact R10Shards.P26_P28.worldRoleSlots_eq_of_unhit hAs.2 hT hF hcore hu_tab hu_ws hu_bs hu_ts hu_bal hlow

private theorem flattenHOL_shape_u256_r31 {v : ValueHOL 64}
    (hsh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v) = true) :
    (flattenHOL v).length = 4 := by
  rcases v with _ | fs | _
  · simp [shapeOfHOLExact, shapeEqHOL] at hsh
  · rcases fs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩⟩ <;>
      try (simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh)
    rcases v0 with ⟨⟨a⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨b⟩⟩ | _ | _ <;>
      rcases v2 with ⟨⟨c⟩⟩ | _ | _ <;> rcases v3 with ⟨⟨d⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
    simp [flattenHOL]
  · simp [shapeOfHOLExact, shapeEqHOL] at hsh

private def setStorageAllocTail : ProgHOL 64 :=
  .decCall (ofString "v") .one (ofString "alloc") [.const 32#64]
    (.seq
      (.store (.var .local (ofString "v")) (.var .local (ofString "value")))
      (.seq
        (.call (some (none, none)) (ofString "jset")
          [.var .local (ofString "inner"), .var .local (ofString "key"), .var .local (ofString "v")])
        (.return (.const 0#64))))

private theorem setStorage_allocTail_step_r31 {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (kw iw : BitVec 64) (vval : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hs_key : s.locals.lookup (ofString "key") = some (.val (.word kw)))
    (hs_inner : s.locals.lookup (ofString "inner") = some (.val (.word iw)))
    (hs_val : s.locals.lookup (ofString "value") = some vval)
    (hsh_val : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vval) = true)
    (hiw_wrs : (iw.toNat, "ts.inner") ∈ worldRoleSlots s)
    (hnt : (evaluateHOLFiniteState s setStorageAllocTail).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s setStorageAllocTail).1) :
    WorldStepSc (bufRegions wsAcctBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
      s (evaluateHOLFiniteState s setStorageAllocTail).1
      (evaluateHOLFiniteState s setStorageAllocTail).2 := by
  have hB := validBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_jn_sp
  dsimp only [setStorageAllocTail] at hnt hfr ⊢
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 32#64] = some [.val (.word 32#64)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  rw [hargs] at hnt hfr ⊢; dsimp only at hnt hfr ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") [.val (.word 32#64)] with _ | ⟨balloc, calloc, ralloc⟩
  · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hl] at hnt hfr ⊢
    by_cases hcz : s.clock = 0
    · simp [hcz] at hnt
    rw [if_neg hcz] at hnt hfr ⊢
    have hlk_alloc_explicit : originalRuntimeCode.lookup (ofString "alloc") =
        some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
      lookup_alloc_r16
    have hballoc := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "alloc") _ _ balloc
      _ ralloc _ calloc (by rw [hc]; exact hlk_alloc_explicit) hl
    subst hballoc
    have hralloc := lookupCodeHOLFinite_installed_return s (ofString "alloc") _ _ _
      _ ralloc _ calloc (by rw [hc]; exact hlk_alloc_explicit) hl
    subst hralloc
    obtain ⟨nw, hnw_eq, hnw_callee⟩ := lookupCode_one_word hlk_alloc_explicit (by rwa [← hc])
    have hnw32 : nw = 32#64 := by injection hnw_eq with h1 _; injection h1 with h1; injection h1 with h1; exact h1.symm
    subst hnw32
    obtain ⟨pw, hpw_lk⟩ : ∃ pw : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) :=
      globalWord_of_globN_pos s "heap_ptr" (by have := hW.1.2.1; rw [sourceBase_val] at this; omega)
    let ent_a := callEntryStateHOLFinite s calloc
    rcases hrun_a : evaluateHOLFiniteState (callEntryStateHOLFinite s calloc) (sourceFnBody Guest.Software.guestFn_alloc) with ⟨res_a, pa⟩
    simp only [hrun_a] at hnt hfr ⊢
    cases res_a with
    | none => exact absurd hfr not_flowingOrResumes_error
    | some cr_a =>
      cases cr_a with
      | timeOut => simp at hnt
      | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
      | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
      | exception eid ev =>
        dsimp only at hfr ⊢
        have hres_ex : Resumes (some (.exception eid ev)) := by
          rcases hfr with h | h | h | hr <;> try simp at h
          exact hr
        have hal := InitECandidate.Solver.Wave8GuestInv.R13.alloc_body_resumes ent_a pw hc hpw_lk
          (by dsimp only [ent_a]; rw [hrun_a]; exact hres_ex)
        dsimp only [ent_a] at hal; rw [hrun_a] at hal
        obtain ⟨_, _, hrv_eq, _⟩ := hal
        cases hrv_eq
      | returned rv_a =>
        have hal := InitECandidate.Solver.Wave8GuestInv.R13.alloc_body_resumes ent_a pw hc hpw_lk
          (by dsimp only [ent_a]; rw [hrun_a]; exact Or.inl ⟨rv_a, rfl⟩)
        dsimp only [ent_a] at hal; rw [hrun_a] at hal
        obtain ⟨nw', hnw'_lk, hrv_eq, hcmp1, hcmp2, hpa_eq⟩ := hal
        have hnw_eq' : (32#64 : BitVec 64) = nw' := by
          have : ent_a.locals.lookup (ofString "n") = some (.val (.word 32#64)) := hnw_callee
          rw [this] at hnw'_lk; injection hnw'_lk with h'; injection h' with h'; injection h'
        subst hnw_eq'
        dsimp only at hrv_eq hpa_eq
        injection hrv_eq with hrv_eq'; injection hrv_eq' with hrv_eq'; subst hrv_eq'
        dsimp only at hnt hfr ⊢
        have hsh_pw : (shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh_pw] at hnt hfr ⊢
        dsimp only at hnt hfr ⊢
        set s1 := setVarHOLFinite (ofString "v") (.val (.word pw)) { pa with locals := s.locals }
        have hs1_next : s1 = { s with
            globals := s.globals.update (ofString "heap_ptr", .val (.word ((pw + (32#64 + 7)) &&& ((0 : BitVec 64) - 8)))),
            locals := s1.locals, clock := s1.clock } := by
          dsimp only [s1, setVarHOLFinite]; rw [hpa_eq]; rfl
        have heff0 : WorldEff s s [] [] ["heap_ptr"] := WorldEff.refl s [] [] ["heap_ptr"] hW.1 hc
        obtain ⟨heff1, _, _, _, hp_lo_s, hp_add, hp_hi, _⟩ :=
          R16Shards.worldEff_alloc_step heff0 (by simp) hpw_lk hcmp1 hcmp2 hs1_next
        have hs1_v : s1.locals.lookup (ofString "v") = some (.val (.word pw)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs1_key : s1.locals.lookup (ofString "key") = some (.val (.word kw)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs_key,
            show ofString "v" ≠ ofString "key" by decide]
        have hs1_inner : s1.locals.lookup (ofString "inner") = some (.val (.word iw)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs_inner,
            show ofString "v" ≠ ofString "inner" by decide]
        have hs1_val : s1.locals.lookup (ofString "value") = some vval := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs_val,
            show ofString "v" ≠ ofString "value" by decide]
        rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
        have hpw_hi : pw.toNat + 32 ≤ heapLimit := by
          change pw.toNat + (32 + 7) / 8 * 8 = globN s1 "heap_ptr" at hp_add; omega
        have hhe_ge_hl : heapLimit ≤ heapEnd := by rw [heapLimit_val, heapEnd_val]; decide
        have heff2 : WorldEff s
            (evaluateHOLFiniteState s1 (.store (.var .local (ofString "v")) (.var .local (ofString "value")))).2
            [] [] ["heap_ptr"] :=
          worldEff_store_multi heff1 _ _ 4 (by decide)
            (fun v hv => by
              simp [evalHOLExact, toExact, hs1_val] at hv
              subst hv
              exact flattenHOL_shape_u256_r31 hsh_val)
            (fun x hx => by
              simp [evalHOLExact, toExact, hs1_v] at hx
              subst hx
              exact ⟨by omega, Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))⟩)
        have hst_loc : (evaluateHOLFiniteState s1
            (.store (.var .local (ofString "v")) (.var .local (ofString "value")))).2.locals = s1.locals := by
          rw [evaluateHOLFiniteState_store]
          split <;> [(split <;> [(split <;> simp); simp]); simp]
        rcases hst : evaluateHOLFiniteState s1
            (.store (.var .local (ofString "v")) (.var .local (ofString "value"))) with ⟨rst, s2⟩
        simp only [hst] at heff2 hst_loc hnt hfr ⊢
        have hstep02 : WorldStepSc (bufRegions wsAcctBufs) ["heap_ptr", "journal_n", "scratch_ptr"]
            stdKeep NoExtra s rst s2 := by
          have hws0 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra s rst s2 :=
            heff2.to_worldStep_Q hW (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
          exact WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp) ⟨hws0, heff2.sp_hi⟩
        cases rst with
        | some cr_st =>
          exact hstep02.with_locals_clock _ _
        | none =>
          dsimp only at hnt hfr ⊢
          have hWs2 : WorldOK s2 := hstep02.worldOK_bufs hB hW
          have hs2_wrs : (iw.toNat, "ts.inner") ∈ worldRoleSlots s2 := by
            rwa [worldEff_preserves_wrs_r31 hW heff2]
          have hs2_inner : evalAt s2 (.var .local (ofString "inner")) = some (.val (.word iw)) := by
            simp [evalAt, evalHOLExact, toExact, hst_loc, hs1_inner]
          rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
          have hmeta_j := (PanRunBounded.evaluateHOLFiniteState_metadata s2
            (.call (some (none, none)) (ofString "jset")
              [.var .local (ofString "inner"), .var .local (ofString "key"), .var .local (ofString "v")])).1
          rcases hj : evaluateHOLFiniteState s2
              (.call (some (none, none)) (ofString "jset")
                [.var .local (ofString "inner"), .var .local (ofString "key"), .var .local (ofString "v")]) with ⟨rj, s3⟩
          simp only [hj] at hmeta_j hnt hfr ⊢
          have hnt_j : (evaluateHOLFiniteState s2
              (.call (some (none, none)) (ofString "jset")
                [.var .local (ofString "inner"), .var .local (ofString "key"), .var .local (ofString "v")])).1 ≠ some .timeOut := by
            rw [hj]; cases rj with | none => simp | some cj => cases cj <;> simp at hnt ⊢
          have hfr_j : FlowingOrResumes (evaluateHOLFiniteState s2
              (.call (some (none, none)) (ofString "jset")
                [.var .local (ofString "inner"), .var .local (ofString "key"), .var .local (ofString "v")])).1 := by
            rw [hj]; cases rj with | none => exact Or.inl rfl | some _ => exact hfr
          have hstep23 := jset_tsInner_step_r31 wsAcctBufs ["heap_ptr", "journal_n", "scratch_ptr"]
            (by simp) (by simp)
            (.var .local (ofString "inner")) (.var .local (ofString "key")) (.var .local (ofString "v"))
            s2 heff2.code hWs2 iw hs2_inner hs2_wrs hnt_j hfr_j
          rw [hj] at hstep23; dsimp only at hstep23
          cases rj with
          | some cr_j =>
            exact (WorldStepSc.trans hB hgw hstep02 hstep23).with_locals_clock _ _
          | none =>
            dsimp only at hnt hfr ⊢
            have hWs3 : WorldOK s3 := hstep23.worldOK_bufs hB hWs2
            have hret := progWStep_return wsAcctBufs ["heap_ptr", "journal_n", "scratch_ptr"] (.const 0#64)
              s3 (hmeta_j.trans heff2.code) hWs3 hnt hfr
            exact (WorldStepSc.trans hB hgw hstep02 (WorldStepSc.trans hB hgw hstep23 hret)).with_locals_clock _ _

theorem wkSc_set_storage :
    WorldKeepsSc WorldOK (bufRegions wsAcctBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
      (ofString "set_storage") := by
  have hB := validBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_jn_sp
  refine ⟨_, _, _, lookup_set_storage, fun {F} s0 hc0 hW0 ⟨vals, hl⟩ hnt0 hres0 => ?_⟩
  have hparams_ok : ∃ (addrw kw : BitVec 64) (vval : ValueHOL 64),
      s0.locals.lookup (ofString "addr") = some (.val (.word addrw)) ∧
      s0.locals.lookup (ofString "key") = some (.val (.word kw)) ∧
      s0.locals.lookup (ofString "value") = some vval ∧
      shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vval) = true := by
    have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "set_storage")
      vals _ s0.locals _ hl
    simp only [lookupCodeHOLExact, lookup_set_storage] at hx
    rcases vals with _ | ⟨va, _ | ⟨vk, _ | ⟨vv, _ | _⟩⟩⟩
    · simp at hx
    · simp at hx
    · simp at hx
    · rcases va with ⟨⟨wa⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hx; done)
      rcases vk with ⟨⟨wk⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hx; done)
      simp [shapeOfHOLExact, shapeEqHOL,
        show ofString "addr" ≠ ofString "key" by decide,
        show ofString "addr" ≠ ofString "value" by decide,
        show ofString "key" ≠ ofString "value" by decide] at hx
      obtain ⟨hsh_vv, hL⟩ := hx
      refine ⟨wa, wk, vv, ?_, ?_, ?_, hsh_vv⟩
      · have := congrFun hL (ofString "addr")
        simpa [FUPDATE,
          show ofString "addr" ≠ ofString "key" by decide,
          show ofString "addr" ≠ ofString "value" by decide,
          show ofString "key" ≠ ofString "addr" by decide,
          show ofString "value" ≠ ofString "addr" by decide] using this.symm
      · have := congrFun hL (ofString "key")
        simpa [FUPDATE,
          show ofString "key" ≠ ofString "value" by decide,
          show ofString "value" ≠ ofString "key" by decide] using this.symm
      · have := congrFun hL (ofString "value")
        simpa [FUPDATE] using this.symm
    · simp at hx
  obtain ⟨addrw, kw, vval, hs0_addr, hs0_key, hs0_val, hsh_val⟩ := hparams_ok
  have hfr0 : FlowingOrResumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_set_storage)).1 :=
    Or.inr (Or.inr (Or.inr hres0))
  simp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_set_storage,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil] at hnt0 hfr0 ⊢
  -- Step 1: `decCall "a" .one "get_account_optional" [addr]`
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt0 hfr0 ⊢
  rcases hargs_ga : @evalListHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
      [.var .local (ofString "addr")] with _ | vs_ga
  · simp [evalListHOLFinite, hargs_ga] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs_ga] at hnt0 hfr0 ⊢
    rcases hlk_ga : lookupCodeHOLFinite s0.code.lookup (ofString "get_account_optional") vs_ga with _ | ⟨bga, cga, rga⟩
    · simp [hlk_ga] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
    · simp only [hlk_ga] at hnt0 hfr0 ⊢
      by_cases hcz0 : s0.clock = 0
      · simp [hcz0] at hnt0
      rw [if_neg hcz0] at hnt0 hfr0 ⊢
      let ent_ga := callEntryStateHOLFinite s0 cga
      have hWent_ga : WorldOK ent_ga := localsFree_worldOK s0 cga (s0.clock - 1) hW0
      have hmeta_ga := (PanRunBounded.evaluateHOLFiniteState_metadata ent_ga bga).1
      rcases hrun_ga : evaluateHOLFiniteState ent_ga bga with ⟨res_ga, p_ga⟩
      simp only [ent_ga] at hrun_ga hmeta_ga
      simp only [hrun_ga] at hmeta_ga hnt0 hfr0 ⊢
      have hnt_ga : (evaluateHOLFiniteState ent_ga bga).1 ≠ some .timeOut := by
        simp only [ent_ga, hrun_ga]; rintro rfl; simp at hnt0
      cases res_ga with
      | none => exact absurd hfr0 not_flowingOrResumes_error
      | some cr_ga =>
        cases cr_ga with
        | timeOut => simp at hnt0
        | error | «break» | «continue» => exact absurd hfr0 not_flowingOrResumes_error
        | finalFfi _ => exact absurd hfr0 not_flowingOrResumes_finalFfi
        | exception eid ev =>
          dsimp only at hfr0 ⊢
          have hres_ex : Resumes (some (.exception eid ev)) := by
            rcases hfr0 with h | h | h | hr <;> try simp at h
            exact hr
          have hspec := FunSpec.at_lookup wkSc_get_account_optional s0 hc0 vs_ga bga cga rga hlk_ga hWent_ga hnt_ga
          simp only [ent_ga, hrun_ga] at hspec
          exact ((hspec hres_ex).mono_bufs (fun _ h => h)
            (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)).from_entry
        | returned vga =>
          dsimp only at hnt0 hfr0 ⊢
          by_cases hsh_ga : (shapeEqHOL (shapeOfHOLExact vga) .one && shapeEqHOL (shapeOfHOLExact vga) rga) = true
          · simp only [hsh_ga, ↓reduceIte] at hnt0 hfr0 ⊢
            have hspec := FunSpec.at_lookup wkSc_get_account_optional s0 hc0 vs_ga bga cga rga hlk_ga hWent_ga hnt_ga
            simp only [ent_ga, hrun_ga] at hspec
            set sa := setVarHOLFinite (ofString "a") vga { p_ga with locals := s0.locals }
            have hstep_ga : WorldStepSc (bufRegions wsAcctBufs) ["heap_ptr", "journal_n", "scratch_ptr"]
                stdKeep NoExtra s0 none sa :=
              ((hspec (Or.inl ⟨vga, rfl⟩)).mono_bufs (fun _ h => h)
                (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)).from_entry
            have hWsa : WorldOK sa := hstep_ga.worldOK_bufs hB hW0
            have hsa_code : sa.code = originalRuntimeCode := hmeta_ga.trans hc0
            have hsa_addr : sa.locals.lookup (ofString "addr") = some (.val (.word addrw)) := by
              simp [sa, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs0_addr,
                show ofString "a" ≠ ofString "addr" by decide]
            have hsa_key : sa.locals.lookup (ofString "key") = some (.val (.word kw)) := by
              simp [sa, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs0_key,
                show ofString "a" ≠ ofString "key" by decide]
            have hsa_val : sa.locals.lookup (ofString "value") = some vval := by
              simp [sa, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs0_val,
                show ofString "a" ≠ ofString "value" by decide]
            -- Step 2: `seq (ite (a == 1) (raise StateErr 3) skip) ...`
            suffices hbody_sa : ∀ { p_rest : ProgHOL 64 },
                p_rest = .seq
                  (.ite (.cmp .equal (.var .local (ofString "a")) (.const 1#64))
                    (.raise (ofString "StateErr") (.const 3#64)) .skip)
                  (.dec (ofString "outer") .one
                    (.load .one (.op .add [.var .global (ofString "ts"), .const 32#64]))
                    (.decCall (ofString "m") (.comb [.one, .one]) (ofString "htab_get")
                      [.var .local (ofString "outer"), .var .local (ofString "addr")]
                      (.dec (ofString "inner") .one (.const 0#64)
                        (.seq
                          (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
                            (.seq
                              (.call (some (some (.local, ofString "inner"), none)) (ofString "htab_new")
                                [.const 32#64, .const 8#64])
                              (.call (some (none, none)) (ofString "jset")
                                [.var .local (ofString "outer"), .var .local (ofString "addr"), .var .local (ofString "inner")]))
                            (.assign .local (ofString "inner") (.rfield 1 (.var .local (ofString "m")))))
                          setStorageAllocTail)))) →
                (evaluateHOLFiniteState sa p_rest).1 ≠ some .timeOut →
                FlowingOrResumes (evaluateHOLFiniteState sa p_rest).1 →
                WorldStepSc (bufRegions wsAcctBufs) ["heap_ptr", "journal_n", "scratch_ptr"]
                  stdKeep NoExtra sa (evaluateHOLFiniteState sa p_rest).1 (evaluateHOLFiniteState sa p_rest).2 by
              have hstep_rest := hbody_sa rfl hnt0 hfr0
              exact (WorldStepSc.trans hB hgw hstep_ga hstep_rest).with_locals_clock _ _
            intro p_rest hp_rest hnt_sa hfr_sa
            subst hp_rest
            rw [evaluateHOLFiniteState_seq_line780] at hnt_sa hfr_sa ⊢
            rcases hite1 : evaluateHOLFiniteState sa
                (.ite (.cmp .equal (.var .local (ofString "a")) (.const 1#64))
                  (.raise (ofString "StateErr") (.const 3#64)) .skip) with ⟨r_ite1, s_ite1⟩
            simp only [hite1] at hnt_sa hfr_sa ⊢
            have hnt_ite1 : (evaluateHOLFiniteState sa
                (.ite (.cmp .equal (.var .local (ofString "a")) (.const 1#64))
                  (.raise (ofString "StateErr") (.const 3#64)) .skip)).1 ≠ some .timeOut := by
              rw [hite1]; cases r_ite1 with | none => simp | some c => cases c <;> simp at hnt_sa ⊢
            have hfr_ite1 : FlowingOrResumes (evaluateHOLFiniteState sa
                (.ite (.cmp .equal (.var .local (ofString "a")) (.const 1#64))
                  (.raise (ofString "StateErr") (.const 3#64)) .skip)).1 := by
              rw [hite1]; cases r_ite1 with | none => exact Or.inl rfl | some _ => exact hfr_sa
            cases r_ite1 with
            | some cr_ite1 =>
              have hs_ite1 := progWStep_ite
                (progWStep_raise wsAcctBufs ["heap_ptr", "journal_n", "scratch_ptr"] (ofString "StateErr") (.const 3#64))
                (progWStep_skip wsAcctBufs ["heap_ptr", "journal_n", "scratch_ptr"])
                sa hsa_code hWsa hnt_ite1 hfr_ite1
              rw [hite1] at hs_ite1
              exact hs_ite1
            | none =>
              have hs_ite1_eq : s_ite1 = sa := by
                rw [evaluateHOLFiniteState_ite] at hite1
                rcases hev_c : @evalHOLExact 64 F _ sa.toExact (fun a => Classical.propDecidable (sa.memaddrs a))
                    (.cmp .equal (.var .local (ofString "a")) (.const 1#64)) with _ | cv
                · simp [hev_c] at hite1
                · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> simp [hev_c] at hite1
                  split_ifs at hite1 with hcw
                  · simp [evaluateHOLFiniteState_skip] at hite1; exact hite1.symm
                  · rcases hlk_e : sa.eshapes.lookup (ofString "StateErr") with _ | sh <;>
                      simp [hlk_e, evalHOLExact] at hite1
                    by_cases hcond : shapeOfHOLExact (ValueHOL.val (HolWordLab.word 3#64)) = sh ∧
                        sizeOfShapeWithContextHOL sa.structs (shapeOfHOLExact (ValueHOL.val (HolWordLab.word 3#64))) ≤ 32
                    · rw [if_pos hcond] at hite1; injection hite1 with h0 _; cases h0
                    · rw [if_neg hcond] at hite1; injection hite1 with h0 _; cases h0
              subst hs_ite1_eq
              dsimp only at hnt_sa hfr_sa ⊢
              -- Step 3: `dec "outer" .one (load (ts + 32))`
              rw [evaluateHOLFiniteState_dec_total] at hnt_sa hfr_sa ⊢
              rcases hev_o : @evalHOLExact 64 F _ sa.toExact (fun a => Classical.propDecidable (sa.memaddrs a))
                  (.load .one (.op .add [.var .global (ofString "ts"), .const 32#64])) with _ | vo
              · simp [hev_o] at hfr_sa; exact absurd hfr_sa not_flowingOrResumes_error
              · simp only [hev_o] at hnt_sa hfr_sa ⊢
                obtain ⟨tw, rfl, htw_nat, hts_nz⟩ := evalAt_loadG_nz sa hWsa.1.1 "ts" 32#64 (by decide) vo hev_o
                have hsh_tw : shapeEqHOL .one (shapeOfHOLExact (.val (.word tw) : ValueHOL 64)) = true := by
                  simp [shapeOfHOLExact, shapeEqHOL]
                simp only [hsh_tw, ↓reduceIte] at hnt_sa hfr_sa ⊢
                set so := setVarHOLFinite (ofString "outer") (.val (.word tw)) sa
                have hWso : WorldOK so := localsFree_worldOK sa _ sa.clock hWsa
                have hso_code : so.code = originalRuntimeCode := hsa_code
                have hso_outer : so.locals.lookup (ofString "outer") = some (.val (.word tw)) := by
                  simp [so, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                have hso_addr : so.locals.lookup (ofString "addr") = some (.val (.word addrw)) := by
                  simp [so, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsa_addr,
                    show ofString "outer" ≠ ofString "addr" by decide]
                have hso_key : so.locals.lookup (ofString "key") = some (.val (.word kw)) := by
                  simp [so, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsa_key,
                    show ofString "outer" ≠ ofString "key" by decide]
                have hso_val : so.locals.lookup (ofString "value") = some vval := by
                  simp [so, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsa_val,
                    show ofString "outer" ≠ ofString "value" by decide]
                suffices hso_step : WorldStepSc (bufRegions wsAcctBufs) ["heap_ptr", "journal_n", "scratch_ptr"]
                    stdKeep NoExtra so
                    (evaluateHOLFiniteState so
                      (.decCall (ofString "m") (.comb [.one, .one]) (ofString "htab_get")
                        [.var .local (ofString "outer"), .var .local (ofString "addr")]
                        (.dec (ofString "inner") .one (.const 0#64)
                          (.seq
                            (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
                              (.seq
                                (.call (some (some (.local, ofString "inner"), none)) (ofString "htab_new")
                                  [.const 32#64, .const 8#64])
                                (.call (some (none, none)) (ofString "jset")
                                  [.var .local (ofString "outer"), .var .local (ofString "addr"), .var .local (ofString "inner")]))
                              (.assign .local (ofString "inner") (.rfield 1 (.var .local (ofString "m")))))
                            setStorageAllocTail)))).1
                    (evaluateHOLFiniteState so
                      (.decCall (ofString "m") (.comb [.one, .one]) (ofString "htab_get")
                        [.var .local (ofString "outer"), .var .local (ofString "addr")]
                        (.dec (ofString "inner") .one (.const 0#64)
                          (.seq
                            (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
                              (.seq
                                (.call (some (some (.local, ofString "inner"), none)) (ofString "htab_new")
                                  [.const 32#64, .const 8#64])
                                (.call (some (none, none)) (ofString "jset")
                                  [.var .local (ofString "outer"), .var .local (ofString "addr"), .var .local (ofString "inner")]))
                              (.assign .local (ofString "inner") (.rfield 1 (.var .local (ofString "m")))))
                            setStorageAllocTail)))).2 by
                  exact (WorldStepSc.of_pre_locals_clock (s := sa) (L := so.locals) (k := sa.clock) hso_step).with_locals_clock _ _
                -- Step 4: `decCall "m" (.comb [.one, .one]) "htab_get" [outer, addr]`
                rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt_sa hfr_sa ⊢
                have hargs_hg : evalListHOLFinite so (h := fun a => Classical.propDecidable (so.memaddrs a))
                    [.var .local (ofString "outer"), .var .local (ofString "addr")] =
                    some [.val (.word tw), .val (.word addrw)] := by
                  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hso_outer, hso_addr]
                rw [hargs_hg] at hnt_sa hfr_sa ⊢; dsimp only at hnt_sa hfr_sa ⊢
                rcases hlk_hg : lookupCodeHOLFinite so.code.lookup (ofString "htab_get")
                    [.val (.word tw), .val (.word addrw)] with _ | ⟨bhg, chg, rhg⟩
                · simp [hlk_hg] at hfr_sa; exact absurd hfr_sa not_flowingOrResumes_error
                · simp only [hlk_hg] at hnt_sa hfr_sa ⊢
                  by_cases hcz_so : so.clock = 0
                  · simp [hcz_so] at hnt_sa
                  rw [if_neg hcz_so] at hnt_sa hfr_sa ⊢
                  have hbhg_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "htab_get")
                    _ _ bhg _ rhg _ chg EvmFrameSpecs.lookup_htab_get (by rwa [← hso_code])
                  subst hbhg_eq
                  have hchg_t : chg.lookup (ofString "t") = some (.val (.word tw)) := by
                    have ht_ev : evalAt so (.var .local (ofString "outer")) = some (.val (.word tw)) := by
                      simp [evalAt, evalHOLExact, toExact, hso_outer]
                    have ⟨v1', _, he1', _, hc1', _⟩ := callee_param_two_r16_code so (ofString "htab_get")
                      (ofString "t") (ofString "key") .one .one _ _
                      (by rw [hso_code]; exact EvmFrameSpecs.lookup_htab_get)
                      (.var .local (ofString "outer")) (.var .local (ofString "addr"))
                      _ _ chg rhg hargs_hg hlk_hg
                    rw [ht_ev] at he1'; injection he1' with h'; subst h'; exact hc1'
                  have hchg_k : chg.lookup (ofString "key") = some (.val (.word addrw)) := by
                    have hk_ev : evalAt so (.var .local (ofString "addr")) = some (.val (.word addrw)) := by
                      simp [evalAt, evalHOLExact, toExact, hso_addr]
                    have ⟨_, v2', _, he2', _, hc2'⟩ := callee_param_two_r16_code so (ofString "htab_get")
                      (ofString "t") (ofString "key") .one .one _ _
                      (by rw [hso_code]; exact EvmFrameSpecs.lookup_htab_get)
                      (.var .local (ofString "outer")) (.var .local (ofString "addr"))
                      _ _ chg rhg hargs_hg hlk_hg
                    rw [hk_ev] at he2'; injection he2' with h'; subst h'; exact hc2'
                  let ent_hg := callEntryStateHOLFinite so chg
                  rcases hrun_hg : evaluateHOLFiniteState ent_hg (sourceFnBody Guest.Software.guestFn_htab_get) with ⟨res_hg, p_hg⟩
                  dsimp only [ent_hg] at hrun_hg
                  simp only [hrun_hg] at hnt_sa hfr_sa ⊢
                  cases res_hg with
                  | none => exact absurd hfr_sa not_flowingOrResumes_error
                  | some cr_hg =>
                    cases cr_hg with
                    | timeOut => simp at hnt_sa
                    | error | «break» | «continue» => exact absurd hfr_sa not_flowingOrResumes_error
                    | finalFfi _ => exact absurd hfr_sa not_flowingOrResumes_finalFfi
                    | exception eid_hg ev_hg =>
                      dsimp only at hfr_sa ⊢
                      have hres_ex : Resumes (some (.exception eid_hg ev_hg)) := by
                        rcases hfr_sa with h | h | h | hr <;> try simp at h
                        exact hr
                      have hro_hg := FunSpec.at_lookup EvmFrameSpecs.ro_htab_get so hso_code
                        _ (sourceFnBody Guest.Software.guestFn_htab_get) chg rhg hlk_hg
                        (guestInv_callEntry so chg hWso.1.1) (by rw [hrun_hg]; simp)
                      have hro_hg' := hro_hg (by rw [hrun_hg]; exact hres_ex)
                      rw [hrun_hg] at hro_hg'; dsimp only at hro_hg'
                      have hws_ex : WorldStepSc (bufRegions wsAcctBufs) ["heap_ptr", "journal_n", "scratch_ptr"]
                          stdKeep NoExtra so (some (.exception eid_hg ev_hg)) (PanSemStateFiniteExact.emptyLocalsHOLFinite p_hg) := by
                        have : PanSemStateFiniteExact.emptyLocalsHOLFinite p_hg =
                            { so with locals := (PanSemStateFiniteExact.emptyLocalsHOLFinite p_hg).locals, clock := p_hg.clock } := by
                          rw [hro_hg']; rfl
                        rw [this]
                        exact (WorldStepSc.refl so (some (.exception eid_hg ev_hg)) hWso.1).with_locals_clock _ _
                      exact hws_ex
                    | returned v_m =>
                      dsimp only at hnt_sa hfr_sa ⊢
                      by_cases hsh_m : (shapeEqHOL (shapeOfHOLExact v_m) (.comb [.one, .one]) && shapeEqHOL (shapeOfHOLExact v_m) rhg) = true
                      · simp only [hsh_m, ↓reduceIte] at hnt_sa hfr_sa ⊢
                        have htw_nz : tw ≠ 0#64 := WkBal.htab_get_t_nonzero ent_hg tw addrw
                          (guestInv_callEntry so chg hWso.1.1) hchg_t hchg_k v_m
                          (by dsimp only [ent_hg]; rw [hrun_hg])
                        have htw_nat_so : tw.toNat = memW so (globN so "ts" + 32) := htw_nat
                        have ht0_nz : memW so (globN so "ts" + 32) ≠ 0 := by
                          intro h0; apply htw_nz; apply BitVec.eq_of_toNat_eq
                          change tw.toNat = 0; simpa [htw_nat_so] using h0
                        have hro_hg := FunSpec.at_lookup EvmFrameSpecs.ro_htab_get so hso_code
                          _ (sourceFnBody Guest.Software.guestFn_htab_get) chg rhg hlk_hg
                          (guestInv_callEntry so chg hWso.1.1) (by rw [hrun_hg]; simp)
                        have hro_hg' := hro_hg (by rw [hrun_hg]; exact Or.inl ⟨_, rfl⟩)
                        rw [hrun_hg] at hro_hg'; dsimp only at hro_hg'
                        obtain ⟨hAso, S0, hWT0⟩ := hWso
                        have hWso_copy : WorldOK so := ⟨hAso, S0, hWT0⟩
                        have htw_S0 : tw.toNat ∈ S0 := by
                          rw [htw_nat_so]; exact (ts32Slot_disj so S0 hWT0.1 hts_nz ht0_nz).1
                        have hwf_hg : HtabWF ent_hg tw.toNat :=
                          (WkBal.htabWF_with_locals so chg (so.clock - 1) tw.toNat).2 (hWT0.1.2.1 _ htw_S0).1
                        obtain ⟨f0, f1, rfl, hf1_in⟩ := WkBal.htab_get_ret_in_values ent_hg tw addrw
                          hso_code hchg_t hchg_k hwf_hg v_m
                          (by dsimp only [ent_hg]; rw [hrun_hg])
                        set sm := setVarHOLFinite (ofString "m") (.rStruct [.val (.word f0), .val (.word f1)])
                          { p_hg with locals := so.locals }
                        -- Step 5: `dec "inner" .one 0`
                        rw [evaluateHOLFiniteState_dec_total] at hnt_sa hfr_sa ⊢
                        have hev_0 : @evalHOLExact 64 F _ sm.toExact (fun a => Classical.propDecidable (sm.memaddrs a))
                            (.const 0#64) = some (.val (.word 0#64)) := rfl
                        have hsh_0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64) : ValueHOL 64)) = true := by
                          simp [shapeOfHOLExact, shapeEqHOL]
                        simp only [hev_0, hsh_0, ↓reduceIte] at hnt_sa hfr_sa ⊢
                        set si := setVarHOLFinite (ofString "inner") (.val (.word 0#64)) sm
                        have hsi_lc : si = { so with locals := si.locals, clock := p_hg.clock } := by
                          dsimp only [si, sm, setVarHOLFinite]; rw [hro_hg']; rfl
                        have hWsi : WorldOK si := by
                          rw [hsi_lc]; exact localsFree_worldOK so si.locals p_hg.clock hWso_copy
                        have hsi_code : si.code = originalRuntimeCode := by rw [hsi_lc]; exact hso_code
                        have hsi_outer : si.locals.lookup (ofString "outer") = some (.val (.word tw)) := by
                          simp [si, sm, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hso_outer,
                            show ofString "inner" ≠ ofString "outer" by decide,
                            show ofString "m" ≠ ofString "outer" by decide]
                        have hsi_addr : si.locals.lookup (ofString "addr") = some (.val (.word addrw)) := by
                          simp [si, sm, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hso_addr,
                            show ofString "inner" ≠ ofString "addr" by decide,
                            show ofString "m" ≠ ofString "addr" by decide]
                        have hsi_key : si.locals.lookup (ofString "key") = some (.val (.word kw)) := by
                          simp [si, sm, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hso_key,
                            show ofString "inner" ≠ ofString "key" by decide,
                            show ofString "m" ≠ ofString "key" by decide]
                        have hsi_val : si.locals.lookup (ofString "value") = some vval := by
                          simp [si, sm, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hso_val,
                            show ofString "inner" ≠ ofString "value" by decide,
                            show ofString "m" ≠ ofString "value" by decide]
                        have hsi_m : si.locals.lookup (ofString "m") =
                            some (.rStruct [.val (.word f0), .val (.word f1)]) := by
                          simp [si, sm, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                            show ofString "inner" ≠ ofString "m" by decide]
                        suffices hsi_step : WorldStepSc (bufRegions wsAcctBufs) ["heap_ptr", "journal_n", "scratch_ptr"]
                            stdKeep NoExtra si
                            (evaluateHOLFiniteState si
                              (.seq
                                (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
                                  (.seq
                                    (.call (some (some (.local, ofString "inner"), none)) (ofString "htab_new")
                                      [.const 32#64, .const 8#64])
                                    (.call (some (none, none)) (ofString "jset")
                                      [.var .local (ofString "outer"), .var .local (ofString "addr"), .var .local (ofString "inner")]))
                                  (.assign .local (ofString "inner") (.rfield 1 (.var .local (ofString "m")))))
                                setStorageAllocTail)).1
                            (evaluateHOLFiniteState si
                              (.seq
                                (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
                                  (.seq
                                    (.call (some (some (.local, ofString "inner"), none)) (ofString "htab_new")
                                      [.const 32#64, .const 8#64])
                                    (.call (some (none, none)) (ofString "jset")
                                      [.var .local (ofString "outer"), .var .local (ofString "addr"), .var .local (ofString "inner")]))
                                  (.assign .local (ofString "inner") (.rfield 1 (.var .local (ofString "m")))))
                                  setStorageAllocTail)).2 by
                          have hso_eq : { so with locals := si.locals, clock := p_hg.clock } = si := hsi_lc.symm
                          have hsi_step' : WorldStepSc (bufRegions wsAcctBufs) ["heap_ptr", "journal_n", "scratch_ptr"]
                              stdKeep NoExtra { so with locals := si.locals, clock := p_hg.clock }
                              (evaluateHOLFiniteState si
                                (.seq
                                  (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
                                    (.seq
                                      (.call (some (some (.local, ofString "inner"), none)) (ofString "htab_new")
                                        [.const 32#64, .const 8#64])
                                      (.call (some (none, none)) (ofString "jset")
                                        [.var .local (ofString "outer"), .var .local (ofString "addr"), .var .local (ofString "inner")]))
                                    (.assign .local (ofString "inner") (.rfield 1 (.var .local (ofString "m")))))
                                  setStorageAllocTail)).1
                              (evaluateHOLFiniteState si
                                (.seq
                                  (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
                                    (.seq
                                      (.call (some (some (.local, ofString "inner"), none)) (ofString "htab_new")
                                        [.const 32#64, .const 8#64])
                                      (.call (some (none, none)) (ofString "jset")
                                        [.var .local (ofString "outer"), .var .local (ofString "addr"), .var .local (ofString "inner")]))
                                    (.assign .local (ofString "inner") (.rfield 1 (.var .local (ofString "m")))))
                                  setStorageAllocTail)).2 := by
                            rw [hso_eq]; exact hsi_step
                          exact (WorldStepSc.of_pre_locals_clock (s := so) (L := si.locals) (k := p_hg.clock) hsi_step').with_locals_clock _ _
                        -- Step 6: `seq (ite (m.0 == 0) (htab_new; jset) (inner := m.1)) setStorageAllocTail`
                        rw [evaluateHOLFiniteState_seq_line780] at hnt_sa hfr_sa ⊢
                        rw [evaluateHOLFiniteState_ite] at hnt_sa hfr_sa ⊢
                        have hev_m0 : @evalHOLExact 64 F _ si.toExact (fun a => Classical.propDecidable (si.memaddrs a))
                            (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64)) =
                            some (.val (.word (if f0 == 0#64 then 1#64 else 0#64))) := by
                          simp [evalHOLExact, toExact, hsi_m, Compiler.Encoders.Asm.wordCmpHOL]
                        rw [hev_m0] at hnt_sa hfr_sa ⊢; dsimp only at hnt_sa hfr_sa ⊢
                        by_cases hf0 : f0 = 0#64
                        · -- Miss branch: `f0 = 0`, execute `htab_new(32, 8); jset(outer, addr, inner)`
                          simp only [hf0, beq_self_eq_true, ↓reduceIte, show (1#64 : BitVec 64) ≠ 0 by decide] at hnt_sa hfr_sa ⊢
                          rw [evaluateHOLFiniteState_seq_line780] at hnt_sa hfr_sa ⊢
                          let p_hn : ProgHOL 64 := .call (some (some (.local, ofString "inner"), none))
                            (ofString "htab_new") [.const 32#64, .const 8#64]
                          let p_js1 : ProgHOL 64 := .call (some (none, none)) (ofString "jset")
                            [.var .local (ofString "outer"), .var .local (ofString "addr"), .var .local (ofString "inner")]
                          have hmeta_hn := (PanRunBounded.evaluateHOLFiniteState_metadata si p_hn).1
                          rcases hhn : evaluateHOLFiniteState si p_hn with ⟨rhn, shn⟩
                          simp only [p_hn] at hhn hmeta_hn
                          simp only [hhn] at hmeta_hn hnt_sa hfr_sa ⊢
                          have hfr_hn : FlowingOrResumes (evaluateHOLFiniteState si p_hn).1 := by
                            dsimp only [p_hn]; rw [hhn]
                            cases rhn with
                            | none => exact Or.inl rfl
                            | some _ => dsimp only at hfr_sa; exact hfr_sa
                          have hstep_hn0 : WorldStepSc (bufRegions wsAcctBufs) ["heap_ptr", "journal_n", "scratch_ptr"]
                              stdKeep NoExtra si rhn shn := by
                            have hw0 := merge_new_call_worldStep si (ofString "inner") 32#64 8#64 hWsi
                              (by decide) (by decide) hfr_hn
                            dsimp only [p_hn] at hw0; rw [hhn] at hw0
                            exact hw0.mono_bufs (fun _ h => by cases h) (by simp)
                          cases rhn with
                          | some cr_hn =>
                            exact hstep_hn0
                          | none =>
                            dsimp only at hnt_sa hfr_sa ⊢
                            have hWshn : WorldOK shn := hstep_hn0.worldOK_bufs hB hWsi
                            have hshn_code : shn.code = originalRuntimeCode := hmeta_hn.trans hsi_code
                            have hmeta_js1 := (PanRunBounded.evaluateHOLFiniteState_metadata shn p_js1).1
                            rcases hjs1 : evaluateHOLFiniteState shn p_js1 with ⟨rjs1, sjs1⟩
                            simp only [p_js1] at hjs1 hmeta_js1
                            simp only [hjs1] at hmeta_js1 hnt_sa hfr_sa ⊢
                            have hnt_js1 : (evaluateHOLFiniteState shn p_js1).1 ≠ some .timeOut := by
                              dsimp only [p_js1]; rw [hjs1]
                              cases rjs1 with | none => simp | some cj => cases cj <;> simp at hnt_sa ⊢
                            have hfr_js1 : FlowingOrResumes (evaluateHOLFiniteState shn p_js1).1 := by
                              dsimp only [p_js1]; rw [hjs1]
                              cases rjs1 with | none => exact Or.inl rfl | some _ => exact hfr_sa
                            -- Extract fresh table `iw` bound to `inner` via `merge_new_call_bound_owned` on `S0`
                            have hWT_si : WorldTyped si S0 := by
                              rw [hsi_lc]; exact (worldTyped_with_locals so si.locals p_hg.clock S0).2 hWT0
                            obtain ⟨Nd0, hWT_si0⟩ := (worldTyped_iff_with si S0).1 hWT_si
                            obtain ⟨iw, hshn_inner, hshn_loc_other, _, hiw_nz_nat, hkey_iw, _, hf_iw, _⟩ :=
                              merge_new_call_bound_owned si (ofString "inner") 32#64 8#64 S0 Nd0
                                hWsi.1 hWT_si0 (by decide) (by decide) hfr_hn
                            rw [hhn] at hshn_inner hshn_loc_other hkey_iw hf_iw
                            dsimp only at hshn_inner hshn_loc_other hkey_iw hf_iw
                            have hiw_nz : iw ≠ 0#64 := fun h0 => hiw_nz_nat (by simp [h0])
                            have hshn_outer : shn.locals.lookup (ofString "outer") = some (.val (.word tw)) :=
                              (hshn_loc_other _ (by decide)).trans hsi_outer
                            have hshn_addr : shn.locals.lookup (ofString "addr") = some (.val (.word addrw)) :=
                              (hshn_loc_other _ (by decide)).trans hsi_addr
                            have hshn_key : shn.locals.lookup (ofString "key") = some (.val (.word kw)) :=
                              (hshn_loc_other _ (by decide)).trans hsi_key
                            have hshn_val : shn.locals.lookup (ofString "value") = some vval :=
                              (hshn_loc_other _ (by decide)).trans hsi_val
                            have hts_shn : globN shn "ts" = globN si "ts" :=
                              globN_eq_of_lookup (hstep_hn0.1.2.2.1 (ofString "ts") (by decide))
                            have hts_si : globN si "ts" = globN sa "ts" := by rw [hsi_lc]; rfl
                            have hts_shn_nz : globN shn "ts" ≠ 0 := by rw [hts_shn, hts_si]; exact hts_nz
                            have htts_shn : tw.toNat = memW shn (globN shn "ts" + 32) := by
                              have hm32 : memW shn (globN si "ts" + 32) = memW si (globN si "ts" + 32) := by
                                have hw0 := merge_new_call_worldStep si (ofString "inner") 32#64 8#64 hWsi
                                  (by decide) (by decide) hfr_hn
                                dsimp only [p_hn] at hw0; rw [hhn] at hw0
                                exact hw0.1.2.2.2.1 ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]) (by simp [stdKeep])
                                  (by rw [hts_si]; exact hts_nz) 32 (by simp) (fun _ h => by cases h)
                              rw [hts_shn, hm32, hsi_lc]
                              exact htw_nat
                            have hjs1_res := jset_ts32_fresh_inner_step_r31 shn
                              (B := wsAcctBufs) (gw := ["heap_ptr", "journal_n", "scratch_ptr"]) (by simp) (by simp)
                              (.var .local (ofString "outer")) (.var .local (ofString "addr")) (.var .local (ofString "inner"))
                              tw addrw iw
                              (by simp [evalAt, evalHOLExact, toExact, hshn_outer])
                              (by simp [evalAt, evalHOLExact, toExact, hshn_addr])
                              (by simp [evalAt, evalHOLExact, toExact, hshn_inner])
                              hWshn hshn_code hts_shn_nz htw_nz hiw_nz htts_shn hkey_iw hf_iw
                              hnt_js1 hfr_js1
                            dsimp only [p_js1] at hjs1_res; rw [hjs1] at hjs1_res
                            obtain ⟨hrjs1_eq, hsjs1_loc, hstep_in_js1, hsp_js1, hiw_wrs_sjs1⟩ := hjs1_res
                            dsimp only at hrjs1_eq hsjs1_loc hstep_in_js1 hsp_js1 hiw_wrs_sjs1
                            subst hrjs1_eq
                            dsimp only at hnt_sa hfr_sa ⊢
                            -- Compose `si -> shn -> sjs1` into `WorldStepSc` via `worldStepSc_trans_owned_r31`
                            have hstep_branch : WorldStepSc (bufRegions wsAcctBufs) ["heap_ptr", "journal_n", "scratch_ptr"]
                                stdKeep NoExtra si none sjs1 := by
                              refine worldStepSc_trans_owned_r31 hB hgw hstep_hn0 (fun S Nd hWT_S => ?_) hstep_in_js1 hsp_js1
                              obtain ⟨iw', hshn_in', _, _, _, _, _, _, hWT_shn', hOG_shn', _⟩ :=
                                merge_new_call_bound_owned si (ofString "inner") 32#64 8#64 S Nd
                                  hWsi.1 hWT_S (by decide) (by decide) hfr_hn
                              rw [hhn] at hshn_in' hWT_shn' hOG_shn'
                              dsimp only at hshn_in' hWT_shn' hOG_shn'
                              have hiw_eq : iw' = iw := by
                                rw [hshn_inner] at hshn_in'
                                injection hshn_in' with h'; injection h' with h'; injection h' with h''
                                exact h''.symm
                              cases hiw_eq
                              have htw_S : tw.toNat ∈ S := by
                                have hts_si_nz : globN si "ts" ≠ 0 := by rw [hts_si]; exact hts_nz
                                have ht0_si_nz : memW si (globN si "ts" + 32) ≠ 0 := by rw [hsi_lc]; exact ht0_nz
                                have htw_si : tw.toNat = memW si (globN si "ts" + 32) := by rw [hsi_lc]; exact htw_nat
                                rw [htw_si]
                                exact (ts32Slot_disj si S hWT_S.1 hts_si_nz ht0_si_nz).1
                              have hw0 := merge_new_call_worldStep si (ofString "inner") 32#64 8#64 hWsi
                                (by decide) (by decide) hfr_hn
                              dsimp only [p_hn] at hw0; rw [hhn] at hw0
                              have hD0 : IvlsDisj (bufRegions [] si) (worldTypedIvls si S Nd) := fun _ h => by cases h
                              obtain ⟨_, _, _, _, _, hFO0, _⟩ := hw0.1.2.2.2.2 S Nd hWT_S hD0
                              refine ⟨S ++ [iw.toNat], Nd, fun t ht => List.mem_append_left _ ht,
                                hWT_shn', hOG_shn', ?_, fun a ha hhf => hFO0 a (fun i hi => ?_) hhf⟩
                              · intro t ht
                                simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
                                rcases ht with rfl | rfl
                                · exact List.mem_append_left _ htw_S
                                · exact List.mem_append_right _ (List.mem_singleton.2 rfl)
                              · rcases List.mem_append.1 hi with hi1 | hfg
                                · rcases List.mem_append.1 hi1 with hwo | hnil
                                  · exact ha i (List.mem_append_left _ (List.mem_append_left _ hwo))
                                  · cases hnil
                                · exact ha i (List.mem_append_right _ hfg)
                            have hWsjs1 : WorldOK sjs1 := hstep_branch.worldOK_bufs hB hWsi
                            have hsjs1_code : sjs1.code = originalRuntimeCode := hmeta_js1.trans hshn_code
                            have hsjs1_key : sjs1.locals.lookup (ofString "key") = some (.val (.word kw)) := by
                              rw [hsjs1_loc]; exact hshn_key
                            have hsjs1_inner : sjs1.locals.lookup (ofString "inner") = some (.val (.word iw)) := by
                              rw [hsjs1_loc]; exact hshn_inner
                            have hsjs1_val : sjs1.locals.lookup (ofString "value") = some vval := by
                              rw [hsjs1_loc]; exact hshn_val
                            have htail := setStorage_allocTail_step_r31 sjs1 kw iw vval
                              hsjs1_code hWsjs1 hsjs1_key hsjs1_inner hsjs1_val hsh_val hiw_wrs_sjs1
                              hnt_sa hfr_sa
                            exact WorldStepSc.trans hB hgw hstep_branch htail
                        · -- Hit branch: `f0 ≠ 0`, `inner := m.1` (`f1`)
                          have hf0_beq : (f0 == 0#64) = false := beq_false_of_ne hf0
                          simp only [hf0_beq, Bool.false_eq_true, ↓reduceIte] at hnt_sa hfr_sa ⊢
                          rw [evaluateHOLFiniteState_assign] at hnt_sa hfr_sa ⊢
                          have hev_m1 : @evalHOLExact 64 F _ si.toExact (fun a => Classical.propDecidable (si.memaddrs a))
                              (.rfield 1 (.var .local (ofString "m"))) = some (.val (.word f1)) := by
                            simp [evalHOLExact, toExact, hsi_m]
                          have hval_f1 : si.isValidValueHOLFinite .local (ofString "inner") (.val (.word f1)) = true := by
                            have hinner_zero : si.locals.lookup (ofString "inner") = some (.val (.word 0#64)) := by
                              simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                            simp [PanSemStateFiniteExact.isValidValueHOLFinite, isValidValueHOLExact,
                              lookupKvarHOLExact, toExact, hinner_zero, shapeOfHOLExact, shapeEqHOL]
                          simp only [hev_m1, hval_f1, ↓reduceIte] at hnt_sa hfr_sa ⊢
                          set s_hit := setVarHOLFinite (ofString "inner") (.val (.word f1)) si
                          have hWs_hit : WorldOK s_hit := localsFree_worldOK si _ si.clock hWsi
                          have hs_hit_code : s_hit.code = originalRuntimeCode := hsi_code
                          have hs_hit_key : s_hit.locals.lookup (ofString "key") = some (.val (.word kw)) := by
                            simp [s_hit, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsi_key,
                              show ofString "inner" ≠ ofString "key" by decide]
                          have hs_hit_inner : s_hit.locals.lookup (ofString "inner") = some (.val (.word f1)) := by
                            simp [s_hit, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                          have hs_hit_val : s_hit.locals.lookup (ofString "value") = some vval := by
                            simp [s_hit, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsi_val,
                              show ofString "inner" ≠ ofString "value" by decide]
                          have hf1_wrs : (f1.toNat, "ts.inner") ∈ worldRoleSlots s_hit := by
                            have hf1_vals : f1.toNat ∈ htabValues so tw.toNat := hf1_in hf0
                            have hf1_vals_so : f1.toNat ∈ htabValues so (memW so (globN so "ts" + 32)) := by
                              rwa [← htw_nat_so]
                            have hts_N0 : HtabValuesIn so (memW so (globN so "ts" + 32)) S0 :=
                              hWT0.1.2.2.2.2.2.2.2.2.1 hts_nz (by rwa [← htw_nat_so])
                            obtain ⟨idx, hidx_mem, hidx_eq⟩ := List.mem_map.1 hf1_vals_so
                            have hf1_S0 : f1.toNat ∈ S0 := by
                              rw [← hidx_eq]; exact hts_N0 idx (List.mem_range.1 hidx_mem)
                            have hwf_f1 : HtabWF so f1.toNat := (hWT0.1.2.1 _ hf1_S0).1
                            have hf1_nz : f1.toNat ≠ 0 := by
                              have hfp88 : (f1.toNat, 88) ∈ htabFootprint so f1.toNat := by simp [htabFootprint]
                              have hlo := (hwf_f1.1 _ hfp88).1.1
                              have hsb : 0 < sourceBase := by decide
                              dsimp at hlo; omega
                            have hs_hit_so : s_hit = { so with locals := s_hit.locals, clock := p_hg.clock } := by
                              dsimp only [s_hit, setVarHOLFinite]; rw [hsi_lc]
                            have hwrs_eq : worldRoleSlots s_hit = worldRoleSlots so := by
                              rw [hs_hit_so]; rfl
                            rw [hwrs_eq]
                            unfold worldRoleSlots
                            refine List.mem_filter.2 ⟨?_, by simp [hf1_nz]⟩
                            apply List.mem_append.2; left; apply List.mem_append.2; right
                            unfold nestRoles
                            have hts_so_nz : globN so "ts" ≠ 0 := hts_nz
                            rw [if_neg hts_so_nz, if_neg ht0_nz]
                            exact List.mem_map.2 ⟨f1.toNat, hf1_vals_so, rfl⟩
                          have htail := setStorage_allocTail_step_r31 s_hit kw f1 vval
                            hs_hit_code hWs_hit hs_hit_key hs_hit_inner hs_hit_val hsh_val hf1_wrs
                            hnt_sa hfr_sa
                          exact WorldStepSc.of_pre_locals_clock (s := si) (L := s_hit.locals) (k := si.clock) htail
                      · simp [hsh_m] at hfr_sa; exact absurd hfr_sa not_flowingOrResumes_error
          · simp [hsh_ga] at hfr0; exact absurd hfr0 not_flowingOrResumes_error

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
