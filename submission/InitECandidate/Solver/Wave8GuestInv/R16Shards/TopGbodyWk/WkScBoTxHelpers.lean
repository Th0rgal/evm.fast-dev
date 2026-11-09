import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkBlockTxProcess
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.wk_u256_to_be_min
set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase (stdKeep)
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8Leaves.Rlp
/-! # Phases 1–4 Relational Closure (`PtxRelCutStrong`) -/
section Phases1To4RelationalClosure
open private acct_copy_step flattenHOL_shape_u256 evaluateHOLFiniteState_seq_assoc
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.AccountWk
theorem wkScBo_increment_nonce :
    WorldKeepsScBo WorldOK (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
      (ofString "increment_nonce") := by
  have hB := validBufList_acctMutBufs
  have hgw : SafeStepGlobals ["heap_ptr", "journal_n", "scratch_ptr"] := by
    intro g hg; simp at hg; rcases hg with rfl | rfl | rfl <;> simp
  refine worldKeepsScBo_of_progWStepBo lookup_increment_nonce ?_
  simp only [sourceFunctionEntry, Guest.Software.guestFn_increment_nonce,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepBo_decCall hB hgw
    (by intro p hp; simp [wsAcctBufs] at hp; rcases hp with rfl | rfl | rfl <;> simp [acctMutBufs])
    (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)
    wkScBo_get_account ?_
  exact progWStepBo_acctCopy_mut_tail hB hgw (by simp) _ _
    (fun {F} s s1 bw heff1 _ hs1_a hbw_lo hbw_hi _ _ =>
      worldEff_store_word heff1 _ _
        (fun v hv => by
          rcases hld : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
              (.load .one (.op .add [.var .local (ofString "a"), .const 0#64])) with _ | vl
          · simp [evalHOLExact, evalListHOLExact] at hv hld; rw [hld] at hv; simp at hv
          · simp [evalHOLExact, evalListHOLExact] at hv hld; rw [hld] at hv
            rcases vl with ⟨⟨wl⟩⟩ | _ | _ <;> simp [panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
            exact ⟨wl + 1#64, hv.symm⟩)
        (fun x hx _ => by
          simp [evalHOLExact, evalListHOLExact, toExact, hs1_a, panOpHOL, wordOpHOL, wordOp,
            valueIsWord, valueWord] at hx
          subst hx
          have hx0 : (bw + 0#64).toNat = bw.toNat := by simp
          exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
    (progWStepBo_seq hB hgw
      (progWStepBo_call0 (by intro p hp; simp at hp; subst hp; simp [acctMutBufs])
        (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp) wkScBo_modify_state_commit)
      (progWStepBo_return _ _ _))
theorem wkScBo_create_ether :
    WorldKeepsScBo WorldOK (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
      (ofString "create_ether") := by
  have hB := validBufList_acctMutBufs
  have hgw : SafeStepGlobals ["heap_ptr", "journal_n", "scratch_ptr"] := by
    intro g hg; simp at hg; rcases hg with rfl | rfl | rfl <;> simp
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have hhl_264 : heapLimit < 2 ^ 64 := by decide
  refine worldKeepsScBo_of_progWStepBo lookup_create_ether ?_
  simp only [sourceFunctionEntry, Guest.Software.guestFn_create_ether,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepBo_decCall hB hgw
    (by intro p hp; simp [wsAcctBufs] at hp; rcases hp with rfl | rfl | rfl <;> simp [acctMutBufs])
    (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)
    wkScBo_get_account ?_
  intro F s0 hc0 hW0 hnt0 hfr0
  rw [evaluateHOLFiniteState_seq_line780] at hnt0 hfr0 ⊢
  rcases h1 : evaluateHOLFiniteState s0
      (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
        [.var .local (ofString "a")]) with ⟨r1, s1⟩
  simp only [h1] at hnt0 hfr0 ⊢
  cases r1 with
  | some cr1 =>
    have hac := acct_copy_step s0 hc0 hW0.1 (by rw [h1]; exact hnt0) (by rw [h1]; exact hfr0)
    rw [h1] at hac
    have hws0 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra s0 (some cr1) s1 :=
      hac.1.to_worldStep_Q hW0 (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
    exact ⟨WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp) ⟨hws0, hac.1.sp_hi⟩,
      fun _ => ptxBlockOutUnhit_of_worldEff_bufs (by intro p hp; cases hp) hac.1 hW0⟩
  | none =>
    have hac := acct_copy_step s0 hc0 hW0.1 (by rw [h1]; simp) (by rw [h1]; exact Or.inl rfl)
    rw [h1] at hac; dsimp only at hac
    obtain ⟨bw, hs1_loc, hbw_lo, hbw_hi⟩ := hac.2 rfl
    have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word bw)) := by
      rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt0 hfr0 ⊢
    rcases hargs_nb : @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        [.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "a"), .const 8#64]),
         .var .local (ofString "amount")] with _ | vnb_args
    · simp [evalListHOLFinite, hargs_nb] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
    · simp only [evalListHOLFinite, hargs_nb] at hnt0 hfr0 ⊢
      rcases hl_nb : lookupCodeHOLFinite s1.code.lookup (ofString "u256_add") vnb_args with _ | ⟨bnb, cnb, rnb⟩
      · simp [hl_nb] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
      · simp only [hl_nb] at hnt0 hfr0 ⊢
        by_cases hcz1 : s1.clock = 0
        · simp [hcz1] at hnt0
        rw [if_neg hcz1] at hnt0 hfr0 ⊢
        rcases hrun_nb : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cnb) bnb with ⟨res_nb, p_nb⟩
        have hrun_nb' : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cnb) bnb = (res_nb, p_nb) := hrun_nb
        simp only [hrun_nb] at hnt0 hfr0 ⊢
        cases res_nb with
        | none => exact absurd hfr0 not_flowingOrResumes_error
        | some cr_nb =>
          cases cr_nb with
          | timeOut => simp at hnt0
          | error | «break» | «continue» => exact absurd hfr0 not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr0 not_flowingOrResumes_finalFfi
          | exception eid ev =>
            dsimp only at hfr0 ⊢
            have hres_ex : Wave8Contracts.M18.Resumes (some (.exception eid ev)) := by
              rcases hfr0 with h | h | h | ⟨_, h⟩ | ⟨_, _, h, hne⟩ <;> try simp at h
              obtain ⟨rfl, rfl⟩ := h
              exact Or.inr ⟨eid, ev, rfl, hne⟩
            have hro := FunSpec.at_lookup ro_u256_add s1 hac.1.code vnb_args bnb cnb rnb hl_nb
              (guestInv_callEntry s1 cnb hac.1.arena.1) (by rw [hrun_nb']; simp)
            have hro' : ((evaluateHOLFiniteState (callEntryStateHOLFinite s1 cnb) bnb).2) = _ :=
              hro (by rw [hrun_nb']; exact hres_ex)
            rw [hrun_nb'] at hro'; dsimp only at hro'
            have heff_ex : WorldEff s0 (emptyLocalsHOLFinite p_nb) [] [] ["heap_ptr"] :=
              (hac.1.of_readOnly hro').locals_clock _ p_nb.clock
            have hws0 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra s0 (some (.exception eid ev))
                (emptyLocalsHOLFinite p_nb) :=
              heff_ex.to_worldStep_Q hW0 (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
            exact ⟨WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp) ⟨hws0, heff_ex.sp_hi⟩,
              fun hnx => by rcases hnx with h | h | h | ⟨_, h⟩ <;> simp at h⟩
          | returned vnb =>
            dsimp only at hnt0 hfr0 ⊢
            by_cases hsh_nb : (shapeEqHOL (shapeOfHOLExact vnb) (.comb [.one, .one, .one, .one]) &&
                shapeEqHOL (shapeOfHOLExact vnb) rnb) = true
            · simp only [hsh_nb, ↓reduceIte] at hnt0 hfr0 ⊢
              have hsh_u256 : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vnb) = true := by
                have h12 : shapeEqHOL (shapeOfHOLExact vnb) (.comb [.one, .one, .one, .one]) = true := by
                  revert hsh_nb
                  cases shapeEqHOL (shapeOfHOLExact vnb) (.comb [.one, .one, .one, .one]) <;> simp
                rcases vnb with _ | fs | _
                · simp [shapeOfHOLExact, shapeEqHOL] at h12
                · rcases fs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩⟩ <;>
                    try (simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h12; done)
                  rcases v0 with ⟨⟨_⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨_⟩⟩ | _ | _ <;>
                    rcases v2 with ⟨⟨_⟩⟩ | _ | _ <;> rcases v3 with ⟨⟨_⟩⟩ | _ | _ <;>
                    simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h12 ⊢
                · simp [shapeOfHOLExact, shapeEqHOL] at h12
              have hro := FunSpec.at_lookup ro_u256_add s1 hac.1.code vnb_args bnb cnb rnb hl_nb
                (guestInv_callEntry s1 cnb hac.1.arena.1) (by rw [hrun_nb']; simp)
              have hro' : ((evaluateHOLFiniteState (callEntryStateHOLFinite s1 cnb) bnb).2) = _ :=
                hro (by rw [hrun_nb']; exact Or.inl ⟨vnb, rfl⟩)
              rw [hrun_nb'] at hro'; dsimp only at hro'
              set s2 := setVarHOLFinite (ofString "nb") vnb { p_nb with locals := s1.locals }
              have heff2 : WorldEff s0 s2 [] [] ["heap_ptr"] :=
                (hac.1.of_readOnly hro').locals_clock _ _
              have hs2_a : s2.locals.lookup (ofString "a") = some (.val (.word bw)) := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_a,
                  show ofString "nb" ≠ ofString "a" by decide]
              have hs2_nb : s2.locals.lookup (ofString "nb") = some vnb := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              rw [evaluateHOLFiniteState_seq_line780] at hnt0 hfr0 ⊢
              rcases hst : evaluateHOLFiniteState s2
                  (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "nb"))) with ⟨rst, s3⟩
              simp only [hst] at hnt0 hfr0 ⊢
              have heff3 : WorldEff s0 s3 [] [] ["heap_ptr"] := by
                have hs3_eq : s3 = (evaluateHOLFiniteState s2
                    (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "nb")))).2 := by
                  rw [hst]
                rw [hs3_eq]
                exact worldEff_store_multi heff2 _ _ 4 (by decide)
                  (fun v hv => by
                    simp [evalHOLExact, toExact, hs2_nb] at hv
                    subst hv
                    exact flattenHOL_shape_u256 hsh_u256)
                  (fun x hx => by
                    simp [evalHOLExact, evalListHOLExact, toExact, hs2_a, panOpHOL, wordOpHOL, wordOp,
                      valueIsWord, valueWord] at hx
                    subst hx
                    have hx8 : (bw + 8#64).toNat = bw.toNat + 8 := by
                      apply BitVec.toNat_add_of_lt; change bw.toNat + 8 < 2 ^ 64; omega
                    exact ⟨by omega, Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))⟩)
              have hstep03 : WorldStepScBo (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"]
                  stdKeep NoExtra s0 rst s3 := by
                have hws0 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra s0 rst s3 :=
                  heff3.to_worldStep_Q hW0 (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
                exact ⟨WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp) ⟨hws0, heff3.sp_hi⟩,
                  fun _ => ptxBlockOutUnhit_of_worldEff_bufs (by intro p hp; cases hp) heff3 hW0⟩
              cases rst with
              | some cr_st =>
                exact hstep03.with_locals_clock id _ _
              | none =>
                dsimp only at hnt0 hfr0 ⊢
                have hWs3 : WorldOK s3 := hstep03.1.worldOK_bufs hB hW0
                have htail_step := progWStepBo_seq hB hgw
                  (progWStepBo_call0 (by intro p hp; simp at hp; subst hp; simp [acctMutBufs])
                    (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp) wkScBo_modify_state_commit)
                  (progWStepBo_return _ _ _)
                  s3 heff3.code hWs3 hnt0 hfr0
                exact WorldStepScBo.trans_flow hB hgw hW0 hstep03 (Or.inl rfl) (htail_step.with_locals_clock id _ _)
            · simp [hsh_nb] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
theorem wkScBo_set_account_balance :
    WorldKeepsScBo WorldOK (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
      (ofString "set_account_balance") := by
  have hB := validBufList_acctMutBufs
  have hgw : SafeStepGlobals ["heap_ptr", "journal_n", "scratch_ptr"] := by
    intro g hg; simp at hg; rcases hg with rfl | rfl | rfl <;> simp
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have hhl_264 : heapLimit < 2 ^ 64 := by decide
  refine ⟨_, _, _, lookup_set_account_balance, fun {F} s0 hc0 hW0 ⟨vals, hl⟩ hnt0 hres0 => ?_⟩
  have hamt_ok : ∃ vamt : ValueHOL 64,
      s0.locals.lookup (ofString "amount") = some vamt ∧
      shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vamt) = true := by
    have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "set_account_balance")
      vals _ s0.locals _ hl
    simp only [lookupCodeHOLExact, lookup_set_account_balance] at hx
    rcases vals with _ | ⟨va, _ | ⟨vamt, _ | _⟩⟩
    · simp at hx
    · simp at hx
    · rcases va with ⟨⟨wa⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hx; done)
      simp [shapeOfHOLExact, shapeEqHOL, show ofString "addr" ≠ ofString "amount" by decide] at hx
      obtain ⟨hsh_amt, hL⟩ := hx
      refine ⟨vamt, ?_, hsh_amt⟩
      have := congrFun hL (ofString "amount")
      simpa [FUPDATE, show ofString "amount" ≠ ofString "addr" by decide,
        show ofString "addr" ≠ ofString "amount" by decide] using this.symm
    · simp at hx
  obtain ⟨vamt, hs0_amt, hsh_amt⟩ := hamt_ok
  have hfr0 : FlowingOrResumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_set_account_balance)).1 :=
    Or.inr (Or.inr (Or.inr hres0))
  simp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_set_account_balance,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil] at hnt0 hfr0 ⊢
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt0 hfr0 ⊢
  rcases hargs : @evalListHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
      [.var .local (ofString "addr")] with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt0 hfr0 ⊢
    rcases hlk : lookupCodeHOLFinite s0.code.lookup (ofString "get_account") vs with _ | ⟨bga, cga, rga⟩
    · simp [hlk] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
    · simp only [hlk] at hnt0 hfr0 ⊢
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
          have hspec := FunSpec.at_lookup wkScBo_get_account s0 hc0 vs bga cga rga hlk hWent_ga hnt_ga
          simp only [ent_ga, hrun_ga] at hspec
          exact ((hspec hres_ex).mono_bufs
            (by intro p hp; simp [wsAcctBufs] at hp; rcases hp with rfl | rfl | rfl <;> simp [acctMutBufs])
            (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)).from_entry id
        | returned vga =>
          dsimp only at hnt0 hfr0 ⊢
          by_cases hsh_ga : (shapeEqHOL (shapeOfHOLExact vga) .one && shapeEqHOL (shapeOfHOLExact vga) rga) = true
          · simp only [hsh_ga, ↓reduceIte] at hnt0 hfr0 ⊢
            have hspec := FunSpec.at_lookup wkScBo_get_account s0 hc0 vs bga cga rga hlk hWent_ga hnt_ga
            simp only [ent_ga, hrun_ga] at hspec
            set sa := setVarHOLFinite (ofString "a") vga { p_ga with locals := s0.locals }
            have hstep_ga : WorldStepScBo (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"]
                stdKeep NoExtra s0 none sa :=
              ((hspec (Or.inl ⟨vga, rfl⟩)).mono_bufs
                (by intro p hp; simp [wsAcctBufs] at hp; rcases hp with rfl | rfl | rfl <;> simp [acctMutBufs])
                (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)).from_entry
                  (fun _ => Or.inr (Or.inr (Or.inr ⟨vga, rfl⟩)))
            have hWsa : WorldOK sa := hstep_ga.1.worldOK_bufs hB hW0
            have hsa_code : sa.code = originalRuntimeCode := hmeta_ga.trans hc0
            have hsa_amt : sa.locals.lookup (ofString "amount") = some vamt := by
              simp [sa, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs0_amt,
                show ofString "a" ≠ ofString "amount" by decide]
            let sabTail : ProgHOL 64 :=
              .seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                (.seq (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount")))
                  (.seq (.call (some (none, none)) (ofString "modify_state_commit")
                    [.var .local (ofString "addr"), .var .local (ofString "a")])
                    (.return (.const 0#64))))
            have hcont_step : WorldStepScBo (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"]
                stdKeep NoExtra sa (evaluateHOLFiniteState sa sabTail).1 (evaluateHOLFiniteState sa sabTail).2 := by
              dsimp only [sabTail] at hnt0 hfr0 ⊢
              rw [evaluateHOLFiniteState_seq_assoc] at hnt0 hfr0 ⊢
              rw [evaluateHOLFiniteState_seq_line780] at hnt0 hfr0 ⊢
              have hm_step : WorldStepScBo (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"]
                  stdKeep NoExtra sa
                  (evaluateHOLFiniteState sa
                    (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                      (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount"))))).1
                  (evaluateHOLFiniteState sa
                    (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                      (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount"))))).2 := by
                have hnt_m : (evaluateHOLFiniteState sa
                    (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                      (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount"))))).1 ≠ some .timeOut := by
                  rcases hm : evaluateHOLFiniteState sa _ with ⟨rm, sm⟩
                  rw [hm] at hnt0; cases rm with | none => simp | some cm => cases cm <;> simp at hnt0 ⊢
                have hfr_m : FlowingOrResumes (evaluateHOLFiniteState sa
                    (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                      (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount"))))).1 := by
                  rcases hm : evaluateHOLFiniteState sa _ with ⟨rm, sm⟩
                  rw [hm] at hfr0; cases rm with | none => exact Or.inl rfl | some cm => exact hfr0
                rw [evaluateHOLFiniteState_seq_line780] at hnt_m hfr_m ⊢
                rcases h1 : evaluateHOLFiniteState sa
                    (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy")
                      [.var .local (ofString "a")]) with ⟨r1, s1⟩
                simp only [h1] at hnt_m hfr_m ⊢
                cases r1 with
                | some cr1 =>
                  have hac := acct_copy_step sa hsa_code hWsa.1 (by rw [h1]; exact hnt_m) (by rw [h1]; exact hfr_m)
                  rw [h1] at hac
                  have hws0 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra sa (some cr1) s1 :=
                    hac.1.to_worldStep_Q hWsa (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
                  exact ⟨WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp) ⟨hws0, hac.1.sp_hi⟩,
                    fun _ => ptxBlockOutUnhit_of_worldEff_bufs (by intro p hp; cases hp) hac.1 hWsa⟩
                | none =>
                  dsimp only at hnt_m hfr_m ⊢
                  have hac := acct_copy_step sa hsa_code hWsa.1 (by rw [h1]; simp) (by rw [h1]; exact Or.inl rfl)
                  rw [h1] at hac; dsimp only at hac
                  obtain ⟨bw, hs1_loc, hbw_lo, hbw_hi⟩ := hac.2 rfl
                  have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word bw)) := by
                    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
                  have hs1_amt : s1.locals.lookup (ofString "amount") = some vamt := by
                    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hsa_amt,
                      show ofString "a" ≠ ofString "amount" by decide]
                  have heff2 : WorldEff sa
                      (evaluateHOLFiniteState s1
                        (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount")))).2
                      [] [] ["heap_ptr"] :=
                    worldEff_store_multi hac.1 _ _ 4 (by decide)
                      (fun v hv => by simp [evalHOLExact, toExact, hs1_amt] at hv; subst hv; exact flattenHOL_shape_u256 hsh_amt)
                      (fun x hx => by
                        simp [evalHOLExact, evalListHOLExact, toExact, hs1_a, panOpHOL, wordOpHOL, wordOp,
                          valueIsWord, valueWord] at hx
                        subst hx
                        have hx8 : (bw + 8#64).toNat = bw.toNat + 8 := by
                          apply BitVec.toNat_add_of_lt; change bw.toNat + 8 < 2 ^ 64; omega
                        exact ⟨by omega, Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))⟩)
                  have hws0 : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra sa
                      (evaluateHOLFiniteState s1
                        (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount")))).1
                      (evaluateHOLFiniteState s1
                        (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount")))).2 :=
                    heff2.to_worldStep_Q hWsa (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial)
                  exact ⟨WorldStepSc.mono_bufs (fun _ h => by cases h) (by simp) ⟨hws0, heff2.sp_hi⟩,
                    fun _ => ptxBlockOutUnhit_of_worldEff_bufs (by intro p hp; cases hp) heff2 hWsa⟩
              have hm_code := (PanRunBounded.evaluateHOLFiniteState_metadata sa
                (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                  (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount"))))).1
              rcases hm : evaluateHOLFiniteState sa
                  (.seq (.call (some (some (.local, ofString "a"), none)) (ofString "acct_copy") [.var .local (ofString "a")])
                    (.store (.op .add [.var .local (ofString "a"), .const 8#64]) (.var .local (ofString "amount")))) with ⟨rm, sm⟩
              simp only [hm] at hm_step hm_code hnt0 hfr0 ⊢
              cases rm with
              | some crm => exact hm_step
              | none =>
                dsimp only at hnt0 hfr0 ⊢
                have hWsm : WorldOK sm := hm_step.1.worldOK_bufs hB hWsa
                have htail := progWStepBo_seq hB hgw
                  (progWStepBo_call0 (by intro p hp; simp at hp; subst hp; simp [acctMutBufs])
                    (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp) wkScBo_modify_state_commit)
                  (progWStepBo_return _ _ _)
                  sm (hm_code.trans hsa_code) hWsm hnt0 hfr0
                exact WorldStepScBo.trans_flow hB hgw hWsa hm_step (Or.inl rfl) htail
            exact WorldStepScBo.trans_flow hB hgw hW0 hstep_ga (Or.inl rfl) (hcont_step.with_locals_clock id _ _)
          · simp [hsh_ga] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
/-- Any aligned word whose cell hits an allocated interval `i` is preserved by a
step whose memory effects a `FrameOutside` frame confines to the fresh heap
growth above the old `heap_ptr` (the keep-set is the zero-length scratch
window, which no aligned cell can hit). Heap-allocated `i` lies below the old
`heap_ptr` and alignment keeps the boundary cell out of the growth; scratch-
allocated `i` lies at or above `scratchStart = heapLimit`, which bounds the
new `heap_ptr` from above, so the growth cannot reach it either. -/
private theorem ivlUnhit_of_freshFrame {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) (hArd : ArenaReady post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hfr : FrameOutside s post [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    {i : Ivl} (hal : Allocated s i) :
    InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post i := by
  have hhp_s : globN s "heap_ptr" ≤ heapLimit := hA.2.1
  have hhp8 : globN s "heap_ptr" % 8 = 0 := hA.2.2.2.2.2.1
  have hsp8 : globN s "scratch_ptr" % 8 = 0 := hA.2.2.2.2.2.2.2.1
  have hsp_lo : scratchStart ≤ globN s "scratch_ptr" :=
    le_trans hA.2.2.1 hA.2.2.2.1
  have hsp_hi : globN s "scratch_ptr" ≤ scratchEnd := hA.2.2.2.2.1
  have hhp_p : globN post "heap_ptr" ≤ heapLimit := hArd.2.2.1
  have hhp_p8 : globN post "heap_ptr" % 8 = 0 := hArd.2.2.2.2.2.2.1
  have hls : heapLimit = scratchStart := rfl
  intro a ha8 hhit
  obtain ⟨hh1, hh2⟩ := hhit
  have hkeep : ∀ j ∈ [((globN s "scratch_ptr", 0) : Ivl)], ¬ CellHits a.toNat j := by
    intro j hj
    have hje : j = (globN s "scratch_ptr", 0) := by simpa using hj
    subst hje
    intro hc
    obtain ⟨hc1, hc2⟩ := hc
    omega
  have hfresh : ¬ CellHits a.toNat
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
    intro ⟨hc1, hc2⟩
    rcases hal with hins | hins
    · obtain ⟨hlo, hhi⟩ := hins
      omega
    · obtain ⟨hlo, hhi⟩ := hins
      omega
  exact hfr a hkeep hfresh
theorem wkScBo_state_fresh_tx :
    WorldKeepsScBo WorldOK (fun _ => [])
      ["heap_ptr", "journal_n", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "state_fresh_tx") := by
  refine ⟨_, _, _, WkBal.lookup_state_fresh_tx, fun {F} s hcode hWOK hparams hnt hres => ?_⟩
  have hws : WorldStep (fun _ => []) ["heap_ptr", "journal_n", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])] NoExtra
      s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_state_fresh_tx)).1
        (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_state_fresh_tx)).2 := by
    obtain ⟨ps, body, ret, hl, hrun⟩ := WkBal.wk_state_fresh_tx
    have heq := hl.symm.trans WkBal.lookup_state_fresh_tx
    injection heq with heq'; obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq'
    exact hrun s hcode hWOK hparams hnt hres
  have hsp : globN (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_state_fresh_tx)).2 "scratch_ptr" =
      globN s "scratch_ptr" :=
    globN_eq_of_lookup (hws.2.2.1 (ofString "scratch_ptr") (by decide))
  refine ⟨⟨hws, by omega⟩, fun _ => ?_⟩
  have hAR0 : ArenaReady s := hWOK.1
  have hbody_eq : sourceFnBody Guest.Software.guestFn_state_fresh_tx =
      .seq (.call (some (some (.global, ofString "ts"), none)) (ofString "alloc") [.const 72])
      (.seq (.store (.op .add [.var .global (ofString "ts"), .const 0]) (.var .global (ofString "bs")))
      (.decCall (ofString "t") .one (ofString "htab_new") [.const 20, .const 64]
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 8]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 20, .const 64])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 16]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 52, .const 64])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 24]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 20, .const 16])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 32]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 52, .const 16])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 40]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 32, .const 16])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 48]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 20, .const 16])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 56]) (.var .local (ofString "t")))
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 52, .const 16])
        (.seq (.store (.op .add [.var .global (ofString "ts"), .const 64]) (.var .local (ofString "t")))
        (.seq (.assign .global (ofString "journal_n") (.const 0))
              (.return (.const 0)))))))))))))))))))) := rfl
  have hnt' := hnt; have hres' := hres
  rw [hbody_eq] at hnt' hres'
  obtain ⟨pw, qw, s0a, hpw_eq, hqw_eq, hs0a_hp, _, hpw8, hAR0a, hs0a_m, _, _, _,
      hsp0a, _, hts0a, _, hnt0a, hres0a, heq0a⟩ :=
    WkBal.seq_call_alloc_global_resumes s (ofString "ts") 72 _ hAR0
      ⟨by decide, by decide, by decide⟩ hnt' hres'
  have hqw_72 : qw.toNat = pw.toNat + 72 := by
    have h72 : (72 : BitVec 64).toNat = 72 := rfl
    rw [h72] at hqw_eq; omega
  have hpw_lo : sourceBase ≤ pw.toNat := by rw [hpw_eq]; exact hAR0.2.1
  have hpw_hi : pw.toNat + 72 ≤ heapLimit := by have := hAR0a.2.2.1; omega
  obtain ⟨bsw, hbsw_lk⟩ := hAR0a.2.2.2.2.2.2.2.2.2 "bs" (by decide)
  obtain ⟨heq0b, hAR0b, _, _, _, _, _, _, hfr0b⟩ :=
    WkBal.seq_store_ts_slot s0a pw 0 bsw (.var .global (ofString "bs")) _ hAR0a hts0a
      hpw_lo hpw_hi hpw8 (by decide) (by decide) hbsw_lk
  set s0 : PanSemStateFiniteExact 64 F :=
    { s0a with memory := fun a => if a = pw + 0 then .word bsw else s0a.memory a }
  rw [heq0b] at hnt0a hres0a
  have hhp0 : globN s0 "heap_ptr" = pw.toNat + 72 := by change globN s0a "heap_ptr" = pw.toNat + 72; omega
  have hsp0 : globN s0 "scratch_ptr" = globN s "scratch_ptr" := hsp0a
  have hfr_s_s0 : FrameOutside s s0 [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN s0 "heap_ptr" - globN s "heap_ptr") := by
    intro a _ hnhf
    exact (hfr0b a (fun _ h => by cases h) (fun ⟨c1, c2⟩ => by
      dsimp only at c1 c2; exact hnhf ⟨by dsimp only; omega, by dsimp only; omega⟩)).trans (by rw [hs0a_m])
  obtain ⟨_, s1, _, _, hAR1, _, hsp1, _, _, _, _, _, _, _, hfr1, _, hg1, hnt1, hres1, _, heq1_2⟩ :=
    WkBal.decCall_htab_new_store_ts_slot s0 pw 8 20 64 _ hAR0b (by omega) hpw_lo hpw8
      (by decide) (by decide) hts0a (by decide) (by decide) hnt0a hres0a
  have hts1 : s1.globals.lookup (ofString "ts") = some (.val (.word pw)) := (hg1 (ofString "ts") (by decide)).symm.trans hts0a
  have hfr_s_s1 := WkBal.frameOutside_collapse_pw_sp s s0 s1 pw.toNat (by omega) (by omega) (by omega) hfr_s_s0 (by rw [hsp0] at hfr1; exact hfr1)
  obtain ⟨_, s2, _, _, hAR2, _, hsp2, _, _, _, _, _, _, _, hfr2, _, hg2, hnt2, hres2, heq2⟩ :=
    WkBal.seq_htab_new_store_ts_slot s1 pw 16 20 64 _ hAR1 (by omega) hpw_lo hpw8 (by decide) (by decide) hts1 (by decide) (by decide) hnt1 hres1
  have hts2 : s2.globals.lookup (ofString "ts") = some (.val (.word pw)) := (hg2 (ofString "ts") (by decide)).symm.trans hts1
  have hfr_s_s2 := WkBal.frameOutside_collapse_pw_sp s s1 s2 pw.toNat (by omega) (by omega) (by omega) hfr_s_s1 (by rw [hsp1, hsp0] at hfr2; exact hfr2)
  obtain ⟨_, s3, _, _, hAR3, _, hsp3, _, _, _, _, _, _, _, hfr3, _, hg3, hnt3, hres3, heq3⟩ :=
    WkBal.seq_htab_new_store_ts_slot s2 pw 24 52 64 _ hAR2 (by omega) hpw_lo hpw8 (by decide) (by decide) hts2 (by decide) (by decide) hnt2 hres2
  have hts3 : s3.globals.lookup (ofString "ts") = some (.val (.word pw)) := (hg3 (ofString "ts") (by decide)).symm.trans hts2
  have hfr_s_s3 := WkBal.frameOutside_collapse_pw_sp s s2 s3 pw.toNat (by omega) (by omega) (by omega) hfr_s_s2 (by rw [hsp2, hsp1, hsp0] at hfr3; exact hfr3)
  obtain ⟨_, s4, _, _, hAR4, _, hsp4, _, _, _, _, _, _, _, hfr4, _, hg4, hnt4, hres4, heq4⟩ :=
    WkBal.seq_htab_new_store_ts_slot s3 pw 32 20 16 _ hAR3 (by omega) hpw_lo hpw8 (by decide) (by decide) hts3 (by decide) (by decide) hnt3 hres3
  have hts4 : s4.globals.lookup (ofString "ts") = some (.val (.word pw)) := (hg4 (ofString "ts") (by decide)).symm.trans hts3
  have hfr_s_s4 := WkBal.frameOutside_collapse_pw_sp s s3 s4 pw.toNat (by omega) (by omega) (by omega) hfr_s_s3 (by rw [hsp3, hsp2, hsp1, hsp0] at hfr4; exact hfr4)
  obtain ⟨_, s5, _, _, hAR5, _, hsp5, _, _, _, _, _, _, _, hfr5, _, hg5, hnt5, hres5, heq5⟩ :=
    WkBal.seq_htab_new_store_ts_slot s4 pw 40 52 16 _ hAR4 (by omega) hpw_lo hpw8 (by decide) (by decide) hts4 (by decide) (by decide) hnt4 hres4
  have hts5 : s5.globals.lookup (ofString "ts") = some (.val (.word pw)) := (hg5 (ofString "ts") (by decide)).symm.trans hts4
  have hfr_s_s5 := WkBal.frameOutside_collapse_pw_sp s s4 s5 pw.toNat (by omega) (by omega) (by omega) hfr_s_s4 (by rw [hsp4, hsp3, hsp2, hsp1, hsp0] at hfr5; exact hfr5)
  obtain ⟨_, s6, _, _, hAR6, _, hsp6, _, _, _, _, _, _, _, hfr6, _, hg6, hnt6, hres6, heq6⟩ :=
    WkBal.seq_htab_new_store_ts_slot s5 pw 48 32 16 _ hAR5 (by omega) hpw_lo hpw8 (by decide) (by decide) hts5 (by decide) (by decide) hnt5 hres5
  have hts6 : s6.globals.lookup (ofString "ts") = some (.val (.word pw)) := (hg6 (ofString "ts") (by decide)).symm.trans hts5
  have hfr_s_s6 := WkBal.frameOutside_collapse_pw_sp s s5 s6 pw.toNat (by omega) (by omega) (by omega) hfr_s_s5 (by rw [hsp5, hsp4, hsp3, hsp2, hsp1, hsp0] at hfr6; exact hfr6)
  obtain ⟨_, s7, _, _, hAR7, _, hsp7, _, _, _, _, _, _, _, hfr7, _, hg7, hnt7, hres7, heq7⟩ :=
    WkBal.seq_htab_new_store_ts_slot s6 pw 56 20 16 _ hAR6 (by omega) hpw_lo hpw8 (by decide) (by decide) hts6 (by decide) (by decide) hnt6 hres6
  have hts7 : s7.globals.lookup (ofString "ts") = some (.val (.word pw)) := (hg7 (ofString "ts") (by decide)).symm.trans hts6
  have hfr_s_s7 := WkBal.frameOutside_collapse_pw_sp s s6 s7 pw.toNat (by omega) (by omega) (by omega) hfr_s_s6 (by rw [hsp6, hsp5, hsp4, hsp3, hsp2, hsp1, hsp0] at hfr7; exact hfr7)
  obtain ⟨_, s8, _, _, hAR8, _, hsp8, _, _, _, _, _, _, _, hfr8, _, _, _, _, heq8⟩ :=
    WkBal.seq_htab_new_store_ts_slot s7 pw 64 52 16 _ hAR7 (by omega) hpw_lo hpw8 (by decide) (by decide) hts7 (by decide) (by decide) hnt7 hres7
  have hfr_s_s8 := WkBal.frameOutside_collapse_pw_sp s s7 s8 pw.toNat (by omega) (by omega) (by omega) hfr_s_s7 (by rw [hsp7, hsp6, hsp5, hsp4, hsp3, hsp2, hsp1, hsp0] at hfr8; exact hfr8)
  obtain ⟨heq9, _, hs9_m, _, _, hs9_hp, _, _, _, _⟩ :=
    WkBal.seq_assign_global_zero_return_zero s8 (ofString "journal_n") hAR8 ⟨"journal_n", by decide, rfl⟩ ⟨by decide, by decide, by decide⟩
  set inner_post := emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "journal_n") (.val (.word 0)) s8)
  have hchain2_2 := congrArg Prod.snd (by rw [heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9] :
    evaluateHOLFiniteState s1 _ = (some (.returned (.val (.word 0))), inner_post))
  dsimp only at hchain2_2
  have hpost_eq : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_state_fresh_tx)).2 =
      { inner_post with locals := HolFiniteMapExact.resVarEq inner_post.locals (ofString "t", s0.locals.lookup (ofString "t")) } := by
    rw [hbody_eq, heq0a, heq0b]
    exact heq1_2.trans (by rw [hchain2_2])
  obtain ⟨_, S', hWT'⟩ := hWOK
  obtain ⟨Nd', hWT⟩ := (worldTyped_iff_with s S').1 hWT'
  have hfr_09 : FrameOutside s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_state_fresh_tx)).2
      [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_state_fresh_tx)).2 "heap_ptr" - globN s "heap_ptr") := by
    rw [hpost_eq]
    intro a hk0 hnhf; change inner_post.memory a = s.memory a; rw [hs9_m]
    exact hfr_s_s8 a hk0 (fun ⟨c1, c2⟩ => by
      dsimp only at c1 c2
      exact hnhf ⟨by dsimp only; omega, by
        dsimp only
        have hip_hp : globN inner_post "heap_ptr" = globN s8 "heap_ptr" := hs9_hp
        change a.toNat < globN s "heap_ptr" + (globN inner_post "heap_ptr" - globN s "heap_ptr")
        omega⟩)
  exact ptxBlockOutUnhit_of_nonempty fun i hi hpos =>
    ivlUnhit_of_freshFrame hAR0.2 hws.1 hws.2.1 hfr_09 (blockOut_allocated_words hWT hi hpos).2.1
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open private txEnc_wordsOK_wordAt_memW txEnc_wordAt_memW_below_hp txEnc_wordsOK_below_hp
  accessListPayloadSumPure_congr authListPayloadSumPure_congr
  eval_decCall_tx_encode_bound txEncodeBoundPure
  accessListPayloadSumPure authListPayloadSumPure txEnc_eval_load_word_below_hp
  txEnc_eval_load_u256_below_hp txEnc_seq_non_timeout
  u256ByteLengthPure_bounds
  eval_call_local_tx_put_u256 eval_call_local_tx_put_to
  eval_call_local_tx_put_access_list eval_call_local_tx_put_blob_hashes
  eval_call_local_tx_put_authorizations
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeTransaction
def RetTxSliceBounded : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post _ _ =>
    PtxBlockOutUnhit s post ∧
    ∀ v, r = some (.returned v) → ∃ a b : BitVec 64,
      v = .rStruct [.val (.word a), .val (.word b)] ∧
      Inside (a.toNat, b.toNat) sourceBase (globN post "heap_ptr") ∧
      a.toNat < 2 ^ 40 ∧ b.toNat < 2 ^ 40
theorem ptxBlockOutUnhit_of_heapByteEff {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {R : List Ivl} {gw : List String}
    (hW : WorldOK s)
    (heff : HeapByteEff s post R gw)
    (hR : ∀ j ∈ R, ∀ i ∈ blockOutObjects s, Disj i j) :
    PtxBlockOutUnhit s post := by
  have hAs : ArenaReady s := hW.1
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  apply ptxBlockOutUnhit_of_nonempty
  intro i hi hipos a ha hh
  obtain ⟨_, hal, ha1, ha2⟩ := blockOut_allocated_words hWT0 hi hipos
  by_contra hmem
  have hh' : i.1 ≤ a.toNat ∧ a.toNat + 8 ≤ i.1 + i.2 := by
    unfold CellHits at hh; omega
  have exclude : ∀ j, Disj i j → ¬ CellHitsPos a.toNat j := by
    intro j hd hc
    unfold Disj at hd
    simp only [CellHitsPos, R13Shards.Keccak256.CellHitsPos, CellHits] at hc
    rcases hd with hz | hz | hl | hr <;> omega
  rcases heff.cell_frame _ hmem with ⟨j, hj, hc⟩ | hc | hc
  · exact exclude j (hR j hj i hi) hc
  · apply exclude (freeGap s) _ hc
    unfold Allocated Inside at hal
    unfold Disj freeGap
    rcases hal with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
    · exact Or.inr (Or.inr (Or.inl (by
        rcases hAs.2 with ⟨_, hp, hf, hsc, _⟩
        have sep : heapLimit ≤ InitE.scratchStart := by decide
        dsimp only; omega)))
    · exact Or.inr (Or.inr (Or.inr (by
        rcases hAs.2 with ⟨_, hp, hf, hsc, _⟩
        dsimp only; omega)))
  · apply exclude (heapFree s) _ hc
    unfold Allocated Inside at hal
    unfold Disj heapFree
    rcases hal with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
    · exact Or.inr (Or.inr (Or.inl hhi))
    · exact Or.inr (Or.inr (Or.inr (by
        rcases hAs.2 with ⟨_, hp, hf, hsc, _⟩
        have sep : heapLimit ≤ InitE.scratchStart := by decide
        dsimp only; omega)))
def TxEncBoundedOut {F : Type} (s0 : PanSemStateFiniteExact 64 F) (Rl : List Ivl) (gw : List String)
    (out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F) : Prop :=
  HeapByteEff s0 out.2 Rl gw ∧
  (∀ v, out.1 = some (.returned v) → ∃ a b : BitVec 64,
    v = .rStruct [.val (.word a), .val (.word b)] ∧
    Inside (a.toNat, b.toNat) sourceBase (globN out.2 "heap_ptr") ∧
    a.toNat < 2 ^ 40 ∧ b.toNat < 2 ^ 40)
theorem txEnc_eff_ret_of_eq_resVar {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {r' : Option (PanSemResultExact 64)} {q : PanSemStateFiniteExact 64 F}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {Rl : List Ivl} {gw : List String}
    (heq : evaluateHOLFiniteState s p = (r', { q with locals := L }))
    (hq : TxEncBoundedOut s0 Rl gw (r', q)) :
    TxEncBoundedOut s0 Rl gw (evaluateHOLFiniteState s p) := by
  rw [heq]
  exact ⟨hq.1.locals_clock L q.clock, hq.2⟩
theorem txEnc_trailer_bounded_resumes {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {buf bnd bodyw pw tw : BitVec 64}
    (heff0 : HeapByteEff s0 s Rl gw)
    (hRl_mem : (buf.toNat, bnd.toNat) ∈ Rl)
    (hbuf_lo : sourceBase ≤ buf.toNat)
    (hbnd_ge10 : 10 ≤ bnd.toNat)
    (hbuf_bnd_le_hp : buf.toNat + bnd.toNat ≤ globN s "heap_ptr")
    (hbuf_bnd_le_hl : buf.toNat + bnd.toNat ≤ heapLimit)
    (hbodyw_nat : bodyw.toNat = buf.toNat + 10)
    (hp_ge_body : bodyw.toNat ≤ pw.toNat)
    (hp_le_end : pw.toNat ≤ buf.toNat + bnd.toNat)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hbody : s.locals.lookup (ofString "body") = some (.val (.word bodyw)))
    (ht : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hnt : (evaluateHOLFiniteState s
      (.dec (ofString "payload_len") .one
        (.op .sub [.var .local (ofString "p"), .var .local (ofString "body")])
        (.decCall (ofString "hl") .one (ofString "rlp_list_header_len")
          [.var .local (ofString "payload_len")]
          (.dec (ofString "start") .one
            (.op .sub [.var .local (ofString "body"), .var .local (ofString "hl")])
            (.seq
              (.call (some (none, none)) (ofString "rlp_encode_list_header")
                [.var .local (ofString "start"), .var .local (ofString "payload_len")])
              (.seq
                (.ite (.cmp .notEqual (.var .local (ofString "t")) (.const 0#64))
                  (.seq
                    (.assign .local (ofString "start")
                      (.op .sub [.var .local (ofString "start"), .const 1#64]))
                    (.storeByte (.var .local (ofString "start")) (.var .local (ofString "t"))))
                  .skip)
                (.return (.rstruct [
                  .var .local (ofString "start"),
                  .op .sub [.var .local (ofString "p"), .var .local (ofString "start")]])))))))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.dec (ofString "payload_len") .one
        (.op .sub [.var .local (ofString "p"), .var .local (ofString "body")])
        (.decCall (ofString "hl") .one (ofString "rlp_list_header_len")
          [.var .local (ofString "payload_len")]
          (.dec (ofString "start") .one
            (.op .sub [.var .local (ofString "body"), .var .local (ofString "hl")])
            (.seq
              (.call (some (none, none)) (ofString "rlp_encode_list_header")
                [.var .local (ofString "start"), .var .local (ofString "payload_len")])
              (.seq
                (.ite (.cmp .notEqual (.var .local (ofString "t")) (.const 0#64))
                  (.seq
                    (.assign .local (ofString "start")
                      (.op .sub [.var .local (ofString "start"), .const 1#64]))
                    (.storeByte (.var .local (ofString "start")) (.var .local (ofString "t"))))
                  .skip)
                (.return (.rstruct [
                  .var .local (ofString "start"),
                  .op .sub [.var .local (ofString "p"), .var .local (ofString "start")]])))))))).1) :
    TxEncBoundedOut s0 Rl gw (evaluateHOLFiniteState s
      (.dec (ofString "payload_len") .one
        (.op .sub [.var .local (ofString "p"), .var .local (ofString "body")])
        (.decCall (ofString "hl") .one (ofString "rlp_list_header_len")
          [.var .local (ofString "payload_len")]
          (.dec (ofString "start") .one
            (.op .sub [.var .local (ofString "body"), .var .local (ofString "hl")])
            (.seq
              (.call (some (none, none)) (ofString "rlp_encode_list_header")
                [.var .local (ofString "start"), .var .local (ofString "payload_len")])
              (.seq
                (.ite (.cmp .notEqual (.var .local (ofString "t")) (.const 0#64))
                  (.seq
                    (.assign .local (ofString "start")
                      (.op .sub [.var .local (ofString "start"), .const 1#64]))
                    (.storeByte (.var .local (ofString "start")) (.var .local (ofString "t"))))
                  .skip)
                (.return (.rstruct [
                  .var .local (ofString "start"),
                  .op .sub [.var .local (ofString "p"), .var .local (ofString "start")]])))))))) := by
  have hhl_lt40 : heapLimit < 2 ^ 40 := by rw [heapLimit_val]; decide
  let plw : BitVec 64 := pw - bodyw
  have hplw_nat : plw.toNat = pw.toNat - bodyw.toNat := BitVec.toNat_sub_of_le hp_ge_body
  have hev_pl : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .sub [.var .local (ofString "p"), .var .local (ofString "body")]) =
      some (.val (.word plw)) := by
    simp [evalHOLExact, evalListHOLExact, hp, hbody, wordOpHOL, wordOp, valueIsWord, valueWord, plw]
  have hsh_pl : shapeEqHOL .one (shapeOfHOLExact (.val (.word plw) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  have hdec_pl : ∀ cont_pl : ProgHOL 64,
      evaluateHOLFiniteState s
        (.dec (ofString "payload_len") .one
          (.op .sub [.var .local (ofString "p"), .var .local (ofString "body")]) cont_pl) =
      ((evaluateHOLFiniteState (setVarHOLFinite (ofString "payload_len") (.val (.word plw)) s) cont_pl).1,
       { (evaluateHOLFiniteState (setVarHOLFinite (ofString "payload_len") (.val (.word plw)) s) cont_pl).2 with
         locals := (evaluateHOLFiniteState (setVarHOLFinite (ofString "payload_len") (.val (.word plw)) s) cont_pl).2.locals.resVarEq
           (ofString "payload_len", s.locals.lookup (ofString "payload_len")) }) := by
    intro cont_pl; rw [evaluateHOLFiniteState_dec_total]; dsimp only; rw [hev_pl]; dsimp only; rw [if_pos hsh_pl]
  rw [hdec_pl] at hnt hres; dsimp only at hnt hres
  apply txEnc_eff_ret_of_eq_resVar (hdec_pl _)
  let u1 := setVarHOLFinite (ofString "payload_len") (.val (.word plw)) s
  have heff_u1 : HeapByteEff s0 u1 Rl gw := heff0.locals_clock u1.locals u1.clock
  have hu1_pl : u1.locals.lookup (ofString "payload_len") = some (.val (.word plw)) := by
    simp [u1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hu1_p : u1.locals.lookup (ofString "p") = some (.val (.word pw)) := by
    simp [u1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp,
      show ofString "payload_len" ≠ ofString "p" from M13.mls_ne rfl]
  have hu1_body : u1.locals.lookup (ofString "body") = some (.val (.word bodyw)) := by
    simp [u1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hbody,
      show ofString "payload_len" ≠ ofString "body" from M13.mls_ne rfl]
  have hu1_t : u1.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [u1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht,
      show ofString "payload_len" ≠ ofString "t" from M13.mls_ne rfl]
  obtain ⟨u2, hhl_nat, hhl_ge1, hhl_le9, hu2_glob, _, hu2_loc, heff_u1_u2, hnt_u2, hdc_hl⟩ :=
    eval_decCall_rlp_list_header_len u1 "hl" (.var .local (ofString "payload_len")) plw _ Rl gw
      heff_u1.arena.1.code heff_u1.arena (by simp [evalHOLExact, hu1_pl]) hnt
  rw [hdc_hl] at hres; dsimp only at hres
  apply txEnc_eff_ret_of_eq_resVar hdc_hl
  let hlw := BitVec.ofNat 64 (rlpHeaderLenPure plw.toNat)
  have heff_u2 : HeapByteEff s0 u2 Rl gw := heff_u1.trans heff_u1_u2
  have hu2_hl : u2.locals.lookup (ofString "hl") = some (.val (.word hlw)) := by
    rw [hu2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hlw]
  have hu2_pl : u2.locals.lookup (ofString "payload_len") = some (.val (.word plw)) := by
    rw [hu2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hu1_pl,
      show ofString "hl" ≠ ofString "payload_len" from M13.mls_ne rfl]
  have hu2_p : u2.locals.lookup (ofString "p") = some (.val (.word pw)) := by
    rw [hu2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hu1_p,
      show ofString "hl" ≠ ofString "p" from M13.mls_ne rfl]
  have hu2_body : u2.locals.lookup (ofString "body") = some (.val (.word bodyw)) := by
    rw [hu2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hu1_body,
      show ofString "hl" ≠ ofString "body" from M13.mls_ne rfl]
  have hu2_t : u2.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    rw [hu2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hu1_t,
      show ofString "hl" ≠ ofString "t" from M13.mls_ne rfl]
  let startw : BitVec 64 := bodyw - hlw
  have hhl_le_body : hlw.toNat ≤ bodyw.toNat := by have : hlw.toNat ≤ 9 := hhl_le9; omega
  have hstartw_nat : startw.toNat = bodyw.toNat - hlw.toNat := BitVec.toNat_sub_of_le hhl_le_body
  have hev_st : @evalHOLExact 64 F _ u2.toExact (fun a => Classical.propDecidable (u2.memaddrs a))
      (.op .sub [.var .local (ofString "body"), .var .local (ofString "hl")]) =
      some (.val (.word startw)) := by
    simp [evalHOLExact, evalListHOLExact, hu2_body, hu2_hl, wordOpHOL, wordOp, valueIsWord, valueWord, startw]
  have hsh_st : shapeEqHOL .one (shapeOfHOLExact (.val (.word startw) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  have hdec_st : ∀ cont_st : ProgHOL 64,
      evaluateHOLFiniteState u2
        (.dec (ofString "start") .one
          (.op .sub [.var .local (ofString "body"), .var .local (ofString "hl")]) cont_st) =
      ((evaluateHOLFiniteState (setVarHOLFinite (ofString "start") (.val (.word startw)) u2) cont_st).1,
       { (evaluateHOLFiniteState (setVarHOLFinite (ofString "start") (.val (.word startw)) u2) cont_st).2 with
         locals := (evaluateHOLFiniteState (setVarHOLFinite (ofString "start") (.val (.word startw)) u2) cont_st).2.locals.resVarEq
           (ofString "start", u2.locals.lookup (ofString "start")) }) := by
    intro cont_st; rw [evaluateHOLFiniteState_dec_total]; dsimp only; rw [hev_st]; dsimp only; rw [if_pos hsh_st]
  rw [hdec_st] at hnt_u2 hres; dsimp only at hnt_u2 hres
  apply txEnc_eff_ret_of_eq_resVar (hdec_st _)
  let u3 := setVarHOLFinite (ofString "start") (.val (.word startw)) u2
  have heff_u3 : HeapByteEff s0 u3 Rl gw := heff_u2.locals_clock u3.locals u3.clock
  have hu3_st : u3.locals.lookup (ofString "start") = some (.val (.word startw)) := by
    simp [u3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hu3_pl : u3.locals.lookup (ofString "payload_len") = some (.val (.word plw)) := by
    simp [u3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2_pl,
      show ofString "start" ≠ ofString "payload_len" from M13.mls_ne rfl]
  have hu3_p : u3.locals.lookup (ofString "p") = some (.val (.word pw)) := by
    simp [u3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2_p,
      show ofString "start" ≠ ofString "p" from M13.mls_ne rfl]
  have hu3_t : u3.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [u3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2_t,
      show ofString "start" ≠ ofString "t" from M13.mls_ne rfl]
  have hnt_elh := txEnc_seq_non_timeout u3 _ _ hnt_u2
  have hc_elh := eval_call_rlp_encode_list_header u3
    (.var .local (ofString "start")) (.var .local (ofString "payload_len"))
    startw plw Rl gw heff_u3.arena.1.code heff_u3.arena
    (by simp [evalHOLExact, hu3_st]) (by simp [evalHOLExact, hu3_pl])
    ⟨(buf.toNat, bnd.toNat), hRl_mem, by
      have hhle : hlw.toNat ≤ 9 := hhl_le9
      have hhge : 1 ≤ hlw.toNat := hhl_ge1
      have hheq : hlw.toNat = rlpHeaderLenPure plw.toNat := hhl_nat
      exact ⟨by omega, by omega⟩⟩
    hnt_elh
  dsimp only at hc_elh
  rcases helh : evaluateHOLFiniteState u3
    (.call (some (none, none)) (ofString "rlp_encode_list_header")
      [.var .local (ofString "start"), .var .local (ofString "payload_len")]) with ⟨relh, u4⟩
  rw [helh] at hc_elh; dsimp only at hc_elh
  unfold TxEncBoundedOut
  rw [evaluateHOLFiniteState_seq_line780, helh] at hnt_u2 hres ⊢
  cases relh with
  | some r =>
    dsimp only at hres
    exact False.elim (hc_elh.2 (by simp) hres)
  | none =>
    dsimp only at hnt_u2 hres ⊢
    obtain ⟨_, heff_u3_u4, hu4_loc⟩ := hc_elh.1 rfl
    have heff_u4 : HeapByteEff s0 u4 Rl gw := heff_u3.trans heff_u3_u4
    have hhp_u4 : globN s "heap_ptr" ≤ globN u4 "heap_ptr" := by
      have hhp12 : globN u1 "heap_ptr" = globN s "heap_ptr" := rfl
      have hhp2 : globN u2 "heap_ptr" = globN u1 "heap_ptr" := by simp [globN, hu2_glob]
      have hhp3 : globN u3 "heap_ptr" = globN u2 "heap_ptr" := rfl
      have hhp4 := heff_u3_u4.hp_le
      omega
    have hu4_st : u4.locals.lookup (ofString "start") = some (.val (.word startw)) := by
      rw [hu4_loc]; exact hu3_st
    have hu4_p : u4.locals.lookup (ofString "p") = some (.val (.word pw)) := by
      rw [hu4_loc]; exact hu3_p
    have hu4_t : u4.locals.lookup (ofString "t") = some (.val (.word tw)) := by
      rw [hu4_loc]; exact hu3_t
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt_u2 hres ⊢
    have hc_t : @evalHOLExact 64 F _ u4.toExact (fun a => Classical.propDecidable (u4.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "t")) (.const 0#64)) =
        some (.val (.word (if tw ≠ 0#64 then 1#64 else 0#64))) := by
      simp [evalHOLExact, hu4_t, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hc_t] at hnt_u2 hres ⊢; dsimp only at hnt_u2 hres ⊢
    by_cases htz : tw = 0#64
    · have hcw0 : (if tw ≠ 0#64 then (1#64 : BitVec 64) else 0#64) = 0 := by simp [htz]
      rw [if_pos hcw0, evaluateHOLFiniteState_skip] at hnt_u2 hres ⊢
      dsimp only at hnt_u2 hres ⊢
      have hev_ret0 : @evalHOLExact 64 F _ u4.toExact (fun a => Classical.propDecidable (u4.memaddrs a))
          (.rstruct [.var .local (ofString "start"),
                     .op .sub [.var .local (ofString "p"), .var .local (ofString "start")]]) =
          some (.rStruct [.val (.word startw), .val (.word (pw - startw))]) := by
        simp [evalHOLExact, evalListHOLExact, hu4_st, hu4_p, wordOpHOL, wordOp, valueIsWord, valueWord]
      have hsz0 : sizeOfShapeWithContextHOL u4.structs (shapeOfHOLExact
          (.rStruct [.val (.word startw), .val (.word (pw - startw))] : ValueHOL 64)) ≤ 32 := by
        simp [shapeOfHOLExact]
      rw [evaluateHOLFiniteState_return, hev_ret0]; dsimp only
      rw [if_pos hsz0]
      refine ⟨heff_u4.locals_clock _ _, fun v hv => ?_⟩
      simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at hv
      subst hv
      have hst_le_p : startw.toNat ≤ pw.toNat := by have : hlw.toNat ≤ 9 := hhl_le9; omega
      have hlen_nat : (pw - startw).toNat = pw.toNat - startw.toNat := BitVec.toNat_sub_of_le hst_le_p
      refine ⟨startw, pw - startw, rfl, ?_, by have : hlw.toNat ≤ 9 := hhl_le9; omega, by omega⟩
      dsimp only [Inside, emptyLocalsHOLFinite, globN]
      change sourceBase ≤ startw.toNat ∧ startw.toNat + (pw - startw).toNat ≤ globN u4 "heap_ptr"
      have : hlw.toNat ≤ 9 := hhl_le9
      omega
    · have hcw1 : ¬ ((if tw ≠ 0#64 then (1#64 : BitVec 64) else 0#64) = 0) := by
        have : (0 : BitVec 64) = 0#64 := rfl; rw [this]; simp [htz]
      rw [if_neg hcw1, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hnt_u2 hres ⊢
      let st1 : BitVec 64 := startw - 1#64
      have h1_le_st : (1#64 : BitVec 64).toNat ≤ startw.toNat := by
        have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
        have : hlw.toNat ≤ 9 := hhl_le9; omega
      have hst1_nat : st1.toNat = startw.toNat - 1 := by
        change (startw - 1#64).toNat = _
        have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
        rw [BitVec.toNat_sub_of_le h1_le_st, h1]
      have hev_sub1 : @evalHOLExact 64 F _ u4.toExact (fun a => Classical.propDecidable (u4.memaddrs a))
          (.op .sub [.var .local (ofString "start"), .const 1#64]) = some (.val (.word st1)) := by
        simp [evalHOLExact, evalListHOLExact, hu4_st, wordOpHOL, wordOp, valueIsWord, valueWord, st1]
      rw [hev_sub1] at hnt_u2 hres ⊢; dsimp only at hnt_u2 hres ⊢
      have hvv_st : isValidValueHOLFinite u4 .local (ofString "start") (.val (.word st1)) = true := by
        simp [isValidValueHOLFinite, lookupKvarHOLFinite, hu4_st, shapeOfHOLExact, shapeEqHOL]
      rw [if_pos hvv_st] at hnt_u2 hres ⊢; dsimp only at hnt_u2 hres ⊢
      set u5 := setKvarHOLFinite .local (ofString "start") (.val (.word st1)) u4
      have heff_u5 : HeapByteEff s0 u5 Rl gw := heff_u4.locals_clock u5.locals u5.clock
      have hu5_st : u5.locals.lookup (ofString "start") = some (.val (.word st1)) := by
        change (u4.locals.update (ofString "start", .val (.word st1))).lookup (ofString "start") = _
        simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hu5_p : u5.locals.lookup (ofString "p") = some (.val (.word pw)) := by
        change (u4.locals.update (ofString "start", .val (.word st1))).lookup (ofString "p") = _
        simp [HolFiniteMapExact.lookup_update, FUPDATE, hu4_p,
          show ofString "start" ≠ ofString "p" from M13.mls_ne rfl]
      obtain ⟨rsb, u6, hsb⟩ : ∃ rsb u6,
          evaluateHOLFiniteState u5
            (.storeByte (.var .local (ofString "start")) (.var .local (ofString "t"))) = (rsb, u6) :=
        ⟨_, _, Prod.mk.eta.symm⟩
      rw [hsb] at hnt_u2 hres ⊢
      rcases (evaluate_storeByte_control_frame u5
        (.var .local (ofString "start")) (.var .local (ofString "t"))).1 with hsn | hse
      · rw [hsb] at hsn; dsimp only at hsn; subst hsn
        dsimp only at hnt_u2 hres ⊢
        have hbre_pair := M13.ByteRegionEffect.of_storeByte hsb (Rl := Rl) (fun addr hdst_ev _ => by
          simp only [evalHOLExact, hu5_st,
            Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
          subst hdst_ev
          refine ⟨(buf.toNat, bnd.toNat), hRl_mem, ?_, ?_⟩
          · have : hlw.toNat ≤ 9 := hhl_le9; omega
          · have : 1 ≤ hlw.toNat := hhl_ge1; omega)
        have heff_u5_u6 : HeapByteEff u5 u6 Rl gw := HeapByteEff.of_m13_bre heff_u5.arena hbre_pair.1
        have heff_u6 : HeapByteEff s0 u6 Rl gw := heff_u5.trans heff_u5_u6
        have hhp_u6 : globN u5 "heap_ptr" ≤ globN u6 "heap_ptr" := heff_u5_u6.hp_le
        have hhp_u5 : globN u5 "heap_ptr" = globN u4 "heap_ptr" := rfl
        have hu6_st : u6.locals.lookup (ofString "start") = some (.val (.word st1)) := by
          rw [hbre_pair.2]; exact hu5_st
        have hu6_p : u6.locals.lookup (ofString "p") = some (.val (.word pw)) := by
          rw [hbre_pair.2]; exact hu5_p
        have hev_ret1 : @evalHOLExact 64 F _ u6.toExact (fun a => Classical.propDecidable (u6.memaddrs a))
            (.rstruct [.var .local (ofString "start"),
                       .op .sub [.var .local (ofString "p"), .var .local (ofString "start")]]) =
            some (.rStruct [.val (.word st1), .val (.word (pw - st1))]) := by
          simp [evalHOLExact, evalListHOLExact, hu6_st, hu6_p, wordOpHOL, wordOp, valueIsWord, valueWord]
        have hsz1 : sizeOfShapeWithContextHOL u6.structs (shapeOfHOLExact
            (.rStruct [.val (.word st1), .val (.word (pw - st1))] : ValueHOL 64)) ≤ 32 := by
          simp [shapeOfHOLExact]
        rw [evaluateHOLFiniteState_return, hev_ret1]; dsimp only
        rw [if_pos hsz1]
        refine ⟨heff_u6.locals_clock _ _, fun v hv => ?_⟩
        simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at hv
        subst hv
        have hst1_le_p : st1.toNat ≤ pw.toNat := by have : hlw.toNat ≤ 9 := hhl_le9; omega
        have hlen1_nat : (pw - st1).toNat = pw.toNat - st1.toNat := BitVec.toNat_sub_of_le hst1_le_p
        refine ⟨st1, pw - st1, rfl, ?_, by have : hlw.toNat ≤ 9 := hhl_le9; omega, by omega⟩
        dsimp only [Inside, emptyLocalsHOLFinite, globN]
        change sourceBase ≤ st1.toNat ∧ st1.toNat + (pw - st1).toNat ≤ globN u6 "heap_ptr"
        have : hlw.toNat ≤ 9 := hhl_le9
        omega
      · rw [hsb] at hse; dsimp only at hse; subst hse
        dsimp only at hres
        exact False.elim (not_resumes_error hres)
theorem txEncBoundedOut_mono {F : Type}
    {s0 : PanSemStateFiniteExact 64 F} {R1 R2 : List Ivl} {gw1 gw2 : List String}
    {out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F}
    (h : TxEncBoundedOut s0 R1 gw1 out)
    (hR : ∀ i ∈ R1, 0 < i.2 →
      (∃ j ∈ R2, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) ∨
      (globN s0 "frame_mem_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ globN s0 "scratch_ptr") ∨
      (globN s0 "heap_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ heapLimit))
    (hgw : ∀ g ∈ gw1, g ∈ gw2) :
    TxEncBoundedOut s0 R2 gw2 out :=
  ⟨h.1.mono hR hgw, h.2⟩
theorem txEnc_call_assign_p_step_hp {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {fname : String} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    {pw : BitVec 64} {bound : Nat}
    (heff0 : HeapByteEff s0 s Rl gw)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hp_sum : pw.toNat + bound < 2 ^ 64)
    (hcall :
      let out := evaluateHOLFiniteState s
        (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args)
      (out.1 = none →
        ∃ len : BitVec 64,
          len.toNat ≤ bound ∧
          out.2.locals = s.locals.update (ofString "w", .val (.word len)) ∧
          HeapByteEff s out.2 Rl gw) ∧
      (out.1 ≠ none → ¬ Resumes out.1))
    (hnt : (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args)
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args)
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ bound ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      globN s "heap_ptr" ≤ globN m "heap_ptr" ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq
          (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args)
            (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
          cont) = evaluateHOLFiniteState m cont := by
  dsimp only at hcall
  rcases hc : evaluateHOLFiniteState s
    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString fname) args) with ⟨rc, sc⟩
  rw [hc] at hcall; dsimp only at hcall
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_seq_line780, hc] at hnt hres ⊢
  cases rc with
  | some r =>
    dsimp only at hres
    exact False.elim (hcall.2 (by simp) hres)
  | none =>
    dsimp only at hnt hres ⊢
    obtain ⟨len, hlen_le, hsc_loc, heff_sc⟩ := hcall.1 rfl
    have hsc_p : sc.locals.lookup (ofString "p") = some (.val (.word pw)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hp,
        show ofString "w" ≠ ofString "p" from M13.mls_ne rfl]
    have hsc_w : sc.locals.lookup (ofString "w") = some (.val (.word len)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    rw [evaluateHOLFiniteState_assign] at hnt hres ⊢
    have hev_add : @evalHOLExact 64 F _ sc.toExact (fun a => Classical.propDecidable (sc.memaddrs a))
        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]) =
        some (.val (.word (pw + len))) := by
      have hpz : pw + (len + 0#64) = pw + len := by rw [BitVec.add_zero]
      simp [evalHOLExact, evalListHOLExact, hsc_p, hsc_w, wordOpHOL, wordOp, valueIsWord, valueWord, hpz]
    rw [hev_add] at hnt hres ⊢; dsimp only at hnt hres ⊢
    have hvv : isValidValueHOLFinite sc .local (ofString "p") (.val (.word (pw + len))) = true := by
      simp [isValidValueHOLFinite, lookupKvarHOLFinite, hsc_p, shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hvv] at hnt hres ⊢; dsimp only at hnt hres ⊢
    let m := setKvarHOLFinite .local (ofString "p") (.val (.word (pw + len))) sc
    have hm_loc : m.locals = (s.locals.update (ofString "w", .val (.word len))).update
        (ofString "p", .val (.word (pw + len))) := by
      change sc.locals.update (ofString "p", .val (.word (pw + len))) = _
      rw [hsc_loc]
    have hm_eff : HeapByteEff s0 m Rl gw :=
      (heff0.trans heff_sc).locals_clock m.locals m.clock
    have hm_hp : globN s "heap_ptr" ≤ globN m "heap_ptr" :=
      (heff_sc.locals_clock m.locals m.clock).hp_le
    have hplen_nat : (pw + len).toNat = pw.toNat + len.toNat := by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    refine ⟨len, m, hlen_le, hplen_nat, ?_, ?_, ?_, hm_eff, hm_hp, hnt, hres, rfl⟩
    · intro k hkw hkp; rw [hm_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hkw, Ne.symm hkp]
    · refine ⟨len, ?_⟩; rw [hm_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "w" from M13.mls_ne rfl]
    · rw [hm_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
theorem txEnc_seq_assoc_step_eq {F : Type}
    (s : PanSemStateFiniteExact 64 F) (a b c : ProgHOL 64) :
    evaluateHOLFiniteState s (.seq a (.seq b c)) =
    evaluateHOLFiniteState s (.seq (.seq a b) c) := by
  simp only [evaluateHOLFiniteState_seq_line780]
  cases evaluateHOLFiniteState s a with | mk ra sa =>
  cases ra <;> rfl
theorem txEnc_call_word_step_hp {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cont : ProgHOL 64} {txw pw : BitVec 64} (off : Nat)
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (htx_ins : Inside (txw.toNat, 384) sourceBase (globN s0 "heap_ptr"))
    (htx_wok : WordsOK s0 (txw.toNat, 384))
    (hoff8 : off % 8 = 0) (hoff_hi : off + 8 ≤ 384)
    (htx : s.locals.lookup (ofString "tx") = some (.val (.word txw)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hw : ∃ w_old : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧ pw.toNat + 9 ≤ ivl.1 + ivl.2 ∧ ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ 9 ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      globN s "heap_ptr" ≤ globN m "heap_ptr" ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq
          (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
              [.var .local (ofString "p"),
               .load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
            (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
          cont) = evaluateHOLFiniteState m cont := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have hev_v := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx off hoff8 hoff_hi
  have hnt_1 := txEnc_seq_non_timeout s _ _ hnt
  have hnt_c := txEnc_seq_non_timeout s _ _ hnt_1
  have hc := eval_call_local_rlp_encode_word s "w"
    (.var .local (ofString "p"))
    (.load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)]))
    pw (BitVec.ofNat 64 (memW s0 (txw.toNat + off)))
    Rl gw heff0.arena.1.code heff0.arena hw
    (by simp [evalHOLExact, hp]) hev_v
    (by obtain ⟨ivl, hivl, h1, h2, _⟩ := hin_ivl; exact ⟨ivl, hivl, h1, h2⟩) hnt_c
  dsimp only at hc
  exact txEnc_call_assign_p_step_hp heff0 hp
    (by obtain ⟨_, _, _, _, _⟩ := hin_ivl; omega)
    ⟨fun hnone => by
      obtain ⟨len, _, hlen9, _, _, hloc, heff_c⟩ := hc.1 hnone
      exact ⟨len, hlen9, hloc, heff_c⟩, hc.2⟩
    hnt hres
theorem txEnc_seq_call_word_hp {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cont : ProgHOL 64} {txw pw : BitVec 64} (off : Nat)
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (htx_ins : Inside (txw.toNat, 384) sourceBase (globN s0 "heap_ptr"))
    (htx_wok : WordsOK s0 (txw.toNat, 384))
    (hoff8 : off % 8 = 0) (hoff_hi : off + 8 ≤ 384)
    (htx : s.locals.lookup (ofString "tx") = some (.val (.word txw)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hw : ∃ w_old : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧ pw.toNat + 9 ≤ ivl.1 + ivl.2 ∧ ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ 9 ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      globN s "heap_ptr" ≤ globN m "heap_ptr" ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
          (.seq (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
            cont)) = evaluateHOLFiniteState m cont := by
  rw [txEnc_seq_assoc_step_eq] at hnt hres ⊢
  exact txEnc_call_word_step_hp off hAR0 heff0 hRl_ge htx_ins htx_wok hoff8 hoff_hi htx hp hw hin_ivl hnt hres
theorem txEnc_call_u256_step_hp {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cont : ProgHOL 64} {txw pw : BitVec 64} (off : Nat)
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hgw : "heap_ptr" ∈ gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (htx_ins : Inside (txw.toNat, 384) sourceBase (globN s0 "heap_ptr"))
    (htx_wok : WordsOK s0 (txw.toNat, 384))
    (hoff8 : off % 8 = 0) (hoff_hi : off + 32 ≤ 384)
    (htx : s.locals.lookup (ofString "tx") = some (.val (.word txw)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hw : ∃ w_old : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧ pw.toNat + 33 ≤ ivl.1 + ivl.2 ∧ ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
            [.var .local (ofString "p"),
             .load (.comb [.one, .one, .one, .one])
               (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
            [.var .local (ofString "p"),
             .load (.comb [.one, .one, .one, .one])
               (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
          (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
        cont)).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ 33 ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      globN s "heap_ptr" ≤ globN m "heap_ptr" ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq
          (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
              [.var .local (ofString "p"),
               .load (.comb [.one, .one, .one, .one])
                 (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
            (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
          cont) = evaluateHOLFiniteState m cont := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have hev_v := txEnc_eval_load_u256_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx off hoff8 hoff_hi
  have hnt_1 := txEnc_seq_non_timeout s _ _ hnt
  have hnt_c := txEnc_seq_non_timeout s _ _ hnt_1
  have hub := u256ByteLengthPure_bounds
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off)))
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off + 8)))
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off + 16)))
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off + 24)))
  have hc := eval_call_local_tx_put_u256 s "w"
    (.var .local (ofString "p"))
    (.load (.comb [.one, .one, .one, .one])
      (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)]))
    pw
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off)))
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off + 8)))
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off + 16)))
    (BitVec.ofNat 64 (memW s0 (txw.toNat + off + 24)))
    Rl gw heff0.arena.1.code heff0.arena hgw hw
    (by simp [evalHOLExact, hp]) hev_v
    (by obtain ⟨ivl, hivl, h1, h2, _⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by have := hub.2.2.2.2.2; omega⟩)
    hnt_c
  dsimp only at hc
  exact txEnc_call_assign_p_step_hp heff0 hp
    (by obtain ⟨_, _, _, _, _⟩ := hin_ivl; omega)
    ⟨fun hnone => by
      obtain ⟨len, _, _, hlen33, _, _, hloc, heff_c⟩ := hc.1 hnone
      exact ⟨len, hlen33, hloc, heff_c⟩, hc.2⟩
    hnt hres
theorem txEnc_seq_call_u256_hp {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cont : ProgHOL 64} {txw pw : BitVec 64} (off : Nat)
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hgw : "heap_ptr" ∈ gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (htx_ins : Inside (txw.toNat, 384) sourceBase (globN s0 "heap_ptr"))
    (htx_wok : WordsOK s0 (txw.toNat, 384))
    (hoff8 : off % 8 = 0) (hoff_hi : off + 32 ≤ 384)
    (htx : s.locals.lookup (ofString "tx") = some (.val (.word txw)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hw : ∃ w_old : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧ pw.toNat + 33 ≤ ivl.1 + ivl.2 ∧ ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
          [.var .local (ofString "p"),
           .load (.comb [.one, .one, .one, .one])
             (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
          [.var .local (ofString "p"),
           .load (.comb [.one, .one, .one, .one])
             (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ 33 ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      globN s "heap_ptr" ≤ globN m "heap_ptr" ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_u256")
            [.var .local (ofString "p"),
             .load (.comb [.one, .one, .one, .one])
               (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
          (.seq (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
            cont)) = evaluateHOLFiniteState m cont := by
  rw [txEnc_seq_assoc_step_eq] at hnt hres ⊢
  exact txEnc_call_u256_step_hp off hAR0 heff0 hgw hRl_ge htx_ins htx_wok hoff8 hoff_hi htx hp hw hin_ivl hnt hres
theorem txEnc_seq_call_to_hp {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cont : ProgHOL 64} {txw pw : BitVec 64} (off : Nat)
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (htx_ins : Inside (txw.toNat, 384) sourceBase (globN s0 "heap_ptr"))
    (htx_wok : WordsOK s0 (txw.toNat, 384))
    (hoff8 : off % 8 = 0) (hoff_hi : off + 8 ≤ 384)
    (htx : s.locals.lookup (ofString "tx") = some (.val (.word txw)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hw : ∃ w_old : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧ pw.toNat + 21 ≤ ivl.1 + ivl.2 ∧ ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_to")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_to")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ 21 ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      globN s "heap_ptr" ≤ globN m "heap_ptr" ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "tx_put_to")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)])])
          (.seq (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
            cont)) = evaluateHOLFiniteState m cont := by
  rw [txEnc_seq_assoc_step_eq] at hnt hres ⊢
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have hev_v := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx off hoff8 hoff_hi
  have hnt_1 := txEnc_seq_non_timeout s _ _ hnt
  have hnt_c := txEnc_seq_non_timeout s _ _ hnt_1
  have hc := eval_call_local_tx_put_to s "w"
    (.var .local (ofString "p"))
    (.load .one (.op .add [.var .local (ofString "tx"), .const (BitVec.ofNat 64 off)]))
    pw (BitVec.ofNat 64 (memW s0 (txw.toNat + off)))
    Rl gw heff0.arena.1.code heff0.arena hw
    (by simp [evalHOLExact, hp]) hev_v
    (by obtain ⟨ivl, hivl, h1, h2, _⟩ := hin_ivl; exact ⟨ivl, hivl, h1, h2⟩) hnt_c
  dsimp only at hc
  exact txEnc_call_assign_p_step_hp heff0 hp
    (by obtain ⟨_, _, _, _, _⟩ := hin_ivl; omega)
    ⟨fun hnone => by
      obtain ⟨len, hlen21, _, _, hloc, heff_c⟩ := hc.1 hnone
      exact ⟨len, hlen21, hloc, heff_c⟩, hc.2⟩
    hnt hres
theorem txEnc_seq_call_bytes_hp {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cont : ProgHOL 64} {txw pw : BitVec 64}
    (hAR0 : ArenaReady s0)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hRl_ge : ∀ ivl ∈ Rl, 0 < ivl.2 → globN s0 "heap_ptr" ≤ ivl.1)
    (htx_ins : Inside (txw.toNat, 384) sourceBase (globN s0 "heap_ptr"))
    (htx_wok : WordsOK s0 (txw.toNat, 384))
    (hdata_lt : memW s0 (txw.toNat + 200) < 2 ^ 32)
    (htx : s.locals.lookup (ofString "tx") = some (.val (.word txw)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hw : ∃ w_old : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w_old)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ pw.toNat ∧
      pw.toNat + 9 + memW s0 (txw.toNat + 200) ≤ ivl.1 + ivl.2 ∧ ivl.1 + ivl.2 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "tx"), .const 192#64]),
           .load .one (.op .add [.var .local (ofString "tx"), .const 200#64])])
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "tx"), .const 192#64]),
           .load .one (.op .add [.var .local (ofString "tx"), .const 200#64])])
        (.seq (.assign .local (ofString "p")
            (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          cont))).1) :
    ∃ (len : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      len.toNat ≤ 9 + memW s0 (txw.toNat + 200) ∧
      (pw + len).toNat = pw.toNat + len.toNat ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word (pw + len))) ∧
      HeapByteEff s0 m Rl gw ∧
      globN s "heap_ptr" ≤ globN m "heap_ptr" ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "tx"), .const 192#64]),
             .load .one (.op .add [.var .local (ofString "tx"), .const 200#64])])
          (.seq (.assign .local (ofString "p")
              (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
            cont)) = evaluateHOLFiniteState m cont := by
  rw [txEnc_seq_assoc_step_eq] at hnt hres ⊢
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have h232 : (2 ^ 32 : Nat) = 4294967296 := rfl
  have hev_src := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx 192 (by decide) (by decide)
  have hev_n := txEnc_eval_load_word_below_hp hAR0 heff0 hRl_ge htx_ins htx_wok "tx" htx 200 (by decide) (by decide)
  let nw := BitVec.ofNat 64 (memW s0 (txw.toNat + 200))
  have hnw_nat : nw.toNat = memW s0 (txw.toNat + 200) := by
    change (BitVec.ofNat 64 (memW s0 (txw.toNat + 200))).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hbnd_hl := rlpHeaderLenPure_bounds nw.toNat
  have hnt_1 := txEnc_seq_non_timeout s _ _ hnt
  have hnt_c := txEnc_seq_non_timeout s _ _ hnt_1
  have hc := eval_call_local_rlp_encode_bytes s "w"
    (.var .local (ofString "p"))
    (.load .one (.op .add [.var .local (ofString "tx"), .const 192#64]))
    (.load .one (.op .add [.var .local (ofString "tx"), .const 200#64]))
    pw (BitVec.ofNat 64 (memW s0 (txw.toNat + 192))) nw
    Rl gw heff0.arena.1.code heff0.arena hw
    (by simp [evalHOLExact, hp]) hev_src hev_n
    (by obtain ⟨ivl, hivl, h1, h2, _⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩) hnt_c
  dsimp only at hc
  exact txEnc_call_assign_p_step_hp heff0 hp
    (by obtain ⟨_, _, _, _, _⟩ := hin_ivl; omega)
    ⟨fun hnone => by
      obtain ⟨len, hlen_le, _, _, hloc, heff_c⟩ := hc.1 hnone
      exact ⟨len, by omega, hloc, heff_c⟩, hc.2⟩
    hnt hres
theorem txEnc_ite_hp {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    {cond : ExpHOL 64} {p_then p_else cont : ProgHOL 64}
    {cw pw : BitVec 64} {bound : Nat}
    (_heff0 : HeapByteEff s0 s Rl gw)
    (hc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
      some (.val (.word cw)))
    (_hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hthen : cw ≠ 0#64 →
      (evaluateHOLFiniteState s (.seq p_then cont)).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState s (.seq p_then cont)).1 →
      ∃ (p' : BitVec 64) (m : PanSemStateFiniteExact 64 F),
        pw.toNat ≤ p'.toNat ∧ p'.toNat ≤ pw.toNat + bound ∧
        (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
        (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
        m.locals.lookup (ofString "p") = some (.val (.word p')) ∧
        HeapByteEff s0 m Rl gw ∧
        globN s "heap_ptr" ≤ globN m "heap_ptr" ∧
        (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
        Resumes (evaluateHOLFiniteState m cont).1 ∧
        evaluateHOLFiniteState s (.seq p_then cont) = evaluateHOLFiniteState m cont)
    (helse : cw = 0#64 →
      (evaluateHOLFiniteState s (.seq p_else cont)).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState s (.seq p_else cont)).1 →
      ∃ (p' : BitVec 64) (m : PanSemStateFiniteExact 64 F),
        pw.toNat ≤ p'.toNat ∧ p'.toNat ≤ pw.toNat + bound ∧
        (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
        (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
        m.locals.lookup (ofString "p") = some (.val (.word p')) ∧
        HeapByteEff s0 m Rl gw ∧
        globN s "heap_ptr" ≤ globN m "heap_ptr" ∧
        (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
        Resumes (evaluateHOLFiniteState m cont).1 ∧
        evaluateHOLFiniteState s (.seq p_else cont) = evaluateHOLFiniteState m cont)
    (hnt : (evaluateHOLFiniteState s (.seq (.ite cond p_then p_else) cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (.seq (.ite cond p_then p_else) cont)).1) :
    ∃ (p' : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      pw.toNat ≤ p'.toNat ∧ p'.toNat ≤ pw.toNat + bound ∧
      (∀ k, k ≠ ofString "w" → k ≠ ofString "p" → m.locals.lookup k = s.locals.lookup k) ∧
      (∃ w_f : BitVec 64, m.locals.lookup (ofString "w") = some (.val (.word w_f))) ∧
      m.locals.lookup (ofString "p") = some (.val (.word p')) ∧
      HeapByteEff s0 m Rl gw ∧
      globN s "heap_ptr" ≤ globN m "heap_ptr" ∧
      (evaluateHOLFiniteState m cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState m cont).1 ∧
      evaluateHOLFiniteState s (.seq (.ite cond p_then p_else) cont) = evaluateHOLFiniteState m cont := by
  have heq_ite : evaluateHOLFiniteState s (.seq (.ite cond p_then p_else) cont) =
      if cw = 0#64 then evaluateHOLFiniteState s (.seq p_else cont)
      else evaluateHOLFiniteState s (.seq p_then cont) := by
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hc]
    dsimp only
    by_cases hcz : cw = 0#64
    · subst hcz; simp [evaluateHOLFiniteState_seq_line780]
    · have hcz0 : ¬ (cw = 0) := hcz
      rw [if_neg hcz0, if_neg hcz, evaluateHOLFiniteState_seq_line780]
  rw [heq_ite] at hnt hres ⊢
  by_cases hcz : cw = 0#64
  · rw [if_pos hcz] at hnt hres ⊢; exact helse hcz hnt hres
  · rw [if_neg hcz] at hnt hres ⊢; exact hthen hcz hnt hres
end Phases1To4RelationalClosure
end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
