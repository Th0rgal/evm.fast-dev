import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB4c2c1JournalAppend

/-!
# Scratch Rung B4c2c: Account-Mutation Callees as `WorldKeepsCodeSc`

Lifts the journaled account-mutation bridges of `AccountWk` (`jset` on `ts+16`,
`jdel` on `ts+32`, `set_account`, `destroy_storage`, `destroy_account`,
`modify_state_commit`) from `WorldStepSc` to `WorldStepCodeSc`. A journal append and a
`ts+32` hash-table deletion both leave every live code-DB root footprint unhit, so the
code-DB roots (`ws+16`, `bs+48`, `ts+48`) keep their exact `htabValues`.
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
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase
open InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas
open InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8M19.Htab
open InitECandidate.Solver.Wave8GuestInv.HtabC00Ports
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-! ## 1. `jset` on the `ts+16` Slot -/

theorem progWStepCode_call0_jset_ts16 (B : BufList) (gw : List String)
    (hhp_in : "heap_ptr" ∈ gw) (hjn_in : "journal_n" ∈ gw)
    (kExp vExp : ExpHOL 64) :
    ProgWStepCode B gw
      (.call (some (none, none)) (ofString "jset")
        [.load .one (.op .add [.var .global (ofString "ts"), .const 16#64]), kExp, vExp]) := by
  intro F s hcode hW hnt hfr
  set argsL : List (ExpHOL 64) :=
    [.load .one (.op .add [.var .global (ofString "ts"), .const 16#64]), kExp, vExp]
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) argsL with _ | values
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    have hargs_fin : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) argsL = some values := by
      rwa [evalListHOLFinite_eq_toExact]
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "jset") values with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        have hbody_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "jset")
          _ _ body' _ ret' values callee lookup_jset (by rwa [← hcode])
        obtain ⟨v1, v2, v3, he1, _, _, hc_t, hc_k, hc_v⟩ := callee_param_three s (ofString "jset")
          (ofString "t") (ofString "key") (ofString "value") .one .one .one _ _
          (by rw [hcode]; exact lookup_jset) _ _ _ values body' callee ret' hargs_fin hl
        obtain ⟨tw, rfl, htw_nat, hts_nz⟩ := evalAt_loadG_nz s hW.1.1 "ts" 16#64 (by decide) v1 he1
        obtain ⟨_, kw, vlw, hvals_eq, _, hc_k', hc_v'⟩ := Fast_C08WkShard03.lookupCode_three_words
          (by decide) (by decide) (by decide) lookup_jset
          (by
            have hret_eq := lookupCodeHOLFinite_installed_return s (ofString "jset")
              _ _ _ _ ret' values callee (by rw [hcode]; exact lookup_jset) hl
            subst hbody_eq hret_eq; rwa [← hcode])
        have hv23 : v2 = .val (.word kw) ∧ v3 = .val (.word vlw) := by
          rw [hc_k] at hc_k'; rw [hc_v] at hc_v'
          exact ⟨Option.some.inj hc_k', Option.some.inj hc_v'⟩
        rcases hv23 with ⟨rfl, rfl⟩
        let ent := callEntryStateHOLFinite s callee
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, post⟩
        simp only [ent, hrun] at hnt hfr ⊢
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | exception eid ev =>
            exfalso
            have hne : eid ≠ ofString "TrapErr" := by
              rcases hfr with h | h | h | ⟨_, h⟩ | ⟨_, _, h, hne⟩ <;> try simp at h
              obtain ⟨rfl, _⟩ := h; exact hne
            have hbody_ok : noCatchableRaise trapOnlyCallees body' = true :=
              trapOnlyCallees_good (ofString "jset") (by decide) values body' callee ret' (by rwa [← hcode])
            have hno := evaluate_noCatchableRaise trapOnlyCallees trapOnlyCallees_good
              body' hbody_ok ent hcode eid ev hne
            dsimp only [ent] at hno; rw [hrun] at hno; exact hno rfl
          | returned rv =>
            dsimp only at hfr ⊢
            split
            · have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
              subst hbody_eq
              have hbody_fold : sourceFnBody Guest.Software.guestFn_jset =
                  .decCall (ofString "old") (.comb [.one, .one]) (ofString "htab_get")
                    [.var .local (ofString "t"), .var .local (ofString "key")]
                    (journalAppendTailProg 4#64 (.rfield 0 (.var .local (ofString "old")))
                      (.seq
                        (.call (some (none, none)) (ofString "htab_set")
                          [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")])
                        (.return (.const 0#64)))) := rfl
              change evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_jset) = (some (.returned rv), post) at hrun
              rw [hbody_fold] at hrun
              rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
              have hent_t : ent.locals.lookup (ofString "t") = some (.val (.word tw)) := hc_t
              have hent_k : ent.locals.lookup (ofString "key") = some (.val (.word kw)) := hc_k
              have hent_v : ent.locals.lookup (ofString "value") = some (.val (.word vlw)) := hc_v
              have hargs_hg : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
                  [.var .local (ofString "t"), .var .local (ofString "key")] =
                  some [.val (.word tw), .val (.word kw)] := by
                simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hent_t, hent_k]
              rw [hargs_hg] at hrun; dsimp only at hrun
              rcases hlk_hg : lookupCodeHOLFinite ent.code.lookup (ofString "htab_get")
                  [.val (.word tw), .val (.word kw)] with _ | ⟨bhg, chg, rhg⟩
              · rw [hlk_hg] at hrun; simp at hrun
              · rw [hlk_hg] at hrun; dsimp only at hrun
                by_cases hcz_ent : ent.clock = 0
                · simp [hcz_ent] at hrun
                rw [if_neg hcz_ent] at hrun
                have hbhg_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "htab_get")
                  _ _ bhg _ rhg _ chg EvmFrameSpecs.lookup_htab_get (by rwa [← show ent.code = originalRuntimeCode from hcode])
                subst hbhg_eq
                obtain ⟨_, _, _, _, hchg_t, hchg_k⟩ := callee_param_two_r16_code ent (ofString "htab_get")
                  (ofString "t") (ofString "key") .one .one _ _
                  (by rw [show ent.code = originalRuntimeCode from hcode]; exact EvmFrameSpecs.lookup_htab_get)
                  (.var .local (ofString "t")) (.var .local (ofString "key"))
                  _ _ chg rhg hargs_hg hlk_hg
                have hchg_t' : chg.lookup (ofString "t") = some (.val (.word tw)) := by
                  have ht_ev : evalAt ent (.var .local (ofString "t")) = some (.val (.word tw)) := by
                    simp [evalAt, evalHOLExact, toExact, hent_t]
                  have ⟨v1', _, he1', _, hc1', _⟩ := callee_param_two_r16_code ent (ofString "htab_get")
                    (ofString "t") (ofString "key") .one .one _ _
                    (by rw [show ent.code = originalRuntimeCode from hcode]; exact EvmFrameSpecs.lookup_htab_get)
                    (.var .local (ofString "t")) (.var .local (ofString "key"))
                    _ _ chg rhg hargs_hg hlk_hg
                  rw [ht_ev] at he1'; injection he1' with h'; subst h'; exact hc1'
                have hchg_k' : chg.lookup (ofString "key") = some (.val (.word kw)) := by
                  have hk_ev : evalAt ent (.var .local (ofString "key")) = some (.val (.word kw)) := by
                    simp [evalAt, evalHOLExact, toExact, hent_k]
                  have ⟨_, v2', _, he2', _, hc2'⟩ := callee_param_two_r16_code ent (ofString "htab_get")
                    (ofString "t") (ofString "key") .one .one _ _
                    (by rw [show ent.code = originalRuntimeCode from hcode]; exact EvmFrameSpecs.lookup_htab_get)
                    (.var .local (ofString "t")) (.var .local (ofString "key"))
                    _ _ chg rhg hargs_hg hlk_hg
                  rw [hk_ev] at he2'; injection he2' with h'; subst h'; exact hc2'
                let ent_hg := callEntryStateHOLFinite ent chg
                rcases hrun_hg : evaluateHOLFiniteState ent_hg (sourceFnBody Guest.Software.guestFn_htab_get) with ⟨res_hg, p_hg⟩
                dsimp only [ent_hg] at hrun_hg
                rw [hrun_hg] at hrun
                cases res_hg with
                | none => simp at hrun
                | some cr_hg =>
                  cases cr_hg with
                  | exception eid_hg ev_hg =>
                    exfalso
                    dsimp only at hrun; injection hrun with hr_eq _
                    cases hr_eq
                  | timeOut | error | «break» | «continue» | finalFfi _ => simp at hrun
                  | returned v_old =>
                    dsimp only at hrun
                    split at hrun <;> try simp at hrun
                    have htw_nz : tw ≠ 0 := WkBal.htab_get_t_nonzero ent_hg tw kw
                      (guestInv_callEntry ent chg hWent.1.1) hchg_t' hchg_k' v_old
                      (by dsimp only [ent_hg]; rw [hrun_hg])
                    have ht0_nz : memW s (globN s "ts" + 16) ≠ 0 := by
                      intro h0; apply htw_nz; apply BitVec.eq_of_toNat_eq
                      change tw.toNat = 0; simpa [htw_nat] using h0
                    obtain ⟨_, S0, hWT0⟩ := hW
                    have htw_S0 : tw.toNat ∈ S0 := by
                      rw [htw_nat]; exact (nonValueSlot_ts16 s S0 hWT0.1 hts_nz ht0_nz).1
                    have hwf_hg : HtabWF ent_hg tw.toNat :=
                      (htabWF_with_locals s chg (ent.clock - 1) tw.toNat).2 (hWT0.1.2.1 _ htw_S0).1
                    obtain ⟨f0, f1, rfl, _⟩ := WkBal.htab_get_ret_in_values ent_hg tw kw
                      hcode hchg_t' hchg_k' hwf_hg v_old
                      (by dsimp only [ent_hg]; rw [hrun_hg])
                    have hro_hg := FunSpec.at_lookup EvmFrameSpecs.ro_htab_get ent hcode
                      _ (sourceFnBody Guest.Software.guestFn_htab_get) chg rhg hlk_hg
                      (guestInv_callEntry ent chg hWent.1.1) (by rw [hrun_hg]; simp)
                    have hro_hg' : ((evaluateHOLFiniteState ent_hg (sourceFnBody Guest.Software.guestFn_htab_get)).2) = _ :=
                      hro_hg (by rw [hrun_hg]; exact Or.inl ⟨_, rfl⟩)
                    dsimp only [ent_hg] at hro_hg'
                    rw [hrun_hg] at hro_hg'
                    dsimp only at hro_hg'
                    set s_old := setVarHOLFinite (ofString "old") (.rStruct [.val (.word f0), .val (.word f1)])
                      { p_hg with locals := ent.locals }
                    have heff_old : WorldEff ent s_old [] [] ["heap_ptr"] :=
                      ((WorldEff.refl ent [] [] ["heap_ptr"] hWent.1 hcode).of_readOnly hro_hg').locals_clock _ _
                    have hg_all_old : ∀ k : MlS, s_old.globals.lookup k = ent.globals.lookup k := by
                      intro k; dsimp only [s_old, setVarHOLFinite]; rw [hro_hg']; rfl
                    have hold_t : s_old.locals.lookup (ofString "t") = some (.val (.word tw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_t,
                        show ofString "old" ≠ ofString "t" by decide]
                    have hold_k : s_old.locals.lookup (ofString "key") = some (.val (.word kw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_k,
                        show ofString "old" ≠ ofString "key" by decide]
                    have hold_v : s_old.locals.lookup (ofString "value") = some (.val (.word vlw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_v,
                        show ofString "old" ≠ ofString "value" by decide]
                    have hold_old : s_old.locals.lookup (ofString "old") =
                        some (.rStruct [.val (.word f0), .val (.word f1)]) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                    rcases htail_old : evaluateHOLFiniteState s_old
                        (journalAppendTailProg 4#64 (.rfield 0 (.var .local (ofString "old")))
                          (.seq
                            (.call (some (none, none)) (ofString "htab_set")
                              [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")])
                            (.return (.const 0#64)))) with ⟨rtail, ptail⟩
                    rw [htail_old] at hrun; dsimp only at hrun
                    have hrtail_eq : rtail = some (.returned rv) := hrun.1
                    have hpost_ptail : post = { ptail with locals := (HolFiniteMapExact.resVarEq ptail.locals
                        (ofString "old", ent.locals.lookup (ofString "old"))) } := hrun.2.symm
                    obtain ⟨mid, tailPost, hstep_j, hmid_t, hmid_k, hmid_v_eq, hmid_tail, hptail_tp⟩ :=
                      journal_append_block_step_code ent s_old
                        4#64 (.rfield 0 (.var .local (ofString "old"))) tw kw f0 f1 f0 hWent heff_old hg_all_old
                        hold_t hold_k hold_old
                        (fun st hst => by simp [evalHOLExact, toExact, hst])
                        (fun S hTS => by
                          have htw_nat' : tw.toNat = memW s (globN s "ts" + 16) := htw_nat
                          have hts_ent : globN ent "ts" = globN s "ts" := rfl
                          have hm16_ent : memW ent (globN ent "ts" + 16) = memW s (globN s "ts" + 16) := rfl
                          have htw_S : tw.toNat ∈ S := by
                            rw [htw_nat']
                            exact (nonValueSlot_ts16 ent S hTS hts_nz (by change memW ent (globN ent "ts" + 16) ≠ 0; rw [hm16_ent]; exact ht0_nz)).1
                          have hjr_16 : journalRole ent tw.toNat = "ts+16" := by
                            unfold journalRole
                            rw [if_pos ⟨hts_nz, by rw [hm16_ent]; exact htw_nat'⟩]
                          refine ⟨htw_S, ?_⟩
                          dsimp only
                          rw [hjr_16]
                          simp only [show ("ts+16" = "ts+32") ↔ False by decide, and_false, ↓reduceIte,
                            List.mem_singleton]
                          rintro p rfl
                          have hm16_wrs : (memW ent (globN ent "ts" + 16), "ts+16") ∈ worldRoleSlots ent := by
                            apply mem_worldRoleSlots_recRole ent "ts" 16 "ts+16" (by rwa [hts_ent])
                              (by rw [hm16_ent]; exact ht0_nz)
                            apply List.mem_append.2; right
                            unfold recRoles; simp [hts_ent, hts_nz]
                          rwa [hm16_ent, ← htw_nat'] at hm16_wrs)
                        (by rw [htail_old, hrtail_eq])
                    have hmid_v : mid.locals.lookup (ofString "value") = some (.val (.word vlw)) :=
                      hmid_v_eq.trans hold_v
                    have hW_mid : WorldOK mid := hstep_j.worldOK_bufs (fun _ h => by cases h) hWent
                    have hmid_code : mid.code = originalRuntimeCode := hW_mid.1.1.code
                    have hts_mid : globN mid "ts" = globN ent "ts" :=
                      globN_eq_of_lookup (hstep_j.1.1.2.2.1 (ofString "ts") (by decide))
                    have hm16_mid : memW mid (globN mid "ts" + 16) = tw.toNat := by
                      rw [hts_mid]
                      have hrk16 := hstep_j.1.1.2.2.2.1
                        ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]) (by simp [R10Shards.P26_P28.stdKeep]) hts_nz
                        16 (by simp) (fun _ h => by cases h)
                      exact hrk16.trans htw_nat.symm
                    obtain ⟨s_hs, hhs, hret_hs⟩ := seq_call0_ret_inv hmid_tail
                    rw [evaluateHOLFiniteState_return] at hret_hs
                    simp only [evalHOLExact, toExact, shapeOfHOLExact, sizeOfShapeWithContextHOL,
                      show (1 : Nat) ≤ 32 by decide, ↓reduceIte, emptyLocalsHOLFinite] at hret_hs
                    have htp_eq : tailPost = { s_hs with locals := HolFiniteMapExact.empty } :=
                      ((Prod.mk.inj hret_hs).2).symm
                    rw [evaluateHOLFiniteState_call] at hhs
                    have hargs_hs : evalListHOLFinite mid (h := fun a => Classical.propDecidable (mid.memaddrs a))
                        [.var .local (ofString "t"), .var .local (ofString "key"), .var .local (ofString "value")] =
                        some [.val (.word tw), .val (.word kw), .val (.word vlw)] := by
                      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hmid_t, hmid_k, hmid_v]
                    rw [hargs_hs] at hhs; dsimp only at hhs
                    rcases hlk_hs : lookupCodeHOLFinite mid.code.lookup (ofString "htab_set")
                        [.val (.word tw), .val (.word kw), .val (.word vlw)] with _ | ⟨bhs, chs, rhs'⟩
                    · rw [hlk_hs] at hhs; simp at hhs
                    · rw [hlk_hs] at hhs; dsimp only at hhs
                      by_cases hcz_mid : mid.clock = 0
                      · simp [hcz_mid] at hhs
                      rw [if_neg hcz_mid] at hhs
                      obtain ⟨v1_hs, _, _, he1_hs, _, _, hchs_t, _, _⟩ := callee_param_three mid (ofString "htab_set")
                        (ofString "t") (ofString "key") (ofString "value") .one .one .one _ _
                        (by rw [hmid_code]; exact EvmFrameSpecs.lookup_htab_set)
                        (.var .local (ofString "t")) (.var .local (ofString "key")) (.var .local (ofString "value"))
                        _ bhs chs rhs' hargs_hs hlk_hs
                      have hv1_hs_eq : v1_hs = .val (.word tw) := by
                        simp [evalAt, evalHOLExact, toExact, hmid_t] at he1_hs; exact he1_hs.symm
                      subst hv1_hs_eq
                      let ent_hs := callEntryStateHOLFinite mid chs
                      have hloc_t_hs : locN ent_hs "t" = memW mid (globN mid "ts" + (16#64 : BitVec 64).toNat) := by
                        change locN ent_hs "t" = memW mid (globN mid "ts" + 16)
                        simp [locN, ent_hs, callEntryStateHOLFinite, hchs_t, hm16_mid]
                      rcases hrun_hs : evaluateHOLFiniteState ent_hs bhs with ⟨res_hs, p_hs⟩
                      dsimp only [ent_hs] at hrun_hs
                      rw [hrun_hs] at hhs
                      cases res_hs with
                      | none => simp at hhs
                      | some cr_hs2 =>
                        cases cr_hs2 with
                        | returned v_hs =>
                          dsimp only at hhs
                          split at hhs <;> try simp at hhs
                          have hs_hs_eq : s_hs = { p_hs with locals := mid.locals } := hhs.symm
                          have hts_mid_nz : globN mid "ts" ≠ 0 := by rwa [hts_mid]
                          have ht0_mid_nz : memW mid (globN mid "ts" + (16#64 : BitVec 64).toNat) ≠ 0 := by
                            change memW mid (globN mid "ts" + 16) ≠ 0
                            rw [hm16_mid]; intro h0; apply htw_nz; exact BitVec.eq_of_toNat_eq h0
                          have hArg_hs : HtabArgWF ent_hs := by
                            obtain ⟨hAm, Sm, hTm, _⟩ := hW_mid
                            have ht0_Sm := (nonValueSlot_ts16 mid Sm hTm hts_mid_nz ht0_mid_nz).1
                            refine ⟨localsFree_arenaReady mid _ _ hAm, ?_, ?_⟩
                            · rw [hloc_t_hs]; exact (htabWF_with_locals mid chs (mid.clock - 1) _).2 (hTm.2.1 _ ht0_Sm).1
                            · rw [hloc_t_hs]; exact fun i hi => ((hTm.2.1 _ ht0_Sm).2 i hi).1
                          have hexit := FunSpec.at_lookup htab_set_spec mid hmid_code
                            _ bhs chs rhs' hlk_hs hArg_hs (by rw [hrun_hs]; simp)
                          rw [hrun_hs] at hexit
                          have hex := hexit v_hs rfl
                          dsimp only [HtabExit] at hex
                          rw [hloc_t_hs] at hex
                          obtain ⟨hAp_hs, hwf_hs, hh0_hs, _, hhp_hs, hfp_hs, hfr_hs, hg_hs⟩ := hex
                          have hbe_hs : p_hs.be = mid.be := by
                            have inv := (PanRunBounded.evaluateHOLFiniteState_metadata ent_hs bhs).2.2.1
                            dsimp only [ent_hs] at inv; rw [hrun_hs] at inv; exact inv
                          have hstep_hs0 : WorldStepCodeSc [] ["heap_ptr"] mid none p_hs :=
                            worldStepCodeSc_of_htabExit_nonCodeValue hW_mid hbe_hs hg_hs hg_hs
                              (fun Sm hTm => nonCodeValueSlot_ts16 mid Sm hTm hts_mid_nz ht0_mid_nz)
                              hAp_hs hwf_hs hh0_hs hhp_hs hfp_hs hfr_hs
                          have hstep_hs : WorldStepCodeSc [] ["heap_ptr", "journal_n"] mid none post := by
                            have hp_post : post = { p_hs with locals := post.locals, clock := post.clock } := by
                              rw [hpost_ptail, hptail_tp, htp_eq, hs_hs_eq]
                            rw [hp_post]
                            exact worldStepCodeSc_mono_bufs
                              (fun _ h => by cases h) (by simp)
                              (worldStepCodeSc_with_locals_clock (r' := none) hstep_hs0 post.locals post.clock)
                          have hstep_ent : WorldStepCodeSc [] ["heap_ptr", "journal_n"] ent none post :=
                            worldStepCodeSc_trans (B := []) (gw := ["heap_ptr", "journal_n"])
                              posBufList_nil (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)
                              hstep_j hstep_hs
                          have hstep_s : WorldStepCodeSc [] ["heap_ptr", "journal_n"] s none { post with locals := s.locals, clock := post.clock } :=
                            worldStepCodeSc_from_entry (r' := none) (callee := callee) (L := s.locals) (k := post.clock) hstep_ent
                          exact worldStepCodeSc_mono_bufs
                            (fun _ h => by cases h)
                            (fun g hg => by
                              simp at hg
                              rcases hg with rfl | rfl
                              · exact hhp_in
                              · exact hjn_in) hstep_s
                        | _ => simp at hhs
            · rename_i hbad; simp only [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error

/-! ## 2. `jdel` on the `ts+32` Slot -/

theorem jdel_ts32_step_code {F : Type} (B : BufList) (gw : List String)
    (hhp_in : "heap_ptr" ∈ gw) (hjn_in : "journal_n" ∈ gw)
    (tExp kExp : ExpHOL 64)
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hW : WorldOK s)
    (tw : BitVec 64)
    (ht_ev : evalAt s tExp = some (.val (.word tw)))
    (htw_nat : tw.toNat = memW s (globN s "ts" + 32))
    (hts_nz : globN s "ts" ≠ 0)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "jdel") [tExp, kExp])).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "jdel") [tExp, kExp])).1) :
    WorldStepCodeSc B gw
      s (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "jdel") [tExp, kExp])).1
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "jdel") [tExp, kExp])).2 := by
  set argsL : List (ExpHOL 64) := [tExp, kExp]
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) argsL with _ | values
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    have hargs_fin : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) argsL = some values := by
      rwa [evalListHOLFinite_eq_toExact]
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "jdel") values with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        have hbody_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "jdel")
          _ _ body' _ ret' values callee lookup_jdel (by rwa [← hcode])
        obtain ⟨v1, v2, he1, he2, hc_t, hc_k⟩ := callee_param_two_r16_code s (ofString "jdel")
          (ofString "t") (ofString "key") .one .one _ _
          (by rw [hcode]; exact lookup_jdel) _ _ values body' callee ret' hargs_fin hl
        have hv1_eq : v1 = .val (.word tw) := by
          rw [ht_ev] at he1; exact (Option.some.inj he1).symm
        subst hv1_eq
        obtain ⟨_, kw, hvals_eq, _, hc_k'⟩ := Fast_C08WkShard03.lookupCode_two_words
          (by decide) lookup_jdel
          (by
            have hret_eq := lookupCodeHOLFinite_installed_return s (ofString "jdel")
              _ _ _ _ ret' values callee (by rw [hcode]; exact lookup_jdel) hl
            subst hbody_eq hret_eq; rwa [← hcode])
        have hv2_eq : v2 = .val (.word kw) := by
          rw [hc_k] at hc_k'; exact Option.some.inj hc_k'
        subst hv2_eq
        let ent := callEntryStateHOLFinite s callee
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, post⟩
        simp only [ent, hrun] at hnt hfr ⊢
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | exception eid ev =>
            exfalso
            have hne : eid ≠ ofString "TrapErr" := by
              rcases hfr with h | h | h | ⟨_, h⟩ | ⟨_, _, h, hne⟩ <;> try simp at h
              obtain ⟨rfl, _⟩ := h; exact hne
            have hbody_ok : noCatchableRaise trapOnlyCallees body' = true :=
              trapOnlyCallees_good (ofString "jdel") (by decide) values body' callee ret' (by rwa [← hcode])
            have hno := evaluate_noCatchableRaise trapOnlyCallees trapOnlyCallees_good
              body' hbody_ok ent hcode eid ev hne
            dsimp only [ent] at hno; rw [hrun] at hno; exact hno rfl
          | returned rv =>
            dsimp only at hfr ⊢
            split
            · have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
              subst hbody_eq
              have hbody_fold : sourceFnBody Guest.Software.guestFn_jdel =
                  .decCall (ofString "old") (.comb [.one, .one]) (ofString "htab_get")
                    [.var .local (ofString "t"), .var .local (ofString "key")]
                    (.seq
                      (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0#64))
                        (.return (.const 0#64))
                        .skip)
                      (journalAppendTailProg 5#64 (.const 1#64)
                        (.seq
                          (.call (some (none, none)) (ofString "htab_del")
                            [.var .local (ofString "t"), .var .local (ofString "key")])
                          (.return (.const 0#64))))) := rfl
              change evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_jdel) = (some (.returned rv), post) at hrun
              rw [hbody_fold] at hrun
              rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
              have hent_t : ent.locals.lookup (ofString "t") = some (.val (.word tw)) := hc_t
              have hent_k : ent.locals.lookup (ofString "key") = some (.val (.word kw)) := hc_k
              have hargs_hg : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
                  [.var .local (ofString "t"), .var .local (ofString "key")] =
                  some [.val (.word tw), .val (.word kw)] := by
                simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hent_t, hent_k]
              rw [hargs_hg] at hrun; dsimp only at hrun
              rcases hlk_hg : lookupCodeHOLFinite ent.code.lookup (ofString "htab_get")
                  [.val (.word tw), .val (.word kw)] with _ | ⟨bhg, chg, rhg⟩
              · rw [hlk_hg] at hrun; simp at hrun
              · rw [hlk_hg] at hrun; dsimp only at hrun
                by_cases hcz_ent : ent.clock = 0
                · simp [hcz_ent] at hrun
                rw [if_neg hcz_ent] at hrun
                have hbhg_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "htab_get")
                  _ _ bhg _ rhg _ chg EvmFrameSpecs.lookup_htab_get (by rwa [← show ent.code = originalRuntimeCode from hcode])
                subst hbhg_eq
                have hchg_t' : chg.lookup (ofString "t") = some (.val (.word tw)) := by
                  have ht_ev : evalAt ent (.var .local (ofString "t")) = some (.val (.word tw)) := by
                    simp [evalAt, evalHOLExact, toExact, hent_t]
                  have ⟨v1', _, he1', _, hc1', _⟩ := callee_param_two_r16_code ent (ofString "htab_get")
                    (ofString "t") (ofString "key") .one .one _ _
                    (by rw [show ent.code = originalRuntimeCode from hcode]; exact EvmFrameSpecs.lookup_htab_get)
                    (.var .local (ofString "t")) (.var .local (ofString "key"))
                    _ _ chg rhg hargs_hg hlk_hg
                  rw [ht_ev] at he1'; injection he1' with h'; subst h'; exact hc1'
                have hchg_k' : chg.lookup (ofString "key") = some (.val (.word kw)) := by
                  have hk_ev : evalAt ent (.var .local (ofString "key")) = some (.val (.word kw)) := by
                    simp [evalAt, evalHOLExact, toExact, hent_k]
                  have ⟨_, v2', _, he2', _, hc2'⟩ := callee_param_two_r16_code ent (ofString "htab_get")
                    (ofString "t") (ofString "key") .one .one _ _
                    (by rw [show ent.code = originalRuntimeCode from hcode]; exact EvmFrameSpecs.lookup_htab_get)
                    (.var .local (ofString "t")) (.var .local (ofString "key"))
                    _ _ chg rhg hargs_hg hlk_hg
                  rw [hk_ev] at he2'; injection he2' with h'; subst h'; exact hc2'
                let ent_hg := callEntryStateHOLFinite ent chg
                rcases hrun_hg : evaluateHOLFiniteState ent_hg (sourceFnBody Guest.Software.guestFn_htab_get) with ⟨res_hg, p_hg⟩
                dsimp only [ent_hg] at hrun_hg
                rw [hrun_hg] at hrun
                cases res_hg with
                | none => simp at hrun
                | some cr_hg =>
                  cases cr_hg with
                  | exception eid_hg ev_hg =>
                    exfalso
                    dsimp only at hrun; injection hrun with hr_eq _
                    cases hr_eq
                  | timeOut | error | «break» | «continue» | finalFfi _ => simp at hrun
                  | returned v_old =>
                    dsimp only at hrun
                    split at hrun <;> try simp at hrun
                    have htw_nz : tw ≠ 0 := WkBal.htab_get_t_nonzero ent_hg tw kw
                      (guestInv_callEntry ent chg hWent.1.1) hchg_t' hchg_k' v_old
                      (by dsimp only [ent_hg]; rw [hrun_hg])
                    have ht0_nz : memW s (globN s "ts" + 32) ≠ 0 := by
                      intro h0; apply htw_nz; apply BitVec.eq_of_toNat_eq
                      change tw.toNat = 0; simpa [htw_nat] using h0
                    obtain ⟨_, S0, hWT0⟩ := hW
                    have htw_S0 : tw.toNat ∈ S0 := by
                      rw [htw_nat]; exact (ts32Slot_disj s S0 hWT0.1 hts_nz ht0_nz).1
                    have hwf_hg : HtabWF ent_hg tw.toNat :=
                      (htabWF_with_locals s chg (ent.clock - 1) tw.toNat).2 (hWT0.1.2.1 _ htw_S0).1
                    obtain ⟨f0, f1, rfl, hf1_in⟩ := WkBal.htab_get_ret_in_values ent_hg tw kw
                      hcode hchg_t' hchg_k' hwf_hg v_old
                      (by dsimp only [ent_hg]; rw [hrun_hg])
                    have hro_hg := FunSpec.at_lookup EvmFrameSpecs.ro_htab_get ent hcode
                      _ (sourceFnBody Guest.Software.guestFn_htab_get) chg rhg hlk_hg
                      (guestInv_callEntry ent chg hWent.1.1) (by rw [hrun_hg]; simp)
                    have hro_hg' : ((evaluateHOLFiniteState ent_hg (sourceFnBody Guest.Software.guestFn_htab_get)).2) = _ :=
                      hro_hg (by rw [hrun_hg]; exact Or.inl ⟨_, rfl⟩)
                    dsimp only [ent_hg] at hro_hg'
                    rw [hrun_hg] at hro_hg'
                    dsimp only at hro_hg'
                    set s_old := setVarHOLFinite (ofString "old") (.rStruct [.val (.word f0), .val (.word f1)])
                      { p_hg with locals := ent.locals }
                    have heff_old : WorldEff ent s_old [] [] ["heap_ptr"] :=
                      ((WorldEff.refl ent [] [] ["heap_ptr"] hWent.1 hcode).of_readOnly hro_hg').locals_clock _ _
                    have hg_all_old : ∀ k : MlS, s_old.globals.lookup k = ent.globals.lookup k := by
                      intro k; dsimp only [s_old, setVarHOLFinite]; rw [hro_hg']; rfl
                    have hold_t : s_old.locals.lookup (ofString "t") = some (.val (.word tw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_t,
                        show ofString "old" ≠ ofString "t" by decide]
                    have hold_k : s_old.locals.lookup (ofString "key") = some (.val (.word kw)) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_k,
                        show ofString "old" ≠ ofString "key" by decide]
                    have hold_old : s_old.locals.lookup (ofString "old") =
                        some (.rStruct [.val (.word f0), .val (.word f1)]) := by
                      simp [s_old, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                    rcases hs1_run : evaluateHOLFiniteState s_old
                        (.seq
                          (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0#64))
                            (.return (.const 0#64))
                            .skip)
                          (journalAppendTailProg 5#64 (.const 1#64)
                            (.seq
                              (.call (some (none, none)) (ofString "htab_del")
                                [.var .local (ofString "t"), .var .local (ofString "key")])
                              (.return (.const 0#64))))) with ⟨rs1_res, ms1⟩
                    rw [hs1_run] at hrun; dsimp only at hrun
                    have hrs1_eq : rs1_res = some (.returned rv) := hrun.1
                    have hpost_ms1 : post = { ms1 with locals := post.locals } := by
                      have hp2 := hrun.2.symm
                      rw [hp2]
                    subst hrs1_eq
                    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hs1_run
                    by_cases hf0_z : f0 = 0#64
                    · subst hf0_z
                      have hev_cmp1 : @evalHOLExact 64 F _ s_old.toExact (fun a => Classical.propDecidable (s_old.memaddrs a))
                          (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0#64)) =
                          some (.val (.word 1#64)) := by
                        simp [evalHOLExact, toExact, hold_old, Compiler.Encoders.Asm.wordCmpHOL]
                      rw [hev_cmp1] at hs1_run; dsimp only at hs1_run
                      rw [if_neg (show (1#64 : BitVec 64) ≠ 0 by decide), evaluateHOLFiniteState_return] at hs1_run
                      simp only [evalHOLExact, toExact, shapeOfHOLExact, sizeOfShapeWithContextHOL,
                        show (1 : Nat) ≤ 32 by decide, ↓reduceIte, emptyLocalsHOLFinite] at hs1_run
                      have hpost_eq : post = { ent with locals := post.locals, clock := post.clock } := by
                        have hp2 := ((Prod.mk.inj hs1_run).2).symm
                        rw [hpost_ms1, hp2]; dsimp only [s_old, setVarHOLFinite]
                        rw [hro_hg']; rfl
                      rw [hpost_eq]
                      have hstep_ent : WorldStepCodeSc [] ["heap_ptr", "journal_n"]
                          ent none { ent with locals := post.locals, clock := post.clock } :=
                        worldStepCodeSc_with_locals_clock (r' := none)
                          (worldStepCodeSc_refl [] ["heap_ptr", "journal_n"] ent none hWent.1) post.locals post.clock
                      exact worldStepCodeSc_mono_bufs
                        (fun _ h => by cases h)
                        (fun g hg => by simp at hg; rcases hg with rfl | rfl <;> assumption)
                        (worldStepCodeSc_from_entry (r' := none) (callee := callee) (L := s.locals) (k := post.clock) hstep_ent)
                    · have hnl0 : Compiler.Encoders.Asm.wordCmpHOL .equal f0 0#64 = false := by
                        simp [Compiler.Encoders.Asm.wordCmpHOL, hf0_z]
                      have hev_cmp0 : @evalHOLExact 64 F _ s_old.toExact (fun a => Classical.propDecidable (s_old.memaddrs a))
                          (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0#64)) =
                          some (.val (.word 0#64)) := by
                        simp [evalHOLExact, toExact, hold_old, hnl0]
                      rw [hev_cmp0] at hs1_run; dsimp only at hs1_run
                      simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hs1_run
                      have hf1_in_ent : f1.toNat ∈ htabValues ent tw.toNat := hf1_in hf0_z
                      obtain ⟨mid, tailPost, hstep_j, hmid_t, hmid_k, _, hmid_tail, hms1_tp⟩ :=
                        journal_append_block_step_code ent s_old
                          5#64 (.const 1#64) tw kw f0 f1 1#64 hWent heff_old hg_all_old
                          hold_t hold_k hold_old
                          (fun st _ => by simp [evalHOLExact, toExact])
                          (fun S hTS => by
                            have hts_ent : globN ent "ts" = globN s "ts" := rfl
                            have hm32_ent : memW ent (globN ent "ts" + 32) = memW s (globN s "ts" + 32) := rfl
                            obtain ⟨ht0_S, _, _, _, _, hne_16⟩ := ts32Slot_disj ent S hTS hts_nz (by rw [hm32_ent]; exact ht0_nz)
                            have htw_S : tw.toNat ∈ S := by rwa [htw_nat, ← hm32_ent]
                            have hjr_32 : journalRole ent tw.toNat = "ts+32" := by
                              unfold journalRole
                              rw [if_neg (fun ⟨_, h16⟩ => hne_16 (by rw [hm32_ent, ← htw_nat]; exact h16.symm))]
                              rw [if_pos ⟨hts_nz, by rw [hm32_ent]; exact htw_nat⟩]
                            have hf1_S : f1.toNat ∈ S := by
                              have hv_in : HtabValuesIn ent (memW ent (globN ent "ts" + 32)) S :=
                                hTS.2.2.2.2.2.2.2.2.1 hts_nz ht0_S
                              have hf1_vals : f1.toNat ∈ htabValues ent (memW ent (globN ent "ts" + 32)) := by
                                rwa [hm32_ent, ← htw_nat]
                              obtain ⟨idx, hidx_mem, hidx_eq⟩ := List.mem_map.1 hf1_vals
                              rw [← hidx_eq]
                              exact hv_in idx (List.mem_range.1 hidx_mem)
                            have hf1_nz : f1.toNat ≠ 0 := by
                              intro h0
                              have hwf0 : HtabWF ent 0 := h0 ▸ (hTS.2.1 _ hf1_S).1
                              have hin0 := (hwf0.1 (0, 88) (by unfold htabFootprint; simp)).1
                              unfold Inside sourceBase at hin0
                              omega
                            have hts_ent_nz : globN ent "ts" ≠ 0 := by rwa [hts_ent]
                            have hf1_wrs : (f1.toNat, "ts.inner") ∈ worldRoleSlots ent := by
                              unfold worldRoleSlots
                              rw [List.mem_filter]
                              refine ⟨?_, by simp [hf1_nz]⟩
                              have hnr : (f1.toNat, "ts.inner") ∈ nestRoles ent "ts" "ts.inner" := by
                                unfold nestRoles
                                rw [if_neg hts_ent_nz, if_neg (by rw [hm32_ent]; exact ht0_nz)]
                                refine List.mem_map.2 ⟨f1.toNat, ?_, rfl⟩
                                rwa [hm32_ent, ← htw_nat]
                              exact List.mem_append_left _ (List.mem_append_right _ hnr)
                            have htw_wrs : (tw.toNat, "ts+32") ∈ worldRoleSlots ent := by
                              have hm32_wrs : (memW ent (globN ent "ts" + 32), "ts+32") ∈ worldRoleSlots ent := by
                                apply mem_worldRoleSlots_recRole ent "ts" 32 "ts+32" hts_ent_nz
                                  (by rw [hm32_ent]; exact ht0_nz)
                                apply List.mem_append.2; right
                                unfold recRoles; simp [hts_ent_nz]
                              rwa [hm32_ent, ← htw_nat] at hm32_wrs
                            refine ⟨htw_S, ?_⟩
                            dsimp only
                            rw [hjr_32]
                            have h1nz : (1#64 : BitVec 64).toNat ≠ 0 ∧ "ts+32" = "ts+32" := ⟨by decide, rfl⟩
                            rw [if_pos h1nz]
                            rintro p hp
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
                            rcases hp with rfl | rfl
                            · exact htw_wrs
                            · exact hf1_wrs)
                          hs1_run
                      have hW_mid : WorldOK mid := hstep_j.worldOK_bufs (fun _ h => by cases h) hWent
                      have hmid_code : mid.code = originalRuntimeCode := hW_mid.1.1.code
                      have hts_mid : globN mid "ts" = globN ent "ts" :=
                        globN_eq_of_lookup (hstep_j.1.1.2.2.1 (ofString "ts") (by decide))
                      have hm32_mid : memW mid (globN mid "ts" + 32) = tw.toNat := by
                        rw [hts_mid]
                        have hrk32 := hstep_j.1.1.2.2.2.1
                          ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]) (by simp [R10Shards.P26_P28.stdKeep]) hts_nz
                          32 (by simp) (fun _ h => by cases h)
                        exact hrk32.trans htw_nat.symm
                      obtain ⟨s_hd, hhd, hret_hd⟩ := seq_call0_ret_inv hmid_tail
                      rw [evaluateHOLFiniteState_return] at hret_hd
                      simp only [evalHOLExact, toExact, shapeOfHOLExact, sizeOfShapeWithContextHOL,
                        show (1 : Nat) ≤ 32 by decide, ↓reduceIte, emptyLocalsHOLFinite] at hret_hd
                      have htp_eq : tailPost = { s_hd with locals := HolFiniteMapExact.empty } :=
                        ((Prod.mk.inj hret_hd).2).symm
                      rw [evaluateHOLFiniteState_call] at hhd
                      have hargs_hd : evalListHOLFinite mid (h := fun a => Classical.propDecidable (mid.memaddrs a))
                          [.var .local (ofString "t"), .var .local (ofString "key")] =
                          some [.val (.word tw), .val (.word kw)] := by
                        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, hmid_t, hmid_k]
                      rw [hargs_hd] at hhd; dsimp only at hhd
                      rcases hlk_hd : lookupCodeHOLFinite mid.code.lookup (ofString "htab_del")
                          [.val (.word tw), .val (.word kw)] with _ | ⟨bhd, chd, rhd'⟩
                      · rw [hlk_hd] at hhd; simp at hhd
                      · rw [hlk_hd] at hhd; dsimp only at hhd
                        by_cases hcz_mid : mid.clock = 0
                        · simp [hcz_mid] at hhd
                        rw [if_neg hcz_mid] at hhd
                        have hbhd_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "htab_del")
                          _ _ bhd _ rhd' _ chd lookup_htab_del_r16 (by rwa [← hmid_code])
                        subst hbhd_eq
                        obtain ⟨v1_hd, _, he1_hd, _, hchd_t, _⟩ := callee_param_two_r16_code mid (ofString "htab_del")
                          (ofString "t") (ofString "key") .one .one _ _
                          (by rw [hmid_code]; exact lookup_htab_del_r16)
                          (.var .local (ofString "t")) (.var .local (ofString "key"))
                          _ _ chd rhd' hargs_hd hlk_hd
                        have hv1_hd_eq : v1_hd = .val (.word tw) := by
                          simp [evalAt, evalHOLExact, toExact, hmid_t] at he1_hd; exact he1_hd.symm
                        subst hv1_hd_eq
                        let ent_hd := callEntryStateHOLFinite mid chd
                        have hloc_t_hd : locN ent_hd "t" = memW mid (globN mid "ts" + 32) := by
                          simp [locN, ent_hd, callEntryStateHOLFinite, hchd_t, hm32_mid]
                        rcases hrun_hd : evaluateHOLFiniteState ent_hd (sourceFnBody Guest.Software.guestFn_htab_del) with ⟨res_hd, p_hd⟩
                        dsimp only [ent_hd] at hrun_hd
                        rw [hrun_hd] at hhd
                        cases res_hd with
                        | none => simp at hhd
                        | some cr_hd2 =>
                          cases cr_hd2 with
                          | returned v_hd =>
                            dsimp only at hhd
                            split at hhd <;> try simp at hhd
                            have hs_hd_eq : s_hd = { p_hd with locals := mid.locals } := hhd.symm
                            have hts_mid_nz : globN mid "ts" ≠ 0 := by rwa [hts_mid]
                            have ht0_mid_nz : memW mid (globN mid "ts" + 32) ≠ 0 := by
                              rw [hm32_mid]; intro h0; apply htw_nz; exact BitVec.eq_of_toNat_eq h0
                            have hArg_hd : HtabArgWF ent_hd := by
                              obtain ⟨hAm, Sm, hTm, _⟩ := hW_mid
                              have ht0_Sm := (ts32Slot_disj mid Sm hTm hts_mid_nz ht0_mid_nz).1
                              refine ⟨localsFree_arenaReady mid _ _ hAm, ?_, ?_⟩
                              · rw [hloc_t_hd]; exact (htabWF_with_locals mid chd (mid.clock - 1) _).2 (hTm.2.1 _ ht0_Sm).1
                              · rw [hloc_t_hd]; exact fun i hi => ((hTm.2.1 _ ht0_Sm).2 i hi).1
                            have hd_sub := htab_del_values_sub ent_hd hmid_code hArg_hd v_hd
                              (by dsimp only [ent_hd]; rw [hrun_hd])
                            dsimp only [ent_hd] at hd_sub
                            have hd_p_eq : (evaluateHOLFiniteState (callEntryStateHOLFinite mid chd)
                                (sourceFnBody Guest.Software.guestFn_htab_del)).2 = p_hd := by
                              rw [hrun_hd]
                            rw [hd_p_eq] at hd_sub
                            obtain ⟨hex_hd, hbe_hd, hvals_sub⟩ := hd_sub
                            dsimp only [HtabExit] at hex_hd
                            rw [hloc_t_hd] at hex_hd hvals_sub
                            obtain ⟨hAp_hd, hwf_hd, hh0_hd, _, hhp_hd, hfp_hd, hfr_hd, hg_hd⟩ := hex_hd
                            have hstep_hd0 : WorldStepCodeSc [] ["heap_ptr"] mid none p_hd :=
                              worldStepCodeSc_of_htabDel_ts32 hW_mid hbe_hd hg_hd hg_hd hts_mid_nz ht0_mid_nz
                                hAp_hd hwf_hd hh0_hd hvals_sub hhp_hd hfp_hd hfr_hd
                            have hstep_hd : WorldStepCodeSc [] ["heap_ptr", "journal_n"] mid none post := by
                              have hp_post : post = { p_hd with locals := post.locals, clock := post.clock } := by
                                rw [hpost_ms1, hms1_tp, htp_eq, hs_hd_eq]
                              rw [hp_post]
                              exact worldStepCodeSc_mono_bufs
                                (fun _ h => by cases h) (by simp)
                                (worldStepCodeSc_with_locals_clock (r' := none) hstep_hd0 post.locals post.clock)
                            have hstep_ent : WorldStepCodeSc [] ["heap_ptr", "journal_n"] ent none post :=
                              worldStepCodeSc_trans (B := []) (gw := ["heap_ptr", "journal_n"])
                                posBufList_nil (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)
                                hstep_j hstep_hd
                            exact worldStepCodeSc_mono_bufs
                              (fun _ h => by cases h)
                              (fun g hg => by simp at hg; rcases hg with rfl | rfl <;> assumption)
                              (worldStepCodeSc_from_entry (r' := none) (callee := callee) (L := s.locals) (k := post.clock) hstep_ent)
                          | _ => simp at hhd
            · rename_i hbad; simp only [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error

/-! ## 3. `set_account` -/

theorem wkCodeSc_set_account :
    WorldKeepsCodeSc [] ["heap_ptr", "journal_n"] (ofString "set_account") := by
  have hB := posBufList_nil
  have hgw : SafeStepGlobals ["heap_ptr", "journal_n"] := by
    intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp
  refine worldKeepsCodeSc_of_progWStepCode lookup_set_account ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_set_account,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCode_seq hB hgw ?_ (progWStepCode_return _ _ _)
  exact progWStepCode_call0_jset_ts16 [] ["heap_ptr", "journal_n"] (by simp) (by simp) _ _

/-! ## 4. `ProgWStepCodeOuter` Combinators -/

def ProgWStepCodeOuter (tw : BitVec 64) (B : BufList) (gw : List String) (prog : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    s.code = originalRuntimeCode → WorldOK s →
    s.locals.lookup (ofString "outer") = some (.val (.word tw)) →
    tw.toNat = memW s (globN s "ts" + 32) → globN s "ts" ≠ 0 →
    (evaluateHOLFiniteState s prog).1 ≠ some .timeOut →
    FlowingOrResumes (evaluateHOLFiniteState s prog).1 →
    WorldStepCodeSc B gw
      s (evaluateHOLFiniteState s prog).1 (evaluateHOLFiniteState s prog).2

theorem progWStepCodeOuter_of_progWStepCode (tw : BitVec 64) {B : BufList} {gw : List String}
    {prog : ProgHOL 64} (h : ProgWStepCode B gw prog) : ProgWStepCodeOuter tw B gw prog :=
  fun s hc hW _ _ _ hnt hfr => h s hc hW hnt hfr

theorem worldStepCodeSc_preserves_ts32 {F : Type} {s mid : PanSemStateFiniteExact 64 F}
    {B : BufList} {gw : List String} {r} {tw : BitVec 64}
    (hB : PosBufList B) (hgw : SafeStepGlobals gw) (hW : WorldOK s)
    (hstep : WorldStepCodeSc B gw s r mid)
    (htw : tw.toNat = memW s (globN s "ts" + 32)) (hts : globN s "ts" ≠ 0) :
    tw.toNat = memW mid (globN mid "ts" + 32) ∧ globN mid "ts" ≠ 0 := by
  have hk_ts : ofString "ts" ∉ gw.map ofString := hgw.not_mem_map (by decide)
  have hts_eq : globN mid "ts" = globN s "ts" := globN_eq_of_lookup (hstep.1.1.2.2.1 _ hk_ts)
  refine ⟨?_, by rwa [hts_eq]⟩
  rw [hts_eq]
  obtain ⟨_, S, hWT⟩ := hW
  obtain ⟨Nd, hWTn⟩ := (worldTyped_iff_with s S).1 hWT
  have hrk := hstep.1.1.2.2.2.1 ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]) (by simp [R10Shards.P26_P28.stdKeep]) hts
    32 (by simp) (typed_record_field_avoids_validBufList hWTn hB "ts" 72 32 (by simp [typedRecords]) hts (by omega))
  exact htw.trans hrk.symm

theorem progWStepCodeOuter_dec {tw : BitVec 64} {B : BufList} {gw : List String}
    {x : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {body : ProgHOL 64}
    (hne : x ≠ ofString "outer") (hb : ProgWStepCodeOuter tw B gw body) :
    ProgWStepCodeOuter tw B gw (.dec x sh e body) := by
  intro F s hc hW hout htw hts hnt hfr
  rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | val
  · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hev] at hnt hfr ⊢
    by_cases hok : shapeEqHOL sh (shapeOfHOLExact val) = true
    · simp only [hok, ↓reduceIte] at hnt hfr ⊢
      set s1 := setVarHOLFinite x val s
      have hW1 : WorldOK s1 := localsFree_worldOK s _ s.clock hW
      have hout1 : s1.locals.lookup (ofString "outer") = some (.val (.word tw)) := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hout]
      have hstep := hb s1 hc hW1 hout1 htw hts hnt hfr
      exact worldStepCodeSc_with_locals_clock (worldStepCodeSc_of_pre_locals_clock hstep)
        _ (evaluateHOLFiniteState s1 body).2.clock
    · simp [hok] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem progWStepCodeOuter_decCall {tw : BitVec 64} {B Bf : BufList} {gw gwf : List String}
    {x : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hne : x ≠ ofString "outer")
    (hBvalid : PosBufList B) (hgwSafe : SafeStepGlobals gw)
    (hB : ∀ p ∈ Bf, p ∈ B) (hgw : ∀ g ∈ gwf, g ∈ gw)
    (hf : WorldKeepsCodeSc Bf gwf fname)
    (hcont : ProgWStepCodeOuter tw B gw cont) :
    ProgWStepCodeOuter tw B gw (.decCall x sh fname args cont) := by
  intro F s hc hW hout htw hts hnt hfr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        let ent := callEntryStateHOLFinite s callee
        have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata ent body').1
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
        simp only [ent] at hrun hmeta
        simp only [hrun] at hmeta hnt hfr ⊢
        have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro rfl; exact hnt (by simp)
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh && shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
              simp only [ent, hrun] at hspec
              have hstep1 : WorldStepCodeSc B gw ent (some (.returned v)) cpost :=
                worldStepCodeSc_mono_bufs hB hgw (hspec (Or.inl ⟨v, rfl⟩))
              set s1 := setVarHOLFinite x v { cpost with locals := s.locals }
              have hs1_step : WorldStepCodeSc B gw s none s1 := by
                simpa only [s1, setVarHOLFinite] using
                  (worldStepCodeSc_from_entry (r' := none) (callee := callee)
                    (L := s.locals.update (x, v)) (k := cpost.clock) hstep1)
              have hWs1 : WorldOK s1 := hs1_step.worldOK_bufs hBvalid.1 hW
              have hs1_code : s1.code = originalRuntimeCode := hmeta.trans hc
              have hout1 : s1.locals.lookup (ofString "outer") = some (.val (.word tw)) := by
                simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hout]
              obtain ⟨htw1, hts1⟩ := worldStepCodeSc_preserves_ts32 hBvalid hgwSafe hW hs1_step htw hts
              have hstep2 := hcont s1 hs1_code hWs1 hout1 htw1 hts1 hnt hfr
              have hstep2' := worldStepCodeSc_with_locals_clock (r' := (evaluateHOLFiniteState s1 cont).1) hstep2
                (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 cont).2.locals (x, s.locals.lookup x))
                (evaluateHOLFiniteState s1 cont).2.clock
              exact worldStepCodeSc_trans hBvalid hgwSafe hs1_step hstep2'
            · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
            simp only [ent, hrun] at hspec
            exact worldStepCodeSc_from_entry (worldStepCodeSc_mono_bufs hB hgw (hspec hres_ex))

theorem progWStepCodeOuter_seq {tw : BitVec 64} {B : BufList} {gw : List String} {p1 p2 : ProgHOL 64}
    (hB : PosBufList B) (hgw : SafeStepGlobals gw) (hp1_no : avoidsLocal (ofString "outer") p1 = true)
    (h1 : ProgWStepCode B gw p1) (h2 : ProgWStepCodeOuter tw B gw p2) :
    ProgWStepCodeOuter tw B gw (.seq p1 p2) := by
  intro F s hc hW hout htw hts hnt hfr
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s p1).1
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt hfr ⊢
  cases r1 with
  | none =>
    have hs1 := h1 s hc hW (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at hs1; dsimp only at hs1
    have hW_mid : WorldOK mid := hs1.worldOK_bufs hB.1 hW
    have hout_mid : mid.locals.lookup (ofString "outer") = some (.val (.word tw)) := by
      have hp := evaluate_avoidsLocal_flowing (ofString "outer") p1 hp1_no s (by rw [hr1]; exact Or.inl rfl)
      rw [hr1] at hp; exact hp.trans hout
    obtain ⟨htw_m, hts_m⟩ := worldStepCodeSc_preserves_ts32 hB hgw hW hs1 htw hts
    have hs2 := h2 mid (hmeta.trans hc) hW_mid hout_mid htw_m hts_m hnt hfr
    exact worldStepCodeSc_trans hB hgw hs1 hs2
  | some r =>
    have hs1 := h1 s hc hW (by rw [hr1]; exact hnt) (by rw [hr1]; exact hfr)
    rw [hr1] at hs1
    exact hs1

theorem progWStepCodeOuter_of_dec_ts32 {B : BufList} {gw : List String} {body : ProgHOL 64}
    (hb : ∀ tw : BitVec 64, ProgWStepCodeOuter tw B gw body) :
    ProgWStepCode B gw (.dec (ofString "outer") .one
      (.load .one (.op .add [.var .global (ofString "ts"), .const 32#64])) body) := by
  intro F s0 hc0 hW0 hnt0 hfr0
  rw [evaluateHOLFiniteState_dec_total] at hnt0 hfr0 ⊢
  rcases hev_o : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ts"), .const 32#64])) with _ | vo
  · simp [hev_o] at hfr0; exact absurd hfr0 not_flowingOrResumes_error
  · simp only [hev_o] at hnt0 hfr0 ⊢
    obtain ⟨tw, rfl, htw_nat, hts_nz⟩ := evalAt_loadG_nz s0 hW0.1.1 "ts" 32#64 (by decide) vo hev_o
    have hsh_ok : shapeEqHOL .one (shapeOfHOLExact (.val (.word tw) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hsh_ok, ↓reduceIte] at hnt0 hfr0 ⊢
    set s1 := setVarHOLFinite (ofString "outer") (.val (.word tw)) s0
    have hW1 : WorldOK s1 := localsFree_worldOK s0 _ s0.clock hW0
    have hs1_outer : s1.locals.lookup (ofString "outer") = some (.val (.word tw)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hstep := hb tw s1 hc0 hW1 hs1_outer htw_nat hts_nz hnt0 hfr0
    exact worldStepCodeSc_with_locals_clock (worldStepCodeSc_of_pre_locals_clock hstep)
      (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 body).2.locals
        (ofString "outer", s0.locals.lookup (ofString "outer")))
      (evaluateHOLFiniteState s1 body).2.clock

/-! ## 5. `destroy_storage`, `destroy_account`, `modify_state_commit` -/

theorem wkCodeSc_destroy_storage :
    WorldKeepsCodeSc [("sk_buf", 52)] ["heap_ptr", "journal_n"]
      (ofString "destroy_storage") := by
  have hB := posBufList_sk
  have hgw : SafeStepGlobals ["heap_ptr", "journal_n"] := by
    intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp
  refine worldKeepsCodeSc_of_progWStepCode lookup_destroy_storage ?_
  simp only [sourceFunctionEntry, Guest.Software.guestFn_destroy_storage,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCodeOuter_of_dec_ts32 (fun tw => ?_)
  refine progWStepCodeOuter_decCall (by decide) hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsCodeSc_of_readOnly EvmFrameSpecs.ro_htab_get) ?_
  refine progWStepCodeOuter_seq hB hgw (by decide)
    (progWStepCode_ite (progWStepCode_return _ _ _) (progWStepCode_skip _ _)) ?_
  refine progWStepCodeOuter_dec (by decide) ?_
  refine progWStepCodeOuter_dec (by decide) ?_
  refine progWStepCodeOuter_dec (by decide) ?_
  refine progWStepCodeOuter_seq hB hgw (by decide) ?_ ?_
  · refine progWStepCode_while hB hgw ?_
    refine progWStepCode_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
      (worldKeepsCodeSc_of_readOnly ro_htab_item) ?_
    refine progWStepCode_seq hB hgw ?_ (progWStepCode_assign_local _ _ _ _)
    refine progWStepCode_ite ?_ (progWStepCode_skip _ _)
    refine progWStepCode_decCall hB hgw (by intro p hp; exact hp) (by intro g hg; cases hg)
      wkCodeSc_sk_make ?_
    exact progWStepCode_call0_htab_set_recSlot "ts" "ts+24" 24 _ _ (by simp) (by decide)
      (fun s S hT hts ht0 => nonCodeValueSlot_ts24 s S hT hts ht0)
  · intro F' s' hc' hW' hout' htw' hts' hnt' hfr'
    have hmeta' := (PanRunBounded.evaluateHOLFiniteState_metadata s'
      (.call (some (none, none)) (ofString "jdel") [.var .local (ofString "outer"), .var .local (ofString "addr")])).1
    rw [evaluateHOLFiniteState_seq_line780] at hnt' hfr' ⊢
    rcases hr1 : evaluateHOLFiniteState s'
      (.call (some (none, none)) (ofString "jdel") [.var .local (ofString "outer"), .var .local (ofString "addr")]) with ⟨r1, mid⟩
    simp only [hr1] at hmeta' hnt' hfr' ⊢
    have ht_ev : evalAt s' (.var .local (ofString "outer")) = some (.val (.word tw)) := by
      simp [evalAt, evalHOLExact, toExact, hout']
    cases r1 with
    | none =>
      have hs1 := jdel_ts32_step_code [("sk_buf", 52)] ["heap_ptr", "journal_n"] (by simp) (by simp)
        (.var .local (ofString "outer")) (.var .local (ofString "addr"))
        s' hc' hW' tw ht_ev htw' hts' (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
      rw [hr1] at hs1; dsimp only at hs1
      have hW_mid : WorldOK mid := hs1.worldOK_bufs hB.1 hW'
      have hs2 := progWStepCode_return [("sk_buf", 52)] ["heap_ptr", "journal_n"] (.const 0#64)
        mid (hmeta'.trans hc') hW_mid hnt' hfr'
      exact worldStepCodeSc_trans hB hgw hs1 hs2
    | some r =>
      have hs1 := jdel_ts32_step_code [("sk_buf", 52)] ["heap_ptr", "journal_n"] (by simp) (by simp)
        (.var .local (ofString "outer")) (.var .local (ofString "addr"))
        s' hc' hW' tw ht_ev htw' hts' (by rw [hr1]; exact hnt') (by rw [hr1]; exact hfr')
      rw [hr1] at hs1
      exact hs1

theorem wkCodeSc_destroy_account :
    WorldKeepsCodeSc [("sk_buf", 52)] ["heap_ptr", "journal_n"]
      (ofString "destroy_account") := by
  have hB := posBufList_sk
  have hgw : SafeStepGlobals ["heap_ptr", "journal_n"] := by
    intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp
  refine worldKeepsCodeSc_of_progWStepCode lookup_destroy_account ?_
  simp only [sourceFunctionEntry,
    Guest.Software.guestFn_set_account,
    Guest.Software.guestFn_destroy_account,
    Guest.Software.guestFn_modify_state_commit,
    Guest.Software.guestFn_clear_account_preserving_balance,
    Guest.Software.guestFn_create_ether,
    Guest.Software.guestFn_increment_nonce,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCode_seq hB hgw
    (progWStepCode_call0 (by intro p hp; exact hp) (by intro g hg; exact hg) wkCodeSc_destroy_storage) ?_
  refine progWStepCode_seq hB hgw
    (progWStepCode_call0 (by intro p hp; cases hp) (by intro g hg; exact hg) wkCodeSc_set_account) ?_
  exact progWStepCode_return _ _ _

theorem wkCodeSc_modify_state_commit :
    WorldKeepsCodeSc [("sk_buf", 52)] ["heap_ptr", "journal_n"]
      (ofString "modify_state_commit") := by
  have hB := posBufList_sk
  have hgw : SafeStepGlobals ["heap_ptr", "journal_n"] := by
    intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp
  refine worldKeepsCodeSc_of_progWStepCode lookup_modify_state_commit ?_
  simp only [sourceFunctionEntry, Guest.Software.guestFn_modify_state_commit,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepCode_seq hB hgw
    (progWStepCode_call0 (by intro p hp; cases hp) (by intro g hg; exact hg) wkCodeSc_set_account) ?_
  refine progWStepCode_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsCodeSc_of_readOnly ro_acct_is_empty) ?_
  refine progWStepCode_seq hB hgw ?_ (progWStepCode_return _ _ _)
  exact progWStepCode_ite
    (progWStepCode_call0 (by intro p hp; exact hp) (by intro g hg; exact hg) wkCodeSc_destroy_account)
    (progWStepCode_skip _ _)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
