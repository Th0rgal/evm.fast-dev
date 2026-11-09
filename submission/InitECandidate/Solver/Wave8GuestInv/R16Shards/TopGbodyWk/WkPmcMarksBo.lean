import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPmcMarksBoA

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
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8Leaves.Rlp

theorem pmcBoDispatch_cut
    (hpm : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultMarksExactBo (ofString "process_message"))
    (hpcm : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultMarksBo (ofString "process_create_message")) :
    PmcBoCut pmcDispatch PmcBoA1 PmcBoA2 := by
  intro F entry tail htail s hcode ⟨hp1, hu_s, hbo_eq_s⟩
  obtain ⟨hM0, hM_s, hs_msg, hsp_s, w_out, hws_s, hs_out, hs_fr, hw_out8, hw_in_s, hw_ok_s, hmem16_s,
    S_s, Nd_s, hMAs, hout_ow_s⟩ := hp1
  have hWOK_en : WorldOK entry := msgReady_worldOK entry hM0
  have hWOK_s : WorldOK s := msgReady_worldOK s hM_s
  obtain ⟨S_m, hWT_m, _, _, hm_in_s, hm_ok_s, _, _, _, _, _⟩ := hM_s.2
  have hm_hi_s : locN s "msg" + 176 ≤ 2 ^ 64 :=
    (ivl_allocated_bound hM_s.1.2 (Or.inl hm_in_s)).2
  have ⟨w_msg, hs_msg_w, hw_msg_nat⟩ : ∃ w_msg : BitVec 64,
      s.locals.lookup (ofString "msg") = some (.val (.word w_msg)) ∧ w_msg.toNat = locN s "msg" := by
    have hm_pos : 0 < locN s "msg" := by
      have hsb : 0 < sourceBase := by decide
      exact Nat.lt_of_lt_of_le hsb hm_in_s.1
    unfold locN at hm_pos ⊢
    rcases hlk : s.locals.lookup (ofString "msg") with _ | ⟨w | _ | _⟩
    · simp [hlk] at hm_pos
    · cases w with
      | word wv => exact ⟨wv, rfl, by simp [hlk]⟩
    · simp [hlk] at hm_pos
    · simp [hlk] at hm_pos
  have hw_msg_ok_s : WordsOK s (w_msg.toNat, 176) := by rwa [hw_msg_nat]
  have hw_msg_hi_s : w_msg.toNat + 176 ≤ 2 ^ 64 := by rwa [hw_msg_nat]
  unfold PmcBoRun
  intro hres hnex
  unfold pmcDispatch pmcCode at hres hnex ⊢
  simp only [sourceFunctionEntry, Guest.Software.guestFn_process_message_call,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil,
    R13Shards.spineAt, R13Shards.spinePlug] at hres hnex ⊢
  have hload24 := pmc_load_local_off hs_msg_w hw_msg_ok_s hw_msg_hi_s (by decide) (show 24 < 176 by decide)
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres hnex ⊢
  have hcond24_ex : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.load .one (.op .add [.var .local (ofString "msg"), .const 24#64])) (.const 0#64)) =
      some (.val (.word (if BitVec.ofNat 64 (memW s (w_msg.toNat + 24)) = 0#64 then 1#64 else 0#64))) := by
    have hl24' : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "msg"), .const 24#64])) =
        some (.val (.word (BitVec.ofNat 64 (memW s (w_msg.toNat + 24))))) := hload24
    unfold evalHOLExact
    rw [hl24']
    simp [evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcond24_ex] at hres hnex ⊢
  dsimp only at hres hnex ⊢
  by_cases h24_eq : BitVec.ofNat 64 (memW s (w_msg.toNat + 24)) = 0#64
  · rw [if_pos h24_eq, if_neg (show ¬ ((1#64 : BitVec 64) = 0) by decide)] at hres hnex ⊢
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hres hnex ⊢
    have hload32 := pmc_load_local_off hs_msg_w hw_msg_ok_s hw_msg_hi_s (by decide) (show 32 < 176 by decide)
    have hargs_ad : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.load .one (.op .add [.var .local (ofString "msg"), .const 32#64])] =
        some [.val (.word (BitVec.ofNat 64 (memW s (w_msg.toNat + 32))))] := by
      rw [evalListHOLFinite_eq_toExact]
      change @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        [.load .one (.op .add [.var .local (ofString "msg"), .const (BitVec.ofNat 64 32)])] = _
      simp [evalListHOLExact, hload32]
    simp only [hargs_ad] at hres hnex ⊢
    set v_ad := ValueHOL.val (.word (BitVec.ofNat 64 (memW s (w_msg.toNat + 32))))
    rcases hl_ad : lookupCodeHOLFinite s.code.lookup (ofString "account_deployable") [v_ad]
        with _ | ⟨body_ad, callee_ad, ret_ad⟩
    · simp only [hl_ad] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hl_ad] at hres hnex ⊢
      by_cases hclk_ad : s.clock = 0
      · simp only [hclk_ad, ↓reduceIte] at hres
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      · simp only [hclk_ad, ↓reduceIte] at hres hnex ⊢
        let ent_ad := callEntryStateHOLFinite s callee_ad
        have hmeta_ad := (evaluateHOLFiniteState_metadata ent_ad body_ad).1
        rcases hrun_ad : evaluateHOLFiniteState ent_ad body_ad with ⟨res_ad, post_ad⟩
        dsimp only [ent_ad] at hrun_ad hmeta_ad
        rw [hrun_ad] at hmeta_ad
        dsimp only at hmeta_ad
        simp only [hrun_ad] at hres hnex ⊢
        have hnt_ad : (evaluateHOLFiniteState ent_ad body_ad).1 ≠ some .timeOut := by
          dsimp only [ent_ad]; rw [hrun_ad]
          rintro rfl
          exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        have hspec_ad := wkScBo_account_deployable.at_lookup s hcode [v_ad] body_ad callee_ad ret_ad hl_ad
          (localsFree_worldOK s callee_ad (s.clock - 1) hWOK_s) hnt_ad
        dsimp only [ent_ad] at hspec_ad
        rw [hrun_ad] at hspec_ad
        dsimp only at hspec_ad
        have hwsAcct_sub_pmc : ∀ p ∈ wsAcctBufs, p ∈ pmcBufs := by
          intro p hp
          simp only [wsAcctBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl <;> simp [pmcBufs]
        have hR1_sub : ∀ j ∈ bufRegions pmcBufs entry ++ [(globN entry "heap_ptr", globN s "heap_ptr" - globN entry "heap_ptr")],
            j ∈ bufRegions pmcBufs entry ∨ Inside j (globN entry "heap_ptr") (globN s "heap_ptr") := by
          intro j hj
          rcases List.mem_append.1 hj with hj_buf | hj_fr
          · exact Or.inl hj_buf
          · simp only [List.mem_singleton] at hj_fr; subst hj_fr
            exact Or.inr ⟨le_rfl, by have := hws_s.2.1; omega⟩
        cases res_ad with
        | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | some br_ad =>
          cases br_ad with
          | timeOut => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | error => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | «break» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | «continue» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | finalFfi _ => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | exception eid eval =>
            exact absurd hnex (nonExResult_not_exception rfl)
          | returned val_ad =>
            dsimp only at hres hnex ⊢
            have hret_ad_eq : ret_ad = .one :=
              lookupCodeHOLFinite_installed_return s (ofString "account_deployable") _ _ body_ad .one ret_ad
                [v_ad] callee_ad (by rw [hcode]; exact lookup_account_deployable) hl_ad
            subst hret_ad_eq
            by_cases hsh_ad : (shapeEqHOL (shapeOfHOLExact val_ad) .one &&
                shapeEqHOL (shapeOfHOLExact val_ad) .one) = true
            · simp only [hsh_ad, ↓reduceIte] at hres hnex ⊢
              have hsh1_ad : shapeEqHOL (shapeOfHOLExact val_ad) .one = true :=
                ((Bool.and_eq_true _ _).mp hsh_ad).1
              obtain ⟨w_dep, rfl⟩ : ∃ w : BitVec 64, val_ad = .val (.word w) := by
                rcases val_ad with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
                · exact ⟨w, rfl⟩
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh1_ad
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh1_ad
              set s_dep := setVarHOLFinite (ofString "dep") (.val (.word w_dep)) { post_ad with locals := s.locals }
              have hws_ad_raw := hspec_ad (Or.inl ⟨.val (.word w_dep), rfl⟩)
              have hws_ad_caller_bo : WorldStepScBo (bufRegions wsAcctBufs) ["heap_ptr", "scratch_ptr"]
                  EvmBase.stdKeep NoExtra s (some (.returned (.val (.word w_dep)))) post_ad :=
                WorldStepScBo.of_pre_locals_clock hws_ad_raw
              have hws_ad_caller : WorldStepSc (bufRegions wsAcctBufs) ["heap_ptr", "scratch_ptr"]
                  EvmBase.stdKeep NoExtra s (some (.returned (.val (.word w_dep)))) post_ad :=
                hws_ad_caller_bo.1
              have hu_s_post_ad : PtxBlockOutUnhit s post_ad :=
                hws_ad_caller_bo.2 (Or.inr (Or.inr (Or.inr ⟨.val (.word w_dep), rfl⟩)))
              have hu_dep : PtxBlockOutUnhit entry s_dep :=
                ptxBlockOutUnhit_trans hu_s hu_s_post_ad hbo_eq_s
              have hbo_eq_dep : blockOutObjects s_dep = blockOutObjects entry := by
                have hbo_glob_ad : globN post_ad "bo" = globN s "bo" :=
                  globN_bo_eq_of_safeGlobals safeStepGlobals_hp_sp hws_ad_caller.1
                have hbo_flds_ad := ptx_bo_fields_eq_of_step validBufList_wsAcctBufs
                  safeStepGlobals_hp_sp hWOK_s hws_ad_caller.1
                have hbo_dep_s : blockOutObjects post_ad = blockOutObjects s :=
                  blockOutObjects_eq_of_ptxBlockOutUnhit hM_s.1 hMAs.2.1 hbo_glob_ad
                    (fun off hoff hnz => hbo_flds_ad off hoff hnz)
                    hu_s_post_ad
                exact hbo_dep_s.trans hbo_eq_s
              have hws_ad_s_dep_sc : WorldStepSc (bufRegions pmcBufs) ["heap_ptr", "scratch_ptr"]
                  EvmBase.stdKeep NoExtra s none s_dep :=
                WorldStepSc.mono_bufs hwsAcct_sub_pmc (fun _ h => h)
                  (hws_ad_caller.with_locals_clock (r' := none) s_dep.locals post_ad.clock)
              have hws_ad_s_dep : WorldStep (bufRegions pmcBufs) ["heap_ptr", "scratch_ptr"] pmcKeep
                  NoExtra s none s_dep :=
                worldStep_pmcKeep_of_stdKeep (fun _ h => h) hws_ad_s_dep_sc.1
              have hs_dep_code : s_dep.code = originalRuntimeCode := hws_ad_s_dep.1.1.code
              have hs_dep_msg : s_dep.locals.lookup (ofString "msg") = entry.locals.lookup (ofString "msg") := by
                simp [s_dep, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hs_msg,
                  show ofString "dep" ≠ ofString "msg" by decide]
              have hs_dep_out : s_dep.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
                simp [s_dep, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hs_out,
                  show ofString "dep" ≠ ofString "out" by decide]
              have hs_dep_fr : s_dep.locals.lookup (ofString "frame") = some (.val (.word 0#64)) := by
                simp [s_dep, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hs_fr,
                  show ofString "dep" ≠ ofString "frame" by decide]
              have hs_dep_dep : s_dep.locals.lookup (ofString "dep") = some (.val (.word w_dep)) := by
                simp [s_dep, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
              have hsp_dep : globN s_dep "scratch_ptr" ≤ globN entry "scratch_ptr" :=
                le_trans hws_ad_s_dep_sc.2 hsp_s
              have hbuf_z_ws : ∀ j ∈ bufRegions wsAcctBufs s, j.2 = 0 → j.1 % 8 = 0 := by
                intro j hj hz
                obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
                simp only [wsAcctBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
                rcases hp with rfl | rfl | rfl <;>
                · simp only [bufferRegion] at hz ⊢
                  split at hz
                  · rename_i h0; rw [h0]
                  · cases hz
              have hdisj_ad_all : IvlsDisj (bufRegions wsAcctBufs s) ((locN s "msg", 176) :: worldTypedIvls s S_s Nd_s) := by
                intro x hx j hj
                obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
                obtain ⟨sz, hgb, _, hle⟩ := validBufList_wsAcctBufs p hp
                rcases List.mem_cons.1 hj with rfl | hj_wti
                · have hfix_p : bufferRegion s (p.1, sz) ∈ fixedObjects s := by
                    unfold fixedObjects
                    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
                    exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
                  have hd_sz := (hMAs.2.2.2.2.2.2.2.2.2.2.2.1 _
                    (by unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix_p))))).flip
                  by_cases h0 : globN s p.1 = 0
                  · simp [bufferRegion, h0]; exact disj_zero_left _
                  · simp only [bufferRegion, h0, ↓reduceIte] at hd_sz ⊢
                    exact (disj_of_inside_right (j := (globN s p.1, p.2)) (j' := (globN s p.1, sz))
                      ⟨le_rfl, by dsimp; omega⟩ hd_sz.flip).flip
                · exact validBufList_disj validBufList_wsAcctBufs hMAs.2.1 _ hx j hj_wti
              obtain ⟨S0_dep, Nd_dep, hMA_dep_pre, _, _⟩ :=
                R10Shards.Fast_GbodyC17ToC21.WorldStep.preserves_msgReadyAt hMAs hws_ad_caller.1
                  hbuf_z_ws hdisj_ad_all
              have hMA_dep : R10Shards.Fast_GbodyC17ToC21.MsgReadyAt s_dep
                  (S0_dep ++ [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)]) Nd_dep :=
                R10Shards.Fast_GbodyC17ToC21.msgReadyAt_with_locals
                  (s := { post_ad with locals := s.locals })
                  (by simp [HolFiniteMapExact.update, FUPDATE, show ofString "dep" ≠ ofString "msg" by decide])
                  hMA_dep_pre
              have hM_dep : MsgReady s_dep :=
                R10Shards.Fast_GbodyC17ToC21.msgReadyAt_msgReady hMA_dep
              have hout_in2 : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
                ⟨le_trans hM0.1.2.1 hw_in_s.1, hw_in_s.2⟩
              have hbuf_z_pmc : ∀ j ∈ bufRegions pmcBufs s, j.2 = 0 → j.1 % 8 = 0 := by
                intro j hj hz
                exact pmcRegions_zero_aligned hMAs.2.2.2.2.2.2.2.2.2.1 j
                  (by rw [pmcRegions_eq_bufRegions]; exact List.mem_cons_of_mem _ hj) hz
              have hout_disj_R_pmc : ∀ S2 Nd2, IvlsDisj [(w_out.toNat, 96)] (worldOwned s S2 Nd2) →
                  ∀ j ∈ bufRegions pmcBufs s, Disj (w_out.toNat, 96) j := by
                intro S2 Nd2 hout2 j hj
                obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
                obtain ⟨sz, hgb, _, hle⟩ := validBufList_pmcBufs p hp
                have hfix_p : bufferRegion s (p.1, sz) ∈ fixedObjects s := by
                  unfold fixedObjects
                  apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
                  exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
                have hd_sz := hout2 (w_out.toNat, 96) (by simp) _
                  (by unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix_p))))
                by_cases h0 : globN s p.1 = 0
                · simp [bufferRegion, h0]; exact disj_zero_right _
                · simp only [bufferRegion, h0, ↓reduceIte] at hd_sz ⊢
                  exact disj_of_inside_right (j' := (globN s p.1, sz)) ⟨le_rfl, by dsimp; omega⟩ hd_sz
              have hws_en_dep := worldStep_pmcPrefix_trans (w_out := w_out)
                hM0.1 hWOK_en hR1_sub
                (fun j hj => Or.inl hj)
                (fun _ _ h => h)
                (fun S2 Nd2 hWT2 _ => validBufList_disj validBufList_pmcBufs hWT2)
                hws_s hsp_s hws_ad_s_dep
                (fun S2 Nd2 S3 Nd3 hWT2 hout2 hOG23 hFO23 _ => by
                  obtain ⟨_, hout_ow3, _⟩ :=
                    heap_ivl_survives_step (b := (w_out.toNat, 96))
                      hM_s.1.2 hws_ad_s_dep.2.1 hOG23 hFO23
                      (worldOwned_zero_aligned hWT2) hbuf_z_pmc hw_out8 (by dsimp) hout_in2
                      (fun j hj => hout2 (w_out.toNat, 96) (by simp) j hj)
                      (hout_disj_R_pmc S2 Nd2 hout2)
                  intro x hx j hj; simp at hx; subst hx; exact hout_ow3 j hj)
              have hws_ad_av2 : WorldStep (fun st => (w_out.toNat, 96) :: bufRegions wsAcctBufs st)
                  ["heap_ptr", "scratch_ptr"] EvmBase.stdKeep
                  (fun s0 _ post0 S' Nd' =>
                    IvlsDisj [(w_out.toNat, 96)] (worldOwned post0 S' Nd') ∧
                    IvlUnhit s0 post0 (w_out.toNat, 96))
                  s (some (.returned (.val (.word w_dep)))) post_ad := by
                obtain ⟨a1, a2, a3, a4, a5⟩ := hws_ad_caller.1
                refine ⟨a1, a2, a3, ?_, fun S_x Nd_x hW_x hD_x => ?_⟩
                · intro rec hrec hnz off hoff hno
                  exact a4 rec hrec hnz off hoff (fun i hi => hno i (List.mem_cons_of_mem _ hi))
                · have hD_ws : IvlsDisj (bufRegions wsAcctBufs s) (worldTypedIvls s S_x Nd_x) :=
                    fun x hx j hj => hD_x x (List.mem_cons_of_mem _ hx) j hj
                  obtain ⟨S', Nd', hsub', hW', hOG', hFO', _⟩ := a5 S_x Nd_x hW_x hD_ws
                  have hout_ow_x : IvlsDisj [(w_out.toNat, 96)] (worldOwned s S_x Nd_x) := by
                    intro x hx j hj
                    simp only [List.mem_singleton] at hx; subst hx
                    unfold worldOwned at hj
                    rcases List.mem_append.1 hj with h1 | hnd
                    · rcases List.mem_append.1 h1 with htab | hfix
                      · apply hD_x (w_out.toNat, 96) List.mem_cons_self j
                        unfold worldTypedIvls
                        apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
                        apply List.mem_append.2; left; exact List.mem_append.2 (Or.inl htab)
                      · apply hout_ow_s (w_out.toNat, 96) (by simp) j
                        unfold worldOwned
                        exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
                    · apply hD_x (w_out.toNat, 96) List.mem_cons_self j
                      unfold worldTypedIvls
                      exact List.mem_append.2 (Or.inr hnd)
                  have hout_disj_ws : ∀ j ∈ bufRegions wsAcctBufs s, Disj (w_out.toNat, 96) j :=
                    fun j hj => hout_disj_R_pmc S_x Nd_x hout_ow_x j
                      (by obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj; exact List.mem_map.2 ⟨p, hwsAcct_sub_pmc p hp, rfl⟩)
                  obtain ⟨_, hout_ow', hout_u'⟩ :=
                    heap_ivl_survives_step (b := (w_out.toNat, 96))
                      hM_s.1.2 a2 hOG' hFO'
                      (worldOwned_zero_aligned hW_x) hbuf_z_ws hw_out8 (by dsimp) hout_in2
                      (fun j hj => hout_ow_x (w_out.toNat, 96) (by simp) j hj) hout_disj_ws
                  refine ⟨S', Nd', hsub', hW', hOG', ?_,
                    ⟨fun x hx j hj => by simp at hx; subst hx; exact hout_ow' j hj, hout_u'⟩⟩
                  intro a ha hhf
                  apply hFO' a _ hhf
                  intro i hi hch
                  rcases List.mem_append.1 hi with hi1 | hfg
                  · rcases List.mem_append.1 hi1 with hwo | hR
                    · exact ha i (List.mem_append_left _ (List.mem_append_left _ hwo)) hch
                    · exact ha i (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ hR))) hch
                  · exact ha i (List.mem_append_right _ hfg) hch
              have hdisj_ad2_all : IvlsDisj ((w_out.toNat, 96) :: bufRegions wsAcctBufs s)
                  ((locN s "msg", 176) :: worldTypedIvls s S_s Nd_s) := by
                intro x hx j hj
                rcases List.mem_cons.1 hx with rfl | hx_ws
                · rcases List.mem_cons.1 hj with rfl | hj_wti
                  · have hm_in_en : Inside (locN entry "msg", 176) sourceBase (globN entry "heap_ptr") := by
                      obtain ⟨_, _, hMA_en⟩ := R10Shards.Fast_GbodyC17ToC21.msgReadyAt_of_msgReady hM0
                      exact hMA_en.2.2.2.2.2.2.2.2.2.2.1
                    have hm_eq_loc : locN s "msg" = locN entry "msg" := by simp [locN, hs_msg]
                    rw [hm_eq_loc]
                    exact Or.inr (Or.inr (Or.inr (Nat.le_trans hm_in_en.2 hw_in_s.1)))
                  · exact hout_ow_s _ (by simp) j (worldTypedIvls_sub_worldOwned _ _ _ j hj_wti)
                · exact hdisj_ad_all x hx_ws j hj
              obtain ⟨S0_dep2, Nd_dep2, hMA_dep2_pre, ⟨hav0_ad, hout_u_ad⟩, hfp_ad2⟩ :=
                R10Shards.Fast_GbodyC17ToC21.WorldStep.preserves_msgReadyAt hMAs hws_ad_av2
                  (fun j hj hz => by
                    rcases List.mem_cons.1 hj with rfl | hj_ws
                    · simp at hz
                    · exact hbuf_z_ws j hj_ws hz)
                  hdisj_ad2_all
              have hMA_dep2 : R10Shards.Fast_GbodyC17ToC21.MsgReadyAt s_dep
                  (S0_dep2 ++ [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)]) Nd_dep2 :=
                R10Shards.Fast_GbodyC17ToC21.msgReadyAt_with_locals
                  (s := { post_ad with locals := s.locals })
                  (by simp [HolFiniteMapExact.update, FUPDATE, show ofString "dep" ≠ ofString "msg" by decide])
                  hMA_dep2_pre
              have hout_ow_dep_at : IvlsDisj [(w_out.toNat, 96)]
                  (worldOwned s_dep (S0_dep2 ++ [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)]) Nd_dep2) := by
                intro x hx j hj
                simp only [List.mem_singleton] at hx; subst hx
                change j ∈ worldOwned post_ad _ Nd_dep2 at hj
                unfold worldOwned at hj
                rcases List.mem_append.1 hj with h1 | hnd
                · rcases List.mem_append.1 h1 with htab | hfix
                  · rw [List.flatMap_append] at htab
                    rcases List.mem_append.1 htab with htab0 | htab_loc
                    · apply hav0_ad (w_out.toNat, 96) (by simp) j
                      unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl htab0)))
                    · obtain ⟨u, hu_loc, hj_fp⟩ := List.mem_flatMap.1 htab_loc
                      rw [hfp_ad2 u hu_loc] at hj_fp
                      have hu_S : u ∈ S_s := by
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_loc
                        rcases hu_loc with rfl | rfl
                        · exact hMAs.2.2.1
                        · exact hMAs.2.2.2.1
                      apply hout_ow_s (w_out.toNat, 96) (by simp) j
                      unfold worldOwned
                      exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨u, hu_S, hj_fp⟩))))
                  · apply hav0_ad (w_out.toNat, 96) (by simp) j
                    unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
                · apply hav0_ad (w_out.toNat, 96) (by simp) j
                  unfold worldOwned; exact List.mem_append.2 (Or.inr hnd)
              have hw_hi_s : w_out.toNat + 96 ≤ 2 ^ 64 :=
                (ivl_allocated_bound hM_s.1.2 (Or.inl hout_in2)).2
              have hmem16_dep : memW s_dep (w_out.toNat + 16) = 0 := by
                change memW post_ad (w_out.toNat + 16) = 0
                rw [memW_eq_of_ivlUnhit hout_u_ad (by omega) hw_hi_s ⟨by dsimp; omega, by dsimp; omega⟩]
                exact hmem16_s
              have hw_in_dep : Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s_dep "heap_ptr") :=
                ⟨hw_in_s.1, le_trans hw_in_s.2 hws_ad_s_dep.2.1⟩
              have hw_ok_dep : WordsOK s_dep (w_out.toNat, 96) :=
                wordsOK_transfer hM_s.1.1 hM_dep.1.1 hw_ok_s
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres hnex ⊢
              have hcond_dep_ex : @evalHOLExact 64 F _ s_dep.toExact (fun a => Classical.propDecidable (s_dep.memaddrs a))
                  (.cmp .equal (.var .local (ofString "dep")) (.const 0#64)) =
                  some (.val (.word (if w_dep = 0#64 then 1#64 else 0#64))) := by
                simp [evalHOLExact, hs_dep_dep, Compiler.Encoders.Asm.wordCmpHOL]
              rw [hcond_dep_ex] at hres hnex ⊢
              dsimp only at hres hnex ⊢
              by_cases hdep0 : w_dep = 0#64
              · rw [if_pos hdep0, if_neg (show ¬ ((1#64 : BitVec 64) = 0) by decide)] at hres hnex ⊢
                have hsr0 : PmcStoreReady (fun _ _ st _ _ => memW st (w_out.toNat + 16) = 0) entry s_dep w_out :=
                  pmcStoreReady_of_prefix hWOK_en
                    (fun j hj => by
                      rcases List.mem_append.1 hj with hj_buf | hj_fr
                      · exact Or.inl hj_buf
                      · simp only [List.mem_singleton] at hj_fr; subst hj_fr
                        exact Or.inr ⟨le_rfl, by have := hws_en_dep.2.1; omega⟩)
                    hws_en_dep (fun _ _ => hmem16_dep) hs_dep_out hw_out8 hw_in_dep hw_ok_dep
                have hs_dep_msg_w : s_dep.locals.lookup (ofString "msg") = some (.val (.word w_msg)) := by
                  rw [hs_dep_msg, ← hs_msg]; exact hs_msg_w
                obtain ⟨_, _, _, _, hm_in_dep, hm_ok_dep, _, _, _, _, _⟩ := hM_dep.2
                have hm_loc_dep : locN s_dep "msg" = w_msg.toNat := by simp [locN, hs_dep_msg_w]
                have hw_msg_ok_dep : WordsOK s_dep (w_msg.toNat, 176) := by rwa [← hm_loc_dep]
                obtain ⟨w_emp, hw_emp⟩ := hM_dep.1.2.2.2.2.2.2.2.2.2 "evm_empty" (by decide)
                obtain ⟨hev1, hsr1⟩ := pmcStoreReady_zero_store (off := 32) (valExp := .const 12#64) (w_val := 12#64)
                  hsr0 (by decide) (by decide) (by decide) rfl
                set st1 := { s_dep with memory := pmcUpdW s_dep.memory (BitVec.ofNat 64 (w_out.toNat + 32)) 12#64 }
                have hmsg_ok1 : WordsOK st1 (w_msg.toNat, 176) := pmc_wordsOK_updW s_dep _ _ _ hw_msg_ok_dep
                have hload48_1 := pmc_load_local_off (s := st1) hs_dep_msg_w hmsg_ok1 hw_msg_hi_s (by decide) (show 48 < 176 by decide)
                obtain ⟨hev2, hsr2⟩ := pmcStoreReady_zero_store (off := 56)
                  (valExp := .load .one (.op .add [.var .local (ofString "msg"), .const 48#64]))
                  hsr1 (by decide) (by decide) (by decide) hload48_1
                set st2 := { st1 with memory := pmcUpdW st1.memory (BitVec.ofNat 64 (w_out.toNat + 56)) (BitVec.ofNat 64 (memW st1 (w_msg.toNat + 48))) }
                have hmsg_ok2 : WordsOK st2 (w_msg.toNat, 176) := pmc_wordsOK_updW st1 _ _ _ hmsg_ok1
                have hload40_2 := pmc_load_local_off (s := st2) hs_dep_msg_w hmsg_ok2 hw_msg_hi_s (by decide) (show 40 < 176 by decide)
                obtain ⟨hev3, hsr3⟩ := pmcStoreReady_zero_store (off := 64)
                  (valExp := .load .one (.op .add [.var .local (ofString "msg"), .const 40#64]))
                  hsr2 (by decide) (by decide) (by decide) hload40_2
                set st3 := { st2 with memory := pmcUpdW st2.memory (BitVec.ofNat 64 (w_out.toNat + 64)) (BitVec.ofNat 64 (memW st2 (w_msg.toNat + 40))) }
                have hemp_3 : @evalHOLExact 64 F _ st3.toExact (fun a => Classical.propDecidable (st3.memaddrs a))
                    (.var .global (ofString "evm_empty")) = some (.val (.word w_emp)) := by
                  simp [evalHOLExact, st3, st2, st1]
                  exact hw_emp
                obtain ⟨hev4, _⟩ := pmcStoreReady_zero_store (off := 40)
                  (valExp := .var .global (ofString "evm_empty"))
                  hsr3 (by decide) (by decide) (by decide) hemp_3
                set st4 := { st3 with memory := pmcUpdW st3.memory (BitVec.ofNat 64 (w_out.toNat + 40)) w_emp }
                have hret_ev : evaluateHOLFiniteState st4 (.return (.var .local (ofString "out"))) =
                    (some (.returned (.val (.word w_out))), emptyLocalsHOLFinite st4) := by
                  rw [evaluateHOLFiniteState_return]
                  have hs4_out : st4.locals.lookup (ofString "out") = some (.val (.word w_out)) := hs_dep_out
                  simp only [evalHOLExact, hs4_out, shapeOfHOLExact, sizeOfShapeWithContextHOL,
                    show (1 : Nat) ≤ 32 by decide, ↓reduceIte]
                have hblk_ev : evaluateHOLFiniteState s_dep
                    (.seq (.store (.op .add [.var .local (ofString "out"), .const 32#64]) (.const 12#64))
                      (.seq (.store (.op .add [.var .local (ofString "out"), .const 56#64]) (.load .one (.op .add [.var .local (ofString "msg"), .const 48#64])))
                        (.seq (.store (.op .add [.var .local (ofString "out"), .const 64#64]) (.load .one (.op .add [.var .local (ofString "msg"), .const 40#64])))
                          (.seq (.store (.op .add [.var .local (ofString "out"), .const 40#64]) (.var .global (ofString "evm_empty")))
                            (.return (.var .local (ofString "out"))))))) =
                    (some (.returned (.val (.word w_out))), emptyLocalsHOLFinite st4) := by
                  rw [evaluateHOLFiniteState_seq_line780,
                    show (32#64 : BitVec 64) = BitVec.ofNat 64 32 from rfl, hev1]
                  dsimp only
                  rw [evaluateHOLFiniteState_seq_line780,
                    show (56#64 : BitVec 64) = BitVec.ofNat 64 56 from rfl, hev2]
                  dsimp only
                  rw [evaluateHOLFiniteState_seq_line780,
                    show (64#64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, hev3]
                  dsimp only
                  rw [evaluateHOLFiniteState_seq_line780,
                    show (40#64 : BitVec 64) = BitVec.ofNat 64 40 from rfl, hev4]
                  dsimp only
                  exact hret_ev
                rw [hblk_ev] at hres hnex ⊢
                dsimp only
                have hu1 : PtxBlockOutUnhit entry st1 :=
                  ptxBlockOutUnhit_of_pmcUpdW hM0 hM_dep.1.2 hw_in_dep (by decide) hu_dep
                have hu2 : PtxBlockOutUnhit entry st2 :=
                  ptxBlockOutUnhit_of_pmcUpdW hM0 hM_dep.1.2 hw_in_dep (by decide) hu1
                have hu3 : PtxBlockOutUnhit entry st3 :=
                  ptxBlockOutUnhit_of_pmcUpdW hM0 hM_dep.1.2 hw_in_dep (by decide) hu2
                have hu4 : PtxBlockOutUnhit entry st4 :=
                  ptxBlockOutUnhit_of_pmcUpdW hM0 hM_dep.1.2 hw_in_dep (by decide) hu3
                exact hu4
              · rw [if_neg hdep0, if_pos (show (0#64 : BitVec 64) = 0 by decide)] at hres hnex ⊢
                rw [evaluateHOLFiniteState_skip] at hres hnex ⊢
                dsimp only at hres hnex ⊢
                have hcall_pcm := pmcBo_call_frame_callee
                  (restL := fun m => HolFiniteMapExact.resVarEq m (ofString "dep", s.locals.lookup (ofString "dep")))
                  hpcm (fun _ _ _ _ _ h => ⟨h.1.1, h.2⟩)
                  ⟨_, _, R10Shards.Fast_GbodyC17ToC21.lookup_process_create_message⟩
                  (fun m => by rw [PanRunBounded.resVarEq_lookup, if_neg (by decide)])
                  (fun m => by rw [PanRunBounded.resVarEq_lookup, if_neg (by decide)])
                  htail hs_dep_code hM0 hM_dep hs_dep_msg hsp_dep
                  hws_en_dep hs_dep_out hs_dep_fr
                  hw_out8 hw_in_dep hw_ok_dep hmem16_dep ⟨_, _, hMA_dep2, hout_ow_dep_at⟩
                  hu_dep hbo_eq_dep
                dsimp only at hcall_pcm hres hnex ⊢
                rcases hrun_pcm : evaluateHOLFiniteState s_dep
                    (.call (some ((some (.local, ofString "frame")), none))
                      (ofString "process_create_message") [.var .local (ofString "msg")]) with ⟨res_pcm, post_pcm⟩
                simp only [hrun_pcm] at hcall_pcm hres hnex ⊢
                cases res_pcm with
                | none =>
                  exact ptxBlockOutUnhit_with_locals_clock _ _ (hcall_pcm hres hnex)
                | some v =>
                  exact ptxBlockOutUnhit_with_locals_clock _ _ (hcall_pcm hres hnex)
            · simp only [hsh_ad, Bool.false_eq_true, ↓reduceIte] at hres
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · rw [if_neg h24_eq, if_pos (show (0#64 : BitVec 64) = 0 by decide)] at hres hnex ⊢
    have hcall_pm := pmcBo_call_frame_callee (restL := fun m => m) hpm
      (fun _ _ _ _ _ h => ⟨h.1.1.1, h.2⟩)
      ⟨_, _, R10Shards.Fast_GbodyC17ToC21.lookup_process_message⟩
      (fun _ => rfl) (fun _ => rfl)
      htail hcode hM0 hM_s hs_msg hsp_s hws_s hs_out hs_fr
      hw_out8 hw_in_s hw_ok_s hmem16_s ⟨S_s, Nd_s, hMAs, hout_ow_s⟩
      hu_s hbo_eq_s
    dsimp only at hcall_pm hres hnex ⊢
    rcases hrun_pm : evaluateHOLFiniteState s
        (.call (some ((some (.local, ofString "frame")), none))
          (ofString "process_message") [.var .local (ofString "msg")]) with ⟨res_pm, post_pm⟩
    simp only [hrun_pm] at hcall_pm hres hnex ⊢
    have hpost_id : ({ post_pm with locals := post_pm.locals } : PanSemStateFiniteExact 64 F) = post_pm := by
      cases post_pm; rfl
    cases res_pm with
    | none =>
      simp only [hpost_id] at hcall_pm
      exact hcall_pm hres hnex
    | some v =>
      simp only [hpost_id] at hcall_pm
      exact hcall_pm hres hnex

/-! ## 5. Phase 3 (`pmcPack`): Block-Output Preservation -/

private theorem pmcBoPack_store_frame_then {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64} {logs off_out off_fr : Nat} {z : Bool} {tail : ProgHOL 64}
    (hps : PmcPackState entry s w_out w_fr logs z)
    (hu : PtxBlockOutUnhit entry s)
    (hoff_out8 : off_out % 8 = 0) (hoff_out_lt : off_out < 96) (hoff_ne16 : off_out ≠ 16)
    (hoff_fr8 : off_fr % 8 = 0) (hoff_fr_lt : off_fr < 280)
    (htail : let w_v := BitVec.ofNat 64 (memW s (w_fr.toNat + off_fr))
      PmcPackState entry
        { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off_out)) w_v }
        w_out w_fr logs z →
      PtxBlockOutUnhit entry
        { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off_out)) w_v } →
      PmcBoRun entry tail
        { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off_out)) w_v }) :
    PmcBoRun entry
      (.seq (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 off_out)])
                    (.load .one (.op .add [.var .local (ofString "frame"), .const (BitVec.ofNat 64 off_fr)])))
            tail) s := by
  have hfr_hi : w_fr.toNat + 280 ≤ 2 ^ 64 := by
    have h1 : w_fr.toNat + 280 ≤ scratchEnd := hps.2.2.2.2.1.2
    have h2 : scratchEnd ≤ 2 ^ 64 := by decide
    omega
  have hload := pmc_load_local_off hps.2.2.1 hps.2.2.2.1 hfr_hi hoff_fr8 hoff_fr_lt
  obtain ⟨hev, hps'⟩ := pmcPackState_store hps hoff_out8 hoff_out_lt hoff_ne16 hload
  have hu' : PtxBlockOutUnhit entry
      { s with memory := (pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off_out))
          (BitVec.ofNat 64 (memW s (w_fr.toNat + off_fr)))) } :=
    ptxBlockOutUnhit_of_pmcUpdW hps.1 hps.2.1.2.1.1.2 hps.2.1.2.2.2.2.1 hoff_out_lt hu
  unfold PmcBoRun at htail ⊢
  rw [evaluateHOLFiniteState_seq_line780, hev]
  exact htail hps' hu'

private theorem pmcBoPack_decCall_ro_then {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64} {logs : Nat} {z : Bool}
    {name fname : MlS} {args : List (ExpHOL 64)} {values : List (ValueHOL 64)}
    {cont : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (hro : ReadOnlyFn fname)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values)
    (hne_out : ofString "out" ≠ name)
    (hne_fr : ofString "frame" ≠ name)
    (hps : PmcPackState entry s w_out w_fr logs z)
    (hu : PtxBlockOutUnhit entry s)
    (hcont : ∀ (w_res : BitVec 64) (s_next : PanSemStateFiniteExact 64 F),
      s_next.code = originalRuntimeCode →
      s_next.locals.lookup name = some (.val (.word w_res)) →
      PmcPackState entry s_next w_out w_fr logs z →
      PtxBlockOutUnhit entry s_next →
      PmcBoRun entry cont s_next) :
    PmcBoRun entry (.decCall name .one fname args cont) s := by
  unfold PmcBoRun
  intro hres hnex
  obtain ⟨params, body, ret, hlook, hspec⟩ := hro
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs] at hres hnex ⊢
  dsimp only at hres hnex ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
  · simp only [hl] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [hl] at hres hnex ⊢
    by_cases hz : s.clock = 0
    · simp only [hz, ↓reduceIte] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hz, ↓reduceIte] at hres hnex ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' values callee (by rw [hcode]; exact hlook) hl
      subst hsame
      have hret_eq := lookupCodeHOLFinite_installed_return s fname params body' body'
        ret ret' values callee (by rw [hcode]; exact hlook) hl
      subst hret_eq
      have hentryEq : callEntryStateHOLFinite s callee =
          { s with locals := callee, clock := (callEntryStateHOLFinite s callee).clock } := by
        cases s; rfl
      have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
          some (body', (callEntryStateHOLFinite s callee).locals, ret') :=
        ⟨values, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩
      have hG : GuestInv s := hps.2.1.2.1.1.1
      rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
      simp only [hrun] at hres hnex ⊢
      cases res with
      | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      | some br =>
        cases br with
        | timeOut => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | error => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | «break» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | «continue» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | finalFfi _ => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | exception eid eval =>
          exact absurd hnex (nonExResult_not_exception rfl)
        | returned val =>
          dsimp only at hres hnex ⊢
          by_cases hsh : (shapeEqHOL (shapeOfHOLExact val) .one &&
              shapeEqHOL (shapeOfHOLExact val) ret') = true
          · simp only [hsh, ↓reduceIte] at hres hnex ⊢
            have hsh1 : shapeEqHOL (shapeOfHOLExact val) .one = true :=
              ((Bool.and_eq_true _ _).mp hsh).1
            have hw_val : ∃ w : BitVec 64, val = .val (.word w) := by
              rcases val with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
              · exact ⟨w, rfl⟩
              · simp [shapeOfHOLExact, shapeEqHOL] at hsh1
              · simp [shapeOfHOLExact, shapeEqHOL] at hsh1
            obtain ⟨w_res, rfl⟩ := hw_val
            have hro_eq := hspec (callEntryStateHOLFinite s callee) hcode
              (guestInv_callEntry s callee hG) hex (by rw [hrun]; simp)
              (by rw [hrun]; exact Or.inl ⟨.val (.word w_res), rfl⟩)
            rw [hrun] at hro_eq; dsimp only at hro_eq
            set s_next := setVarHOLFinite name (.val (.word w_res)) { post with locals := s.locals }
            have hs_next_eq : s_next = { s with locals := s_next.locals, clock := post.clock } := by
              have h1 := R13.state_trans_locals_clock hentryEq hro_eq
              have h2 : s_next = { post with locals := s_next.locals, clock := post.clock } := by
                dsimp only [s_next]; cases post; rfl
              exact R13.state_trans_locals_clock h1 h2
            have hs_next_code : s_next.code = originalRuntimeCode := by
              rw [hs_next_eq]; exact hcode
            have hs_next_name : s_next.locals.lookup name = some (.val (.word w_res)) := by
              dsimp only [s_next]; unfold setVarHOLFinite
              simp [HolFiniteMapExact.update, FUPDATE]
            have hs_next_out : s_next.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
              dsimp only [s_next]; unfold setVarHOLFinite
              simp [HolFiniteMapExact.update, FUPDATE, hne_out.symm, hps.2.1.2.2.1]
            have hs_next_fr : s_next.locals.lookup (ofString "frame") = some (.val (.word w_fr)) := by
              dsimp only [s_next]; unfold setVarHOLFinite
              simp [HolFiniteMapExact.update, FUPDATE, hne_fr.symm, hps.2.2.1]
            have hps_next : PmcPackState entry s_next w_out w_fr logs z := by
              have hps' := pmcPackState_with_locals_clock s_next.locals post.clock
                hs_next_out hs_next_fr hps
              rwa [← hs_next_eq] at hps'
            have hu_next : PtxBlockOutUnhit entry s_next := by
              rw [hs_next_eq]; exact hu
            have hcont_run := hcont w_res s_next hs_next_code hs_next_name hps_next hu_next
            unfold PmcBoRun at hcont_run
            rcases hc_run : evaluateHOLFiniteState s_next cont with ⟨cres, cpost⟩
            rw [hc_run] at hcont_run
            simp only [hc_run] at hres hnex ⊢
            cases cres with
            | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
            | some cbr =>
              cases cbr with
              | timeOut => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
              | error => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
              | «break» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
              | «continue» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
              | finalFfi _ => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
              | exception ceid ceval =>
                exact absurd hnex (nonExResult_not_exception rfl)
              | returned cval =>
                exact ptxBlockOutUnhit_with_locals_clock _ cpost.clock
                  (hcont_run (Or.inl ⟨cval, rfl⟩) (Or.inr (Or.inr (Or.inr ⟨cval, rfl⟩))))
          · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hres
            exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

private theorem pmcBoPack_ite160_step {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64} {logs : Nat} {z : Bool} {tail : ProgHOL 64}
    (hps : PmcPackState entry s w_out w_fr logs z)
    (hu : PtxBlockOutUnhit entry s)
    (htail : ∀ (z' : Bool) (s_mid : PanSemStateFiniteExact 64 F),
      PmcPackState entry s_mid w_out w_fr logs z' →
      PtxBlockOutUnhit entry s_mid →
      PmcBoRun entry tail s_mid) :
    PmcBoRun entry
      (.seq
        (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "frame"), .const (BitVec.ofNat 64 160)]))
                           (.const (BitVec.ofNat 64 0)))
          (.seq
            (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 16)])
                    (.load .one (.op .add [.var .local (ofString "frame"), .const (BitVec.ofNat 64 88)])))
            (.seq
              (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 24)])
                      (.load .one (.op .add [.var .local (ofString "frame"), .const (BitVec.ofNat 64 136)])))
              (.dec (ofString "rc") .one
                (.load .one (.op .add [.var .local (ofString "frame"), .const (BitVec.ofNat 64 96)]))
                (.seq
                  (.ite (.cmp .less (.var .local (ofString "rc")) (.const (BitVec.ofNat 64 0)))
                    (.assign .local (ofString "rc") (.const (BitVec.ofNat 64 0)))
                    .skip)
                  (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 8)])
                          (.var .local (ofString "rc")))))))
          .skip)
        tail) s := by
  have hfr_hi : w_fr.toNat + 280 ≤ 2 ^ 64 := by
    have h1 : w_fr.toNat + 280 ≤ scratchEnd := hps.2.2.2.2.1.2
    have h2 : scratchEnd ≤ 2 ^ 64 := by decide
    omega
  have hload160 := pmc_load_local_off hps.2.2.1 hps.2.2.2.1 hfr_hi (by decide) (show 160 < 280 by decide)
  set w160 := BitVec.ofNat 64 (memW s (w_fr.toNat + 160))
  unfold PmcBoRun
  intro hres hnex
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres hnex ⊢
  have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.load .one (.op .add [.var .local (ofString "frame"), .const 160#64])) (.const 0#64)) =
      some (.val (.word (if w160 = 0#64 then 1#64 else 0#64))) := by
    have hl160' : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "frame"), .const 160#64])) =
        some (.val (.word w160)) := hload160
    unfold evalHOLExact
    rw [hl160']
    simp [evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL]
  simp only [show BitVec.ofNat 64 160 = 160#64 from rfl,
    show BitVec.ofNat 64 0 = 0#64 from rfl] at hres hnex ⊢
  rw [hcond] at hres hnex ⊢
  dsimp only at hres hnex ⊢
  by_cases h160_eq : w160 = 0#64
  · rw [if_pos h160_eq, if_neg (show ¬ ((1#64 : BitVec 64) = 0) by decide)] at hres hnex ⊢
    have hload88 := pmc_load_local_off hps.2.2.1 hps.2.2.2.1 hfr_hi (by decide) (show 88 < 280 by decide)
    obtain ⟨hM0, hsr, hs_fr, hw_fr_ok, hfr_in, hlok, hdisj, hlogs_eq, _, _⟩ := hps
    set w88 := BitVec.ofNat 64 (memW s (w_fr.toNat + 88))
    set a16 := BitVec.ofNat 64 (w_out.toNat + 16)
    have hAs : ArenaOK s := hsr.2.1.1.2
    have hgS : GuestInv s := hsr.2.1.1.1
    have hw_in_sb : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
      ⟨le_trans hsr.1.1.2.1 hsr.2.2.2.2.1.1, hsr.2.2.2.2.1.2⟩
    have hw_hi : w_out.toNat + 96 ≤ 2 ^ 64 :=
      (ivl_allocated_bound hAs (Or.inl hw_in_sb)).2
    obtain ⟨hev16, hsr1⟩ := pmcStoreReady_store
      (Q2 := fun _ _ st S' Nd' => PmcLogsLiveOwned st S' Nd' logs)
      hsr (off := 16) (by decide) (by decide) hload88
      (fun S' Nd' _ _ howned_eq _ hlive =>
        (pmc_logs_preserve_store_out hAs hgS hw_hi (by decide) (by decide) hlok hlive hdisj howned_eq).2.1)
    obtain ⟨S_en, Nd_en, hMA_en⟩ := R10Shards.Fast_GbodyC17ToC21.msgReadyAt_of_msgReady hM0
    have hT_en : ∀ t ∈ pmcTables entry, t ∈ S_en := by
      intro t ht; simp [pmcTables] at ht; rcases ht with rfl | rfl
      · exact hMA_en.2.2.1
      · exact hMA_en.2.2.2.1
    have hD_en : IvlsDisj (pmcRegions entry) (worldTypedIvls entry S_en Nd_en) := by
      rw [pmcRegions_eq_bufRegions]; intro x hx j hj
      rcases List.mem_cons.1 hx with rfl | hx_buf
      · exact hMA_en.2.2.2.2.2.2.2.2.2.2.2.1 j (worldTypedIvls_sub_worldOwned entry S_en Nd_en j hj)
      · exact validBufList_disj validBufList_pmcBufs hMA_en.2.1 x hx_buf j hj
    obtain ⟨S_p, Nd_p, _, hWT_p, _, _, hout_ow_p, hlive_p⟩ := hsr.2.1.2.2.2.2 S_en Nd_en hMA_en.2.1 hT_en hD_en
    have hx16_lt : w_out.toNat + 16 < 2 ^ 64 := by omega
    obtain ⟨_, hdom16, _⟩ := hsr.2.2.2.2.2.2.2 2 (by dsimp only at *; omega)
    rw [show w_out.toNat + 8 * 2 = w_out.toNat + 16 by omega] at hdom16
    have hx16_in : w_out.toNat ≤ a16.toNat ∧ a16.toNat + 8 ≤ w_out.toNat + 96 := by
      dsimp only [a16]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx16_lt]; omega
    obtain ⟨_, _, howned16, _, _, _⟩ :=
      worldTypedWith_store_word_disj (post := { s with memory := pmcUpdW s.memory a16 w88 })
        hsr.2.1.1 hdom16
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun a hne => by unfold pmcUpdW; exact if_neg hne⟩
        hWT_p
        (fun j hj => disj_of_inside_right (j' := (w_out.toNat, 96)) ⟨hx16_in.1, hx16_in.2⟩
          (hout_ow_p (w_out.toNat, 96) (by simp) j (worldTypedIvls_sub_worldOwned s S_p Nd_p j hj)).flip)
    obtain ⟨hlok1, _, hdisj1⟩ :=
      pmc_logs_preserve_store_out hAs hgS hw_hi (by decide) (by decide) hlok hlive_p hdisj howned16
    have hfr88_1 : memW { s with memory := pmcUpdW s.memory a16 w88 } (w_fr.toNat + 88) = memW s (w_fr.toNat + 88) :=
      pmc_frame_memW_store_out hAs hsr.2.2.2.2.1.2 hfr_in (by decide) (by decide)
    have hlogs_lt : memW s (w_fr.toNat + 88) < 2 ^ 64 := by
      unfold memW; cases s.memory (BitVec.ofNat 64 (w_fr.toNat + 88)) with
      | word w => exact w.isLt
    have hout16_1 : memW { s with memory := pmcUpdW s.memory a16 w88 } (w_out.toNat + 16) = logs := by
      dsimp only [a16, w88]
      rw [pmc_memW_updW_same s (w_out.toNat + 16) _, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlogs_lt, ← hlogs_eq]
    set s1 := { s with memory := pmcUpdW s.memory a16 w88 }
    have hps1 : PmcPackState entry s1 w_out w_fr logs false :=
      ⟨hM0, hsr1, hs_fr, pmc_wordsOK_updW s _ _ _ hw_fr_ok, hfr_in, hlok1, hdisj1,
        hlogs_eq.trans hfr88_1.symm, fun h => Bool.noConfusion h, fun _ => hout16_1⟩
    have hu1 : PtxBlockOutUnhit entry s1 :=
      ptxBlockOutUnhit_of_pmcUpdW hM0 hAs hsr.2.2.2.2.1 (by decide) hu
    rw [evaluateHOLFiniteState_seq_line780, hev16] at hres hnex ⊢
    dsimp only at hres hnex ⊢
    have hload136 := pmc_load_local_off hps1.2.2.1 hps1.2.2.2.1 hfr_hi (by decide) (show 136 < 280 by decide)
    obtain ⟨hev24, hps2⟩ := pmcPackState_store hps1 (off := 24) (by decide) (by decide) (by decide) hload136
    set w136 := BitVec.ofNat 64 (memW s1 (w_fr.toNat + 136))
    set a24 := BitVec.ofNat 64 (w_out.toNat + 24)
    set s2 := { s1 with memory := pmcUpdW s1.memory a24 w136 }
    have hu2 : PtxBlockOutUnhit entry s2 :=
      ptxBlockOutUnhit_of_pmcUpdW hM0 hps1.2.1.2.1.1.2 hps1.2.1.2.2.2.2.1 (by decide) hu1
    rw [evaluateHOLFiniteState_seq_line780, hev24] at hres hnex ⊢
    dsimp only at hres hnex ⊢
    have hload96 := pmc_load_local_off hps2.2.2.1 hps2.2.2.2.1 hfr_hi (by decide) (show 96 < 280 by decide)
    set w96 := BitVec.ofNat 64 (memW s2 (w_fr.toNat + 96))
    rw [evaluateHOLFiniteState_dec_total] at hres hnex ⊢
    dsimp only at hres hnex ⊢
    have hsh_rc : shapeEqHOL .one (shapeOfHOLExact (.val (.word w96) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    have hl96' : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "frame"), .const 96#64])) =
        some (.val (.word w96)) := hload96
    rw [hl96'] at hres hnex ⊢
    dsimp only at hres hnex ⊢
    rw [if_pos hsh_rc] at hres hnex ⊢
    set s3 := setVarHOLFinite (ofString "rc") (.val (.word w96)) s2
    have hs3_rc : s3.locals.lookup (ofString "rc") = some (.val (.word w96)) := by
      simp [s3, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
    have hs3_out : s3.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
      simp [s3, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "rc" ≠ ofString "out" by decide, hps2.2.1.2.2.1]
    have hs3_fr : s3.locals.lookup (ofString "frame") = some (.val (.word w_fr)) := by
      simp [s3, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "rc" ≠ ofString "frame" by decide, hps2.2.2.1]
    have hps3 : PmcPackState entry s3 w_out w_fr logs false :=
      pmcPackState_with_locals_clock s3.locals s2.clock hs3_out hs3_fr hps2
    have hu3 : PtxBlockOutUnhit entry s3 := hu2
    have hcmp_rc : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
        (.cmp .less (.var .local (ofString "rc")) (.const 0#64)) =
        some (.val (.word (if Compiler.Encoders.Asm.holAsmSignedLess w96 0#64 then 1#64 else 0#64))) := by
      unfold evalHOLExact
      simp [evalHOLExact, hs3_rc, Compiler.Encoders.Asm.wordCmpHOL]
      split <;> rename_i h <;> simp [h]
    have hite_rc : ∃ (w_rc' : BitVec 64) (s4 : PanSemStateFiniteExact 64 F),
        evaluateHOLFiniteState s3
          (.ite (.cmp .less (.var .local (ofString "rc")) (.const 0#64))
            (.assign .local (ofString "rc") (.const 0#64))
            .skip) = (none, s4) ∧
        s4.locals.lookup (ofString "rc") = some (.val (.word w_rc')) ∧
        (∀ x, x ≠ ofString "rc" → s4.locals.lookup x = s2.locals.lookup x) ∧
        PmcPackState entry s4 w_out w_fr logs false ∧
        PtxBlockOutUnhit entry s4 := by
      rw [evaluateHOLFiniteState_ite, hcmp_rc]
      dsimp only
      by_cases hslt : Compiler.Encoders.Asm.holAsmSignedLess w96 0#64 = true
      · rw [if_pos hslt, if_neg (show ¬ ((1#64 : BitVec 64) = 0) by decide), evaluateHOLFiniteState_assign]
        have hev0 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
            (.const 0#64) = some (.val (.word 0#64)) := by simp [evalHOLExact]
        have hval0 : isValidValueHOLFinite s3 .local (ofString "rc") (.val (.word 0#64)) = true := by
          simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs3_rc, shapeOfHOLExact, shapeEqHOL]
        rw [hev0]; dsimp only; rw [if_pos hval0]
        set s4 := setKvarHOLFinite .local (ofString "rc") (.val (.word 0#64)) s3
        have hs4_rc : s4.locals.lookup (ofString "rc") = some (.val (.word 0#64)) := by
          simp [s4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
        have hs4_ne : ∀ x, x ≠ ofString "rc" → s4.locals.lookup x = s2.locals.lookup x := by
          intro x hx
          simp [s4, s3, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hx.symm]
        have hs4_out : s4.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
          rw [hs4_ne _ (by decide)]; exact hps2.2.1.2.2.1
        have hs4_fr : s4.locals.lookup (ofString "frame") = some (.val (.word w_fr)) := by
          rw [hs4_ne _ (by decide)]; exact hps2.2.2.1
        exact ⟨0#64, s4, rfl, hs4_rc, hs4_ne,
          pmcPackState_with_locals_clock s4.locals s3.clock hs4_out hs4_fr hps3, hu3⟩
      · rw [if_neg hslt, if_pos (show (0#64 : BitVec 64) = 0 by decide), evaluateHOLFiniteState_skip]
        have hs3_ne : ∀ x, x ≠ ofString "rc" → s3.locals.lookup x = s2.locals.lookup x := by
          intro x hx
          simp [s3, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hx.symm]
        exact ⟨w96, s3, rfl, hs3_rc, hs3_ne, hps3, hu3⟩
    obtain ⟨w_rc', s4, hev_ite, hs4_rc, hs4_ne, hps4, hu4⟩ := hite_rc
    have hev_rc_var : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
        (.var .local (ofString "rc")) = some (.val (.word w_rc')) := by
      simp [evalHOLExact, hs4_rc]
    obtain ⟨hev8, hps5⟩ := pmcPackState_store hps4 (off := 8) (by decide) (by decide) (by decide) hev_rc_var
    set a8 := BitVec.ofNat 64 (w_out.toNat + 8)
    have hu5 : PtxBlockOutUnhit entry { s4 with memory := pmcUpdW s4.memory a8 w_rc' } :=
      ptxBlockOutUnhit_of_pmcUpdW hM0 hps4.2.1.2.1.1.2 hps4.2.1.2.2.2.2.1 (by decide) hu4
    have hbody_dec : evaluateHOLFiniteState s3
        (.seq
          (.ite (.cmp .less (.var .local (ofString "rc")) (.const 0#64))
            (.assign .local (ofString "rc") (.const 0#64))
            .skip)
          (.store (.op .add [.var .local (ofString "out"), .const 8#64])
                  (.var .local (ofString "rc")))) =
        (none, { s4 with memory := pmcUpdW s4.memory a8 w_rc' }) := by
      rw [evaluateHOLFiniteState_seq_line780, hev_ite]
      exact hev8
    rw [hbody_dec] at hres hnex ⊢
    dsimp only at hres hnex ⊢
    set L_mid := HolFiniteMapExact.resVarEq s4.locals (ofString "rc", s2.locals.lookup (ofString "rc"))
    set s_mid := { s4 with memory := pmcUpdW s4.memory a8 w_rc', locals := L_mid }
    have hs_mid_out : s_mid.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
      dsimp only [s_mid, L_mid]
      rw [PanRunBounded.resVarEq_lookup, if_neg (show ofString "out" ≠ ofString "rc" by decide)]
      rw [hs4_ne _ (by decide)]; exact hps2.2.1.2.2.1
    have hs_mid_fr : s_mid.locals.lookup (ofString "frame") = some (.val (.word w_fr)) := by
      dsimp only [s_mid, L_mid]
      rw [PanRunBounded.resVarEq_lookup, if_neg (show ofString "frame" ≠ ofString "rc" by decide)]
      rw [hs4_ne _ (by decide)]; exact hps2.2.2.1
    have hps_mid : PmcPackState entry s_mid w_out w_fr logs false :=
      pmcPackState_with_locals_clock s_mid.locals s4.clock hs_mid_out hs_mid_fr hps5
    have hu_mid : PtxBlockOutUnhit entry s_mid := hu5
    exact htail false s_mid hps_mid hu_mid hres hnex
  · rw [if_neg h160_eq, if_pos (show (0#64 : BitVec 64) = 0 by decide), evaluateHOLFiniteState_skip] at hres hnex ⊢
    dsimp only at hres hnex ⊢
    exact htail z s hps hu hres hnex

private theorem pmcBoPack_return {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64} {logs : Nat} {z : Bool}
    (hps : PmcPackState entry s w_out w_fr logs z)
    (hu : PtxBlockOutUnhit entry s) :
    PmcBoRun entry (.return (.var .local (ofString "out"))) s := by
  intro _ _
  have hs_out : s.locals.lookup (ofString "out") = some (.val (.word w_out)) := hps.2.1.2.2.1
  rw [evaluateHOLFiniteState_return]
  simp only [evalHOLExact, hs_out, shapeOfHOLExact, sizeOfShapeWithContextHOL,
    show (1 : Nat) ≤ 32 by decide, ↓reduceIte]
  exact hu

theorem pmcBoPack_cut {F : Type} (entry s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (ha2 : PmcBoA2 entry s) :
    PmcBoRun entry pmcPack s := by
  obtain ⟨⟨hM0, w_out, w_fr, hstep, hs_out, hs_fr, hw_out8, hw_in, hw_ok, hz16,
    hw_fr_ok, hfr_in, hlok, hdisj⟩, hu0⟩ := ha2
  have hps0 := pmcPackState_of_a2 hM0 hstep hs_out hs_fr hw_out8 hw_in hw_ok hz16
    hw_fr_ok hfr_in hlok hdisj
  have hfr_hi : w_fr.toNat + 280 ≤ 2 ^ 64 := by
    have h1 : w_fr.toNat + 280 ≤ scratchEnd := hfr_in.2
    have h2 : scratchEnd ≤ 2 ^ 64 := by decide
    omega
  have hst_fr : ∀ {s0 : PanSemStateFiniteExact 64 F} {z0 : Bool} {off_out off_fr : Nat} {tail : ProgHOL 64},
      s0.code = originalRuntimeCode →
      PmcPackState entry s0 w_out w_fr (memW s (w_fr.toNat + 88)) z0 →
      PtxBlockOutUnhit entry s0 →
      off_out % 8 = 0 → off_out < 96 → off_out ≠ 16 →
      off_fr % 8 = 0 → off_fr < 280 →
      (∀ s1 : PanSemStateFiniteExact 64 F,
        s1.code = originalRuntimeCode →
        PmcPackState entry s1 w_out w_fr (memW s (w_fr.toNat + 88)) z0 →
        PtxBlockOutUnhit entry s1 →
        PmcBoRun entry tail s1) →
      PmcBoRun entry
        (.seq (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 off_out)])
                      (.load .one (.op .add [.var .local (ofString "frame"), .const (BitVec.ofNat 64 off_fr)])))
              tail) s0 :=
    fun hc0 hp0 hu_0 ho8 holt hone hf8 hflt ht =>
      pmcBoPack_store_frame_then hp0 hu_0 ho8 holt hone hf8 hflt (fun hp1 hu_1 => ht _ hc0 hp1 hu_1)
  unfold PmcBoRun
  intro hres hnex
  unfold pmcPack pmcCode at hres hnex ⊢
  simp only [sourceFunctionEntry, Guest.Software.guestFn_process_message_call,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil,
    R13Shards.spineAt] at hres hnex ⊢
  revert hres hnex
  change PmcBoRun entry _ s
  refine hst_fr hcode hps0 hu0 (by decide) (by decide) (by decide) (by decide) (by decide) (fun s1 hc1 hps1 hu1 => ?_)
  refine hst_fr hc1 hps1 hu1 (by decide) (by decide) (by decide) (by decide) (by decide) (fun s2 hc2 hps2 hu2 => ?_)
  refine hst_fr hc2 hps2 hu2 (by decide) (by decide) (by decide) (by decide) (by decide) (fun s3 hc3 hps3 hu3 => ?_)
  refine hst_fr hc3 hps3 hu3 (by decide) (by decide) (by decide) (by decide) (by decide) (fun s4 hc4 hps4 hu4 => ?_)
  refine hst_fr hc4 hps4 hu4 (by decide) (by decide) (by decide) (by decide) (by decide) (fun s5 hc5 hps5 hu5 => ?_)
  refine hst_fr hc5 hps5 hu5 (by decide) (by decide) (by decide) (by decide) (by decide) (fun s6 hc6 hps6 hu6 => ?_)
  have hargs6 : evalListHOLFinite s6 (h := fun a => Classical.propDecidable (s6.memaddrs a))
      [.var .local (ofString "frame")] = some [.val (.word w_fr)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact, hps6.2.2.1]
  refine pmcBoPack_decCall_ro_then hc6 ro_frame_state_gas_used hargs6 (by decide) (by decide) hps6 hu6
    (fun w_fsg s_fsg hc7 hs_fsg hps7 hu7 => ?_)
  have hload200 := pmc_load_local_off hps7.2.2.1 hps7.2.2.2.1 hfr_hi (by decide) (show 200 < 280 by decide)
  have hval72 : @evalHOLExact 64 F _ s_fsg.toExact (fun a => Classical.propDecidable (s_fsg.memaddrs a))
      (.op .add [.var .local (ofString "fsg"),
        .load .one (.op .add [.var .local (ofString "frame"), .const (BitVec.ofNat 64 200)])]) =
      some (.val (.word (w_fsg + BitVec.ofNat 64 (memW s_fsg (w_fr.toNat + 200))))) := by
    have hl200' : @evalHOLExact 64 F _ s_fsg.toExact (fun a => Classical.propDecidable (s_fsg.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "frame"), .const 200#64])) =
        some (.val (.word (BitVec.ofNat 64 (memW s_fsg (w_fr.toNat + 200))))) := hload200
    have hfsg' : @evalHOLExact 64 F _ s_fsg.toExact (fun a => Classical.propDecidable (s_fsg.memaddrs a))
        (.var .local (ofString "fsg")) = some (.val (.word w_fsg)) := by
      simp [evalHOLExact, hs_fsg]
    have hlist72 : @evalListHOLExact 64 F _ s_fsg.toExact (fun a => Classical.propDecidable (s_fsg.memaddrs a))
        [.var .local (ofString "fsg"),
         .load .one (.op .add [.var .local (ofString "frame"), .const 200#64])] =
        some [.val (.word w_fsg), .val (.word (BitVec.ofNat 64 (memW s_fsg (w_fr.toNat + 200))))] := by
      simp [evalListHOLExact, hfsg', hl200']
    unfold evalHOLExact
    rw [hlist72]
    simp [valueIsWord, valueWord, wordOpHOL, wordOp]
  obtain ⟨hev72, hps8⟩ := pmcPackState_store hps7 (off := 72) (by decide) (by decide) (by decide) hval72
  have hu8 : PtxBlockOutUnhit entry
      { s_fsg with memory := (pmcUpdW s_fsg.memory (BitVec.ofNat 64 (w_out.toNat + 72))
          (w_fsg + BitVec.ofNat 64 (memW s_fsg (w_fr.toNat + 200)))) } :=
    ptxBlockOutUnhit_of_pmcUpdW hps7.1 hps7.2.1.2.1.1.2 hps7.2.1.2.2.2.2.1 (by decide) hu7
  unfold PmcBoRun
  rw [evaluateHOLFiniteState_seq_line780, hev72]
  change PmcBoRun entry _ _
  refine pmcBoPack_ite160_step hps8 hu8 (fun _ s_post hps9 hu9 => ?_)
  refine pmcBoPack_store_frame_then hps9 hu9 (by decide) (by decide) (by decide) (by decide) (by decide) (fun hps10 hu10 => ?_)
  refine pmcBoPack_store_frame_then hps10 hu10 (by decide) (by decide) (by decide) (by decide) (by decide) (fun hps11 hu11 => ?_)
  exact pmcBoPack_return hps11 hu11

/-! ## 6. Top-Level `PmcMarksBoStrong` Assembly from Callees -/

/-- Strengthened `process_message_call` bridge: given `process_message` and
    `process_create_message` satisfying their `WorldKeepsIn` marks contracts
    plus `PtxBlockOutUnhit` on non-exception returns, produces `PmcMarksBoStrong`
    (closing the Phase 3 `PmcMarksBoStrong` callee hypothesis). -/
theorem wk_process_message_call_marks_bo_of_callees
    (hpm : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultMarksExactBo (ofString "process_message"))
    (hpcm : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultMarksBo (ofString "process_create_message")) :
    PmcMarksBoStrong := by
  have hpm_m : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultMarksExact (ofString "process_message") :=
    worldKeepsIn_mono_extra (fun _ _ _ _ _ h => h.1) hpm
  have hpcm_m : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultMarks (ofString "process_create_message") :=
    worldKeepsIn_mono_extra (fun _ _ _ _ _ h => h.1) hpcm
  have hmarks_wk := wk_process_message_call_marks_of_callees hpm_m hpcm_m
  refine ⟨_, _, _, pmc_lookup, ?_⟩
  intro F s hcode hready _hparams _hnt hres
  have hpm_s : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultStrong (ofString "process_message") :=
    worldKeepsIn_mono_extra (fun _ _ _ _ _ h => h.1.1) hpm_m
  have hpcm_s : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultStrong (ofString "process_create_message") :=
    worldKeepsIn_mono_extra (fun _ _ _ _ _ h => h.1) hpcm_m
  have hstrong_run := pmcInit_cut s _
    (pmcDispatch_cut hpm_s hpcm_s s _ (pmcPack_cut s)) s hcode (pmcA0_init s hready)
  rw [← pmc_phases_eq] at hstrong_run
  unfold PmcRelRunStrong pmcCode pmcTables pmcRegions ptxRegions pmcGlobals pmcKeep at hstrong_run
  have hws_strong := hstrong_run hres
  have hmarks_run := pmcMarksInit_cut s _
    (pmcMarksDispatch_cut hpm_m hpcm_m s _ (pmcMarksPack_cut s)) s hcode (pmcA0_init s hready)
  rw [← pmc_phases_eq] at hmarks_run
  unfold PmcMarksRun pmcCode at hmarks_run
  have hmarks := hmarks_run hres
  have hbo_run := pmcBoInit_cut s _
    (pmcBoDispatch_cut hpm hpcm s _ (pmcBoPack_cut s)) s hcode (pmcA0_init s hready)
  rw [← pmc_phases_eq] at hbo_run
  unfold PmcBoRun pmcCode at hbo_run
  obtain ⟨hAp, hhp, hG, hK, hW⟩ := hws_strong
  refine ⟨hAp, hhp, hG, hK, fun S Nd hWT hTS hD => ?_⟩
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hQ⟩ := hW S Nd hWT hTS hD
  exact ⟨S', Nd', hsub, hWT', hOG, hFO, ⟨hQ, hmarks⟩, fun hnex => hbo_run hres hnex⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
