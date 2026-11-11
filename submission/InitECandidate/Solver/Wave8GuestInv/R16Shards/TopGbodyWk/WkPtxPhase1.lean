import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase1C

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
open InitECandidate.Solver.Wave8GuestInv.R13Shards
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

open private wk_alloc_local rt_alloc_local ro_u256_fits_word ro_u256_lt
  ro_calculate_total_blob_gas ro_fee_mul ro_u256_add_carry ro_is_valid_delegation
  wsEnv_of_worldOK_local heapByteEff_of_m23_bre_local wk_calculate_blob_gas_price_local
  lookup_calculate_blob_gas_price_local lookup_taylor_exponential_local
  taylor_exponential_wsSafe_local lookup_check_transaction checkTxBufs
  validBufList_checkTxBufs safeStepGlobals_checkTx ptxWorldStep_strong_with_locals_right
  acctMut_sub_ptx acctMut_globals_sub ptxKeep_not_acctMut_global
  noReturnProg evaluate_noReturnProg
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkBlockTxProcess

/-! # Phase 1 Relational Cut (`WkPtxPhase1`) -/

/-! ## 1. Prefix Step Lemmas (Up to `StageP 1`) -/

theorem p1_prefix_state_fresh_tx {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {tail : ProgHOL 64}
    (hc : s.code = originalRuntimeCode)
    (hef : PtxEntryFull entry s)
    (htail : ∀ s1 : PanSemStateFiniteExact 64 F,
      s1.code = originalRuntimeCode →
      P1State false 0 [] false entry s1 →
      TxValidEncodeReady s1 →
      TxValidRecoverReady s1 →
      PtxRelRunStrong entry tail s1) :
    PtxRelRunStrong entry (.seq (.call (some (none, none)) (ofString "state_fresh_tx") []) tail) s := by
  obtain ⟨heq_e, hRs, hb, hVE, hVR⟩ := hef
  subst heq_e
  have hbase0 : PtxRelBase false entry entry := ptxRelBase_init entry hRs hb
  have hst0 : PtxP1.StageP 0 entry := PtxP1.stage0 hRs
  refine ptxRelRunStrong_call0_scBo (B := [])
    (gw := ["heap_ptr", "journal_n", "ts"]) (keep := ptxWithdrawalKeep) (Q := NoExtra)
    hbase0 hc
    (by intro p hp; cases hp) (by intro p hp; cases hp)
    (by intro g hg; simp at hg; rcases hg with rfl | rfl | rfl <;> decide)
    (by decide) (by decide)
    ptxKeepSub_ptxWithdrawalKeep (Or.inr (by simp [ptxWithdrawalKeep]))
    (ofString "state_fresh_tx") [] tail wkScBo_state_fresh_tx
    (fun vs body callee ret v post _ hl hb_ev hstep _ hbase1 hpc => ?_)
  have hstep_s : WorldStep (bufRegions []) ["heap_ptr", "journal_n", "ts"] ptxWithdrawalKeep NoExtra
      entry (some (.returned v)) post :=
    R13Shards.worldStep_with_locals hstep entry.locals entry.clock
  have hst1 : PtxP1.StageP 0 { post with locals := entry.locals } :=
    PtxP1.stage_after_scratchStep hstep hst0 (gs := []) (by simp [PtxP1.ScratchSpec]) rfl
      (by decide) (by decide)
      (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp [ptxWithdrawalKeep]) (by decide)
  have hu_heap := state_fresh_tx_heap_unhit hc hbase0.world hl hb_ev
  have hVE_post : TxValidEncodeAt post (locN entry "tx") :=
    txValidEncodeAt_step_heap_unhit hbase0.world.1 hstep.1 hstep.2.1 hu_heap hVE
  have hVR_post : TxValidRecoverReadyAt post (locN entry "tx") :=
    txValidRecoverReadyAt_step_heap_unhit hbase0.world.1 hstep.1.1 hstep.2.1 hu_heap hVR
  have hVE1 : TxValidEncodeReady { post with locals := entry.locals } :=
    txValidEncodeAt_with_locals post entry.locals post.clock hVE_post
  have hVR1 : TxValidRecoverReady { post with locals := entry.locals } :=
    txValidRecoverReadyAt_with_locals post entry.locals post.clock hVR_post
  have hexpw1 : globN { post with locals := entry.locals } "bn_expw" = globN entry "bn_expw" :=
    globN_eq_of_lookup (hstep_s.2.2.1 _ (by decide))
  have hgamma1 : globN { post with locals := entry.locals } "bn_gamma" = globN entry "bn_gamma" :=
    globN_eq_of_lookup (hstep_s.2.2.1 _ (by decide))
  have hp1 : P1State false 0 [] false entry { post with locals := entry.locals } :=
    ⟨hbase1, hst1, fun _ hx => False.elim (List.not_mem_nil hx), hexpw1, hgamma1, rfl, rfl,
      fun hh => Bool.noConfusion hh⟩
  exact htail { post with locals := entry.locals } hpc hp1 hVE1 hVR1

theorem p1_prefix_assign_bal_index {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {tail : ProgHOL 64}
    (hc : s.code = originalRuntimeCode)
    (hp : P1State false 0 [] false entry s)
    (hVE : TxValidEncodeReady s)
    (hVR : TxValidRecoverReady s)
    (htail : ∀ s1 : PanSemStateFiniteExact 64 F,
      s1.code = originalRuntimeCode →
      P1State false 0 [("tx", .one), ("index", .one)] false entry s1 →
      TxValidEncodeReady s1 →
      TxValidRecoverReady s1 →
      PtxRelRunStrong entry tail s1) :
    PtxRelRunStrong entry
      (.seq (.assign .global (ofString "bal_index")
        (.op .add [.var .local (ofString "index"), .const 1])) tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hres ⊢
  rcases hv : evalAt s (.op .add [.var .local (ofString "index"), .const 1]) with _ | v
  · change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) _ = none at hv
    rw [hv] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h)
  · have hv_ex : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.op .add [.var .local (ofString "index"), .const 1]) = some v := hv
    rw [hv_ex] at hres ⊢
    dsimp only at hres ⊢
    by_cases hval : isValidValueHOLFinite s .global (ofString "bal_index") v = true
    · rw [if_pos hval] at hres ⊢
      obtain ⟨w, rfl⟩ := PtxP1.eval_is_word_op hv
      obtain ⟨w_tx, hw_tx⟩ := phase1_txReadyStrong_tx_word hp.stage.1
      obtain ⟨w_idx, hw_idx⟩ := phase1_index_word_of_add hv
      set s1 := setKvarHOLFinite .global (ofString "bal_index") (.val (.word w)) s
      have hbase1 : PtxRelBase false entry s1 := ptxRelBase_assign_bal_index hp.base w
      have hRs1 : TxReadyStrong s1 := PtxP1.txReadyStrong_assign_bal_index hp.stage.1 w
      have hst1 : PtxP1.StageP 0 s1 := PtxP1.stage0 hRs1
      have hsh1 : PtxLocalShapeMap [("tx", .one), ("index", .one)] s1 := by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact ⟨.val (.word w_tx), hw_tx, by simp [shapeOfHOLExact]⟩
        · exact ⟨.val (.word w_idx), hw_idx, by simp [shapeOfHOLExact]⟩
      have hexpw1 : globN s1 "bn_expw" = globN entry "bn_expw" := by
        have hg : globN s1 "bn_expw" = globN s "bn_expw" := by
          simp [s1, globN, setKvarHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE,
            show ofString "bal_index" ≠ ofString "bn_expw" by decide]
        exact hg.trans hp.expw
      have hgamma1 : globN s1 "bn_gamma" = globN entry "bn_gamma" := by
        have hg : globN s1 "bn_gamma" = globN s "bn_gamma" := by
          simp [s1, globN, setKvarHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE,
            show ofString "bal_index" ≠ ofString "bn_gamma" by decide]
        exact hg.trans hp.gamma
      have hVE1 : TxValidEncodeReady s1 := by
        have hhp : globN s1 "heap_ptr" = globN s "heap_ptr" := by
          simp [s1, globN, setKvarHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE,
            show ofString "bal_index" ≠ ofString "heap_ptr" by decide]
        exact txValidEncodeAt_step_heap_unhit hp.base.world.1 hbase1.world.1
          (by rw [hhp]) (fun _ _ _ => rfl) hVE
      have hVR1 : TxValidRecoverReady s1 := by
        have hhp : globN s1 "heap_ptr" = globN s "heap_ptr" := by
          simp [s1, globN, setKvarHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE,
            show ofString "bal_index" ≠ ofString "heap_ptr" by decide]
        exact txValidRecoverReadyAt_step_heap_unhit hp.base.world.1 hbase1.world.1.1
          (by rw [hhp]) (fun _ _ _ => rfl) hVR
      have hp1 : P1State false 0 [("tx", .one), ("index", .one)] false entry s1 :=
        ⟨hbase1, hst1, hsh1, hexpw1, hgamma1, hp.tx_eq, hp.idx_eq, fun hh => Bool.noConfusion hh⟩
      exact htail s1 hc hp1 hVE1 hVR1 hres
    · rw [if_neg hval] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h)

theorem p1_prefix_encode_transaction {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {tail : ProgHOL 64}
    (hc : s.code = originalRuntimeCode)
    (hp : P1State false 0 [("tx", .one), ("index", .one)] false entry s)
    (hVE : TxValidEncodeReady s)
    (hVR : TxValidRecoverReady s)
    (htail : ∀ (s1 : PanSemStateFiniteExact 64 F) (a b : BitVec 64),
      s1.code = originalRuntimeCode →
      P1State false 0 [("enc", .comb [.one, .one]), ("tx", .one), ("index", .one)] false entry s1 →
      s1.locals.lookup (ofString "enc") = some (.rStruct [.val (.word a), .val (.word b)]) →
      b.toNat < 2 ^ 40 →
      TxValidRecoverReady s1 →
      PtxRelRunStrong entry tail s1) :
    PtxRelRunStrong entry
      (.decCall (ofString "enc") (.comb [.one, .one]) (ofString "encode_transaction")
        [.var .local (ofString "tx")] tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hres ⊢
  rcases ha : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "tx")] with _ | vs
  · simp [evalListHOLFinite, ha] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [evalListHOLFinite, ha] at hres ⊢
    have ha_fin : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "tx")] = some vs := by simpa [evalListHOLFinite] using ha
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "encode_transaction") vs with _ | ⟨body, callee, ret⟩
    · simp only [hl] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hl] at hres ⊢
      by_cases hcz : s.clock = 0
      · simp only [hcz, ↓reduceIte] at hres
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      · simp only [hcz, ↓reduceIte] at hres ⊢
        obtain ⟨tv, he_tx, ht_tx⟩ := PtxP1.params_one_value s (ofString "encode_transaction") (ofString "tx")
          .one _ (.comb [.one, .one]) (by rw [hc]; exact PtxP1.lookup_encode_transaction)
          (.var .local (ofString "tx")) vs body callee ret ha_fin hl
        have htx_cal : callee.lookup (ofString "tx") = s.locals.lookup (ofString "tx") := ht_tx.trans he_tx.symm
        have hVE_cal : TxValidEncodeReady (callEntryStateHOLFinite s callee) := by
          unfold TxValidEncodeReady at hVE ⊢
          have hloc : locN (callEntryStateHOLFinite s callee) "tx" = locN s "tx" := by
            simp [callEntryStateHOLFinite, locN, htx_cal]
          rw [hloc]
          exact txValidEncodeAt_with_locals s callee (s.clock - 1) hVE
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, post⟩
        have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (rb, post) := hb
        rw [hb] at hmeta
        simp only [hb] at hres ⊢
        cases rb with
        | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | some cr =>
          cases cr with
          | timeOut | error | «break» | «continue» | finalFfi _ =>
            exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | exception eid ev =>
            dsimp only at hres ⊢
            have hspec := FunSpec.at_lookup «wk_encode_transaction_bounded» s hc vs body callee ret hl
              ⟨localsFree_worldOK s callee (s.clock - 1) hp.base.world, hVE_cal⟩ (by rw [hb']; simp)
            rw [hb'] at hspec
            have hstep_cal := hspec hres
            have hstep_s : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra s (some (.exception eid ev)) post :=
              R13Shards.worldStep_with_locals hstep_cal s.locals s.clock
            have hex := ptxRelBase_exception_worldStep hp.base
              (by intro p hp0; cases hp0) (by intro p hp0; cases hp0)
              (by intro g hg; simp at hg; subst hg; decide)
              ptxKeepSub_stdKeep hstep_s
            exact ptxWorldStep_strong_with_locals_right .empty post.clock hex
          | returned rv =>
            dsimp only at hres ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact rv) (.comb [.one, .one]) && shapeEqHOL (shapeOfHOLExact rv) ret) = true
            · simp only [hsh, ↓reduceIte] at hres ⊢
              have hsh1 : shapeEqHOL (shapeOfHOLExact rv) (.comb [.one, .one]) = true :=
                ((Bool.and_eq_true _ _).mp hsh).1
              have hsh_eq : shapeOfHOLExact rv = .comb [.one, .one] :=
                (shapeEqHOL_eq_true _ _).1 hsh1
              obtain ⟨a, b, rfl⟩ := PtxP1.shape_pair_words hsh1
              have hspec := FunSpec.at_lookup «wk_encode_transaction_bounded» s hc vs body callee ret hl
                ⟨localsFree_worldOK s callee (s.clock - 1) hp.base.world, hVE_cal⟩ (by rw [hb']; simp)
              rw [hb'] at hspec
              have hstep_cal := hspec (Or.inl ⟨_, rfl⟩)
              have hstep_s : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra
                  s (some (.returned (.rStruct [.val (.word a), .val (.word b)]))) post :=
                R13Shards.worldStep_with_locals hstep_cal s.locals s.clock
              obtain ⟨Sc, Nc, hWc, _⟩ := hp.stage.1.2.2.2.2
              obtain ⟨_, _, _, _, _, _, hbo_u_cal, hret_sl⟩ :=
                hstep_cal.2.2.2.2 Sc Nc
                  ((R13Shards.worldTypedWith_with_locals s callee (s.clock - 1) Sc Nc).2 hWc)
                  (by simp [IvlsDisj])
              obtain ⟨a', b', hv_eq, _, _, hb_lt⟩ := hret_sl _ rfl
              injection hv_eq with hfs_eq
              injection hfs_eq with h0 hfs1
              injection hfs1 with h1 _
              injection h0 with h0'; injection h0' with ha_eq
              injection h1 with h1'; injection h1' with hb_eq
              subst ha_eq; subst hb_eq
              have hsp_eq : globN post "scratch_ptr" = globN s "scratch_ptr" :=
                globN_eq_of_lookup (hstep_s.2.2.1 _ (by decide))
              have hfmp_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" :=
                globN_eq_of_lookup (hstep_s.2.2.1 _ (by decide))
              have hbo_u : PtxBlockOutUnhit s post := hbo_u_cal
              have hbase_post : PtxRelBase false entry post :=
                ptxRelBase_step_of_blockOutUnhit hp.base
                  (by intro p hp0; cases hp0) (by intro p hp0; cases hp0)
                  (by intro g hg; simp at hg; subst hg; decide)
                  ptxKeepSub_stdKeep (by decide) (Or.inr (by simp [stdKeep]))
                  hstep_s (by omega) (by omega) hbo_u
              set s1 := setVarHOLFinite (ofString "enc") (.rStruct [.val (.word a), .val (.word b)])
                { post with locals := s.locals }
              have hbase1 : PtxRelBase false entry s1 :=
                ptxRelBase_with_locals hbase_post
                  (s.locals.update (ofString "enc", .rStruct [.val (.word a), .val (.word b)])) post.clock
              have hst_post : PtxP1.StageP 0 { post with locals := s.locals } :=
                PtxP1.stage_after_scratchStep hstep_cal hp.stage (gs := []) (by simp [PtxP1.ScratchSpec]) rfl
                  (by decide) (by decide)
                  (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp [stdKeep]) (by decide)
              have hst1 : PtxP1.StageP 0 s1 :=
                LocalsOnly.setVar (PtxP1.localsOnly_stage 0) (by decide) _ _ hst_post
              have hsh1 : PtxLocalShapeMap [("enc", .comb [.one, .one]), ("tx", .one), ("index", .one)] s1 :=
                ptxLocalShapeMap_add s post hp.shapes "enc" (.comb [.one, .one]) _ (by decide) hsh_eq
              have hexpw1 : globN s1 "bn_expw" = globN entry "bn_expw" :=
                (globN_eq_of_lookup (hstep_s.2.2.1 _ (by decide))).trans hp.expw
              have hgamma1 : globN s1 "bn_gamma" = globN entry "bn_gamma" :=
                (globN_eq_of_lookup (hstep_s.2.2.1 _ (by decide))).trans hp.gamma
              have htx1 : s1.locals.lookup (ofString "tx") = entry.locals.lookup (ofString "tx") := by
                simp only [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show (ofString "enc" == ofString "tx") = false by decide, Bool.false_eq_true, ↓reduceIte]
                exact hp.tx_eq
              have hidx1 : s1.locals.lookup (ofString "index") = entry.locals.lookup (ofString "index") := by
                simp only [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show (ofString "enc" == ofString "index") = false by decide, Bool.false_eq_true, ↓reduceIte]
                exact hp.idx_eq
              have henc1 : s1.locals.lookup (ofString "enc") = some (.rStruct [.val (.word a), .val (.word b)]) := by
                simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
              have hu_heap := encode_tx_heap_unhit hc hp.base.world hVE ha_fin hl hb'
              have hVR_post : TxValidRecoverReadyAt post (locN s "tx") :=
                txValidRecoverReadyAt_step_heap_unhit hp.base.world.1 hstep_cal.1.1 hstep_cal.2.1 hu_heap hVR
              have htx_loc1 : locN s1 "tx" = locN s "tx" := by
                simp only [s1, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show (ofString "enc" == ofString "tx") = false by decide, Bool.false_eq_true, ↓reduceIte]
              have hVR1 : TxValidRecoverReady s1 := by
                unfold TxValidRecoverReady
                rw [htx_loc1]
                exact txValidRecoverReadyAt_with_locals post s1.locals post.clock hVR_post
              have hp1 : P1State false 0 [("enc", .comb [.one, .one]), ("tx", .one), ("index", .one)] false entry s1 :=
                ⟨hbase1, hst1, hsh1, hexpw1, hgamma1, htx1, hidx1, fun hh => Bool.noConfusion hh⟩
              have hmid := htail s1 a b (hmeta.trans hc) hp1 henc1 hb_lt hVR1 hres
              exact ptxWorldStep_strong_with_locals_right
                (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 tail).2.locals
                  (ofString "enc", s.locals.lookup (ofString "enc")))
                (evaluateHOLFiniteState s1 tail).2.clock hmid
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hres
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

theorem p1_prefix_store_encSlots {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {a b : BitVec 64} {tail : ProgHOL 64}
    (hc : s.code = originalRuntimeCode)
    (hp : P1State false 0 [("enc", .comb [.one, .one]), ("tx", .one), ("index", .one)] false entry s)
    (henc : s.locals.lookup (ofString "enc") = some (.rStruct [.val (.word a), .val (.word b)]))
    (hb_lt : b.toNat < 2 ^ 40)
    (hVR : TxValidRecoverReady s)
    (htail : ∀ s2 : PanSemStateFiniteExact 64 F,
      s2.code = originalRuntimeCode →
      P1State true 0 [("enc", .comb [.one, .one]), ("tx", .one), ("index", .one)] false entry s2 →
      TxValidRecoverReady s2 →
      PtxRelRunStrong entry tail s2) :
    PtxRelRunStrong entry
      (.seq (.store (PtxP1.encDst false) (.rfield 0 (.var .local (ofString "enc"))))
        (.seq (.store (PtxP1.encDst true) (.rfield 1 (.var .local (ofString "enc")))) tail)) s := by
  intro hres
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store] at hres ⊢
  rcases hx0 : @evalHOLExact 64 F _ s.toExact (fun addr => Classical.propDecidable (s.memaddrs addr))
      (PtxP1.encDst false) with _ | vx0
  · simp [hx0] at hres; exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [hx0] at hres ⊢
    rcases vx0 with ⟨⟨x0⟩⟩ | _ | _
    · have hv0 : @evalHOLExact 64 F _ s.toExact (fun addr => Classical.propDecidable (s.memaddrs addr))
          (.rfield 0 (.var .local (ofString "enc"))) = some (.val (.word a)) := by
        simp [evalHOLExact, henc]
      simp only [valueIsWord, ↓reduceIte, valueWord, hv0] at hres ⊢
      rcases hst0 : @panMemStoresHOL 64 _ x0 (flattenHOL (ValueHOL.val (HolWordLab.word a)))
          s.memaddrs (fun addr => Classical.propDecidable (s.memaddrs addr)) s.memory with _ | mem1
      · simp [hst0] at hres; exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      · simp only [hst0] at hres ⊢
        obtain ⟨hdom0, _, hmem0⟩ := R13Shards.panMemStoresHOL_word_spec (s := s) (by simpa only [flattenHOL] using hst0)
        have hin0 := PtxP1.encDst0_inside hp.stage.1 hx0
        have hidx_eq0 : locN s "index" = locN entry "index" := by simp only [locN, hp.idx_eq]
        set s1 : PanSemStateFiniteExact 64 F := { s with memory := mem1 }
        have hbase1 : PtxRelBase false entry s1 :=
          ptxRelBase_store_encSlot0 hp.base hp.stage.1 hidx_eq0 hx0 hdom0 hmem0
        have hRs1 : TxReadyStrong s1 := PtxP1.txReadyStrong_store_encArray hp.stage.1 hdom0 hin0 hmem0
        have hVR1 : TxValidRecoverReady s1 := txValidRecoverReadyAt_store_encArray hp.stage.1 hin0 hmem0 hVR
        have henc1 : s1.locals.lookup (ofString "enc") = some (.rStruct [.val (.word a), .val (.word b)]) := henc
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store] at hres ⊢
        rcases hx1 : @evalHOLExact 64 F _ s1.toExact (fun addr => Classical.propDecidable (s1.memaddrs addr))
            (PtxP1.encDst true) with _ | vx1
        · simp [hx1] at hres; exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        · simp only [hx1] at hres ⊢
          rcases vx1 with ⟨⟨x1⟩⟩ | _ | _
          · have hv1 : @evalHOLExact 64 F _ s1.toExact (fun addr => Classical.propDecidable (s1.memaddrs addr))
                (.rfield 1 (.var .local (ofString "enc"))) = some (.val (.word b)) := by
              simp [evalHOLExact, henc1]
            simp only [valueIsWord, ↓reduceIte, valueWord, hv1] at hres ⊢
            rcases hst1 : @panMemStoresHOL 64 _ x1 (flattenHOL (ValueHOL.val (HolWordLab.word b)))
                s1.memaddrs (fun addr => Classical.propDecidable (s1.memaddrs addr)) s1.memory with _ | mem2
            · simp [hst1] at hres; exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
            · simp only [hst1] at hres ⊢
              obtain ⟨hdom1, hmem1_x, hmem1⟩ :=
                R13Shards.panMemStoresHOL_word_spec (s := s1) (by simpa only [flattenHOL] using hst1)
              have hin1 := PtxP1.encDst8_inside hRs1 hx1
              have hidx_eq1 : locN s1 "index" = locN entry "index" := hidx_eq0
              set s2 : PanSemStateFiniteExact 64 F := { s1 with memory := mem2 }
              have hbase2 : PtxRelBase true entry s2 :=
                ptxRelBase_store_encSlot1 hbase1 hRs1 hidx_eq1 hb_lt hx1 hdom1 hmem1_x hmem1
              have hRs2 : TxReadyStrong s2 := PtxP1.txReadyStrong_store_encArray hRs1 hdom1 hin1 hmem1
              have hVR2 : TxValidRecoverReady s2 := txValidRecoverReadyAt_store_encArray hRs1 hin1 hmem1 hVR1
              have hp2 : P1State true 0 [("enc", .comb [.one, .one]), ("tx", .one), ("index", .one)] false entry s2 :=
                ⟨hbase2, PtxP1.stage0 hRs2, hp.shapes, hp.expw, hp.gamma, hp.tx_eq, hp.idx_eq,
                  fun hh => Bool.noConfusion hh⟩
              exact htail s2 hc hp2 hVR2 hres
          · simp [valueIsWord] at hres; exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          · simp [valueIsWord] at hres; exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp [valueIsWord] at hres; exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp [valueIsWord] at hres; exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

theorem p1_prefix_alloc_recover {F : Type} {xs : List (String × ShapeHOL)}
    {entry s : PanSemStateFiniteExact 64 F} {tail : ProgHOL 64}
    (hc : s.code = originalRuntimeCode)
    (hp : P1State true 0 xs false entry s)
    (hne_xs : ∀ x ∈ xs, ofString x.1 ≠ ofString "sender")
    (hVR : TxValidRecoverReady s)
    (htail : ∀ s2 : PanSemStateFiniteExact 64 F,
      s2.code = originalRuntimeCode →
      P1State true 1 (("sender", .one) :: xs) true entry s2 →
      PtxRelRunStrong entry tail s2) :
    PtxRelRunStrong entry
      (.decCall (ofString "sender") .one (ofString "alloc") [.const 24]
        (.seq (.call (some (none, none)) (ofString "recover_sender_with_chain_id") PtxP1.recoverArgs) tail)) s := by
  intro hres
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hres ⊢
  have ha_al : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const 24] = some [.val (.word 24#64)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact]
  simp only [ha_al] at hres ⊢
  rcases hl_al : lookupCodeHOLFinite s.code.lookup (ofString "alloc") [.val (.word 24#64)]
      with _ | ⟨body_al, cal_al, ret_al⟩
  · simp only [hl_al] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [hl_al] at hres ⊢
    by_cases hcz_al : s.clock = 0
    · simp only [hcz_al, ↓reduceIte] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hcz_al, ↓reduceIte] at hres ⊢
      obtain ⟨nv, he_n, hn_cal⟩ := PtxP1.params_one_value s (ofString "alloc") (ofString "n")
        .one _ .one (by rw [hc]; exact PtxP1.lookup_alloc) (.const 24) [.val (.word 24#64)] body_al cal_al ret_al ha_al hl_al
      have hnv : nv = .val (.word 24#64) := by simpa [evalAt, evalHOLExact] using he_n.symm
      subst hnv
      have hcn : locN (callEntryStateHOLFinite s cal_al) "n" = 24 := by
        simp [locN, callEntryStateHOLFinite, hn_cal]
      have hl_al_rt : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "alloc") [.val (.word 24#64)] =
          some (body_al, cal_al, ret_al) := by rwa [← hc]
      have hraw_al := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "alloc")
        [.val (.word 24#64)] body_al cal_al ret_al hl_al_rt
      have hbody_al_eq : body_al = sourceFnBody Guest.Software.guestFn_alloc := by
        unfold lookupCodeHOLExact at hraw_al
        rw [R13Shards.lookup_alloc_r13] at hraw_al
        dsimp only at hraw_al
        split at hraw_al
        · injection hraw_al with hp0; exact (Prod.mk.inj hp0).1.symm
        · cases hraw_al
      have hmeta_al := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s cal_al) body_al).1
      rcases hb_al : evaluateHOLFiniteState (callEntryStateHOLFinite s cal_al) body_al with ⟨rb_al, post_al⟩
      have hb_al' : evaluateHOLFiniteState (callEntryStateHOLFinite s cal_al) body_al = (rb_al, post_al) := hb_al
      rw [hb_al] at hmeta_al
      simp only [hb_al] at hres ⊢
      cases rb_al with
      | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      | some cr_al =>
        cases cr_al with
        | timeOut | error | «break» | «continue» | finalFfi _ =>
          exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | exception eid ev =>
          dsimp only at hres ⊢
          have hspec_al := FunSpec.at_lookup wk_alloc_local s hc _ body_al cal_al ret_al hl_al
            (localsFree_worldOK s cal_al (s.clock - 1) hp.base.world) (by rw [hb_al']; simp)
          rw [hb_al'] at hspec_al
          have hstep_s : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra
              s (some (.exception eid ev)) post_al :=
            R13Shards.worldStep_with_locals (hspec_al hres) s.locals s.clock
          have hex := ptxRelBase_exception_worldStep hp.base
            (by intro p hp0; cases hp0) (by intro p hp0; cases hp0)
            (by intro g hg; simp at hg; subst hg; decide)
            ptxKeepSub_stdKeep hstep_s
          exact ptxWorldStep_strong_with_locals_right .empty post_al.clock hex
        | returned val_al =>
          dsimp only at hres ⊢
          by_cases hsh_al : (shapeEqHOL (shapeOfHOLExact val_al) .one && shapeEqHOL (shapeOfHOLExact val_al) ret_al) = true
          · simp only [hsh_al, ↓reduceIte] at hres ⊢
            have hab_al := R13Shards.alloc_body_resumes_props (callEntryStateHOLFinite s cal_al)
              hc (localsFree_arenaReady s cal_al (s.clock - 1) hp.base.world.1)
              (by rw [← hbody_al_eq, hb_al']; exact Or.inl ⟨val_al, rfl⟩)
            dsimp only at hab_al
            rw [← hbody_al_eq, hb_al'] at hab_al
            obtain ⟨p_al, q_al, hrv_al, hp_al_eq, _, _, _, hp_le_q_al, hpost_al_g, hpost_al_m, hpost_al_be, _, hA_al_post, hpost_al_hp, hpost_al_sp⟩ := hab_al
            have hrt_al := FunSpec.at_lookup rt_alloc_local s hc _ body_al cal_al ret_al hl_al
              (localsFree_arenaReady s cal_al (s.clock - 1) hp.base.world.1) (by rw [hb_al']; simp)
            rw [hb_al'] at hrt_al
            obtain ⟨w_snd, rfl, hAR_al, _, hw_snd8, hw_in_al, hw_ok_al⟩ := hrt_al val_al rfl
            rw [hcn] at hw_in_al hw_ok_al
            change Inside (w_snd.toNat, 24) (globN s "heap_ptr") (globN post_al "heap_ptr") at hw_in_al
            change WordsOK post_al (w_snd.toNat, 24) at hw_ok_al
            have heff_al : R13Shards.WorldFrameEff s post_al (([] : List Ivl) ++ ([] : List Ivl)) ["heap_ptr"] := by
              refine ⟨hA_al_post, hw_in_al.1.trans (by dsimp [Inside] at hw_in_al; omega),
                by rw [hpost_al_sp]; rfl,
                fun k hk => ?_, hpost_al_be,
                fun a _ => by rw [hpost_al_m]; rfl,
                fun a _ _ => by rw [hpost_al_m]; rfl,
                fun b _ _ _ => by unfold memB; rw [hpost_al_m, hpost_al_be]; rfl⟩
              have hne : ofString "heap_ptr" ≠ k := fun h => hk (by simp [h])
              rw [hpost_al_g]; simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
            have hws_al_dj : Wave8Contracts.M12.WorldStep (bufRegions []) ["heap_ptr"] Wave8Contracts.M12.stdKeep
                (fun _ _ post0 Sy Ndy => IvlsDisj [(w_snd.toNat, 24)] (worldOwned post0 Sy Ndy))
                s (some (PanSemResultExact.returned (.val (.word w_snd)))) post_al :=
              heff_al.to_worldStep (R := bufRegions []) (extra := fun _ => []) (gw := ["heap_ptr"])
                (Q := fun _ _ post0 Sy Ndy => IvlsDisj [(w_snd.toNat, 24)] (worldOwned post0 Sy Ndy))
                (r := some (PanSemResultExact.returned (.val (.word w_snd)))) hp.base.world
                (fun g hg => Or.inl (by simpa using hg))
                (fun _ h => by simp at h)
                (fun Sy Ndy hWTy _ _ hno_new =>
                  R13Shards.disj_fresh_heap_of_worldOwned hp.base.world.1 hA_al_post hWTy
                    (fun o ho => by rcases hno_new o ho with rfl | h; exact Or.inl rfl; exact Or.inr (Or.inl h))
                    hno_new hw_in_al)
            have hal_typed : ∀ Sx Ndx, WorldTypedWith s Sx Ndx →
                ∃ Sy Ndy, (∀ t ∈ Sx, t ∈ Sy) ∧
                WorldTypedWith post_al Sy Ndy ∧
                OwnedGrows s post_al (worldOwned s Sx Ndx) (worldOwned post_al Sy Ndy) ∧
                FrameOutside s post_al (worldOwned s Sx Ndx ++ ([] : List Ivl) ++ [freeGap s]) (heapFree s) ∧
                IvlsDisj [(w_snd.toNat, 24)] (worldOwned post_al Sy Ndy) :=
              fun Sx Ndx hWTx => hws_al_dj.2.2.2.2 Sx Ndx hWTx (by simp [Wave8Contracts.M12.IvlsDisj, bufRegions])
            have hstep_al := FunSpec.at_lookup wk_alloc_local s hc _ body_al cal_al ret_al hl_al
              (localsFree_worldOK s cal_al (s.clock - 1) hp.base.world) (by rw [hb_al']; simp)
            rw [hb_al'] at hstep_al
            have hws_cal := hstep_al (Or.inl ⟨.val (.word w_snd), rfl⟩)
            have hws_s : WorldStep (bufRegions []) ["heap_ptr"] stdKeep NoExtra
                s (some (.returned (.val (.word w_snd)))) post_al :=
              R13Shards.worldStep_with_locals hws_cal s.locals s.clock
            have hbo_u_al : PtxBlockOutUnhit s post_al := by
              intro _ _ a _ _; rw [hpost_al_m]; rfl
            have hsp_al : globN post_al "scratch_ptr" = globN s "scratch_ptr" :=
              globN_eq_of_lookup (hws_s.2.2.1 _ (by decide))
            have hfmp_al : globN post_al "frame_mem_ptr" = globN s "frame_mem_ptr" :=
              globN_eq_of_lookup (hws_s.2.2.1 _ (by decide))
            have hbase_post_al : PtxRelBase true entry post_al :=
              ptxRelBase_step_of_blockOutUnhit hp.base
                (by intro p hp0; cases hp0) (by intro p hp0; cases hp0)
                (by intro g hg; simp at hg; subst hg; decide)
                ptxKeepSub_stdKeep (by decide) (Or.inr (by simp [stdKeep]))
                hws_s (by omega) (by omega) hbo_u_al
            set s1 := setVarHOLFinite (ofString "sender") (.val (.word w_snd)) { post_al with locals := s.locals }
            have hbase1 : PtxRelBase true entry s1 :=
              ptxRelBase_with_locals hbase_post_al (s.locals.update (ofString "sender", .val (.word w_snd))) post_al.clock
            have hc1 : s1.code = originalRuntimeCode := hmeta_al.trans hc
            have hsready := PtxP1.stage_after_scratchStep hws_cal hp.stage (gs := []) (by simp [PtxP1.ScratchSpec]) rfl
              (by decide) (by decide)
              (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp [stdKeep]) (by decide)
            obtain ⟨S0, Nd0, hW0, hT0⟩ := hp.stage.1.2.2.2.2
            obtain ⟨S1, Nd1, _, hW1, hog1, hfr1, hret1⟩ := hws_cal.2.2.2.2 S0 Nd0
              ((R13Shards.worldTypedWith_with_locals s cal_al (s.clock - 1) S0 Nd0).mpr hW0) (by simp [IvlsDisj])
            obtain ⟨w_snd', heq_w, hav1⟩ := hret1 (.val (.word w_snd)) rfl
            injection heq_w with heq_w'; injection heq_w' with heq_w''; subst heq_w''
            dsimp only at hav1; rw [hcn] at hav1
            change IvlsDisj [(w_snd.toNat, 24)] (worldOwned post_al S1 Nd1) at hav1
            have hT1 := PtxP1.txAccessListOK_survives_step hp.stage.1.1.1.1 hws_cal.1.1 hws_cal.2.1 hW0
              (R := []) (by simp) hog1 hfr1 hT0 (by simp) (by simp) (locals := s.locals) rfl
            have hm208 : memW post_al (locN s "tx" + 208) = memW s (locN s "tx" + 208) := by
              unfold memW; rw [hpost_al_m]; rfl
            have hm216 : memW post_al (locN s "tx" + 216) = memW s (locN s "tx" + 216) := by
              unfold memW; rw [hpost_al_m]; rfl
            have htx_s1 : s1.locals.lookup (ofString "tx") = s.locals.lookup (ofString "tx") := by
              simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
                show ofString "sender" ≠ ofString "tx" by decide]
            have hidx_s1 : s1.locals.lookup (ofString "index") = s.locals.lookup (ofString "index") := by
              simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
                show ofString "sender" ≠ ofString "index" by decide]
            have hsnd_s1 : locN s1 "sender" = w_snd.toNat := by
              simp [s1, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
            have htxN_s1 : locN s1 "tx" = locN s "tx" := locN_congr s s1.locals post_al.clock "tx" htx_s1
            have hrdy1 : TxReadyStrong s1 := PtxP1.txReadyStrong_with_locals
              { post_al with locals := s.locals } s1.locals post_al.clock htx_s1 hidx_s1 hsready.1
            have hpFresh : globN s "heap_ptr" ≤ w_snd.toNat := hw_in_al.1
            have hsndOK1 : PtxP1.SenderOK s1 := by
              unfold PtxP1.SenderOK; rw [hsnd_s1]
              exact ⟨⟨hp.base.world.1.2.1.trans hpFresh, hw_in_al.2⟩, hw_ok_al⟩
            have hW_s1 : WorldTypedWith s1 S1 Nd1 :=
              (R13Shards.worldTypedWith_with_locals post_al s1.locals post_al.clock S1 Nd1).mpr hW1
            have hT_s1 : TxAccessListOK s1 S1 Nd1 :=
              PtxP1.txAccessListOK_with_locals { post_al with locals := s.locals } s1.locals post_al.clock htx_s1 hT1
            have hOw_s1 : IvlsDisj [(locN s1 "sender", 24)] (worldOwned s1 S1 Nd1) := by
              rw [hsnd_s1]; exact hav1
            have hTx_disj1 : Disj (locN s1 "tx", 384) (locN s1 "sender", 24) := by
              rw [htxN_s1, hsnd_s1]
              exact Or.inr (Or.inr (Or.inl (hT0.1.2.1.2.trans hpFresh)))
            have hRecs_disj1 : 0 < memW s1 (locN s1 "tx" + 216) →
                Disj (memW s1 (locN s1 "tx" + 208), 24 * memW s1 (locN s1 "tx" + 216)) (locN s1 "sender", 24) := by
              rw [htxN_s1, hsnd_s1]
              change 0 < memW post_al (locN s "tx" + 216) →
                Disj (memW post_al (locN s "tx" + 208), 24 * memW post_al (locN s "tx" + 216)) (w_snd.toNat, 24)
              rw [hm208, hm216]
              intro hn
              exact Or.inr (Or.inr (Or.inl ((hT0.2.2 hn).1.2.trans hpFresh)))
            have hSA1 : PtxP1.SenderAllocated s1 :=
              ⟨hrdy1, hsndOK1, S1, Nd1, hW_s1, hT_s1,
                fun j hj => hOw_s1 _ (by simp) j (R13Shards.worldTypedIvls_sub_worldOwned hj),
                hTx_disj1, hRecs_disj1⟩
            have hSAO1 : SenderAllocatedOwned s1 :=
              ⟨hSA1, S1, Nd1, hW_s1, hT_s1, hOw_s1, hTx_disj1, hRecs_disj1⟩
            have hVR_s1 : TxValidRecoverReady s1 := by
              unfold TxValidRecoverReady
              rw [htxN_s1]
              exact txValidRecoverReadyAt_with_locals post_al s1.locals post_al.clock
                (txValidRecoverReadyAt_step_heap_unhit hp.base.world.1 hAR_al.1 hws_cal.2.1
                  (fun a _ _ => by rw [hpost_al_m]; rfl) hVR)
            have hsh_s1 : PtxLocalShapeMap (("sender", .one) :: xs) s1 :=
              ptxLocalShapeMap_add s post_al hp.shapes "sender" .one (.val (.word w_snd)) hne_xs
                (by simp [shapeOfHOLExact])
            have hexpw1 : globN s1 "bn_expw" = globN entry "bn_expw" :=
              (globN_eq_of_lookup (hws_s.2.2.1 _ (by decide))).trans hp.expw
            have hgamma1 : globN s1 "bn_gamma" = globN entry "bn_gamma" :=
              (globN_eq_of_lookup (hws_s.2.2.1 _ (by decide))).trans hp.gamma
            suffices hrec_run : PtxRelRunStrong entry
                (.seq (.call (some (none, none)) (ofString "recover_sender_with_chain_id") PtxP1.recoverArgs) tail) s1 by
              have hmid := hrec_run hres
              exact ptxWorldStep_strong_with_locals_right
                (HolFiniteMapExact.resVarEq
                  (evaluateHOLFiniteState s1
                    (.seq (.call (some (none, none)) (ofString "recover_sender_with_chain_id") PtxP1.recoverArgs) tail)).2.locals
                  (ofString "sender", s.locals.lookup (ofString "sender")))
                (evaluateHOLFiniteState s1
                  (.seq (.call (some (none, none)) (ofString "recover_sender_with_chain_id") PtxP1.recoverArgs) tail)).2.clock
                hmid
            intro hres_rc
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hres_rc ⊢
            rcases ha_rc : @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
                PtxP1.recoverArgs with _ | vs_rc
            · simp [evalListHOLFinite, ha_rc] at hres_rc
              exact absurd hres_rc (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
            · simp only [evalListHOLFinite, ha_rc] at hres_rc ⊢
              have ha_rc_fin : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
                  PtxP1.recoverArgs = some vs_rc := by simpa [evalListHOLFinite] using ha_rc
              rcases hl_rc : lookupCodeHOLFinite s1.code.lookup (ofString "recover_sender_with_chain_id") vs_rc
                  with _ | ⟨body_rc, cal_rc, ret_rc⟩
              · simp only [hl_rc] at hres_rc
                exact absurd hres_rc (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
              · simp only [hl_rc] at hres_rc ⊢
                by_cases hcz_rc : s1.clock = 0
                · simp only [hcz_rc, ↓reduceIte] at hres_rc
                  exact absurd hres_rc (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                · simp only [hcz_rc, ↓reduceIte] at hres_rc ⊢
                  obtain ⟨v1_rc, _, v3_rc, he1_rc, _, he3_rc, hp_rc, _, hr_rc⟩ :=
                    PtxP1.params_three_values s1 (ofString "recover_sender_with_chain_id")
                      (ofString "tx") (ofString "chain_id") (ofString "out20") .one .one .one _ .one
                      (by rw [hc1]; exact PtxP1.lookup_recover_sender_with_chain_id)
                      (.var .local (ofString "tx"))
                      (.load .one (.op .add [.var .global (ofString "be"), .const 0]))
                      (.var .local (ofString "sender")) vs_rc body_rc cal_rc ret_rc ha_rc_fin hl_rc
                  have htx_cal_rc : cal_rc.lookup (ofString "tx") = s1.locals.lookup (ofString "tx") :=
                    hp_rc.trans he1_rc.symm
                  have hout_rc : locN (callEntryStateHOLFinite s1 cal_rc) "out20" = locN s1 "sender" := by
                    simp only [locN, callEntryStateHOLFinite, hr_rc,
                      show s1.locals.lookup (ofString "sender") = some v3_rc from he3_rc]
                  have hVR_cal_rc : TxValidRecoverReady (callEntryStateHOLFinite s1 cal_rc) := by
                    unfold TxValidRecoverReady at hVR_s1 ⊢
                    have hloc : locN (callEntryStateHOLFinite s1 cal_rc) "tx" = locN s1 "tx" := by
                      simp [callEntryStateHOLFinite, locN, htx_cal_rc]
                    rw [hloc]
                    exact txValidRecoverReadyAt_with_locals s1 cal_rc (s1.clock - 1) hVR_s1
                  have hin20 : Inside (locN s1 "sender", 20) (locN s1 "sender") (locN s1 "sender" + 24) :=
                    ⟨le_rfl, by omega⟩
                  have hout_bo_rc : ∀ i ∈ blockOutObjects (callEntryStateHOLFinite s1 cal_rc),
                      Disj i (locN (callEntryStateHOLFinite s1 cal_rc) "out20", 20) := by
                    rw [hout_rc]
                    intro i hi
                    have hi_s1 : i ∈ blockOutObjects s1 := hi
                    have hi_ow : i ∈ worldOwned s1 S1 Nd1 :=
                      List.mem_append_left _ (List.mem_append_right _
                        (List.mem_append_left _ (List.mem_append_right _ hi_s1)))
                    exact R13Shards.disj_symm
                      (R13Shards.disj_of_inside_left hin20
                        (hOw_s1 (locN s1 "sender", 24) (by simp) i hi_ow))
                  have hB_rc : ValidBufList [("keccak_pad", 136), ("keccak_st", 200), ("u256_ws", 640)] := by
                    intro p hp0
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp0
                    rcases hp0 with rfl | rfl | rfl
                    · exact ⟨136, by decide, by decide, le_rfl⟩
                    · exact ⟨200, by decide, by decide, le_rfl⟩
                    · exact ⟨640, by decide, by decide, le_rfl⟩
                  have hBsub_rc : ∀ p ∈ ([("keccak_pad", 136), ("keccak_st", 200), ("u256_ws", 640)] : BufList),
                      p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals := by
                    intro p hp0
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp0
                    rcases hp0 with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
                  have hmeta_rc := (PanRunBounded.evaluateHOLFiniteState_metadata
                    (callEntryStateHOLFinite s1 cal_rc) body_rc).1
                  rcases hb_rc : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal_rc) body_rc
                      with ⟨rb_rc, post_rc⟩
                  have hb_rc' : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal_rc) body_rc =
                      (rb_rc, post_rc) := hb_rc
                  rw [hb_rc] at hmeta_rc
                  simp only [hb_rc] at hres_rc ⊢
                  have hrec_kept_buf : ∀ r_rc,
                      WorldStep
                        (fun _ => [(locN s1 "sender", 20), bufferRegion s1 ("keccak_pad", 136),
                          bufferRegion s1 ("keccak_st", 200), bufferRegion s1 ("u256_ws", 640)])
                        ["heap_ptr"] stdKeep
                        (fun s0 _ post0 _ _ => PtxBlockOutUnhit s0 post0)
                        s1 r_rc post_rc →
                      RecordsKept (bufRegions [("keccak_pad", 136), ("keccak_st", 200), ("u256_ws", 640)])
                        stdKeep s1 post_rc := by
                    intro r_rc hws0 rec hrec hnz off hoff hno
                    apply hws0.2.2.2.1 rec hrec hnz off hoff
                    intro i hi
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                    rcases hi with rfl | rfl | rfl | rfl
                    · intro hch
                      have hrec_sz : ∃ sz, (rec.1, sz) ∈ globalBuffers ∧ off + 8 ≤ sz ∧ 0 < sz := by
                        simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
                        rcases hrec with rfl | rfl | rfl | rfl
                        · refine ⟨40, by decide, ?_, by decide⟩; simp at hoff; omega
                        · refine ⟨80, by decide, ?_, by decide⟩; simp at hoff; omega
                        · refine ⟨72, by decide, ?_, by decide⟩; simp at hoff; omega
                        · refine ⟨88, by decide, ?_, by decide⟩; simp at hoff; omega
                      obtain ⟨sz, hgb, hoff_sz, hsz_pos⟩ := hrec_sz
                      have hrec_fix : (globN s1 rec.1, sz) ∈ fixedObjects s1 := by
                        unfold fixedObjects
                        apply List.mem_append_left
                        apply List.mem_append_left
                        apply List.mem_append_left
                        exact List.mem_map.2 ⟨(rec.1, sz), hgb, by simp [hnz]⟩
                      have hrec_ow : (globN s1 rec.1, sz) ∈ worldOwned s1 S1 Nd1 :=
                        List.mem_append_left _ (List.mem_append_right _ hrec_fix)
                      have hd_rec := hOw_s1 (locN s1 "sender", 24) (by simp) _ hrec_ow
                      rcases hd_rec with h0 | h0 | hd1 | hd2
                      · simp at h0
                      · dsimp only at h0; omega
                      · dsimp only [CellHits] at hd1 hch; omega
                      · dsimp only [CellHits] at hd2 hch; omega
                    · exact hno _ (by simp [bufRegions])
                    · exact hno _ (by simp [bufRegions])
                    · exact hno _ (by simp [bufRegions])
                  have hstep_entry_rc : ∀ r_rc,
                      WorldStep
                        (fun _ => [(locN s1 "sender", 20), bufferRegion s1 ("keccak_pad", 136),
                          bufferRegion s1 ("keccak_st", 200), bufferRegion s1 ("u256_ws", 640)])
                        ["heap_ptr"] stdKeep
                        (fun s0 _ post0 _ _ => PtxBlockOutUnhit s0 post0)
                        s1 r_rc post_rc →
                      WorldStep ptxRegions ptxGlobals ptxKeep NoExtra entry r_rc post_rc := by
                    intro r_rc hws0
                    have hRsub := ptxBufs_sub_entry hbase1.globals hBsub_rc
                    refine ⟨hws0.1, le_trans hbase1.heap_entry hws0.2.1, ?_, ?_, ?_⟩
                    · intro k hk
                      have hkg : k ∉ (["heap_ptr"] : List String).map ofString := by
                        intro hm
                        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
                        simp at hg; subst hg
                        exact hk (by decide)
                      exact (hbase1.globals k hk).trans (hws0.2.2.1 k hkg)
                    · intro rec hr hn off hoff hno
                      obtain ⟨offs, hkr, hko⟩ := ptxKeepSub_stdKeep rec hr
                      have heq : globN s1 rec.1 = globN entry rec.1 := by
                        have hni : ofString rec.1 ∉ ptxGlobals.map ofString := by
                          simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
                          rcases hr with rfl | rfl | rfl | rfl
                          · decide
                          · decide
                          · simp at hoff
                          · decide
                        exact globN_eq_of_lookup (hbase1.globals (ofString rec.1) hni)
                      have hks := hrec_kept_buf r_rc hws0 (rec.1, offs) hkr (by simpa only [heq] using hn)
                        off (hko off hoff) (by intro i hi; simpa only [heq] using hno i (hRsub i hi))
                      rw [heq] at hks
                      exact hks.trans (hbase1.records rec hr hn off hoff hno)
                    · intro S_e0 Nd_e0 hWT_e0 hD_e0
                      obtain ⟨Sc, Nc, hsub_c, hWT_sc, hOG_c, hFO_c⟩ := hp.base.typing S_e0 Nd_e0 hWT_e0 hD_e0
                      obtain ⟨Sc', Nc', hsub_al, hWT_al_c, hOG_al_c, hFO_al_c, hdj_snd_c⟩ := hal_typed Sc Nc hWT_sc
                      have hWT_s1_c : WorldTypedWith s1 Sc' Nc' :=
                        (R13Shards.worldTypedWith_with_locals post_al s1.locals post_al.clock Sc' Nc').mpr hWT_al_c
                      have hOG_e_s1 : OwnedGrows entry s1 (worldOwned entry S_e0 Nd_e0) (worldOwned s1 Sc' Nc') :=
                        ptx_ownedGrows_trans hp.base.heap_entry hws_s.2.1 hOG_c hOG_al_c
                      have hFO_e_s1 : FrameOutside entry s1
                          (worldOwned entry S_e0 Nd_e0 ++ ptxRegions entry ++ [freeGap entry]) (heapFree entry) :=
                        ptx_frameOutside_trans hp.base.arena_entry hp.base.world.1 hp.base.heap_entry
                          hp.base.frame_entry hp.base.scratch_entry hOG_c (fun _ hi => by cases hi) hFO_c hFO_al_c
                      have hDc' : IvlsDisj
                          [(locN s1 "sender", 20), bufferRegion s1 ("keccak_pad", 136),
                            bufferRegion s1 ("keccak_st", 200), bufferRegion s1 ("u256_ws", 640)]
                          (worldTypedIvls s1 Sc' Nc') := by
                        intro i hi j hj
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                        rcases hi with rfl | rfl | rfl | rfl
                        · have hdj24 : Disj (locN s1 "sender", 24) j := by
                            rw [hsnd_s1]
                            exact hdj_snd_c (w_snd.toNat, 24) (by simp) j (R13Shards.worldTypedIvls_sub_worldOwned hj)
                          exact R13Shards.disj_of_inside_left hin20 hdj24
                        · exact validBufList_disj hB_rc hWT_s1_c _ (by simp [bufRegions]) j hj
                        · exact validBufList_disj hB_rc hWT_s1_c _ (by simp [bufRegions]) j hj
                        · exact validBufList_disj hB_rc hWT_s1_c _ (by simp [bufRegions]) j hj
                      obtain ⟨Sn, Nn, hsubn, hWTn, hOGn, hFOn, _⟩ := hws0.2.2.2.2 Sc' Nc' hWT_s1_c hDc'
                      have hhp_s1_eq : globN s1 "heap_ptr" = globN post_al "heap_ptr" := rfl
                      have hin_snd_e : Inside (locN s1 "sender", 20) (globN entry "heap_ptr") (globN s1 "heap_ptr") := by
                        rw [hsnd_s1, hhp_s1_eq]
                        exact ⟨le_trans hp.base.heap_entry hw_in_al.1, by dsimp [Inside] at hw_in_al ⊢; omega⟩
                      have hR_msg : ∀ i ∈ [(locN s1 "sender", 20), bufferRegion s1 ("keccak_pad", 136),
                          bufferRegion s1 ("keccak_st", 200), bufferRegion s1 ("u256_ws", 640)],
                          i = (locN s1 "sender", 20) ∨ i ∈ ptxRegions entry := by
                        intro i hi
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                        rcases hi with rfl | rfl | rfl | rfl
                        · exact Or.inl rfl
                        · exact Or.inr (hRsub _ (by simp [bufRegions]))
                        · exact Or.inr (hRsub _ (by simp [bufRegions]))
                        · exact Or.inr (hRsub _ (by simp [bufRegions]))
                      refine ⟨Sn, Nn, fun t ht => hsubn t (hsub_al t (hsub_c t ht)), hWTn,
                        ptx_ownedGrows_trans hbase1.heap_entry hws0.2.1 hOG_e_s1 hOGn, ?_, trivial⟩
                      exact ptx_frameOutside_trans_msg hbase1.arena_entry hbase1.world.1
                        hbase1.heap_entry hbase1.frame_entry hbase1.scratch_entry
                        hOG_e_s1 hin_snd_e hR_msg hFO_e_s1 hFOn
                  have hRT_rc : IvlsDisj
                      [(locN s1 "sender", 20), bufferRegion s1 ("keccak_pad", 136),
                        bufferRegion s1 ("keccak_st", 200), bufferRegion s1 ("u256_ws", 640)]
                      (worldTypedIvls s1 S1 Nd1) := by
                    intro i hi j hj
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                    rcases hi with rfl | rfl | rfl | rfl
                    · exact R13Shards.disj_of_inside_left hin20
                        (hOw_s1 (locN s1 "sender", 24) (by simp) j (R13Shards.worldTypedIvls_sub_worldOwned hj))
                    · exact bufferRegion_disj_le hW_s1 ("keccak_pad", 136) (by decide) (by decide) 136 le_rfl j hj
                    · exact bufferRegion_disj_le hW_s1 ("keccak_st", 200) (by decide) (by decide) 200 le_rfl j hj
                    · exact bufferRegion_disj_le hW_s1 ("u256_ws", 640) (by decide) (by decide) 640 le_rfl j hj
                  cases rb_rc with
                  | none => exact absurd hres_rc (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                  | some cr_rc =>
                    cases cr_rc with
                    | timeOut | error | «break» | «continue» | finalFfi _ =>
                      exact absurd hres_rc (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                    | exception eid ev =>
                      dsimp only at hres_rc ⊢
                      have hspec_rc := FunSpec.at_lookup «wk_recover_sender_with_chain_id_bo» s1 hc1
                        vs_rc body_rc cal_rc ret_rc hl_rc
                        ⟨localsFree_worldOK s1 cal_rc (s1.clock - 1) hbase1.world, hVR_cal_rc, hout_bo_rc⟩
                        (by rw [hb_rc']; simp)
                      rw [hb_rc'] at hspec_rc
                      have hstep_rc_e := hspec_rc hres_rc
                      have hs_rc0 : WorldStep
                          (fun _ => [(locN (callEntryStateHOLFinite s1 cal_rc) "out20", 20),
                            bufferRegion s1 ("keccak_pad", 136), bufferRegion s1 ("keccak_st", 200),
                            bufferRegion s1 ("u256_ws", 640)])
                          ["heap_ptr"] stdKeep
                          (fun s0 _ post0 _ _ => PtxBlockOutUnhit s0 post0)
                          s1 (some (.exception eid ev)) post_rc :=
                        ⟨hstep_rc_e.1, hstep_rc_e.2.1, hstep_rc_e.2.2.1, hstep_rc_e.2.2.2.1,
                          fun Sx Ndx hWx hDx =>
                            hstep_rc_e.2.2.2.2 Sx Ndx
                              ((R13Shards.worldTypedWith_with_locals s1 cal_rc (s1.clock - 1) Sx Ndx).2 hWx) hDx⟩
                      rw [hout_rc] at hs_rc0
                      have hb_ex := hstep_entry_rc _ hs_rc0
                      have hex_rc : WorldStep ptxRegions ptxGlobals ptxKeep PtxLogsAndSlices
                          entry (some (.exception eid ev)) post_rc := by
                        refine ⟨hb_ex.1, hb_ex.2.1, hb_ex.2.2.1, hb_ex.2.2.2.1, ?_⟩
                        intro S0x Nd0x hWT0x hD0x
                        obtain ⟨Sn, Nn, hsubn, hWTn, hOGn, hFOn, _⟩ := hb_ex.2.2.2.2 S0x Nd0x hWT0x hD0x
                        exact ⟨Sn, Nn, hsubn, hWTn, hOGn, hFOn,
                          (by intro val hv; cases hv), (by intro val hv; cases hv)⟩
                      exact ptxWorldStep_strong_with_locals_right .empty post_rc.clock hex_rc
                    | returned v_rc =>
                      dsimp only at hres_rc ⊢
                      by_cases hsh_rc : shapeEqHOL (shapeOfHOLExact v_rc) ret_rc = true
                      · simp only [hsh_rc, ↓reduceIte] at hres_rc ⊢
                        have hspec_rc := FunSpec.at_lookup «wk_recover_sender_with_chain_id_bo» s1 hc1
                          vs_rc body_rc cal_rc ret_rc hl_rc
                          ⟨localsFree_worldOK s1 cal_rc (s1.clock - 1) hbase1.world, hVR_cal_rc, hout_bo_rc⟩
                          (by rw [hb_rc']; simp)
                        rw [hb_rc'] at hspec_rc
                        have hstep_rc_cal := hspec_rc (Or.inl ⟨v_rc, rfl⟩)
                        have hs_rc0 : WorldStep
                            (fun _ => [(locN (callEntryStateHOLFinite s1 cal_rc) "out20", 20),
                              bufferRegion s1 ("keccak_pad", 136), bufferRegion s1 ("keccak_st", 200),
                              bufferRegion s1 ("u256_ws", 640)])
                            ["heap_ptr"] stdKeep
                            (fun s0 _ post0 _ _ => PtxBlockOutUnhit s0 post0)
                            s1 (some (.returned v_rc)) post_rc :=
                          ⟨hstep_rc_cal.1, hstep_rc_cal.2.1, hstep_rc_cal.2.2.1, hstep_rc_cal.2.2.2.1,
                            fun Sx Ndx hWx hDx =>
                              hstep_rc_cal.2.2.2.2 Sx Ndx
                                ((R13Shards.worldTypedWith_with_locals s1 cal_rc (s1.clock - 1) Sx Ndx).2 hWx) hDx⟩
                        rw [hout_rc] at hs_rc0
                        have hs_rc_no : WorldStep
                            (fun _ => [(locN s1 "sender", 20), bufferRegion s1 ("keccak_pad", 136),
                              bufferRegion s1 ("keccak_st", 200), bufferRegion s1 ("u256_ws", 640)])
                            ["heap_ptr"] stdKeep NoExtra s1 (some (.returned v_rc)) post_rc :=
                          ⟨hs_rc0.1, hs_rc0.2.1, hs_rc0.2.2.1, hs_rc0.2.2.2.1, fun Sx Ndx hWx hDx => by
                            obtain ⟨Sy, Ndy, h1, h2, h3, h4, _⟩ := hs_rc0.2.2.2.2 Sx Ndx hWx hDx
                            exact ⟨Sy, Ndy, h1, h2, h3, h4, trivial⟩⟩
                        have hws_entry_rc := hstep_entry_rc _ hs_rc0
                        obtain ⟨S_wp, Nd_wp, _, hWT_wp, _, _, hbo_u_rc⟩ :=
                          hs_rc0.2.2.2.2 S1 Nd1 hW_s1 hRT_rc
                        have hworld_post_rc : WorldOK post_rc :=
                          ⟨hs_rc0.1, S_wp, (worldTyped_iff_with post_rc S_wp).2 ⟨Nd_wp, hWT_wp⟩⟩
                        have hsp_rc : globN post_rc "scratch_ptr" = globN s1 "scratch_ptr" :=
                          globN_eq_of_lookup (hs_rc0.2.2.1 _ (by decide))
                        have hfmp_rc : globN post_rc "frame_mem_ptr" = globN s1 "frame_mem_ptr" :=
                          globN_eq_of_lookup (hs_rc0.2.2.1 _ (by decide))
                        have hbase_post_rc : PtxRelBase true entry post_rc := by
                          have hbo_eq : globN post_rc "bo" = globN s1 "bo" :=
                            globN_eq_of_lookup (hs_rc0.2.2.1 _ (by decide))
                          have hbo_s1_entry : globN s1 "bo" = globN entry "bo" :=
                            globN_eq_of_lookup (hbase1.globals (ofString "bo") (by decide))
                          obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, _, hbo40_nz_e, hbo72_nz_e, S_e, Nd_e, hWT_e, _⟩ :=
                            hbase1.ready_entry
                          have hbo_nz_s1 : globN s1 "bo" ≠ 0 := by rw [hbo_s1_entry]; exact hbo_nz_e
                          have hrec_buf := hrec_kept_buf _ hs_rc0
                          have hbo_field_s1 : ∀ off ∈ ([24, 32, 40, 72, 80] : List Nat),
                              off % 8 = 0 → off + 8 ≤ 88 → memW post_rc (globN s1 "bo" + off) = memW s1 (globN s1 "bo" + off) := by
                            intro off hoff hoff8 hlt
                            exact ptx_bo_field_eq_of_step hB_rc hW_s1 hrec_buf
                              (by simp [stdKeep] : ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) ∈ stdKeep) hbo_nz_s1
                              (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff ⊢;
                                  rcases hoff with rfl | rfl | rfl | rfl | rfl <;> simp) hoff8 hlt
                          have hbo24_s1 : memW s1 (globN s1 "bo" + 24) = memW entry (globN entry "bo" + 24) :=
                            ptx_entry_bo_field_eq hWT_e hbase1.globals hbase1.records hbo_nz_e (by simp) (by omega)
                          have hbo32_s1 : memW s1 (globN s1 "bo" + 32) = memW entry (globN entry "bo" + 32) :=
                            ptx_entry_bo_field_eq hWT_e hbase1.globals hbase1.records hbo_nz_e (by simp) (by omega)
                          have hbo40_s1 : memW s1 (globN s1 "bo" + 40) = memW entry (globN entry "bo" + 40) :=
                            ptx_entry_bo_field_eq hWT_e hbase1.globals hbase1.records hbo_nz_e (by simp) (by omega)
                          have hbo72_s1 : memW s1 (globN s1 "bo" + 72) = memW entry (globN entry "bo" + 72) :=
                            ptx_entry_bo_field_eq hWT_e hbase1.globals hbase1.records hbo_nz_e (by simp) (by omega)
                          have hbo80_s1 : memW s1 (globN s1 "bo" + 80) = memW entry (globN entry "bo" + 80) :=
                            ptx_entry_bo_field_eq hWT_e hbase1.globals hbase1.records hbo_nz_e (by simp) (by omega)
                          have hbo40_nz_s1 : memW s1 (globN s1 "bo" + 40) ≠ 0 := by rw [hbo40_s1]; exact hbo40_nz_e
                          have hbo72_nz_s1 : memW s1 (globN s1 "bo" + 72) ≠ 0 := by rw [hbo72_s1]; exact hbo72_nz_e
                          have hbo40_post : memW post_rc (globN post_rc "bo" + 40) = memW s1 (globN s1 "bo" + 40) := by
                            rw [hbo_eq]; exact hbo_field_s1 40 (by simp) (by decide) (by omega)
                          have hbo72_post : memW post_rc (globN post_rc "bo" + 72) = memW s1 (globN s1 "bo" + 72) := by
                            rw [hbo_eq]; exact hbo_field_s1 72 (by simp) (by decide) (by omega)
                          have hlog_hdr0 : memW post_rc (memW post_rc (globN post_rc "bo" + 40)) =
                              memW s1 (memW s1 (globN s1 "bo" + 40)) := by
                            rw [hbo40_post]
                            have hm : (memW s1 (globN s1 "bo" + 40), 24) ∈ blockOutObjects s1 := by
                              simp [blockOutObjects, hbo_nz_s1, hbo40_nz_s1]
                            simpa using memW_eq_of_ptxBlockOutUnhit hbase1.world.1 hW_s1 hbo_u_rc hm (off := 0) (by decide) (by decide)
                          have hrcpt_hdr0 : memW post_rc (memW post_rc (globN post_rc "bo" + 72)) =
                              memW s1 (memW s1 (globN s1 "bo" + 72)) := by
                            rw [hbo72_post]
                            simpa using ptx_receipt_header_eq_of_blockOutUnhit hbase1.world.1 hW_s1 hbo_u_rc hbo_nz_s1 hbo72_nz_s1 (off := 0) (by simp)
                          have hrcpt_hdr8 : memW post_rc (memW post_rc (globN post_rc "bo" + 72) + 8) =
                              memW s1 (memW s1 (globN s1 "bo" + 72) + 8) := by
                            rw [hbo72_post]
                            exact ptx_receipt_header_eq_of_blockOutUnhit hbase1.world.1 hW_s1 hbo_u_rc hbo_nz_s1 hbo72_nz_s1 (by simp)
                          have hsl_eq : ∀ off ∈ ([24, 32] : List Nat), ∀ k, k ≤ locN entry "index" →
                              memW post_rc (memW post_rc (globN post_rc "bo" + off) + 16 * k + 8) =
                                memW s1 (memW s1 (globN s1 "bo" + off) + 16 * k + 8) := by
                            intro off hoff k hk
                            have hoff_in : off ∈ ([24, 32, 40, 72, 80] : List Nat) := by
                              simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
                              rcases hoff with rfl | rfl <;> simp
                            have hbo_off_eq : memW post_rc (globN post_rc "bo" + off) = memW s1 (globN s1 "bo" + off) := by
                              rw [hbo_eq]
                              apply hbo_field_s1 off hoff_in
                              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
                                rcases hoff with rfl | rfl <;> decide
                              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
                                rcases hoff with rfl | rfl <;> omega
                            rw [hbo_off_eq]
                            have hp_nz : memW s1 (globN s1 "bo" + off) ≠ 0 := by
                              simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
                              rcases hoff with rfl | rfl
                              · rw [hbo24_s1]; exact hbo24_nz_e
                              · rw [hbo32_s1]; exact hbo32_nz_e
                            apply ptx_slice_length_eq_of_blockOutUnhit hbase1.world.1 hW_s1 hbo_u_rc hbo_nz_s1 hoff hp_nz
                            rw [hbo80_s1]; omega
                          refine ⟨hbase1.ready_entry, hbase1.arena_entry,
                            by have := hbase1.frame_entry; omega,
                            by have := hbase1.scratch_entry; omega,
                            hworld_post_rc, hws_entry_rc.2.1, hws_entry_rc.2.2.1, hws_entry_rc.2.2.2.1,
                            by rw [hrcpt_hdr0]; exact hbase1.rcpt_backing,
                            by rw [hlog_hdr0]; exact hbase1.log_backing,
                            hrcpt_hdr8.trans hbase1.rcpt_len_eq,
                            fun off hoff k hk => (hsl_eq off hoff k (Nat.le_of_lt hk)).trans (hbase1.slices_prev off hoff k hk),
                            fun ht => by rw [hsl_eq 24 (by simp) (locN entry "index") le_rfl]; exact hbase1.tx_slice_cur ht,
                            ?_⟩
                          intro S0x Nd0x hWT0x hD0x
                          obtain ⟨Sn, Nn, hsubn, hWn, hOGn, hFOn, _⟩ := hws_entry_rc.2.2.2.2 S0x Nd0x hWT0x hD0x
                          exact ⟨Sn, Nn, hsubn, hWn, hOGn, hFOn⟩
                        set s2 : PanSemStateFiniteExact 64 F := { post_rc with locals := s1.locals }
                        have hbase2 : PtxRelBase true entry s2 :=
                          ptxRelBase_with_locals hbase_post_rc s1.locals post_rc.clock
                        have hown2 : SenderTxOwned s2 := senderTxOwned_after_recover hSAO1 hs_rc_no
                        have hR0_rc : ∀ i ∈ [(locN s1 "sender", 20), bufferRegion s1 ("keccak_pad", 136),
                            bufferRegion s1 ("keccak_st", 200), bufferRegion s1 ("u256_ws", 640)],
                            i.2 = 0 → i.1 % 8 = 0 := by
                          intro i hi
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                          rcases hi with rfl | rfl | rfl | rfl
                          · simp
                          · exact PtxP1.bufferRegion_zero_aligned s1 "keccak_pad" 136 (by decide)
                          · exact PtxP1.bufferRegion_zero_aligned s1 "keccak_st" 200 (by decide)
                          · exact PtxP1.bufferRegion_zero_aligned s1 "u256_ws" 640 (by decide)
                        have hReady2 : TxReadyStrong s2 := by
                          apply PtxP1.txReadyStrong_worldStep hs_rc_no hbase1.world.1
                            (PtxP1.txEnv_of_ready hrdy1) hW_s1 hT_s1
                            (by decide) (by decide)
                            (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp [stdKeep]) (by decide)
                            hR0_rc hRT_rc
                          · intro i hi
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                            rcases hi with rfl | rfl | rfl | rfl
                            · exact R13Shards.disj_of_inside_right hin20 hTx_disj1
                            · exact PtxP1.heap_ivl_disj_bufferRegion_le (fun j hj => hT_s1.2.1 _ (by simp) j hj) ("keccak_pad", 136) (by decide) 136 le_rfl
                            · exact PtxP1.heap_ivl_disj_bufferRegion_le (fun j hj => hT_s1.2.1 _ (by simp) j hj) ("keccak_st", 200) (by decide) 200 le_rfl
                            · exact PtxP1.heap_ivl_disj_bufferRegion_le (fun j hj => hT_s1.2.1 _ (by simp) j hj) ("u256_ws", 640) (by decide) 640 le_rfl
                          · intro hn i hi
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                            rcases hi with rfl | rfl | rfl | rfl
                            · exact R13Shards.disj_of_inside_right hin20 (hRecs_disj1 hn)
                            · exact PtxP1.heap_ivl_disj_bufferRegion_le (fun j hj => (hT_s1.2.2 hn).2 _ (by simp) j hj) ("keccak_pad", 136) (by decide) 136 le_rfl
                            · exact PtxP1.heap_ivl_disj_bufferRegion_le (fun j hj => (hT_s1.2.2 hn).2 _ (by simp) j hj) ("keccak_st", 200) (by decide) 200 le_rfl
                            · exact PtxP1.heap_ivl_disj_bufferRegion_le (fun j hj => (hT_s1.2.2 hn).2 _ (by simp) j hj) ("u256_ws", 640) (by decide) 640 le_rfl
                        have hSender2 := PtxP1.senderOK_grows hbase1.world.1.1 hReady2.1.1.1.1 hs_rc_no.2.1 rfl hsndOK1
                        have hst2 : PtxP1.StageP 1 s2 := ⟨hReady2, fun _ => hSender2, by omega, by omega, by omega⟩
                        have hexpw2 : globN s2 "bn_expw" = globN entry "bn_expw" :=
                          (globN_eq_of_lookup (hs_rc0.2.2.1 _ (by decide))).trans hexpw1
                        have hgamma2 : globN s2 "bn_gamma" = globN entry "bn_gamma" :=
                          (globN_eq_of_lookup (hs_rc0.2.2.1 _ (by decide))).trans hgamma1
                        have hp2 : P1State true 1 (("sender", .one) :: xs) true entry s2 :=
                          ⟨hbase2, hst2,
                            phase1_map_localsOnly _ s1 s1.locals post_rc.clock (fun _ _ => rfl) hsh_s1,
                            hexpw2, hgamma2, htx_s1.trans hp.tx_eq, hidx_s1.trans hp.idx_eq, fun _ => hown2⟩
                        exact htail s2 (hmeta_rc.trans hc1) hp2 hres_rc
                      · simp only [hsh_rc, Bool.false_eq_true, ↓reduceIte] at hres_rc
                        exact absurd hres_rc (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          · simp only [hsh_al, Bool.false_eq_true, ↓reduceIte] at hres
            exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

/-! ## 2. Stage Upgrades (`StageP 1 -> 2 -> 3 -> 4`) -/

theorem p1_validate_tx {F : Type} {xs : List (String × ShapeHOL)}
    {entry s : PanSemStateFiniteExact 64 F} {tail : ProgHOL 64}
    (hc : s.code = originalRuntimeCode)
    (hp : P1State true 1 xs true entry s)
    (hne_xs : ∀ x ∈ xs, ofString x.1 ≠ ofString "intrinsic")
    (htail : ∀ s1 : PanSemStateFiniteExact 64 F,
      s1.code = originalRuntimeCode →
      P1State true 2 (("intrinsic", .comb [.one, .one, .one]) :: xs) true entry s1 →
      PtxRelRunStrong entry tail s1) :
    PtxRelRunStrong entry
      (.decCall (ofString "intrinsic") (.comb [.one, .one, .one]) (ofString "validate_transaction")
        [.var .local (ofString "tx"), .var .local (ofString "sender")] tail) s := by
  refine p1_decCall_ro_add hc "intrinsic" (.comb [.one, .one, .one]) (ofString "validate_transaction")
    [.var .local (ofString "tx"), .var .local (ofString "sender")] tail ptx_ro_validate_tx hp
    (by decide) hne_xs (by decide) (by decide) (by decide)
    (fun vs body callee ret v post _ hl hb _ hp1 hc1 => ?_)
  have hs := FunSpec.at_lookup ptx_rv_validate_tx s hc vs body callee ret hl
    (guestInv_callEntry s callee hp.base.world.1.1) (by rw [hb]; simp)
  rw [hb] at hs
  obtain ⟨a, b, c, rfl, hle⟩ := hs v rfl
  have hst2 : PtxP1.StageP 2 (setVarHOLFinite (ofString "intrinsic")
      (.rStruct [.val (.word a), .val (.word b), .val (.word c)]) { post with locals := s.locals }) :=
    ⟨hp1.stage.1, fun _ => hp1.stage.2.1 (by omega),
      fun _ => ⟨a, b, c, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE], hle⟩,
      by omega, by omega⟩
  exact htail _ hc1 ⟨hp1.base, hst2, hp1.shapes, hp1.expw, hp1.gamma, hp1.tx_eq, hp1.idx_eq, hp1.snd_own⟩

theorem p1_regular_budget {F : Type} {xs : List (String × ShapeHOL)}
    {entry s : PanSemStateFiniteExact 64 F} {tail : ProgHOL 64}
    (hc : s.code = originalRuntimeCode)
    (hp : P1State true 2 xs true entry s)
    (hne_xs : ∀ x ∈ xs, ofString x.1 ≠ ofString "regular_budget")
    (htail : ∀ s1 : PanSemStateFiniteExact 64 F,
      s1.code = originalRuntimeCode →
      P1State true 3 xs true entry s1 →
      PtxRelRunStrong entry tail s1) :
    PtxRelRunStrong entry (.dec (ofString "regular_budget") .one PtxP1.regularBudgetExp tail) s := by
  refine p1_dec_keep "regular_budget" .one PtxP1.regularBudgetExp tail hp
    (by decide) hne_xs (by decide) (by decide) (by decide)
    (fun v hev _ hp1 => ?_)
  have hst3 := PtxP1.declare_regular_budget s v hp.stage hev
  exact htail _ hc ⟨hp1.base, hst3, hp1.shapes, hp1.expw, hp1.gamma, hp1.tx_eq, hp1.idx_eq, hp1.snd_own⟩

theorem p1_min_mgas {F : Type} {xs : List (String × ShapeHOL)}
    {entry s : PanSemStateFiniteExact 64 F} {tail : ProgHOL 64}
    (hc : s.code = originalRuntimeCode)
    (hp : P1State true 3 xs true entry s)
    (hne_xs : ∀ x ∈ xs, ofString x.1 ≠ ofString "mgas")
    (htail : ∀ s1 : PanSemStateFiniteExact 64 F,
      s1.code = originalRuntimeCode →
      P1State true 4 (("mgas", .one) :: xs) true entry s1 →
      PtxRelRunStrong entry tail s1) :
    PtxRelRunStrong entry
      (.decCall (ofString "mgas") .one (ofString "min")
        [.var .local (ofString "regular_budget"), .var .local (ofString "execution_gas")] tail) s := by
  refine p1_decCall_ro_add hc "mgas" .one (ofString "min")
    [.var .local (ofString "regular_budget"), .var .local (ofString "execution_gas")]
    tail ptx_ro_min hp (by decide) hne_xs (by decide) (by decide) (by decide)
    (fun vs body callee ret v post ha hl hb _ hp1 hc1 => ?_)
  obtain ⟨v1, _, he1, _, hpa, _⟩ := PtxP1.params_two_values s (ofString "min") (ofString "a") (ofString "b")
    .one .one _ .one (by rw [hc]; exact PtxP1.lookup_min)
    (.var .local (ofString "regular_budget")) (.var .local (ofString "execution_gas")) vs body callee ret ha hl
  have hca : locN (callEntryStateHOLFinite s callee) "a" = locN s "regular_budget" := by
    simp only [locN, callEntryStateHOLFinite, hpa,
      show s.locals.lookup (ofString "regular_budget") = some v1 from he1]
  have hs := FunSpec.at_lookup ptx_rv_min s hc vs body callee ret hl
    (guestInv_callEntry s callee hp.base.world.1.1) (by rw [hb]; simp)
  rw [hb] at hs
  obtain ⟨w, rfl, hle⟩ := hs v rfl
  have hst4 : PtxP1.StageP 4 (setVarHOLFinite (ofString "mgas") (.val (.word w)) { post with locals := s.locals }) := by
    refine ⟨hp1.stage.1, fun _ => hp1.stage.2.1 (by omega), fun _ => hp1.stage.2.2.1 (by omega),
      fun _ => hp1.stage.2.2.2.1 (by omega), ?_⟩
    intro _
    rw [locN_setVar_same]
    change w.toNat ≤ locN (callEntryStateHOLFinite s callee) "a" at hle
    rw [hca] at hle
    exact hle.trans (hp.stage.2.2.2.1 (by omega))
  exact htail _ hc1 ⟨hp1.base, hst4, hp1.shapes, hp1.expw, hp1.gamma, hp1.tx_eq, hp1.idx_eq, hp1.snd_own⟩

theorem p1_tx_chain_id {F : Type} {xs : List (String × ShapeHOL)}
    {entry s : PanSemStateFiniteExact 64 F} {tail : ProgHOL 64}
    (hc : s.code = originalRuntimeCode)
    (hp : P1State true 0 xs false entry s)
    (hne_xs : ∀ x ∈ xs, ofString x.1 ≠ ofString "cid")
    (hVR : TxValidRecoverReady s)
    (htail : ∀ s1 : PanSemStateFiniteExact 64 F,
      s1.code = originalRuntimeCode →
      P1State true 0 xs false entry s1 →
      TxValidRecoverReady s1 →
      PtxRelRunStrong entry tail s1) :
    PtxRelRunStrong entry
      (.decCall (ofString "cid") (.comb [.one, .one]) (ofString "tx_chain_id")
        [.var .local (ofString "tx")] tail) s := by
  refine ptxRelRunStrong_decCall_ro hp.base hc (ofString "cid") (.comb [.one, .one])
    (ofString "tx_chain_id") [.var .local (ofString "tx")] tail ptx_ro_chain_id
    (fun _ _ _ _ v post _ _ _ _ hro_eq => ?_)
  have hpost_eq : ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F) =
      { s with locals := s.locals, clock := post.clock } := by rw [hro_eq]; rfl
  set s1 := setVarHOLFinite (ofString "cid") v { post with locals := s.locals }
  have hp0 : P1State true 0 xs false entry { post with locals := s.locals } := by
    rw [hpost_eq]
    exact p1State_with_locals hp s.locals post.clock
      (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl (fun _ => rfl)
  have hp1 : P1State true 0 xs false entry s1 :=
    ⟨ptxRelBase_with_locals hp0.base (s.locals.update (ofString "cid", v)) post.clock,
      LocalsOnly.setVar (PtxP1.localsOnly_stage 0) (by decide) v _ hp0.stage,
      ptxLocalShapeMap_resume s post hp.shapes "cid" v hne_xs,
      hp0.expw, hp0.gamma,
      by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
          show ofString "cid" ≠ ofString "tx" by decide, hp.tx_eq],
      by simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
          show ofString "cid" ≠ ofString "index" by decide, hp.idx_eq],
      fun hh => Bool.noConfusion hh⟩
  have hc1 : s1.code = originalRuntimeCode := by change post.code = _; rw [hro_eq]; exact hc
  have hVR1 : TxValidRecoverReady s1 := by
    unfold TxValidRecoverReady
    have htxN : locN s1 "tx" = locN s "tx" := by
      simp [s1, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "cid" ≠ ofString "tx" by decide]
    rw [htxN]
    have hs1_eq : s1 = { s with locals := s1.locals, clock := post.clock } := by
      change setVarHOLFinite (ofString "cid") v { post with locals := s.locals } = _
      rw [hro_eq]; rfl
    rw [hs1_eq]
    exact txValidRecoverReadyAt_with_locals s s1.locals post.clock hVR
  exact htail s1 hc1 hp1 hVR1

/-! ## 3. Full `ptxPhase1_relCut_strong` Assembly -/

theorem ptxPhase1_relCut_strong :
    PtxRelCutStrong R13Shards.ptxPhase1 PtxEntryFull PtxAfterPhase1 := by
  intro F entry tail htail s hc hef
  unfold R13Shards.ptxPhase1 ptxCode
  simp only [sourceFunctionEntry, Guest.Software.guestFn_process_transaction,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil, spinePlug]
  refine p1_prefix_state_fresh_tx hc hef (fun s1 hc1 hp1 hVE1 hVR1 => ?_)
  refine p1_prefix_assign_bal_index hc1 hp1 hVE1 hVR1 (fun s2 hc2 hp2 hVE2 hVR2 => ?_)
  refine p1_prefix_encode_transaction hc2 hp2 hVE2 hVR2 (fun s3 a b hc3 hp3 henc3 hb_lt3 hVR3 => ?_)
  refine p1_prefix_store_encSlots hc3 hp3 henc3 hb_lt3 hVR3 (fun s4 hc4 hp4 hVR4 => ?_)
  refine p1_skip hp4 (fun hp4' => ?_)
  refine p1_tx_chain_id hc4 hp4' (by decide) hVR4 (fun s5 hc5 hp5 hVR5 => ?_)
  refine p1_chainGuard hc5 hp5 (fun hp5' hc5' => ?_)
  refine p1_prefix_alloc_recover hc5' hp5' (by decide) hVR5 (fun s6 hc6 hp6 => ?_)
  refine p1_skip hp6 (fun hp6' => ?_)
  refine p1_validate_tx hc6 hp6' (by decide) (fun s7 hc7 hp7 => ?_)
  refine p1_skip hp7 (fun hp7' => ?_)
  refine p1_dec_keep "intrinsic_gas" .one _ _ hp7'
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun v_ig _ _ hp8 => ?_)
  have hc8 : (setVarHOLFinite (ofString "intrinsic_gas") v_ig s7).code = originalRuntimeCode := hc7
  refine p1_decCall_scBo_add hc8 hp8 (by decide)
    validBufList_checkTxBufs
    (by intro p hp0; simp [checkTxBufs] at hp0; rcases hp0 with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
    (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    ptxKeepSub_stdKeep (Or.inr (by simp [stdKeep]))
    (gs := [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64), ("sk_buf", 64, 52), ("u256_ws", 640, 640)])
    (by unfold PtxP1.ScratchSpec; decide) (fun _ => rfl)
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp [stdKeep]) (by decide)
    "price" (.comb [.one, .one, .one, .one]) (ofString "check_transaction") _ _
    wkScBo_check_transaction (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ hp9 hc9 => ?_)
  refine p1_skip hp9 (fun hp9' => ?_)
  refine p1_decCall_ro_add hc9 "tx_blob_gas_used" .one (ofString "calculate_total_blob_gas")
    [.var .local (ofString "tx")] _ ro_calculate_total_blob_gas hp9'
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ _ _ _ _ hp10 hc10 => ?_)
  refine p1_decCall_scBo_keep hc10 hp10 (by decide)
    validBufList_wsAcctBufs
    (by intro p hp0; simp [wsAcctBufs] at hp0; rcases hp0 with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
    (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    ptxKeepSub_stdKeep (Or.inr (by simp [stdKeep]))
    (gs := [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64)])
    (by unfold PtxP1.ScratchSpec; decide) (fun _ => rfl)
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp [stdKeep]) (by decide)
    "acct" .one (ofString "get_account") _ _
    wkScBo_get_account (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ hp11 hc11 => ?_)
  refine p1_skip hp11 (fun hp11' => ?_)
  refine p1_dec_keep "blob_gas_fee" (.comb [.one, .one, .one, .one]) _ _ hp11'
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ hp12 => ?_)
  refine p1_blobBranch (by simpa [setVarHOLFinite] using hc11) hp12 (by decide) (by decide) (by decide) (fun s13 hp13 hc13 => ?_)
  refine p1_dec_add "gas" .one _ _ hp13
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ hp14 => ?_)
  refine p1_decCall_ro_keep (by simpa [setVarHOLFinite] using hc13) "egf" (.comb [.one, .one, .one, .one, .one]) (ofString "fee_mul")
    _ _ ro_fee_mul hp14
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ _ _ _ _ hp15 hc15 => ?_)
  refine p1_dec_keep "effective_gas_fee" (.comb [.one, .one, .one, .one]) _ _ hp15
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ hp16 => ?_)
  refine p1_dec_keep "execution_gas" .one _ _ hp16
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ hp17 => ?_)
  refine p1_regular_budget (by simpa [setVarHOLFinite] using hc15) hp17 (by decide) (fun s18 hc18 hp18 => ?_)
  refine p1_min_mgas hc18 hp18 (by decide) (fun s19 hc19 hp19 => ?_)
  refine p1_dec_add "reservoir" .one _ _ hp19
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ hp20 => ?_)
  refine p1_call0_scBo (by simpa [setVarHOLFinite] using hc19) hp20 (by decide)
    validBufList_acctMutBufs
    (by intro p hp0; simp [acctMutBufs] at hp0; rcases hp0 with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
    acctMut_globals_sub (by decide) (by decide) (by decide) (by decide) (by decide)
    ptxKeepSub_stdKeep (Or.inr (by simp [stdKeep]))
    (gs := [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64), ("sk_buf", 64, 52)])
    (by unfold PtxP1.ScratchSpec; decide) (fun _ => rfl)
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp [stdKeep]) (by decide)
    (ofString "increment_nonce") _ _ wkScBo_increment_nonce
    (fun _ hp21 hc21 => ?_)
  refine p1_dec_keep "bal" (.comb [.one, .one, .one, .one]) _ _ hp21
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ hp22 => ?_)
  refine p1_callLocal_ro_keep (by simpa [setVarHOLFinite] using hc21) "bal" (ofString "u256_sub") _ _ ptx_ro_u256_sub hp22
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ hp23 hc23 => ?_)
  refine p1_callLocal_ro_keep hc23 "bal" (ofString "u256_sub") _ _ ptx_ro_u256_sub hp23
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ hp24 hc24 => ?_)
  refine p1_call0_scBo hc24 hp24 (by decide)
    validBufList_acctMutBufs
    (by intro p hp0; simp [acctMutBufs] at hp0; rcases hp0 with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
    acctMut_globals_sub (by decide) (by decide) (by decide) (by decide) (by decide)
    ptxKeepSub_stdKeep (Or.inr (by simp [stdKeep]))
    (gs := [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64), ("sk_buf", 64, 52)])
    (by unfold PtxP1.ScratchSpec; decide) (fun _ => rfl)
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp [stdKeep]) (by decide)
    (ofString "set_account_balance") _ _ wkScBo_set_account_balance
    (fun _ hp25 hc25 => ?_)
  refine p1_skip hp25 (fun hp26 => ?_)
  have hsh_final := phase1_map_strong hp26.shapes (by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) (by simp) (by simp) (by simp)
  have hv_final : PtxValidatedStrong _ := phase1_stage4_strong hp26.stage hsh_final
  exact htail _ hc25 ⟨hp26.base, hv_final, hp26.expw, hp26.gamma, hp26.tx_eq, hp26.idx_eq, hp26.snd_own rfl⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
