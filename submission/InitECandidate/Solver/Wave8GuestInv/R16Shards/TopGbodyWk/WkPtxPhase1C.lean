import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase1B
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_tx_chain_id
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_sub
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_validate_transaction
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_min
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_min
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_validate_transaction

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

open private acct_copy_step flattenHOL_shape_u256 evaluateHOLFiniteState_seq_assoc
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.AccountWk

open private eval_tx_encode_generic_mode0_bounded_resumes
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkEncodeTxBounded

/-! # Phase 1 State & Combinator Infrastructure (`WkPtxPhase1C`) -/

def PtxEntryFull {F : Type} (entry s : PanSemStateFiniteExact 64 F) : Prop :=
  entry = s ∧ TxReadyFullStrong s

theorem txReadyFullStrong_init {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : TxReadyFullStrong s) : PtxEntryFull s s := ⟨rfl, h⟩

theorem ptx_ro_chain_id : ReadOnlyFn (ofString "tx_chain_id") :=
  InitECandidate.Solver.Wave8GuestInv.M17.ro_tx_chain_id

theorem ptx_ro_u256_sub : ReadOnlyFn (ofString "u256_sub") :=
  InitECandidate.Solver.Wave8Contracts.M18.«ro_u256_sub»

theorem ptx_ro_validate_tx : ReadOnlyFn (ofString "validate_transaction") :=
  InitECandidate.Solver.Wave8Contracts.M18.«ro_validate_transaction»

theorem ptx_ro_min : ReadOnlyFn (ofString "min") :=
  InitECandidate.Solver.Wave8Contracts.M15.«ro_min»

theorem ptx_rv_min :
    FunSpec GuestInv (fun s r _ => ∀ v, r = some (.returned v) →
      ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ locN s "a") (ofString "min") :=
  InitECandidate.Solver.Wave8Contracts.M27.rv_min

theorem ptx_rv_validate_tx :
    FunSpec GuestInv (fun _ r _ => ∀ v, r = some (.returned v) →
      ∃ a b c : BitVec 64, v = .rStruct [.val (.word a), .val (.word b), .val (.word c)] ∧
        a.toNat ≤ 16777216) (ofString "validate_transaction") :=
  InitECandidate.Solver.Wave8Contracts.M27.rv_validate_transaction

theorem ptx_id_exception_step {F : Type} {txDone : Bool}
    {entry s : PanSemStateFiniteExact 64 F} {eid : MlS} {ev : ValueHOL 64}
    (hbase : PtxRelBase txDone entry s) (ck : Nat) :
    WorldStep ptxRegions ptxGlobals ptxKeep PtxLogsAndSlices
      entry (some (.exception eid ev)) { s with locals := .empty, clock := ck } := by
  have hid : WorldStep (bufRegions []) [] stdKeep NoExtra s (some (.exception eid ev)) s := by
    refine ⟨hbase.world.1, le_rfl, fun _ _ => rfl, fun _ _ _ _ _ _ => rfl, ?_⟩
    intro S0 Nd0 hWT0 _
    exact ⟨S0, Nd0, fun _ ht => ht, hWT0,
      fun o ho => Or.inr (Or.inl ⟨o, ho, le_rfl, le_rfl⟩),
      fun _ _ _ => rfl, trivial⟩
  have hex := ptxRelBase_exception_worldStep hbase
    (by intro p hp; cases hp) (by intro p hp; cases hp) (by intro g hg; cases hg)
    ptxKeepSub_stdKeep hid
  exact ptxWorldStep_strong_with_locals_right .empty ck hex

/-! ## 1. Heap-Below-`heap_ptr` Unhit for `state_fresh_tx`, `encode_transaction`, and `encArray` Stores -/

theorem state_fresh_tx_heap_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {rv : ValueHOL 64}
    (hc : s.code = originalRuntimeCode)
    (hWOK : WorldOK s)
    {vs : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret : ShapeHOL}
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "state_fresh_tx") vs = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned rv), post)) :
    ∀ a : BitVec 64, sourceBase ≤ a.toNat → a.toNat + 8 ≤ globN s "heap_ptr" →
      post.memory a = s.memory a := by
  have hbody := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "state_fresh_tx")
    _ _ body _ ret vs callee (by rw [hc]; exact WkBal.lookup_state_fresh_tx) hl
  subst hbody
  let ent := callEntryStateHOLFinite s callee
  have hent_code : ent.code = originalRuntimeCode := hc
  have hW_ent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hWOK
  have hAR0 : ArenaReady ent := hW_ent.1
  have hnt' : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_state_fresh_tx)).1 ≠ some .timeOut := by
    rw [hb]; simp
  have hres' : Resumes (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_state_fresh_tx)).1 := by
    rw [hb]; exact Or.inl ⟨rv, rfl⟩
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
  rw [hbody_eq] at hnt' hres'
  obtain ⟨pw, qw, s0a, hpw_eq, hqw_eq, hs0a_hp, _, hpw8, hAR0a, hs0a_m, _, _, _,
      hsp0a, _, hts0a, _, hnt0a, hres0a, heq0a⟩ :=
    WkBal.seq_call_alloc_global_resumes ent (ofString "ts") 72 _ hAR0
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
  have hsp0 : globN s0 "scratch_ptr" = globN ent "scratch_ptr" := hsp0a
  have hfr_s_s0 : FrameOutside ent s0 [(globN ent "scratch_ptr", 0)]
      (globN ent "heap_ptr", globN s0 "heap_ptr" - globN ent "heap_ptr") := by
    intro a _ hnhf
    exact (hfr0b a (fun _ h => by cases h) (fun ⟨c1, c2⟩ => by
      dsimp only at c1 c2; exact hnhf ⟨by dsimp only; omega, by dsimp only; omega⟩)).trans (by rw [hs0a_m])
  obtain ⟨_, s1, _, _, hAR1, _, hsp1, _, _, _, _, _, _, _, hfr1, _, hg1, hnt1, hres1, _, heq1_2⟩ :=
    WkBal.decCall_htab_new_store_ts_slot s0 pw 8 20 64 _ hAR0b (by omega) hpw_lo hpw8
      (by decide) (by decide) hts0a (by decide) (by decide) hnt0a hres0a
  have hts1 : s1.globals.lookup (ofString "ts") = some (.val (.word pw)) := (hg1 (ofString "ts") (by decide)).symm.trans hts0a
  have hfr_s_s1 := WkBal.frameOutside_collapse_pw_sp ent s0 s1 pw.toNat (by omega) (by omega) (by omega) hfr_s_s0 (by rw [hsp0] at hfr1; exact hfr1)
  obtain ⟨_, s2, _, _, hAR2, _, hsp2, _, _, _, _, _, _, _, hfr2, _, hg2, hnt2, hres2, heq2⟩ :=
    WkBal.seq_htab_new_store_ts_slot s1 pw 16 20 64 _ hAR1 (by omega) hpw_lo hpw8 (by decide) (by decide) hts1 (by decide) (by decide) hnt1 hres1
  have hts2 : s2.globals.lookup (ofString "ts") = some (.val (.word pw)) := (hg2 (ofString "ts") (by decide)).symm.trans hts1
  have hfr_s_s2 := WkBal.frameOutside_collapse_pw_sp ent s1 s2 pw.toNat (by omega) (by omega) (by omega) hfr_s_s1 (by rw [hsp1, hsp0] at hfr2; exact hfr2)
  obtain ⟨_, s3, _, _, hAR3, _, hsp3, _, _, _, _, _, _, _, hfr3, _, hg3, hnt3, hres3, heq3⟩ :=
    WkBal.seq_htab_new_store_ts_slot s2 pw 24 52 64 _ hAR2 (by omega) hpw_lo hpw8 (by decide) (by decide) hts2 (by decide) (by decide) hnt2 hres2
  have hts3 : s3.globals.lookup (ofString "ts") = some (.val (.word pw)) := (hg3 (ofString "ts") (by decide)).symm.trans hts2
  have hfr_s_s3 := WkBal.frameOutside_collapse_pw_sp ent s2 s3 pw.toNat (by omega) (by omega) (by omega) hfr_s_s2 (by rw [hsp2, hsp1, hsp0] at hfr3; exact hfr3)
  obtain ⟨_, s4, _, _, hAR4, _, hsp4, _, _, _, _, _, _, _, hfr4, _, hg4, hnt4, hres4, heq4⟩ :=
    WkBal.seq_htab_new_store_ts_slot s3 pw 32 20 16 _ hAR3 (by omega) hpw_lo hpw8 (by decide) (by decide) hts3 (by decide) (by decide) hnt3 hres3
  have hts4 : s4.globals.lookup (ofString "ts") = some (.val (.word pw)) := (hg4 (ofString "ts") (by decide)).symm.trans hts3
  have hfr_s_s4 := WkBal.frameOutside_collapse_pw_sp ent s3 s4 pw.toNat (by omega) (by omega) (by omega) hfr_s_s3 (by rw [hsp3, hsp2, hsp1, hsp0] at hfr4; exact hfr4)
  obtain ⟨_, s5, _, _, hAR5, _, hsp5, _, _, _, _, _, _, _, hfr5, _, hg5, hnt5, hres5, heq5⟩ :=
    WkBal.seq_htab_new_store_ts_slot s4 pw 40 52 16 _ hAR4 (by omega) hpw_lo hpw8 (by decide) (by decide) hts4 (by decide) (by decide) hnt4 hres4
  have hts5 : s5.globals.lookup (ofString "ts") = some (.val (.word pw)) := (hg5 (ofString "ts") (by decide)).symm.trans hts4
  have hfr_s_s5 := WkBal.frameOutside_collapse_pw_sp ent s4 s5 pw.toNat (by omega) (by omega) (by omega) hfr_s_s4 (by rw [hsp4, hsp3, hsp2, hsp1, hsp0] at hfr5; exact hfr5)
  obtain ⟨_, s6, _, _, hAR6, _, hsp6, _, _, _, _, _, _, _, hfr6, _, hg6, hnt6, hres6, heq6⟩ :=
    WkBal.seq_htab_new_store_ts_slot s5 pw 48 32 16 _ hAR5 (by omega) hpw_lo hpw8 (by decide) (by decide) hts5 (by decide) (by decide) hnt5 hres5
  have hts6 : s6.globals.lookup (ofString "ts") = some (.val (.word pw)) := (hg6 (ofString "ts") (by decide)).symm.trans hts5
  have hfr_s_s6 := WkBal.frameOutside_collapse_pw_sp ent s5 s6 pw.toNat (by omega) (by omega) (by omega) hfr_s_s5 (by rw [hsp5, hsp4, hsp3, hsp2, hsp1, hsp0] at hfr6; exact hfr6)
  obtain ⟨_, s7, _, _, hAR7, _, hsp7, _, _, _, _, _, _, _, hfr7, _, hg7, hnt7, hres7, heq7⟩ :=
    WkBal.seq_htab_new_store_ts_slot s6 pw 56 20 16 _ hAR6 (by omega) hpw_lo hpw8 (by decide) (by decide) hts6 (by decide) (by decide) hnt6 hres6
  have hts7 : s7.globals.lookup (ofString "ts") = some (.val (.word pw)) := (hg7 (ofString "ts") (by decide)).symm.trans hts6
  have hfr_s_s7 := WkBal.frameOutside_collapse_pw_sp ent s6 s7 pw.toNat (by omega) (by omega) (by omega) hfr_s_s6 (by rw [hsp6, hsp5, hsp4, hsp3, hsp2, hsp1, hsp0] at hfr7; exact hfr7)
  obtain ⟨_, s8, _, _, hAR8, _, hsp8, _, _, _, _, _, _, _, hfr8, _, _, _, _, heq8⟩ :=
    WkBal.seq_htab_new_store_ts_slot s7 pw 64 52 16 _ hAR7 (by omega) hpw_lo hpw8 (by decide) (by decide) hts7 (by decide) (by decide) hnt7 hres7
  have hfr_s_s8 := WkBal.frameOutside_collapse_pw_sp ent s7 s8 pw.toNat (by omega) (by omega) (by omega) hfr_s_s7 (by rw [hsp7, hsp6, hsp5, hsp4, hsp3, hsp2, hsp1, hsp0] at hfr8; exact hfr8)
  obtain ⟨heq9, _, hs9_m, _, _, _, _, _, _, _⟩ :=
    WkBal.seq_assign_global_zero_return_zero s8 (ofString "journal_n") hAR8 ⟨"journal_n", by decide, rfl⟩ ⟨by decide, by decide, by decide⟩
  set inner_post := emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "journal_n") (.val (.word 0)) s8)
  have hchain2_2 := congrArg Prod.snd (by rw [heq2, heq3, heq4, heq5, heq6, heq7, heq8, heq9] :
    evaluateHOLFiniteState s1 _ = (some (.returned (.val (.word 0))), inner_post))
  dsimp only at hchain2_2
  have hpost_eq : post = { inner_post with locals := HolFiniteMapExact.resVarEq inner_post.locals (ofString "t", s0.locals.lookup (ofString "t")) } := by
    have h1 : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_state_fresh_tx)).2 = post := by rw [hb]
    rw [← h1, hbody_eq, heq0a, heq0b]
    exact heq1_2.trans (by rw [hchain2_2])
  intro a hlo hhi
  rw [hpost_eq]
  change inner_post.memory a = s.memory a
  rw [hs9_m]
  have hp_eq : globN ent "heap_ptr" = globN s "heap_ptr" := rfl
  have hhl_ss : heapLimit ≤ scratchStart := by decide
  have h1 := hAR0.2.2.1
  have h2 := hAR0.2.2.2.1
  have h3 := hAR0.2.2.2.2.1
  exact hfr_s_s8 a
    (by intro iv hiv; simp at hiv; subst hiv; rintro ⟨ch1, _⟩; dsimp only at ch1; omega)
    (fun ⟨c1, _⟩ => by dsimp only at c1; omega)

theorem encode_tx_heap_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {rv : ValueHOL 64}
    (hc : s.code = originalRuntimeCode)
    (hWOK : WorldOK s) (hVE : TxValidEncodeReady s)
    {vs : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret : ShapeHOL}
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "tx")] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "encode_transaction") vs = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned rv), post)) :
    ∀ a : BitVec 64, sourceBase ≤ a.toNat → a.toNat + 8 ≤ globN s "heap_ptr" →
      post.memory a = s.memory a := by
  obtain ⟨tv, he, ht⟩ := PtxP1.params_one_value s (ofString "encode_transaction") (ofString "tx")
    .one _ (.comb [.one, .one]) (by rw [hc]; exact PtxP1.lookup_encode_transaction)
    (.var .local (ofString "tx")) vs body callee ret ha hl
  have htx_cal : callee.lookup (ofString "tx") = s.locals.lookup (ofString "tx") := ht.trans he.symm
  have hraw_lk := lookupCodeHOLFinite_eq_some s.code.lookup (ofString "encode_transaction") vs body callee ret hl
  have hret_eq : ret = .comb [.one, .one] := by
    rw [hc] at hraw_lk
    simp only [lookupCodeHOLExact, lookup_encode_transaction_strong] at hraw_lk
    split at hraw_lk
    · exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj hraw_lk)).2).2.symm
    · cases hraw_lk
  subst hret_eq
  have hbody_eq : body = sourceFnBody Guest.Software.guestFn_encode_transaction :=
    lookupCodeHOLFinite_installed_body s.code.lookup (ofString "encode_transaction")
      _ _ body _ _ vs callee (by rw [hc]; exact lookup_encode_transaction_strong) hl
  subst hbody_eq
  let ent0 := callEntryStateHOLFinite s callee
  have hent0_code : ent0.code = originalRuntimeCode := hc
  have hW_ent0 : WorldOK ent0 := localsFree_worldOK s callee (s.clock - 1) hWOK
  have hVE_ent0 : TxValidEncodeReady ent0 := by
    unfold TxValidEncodeReady at hVE ⊢
    have hloc : locN ent0 "tx" = locN s "tx" := by simp [ent0, callEntryStateHOLFinite, locN, htx_cal]
    rw [hloc]
    exact txValidEncodeAt_with_locals s callee (s.clock - 1) hVE
  suffices heff : HeapByteEff ent0 post [] ["heap_ptr"] by
    have hent0_hp : globN ent0 "heap_ptr" = globN s "heap_ptr" := rfl
    have hent0_fp : globN ent0 "frame_mem_ptr" = globN s "frame_mem_ptr" := rfl
    intro a hlo hhi
    by_contra hne
    rcases heff.cell_frame a hne with ⟨iv, hiv, _⟩ | ⟨_, hfg1, _⟩ | ⟨_, hhf1, _⟩
    · simp at hiv
    · unfold freeGap at hfg1
      rw [hent0_fp] at hfg1
      have hhl_ss : heapLimit ≤ scratchStart := by decide
      have h1 := hWOK.1.2.2.1; have h2 := hWOK.1.2.2.2.1; have h3 := hWOK.1.2.2.2.2.1
      dsimp only at hfg1; omega
    · unfold heapFree at hhf1
      rw [hent0_hp] at hhf1
      dsimp only at hhf1; omega
  have hnt : (evaluateHOLFiniteState ent0 (sourceFnBody Guest.Software.guestFn_encode_transaction)).1 ≠ some .timeOut := by
    rw [hb]; simp
  have hres : Resumes (evaluateHOLFiniteState ent0 (sourceFnBody Guest.Software.guestFn_encode_transaction)).1 := by
    rw [hb]; exact Or.inl ⟨rv, rfl⟩
  have hl_tx0 : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "encode_transaction") vs =
      some (sourceFnBody Guest.Software.guestFn_encode_transaction, ent0.locals, .comb [.one, .one]) := by
    simpa [ent0, callEntryStateHOLFinite, hc] using hl
  obtain ⟨tx0, _, htx0⟩ := WkBlockTxEnc.lookupCode_one_word_any lookup_encode_transaction_strong hl_tx0
  have hAR : ArenaReady ent0 := hW_ent0.1
  have hbody_fn : sourceFnBody Guest.Software.guestFn_encode_transaction =
      .call none (ofString "tx_encode_generic")
        [.var .local (ofString "tx"), .const 0, .const 0] := rfl
  have hpost_eq : post = (evaluateHOLFiniteState ent0 (sourceFnBody Guest.Software.guestFn_encode_transaction)).2 := by
    rw [hb]
  rw [hpost_eq, hbody_fn]
  rw [hbody_fn] at hnt hres
  rw [evaluateHOLFiniteState_call] at hnt hres ⊢
  have ha0 : evalListHOLFinite ent0 (h := fun a => Classical.propDecidable (ent0.memaddrs a))
      [.var .local (ofString "tx"), .const 0, .const 0] =
      some [.val (.word tx0), .val (.word 0#64), .val (.word 0#64)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, htx0]
  rw [ha0] at hnt hres ⊢
  have hlk : lookupCodeHOLFinite ent0.code.lookup (ofString "tx_encode_generic")
      [.val (.word tx0), .val (.word 0#64), .val (.word 0#64)] =
      some (sourceFnBody Guest.Software.guestFn_tx_encode_generic,
        ((HolFiniteMapExact.empty.update (ofString "tx", ValueHOL.val (.word tx0))).update
          (ofString "mode", ValueHOL.val (.word 0#64))).update
          (ofString "chain_id", ValueHOL.val (.word 0#64)),
        .comb [.one, .one]) := by
    have hraw : lookupCodeHOLExact ent0.code.lookup (ofString "tx_encode_generic")
        [.val (.word tx0), .val (.word 0#64), .val (.word 0#64)] =
        some (sourceFnBody Guest.Software.guestFn_tx_encode_generic,
          (fun key => if key = ofString "chain_id" then some (.val (.word 0#64))
            else if key = ofString "mode" then some (.val (.word 0#64))
            else if key = ofString "tx" then some (.val (.word tx0)) else none),
          .comb [.one, .one]) := by
      have hne1 : ofString "tx" ≠ ofString "mode" := by decide
      have hne2 : ofString "tx" ≠ ofString "chain_id" := by decide
      have hne3 : ofString "mode" ≠ ofString "chain_id" := by decide
      simp [lookupCodeHOLExact, hent0_code, lookup_tx_encode_generic, shapeOfHOLExact, shapeEqHOL,
        shapeEqHOL.shapeEqListHOL, hne1, hne2, hne3]
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite
    split
    · rename_i missing; rw [hraw] at missing; cases missing
    · rename_i foundBody foundLocals foundShape found
      have equal := Option.some.inj (found.symm.trans hraw)
      obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
      apply congrArg (fun locals => some (sourceFnBody Guest.Software.guestFn_tx_encode_generic, locals, ShapeHOL.comb [.one, .one]))
      apply HolFiniteMapExact.ext; funext key
      by_cases hkc : key = ofString "chain_id"
      · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
      · by_cases hkm : key = ofString "mode"
        · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
            show ofString "chain_id" ≠ ofString "mode" from by decide, hkc]
        · by_cases hkt : key = ofString "tx"
          · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
              show ofString "chain_id" ≠ ofString "tx" from by decide,
              show ofString "mode" ≠ ofString "tx" from by decide, hkc, hkm]
          · simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
              hkc, hkm, hkt, Ne.symm hkc, Ne.symm hkm, Ne.symm hkt]
  simp only [hlk] at hnt hres ⊢
  by_cases hcz : ent0.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt hres ⊢
    set cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
      ((HolFiniteMapExact.empty.update (ofString "tx", ValueHOL.val (.word tx0))).update
        (ofString "mode", ValueHOL.val (.word 0#64))).update (ofString "chain_id", ValueHOL.val (.word 0#64))
    let ent := callEntryStateHOLFinite ent0 cmap
    have hent_tx : ent.locals.lookup (ofString "tx") = some (.val (.word tx0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "chain_id" ≠ ofString "tx" by decide,
        show ofString "mode" ≠ ofString "tx" by decide]
    have hent_mode : ent.locals.lookup (ofString "mode") = some (.val (.word 0#64)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "chain_id" ≠ ofString "mode" by decide]
    have heff_s_ent : HeapByteEff ent0 ent [] ["heap_ptr"] :=
      (HeapByteEff.refl hAR [] ["heap_ptr"]).locals_clock ent.locals ent.clock
    have hAR_ent : ArenaReady ent := heff_s_ent.arena
    rcases hbody_ev : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_tx_encode_generic) with ⟨rbody, sbody⟩
    change evaluateHOLFiniteState (callEntryStateHOLFinite ent0 cmap)
        (sourceFnBody Guest.Software.guestFn_tx_encode_generic) = (rbody, sbody) at hbody_ev
    simp only [hbody_ev] at hnt hres ⊢
    have hnt_body : rbody ≠ some .timeOut := by rintro rfl; exact hnt rfl
    have hres_body : Resumes rbody := by
      cases rbody with
      | none => exact False.elim (WkBlockTxEnc.not_resumes_error hres)
      | some r =>
        cases r with
        | timeOut => exact absurd rfl hnt_body
        | returned rv0 =>
          dsimp only at hres; split at hres
          · exact Or.inl ⟨_, rfl⟩
          · exact False.elim (WkBlockTxEnc.not_resumes_error hres)
        | exception eid ev => exact hres
        | «break» | «continue» | error => exact False.elim (WkBlockTxEnc.not_resumes_error hres)
        | finalFfi _ => rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
    have htx_enc_ent : TxValidEncodeAt ent tx0.toNat := by
      have hloc_tx : locN ent0 "tx" = tx0.toNat := by simp [locN, htx0]
      exact hloc_tx ▸ hVE_ent0
    have hgen := eval_tx_encode_generic_mode0_bounded_resumes ent tx0 hAR_ent htx_enc_ent hent_tx hent_mode
      (by rw [hbody_ev]; exact hnt_body) (by rw [hbody_ev]; exact hres_body)
    rw [hbody_ev] at hgen
    have hbody_eff : HeapByteEff ent0 sbody [] ["heap_ptr"] := heff_s_ent.trans hgen.1
    cases rbody with
    | none => exact False.elim (WkBlockTxEnc.not_resumes_error hres)
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_body
      | returned rv0 =>
        dsimp only at hres ⊢; split
        · exact hbody_eff.locals_clock _ _
        · rename_i hbad; rw [if_neg hbad] at hres; exact False.elim (WkBlockTxEnc.not_resumes_error hres)
      | «break» | «continue» | error => exact False.elim (WkBlockTxEnc.not_resumes_error hres)
      | exception _ _ => exact hbody_eff.locals_clock _ _
      | finalFfi _ => rcases hres_body with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h

theorem txValidRecoverReadyAt_store_encArray {F : Type}
    {s : PanSemStateFiniteExact 64 F}
    (hRs : TxReadyStrong s)
    {x : BitVec 64}
    (hin : Inside (x.toNat, 8) (PtxP1.encArray s).1 ((PtxP1.encArray s).1 + (PtxP1.encArray s).2))
    {mem' : BitVec 64 → HolWordLab 64}
    (hm : ∀ a, a ≠ x → mem' a = s.memory a)
    (hVR : TxValidRecoverReadyAt s (locN s "tx")) :
    TxValidRecoverReadyAt { s with memory := mem' } (locN s "tx") := by
  let post : PanSemStateFiniteExact 64 F := { s with memory := mem' }
  have hGp : GuestInv post := guestInv_congr (s := s) rfl rfl rfl rfl hRs.1.1.1.1
  obtain ⟨S, Nd, hW, hT⟩ := hRs.2.2.2.2
  have harr_ow : PtxP1.encArray s ∈ worldOwned s S Nd :=
    List.mem_append_left _ (List.mem_append_right _ (PtxP1.encArray_mem_fixed (PtxP1.txEnv_of_ready hRs)))
  have hhi_arr := (R13Shards.ivl_allocated_bound hRs.1.1.1.2 (PtxP1.encArray_words hW.2.2.1 (PtxP1.txEnv_of_ready hRs)).1).2
  dsimp only [PtxP1.encArray] at hhi_arr
  have hhl_64 : heapLimit ≤ 2 ^ 64 := by rw [WkBlockTxEnc.heapLimit_val]; decide
  have hse_64 : scratchEnd ≤ 2 ^ 64 := by rw [WkBlockTxEnc.scratchEnd_val]; decide
  have hm_disj : ∀ iv : Ivl, Inside iv sourceBase (globN s "heap_ptr") → iv.1 % 8 = 0 →
      Disj iv (PtxP1.encArray s) →
      ∀ off, off % 8 = 0 → off + 8 ≤ iv.2 → memW post (iv.1 + off) = memW s (iv.1 + off) := by
    intro iv hin_iv _ hd off _ hoff_lt
    have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hRs.1.1.1.2.2.1
    have hlt64 : iv.1 + off < 2 ^ 64 := by unfold Inside at hin_iv; omega
    have hne : BitVec.ofNat 64 (iv.1 + off) ≠ x := by
      intro heq
      have htonat := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64] at htonat
      have hd_x := R13Shards.disj_of_inside_right hin hd
      rcases hd_x with h0 | h0 | hd1 | hd2 <;> (try dsimp only at *) <;> omega
    unfold memW; dsimp only [post]; rw [hm _ hne]
  obtain ⟨hTV, hin208, hin272⟩ := hVR
  obtain ⟨hw, hin_tx, h0, h200, h216_lim, hsl, h264_lim, h280_lim, hw208, hw272⟩ := hTV
  have hd_tx : Disj (locN s "tx", 384) (PtxP1.encArray s) := hT.2.1 _ (by simp) _ harr_ow
  have htx8 : (locN s "tx") % 8 = 0 := hw.1
  have e0 : memW post (locN s "tx") = memW s (locN s "tx") := by
    simpa using hm_disj (locN s "tx", 384) hin_tx htx8 hd_tx 0 (by decide) (by omega)
  have e200 : memW post (locN s "tx" + 200) = memW s (locN s "tx" + 200) :=
    hm_disj (locN s "tx", 384) hin_tx htx8 hd_tx 200 (by decide) (by omega)
  have e208 : memW post (locN s "tx" + 208) = memW s (locN s "tx" + 208) :=
    hm_disj (locN s "tx", 384) hin_tx htx8 hd_tx 208 (by decide) (by omega)
  have e216 : memW post (locN s "tx" + 216) = memW s (locN s "tx" + 216) :=
    hm_disj (locN s "tx", 384) hin_tx htx8 hd_tx 216 (by decide) (by omega)
  have e264 : memW post (locN s "tx" + 264) = memW s (locN s "tx" + 264) :=
    hm_disj (locN s "tx", 384) hin_tx htx8 hd_tx 264 (by decide) (by omega)
  have e272 : memW post (locN s "tx" + 272) = memW s (locN s "tx" + 272) :=
    hm_disj (locN s "tx", 384) hin_tx htx8 hd_tx 272 (by decide) (by omega)
  have e280 : memW post (locN s "tx" + 280) = memW s (locN s "tx" + 280) :=
    hm_disj (locN s "tx", 384) hin_tx htx8 hd_tx 280 (by decide) (by omega)
  have hsl_eq : txAccessSlots post (locN s "tx") = txAccessSlots s (locN s "tx") := by
    unfold txAccessSlots
    rw [e216, e208]
    by_cases hpos : 0 < memW s (locN s "tx" + 216)
    · apply congrArg List.sum
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      have hd208 : Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) (PtxP1.encArray s) :=
        (hT.2.2 hpos).2 _ (by simp) _ harr_ow
      have hlen208 : 24 * i + 16 + 8 ≤ (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)).2 := by
        dsimp only; omega
      simpa [Nat.add_assoc] using hm_disj _ (hin208 hpos) (hw208 hpos).1 hd208 (24 * i + 16) (by omega) hlen208
    · have hz : memW s (locN s "tx" + 216) = 0 := by omega
      simp [hz]
  refine ⟨?_, ?_, ?_⟩
  · unfold TxValidAt
    rw [e0, e200, e208, e216, e264, e272, e280, hsl_eq]
    exact ⟨R13Shards.wordsOK_transfer hRs.1.1.1.1 hGp hw, hin_tx,
      h0, h200, h216_lim, hsl, h264_lim, h280_lim,
      fun hp => R13Shards.wordsOK_transfer hRs.1.1.1.1 hGp (hw208 hp),
      fun hp => R13Shards.wordsOK_transfer hRs.1.1.1.1 hGp (hw272 hp)⟩
  · rw [e216, e208]; exact hin208
  · rw [e280, e272]; exact hin272

/-! ## 2. Bundled Phase 1 State & `PtxRelRunStrong` Step Helpers -/

structure P1State {F : Type} (txDone : Bool) (n : Nat)
    (xs : List (String × ShapeHOL)) (hasSnd : Bool)
    (entry s : PanSemStateFiniteExact 64 F) : Prop where
  base : PtxRelBase txDone entry s
  stage : PtxP1.StageP n s
  shapes : PtxLocalShapeMap xs s
  expw : globN s "bn_expw" = globN entry "bn_expw"
  gamma : globN s "bn_gamma" = globN entry "bn_gamma"
  tx_eq : s.locals.lookup (ofString "tx") = entry.locals.lookup (ofString "tx")
  idx_eq : s.locals.lookup (ofString "index") = entry.locals.lookup (ofString "index")
  snd_own : hasSnd = true → SenderTxOwned s

theorem p1State_with_locals {F : Type} {txDone : Bool} {n : Nat}
    {xs : List (String × ShapeHOL)} {hasSnd : Bool}
    {entry s : PanSemStateFiniteExact 64 F}
    (hp : P1State txDone n xs hasSnd entry s)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (ck : Nat)
    (hst : ∀ k ∈ PtxP1.stageNames n, L.lookup (ofString k) = s.locals.lookup (ofString k))
    (hxs : ∀ x ∈ xs, L.lookup (ofString x.1) = s.locals.lookup (ofString x.1))
    (htx : L.lookup (ofString "tx") = s.locals.lookup (ofString "tx"))
    (hidx : L.lookup (ofString "index") = s.locals.lookup (ofString "index"))
    (hsnd : hasSnd = true → L.lookup (ofString "sender") = s.locals.lookup (ofString "sender")) :
    P1State txDone n xs hasSnd entry { s with locals := L, clock := ck } := by
  refine ⟨ptxRelBase_with_locals hp.base L ck,
    PtxP1.localsOnly_stage n s L ck hst hp.stage,
    phase1_map_localsOnly xs s L ck (fun nm hnm => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hnm
      exact hxs x hx) hp.shapes,
    hp.expw, hp.gamma, htx.trans hp.tx_eq, hidx.trans hp.idx_eq,
    fun hh => senderTxOwned_with_locals s L ck htx (hsnd hh) (hp.snd_own hh)⟩

theorem p1_skip {F : Type} {txDone : Bool} {n : Nat}
    {xs : List (String × ShapeHOL)} {hasSnd : Bool}
    {entry s : PanSemStateFiniteExact 64 F} {tail : ProgHOL 64}
    (hp : P1State txDone n xs hasSnd entry s)
    (htail : P1State txDone n xs hasSnd entry { s with clock := s.clock } →
      PtxRelRunStrong entry tail s) :
    PtxRelRunStrong entry (.seq .skip tail) s :=
  ptxRelRunStrong_skip (htail hp)

theorem p1_dec_add {F : Type} {txDone : Bool} {n : Nat}
    {xs : List (String × ShapeHOL)} {hasSnd : Bool}
    {entry s : PanSemStateFiniteExact 64 F}
    (name : String) (sh : ShapeHOL) (e : ExpHOL 64) (tail : ProgHOL 64)
    (hp : P1State txDone n xs hasSnd entry s)
    (hne_st : ∀ k ∈ PtxP1.stageNames n, ofString k ≠ ofString name)
    (hne_xs : ∀ x ∈ xs, ofString x.1 ≠ ofString name)
    (hne_tx : ofString "tx" ≠ ofString name)
    (hne_idx : ofString "index" ≠ ofString name)
    (hne_snd : ofString "sender" ≠ ofString name)
    (htail : ∀ v : ValueHOL 64, evalAt s e = some v → shapeOfHOLExact v = sh →
      P1State txDone n ((name, sh) :: xs) hasSnd entry (setVarHOLFinite (ofString name) v s) →
      PtxRelRunStrong entry tail (setVarHOLFinite (ofString name) v s)) :
    PtxRelRunStrong entry (.dec (ofString name) sh e tail) s := by
  refine ptxRelRunStrong_dec (ofString name) sh e tail (fun v hev hsh => ?_)
  have hp' : P1State txDone n ((name, sh) :: xs) hasSnd entry (setVarHOLFinite (ofString name) v s) := by
    refine ⟨ptxRelBase_with_locals hp.base (s.locals.update (ofString name, v)) s.clock,
      LocalsOnly.setVar (PtxP1.localsOnly_stage n) hne_st v s hp.stage,
      ptxLocalShapeMap_add s s hp.shapes name sh v hne_xs hsh,
      hp.expw, hp.gamma,
      by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm hne_tx, hp.tx_eq],
      by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm hne_idx, hp.idx_eq],
      fun hh => senderTxOwned_setVar (Ne.symm hne_tx) (Ne.symm hne_snd) (hp.snd_own hh)⟩
  exact htail v hev hsh hp'

theorem p1_dec_keep {F : Type} {txDone : Bool} {n : Nat}
    {xs : List (String × ShapeHOL)} {hasSnd : Bool}
    {entry s : PanSemStateFiniteExact 64 F}
    (name : String) (sh : ShapeHOL) (e : ExpHOL 64) (tail : ProgHOL 64)
    (hp : P1State txDone n xs hasSnd entry s)
    (hne_st : ∀ k ∈ PtxP1.stageNames n, ofString k ≠ ofString name)
    (hne_xs : ∀ x ∈ xs, ofString x.1 ≠ ofString name)
    (hne_tx : ofString "tx" ≠ ofString name)
    (hne_idx : ofString "index" ≠ ofString name)
    (hne_snd : ofString "sender" ≠ ofString name)
    (htail : ∀ v : ValueHOL 64, evalAt s e = some v → shapeOfHOLExact v = sh →
      P1State txDone n xs hasSnd entry (setVarHOLFinite (ofString name) v s) →
      PtxRelRunStrong entry tail (setVarHOLFinite (ofString name) v s)) :
    PtxRelRunStrong entry (.dec (ofString name) sh e tail) s := by
  refine ptxRelRunStrong_dec (ofString name) sh e tail (fun v hev hsh => ?_)
  have hp' : P1State txDone n xs hasSnd entry (setVarHOLFinite (ofString name) v s) := by
    refine ⟨ptxRelBase_with_locals hp.base (s.locals.update (ofString name, v)) s.clock,
      LocalsOnly.setVar (PtxP1.localsOnly_stage n) hne_st v s hp.stage,
      ptxLocalShapeMap_resume s s hp.shapes name v hne_xs,
      hp.expw, hp.gamma,
      by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm hne_tx, hp.tx_eq],
      by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm hne_idx, hp.idx_eq],
      fun hh => senderTxOwned_setVar (Ne.symm hne_tx) (Ne.symm hne_snd) (hp.snd_own hh)⟩
  exact htail v hev hsh hp'

theorem p1_decCall_ro_add {F : Type} {txDone : Bool} {n : Nat}
    {xs : List (String × ShapeHOL)} {hasSnd : Bool}
    {entry s : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode)
    (name : String) (sh : ShapeHOL) (fname : MlS) (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (hro : ReadOnlyFn fname)
    (hp : P1State txDone n xs hasSnd entry s)
    (hne_st : ∀ k ∈ PtxP1.stageNames n, ofString k ≠ ofString name)
    (hne_xs : ∀ x ∈ xs, ofString x.1 ≠ ofString name)
    (hne_tx : ofString "tx" ≠ ofString name)
    (hne_idx : ofString "index" ≠ ofString name)
    (hne_snd : ofString "sender" ≠ ofString name)
    (htail : ∀ (vs : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
      (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs →
      lookupCodeHOLFinite s.code.lookup fname vs = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      shapeOfHOLExact v = sh →
      P1State txDone n ((name, sh) :: xs) hasSnd entry
        (setVarHOLFinite (ofString name) v { post with locals := s.locals }) →
      (setVarHOLFinite (ofString name) v { post with locals := s.locals }).code = originalRuntimeCode →
      PtxRelRunStrong entry tail (setVarHOLFinite (ofString name) v { post with locals := s.locals })) :
    PtxRelRunStrong entry (.decCall (ofString name) sh fname args tail) s := by
  refine ptxRelRunStrong_decCall_ro hp.base hc (ofString name) sh fname args tail hro
    (fun vs body callee ret v post ha hl hb hsh hro_eq => ?_)
  have hpost_eq : ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F) =
      { s with locals := s.locals, clock := post.clock } := by rw [hro_eq]; rfl
  have hp0 : P1State txDone n xs hasSnd entry { post with locals := s.locals } := by
    rw [hpost_eq]
    exact p1State_with_locals hp s.locals post.clock
      (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl (fun _ => rfl)
  have hp' : P1State txDone n ((name, sh) :: xs) hasSnd entry
      (setVarHOLFinite (ofString name) v { post with locals := s.locals }) := by
    refine ⟨ptxRelBase_with_locals hp0.base (s.locals.update (ofString name, v)) post.clock,
      LocalsOnly.setVar (PtxP1.localsOnly_stage n) hne_st v _ hp0.stage,
      ptxLocalShapeMap_add s post hp.shapes name sh v hne_xs hsh,
      hp0.expw, hp0.gamma,
      ?_, ?_,
      fun hh => senderTxOwned_setVar (Ne.symm hne_tx) (Ne.symm hne_snd) (hp0.snd_own hh)⟩
    · simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        beq_false_of_ne (Ne.symm hne_tx), Bool.false_eq_true, ↓reduceIte]
      exact hp.tx_eq
    · simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        beq_false_of_ne (Ne.symm hne_idx), Bool.false_eq_true, ↓reduceIte]
      exact hp.idx_eq
  have hcode' : (setVarHOLFinite (ofString name) v { post with locals := s.locals }).code =
      originalRuntimeCode := by change post.code = _; rw [hro_eq]; exact hc
  exact htail vs body callee ret v post ha hl hb hsh hp' hcode'

theorem p1_decCall_ro_keep {F : Type} {txDone : Bool} {n : Nat}
    {xs : List (String × ShapeHOL)} {hasSnd : Bool}
    {entry s : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode)
    (name : String) (sh : ShapeHOL) (fname : MlS) (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (hro : ReadOnlyFn fname)
    (hp : P1State txDone n xs hasSnd entry s)
    (hne_st : ∀ k ∈ PtxP1.stageNames n, ofString k ≠ ofString name)
    (hne_xs : ∀ x ∈ xs, ofString x.1 ≠ ofString name)
    (hne_tx : ofString "tx" ≠ ofString name)
    (hne_idx : ofString "index" ≠ ofString name)
    (hne_snd : ofString "sender" ≠ ofString name)
    (htail : ∀ (vs : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
      (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs →
      lookupCodeHOLFinite s.code.lookup fname vs = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      shapeOfHOLExact v = sh →
      P1State txDone n xs hasSnd entry
        (setVarHOLFinite (ofString name) v { post with locals := s.locals }) →
      (setVarHOLFinite (ofString name) v { post with locals := s.locals }).code = originalRuntimeCode →
      PtxRelRunStrong entry tail (setVarHOLFinite (ofString name) v { post with locals := s.locals })) :
    PtxRelRunStrong entry (.decCall (ofString name) sh fname args tail) s := by
  refine ptxRelRunStrong_decCall_ro hp.base hc (ofString name) sh fname args tail hro
    (fun vs body callee ret v post ha hl hb hsh hro_eq => ?_)
  have hpost_eq : ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F) =
      { s with locals := s.locals, clock := post.clock } := by rw [hro_eq]; rfl
  have hp0 : P1State txDone n xs hasSnd entry { post with locals := s.locals } := by
    rw [hpost_eq]
    exact p1State_with_locals hp s.locals post.clock
      (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl (fun _ => rfl)
  have hp' : P1State txDone n xs hasSnd entry
      (setVarHOLFinite (ofString name) v { post with locals := s.locals }) := by
    refine ⟨ptxRelBase_with_locals hp0.base (s.locals.update (ofString name, v)) post.clock,
      LocalsOnly.setVar (PtxP1.localsOnly_stage n) hne_st v _ hp0.stage,
      ptxLocalShapeMap_resume s post hp.shapes name v hne_xs,
      hp0.expw, hp0.gamma,
      ?_, ?_,
      fun hh => senderTxOwned_setVar (Ne.symm hne_tx) (Ne.symm hne_snd) (hp0.snd_own hh)⟩
    · simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        beq_false_of_ne (Ne.symm hne_tx), Bool.false_eq_true, ↓reduceIte]
      exact hp.tx_eq
    · simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        beq_false_of_ne (Ne.symm hne_idx), Bool.false_eq_true, ↓reduceIte]
      exact hp.idx_eq
  have hcode' : (setVarHOLFinite (ofString name) v { post with locals := s.locals }).code =
      originalRuntimeCode := by change post.code = _; rw [hro_eq]; exact hc
  exact htail vs body callee ret v post ha hl hb hsh hp' hcode'

theorem p1_decCall_scBo_add {F : Type} {txDone : Bool} {n : Nat}
    {xs : List (String × ShapeHOL)}
    {B : BufList} {gw : List String} {keep : List (String × List Nat)} {boKeep : List Nat}
    {gs : List (String × Nat × Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {entry s : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode)
    (hp : P1State txDone n xs true entry s)
    (hn_pos : 0 < n)
    (hB : ValidBufList B)
    (hBsub : ∀ p ∈ B, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals)
    (hgw : ∀ g ∈ gw, g ∈ ptxGlobals)
    (hfmp_gw : ofString "frame_mem_ptr" ∉ gw.map ofString)
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hjcap_gw : ofString "journal_cap" ∉ gw.map ofString)
    (hexpw_gw : ofString "bn_expw" ∉ gw.map ofString)
    (hgamma_gw : ofString "bn_gamma" ∉ gw.map ofString)
    (hkeep : PtxKeepSub keep)
    (hbo_keep_or : ("bo", [24, 32, 40, 56, 64, 72, 80]) ∈ keep ∨
      ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) ∈ keep)
    (hgs : PtxP1.ScratchSpec gs)
    (hR : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F),
      bufRegions B t = gs.map (fun e => bufferRegion t (e.1, e.2.2)))
    (hbo_keep : ("bo", boKeep) ∈ keep)
    (hoffs : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat), k ∈ boKeep)
    (name : String) (sh : ShapeHOL) (fname : MlS) (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (hwk : WorldKeepsScBo WorldOK (bufRegions B) gw keep Q fname)
    (hne_st : ∀ k ∈ PtxP1.stageNames n, ofString k ≠ ofString name)
    (hne_xs : ∀ x ∈ xs, ofString x.1 ≠ ofString name)
    (hne_tx : ofString "tx" ≠ ofString name)
    (hne_idx : ofString "index" ≠ ofString name)
    (hne_snd : ofString "sender" ≠ ofString name)
    (htail : ∀ (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      P1State txDone n ((name, sh) :: xs) true entry
        (setVarHOLFinite (ofString name) v { post with locals := s.locals }) →
      (setVarHOLFinite (ofString name) v { post with locals := s.locals }).code = originalRuntimeCode →
      PtxRelRunStrong entry tail (setVarHOLFinite (ofString name) v { post with locals := s.locals })) :
    PtxRelRunStrong entry (.decCall (ofString name) sh fname args tail) s := by
  refine ptxRelRunStrong_decCall_scBo hp.base hc hB hBsub hgw hfmp_gw hbo_gw hkeep hbo_keep_or
    (ofString name) sh fname args tail hwk (fun vs body callee ret v post _ _ _ hsh hstep hbase_res hpc => ?_)
  have hstep_s : WorldStep (bufRegions B) gw keep NoExtra s (some (.returned v)) post :=
    R13Shards.worldStep_with_locals hstep s.locals s.clock
  have hst0 : PtxP1.StageP n { post with locals := s.locals } :=
    PtxP1.stage_after_scratchStep hstep hp.stage hgs (hR s) hbo_gw hjcap_gw hbo_keep hoffs
  have hst' := LocalsOnly.setVar (PtxP1.localsOnly_stage n) hne_st v _ hst0
  have hown0 := senderTxOwned_scratchStep hB hp.base.world.1 (hp.stage.2.1 hn_pos).1
    (hp.snd_own rfl) hstep_s
  have hexpw' : globN post "bn_expw" = globN entry "bn_expw" :=
    (globN_eq_of_lookup (hstep_s.2.2.1 _ hexpw_gw)).trans hp.expw
  have hgamma' : globN post "bn_gamma" = globN entry "bn_gamma" :=
    (globN_eq_of_lookup (hstep_s.2.2.1 _ hgamma_gw)).trans hp.gamma
  have hp' : P1State txDone n ((name, sh) :: xs) true entry
      (setVarHOLFinite (ofString name) v { post with locals := s.locals }) :=
    ⟨hbase_res, hst', ptxLocalShapeMap_add s post hp.shapes name sh v hne_xs hsh,
      hexpw', hgamma',
      by simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          beq_false_of_ne (Ne.symm hne_tx), Bool.false_eq_true, ↓reduceIte]; exact hp.tx_eq,
      by simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          beq_false_of_ne (Ne.symm hne_idx), Bool.false_eq_true, ↓reduceIte]; exact hp.idx_eq,
      fun _ => senderTxOwned_setVar (Ne.symm hne_tx) (Ne.symm hne_snd) hown0⟩
  exact htail v post hp' hpc

theorem p1_decCall_scBo_keep {F : Type} {txDone : Bool} {n : Nat}
    {xs : List (String × ShapeHOL)}
    {B : BufList} {gw : List String} {keep : List (String × List Nat)} {boKeep : List Nat}
    {gs : List (String × Nat × Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {entry s : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode)
    (hp : P1State txDone n xs true entry s)
    (hn_pos : 0 < n)
    (hB : ValidBufList B)
    (hBsub : ∀ p ∈ B, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals)
    (hgw : ∀ g ∈ gw, g ∈ ptxGlobals)
    (hfmp_gw : ofString "frame_mem_ptr" ∉ gw.map ofString)
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hjcap_gw : ofString "journal_cap" ∉ gw.map ofString)
    (hexpw_gw : ofString "bn_expw" ∉ gw.map ofString)
    (hgamma_gw : ofString "bn_gamma" ∉ gw.map ofString)
    (hkeep : PtxKeepSub keep)
    (hbo_keep_or : ("bo", [24, 32, 40, 56, 64, 72, 80]) ∈ keep ∨
      ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) ∈ keep)
    (hgs : PtxP1.ScratchSpec gs)
    (hR : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F),
      bufRegions B t = gs.map (fun e => bufferRegion t (e.1, e.2.2)))
    (hbo_keep : ("bo", boKeep) ∈ keep)
    (hoffs : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat), k ∈ boKeep)
    (name : String) (sh : ShapeHOL) (fname : MlS) (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (hwk : WorldKeepsScBo WorldOK (bufRegions B) gw keep Q fname)
    (hne_st : ∀ k ∈ PtxP1.stageNames n, ofString k ≠ ofString name)
    (hne_xs : ∀ x ∈ xs, ofString x.1 ≠ ofString name)
    (hne_tx : ofString "tx" ≠ ofString name)
    (hne_idx : ofString "index" ≠ ofString name)
    (hne_snd : ofString "sender" ≠ ofString name)
    (htail : ∀ (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      P1State txDone n xs true entry
        (setVarHOLFinite (ofString name) v { post with locals := s.locals }) →
      (setVarHOLFinite (ofString name) v { post with locals := s.locals }).code = originalRuntimeCode →
      PtxRelRunStrong entry tail (setVarHOLFinite (ofString name) v { post with locals := s.locals })) :
    PtxRelRunStrong entry (.decCall (ofString name) sh fname args tail) s := by
  refine ptxRelRunStrong_decCall_scBo hp.base hc hB hBsub hgw hfmp_gw hbo_gw hkeep hbo_keep_or
    (ofString name) sh fname args tail hwk (fun vs body callee ret v post _ _ _ _ hstep hbase_res hpc => ?_)
  have hstep_s : WorldStep (bufRegions B) gw keep NoExtra s (some (.returned v)) post :=
    R13Shards.worldStep_with_locals hstep s.locals s.clock
  have hst0 : PtxP1.StageP n { post with locals := s.locals } :=
    PtxP1.stage_after_scratchStep hstep hp.stage hgs (hR s) hbo_gw hjcap_gw hbo_keep hoffs
  have hst' := LocalsOnly.setVar (PtxP1.localsOnly_stage n) hne_st v _ hst0
  have hown0 := senderTxOwned_scratchStep hB hp.base.world.1 (hp.stage.2.1 hn_pos).1
    (hp.snd_own rfl) hstep_s
  have hexpw' : globN post "bn_expw" = globN entry "bn_expw" :=
    (globN_eq_of_lookup (hstep_s.2.2.1 _ hexpw_gw)).trans hp.expw
  have hgamma' : globN post "bn_gamma" = globN entry "bn_gamma" :=
    (globN_eq_of_lookup (hstep_s.2.2.1 _ hgamma_gw)).trans hp.gamma
  have hp' : P1State txDone n xs true entry
      (setVarHOLFinite (ofString name) v { post with locals := s.locals }) :=
    ⟨hbase_res, hst', ptxLocalShapeMap_resume s post hp.shapes name v hne_xs,
      hexpw', hgamma',
      by simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          beq_false_of_ne (Ne.symm hne_tx), Bool.false_eq_true, ↓reduceIte]; exact hp.tx_eq,
      by simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          beq_false_of_ne (Ne.symm hne_idx), Bool.false_eq_true, ↓reduceIte]; exact hp.idx_eq,
      fun _ => senderTxOwned_setVar (Ne.symm hne_tx) (Ne.symm hne_snd) hown0⟩
  exact htail v post hp' hpc

theorem p1_call0_scBo {F : Type} {txDone : Bool} {n : Nat}
    {xs : List (String × ShapeHOL)}
    {B : BufList} {gw : List String} {keep : List (String × List Nat)} {boKeep : List Nat}
    {gs : List (String × Nat × Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {entry s : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode)
    (hp : P1State txDone n xs true entry s)
    (hn_pos : 0 < n)
    (hB : ValidBufList B)
    (hBsub : ∀ p ∈ B, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals)
    (hgw : ∀ g ∈ gw, g ∈ ptxGlobals)
    (hfmp_gw : ofString "frame_mem_ptr" ∉ gw.map ofString)
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hjcap_gw : ofString "journal_cap" ∉ gw.map ofString)
    (hexpw_gw : ofString "bn_expw" ∉ gw.map ofString)
    (hgamma_gw : ofString "bn_gamma" ∉ gw.map ofString)
    (hkeep : PtxKeepSub keep)
    (hbo_keep_or : ("bo", [24, 32, 40, 56, 64, 72, 80]) ∈ keep ∨
      ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) ∈ keep)
    (hgs : PtxP1.ScratchSpec gs)
    (hR : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F),
      bufRegions B t = gs.map (fun e => bufferRegion t (e.1, e.2.2)))
    (hbo_keep : ("bo", boKeep) ∈ keep)
    (hoffs : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat), k ∈ boKeep)
    (fname : MlS) (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (hwk : WorldKeepsScBo WorldOK (bufRegions B) gw keep Q fname)
    (htail : ∀ (post : PanSemStateFiniteExact 64 F),
      P1State txDone n xs true entry { post with locals := s.locals } →
      ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F).code = originalRuntimeCode →
      PtxRelRunStrong entry tail { post with locals := s.locals }) :
    PtxRelRunStrong entry (.seq (.call (some (none, none)) fname args) tail) s := by
  refine ptxRelRunStrong_call0_scBo hp.base hc hB hBsub hgw hfmp_gw hbo_gw hkeep hbo_keep_or
    fname args tail hwk (fun vs body callee ret v post _ _ _ hstep _ hbase_res hpc => ?_)
  have hstep_s : WorldStep (bufRegions B) gw keep NoExtra s (some (.returned v)) post :=
    R13Shards.worldStep_with_locals hstep s.locals s.clock
  have hst0 : PtxP1.StageP n { post with locals := s.locals } :=
    PtxP1.stage_after_scratchStep hstep hp.stage hgs (hR s) hbo_gw hjcap_gw hbo_keep hoffs
  have hown0 := senderTxOwned_scratchStep hB hp.base.world.1 (hp.stage.2.1 hn_pos).1
    (hp.snd_own rfl) hstep_s
  have hexpw' : globN post "bn_expw" = globN entry "bn_expw" :=
    (globN_eq_of_lookup (hstep_s.2.2.1 _ hexpw_gw)).trans hp.expw
  have hgamma' : globN post "bn_gamma" = globN entry "bn_gamma" :=
    (globN_eq_of_lookup (hstep_s.2.2.1 _ hgamma_gw)).trans hp.gamma
  have hp' : P1State txDone n xs true entry { post with locals := s.locals } :=
    ⟨hbase_res, hst0, phase1_map_localsOnly xs s s.locals post.clock (fun _ _ => rfl) hp.shapes,
      hexpw', hgamma', hp.tx_eq, hp.idx_eq, fun _ => hown0⟩
  exact htail post hp' hpc

theorem p1_callLocal_ro_keep {F : Type} {txDone : Bool} {n : Nat}
    {xs : List (String × ShapeHOL)} {hasSnd : Bool}
    {entry s : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode)
    (name : String) (fname : MlS) (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (hro : ReadOnlyFn fname)
    (hp : P1State txDone n xs hasSnd entry s)
    (hne_st : ∀ k ∈ PtxP1.stageNames n, ofString k ≠ ofString name)
    (hne_xs : ∀ x ∈ xs, ofString x.1 ≠ ofString name)
    (hne_tx : ofString "tx" ≠ ofString name)
    (hne_idx : ofString "index" ≠ ofString name)
    (hne_snd : ofString "sender" ≠ ofString name)
    (htail : ∀ (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      P1State txDone n xs hasSnd entry
        (setKvarHOLFinite .local (ofString name) v { post with locals := s.locals }) →
      (setKvarHOLFinite .local (ofString name) v { post with locals := s.locals }).code =
        originalRuntimeCode →
      PtxRelRunStrong entry tail
        (setKvarHOLFinite .local (ofString name) v { post with locals := s.locals })) :
    PtxRelRunStrong entry (.seq (.call (some (some (.local, ofString name), none)) fname args) tail) s := by
  refine ptxRelRunStrong_callLocal_ro hp.base hc (ofString name) fname args tail hro
    (fun _ _ callee _ v post _ _ _ _ hro_eq => ?_)
  have hpost_eq : ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F) =
      { s with locals := s.locals, clock := post.clock } := by rw [hro_eq]; rfl
  have hp0 : P1State txDone n xs hasSnd entry { post with locals := s.locals } := by
    rw [hpost_eq]
    exact p1State_with_locals hp s.locals post.clock
      (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl (fun _ => rfl)
  have hset_eq : setKvarHOLFinite .local (ofString name) v { post with locals := s.locals } =
      setVarHOLFinite (ofString name) v { post with locals := s.locals } := rfl
  have hp' : P1State txDone n xs hasSnd entry
      (setKvarHOLFinite .local (ofString name) v { post with locals := s.locals }) := by
    rw [hset_eq]
    refine ⟨ptxRelBase_with_locals hp0.base (s.locals.update (ofString name, v)) post.clock,
      LocalsOnly.setVar (PtxP1.localsOnly_stage n) hne_st v _ hp0.stage,
      ptxLocalShapeMap_resume s post hp.shapes name v hne_xs,
      hp0.expw, hp0.gamma, ?_, ?_,
      fun hh => senderTxOwned_setVar (Ne.symm hne_tx) (Ne.symm hne_snd) (hp0.snd_own hh)⟩
    · simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        beq_false_of_ne (Ne.symm hne_tx), Bool.false_eq_true, ↓reduceIte]
      exact hp.tx_eq
    · simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        beq_false_of_ne (Ne.symm hne_idx), Bool.false_eq_true, ↓reduceIte]
      exact hp.idx_eq
  have hcode' : (setKvarHOLFinite .local (ofString name) v { post with locals := s.locals }).code =
      originalRuntimeCode := by change post.code = _; rw [hro_eq]; exact hc
  exact htail v post hp' hcode'

theorem p1_ite_skip {F : Type} {txDone : Bool} {n : Nat}
    {xs : List (String × ShapeHOL)} {hasSnd : Bool}
    {entry s : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode)
    (hp : P1State txDone n xs hasSnd entry s)
    (cond : ExpHOL 64) (thn tail : ProgHOL 64)
    (hthn : PtxRelRunStrong entry (.seq thn tail) s)
    (htail : P1State txDone n xs hasSnd entry s → s.code = originalRuntimeCode →
      PtxRelRunStrong entry tail s) :
    PtxRelRunStrong entry (.seq (.ite cond thn .skip) tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres ⊢
  rcases hcv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | vc
  · simp [hcv] at hres; exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [hcv] at hres ⊢
    rcases vc with ⟨⟨wc⟩⟩ | _ | _
    · simp only [valueIsWord, ↓reduceIte, valueWord, evaluateHOLFiniteState_skip] at hres ⊢
      by_cases hwz : wc = 0
      · rw [if_pos hwz] at hres ⊢
        exact htail hp hc hres
      · rw [if_neg hwz] at hres ⊢
        have hthn' := hthn
        unfold PtxRelRunStrong at hthn'
        rw [evaluateHOLFiniteState_seq_line780] at hthn'
        exact hthn' hres
    · simp [valueIsWord] at hres; exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp [valueIsWord] at hres; exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

theorem p1_chainGuard {F : Type} {xs : List (String × ShapeHOL)}
    {entry s : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode)
    (hp : P1State true 0 xs false entry s)
    {tail : ProgHOL 64}
    (htail : P1State true 0 xs false entry s → s.code = originalRuntimeCode →
      PtxRelRunStrong entry tail s) :
    PtxRelRunStrong entry (.seq PtxP1.chainGuard tail) s := by
  refine p1_ite_skip hc hp _ _ tail ?_ htail
  refine p1_ite_skip hc hp _ _ tail ?_ htail
  intro hres
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_raise] at hres ⊢
  rcases hes : s.eshapes.lookup (ofString "BlockErr") with _ | esh
  · simp [hes] at hres; exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · have he100 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const 100) =
        some (.val (.word 100#64)) := rfl
    simp only [hes, he100] at hres ⊢
    by_cases hcond : shapeOfHOLExact (ValueHOL.val (HolWordLab.word 100#64)) = esh ∧
        sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact (ValueHOL.val (HolWordLab.word 100#64))) ≤ 32
    · rw [if_pos hcond] at hres ⊢
      dsimp only at hres ⊢
      exact ptx_id_exception_step hp.base s.clock
    · rw [if_neg hcond] at hres ⊢
      dsimp only at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h)

theorem p1_decCall_seq_scBo {F : Type} {txDone : Bool}
    {B : BufList} {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {entry s : PanSemStateFiniteExact 64 F}
    (hbase : PtxRelBase txDone entry s)
    (hc : s.code = originalRuntimeCode)
    (hB : ValidBufList B)
    (hBsub : ∀ p ∈ B, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals)
    (hgw : ∀ g ∈ gw, g ∈ ptxGlobals)
    (hfmp_gw : ofString "frame_mem_ptr" ∉ gw.map ofString)
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hkeep : PtxKeepSub keep)
    (hbo_keep : ("bo", [24, 32, 40, 56, 64, 72, 80]) ∈ keep ∨
      ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) ∈ keep)
    (name : MlS) (sh : ShapeHOL) (fname : MlS) (args : List (ExpHOL 64))
    (cont tail : ProgHOL 64)
    (hno : noReturnProg cont = true)
    (hwk : WorldKeepsScBo WorldOK (bufRegions B) gw keep Q fname)
    (hcont : ∀ (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      WorldStep (bufRegions B) gw keep Q (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      PtxRelBase txDone entry (setVarHOLFinite name v { post with locals := s.locals }) →
      (setVarHOLFinite name v { post with locals := s.locals }).code = originalRuntimeCode →
      (∀ eid ev mid,
        evaluateHOLFiniteState (setVarHOLFinite name v { post with locals := s.locals }) cont =
          (some (.exception eid ev), mid) →
        eid ≠ ofString "TrapErr" →
        WorldStep ptxRegions ptxGlobals ptxKeep PtxLogsAndSlices entry (some (.exception eid ev)) mid) ∧
      (∀ mid,
        evaluateHOLFiniteState (setVarHOLFinite name v { post with locals := s.locals }) cont = (none, mid) →
        PtxRelRunStrong entry tail
          { mid with locals := HolFiniteMapExact.resVarEq mid.locals (name, s.locals.lookup name) })) :
    PtxRelRunStrong entry (.seq (.decCall name sh fname args cont) tail) s := by
  intro hres
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_decCall_fixClockRewrite] at hres ⊢
  rcases ha : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, ha] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [evalListHOLFinite, ha] at hres ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body, callee, ret⟩
    · simp only [hl] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hl] at hres ⊢
      by_cases hcz : s.clock = 0
      · simp only [hcz, ↓reduceIte] at hres
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      · simp only [hcz, ↓reduceIte] at hres ⊢
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r1, post⟩
        have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r1, post) := hb
        rw [hb] at hmeta
        simp only [hb] at hres ⊢
        cases r1 with
        | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | some cr1 =>
          cases cr1 with
          | timeOut | error | «break» | «continue» | finalFfi _ =>
            exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | exception eid ev =>
            dsimp only at hres ⊢
            have hne : eid ≠ ofString "TrapErr" := by
              rcases hres with ⟨_, h⟩ | ⟨_, _, h, hne⟩
              · cases h
              · injection h with h'; injection h' with he _; exact he ▸ hne
            have hspec := hwk.at_lookup s hc vs body callee ret hl
              (localsFree_worldOK s callee (s.clock - 1) hbase.world) (by rw [hb']; simp)
            rw [hb'] at hspec
            have hstep_s := R13Shards.worldStep_with_locals
              (hspec (Or.inr ⟨eid, ev, rfl, hne⟩)).1.1 s.locals s.clock
            have hex := ptxRelBase_exception_worldStep hbase hB hBsub hgw hkeep hstep_s
            exact ptxWorldStep_strong_with_locals_right .empty post.clock hex
          | returned rv =>
            dsimp only at hres ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact rv) sh && shapeEqHOL (shapeOfHOLExact rv) ret) = true
            · simp only [hsh, ↓reduceIte] at hres ⊢
              have hspec := hwk.at_lookup s hc vs body callee ret hl
                (localsFree_worldOK s callee (s.clock - 1) hbase.world) (by rw [hb']; simp)
              rw [hb'] at hspec
              have hsc := hspec (Or.inl ⟨rv, rfl⟩)
              have hstep_s := R13Shards.worldStep_with_locals hsc.1.1 s.locals s.clock
              have hfmp_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" :=
                globN_eq_of_lookup (hstep_s.2.2.1 _ hfmp_gw)
              have hbase_post : PtxRelBase txDone entry post :=
                ptxRelBase_step_of_blockOutUnhit hbase hB hBsub hgw hkeep hbo_gw hbo_keep
                  hstep_s hsc.1.2 (by omega) (hsc.2 (Or.inr (Or.inr (Or.inr ⟨rv, rfl⟩))))
              have hbase_res : PtxRelBase txDone entry (setVarHOLFinite name rv { post with locals := s.locals }) :=
                ptxRelBase_with_locals hbase_post (s.locals.update (name, rv)) post.clock
              have hpc : (setVarHOLFinite name rv { post with locals := s.locals }).code = originalRuntimeCode :=
                hmeta.trans hc
              have ⟨hexc_c, hfall_c⟩ := hcont callee rv post hsc.1.1 hbase_res hpc
              set s1 := setVarHOLFinite name rv { post with locals := s.locals }
              have hnr := evaluate_noReturnProg cont hno s1
              rcases hc_ev : evaluateHOLFiniteState s1 cont with ⟨rc, mid⟩
              have hc_ev' : evaluateHOLFiniteState s1 cont = (rc, mid) := hc_ev
              simp only [hc_ev] at hres ⊢
              cases rc with
              | none => exact hfall_c mid hc_ev' hres
              | some crc =>
                cases crc with
                | timeOut | error | «break» | «continue» | finalFfi _ =>
                  exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                | returned vc =>
                  exact absurd rfl (by have h1 := hnr vc; rw [hc_ev'] at h1; exact h1)
                | exception ec vc =>
                  have hne_c : ec ≠ ofString "TrapErr" := by
                    rcases hres with ⟨_, h⟩ | ⟨_, _, h, hne⟩
                    · cases h
                    · injection h with h'; injection h' with he _; exact he ▸ hne
                  exact ptxWorldStep_strong_with_locals_right
                    (HolFiniteMapExact.resVarEq mid.locals (name, s.locals.lookup name))
                    mid.clock (hexc_c ec vc mid hc_ev' hne_c)
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hres
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

theorem p1_blobBranch {F : Type} {xs : List (String × ShapeHOL)}
    {entry s : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode)
    (hp : P1State true 2 xs true entry s)
    (hne_bgp : ∀ x ∈ xs, ofString x.1 ≠ ofString "bgp")
    (hne_bgf : ∀ x ∈ xs, ofString x.1 ≠ ofString "bgf")
    (hne_bgfee : ∀ x ∈ xs, ofString x.1 ≠ ofString "blob_gas_fee")
    {tail : ProgHOL 64}
    (htail : ∀ s', P1State true 2 xs true entry s' → s'.code = originalRuntimeCode →
      PtxRelRunStrong entry tail s') :
    PtxRelRunStrong entry (.seq (.ite
      (.cmp .notEqual (.var .local (ofString "tx_blob_gas_used")) (.const 0))
      PtxP1.blobBranch .skip) tail) s := by
  refine p1_ite_skip hc hp _ _ tail ?_ (fun hp0 hc0 => htail s hp0 hc0)
  unfold PtxP1.blobBranch
  have hB1 : ValidBufList [("u256_ws", 640)] := by
    intro p hp0; cases p; simp at hp0; rcases hp0 with ⟨rfl, rfl⟩
    exact ⟨640, by decide, by decide, le_rfl⟩
  have hBsub1 : ∀ p ∈ ([("u256_ws", 640)] : BufList), p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals := by
    intro p hp0; cases p; simp at hp0; rcases hp0 with ⟨rfl, rfl⟩; exact ⟨by decide, by decide⟩
  refine p1_decCall_seq_scBo hp.base hc hB1 hBsub1 (by intro g hg; cases hg) (by decide) (by decide)
    ptxKeepSub_stdKeep (Or.inr (by simp [stdKeep]))
    (ofString "bgp") (.comb [.one, .one, .one, .one]) (ofString "calculate_blob_gas_price")
    [.load .one (.op .add [.var .global (ofString "be"), .const 96])] _ tail
    (by unfold noReturnProg; decide) wkScBo_calculate_blob_gas_price ?_
  intro cal1 rv1 p1 hstep1_e hbase1 hc1
  have hstep1_s : WorldStep (bufRegions [("u256_ws", 640)]) [] stdKeep NoExtra s (some (.returned rv1)) p1 :=
    R13Shards.worldStep_with_locals hstep1_e s.locals s.clock
  have hst1_0 : PtxP1.StageP 2 { p1 with locals := s.locals } :=
    PtxP1.stage_after_scratchStep hstep1_e hp.stage
      (gs := [("u256_ws", 640, 640)]) (by unfold PtxP1.ScratchSpec; decide)
      rfl (by decide) (by decide)
      (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp [stdKeep]) (by decide)
  have hown1_0 := senderTxOwned_scratchStep hB1 hp.base.world.1 (hp.stage.2.1 (by omega)).1
    (hp.snd_own rfl) hstep1_s
  have hexpw1 : globN p1 "bn_expw" = globN entry "bn_expw" :=
    (globN_eq_of_lookup (hstep1_s.2.2.1 _ (by decide))).trans hp.expw
  have hgamma1 : globN p1 "bn_gamma" = globN entry "bn_gamma" :=
    (globN_eq_of_lookup (hstep1_s.2.2.1 _ (by decide))).trans hp.gamma
  set s1 := setVarHOLFinite (ofString "bgp") rv1 { p1 with locals := s.locals }
  have hp1 : P1State true 2 xs true entry s1 :=
    ⟨hbase1,
      LocalsOnly.setVar (PtxP1.localsOnly_stage 2) (by decide) rv1 _ hst1_0,
      ptxLocalShapeMap_resume s p1 hp.shapes "bgp" rv1 hne_bgp,
      hexpw1, hgamma1,
      by simp only [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show (ofString "bgp" == ofString "tx") = false by decide, Bool.false_eq_true, ↓reduceIte]; exact hp.tx_eq,
      by simp only [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show (ofString "bgp" == ofString "index") = false by decide, Bool.false_eq_true, ↓reduceIte]; exact hp.idx_eq,
      fun _ => senderTxOwned_setVar (by decide) (by decide) hown1_0⟩
  constructor
  · intro eid ev mid hbp hne
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hbp
    rcases ha2 : @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        [.var .local (ofString "tx_blob_gas_used"), .var .local (ofString "bgp")] with _ | vs2
    · simp [evalListHOLFinite, ha2] at hbp
    · simp only [evalListHOLFinite, ha2] at hbp
      rcases hl2 : lookupCodeHOLFinite s1.code.lookup (ofString "fee_mul") vs2 with _ | ⟨b2, cal2, ret2⟩
      · simp [hl2] at hbp
      · simp only [hl2] at hbp
        by_cases hcz2 : s1.clock = 0
        · simp [hcz2] at hbp
        · simp only [hcz2, ↓reduceIte] at hbp
          rcases hb2 : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal2) b2 with ⟨r2, p2⟩
          have hb2' : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal2) b2 = (r2, p2) := hb2
          simp only [hb2] at hbp
          cases r2 with
          | none => simp at hbp
          | some cr2 =>
            cases cr2 with
            | timeOut | error | «break» | «continue» | finalFfi _ => simp at hbp
            | exception e2 v2 =>
              dsimp only at hbp
              injection hbp with h1 h2; injection h1 with h1'; injection h1' with he hv
              have hspec2 := FunSpec.at_lookup ro_fee_mul s1 hc1 vs2 b2 cal2 ret2 hl2
                (guestInv_callEntry s1 cal2 hbase1.world.1.1) (by rw [hb2']; simp)
              have hro2 : p2 = { callEntryStateHOLFinite s1 cal2 with locals := p2.locals, clock := p2.clock } := by
                have h0 := hspec2 (by rw [hb2']; exact Or.inr ⟨e2, v2, rfl, he ▸ hne⟩)
                simpa [hb2'] using h0
              have hp2_eq : mid = { s1 with locals := .empty, clock := p2.clock } := by
                rw [← h2, hro2]; rfl
              rw [← he, ← hv, hp2_eq]
              exact ptx_id_exception_step hbase1 p2.clock
            | returned rv2 =>
              dsimp only at hbp
              split at hbp
              · set s2 := setVarHOLFinite (ofString "bgf") rv2 { p2 with locals := s1.locals }
                rcases ha_ev : evaluateHOLFiniteState s2
                    (.assign .local (ofString "blob_gas_fee")
                      (.rstruct [.rfield 1 (.var .local (ofString "bgf")), .rfield 2 (.var .local (ofString "bgf")),
                        .rfield 3 (.var .local (ofString "bgf")), .rfield 4 (.var .local (ofString "bgf"))])) with ⟨ra, pa⟩
                have ha_ev' : evaluateHOLFiniteState s2
                    (.assign .local (ofString "blob_gas_fee")
                      (.rstruct [.rfield 1 (.var .local (ofString "bgf")), .rfield 2 (.var .local (ofString "bgf")),
                        .rfield 3 (.var .local (ofString "bgf")), .rfield 4 (.var .local (ofString "bgf"))])) = (ra, pa) := ha_ev
                rw [ha_ev] at hbp
                injection hbp with h1 _
                have hnr_a : ra ≠ some (.exception eid ev) := by
                  rw [evaluateHOLFiniteState_assign] at ha_ev'
                  split at ha_ev'
                  · injection ha_ev' with hr _; rw [← hr]; simp
                  · split at ha_ev' <;> (injection ha_ev' with hr _; rw [← hr]; simp)
                exact absurd h1 hnr_a
              · simp at hbp
  · intro mid hbp
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hbp
    rcases ha2 : @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        [.var .local (ofString "tx_blob_gas_used"), .var .local (ofString "bgp")] with _ | vs2
    · simp [evalListHOLFinite, ha2] at hbp
    · simp only [evalListHOLFinite, ha2] at hbp
      rcases hl2 : lookupCodeHOLFinite s1.code.lookup (ofString "fee_mul") vs2 with _ | ⟨b2, cal2, ret2⟩
      · simp [hl2] at hbp
      · simp only [hl2] at hbp
        by_cases hcz2 : s1.clock = 0
        · simp [hcz2] at hbp
        · simp only [hcz2, ↓reduceIte] at hbp
          rcases hb2 : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal2) b2 with ⟨r2, p2⟩
          have hb2' : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal2) b2 = (r2, p2) := hb2
          simp only [hb2] at hbp
          cases r2 with
          | none => simp at hbp
          | some cr2 =>
            cases cr2 with
            | timeOut | error | «break» | «continue» | finalFfi _ | exception _ _ => simp at hbp
            | returned rv2 =>
              dsimp only at hbp
              split at hbp
              · have hspec2 := FunSpec.at_lookup ro_fee_mul s1 hc1 vs2 b2 cal2 ret2 hl2
                  (guestInv_callEntry s1 cal2 hbase1.world.1.1) (by rw [hb2']; simp)
                have hro2 : p2 = { callEntryStateHOLFinite s1 cal2 with locals := p2.locals, clock := p2.clock } := by
                  have h0 := hspec2 (by rw [hb2']; exact Or.inl ⟨rv2, rfl⟩)
                  simpa [hb2'] using h0
                set s2 := setVarHOLFinite (ofString "bgf") rv2 { p2 with locals := s1.locals }
                rcases ha_ev : evaluateHOLFiniteState s2
                    (.assign .local (ofString "blob_gas_fee")
                      (.rstruct [.rfield 1 (.var .local (ofString "bgf")), .rfield 2 (.var .local (ofString "bgf")),
                        .rfield 3 (.var .local (ofString "bgf")), .rfield 4 (.var .local (ofString "bgf"))])) with ⟨ra, pa⟩
                have ha_ev' : evaluateHOLFiniteState s2
                    (.assign .local (ofString "blob_gas_fee")
                      (.rstruct [.rfield 1 (.var .local (ofString "bgf")), .rfield 2 (.var .local (ofString "bgf")),
                        .rfield 3 (.var .local (ofString "bgf")), .rfield 4 (.var .local (ofString "bgf"))])) = (ra, pa) := ha_ev
                rw [ha_ev] at hbp
                injection hbp with hra hmid
                subst hra
                obtain ⟨v3, hv3_pa⟩ : ∃ v3, pa = setKvarHOLFinite .local (ofString "blob_gas_fee") v3 s2 := by
                  rw [evaluateHOLFiniteState_assign] at ha_ev'
                  split at ha_ev'
                  · simp at ha_ev'
                  · rename_i v3 _
                    split at ha_ev'
                    · injection ha_ev' with _ hpa; exact ⟨v3, hpa.symm⟩
                    · simp at ha_ev'
                subst hv3_pa
                set Lf := HolFiniteMapExact.resVarEq
                  (HolFiniteMapExact.resVarEq
                    (s2.locals.update (ofString "blob_gas_fee", v3))
                    (ofString "bgf", s1.locals.lookup (ofString "bgf")))
                  (ofString "bgp", s.locals.lookup (ofString "bgp"))
                have hfin_eq : ({ mid with
                    locals := HolFiniteMapExact.resVarEq mid.locals (ofString "bgp", s.locals.lookup (ofString "bgp")) } :
                    PanSemStateFiniteExact 64 F) =
                    { s1 with locals := Lf, clock := p2.clock } := by
                  rw [← hmid]
                  simp only [Lf, s2, setVarHOLFinite, setKvarHOLFinite]
                  rw [hro2]; rfl
                rw [hfin_eq]
                have hLf_other : ∀ k : String,
                    ofString k ≠ ofString "bgp" →
                    ofString k ≠ ofString "bgf" →
                    ofString k ≠ ofString "blob_gas_fee" →
                    Lf.lookup (ofString k) = s1.locals.lookup (ofString k) := by
                  intro k h1k h2k h3k
                  simp only [Lf, s2, setVarHOLFinite, PanRunBounded.resVarEq_lookup,
                    if_neg h1k, if_neg h2k, HolFiniteMapExact.lookup_update, FUPDATE,
                    beq_false_of_ne (Ne.symm h3k), beq_false_of_ne (Ne.symm h2k),
                    Bool.false_eq_true, ↓reduceIte]
                have hp_fin : P1State true 2 xs true entry { s1 with locals := Lf, clock := p2.clock } := by
                  refine p1State_with_locals hp1 Lf p2.clock ?_ ?_ ?_ ?_ ?_
                  · intro k hk
                    have hk4 : k = "tx" ∨ k = "index" ∨ k = "sender" ∨ k = "intrinsic" := by
                      simpa [PtxP1.stageNames] using hk
                    rcases hk4 with rfl | rfl | rfl | rfl <;>
                      exact hLf_other _ (by decide) (by decide) (by decide)
                  · intro x hx
                    exact hLf_other x.1 (hne_bgp x hx) (hne_bgf x hx) (hne_bgfee x hx)
                  · exact hLf_other "tx" (by decide) (by decide) (by decide)
                  · exact hLf_other "index" (by decide) (by decide) (by decide)
                  · intro _; exact hLf_other "sender" (by decide) (by decide) (by decide)
                exact htail _ hp_fin hc1
              · simp at hbp

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
