import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPmcMarksBo
import InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover.RecoverSender
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_tx_chain_id
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_validate_transaction
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_validate_transaction
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_min

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
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkBlockTxProcess

open private wordsOK_post_of_memaddrs txValidRecoverReadyAt_step_heap
  recover_sender_with_chain_id_body_heapByteEff
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover.RecoverSender

/-! # Phase 1 Leaf Specs & Relational Helpers (`WkPtxPhase1A`) -/

/-! ## 0. `progWStepBo_raise` & `wkScBo_get_code` -/

theorem progWStepBo_raise (B : BufList) (gw : List String) (eid : MlS) (e : ExpHOL 64) :
    ProgWStepBo B gw (.raise eid e) := by
  intro F s _ hW _ hfr
  rw [evaluateHOLFiniteState_raise] at hfr ⊢
  rcases hsh : s.eshapes.lookup eid with _ | sh
  · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hsh] at hfr ⊢
    rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | v
    · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hev] at hfr ⊢
      split
      · exact (WorldStepScBo.refl s none hW.1).with_locals_clock (fun _ => Or.inl rfl) _ s.clock
      · rename_i hbad; simp [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem wkScBo_get_code :
    WorldKeepsScBo WorldOK (bufRegions [("sk_buf", 52)]) ["heap_ptr"] stdKeep NoExtra
      (ofString "get_code") := by
  have hB : ValidBufList [("sk_buf", 52)] := by
    intro p hp; simp at hp; subst hp
    exact ⟨64, by decide, by decide, by decide⟩
  have hgw : SafeStepGlobals ["heap_ptr"] := by intro g hg; simp at hg; subst hg; simp
  refine worldKeepsScBo_of_progWStepBo lookup_get_code ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_get_code,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepBo_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsScBo_of_readOnly EvmFrameSpecs.ro_memeq) ?_
  refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_return _ _ _) (progWStepBo_skip _ _)) ?_
  refine progWStepBo_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsScBo_of_readOnly EvmFrameSpecs.ro_htab_get) ?_
  refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_return _ _ _) (progWStepBo_skip _ _)) ?_
  refine progWStepBo_seq hB hgw
    (progWStepBo_call_local (by intro p hp; cases hp) (by intro g hg; cases hg)
      (worldKeepsScBo_of_readOnly EvmFrameSpecs.ro_htab_get)) ?_
  refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_return _ _ _) (progWStepBo_skip _ _)) ?_
  refine progWStepBo_decCall hB hgw (by intro p hp; exact hp) (by intro g hg; cases hg)
    worldKeepsScBo_sk_make ?_
  refine progWStepBo_seq hB hgw
    (progWStepBo_call0_htab_set_recSlot "ts" "ts+40" 40 _ _ (by simp) (by decide)
      (fun s S hT hts ht0 => nonValueSlot_ts40 s S hT hts ht0)) ?_
  refine progWStepBo_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsScBo_of_readOnly ro_ws_get_code) ?_
  exact progWStepBo_return _ _ _

/-! ## 1. `wkScBo_calculate_blob_gas_price` & `wkScBo_check_transaction` -/

theorem wkScBo_calculate_blob_gas_price :
    WorldKeepsScBo WorldOK (bufRegions [("u256_ws", 640)]) [] stdKeep NoExtra
      (ofString "calculate_blob_gas_price") := by
  refine ⟨_, _, _, lookup_calculate_blob_gas_price_local, fun {F} s hcode hW _ _ hres => ?_⟩
  have he0 : WsEnv s s := wsEnv_of_worldOK_local hcode hW
  have hsafe : WsSafe s (untypedGlobalBufIvls s)
      (evaluateHOLFiniteState s
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
          (extractFn Guest.Software.guestFn_calculate_blob_gas_price).body)) := by
    dsimp only [extractFn, Guest.Software.guestFn_calculate_blob_gas_price,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map]
    refine WsSafe.decCall ?_ ?_
    · intro vals body callee rs _ hl _
      rw [he0.code] at hl
      have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
      simp only [lookupCodeHOLExact, lookup_taylor_exponential_local, List.length] at hraw
      rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩
      · simp at hraw
      · simp at hraw
      · simp at hraw
      · simp only [List.length, ↓reduceIte] at hraw
        split at hraw
        · have hb : body = _ := (Prod.mk.inj (Option.some.inj hraw)).1.symm
          subst hb
          exact taylor_exponential_wsSafe_local (he0.with_locals_clock callee _)
        · simp at hraw
      · simp [List.length] at hraw
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _
      exact WsSafe.return_exp _ _ _
  have heff_m23 := hsafe.2 hres
  have heff_hb : HeapByteEff s
      (evaluateHOLFiniteState s
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
          (extractFn Guest.Software.guestFn_calculate_blob_gas_price).body)).2
      ([(globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)] ++
       [("sk_buf", 64), ("keccak_pad", 136), ("keccak_st", 200), ("mpt_nib_scratch", 64)].map (bufferRegion s)) [] :=
    heapByteEff_of_m23_bre_local hW.1 heff_m23
  have hstep : WorldStep (bufRegions [("u256_ws", 640)]) [] stdKeep NoExtra s
      (evaluateHOLFiniteState s
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
          (extractFn Guest.Software.guestFn_calculate_blob_gas_price).body)).1
      (evaluateHOLFiniteState s
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
          (extractFn Guest.Software.guestFn_calculate_blob_gas_price).body)).2 :=
    HeapByteEff.to_worldStep
      [("sk_buf", 64), ("keccak_pad", 136), ("keccak_st", 200), ("mpt_nib_scratch", 64)]
      (by decide) (by simp) hW heff_hb (fun _ _ _ _ _ => trivial)
  have hsp_eq : globN (evaluateHOLFiniteState s
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_calculate_blob_gas_price).body)).2 "scratch_ptr" =
      globN s "scratch_ptr" :=
    globN_eq_of_lookup (hstep.2.2.1 (ofString "scratch_ptr") (by decide))
  refine ⟨⟨hstep, by rw [hsp_eq]⟩, fun _ => ?_⟩
  apply ptxBlockOutUnhit_of_heapByteEff hW heff_hb
  intro j hj i hi
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  simp only [List.mem_append, List.mem_singleton, List.mem_map] at hj
  rcases hj with rfl | ⟨gn, hgn, rfl⟩
  · exact PtxP34.blockOut_disj_global_buffer hWT0.2.2.1 hi (g := ("u256_ws", 640)) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hgn
    rcases hgn with rfl | rfl | rfl | rfl <;>
      exact PtxP34.blockOut_disj_global_buffer hWT0.2.2.1 hi (by decide)

theorem wkScBo_check_transaction :
    WorldKeepsScBo WorldOK (bufRegions checkTxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      (ofString "check_transaction") := by
  have hB := validBufList_checkTxBufs
  have hgw := safeStepGlobals_checkTx
  have hB0 : ∀ p ∈ ([] : BufList), p ∈ checkTxBufs := by intro p hp; cases hp
  have hgw0 : ∀ g ∈ ([] : List String), g ∈ ["heap_ptr", "scratch_ptr"] := by intro g hg; cases hg
  refine worldKeepsScBo_of_progWStepBo lookup_check_transaction ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_check_transaction,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepBo_dec ?_
  refine progWStepBo_dec ?_
  refine progWStepBo_dec ?_
  refine progWStepBo_dec ?_
  refine progWStepBo_dec ?_
  refine progWStepBo_decCall hB hgw hB0 hgw0
    (worldKeepsScBo_of_readOnly Wave8Contracts.M15.ro_min) ?_
  refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_raise _ _ _ _) (progWStepBo_skip _ _)) ?_
  refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_raise _ _ _ _) (progWStepBo_skip _ _)) ?_
  refine progWStepBo_decCall hB hgw hB0 hgw0
    (worldKeepsScBo_of_readOnly ro_calculate_total_blob_gas) ?_
  refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_raise _ _ _ _) (progWStepBo_skip _ _)) ?_
  refine progWStepBo_decCall hB hgw
    (by intro p hp; simp [wsAcctBufs, checkTxBufs] at hp ⊢
        rcases hp with rfl | rfl | rfl <;> simp)
    (fun _ h => h)
    wkScBo_get_account ?_
  refine progWStepBo_dec ?_
  refine progWStepBo_dec ?_
  refine progWStepBo_dec ?_
  refine progWStepBo_dec ?_
  refine progWStepBo_seq hB hgw ?_ ?_
  · refine progWStepBo_ite ?_ ?_
    · refine progWStepBo_dec ?_
      refine progWStepBo_decCall hB hgw hB0 hgw0 (worldKeepsScBo_of_readOnly ro_u256_lt) ?_
      refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_raise _ _ _ _) (progWStepBo_skip _ _)) ?_
      refine progWStepBo_seq hB hgw (progWStepBo_assign_local _ _ _ _) (progWStepBo_assign_local _ _ _ _)
    · refine progWStepBo_dec ?_
      refine progWStepBo_dec ?_
      refine progWStepBo_decCall hB hgw hB0 hgw0 (worldKeepsScBo_of_readOnly ro_u256_lt) ?_
      refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_raise _ _ _ _) (progWStepBo_skip _ _)) ?_
      refine progWStepBo_decCall hB hgw hB0 hgw0 (worldKeepsScBo_of_readOnly ro_u256_lt) ?_
      refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_raise _ _ _ _) (progWStepBo_skip _ _)) ?_
      refine progWStepBo_decCall hB hgw hB0 hgw0
        (worldKeepsScBo_of_readOnly Wave8Contracts.M18.ro_u256_sub) ?_
      refine progWStepBo_decCall hB hgw hB0 hgw0 (worldKeepsScBo_of_readOnly ro_u256_lt) ?_
      refine progWStepBo_dec ?_
      refine progWStepBo_seq hB hgw
        (progWStepBo_ite (progWStepBo_assign_local _ _ _ _) (progWStepBo_skip _ _)) ?_
      refine progWStepBo_seq hB hgw
        (progWStepBo_call_local hB0 hgw0 (worldKeepsScBo_of_readOnly ro_u256_add))
        (progWStepBo_assign_local _ _ _ _)
  · refine progWStepBo_decCall hB hgw hB0 hgw0 (worldKeepsScBo_of_readOnly ro_fee_mul) ?_
    refine progWStepBo_dec ?_
    refine progWStepBo_dec ?_
    refine progWStepBo_seq hB hgw ?_ ?_
    · refine progWStepBo_ite ?_ (progWStepBo_skip _ _)
      refine progWStepBo_dec ?_
      refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_raise _ _ _ _) (progWStepBo_skip _ _)) ?_
      refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_raise _ _ _ _) (progWStepBo_skip _ _)) ?_
      refine progWStepBo_dec ?_
      refine progWStepBo_seq hB hgw
        (progWStepBo_while hB hgw
          (progWStepBo_seq hB hgw
            (progWStepBo_ite (progWStepBo_raise _ _ _ _) (progWStepBo_skip _ _))
            (progWStepBo_assign_local _ _ _ _))) ?_
      refine progWStepBo_decCall hB hgw
        (by intro p hp; simp at hp; subst hp; simp [checkTxBufs])
        hgw0
        wkScBo_calculate_blob_gas_price ?_
      refine progWStepBo_dec ?_
      refine progWStepBo_decCall hB hgw hB0 hgw0 (worldKeepsScBo_of_readOnly ro_u256_lt) ?_
      refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_raise _ _ _ _) (progWStepBo_skip _ _)) ?_
      refine progWStepBo_decCall hB hgw hB0 hgw0 (worldKeepsScBo_of_readOnly ro_fee_mul) ?_
      refine progWStepBo_seq hB hgw
        (progWStepBo_ite (progWStepBo_assign_local _ _ _ _) (progWStepBo_skip _ _)) ?_
      refine progWStepBo_decCall hB hgw hB0 hgw0 (worldKeepsScBo_of_readOnly ro_u256_add_carry) ?_
      refine progWStepBo_seq hB hgw
        (progWStepBo_ite (progWStepBo_assign_local _ _ _ _) (progWStepBo_skip _ _))
        (progWStepBo_assign_local _ _ _ _)
    · refine progWStepBo_seq hB hgw
        (progWStepBo_ite
          (progWStepBo_ite (progWStepBo_raise _ _ _ _) (progWStepBo_skip _ _))
          (progWStepBo_skip _ _)) ?_
      refine progWStepBo_dec ?_
      refine progWStepBo_decCall hB hgw hB0 hgw0 (worldKeepsScBo_of_readOnly ro_u256_fits_word) ?_
      refine progWStepBo_dec ?_
      refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_raise _ _ _ _) (progWStepBo_skip _ _)) ?_
      refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_raise _ _ _ _) (progWStepBo_skip _ _)) ?_
      refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_raise _ _ _ _) (progWStepBo_skip _ _)) ?_
      refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_raise _ _ _ _) (progWStepBo_skip _ _)) ?_
      refine progWStepBo_decCall hB hgw hB0 hgw0 (worldKeepsScBo_of_readOnly ro_u256_add_carry) ?_
      refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_raise _ _ _ _) (progWStepBo_skip _ _)) ?_
      refine progWStepBo_decCall hB hgw hB0 hgw0 (worldKeepsScBo_of_readOnly ro_u256_lt) ?_
      refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_raise _ _ _ _) (progWStepBo_skip _ _)) ?_
      refine progWStepBo_decCall hB hgw
        (by intro p hp; simp at hp; subst hp; simp [checkTxBufs])
        (by intro g hg; simp at hg; subst hg; simp)
        wkScBo_get_code ?_
      refine progWStepBo_decCall hB hgw hB0 hgw0
        (worldKeepsScBo_of_readOnly EvmFrameSpecs.ro_memeq) ?_
      refine progWStepBo_seq hB hgw ?_ (progWStepBo_return _ _ _)
      refine progWStepBo_ite ?_ (progWStepBo_skip _ _)
      refine progWStepBo_decCall hB hgw hB0 hgw0
        (worldKeepsScBo_of_readOnly ro_is_valid_delegation) ?_
      exact progWStepBo_ite (progWStepBo_raise _ _ _ _) (progWStepBo_skip _ _)

theorem «wk_check_transaction_bo» :
    WorldKeeps WorldOK
      (fun s =>
        [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
         (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
         (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
         (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["heap_ptr", "scratch_ptr"]
      stdKeep
      (fun s r post _ _ => NonExResult r → PtxBlockOutUnhit s post)
      (ofString "check_transaction") := by
  obtain ⟨ps, body, ret, hl, hb⟩ := wkScBo_check_transaction
  refine ⟨ps, body, ret, hl, fun {F} s hc hW hex hnt hres => ?_⟩
  have hstep := hb s hc hW hex hnt hres
  obtain ⟨a1, a2, a3, a4, a5⟩ := hstep.1.1
  refine ⟨a1, a2, a3, a4, fun S Nd hWT hD => ?_⟩
  obtain ⟨S', Nd', hs, hw', hog, hfo, _⟩ := a5 S Nd hWT hD
  exact ⟨S', Nd', hs, hw', hog, hfo, hstep.2⟩

/-! ## 2. `wk_recover_sender_with_chain_id_bo` -/

theorem «wk_recover_sender_with_chain_id_bo» :
    WorldKeeps
      (fun s => WorldOK s ∧ TxValidRecoverReady s ∧
        (∀ i ∈ blockOutObjects s, Disj i (locN s "out20", 20)))
      (fun s =>
        [(locN s "out20", 20),
         (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
         (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["heap_ptr"]
      stdKeep
      (fun s _ post _ _ => PtxBlockOutUnhit s post)
      (ofString "recover_sender_with_chain_id") := by
  refine ⟨_, _, _, lookup_recover_sender_with_chain_id, fun {F} s hcode ⟨hW, hTV, hout_bo⟩ hparams hnt hres => ?_⟩
  have hAR : ArenaReady s := hW.1
  obtain ⟨vals, hl_args⟩ := hparams
  obtain ⟨tx0, cid0, out0, _, htx, hcid, hout⟩ :=
    R13Shards.Keccak256.lookupCode_three_words (by decide) (by decide) (by decide)
      lookup_recover_sender_with_chain_id hl_args
  have htx_locN : locN s "tx" = tx0.toNat := by simp [locN, htx]
  have hout_locN : locN s "out20" = out0.toNat := by simp [locN, hout]
  have hV : TxValidRecoverReadyAt s tx0.toNat := by
    unfold TxValidRecoverReady at hTV
    rwa [htx_locN] at hTV
  have hws_bnd : globN s "u256_ws" = 0 ∨ globN s "u256_ws" + 640 ≤ 2 ^ 64 :=
    (wsEnv_of_worldOK_local hcode hW).ws_bnd
  let Rs : List Ivl :=
    [(locN s "out20", 20),
     (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
     (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
     (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)]
  let Bs : List (String × Nat) := [("sk_buf", 64), ("mpt_nib_scratch", 64)]
  have hmain : HeapByteEff s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_recover_sender_with_chain_id)).2
      (Rs ++ Bs.map (bufferRegion s)) ["heap_ptr"] := by
    refine recover_sender_with_chain_id_body_heapByteEff hAR
      (by decide) (by intro g hg; simp at hg; exact Or.inl hg)
      hV htx hcid hout hws_bnd ?_ ?_ ?_ ?_ hnt hres
    · intro iv hiv _
      simp only [untypedGlobalBufIvls, List.map, List.mem_cons, List.not_mem_nil, or_false] at hiv
      rcases hiv with rfl | rfl | rfl | rfl | rfl
      · exact ⟨(globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640),
          by simp [Rs], le_rfl, le_rfl⟩
      · exact ⟨bufferRegion s ("sk_buf", 64),
          by simp [Bs, bufferRegion], le_rfl, le_rfl⟩
      · exact ⟨(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
          by simp [Rs], le_rfl, le_rfl⟩
      · exact ⟨(globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
          by simp [Rs], le_rfl, le_rfl⟩
      · exact ⟨bufferRegion s ("mpt_nib_scratch", 64),
          by simp [Bs, bufferRegion], le_rfl, le_rfl⟩
    · exact ⟨(locN s "out20", 20), by simp [Rs], by rw [hout_locN], by rw [hout_locN]⟩
    · intro hnz
      exact ⟨(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        by simp [Rs], le_rfl, by simp [hnz]⟩
    · intro hnz
      exact ⟨(globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        by simp [Rs], le_rfl, by simp [hnz]⟩
  have hbo_unhit : PtxBlockOutUnhit s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_recover_sender_with_chain_id)).2 := by
    apply ptxBlockOutUnhit_of_heapByteEff hW hmain
    intro j hj i hi
    obtain ⟨S0, hWT0_ex⟩ := hW.2
    obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
    simp only [Rs, Bs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hj
    rcases hj with (rfl | rfl | rfl | rfl) | ⟨gn, hgn, rfl⟩
    · exact hout_bo i hi
    · exact PtxP34.blockOut_disj_global_buffer hWT0.2.2.1 hi (g := ("keccak_pad", 136)) (by decide)
    · exact PtxP34.blockOut_disj_global_buffer hWT0.2.2.1 hi (g := ("keccak_st", 200)) (by decide)
    · exact PtxP34.blockOut_disj_global_buffer hWT0.2.2.1 hi (g := ("u256_ws", 640)) (by decide)
    · rcases hgn with rfl | rfl
      · exact PtxP34.blockOut_disj_global_buffer hWT0.2.2.1 hi (g := ("sk_buf", 64)) (by decide)
      · exact PtxP34.blockOut_disj_global_buffer hWT0.2.2.1 hi (g := ("mpt_nib_scratch", 64)) (by decide)
  exact hmain.to_worldStep (R := fun t =>
      [(locN t "out20", 20),
       (globN t "keccak_pad", if globN t "keccak_pad" = 0 then 0 else 136),
       (globN t "keccak_st", if globN t "keccak_st" = 0 then 0 else 200),
       (globN t "u256_ws", if globN t "u256_ws" = 0 then 0 else 640)])
    (B := Bs)
    (by
      intro gs hgs
      simp only [Bs, List.mem_cons, List.not_mem_nil, or_false] at hgs
      rcases hgs with rfl | rfl <;> exact ⟨by decide, by decide⟩)
    (by intro g hg; simp at hg; exact Or.inl hg)
    hW (fun _ _ _ _ _ => hbo_unhit)

/-! ## 3. Preservation of `TxValidEncodeAt` & `TxValidRecoverReadyAt` Across Unhit Steps -/

def TxReadyFullStrong {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  TxReadyStrong s ∧ (memW s (memW s (globN s "bo" + 40)) ≠ 0 ∧ memW s (memW s (globN s "bo" + 72)) ≠ 0) ∧
    TxValidEncodeReady s ∧ TxValidRecoverReady s

theorem disj_heapFree_grows {F : Type} {s post : PanSemStateFiniteExact 64 F} {iv : Ivl}
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hhp_lim : globN post "heap_ptr" ≤ heapLimit)
    (hd : Disj iv (heapFree s)) :
    Disj iv (heapFree post) := by
  unfold Disj heapFree at hd ⊢
  dsimp only at hd ⊢
  rcases hd with h0 | h0 | hl | hr
  · exact Or.inl h0
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

theorem txValidEncodeAt_with_locals {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (ck : Nat) {tx : Nat}
    (h : TxValidEncodeAt s tx) :
    TxValidEncodeAt { s with locals := L, clock := ck } tx :=
  h

theorem txValidRecoverReadyAt_with_locals {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (ck : Nat) {tx : Nat}
    (h : TxValidRecoverReadyAt s tx) :
    TxValidRecoverReadyAt { s with locals := L, clock := ck } tx :=
  h

theorem txValidEncodeAt_step_heap_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {tx : Nat}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hu_heap : ∀ a : BitVec 64, sourceBase ≤ a.toNat → a.toNat + 8 ≤ globN s "heap_ptr" →
      post.memory a = s.memory a)
    (hV : TxValidEncodeAt s tx) :
    TxValidEncodeAt post tx := by
  have hGp : GuestInv post := hAp.1
  have hhp_lim_p : globN post "heap_ptr" ≤ heapLimit := hAp.2.2.1
  obtain ⟨hTV, h152, hb192, hd192, h216, h264, h280⟩ := hV
  obtain ⟨hw, hin, h0, h200, h216_lim, hsl, h264_lim, h280_lim, hw208, hw272⟩ := hTV
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have hhl_2p64 : heapLimit ≤ 2 ^ 64 := by rw [WkBlockTxEnc.heapLimit_val]; decide
  have hm_in : ∀ iv : Ivl, Inside iv sourceBase (globN s "heap_ptr") → iv.1 % 8 = 0 →
      ∀ off, off % 8 = 0 → off + 8 ≤ iv.2 → memW post (iv.1 + off) = memW s (iv.1 + off) := by
    intro iv hin_iv hal8 off hoff8 hoff_lt
    have hlo : sourceBase ≤ iv.1 + off := by unfold Inside at hin_iv; omega
    have hhi : iv.1 + off + 8 ≤ globN s "heap_ptr" := by unfold Inside at hin_iv; omega
    have hlt64 : iv.1 + off < 2 ^ 64 := by omega
    have hbv : (BitVec.ofNat 64 (iv.1 + off)).toNat = iv.1 + off := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
    have hmem_eq := hu_heap (BitVec.ofNat 64 (iv.1 + off)) (by rw [hbv]; exact hlo) (by rw [hbv]; exact hhi)
    unfold memW; rw [hmem_eq]
  have htx8 : tx % 8 = 0 := hw.1
  have e0 : memW post tx = memW s tx := by simpa using hm_in (tx, 384) hin htx8 0 (by decide) (by omega)
  have e152 : memW post (tx + 152) = memW s (tx + 152) := hm_in (tx, 384) hin htx8 152 (by decide) (by omega)
  have e192 : memW post (tx + 192) = memW s (tx + 192) := hm_in (tx, 384) hin htx8 192 (by decide) (by omega)
  have e200 : memW post (tx + 200) = memW s (tx + 200) := hm_in (tx, 384) hin htx8 200 (by decide) (by omega)
  have e208 : memW post (tx + 208) = memW s (tx + 208) := hm_in (tx, 384) hin htx8 208 (by decide) (by omega)
  have e216 : memW post (tx + 216) = memW s (tx + 216) := hm_in (tx, 384) hin htx8 216 (by decide) (by omega)
  have e256 : memW post (tx + 256) = memW s (tx + 256) := hm_in (tx, 384) hin htx8 256 (by decide) (by omega)
  have e264 : memW post (tx + 264) = memW s (tx + 264) := hm_in (tx, 384) hin htx8 264 (by decide) (by omega)
  have e272 : memW post (tx + 272) = memW s (tx + 272) := hm_in (tx, 384) hin htx8 272 (by decide) (by omega)
  have e280 : memW post (tx + 280) = memW s (tx + 280) := hm_in (tx, 384) hin htx8 280 (by decide) (by omega)
  have hsl_eq : txAccessSlots post tx = txAccessSlots s tx := by
    unfold txAccessSlots
    rw [e216, e208]
    by_cases hpos : 0 < memW s (tx + 216)
    · apply congrArg List.sum
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      have hal208 : memW s (tx + 208) % 8 = 0 := (hw208 hpos).1
      simpa [Nat.add_assoc] using hm_in (memW s (tx + 208), 24 * memW s (tx + 216))
        (h216 hpos).1 hal208 (24 * i + 16) (by omega) (by omega)
    · have hz : memW s (tx + 216) = 0 := by omega
      simp [hz]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold TxValidAt
    rw [e0, e200, e208, e216, e264, e272, e280, hsl_eq]
    exact ⟨R13Shards.wordsOK_transfer hAs.1 hGp hw, ⟨hin.1, hin.2.trans hhp⟩,
      h0, h200, h216_lim, hsl, h264_lim, h280_lim,
      fun hp => R13Shards.wordsOK_transfer hAs.1 hGp (hw208 hp),
      fun hp => R13Shards.wordsOK_transfer hAs.1 hGp (hw272 hp)⟩
  · rw [e152]
    intro hnz
    exact ⟨(h152 hnz).1, disj_heapFree_grows hhp hhp_lim_p (h152 hnz).2⟩
  · rw [e192, e200]; exact hb192
  · rw [e192, e200]; exact disj_heapFree_grows hhp hhp_lim_p hd192
  · rw [e216, e208]
    intro hpos
    obtain ⟨hin208, hall⟩ := h216 hpos
    have hal208 : memW s (tx + 208) % 8 = 0 := (hw208 hpos).1
    refine ⟨⟨hin208.1, hin208.2.trans hhp⟩, fun i hi => ?_⟩
    have hai := hall i hi
    have ea0 : memW post (memW s (tx + 208) + 24 * i) = memW s (memW s (tx + 208) + 24 * i) := by
      simpa using hm_in (memW s (tx + 208), 24 * memW s (tx + 216)) hin208 hal208 (24 * i) (by omega) (by omega)
    have ea8 : memW post (memW s (tx + 208) + 24 * i + 8) = memW s (memW s (tx + 208) + 24 * i + 8) := by
      simpa [Nat.add_assoc] using hm_in (memW s (tx + 208), 24 * memW s (tx + 216)) hin208 hal208 (24 * i + 8) (by omega) (by omega)
    have ea16 : memW post (memW s (tx + 208) + 24 * i + 16) = memW s (memW s (tx + 208) + 24 * i + 16) := by
      simpa [Nat.add_assoc] using hm_in (memW s (tx + 208), 24 * memW s (tx + 216)) hin208 hal208 (24 * i + 16) (by omega) (by omega)
    dsimp only at hai ⊢
    rw [ea0, ea8, ea16]
    exact ⟨hai.1, disj_heapFree_grows hhp hhp_lim_p hai.2.1, fun hp16 =>
      ⟨⟨(hai.2.2 hp16).1.1, (hai.2.2 hp16).1.2.trans hhp⟩,
        R13Shards.wordsOK_transfer hAs.1 hGp (hai.2.2 hp16).2⟩⟩
  · rw [e0, e264, e256]
    intro hcond
    exact ⟨⟨(h264 hcond).1.1, (h264 hcond).1.2.trans hhp⟩,
      R13Shards.wordsOK_transfer hAs.1 hGp (h264 hcond).2⟩
  · rw [e0, e280, e272]
    intro hcond
    obtain ⟨hin272, hall⟩ := h280 hcond
    have hal272 : memW s (tx + 272) % 8 = 0 := (hw272 hcond.2).1
    refine ⟨⟨hin272.1, hin272.2.trans hhp⟩, fun i hi => ?_⟩
    have hai := hall i hi
    have eau32 : memW post (memW s (tx + 272) + 120 * i + 32) = memW s (memW s (tx + 272) + 120 * i + 32) := by
      simpa [Nat.add_assoc] using hm_in (memW s (tx + 272), 120 * memW s (tx + 280)) hin272 hal272 (120 * i + 32) (by omega) (by omega)
    dsimp only at hai ⊢
    rw [eau32]
    exact ⟨hai.1, disj_heapFree_grows hhp hhp_lim_p hai.2⟩

theorem txValidRecoverReadyAt_step_heap_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {tx : Nat}
    (hAs : ArenaReady s) (hGp : GuestInv post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hu_heap : ∀ a : BitVec 64, sourceBase ≤ a.toNat → a.toNat + 8 ≤ globN s "heap_ptr" →
      post.memory a = s.memory a)
    (hV : TxValidRecoverReadyAt s tx) :
    TxValidRecoverReadyAt post tx := by
  obtain ⟨hTV, hin208, hin272⟩ := hV
  obtain ⟨hw, hin, h0, h200, h216_lim, hsl, h264_lim, h280_lim, hw208, hw272⟩ := hTV
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have hhl_2p64 : heapLimit ≤ 2 ^ 64 := by rw [WkBlockTxEnc.heapLimit_val]; decide
  have hm_in : ∀ iv : Ivl, Inside iv sourceBase (globN s "heap_ptr") → iv.1 % 8 = 0 →
      ∀ off, off % 8 = 0 → off + 8 ≤ iv.2 → memW post (iv.1 + off) = memW s (iv.1 + off) := by
    intro iv hin_iv hal8 off hoff8 hoff_lt
    have hlo : sourceBase ≤ iv.1 + off := by unfold Inside at hin_iv; omega
    have hhi : iv.1 + off + 8 ≤ globN s "heap_ptr" := by unfold Inside at hin_iv; omega
    have hlt64 : iv.1 + off < 2 ^ 64 := by omega
    have hbv : (BitVec.ofNat 64 (iv.1 + off)).toNat = iv.1 + off := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
    have hmem_eq := hu_heap (BitVec.ofNat 64 (iv.1 + off)) (by rw [hbv]; exact hlo) (by rw [hbv]; exact hhi)
    unfold memW; rw [hmem_eq]
  have htx8 : tx % 8 = 0 := hw.1
  have e0 : memW post tx = memW s tx := by simpa using hm_in (tx, 384) hin htx8 0 (by decide) (by omega)
  have e200 : memW post (tx + 200) = memW s (tx + 200) := hm_in (tx, 384) hin htx8 200 (by decide) (by omega)
  have e208 : memW post (tx + 208) = memW s (tx + 208) := hm_in (tx, 384) hin htx8 208 (by decide) (by omega)
  have e216 : memW post (tx + 216) = memW s (tx + 216) := hm_in (tx, 384) hin htx8 216 (by decide) (by omega)
  have e264 : memW post (tx + 264) = memW s (tx + 264) := hm_in (tx, 384) hin htx8 264 (by decide) (by omega)
  have e272 : memW post (tx + 272) = memW s (tx + 272) := hm_in (tx, 384) hin htx8 272 (by decide) (by omega)
  have e280 : memW post (tx + 280) = memW s (tx + 280) := hm_in (tx, 384) hin htx8 280 (by decide) (by omega)
  have hsl_eq : txAccessSlots post tx = txAccessSlots s tx := by
    unfold txAccessSlots
    rw [e216, e208]
    by_cases hpos : 0 < memW s (tx + 216)
    · apply congrArg List.sum
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      have hal208 : memW s (tx + 208) % 8 = 0 := (hw208 hpos).1
      simpa [Nat.add_assoc] using hm_in (memW s (tx + 208), 24 * memW s (tx + 216))
        (hin208 hpos) hal208 (24 * i + 16) (by omega) (by omega)
    · have hz : memW s (tx + 216) = 0 := by omega
      simp [hz]
  refine ⟨?_, ?_, ?_⟩
  · unfold TxValidAt
    rw [e0, e200, e208, e216, e264, e272, e280, hsl_eq]
    exact ⟨R13Shards.wordsOK_transfer hAs.1 hGp hw, ⟨hin.1, hin.2.trans hhp⟩,
      h0, h200, h216_lim, hsl, h264_lim, h280_lim,
      fun hp => R13Shards.wordsOK_transfer hAs.1 hGp (hw208 hp),
      fun hp => R13Shards.wordsOK_transfer hAs.1 hGp (hw272 hp)⟩
  · rw [e216, e208]
    exact fun hp => ⟨(hin208 hp).1, (hin208 hp).2.trans hhp⟩
  · rw [e280, e272]
    exact fun hp => ⟨(hin272 hp).1, (hin272 hp).2.trans hhp⟩

/-! ## 4. Relational `PtxRelBase` Steps for `bal_index := index + 1` and `bo+24` `encArray` Stores -/

theorem ptxRelBase_assign_bal_index {F : Type} {txDone : Bool}
    {entry s : PanSemStateFiniteExact 64 F} (h : PtxRelBase txDone entry s) (w : BitVec 64) :
    PtxRelBase txDone entry (setKvarHOLFinite .global (ofString "bal_index") (.val (.word w)) s) := by
  let post := setGlobalHOLFinite (ofString "bal_index") (.val (.word w)) s
  change PtxRelBase txDone entry post
  obtain ⟨S0, hWT0_ex⟩ := h.world.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  obtain ⟨hA', hW', how⟩ := R16Shards.worldTypedWith_setGlobal_untracked
    (gname := ofString "bal_index") (w := w)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    h.world.1 hWT0
  have hW_post : WorldOK post := ⟨hA', S0, (worldTyped_iff_with post S0).2 ⟨Nd0, hW'⟩⟩
  have hg_same : ∀ nm, ofString nm ≠ ofString "bal_index" → globN post nm = globN s nm := fun nm hne => by
    simp [post, globN, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm hne]
  have hfmp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := hg_same _ (by decide)
  have hsp : globN post "scratch_ptr" = globN s "scratch_ptr" := hg_same _ (by decide)
  have hhp : globN post "heap_ptr" = globN s "heap_ptr" := hg_same _ (by decide)
  have hbo : globN post "bo" = globN s "bo" := hg_same _ (by decide)
  refine ⟨h.ready_entry, h.arena_entry, by rw [hfmp]; exact h.frame_entry,
    by rw [hsp]; exact h.scratch_entry, hW_post, by rw [hhp]; exact h.heap_entry, ?_, ?_,
    by change memW s (memW s (globN post "bo" + 72)) ≠ 0; rw [hbo]; exact h.rcpt_backing,
    by change memW s (memW s (globN post "bo" + 40)) ≠ 0; rw [hbo]; exact h.log_backing,
    by change memW s (memW s (globN post "bo" + 72) + 8) = _; rw [hbo]; exact h.rcpt_len_eq,
    fun off hoff i hi => by
      change memW s (memW s (globN post "bo" + off) + 16 * i + 8) = _
      rw [hbo]; exact h.slices_prev off hoff i hi,
    fun ht => by
      change memW s (memW s (globN post "bo" + 24) + 16 * locN entry "index" + 8) < 2 ^ 40
      rw [hbo]; exact h.tx_slice_cur ht,
    ?_⟩
  · intro k hk
    have hk_ne : ofString "bal_index" ≠ k := by
      intro heq; subst heq; exact hk (by decide)
    simp only [post, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      beq_false_of_ne hk_ne, Bool.false_eq_true, ↓reduceIte]
    exact h.globals k hk
  · intro rec hrec hnz off hoff hno
    exact h.records rec hrec hnz off hoff hno
  · intro S_e Nd_e hWT_e hD_e
    obtain ⟨Sc, Nc, hsub, hWc, hOG, hFO⟩ := h.typing S_e Nd_e hWT_e hD_e
    obtain ⟨_, hWc', how_c⟩ := R16Shards.worldTypedWith_setGlobal_untracked
      (gname := ofString "bal_index") (w := w)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      h.world.1 hWc
    have hOG' : OwnedGrows entry post (worldOwned entry S_e Nd_e) (worldOwned post Sc Nc) := by
      unfold OwnedGrows at hOG ⊢
      rw [how_c, hhp]
      exact hOG
    exact ⟨Sc, Nc, hsub, hWc', hOG', hFO⟩

theorem ptxRelBase_store_encSlot0 {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    (h : PtxRelBase false entry s)
    (hRs : TxReadyStrong s)
    (hidx_eq : locN s "index" = locN entry "index")
    {x : BitVec 64} (hx_ev : evalAt s (PtxP1.encDst false) = some (.val (.word x)))
    (hx_dom : s.memaddrs x)
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    PtxRelBase false entry { s with memory := mem' } := by
  let post : PanSemStateFiniteExact 64 F := { s with memory := mem' }
  have hEs := PtxP1.txEnv_of_ready hRs
  have hin := PtxP1.encDst0_inside hRs hx_ev
  obtain ⟨S_e0, Nd_e0, hWT_e0, _⟩ := h.ready_entry.2.2.2.2
  have hbo_e : globN s "bo" = globN entry "bo" :=
    globN_eq_of_lookup (h.globals (ofString "bo") (by decide))
  have hbo24_s : memW s (globN s "bo" + 24) = memW entry (globN entry "bo" + 24) :=
    ptx_entry_bo_field_eq hWT_e0 h.globals h.records h.ready_entry.1.2.1 (by simp) (by omega)
  have hbo80_s : memW s (globN s "bo" + 80) = memW entry (globN entry "bo" + 80) :=
    ptx_entry_bo_field_eq hWT_e0 h.globals h.records h.ready_entry.1.2.1 (by simp) (by omega)
  obtain ⟨S_s, Nd_s, hWT_s, _⟩ := hRs.2.2.2.2
  obtain ⟨hWT_p, _, _⟩ := PtxP1.store_encArray_world h.world.1 hEs hWT_s hx_dom hin hm
  have hAp : ArenaReady post := ⟨guestInv_congr (s := s) rfl rfl rfl rfl h.world.1.1, h.world.1.2⟩
  have hWp : WorldOK post := ⟨hAp, S_s, (worldTyped_iff_with post S_s).2 ⟨Nd_s, hWT_p⟩⟩
  have hx_nat : x.toNat = memW s (globN s "bo" + 24) + 16 * locN s "index" := by
    change evalAt s (.op .add
      [.load .one (.op .add [.var .global (ofString "bo"), .const 24]),
        .panop .mul [.var .local (ofString "index"), .const 16]]) = _ at hx_ev
    rcases hld : evalAt s (.load .one (.op .add [.var .global (ofString "bo"), .const 24])) with _ | vbase
    · simp only [evalAt, evalHOLExact, evalListHOLExact] at hx_ev hld; rw [hld] at hx_ev; simp at hx_ev
    obtain ⟨abase, rfl, habase_nat⟩ := evalAt_loadG s "bo" 24 vbase hld
    have habase : abase.toNat = memW s (globN s "bo" + 24) := habase_nat
    simp only [evalAt, evalHOLExact, evalListHOLExact] at hx_ev hld
    rw [hld] at hx_ev
    rcases hidx_v : s.locals.lookup (ofString "index") with _ | vidx
    · simp [hidx_v] at hx_ev
    rcases vidx with ⟨⟨idx_bv⟩⟩ | _ | _
    · simp only [hidx_v, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self,
        ↓reduceIte, panOpHOL, wordOpHOL, wordOp, List.foldr, Option.some.injEq,
        ValueHOL.val.injEq, HolWordLab.word.injEq] at hx_ev
      have hidx_nat : locN s "index" = idx_bv.toNat := by simp [locN, hidx_v]
      have hhi := (R13Shards.ivl_allocated_bound h.world.1.2 (PtxP1.encArray_words hWT_s.2.2.1 hEs).1).2
      dsimp only [PtxP1.encArray] at hhi
      have hhl_arr : memW s (globN s "bo" + 24) + (16 * memW s (globN s "bo" + 80) + 16) ≤ 2 ^ 64 := by
        have h1 : heapLimit ≤ 2 ^ 64 := by rw [WkBlockTxEnc.heapLimit_val]; decide
        have h2 : scratchEnd ≤ 2 ^ 64 := by rw [WkBlockTxEnc.scratchEnd_val]; decide
        omega
      have hidx_lt : idx_bv.toNat < memW s (globN s "bo" + 80) := hidx_nat ▸ hEs.idx_lt
      rw [← hx_ev]
      simp only [BitVec.toNat_add, BitVec.toNat_mul]
      have hz0 : (0 : BitVec 64).toNat = 0 := by decide
      have h16 : (16 : BitVec 64).toNat = 16 := by decide
      have h24 : (24 : BitVec 64).toNat = 24 := by decide
      have h8 : (8 : BitVec 64).toNat = 8 := by decide
      rw [hz0]
      simp only [h16, h24, h8] at *
      omega
    · simp [hidx_v, valueIsWord] at hx_ev
    · simp [hidx_v, valueIsWord] at hx_ev
  obtain ⟨_, hbo_pw, hgb_rest, _, _⟩ := R13Shards.fixedObjects_disj_parts hWT_s.2.2.1
  obtain ⟨_, _, hbo_eq⟩ := R13Shards.blockOutObjects_eq_list hEs hWT_s.1
  have hbo_len : (blockOutObjects s).length = 7 := by rw [hbo_eq]; rfl
  have h0_eq : (blockOutObjects s)[0] = PtxP1.encArray s := by simp [hbo_eq, PtxP1.encArray, hEs.bo_nz, hEs.bo24]
  have hbo_idx_disj : ∀ (j : Nat) (hj : j < (blockOutObjects s).length), 0 < j →
      Disj (blockOutObjects s)[j] (PtxP1.encArray s) := by
    intro j hj hgt
    have hget := List.pairwise_iff_getElem.1 hbo_pw
    exact R13Shards.disj_symm (h0_eq ▸ hget 0 j (by omega) hj hgt)
  have hm_ne_ivl : ∀ iv : Ivl, Disj iv (PtxP1.encArray s) → Allocated s iv →
      ∀ off, off + 8 ≤ iv.2 → memW post (iv.1 + off) = memW s (iv.1 + off) := by
    intro iv hd hal off hoff
    have hhi_iv := (R13Shards.ivl_allocated_bound h.world.1.2 hal).2
    have hhl_64 : iv.1 + iv.2 ≤ 2 ^ 64 := by
      have h1 : heapLimit ≤ 2 ^ 64 := by rw [WkBlockTxEnc.heapLimit_val]; decide
      have h2 : scratchEnd ≤ 2 ^ 64 := by rw [WkBlockTxEnc.scratchEnd_val]; decide
      omega
    have hlt64 : iv.1 + off < 2 ^ 64 := by omega
    have hne : BitVec.ofNat 64 (iv.1 + off) ≠ x := by
      intro heq
      have htonat := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64] at htonat
      have hd_x := R13Shards.disj_of_inside_right hin hd
      rcases hd_x with h0 | h0 | hd1 | hd2 <;> (dsimp only at *; omega)
    unfold memW; dsimp only [post]; rw [hm _ hne]
  have hbo_disj_arr : Disj (globN s "bo", 88) (PtxP1.encArray s) :=
    hgb_rest _ (List.mem_map.2 ⟨("bo", 88), by decide, by simp [hEs.bo_nz]⟩) _
      (List.mem_append_left _ (List.mem_append_right _ (PtxP1.encArray_mem_block hEs)))
  have hbo_al : Allocated s (globN s "bo", 88) := (R13Shards.bo_words hWT_s.2.2.1 hEs.bo_nz).1
  have hbo_mem : ∀ off, off + 8 ≤ 88 → memW post (globN s "bo" + off) = memW s (globN s "bo" + off) :=
    hm_ne_ivl (globN s "bo", 88) hbo_disj_arr hbo_al
  have h40_disj : Disj (memW s (globN s "bo" + 40), 24) (PtxP1.encArray s) := by
    have h3 : (blockOutObjects s)[3] = (memW s (globN s "bo" + 40), 24) := by simp [hbo_eq]
    exact h3 ▸ hbo_idx_disj 3 (by omega) (by omega)
  have h72_disj : Disj (memW s (globN s "bo" + 72), 24) (PtxP1.encArray s) := by
    have h5 : (blockOutObjects s)[5] = (memW s (globN s "bo" + 72), 24) := by simp [hbo_eq]
    exact h5 ▸ hbo_idx_disj 5 (by omega) (by omega)
  have h32_disj : Disj (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16) (PtxP1.encArray s) := by
    have h1 : (blockOutObjects s)[1] = (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16) := by
      simp [hbo_eq, hEs.bo_nz, hEs.bo32]
    exact h1 ▸ hbo_idx_disj 1 (by omega) (by omega)
  have h40_al : Allocated s (memW s (globN s "bo" + 40), 24) :=
    ((hWT_s.2.2.1.1 _ (List.mem_append_left _ (List.mem_append_right _ (by simp [blockOutObjects, hEs.bo_nz, hEs.bo40])))).resolve_left (by simp)).1
  have h72_al : Allocated s (memW s (globN s "bo" + 72), 24) :=
    ((hWT_s.2.2.1.1 _ (List.mem_append_left _ (List.mem_append_right _ (by simp [blockOutObjects, hEs.bo_nz, hEs.bo72])))).resolve_left (by simp)).1
  have h32_al : Allocated s (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16) :=
    ((hWT_s.2.2.1.1 _ (List.mem_append_left _ (List.mem_append_right _ (by simp [blockOutObjects, hEs.bo_nz, hEs.bo32])))).resolve_left (by simp)).1
  refine ⟨h.ready_entry, h.arena_entry, h.frame_entry, h.scratch_entry, hWp, h.heap_entry, h.globals, ?_, ?_, ?_, ?_, ?_, (fun ht => by cases ht), ?_⟩
  · intro rec hrec hnz off hoff hno
    have hrec_eq : memW post (globN entry rec.1 + off) = memW s (globN entry rec.1 + off) := by
      have hge : globN s rec.1 = globN entry rec.1 := by
        simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
        rcases hrec with rfl | rfl | rfl | rfl
        · exact globN_eq_of_lookup (h.globals (ofString "ws") (by decide))
        · exact globN_eq_of_lookup (h.globals (ofString "bs") (by decide))
        · simp at hoff
        · exact hbo_e
      rw [← hge]
      have hnz_s : globN s rec.1 ≠ 0 := by rwa [hge]
      simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · have hd := hgb_rest (globN s "ws", 40) (List.mem_map.2 ⟨("ws", 40), by decide, by dsimp only; rw [if_neg hnz_s]⟩) _
          (List.mem_append_left _ (List.mem_append_right _ (PtxP1.encArray_mem_block hEs)))
        have hal := ((hWT_s.2.2.1.1 (globN s "ws", 40) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_map.2 ⟨("ws", 40), by decide, by dsimp only; rw [if_neg hnz_s]⟩))))).resolve_left (by simp)).1
        exact hm_ne_ivl (globN s "ws", 40) hd hal off (by simp at hoff; omega)
      · have hd := hgb_rest (globN s "bs", 80) (List.mem_map.2 ⟨("bs", 80), by decide, by dsimp only; rw [if_neg hnz_s]⟩) _
          (List.mem_append_left _ (List.mem_append_right _ (PtxP1.encArray_mem_block hEs)))
        have hal := ((hWT_s.2.2.1.1 (globN s "bs", 80) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_map.2 ⟨("bs", 80), by decide, by dsimp only; rw [if_neg hnz_s]⟩))))).resolve_left (by simp)).1
        exact hm_ne_ivl (globN s "bs", 80) hd hal off (by simp at hoff; omega)
      · simp at hoff
      · exact hbo_mem off (by simp at hoff; omega)
    exact hrec_eq.trans (h.records rec hrec hnz off hoff hno)
  · change memW post (memW post (globN s "bo" + 72)) ≠ 0
    have h72_0 : memW post (memW s (globN s "bo" + 72)) = memW s (memW s (globN s "bo" + 72)) := by
      simpa using hm_ne_ivl _ h72_disj h72_al 0 (by omega)
    rw [hbo_mem 72 (by omega), h72_0]
    exact h.rcpt_backing
  · change memW post (memW post (globN s "bo" + 40)) ≠ 0
    have h40_0 : memW post (memW s (globN s "bo" + 40)) = memW s (memW s (globN s "bo" + 40)) := by
      simpa using hm_ne_ivl _ h40_disj h40_al 0 (by omega)
    rw [hbo_mem 40 (by omega), h40_0]
    exact h.log_backing
  · change memW post (memW post (globN s "bo" + 72) + 8) = _
    rw [hbo_mem 72 (by omega), hm_ne_ivl _ h72_disj h72_al 8 (by omega)]
    exact h.rcpt_len_eq
  · intro off hoff i hi
    change memW post (memW post (globN s "bo" + off) + 16 * i + 8) = _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl
    · rw [hbo_mem 24 (by omega)]
      have hhi_arr := (R13Shards.ivl_allocated_bound h.world.1.2 (PtxP1.encArray_words hWT_s.2.2.1 hEs).1).2
      dsimp only [PtxP1.encArray] at hhi_arr
      have hhl_64 : memW s (globN s "bo" + 24) + (16 * memW s (globN s "bo" + 80) + 16) ≤ 2 ^ 64 := by
        have h1 : heapLimit ≤ 2 ^ 64 := by rw [WkBlockTxEnc.heapLimit_val]; decide
        have h2 : scratchEnd ≤ 2 ^ 64 := by rw [WkBlockTxEnc.scratchEnd_val]; decide
        omega
      have hi_lt : i < memW s (globN s "bo" + 80) := by
        have := hEs.idx_lt; omega
      have hlt64 : memW s (globN s "bo" + 24) + 16 * i + 8 < 2 ^ 64 := by omega
      have hne : BitVec.ofNat 64 (memW s (globN s "bo" + 24) + 16 * i + 8) ≠ x := by
        intro heq
        have htonat := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64, hx_nat, hidx_eq] at htonat
        omega
      have hm_eq : memW post (memW s (globN s "bo" + 24) + 16 * i + 8) =
          memW s (memW s (globN s "bo" + 24) + 16 * i + 8) := by
        unfold memW at hne ⊢; dsimp only [post]; rw [hm _ hne]
      exact hm_eq.trans (h.slices_prev 24 (by simp) i hi)
    · rw [hbo_mem 32 (by omega)]
      have hi_lt : i < memW s (globN s "bo" + 80) := by have := hEs.idx_lt; omega
      have hm_eq : memW post (memW s (globN s "bo" + 32) + 16 * i + 8) =
          memW s (memW s (globN s "bo" + 32) + 16 * i + 8) := by
        simpa [Nat.add_assoc] using hm_ne_ivl _ h32_disj h32_al (16 * i + 8) (by omega)
      exact hm_eq.trans (h.slices_prev 32 (by simp) i hi)
  · intro S0 Nd0 hWT0 hD0
    obtain ⟨Sc, Nc, hsub, hWc, hOG, hFO⟩ := h.typing S0 Nd0 hWT0 hD0
    obtain ⟨hWc_p, how_c, _⟩ := PtxP1.store_encArray_world h.world.1 hEs hWc hx_dom hin hm
    have hOG_p : OwnedGrows entry post (worldOwned entry S0 Nd0) (worldOwned post Sc Nc) := by
      unfold OwnedGrows at hOG ⊢
      rw [how_c]; exact hOG
    have harr_e : PtxP1.encArray entry ∈ worldOwned entry S0 Nd0 :=
      List.mem_append_left _ (List.mem_append_right _ (PtxP1.encArray_mem_fixed (PtxP1.txEnv_of_ready h.ready_entry)))
    have harr_eq : PtxP1.encArray s = PtxP1.encArray entry := by
      unfold PtxP1.encArray; rw [hbo24_s, hbo80_s]
    have hFO_p : FrameOutside entry post (worldOwned entry S0 Nd0 ++ ptxRegions entry ++ [freeGap entry]) (heapFree entry) := by
      intro a ha hhf
      have hne_x : a ≠ x := by
        intro rfl
        apply ha (PtxP1.encArray entry) (List.mem_append_left _ (List.mem_append_left _ harr_e))
        rw [← harr_eq]
        unfold CellHits; unfold Inside at hin; omega
      exact (hm a hne_x).trans (hFO a ha hhf)
    exact ⟨Sc, Nc, hsub, hWc_p, hOG_p, hFO_p⟩

theorem ptxRelBase_store_encSlot1 {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    (h : PtxRelBase false entry s)
    (hRs : TxReadyStrong s)
    (hidx_eq : locN s "index" = locN entry "index")
    {x b : BitVec 64} (hb_lt : b.toNat < 2 ^ 40)
    (hx_ev : evalAt s (PtxP1.encDst true) = some (.val (.word x)))
    (hx_dom : s.memaddrs x)
    {mem' : BitVec 64 → HolWordLab 64}
    (hmem_x : mem' x = .word b)
    (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    PtxRelBase true entry { s with memory := mem' } := by
  let post : PanSemStateFiniteExact 64 F := { s with memory := mem' }
  have hEs := PtxP1.txEnv_of_ready hRs
  have hin := PtxP1.encDst8_inside hRs hx_ev
  obtain ⟨S_e0, Nd_e0, hWT_e0, _⟩ := h.ready_entry.2.2.2.2
  have hbo_e : globN s "bo" = globN entry "bo" :=
    globN_eq_of_lookup (h.globals (ofString "bo") (by decide))
  have hbo24_s : memW s (globN s "bo" + 24) = memW entry (globN entry "bo" + 24) :=
    ptx_entry_bo_field_eq hWT_e0 h.globals h.records h.ready_entry.1.2.1 (by simp) (by omega)
  have hbo80_s : memW s (globN s "bo" + 80) = memW entry (globN entry "bo" + 80) :=
    ptx_entry_bo_field_eq hWT_e0 h.globals h.records h.ready_entry.1.2.1 (by simp) (by omega)
  obtain ⟨S_s, Nd_s, hWT_s, _⟩ := hRs.2.2.2.2
  obtain ⟨hWT_p, _, _⟩ := PtxP1.store_encArray_world h.world.1 hEs hWT_s hx_dom hin hm
  have hAp : ArenaReady post := ⟨guestInv_congr (s := s) rfl rfl rfl rfl h.world.1.1, h.world.1.2⟩
  have hWp : WorldOK post := ⟨hAp, S_s, (worldTyped_iff_with post S_s).2 ⟨Nd_s, hWT_p⟩⟩
  have hx_nat : x.toNat = memW s (globN s "bo" + 24) + 16 * locN s "index" + 8 := by
    change evalAt s (.op .add
      [.load .one (.op .add [.var .global (ofString "bo"), .const 24]),
        .panop .mul [.var .local (ofString "index"), .const 16], .const 8]) = _ at hx_ev
    rcases hld : evalAt s (.load .one (.op .add [.var .global (ofString "bo"), .const 24])) with _ | vbase
    · simp only [evalAt, evalHOLExact, evalListHOLExact] at hx_ev hld; rw [hld] at hx_ev; simp at hx_ev
    obtain ⟨abase, rfl, habase_nat⟩ := evalAt_loadG s "bo" 24 vbase hld
    have habase : abase.toNat = memW s (globN s "bo" + 24) := habase_nat
    simp only [evalAt, evalHOLExact, evalListHOLExact] at hx_ev hld
    rw [hld] at hx_ev
    rcases hidx_v : s.locals.lookup (ofString "index") with _ | vidx
    · simp [hidx_v] at hx_ev
    rcases vidx with ⟨⟨idx_bv⟩⟩ | _ | _
    · simp only [hidx_v, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self,
        ↓reduceIte, panOpHOL, wordOpHOL, wordOp, List.foldr, Option.some.injEq,
        ValueHOL.val.injEq, HolWordLab.word.injEq] at hx_ev
      have hidx_nat : locN s "index" = idx_bv.toNat := by simp [locN, hidx_v]
      have hhi := (R13Shards.ivl_allocated_bound h.world.1.2 (PtxP1.encArray_words hWT_s.2.2.1 hEs).1).2
      dsimp only [PtxP1.encArray] at hhi
      have hhl_arr : memW s (globN s "bo" + 24) + (16 * memW s (globN s "bo" + 80) + 16) ≤ 2 ^ 64 := by
        have h1 : heapLimit ≤ 2 ^ 64 := by rw [WkBlockTxEnc.heapLimit_val]; decide
        have h2 : scratchEnd ≤ 2 ^ 64 := by rw [WkBlockTxEnc.scratchEnd_val]; decide
        omega
      have hidx_lt : idx_bv.toNat < memW s (globN s "bo" + 80) := hidx_nat ▸ hEs.idx_lt
      rw [← hx_ev]
      simp only [BitVec.toNat_add, BitVec.toNat_mul]
      have hz0 : (0 : BitVec 64).toNat = 0 := by decide
      have h16 : (16 : BitVec 64).toNat = 16 := by decide
      have h24 : (24 : BitVec 64).toNat = 24 := by decide
      have h8 : (8 : BitVec 64).toNat = 8 := by decide
      rw [hz0]
      simp only [h16, h24, h8] at *
      omega
    · simp [hidx_v, valueIsWord] at hx_ev
    · simp [hidx_v, valueIsWord] at hx_ev
  obtain ⟨_, hbo_pw, hgb_rest, _, _⟩ := R13Shards.fixedObjects_disj_parts hWT_s.2.2.1
  obtain ⟨_, _, hbo_eq⟩ := R13Shards.blockOutObjects_eq_list hEs hWT_s.1
  have hbo_len : (blockOutObjects s).length = 7 := by rw [hbo_eq]; rfl
  have h0_eq : (blockOutObjects s)[0] = PtxP1.encArray s := by simp [hbo_eq, PtxP1.encArray, hEs.bo_nz, hEs.bo24]
  have hbo_idx_disj : ∀ (j : Nat) (hj : j < (blockOutObjects s).length), 0 < j →
      Disj (blockOutObjects s)[j] (PtxP1.encArray s) := by
    intro j hj hgt
    have hget := List.pairwise_iff_getElem.1 hbo_pw
    exact R13Shards.disj_symm (h0_eq ▸ hget 0 j (by omega) hj hgt)
  have hm_ne_ivl : ∀ iv : Ivl, Disj iv (PtxP1.encArray s) → Allocated s iv →
      ∀ off, off + 8 ≤ iv.2 → memW post (iv.1 + off) = memW s (iv.1 + off) := by
    intro iv hd hal off hoff
    have hhi_iv := (R13Shards.ivl_allocated_bound h.world.1.2 hal).2
    have hhl_64 : iv.1 + iv.2 ≤ 2 ^ 64 := by
      have h1 : heapLimit ≤ 2 ^ 64 := by rw [WkBlockTxEnc.heapLimit_val]; decide
      have h2 : scratchEnd ≤ 2 ^ 64 := by rw [WkBlockTxEnc.scratchEnd_val]; decide
      omega
    have hlt64 : iv.1 + off < 2 ^ 64 := by omega
    have hne : BitVec.ofNat 64 (iv.1 + off) ≠ x := by
      intro heq
      have htonat := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64] at htonat
      have hd_x := R13Shards.disj_of_inside_right hin hd
      rcases hd_x with h0 | h0 | hd1 | hd2 <;> (dsimp only at *; omega)
    unfold memW; dsimp only [post]; rw [hm _ hne]
  have hbo_disj_arr : Disj (globN s "bo", 88) (PtxP1.encArray s) :=
    hgb_rest _ (List.mem_map.2 ⟨("bo", 88), by decide, by simp [hEs.bo_nz]⟩) _
      (List.mem_append_left _ (List.mem_append_right _ (PtxP1.encArray_mem_block hEs)))
  have hbo_al : Allocated s (globN s "bo", 88) := (R13Shards.bo_words hWT_s.2.2.1 hEs.bo_nz).1
  have hbo_mem : ∀ off, off + 8 ≤ 88 → memW post (globN s "bo" + off) = memW s (globN s "bo" + off) :=
    hm_ne_ivl (globN s "bo", 88) hbo_disj_arr hbo_al
  have h40_disj : Disj (memW s (globN s "bo" + 40), 24) (PtxP1.encArray s) := by
    have h3 : (blockOutObjects s)[3] = (memW s (globN s "bo" + 40), 24) := by simp [hbo_eq]
    exact h3 ▸ hbo_idx_disj 3 (by omega) (by omega)
  have h72_disj : Disj (memW s (globN s "bo" + 72), 24) (PtxP1.encArray s) := by
    have h5 : (blockOutObjects s)[5] = (memW s (globN s "bo" + 72), 24) := by simp [hbo_eq]
    exact h5 ▸ hbo_idx_disj 5 (by omega) (by omega)
  have h32_disj : Disj (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16) (PtxP1.encArray s) := by
    have h1 : (blockOutObjects s)[1] = (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16) := by
      simp [hbo_eq, hEs.bo_nz, hEs.bo32]
    exact h1 ▸ hbo_idx_disj 1 (by omega) (by omega)
  have h40_al : Allocated s (memW s (globN s "bo" + 40), 24) :=
    ((hWT_s.2.2.1.1 _ (List.mem_append_left _ (List.mem_append_right _ (by simp [blockOutObjects, hEs.bo_nz, hEs.bo40])))).resolve_left (by simp)).1
  have h72_al : Allocated s (memW s (globN s "bo" + 72), 24) :=
    ((hWT_s.2.2.1.1 _ (List.mem_append_left _ (List.mem_append_right _ (by simp [blockOutObjects, hEs.bo_nz, hEs.bo72])))).resolve_left (by simp)).1
  have h32_al : Allocated s (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16) :=
    ((hWT_s.2.2.1.1 _ (List.mem_append_left _ (List.mem_append_right _ (by simp [blockOutObjects, hEs.bo_nz, hEs.bo32])))).resolve_left (by simp)).1
  have hhi_arr := (R13Shards.ivl_allocated_bound h.world.1.2 (PtxP1.encArray_words hWT_s.2.2.1 hEs).1).2
  dsimp only [PtxP1.encArray] at hhi_arr
  have hhl_64 : memW s (globN s "bo" + 24) + (16 * memW s (globN s "bo" + 80) + 16) ≤ 2 ^ 64 := by
    have h1 : heapLimit ≤ 2 ^ 64 := by rw [WkBlockTxEnc.heapLimit_val]; decide
    have h2 : scratchEnd ≤ 2 ^ 64 := by rw [WkBlockTxEnc.scratchEnd_val]; decide
    omega
  refine ⟨h.ready_entry, h.arena_entry, h.frame_entry, h.scratch_entry, hWp, h.heap_entry, h.globals, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rec hrec hnz off hoff hno
    have hrec_eq : memW post (globN entry rec.1 + off) = memW s (globN entry rec.1 + off) := by
      have hge : globN s rec.1 = globN entry rec.1 := by
        simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
        rcases hrec with rfl | rfl | rfl | rfl
        · exact globN_eq_of_lookup (h.globals (ofString "ws") (by decide))
        · exact globN_eq_of_lookup (h.globals (ofString "bs") (by decide))
        · simp at hoff
        · exact hbo_e
      rw [← hge]
      have hnz_s : globN s rec.1 ≠ 0 := by rwa [hge]
      simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · have hd := hgb_rest (globN s "ws", 40) (List.mem_map.2 ⟨("ws", 40), by decide, by dsimp only; rw [if_neg hnz_s]⟩) _
          (List.mem_append_left _ (List.mem_append_right _ (PtxP1.encArray_mem_block hEs)))
        have hal := ((hWT_s.2.2.1.1 (globN s "ws", 40) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_map.2 ⟨("ws", 40), by decide, by dsimp only; rw [if_neg hnz_s]⟩))))).resolve_left (by simp)).1
        exact hm_ne_ivl (globN s "ws", 40) hd hal off (by simp at hoff; omega)
      · have hd := hgb_rest (globN s "bs", 80) (List.mem_map.2 ⟨("bs", 80), by decide, by dsimp only; rw [if_neg hnz_s]⟩) _
          (List.mem_append_left _ (List.mem_append_right _ (PtxP1.encArray_mem_block hEs)))
        have hal := ((hWT_s.2.2.1.1 (globN s "bs", 80) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_map.2 ⟨("bs", 80), by decide, by dsimp only; rw [if_neg hnz_s]⟩))))).resolve_left (by simp)).1
        exact hm_ne_ivl (globN s "bs", 80) hd hal off (by simp at hoff; omega)
      · simp at hoff
      · exact hbo_mem off (by simp at hoff; omega)
    exact hrec_eq.trans (h.records rec hrec hnz off hoff hno)
  · change memW post (memW post (globN s "bo" + 72)) ≠ 0
    have h72_0 : memW post (memW s (globN s "bo" + 72)) = memW s (memW s (globN s "bo" + 72)) := by
      simpa using hm_ne_ivl _ h72_disj h72_al 0 (by omega)
    rw [hbo_mem 72 (by omega), h72_0]
    exact h.rcpt_backing
  · change memW post (memW post (globN s "bo" + 40)) ≠ 0
    have h40_0 : memW post (memW s (globN s "bo" + 40)) = memW s (memW s (globN s "bo" + 40)) := by
      simpa using hm_ne_ivl _ h40_disj h40_al 0 (by omega)
    rw [hbo_mem 40 (by omega), h40_0]
    exact h.log_backing
  · change memW post (memW post (globN s "bo" + 72) + 8) = _
    rw [hbo_mem 72 (by omega), hm_ne_ivl _ h72_disj h72_al 8 (by omega)]
    exact h.rcpt_len_eq
  · intro off hoff i hi
    change memW post (memW post (globN s "bo" + off) + 16 * i + 8) = _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl
    · rw [hbo_mem 24 (by omega)]
      have hi_lt : i < memW s (globN s "bo" + 80) := by have := hEs.idx_lt; omega
      have hlt64 : memW s (globN s "bo" + 24) + 16 * i + 8 < 2 ^ 64 := by omega
      have hne : BitVec.ofNat 64 (memW s (globN s "bo" + 24) + 16 * i + 8) ≠ x := by
        intro heq
        have htonat := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64, hx_nat, hidx_eq] at htonat
        omega
      have hm_eq : memW post (memW s (globN s "bo" + 24) + 16 * i + 8) =
          memW s (memW s (globN s "bo" + 24) + 16 * i + 8) := by
        unfold memW at hne ⊢; dsimp only [post]; rw [hm _ hne]
      exact hm_eq.trans (h.slices_prev 24 (by simp) i hi)
    · rw [hbo_mem 32 (by omega)]
      have hi_lt : i < memW s (globN s "bo" + 80) := by have := hEs.idx_lt; omega
      have hm_eq : memW post (memW s (globN s "bo" + 32) + 16 * i + 8) =
          memW s (memW s (globN s "bo" + 32) + 16 * i + 8) := by
        simpa [Nat.add_assoc] using hm_ne_ivl _ h32_disj h32_al (16 * i + 8) (by omega)
      exact hm_eq.trans (h.slices_prev 32 (by simp) i hi)
  · intro _
    change memW post (memW post (globN s "bo" + 24) + 16 * locN entry "index" + 8) < 2 ^ 40
    rw [hbo_mem 24 (by omega), ← hidx_eq, ← hx_nat]
    have hbv_x : BitVec.ofNat 64 x.toNat = x := BitVec.ofNat_toNat 64 x |>.trans rfl
    unfold memW; dsimp only [post]
    rw [hbv_x, hmem_x]
    exact hb_lt
  · intro S0 Nd0 hWT0 hD0
    obtain ⟨Sc, Nc, hsub, hWc, hOG, hFO⟩ := h.typing S0 Nd0 hWT0 hD0
    obtain ⟨hWc_p, how_c, _⟩ := PtxP1.store_encArray_world h.world.1 hEs hWc hx_dom hin hm
    have hOG_p : OwnedGrows entry post (worldOwned entry S0 Nd0) (worldOwned post Sc Nc) := by
      unfold OwnedGrows at hOG ⊢
      rw [how_c]; exact hOG
    have harr_e : PtxP1.encArray entry ∈ worldOwned entry S0 Nd0 :=
      List.mem_append_left _ (List.mem_append_right _ (PtxP1.encArray_mem_fixed (PtxP1.txEnv_of_ready h.ready_entry)))
    have harr_eq : PtxP1.encArray s = PtxP1.encArray entry := by
      unfold PtxP1.encArray; rw [hbo24_s, hbo80_s]
    have hFO_p : FrameOutside entry post (worldOwned entry S0 Nd0 ++ ptxRegions entry ++ [freeGap entry]) (heapFree entry) := by
      intro a ha hhf
      have hne_x : a ≠ x := by
        intro rfl
        apply ha (PtxP1.encArray entry) (List.mem_append_left _ (List.mem_append_left _ harr_e))
        rw [← harr_eq]
        unfold CellHits; unfold Inside at hin; omega
      exact (hm a hne_x).trans (hFO a ha hhf)
    exact ⟨Sc, Nc, hsub, hWc_p, hOG_p, hFO_p⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
