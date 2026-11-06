import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.WkGetAccount
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.AccountWk
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.U256DivWs
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.BlobGasPrice
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.EncodeTransaction
import InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover.RecoverSender
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.U256WsSpecs
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_calculate_total_blob_gas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_fee_mul
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_item
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_min
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_sub
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.wk_memzero
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M29.zv_memzero
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01AllocMpt
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01Memcpy
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.RlpMemcpyLemmas
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard06b
import InitECandidate.Solver.Wave8GuestInv.R13Shards.PtxPhase45R11
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PtxPhase1R11
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PtxPhase34R11
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalInitFresh
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2Strong
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PayloadWorldHelpers
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.RlpWord

/-!
# R16k Shard `WkBlockTxProcess`: Block & Transaction Execution `wk_*` Contracts

Standalone complete proofs in `InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk`,
matching the frozen statements in `ContractParts/C08.lean` verbatim.
-/

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

/-! ## 1. Pure Read-Only Helpers & `WorldKeepsSc` Bridges -/

private theorem noCallee_good :
    ∀ f, (fun (_ : MlS) => false) f = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs) →
      roProgR16 (fun _ => false) body = true :=
  fun _ hf => by cases hf

private theorem ro_u256_fits_word : ReadOnlyFn (ofString "u256_fits_word") :=
  readOnlyFn_of_roProgR16 41 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_fits_word rfl (fun _ => false) noCallee_good (by decide)

private theorem ro_u256_lt : ReadOnlyFn (ofString "u256_lt") :=
  readOnlyFn_of_roProgR16 46 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_lt rfl (fun _ => false) noCallee_good (by decide)

private theorem ro_calculate_total_blob_gas : ReadOnlyFn (ofString "calculate_total_blob_gas") := by
  rcases Wave8Contracts.M14.ro_calculate_total_blob_gas with ⟨ps, body, ret, hl, hrun⟩
  exact ⟨ps, body, ret, hl, fun s hc hp _ hnt => hrun s hc hp hnt⟩

private theorem ro_fee_mul : ReadOnlyFn (ofString "fee_mul") := by
  rcases Wave8Contracts.M14.ro_fee_mul with ⟨ps, body, ret, hl, hrun⟩
  exact ⟨ps, body, ret, hl, fun s hc hp _ hnt => hrun s hc hp hnt⟩

private theorem ro_u256_add_carry : ReadOnlyFn (ofString "u256_add_carry") :=
  Wave8Contracts.M18.readOnlyFn_of_guestAst 55 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_add_carry rfl (fun _ => false) (fun _ h => by cases h) rfl

private theorem ro_u256_add : ReadOnlyFn (ofString "u256_add") :=
  Wave8Contracts.M18.readOnlyFn_of_guestAst 56 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_add rfl (fun _ => false) (fun _ h => by cases h) rfl

theorem ro_frame_state_gas_used : ReadOnlyFn (ofString "frame_state_gas_used") :=
  readOnlyFn_of_roProgR16 451 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_frame_state_gas_used rfl (fun _ => false) noCallee_good (by decide)

private theorem ro_is_valid_delegation : ReadOnlyFn (ofString "is_valid_delegation") :=
  readOnlyFn_of_roProgR16 446 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_is_valid_delegation rfl (fun _ => false) noCallee_good (by decide)

/-! ## 2. Self-Contained `wkSc_calculate_blob_gas_price` -/

private theorem lookup_u256_div_local :
    originalRuntimeCode.lookup (ofString "u256_div") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]),
             (ofString "b", .comb [.one, .one, .one, .one])],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_u256_div).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 70 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_div) rfl

private theorem lookup_taylor_exponential_local :
    originalRuntimeCode.lookup (ofString "taylor_exponential") =
      some ([(ofString "factor", .one), (ofString "numerator", .one), (ofString "denominator", .one)],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_taylor_exponential).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 232 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_taylor_exponential) rfl

private theorem lookup_calculate_blob_gas_price_local :
    originalRuntimeCode.lookup (ofString "calculate_blob_gas_price") =
      some ([(ofString "excess_blob_gas", .one)],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_calculate_blob_gas_price).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 233 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_calculate_blob_gas_price) rfl

private theorem lookup_two_comb4_b_local {fname : MlS} {body0 : ProgHOL 64} {retSh : ShapeHOL}
    (hlk : originalRuntimeCode.lookup fname =
      some ([(ofString "a", .comb [.one, .one, .one, .one]),
             (ofString "b", .comb [.one, .one, .one, .one])], body0, retSh))
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs)) :
    body = body0 ∧
    (∃ b0 b1 b2 b3, callee.lookup (ofString "b") =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)])) := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, hlk, List.length] at hraw
  rcases vals with _ | ⟨va, _ | ⟨vb, _ | _⟩⟩
  · simp at hraw
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = body0 := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      obtain ⟨b0, b1, b2, b3, rfl⟩ := eval_comb4_of_shape (Or.inl hshapes.2.2.2)
      refine ⟨hb, ⟨b0, b1, b2, b3, ?_⟩⟩
      simpa [FUPDATE_LIST, FUPDATE] using congrFun hfn (ofString "b")
    · simp at hraw
  · simp [List.length] at hraw

private theorem call_u256_divmod_wsSafe_local {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "u256_divmod") vals = some (body, callee, rs)) :
    WsSafe (callEntryStateHOLFinite s callee) (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body) := by
  rw [he.code] at hl
  obtain ⟨rfl, ⟨b0, b1, b2, b3, hb_c⟩⟩ := lookup_two_comb4_b_local lookup_u256_divmod hl
  exact u256_divmod_wsSafe (he.with_locals_clock callee _) hb_c

private theorem call_u256_div_wsSafe_local {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "u256_div") vals = some (body, callee, rs)) :
    WsSafe (callEntryStateHOLFinite s callee) (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body) := by
  rw [he.code] at hl
  obtain ⟨rfl, _⟩ := lookup_two_comb4_b_local lookup_u256_div_local hl
  dsimp only [extractFn, Guest.Software.guestFn_u256_div,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map]
  refine WsSafe.decCall ?_ ?_
  · intro vals' body' callee' rs' _ hl' _
    exact call_u256_divmod_wsSafe_local (he.with_locals_clock callee _) hl'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _
    exact WsSafe.return_exp _ _ _

private theorem wsSafe_call_local_aux {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {nm : MlS} {fname : MlS} {args : List (ExpHOL 64)}
    (hcal : ∀ vals body callee rs,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals →
      lookupCodeHOLFinite s.code.lookup fname vals = some (body, callee, rs) →
      s.clock ≠ 0 →
      WsSafe (callEntryStateHOLFinite s callee) Rl
        (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body)) :
    WsSafe s Rl (evaluateHOLFiniteState s (.call (some (some (.local, nm), none)) fname args)) := by
  rw [evaluateHOLFiniteState_call]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
    · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    · dsimp only
      by_cases hz : s.clock = 0
      · rw [if_pos hz]
        exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
      · rw [if_neg hz]
        have hc := hcal vals body callee rs hargs hl hz
        have he_ce : Wave8Contracts.M23.ByteRegionEffect s (callEntryStateHOLFinite s callee) Rl :=
          (Wave8Contracts.M23.ByteRegionEffect.refl s Rl).with_locals_clock callee (s.clock - 1)
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, cpost⟩
        rw [hrun] at hc
        cases rb with
        | none =>
          exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
        | some r0 =>
          cases r0 with
          | returned v =>
            have he_cp : Wave8Contracts.M23.ByteRegionEffect s cpost Rl := he_ce.trans (hc.2 (Or.inl ⟨v, rfl⟩))
            dsimp only
            split
            · split
              · exact ⟨fun _ => he_cp.with_locals_clock _ cpost.clock,
                  fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
              · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
            · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
          | exception eid ev =>
            exact ⟨fun h => by simp at h,
              fun hr => by
                rcases hr with ⟨_, h⟩ | ⟨e', v', h, hne⟩
                · simp at h
                · injection h with h'; injection h' with h1 h2; subst h1 h2
                  exact (he_ce.trans (hc.2 (Or.inr ⟨eid, ev, rfl, hne⟩))).with_locals_clock _ cpost.clock⟩
          | timeOut | error | «break» | «continue» | finalFfi _ =>
            exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

private theorem WsSafe_while_wsEnv_local {F : Type} {cond : ExpHOL 64} {body : ProgHOL 64}
    {s0 s : PanSemStateFiniteExact 64 F}
    (hnb : noTopBreakContinue body = true)
    (he : WsEnv s0 s)
    (hbody : ∀ t, WsEnv s0 t → WsSafe t (untypedGlobalBufIvls s0) (evaluateHOLFiniteState t body)) :
    WsSafe s (untypedGlobalBufIvls s0) (evaluateHOLFiniteState s (.while cond body)) :=
  WsSafe.while_loop hnb (fun t => WsEnv s0 t)
    (fun _ ht => ht.with_locals_clock _ _)
    (fun t _ ht _ _ =>
      let hs := hbody (decClockHOLFinite t) ht
      ⟨hs, fun hn => ht.step (hs.1 hn)⟩)
    s he

private theorem wsEnv_setVar_local {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) (nm : MlS) (v : ValueHOL 64) :
    WsEnv s0 (setVarHOLFinite nm v s) :=
  ⟨he.code, he.memaddrs, he.globals, he.ws_bnd⟩

private theorem taylor_exponential_wsSafe_local {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) :
    WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
          (extractFn Guest.Software.guestFn_taylor_exponential).body)) := by
  dsimp only [extractFn, Guest.Software.guestFn_taylor_exponential,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  refine WsSafe.decCall_ro he (by decide) fun _ _ he1 _ _ => ?_
  refine WsSafe.decCall_ro he1 (by decide) fun _ _ he2 _ _ => ?_
  refine WsSafe.decCall_ro he2 (by decide) fun _ _ he3 _ _ => ?_
  refine WsSafe.seq (WsSafe.of_readOnly he3.code (by decide)) fun _ heff_m => ?_
  have he4 := he3.step heff_m
  refine WsSafe.dec fun v_out _ _ => ?_
  have he4a := wsEnv_setVar_local he4 (ofString "out") v_out
  refine WsSafe.dec fun v_i _ _ => ?_
  have he4b := wsEnv_setVar_local he4a (ofString "i") v_i
  refine WsSafe.dec fun v_zero _ _ => ?_
  have he5 := wsEnv_setVar_local he4b (ofString "zero") v_zero
  refine WsSafe.decCall_ro he5 (by decide) fun _ _ he6 _ _ => ?_
  refine WsSafe.seq (WsSafe_while_wsEnv_local (by decide) he6 fun t ht => ?_) ?_
  · refine WsSafe.seq (WsSafe.of_readOnly ht.code (by decide)) fun _ heff_a => ?_
    have ht1 := ht.step heff_a
    refine WsSafe.decCall_ro ht1 (by decide) fun _ _ ht2 _ _ => ?_
    refine WsSafe.seq (WsSafe.of_readOnly ht2.code (by decide)) fun _ heff_t => ?_
    have ht3 := ht2.step heff_t
    refine WsSafe.dec fun v_p _ _ => ?_
    have ht4 := wsEnv_setVar_local ht3 (ofString "p") v_p
    refine WsSafe.decCall_ro ht4 (by decide) fun _ _ ht5 _ _ => ?_
    refine WsSafe.seq (WsSafe.of_readOnly ht5.code (by decide)) fun _ heff_dm => ?_
    have ht6 := ht5.step heff_dm
    refine WsSafe.seq (wsSafe_call_local_aux fun _ _ _ _ _ hl _ => call_u256_div_wsSafe_local ht6 hl)
      fun _ heff_dv => ?_
    have ht7 := ht6.step heff_dv
    refine WsSafe.seq (WsSafe.assign_local _ _ _ _) fun _ heff_inc => ?_
    have ht8 := ht7.step heff_inc
    exact WsSafe.of_readOnly ht8.code (by decide)
  · intro _ heff_w
    have he7 := he6.step heff_w
    refine WsSafe.seq (wsSafe_call_local_aux fun _ _ _ _ _ hl _ => call_u256_div_wsSafe_local he7 hl)
      fun _ _ => ?_
    exact WsSafe.return_exp _ _ _

private theorem wsEnv_of_worldOK_local {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s) : WsEnv s s := by
  refine ⟨hc, hW.1.1.memaddrs, rfl, ?_⟩
  by_cases hz : globN s "u256_ws" = 0
  · exact Or.inl hz
  · obtain ⟨hAR, _, _, _, hFT, _⟩ := hW
    have hmem : (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640) ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨("u256_ws", 640), by decide, rfl⟩
    rw [if_neg hz] at hmem
    rcases hFT.1 _ hmem with h0 | ⟨hal, _⟩
    · dsimp only at h0; omega
    · have hhl : heapLimit ≤ 2 ^ 64 := by rw [WkBlockTxEnc.heapLimit_val]; decide
      have hse : scratchEnd ≤ 2 ^ 64 := by rw [WkBlockTxEnc.scratchEnd_val]; decide
      obtain ⟨_, hhp_hi, _, hfp_sp, _⟩ := hAR.2
      rcases hal with ⟨_, hhi⟩ | ⟨_, hhi⟩ <;> (dsimp only at hhi; exact Or.inr (by omega))

private theorem heapByteEff_of_m23_bre_local {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl}
    (hAR : ArenaReady s) (heff : Wave8Contracts.M23.ByteRegionEffect s post Rl) :
    HeapByteEff s post Rl [] := by
  have hG : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAR.1
  have hA : ArenaOK post := arenaOK_congr heff.globals hAR.2
  have hg_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  refine ⟨⟨hG, hA⟩, heff.memaddrs, by rw [hg_eq], hg_eq _, by rw [hg_eq], heff.be,
    fun k _ => by rw [heff.globals], ?_, ?_, ?_⟩
  · intro a hne; by_contra hna; exact hne (heff.out_dom a hna)
  · intro a hne; left
    have hdom : ordinaryDomain a := by
      rw [← hAR.1.memaddrs]; by_contra hna; exact hne (heff.out_dom a hna)
    have ha_ord := (WkBlockTxEnc.ordinaryDomain_iff a).1 hdom
    have hhe_lt : heapEnd ≤ 2 ^ 64 := by rw [WkBlockTxEnc.heapEnd_val]; decide
    by_contra hno
    apply hne
    apply mem_eq_of_bytes_eq heff.be a hdom
    intro k hk
    apply heff.byte_frame (a.toNat + k) (by omega)
    intro i hi ⟨hb1, hb2⟩
    exact hno ⟨i, hi, by omega, by omega, by omega⟩
  · intro b hb hne; left
    by_contra hno
    apply hne; apply heff.byte_frame b hb
    intro i hi hin; exact hno ⟨i, hi, hin⟩

private theorem wk_calculate_blob_gas_price_local :
    WorldKeeps WorldOK (fun s => [(globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "calculate_blob_gas_price") := by
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
  exact HeapByteEff.to_worldStep
    [("sk_buf", 64), ("keccak_pad", 136), ("keccak_st", 200), ("mpt_nib_scratch", 64)]
    (by decide) (by simp) hW heff_hb (fun _ _ _ _ _ => trivial)

private theorem wkSc_calculate_blob_gas_price :
    WorldKeepsSc WorldOK (bufRegions [("u256_ws", 640)]) [] stdKeep NoExtra
      (ofString "calculate_blob_gas_price") := by
  obtain ⟨ps, body, ret, hl, hb⟩ := wk_calculate_blob_gas_price_local
  refine ⟨ps, body, ret, hl, fun s hc hW hex hnt hres => ?_⟩
  have hstep := hb s hc hW hex hnt hres
  have hsp_eq : globN (evaluateHOLFiniteState s body).2 "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (hstep.2.2.1 (ofString "scratch_ptr") (by decide))
  exact ⟨hstep, by rw [hsp_eq]⟩

/-! ## 3. Theorem 1: `«wk_check_transaction»` -/

private theorem lookup_check_transaction :
    originalRuntimeCode.lookup (ofString "check_transaction") =
      some ((sourceFunctionEntry Guest.Software.guestFn_check_transaction).2) :=
  lookup_of_guestAst_getElem 872 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_check_transaction) rfl

private abbrev checkTxBufs : BufList :=
  [("keccak_pad", 136), ("keccak_st", 200), ("mpt_nib_scratch", 64), ("sk_buf", 52), ("u256_ws", 640)]

private theorem validBufList_checkTxBufs : ValidBufList checkTxBufs := by
  intro p hp
  simp only [checkTxBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact ⟨136, by decide, by decide, by decide⟩
  · exact ⟨200, by decide, by decide, by decide⟩
  · exact ⟨64, by decide, by decide, by decide⟩
  · exact ⟨64, by decide, by decide, by decide⟩
  · exact ⟨640, by decide, by decide, by decide⟩

private theorem safeStepGlobals_checkTx : SafeStepGlobals ["heap_ptr", "scratch_ptr"] := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> simp

private theorem wkSc_check_transaction :
    WorldKeepsSc WorldOK (bufRegions checkTxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      (ofString "check_transaction") := by
  have hB := validBufList_checkTxBufs
  have hgw := safeStepGlobals_checkTx
  have hB0 : ∀ p ∈ ([] : BufList), p ∈ checkTxBufs := by intro p hp; cases hp
  have hgw0 : ∀ g ∈ ([] : List String), g ∈ ["heap_ptr", "scratch_ptr"] := by intro g hg; cases hg
  refine worldKeepsSc_of_progWStep lookup_check_transaction ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_check_transaction,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_dec ?_ -- block_gas_limit
  refine progWStep_dec ?_ -- regular_avail
  refine progWStep_dec ?_ -- state_avail
  refine progWStep_dec ?_ -- blob_avail
  refine progWStep_dec ?_ -- gas
  refine progWStep_decCall hB hgw hB0 hgw0
    (worldKeepsSc_of_readOnly Wave8Contracts.M15.ro_min) ?_ -- capped = min(...)
  refine progWStep_seq hB hgw (progWStep_ite (progWStep_raise _ _ _ _) (progWStep_skip _ _)) ?_
  refine progWStep_seq hB hgw (progWStep_ite (progWStep_raise _ _ _ _) (progWStep_skip _ _)) ?_
  refine progWStep_decCall hB hgw hB0 hgw0
    (worldKeepsSc_of_readOnly ro_calculate_total_blob_gas) ?_ -- tx_blob_gas
  refine progWStep_seq hB hgw (progWStep_ite (progWStep_raise _ _ _ _) (progWStep_skip _ _)) ?_
  refine progWStep_decCall hB hgw
    (by intro p hp; simp [wsAcctBufs, checkTxBufs] at hp ⊢
        rcases hp with rfl | rfl | rfl <;> simp)
    (fun _ h => h)
    wkSc_get_account ?_ -- acct = get_account(sender)
  refine progWStep_dec ?_ -- base_fee
  refine progWStep_dec ?_ -- price
  refine progWStep_dec ?_ -- max_fee_per_gas
  refine progWStep_dec ?_ -- ty
  refine progWStep_seq hB hgw ?_ ?_
  · -- if ty == 0 || ty == 1
    refine progWStep_ite ?_ ?_
    · refine progWStep_dec ?_ -- gp
      refine progWStep_decCall hB hgw hB0 hgw0 (worldKeepsSc_of_readOnly ro_u256_lt) ?_
      refine progWStep_seq hB hgw (progWStep_ite (progWStep_raise _ _ _ _) (progWStep_skip _ _)) ?_
      refine progWStep_seq hB hgw (progWStep_assign_local _ _ _ _) (progWStep_assign_local _ _ _ _)
    · refine progWStep_dec ?_ -- mf
      refine progWStep_dec ?_ -- mp
      refine progWStep_decCall hB hgw hB0 hgw0 (worldKeepsSc_of_readOnly ro_u256_lt) ?_
      refine progWStep_seq hB hgw (progWStep_ite (progWStep_raise _ _ _ _) (progWStep_skip _ _)) ?_
      refine progWStep_decCall hB hgw hB0 hgw0 (worldKeepsSc_of_readOnly ro_u256_lt) ?_
      refine progWStep_seq hB hgw (progWStep_ite (progWStep_raise _ _ _ _) (progWStep_skip _ _)) ?_
      refine progWStep_decCall hB hgw hB0 hgw0
        (worldKeepsSc_of_readOnly Wave8Contracts.M18.ro_u256_sub) ?_
      refine progWStep_decCall hB hgw hB0 hgw0 (worldKeepsSc_of_readOnly ro_u256_lt) ?_
      refine progWStep_dec ?_ -- prio
      refine progWStep_seq hB hgw
        (progWStep_ite (progWStep_assign_local _ _ _ _) (progWStep_skip _ _)) ?_
      refine progWStep_seq hB hgw
        (progWStep_call_local hB0 hgw0 (worldKeepsSc_of_readOnly ro_u256_add))
        (progWStep_assign_local _ _ _ _)
  · refine progWStep_decCall hB hgw hB0 hgw0 (worldKeepsSc_of_readOnly ro_fee_mul) ?_
    refine progWStep_dec ?_ -- ovf
    refine progWStep_dec ?_ -- max_gas_fee
    refine progWStep_seq hB hgw ?_ ?_
    · -- if ty == 3
      refine progWStep_ite ?_ (progWStep_skip _ _)
      refine progWStep_dec ?_ -- nb
      refine progWStep_seq hB hgw (progWStep_ite (progWStep_raise _ _ _ _) (progWStep_skip _ _)) ?_
      refine progWStep_seq hB hgw (progWStep_ite (progWStep_raise _ _ _ _) (progWStep_skip _ _)) ?_
      refine progWStep_dec ?_ -- j
      refine progWStep_seq hB hgw
        (progWStep_while hB hgw
          (progWStep_seq hB hgw
            (progWStep_ite (progWStep_raise _ _ _ _) (progWStep_skip _ _))
            (progWStep_assign_local _ _ _ _))) ?_
      refine progWStep_decCall hB hgw
        (by intro p hp; simp at hp; subst hp; simp [checkTxBufs])
        hgw0
        wkSc_calculate_blob_gas_price ?_
      refine progWStep_dec ?_ -- mfb
      refine progWStep_decCall hB hgw hB0 hgw0 (worldKeepsSc_of_readOnly ro_u256_lt) ?_
      refine progWStep_seq hB hgw (progWStep_ite (progWStep_raise _ _ _ _) (progWStep_skip _ _)) ?_
      refine progWStep_decCall hB hgw hB0 hgw0 (worldKeepsSc_of_readOnly ro_fee_mul) ?_
      refine progWStep_seq hB hgw
        (progWStep_ite (progWStep_assign_local _ _ _ _) (progWStep_skip _ _)) ?_
      refine progWStep_decCall hB hgw hB0 hgw0 (worldKeepsSc_of_readOnly ro_u256_add_carry) ?_
      refine progWStep_seq hB hgw
        (progWStep_ite (progWStep_assign_local _ _ _ _) (progWStep_skip _ _))
        (progWStep_assign_local _ _ _ _)
    · refine progWStep_seq hB hgw
        (progWStep_ite
          (progWStep_ite (progWStep_raise _ _ _ _) (progWStep_skip _ _))
          (progWStep_skip _ _)) ?_
      refine progWStep_dec ?_ -- tn
      refine progWStep_decCall hB hgw hB0 hgw0 (worldKeepsSc_of_readOnly ro_u256_fits_word) ?_
      refine progWStep_dec ?_ -- an
      refine progWStep_seq hB hgw (progWStep_ite (progWStep_raise _ _ _ _) (progWStep_skip _ _)) ?_
      refine progWStep_seq hB hgw (progWStep_ite (progWStep_raise _ _ _ _) (progWStep_skip _ _)) ?_
      refine progWStep_seq hB hgw (progWStep_ite (progWStep_raise _ _ _ _) (progWStep_skip _ _)) ?_
      refine progWStep_seq hB hgw (progWStep_ite (progWStep_raise _ _ _ _) (progWStep_skip _ _)) ?_
      refine progWStep_decCall hB hgw hB0 hgw0 (worldKeepsSc_of_readOnly ro_u256_add_carry) ?_
      refine progWStep_seq hB hgw (progWStep_ite (progWStep_raise _ _ _ _) (progWStep_skip _ _)) ?_
      refine progWStep_decCall hB hgw hB0 hgw0 (worldKeepsSc_of_readOnly ro_u256_lt) ?_
      refine progWStep_seq hB hgw (progWStep_ite (progWStep_raise _ _ _ _) (progWStep_skip _ _)) ?_
      refine progWStep_decCall hB hgw
        (by intro p hp; simp at hp; subst hp; simp [checkTxBufs])
        (by intro g hg; simp at hg; subst hg; simp)
        wkSc_get_code ?_
      refine progWStep_decCall hB hgw hB0 hgw0
        (worldKeepsSc_of_readOnly EvmFrameSpecs.ro_memeq) ?_
      refine progWStep_seq hB hgw ?_ (progWStep_return _ _ _)
      refine progWStep_ite ?_ (progWStep_skip _ _)
      refine progWStep_decCall hB hgw hB0 hgw0
        (worldKeepsSc_of_readOnly ro_is_valid_delegation) ?_
      exact progWStep_ite (progWStep_raise _ _ _ _) (progWStep_skip _ _)

/-- `check_transaction` (AST line 32951): relational world step with output region. -/
theorem «wk_check_transaction» :
    WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
    ["heap_ptr", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "check_transaction") :=
  wkSc_check_transaction.to_worldKeeps

def PmcLogsLiveOwned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (logs : Nat) : Prop :=
  logs ≠ 0 →
    Allocated s (memW s logs, 8 * memW s (logs + 8)) ∧
    IvlsDisj [(logs, 24), (memW s logs, 8 * memW s (logs + 8))] (worldOwned s S Nd) ∧
    ∀ i, i < memW s (logs + 8) →
      IvlsDisj (logOwnedIvls s (memW s (memW s logs + 8 * i))) (worldOwned s S Nd)

def PmcLogsDisjOut {F : Type} (s post : PanSemStateFiniteExact 64 F) (logs : Nat) : Prop :=
  logs ≠ 0 →
    (Inside (logs, 24) (globN post "scratch_ptr") scratchEnd ∨
      Inside (logs, 24) (globN s "heap_ptr") (globN post "heap_ptr")) ∧
    (Inside (memW post logs, 8 * memW post (logs + 8)) (globN post "scratch_ptr") scratchEnd ∨
      Inside (memW post logs, 8 * memW post (logs + 8)) (globN s "heap_ptr") (globN post "heap_ptr")) ∧
    ∀ i, i < memW post (logs + 8) →
      Inside (memW post (memW post logs + 8 * i), 40) (globN s "heap_ptr") (globN post "heap_ptr")

def RetFrameResultStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S Nd => RetFrameResult s r post S Nd ∧
    ∀ v, r = some (.returned v) → ∃ w : BitVec 64,
      v = .val (.word w) ∧
      Inside (w.toNat, 280) (globN post "scratch_ptr") scratchEnd ∧
      IvlsDisj [(w.toNat, 280)] (worldOwned post S Nd) ∧
      PmcLogsLiveOwned post S Nd (memW post (w.toNat + 88)) ∧
      PmcLogsDisjOut s post (memW post (w.toNat + 88))

theorem worldStepIn_mono_extra
    {T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q Q' : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    (hQ : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) r post S Nd,
      Q s r post S Nd → Q' s r post S Nd)
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (h : WorldStepIn T R gw keep Q s r post) :
    WorldStepIn T R gw keep Q' s r post := by
  obtain ⟨hA, hH, hG, hK, hW⟩ := h
  refine ⟨hA, hH, hG, hK, ?_⟩
  intro S Nd hT hTS hD
  obtain ⟨S', Nd', hsub, hWT, hOG, hFO, hret⟩ := hW S Nd hT hTS hD
  exact ⟨S', Nd', hsub, hWT, hOG, hFO, hQ s r post S' Nd' hret⟩

def RetMessageOutputStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S Nd => RetMessageOutput s r post S Nd ∧
    ∀ v, r = some (.returned v) → ∃ w : BitVec 64,
      v = .val (.word w) ∧ PmcLogsLiveOwned post S Nd (memW post (w.toNat + 16))

def RetFrameMarksPost {F : Type}
    (s : PanSemStateFiniteExact 64 F) (r : Option (PanSemResultExact 64))
    (post : PanSemStateFiniteExact 64 F) : Prop :=
  globN s "frame_mem_ptr" ≤ globN post "frame_mem_ptr" ∧
  globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
  ∀ v, r = some (.returned v) → ∃ w : BitVec 64,
    v = .val (.word w) ∧
    memW post (w.toNat + 208) ≤ globN s "scratch_ptr" ∧
    memW post (w.toNat + 224) = globN s "frame_mem_ptr" ∧
    memW post (w.toNat + 224) ≤ memW post (w.toNat + 208) ∧
    memW post (w.toNat + 208) % 8 = 0 ∧
    memW post (w.toNat + 128) ≤ scratchEnd

def RetFrameResultMarks : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S Nd => RetFrameResultStrong s r post S Nd ∧ RetFrameMarksPost s r post

def RetFrameResultMarksExact : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S Nd =>
    RetFrameResultMarks s r post S Nd ∧
    ∀ v, r = some (.returned v) → ∃ w : BitVec 64,
      v = .val (.word w) ∧
      memW post (w.toNat + 208) = globN s "scratch_ptr"

def PmcMarksPost {F : Type}
    (s : PanSemStateFiniteExact 64 F) (r : Option (PanSemResultExact 64))
    (post : PanSemStateFiniteExact 64 F) : Prop :=
  globN s "frame_mem_ptr" ≤ globN post "frame_mem_ptr" ∧
  globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
  ∀ v, r = some (.returned v) → ∃ w : BitVec 64,
    v = .val (.word w) ∧
    Inside (w.toNat, 96) (globN s "heap_ptr") (globN post "heap_ptr") ∧
    memW post (w.toNat + 48) ≤ scratchEnd ∧
    (memW post (w.toNat + 80) ≠ 0 →
      memW post (w.toNat + 80) ≤ globN s "scratch_ptr" ∧
      memW post (w.toNat + 88) = globN s "frame_mem_ptr" ∧
      memW post (w.toNat + 88) ≤ memW post (w.toNat + 80) ∧
      memW post (w.toNat + 80) % 8 = 0 ∧
      (memW s (locN s "msg" + 24) ≠ 0 →
        memW post (w.toNat + 80) = globN s "scratch_ptr"))

def RetMessageOutputMarks : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S Nd => RetMessageOutputStrong s r post S Nd ∧ PmcMarksPost s r post

theorem worldKeepsIn_mono_extra
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q Q' : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {fname : MlS}
    (hQ : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) r post S Nd,
      Q s r post S Nd → Q' s r post S Nd)
    (h : WorldKeepsIn P T R gw keep Q fname) :
    WorldKeepsIn P T R gw keep Q' fname := by
  obtain ⟨ps, body, ret, hl, hb⟩ := h
  refine ⟨ps, body, ret, hl, fun s hc hp hex hnt hr => ?_⟩
  exact worldStepIn_mono_extra hQ (hb s hc hp hex hnt hr)

theorem worldKeepsIn_of_strong_message_output
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)} {fname : MlS}
    (h : WorldKeepsIn P T R gw keep RetMessageOutputStrong fname) :
    WorldKeepsIn P T R gw keep RetMessageOutput fname :=
  worldKeepsIn_mono_extra (fun _ _ _ _ _ hret => hret.1) h

theorem pmcLogsLiveOwned_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) : PmcLogsLiveOwned s S Nd 0 := by
  intro h
  exact (h rfl).elim

theorem pmcLogsLiveOwned_disjFixed {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {logs : Nat} (h : PmcLogsLiveOwned s S Nd logs) :
    LogsDisjFixed s logs := by
  by_cases hz : logs = 0
  · exact Or.inl hz
  · obtain ⟨halloc, hhead, hentry⟩ := h hz
    refine Or.inr ⟨halloc, ?_⟩
    intro i hi j hj
    have hjw : j ∈ worldOwned s S Nd :=
      List.mem_append_left _ (List.mem_append_right _ hj)
    rcases List.mem_append.mp hi with hi | hi
    · exact hhead i hi j hjw
    · obtain ⟨k, hk, hi⟩ := List.mem_flatMap.mp hi
      exact hentry k (List.mem_range.mp hk) i hi j hjw

theorem pmcLogsLiveOwned_mono_world {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd S' Nd' : List Nat} {logs : Nat}
    (hsub : ∀ i ∈ worldOwned s S' Nd', i ∈ worldOwned s S Nd)
    (h : PmcLogsLiveOwned s S Nd logs) : PmcLogsLiveOwned s S' Nd' logs := by
  intro hnz
  obtain ⟨halloc, hhead, hentry⟩ := h hnz
  exact ⟨halloc, fun i hi j hj => hhead i hi j (hsub j hj),
    fun k hk i hi j hj => hentry k hk i hi j (hsub j hj)⟩

theorem retFrameResultStrong_logsDisjFixed {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {S Nd : List Nat} (h : RetFrameResultStrong s r post S Nd)
    {v : ValueHOL 64} (hr : r = some (.returned v)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      LogsListOK post (memW post (w.toNat + 88)) ∧
      LogsDisjFixed post (memW post (w.toNat + 88)) := by
  obtain ⟨w, hw, _, _, hlogs⟩ := h.1 v hr
  obtain ⟨w', hw', _, _, howned, _⟩ := h.2 v hr
  have heq : w = w' := by cases hw.symm.trans hw'; rfl
  subst w'
  exact ⟨w, hw, hlogs, pmcLogsLiveOwned_disjFixed howned⟩

theorem worldKeepsIn_of_strong_frame_result
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)} {fname : MlS}
    (h : WorldKeepsIn P T R gw keep RetFrameResultStrong fname) :
    WorldKeepsIn P T R gw keep RetFrameResult fname :=
  worldKeepsIn_mono_extra (fun _ _ _ _ _ hret => hret.1) h

theorem pmc_logOwnedIvls_eq_of_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {log : Nat}
    (hAs : ArenaOK s) (hl : LogEntryOK s log)
    (hu : R13Shards.IvlUnhit s post (log, 40))
    (hsys : globN post "vm_system_address" = globN s "vm_system_address") :
    logOwnedIvls post log = logOwnedIvls s log := by
  have hb := (R13Shards.ivl_allocated_bound hAs (Or.inl hl.2.1)).2
  have ha := hl.1.1
  have hm : ∀ k ∈ ([0, 8, 16, 24, 32] : List Nat),
      memW post (log + k) = memW s (log + k) := by
    intro k hk
    apply R13Shards.memW_eq_of_ivlUnhit hu
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    · exact hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> (constructor <;> omega)
  have h0 : memW post log = memW s log := by simpa using hm 0 (by simp)
  simp only [logOwnedIvls, logRecordIvls, hsys, h0,
    hm 8 (by simp), hm 16 (by simp), hm 24 (by simp), hm 32 (by simp)]

theorem pmc_logsListOK_congr_live {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {logs : Nat} (hAs : ArenaOK s) (hgS : GuestInv s) (hgP : GuestInv post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (h : LogsListOK s logs)
    (halloc : Allocated s (logs, 24) → Allocated post (logs, 24))
    (hhead : ∀ k ∈ ([0, 8, 16] : List Nat),
      memW post (logs + k) = memW s (logs + k))
    (hptr : ∀ i, i < memW s (logs + 8) →
      memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i))
    (hentry : ∀ i, i < memW s (logs + 8) →
      R13Shards.IvlUnhit s post (memW s (memW s logs + 8 * i), 40)) :
    LogsListOK post logs := by
  rcases h with hz | ⟨hw, ha, hn, hc, he⟩
  · exact Or.inl hz
  have h0 : memW post logs = memW s logs := by simpa using hhead 0 (by simp)
  have h8 := hhead 8 (by simp)
  have h16 := hhead 16 (by simp)
  refine Or.inr ⟨R13Shards.wordsOK_transfer hgS hgP hw, halloc ha, ?_, ?_, ?_⟩
  · rw [h8]; exact hn
  · rw [h8, h16]; exact hc
  · intro i hi
    rw [h8] at hi
    rw [h0, hptr i hi]
    exact ⟨R13Shards.wordAt_transfer hgS hgP (he i hi).1,
      R13Shards.logEntryOK_congr_unhit hAs hgS hgP hhp (he i hi).2 (hentry i hi)⟩

theorem pmcLogsLiveOwned_congr_live {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd S' Nd' : List Nat} {logs : Nat}
    (hAs : ArenaOK s) (hl : LogsListOK s logs)
    (h : PmcLogsLiveOwned s S Nd logs)
    (hworld : worldOwned post S' Nd' = worldOwned s S Nd)
    (hsys : globN post "vm_system_address" = globN s "vm_system_address")
    (halloc : Allocated s (memW s logs, 8 * memW s (logs + 8)) →
      Allocated post (memW s logs, 8 * memW s (logs + 8)))
    (hhead : ∀ k ∈ ([0, 8] : List Nat),
      memW post (logs + k) = memW s (logs + k))
    (hptr : ∀ i, i < memW s (logs + 8) →
      memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i))
    (hentry : ∀ i, i < memW s (logs + 8) →
      R13Shards.IvlUnhit s post (memW s (memW s logs + 8 * i), 40)) :
    PmcLogsLiveOwned post S' Nd' logs := by
  intro hnz
  obtain ⟨ha, hd, he⟩ := h hnz
  have h0 : memW post logs = memW s logs := by simpa using hhead 0 (by simp)
  have h8 := hhead 8 (by simp)
  rcases hl with hz | hl
  · exact (hnz hz).elim
  refine ⟨?_, ?_, ?_⟩
  · rw [h0, h8]
    exact halloc ha
  · rw [h0, h8, hworld]
    exact hd
  · intro i hi
    rw [h8] at hi
    rw [h0, hptr i hi, pmc_logOwnedIvls_eq_of_unhit hAs (hl.2.2.2.2 i hi).2
      (hentry i hi) hsys, hworld]
    exact he i hi

def ptxRegions {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)]

def ptxGlobals : List String :=
  ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]

def ptxKeep : List (String × List Nat) :=
  [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
   ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]

def PtxRelRun {F : Type} (entry : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) (s : PanSemStateFiniteExact 64 F) : Prop :=
  Resumes (evaluateHOLFiniteState s p).1 →
    WorldStep ptxRegions ptxGlobals ptxKeep RetTransactionLogs entry
      (evaluateHOLFiniteState s p).1 (evaluateHOLFiniteState s p).2

def PtxRelCut (phase : ProgHOL 64 → ProgHOL 64)
    (A B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop) : Prop :=
  ∀ {F : Type} (entry : PanSemStateFiniteExact 64 F) (tail : ProgHOL 64),
    (∀ s : PanSemStateFiniteExact 64 F, s.code = originalRuntimeCode →
      B entry s → PtxRelRun entry tail s) →
    ∀ s : PanSemStateFiniteExact 64 F, s.code = originalRuntimeCode →
      A entry s → PtxRelRun entry (phase tail) s

theorem wk_process_transaction_of
    (A0 A1 A2 A3 A4 : ∀ {F : Type},
      PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop)
    (hinit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), TxReadyStrong s → A0 s s)
    (h1 : PtxRelCut R13Shards.ptxPhase1 A0 A1)
    (h2 : PtxRelCut R13Shards.ptxPhase2 A1 A2)
    (h3 : PtxRelCut R13Shards.ptxPhase3 A2 A3)
    (h4 : PtxRelCut R13Shards.ptxPhase4 A3 A4)
    (h5 : ∀ {F : Type} (entry s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → A4 entry s → PtxRelRun entry R13Shards.ptxPhase5 s) :
    WorldKeeps TxReadyStrong
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]
      RetTransactionLogs (ofString "process_transaction") := by
  refine ⟨_, _, _, R13Shards.ptx_lookup, ?_⟩
  intro F s hcode hready _hparams _hnt
  have hb := h1 s _ (h2 s _ (h3 s _ (h4 s _ (h5 s)))) s hcode (hinit s hready)
  rw [← R13Shards.ptx_phases_eq] at hb
  unfold PtxRelRun R13Shards.ptxCode ptxRegions ptxGlobals ptxKeep at hb
  exact hb

def pmcTables {F : Type} (s : PanSemStateFiniteExact 64 F) : List Nat :=
  [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)]

def pmcRegions {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  (locN s "msg", 176) :: (ptxRegions s).take 1 ++ (ptxRegions s).drop 2

def pmcGlobals : List String :=
  ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]

def pmcKeep : List (String × List Nat) :=
  [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
   ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]

def pmcCode : ProgHOL 64 :=
  (sourceFunctionEntry Guest.Software.guestFn_process_message_call).2.2.1

def pmcInit (tail : ProgHOL 64) : ProgHOL 64 := R13Shards.spinePlug 4 pmcCode tail

def pmcDispatch (tail : ProgHOL 64) : ProgHOL 64 :=
  R13Shards.spinePlug 1 (R13Shards.spineAt 4 pmcCode) tail

def pmcPack : ProgHOL 64 := R13Shards.spineAt 5 pmcCode

theorem pmc_phases_eq : pmcCode = pmcInit (pmcDispatch pmcPack) := by
  unfold pmcInit pmcDispatch pmcPack
  rw [R13Shards.spinePlug_restore_at 4 1, R13Shards.spinePlug_restore]

theorem pmc_lookup : originalRuntimeCode.lookup (ofString "process_message_call") =
    some ((sourceFunctionEntry Guest.Software.guestFn_process_message_call).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 607 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_process_message_call) rfl

def PmcRelRun {F : Type} (entry : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) (s : PanSemStateFiniteExact 64 F) : Prop :=
  Resumes (evaluateHOLFiniteState s p).1 →
    WorldStepIn pmcTables pmcRegions pmcGlobals pmcKeep RetMessageOutput entry
      (evaluateHOLFiniteState s p).1 (evaluateHOLFiniteState s p).2

def PmcRelCut (phase : ProgHOL 64 → ProgHOL 64)
    (A B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop) : Prop :=
  ∀ {F : Type} (entry : PanSemStateFiniteExact 64 F) (tail : ProgHOL 64),
    (∀ s : PanSemStateFiniteExact 64 F, s.code = originalRuntimeCode →
      B entry s → PmcRelRun entry tail s) →
    ∀ s : PanSemStateFiniteExact 64 F, s.code = originalRuntimeCode →
      A entry s → PmcRelRun entry (phase tail) s

theorem wk_process_message_call_of
    (A0 A1 A2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop)
    (hinit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), MsgReady s → A0 s s)
    (hallocZero : PmcRelCut pmcInit A0 A1)
    (hdispatch : PmcRelCut pmcDispatch A1 A2)
    (hpack : ∀ {F : Type} (entry s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → A2 entry s → PmcRelRun entry pmcPack s) :
    WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => [(locN s "msg", 176), (globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetMessageOutput (ofString "process_message_call") := by
  refine ⟨_, _, _, pmc_lookup, ?_⟩
  intro F s hcode hready _hparams _hnt
  have hb := hallocZero s _ (hdispatch s _ (hpack s)) s hcode (hinit s hready)
  rw [← pmc_phases_eq] at hb
  unfold PmcRelRun pmcCode pmcTables pmcRegions ptxRegions pmcGlobals pmcKeep at hb
  exact hb

def PmcRelRunStrong {F : Type} (entry : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) (s : PanSemStateFiniteExact 64 F) : Prop :=
  Resumes (evaluateHOLFiniteState s p).1 →
    WorldStepIn pmcTables pmcRegions pmcGlobals pmcKeep RetMessageOutputStrong entry
      (evaluateHOLFiniteState s p).1 (evaluateHOLFiniteState s p).2

def PmcRelCutStrong (phase : ProgHOL 64 → ProgHOL 64)
    (A B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop) : Prop :=
  ∀ {F : Type} (entry : PanSemStateFiniteExact 64 F) (tail : ProgHOL 64),
    (∀ s : PanSemStateFiniteExact 64 F, s.code = originalRuntimeCode →
      B entry s → PmcRelRunStrong entry tail s) →
    ∀ s : PanSemStateFiniteExact 64 F, s.code = originalRuntimeCode →
      A entry s → PmcRelRunStrong entry (phase tail) s

theorem wk_process_message_call_strong_of
    (A0 A1 A2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop)
    (hinit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), MsgReady s → A0 s s)
    (hallocZero : PmcRelCutStrong pmcInit A0 A1)
    (hdispatch : PmcRelCutStrong pmcDispatch A1 A2)
    (hpack : ∀ {F : Type} (entry s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → A2 entry s → PmcRelRunStrong entry pmcPack s) :
    WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => [(locN s "msg", 176), (globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetMessageOutputStrong (ofString "process_message_call") := by
  refine ⟨_, _, _, pmc_lookup, ?_⟩
  intro F s hcode hready _hparams _hnt
  have hb := hallocZero s _ (hdispatch s _ (hpack s)) s hcode (hinit s hready)
  rw [← pmc_phases_eq] at hb
  unfold PmcRelRunStrong pmcCode pmcTables pmcRegions ptxRegions pmcGlobals pmcKeep at hb
  exact hb

private theorem wk_alloc_local :
    WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc") :=
  R13Shards.wk_alloc_impl

private theorem rt_alloc_local :
    Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc") :=
  R13Shards.rt_alloc_impl

private theorem wk_memzero_local :
    WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")])
      []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "memzero") :=
  Wave8Contracts.M08.«wk_memzero»

private theorem zv_memzero_local : ZeroFills (ofString "memzero") :=
  Wave8Contracts.M29.«zv_memzero»

/-! ## 6. Concrete `process_message_call` Phase Cuts & Callee Closure -/

def pmcBufs : BufList :=
  [("b2_v", 128), ("bn_expw", 352), ("bn_gamma", 384), ("evm_key_buf", 32),
   ("keccak_pad", 136), ("keccak_st", 200), ("mpt_nib_scratch", 64), ("pre_hdr_buf", 96),
   ("rmd_h", 40), ("rmd_pad", 128), ("rmd_x", 128), ("sha_pad", 128), ("sha_st", 64),
   ("sk_buf", 52), ("u256_ws", 640)]

theorem validBufList_pmcBufs : ValidBufList pmcBufs := by
  intro p hp
  simp only [pmcBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨128, by decide, by decide, le_rfl⟩
  · exact ⟨352, by decide, by decide, le_rfl⟩
  · exact ⟨384, by decide, by decide, le_rfl⟩
  · exact ⟨32, by decide, by decide, le_rfl⟩
  · exact ⟨136, by decide, by decide, le_rfl⟩
  · exact ⟨200, by decide, by decide, le_rfl⟩
  · exact ⟨64, by decide, by decide, le_rfl⟩
  · exact ⟨96, by decide, by decide, le_rfl⟩
  · exact ⟨40, by decide, by decide, le_rfl⟩
  · exact ⟨128, by decide, by decide, le_rfl⟩
  · exact ⟨128, by decide, by decide, le_rfl⟩
  · exact ⟨128, by decide, by decide, le_rfl⟩
  · exact ⟨64, by decide, by decide, le_rfl⟩
  · exact ⟨64, by decide, by decide, by decide⟩
  · exact ⟨640, by decide, by decide, le_rfl⟩

theorem pmcRegions_eq_bufRegions {F : Type} (s : PanSemStateFiniteExact 64 F) :
    pmcRegions s = (locN s "msg", 176) :: bufRegions pmcBufs s := rfl

theorem pmcRegions_disj_of_msgReady {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    (hm_disj : ∀ o ∈ worldOwned s S Nd, Disj (locN s "msg", 176) o) :
    IvlsDisj (pmcRegions s) (worldTypedIvls s S Nd) := by
  rw [pmcRegions_eq_bufRegions]
  intro x hx j hj
  rcases List.mem_cons.1 hx with rfl | hx_buf
  · exact hm_disj j (worldTypedIvls_sub_worldOwned s S Nd j hj)
  · exact validBufList_disj validBufList_pmcBufs hW x hx_buf j hj

theorem pmcRegions_zero_aligned {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hm8 : locN s "msg" % 8 = 0) :
    ∀ j ∈ pmcRegions s, j.2 = 0 → j.1 % 8 = 0 := by
  rw [pmcRegions_eq_bufRegions]
  intro j hj hz
  rcases List.mem_cons.1 hj with rfl | hj_buf
  · exact hm8
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj_buf
    simp only [pmcBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [bufferRegion] at hz ⊢
      split at hz
      · rename_i h0; rw [h0]
      · cases hz

theorem allocated_ivl_survives_step_local {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {old new R : List Ivl} {b : Ivl}
    (hAs : ArenaOK s) (hAp : ArenaOK post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hold0 : ∀ j ∈ old, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post old new)
    (hfr : FrameOutside s post (old ++ R ++ [freeGap s]) (heapFree s))
    (hb1 : b.1 % 8 = 0) (hb2 : b.2 % 8 = 0)
    (hb : Allocated s b) (hold : ∀ j ∈ old, Disj b j)
    (hR : ∀ j ∈ R, Disj b j) :
    Allocated post b ∧ (∀ o ∈ new, Disj b o) ∧ IvlUnhit s post b := by
  have hag : AllocatorGrows s post := ⟨hhp, hsp⟩
  refine ⟨hag.allocated hb, ?_⟩
  rcases hb with hh | hs
  · exact (heap_ivl_survives_step hAs hhp hog hfr hold0 hR0 hb1 hb2 hh hold hR).2
  have hsep : heapLimit ≤ scratchStart := by decide
  have hfm := hAs.2.2.1
  have hsc := hAs.2.2.2.1
  have hhp_lim := hAs.2.1
  have hhpp_lim := hAp.2.1
  constructor
  · intro o ho
    rcases hog o ho with rfl | ⟨j, hj, hin⟩ | hfresh
    · exact disj_zero_right b
    · exact disj_of_inside_right hin (hold j hj)
    · exact Or.inr (Or.inr (Or.inr (by unfold Inside at hfresh hs; omega)))
  · intro a ha8 hhit
    apply hfr a
    · intro j hj hcj
      rcases List.mem_append.1 hj with hj12 | hfg
      · rcases List.mem_append.1 hj12 with ho | hr
        · exact not_cellHits_of_disj hb1 hb2 ha8 (hold0 j ho) hhit (hold j ho) hcj
        · exact not_cellHits_of_disj hb1 hb2 ha8 (hR0 j hr) hhit (hR j hr) hcj
      · simp only [List.mem_singleton] at hfg; subst hfg
        obtain ⟨hc1, hc2⟩ := hhit
        obtain ⟨hj1, hj2⟩ := hcj
        unfold freeGap at hj1 hj2
        unfold Inside at hs
        dsimp at hj1 hj2
        omega
    · intro ⟨hf1, hf2⟩
      obtain ⟨hc1, hc2⟩ := hhit
      unfold heapFree at hf1 hf2
      unfold Inside at hs
      dsimp at hf1 hf2
      omega

theorem worldStepIn_pmc_trans_prefix {F : Type}
    {R1 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {Q1 Q Q_out : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s1 s2 s3 : PanSemStateFiniteExact 64 F}
    {r1 r2 : Option (PanSemResultExact 64)}
    {w_out : BitVec 64}
    (hmsg_eq : locN s2 "msg" = locN s1 "msg")
    (hm8 : locN s1 "msg" % 8 = 0)
    (hm_in1 : Inside (locN s1 "msg", 176) sourceBase (globN s1 "heap_ptr"))
    (hm_fix1 : ∀ j ∈ fixedObjects s1, Disj (locN s1 "msg", 176) j)
    (hA1 : ArenaReady s1)
    (hWOK1 : WorldOK s1)
    (hR1_z : ∀ j ∈ R1 s1, j.2 = 0 → j.1 % 8 = 0)
    (hR1_sub : ∀ j ∈ R1 s1, j ∈ bufRegions pmcBufs s1 ∨
      Inside j (globN s1 "heap_ptr") (globN s2 "heap_ptr"))
    (hw_out8 : w_out.toNat % 8 = 0)
    (hw_in12 : Inside (w_out.toNat, 96) (globN s1 "heap_ptr") (globN s2 "heap_ptr"))
    (hQ1_out : ∀ S2 Nd2, Q1 s1 r1 s2 S2 Nd2 →
      IvlsDisj [(w_out.toNat, 96)] (worldOwned s2 S2 Nd2))
    (h12 : WorldStep R1 ["heap_ptr", "scratch_ptr"] pmcKeep Q1 s1 r1 s2)
    (hsp12 : globN s2 "scratch_ptr" ≤ globN s1 "scratch_ptr")
    (h23 : WorldStepIn pmcTables pmcRegions pmcGlobals pmcKeep Q s2 r2 s3)
    (hQ_out : ∀ S3 Nd3,
      IvlsDisj [(w_out.toNat, 96)] (worldOwned s3 S3 Nd3) →
      IvlUnhit s2 s3 (w_out.toNat, 96) →
      Q s2 r2 s3 S3 Nd3 →
      Q_out s1 r2 s3 S3 Nd3) :
    WorldStepIn pmcTables pmcRegions pmcGlobals pmcKeep Q_out s1 r2 s3 := by
  obtain ⟨hA2, hhp12, hG12, hK12, hW12⟩ := h12
  obtain ⟨hA3, hhp23, hG23, hK23, hW23⟩ := h23
  have hsafe : SafeStepGlobals ["heap_ptr", "scratch_ptr"] := by
    intro g hg; simp at hg ⊢; rcases hg with rfl | rfl <;> simp
  have hbuf21 : bufRegions pmcBufs s2 = bufRegions pmcBufs s1 :=
    bufRegions_eq_of_safeGlobals validBufList_pmcBufs hsafe hG12
  have hreg21 : pmcRegions s2 = pmcRegions s1 := by
    rw [pmcRegions_eq_bufRegions, pmcRegions_eq_bufRegions, hmsg_eq, hbuf21]
  have hfmp12 : globN s1 "frame_mem_ptr" = globN s2 "frame_mem_ptr" :=
    (globN_eq_of_lookup (hG12 (ofString "frame_mem_ptr") (by decide))).symm
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, S_ok, hWT_ok0⟩ := hWOK1
  obtain ⟨Nd_ok, hWT_ok⟩ := (worldTyped_iff_with s1 S_ok).1 hWT_ok0
  have hrec_not_fresh : ∀ rec ∈ pmcKeep, globN s1 rec.1 ≠ 0 → ∀ off ∈ rec.2,
      ∀ i : Ivl, Inside i (globN s1 "heap_ptr") (globN s2 "heap_ptr") →
      ¬ CellHits (globN s1 rec.1 + off) i := by
    intro rec hrec hnz off hoff i hi_fresh ⟨hc1, hc2⟩
    have ⟨sz, htr, hoff_lt⟩ : ∃ sz, (rec.1, sz) ∈ typedRecords ∧ off + 8 ≤ sz := by
      simp only [pmcKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by simp [typedRecords], ?_⟩; simp at hoff; omega
      · refine ⟨80, by simp [typedRecords], ?_⟩; simp at hoff; omega
      · refine ⟨72, by simp [typedRecords], ?_⟩; simp at hoff; omega
      · refine ⟨88, by simp [typedRecords], ?_⟩; simp at hoff; omega
    have hfix_mem := typedRecord_mem_fixedObjects s1 htr
    simp only [hnz, ↓reduceIte] at hfix_mem
    rcases hWT_ok.2.2.1.1 (globN s1 rec.1, sz) hfix_mem with hz | ⟨hal, _⟩
    · dsimp at hz; omega
    · rcases hal with ⟨_, hhi⟩ | ⟨hlo, _⟩
      · dsimp at hhi; unfold Inside at hi_fresh; omega
      · dsimp at hlo; unfold Inside at hi_fresh
        have := hA1.2.2.1; have := hA2.2.2.1; have := hA1.2.2.2.1; have := hA1.2.2.2.2.1
        omega
  refine ⟨hA3, le_trans hhp12 hhp23, ?_, ?_, ?_⟩
  · intro k hk
    have hk12 : k ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString := by
      intro hm; apply hk
      simp only [List.mem_map, pmcGlobals] at hm ⊢
      obtain ⟨g, hg, rfl⟩ := hm
      refine ⟨g, ?_, rfl⟩
      simp at hg; rcases hg with rfl | rfl <;> simp
    exact (hG12 k hk12).trans (hG23 k hk)
  · intro rec hrec hnz off hoff hno
    have hrec_ne : ofString rec.1 ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString := by
      simp only [pmcKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl <;> decide
    have hg_rec : globN s2 rec.1 = globN s1 rec.1 :=
      globN_eq_of_lookup (hG12 (ofString rec.1) hrec_ne)
    have h2 := hK23 rec hrec (by rw [hg_rec]; exact hnz) off hoff
      (by change ∀ i ∈ pmcRegions s2, ¬ CellHits (globN s2 rec.1 + off) i
          rw [hreg21, hg_rec]; exact hno)
    have h1 := hK12 rec hrec hnz off hoff (fun i hi hch => by
      rcases hR1_sub i hi with hi_buf | hi_fresh
      · exact hno i (by change i ∈ pmcRegions s1; rw [pmcRegions_eq_bufRegions]; exact List.mem_cons_of_mem _ hi_buf) hch
      · exact hrec_not_fresh rec hrec hnz off hoff i hi_fresh hch)
    rw [hg_rec] at h2
    exact h2.trans h1
  · intro S Nd hWT1 hT1 hD1
    have hD1_R1 : IvlsDisj (R1 s1) (worldTypedIvls s1 S Nd) := by
      intro x hx j hj
      rcases hR1_sub x hx with hx_buf | hx_fresh
      · exact validBufList_disj validBufList_pmcBufs hWT1 x hx_buf j hj
      · rcases worldOwned_zero_or_allocated hWT1 j (worldTypedIvls_sub_worldOwned s1 S Nd j hj) with
            rfl | ⟨_, hal_j⟩
        · exact disj_zero_right x
        · rcases hal_j with ⟨_, hhi_j⟩ | ⟨hlo_j, _⟩
          · exact Or.inr (Or.inr (Or.inr (Nat.le_trans hhi_j hx_fresh.1)))
          · exact Or.inr (Or.inr (Or.inl (by
              unfold Inside at hx_fresh
              have := hA1.2.2.1; have := hA2.2.2.1; have := hA1.2.2.2.1; have := hA1.2.2.2.2.1
              omega)))
    obtain ⟨S2, Nd2, hsub12, hWT2, hOG12, hFO12, hQ12⟩ := hW12 S Nd hWT1 hD1_R1
    have hm_disj_ow1 : ∀ j ∈ worldOwned s1 S Nd, Disj (locN s1 "msg", 176) j := by
      intro j hj
      unfold worldOwned at hj
      rcases List.mem_append.1 hj with h1 | hnd
      · rcases List.mem_append.1 h1 with htab | hfix
        · apply hD1 (locN s1 "msg", 176) (by simp [pmcRegions])
          unfold worldTypedIvls
          apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left
          exact List.mem_append.2 (Or.inl htab)
        · exact hm_fix1 j hfix
      · apply hD1 (locN s1 "msg", 176) (by simp [pmcRegions])
        unfold worldTypedIvls
        exact List.mem_append.2 (Or.inr hnd)
    have hm_disj_R1 : ∀ j ∈ R1 s1, Disj (locN s1 "msg", 176) j := by
      intro j hj
      rcases hR1_sub j hj with hj_buf | hj_fresh
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj_buf
        obtain ⟨sz, hgb, _, hle⟩ := validBufList_pmcBufs p hp
        have hfix_p : bufferRegion s1 (p.1, sz) ∈ fixedObjects s1 := by
          unfold fixedObjects
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
          exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
        have hd_sz := hm_fix1 _ hfix_p
        by_cases h0 : globN s1 p.1 = 0
        · simp [bufferRegion, h0]; exact disj_zero_right _
        · simp only [bufferRegion, h0, ↓reduceIte] at hd_sz ⊢
          exact disj_of_inside_right (j' := (globN s1 p.1, sz))
            ⟨le_rfl, by dsimp; omega⟩ hd_sz
      · exact Or.inr (Or.inr (Or.inl (Nat.le_trans hm_in1.2 hj_fresh.1)))
    obtain ⟨_, hm_disj_ow2, hm_u12⟩ :=
      heap_ivl_survives_step (b := (locN s1 "msg", 176)) hA1.2 hhp12 hOG12 hFO12
        (worldOwned_zero_aligned hWT1) hR1_z hm8 (by dsimp) hm_in1 hm_disj_ow1 hm_disj_R1
    have hm_hi : locN s1 "msg" + 176 ≤ 2 ^ 64 :=
      (ivl_allocated_bound hA1.2 (Or.inl hm_in1)).2
    have hm152_eq : memW s2 (locN s2 "msg" + 152) = memW s1 (locN s1 "msg" + 152) := by
      rw [hmsg_eq]
      exact memW_eq_of_ivlUnhit hm_u12 (by omega) hm_hi ⟨by dsimp; omega, by dsimp; omega⟩
    have hm160_eq : memW s2 (locN s2 "msg" + 160) = memW s1 (locN s1 "msg" + 160) := by
      rw [hmsg_eq]
      exact memW_eq_of_ivlUnhit hm_u12 (by omega) hm_hi ⟨by dsimp; omega, by dsimp; omega⟩
    have hT2 : ∀ t ∈ pmcTables s2, t ∈ S2 := by
      intro t ht
      simp only [pmcTables, hm152_eq, hm160_eq] at ht
      exact hsub12 t (hT1 t ht)
    have hD2 : IvlsDisj (pmcRegions s2) (worldTypedIvls s2 S2 Nd2) := by
      apply pmcRegions_disj_of_msgReady hWT2
      rw [hmsg_eq]
      exact hm_disj_ow2
    obtain ⟨S3, Nd3, hsub23, hWT3, hOG23, hFO23, hQ23⟩ := hW23 S2 Nd2 hWT2 hT2 hD2
    have hout_ow2 : IvlsDisj [(w_out.toNat, 96)] (worldOwned s2 S2 Nd2) := hQ1_out S2 Nd2 hQ12
    have hout_in2 : Inside (w_out.toNat, 96) sourceBase (globN s2 "heap_ptr") :=
      ⟨le_trans hA1.2.1 hw_in12.1, hw_in12.2⟩
    have hout_disj_R2 : ∀ j ∈ pmcRegions s2, Disj (w_out.toNat, 96) j := by
      rw [pmcRegions_eq_bufRegions]
      intro j hj
      rcases List.mem_cons.1 hj with rfl | hj_buf
      · rw [hmsg_eq]
        exact Or.inr (Or.inr (Or.inr (Nat.le_trans hm_in1.2 hw_in12.1)))
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj_buf
        obtain ⟨sz, hgb, _, hle⟩ := validBufList_pmcBufs p hp
        have hfix_p : bufferRegion s2 (p.1, sz) ∈ fixedObjects s2 := by
          unfold fixedObjects
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
          exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
        have hd_sz := hout_ow2 (w_out.toNat, 96) (by simp) _
          (by unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix_p))))
        by_cases h0 : globN s2 p.1 = 0
        · simp [bufferRegion, h0]; exact disj_zero_right _
        · simp only [bufferRegion, h0, ↓reduceIte] at hd_sz ⊢
          exact disj_of_inside_right (j' := (globN s2 p.1, sz))
            ⟨le_rfl, by dsimp; omega⟩ hd_sz
    obtain ⟨_, hout_ow3, hout_u23⟩ :=
      heap_ivl_survives_step (b := (w_out.toNat, 96))
        hA2.2 hhp23 hOG23 hFO23
        (worldOwned_zero_aligned hWT2)
        (pmcRegions_zero_aligned (by rw [hmsg_eq]; exact hm8))
        hw_out8 (by dsimp) hout_in2
        (fun j hj => hout_ow2 (w_out.toNat, 96) (by simp) j hj)
        hout_disj_R2
    refine ⟨S3, Nd3, fun t ht => hsub23 t (hsub12 t ht), hWT3, ?_, ?_,
      hQ_out S3 Nd3 (fun x hx j hj => by simp at hx; subst hx; exact hout_ow3 j hj) hout_u23 hQ23⟩
    · intro o ho
      rcases hOG23 o ho with rfl | ⟨j, hj, hin_oj⟩ | hin_o23
      · exact Or.inl rfl
      · rcases hOG12 j hj with rfl | ⟨k, hk, hin_jk⟩ | hin_j12
        · left
          rcases o with ⟨o1, o2⟩
          dsimp only [Inside] at hin_oj
          exact Prod.ext (by omega) (by omega)
        · exact Or.inr (Or.inl ⟨k, hk, le_trans hin_jk.1 hin_oj.1, le_trans hin_oj.2 hin_jk.2⟩)
        · exact Or.inr (Or.inr ⟨le_trans hin_j12.1 hin_oj.1,
            le_trans hin_oj.2 (le_trans hin_j12.2 hhp23)⟩)
      · exact Or.inr (Or.inr ⟨le_trans hhp12 hin_o23.1, hin_o23.2⟩)
    · intro a ha hhf
      have ha12 : ∀ i ∈ worldOwned s1 S Nd ++ R1 s1 ++ [freeGap s1], ¬ CellHits a.toNat i := by
        intro i hi hch
        rcases List.mem_append.1 hi with hi1 | hfg1
        · rcases List.mem_append.1 hi1 with hwo1 | hR1
          · exact ha i (List.mem_append_left _ (List.mem_append_left _ hwo1)) hch
          · rcases hR1_sub i hR1 with hi_buf | hi_fresh
            · exact ha i (List.mem_append_left _ (List.mem_append_right _
                (by change i ∈ pmcRegions s1; rw [pmcRegions_eq_bufRegions]; exact List.mem_cons_of_mem _ hi_buf))) hch
            · obtain ⟨hc1, hc2⟩ := hch
              have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
              exact hhf ⟨by unfold heapFree; dsimp only [Inside] at hi_fresh ⊢; omega,
                         by unfold heapFree; dsimp only [Inside] at hi_fresh ⊢; omega⟩
        · exact ha i (List.mem_append_right _ hfg1) hch
      have hm12 : s2.memory a = s1.memory a := hFO12 a ha12 hhf
      have hm23 : s3.memory a = s2.memory a := by
        apply hFO23 a
        · intro i hi hch
          obtain ⟨hc1, hc2⟩ := hch
          rcases List.mem_append.1 hi with hi1 | hfg2
          · rcases List.mem_append.1 hi1 with hwo2 | hR2
            · rcases hOG12 i hwo2 with rfl | ⟨k, hk, hin_ik⟩ | hin_i12
              · dsimp only at hc2; omega
              · exact ha k (List.mem_append_left _ (List.mem_append_left _ hk))
                  ⟨by dsimp only [Inside] at hin_ik; omega,
                   by dsimp only [Inside] at hin_ik; omega⟩
              · have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
                exact hhf ⟨by unfold heapFree; dsimp only [Inside] at hin_i12 ⊢; omega,
                           by unfold heapFree; dsimp only [Inside] at hin_i12 ⊢; omega⟩
            · change i ∈ pmcRegions s2 at hR2
              rw [hreg21] at hR2
              exact ha i (List.mem_append_left _ (List.mem_append_right _ hR2)) ⟨hc1, hc2⟩
          · simp only [List.mem_singleton] at hfg2; subst hfg2
            exact ha (freeGap s1) (List.mem_append_right _ (List.mem_singleton.2 rfl))
              ⟨by
                have hc1' : a.toNat + 8 > globN s2 "frame_mem_ptr" := hc1
                change a.toNat + 8 > globN s1 "frame_mem_ptr"
                omega,
               by
                have hc2' : a.toNat < globN s2 "frame_mem_ptr" + (globN s2 "scratch_ptr" - globN s2 "frame_mem_ptr") := hc2
                have hfmp_sp2 : globN s2 "frame_mem_ptr" ≤ globN s2 "scratch_ptr" := hA2.2.2.2.2.1
                change a.toNat < globN s1 "frame_mem_ptr" + (globN s1 "scratch_ptr" - globN s1 "frame_mem_ptr")
                omega⟩
        · intro ⟨hc1, hc2⟩
          have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
          exact hhf ⟨by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega,
                     by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega⟩
      exact hm23.trans hm12

theorem worldStepIn_pmc_store_out_word {F : Type}
    {Q1 Q2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {entry s : PanSemStateFiniteExact 64 F}
    {r r' : Option (PanSemResultExact 64)}
    {w_out x : BitVec 64} {mem' : BitVec 64 → HolWordLab 64}
    (hstep : WorldStepIn pmcTables pmcRegions pmcGlobals pmcKeep
      (fun en rr st S' Nd' =>
        IvlsDisj [(w_out.toNat, 96)] (worldOwned st S' Nd') ∧ Q1 en rr st S' Nd')
      entry r s)
    (hen_WOK : WorldOK entry)
    (hw_in : Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s "heap_ptr"))
    (hx_in : w_out.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ w_out.toNat + 96)
    (hx_dom : s.memaddrs x)
    (hm_eq : ∀ a : BitVec 64, a ≠ x → mem' a = s.memory a)
    (hQ' : ∀ S' Nd',
      WorldTypedWith s S' Nd' →
      WorldTypedWith { s with memory := mem' } S' Nd' →
      worldOwned { s with memory := mem' } S' Nd' = worldOwned s S' Nd' →
      IvlsDisj [(w_out.toNat, 96)] (worldOwned s S' Nd') →
      Q1 entry r s S' Nd' →
      Q2 entry r' { s with memory := mem' } S' Nd') :
    WorldStepIn pmcTables pmcRegions pmcGlobals pmcKeep
      (fun en rr st S' Nd' =>
        IvlsDisj [(w_out.toNat, 96)] (worldOwned st S' Nd') ∧ Q2 en rr st S' Nd')
      entry r' { s with memory := mem' } := by
  let post : PanSemStateFiniteExact 64 F := { s with memory := mem' }
  obtain ⟨hen_AR, S_en, hWT_en0⟩ := hen_WOK
  obtain ⟨Nd_en, hWT_en⟩ := (worldTyped_iff_with entry S_en).1 hWT_en0
  obtain ⟨hAs, hhp, hG, hK, hW⟩ := hstep
  have hx_ord : x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
    rw [hAs.1.memaddrs, ordinaryDomain_iff] at hx_dom; exact hx_dom
  have hhp_s_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have hsep : heapLimit ≤ scratchStart := by decide
  have hx_hf : CellHits x.toNat (heapFree entry) := by
    unfold CellHits heapFree
    dsimp only [Inside] at hw_in ⊢
    omega
  have hgP : GuestInv post := ⟨hAs.1.code, hAs.1.memaddrs, hAs.1.shMemaddrs, hAs.1.baseAddr⟩
  have hAp : ArenaReady post := ⟨hgP, hAs.2⟩
  refine ⟨hAp, hhp, hG, ?_, ?_⟩
  · intro rec hrec hnz off hoff hno
    have hprev := hK rec hrec hnz off hoff hno
    have hrec_sz : ∃ sz, (rec.1, sz) ∈ typedRecords ∧ off % 8 = 0 ∧ off + 8 ≤ sz := by
      simp only [pmcKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by simp [typedRecords], ?_, ?_⟩ <;> (simp at hoff; omega)
      · refine ⟨80, by simp [typedRecords], ?_, ?_⟩ <;> (simp at hoff; omega)
      · refine ⟨72, by simp [typedRecords], ?_, ?_⟩ <;> (simp at hoff; omega)
      · refine ⟨88, by simp [typedRecords], ?_, ?_⟩ <;> (simp at hoff; omega)
    obtain ⟨sz, htr, hoff8, hoff_lt⟩ := hrec_sz
    have hfix_mem := typedRecord_mem_fixedObjects entry htr
    simp only [hnz, ↓reduceIte] at hfix_mem
    have hne : BitVec.ofNat 64 (globN entry rec.1 + off) ≠ x := by
      intro heq
      rcases hWT_en.2.2.1.1 (globN entry rec.1, sz) hfix_mem with hz | ⟨hal, _⟩
      · dsimp at hz; omega
      · have hhi_rec := (ivl_allocated_bound hen_AR.2 hal).2
        have hlt64 : globN entry rec.1 + off < 2 ^ 64 := by dsimp at hhi_rec; omega
        have hnat : globN entry rec.1 + off = x.toNat := by
          have := congrArg BitVec.toNat heq
          rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64] at this
        rcases hal with ⟨_, hhi⟩ | ⟨hlo, _⟩
        · dsimp at hhi; dsimp only [Inside] at hw_in; omega
        · dsimp at hlo; dsimp only [Inside] at hw_in
          have := hen_AR.2.2.1; have := hen_AR.2.2.2.1; have := hen_AR.2.2.2.2.1
          omega
    unfold memW
    change (match mem' (BitVec.ofNat 64 (globN entry rec.1 + off)) with | .word w => w.toNat) = _
    rw [hm_eq _ hne]
    exact hprev
  · intro S Nd hWT hT hD
    obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hout_disj, hQ0⟩ := hW S Nd hWT hT hD
    have hdisj_x : ∀ j ∈ worldTypedIvls s S' Nd', Disj j (x.toNat, 8) := by
      intro j hj
      have hj_ow := worldTypedIvls_sub_worldOwned s S' Nd' j hj
      have hd96 := (hout_disj (w_out.toNat, 96) (by simp) j hj_ow).flip
      exact disj_of_inside_right (j' := (w_out.toNat, 96)) ⟨hx_in.1, hx_in.2⟩ hd96
    obtain ⟨_, hWT_post, hwo_eq, _, _, _⟩ :=
      worldTypedWith_store_word_disj (post := post) hAs hx_dom
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, hm_eq⟩ hWT' hdisj_x
    refine ⟨S', Nd', hsub, hWT_post, ?_, ?_,
      by rw [hwo_eq]; exact hout_disj,
      hQ' S' Nd' hWT' hWT_post hwo_eq hout_disj hQ0⟩
    · change OwnedGrows entry post (worldOwned entry S Nd) (worldOwned post S' Nd')
      rw [hwo_eq]
      exact hOG
    · intro a ha hhf
      have hax : a ≠ x := by
        rintro rfl
        exact hhf hx_hf
      exact (hm_eq a hax).trans (hFO a ha hhf)

theorem worldStepIn_pmc_of_prefix_not_returned {F : Type}
    {R1 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s1 s2 : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    (hQ_vac : ∀ S' Nd', Q s1 r s2 S' Nd')
    (hA1 : ArenaReady s1)
    (hWOK1 : WorldOK s1)
    (hR1_sub : ∀ j ∈ R1 s1, j ∈ bufRegions pmcBufs s1 ∨
      Inside j (globN s1 "heap_ptr") (globN s2 "heap_ptr"))
    (h12 : WorldStep R1 ["heap_ptr", "scratch_ptr"] pmcKeep NoExtra s1 r s2) :
    WorldStepIn pmcTables pmcRegions pmcGlobals pmcKeep Q s1 r s2 := by
  obtain ⟨hA2, hhp12, hG12, hK12, hW12⟩ := h12
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, S_ok, hWT_ok0⟩ := hWOK1
  obtain ⟨Nd_ok, hWT_ok⟩ := (worldTyped_iff_with s1 S_ok).1 hWT_ok0
  have hrec_not_fresh : ∀ rec ∈ pmcKeep, globN s1 rec.1 ≠ 0 → ∀ off ∈ rec.2,
      ∀ i : Ivl, Inside i (globN s1 "heap_ptr") (globN s2 "heap_ptr") →
      ¬ CellHits (globN s1 rec.1 + off) i := by
    intro rec hrec hnz off hoff i hi_fresh ⟨hc1, hc2⟩
    have ⟨sz, htr, hoff_lt⟩ : ∃ sz, (rec.1, sz) ∈ typedRecords ∧ off + 8 ≤ sz := by
      simp only [pmcKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by simp [typedRecords], ?_⟩; simp at hoff; omega
      · refine ⟨80, by simp [typedRecords], ?_⟩; simp at hoff; omega
      · refine ⟨72, by simp [typedRecords], ?_⟩; simp at hoff; omega
      · refine ⟨88, by simp [typedRecords], ?_⟩; simp at hoff; omega
    have hfix_mem := typedRecord_mem_fixedObjects s1 htr
    simp only [hnz, ↓reduceIte] at hfix_mem
    rcases hWT_ok.2.2.1.1 (globN s1 rec.1, sz) hfix_mem with hz | ⟨hal, _⟩
    · dsimp at hz; omega
    · rcases hal with ⟨_, hhi⟩ | ⟨hlo, _⟩
      · dsimp at hhi; unfold Inside at hi_fresh; omega
      · dsimp at hlo; unfold Inside at hi_fresh
        have := hA1.2.2.1; have := hA2.2.2.1; have := hA1.2.2.2.1; have := hA1.2.2.2.2.1
        omega
  refine ⟨hA2, hhp12, ?_, ?_, ?_⟩
  · intro k hk
    apply hG12 k
    intro hm
    apply hk
    simp only [List.mem_map, pmcGlobals] at hm ⊢
    obtain ⟨g, hg, rfl⟩ := hm
    refine ⟨g, ?_, rfl⟩
    simp at hg; rcases hg with rfl | rfl <;> simp
  · intro rec hrec hnz off hoff hno
    exact hK12 rec hrec hnz off hoff (fun i hi hch => by
      rcases hR1_sub i hi with hi_buf | hi_fresh
      · exact hno i (by change i ∈ pmcRegions s1; rw [pmcRegions_eq_bufRegions]; exact List.mem_cons_of_mem _ hi_buf) hch
      · exact hrec_not_fresh rec hrec hnz off hoff i hi_fresh hch)
  · intro S Nd hWT1 _ hD1
    have hD1_R1 : IvlsDisj (R1 s1) (worldTypedIvls s1 S Nd) := by
      intro x hx j hj
      rcases hR1_sub x hx with hx_buf | hx_fresh
      · exact validBufList_disj validBufList_pmcBufs hWT1 x hx_buf j hj
      · rcases worldOwned_zero_or_allocated hWT1 j (worldTypedIvls_sub_worldOwned s1 S Nd j hj) with
            rfl | ⟨_, hal_j⟩
        · exact disj_zero_right x
        · rcases hal_j with ⟨_, hhi_j⟩ | ⟨hlo_j, _⟩
          · exact Or.inr (Or.inr (Or.inr (Nat.le_trans hhi_j hx_fresh.1)))
          · exact Or.inr (Or.inr (Or.inl (by
              unfold Inside at hx_fresh
              have := hA1.2.2.1; have := hA2.2.2.1; have := hA1.2.2.2.1; have := hA1.2.2.2.2.1
              omega)))
    obtain ⟨S2, Nd2, hsub12, hWT2, hOG12, hFO12, _⟩ := hW12 S Nd hWT1 hD1_R1
    refine ⟨S2, Nd2, hsub12, hWT2, hOG12, ?_, hQ_vac S2 Nd2⟩
    intro a ha hhf
    apply hFO12 a _ hhf
    intro i hi hch
    rcases List.mem_append.1 hi with hi1 | hfg1
    · rcases List.mem_append.1 hi1 with hwo1 | hR1
      · exact ha i (List.mem_append_left _ (List.mem_append_left _ hwo1)) hch
      · rcases hR1_sub i hR1 with hi_buf | hi_fresh
        · exact ha i (List.mem_append_left _ (List.mem_append_right _
            (by change i ∈ pmcRegions s1; rw [pmcRegions_eq_bufRegions]; exact List.mem_cons_of_mem _ hi_buf))) hch
        · obtain ⟨hc1, hc2⟩ := hch
          have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
          exact hhf ⟨by unfold heapFree; dsimp only [Inside] at hi_fresh ⊢; omega,
                     by unfold heapFree; dsimp only [Inside] at hi_fresh ⊢; omega⟩
    · exact ha i (List.mem_append_right _ hfg1) hch

theorem worldStep_pmcPrefix_trans {F : Type}
    {R1 R2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {Q1 Q2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s1 s2 s3 : PanSemStateFiniteExact 64 F}
    {r1 r2 : Option (PanSemResultExact 64)}
    {w_out : BitVec 64}
    (hA1 : ArenaReady s1)
    (hWOK1 : WorldOK s1)
    (hR1_sub : ∀ j ∈ R1 s1, j ∈ bufRegions pmcBufs s1 ∨
      Inside j (globN s1 "heap_ptr") (globN s2 "heap_ptr"))
    (hR2_sub : ∀ j ∈ R2 s2, j ∈ bufRegions pmcBufs s2 ∨
      Inside j (globN s1 "heap_ptr") (globN s3 "heap_ptr"))
    (hQ1_out : ∀ S2 Nd2, Q1 s1 r1 s2 S2 Nd2 →
      IvlsDisj [(w_out.toNat, 96)] (worldOwned s2 S2 Nd2))
    (hR2_disj : ∀ S2 Nd2, WorldTypedWith s2 S2 Nd2 →
      IvlsDisj [(w_out.toNat, 96)] (worldOwned s2 S2 Nd2) →
      IvlsDisj (R2 s2) (worldTypedIvls s2 S2 Nd2))
    (h12 : WorldStep R1 ["heap_ptr", "scratch_ptr"] pmcKeep Q1 s1 r1 s2)
    (hsp12 : globN s2 "scratch_ptr" ≤ globN s1 "scratch_ptr")
    (h23 : WorldStep R2 ["heap_ptr", "scratch_ptr"] pmcKeep Q2 s2 r2 s3)
    (hout_ow3_gen : ∀ S2 Nd2 S3 Nd3,
      WorldTypedWith s2 S2 Nd2 →
      IvlsDisj [(w_out.toNat, 96)] (worldOwned s2 S2 Nd2) →
      OwnedGrows s2 s3 (worldOwned s2 S2 Nd2) (worldOwned s3 S3 Nd3) →
      FrameOutside s2 s3 (worldOwned s2 S2 Nd2 ++ R2 s2 ++ [freeGap s2]) (heapFree s2) →
      Q2 s2 r2 s3 S3 Nd3 →
      IvlsDisj [(w_out.toNat, 96)] (worldOwned s3 S3 Nd3)) :
    WorldStep (fun s => bufRegions pmcBufs s ++ [(globN s1 "heap_ptr", globN s3 "heap_ptr" - globN s1 "heap_ptr")])
      ["heap_ptr", "scratch_ptr"] pmcKeep
      (fun _ _ st S3 Nd3 => IvlsDisj [(w_out.toNat, 96)] (worldOwned st S3 Nd3))
      s1 r2 s3 := by
  obtain ⟨hA2, hhp12, hG12, hK12, hW12⟩ := h12
  obtain ⟨hA3, hhp23, hG23, hK23, hW23⟩ := h23
  have hsafe : SafeStepGlobals ["heap_ptr", "scratch_ptr"] := by
    intro g hg; simp at hg ⊢; rcases hg with rfl | rfl <;> simp
  have hbuf21 : bufRegions pmcBufs s2 = bufRegions pmcBufs s1 :=
    bufRegions_eq_of_safeGlobals validBufList_pmcBufs hsafe hG12
  have hfmp12 : globN s1 "frame_mem_ptr" = globN s2 "frame_mem_ptr" :=
    (globN_eq_of_lookup (hG12 (ofString "frame_mem_ptr") (by decide))).symm
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, S_ok, hWT_ok0⟩ := hWOK1
  obtain ⟨Nd_ok, hWT_ok⟩ := (worldTyped_iff_with s1 S_ok).1 hWT_ok0
  have hrec_not_fresh : ∀ rec ∈ pmcKeep, globN s1 rec.1 ≠ 0 → ∀ off ∈ rec.2,
      ∀ i : Ivl, Inside i (globN s1 "heap_ptr") (globN s3 "heap_ptr") →
      ¬ CellHits (globN s1 rec.1 + off) i := by
    intro rec hrec hnz off hoff i hi_fresh ⟨hc1, hc2⟩
    have ⟨sz, htr, hoff_lt⟩ : ∃ sz, (rec.1, sz) ∈ typedRecords ∧ off + 8 ≤ sz := by
      simp only [pmcKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by simp [typedRecords], ?_⟩; simp at hoff; omega
      · refine ⟨80, by simp [typedRecords], ?_⟩; simp at hoff; omega
      · refine ⟨72, by simp [typedRecords], ?_⟩; simp at hoff; omega
      · refine ⟨88, by simp [typedRecords], ?_⟩; simp at hoff; omega
    have hfix_mem := typedRecord_mem_fixedObjects s1 htr
    simp only [hnz, ↓reduceIte] at hfix_mem
    rcases hWT_ok.2.2.1.1 (globN s1 rec.1, sz) hfix_mem with hz | ⟨hal, _⟩
    · dsimp at hz; omega
    · rcases hal with ⟨_, hhi⟩ | ⟨hlo, _⟩
      · dsimp at hhi; unfold Inside at hi_fresh; omega
      · dsimp at hlo; unfold Inside at hi_fresh
        have := hA1.2.2.1; have := hA3.2.2.1; have := hA1.2.2.2.1; have := hA1.2.2.2.2.1
        omega
  refine ⟨hA3, le_trans hhp12 hhp23, fun k hk => (hG12 k hk).trans (hG23 k hk), ?_, ?_⟩
  · intro rec hrec hnz off hoff hno
    have hrec_ne : ofString rec.1 ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString := by
      simp only [pmcKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl <;> decide
    have hg_rec : globN s2 rec.1 = globN s1 rec.1 :=
      globN_eq_of_lookup (hG12 (ofString rec.1) hrec_ne)
    have h1 := hK12 rec hrec hnz off hoff (fun i hi hch => by
      rcases hR1_sub i hi with hi_buf | hi_fresh
      · exact hno i (List.mem_append_left _ hi_buf) hch
      · exact hrec_not_fresh rec hrec hnz off hoff i ⟨hi_fresh.1, le_trans hi_fresh.2 hhp23⟩ hch)
    have h2 := hK23 rec hrec (by rw [hg_rec]; exact hnz) off hoff (fun i hi hch => by
      rw [hg_rec] at hch
      rcases hR2_sub i hi with hi_buf | hi_fresh
      · rw [hbuf21] at hi_buf
        exact hno i (List.mem_append_left _ hi_buf) hch
      · exact hrec_not_fresh rec hrec hnz off hoff i hi_fresh hch)
    rw [hg_rec] at h2
    exact h2.trans h1
  · intro S Nd hWT1 hD1
    have hD1_R1 : IvlsDisj (R1 s1) (worldTypedIvls s1 S Nd) := by
      intro x hx j hj
      rcases hR1_sub x hx with hx_buf | hx_fresh
      · exact hD1 x (List.mem_append_left _ hx_buf) j hj
      · rcases worldOwned_zero_or_allocated hWT1 j (worldTypedIvls_sub_worldOwned s1 S Nd j hj) with
            rfl | ⟨_, hal_j⟩
        · exact disj_zero_right x
        · rcases hal_j with ⟨_, hhi_j⟩ | ⟨hlo_j, _⟩
          · exact Or.inr (Or.inr (Or.inr (Nat.le_trans hhi_j hx_fresh.1)))
          · exact Or.inr (Or.inr (Or.inl (by
              unfold Inside at hx_fresh
              have := hA1.2.2.1; have := hA2.2.2.1; have := hA1.2.2.2.1; have := hA1.2.2.2.2.1
              omega)))
    obtain ⟨S2, Nd2, hsub12, hWT2, hOG12, hFO12, hQ12⟩ := hW12 S Nd hWT1 hD1_R1
    have hout_ow2 : IvlsDisj [(w_out.toNat, 96)] (worldOwned s2 S2 Nd2) := hQ1_out S2 Nd2 hQ12
    obtain ⟨S3, Nd3, hsub23, hWT3, hOG23, hFO23, hQ23⟩ := hW23 S2 Nd2 hWT2 (hR2_disj S2 Nd2 hWT2 hout_ow2)
    refine ⟨S3, Nd3, fun t ht => hsub23 t (hsub12 t ht), hWT3, ?_, ?_,
      hout_ow3_gen S2 Nd2 S3 Nd3 hWT2 hout_ow2 hOG23 hFO23 hQ23⟩
    · intro o ho
      rcases hOG23 o ho with rfl | ⟨j, hj, hin_oj⟩ | hin_o23
      · exact Or.inl rfl
      · rcases hOG12 j hj with rfl | ⟨k, hk, hin_jk⟩ | hin_j12
        · left
          rcases o with ⟨o1, o2⟩
          dsimp only [Inside] at hin_oj
          exact Prod.ext (by omega) (by omega)
        · exact Or.inr (Or.inl ⟨k, hk, le_trans hin_jk.1 hin_oj.1, le_trans hin_oj.2 hin_jk.2⟩)
        · exact Or.inr (Or.inr ⟨le_trans hin_j12.1 hin_oj.1,
            le_trans hin_oj.2 (le_trans hin_j12.2 hhp23)⟩)
      · exact Or.inr (Or.inr ⟨le_trans hhp12 hin_o23.1, hin_o23.2⟩)
    · intro a ha hhf
      have ha12 : ∀ i ∈ worldOwned s1 S Nd ++ R1 s1 ++ [freeGap s1], ¬ CellHits a.toNat i := by
        intro i hi hch
        rcases List.mem_append.1 hi with hi1 | hfg1
        · rcases List.mem_append.1 hi1 with hwo1 | hR1
          · exact ha i (List.mem_append_left _ (List.mem_append_left _ hwo1)) hch
          · rcases hR1_sub i hR1 with hi_buf | hi_fresh
            · exact ha i (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ hi_buf))) hch
            · obtain ⟨hc1, hc2⟩ := hch
              have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
              exact hhf ⟨by unfold heapFree; dsimp only [Inside] at hi_fresh ⊢; omega,
                         by unfold heapFree; dsimp only [Inside] at hi_fresh ⊢; omega⟩
        · exact ha i (List.mem_append_right _ hfg1) hch
      have hm12 : s2.memory a = s1.memory a := hFO12 a ha12 hhf
      have hm23 : s3.memory a = s2.memory a := by
        apply hFO23 a
        · intro i hi hch
          obtain ⟨hc1, hc2⟩ := hch
          rcases List.mem_append.1 hi with hi1 | hfg2
          · rcases List.mem_append.1 hi1 with hwo2 | hR2
            · rcases hOG12 i hwo2 with rfl | ⟨k, hk, hin_ik⟩ | hin_i12
              · dsimp only at hc2; omega
              · exact ha k (List.mem_append_left _ (List.mem_append_left _ hk))
                  ⟨by dsimp only [Inside] at hin_ik; omega,
                   by dsimp only [Inside] at hin_ik; omega⟩
              · have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
                exact hhf ⟨by unfold heapFree; dsimp only [Inside] at hin_i12 ⊢; omega,
                           by unfold heapFree; dsimp only [Inside] at hin_i12 ⊢; omega⟩
            · rcases hR2_sub i hR2 with hi_buf | hi_fresh
              · rw [hbuf21] at hi_buf
                exact ha i (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ hi_buf))) ⟨hc1, hc2⟩
              · have hp3_lim : globN s3 "heap_ptr" ≤ heapLimit := hA3.2.2.1
                exact hhf ⟨by unfold heapFree; dsimp only [Inside] at hi_fresh ⊢; omega,
                           by unfold heapFree; dsimp only [Inside] at hi_fresh ⊢; omega⟩
          · simp only [List.mem_singleton] at hfg2; subst hfg2
            exact ha (freeGap s1) (List.mem_append_right _ (List.mem_singleton.2 rfl))
              ⟨by
                have hc1' : a.toNat + 8 > globN s2 "frame_mem_ptr" := hc1
                change a.toNat + 8 > globN s1 "frame_mem_ptr"
                omega,
               by
                have hc2' : a.toNat < globN s2 "frame_mem_ptr" + (globN s2 "scratch_ptr" - globN s2 "frame_mem_ptr") := hc2
                have hfmp_sp2 : globN s2 "frame_mem_ptr" ≤ globN s2 "scratch_ptr" := hA2.2.2.2.2.1
                change a.toNat < globN s1 "frame_mem_ptr" + (globN s1 "scratch_ptr" - globN s1 "frame_mem_ptr")
                omega⟩
        · intro ⟨hc1, hc2⟩
          have hp2_lim : globN s2 "heap_ptr" ≤ heapLimit := hA2.2.2.1
          exact hhf ⟨by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega,
                     by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega⟩
      exact hm23.trans hm12

theorem worldStep_pmcKeep_of_stdKeep {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hgw : ∀ g ∈ gw, g ∈ (["heap_ptr", "scratch_ptr"] : List String))
    (h : WorldStep R gw stdKeep Q s r post) :
    WorldStep R ["heap_ptr", "scratch_ptr"] pmcKeep Q s r post := by
  obtain ⟨hAp, hhp, hG, hK, hW⟩ := h
  refine ⟨hAp, hhp, ?_, ?_, hW⟩
  · intro k hk
    apply hG k
    intro hm
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
    exact hk (List.mem_map.2 ⟨g, hgw g hg, rfl⟩)
  · intro rec hrec hnz off hoff hno
    simp only [pmcKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
    rcases hrec with rfl | rfl | rfl | rfl
    · exact hK ("ws", [0, 8, 16, 24, 32]) (by simp [stdKeep]) hnz off hoff hno
    · exact hK ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]) (by simp [stdKeep]) hnz off
        (by simp at hoff ⊢; omega) hno
    · exact hK ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]) (by simp [stdKeep]) hnz off hoff hno
    · exact hK ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp [stdKeep]) hnz off hoff hno

theorem worldStep_pmcKeep_with_locals_clock {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {s post : PanSemStateFiniteExact 64 F} {r r' : Option (PanSemResultExact 64)}
    (h : WorldStep R ["heap_ptr", "scratch_ptr"] pmcKeep NoExtra s r post)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    WorldStep R ["heap_ptr", "scratch_ptr"] pmcKeep NoExtra s r' { post with locals := L, clock := k } := by
  obtain ⟨hAp, hhp, hG, hK, hW⟩ := h
  refine ⟨localsFree_arenaReady post L k hAp, hhp, hG, hK, fun S Nd hWT hD => ?_⟩
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, _⟩ := hW S Nd hWT hD
  exact ⟨S', Nd', hsub, (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals post L k S' Nd').2 hWT',
    hOG, hFO, trivial⟩

theorem worldStep_of_region_writes_ownedEq {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    (hWOK : WorldOK s)
    (hmeta : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
      post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals)
    (hfr : FrameOutside s post (R s) (0, 0))
    (hbyte : ∀ a : Nat, a < 2 ^ 64 → (∀ j ∈ R s, ¬ InIvl a j) → memB post a = memB s a)
    (hdom_wr : ∀ a : BitVec 64, post.memory a ≠ s.memory a → s.memaddrs a) :
    WorldStep R [] stdKeep
      (fun s0 _ post0 S' Nd' => ∀ P : List Ivl → Prop, P (worldOwned s0 S' Nd') → P (worldOwned post0 S' Nd'))
      s r post ∧
    (∀ S Nd, WorldTypedWith s S Nd → IvlsDisj (R s) (worldTypedIvls s S Nd) →
      WorldTypedWith post S Nd ∧ worldOwned post S Nd = worldOwned s S Nd) := by
  have hAs := hWOK.1
  have hgP : GuestInv post := guestInv_congr hmeta.1 hmeta.2.1 hmeta.2.2.1 hmeta.2.2.2.1 hAs.1
  have hAp : ArenaReady post := ⟨hgP, arenaOK_congr hmeta.2.2.2.2.2 hAs.2⟩
  have hag : AllocatorGrows s post := by
    unfold AllocatorGrows; simp only [Wave8Contracts.M08.globN_congr hmeta.2.2.2.2.2]; exact ⟨le_rfl, le_rfl⟩
  have hgw : GlobalsKept [] s post := fun _ _ => by rw [hmeta.2.2.2.2.2]
  have hgs := Wave8Contracts.M08.worldGlobalsSame_of_kept hgw (fun _ h => by simp at h)
  have hm0 := Wave8Contracts.M08.mem0_8_16_eq_of_domain_writes hdom_wr hAs.1
  have hfr_ext : FrameOutside s post (R s ++ [freeGap s]) (heapFree s) := by
    intro a hk _
    exact hfr a (fun j hj => hk j (List.mem_append.2 (Or.inl hj)))
      (fun hc => by unfold CellHits at hc; omega)
  have hrk := Wave8Contracts.M08.recordsKept_of_free_writes hWOK hfr_ext
  have hcore : ∀ S Nd, WorldTypedWith s S Nd → IvlsDisj (R s) (worldTypedIvls s S Nd) →
      WorldTypedWith post S Nd ∧ worldOwned post S Nd = worldOwned s S Nd := by
    intro S Nd hWT hdisjR
    obtain ⟨hT, hJ, hF, hTr⟩ := hWT
    have hu_al : ∀ i : Ivl, i ∈ worldTypedIvls s S Nd → i.1 % 8 = 0 → i.2 % 8 = 0 → Wave8Contracts.M08.IvlUnhit s post i := by
      intro i hi _ _ a ha8 hin1 hin2
      by_cases heq : post.memory a = s.memory a
      · exact heq
      · have hadom : ordinaryDomain a := by
          have := hdom_wr a heq
          rwa [hAs.1.memaddrs] at this
        have ha_ord : a.toNat % 8 = 0 ∧ sourceBase ≤ a.toNat ∧ a.toNat < heapEnd := by
          rwa [Wave8Contracts.M08.ordinaryDomain_iff] at hadom
        have hhe_lt : heapEnd ≤ 2 ^ 64 := by decide
        apply Wave8Contracts.M08.mem_eq_of_bytes_eq hadom hmeta.2.2.2.2.1
        intro k hk
        apply hbyte (a.toNat + k) (by omega)
        intro j hj hinv
        have hdj := hdisjR j hj i hi
        unfold InIvl at hinv
        rcases hdj with h0 | h0 | hd | hd <;> omega
    have hfix_al : ∀ i ∈ fixedObjects s, i.2 = 0 ∨ (i.1 % 8 = 0 ∧ i.2 % 8 = 0) := by
      intro i hi
      rcases hF.1 i hi with h0 | ⟨_, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hw.1, hw.2.1⟩
    have hu_fix_wti : ∀ i ∈ worldTypedIvls s S Nd, i ∈ fixedObjects s → i.2 ≠ 0 → Wave8Contracts.M08.IvlUnhit s post i := by
      intro i hwti hfi hpos
      rcases hfix_al i hfi with h0 | ⟨ha1, ha2⟩
      · exact absurd h0 hpos
      · exact hu_al i hwti ha1 ha2
    obtain ⟨hWT_post, howned_eq, _, _, _⟩ :=
      Wave8Contracts.M08.worldTypedWith_congr_parts hAs hAp hag hgs ⟨hT, hJ, hF, hTr⟩
        (fun t ht i hi => by
          have hw := ((hT.2.1 t ht).1.1 i hi).2
          refine hu_al i ?_ hw.1 hw.2.1
          unfold worldTypedIvls
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left
          exact List.mem_flatMap.2 ⟨t, ht, hi⟩)
        (fun hnz => hu_fix_wti _
          (by unfold worldTypedIvls
              apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
              apply List.mem_append.2; left; apply List.mem_append.2; right
              exact List.mem_map.2 ⟨("ws", 40), by simp [typedRecords], by simp [hnz]⟩)
          (by simpa [hnz] using Wave8Contracts.M08.typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by simp [Wave8Contracts.M08.typedRecords]))
          (by simp))
        (fun hnz => hu_fix_wti _
          (by unfold worldTypedIvls
              apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
              apply List.mem_append.2; left; apply List.mem_append.2; right
              exact List.mem_map.2 ⟨("bs", 80), by simp [typedRecords], by simp [hnz]⟩)
          (by simpa [hnz] using Wave8Contracts.M08.typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by simp [Wave8Contracts.M08.typedRecords]))
          (by simp))
        (fun hnz => hu_fix_wti _
          (by unfold worldTypedIvls
              apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
              apply List.mem_append.2; left; apply List.mem_append.2; right
              exact List.mem_map.2 ⟨("ts", 72), by simp [typedRecords], by simp [hnz]⟩)
          (by simpa [hnz] using Wave8Contracts.M08.typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by simp [Wave8Contracts.M08.typedRecords]))
          (by simp))
        (fun hnz => hu_fix_wti _
          (by unfold worldTypedIvls
              apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
              apply List.mem_append.2; left; apply List.mem_append.2; right
              exact List.mem_map.2 ⟨("bo", 88), by simp [typedRecords], by simp [hnz]⟩)
          (by simpa [hnz] using Wave8Contracts.M08.typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by simp [Wave8Contracts.M08.typedRecords]))
          (by simp))
        (fun hcnz => hu_fix_wti (globN s "journal", 32 * globN s "journal_cap")
          (by unfold worldTypedIvls
              apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
              apply List.mem_append.2; right; simp [hcnz])
          (by unfold fixedObjects
              apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right; simp [hcnz])
          (by dsimp only; omega))
        (fun i hi h24 => hu_fix_wti i
          (by unfold worldTypedIvls
              apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
          (by unfold fixedObjects
              apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
          (by omega))
        (fun i hi hpos => hu_fix_wti i
          (by unfold worldTypedIvls
              apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
          (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi))
          hpos)
        (fun n hn => by
          have hw := (hTr.1.1 n hn).2.2.2.1
          refine hu_al _ ?_ hw.1 hw.2.1
          unfold worldTypedIvls
          refine List.mem_append.2 (Or.inr ?_)
          unfold nodeExtents
          exact List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩)
        (fun n hn h12 hlen0 k hk => by
          have h264 : heapLimit ≤ 2 ^ 64 := by decide
          rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, _, hin_p, _⟩
          · exact absurd h0 hlen0
          · have hp_wti : (memW s (n + 32), memW s (n + 40)) ∈ worldTypedIvls s S Nd := by
              unfold worldTypedIvls
              refine List.mem_append.2 (Or.inr ?_)
              unfold nodeExtents
              exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
            apply hbyte _ (by have := hin_p.2; omega)
            intro j hj hinv
            have hdj := hdisjR j hj _ hp_wti
            unfold InIvl at hinv
            rcases hdj with h0 | h0 | hd | hd <;> omega)
        hm0
    exact ⟨hWT_post, howned_eq⟩
  refine ⟨⟨hAp, hag.1, hgw, hrk, fun S Nd hWT hdisjR => ?_⟩, hcore⟩
  obtain ⟨hWT_post, howned_eq⟩ := hcore S Nd hWT hdisjR
  refine ⟨S, Nd, fun _ ht => ht, hWT_post, ?_, ?_, fun P hP => by rwa [howned_eq]⟩
  · rw [howned_eq]; exact Wave8Contracts.M08.ownedGrows_refl s post _
  · intro a hkeep _
    exact hfr a
      (fun j hj => hkeep j (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hj)))))
      (fun hc => by unfold CellHits at hc; omega)

theorem worldStepIn_pmc_with_locals_clock {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (h : WorldStepIn pmcTables pmcRegions pmcGlobals pmcKeep RetMessageOutputStrong s r post)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    WorldStepIn pmcTables pmcRegions pmcGlobals pmcKeep RetMessageOutputStrong s r
      { post with locals := L, clock := k } := by
  obtain ⟨hAp, hhp, hG, hK, hW⟩ := h
  have hAp' := localsFree_arenaReady post L k hAp
  refine ⟨hAp', hhp, hG, hK, fun S Nd hWT hTS hD => ?_⟩
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hret, hstrong⟩ := hW S Nd hWT hTS hD
  refine ⟨S', Nd', hsub, (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals post L k S' Nd').2 hWT',
    hOG, hFO, ⟨fun v hv => ?_, fun v hv => ?_⟩⟩
  · obtain ⟨w, hveq, hwok, hin, hdisj, hlok⟩ := hret v hv
    exact ⟨w, hveq, hwok, hin, hdisj,
      pmc_logsListOK_congr_live hAp.2 hAp.1 hAp'.1 le_rfl hlok (fun a => a)
        (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)⟩
  · obtain ⟨w, hveq, hlive⟩ := hstrong v hv
    obtain ⟨w', hveq', _, _, _, hlok⟩ := hret v hv
    rw [hveq] at hveq'; injection hveq' with hveq''; injection hveq'' with hw_eq; subst hw_eq
    exact ⟨w, hveq, pmcLogsLiveOwned_congr_live hAp.2 hlok hlive rfl rfl
      (fun a => a) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)⟩

theorem worldStep_pmcKeep_with_locals_clock_Q {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {P : List Ivl → Prop}
    {s post : PanSemStateFiniteExact 64 F} {r r' : Option (PanSemResultExact 64)}
    (h : WorldStep R ["heap_ptr", "scratch_ptr"] pmcKeep
      (fun _ _ st S' Nd' => P (worldOwned st S' Nd')) s r post)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    WorldStep R ["heap_ptr", "scratch_ptr"] pmcKeep
      (fun _ _ st S' Nd' => P (worldOwned st S' Nd')) s r' { post with locals := L, clock := k } := by
  obtain ⟨hAp, hhp, hG, hK, hW⟩ := h
  refine ⟨localsFree_arenaReady post L k hAp, hhp, hG, hK, fun S Nd hWT hD => ?_⟩
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hP⟩ := hW S Nd hWT hD
  exact ⟨S', Nd', hsub, (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals post L k S' Nd').2 hWT',
    hOG, hFO, hP⟩

def PmcA0 {F : Type} (entry s : PanSemStateFiniteExact 64 F) : Prop :=
  s = entry ∧ MsgReady entry

def PmcA1 {F : Type} (entry s : PanSemStateFiniteExact 64 F) : Prop :=
  MsgReady entry ∧
  MsgReady s ∧
  s.locals.lookup (ofString "msg") = entry.locals.lookup (ofString "msg") ∧
  globN s "scratch_ptr" ≤ globN entry "scratch_ptr" ∧
  ∃ w_out : BitVec 64,
    WorldStep (fun st => bufRegions pmcBufs st ++ [(globN entry "heap_ptr", globN s "heap_ptr" - globN entry "heap_ptr")])
      ["heap_ptr", "scratch_ptr"] pmcKeep
      (fun _ _ st S Nd => IvlsDisj [(w_out.toNat, 96)] (worldOwned st S Nd))
      entry none s ∧
    s.locals.lookup (ofString "out") = some (.val (.word w_out)) ∧
    s.locals.lookup (ofString "frame") = some (.val (.word 0#64)) ∧
    w_out.toNat % 8 = 0 ∧
    Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s "heap_ptr") ∧
    WordsOK s (w_out.toNat, 96) ∧
    memW s (w_out.toNat + 16) = 0 ∧
    ∃ S_s Nd_s,
      R10Shards.Fast_GbodyC17ToC21.MsgReadyAt s S_s Nd_s ∧
      IvlsDisj [(w_out.toNat, 96)] (worldOwned s S_s Nd_s)

def PmcA2 {F : Type} (entry s : PanSemStateFiniteExact 64 F) : Prop :=
  MsgReady entry ∧
  ∃ w_out w_fr : BitVec 64,
    WorldStepIn pmcTables pmcRegions pmcGlobals pmcKeep
      (fun _ _ post S Nd =>
        IvlsDisj [(w_out.toNat, 96)] (worldOwned post S Nd) ∧
        PmcLogsLiveOwned post S Nd (memW post (w_fr.toNat + 88)))
      entry none s ∧
    s.locals.lookup (ofString "out") = some (.val (.word w_out)) ∧
    s.locals.lookup (ofString "frame") = some (.val (.word w_fr)) ∧
    w_out.toNat % 8 = 0 ∧
    Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s "heap_ptr") ∧
    WordsOK s (w_out.toNat, 96) ∧
    memW s (w_out.toNat + 16) = 0 ∧
    WordsOK s (w_fr.toNat, 280) ∧
    Inside (w_fr.toNat, 280) (globN s "scratch_ptr") scratchEnd ∧
    LogsListOK s (memW s (w_fr.toNat + 88)) ∧
    (memW s (w_fr.toNat + 88) ≠ 0 →
      Disj (memW s (w_fr.toNat + 88), 24) (w_out.toNat, 96) ∧
      Disj (memW s (memW s (w_fr.toNat + 88)), 8 * memW s (memW s (w_fr.toNat + 88) + 8)) (w_out.toNat, 96) ∧
      ∀ i, i < memW s (memW s (w_fr.toNat + 88) + 8) →
        Disj (memW s (memW s (memW s (w_fr.toNat + 88)) + 8 * i), 40) (w_out.toNat, 96))

theorem pmc_resumes_not_returned_vac {F : Type}
    {entry post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hnr : ∀ v, r ≠ some (.returned v)) {S Nd : List Nat} :
    RetMessageOutputStrong entry r post S Nd :=
  ⟨fun v hv => absurd hv (hnr v), fun v hv => absurd hv (hnr v)⟩

theorem pmcA0_init {F : Type} (s : PanSemStateFiniteExact 64 F) (h : MsgReady s) :
    PmcA0 s s :=
  ⟨rfl, h⟩

theorem pmcInit_cut : PmcRelCutStrong pmcInit PmcA0 PmcA1 := by
  intro F entry tail htail s hcode ⟨hs_eq, hM0⟩
  cases hs_eq
  unfold PmcRelRunStrong
  intro hres
  unfold pmcInit pmcCode at hres ⊢
  simp only [sourceFunctionEntry, Guest.Software.guestFn_process_message_call,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil,
    R13Shards.spinePlug] at hres ⊢
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_skip] at hres ⊢
  dsimp only at hres ⊢
  -- Step 1: decCall "out" .one "alloc" [96]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hres ⊢
  have hargs_al : evalListHOLFinite entry (h := fun a => Classical.propDecidable (entry.memaddrs a))
      [.const 96#64] = some [.val (.word 96#64)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact]
  simp only [hargs_al] at hres ⊢
  rcases hl_al : lookupCodeHOLFinite entry.code.lookup (ofString "alloc") [.val (.word 96#64)]
      with _ | ⟨body_al, callee_al, ret_al⟩
  · simp only [hl_al] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [hl_al] at hres ⊢
    by_cases hclk0 : entry.clock = 0
    · simp only [hclk0, ↓reduceIte] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hclk0, ↓reduceIte] at hres ⊢
      have hpc_al := R10Shards.Fast_GbodyC17ToC21.callee_param_one_exp entry (ofString "alloc")
        (ofString "n") .one _ _ (by rw [hcode]; exact R10Shards.Fast_GbodyC17ToC21.lookup_alloc_fn)
        (.const 96#64) (.val (.word 96#64)) [.val (.word 96#64)] body_al callee_al ret_al rfl hargs_al hl_al
      have hn_al : locN (callEntryStateHOLFinite entry callee_al) "n" = 96 := by
        simp [locN, callEntryStateHOLFinite, hpc_al.2]
      have hmeta_al := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite entry callee_al) body_al).1
      rcases hrun_al : evaluateHOLFiniteState (callEntryStateHOLFinite entry callee_al) body_al with ⟨res_al, post_al⟩
      rw [hrun_al] at hmeta_al
      dsimp only at hmeta_al
      simp only [hrun_al] at hres ⊢
      have hWOK_en : WorldOK entry := msgReady_worldOK entry hM0
      cases res_al with
      | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      | some br_al =>
        cases br_al with
        | timeOut => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | error => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | «break» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | «continue» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | finalFfi _ => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | exception eid eval =>
          dsimp only at hres ⊢
          have hstep_al := FunSpec.at_lookup wk_alloc_local entry hcode _ body_al callee_al ret_al hl_al
            (localsFree_worldOK entry callee_al (entry.clock - 1) hWOK_en)
            (by rw [hrun_al]; simp)
          rw [hrun_al] at hstep_al
          have hws_al := hstep_al hres
          have hws_al_caller : WorldStep (fun _ => []) ["heap_ptr", "scratch_ptr"] pmcKeep NoExtra
              entry (some (.exception eid eval)) (emptyLocalsHOLFinite post_al) := by
            have h1 : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra
                entry (some (.exception eid eval)) post_al := by
              obtain ⟨a1, a2, a3, a4, a5⟩ := hws_al
              exact ⟨a1, a2, a3, a4, fun S_x Nd_x hW_x _ => by
                obtain ⟨S', Nd', hs, hw', hog, hfo, _⟩ :=
                  a5 S_x Nd_x ((R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals _ _ _ _ _).2 hW_x)
                    (fun x hx => by simp at hx)
                exact ⟨S', Nd', hs, hw', hog, hfo, trivial⟩⟩
            exact worldStep_pmcKeep_with_locals_clock
              (worldStep_pmcKeep_of_stdKeep (by intro g hg; simp at hg; subst hg; simp) h1)
              HolFiniteMapExact.empty post_al.clock
          exact worldStepIn_pmc_of_prefix_not_returned
            (fun _ _ => pmc_resumes_not_returned_vac (by intro _ h; simp at h))
            hM0.1 hWOK_en (by intro j hj; simp at hj) hws_al_caller
        | returned val_al =>
          dsimp only at hres ⊢
          by_cases hsh_al : (shapeEqHOL (shapeOfHOLExact val_al) .one && shapeEqHOL (shapeOfHOLExact val_al) ret_al) = true
          · simp only [hsh_al, ↓reduceIte] at hres ⊢
            have hstep_al := FunSpec.at_lookup wk_alloc_local entry hcode _ body_al callee_al ret_al hl_al
              (localsFree_worldOK entry callee_al (entry.clock - 1) hWOK_en)
              (by rw [hrun_al]; simp)
            rw [hrun_al] at hstep_al
            have hws_al := hstep_al (Or.inl ⟨val_al, rfl⟩)
            have hrt_al := FunSpec.at_lookup rt_alloc_local entry hcode _ body_al callee_al ret_al hl_al
              (localsFree_arenaReady entry callee_al (entry.clock - 1) hM0.1)
              (by rw [hrun_al]; simp)
            rw [hrun_al] at hrt_al
            obtain ⟨w_out, rfl, hAR_al, hAG_al, hw_out8, hw_in_al, hw_ok_al⟩ := hrt_al val_al rfl
            rw [hn_al] at hw_in_al hw_ok_al
            change Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN post_al "heap_ptr") at hw_in_al
            change WordsOK post_al (w_out.toNat, 96) at hw_ok_al
            set s1 := setVarHOLFinite (ofString "out") (.val (.word w_out)) { post_al with locals := entry.locals }
            have hs1_code : s1.code = originalRuntimeCode := hAR_al.1.code
            have hs1_out : s1.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
              simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
            have hs1_msg : s1.locals.lookup (ofString "msg") = entry.locals.lookup (ofString "msg") := by
              simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
                show ofString "out" ≠ ofString "msg" by decide]
            obtain ⟨S_en, Nd_en, hMA_en⟩ := R10Shards.Fast_GbodyC17ToC21.msgReadyAt_of_msgReady hM0
            have hws_al_av : WorldStep (fun _ => []) ["heap_ptr"] stdKeep
                (fun _ r' post' S' Nd' => ∀ v', r' = some (.returned v') → ∃ w : BitVec 64,
                  v' = .val (.word w) ∧ IvlsDisj [(w.toNat, 96)] (worldOwned post' S' Nd'))
                entry (some (.returned (.val (.word w_out)))) post_al := by
              obtain ⟨a1, a2, a3, a4, a5⟩ := hws_al
              refine ⟨a1, a2, a3, a4, fun S_x Nd_x hW_x _ => ?_⟩
              obtain ⟨S', Nd', hs, hw', hog, hfo, hq⟩ :=
                a5 S_x Nd_x ((R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals _ _ _ _ _).2 hW_x)
                  (fun x hx => by simp at hx)
              refine ⟨S', Nd', hs, hw', hog, hfo, fun v' hv' => ?_⟩
              obtain ⟨w, hw_eq, hav⟩ := hq v' hv'
              dsimp only at hav; rw [hn_al] at hav
              exact ⟨w, hw_eq, hav⟩
            obtain ⟨S0_s1, Nd_s1, hMA_post_al, hQ0_al, hfp_al⟩ :=
              R10Shards.Fast_GbodyC17ToC21.WorldStep.preserves_msgReadyAt hMA_en hws_al_av
                (fun j hj => by simp at hj) (fun x hx => by simp at hx)
            obtain ⟨w_out', hw_eq, hav0_al⟩ := hQ0_al (.val (.word w_out)) rfl
            injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
            have hMA_s1 : R10Shards.Fast_GbodyC17ToC21.MsgReadyAt s1
                (S0_s1 ++ [memW entry (locN entry "msg" + 152), memW entry (locN entry "msg" + 160)]) Nd_s1 :=
              R10Shards.Fast_GbodyC17ToC21.msgReadyAt_with_locals
                (s := { post_al with locals := entry.locals })
                (by simp [HolFiniteMapExact.update, FUPDATE, show ofString "out" ≠ ofString "msg" by decide])
                hMA_post_al
            have hM_s1 : MsgReady s1 :=
              R10Shards.Fast_GbodyC17ToC21.msgReadyAt_msgReady hMA_s1
            have hWOK_s1 : WorldOK s1 := msgReady_worldOK s1 hM_s1
            have hsp_s1 : globN s1 "scratch_ptr" ≤ globN entry "scratch_ptr" := hAG_al.2
            have hw_in_s1 : Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s1 "heap_ptr") := hw_in_al
            have hw_ok_s1 : WordsOK s1 (w_out.toNat, 96) := hw_ok_al
            have hout_ow_s1_at : IvlsDisj [(w_out.toNat, 96)]
                (worldOwned s1 (S0_s1 ++ [memW entry (locN entry "msg" + 152), memW entry (locN entry "msg" + 160)]) Nd_s1) := by
              intro x hx j hj
              simp only [List.mem_singleton] at hx; subst hx
              change j ∈ worldOwned post_al _ Nd_s1 at hj
              unfold worldOwned at hj
              rcases List.mem_append.1 hj with h1 | hnd
              · rcases List.mem_append.1 h1 with htab | hfix
                · rw [List.flatMap_append] at htab
                  rcases List.mem_append.1 htab with htab0 | htab_loc
                  · apply hav0_al (w_out.toNat, 96) (by simp) j
                    unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl htab0)))
                  · obtain ⟨u, hu_loc, hj_fp⟩ := List.mem_flatMap.1 htab_loc
                    rw [hfp_al u hu_loc] at hj_fp
                    have hu_S : u ∈ S_en := by
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_loc
                      rcases hu_loc with rfl | rfl
                      · exact hMA_en.2.2.1
                      · exact hMA_en.2.2.2.1
                    have hal_j : Allocated entry j := ((hMA_en.2.1.1.2.1 u hu_S).2 j hj_fp).1
                    have hsep : heapLimit ≤ scratchStart := by decide
                    obtain ⟨_, h1_s, h2_s, h3_s, _⟩ := hMA_en.1.2
                    rcases hal_j with ⟨_, hhi_j⟩ | ⟨hlo_j, _⟩
                    · exact Or.inr (Or.inr (Or.inr (Nat.le_trans hhi_j hw_in_al.1)))
                    · exact Or.inr (Or.inr (Or.inl (by
                        have hhp_lim : globN post_al "heap_ptr" ≤ heapLimit := hAR_al.2.2.1
                        have hsc_lo : scratchStart ≤ globN entry "scratch_ptr" :=
                          Nat.le_trans h2_s h3_s
                        unfold Inside at hw_in_al; omega)))
                · apply hav0_al (w_out.toNat, 96) (by simp) j
                  unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
              · apply hav0_al (w_out.toNat, 96) (by simp) j
                unfold worldOwned; exact List.mem_append.2 (Or.inr hnd)
            have hws_s1 : WorldStep (fun _ => []) ["heap_ptr", "scratch_ptr"] pmcKeep
                (fun _ _ st S' Nd' => IvlsDisj [(w_out.toNat, 96)] (worldOwned st S' Nd'))
                entry none s1 := by
              have h1 : WorldStep (fun _ => []) ["heap_ptr"] stdKeep
                  (fun _ _ st S' Nd' => IvlsDisj [(w_out.toNat, 96)] (worldOwned st S' Nd'))
                  entry (some (.returned (.val (.word w_out)))) post_al := by
                obtain ⟨a1, a2, a3, a4, a5⟩ := hws_al_av
                refine ⟨a1, a2, a3, a4, fun S_x Nd_x hW_x hD_x => ?_⟩
                obtain ⟨S', Nd', hs, hw', hog, hfo, hq⟩ := a5 S_x Nd_x hW_x hD_x
                obtain ⟨w', hw_eq, hav⟩ := hq (.val (.word w_out)) rfl
                injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
                exact ⟨S', Nd', hs, hw', hog, hfo, hav⟩
              exact worldStep_pmcKeep_with_locals_clock_Q
                (worldStep_pmcKeep_of_stdKeep (by intro g hg; simp at hg; subst hg; simp) h1)
                s1.locals post_al.clock
            -- Step 2: seq (call "memzero" [out, 96]) (dec "frame" .one 0 tail)
            rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
            rw [evaluateHOLFiniteState_call] at hres ⊢
            have hargs_mz : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
                [.var .local (ofString "out"), .const 96#64] = some [.val (.word w_out), .val (.word 96#64)] := by
              rw [evalListHOLFinite_eq_toExact]
              simp [evalListHOLExact, evalHOLExact, hs1_out]
            simp only [hargs_mz] at hres ⊢
            rcases hl_mz : lookupCodeHOLFinite s1.code.lookup (ofString "memzero")
                [.val (.word w_out), .val (.word 96#64)] with _ | ⟨body_mz, callee_mz, ret_mz⟩
            · simp only [hl_mz] at hres
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
            · simp only [hl_mz] at hres ⊢
              by_cases hclk1 : s1.clock = 0
              · simp only [hclk1, ↓reduceIte] at hres
                exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
              · simp only [hclk1, ↓reduceIte] at hres ⊢
                have hl_mz_rt : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "memzero")
                    [.val (.word w_out), .val (.word 96#64)] = some (body_mz, callee_mz, ret_mz) := by
                  rwa [← hs1_code]
                have hraw_mz := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "memzero")
                  [.val (.word w_out), .val (.word 96#64)] body_mz callee_mz ret_mz hl_mz_rt
                have hlook_mz_fn := R10Shards.Fast_GbodyC17ToC21.lookup_memzero_fn
                have hbody_mz_eq : body_mz = sourceFnBody Guest.Software.guestFn_memzero ∧ ret_mz = .one := by
                  unfold lookupCodeHOLExact at hraw_mz
                  rw [hlook_mz_fn] at hraw_mz
                  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memzero,
                    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
                    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
                    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural] at hraw_mz ⊢
                  split at hraw_mz
                  · injection hraw_mz with hp
                    exact ⟨(Prod.mk.inj hp).1.symm, (Prod.mk.inj (Prod.mk.inj hp).2).2.symm⟩
                  · cases hraw_mz
                have hp2_mz := R10Shards.Fast_GbodyC17ToC21.callee_param_two s1 (ofString "memzero")
                  (ofString "dst") (ofString "n") .one .one _ _
                  (by rw [hs1_code]; exact hlook_mz_fn)
                  (.var .local (ofString "out")) (.const 96#64) (.val (.word w_out)) (.val (.word 96#64))
                  [.val (.word w_out), .val (.word 96#64)] body_mz callee_mz ret_mz
                  (by simp [evalAt, evalHOLExact, hs1_out]) rfl hargs_mz hl_mz
                have hdst_mz : locN (callEntryStateHOLFinite s1 callee_mz) "dst" = w_out.toNat := by
                  simp [locN, callEntryStateHOLFinite, hp2_mz.2.1]
                have hn_mz : locN (callEntryStateHOLFinite s1 callee_mz) "n" = 96 := by
                  simp [locN, callEntryStateHOLFinite, hp2_mz.2.2]
                rcases hrun_mz : evaluateHOLFiniteState (callEntryStateHOLFinite s1 callee_mz) body_mz with ⟨res_mz, post_mz⟩
                simp only [hrun_mz] at hres ⊢
                have hres_mz_body : Resumes res_mz →
                    Wave8Contracts.M08.RegionWriteFrame (callEntryStateHOLFinite s1 callee_mz) post_mz (w_out.toNat, 96) := by
                  intro hr_mz
                  have hce_code : (callEntryStateHOLFinite s1 callee_mz).code = originalRuntimeCode := hs1_code
                  have hce_G : GuestInv (callEntryStateHOLFinite s1 callee_mz) :=
                    (localsFree_arenaReady s1 callee_mz (s1.clock - 1) hM_s1.1).1
                  have hr_m08 : Wave8Contracts.M08.Resumes res_mz := by
                    rcases hr_mz with ⟨v, hv⟩ | ⟨e, v, hv, ht⟩
                    · exact Or.inl ⟨v, hv⟩
                    · exact Or.inr ⟨e, v, hv, ht⟩
                  have hmwf := Wave8Contracts.M08.memzero_body_frame (callEntryStateHOLFinite s1 callee_mz)
                    hce_code hce_G (by rw [← hbody_mz_eq.1, hrun_mz]; exact hr_m08)
                  rw [← hbody_mz_eq.1, hrun_mz, hdst_mz, hn_mz] at hmwf
                  exact hmwf
                cases res_mz with
                | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                | some br_mz =>
                  cases br_mz with
                  | timeOut => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                  | error => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                  | «break» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                  | «continue» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                  | finalFfi _ => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                  | exception eid eval =>
                    dsimp only at hres ⊢
                    have hmwf := hres_mz_body hres
                    obtain ⟨hws_mz_raw, _⟩ :=
                      worldStep_of_region_writes_ownedEq (s := s1) (post := post_mz)
                        (r := some (.exception eid eval)) (R := fun _ => [(w_out.toNat, 96)])
                        hWOK_s1
                        ⟨hmwf.1, hmwf.2.1, hmwf.2.2.1, hmwf.2.2.2.1, hmwf.2.2.2.2.1, hmwf.2.2.2.2.2.1⟩
                        hmwf.2.2.2.2.2.2.1
                        (fun a ha_lt hnot => hmwf.2.2.2.2.2.2.2.1 a ha_lt (fun hin => hnot _ (List.mem_singleton.2 rfl) hin))
                        hmwf.2.2.2.2.2.2.2.2
                    have hws_mz_s1 : WorldStep (fun _ => [(w_out.toNat, 96)]) ["heap_ptr", "scratch_ptr"] pmcKeep
                        NoExtra s1 (some (.exception eid eval)) (emptyLocalsHOLFinite post_mz) := by
                      have hne : WorldStep (fun _ => [(w_out.toNat, 96)]) [] stdKeep NoExtra
                          s1 (some (.exception eid eval)) post_mz := by
                        obtain ⟨a1, a2, a3, a4, a5⟩ := hws_mz_raw
                        exact ⟨a1, a2, a3, a4, fun S_x Nd_x hW_x hD_x => by
                          obtain ⟨S', Nd', hs, hw', hog, hfo, _⟩ := a5 S_x Nd_x hW_x hD_x
                          exact ⟨S', Nd', hs, hw', hog, hfo, trivial⟩⟩
                      exact worldStep_pmcKeep_with_locals_clock
                        (worldStep_pmcKeep_of_stdKeep (by intro g hg; cases hg) hne)
                        HolFiniteMapExact.empty post_mz.clock
                    have hhp_mz_eq : globN (emptyLocalsHOLFinite post_mz) "heap_ptr" = globN s1 "heap_ptr" :=
                      Wave8Contracts.M08.globN_congr hmwf.2.2.2.2.2.1 "heap_ptr"
                    have hws_en_mz := worldStep_pmcPrefix_trans (w_out := w_out)
                      (Q2 := NoExtra)
                      hM0.1 hWOK_en
                      (fun j hj => by simp at hj)
                      (fun j hj => by simp at hj; subst hj; right; rw [hhp_mz_eq]; exact hw_in_s1)
                      (fun _ _ h => h)
                      (fun S2 Nd2 _ hout2 x hx j hj => by
                        simp at hx; subst hx
                        exact hout2 _ (by simp) j (worldTypedIvls_sub_worldOwned _ _ _ j hj))
                      hws_s1 hsp_s1 hws_mz_s1
                      (fun S2 Nd2 S3 Nd3 _ hout2 hOG23 _ _ => by
                        intro x hx j hj
                        simp at hx; subst hx
                        rcases hOG23 j hj with rfl | ⟨k, hk, hin⟩ | hfresh
                        · exact disj_zero_right _
                        · exact disj_of_inside_right hin (hout2 _ (by simp) k hk)
                        · exact Or.inr (Or.inr (Or.inl (Nat.le_trans hw_in_s1.2 hfresh.1))))
                    have hws_en_mz_ne : WorldStep
                        (fun s => bufRegions pmcBufs s ++ [(globN entry "heap_ptr", globN (emptyLocalsHOLFinite post_mz) "heap_ptr" - globN entry "heap_ptr")])
                        ["heap_ptr", "scratch_ptr"] pmcKeep NoExtra
                        entry (some (.exception eid eval)) (emptyLocalsHOLFinite post_mz) := by
                      obtain ⟨a1, a2, a3, a4, a5⟩ := hws_en_mz
                      exact ⟨a1, a2, a3, a4, fun S_x Nd_x hW_x hD_x => by
                        obtain ⟨S', Nd', hs, hw', hog, hfo, _⟩ := a5 S_x Nd_x hW_x hD_x
                        exact ⟨S', Nd', hs, hw', hog, hfo, trivial⟩⟩
                    exact worldStepIn_pmc_with_locals_clock
                      (worldStepIn_pmc_of_prefix_not_returned
                        (R1 := fun s => bufRegions pmcBufs s ++ [(globN entry "heap_ptr", globN (emptyLocalsHOLFinite post_mz) "heap_ptr" - globN entry "heap_ptr")])
                        (fun _ _ => pmc_resumes_not_returned_vac (by intro _ h; simp at h))
                        hM0.1 hWOK_en
                        (fun j hj => by
                          rcases List.mem_append.1 hj with hbuf | hfr
                          · exact Or.inl hbuf
                          · simp at hfr; subst hfr
                            have hle : globN entry "heap_ptr" ≤ globN (emptyLocalsHOLFinite post_mz) "heap_ptr" := hws_en_mz.2.1
                            exact Or.inr ⟨le_rfl, by omega⟩)
                        hws_en_mz_ne)
                      _ post_mz.clock
                  | returned val_mz =>
                    dsimp only at hres ⊢
                    by_cases hsh_mz : shapeEqHOL (shapeOfHOLExact val_mz) ret_mz
                    · simp only [hsh_mz, ↓reduceIte] at hres ⊢
                      have hmwf := hres_mz_body (Or.inl ⟨val_mz, rfl⟩)
                      obtain ⟨hws_mz_raw, hcore_mz⟩ :=
                        worldStep_of_region_writes_ownedEq (s := s1) (post := post_mz)
                          (r := some (.returned val_mz)) (R := fun _ => [(w_out.toNat, 96)])
                          hWOK_s1
                          ⟨hmwf.1, hmwf.2.1, hmwf.2.2.1, hmwf.2.2.2.1, hmwf.2.2.2.2.1, hmwf.2.2.2.2.2.1⟩
                          hmwf.2.2.2.2.2.2.1
                          (fun a ha_lt hnot => hmwf.2.2.2.2.2.2.2.1 a ha_lt (fun hin => hnot _ (List.mem_singleton.2 rfl) hin))
                          hmwf.2.2.2.2.2.2.2.2
                      have hzf := FunSpec.at_lookup zv_memzero_local s1 hs1_code _ body_mz callee_mz ret_mz hl_mz
                        (localsFree_arenaReady s1 callee_mz (s1.clock - 1) hM_s1.1)
                        (by rw [hrun_mz]; simp)
                      rw [hrun_mz] at hzf
                      have hmem16_zero : memW post_mz (w_out.toNat + 16) = 0 :=
                        hzf val_mz rfl (w_out.toNat + 16)
                          (by rw [hdst_mz]; omega)
                          (by rw [hdst_mz, hn_mz]; omega)
                          (by omega)
                      -- Step 3: dec "frame" .one 0 tail from { post_mz with locals := s1.locals }
                      set s2_pre : PanSemStateFiniteExact 64 F := { post_mz with locals := s1.locals }
                      rw [evaluateHOLFiniteState_dec_total] at hres ⊢
                      simp only [evalHOLExact, shapeEqHOL, shapeOfHOLExact, ↓reduceIte] at hres ⊢
                      set s2 := setVarHOLFinite (ofString "frame") (.val (.word 0#64)) s2_pre
                      have hhp_mz_eq : globN s2 "heap_ptr" = globN s1 "heap_ptr" :=
                        Wave8Contracts.M08.globN_congr hmwf.2.2.2.2.2.1 "heap_ptr"
                      have hsp_mz_eq : globN s2 "scratch_ptr" = globN s1 "scratch_ptr" :=
                        Wave8Contracts.M08.globN_congr hmwf.2.2.2.2.2.1 "scratch_ptr"
                      have hs2_code : s2.code = originalRuntimeCode := by
                        change post_mz.code = originalRuntimeCode
                        rw [hmwf.1]; exact hs1_code
                      have hs2_msg : s2.locals.lookup (ofString "msg") = entry.locals.lookup (ofString "msg") := by
                        simp [s2, s2_pre, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hs1_msg,
                          show ofString "frame" ≠ ofString "msg" by decide]
                      have hs2_out : s2.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
                        simp [s2, s2_pre, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hs1_out,
                          show ofString "frame" ≠ ofString "out" by decide]
                      have hs2_fr : s2.locals.lookup (ofString "frame") = some (.val (.word 0#64)) := by
                        simp [s2, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
                      set S_s1_full := S0_s1 ++ [memW entry (locN entry "msg" + 152), memW entry (locN entry "msg" + 160)]
                      have hdisj_mz_all : IvlsDisj [(w_out.toNat, 96)]
                          ((locN s1 "msg", 176) :: worldTypedIvls s1 S_s1_full Nd_s1) := by
                        intro x hx j hj
                        simp only [List.mem_singleton] at hx; subst hx
                        rcases List.mem_cons.1 hj with rfl | hj_wti
                        · have hm_in_en : Inside (locN entry "msg", 176) sourceBase (globN entry "heap_ptr") :=
                            hMA_en.2.2.2.2.2.2.2.2.2.2.1
                          have hm_eq_loc : locN s1 "msg" = locN entry "msg" := by simp [locN, hs1_msg]
                          rw [hm_eq_loc]
                          exact Or.inr (Or.inr (Or.inr (Nat.le_trans hm_in_en.2 hw_in_s1.1)))
                        · exact hout_ow_s1_at _ (by simp) j (worldTypedIvls_sub_worldOwned _ _ _ j hj_wti)
                      have hws_mz_av : WorldStep (fun _ => [(w_out.toNat, 96)]) [] stdKeep
                          (fun _ _ post0 S' Nd' => IvlsDisj [(w_out.toNat, 96)] (worldOwned post0 S' Nd'))
                          s1 (some (.returned val_mz)) post_mz := by
                        obtain ⟨a1, a2, a3, a4, _⟩ := hws_mz_raw
                        refine ⟨a1, a2, a3, a4, fun S_x Nd_x hW_x hD_x => ?_⟩
                        obtain ⟨hWT_post, howned_eq⟩ := hcore_mz S_x Nd_x hW_x hD_x
                        refine ⟨S_x, Nd_x, fun _ ht => ht, hWT_post,
                          by rw [howned_eq]; exact Wave8Contracts.M08.ownedGrows_refl s1 post_mz _,
                          fun a hkeep _ => hmwf.2.2.2.2.2.2.1 a
                            (fun j hj => hkeep j (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hj)))))
                            (fun hc => by unfold CellHits at hc; omega), ?_⟩
                        dsimp only
                        rw [howned_eq]
                        intro x hx j hj
                        unfold worldOwned at hj
                        rcases List.mem_append.1 hj with h1 | hnd
                        · rcases List.mem_append.1 h1 with htab | hfix
                          · apply hD_x x hx j
                            unfold worldTypedIvls
                            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
                            apply List.mem_append.2; left; exact List.mem_append.2 (Or.inl htab)
                          · apply hout_ow_s1_at x hx j
                            unfold worldOwned
                            exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
                        · apply hD_x x hx j
                          unfold worldTypedIvls
                          exact List.mem_append.2 (Or.inr hnd)
                      obtain ⟨S0_s2, Nd_s2, hMA_s2_pre, hav0_mz, hfp_mz⟩ :=
                        R10Shards.Fast_GbodyC17ToC21.WorldStep.preserves_msgReadyAt hMA_s1 hws_mz_av
                          (fun x hx h0 => by simp at hx; subst hx; simp at h0) hdisj_mz_all
                      have hMA_s2 : R10Shards.Fast_GbodyC17ToC21.MsgReadyAt s2
                          (S0_s2 ++ [memW s1 (locN s1 "msg" + 152), memW s1 (locN s1 "msg" + 160)]) Nd_s2 :=
                        R10Shards.Fast_GbodyC17ToC21.msgReadyAt_with_locals
                          (s := s2_pre)
                          (by simp [HolFiniteMapExact.update, FUPDATE, show ofString "frame" ≠ ofString "msg" by decide])
                          hMA_s2_pre
                      have hM_s2 : MsgReady s2 :=
                        R10Shards.Fast_GbodyC17ToC21.msgReadyAt_msgReady hMA_s2
                      have hout_ow_s2_at : IvlsDisj [(w_out.toNat, 96)]
                          (worldOwned s2 (S0_s2 ++ [memW s1 (locN s1 "msg" + 152), memW s1 (locN s1 "msg" + 160)]) Nd_s2) := by
                        intro x hx j hj
                        simp only [List.mem_singleton] at hx; subst hx
                        change j ∈ worldOwned post_mz _ Nd_s2 at hj
                        unfold worldOwned at hj
                        rcases List.mem_append.1 hj with h1 | hnd
                        · rcases List.mem_append.1 h1 with htab | hfix
                          · rw [List.flatMap_append] at htab
                            rcases List.mem_append.1 htab with htab0 | htab_loc
                            · apply hav0_mz (w_out.toNat, 96) (by simp) j
                              unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl htab0)))
                            · obtain ⟨u, hu_loc, hj_fp⟩ := List.mem_flatMap.1 htab_loc
                              rw [hfp_mz u hu_loc] at hj_fp
                              have hu_S : u ∈ S_s1_full := by
                                simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_loc
                                rcases hu_loc with rfl | rfl
                                · exact hMA_s1.2.2.1
                                · exact hMA_s1.2.2.2.1
                              apply hout_ow_s1_at (w_out.toNat, 96) (by simp) j
                              unfold worldOwned
                              exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨u, hu_S, hj_fp⟩))))
                          · apply hav0_mz (w_out.toNat, 96) (by simp) j
                            unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
                        · apply hav0_mz (w_out.toNat, 96) (by simp) j
                          unfold worldOwned; exact List.mem_append.2 (Or.inr hnd)
                      have hws_mz_s1 : WorldStep (fun _ => [(w_out.toNat, 96)]) ["heap_ptr", "scratch_ptr"] pmcKeep
                          (fun _ _ st S' Nd' => IvlsDisj [(w_out.toNat, 96)] (worldOwned st S' Nd'))
                          s1 none s2 :=
                        worldStep_pmcKeep_with_locals_clock_Q
                          (worldStep_pmcKeep_of_stdKeep (by intro g hg; cases hg) hws_mz_av)
                          s2.locals post_mz.clock
                      have hws_en_s2 := worldStep_pmcPrefix_trans (w_out := w_out)
                        hM0.1 hWOK_en
                        (fun j hj => by simp at hj)
                        (fun j hj => by simp at hj; subst hj; right; rw [hhp_mz_eq]; exact hw_in_s1)
                        (fun _ _ h => h)
                        (fun S2 Nd2 _ hout2 x hx j hj => by
                          simp at hx; subst hx
                          exact hout2 _ (by simp) j (worldTypedIvls_sub_worldOwned _ _ _ j hj))
                        hws_s1 hsp_s1 hws_mz_s1
                        (fun _ _ _ _ _ _ _ _ hQ23 => hQ23)
                      have hw_in_s2 : Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s2 "heap_ptr") := by
                        rw [hhp_mz_eq]; exact hw_in_s1
                      have hw_ok_s2 : WordsOK s2 (w_out.toNat, 96) :=
                        wordsOK_transfer hM_s1.1.1 hM_s2.1.1 hw_ok_s1
                      have hsp_s2 : globN s2 "scratch_ptr" ≤ globN entry "scratch_ptr" := by
                        rw [hsp_mz_eq]; exact hsp_s1
                      have hp1 : PmcA1 entry s2 :=
                        ⟨hM0, hM_s2, hs2_msg, hsp_s2, w_out, hws_en_s2, hs2_out, hs2_fr, hw_out8,
                          hw_in_s2, hw_ok_s2, hmem16_zero,
                          _, _, hMA_s2, hout_ow_s2_at⟩
                      have htail_run := htail s2 hs2_code hp1
                      unfold PmcRelRunStrong at htail_run
                      rcases hrun_tail : evaluateHOLFiniteState s2 tail with ⟨res_t, post_t⟩
                      rw [hrun_tail] at htail_run
                      simp only [hrun_tail] at hres ⊢
                      cases res_t with
                      | none =>
                        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                      | some br_t =>
                        cases br_t with
                        | timeOut => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                        | error => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                        | «break» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                        | «continue» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                        | finalFfi _ => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                        | exception eid eval =>
                          exact worldStepIn_pmc_with_locals_clock
                            (worldStepIn_pmc_with_locals_clock (htail_run hres) _ post_t.clock)
                            _ post_t.clock
                        | returned val_t =>
                          exact worldStepIn_pmc_with_locals_clock
                            (worldStepIn_pmc_with_locals_clock (htail_run (Or.inl ⟨val_t, rfl⟩)) _ post_t.clock)
                            _ post_t.clock
                    · simp only [hsh_mz, Bool.false_eq_true, ↓reduceIte] at hres
                      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          · simp only [hsh_al, Bool.false_eq_true, ↓reduceIte] at hres
            exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

def pmcUpdW (m : BitVec 64 → HolWordLab 64) (a w : BitVec 64) : BitVec 64 → HolWordLab 64 :=
  fun x => if x = a then .word w else m x

theorem pmc_wordsOK_updW {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a w : BitVec 64) (i : Ivl) (hi : WordsOK s i) :
    WordsOK { s with memory := pmcUpdW s.memory a w } i := by
  refine ⟨hi.1, hi.2.1, fun k hk => ?_⟩
  obtain ⟨u, hdom, hu⟩ := hi.2.2 k hk
  by_cases heq : BitVec.ofNat 64 (i.1 + 8 * k) = a
  · exact ⟨w, hdom, by simp [pmcUpdW, heq]⟩
  · exact ⟨u, hdom, by simp [pmcUpdW, heq, hu]⟩

theorem pmc_memW_updW_same {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) (w : BitVec 64) :
    memW { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 a) w } a = w.toNat := by
  unfold memW pmcUpdW; simp

theorem pmc_memW_updW_ne {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : Nat) (w : BitVec 64)
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : b ≠ a) :
    memW { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 a) w } b = memW s b := by
  unfold memW pmcUpdW
  have hbv : BitVec.ofNat 64 b ≠ BitVec.ofNat 64 a := by
    intro heq
    have := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt ha] at this
    exact hne this
  simp [hbv]

theorem pmc_store_out_eval {F : Type} {s : PanSemStateFiniteExact 64 F}
    {w_out : BitVec 64} {off : Nat} {valExp : ExpHOL 64} {w_val : BitVec 64}
    (hs_out : s.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hw_ok : WordsOK s (w_out.toNat, 96))
    (hw_hi : w_out.toNat + 96 ≤ 2 ^ 64)
    (hoff8 : off % 8 = 0)
    (hoff_lt : off < 96)
    (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some (.val (.word w_val))) :
    evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 off)]) valExp) =
      (none, { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val }) := by
  have hdst_eq : w_out + (BitVec.ofNat 64 off + (0 : BitVec 64)) = BitVec.ofNat 64 (w_out.toNat + off) := by
    apply BitVec.eq_of_toNat_eq
    have hz0 : ((0 : BitVec 64)).toNat = 0 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hz0, Nat.add_zero,
      Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show w_out.toNat + off < 2 ^ 64 by omega)]
  have hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (BitVec.ofNat 64 (w_out.toNat + off)))) := by
    simp only [evalHOLExact, evalListHOLExact, hs_out, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, hdst_eq]
  obtain ⟨_, hdom, _⟩ := hw_ok.2.2 (off / 8) (by dsimp only at *; omega)
  have hk_eq : w_out.toNat + 8 * (off / 8) = w_out.toNat + off := by omega
  rw [hk_eq] at hdom
  rw [evaluateHOLFiniteState_store, hdst, hval]
  dsimp only
  simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom, ↓reduceIte]
  rfl

theorem pmc_load_local_off {F : Type} {s : PanSemStateFiniteExact 64 F}
    {lname : String} {w_base : BitVec 64} {sz off : Nat}
    (hlk : s.locals.lookup (ofString lname) = some (.val (.word w_base)))
    (hw_ok : WordsOK s (w_base.toNat, sz))
    (hw_hi : w_base.toNat + sz ≤ 2 ^ 64)
    (hoff8 : off % 8 = 0)
    (hoff_lt : off < sz) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .local (ofString lname), .const (BitVec.ofNat 64 off)])) =
      some (.val (.word (BitVec.ofNat 64 (memW s (w_base.toNat + off))))) := by
  have haddr_eq : w_base + (BitVec.ofNat 64 off + (0 : BitVec 64)) = BitVec.ofNat 64 (w_base.toNat + off) := by
    apply BitVec.eq_of_toNat_eq
    have hz0 : ((0 : BitVec 64)).toNat = 0 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hz0, Nat.add_zero,
      Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show w_base.toNat + off < 2 ^ 64 by omega)]
  have hsz8 : sz % 8 = 0 := hw_ok.2.1
  obtain ⟨u, hdom, hu⟩ := hw_ok.2.2 (off / 8) (by dsimp only at *; omega)
  have hk_eq : w_base.toNat + 8 * (off / 8) = w_base.toNat + off := by omega
  rw [hk_eq] at hdom hu
  have hu_nat : BitVec.ofNat 64 (memW s (w_base.toNat + off)) = u := by
    unfold memW; rw [hu]; simp
  simp only [evalHOLExact, evalListHOLExact, hlk, wordOpHOL, wordOp, valueIsWord, valueWord,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
    haddr_eq, isWfShapeExactHOL, memLoadHOLExact, panMemLoadHOL,
    hdom, hu, hu_nat]

theorem pmcRegions_eq_of_msg_locals {F : Type}
    {s : PanSemStateFiniteExact 64 F} {L : HolFiniteMapExact MlS (ValueHOL 64)} {k : Nat}
    (hmsg : locN { s with locals := L, clock := k } "msg" = locN s "msg") :
    pmcRegions { s with locals := L, clock := k } = pmcRegions s := by
  rw [pmcRegions_eq_bufRegions, pmcRegions_eq_bufRegions, hmsg]; rfl

theorem pmc_recordsKept_with_locals {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {L1 L2 : HolFiniteMapExact MlS (ValueHOL 64)} {k1 k2 : Nat}
    (hmsg : locN { s with locals := L1, clock := k1 } "msg" = locN s "msg")
    (h : RecordsKept pmcRegions pmcKeep { s with locals := L1, clock := k1 } post) :
    RecordsKept pmcRegions pmcKeep s { post with locals := L2, clock := k2 } := by
  have hreg := pmcRegions_eq_of_msg_locals hmsg
  intro r hr hnz off hoff hnh
  exact h r hr hnz off hoff (fun i hi => hnh i (by dsimp only at hi; rwa [hreg] at hi))

theorem pmc_frameOutside_with_locals {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {L1 L2 : HolFiniteMapExact MlS (ValueHOL 64)} {k1 k2 : Nat} {S Nd : List Nat}
    (hmsg : locN { s with locals := L1, clock := k1 } "msg" = locN s "msg")
    (h : FrameOutside { s with locals := L1, clock := k1 } post
      (worldOwned { s with locals := L1, clock := k1 } S Nd ++
       pmcRegions { s with locals := L1, clock := k1 } ++
       [freeGap { s with locals := L1, clock := k1 }])
      (heapFree { s with locals := L1, clock := k1 })) :
    FrameOutside s { post with locals := L2, clock := k2 }
      (worldOwned s S Nd ++ pmcRegions s ++ [freeGap s]) (heapFree s) := by
  have hreg := pmcRegions_eq_of_msg_locals hmsg
  have hwo : worldOwned { s with locals := L1, clock := k1 } S Nd = worldOwned s S Nd := rfl
  have hfg : freeGap { s with locals := L1, clock := k1 } = freeGap s := rfl
  have hhf : heapFree { s with locals := L1, clock := k1 } = heapFree s := rfl
  intro a hkeep hfresh
  exact h a (by rw [hwo, hreg, hfg]; exact hkeep) (by rw [hhf]; exact hfresh)

theorem pmcA2_with_locals {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hs_out : L.lookup (ofString "out") = s.locals.lookup (ofString "out"))
    (hs_fr : L.lookup (ofString "frame") = s.locals.lookup (ofString "frame"))
    (hp2 : PmcA2 entry s) :
    PmcA2 entry { s with locals := L } := by
  obtain ⟨hM0, w_out, w_fr, hws, hout, hfr, hw8, hwin, hwok, hm16, hwfrok, hwfrin, hlok, hdisj⟩ := hp2
  refine ⟨hM0, w_out, w_fr, ?_, ?_, ?_, hw8, hwin, hwok, hm16, hwfrok, hwfrin, hlok, hdisj⟩
  · obtain ⟨hA, hhp, hG, hK, hW⟩ := hws
    refine ⟨localsFree_arenaReady s L s.clock hA, hhp, hG, hK, fun S_x Nd_x hWT_x hT_x hD_x => ?_⟩
    obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hout_d, hlive⟩ := hW S_x Nd_x hWT_x hT_x hD_x
    exact ⟨S', Nd', hsub,
      (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals s L s.clock S' Nd').2 hWT',
      hOG, hFO, hout_d, hlive⟩
  · rw [hs_out]; exact hout
  · rw [hs_fr]; exact hfr

theorem pmc_call_frame_callee {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {fname : MlS} {tail : ProgHOL 64}
    {w_out : BitVec 64}
    {restL : HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64)}
    (hcall_spec : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep RetFrameResultStrong fname)
    (hlook_rt : ∃ b r, originalRuntimeCode.lookup fname = some ([(ofString "msg", .one)], b, r))
    (hrest_out : ∀ m, (restL m).lookup (ofString "out") = m.lookup (ofString "out"))
    (hrest_fr : ∀ m, (restL m).lookup (ofString "frame") = m.lookup (ofString "frame"))
    (htail : ∀ s' : PanSemStateFiniteExact 64 F, s'.code = originalRuntimeCode →
      PmcA2 entry s' → PmcRelRunStrong entry tail s')
    (hcode : s.code = originalRuntimeCode)
    (hM0 : MsgReady entry)
    (hM_s : MsgReady s)
    (hs_msg : s.locals.lookup (ofString "msg") = entry.locals.lookup (ofString "msg"))
    (hsp_s : globN s "scratch_ptr" ≤ globN entry "scratch_ptr")
    (hws_s : WorldStep (fun st => bufRegions pmcBufs st ++ [(globN entry "heap_ptr", globN s "heap_ptr" - globN entry "heap_ptr")])
      ["heap_ptr", "scratch_ptr"] pmcKeep
      (fun _ _ st S Nd => IvlsDisj [(w_out.toNat, 96)] (worldOwned st S Nd))
      entry none s)
    (hs_out : s.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hs_fr : s.locals.lookup (ofString "frame") = some (.val (.word 0#64)))
    (hw_out8 : w_out.toNat % 8 = 0)
    (hw_in_s : Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s "heap_ptr"))
    (hw_ok_s : WordsOK s (w_out.toNat, 96))
    (hmem16_s : memW s (w_out.toNat + 16) = 0)
    (hMA_s : ∃ S_s Nd_s,
      R10Shards.Fast_GbodyC17ToC21.MsgReadyAt s S_s Nd_s ∧
      IvlsDisj [(w_out.toNat, 96)] (worldOwned s S_s Nd_s)) :
    let out1 := evaluateHOLFiniteState s
      (.call (some ((some (.local, ofString "frame")), none)) fname [.var .local (ofString "msg")])
    let out := match out1.1 with
      | none => evaluateHOLFiniteState { out1.2 with locals := restL out1.2.locals } tail
      | some _ => (out1.1, { out1.2 with locals := restL out1.2.locals })
    Resumes out.1 →
      WorldStepIn pmcTables pmcRegions pmcGlobals pmcKeep RetMessageOutputStrong
        entry out.1 out.2 := by
  dsimp only
  intro hres
  rw [evaluateHOLFiniteState_call] at hres ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "msg")] with _ | vals
  · simp only [hargs] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [hargs] at hres ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body_c, callee_c, ret_c⟩
    · simp only [hl] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hl] at hres ⊢
      by_cases hclk : s.clock = 0
      · simp only [hclk, ↓reduceIte] at hres
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      · simp only [hclk, ↓reduceIte] at hres ⊢
        obtain ⟨b_rt, r_rt, hlook_fn⟩ := hlook_rt
        have hpc_msg : callee_c.lookup (ofString "msg") = s.locals.lookup (ofString "msg") :=
          callee_param_one s fname (ofString "msg") .one b_rt r_rt
            (by rw [hcode]; exact hlook_fn) vals body_c callee_c ret_c hargs hl
        let ent := callEntryStateHOLFinite s callee_c
        have hM_ent : MsgReady ent :=
          localsOnly_msgReady s callee_c (s.clock - 1)
            (fun n hn => by simp at hn; subst hn; exact hpc_msg) hM_s
        have hmeta_c := (evaluateHOLFiniteState_metadata ent body_c).1
        rcases hrun_c : evaluateHOLFiniteState ent body_c with ⟨res_c, post_c⟩
        dsimp only [ent] at hrun_c hmeta_c
        rw [hrun_c] at hmeta_c
        dsimp only at hmeta_c
        simp only [hrun_c] at hres ⊢
        have hnt_c : (evaluateHOLFiniteState ent body_c).1 ≠ some .timeOut := by
          dsimp only [ent]; rw [hrun_c]
          rintro rfl
          exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        have hspec := FunSpec.at_lookup hcall_spec s hcode vals body_c callee_c ret_c hl hM_ent hnt_c
        dsimp only [ent] at hspec
        rw [hrun_c] at hspec
        dsimp only at hspec
        obtain ⟨_, _, hMA_en⟩ := R10Shards.Fast_GbodyC17ToC21.msgReadyAt_of_msgReady hM0
        have hm8_en : locN entry "msg" % 8 = 0 := hMA_en.2.2.2.2.2.2.2.2.2.1
        have hm_in_en : Inside (locN entry "msg", 176) sourceBase (globN entry "heap_ptr") :=
          hMA_en.2.2.2.2.2.2.2.2.2.2.1
        have hm_fix_en : ∀ j ∈ fixedObjects entry, Disj (locN entry "msg", 176) j := by
          intro j hj
          apply hMA_en.2.2.2.2.2.2.2.2.2.2.2.1 j
          unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hj)))
        have hmsg_loc_s : locN s "msg" = locN entry "msg" := by simp [locN, hs_msg]
        have hmsg_loc_ent : locN ent "msg" = locN s "msg" := by
          simp [ent, callEntryStateHOLFinite, locN, hpc_msg]
        have hR1_z : ∀ j ∈ bufRegions pmcBufs entry ++ [(globN entry "heap_ptr", globN s "heap_ptr" - globN entry "heap_ptr")],
            j.2 = 0 → j.1 % 8 = 0 := by
          intro j hj hz
          rcases List.mem_append.1 hj with hj_buf | hj_fr
          · exact pmcRegions_zero_aligned hm8_en j
              (by rw [pmcRegions_eq_bufRegions]; exact List.mem_cons_of_mem _ hj_buf) hz
          · simp only [List.mem_singleton] at hj_fr; subst hj_fr
            exact hM0.1.2.2.2.2.2.2.1
        have hR1_sub : ∀ j ∈ bufRegions pmcBufs entry ++ [(globN entry "heap_ptr", globN s "heap_ptr" - globN entry "heap_ptr")],
            j ∈ bufRegions pmcBufs entry ∨ Inside j (globN entry "heap_ptr") (globN s "heap_ptr") := by
          intro j hj
          rcases List.mem_append.1 hj with hj_buf | hj_fr
          · exact Or.inl hj_buf
          · simp only [List.mem_singleton] at hj_fr; subst hj_fr
            exact Or.inr ⟨le_rfl, by have := hws_s.2.1; omega⟩
        cases res_c with
        | none =>
          exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | some br_c =>
          cases br_c with
          | timeOut => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | error => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | «break» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | «continue» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | finalFfi _ => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | exception eid eval =>
            dsimp only at hres ⊢
            have hstep_ex := hspec hres
            have htabs_ent : pmcTables ent = pmcTables s := by
              unfold pmcTables; rw [hmsg_loc_ent]; rfl
            have hreg_ent : pmcRegions ent = pmcRegions s :=
              pmcRegions_eq_of_msg_locals hmsg_loc_ent
            have hstep_s : WorldStepIn pmcTables pmcRegions pmcGlobals pmcKeep RetMessageOutputStrong
                s (some (.exception eid eval)) (emptyLocalsHOLFinite post_c) := by
              obtain ⟨hAp, hhp, hG, hK, hW⟩ := hstep_ex
              refine ⟨localsFree_arenaReady post_c HolFiniteMapExact.empty post_c.clock hAp, hhp, hG,
                pmc_recordsKept_with_locals hmsg_loc_ent hK,
                fun S_x Nd_x hWT_x hT_x hD_x => ?_⟩
              have hT_ent : ∀ t ∈ pmcTables ent, t ∈ S_x := by rwa [htabs_ent]
              have hD_ent : IvlsDisj (pmcRegions ent) (worldTypedIvls ent S_x Nd_x) := by
                have hwti : worldTypedIvls ent S_x Nd_x = worldTypedIvls s S_x Nd_x := rfl
                rwa [hreg_ent, hwti]
              obtain ⟨S', Nd', hsub, hWT', hOG, hFO, _⟩ :=
                hW S_x Nd_x ((R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals _ _ _ _ _).2 hWT_x) hT_ent hD_ent
              exact ⟨S', Nd', hsub,
                (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals post_c HolFiniteMapExact.empty post_c.clock S' Nd').2 hWT',
                hOG, pmc_frameOutside_with_locals hmsg_loc_ent hFO,
                fun v hv => absurd hv (by simp), fun v hv => absurd hv (by simp)⟩
            exact worldStepIn_pmc_with_locals_clock
              (worldStepIn_pmc_trans_prefix (w_out := w_out)
                (Q := RetMessageOutputStrong) (Q_out := RetMessageOutputStrong)
                hmsg_loc_s hm8_en hm_in_en hm_fix_en hM0.1 (msgReady_worldOK entry hM0)
                hR1_z hR1_sub hw_out8 hw_in_s (fun _ _ h => h) hws_s hsp_s hstep_s
                (fun _ _ _ _ _ => pmc_resumes_not_returned_vac (by simp)))
              (restL (emptyLocalsHOLFinite post_c).locals) post_c.clock
          | returned val_c =>
            dsimp only at hres ⊢
            by_cases hsh1 : shapeEqHOL (shapeOfHOLExact val_c) ret_c = true
            · simp only [hsh1, ↓reduceIte] at hres ⊢
              simp only [isValidValueHOLExact, lookupKvarHOLExact, hs_fr] at hres ⊢
              by_cases hsh2 : shapeEqHOL (shapeOfHOLExact val_c) (shapeOfHOLExact (.val (.word 0#64))) = true
              · simp only [hsh2, ↓reduceIte, setKvarHOLFinite] at hres ⊢
                have hstep_ret := hspec (Or.inl ⟨val_c, rfl⟩)
                have htabs_ent : pmcTables ent = pmcTables s := by
                  unfold pmcTables; rw [hmsg_loc_ent]; rfl
                have hreg_ent : pmcRegions ent = pmcRegions s :=
                  pmcRegions_eq_of_msg_locals hmsg_loc_ent
                obtain ⟨S_s, Nd_s, hMAs, hout_ow_s⟩ := hMA_s
                have hT_ent0 : ∀ t ∈ pmcTables ent, t ∈ S_s := by
                  rw [htabs_ent]
                  intro t ht
                  simp only [pmcTables, List.mem_cons, List.not_mem_nil, or_false] at ht
                  rcases ht with rfl | rfl
                  · exact hMAs.2.2.1
                  · exact hMAs.2.2.2.1
                have hD_ent0 : IvlsDisj (pmcRegions ent) (worldTypedIvls ent S_s Nd_s) := by
                  have hwti : worldTypedIvls ent S_s Nd_s = worldTypedIvls s S_s Nd_s := rfl
                  rw [hreg_ent, hwti]
                  exact pmcRegions_disj_of_msgReady hMAs.2.1 hMAs.2.2.2.2.2.2.2.2.2.2.2.1
                obtain ⟨S_p0, Nd_p0, _, hWT_p0, _, _, hret0, hstrong0⟩ :=
                  hstep_ret.2.2.2.2 S_s Nd_s
                    ((R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals _ _ _ _ _).2 hMAs.2.1)
                    hT_ent0 hD_ent0
                obtain ⟨w_fr, hvc_eq, hw_fr_ok0, _, hlok0⟩ := hret0 val_c rfl
                obtain ⟨w_fr', hvc_eq', hin_fr0, _, hlive0, hdisj_out0⟩ := hstrong0 val_c rfl
                rw [hvc_eq] at hvc_eq'; injection hvc_eq' with hvc_eq''; injection hvc_eq'' with hw_fr_eq; subst hw_fr_eq
                subst hvc_eq
                set s_next := setVarHOLFinite (ofString "frame") (.val (.word w_fr))
                  { post_c with locals := s.locals, clock := post_c.clock }
                have hs_next_code : s_next.code = originalRuntimeCode := hmeta_c.trans hcode
                have hs_next_out : s_next.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
                  simp [s_next, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hs_out,
                    show ofString "frame" ≠ ofString "out" by decide]
                have hs_next_fr : s_next.locals.lookup (ofString "frame") = some (.val (.word w_fr)) := by
                  simp [s_next, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
                have hstep_s_next : WorldStepIn pmcTables pmcRegions pmcGlobals pmcKeep
                    (fun _ _ post S' Nd' => PmcLogsLiveOwned post S' Nd' (memW post (w_fr.toNat + 88)))
                    s none s_next := by
                  obtain ⟨hAp, hhp, hG, hK, hW⟩ := hstep_ret
                  refine ⟨localsFree_arenaReady post_c s_next.locals post_c.clock hAp, hhp, hG,
                    pmc_recordsKept_with_locals hmsg_loc_ent hK,
                    fun S_x Nd_x hWT_x hT_x hD_x => ?_⟩
                  have hT_ent : ∀ t ∈ pmcTables ent, t ∈ S_x := by rwa [htabs_ent]
                  have hD_ent : IvlsDisj (pmcRegions ent) (worldTypedIvls ent S_x Nd_x) := by
                    have hwti : worldTypedIvls ent S_x Nd_x = worldTypedIvls s S_x Nd_x := rfl
                    rwa [hreg_ent, hwti]
                  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hret_x, hstrong_x⟩ :=
                    hW S_x Nd_x ((R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals _ _ _ _ _).2 hWT_x) hT_ent hD_ent
                  obtain ⟨w_fr_x, hvc_x, _, _, hlive_x, _⟩ := hstrong_x (.val (.word w_fr)) rfl
                  injection hvc_x with hvc_x'; injection hvc_x' with hw_x; subst hw_x
                  obtain ⟨w_fr_y, hvc_y, _, _, hlok_x⟩ := hret_x (.val (.word w_fr)) rfl
                  injection hvc_y with hvc_y'; injection hvc_y' with hw_y; subst hw_y
                  exact ⟨S', Nd', hsub,
                    (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals post_c s_next.locals post_c.clock S' Nd').2 hWT',
                    hOG, pmc_frameOutside_with_locals hmsg_loc_ent hFO,
                    pmcLogsLiveOwned_congr_live hAp.2 hlok_x hlive_x rfl rfl
                      (fun a => a) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)⟩
                have hws_en_next := worldStepIn_pmc_trans_prefix (w_out := w_out)
                  (Q := fun _ _ post S' Nd' => PmcLogsLiveOwned post S' Nd' (memW post (w_fr.toNat + 88)))
                  (Q_out := fun _ _ post S' Nd' =>
                    IvlsDisj [(w_out.toNat, 96)] (worldOwned post S' Nd') ∧
                    PmcLogsLiveOwned post S' Nd' (memW post (w_fr.toNat + 88)))
                  hmsg_loc_s hm8_en hm_in_en hm_fix_en hM0.1 (msgReady_worldOK entry hM0)
                  hR1_z hR1_sub hw_out8 hw_in_s (fun _ _ h => h) hws_s hsp_s hstep_s_next
                  (fun _ _ hout_ow3 _ hlive3 => ⟨hout_ow3, hlive3⟩)
                -- Also extract IvlUnhit s s_next (w_out.toNat, 96) at (S_s, Nd_s)!
                have hout_in2 : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
                  ⟨le_trans hM0.1.2.1 hw_in_s.1, hw_in_s.2⟩
                have hout_disj_R2 : ∀ j ∈ pmcRegions s, Disj (w_out.toNat, 96) j := by
                  rw [pmcRegions_eq_bufRegions]
                  intro j hj
                  rcases List.mem_cons.1 hj with rfl | hj_buf
                  · rw [hmsg_loc_s]
                    exact Or.inr (Or.inr (Or.inr (Nat.le_trans hm_in_en.2 hw_in_s.1)))
                  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj_buf
                    obtain ⟨sz, hgb, _, hle⟩ := validBufList_pmcBufs p hp
                    have hfix_p : bufferRegion s (p.1, sz) ∈ fixedObjects s := by
                      unfold fixedObjects
                      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
                      exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
                    have hd_sz := hout_ow_s (w_out.toNat, 96) (by simp) _
                      (by unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix_p))))
                    by_cases h0 : globN s p.1 = 0
                    · simp [bufferRegion, h0]; exact disj_zero_right _
                    · simp only [bufferRegion, h0, ↓reduceIte] at hd_sz ⊢
                      exact disj_of_inside_right (j' := (globN s p.1, sz))
                        ⟨le_rfl, by dsimp; omega⟩ hd_sz
                obtain ⟨_, _, _, _, hOG_at, hFO_at, _⟩ :=
                  hstep_s_next.2.2.2.2 S_s Nd_s hMAs.2.1
                    (by
                      intro t ht
                      simp only [pmcTables, List.mem_cons, List.not_mem_nil, or_false] at ht
                      rcases ht with rfl | rfl
                      · exact hMAs.2.2.1
                      · exact hMAs.2.2.2.1)
                    (pmcRegions_disj_of_msgReady hMAs.2.1 hMAs.2.2.2.2.2.2.2.2.2.2.2.1)
                obtain ⟨_, _, hout_u_s_next⟩ :=
                  heap_ivl_survives_step (b := (w_out.toNat, 96))
                    hM_s.1.2 hstep_s_next.2.1 hOG_at hFO_at
                    (worldOwned_zero_aligned hMAs.2.1)
                    (pmcRegions_zero_aligned (by rw [hmsg_loc_s]; exact hm8_en))
                    hw_out8 (by dsimp) hout_in2
                    (fun j hj => hout_ow_s (w_out.toNat, 96) (by simp) j hj)
                    hout_disj_R2
                have hw_hi_s : w_out.toNat + 96 ≤ 2 ^ 64 :=
                  (ivl_allocated_bound hM_s.1.2 (Or.inl hout_in2)).2
                have hmem16_next : memW s_next (w_out.toNat + 16) = 0 := by
                  rw [memW_eq_of_ivlUnhit hout_u_s_next (by omega) hw_hi_s ⟨by dsimp; omega, by dsimp; omega⟩]
                  exact hmem16_s
                have hw_in_next : Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s_next "heap_ptr") :=
                  ⟨hw_in_s.1, le_trans hw_in_s.2 hstep_s_next.2.1⟩
                have hw_ok_next : WordsOK s_next (w_out.toNat, 96) :=
                  wordsOK_transfer hM_s.1.1 hws_en_next.1.1 hw_ok_s
                have hw_fr_ok_next : WordsOK s_next (w_fr.toNat, 280) :=
                  wordsOK_transfer hstep_ret.1.1 hws_en_next.1.1 hw_fr_ok0
                have hlok_next : LogsListOK s_next (memW s_next (w_fr.toNat + 88)) :=
                  pmc_logsListOK_congr_live hstep_ret.1.2 hstep_ret.1.1 hws_en_next.1.1 le_rfl hlok0
                    (fun a => a) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)
                have hdisj_logs_out : memW s_next (w_fr.toNat + 88) ≠ 0 →
                    Disj (memW s_next (w_fr.toNat + 88), 24) (w_out.toNat, 96) ∧
                    Disj (memW s_next (memW s_next (w_fr.toNat + 88)),
                      8 * memW s_next (memW s_next (w_fr.toNat + 88) + 8)) (w_out.toNat, 96) ∧
                    ∀ i, i < memW s_next (memW s_next (w_fr.toNat + 88) + 8) →
                      Disj (memW s_next (memW s_next (memW s_next (w_fr.toNat + 88)) + 8 * i), 40) (w_out.toNat, 96) := by
                  intro hnz
                  have hhp_ent_s : globN ent "heap_ptr" = globN s "heap_ptr" := rfl
                  have hmem_s_next_eq : ∀ a : Nat, memW s_next a = memW post_c a := fun _ => rfl
                  simp only [hmem_s_next_eq] at hnz ⊢
                  obtain ⟨hd_hd, hd_arr, hd_ent⟩ := hdisj_out0 hnz
                  have hsep : heapLimit ≤ scratchStart := by decide
                  have hhp_lim : globN post_c "heap_ptr" ≤ heapLimit := hstep_ret.1.2.2.1
                  have hsc_lo : scratchStart ≤ globN post_c "scratch_ptr" :=
                    le_trans hstep_ret.1.2.2.2.1 hstep_ret.1.2.2.2.2.1
                  have hw_hi_s_hp : w_out.toNat + 96 ≤ globN s "heap_ptr" := hw_in_s.2
                  have hhp_s_le : globN s "heap_ptr" ≤ globN post_c "heap_ptr" := hstep_ret.2.1
                  refine ⟨?_, ?_, ?_⟩
                  · rcases hd_hd with hin_sc | hin_hp
                    · exact Or.inr (Or.inr (Or.inr (by unfold Inside at hin_sc; dsimp only at *; omega)))
                    · rw [hhp_ent_s] at hin_hp
                      exact Or.inr (Or.inr (Or.inr (le_trans hw_hi_s_hp hin_hp.1)))
                  · rcases hd_arr with hin_sc | hin_hp
                    · exact Or.inr (Or.inr (Or.inr (by unfold Inside at hin_sc; dsimp only at *; omega)))
                    · rw [hhp_ent_s] at hin_hp
                      exact Or.inr (Or.inr (Or.inr (le_trans hw_hi_s_hp hin_hp.1)))
                  · intro i hi
                    have hin_hp := hd_ent i hi
                    rw [hhp_ent_s] at hin_hp
                    exact Or.inr (Or.inr (Or.inr (le_trans hw_hi_s_hp hin_hp.1)))
                have hp2 : PmcA2 entry { s_next with locals := restL s_next.locals } :=
                  pmcA2_with_locals (hrest_out s_next.locals) (hrest_fr s_next.locals)
                    ⟨hM0, w_out, w_fr, hws_en_next, hs_next_out, hs_next_fr, hw_out8,
                      hw_in_next, hw_ok_next, hmem16_next, hw_fr_ok_next, hin_fr0, hlok_next, hdisj_logs_out⟩
                exact htail { s_next with locals := restL s_next.locals } hs_next_code hp2 hres
              · simp only [hsh2, Bool.false_eq_true, ↓reduceIte] at hres
                exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
            · simp only [hsh1, ↓reduceIte] at hres
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

def PmcStoreReady {F : Type}
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop)
    (entry s : PanSemStateFiniteExact 64 F) (w_out : BitVec 64) : Prop :=
  WorldOK entry ∧
  WorldStepIn pmcTables pmcRegions pmcGlobals pmcKeep
    (fun en rr st S' Nd' =>
      IvlsDisj [(w_out.toNat, 96)] (worldOwned st S' Nd') ∧ Q en rr st S' Nd')
    entry none s ∧
  s.locals.lookup (ofString "out") = some (.val (.word w_out)) ∧
  w_out.toNat % 8 = 0 ∧
  Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s "heap_ptr") ∧
  WordsOK s (w_out.toNat, 96)

theorem pmcStoreReady_store {F : Type}
    {Q1 Q2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {entry s : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    {off : Nat} {valExp : ExpHOL 64} {w_val : BitVec 64}
    (hsr : PmcStoreReady Q1 entry s w_out)
    (hoff8 : off % 8 = 0)
    (hoff_lt : off < 96)
    (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some (.val (.word w_val)))
    (hQ12 : ∀ S' Nd',
      WorldTypedWith s S' Nd' →
      WorldTypedWith { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val } S' Nd' →
      worldOwned { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val } S' Nd' =
        worldOwned s S' Nd' →
      IvlsDisj [(w_out.toNat, 96)] (worldOwned s S' Nd') →
      Q1 entry none s S' Nd' →
      Q2 entry none { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val } S' Nd') :
    evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 off)]) valExp) =
      (none, { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val }) ∧
    PmcStoreReady Q2 entry
      { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val } w_out := by
  obtain ⟨hen_WOK, hstep, hs_out, hw_out8, hw_in, hw_ok⟩ := hsr
  have hw_in_sb : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
    ⟨le_trans hen_WOK.1.2.1 hw_in.1, hw_in.2⟩
  have hw_hi : w_out.toNat + 96 ≤ 2 ^ 64 :=
    (ivl_allocated_bound hstep.1.2 (Or.inl hw_in_sb)).2
  have hev := pmc_store_out_eval hs_out hw_ok hw_hi hoff8 hoff_lt hval
  obtain ⟨_, hdom, _⟩ := hw_ok.2.2 (off / 8) (by dsimp only at *; omega)
  have hk_eq : w_out.toNat + 8 * (off / 8) = w_out.toNat + off := by omega
  rw [hk_eq] at hdom
  have hx_lt : w_out.toNat + off < 2 ^ 64 := by omega
  have hx_in : w_out.toNat ≤ (BitVec.ofNat 64 (w_out.toNat + off)).toNat ∧
      (BitVec.ofNat 64 (w_out.toNat + off)).toNat + 8 ≤ w_out.toNat + 96 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx_lt]; omega
  have hstep' := worldStepIn_pmc_store_out_word hstep hen_WOK hw_in hx_in hdom
    (fun a hne => by unfold pmcUpdW; exact if_neg hne) hQ12
  exact ⟨hev, hen_WOK, hstep', hs_out, hw_out8, hw_in, pmc_wordsOK_updW s _ _ _ hw_ok⟩

theorem pmcStoreReady_return {F : Type}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {entry s : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (hsr : PmcStoreReady Q entry s w_out)
    (hQ_logs : ∀ S' Nd',
      IvlsDisj [(w_out.toNat, 96)] (worldOwned s S' Nd') →
      Q entry none s S' Nd' →
      LogsListOK s (memW s (w_out.toNat + 16)) ∧
      PmcLogsLiveOwned s S' Nd' (memW s (w_out.toNat + 16))) :
    WorldStepIn pmcTables pmcRegions pmcGlobals pmcKeep RetMessageOutputStrong entry
      (evaluateHOLFiniteState s (.return (.var .local (ofString "out")))).1
      (evaluateHOLFiniteState s (.return (.var .local (ofString "out")))).2 := by
  obtain ⟨hen_WOK, hstep, hs_out, _, hw_in, hw_ok⟩ := hsr
  rw [evaluateHOLFiniteState_return]
  simp only [evalHOLExact, hs_out, shapeOfHOLExact, sizeOfShapeWithContextHOL,
    show (1 : Nat) ≤ 32 by decide, ↓reduceIte]
  dsimp only [emptyLocalsHOLFinite]
  have hw_in_sb : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
    ⟨le_trans hen_WOK.1.2.1 hw_in.1, hw_in.2⟩
  refine worldStepIn_pmc_with_locals_clock ?_ HolFiniteMapExact.empty s.clock
  obtain ⟨hAs, hhp, hG, hK, hW⟩ := hstep
  refine ⟨hAs, hhp, hG, hK, fun S Nd hWT hTS hD => ?_⟩
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hout_disj, hQ⟩ := hW S Nd hWT hTS hD
  obtain ⟨hlok, hlive⟩ := hQ_logs S' Nd' hout_disj hQ
  refine ⟨S', Nd', hsub, hWT', hOG, hFO, ⟨fun v hv => ?_, fun v hv => ?_⟩⟩
  · injection hv with hv'; injection hv' with hv''; subst hv''
    exact ⟨w_out, rfl, hw_ok, hw_in_sb, hout_disj, hlok⟩
  · injection hv with hv'; injection hv' with hv''; subst hv''
    exact ⟨w_out, rfl, hlive⟩

theorem pmc_logs_preserve_store_out {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S' Nd' : List Nat}
    {w_out : BitVec 64} {off : Nat} {w_val : BitVec 64} {logs : Nat}
    (hAs : ArenaOK s) (hgS : GuestInv s)
    (hw_hi : w_out.toNat + 96 ≤ 2 ^ 64)
    (hoff8 : off % 8 = 0) (hoff_lt : off < 96)
    (hlok : LogsListOK s logs)
    (hlive : PmcLogsLiveOwned s S' Nd' logs)
    (hdisj : logs ≠ 0 →
      Disj (logs, 24) (w_out.toNat, 96) ∧
      Disj (memW s logs, 8 * memW s (logs + 8)) (w_out.toNat, 96) ∧
      ∀ i, i < memW s (logs + 8) →
        Disj (memW s (memW s logs + 8 * i), 40) (w_out.toNat, 96))
    (howned_eq : worldOwned { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val } S' Nd' =
      worldOwned s S' Nd') :
    let post := { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val }
    LogsListOK post logs ∧
    PmcLogsLiveOwned post S' Nd' logs ∧
    (logs ≠ 0 →
      Disj (logs, 24) (w_out.toNat, 96) ∧
      Disj (memW post logs, 8 * memW post (logs + 8)) (w_out.toNat, 96) ∧
      ∀ i, i < memW post (logs + 8) →
        Disj (memW post (memW post logs + 8 * i), 40) (w_out.toNat, 96)) := by
  dsimp only
  set post := { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val }
  rcases eq_or_ne logs 0 with rfl | hnz
  · exact ⟨Or.inl rfl, pmcLogsLiveOwned_zero post S' Nd', fun h => absurd rfl h⟩
  · rcases hlok with rfl | ⟨hw_l, hal_l, hn_lt, hn_cap, hent⟩
    · exact absurd rfl hnz
    · obtain ⟨hd_hd, hd_arr, hd_ent⟩ := hdisj hnz
      obtain ⟨hal_arr, _, _⟩ := hlive hnz
      have hhi_hd := (ivl_allocated_bound hAs hal_l).2
      have hhi_arr := (ivl_allocated_bound hAs hal_arr).2
      have hx_lt : w_out.toNat + off < 2 ^ 64 := by omega
      have hhead : ∀ k ∈ ([0, 8, 16] : List Nat), memW post (logs + k) = memW s (logs + k) := by
        intro k hk
        have hk_lt : k + 8 ≤ 24 := by simp at hk; omega
        apply pmc_memW_updW_ne s (w_out.toNat + off) (logs + k) w_val hx_lt
          (by dsimp at hhi_hd; omega)
        rcases hd_hd with h0 | h0 | hd | hd
        · dsimp at h0; omega
        · dsimp at h0; omega
        · dsimp at hd; omega
        · dsimp at hd; omega
      have hptr : ∀ i, i < memW s (logs + 8) →
          memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i) := by
        intro i hi
        apply pmc_memW_updW_ne s (w_out.toNat + off) (memW s logs + 8 * i) w_val hx_lt
          (by dsimp at hhi_arr; omega)
        rcases hd_arr with h0 | h0 | hd | hd
        · dsimp at h0; omega
        · dsimp at h0; omega
        · dsimp at hd; omega
        · dsimp at hd; omega
      have hentry_u : ∀ i, i < memW s (logs + 8) →
          R13Shards.IvlUnhit s post (memW s (memW s logs + 8 * i), 40) := by
        intro i hi a ha8 hch
        have hde := hd_ent i hi
        have hne : a ≠ BitVec.ofNat 64 (w_out.toNat + off) := by
          intro heq
          have ha_eq : a.toNat = w_out.toNat + off := by
            rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx_lt]
          obtain ⟨hc1, hc2⟩ := hch
          rcases hde with h0 | h0 | hd | hd
          · dsimp at h0 hc1 hc2; omega
          · dsimp at h0 hc1 hc2; omega
          · dsimp at hd hc1 hc2; omega
          · dsimp at hd hc1 hc2; omega
        simp [post, pmcUpdW, hne]
      have hgP : GuestInv post := ⟨hgS.code, hgS.memaddrs, hgS.shMemaddrs, hgS.baseAddr⟩
      have hlok' := pmc_logsListOK_congr_live hAs hgS hgP le_rfl
        (Or.inr ⟨hw_l, hal_l, hn_lt, hn_cap, hent⟩) (fun a => a) hhead hptr hentry_u
      have hlive' := pmcLogsLiveOwned_congr_live hAs
        (Or.inr ⟨hw_l, hal_l, hn_lt, hn_cap, hent⟩) hlive howned_eq rfl
        (fun a => a) (fun k hk => hhead k (by simp at hk ⊢; omega)) hptr hentry_u
      have h0_eq : memW post logs = memW s logs := by simpa using hhead 0 (by simp)
      have h8_eq : memW post (logs + 8) = memW s (logs + 8) := hhead 8 (by simp)
      refine ⟨hlok', hlive', fun _ => ⟨hd_hd, by rw [h0_eq, h8_eq]; exact hd_arr, fun i hi => ?_⟩⟩
      rw [h8_eq] at hi
      rw [h0_eq, hptr i hi]
      exact hd_ent i hi

theorem pmcStoreReady_store_then {F : Type}
    {Q1 Q2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {entry s : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    {off : Nat} {valExp : ExpHOL 64} {w_val : BitVec 64} {tail : ProgHOL 64}
    (hsr : PmcStoreReady Q1 entry s w_out)
    (hoff8 : off % 8 = 0) (hoff_lt : off < 96)
    (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some (.val (.word w_val)))
    (hQ12 : ∀ S' Nd',
      WorldTypedWith s S' Nd' →
      WorldTypedWith { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val } S' Nd' →
      worldOwned { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val } S' Nd' =
        worldOwned s S' Nd' →
      IvlsDisj [(w_out.toNat, 96)] (worldOwned s S' Nd') →
      Q1 entry none s S' Nd' →
      Q2 entry none { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val } S' Nd')
    (htail : PmcStoreReady Q2 entry
      { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val } w_out →
      PmcRelRunStrong entry tail
        { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val }) :
    PmcRelRunStrong entry
      (.seq (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 off)]) valExp) tail) s := by
  obtain ⟨heval, hready⟩ := pmcStoreReady_store hsr hoff8 hoff_lt hval hQ12
  unfold PmcRelRunStrong at htail ⊢
  rw [evaluateHOLFiniteState_seq_line780, heval]
  exact htail hready

theorem pmcStoreReady_zero_store {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    {off : Nat} {valExp : ExpHOL 64} {w_val : BitVec 64}
    (hsr : PmcStoreReady (fun _ _ st _ _ => memW st (w_out.toNat + 16) = 0)
      entry s w_out)
    (hoff8 : off % 8 = 0) (hoff_lt : off < 96) (hoff_ne : off ≠ 16)
    (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some (.val (.word w_val))) :
    evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 off)]) valExp) =
      (none, { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val }) ∧
    PmcStoreReady (fun _ _ st _ _ => memW st (w_out.toNat + 16) = 0) entry
      { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val } w_out := by
  have hw_in : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
    ⟨le_trans hsr.1.1.2.1 hsr.2.2.2.2.1.1, hsr.2.2.2.2.1.2⟩
  have hw_hi : w_out.toNat + 96 ≤ 2 ^ 64 :=
    (ivl_allocated_bound hsr.2.1.1.2 (Or.inl hw_in)).2
  refine pmcStoreReady_store hsr hoff8 hoff_lt hval ?_
  intro S Nd _ _ _ _ hzero
  rw [pmc_memW_updW_ne s (w_out.toNat + off) (w_out.toNat + 16) w_val
    (by omega) (by omega) (by omega)]
  exact hzero

theorem pmcStoreReady_zero_store_then {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    {off : Nat} {valExp : ExpHOL 64} {w_val : BitVec 64} {tail : ProgHOL 64}
    (hsr : PmcStoreReady (fun _ _ st _ _ => memW st (w_out.toNat + 16) = 0)
      entry s w_out)
    (hoff8 : off % 8 = 0) (hoff_lt : off < 96) (hoff_ne : off ≠ 16)
    (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some (.val (.word w_val)))
    (htail : PmcStoreReady (fun _ _ st _ _ => memW st (w_out.toNat + 16) = 0) entry
      { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val } w_out →
      PmcRelRunStrong entry tail
        { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val }) :
    PmcRelRunStrong entry
      (.seq (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 off)]) valExp) tail) s := by
  obtain ⟨heval, hready⟩ := pmcStoreReady_zero_store hsr hoff8 hoff_lt hoff_ne hval
  unfold PmcRelRunStrong at htail ⊢
  rw [evaluateHOLFiniteState_seq_line780, heval]
  exact htail hready

theorem pmcStoreReady_zero_return {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (hsr : PmcStoreReady (fun _ _ st _ _ => memW st (w_out.toNat + 16) = 0)
      entry s w_out) :
    PmcRelRunStrong entry (.return (.var .local (ofString "out"))) s := by
  intro _
  refine pmcStoreReady_return hsr ?_
  intro S Nd _ hzero
  rw [hzero]
  exact ⟨Or.inl rfl, pmcLogsLiveOwned_zero s S Nd⟩

theorem pmcStoreReady_of_prefix {F : Type}
    {R1 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {Q2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {entry s : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (hen_WOK : WorldOK entry)
    (hR1_sub : ∀ j ∈ R1 entry, j ∈ bufRegions pmcBufs entry ∨
      Inside j (globN entry "heap_ptr") (globN s "heap_ptr"))
    (h12 : WorldStep R1 ["heap_ptr", "scratch_ptr"] pmcKeep
      (fun _ _ st S' Nd' => IvlsDisj [(w_out.toNat, 96)] (worldOwned st S' Nd')) entry none s)
    (hQ2 : ∀ S' Nd', Q2 entry none s S' Nd')
    (hs_out : s.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hw_out8 : w_out.toNat % 8 = 0)
    (hw_in : Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s "heap_ptr"))
    (hw_ok : WordsOK s (w_out.toNat, 96)) :
    PmcStoreReady Q2 entry s w_out := by
  refine ⟨hen_WOK, ?_, hs_out, hw_out8, hw_in, hw_ok⟩
  obtain ⟨hA2, hhp12, hG12, hK12, hW12⟩ := h12
  have hA1 : ArenaReady entry := hen_WOK.1
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, S_ok, hWT_ok0⟩ := hen_WOK
  obtain ⟨Nd_ok, hWT_ok⟩ := (worldTyped_iff_with entry S_ok).1 hWT_ok0
  have hrec_not_fresh : ∀ rec ∈ pmcKeep, globN entry rec.1 ≠ 0 → ∀ off ∈ rec.2,
      ∀ i : Ivl, Inside i (globN entry "heap_ptr") (globN s "heap_ptr") →
      ¬ CellHits (globN entry rec.1 + off) i := by
    intro rec hrec hnz off hoff i hi_fresh ⟨hc1, hc2⟩
    have ⟨sz, htr, hoff_lt⟩ : ∃ sz, (rec.1, sz) ∈ typedRecords ∧ off + 8 ≤ sz := by
      simp only [pmcKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by simp [typedRecords], ?_⟩; simp at hoff; omega
      · refine ⟨80, by simp [typedRecords], ?_⟩; simp at hoff; omega
      · refine ⟨72, by simp [typedRecords], ?_⟩; simp at hoff; omega
      · refine ⟨88, by simp [typedRecords], ?_⟩; simp at hoff; omega
    have hfix_mem := typedRecord_mem_fixedObjects entry htr
    simp only [hnz, ↓reduceIte] at hfix_mem
    rcases hWT_ok.2.2.1.1 (globN entry rec.1, sz) hfix_mem with hz | ⟨hal, _⟩
    · dsimp at hz; omega
    · rcases hal with ⟨_, hhi⟩ | ⟨hlo, _⟩
      · dsimp at hhi; unfold Inside at hi_fresh; omega
      · dsimp at hlo; unfold Inside at hi_fresh
        have := hA1.2.2.1; have := hA2.2.2.1; have := hA1.2.2.2.1; have := hA1.2.2.2.2.1
        omega
  refine ⟨hA2, hhp12, ?_, ?_, ?_⟩
  · intro k hk
    apply hG12 k
    intro hm
    apply hk
    simp only [List.mem_map, pmcGlobals] at hm ⊢
    obtain ⟨g, hg, rfl⟩ := hm
    refine ⟨g, ?_, rfl⟩
    simp at hg; rcases hg with rfl | rfl <;> simp
  · intro rec hrec hnz off hoff hno
    exact hK12 rec hrec hnz off hoff (fun i hi hch => by
      rcases hR1_sub i hi with hi_buf | hi_fresh
      · exact hno i (by change i ∈ pmcRegions entry; rw [pmcRegions_eq_bufRegions]; exact List.mem_cons_of_mem _ hi_buf) hch
      · exact hrec_not_fresh rec hrec hnz off hoff i hi_fresh hch)
  · intro S Nd hWT1 _ hD1
    have hD1_R1 : IvlsDisj (R1 entry) (worldTypedIvls entry S Nd) := by
      intro x hx j hj
      rcases hR1_sub x hx with hx_buf | hx_fresh
      · exact validBufList_disj validBufList_pmcBufs hWT1 x hx_buf j hj
      · rcases worldOwned_zero_or_allocated hWT1 j (worldTypedIvls_sub_worldOwned entry S Nd j hj) with
            rfl | ⟨_, hal_j⟩
        · exact disj_zero_right x
        · rcases hal_j with ⟨_, hhi_j⟩ | ⟨hlo_j, _⟩
          · exact Or.inr (Or.inr (Or.inr (Nat.le_trans hhi_j hx_fresh.1)))
          · exact Or.inr (Or.inr (Or.inl (by
              unfold Inside at hx_fresh
              have := hA1.2.2.1; have := hA2.2.2.1; have := hA1.2.2.2.1; have := hA1.2.2.2.2.1
              omega)))
    obtain ⟨S2, Nd2, hsub12, hWT2, hOG12, hFO12, hout_disj⟩ := hW12 S Nd hWT1 hD1_R1
    refine ⟨S2, Nd2, hsub12, hWT2, hOG12, ?_, hout_disj, hQ2 S2 Nd2⟩
    intro a ha hhf
    apply hFO12 a _ hhf
    intro i hi hch
    rcases List.mem_append.1 hi with hi1 | hfg1
    · rcases List.mem_append.1 hi1 with hwo1 | hR1
      · exact ha i (List.mem_append_left _ (List.mem_append_left _ hwo1)) hch
      · rcases hR1_sub i hR1 with hi_buf | hi_fresh
        · exact ha i (List.mem_append_left _ (List.mem_append_right _
            (by change i ∈ pmcRegions entry; rw [pmcRegions_eq_bufRegions]; exact List.mem_cons_of_mem _ hi_buf))) hch
        · obtain ⟨hc1, hc2⟩ := hch
          have hp2_lim : globN s "heap_ptr" ≤ heapLimit := hA2.2.2.1
          exact hhf ⟨by unfold heapFree; dsimp only [Inside] at hi_fresh ⊢; omega,
                     by unfold heapFree; dsimp only [Inside] at hi_fresh ⊢; omega⟩
    · exact ha i (List.mem_append_right _ hfg1) hch

theorem pmcDispatch_cut
    (hpm : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultStrong (ofString "process_message"))
    (hpcm : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultStrong (ofString "process_create_message")) :
    PmcRelCutStrong pmcDispatch PmcA1 PmcA2 := by
  intro F entry tail htail s hcode hp1
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
  unfold PmcRelRunStrong
  intro hres
  unfold pmcDispatch pmcCode at hres ⊢
  simp only [sourceFunctionEntry, Guest.Software.guestFn_process_message_call,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil,
    R13Shards.spineAt, R13Shards.spinePlug] at hres ⊢
  -- Evaluate outer ite condition: load .one (msg + 24) == 0
  have hload24 := pmc_load_local_off hs_msg_w hw_msg_ok_s hw_msg_hi_s (by decide) (show 24 < 176 by decide)
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres ⊢
  have hcond24_ex : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.load .one (.op .add [.var .local (ofString "msg"), .const 24#64])) (.const 0#64)) =
      some (.val (.word (if BitVec.ofNat 64 (memW s (w_msg.toNat + 24)) = 0#64 then 1#64 else 0#64))) := by
    have hl24' : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "msg"), .const 24#64])) =
        some (.val (.word (BitVec.ofNat 64 (memW s (w_msg.toNat + 24))))) := hload24
    unfold evalHOLExact
    rw [hl24']
    simp [evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcond24_ex] at hres ⊢
  dsimp only at hres ⊢
  by_cases h24_eq : BitVec.ofNat 64 (memW s (w_msg.toNat + 24)) = 0#64
  · -- Then branch: create message path
    rw [if_pos h24_eq, if_neg (show ¬ ((1#64 : BitVec 64) = 0) by decide)] at hres ⊢
    -- Evaluate decCall "dep" .one "account_deployable" [load .one (msg + 32)]
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hres ⊢
    have hload32 := pmc_load_local_off hs_msg_w hw_msg_ok_s hw_msg_hi_s (by decide) (show 32 < 176 by decide)
    have hargs_ad : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.load .one (.op .add [.var .local (ofString "msg"), .const 32#64])] =
        some [.val (.word (BitVec.ofNat 64 (memW s (w_msg.toNat + 32))))] := by
      rw [evalListHOLFinite_eq_toExact]
      change @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        [.load .one (.op .add [.var .local (ofString "msg"), .const (BitVec.ofNat 64 32)])] = _
      simp [evalListHOLExact, hload32]
    simp only [hargs_ad] at hres ⊢
    set v_ad := ValueHOL.val (.word (BitVec.ofNat 64 (memW s (w_msg.toNat + 32))))
    rcases hl_ad : lookupCodeHOLFinite s.code.lookup (ofString "account_deployable") [v_ad]
        with _ | ⟨body_ad, callee_ad, ret_ad⟩
    · simp only [hl_ad] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hl_ad] at hres ⊢
      by_cases hclk_ad : s.clock = 0
      · simp only [hclk_ad, ↓reduceIte] at hres
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      · simp only [hclk_ad, ↓reduceIte] at hres ⊢
        let ent_ad := callEntryStateHOLFinite s callee_ad
        have hmeta_ad := (evaluateHOLFiniteState_metadata ent_ad body_ad).1
        rcases hrun_ad : evaluateHOLFiniteState ent_ad body_ad with ⟨res_ad, post_ad⟩
        dsimp only [ent_ad] at hrun_ad hmeta_ad
        rw [hrun_ad] at hmeta_ad
        dsimp only at hmeta_ad
        simp only [hrun_ad] at hres ⊢
        have hnt_ad : (evaluateHOLFiniteState ent_ad body_ad).1 ≠ some .timeOut := by
          dsimp only [ent_ad]; rw [hrun_ad]
          rintro rfl
          exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        have hspec_ad := wkSc_account_deployable.at_lookup s hcode [v_ad] body_ad callee_ad ret_ad hl_ad
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
            dsimp only at hres ⊢
            have hws_ad_sc := WorldStepSc.mono_bufs hwsAcct_sub_pmc (fun _ h => h)
              (WorldStepSc.from_entry (s := s) (r' := some (.exception eid eval))
                (L := HolFiniteMapExact.empty) (k := post_ad.clock) (hspec_ad hres))
            have hws_ad_pmc : WorldStep (bufRegions pmcBufs) ["heap_ptr", "scratch_ptr"] pmcKeep
                NoExtra s (some (.exception eid eval)) (emptyLocalsHOLFinite post_ad) :=
              worldStep_pmcKeep_of_stdKeep (fun _ h => h) hws_ad_sc.1
            have hws_en_ex := worldStep_pmcPrefix_trans (w_out := w_out)
              hM0.1 hWOK_en hR1_sub
              (fun j hj => Or.inl hj)
              (fun _ _ h => h)
              (fun S2 Nd2 hWT2 _ => validBufList_disj validBufList_pmcBufs hWT2)
              hws_s hsp_s hws_ad_pmc
              (fun S2 Nd2 S3 Nd3 hWT2 hout2 hOG23 hFO23 _ => by
                have hout_in2 : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
                  ⟨le_trans hM0.1.2.1 hw_in_s.1, hw_in_s.2⟩
                have hout_disj_R2 : ∀ j ∈ bufRegions pmcBufs s, Disj (w_out.toNat, 96) j := by
                  intro j hj
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
                have hbuf_z : ∀ j ∈ bufRegions pmcBufs s, j.2 = 0 → j.1 % 8 = 0 := by
                  intro j hj hz
                  obtain ⟨S_en, Nd_en, hMA_en⟩ := R10Shards.Fast_GbodyC17ToC21.msgReadyAt_of_msgReady hM0
                  have hm8_s : locN s "msg" % 8 = 0 := by
                    have : locN s "msg" = locN entry "msg" := by simp [locN, hs_msg]
                    rw [this]; exact hMA_en.2.2.2.2.2.2.2.2.2.1
                  exact pmcRegions_zero_aligned hm8_s j
                    (by rw [pmcRegions_eq_bufRegions]; exact List.mem_cons_of_mem _ hj) hz
                obtain ⟨_, hout_ow3, _⟩ :=
                  heap_ivl_survives_step (b := (w_out.toNat, 96))
                    hM_s.1.2 hws_ad_pmc.2.1 hOG23 hFO23
                    (worldOwned_zero_aligned hWT2) hbuf_z hw_out8 (by dsimp) hout_in2
                    (fun j hj => hout2 (w_out.toNat, 96) (by simp) j hj) hout_disj_R2
                intro x hx j hj; simp at hx; subst hx; exact hout_ow3 j hj)
            have hws_en_ex_no : WorldStep
                (fun st => bufRegions pmcBufs st ++ [(globN entry "heap_ptr", globN (emptyLocalsHOLFinite post_ad) "heap_ptr" - globN entry "heap_ptr")])
                ["heap_ptr", "scratch_ptr"] pmcKeep NoExtra entry (some (.exception eid eval)) (emptyLocalsHOLFinite post_ad) := by
              obtain ⟨a1, a2, a3, a4, a5⟩ := hws_en_ex
              refine ⟨a1, a2, a3, a4, fun S_x Nd_x hW_x hD_x => ?_⟩
              obtain ⟨S', Nd', hs, hw', hog, hfo, _⟩ := a5 S_x Nd_x hW_x hD_x
              exact ⟨S', Nd', hs, hw', hog, hfo, trivial⟩
            exact worldStepIn_pmc_of_prefix_not_returned
              (fun S' Nd' => pmc_resumes_not_returned_vac (fun _ hv => by cases hv))
              hM0.1 hWOK_en
              (fun j hj => by
                rcases List.mem_append.1 hj with hj_buf | hj_fr
                · exact Or.inl hj_buf
                · simp only [List.mem_singleton] at hj_fr; subst hj_fr
                  exact Or.inr ⟨le_rfl, by have := hws_en_ex_no.2.1; omega⟩)
              hws_en_ex_no
          | returned val_ad =>
            dsimp only at hres ⊢
            have hret_ad_eq : ret_ad = .one :=
              lookupCodeHOLFinite_installed_return s (ofString "account_deployable") _ _ body_ad .one ret_ad
                [v_ad] callee_ad (by rw [hcode]; exact lookup_account_deployable) hl_ad
            subst hret_ad_eq
            by_cases hsh_ad : (shapeEqHOL (shapeOfHOLExact val_ad) .one &&
                shapeEqHOL (shapeOfHOLExact val_ad) .one) = true
            · simp only [hsh_ad, ↓reduceIte] at hres ⊢
              have hsh1_ad : shapeEqHOL (shapeOfHOLExact val_ad) .one = true :=
                ((Bool.and_eq_true _ _).mp hsh_ad).1
              obtain ⟨w_dep, rfl⟩ : ∃ w : BitVec 64, val_ad = .val (.word w) := by
                rcases val_ad with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
                · exact ⟨w, rfl⟩
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh1_ad
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh1_ad
              set s_dep := setVarHOLFinite (ofString "dep") (.val (.word w_dep)) { post_ad with locals := s.locals }
              have hws_ad_raw := hspec_ad (Or.inl ⟨.val (.word w_dep), rfl⟩)
              have hws_ad_caller : WorldStepSc (bufRegions wsAcctBufs) ["heap_ptr", "scratch_ptr"] stdKeep
                  NoExtra s (some (.returned (.val (.word w_dep)))) post_ad :=
                WorldStepSc.of_pre_locals_clock hws_ad_raw
              have hws_ad_s_dep_sc : WorldStepSc (bufRegions pmcBufs) ["heap_ptr", "scratch_ptr"] stdKeep
                  NoExtra s none s_dep :=
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
              -- Preserve MsgReadyAt across account_deployable
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
                obtain ⟨sz, hgb, hnr, hle⟩ := validBufList_wsAcctBufs p hp
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
              obtain ⟨S0_dep, Nd_dep, hMA_dep_pre, _, hfp_ad⟩ :=
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
              -- Survive w_out across s -> s_dep at EVERY WorldTypedWith witness and at (S_s, Nd_s)
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
                  ["heap_ptr", "scratch_ptr"] stdKeep
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
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres ⊢
              have hcond_dep_ex : @evalHOLExact 64 F _ s_dep.toExact (fun a => Classical.propDecidable (s_dep.memaddrs a))
                  (.cmp .equal (.var .local (ofString "dep")) (.const 0#64)) =
                  some (.val (.word (if w_dep = 0#64 then 1#64 else 0#64))) := by
                simp [evalHOLExact, hs_dep_dep, Compiler.Encoders.Asm.wordCmpHOL]
              rw [hcond_dep_ex] at hres ⊢
              dsimp only at hres ⊢
              by_cases hdep0 : w_dep = 0#64
              · -- Early return: dep == 0!
                rw [if_pos hdep0, if_neg (show ¬ ((1#64 : BitVec 64) = 0) by decide)] at hres ⊢
                -- Notice: the 4 stores + return ALWAYS produce `some (.returned ...)` (not `none`), so the outer `.seq`s never enter `process_create_message` or `tail`!
                -- Let's promote `hws_en_dep` to `PmcStoreReady`!
                have hsr0 : PmcStoreReady (fun _ _ st _ _ => memW st (w_out.toNat + 16) = 0) entry s_dep w_out :=
                  pmcStoreReady_of_prefix hWOK_en
                    (fun j hj => by
                      rcases List.mem_append.1 hj with hj_buf | hj_fr
                      · exact Or.inl hj_buf
                      · simp only [List.mem_singleton] at hj_fr; subst hj_fr
                        exact Or.inr ⟨le_rfl, by have := hws_en_dep.2.1; omega⟩)
                    hws_en_dep (fun _ _ => hmem16_dep) hs_dep_out hw_out8 hw_in_dep hw_ok_dep
                -- Also get `w_msg` facts in `s_dep` (and preserved across updates to `w_out` since `msg` is `< entry.hp ≤ w_out`!):
                have hs_dep_msg_w : s_dep.locals.lookup (ofString "msg") = some (.val (.word w_msg)) := by
                  rw [hs_dep_msg, ← hs_msg]; exact hs_msg_w
                obtain ⟨_, _, _, _, hm_in_dep, hm_ok_dep, _, _, _, _, _⟩ := hM_dep.2
                have hm_loc_dep : locN s_dep "msg" = w_msg.toNat := by simp [locN, hs_dep_msg_w]
                have hw_msg_ok_dep : WordsOK s_dep (w_msg.toNat, 176) := by rwa [← hm_loc_dep]
                have hw_msg_in_en : w_msg.toNat + 176 ≤ w_out.toNat := by
                  obtain ⟨_, _, hMA_en⟩ := R10Shards.Fast_GbodyC17ToC21.msgReadyAt_of_msgReady hM0
                  have hm_loc_en : locN entry "msg" = w_msg.toNat := by
                    rw [← hm_loc_dep]; simp [locN, hs_dep_msg]
                  have := hMA_en.2.2.2.2.2.2.2.2.2.2.1.2
                  rw [hm_loc_en] at this
                  exact le_trans this hw_in_dep.1
                -- Global `evm_empty` in `s_dep` via `GlobalsWord s_dep` (`hM_dep.1.2.2.2.2.2.2.2.2.2`):
                obtain ⟨w_emp, hw_emp⟩ := hM_dep.1.2.2.2.2.2.2.2.2.2 "evm_empty" (by decide)
                -- Store 1: out + 32 := 12
                obtain ⟨hev1, hsr1⟩ := pmcStoreReady_zero_store (off := 32) (valExp := .const 12#64) (w_val := 12#64)
                  hsr0 (by decide) (by decide) (by decide) rfl
                set st1 := { s_dep with memory := pmcUpdW s_dep.memory (BitVec.ofNat 64 (w_out.toNat + 32)) 12#64 }
                -- Store 2: out + 56 := load .one (msg + 48)
                have hmsg_ok1 : WordsOK st1 (w_msg.toNat, 176) := pmc_wordsOK_updW s_dep _ _ _ hw_msg_ok_dep
                have hload48_1 := pmc_load_local_off (s := st1) hs_dep_msg_w hmsg_ok1 hw_msg_hi_s (by decide) (show 48 < 176 by decide)
                obtain ⟨hev2, hsr2⟩ := pmcStoreReady_zero_store (off := 56)
                  (valExp := .load .one (.op .add [.var .local (ofString "msg"), .const 48#64]))
                  hsr1 (by decide) (by decide) (by decide) hload48_1
                set st2 := { st1 with memory := pmcUpdW st1.memory (BitVec.ofNat 64 (w_out.toNat + 56)) (BitVec.ofNat 64 (memW st1 (w_msg.toNat + 48))) }
                -- Store 3: out + 64 := load .one (msg + 40)
                have hmsg_ok2 : WordsOK st2 (w_msg.toNat, 176) := pmc_wordsOK_updW st1 _ _ _ hmsg_ok1
                have hload40_2 := pmc_load_local_off (s := st2) hs_dep_msg_w hmsg_ok2 hw_msg_hi_s (by decide) (show 40 < 176 by decide)
                obtain ⟨hev3, hsr3⟩ := pmcStoreReady_zero_store (off := 64)
                  (valExp := .load .one (.op .add [.var .local (ofString "msg"), .const 40#64]))
                  hsr2 (by decide) (by decide) (by decide) hload40_2
                set st3 := { st2 with memory := pmcUpdW st2.memory (BitVec.ofNat 64 (w_out.toNat + 64)) (BitVec.ofNat 64 (memW st2 (w_msg.toNat + 40))) }
                -- Store 4: out + 40 := global evm_empty
                have hemp_3 : @evalHOLExact 64 F _ st3.toExact (fun a => Classical.propDecidable (st3.memaddrs a))
                    (.var .global (ofString "evm_empty")) = some (.val (.word w_emp)) := by
                  simp [evalHOLExact, st3, st2, st1]
                  exact hw_emp
                obtain ⟨hev4, hsr4⟩ := pmcStoreReady_zero_store (off := 40)
                  (valExp := .var .global (ofString "evm_empty"))
                  hsr3 (by decide) (by decide) (by decide) hemp_3
                set st4 := { st3 with memory := pmcUpdW st3.memory (BitVec.ofNat 64 (w_out.toNat + 40)) w_emp }
                -- Evaluate the sequence of 4 stores + return inside the two outer `.seq`s + `decCall` local restoration!
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
                rw [hblk_ev] at hres ⊢
                dsimp only at hres ⊢
                have hrun4 := pmcStoreReady_zero_return hsr4
                unfold PmcRelRunStrong at hrun4
                rw [hret_ev] at hrun4
                exact worldStepIn_pmc_with_locals_clock
                  (hrun4 (Or.inl ⟨.val (.word w_out), rfl⟩)) _ (emptyLocalsHOLFinite st4).clock
              · -- dep != 0: skip, then call frame := process_create_message [msg], then tail!
                rw [if_neg hdep0, if_pos (show (0#64 : BitVec 64) = 0 by decide)] at hres ⊢
                rw [evaluateHOLFiniteState_skip] at hres ⊢
                dsimp only at hres ⊢
                have hcall_pcm := pmc_call_frame_callee
                  (restL := fun m => HolFiniteMapExact.resVarEq m (ofString "dep", s.locals.lookup (ofString "dep")))
                  hpcm
                  ⟨_, _, R10Shards.Fast_GbodyC17ToC21.lookup_process_create_message⟩
                  (fun m => by rw [PanRunBounded.resVarEq_lookup, if_neg (by decide)])
                  (fun m => by rw [PanRunBounded.resVarEq_lookup, if_neg (by decide)])
                  htail hs_dep_code hM0 hM_dep hs_dep_msg hsp_dep hws_en_dep hs_dep_out hs_dep_fr
                  hw_out8 hw_in_dep hw_ok_dep hmem16_dep ⟨_, _, hMA_dep2, hout_ow_dep_at⟩
                dsimp only at hcall_pcm hres ⊢
                rcases hrun_pcm : evaluateHOLFiniteState s_dep
                    (.call (some ((some (.local, ofString "frame")), none))
                      (ofString "process_create_message") [.var .local (ofString "msg")]) with ⟨res_pcm, post_pcm⟩
                simp only [hrun_pcm] at hcall_pcm hres ⊢
                cases res_pcm with
                | none => exact hcall_pcm hres
                | some v => exact hcall_pcm hres
            · simp only [hsh_ad, Bool.false_eq_true, ↓reduceIte] at hres
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · -- Else branch: msg + 24 != 0 -> call frame := process_message [msg]; tail
    rw [if_neg h24_eq, if_pos (show (0#64 : BitVec 64) = 0 by decide)] at hres ⊢
    have hcall_pm := pmc_call_frame_callee (restL := fun m => m) hpm
      ⟨_, _, R10Shards.Fast_GbodyC17ToC21.lookup_process_message⟩
      (fun _ => rfl) (fun _ => rfl)
      htail hcode hM0 hM_s hs_msg hsp_s hws_s hs_out hs_fr
      hw_out8 hw_in_s hw_ok_s hmem16_s ⟨S_s, Nd_s, hMAs, hout_ow_s⟩
    dsimp only at hcall_pm hres ⊢
    rcases hrun_pm : evaluateHOLFiniteState s
        (.call (some ((some (.local, ofString "frame")), none))
          (ofString "process_message") [.var .local (ofString "msg")]) with ⟨res_pm, post_pm⟩
    simp only [hrun_pm] at hcall_pm hres ⊢
    have hpost_id : ({ post_pm with locals := post_pm.locals } : PanSemStateFiniteExact 64 F) = post_pm := by
      cases post_pm; rfl
    cases res_pm with
    | none =>
      simp only [hpost_id] at hcall_pm
      exact hcall_pm hres
    | some v =>
      simp only [hpost_id] at hcall_pm
      exact hcall_pm hres

theorem pmc_frame_memW_store_out {F : Type}
    {s : PanSemStateFiniteExact 64 F} {w_out w_fr w_val : BitVec 64}
    {off k : Nat}
    (hA : ArenaOK s)
    (hout : w_out.toNat + 96 ≤ globN s "heap_ptr")
    (hfr : Inside (w_fr.toNat, 280) (globN s "scratch_ptr") scratchEnd)
    (hoff : off < 96) (hk : k < 280) :
    memW { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val }
      (w_fr.toNat + k) = memW s (w_fr.toNat + k) := by
  have hhp : globN s "heap_ptr" ≤ heapLimit := hA.2.1
  have hsp : scratchStart ≤ globN s "scratch_ptr" := le_trans hA.2.2.1 hA.2.2.2.1
  have hsep : heapLimit ≤ scratchStart := by decide
  have hend : scratchEnd ≤ 2 ^ 64 := by decide
  obtain ⟨hlo, hhi⟩ := hfr
  apply pmc_memW_updW_ne
  · omega
  · omega
  · omega

def PmcPackState {F : Type}
    (entry s : PanSemStateFiniteExact 64 F)
    (w_out w_fr : BitVec 64) (logs : Nat) (zero16 : Bool) : Prop :=
  MsgReady entry ∧
  PmcStoreReady
    (fun _ _ st S' Nd' => PmcLogsLiveOwned st S' Nd' logs)
    entry s w_out ∧
  s.locals.lookup (ofString "frame") = some (.val (.word w_fr)) ∧
  WordsOK s (w_fr.toNat, 280) ∧
  Inside (w_fr.toNat, 280) (globN s "scratch_ptr") scratchEnd ∧
  LogsListOK s logs ∧
  (logs ≠ 0 →
    Disj (logs, 24) (w_out.toNat, 96) ∧
    Disj (memW s logs, 8 * memW s (logs + 8)) (w_out.toNat, 96) ∧
    ∀ i, i < memW s (logs + 8) →
      Disj (memW s (memW s logs + 8 * i), 40) (w_out.toNat, 96)) ∧
  logs = memW s (w_fr.toNat + 88) ∧
  (zero16 = true → memW s (w_out.toNat + 16) = 0) ∧
  (zero16 = false → memW s (w_out.toNat + 16) = logs)

theorem pmcPackState_of_a2 {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64}
    (hM0 : MsgReady entry)
    (hstep : WorldStepIn pmcTables pmcRegions pmcGlobals pmcKeep
      (fun _ _ post S Nd =>
        IvlsDisj [(w_out.toNat, 96)] (worldOwned post S Nd) ∧
        PmcLogsLiveOwned post S Nd (memW post (w_fr.toNat + 88)))
      entry none s)
    (hs_out : s.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hs_fr : s.locals.lookup (ofString "frame") = some (.val (.word w_fr)))
    (hw_out8 : w_out.toNat % 8 = 0)
    (hw_in : Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s "heap_ptr"))
    (hw_ok : WordsOK s (w_out.toNat, 96))
    (hz16 : memW s (w_out.toNat + 16) = 0)
    (hw_fr_ok : WordsOK s (w_fr.toNat, 280))
    (hfr_in : Inside (w_fr.toNat, 280) (globN s "scratch_ptr") scratchEnd)
    (hlok : LogsListOK s (memW s (w_fr.toNat + 88)))
    (hdisj : memW s (w_fr.toNat + 88) ≠ 0 →
      Disj (memW s (w_fr.toNat + 88), 24) (w_out.toNat, 96) ∧
      Disj (memW s (memW s (w_fr.toNat + 88)), 8 * memW s (memW s (w_fr.toNat + 88) + 8)) (w_out.toNat, 96) ∧
      ∀ i, i < memW s (memW s (w_fr.toNat + 88) + 8) →
        Disj (memW s (memW s (memW s (w_fr.toNat + 88)) + 8 * i), 40) (w_out.toNat, 96)) :
    PmcPackState entry s w_out w_fr (memW s (w_fr.toNat + 88)) true :=
  ⟨hM0, ⟨msgReady_worldOK entry hM0, hstep, hs_out, hw_out8, hw_in, hw_ok⟩,
    hs_fr, hw_fr_ok, hfr_in, hlok, hdisj, rfl, fun _ => hz16, fun h => Bool.noConfusion h⟩

theorem pmcPackState_store {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64} {logs off : Nat} {z : Bool}
    {valExp : ExpHOL 64} {w_val : BitVec 64}
    (hps : PmcPackState entry s w_out w_fr logs z)
    (hoff8 : off % 8 = 0) (hoff_lt : off < 96) (hoff_ne16 : off ≠ 16)
    (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some (.val (.word w_val))) :
    evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 off)]) valExp) =
      (none, { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val }) ∧
    PmcPackState entry
      { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val }
      w_out w_fr logs z := by
  obtain ⟨hM0, hsr, hs_fr, hw_fr_ok, hfr_in, hlok, hdisj, hlogs_eq, hz_t, hz_f⟩ := hps
  have hAs : ArenaOK s := hsr.2.1.1.2
  have hgS : GuestInv s := hsr.2.1.1.1
  have hw_in_sb : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
    ⟨le_trans hsr.1.1.2.1 hsr.2.2.2.2.1.1, hsr.2.2.2.2.1.2⟩
  have hw_hi : w_out.toNat + 96 ≤ 2 ^ 64 :=
    (ivl_allocated_bound hAs (Or.inl hw_in_sb)).2
  obtain ⟨hev, hsr'⟩ := pmcStoreReady_store
    (Q2 := fun _ _ st S' Nd' => PmcLogsLiveOwned st S' Nd' logs)
    hsr hoff8 hoff_lt hval
    (fun S' Nd' _ _ howned_eq _ hlive =>
      (pmc_logs_preserve_store_out hAs hgS hw_hi hoff8 hoff_lt hlok hlive hdisj howned_eq).2.1)
  obtain ⟨S_en, Nd_en, hMA_en⟩ := R10Shards.Fast_GbodyC17ToC21.msgReadyAt_of_msgReady hM0
  have hT_en : ∀ t ∈ pmcTables entry, t ∈ S_en := by
    intro t ht; simp [pmcTables] at ht
    rcases ht with rfl | rfl
    · exact hMA_en.2.2.1
    · exact hMA_en.2.2.2.1
  have hD_en : IvlsDisj (pmcRegions entry) (worldTypedIvls entry S_en Nd_en) := by
    rw [pmcRegions_eq_bufRegions]
    intro x hx j hj
    rcases List.mem_cons.1 hx with rfl | hx_buf
    · exact hMA_en.2.2.2.2.2.2.2.2.2.2.2.1 j (worldTypedIvls_sub_worldOwned entry S_en Nd_en j hj)
    · exact validBufList_disj validBufList_pmcBufs hMA_en.2.1 x hx_buf j hj
  obtain ⟨S_p, Nd_p, _, hWT_p, _, _, hout_ow_p, hlive_p⟩ := hsr.2.1.2.2.2.2 S_en Nd_en hMA_en.2.1 hT_en hD_en
  have hx_lt : w_out.toNat + off < 2 ^ 64 := by omega
  obtain ⟨_, hdom, _⟩ := hsr.2.2.2.2.2.2.2 (off / 8) (by dsimp only at *; omega)
  have hk_eq : w_out.toNat + 8 * (off / 8) = w_out.toNat + off := by omega
  rw [hk_eq] at hdom
  have hx_in : w_out.toNat ≤ (BitVec.ofNat 64 (w_out.toNat + off)).toNat ∧
      (BitVec.ofNat 64 (w_out.toNat + off)).toNat + 8 ≤ w_out.toNat + 96 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx_lt]; omega
  obtain ⟨_, _, howned_eq, _, _, _⟩ :=
    worldTypedWith_store_word_disj
      (post := { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val })
      hsr.2.1.1 hdom
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun a hne => by unfold pmcUpdW; exact if_neg hne⟩
      hWT_p
      (fun j hj => disj_of_inside_right (j' := (w_out.toNat, 96)) ⟨hx_in.1, hx_in.2⟩
        (hout_ow_p (w_out.toNat, 96) (by simp) j (worldTypedIvls_sub_worldOwned s S_p Nd_p j hj)).flip)
  obtain ⟨hlok', _, hdisj'⟩ :=
    pmc_logs_preserve_store_out hAs hgS hw_hi hoff8 hoff_lt hlok hlive_p hdisj howned_eq
  have hfr88 : memW { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val }
      (w_fr.toNat + 88) = memW s (w_fr.toNat + 88) :=
    pmc_frame_memW_store_out hAs hsr.2.2.2.2.1.2 hfr_in hoff_lt (by decide)
  have hout16 : memW { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val }
      (w_out.toNat + 16) = memW s (w_out.toNat + 16) :=
    pmc_memW_updW_ne s (w_out.toNat + off) (w_out.toNat + 16) w_val hx_lt (by omega) (by omega)
  exact ⟨hev, hM0, hsr', hs_fr, pmc_wordsOK_updW s _ _ _ hw_fr_ok, hfr_in, hlok', hdisj',
    hlogs_eq.trans hfr88.symm,
    fun hz => hout16.trans (hz_t hz), fun hz => hout16.trans (hz_f hz)⟩

theorem pmcPackState_store16_logs {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64} {logs : Nat} {z : Bool} {tail : ProgHOL 64}
    (hps : PmcPackState entry s w_out w_fr logs z)
    (htail : let w_v := BitVec.ofNat 64 (memW s (w_fr.toNat + 88))
      PmcPackState entry
        { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + 16)) w_v }
        w_out w_fr logs false →
      PmcRelRunStrong entry tail
        { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + 16)) w_v }) :
    PmcRelRunStrong entry
      (.seq (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 16)])
                    (.load .one (.op .add [.var .local (ofString "frame"), .const (BitVec.ofNat 64 88)])))
            tail) s := by
  obtain ⟨hM0, hsr, hs_fr, hw_fr_ok, hfr_in, hlok, hdisj, hlogs_eq, _, _⟩ := hps
  set w_v := BitVec.ofNat 64 (memW s (w_fr.toNat + 88))
  set a16 := BitVec.ofNat 64 (w_out.toNat + 16)
  have hfr_hi : w_fr.toNat + 280 ≤ 2 ^ 64 := by
    have h1 : w_fr.toNat + 280 ≤ scratchEnd := hfr_in.2
    have h2 : scratchEnd ≤ 2 ^ 64 := by decide
    omega
  have hload := pmc_load_local_off hs_fr hw_fr_ok hfr_hi (by decide) (show 88 < 280 by decide)
  have hAs : ArenaOK s := hsr.2.1.1.2
  have hgS : GuestInv s := hsr.2.1.1.1
  have hw_in_sb : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
    ⟨le_trans hsr.1.1.2.1 hsr.2.2.2.2.1.1, hsr.2.2.2.2.1.2⟩
  have hw_hi : w_out.toNat + 96 ≤ 2 ^ 64 :=
    (ivl_allocated_bound hAs (Or.inl hw_in_sb)).2
  obtain ⟨hev, hsr'⟩ := pmcStoreReady_store
    (Q2 := fun _ _ st S' Nd' => PmcLogsLiveOwned st S' Nd' logs)
    hsr (off := 16) (by decide) (by decide) hload
    (fun S' Nd' _ _ howned_eq _ hlive =>
      (pmc_logs_preserve_store_out hAs hgS hw_hi (by decide) (by decide) hlok hlive hdisj howned_eq).2.1)
  obtain ⟨S_en, Nd_en, hMA_en⟩ := R10Shards.Fast_GbodyC17ToC21.msgReadyAt_of_msgReady hM0
  have hT_en : ∀ t ∈ pmcTables entry, t ∈ S_en := by
    intro t ht; simp [pmcTables] at ht
    rcases ht with rfl | rfl
    · exact hMA_en.2.2.1
    · exact hMA_en.2.2.2.1
  have hD_en : IvlsDisj (pmcRegions entry) (worldTypedIvls entry S_en Nd_en) := by
    rw [pmcRegions_eq_bufRegions]
    intro x hx j hj
    rcases List.mem_cons.1 hx with rfl | hx_buf
    · exact hMA_en.2.2.2.2.2.2.2.2.2.2.2.1 j (worldTypedIvls_sub_worldOwned entry S_en Nd_en j hj)
    · exact validBufList_disj validBufList_pmcBufs hMA_en.2.1 x hx_buf j hj
  obtain ⟨S_p, Nd_p, _, hWT_p, _, _, hout_ow_p, hlive_p⟩ := hsr.2.1.2.2.2.2 S_en Nd_en hMA_en.2.1 hT_en hD_en
  have hx_lt : w_out.toNat + 16 < 2 ^ 64 := by omega
  obtain ⟨_, hdom, _⟩ := hsr.2.2.2.2.2.2.2 2 (by dsimp only at *; omega)
  have hk_eq : w_out.toNat + 8 * 2 = w_out.toNat + 16 := by omega
  rw [hk_eq] at hdom
  have hx_in : w_out.toNat ≤ a16.toNat ∧ a16.toNat + 8 ≤ w_out.toNat + 96 := by
    dsimp only [a16]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx_lt]; omega
  obtain ⟨_, _, howned_eq, _, _, _⟩ :=
    worldTypedWith_store_word_disj
      (post := { s with memory := pmcUpdW s.memory a16 w_v })
      hsr.2.1.1 hdom
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun a hne => by unfold pmcUpdW; exact if_neg hne⟩
      hWT_p
      (fun j hj => disj_of_inside_right (j' := (w_out.toNat, 96)) ⟨hx_in.1, hx_in.2⟩
        (hout_ow_p (w_out.toNat, 96) (by simp) j (worldTypedIvls_sub_worldOwned s S_p Nd_p j hj)).flip)
  obtain ⟨hlok', _, hdisj'⟩ :=
    pmc_logs_preserve_store_out hAs hgS hw_hi (by decide) (by decide) hlok hlive_p hdisj howned_eq
  have hfr88 : memW { s with memory := pmcUpdW s.memory a16 w_v }
      (w_fr.toNat + 88) = memW s (w_fr.toNat + 88) :=
    pmc_frame_memW_store_out hAs hsr.2.2.2.2.1.2 hfr_in (by decide) (by decide)
  have hlogs_lt : memW s (w_fr.toNat + 88) < 2 ^ 64 := by
    unfold memW; cases s.memory (BitVec.ofNat 64 (w_fr.toNat + 88)) with
    | word w => exact w.isLt
  have hout16 : memW { s with memory := pmcUpdW s.memory a16 w_v } (w_out.toNat + 16) = logs := by
    dsimp only [a16, w_v]
    rw [pmc_memW_updW_same s (w_out.toNat + 16) _,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlogs_lt, ← hlogs_eq]
  unfold PmcRelRunStrong at htail ⊢
  rw [evaluateHOLFiniteState_seq_line780, hev]
  exact htail ⟨hM0, hsr', hs_fr, pmc_wordsOK_updW s _ _ _ hw_fr_ok, hfr_in, hlok', hdisj',
    hlogs_eq.trans hfr88.symm, fun h => Bool.noConfusion h, fun _ => hout16⟩

theorem pmcPackState_store_frame_then {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64} {logs off_out off_fr : Nat} {z : Bool} {tail : ProgHOL 64}
    (hps : PmcPackState entry s w_out w_fr logs z)
    (hoff_out8 : off_out % 8 = 0) (hoff_out_lt : off_out < 96) (hoff_ne16 : off_out ≠ 16)
    (hoff_fr8 : off_fr % 8 = 0) (hoff_fr_lt : off_fr < 280)
    (htail : let w_v := BitVec.ofNat 64 (memW s (w_fr.toNat + off_fr))
      PmcPackState entry
        { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off_out)) w_v }
        w_out w_fr logs z →
      PmcRelRunStrong entry tail
        { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off_out)) w_v }) :
    PmcRelRunStrong entry
      (.seq (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 off_out)])
                    (.load .one (.op .add [.var .local (ofString "frame"), .const (BitVec.ofNat 64 off_fr)])))
            tail) s := by
  have hfr_hi : w_fr.toNat + 280 ≤ 2 ^ 64 := by
    have h1 : w_fr.toNat + 280 ≤ scratchEnd := hps.2.2.2.2.1.2
    have h2 : scratchEnd ≤ 2 ^ 64 := by decide
    omega
  have hload := pmc_load_local_off hps.2.2.1 hps.2.2.2.1 hfr_hi hoff_fr8 hoff_fr_lt
  obtain ⟨hev, hps'⟩ := pmcPackState_store hps hoff_out8 hoff_out_lt hoff_ne16 hload
  unfold PmcRelRunStrong at htail ⊢
  rw [evaluateHOLFiniteState_seq_line780, hev]
  exact htail hps'

theorem pmcPackState_with_locals_clock {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64} {logs : Nat} {z : Bool}
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hL_out : L.lookup (ofString "out") = some (.val (.word w_out)))
    (hL_fr : L.lookup (ofString "frame") = some (.val (.word w_fr)))
    (hps : PmcPackState entry s w_out w_fr logs z) :
    PmcPackState entry { s with locals := L, clock := k } w_out w_fr logs z := by
  obtain ⟨hM0, ⟨hen_WOK, hstep, _, hw_out8, hw_in, hw_ok⟩, _, hw_fr_ok, hfr_in,
    hlok, hdisj, hlogs_eq, hz_t, hz_f⟩ := hps
  have hAs : ArenaOK s := hstep.1.2
  have hAp' := localsFree_arenaReady s L k hstep.1
  have hstep' : WorldStepIn pmcTables pmcRegions pmcGlobals pmcKeep
      (fun _ _ st S' Nd' =>
        IvlsDisj [(w_out.toNat, 96)] (worldOwned st S' Nd') ∧ PmcLogsLiveOwned st S' Nd' logs)
      entry none { s with locals := L, clock := k } := by
    obtain ⟨_, hhp, hG, hK, hW⟩ := hstep
    refine ⟨hAp', hhp, hG, hK, fun S Nd hWT hTS hD => ?_⟩
    obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hout_d, hlive⟩ := hW S Nd hWT hTS hD
    refine ⟨S', Nd', hsub,
      (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals s L k S' Nd').2 hWT',
      hOG, hFO, hout_d,
      pmcLogsLiveOwned_congr_live hAs hlok hlive rfl rfl (fun a => a)
        (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)⟩
  have hlok' := pmc_logsListOK_congr_live hAs hstep.1.1 hAp'.1 le_rfl hlok (fun a => a)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)
  exact ⟨hM0, ⟨hen_WOK, hstep', hL_out, hw_out8, hw_in, hw_ok⟩,
    hL_fr, hw_fr_ok, hfr_in, hlok', hdisj, hlogs_eq, hz_t, hz_f⟩

theorem pmcPackState_return {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64} {logs : Nat} {z : Bool}
    (hps : PmcPackState entry s w_out w_fr logs z) :
    PmcRelRunStrong entry (.return (.var .local (ofString "out"))) s := by
  intro _
  obtain ⟨_, hsr, _, _, _, hlok, _, _, hz_t, hz_f⟩ := hps
  refine pmcStoreReady_return hsr ?_
  intro S' Nd' _ hlive
  cases z
  · rw [hz_f rfl]; exact ⟨hlok, hlive⟩
  · rw [hz_t rfl]; exact ⟨Or.inl rfl, pmcLogsLiveOwned_zero s S' Nd'⟩

theorem pmcPackState_not_returned {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64} {logs : Nat} {z : Bool}
    {r : Option (PanSemResultExact 64)}
    (hnr : ∀ v, r ≠ some (.returned v))
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hps : PmcPackState entry s w_out w_fr logs z) :
    WorldStepIn pmcTables pmcRegions pmcGlobals pmcKeep RetMessageOutputStrong entry r
      { s with locals := L, clock := k } := by
  obtain ⟨_, ⟨_, hstep, _, _, _, _⟩, _, _, _, _, _, _, _, _⟩ := hps
  obtain ⟨hAs, hhp, hG, hK, hW⟩ := hstep
  refine ⟨localsFree_arenaReady s L k hAs, hhp, hG, hK, fun S Nd hWT hTS hD => ?_⟩
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, _⟩ := hW S Nd hWT hTS hD
  exact ⟨S', Nd', hsub,
    (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals s L k S' Nd').2 hWT',
    hOG, hFO, pmc_resumes_not_returned_vac hnr⟩

theorem pmcPackState_decCall_ro_then {F : Type}
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
    (hcont : ∀ (w_res : BitVec 64) (s_next : PanSemStateFiniteExact 64 F),
      s_next.code = originalRuntimeCode →
      s_next.locals.lookup name = some (.val (.word w_res)) →
      PmcPackState entry s_next w_out w_fr logs z →
      PmcRelRunStrong entry cont s_next) :
    PmcRelRunStrong entry (.decCall name .one fname args cont) s := by
  unfold PmcRelRunStrong
  intro hres
  obtain ⟨params, body, ret, hlook, hspec⟩ := hro
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs] at hres ⊢
  dsimp only at hres ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
  · simp only [hl] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [hl] at hres ⊢
    by_cases hz : s.clock = 0
    · simp only [hz, ↓reduceIte] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hz, ↓reduceIte] at hres ⊢
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
      simp only [hrun] at hres ⊢
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
          dsimp only at hres ⊢
          have hro_eq := hspec (callEntryStateHOLFinite s callee) hcode
            (guestInv_callEntry s callee hG) hex (by rw [hrun]; simp) (by rw [hrun]; exact hres)
          rw [hrun] at hro_eq; dsimp only at hro_eq
          have hpost_eq : emptyLocalsHOLFinite post =
              { s with locals := HolFiniteMapExact.empty, clock := post.clock } := by
            have := R13.state_trans_locals_clock hentryEq hro_eq
            exact R13.state_eq_with_locals_clock this _ post.clock
          rw [hpost_eq]
          exact pmcPackState_not_returned (by intro _ h; cases h) _ post.clock hps
        | returned val =>
          dsimp only at hres ⊢
          by_cases hsh : (shapeEqHOL (shapeOfHOLExact val) .one &&
              shapeEqHOL (shapeOfHOLExact val) ret') = true
          · simp only [hsh, ↓reduceIte] at hres ⊢
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
            have hcont_run := hcont w_res s_next hs_next_code hs_next_name hps_next
            unfold PmcRelRunStrong at hcont_run
            rcases hc_run : evaluateHOLFiniteState s_next cont with ⟨cres, cpost⟩
            rw [hc_run] at hcont_run
            simp only [hc_run] at hres ⊢
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
                exact worldStepIn_pmc_with_locals_clock (hcont_run hres) _ cpost.clock
              | returned cval =>
                exact worldStepIn_pmc_with_locals_clock (hcont_run (Or.inl ⟨cval, rfl⟩)) _ cpost.clock
          · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hres
            exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

theorem pmcPackState_ite160_step {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64} {logs : Nat} {z : Bool} {tail : ProgHOL 64}
    (hps : PmcPackState entry s w_out w_fr logs z)
    (htail : ∀ (z' : Bool) (s_mid : PanSemStateFiniteExact 64 F),
      PmcPackState entry s_mid w_out w_fr logs z' →
      PmcRelRunStrong entry tail s_mid) :
    PmcRelRunStrong entry
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
  unfold PmcRelRunStrong
  intro hres
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres ⊢
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
    show BitVec.ofNat 64 0 = 0#64 from rfl] at hres ⊢
  rw [hcond] at hres ⊢
  dsimp only at hres ⊢
  by_cases h160_eq : w160 = 0#64
  · rw [if_pos h160_eq, if_neg (show ¬ ((1#64 : BitVec 64) = 0) by decide)] at hres ⊢
    -- Step 1 inside then: store out+16 := load (frame+88)
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
    rw [evaluateHOLFiniteState_seq_line780, hev16] at hres ⊢
    dsimp only at hres ⊢
    -- Step 2 inside then: store out+24 := load (frame+136)
    have hload136 := pmc_load_local_off hps1.2.2.1 hps1.2.2.2.1 hfr_hi (by decide) (show 136 < 280 by decide)
    obtain ⟨hev24, hps2⟩ := pmcPackState_store hps1 (off := 24) (by decide) (by decide) (by decide) hload136
    set w136 := BitVec.ofNat 64 (memW s1 (w_fr.toNat + 136))
    set a24 := BitVec.ofNat 64 (w_out.toNat + 24)
    set s2 := { s1 with memory := pmcUpdW s1.memory a24 w136 }
    rw [evaluateHOLFiniteState_seq_line780, hev24] at hres ⊢
    dsimp only at hres ⊢
    -- Step 3 inside then: dec "rc" .one (load (frame+96)) (...)
    have hload96 := pmc_load_local_off hps2.2.2.1 hps2.2.2.2.1 hfr_hi (by decide) (show 96 < 280 by decide)
    set w96 := BitVec.ofNat 64 (memW s2 (w_fr.toNat + 96))
    rw [evaluateHOLFiniteState_dec_total] at hres ⊢
    dsimp only at hres ⊢
    have hsh_rc : shapeEqHOL .one (shapeOfHOLExact (.val (.word w96) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    have hl96' : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "frame"), .const 96#64])) =
        some (.val (.word w96)) := hload96
    rw [hl96'] at hres ⊢
    dsimp only at hres ⊢
    rw [if_pos hsh_rc] at hres ⊢
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
        PmcPackState entry s4 w_out w_fr logs false := by
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
          pmcPackState_with_locals_clock s4.locals s3.clock hs4_out hs4_fr hps3⟩
      · rw [if_neg hslt, if_pos (show (0#64 : BitVec 64) = 0 by decide), evaluateHOLFiniteState_skip]
        have hs3_ne : ∀ x, x ≠ ofString "rc" → s3.locals.lookup x = s2.locals.lookup x := by
          intro x hx
          simp [s3, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hx.symm]
        exact ⟨w96, s3, rfl, hs3_rc, hs3_ne, hps3⟩
    obtain ⟨w_rc', s4, hev_ite, hs4_rc, hs4_ne, hps4⟩ := hite_rc
    have hev_rc_var : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
        (.var .local (ofString "rc")) = some (.val (.word w_rc')) := by
      simp [evalHOLExact, hs4_rc]
    obtain ⟨hev8, hps5⟩ := pmcPackState_store hps4 (off := 8) (by decide) (by decide) (by decide) hev_rc_var
    set a8 := BitVec.ofNat 64 (w_out.toNat + 8)
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
    rw [hbody_dec] at hres ⊢
    dsimp only at hres ⊢
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
    exact htail false s_mid hps_mid hres
  · rw [if_neg h160_eq, if_pos (show (0#64 : BitVec 64) = 0 by decide), evaluateHOLFiniteState_skip] at hres ⊢
    dsimp only at hres ⊢
    exact htail z s hps hres

theorem pmcPack_cut {F : Type} (entry s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (ha2 : PmcA2 entry s) :
    PmcRelRunStrong entry pmcPack s := by
  obtain ⟨hM0, w_out, w_fr, hstep, hs_out, hs_fr, hw_out8, hw_in, hw_ok, hz16,
    hw_fr_ok, hfr_in, hlok, hdisj⟩ := ha2
  have hps0 := pmcPackState_of_a2 hM0 hstep hs_out hs_fr hw_out8 hw_in hw_ok hz16
    hw_fr_ok hfr_in hlok hdisj
  have hfr_hi : w_fr.toNat + 280 ≤ 2 ^ 64 := by
    have h1 : w_fr.toNat + 280 ≤ scratchEnd := hfr_in.2
    have h2 : scratchEnd ≤ 2 ^ 64 := by decide
    omega
  have hst_fr : ∀ {s0 : PanSemStateFiniteExact 64 F} {z0 : Bool} {off_out off_fr : Nat} {tail : ProgHOL 64},
      s0.code = originalRuntimeCode →
      PmcPackState entry s0 w_out w_fr (memW s (w_fr.toNat + 88)) z0 →
      off_out % 8 = 0 → off_out < 96 → off_out ≠ 16 →
      off_fr % 8 = 0 → off_fr < 280 →
      (∀ s1 : PanSemStateFiniteExact 64 F,
        s1.code = originalRuntimeCode →
        PmcPackState entry s1 w_out w_fr (memW s (w_fr.toNat + 88)) z0 →
        PmcRelRunStrong entry tail s1) →
      PmcRelRunStrong entry
        (.seq (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 off_out)])
                      (.load .one (.op .add [.var .local (ofString "frame"), .const (BitVec.ofNat 64 off_fr)])))
              tail) s0 :=
    fun hc0 hp0 ho8 holt hone hf8 hflt ht =>
      pmcPackState_store_frame_then hp0 ho8 holt hone hf8 hflt (fun hp1 => ht _ hc0 hp1)
  unfold PmcRelRunStrong
  intro hres
  unfold pmcPack pmcCode at hres ⊢
  simp only [sourceFunctionEntry, Guest.Software.guestFn_process_message_call,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil,
    R13Shards.spineAt] at hres ⊢
  revert hres
  change PmcRelRunStrong entry _ s
  refine hst_fr hcode hps0 (by decide) (by decide) (by decide) (by decide) (by decide) (fun s1 hc1 hps1 => ?_)
  refine hst_fr hc1 hps1 (by decide) (by decide) (by decide) (by decide) (by decide) (fun s2 hc2 hps2 => ?_)
  refine hst_fr hc2 hps2 (by decide) (by decide) (by decide) (by decide) (by decide) (fun s3 hc3 hps3 => ?_)
  refine hst_fr hc3 hps3 (by decide) (by decide) (by decide) (by decide) (by decide) (fun s4 hc4 hps4 => ?_)
  refine hst_fr hc4 hps4 (by decide) (by decide) (by decide) (by decide) (by decide) (fun s5 hc5 hps5 => ?_)
  refine hst_fr hc5 hps5 (by decide) (by decide) (by decide) (by decide) (by decide) (fun s6 hc6 hps6 => ?_)
  have hargs6 : evalListHOLFinite s6 (h := fun a => Classical.propDecidable (s6.memaddrs a))
      [.var .local (ofString "frame")] = some [.val (.word w_fr)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact, hps6.2.2.1]
  refine pmcPackState_decCall_ro_then hc6 ro_frame_state_gas_used hargs6 (by decide) (by decide) hps6
    (fun w_fsg s_fsg hc7 hs_fsg hps7 => ?_)
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
  unfold PmcRelRunStrong
  rw [evaluateHOLFiniteState_seq_line780, hev72]
  change PmcRelRunStrong entry _ _
  refine pmcPackState_ite160_step hps8 (fun _ s_post hps9 => ?_)
  refine pmcPackState_store_frame_then hps9 (by decide) (by decide) (by decide) (by decide) (by decide) (fun hps10 => ?_)
  refine pmcPackState_store_frame_then hps10 (by decide) (by decide) (by decide) (by decide) (by decide) (fun hps11 => ?_)
  exact pmcPackState_return hps11

theorem wk_process_message_call_strong_of_callees
    (hpm : WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => [(locN s "msg", 176), (globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetFrameResultStrong (ofString "process_message"))
    (hpcm : WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => [(locN s "msg", 176), (globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetFrameResultStrong (ofString "process_create_message")) :
    WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => [(locN s "msg", 176), (globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetMessageOutputStrong (ofString "process_message_call") :=
  wk_process_message_call_strong_of PmcA0 PmcA1 PmcA2 pmcA0_init pmcInit_cut
    (pmcDispatch_cut hpm hpcm) pmcPack_cut

theorem wk_process_message_call_of_callees
    (hpm : WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => [(locN s "msg", 176), (globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetFrameResultStrong (ofString "process_message"))
    (hpcm : WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => [(locN s "msg", 176), (globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetFrameResultStrong (ofString "process_create_message")) :
    WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => [(locN s "msg", 176), (globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetMessageOutput (ofString "process_message_call") :=
  worldKeepsIn_of_strong_message_output (wk_process_message_call_strong_of_callees hpm hpcm)

/-! ## 11b. Mark-Strengthened `process_message_call` (`RetMessageOutputMarks`) -/

def PmcMarksRun {F : Type} (entry : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) (s : PanSemStateFiniteExact 64 F) : Prop :=
  Resumes (evaluateHOLFiniteState s p).1 →
    PmcMarksPost entry (evaluateHOLFiniteState s p).1 (evaluateHOLFiniteState s p).2

def PmcMarksCut (phase : ProgHOL 64 → ProgHOL 64)
    (A B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop) : Prop :=
  ∀ {F : Type} (entry : PanSemStateFiniteExact 64 F) (tail : ProgHOL 64),
    (∀ s : PanSemStateFiniteExact 64 F, s.code = originalRuntimeCode →
      B entry s → PmcMarksRun entry tail s) →
    ∀ s : PanSemStateFiniteExact 64 F, s.code = originalRuntimeCode →
      A entry s → PmcMarksRun entry (phase tail) s

theorem pmcMarksPost_with_locals_clock {F : Type}
    {entry post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (h : PmcMarksPost entry r post) :
    PmcMarksPost entry r { post with locals := L, clock := k } :=
  h

theorem pmcMarksPost_not_returned {F : Type}
    {entry post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hnr : ∀ v, r ≠ some (.returned v))
    (hfmp : globN entry "frame_mem_ptr" ≤ globN post "frame_mem_ptr")
    (hsp : globN post "scratch_ptr" ≤ globN entry "scratch_ptr") :
    PmcMarksPost entry r post :=
  ⟨hfmp, hsp, fun v hv => absurd hv (hnr v)⟩

def PmcMarksA1 {F : Type} (entry s : PanSemStateFiniteExact 64 F) : Prop :=
  PmcA1 entry s ∧
  globN s "frame_mem_ptr" = globN entry "frame_mem_ptr" ∧
  globN s "scratch_ptr" = globN entry "scratch_ptr" ∧
  memW s (locN s "msg" + 24) = memW entry (locN entry "msg" + 24) ∧
  ∃ w_out : BitVec 64,
    s.locals.lookup (ofString "out") = some (.val (.word w_out)) ∧
    memW s (w_out.toNat + 48) = 0 ∧
    memW s (w_out.toNat + 80) = 0 ∧
    memW s (w_out.toNat + 88) = 0

def PmcMarksA2 {F : Type} (entry s : PanSemStateFiniteExact 64 F) : Prop :=
  PmcA2 entry s ∧
  globN entry "frame_mem_ptr" ≤ globN s "frame_mem_ptr" ∧
  globN s "scratch_ptr" ≤ globN entry "scratch_ptr" ∧
  ∃ w_out w_fr : BitVec 64,
    s.locals.lookup (ofString "out") = some (.val (.word w_out)) ∧
    s.locals.lookup (ofString "frame") = some (.val (.word w_fr)) ∧
    memW s (w_fr.toNat + 128) ≤ scratchEnd ∧
    memW s (w_fr.toNat + 208) ≤ globN entry "scratch_ptr" ∧
    memW s (w_fr.toNat + 224) = globN entry "frame_mem_ptr" ∧
    memW s (w_fr.toNat + 224) ≤ memW s (w_fr.toNat + 208) ∧
    memW s (w_fr.toNat + 208) % 8 = 0 ∧
    (memW entry (locN entry "msg" + 24) ≠ 0 →
      memW s (w_fr.toNat + 208) = globN entry "scratch_ptr")

theorem pmcMarksInit_cut : PmcMarksCut pmcInit PmcA0 PmcMarksA1 := by
  intro F entry tail htail s hcode ⟨hs_eq, hM0⟩
  cases hs_eq
  unfold PmcMarksRun
  intro hres
  unfold pmcInit pmcCode at hres ⊢
  simp only [sourceFunctionEntry, Guest.Software.guestFn_process_message_call,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil,
    R13Shards.spinePlug] at hres ⊢
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_skip] at hres ⊢
  dsimp only at hres ⊢
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hres ⊢
  have hargs_al : evalListHOLFinite entry (h := fun a => Classical.propDecidable (entry.memaddrs a))
      [.const 96#64] = some [.val (.word 96#64)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact]
  simp only [hargs_al] at hres ⊢
  rcases hl_al : lookupCodeHOLFinite entry.code.lookup (ofString "alloc") [.val (.word 96#64)]
      with _ | ⟨body_al, callee_al, ret_al⟩
  · simp only [hl_al] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [hl_al] at hres ⊢
    by_cases hclk0 : entry.clock = 0
    · simp only [hclk0, ↓reduceIte] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hclk0, ↓reduceIte] at hres ⊢
      have hpc_al := R10Shards.Fast_GbodyC17ToC21.callee_param_one_exp entry (ofString "alloc")
        (ofString "n") .one _ _ (by rw [hcode]; exact R10Shards.Fast_GbodyC17ToC21.lookup_alloc_fn)
        (.const 96#64) (.val (.word 96#64)) [.val (.word 96#64)] body_al callee_al ret_al rfl hargs_al hl_al
      have hn_al : locN (callEntryStateHOLFinite entry callee_al) "n" = 96 := by
        simp [locN, callEntryStateHOLFinite, hpc_al.2]
      rcases hrun_al : evaluateHOLFiniteState (callEntryStateHOLFinite entry callee_al) body_al with ⟨res_al, post_al⟩
      simp only [hrun_al] at hres ⊢
      have hWOK_en : WorldOK entry := msgReady_worldOK entry hM0
      cases res_al with
      | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      | some br_al =>
        cases br_al with
        | timeOut => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | error => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | «break» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | «continue» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | finalFfi _ => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | exception eid eval =>
          dsimp only at hres ⊢
          have hstep_al := FunSpec.at_lookup wk_alloc_local entry hcode _ body_al callee_al ret_al hl_al
            (localsFree_worldOK entry callee_al (entry.clock - 1) hWOK_en)
            (by rw [hrun_al]; simp)
          rw [hrun_al] at hstep_al
          have hws_al := hstep_al hres
          have hfmp_eq : globN post_al "frame_mem_ptr" = globN entry "frame_mem_ptr" := by
            unfold globN
            have hg := hws_al.2.2.1 (ofString "frame_mem_ptr") (by decide)
            dsimp only [callEntryStateHOLFinite] at hg
            rw [hg]
          have hsp_eq : globN post_al "scratch_ptr" = globN entry "scratch_ptr" := by
            unfold globN
            have hg := hws_al.2.2.1 (ofString "scratch_ptr") (by decide)
            dsimp only [callEntryStateHOLFinite] at hg
            rw [hg]
          exact pmcMarksPost_not_returned (by intro _ h; simp at h)
            (Nat.le_of_eq hfmp_eq.symm) (Nat.le_of_eq hsp_eq)
        | returned val_al =>
          dsimp only at hres ⊢
          by_cases hsh_al : (shapeEqHOL (shapeOfHOLExact val_al) .one && shapeEqHOL (shapeOfHOLExact val_al) ret_al) = true
          · simp only [hsh_al, ↓reduceIte] at hres ⊢
            have hstep_al := FunSpec.at_lookup wk_alloc_local entry hcode _ body_al callee_al ret_al hl_al
              (localsFree_worldOK entry callee_al (entry.clock - 1) hWOK_en)
              (by rw [hrun_al]; simp)
            rw [hrun_al] at hstep_al
            have hws_al := hstep_al (Or.inl ⟨val_al, rfl⟩)
            have hrt_al := FunSpec.at_lookup rt_alloc_local entry hcode _ body_al callee_al ret_al hl_al
              (localsFree_arenaReady entry callee_al (entry.clock - 1) hM0.1)
              (by rw [hrun_al]; simp)
            rw [hrun_al] at hrt_al
            obtain ⟨w_out, rfl, hAR_al, hAG_al, hw_out8, hw_in_al, hw_ok_al⟩ := hrt_al val_al rfl
            rw [hn_al] at hw_in_al hw_ok_al
            change Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN post_al "heap_ptr") at hw_in_al
            change WordsOK post_al (w_out.toNat, 96) at hw_ok_al
            set s1 := setVarHOLFinite (ofString "out") (.val (.word w_out)) { post_al with locals := entry.locals }
            have hs1_code : s1.code = originalRuntimeCode := hAR_al.1.code
            have hs1_out : s1.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
              simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
            have hs1_msg : s1.locals.lookup (ofString "msg") = entry.locals.lookup (ofString "msg") := by
              simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
                show ofString "out" ≠ ofString "msg" by decide]
            have hfmp_s1 : globN s1 "frame_mem_ptr" = globN entry "frame_mem_ptr" := by
              change globN post_al "frame_mem_ptr" = globN entry "frame_mem_ptr"
              unfold globN
              have hg := hws_al.2.2.1 (ofString "frame_mem_ptr") (by decide)
              dsimp only [callEntryStateHOLFinite] at hg
              rw [hg]
            have hsp_s1_eq : globN s1 "scratch_ptr" = globN entry "scratch_ptr" := by
              change globN post_al "scratch_ptr" = globN entry "scratch_ptr"
              unfold globN
              have hg := hws_al.2.2.1 (ofString "scratch_ptr") (by decide)
              dsimp only [callEntryStateHOLFinite] at hg
              rw [hg]
            obtain ⟨S_en, Nd_en, hMA_en⟩ := R10Shards.Fast_GbodyC17ToC21.msgReadyAt_of_msgReady hM0
            have hws_al_av : WorldStep (fun _ => []) ["heap_ptr"] stdKeep
                (fun _ r' post' S' Nd' => ∀ v', r' = some (.returned v') → ∃ w : BitVec 64,
                  v' = .val (.word w) ∧ IvlsDisj [(w.toNat, 96)] (worldOwned post' S' Nd'))
                entry (some (.returned (.val (.word w_out)))) post_al := by
              obtain ⟨a1, a2, a3, a4, a5⟩ := hws_al
              refine ⟨a1, a2, a3, a4, fun S_x Nd_x hW_x _ => ?_⟩
              obtain ⟨S', Nd', hs, hw', hog, hfo, hq⟩ :=
                a5 S_x Nd_x ((R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals _ _ _ _ _).2 hW_x)
                  (fun x hx => by simp at hx)
              refine ⟨S', Nd', hs, hw', hog, hfo, fun v' hv' => ?_⟩
              obtain ⟨w, hw_eq, hav⟩ := hq v' hv'
              dsimp only at hav; rw [hn_al] at hav
              exact ⟨w, hw_eq, hav⟩
            obtain ⟨S0_s1, Nd_s1, hMA_post_al, hQ0_al, hfp_al⟩ :=
              R10Shards.Fast_GbodyC17ToC21.WorldStep.preserves_msgReadyAt hMA_en hws_al_av
                (fun j hj => by simp at hj) (fun x hx => by simp at hx)
            obtain ⟨w_out', hw_eq, hav0_al⟩ := hQ0_al (.val (.word w_out)) rfl
            injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
            have hMA_s1 : R10Shards.Fast_GbodyC17ToC21.MsgReadyAt s1
                (S0_s1 ++ [memW entry (locN entry "msg" + 152), memW entry (locN entry "msg" + 160)]) Nd_s1 :=
              R10Shards.Fast_GbodyC17ToC21.msgReadyAt_with_locals
                (s := { post_al with locals := entry.locals })
                (by simp [HolFiniteMapExact.update, FUPDATE, show ofString "out" ≠ ofString "msg" by decide])
                hMA_post_al
            have hM_s1 : MsgReady s1 :=
              R10Shards.Fast_GbodyC17ToC21.msgReadyAt_msgReady hMA_s1
            have hWOK_s1 : WorldOK s1 := msgReady_worldOK s1 hM_s1
            have hsp_s1 : globN s1 "scratch_ptr" ≤ globN entry "scratch_ptr" := hAG_al.2
            have hw_in_s1 : Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s1 "heap_ptr") := hw_in_al
            have hw_ok_s1 : WordsOK s1 (w_out.toNat, 96) := hw_ok_al
            -- Also msg+24 preserved across alloc:
            have hm_in_en : Inside (locN entry "msg", 176) sourceBase (globN entry "heap_ptr") :=
              hMA_en.2.2.2.2.2.2.2.2.2.2.1
            have hm_hi_en : locN entry "msg" + 176 ≤ 2 ^ 64 :=
              (ivl_allocated_bound hM0.1.2 (Or.inl hm_in_en)).2
            obtain ⟨_, _, _, _, hOG_al_en, hFO_al_en, _⟩ :=
              hws_al_av.2.2.2.2 S_en Nd_en hMA_en.2.1 (fun x hx => by simp at hx)
            have hmsg_u_al : IvlUnhit entry s1 (locN entry "msg", 176) :=
              (heap_ivl_survives_step (b := (locN entry "msg", 176))
                hM0.1.2 hws_al_av.2.1 hOG_al_en hFO_al_en
                (worldOwned_zero_aligned hMA_en.2.1) (fun _ hj => by simp at hj)
                hMA_en.2.2.2.2.2.2.2.2.2.1 (by dsimp) hm_in_en
                hMA_en.2.2.2.2.2.2.2.2.2.2.2.1 (fun _ hj => by simp at hj)).2.2
            have hmsg24_s1 : memW s1 (locN entry "msg" + 24) = memW entry (locN entry "msg" + 24) :=
              memW_eq_of_ivlUnhit hmsg_u_al (by have := hMA_en.2.2.2.2.2.2.2.2.2.1; omega) hm_hi_en
                ⟨by dsimp; omega, by dsimp; omega⟩
            have hout_ow_s1_at : IvlsDisj [(w_out.toNat, 96)]
                (worldOwned s1 (S0_s1 ++ [memW entry (locN entry "msg" + 152), memW entry (locN entry "msg" + 160)]) Nd_s1) := by
              intro x hx j hj
              simp only [List.mem_singleton] at hx; subst hx
              change j ∈ worldOwned post_al _ Nd_s1 at hj
              unfold worldOwned at hj
              rcases List.mem_append.1 hj with h1 | hnd
              · rcases List.mem_append.1 h1 with htab | hfix
                · rw [List.flatMap_append] at htab
                  rcases List.mem_append.1 htab with htab0 | htab_loc
                  · apply hav0_al (w_out.toNat, 96) (by simp) j
                    unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl htab0)))
                  · obtain ⟨u, hu_loc, hj_fp⟩ := List.mem_flatMap.1 htab_loc
                    rw [hfp_al u hu_loc] at hj_fp
                    have hu_S : u ∈ S_en := by
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_loc
                      rcases hu_loc with rfl | rfl
                      · exact hMA_en.2.2.1
                      · exact hMA_en.2.2.2.1
                    have hal_j : Allocated entry j := ((hMA_en.2.1.1.2.1 u hu_S).2 j hj_fp).1
                    have hsep : heapLimit ≤ scratchStart := by decide
                    obtain ⟨_, h1_s, h2_s, h3_s, _⟩ := hMA_en.1.2
                    rcases hal_j with ⟨_, hhi_j⟩ | ⟨hlo_j, _⟩
                    · exact Or.inr (Or.inr (Or.inr (Nat.le_trans hhi_j hw_in_al.1)))
                    · exact Or.inr (Or.inr (Or.inl (by
                        have hhp_lim : globN post_al "heap_ptr" ≤ heapLimit := hAR_al.2.2.1
                        have hsc_lo : scratchStart ≤ globN entry "scratch_ptr" :=
                          Nat.le_trans h2_s h3_s
                        unfold Inside at hw_in_al; omega)))
                · apply hav0_al (w_out.toNat, 96) (by simp) j
                  unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
              · apply hav0_al (w_out.toNat, 96) (by simp) j
                unfold worldOwned; exact List.mem_append.2 (Or.inr hnd)
            have hws_s1 : WorldStep (fun _ => []) ["heap_ptr", "scratch_ptr"] pmcKeep
                (fun _ _ st S' Nd' => IvlsDisj [(w_out.toNat, 96)] (worldOwned st S' Nd'))
                entry none s1 := by
              have h1 : WorldStep (fun _ => []) ["heap_ptr"] stdKeep
                  (fun _ _ st S' Nd' => IvlsDisj [(w_out.toNat, 96)] (worldOwned st S' Nd'))
                  entry (some (.returned (.val (.word w_out)))) post_al := by
                obtain ⟨a1, a2, a3, a4, a5⟩ := hws_al_av
                refine ⟨a1, a2, a3, a4, fun S_x Nd_x hW_x hD_x => ?_⟩
                obtain ⟨S', Nd', hs, hw', hog, hfo, hq⟩ := a5 S_x Nd_x hW_x hD_x
                obtain ⟨w', hw_eq, hav⟩ := hq (.val (.word w_out)) rfl
                injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
                exact ⟨S', Nd', hs, hw', hog, hfo, hav⟩
              exact worldStep_pmcKeep_with_locals_clock_Q
                (worldStep_pmcKeep_of_stdKeep (by intro g hg; simp at hg; subst hg; simp) h1)
                s1.locals post_al.clock
            rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
            rw [evaluateHOLFiniteState_call] at hres ⊢
            have hargs_mz : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
                [.var .local (ofString "out"), .const 96#64] = some [.val (.word w_out), .val (.word 96#64)] := by
              rw [evalListHOLFinite_eq_toExact]
              simp [evalListHOLExact, evalHOLExact, hs1_out]
            simp only [hargs_mz] at hres ⊢
            rcases hl_mz : lookupCodeHOLFinite s1.code.lookup (ofString "memzero")
                [.val (.word w_out), .val (.word 96#64)] with _ | ⟨body_mz, callee_mz, ret_mz⟩
            · simp only [hl_mz] at hres
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
            · simp only [hl_mz] at hres ⊢
              by_cases hclk1 : s1.clock = 0
              · simp only [hclk1, ↓reduceIte] at hres
                exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
              · simp only [hclk1, ↓reduceIte] at hres ⊢
                have hl_mz_rt : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "memzero")
                    [.val (.word w_out), .val (.word 96#64)] = some (body_mz, callee_mz, ret_mz) := by
                  rwa [← hs1_code]
                have hraw_mz := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "memzero")
                  [.val (.word w_out), .val (.word 96#64)] body_mz callee_mz ret_mz hl_mz_rt
                have hlook_mz_fn := R10Shards.Fast_GbodyC17ToC21.lookup_memzero_fn
                have hbody_mz_eq : body_mz = sourceFnBody Guest.Software.guestFn_memzero ∧ ret_mz = .one := by
                  unfold lookupCodeHOLExact at hraw_mz
                  rw [hlook_mz_fn] at hraw_mz
                  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memzero,
                    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
                    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
                    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural] at hraw_mz ⊢
                  split at hraw_mz
                  · injection hraw_mz with hp
                    exact ⟨(Prod.mk.inj hp).1.symm, (Prod.mk.inj (Prod.mk.inj hp).2).2.symm⟩
                  · cases hraw_mz
                have hp2_mz := R10Shards.Fast_GbodyC17ToC21.callee_param_two s1 (ofString "memzero")
                  (ofString "dst") (ofString "n") .one .one _ _
                  (by rw [hs1_code]; exact hlook_mz_fn)
                  (.var .local (ofString "out")) (.const 96#64) (.val (.word w_out)) (.val (.word 96#64))
                  [.val (.word w_out), .val (.word 96#64)] body_mz callee_mz ret_mz
                  (by simp [evalAt, evalHOLExact, hs1_out]) rfl hargs_mz hl_mz
                have hdst_mz : locN (callEntryStateHOLFinite s1 callee_mz) "dst" = w_out.toNat := by
                  simp [locN, callEntryStateHOLFinite, hp2_mz.2.1]
                have hn_mz : locN (callEntryStateHOLFinite s1 callee_mz) "n" = 96 := by
                  simp [locN, callEntryStateHOLFinite, hp2_mz.2.2]
                rcases hrun_mz : evaluateHOLFiniteState (callEntryStateHOLFinite s1 callee_mz) body_mz with ⟨res_mz, post_mz⟩
                simp only [hrun_mz] at hres ⊢
                have hres_mz_body : Resumes res_mz →
                    Wave8Contracts.M08.RegionWriteFrame (callEntryStateHOLFinite s1 callee_mz) post_mz (w_out.toNat, 96) := by
                  intro hr_mz
                  have hce_code : (callEntryStateHOLFinite s1 callee_mz).code = originalRuntimeCode := hs1_code
                  have hce_G : GuestInv (callEntryStateHOLFinite s1 callee_mz) :=
                    (localsFree_arenaReady s1 callee_mz (s1.clock - 1) hM_s1.1).1
                  have hr_m08 : Wave8Contracts.M08.Resumes res_mz := by
                    rcases hr_mz with ⟨v, hv⟩ | ⟨e, v, hv, ht⟩
                    · exact Or.inl ⟨v, hv⟩
                    · exact Or.inr ⟨e, v, hv, ht⟩
                  have hmwf := Wave8Contracts.M08.memzero_body_frame (callEntryStateHOLFinite s1 callee_mz)
                    hce_code hce_G (by rw [← hbody_mz_eq.1, hrun_mz]; exact hr_m08)
                  rw [← hbody_mz_eq.1, hrun_mz, hdst_mz, hn_mz] at hmwf
                  exact hmwf
                cases res_mz with
                | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                | some br_mz =>
                  cases br_mz with
                  | timeOut => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                  | error => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                  | «break» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                  | «continue» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                  | finalFfi _ => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                  | exception eid eval =>
                    dsimp only at hres ⊢
                    have hmwf := hres_mz_body hres
                    have hfmp_mz : globN post_mz "frame_mem_ptr" = globN entry "frame_mem_ptr" :=
                      (Wave8Contracts.M08.globN_congr hmwf.2.2.2.2.2.1 "frame_mem_ptr").trans hfmp_s1
                    have hsp_mz : globN post_mz "scratch_ptr" = globN entry "scratch_ptr" :=
                      (Wave8Contracts.M08.globN_congr hmwf.2.2.2.2.2.1 "scratch_ptr").trans hsp_s1_eq
                    exact pmcMarksPost_not_returned (by intro _ h; simp at h)
                      (Nat.le_of_eq hfmp_mz.symm) (Nat.le_of_eq hsp_mz)
                  | returned val_mz =>
                    dsimp only at hres ⊢
                    by_cases hsh_mz : shapeEqHOL (shapeOfHOLExact val_mz) ret_mz
                    · simp only [hsh_mz, ↓reduceIte] at hres ⊢
                      have hmwf := hres_mz_body (Or.inl ⟨val_mz, rfl⟩)
                      obtain ⟨hws_mz_raw, hcore_mz⟩ :=
                        worldStep_of_region_writes_ownedEq (s := s1) (post := post_mz)
                          (r := some (.returned val_mz)) (R := fun _ => [(w_out.toNat, 96)])
                          hWOK_s1
                          ⟨hmwf.1, hmwf.2.1, hmwf.2.2.1, hmwf.2.2.2.1, hmwf.2.2.2.2.1, hmwf.2.2.2.2.2.1⟩
                          hmwf.2.2.2.2.2.2.1
                          (fun a ha_lt hnot => hmwf.2.2.2.2.2.2.2.1 a ha_lt (fun hin => hnot _ (List.mem_singleton.2 rfl) hin))
                          hmwf.2.2.2.2.2.2.2.2
                      have hzf := FunSpec.at_lookup zv_memzero_local s1 hs1_code _ body_mz callee_mz ret_mz hl_mz
                        (localsFree_arenaReady s1 callee_mz (s1.clock - 1) hM_s1.1)
                        (by rw [hrun_mz]; simp)
                      rw [hrun_mz] at hzf
                      have hmem16_zero : memW post_mz (w_out.toNat + 16) = 0 :=
                        hzf val_mz rfl (w_out.toNat + 16) (by rw [hdst_mz]; omega) (by rw [hdst_mz, hn_mz]; omega) (by omega)
                      have hmem48_zero : memW post_mz (w_out.toNat + 48) = 0 :=
                        hzf val_mz rfl (w_out.toNat + 48) (by rw [hdst_mz]; omega) (by rw [hdst_mz, hn_mz]; omega) (by omega)
                      have hmem80_zero : memW post_mz (w_out.toNat + 80) = 0 :=
                        hzf val_mz rfl (w_out.toNat + 80) (by rw [hdst_mz]; omega) (by rw [hdst_mz, hn_mz]; omega) (by omega)
                      have hmem88_zero : memW post_mz (w_out.toNat + 88) = 0 :=
                        hzf val_mz rfl (w_out.toNat + 88) (by rw [hdst_mz]; omega)
                          (by rw [hdst_mz, hn_mz]) (by omega)
                      set s2_pre : PanSemStateFiniteExact 64 F := { post_mz with locals := s1.locals }
                      rw [evaluateHOLFiniteState_dec_total] at hres ⊢
                      simp only [evalHOLExact, shapeEqHOL, shapeOfHOLExact, ↓reduceIte] at hres ⊢
                      set s2 := setVarHOLFinite (ofString "frame") (.val (.word 0#64)) s2_pre
                      have hhp_mz_eq : globN s2 "heap_ptr" = globN s1 "heap_ptr" :=
                        Wave8Contracts.M08.globN_congr hmwf.2.2.2.2.2.1 "heap_ptr"
                      have hsp_mz_eq : globN s2 "scratch_ptr" = globN s1 "scratch_ptr" :=
                        Wave8Contracts.M08.globN_congr hmwf.2.2.2.2.2.1 "scratch_ptr"
                      have hfmp_mz_eq : globN s2 "frame_mem_ptr" = globN s1 "frame_mem_ptr" :=
                        Wave8Contracts.M08.globN_congr hmwf.2.2.2.2.2.1 "frame_mem_ptr"
                      have hs2_code : s2.code = originalRuntimeCode := by
                        change post_mz.code = originalRuntimeCode
                        rw [hmwf.1]; exact hs1_code
                      have hs2_msg : s2.locals.lookup (ofString "msg") = entry.locals.lookup (ofString "msg") := by
                        simp [s2, s2_pre, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hs1_msg,
                          show ofString "frame" ≠ ofString "msg" by decide]
                      have hs2_out : s2.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
                        simp [s2, s2_pre, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hs1_out,
                          show ofString "frame" ≠ ofString "out" by decide]
                      have hs2_fr : s2.locals.lookup (ofString "frame") = some (.val (.word 0#64)) := by
                        simp [s2, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
                      set S_s1_full := S0_s1 ++ [memW entry (locN entry "msg" + 152), memW entry (locN entry "msg" + 160)]
                      have hdisj_mz_all : IvlsDisj [(w_out.toNat, 96)]
                          ((locN s1 "msg", 176) :: worldTypedIvls s1 S_s1_full Nd_s1) := by
                        intro x hx j hj
                        simp only [List.mem_singleton] at hx; subst hx
                        rcases List.mem_cons.1 hj with rfl | hj_wti
                        · have hm_eq_loc : locN s1 "msg" = locN entry "msg" := by simp [locN, hs1_msg]
                          rw [hm_eq_loc]
                          exact Or.inr (Or.inr (Or.inr (Nat.le_trans hm_in_en.2 hw_in_s1.1)))
                        · exact hout_ow_s1_at _ (by simp) j (worldTypedIvls_sub_worldOwned _ _ _ j hj_wti)
                      have hws_mz_av : WorldStep (fun _ => [(w_out.toNat, 96)]) [] stdKeep
                          (fun _ _ post0 S' Nd' => IvlsDisj [(w_out.toNat, 96)] (worldOwned post0 S' Nd'))
                          s1 (some (.returned val_mz)) post_mz := by
                        obtain ⟨a1, a2, a3, a4, _⟩ := hws_mz_raw
                        refine ⟨a1, a2, a3, a4, fun S_x Nd_x hW_x hD_x => ?_⟩
                        obtain ⟨hWT_post, howned_eq⟩ := hcore_mz S_x Nd_x hW_x hD_x
                        refine ⟨S_x, Nd_x, fun _ ht => ht, hWT_post,
                          by rw [howned_eq]; exact Wave8Contracts.M08.ownedGrows_refl s1 post_mz _,
                          fun a hkeep _ => hmwf.2.2.2.2.2.2.1 a
                            (fun j hj => hkeep j (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hj)))))
                            (fun hc => by unfold CellHits at hc; omega), ?_⟩
                        dsimp only
                        rw [howned_eq]
                        intro x hx j hj
                        unfold worldOwned at hj
                        rcases List.mem_append.1 hj with h1 | hnd
                        · rcases List.mem_append.1 h1 with htab | hfix
                          · apply hD_x x hx j
                            unfold worldTypedIvls
                            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
                            apply List.mem_append.2; left; exact List.mem_append.2 (Or.inl htab)
                          · apply hout_ow_s1_at x hx j
                            unfold worldOwned
                            exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
                        · apply hD_x x hx j
                          unfold worldTypedIvls
                          exact List.mem_append.2 (Or.inr hnd)
                      obtain ⟨S0_s2, Nd_s2, hMA_s2_pre, hav0_mz, hfp_mz⟩ :=
                        R10Shards.Fast_GbodyC17ToC21.WorldStep.preserves_msgReadyAt hMA_s1 hws_mz_av
                          (fun x hx h0 => by simp at hx; subst hx; simp at h0) hdisj_mz_all
                      have hMA_s2 : R10Shards.Fast_GbodyC17ToC21.MsgReadyAt s2
                          (S0_s2 ++ [memW s1 (locN s1 "msg" + 152), memW s1 (locN s1 "msg" + 160)]) Nd_s2 :=
                        R10Shards.Fast_GbodyC17ToC21.msgReadyAt_with_locals
                          (s := s2_pre)
                          (by simp [HolFiniteMapExact.update, FUPDATE, show ofString "frame" ≠ ofString "msg" by decide])
                          hMA_s2_pre
                      have hM_s2 : MsgReady s2 :=
                        R10Shards.Fast_GbodyC17ToC21.msgReadyAt_msgReady hMA_s2
                      have hout_ow_s2_at : IvlsDisj [(w_out.toNat, 96)]
                          (worldOwned s2 (S0_s2 ++ [memW s1 (locN s1 "msg" + 152), memW s1 (locN s1 "msg" + 160)]) Nd_s2) := by
                        intro x hx j hj
                        simp only [List.mem_singleton] at hx; subst hx
                        change j ∈ worldOwned post_mz _ Nd_s2 at hj
                        unfold worldOwned at hj
                        rcases List.mem_append.1 hj with h1 | hnd
                        · rcases List.mem_append.1 h1 with htab | hfix
                          · rw [List.flatMap_append] at htab
                            rcases List.mem_append.1 htab with htab0 | htab_loc
                            · apply hav0_mz (w_out.toNat, 96) (by simp) j
                              unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl htab0)))
                            · obtain ⟨u, hu_loc, hj_fp⟩ := List.mem_flatMap.1 htab_loc
                              rw [hfp_mz u hu_loc] at hj_fp
                              have hu_S : u ∈ S_s1_full := by
                                simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_loc
                                rcases hu_loc with rfl | rfl
                                · exact hMA_s1.2.2.1
                                · exact hMA_s1.2.2.2.1
                              apply hout_ow_s1_at (w_out.toNat, 96) (by simp) j
                              unfold worldOwned
                              exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨u, hu_S, hj_fp⟩))))
                          · apply hav0_mz (w_out.toNat, 96) (by simp) j
                            unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
                        · apply hav0_mz (w_out.toNat, 96) (by simp) j
                          unfold worldOwned; exact List.mem_append.2 (Or.inr hnd)
                      have hws_s1_s2 : WorldStep (fun _ => [(w_out.toNat, 96)]) ["heap_ptr", "scratch_ptr"] pmcKeep
                          (fun _ _ st S' Nd' => IvlsDisj [(w_out.toNat, 96)] (worldOwned st S' Nd'))
                          s1 none s2 :=
                        worldStep_pmcKeep_with_locals_clock_Q
                          (worldStep_pmcKeep_of_stdKeep (by intro g hg; cases hg) hws_mz_av)
                          s2.locals post_mz.clock
                      have hws_en_s2 := worldStep_pmcPrefix_trans (w_out := w_out)
                        (Q2 := fun _ _ st S' Nd' => IvlsDisj [(w_out.toNat, 96)] (worldOwned st S' Nd'))
                        hM0.1 hWOK_en
                        (fun j hj => by simp at hj)
                        (fun j hj => by simp at hj; subst hj; right; rw [hhp_mz_eq]; exact hw_in_s1)
                        (fun _ _ h => h)
                        (fun S2 Nd2 _ hout2 x hx j hj => by
                          simp at hx; subst hx
                          exact hout2 _ (by simp) j (worldTypedIvls_sub_worldOwned _ _ _ j hj))
                        hws_s1 hsp_s1 hws_s1_s2
                        (fun _ _ _ _ _ _ _ _ hq2 => hq2)
                      have hw_in_s2 : Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s2 "heap_ptr") := by
                        rw [hhp_mz_eq]; exact hw_in_s1
                      have hw_ok_s2 : WordsOK s2 (w_out.toNat, 96) :=
                        wordsOK_transfer hM_s1.1.1 hM_s2.1.1 hw_ok_s1
                      have hsp_s2 : globN s2 "scratch_ptr" ≤ globN entry "scratch_ptr" := by
                        rw [hsp_mz_eq]; exact hsp_s1
                      have hmsg_u_mz : IvlUnhit s1 s2 (locN entry "msg", 176) := by
                        intro a ha8 hch
                        apply hmwf.2.2.2.2.2.2.1 a
                        · intro j hj hchj
                          simp only [List.mem_singleton] at hj; subst hj
                          dsimp only [CellHits] at hch hchj
                          dsimp only [Inside] at hm_in_en hw_in_s1; omega
                        · intro hch0; dsimp only [CellHits] at hch0; omega
                      have hmsg24_s2 : memW s2 (locN s2 "msg" + 24) = memW entry (locN entry "msg" + 24) := by
                        have hm_loc_s2 : locN s2 "msg" = locN entry "msg" := by simp [locN, hs2_msg]
                        rw [hm_loc_s2]
                        exact (memW_eq_of_ivlUnhit hmsg_u_mz (by have := hMA_en.2.2.2.2.2.2.2.2.2.1; omega)
                          hm_hi_en ⟨by dsimp; omega, by dsimp; omega⟩).trans hmsg24_s1
                      have hp1 : PmcMarksA1 entry s2 :=
                        ⟨⟨hM0, hM_s2, hs2_msg, hsp_s2, w_out, hws_en_s2, hs2_out, hs2_fr, hw_out8,
                          hw_in_s2, hw_ok_s2, hmem16_zero, _, _, hMA_s2, hout_ow_s2_at⟩,
                         hfmp_mz_eq.trans hfmp_s1, hsp_mz_eq.trans hsp_s1_eq, hmsg24_s2,
                         w_out, hs2_out, hmem48_zero, hmem80_zero, hmem88_zero⟩
                      have htail_run := htail s2 hs2_code hp1
                      unfold PmcMarksRun at htail_run
                      rcases hrun_tail : evaluateHOLFiniteState s2 tail with ⟨res_t, post_t⟩
                      rw [hrun_tail] at htail_run
                      simp only [hrun_tail] at hres ⊢
                      cases res_t with
                      | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                      | some br_t =>
                        cases br_t with
                        | timeOut => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                        | error => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                        | «break» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                        | «continue» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                        | finalFfi _ => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                        | exception eid eval =>
                          exact pmcMarksPost_with_locals_clock _ post_t.clock
                            (pmcMarksPost_with_locals_clock _ post_t.clock (htail_run hres))
                        | returned val_t =>
                          exact pmcMarksPost_with_locals_clock _ post_t.clock
                            (pmcMarksPost_with_locals_clock _ post_t.clock (htail_run (Or.inl ⟨val_t, rfl⟩)))
                    · simp only [hsh_mz, Bool.false_eq_true, ↓reduceIte] at hres
                      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          · simp only [hsh_al, Bool.false_eq_true, ↓reduceIte] at hres
            exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

theorem pmcMarksA2_with_locals {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hout : L.lookup (ofString "out") = s.locals.lookup (ofString "out"))
    (hfr : L.lookup (ofString "frame") = s.locals.lookup (ofString "frame"))
    (hp : PmcMarksA2 entry s) :
    PmcMarksA2 entry { s with locals := L } := by
  obtain ⟨hpA2, hfmp, hsp, w_out, w_fr, hs_out, hs_fr, h128, h208, h224, hle, h8, hex⟩ := hp
  refine ⟨pmcA2_with_locals hout hfr hpA2, hfmp, hsp, w_out, w_fr, ?_, ?_, h128, h208, h224, hle, h8, hex⟩
  · rw [hout]; exact hs_out
  · rw [hfr]; exact hs_fr

theorem pmcMarks_call_frame_callee {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {fname : MlS} {tail : ProgHOL 64}
    {w_out : BitVec 64}
    {Q_c : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {restL : HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64)}
    (hcall_spec : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep Q_c fname)
    (hQ_marks : ∀ {F' : Type} (s0 : PanSemStateFiniteExact 64 F') r0 post0 S0 Nd0,
      Q_c s0 r0 post0 S0 Nd0 → RetFrameResultMarks s0 r0 post0 S0 Nd0)
    (hQ_exact : memW entry (locN entry "msg" + 24) ≠ 0 →
      ∀ {F' : Type} (s0 : PanSemStateFiniteExact 64 F') r0 post0 S0 Nd0,
        Q_c s0 r0 post0 S0 Nd0 →
        ∀ v0, r0 = some (.returned v0) → ∃ w0 : BitVec 64,
          v0 = .val (.word w0) ∧ memW post0 (w0.toNat + 208) = globN s0 "scratch_ptr")
    (hlook_rt : ∃ b r, originalRuntimeCode.lookup fname = some ([(ofString "msg", .one)], b, r))
    (hrest_out : ∀ m, (restL m).lookup (ofString "out") = m.lookup (ofString "out"))
    (hrest_fr : ∀ m, (restL m).lookup (ofString "frame") = m.lookup (ofString "frame"))
    (htail : ∀ s' : PanSemStateFiniteExact 64 F, s'.code = originalRuntimeCode →
      PmcMarksA2 entry s' → PmcMarksRun entry tail s')
    (hcode : s.code = originalRuntimeCode)
    (hM0 : MsgReady entry)
    (hM_s : MsgReady s)
    (hs_msg : s.locals.lookup (ofString "msg") = entry.locals.lookup (ofString "msg"))
    (hfmp_s : globN s "frame_mem_ptr" = globN entry "frame_mem_ptr")
    (hsp_s : globN s "scratch_ptr" ≤ globN entry "scratch_ptr")
    (hsp_s_exact : memW entry (locN entry "msg" + 24) ≠ 0 → globN s "scratch_ptr" = globN entry "scratch_ptr")
    (hws_s : WorldStep (fun st => bufRegions pmcBufs st ++ [(globN entry "heap_ptr", globN s "heap_ptr" - globN entry "heap_ptr")])
      ["heap_ptr", "scratch_ptr"] pmcKeep
      (fun _ _ st S Nd => IvlsDisj [(w_out.toNat, 96)] (worldOwned st S Nd))
      entry none s)
    (hs_out : s.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hs_fr : s.locals.lookup (ofString "frame") = some (.val (.word 0#64)))
    (hw_out8 : w_out.toNat % 8 = 0)
    (hw_in_s : Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s "heap_ptr"))
    (hw_ok_s : WordsOK s (w_out.toNat, 96))
    (hmem16_s : memW s (w_out.toNat + 16) = 0)
    (hMA_s : ∃ S_s Nd_s,
      R10Shards.Fast_GbodyC17ToC21.MsgReadyAt s S_s Nd_s ∧
      IvlsDisj [(w_out.toNat, 96)] (worldOwned s S_s Nd_s)) :
    let out1 := evaluateHOLFiniteState s
      (.call (some ((some (.local, ofString "frame")), none)) fname [.var .local (ofString "msg")])
    let out := match out1.1 with
      | none => evaluateHOLFiniteState { out1.2 with locals := restL out1.2.locals } tail
      | some _ => (out1.1, { out1.2 with locals := restL out1.2.locals })
    Resumes out.1 →
      PmcMarksPost entry out.1 out.2 := by
  dsimp only
  intro hres
  rw [evaluateHOLFiniteState_call] at hres ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "msg")] with _ | vals
  · simp only [hargs] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [hargs] at hres ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body_c, callee_c, ret_c⟩
    · simp only [hl] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hl] at hres ⊢
      by_cases hclk : s.clock = 0
      · simp only [hclk, ↓reduceIte] at hres
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      · simp only [hclk, ↓reduceIte] at hres ⊢
        obtain ⟨b_rt, r_rt, hlook_fn⟩ := hlook_rt
        have hpc_msg : callee_c.lookup (ofString "msg") = s.locals.lookup (ofString "msg") :=
          callee_param_one s fname (ofString "msg") .one b_rt r_rt
            (by rw [hcode]; exact hlook_fn) vals body_c callee_c ret_c hargs hl
        let ent := callEntryStateHOLFinite s callee_c
        have hM_ent : MsgReady ent :=
          localsOnly_msgReady s callee_c (s.clock - 1)
            (fun n hn => by simp at hn; subst hn; exact hpc_msg) hM_s
        have hmeta_c := (evaluateHOLFiniteState_metadata ent body_c).1
        rcases hrun_c : evaluateHOLFiniteState ent body_c with ⟨res_c, post_c⟩
        dsimp only [ent] at hrun_c hmeta_c
        rw [hrun_c] at hmeta_c
        dsimp only at hmeta_c
        simp only [hrun_c] at hres ⊢
        have hnt_c : (evaluateHOLFiniteState ent body_c).1 ≠ some .timeOut := by
          dsimp only [ent]; rw [hrun_c]
          rintro rfl
          exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        have hspec := FunSpec.at_lookup hcall_spec s hcode vals body_c callee_c ret_c hl hM_ent hnt_c
        dsimp only [ent] at hspec
        rw [hrun_c] at hspec
        dsimp only at hspec
        obtain ⟨_, _, hMA_en⟩ := R10Shards.Fast_GbodyC17ToC21.msgReadyAt_of_msgReady hM0
        have hm8_en : locN entry "msg" % 8 = 0 := hMA_en.2.2.2.2.2.2.2.2.2.1
        have hm_in_en : Inside (locN entry "msg", 176) sourceBase (globN entry "heap_ptr") :=
          hMA_en.2.2.2.2.2.2.2.2.2.2.1
        have hm_fix_en : ∀ j ∈ fixedObjects entry, Disj (locN entry "msg", 176) j := by
          intro j hj
          apply hMA_en.2.2.2.2.2.2.2.2.2.2.2.1 j
          unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hj)))
        have hmsg_loc_s : locN s "msg" = locN entry "msg" := by simp [locN, hs_msg]
        have hmsg_loc_ent : locN ent "msg" = locN s "msg" := by
          simp [ent, callEntryStateHOLFinite, locN, hpc_msg]
        have hR1_z : ∀ j ∈ bufRegions pmcBufs entry ++ [(globN entry "heap_ptr", globN s "heap_ptr" - globN entry "heap_ptr")],
            j.2 = 0 → j.1 % 8 = 0 := by
          intro j hj hz
          rcases List.mem_append.1 hj with hj_buf | hj_fr
          · exact pmcRegions_zero_aligned hm8_en j
              (by rw [pmcRegions_eq_bufRegions]; exact List.mem_cons_of_mem _ hj_buf) hz
          · simp only [List.mem_singleton] at hj_fr; subst hj_fr
            exact hM0.1.2.2.2.2.2.2.1
        have hR1_sub : ∀ j ∈ bufRegions pmcBufs entry ++ [(globN entry "heap_ptr", globN s "heap_ptr" - globN entry "heap_ptr")],
            j ∈ bufRegions pmcBufs entry ∨ Inside j (globN entry "heap_ptr") (globN s "heap_ptr") := by
          intro j hj
          rcases List.mem_append.1 hj with hj_buf | hj_fr
          · exact Or.inl hj_buf
          · simp only [List.mem_singleton] at hj_fr; subst hj_fr
            exact Or.inr ⟨le_rfl, by have := hws_s.2.1; omega⟩
        obtain ⟨S_s, Nd_s, hMAs, hout_ow_s⟩ := hMA_s
        have htabs_ent : pmcTables ent = pmcTables s := by
          unfold pmcTables; rw [hmsg_loc_ent]; rfl
        have hreg_ent : pmcRegions ent = pmcRegions s :=
          pmcRegions_eq_of_msg_locals hmsg_loc_ent
        have hT_ent0 : ∀ t ∈ pmcTables ent, t ∈ S_s := by
          rw [htabs_ent]
          intro t ht
          simp only [pmcTables, List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact hMAs.2.2.1
          · exact hMAs.2.2.2.1
        have hD_ent0 : IvlsDisj (pmcRegions ent) (worldTypedIvls ent S_s Nd_s) := by
          have hwti : worldTypedIvls ent S_s Nd_s = worldTypedIvls s S_s Nd_s := rfl
          rw [hreg_ent, hwti]
          exact pmcRegions_disj_of_msgReady hMAs.2.1 hMAs.2.2.2.2.2.2.2.2.2.2.2.1
        cases res_c with
        | none =>
          exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | some br_c =>
          cases br_c with
          | timeOut => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | error => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | «break» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | «continue» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | finalFfi _ => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | exception eid eval =>
            dsimp only at hres ⊢
            have hstep_ex := hspec hres
            obtain ⟨S_p0, Nd_p0, _, _, _, _, hQ0⟩ :=
              hstep_ex.2.2.2.2 S_s Nd_s
                ((R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals _ _ _ _ _).2 hMAs.2.1)
                hT_ent0 hD_ent0
            have hmarks0 := (hQ_marks _ _ _ _ _ hQ0).2
            have hfmp_c : globN entry "frame_mem_ptr" ≤ globN post_c "frame_mem_ptr" := by
              rw [← hfmp_s]; exact hmarks0.1
            have hsp_c : globN post_c "scratch_ptr" ≤ globN entry "scratch_ptr" :=
              le_trans hmarks0.2.1 hsp_s
            exact pmcMarksPost_not_returned (by intro _ h; simp at h) hfmp_c hsp_c
          | returned val_c =>
            dsimp only at hres ⊢
            by_cases hsh1 : shapeEqHOL (shapeOfHOLExact val_c) ret_c = true
            · simp only [hsh1, ↓reduceIte] at hres ⊢
              simp only [isValidValueHOLExact, lookupKvarHOLExact, hs_fr] at hres ⊢
              by_cases hsh2 : shapeEqHOL (shapeOfHOLExact val_c) (shapeOfHOLExact (.val (.word 0#64))) = true
              · simp only [hsh2, ↓reduceIte, setKvarHOLFinite] at hres ⊢
                have hstep_ret := hspec (Or.inl ⟨val_c, rfl⟩)
                obtain ⟨S_p0, Nd_p0, _, hWT_p0, _, _, hQ0⟩ :=
                  hstep_ret.2.2.2.2 S_s Nd_s
                    ((R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals _ _ _ _ _).2 hMAs.2.1)
                    hT_ent0 hD_ent0
                obtain ⟨⟨hret0, hstrong0⟩, hmarks0⟩ := hQ_marks _ _ _ _ _ hQ0
                obtain ⟨w_fr, hvc_eq, hw_fr_ok0, _, hlok0⟩ := hret0 val_c rfl
                obtain ⟨w_fr', hvc_eq', hin_fr0, _, hlive0, hdisj_out0⟩ := hstrong0 val_c rfl
                rw [hvc_eq] at hvc_eq'; injection hvc_eq' with hvc_eq''; injection hvc_eq'' with hw_fr_eq; subst hw_fr_eq
                subst hvc_eq
                obtain ⟨w_fr_m, hvc_m, h208_le0, h224_eq0, h224_le0, h208_8, h128_le⟩ :=
                  hmarks0.2.2 (.val (.word w_fr)) rfl
                injection hvc_m with hvc_m'; injection hvc_m' with hw_m; subst hw_m
                set s_next := setVarHOLFinite (ofString "frame") (.val (.word w_fr))
                  { post_c with locals := s.locals, clock := post_c.clock }
                have hs_next_code : s_next.code = originalRuntimeCode := hmeta_c.trans hcode
                have hs_next_out : s_next.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
                  simp [s_next, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hs_out,
                    show ofString "frame" ≠ ofString "out" by decide]
                have hs_next_fr : s_next.locals.lookup (ofString "frame") = some (.val (.word w_fr)) := by
                  simp [s_next, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
                have hstep_s_next : WorldStepIn pmcTables pmcRegions pmcGlobals pmcKeep
                    (fun _ _ post S' Nd' => PmcLogsLiveOwned post S' Nd' (memW post (w_fr.toNat + 88)))
                    s none s_next := by
                  obtain ⟨hAp, hhp, hG, hK, hW⟩ := hstep_ret
                  refine ⟨localsFree_arenaReady post_c s_next.locals post_c.clock hAp, hhp, hG,
                    pmc_recordsKept_with_locals hmsg_loc_ent hK,
                    fun S_x Nd_x hWT_x hT_x hD_x => ?_⟩
                  have hT_ent : ∀ t ∈ pmcTables ent, t ∈ S_x := by rwa [htabs_ent]
                  have hD_ent : IvlsDisj (pmcRegions ent) (worldTypedIvls ent S_x Nd_x) := by
                    have hwti : worldTypedIvls ent S_x Nd_x = worldTypedIvls s S_x Nd_x := rfl
                    rwa [hreg_ent, hwti]
                  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hQ_x⟩ :=
                    hW S_x Nd_x ((R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals _ _ _ _ _).2 hWT_x) hT_ent hD_ent
                  obtain ⟨⟨hret_x, hstrong_x⟩, _⟩ := hQ_marks _ _ _ _ _ hQ_x
                  obtain ⟨w_fr_x, hvc_x, _, _, hlive_x, _⟩ := hstrong_x (.val (.word w_fr)) rfl
                  injection hvc_x with hvc_x'; injection hvc_x' with hw_x; subst hw_x
                  obtain ⟨w_fr_y, hvc_y, _, _, hlok_x⟩ := hret_x (.val (.word w_fr)) rfl
                  injection hvc_y with hvc_y'; injection hvc_y' with hw_y; subst hw_y
                  exact ⟨S', Nd', hsub,
                    (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals post_c s_next.locals post_c.clock S' Nd').2 hWT',
                    hOG, pmc_frameOutside_with_locals hmsg_loc_ent hFO,
                    pmcLogsLiveOwned_congr_live hAp.2 hlok_x hlive_x rfl rfl
                      (fun a => a) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)⟩
                have hws_en_next := worldStepIn_pmc_trans_prefix (w_out := w_out)
                  (Q := fun _ _ post S' Nd' => PmcLogsLiveOwned post S' Nd' (memW post (w_fr.toNat + 88)))
                  (Q_out := fun _ _ post S' Nd' =>
                    IvlsDisj [(w_out.toNat, 96)] (worldOwned post S' Nd') ∧
                    PmcLogsLiveOwned post S' Nd' (memW post (w_fr.toNat + 88)))
                  hmsg_loc_s hm8_en hm_in_en hm_fix_en hM0.1 (msgReady_worldOK entry hM0)
                  hR1_z hR1_sub hw_out8 hw_in_s (fun _ _ h => h) hws_s hsp_s hstep_s_next
                  (fun _ _ hout_ow3 _ hlive3 => ⟨hout_ow3, hlive3⟩)
                have hout_in2 : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
                  ⟨le_trans hM0.1.2.1 hw_in_s.1, hw_in_s.2⟩
                have hout_disj_R2 : ∀ j ∈ pmcRegions s, Disj (w_out.toNat, 96) j := by
                  rw [pmcRegions_eq_bufRegions]
                  intro j hj
                  rcases List.mem_cons.1 hj with rfl | hj_buf
                  · rw [hmsg_loc_s]
                    exact Or.inr (Or.inr (Or.inr (Nat.le_trans hm_in_en.2 hw_in_s.1)))
                  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj_buf
                    obtain ⟨sz, hgb, _, hle⟩ := validBufList_pmcBufs p hp
                    have hfix_p : bufferRegion s (p.1, sz) ∈ fixedObjects s := by
                      unfold fixedObjects
                      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
                      exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
                    have hd_sz := hout_ow_s (w_out.toNat, 96) (by simp) _
                      (by unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix_p))))
                    by_cases h0 : globN s p.1 = 0
                    · simp [bufferRegion, h0]; exact disj_zero_right _
                    · simp only [bufferRegion, h0, ↓reduceIte] at hd_sz ⊢
                      exact disj_of_inside_right (j' := (globN s p.1, sz))
                        ⟨le_rfl, by dsimp; omega⟩ hd_sz
                obtain ⟨_, _, _, _, hOG_at, hFO_at, _⟩ :=
                  hstep_s_next.2.2.2.2 S_s Nd_s hMAs.2.1
                    (by
                      intro t ht
                      simp only [pmcTables, List.mem_cons, List.not_mem_nil, or_false] at ht
                      rcases ht with rfl | rfl
                      · exact hMAs.2.2.1
                      · exact hMAs.2.2.2.1)
                    (pmcRegions_disj_of_msgReady hMAs.2.1 hMAs.2.2.2.2.2.2.2.2.2.2.2.1)
                obtain ⟨_, _, hout_u_s_next⟩ :=
                  heap_ivl_survives_step (b := (w_out.toNat, 96))
                    hM_s.1.2 hstep_s_next.2.1 hOG_at hFO_at
                    (worldOwned_zero_aligned hMAs.2.1)
                    (pmcRegions_zero_aligned (by rw [hmsg_loc_s]; exact hm8_en))
                    hw_out8 (by dsimp) hout_in2
                    (fun j hj => hout_ow_s (w_out.toNat, 96) (by simp) j hj)
                    hout_disj_R2
                have hw_hi_s : w_out.toNat + 96 ≤ 2 ^ 64 :=
                  (ivl_allocated_bound hM_s.1.2 (Or.inl hout_in2)).2
                have hmem16_next : memW s_next (w_out.toNat + 16) = 0 := by
                  rw [memW_eq_of_ivlUnhit hout_u_s_next (by omega) hw_hi_s ⟨by dsimp; omega, by dsimp; omega⟩]
                  exact hmem16_s
                have hw_in_next : Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s_next "heap_ptr") :=
                  ⟨hw_in_s.1, le_trans hw_in_s.2 hstep_s_next.2.1⟩
                have hw_ok_next : WordsOK s_next (w_out.toNat, 96) :=
                  wordsOK_transfer hM_s.1.1 hws_en_next.1.1 hw_ok_s
                have hw_fr_ok_next : WordsOK s_next (w_fr.toNat, 280) :=
                  wordsOK_transfer hstep_ret.1.1 hws_en_next.1.1 hw_fr_ok0
                have hlok_next : LogsListOK s_next (memW s_next (w_fr.toNat + 88)) :=
                  pmc_logsListOK_congr_live hstep_ret.1.2 hstep_ret.1.1 hws_en_next.1.1 le_rfl hlok0
                    (fun a => a) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)
                have hdisj_logs_out : memW s_next (w_fr.toNat + 88) ≠ 0 →
                    Disj (memW s_next (w_fr.toNat + 88), 24) (w_out.toNat, 96) ∧
                    Disj (memW s_next (memW s_next (w_fr.toNat + 88)),
                      8 * memW s_next (memW s_next (w_fr.toNat + 88) + 8)) (w_out.toNat, 96) ∧
                    ∀ i, i < memW s_next (memW s_next (w_fr.toNat + 88) + 8) →
                      Disj (memW s_next (memW s_next (memW s_next (w_fr.toNat + 88)) + 8 * i), 40) (w_out.toNat, 96) := by
                  intro hnz
                  have hhp_ent_s : globN ent "heap_ptr" = globN s "heap_ptr" := rfl
                  have hmem_s_next_eq : ∀ a : Nat, memW s_next a = memW post_c a := fun _ => rfl
                  simp only [hmem_s_next_eq] at hnz ⊢
                  obtain ⟨hd_hd, hd_arr, hd_ent⟩ := hdisj_out0 hnz
                  have hsep : heapLimit ≤ scratchStart := by decide
                  have hhp_lim : globN post_c "heap_ptr" ≤ heapLimit := hstep_ret.1.2.2.1
                  have hsc_lo : scratchStart ≤ globN post_c "scratch_ptr" :=
                    le_trans hstep_ret.1.2.2.2.1 hstep_ret.1.2.2.2.2.1
                  have hw_hi_s_hp : w_out.toNat + 96 ≤ globN s "heap_ptr" := hw_in_s.2
                  have hhp_s_le : globN s "heap_ptr" ≤ globN post_c "heap_ptr" := hstep_ret.2.1
                  refine ⟨?_, ?_, ?_⟩
                  · rcases hd_hd with hin_sc | hin_hp
                    · exact Or.inr (Or.inr (Or.inr (by unfold Inside at hin_sc; dsimp only at *; omega)))
                    · rw [hhp_ent_s] at hin_hp
                      exact Or.inr (Or.inr (Or.inr (le_trans hw_hi_s_hp hin_hp.1)))
                  · rcases hd_arr with hin_sc | hin_hp
                    · exact Or.inr (Or.inr (Or.inr (by unfold Inside at hin_sc; dsimp only at *; omega)))
                    · rw [hhp_ent_s] at hin_hp
                      exact Or.inr (Or.inr (Or.inr (le_trans hw_hi_s_hp hin_hp.1)))
                  · intro i hi
                    have hin_hp := hd_ent i hi
                    rw [hhp_ent_s] at hin_hp
                    exact Or.inr (Or.inr (Or.inr (le_trans hw_hi_s_hp hin_hp.1)))
                have hfmp_next : globN entry "frame_mem_ptr" ≤ globN s_next "frame_mem_ptr" := by
                  rw [← hfmp_s]; exact hmarks0.1
                have hsp_next : globN s_next "scratch_ptr" ≤ globN entry "scratch_ptr" :=
                  le_trans hmarks0.2.1 hsp_s
                have h208_le_en : memW s_next (w_fr.toNat + 208) ≤ globN entry "scratch_ptr" :=
                  le_trans h208_le0 hsp_s
                have h224_eq_en : memW s_next (w_fr.toNat + 224) = globN entry "frame_mem_ptr" :=
                  h224_eq0.trans hfmp_s
                have h208_ex_en : memW entry (locN entry "msg" + 24) ≠ 0 →
                    memW s_next (w_fr.toNat + 208) = globN entry "scratch_ptr" := by
                  intro hnz24
                  obtain ⟨w_e, hvc_e, h208_eq0⟩ := hQ_exact hnz24 _ _ _ _ _ hQ0 (.val (.word w_fr)) rfl
                  injection hvc_e with hvc_e'; injection hvc_e' with hw_e; subst hw_e
                  exact h208_eq0.trans (hsp_s_exact hnz24)
                have hp2 : PmcMarksA2 entry { s_next with locals := restL s_next.locals } :=
                  pmcMarksA2_with_locals (hrest_out s_next.locals) (hrest_fr s_next.locals)
                    ⟨⟨hM0, w_out, w_fr, hws_en_next, hs_next_out, hs_next_fr, hw_out8,
                      hw_in_next, hw_ok_next, hmem16_next, hw_fr_ok_next, hin_fr0, hlok_next, hdisj_logs_out⟩,
                     hfmp_next, hsp_next, w_out, w_fr, hs_next_out, hs_next_fr,
                     h128_le, h208_le_en, h224_eq_en, h224_le0, h208_8, h208_ex_en⟩
                exact htail { s_next with locals := restL s_next.locals } hs_next_code hp2 hres
              · simp only [hsh2, Bool.false_eq_true, ↓reduceIte] at hres
                exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
            · simp only [hsh1, ↓reduceIte] at hres
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

theorem pmcMarksDispatch_cut
    (hpm : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultMarksExact (ofString "process_message"))
    (hpcm : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultMarks (ofString "process_create_message")) :
    PmcMarksCut pmcDispatch PmcMarksA1 PmcMarksA2 := by
  intro F entry tail htail s hcode hp1m
  obtain ⟨hp1, hfmp_s, hsp_s_eq, hm24_eq, w_out_m, hs_out_m, h48_s, h80_s, h88_s⟩ := hp1m
  obtain ⟨hM0, hM_s, hs_msg, hsp_s, w_out, hws_s, hs_out, hs_fr, hw_out8, hw_in_s, hw_ok_s, hmem16_s,
    S_s, Nd_s, hMAs, hout_ow_s⟩ := hp1
  rw [hs_out] at hs_out_m; injection hs_out_m with hs_out_m'; injection hs_out_m' with hw_out_eq
  injection hw_out_eq with hw_out_eq
  subst w_out_m
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
  unfold PmcMarksRun
  intro hres
  unfold pmcDispatch pmcCode at hres ⊢
  simp only [sourceFunctionEntry, Guest.Software.guestFn_process_message_call,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil,
    R13Shards.spineAt, R13Shards.spinePlug] at hres ⊢
  have hload24 := pmc_load_local_off hs_msg_w hw_msg_ok_s hw_msg_hi_s (by decide) (show 24 < 176 by decide)
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres ⊢
  have hcond24_ex : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.load .one (.op .add [.var .local (ofString "msg"), .const 24#64])) (.const 0#64)) =
      some (.val (.word (if BitVec.ofNat 64 (memW s (w_msg.toNat + 24)) = 0#64 then 1#64 else 0#64))) := by
    have hl24' : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "msg"), .const 24#64])) =
        some (.val (.word (BitVec.ofNat 64 (memW s (w_msg.toNat + 24))))) := hload24
    unfold evalHOLExact
    rw [hl24']
    simp [evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcond24_ex] at hres ⊢
  dsimp only at hres ⊢
  by_cases h24_eq : BitVec.ofNat 64 (memW s (w_msg.toNat + 24)) = 0#64
  · rw [if_pos h24_eq, if_neg (show ¬ ((1#64 : BitVec 64) = 0) by decide)] at hres ⊢
    have hm24_en_zero : memW entry (locN entry "msg" + 24) = 0 := by
      have hlt24 : memW s (w_msg.toNat + 24) < 2 ^ 64 := by
        unfold memW; cases s.memory (BitVec.ofNat 64 (w_msg.toNat + 24)) with
        | word w => exact w.isLt
      have hz_s : memW s (w_msg.toNat + 24) = 0 := by
        have := congrArg BitVec.toNat h24_eq
        simp only [BitVec.toNat_ofNat, BitVec.toNat_zero] at this
        rw [Nat.mod_eq_of_lt hlt24] at this
        exact this
      rw [← hm24_eq, ← hw_msg_nat]
      exact hz_s
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hres ⊢
    have hload32 := pmc_load_local_off hs_msg_w hw_msg_ok_s hw_msg_hi_s (by decide) (show 32 < 176 by decide)
    have hargs_ad : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.load .one (.op .add [.var .local (ofString "msg"), .const 32#64])] =
        some [.val (.word (BitVec.ofNat 64 (memW s (w_msg.toNat + 32))))] := by
      rw [evalListHOLFinite_eq_toExact]
      change @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        [.load .one (.op .add [.var .local (ofString "msg"), .const (BitVec.ofNat 64 32)])] = _
      simp [evalListHOLExact, hload32]
    simp only [hargs_ad] at hres ⊢
    set v_ad := ValueHOL.val (.word (BitVec.ofNat 64 (memW s (w_msg.toNat + 32))))
    rcases hl_ad : lookupCodeHOLFinite s.code.lookup (ofString "account_deployable") [v_ad]
        with _ | ⟨body_ad, callee_ad, ret_ad⟩
    · simp only [hl_ad] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hl_ad] at hres ⊢
      by_cases hclk_ad : s.clock = 0
      · simp only [hclk_ad, ↓reduceIte] at hres
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      · simp only [hclk_ad, ↓reduceIte] at hres ⊢
        let ent_ad := callEntryStateHOLFinite s callee_ad
        have hmeta_ad := (evaluateHOLFiniteState_metadata ent_ad body_ad).1
        rcases hrun_ad : evaluateHOLFiniteState ent_ad body_ad with ⟨res_ad, post_ad⟩
        dsimp only [ent_ad] at hrun_ad hmeta_ad
        rw [hrun_ad] at hmeta_ad
        dsimp only at hmeta_ad
        simp only [hrun_ad] at hres ⊢
        have hnt_ad : (evaluateHOLFiniteState ent_ad body_ad).1 ≠ some .timeOut := by
          dsimp only [ent_ad]; rw [hrun_ad]
          rintro rfl
          exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        have hspec_ad := wkSc_account_deployable.at_lookup s hcode [v_ad] body_ad callee_ad ret_ad hl_ad
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
            dsimp only at hres ⊢
            have hws_ad_ex := WorldStepSc.from_entry (s := s) (r' := some (.exception eid eval))
              (L := HolFiniteMapExact.empty) (k := post_ad.clock) (hspec_ad hres)
            have hfmp_ad : globN entry "frame_mem_ptr" ≤ globN (emptyLocalsHOLFinite post_ad) "frame_mem_ptr" := by
              have hfg := hws_ad_ex.1.2.2.1 (ofString "frame_mem_ptr") (by decide)
              have heq_fmp : globN (emptyLocalsHOLFinite post_ad) "frame_mem_ptr" = globN s "frame_mem_ptr" := by
                unfold globN; rw [hfg]; rfl
              rw [heq_fmp, hfmp_s]
            have hsp_ad : globN (emptyLocalsHOLFinite post_ad) "scratch_ptr" ≤ globN entry "scratch_ptr" :=
              le_trans hws_ad_ex.2 hsp_s
            exact pmcMarksPost_not_returned (by intro _ h; simp at h) hfmp_ad hsp_ad
          | returned val_ad =>
            dsimp only at hres ⊢
            have hret_ad_eq : ret_ad = .one :=
              lookupCodeHOLFinite_installed_return s (ofString "account_deployable") _ _ body_ad .one ret_ad
                [v_ad] callee_ad (by rw [hcode]; exact lookup_account_deployable) hl_ad
            subst hret_ad_eq
            by_cases hsh_ad : (shapeEqHOL (shapeOfHOLExact val_ad) .one &&
                shapeEqHOL (shapeOfHOLExact val_ad) .one) = true
            · simp only [hsh_ad, ↓reduceIte] at hres ⊢
              have hsh1_ad : shapeEqHOL (shapeOfHOLExact val_ad) .one = true :=
                ((Bool.and_eq_true _ _).mp hsh_ad).1
              obtain ⟨w_dep, rfl⟩ : ∃ w : BitVec 64, val_ad = .val (.word w) := by
                rcases val_ad with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
                · exact ⟨w, rfl⟩
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh1_ad
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh1_ad
              set s_dep := setVarHOLFinite (ofString "dep") (.val (.word w_dep)) { post_ad with locals := s.locals }
              have hws_ad_raw := hspec_ad (Or.inl ⟨.val (.word w_dep), rfl⟩)
              have hws_ad_caller : WorldStepSc (bufRegions wsAcctBufs) ["heap_ptr", "scratch_ptr"] stdKeep
                  NoExtra s (some (.returned (.val (.word w_dep)))) post_ad :=
                WorldStepSc.of_pre_locals_clock hws_ad_raw
              have hws_ad_s_dep_sc : WorldStepSc (bufRegions pmcBufs) ["heap_ptr", "scratch_ptr"] stdKeep
                  NoExtra s none s_dep :=
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
              have hfmp_dep : globN s_dep "frame_mem_ptr" = globN entry "frame_mem_ptr" := by
                have hfg := hws_ad_s_dep.2.2.1 (ofString "frame_mem_ptr") (by decide)
                have heq_fmp : globN s_dep "frame_mem_ptr" = globN s "frame_mem_ptr" := by
                  unfold globN; rw [hfg]
                exact heq_fmp.trans hfmp_s
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
                obtain ⟨sz, hgb, hnr, hle⟩ := validBufList_wsAcctBufs p hp
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
              obtain ⟨S0_dep, Nd_dep, hMA_dep_pre, _, hfp_ad⟩ :=
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
                  ["heap_ptr", "scratch_ptr"] stdKeep
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
              have hmem48_dep : memW s_dep (w_out.toNat + 48) = 0 := by
                change memW post_ad (w_out.toNat + 48) = 0
                rw [memW_eq_of_ivlUnhit hout_u_ad (by omega) hw_hi_s ⟨by dsimp; omega, by dsimp; omega⟩]
                exact h48_s
              have hmem80_dep : memW s_dep (w_out.toNat + 80) = 0 := by
                change memW post_ad (w_out.toNat + 80) = 0
                rw [memW_eq_of_ivlUnhit hout_u_ad (by omega) hw_hi_s ⟨by dsimp; omega, by dsimp; omega⟩]
                exact h80_s
              have hw_in_dep : Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s_dep "heap_ptr") :=
                ⟨hw_in_s.1, le_trans hw_in_s.2 hws_ad_s_dep.2.1⟩
              have hw_ok_dep : WordsOK s_dep (w_out.toNat, 96) :=
                wordsOK_transfer hM_s.1.1 hM_dep.1.1 hw_ok_s
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres ⊢
              have hcond_dep_ex : @evalHOLExact 64 F _ s_dep.toExact (fun a => Classical.propDecidable (s_dep.memaddrs a))
                  (.cmp .equal (.var .local (ofString "dep")) (.const 0#64)) =
                  some (.val (.word (if w_dep = 0#64 then 1#64 else 0#64))) := by
                simp [evalHOLExact, hs_dep_dep, Compiler.Encoders.Asm.wordCmpHOL]
              rw [hcond_dep_ex] at hres ⊢
              dsimp only at hres ⊢
              by_cases hdep0 : w_dep = 0#64
              · rw [if_pos hdep0, if_neg (show ¬ ((1#64 : BitVec 64) = 0) by decide)] at hres ⊢
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
                obtain ⟨hev4, hsr4⟩ := pmcStoreReady_zero_store (off := 40)
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
                rw [hblk_ev] at hres ⊢
                dsimp only at hres ⊢
                have h48_st4 : memW st4 (w_out.toNat + 48) = 0 := by
                  have h4 : memW st4 (w_out.toNat + 48) = memW st3 (w_out.toNat + 48) :=
                    pmc_memW_updW_ne st3 (w_out.toNat + 40) (w_out.toNat + 48) _ (by omega) (by omega) (by omega)
                  have h3 : memW st3 (w_out.toNat + 48) = memW st2 (w_out.toNat + 48) :=
                    pmc_memW_updW_ne st2 (w_out.toNat + 64) (w_out.toNat + 48) _ (by omega) (by omega) (by omega)
                  have h2 : memW st2 (w_out.toNat + 48) = memW st1 (w_out.toNat + 48) :=
                    pmc_memW_updW_ne st1 (w_out.toNat + 56) (w_out.toNat + 48) _ (by omega) (by omega) (by omega)
                  have h1 : memW st1 (w_out.toNat + 48) = memW s_dep (w_out.toNat + 48) :=
                    pmc_memW_updW_ne s_dep (w_out.toNat + 32) (w_out.toNat + 48) _ (by omega) (by omega) (by omega)
                  rw [h4, h3, h2, h1]; exact hmem48_dep
                have h80_st4 : memW st4 (w_out.toNat + 80) = 0 := by
                  have h4 : memW st4 (w_out.toNat + 80) = memW st3 (w_out.toNat + 80) :=
                    pmc_memW_updW_ne st3 (w_out.toNat + 40) (w_out.toNat + 80) _ (by omega) (by omega) (by omega)
                  have h3 : memW st3 (w_out.toNat + 80) = memW st2 (w_out.toNat + 80) :=
                    pmc_memW_updW_ne st2 (w_out.toNat + 64) (w_out.toNat + 80) _ (by omega) (by omega) (by omega)
                  have h2 : memW st2 (w_out.toNat + 80) = memW st1 (w_out.toNat + 80) :=
                    pmc_memW_updW_ne st1 (w_out.toNat + 56) (w_out.toNat + 80) _ (by omega) (by omega) (by omega)
                  have h1 : memW st1 (w_out.toNat + 80) = memW s_dep (w_out.toNat + 80) :=
                    pmc_memW_updW_ne s_dep (w_out.toNat + 32) (w_out.toNat + 80) _ (by omega) (by omega) (by omega)
                  rw [h4, h3, h2, h1]; exact hmem80_dep
                apply pmcMarksPost_with_locals_clock _ (emptyLocalsHOLFinite st4).clock
                refine ⟨?_, hsp_dep, fun v hv => ?_⟩
                · change globN entry "frame_mem_ptr" ≤ globN s_dep "frame_mem_ptr"
                  rw [hfmp_dep]
                · injection hv with hv'; injection hv' with hv''; subst v
                  refine ⟨w_out, rfl, hw_in_dep, ?_, fun hnz80 => absurd h80_st4 hnz80⟩
                  change memW st4 (w_out.toNat + 48) ≤ scratchEnd
                  rw [h48_st4]; exact Nat.zero_le _
              · rw [if_neg hdep0, if_pos (show (0#64 : BitVec 64) = 0 by decide)] at hres ⊢
                rw [evaluateHOLFiniteState_skip] at hres ⊢
                dsimp only at hres ⊢
                have hcall_pcm := pmcMarks_call_frame_callee
                  (restL := fun m => HolFiniteMapExact.resVarEq m (ofString "dep", s.locals.lookup (ofString "dep")))
                  hpcm (fun _ _ _ _ _ h => h)
                  (fun hnz => absurd hm24_en_zero hnz)
                  ⟨_, _, R10Shards.Fast_GbodyC17ToC21.lookup_process_create_message⟩
                  (fun m => by rw [PanRunBounded.resVarEq_lookup, if_neg (by decide)])
                  (fun m => by rw [PanRunBounded.resVarEq_lookup, if_neg (by decide)])
                  htail hs_dep_code hM0 hM_dep hs_dep_msg hfmp_dep hsp_dep
                  (fun hnz => absurd hm24_en_zero hnz)
                  hws_en_dep hs_dep_out hs_dep_fr
                  hw_out8 hw_in_dep hw_ok_dep hmem16_dep ⟨_, _, hMA_dep2, hout_ow_dep_at⟩
                dsimp only at hcall_pcm hres ⊢
                rcases hrun_pcm : evaluateHOLFiniteState s_dep
                    (.call (some ((some (.local, ofString "frame")), none))
                      (ofString "process_create_message") [.var .local (ofString "msg")]) with ⟨res_pcm, post_pcm⟩
                simp only [hrun_pcm] at hcall_pcm hres ⊢
                cases res_pcm with
                | none => exact hcall_pcm hres
                | some v => exact hcall_pcm hres
            · simp only [hsh_ad, Bool.false_eq_true, ↓reduceIte] at hres
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · rw [if_neg h24_eq, if_pos (show (0#64 : BitVec 64) = 0 by decide)] at hres ⊢
    have hcall_pm := pmcMarks_call_frame_callee (restL := fun m => m) hpm
      (fun _ _ _ _ _ h => h.1)
      (fun _ _ _ _ _ _ _ h => h.2)
      ⟨_, _, R10Shards.Fast_GbodyC17ToC21.lookup_process_message⟩
      (fun _ => rfl) (fun _ => rfl)
      htail hcode hM0 hM_s hs_msg hfmp_s hsp_s (fun _ => hsp_s_eq) hws_s hs_out hs_fr
      hw_out8 hw_in_s hw_ok_s hmem16_s ⟨S_s, Nd_s, hMAs, hout_ow_s⟩
    dsimp only at hcall_pm hres ⊢
    rcases hrun_pm : evaluateHOLFiniteState s
        (.call (some ((some (.local, ofString "frame")), none))
          (ofString "process_message") [.var .local (ofString "msg")]) with ⟨res_pm, post_pm⟩
    simp only [hrun_pm] at hcall_pm hres ⊢
    have hpost_id : ({ post_pm with locals := post_pm.locals } : PanSemStateFiniteExact 64 F) = post_pm := by
      cases post_pm; rfl
    cases res_pm with
    | none =>
      simp only [hpost_id] at hcall_pm
      exact hcall_pm hres
    | some v =>
      simp only [hpost_id] at hcall_pm
      exact hcall_pm hres

def PmcMarksPackState {F : Type}
    (entry s : PanSemStateFiniteExact 64 F)
    (w_out w_fr : BitVec 64) (logs : Nat) (z : Bool)
    ( has48 has80 has88 : Bool ) : Prop :=
  PmcPackState entry s w_out w_fr logs z ∧
  globN entry "frame_mem_ptr" ≤ globN s "frame_mem_ptr" ∧
  globN s "scratch_ptr" ≤ globN entry "scratch_ptr" ∧
  memW s (w_fr.toNat + 128) ≤ scratchEnd ∧
  memW s (w_fr.toNat + 208) ≤ globN entry "scratch_ptr" ∧
  memW s (w_fr.toNat + 224) = globN entry "frame_mem_ptr" ∧
  memW s (w_fr.toNat + 224) ≤ memW s (w_fr.toNat + 208) ∧
  memW s (w_fr.toNat + 208) % 8 = 0 ∧
  (memW entry (locN entry "msg" + 24) ≠ 0 →
    memW s (w_fr.toNat + 208) = globN entry "scratch_ptr") ∧
  (has48 = true → memW s (w_out.toNat + 48) = memW s (w_fr.toNat + 128)) ∧
  (has80 = true → memW s (w_out.toNat + 80) = memW s (w_fr.toNat + 208)) ∧
  (has88 = true → memW s (w_out.toNat + 88) = memW s (w_fr.toNat + 224))

theorem pmcMarksPackState_with_locals_clock {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64} {logs : Nat} {z has48 has80 has88 : Bool}
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hL_out : L.lookup (ofString "out") = some (.val (.word w_out)))
    (hL_fr : L.lookup (ofString "frame") = some (.val (.word w_fr)))
    (hmps : PmcMarksPackState entry s w_out w_fr logs z has48 has80 has88) :
    PmcMarksPackState entry { s with locals := L, clock := k } w_out w_fr logs z has48 has80 has88 := by
  obtain ⟨hps, hfmp, hsp, h128, h208, h224, hle, h8, hex, h48, h80, h88⟩ := hmps
  exact ⟨pmcPackState_with_locals_clock L k hL_out hL_fr hps,
    hfmp, hsp, h128, h208, h224, hle, h8, hex, h48, h80, h88⟩

theorem pmcMarksPackState_store_other {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64} {logs off : Nat} {z has48 has80 has88 : Bool}
    {valExp : ExpHOL 64} {w_val : BitVec 64}
    (hmps : PmcMarksPackState entry s w_out w_fr logs z has48 has80 has88)
    (hoff8 : off % 8 = 0) (hoff_lt : off < 96) (hoff_ne16 : off ≠ 16)
    (hoff_ne48 : off ≠ 48) (hoff_ne80 : off ≠ 80) (hoff_ne88 : off ≠ 88)
    (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some (.val (.word w_val))) :
    evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 off)]) valExp) =
      (none, { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val }) ∧
    PmcMarksPackState entry
      { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val }
      w_out w_fr logs z has48 has80 has88 := by
  obtain ⟨hps, hfmp, hsp, h128, h208, h224, hle, h8, hex, h48, h80, h88⟩ := hmps
  obtain ⟨hev, hps'⟩ := pmcPackState_store hps hoff8 hoff_lt hoff_ne16 hval
  have hAs : ArenaOK s := hps.2.1.2.1.1.2
  have hout_hp : w_out.toNat + 96 ≤ globN s "heap_ptr" := hps.2.1.2.2.2.2.1.2
  have hfr_in := hps.2.2.2.2.1
  have hw_in_sb : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
    ⟨le_trans hps.2.1.1.1.2.1 hps.2.1.2.2.2.2.1.1, hout_hp⟩
  have hw_hi : w_out.toNat + 96 ≤ 2 ^ 64 :=
    (ivl_allocated_bound hAs (Or.inl hw_in_sb)).2
  have hfr128 := pmc_frame_memW_store_out (w_fr := w_fr) (w_val := w_val) hAs hout_hp hfr_in hoff_lt (show 128 < 280 by decide)
  have hfr208 := pmc_frame_memW_store_out (w_fr := w_fr) (w_val := w_val) hAs hout_hp hfr_in hoff_lt (show 208 < 280 by decide)
  have hfr224 := pmc_frame_memW_store_out (w_fr := w_fr) (w_val := w_val) hAs hout_hp hfr_in hoff_lt (show 224 < 280 by decide)
  have hout48 := pmc_memW_updW_ne s (w_out.toNat + off) (w_out.toNat + 48) w_val (by omega) (by omega) (by omega)
  have hout80 := pmc_memW_updW_ne s (w_out.toNat + off) (w_out.toNat + 80) w_val (by omega) (by omega) (by omega)
  have hout88 := pmc_memW_updW_ne s (w_out.toNat + off) (w_out.toNat + 88) w_val (by omega) (by omega) (by omega)
  refine ⟨hev, hps', hfmp, hsp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr128]; exact h128
  · rw [hfr208]; exact h208
  · rw [hfr224]; exact h224
  · rw [hfr224, hfr208]; exact hle
  · rw [hfr208]; exact h8
  · intro hnz; rw [hfr208]; exact hex hnz
  · intro ht; rw [hout48, hfr128]; exact h48 ht
  · intro ht; rw [hout80, hfr208]; exact h80 ht
  · intro ht; rw [hout88, hfr224]; exact h88 ht

theorem pmcMarksPackState_store_frame_other_then {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64} {logs off_out off_fr : Nat} {z has48 has80 has88 : Bool}
    {tail : ProgHOL 64}
    (hmps : PmcMarksPackState entry s w_out w_fr logs z has48 has80 has88)
    (hoff_out8 : off_out % 8 = 0) (hoff_out_lt : off_out < 96) (hoff_ne16 : off_out ≠ 16)
    (hoff_ne48 : off_out ≠ 48) (hoff_ne80 : off_out ≠ 80) (hoff_ne88 : off_out ≠ 88)
    (hoff_fr8 : off_fr % 8 = 0) (hoff_fr_lt : off_fr < 280)
    (htail : let w_v := BitVec.ofNat 64 (memW s (w_fr.toNat + off_fr))
      PmcMarksPackState entry
        { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off_out)) w_v }
        w_out w_fr logs z has48 has80 has88 →
      PmcMarksRun entry tail
        { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off_out)) w_v }) :
    PmcMarksRun entry
      (.seq (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 off_out)])
                    (.load .one (.op .add [.var .local (ofString "frame"), .const (BitVec.ofNat 64 off_fr)])))
            tail) s := by
  have hfr_hi : w_fr.toNat + 280 ≤ 2 ^ 64 := by
    have h1 : w_fr.toNat + 280 ≤ scratchEnd := hmps.1.2.2.2.2.1.2
    have h2 : scratchEnd ≤ 2 ^ 64 := by decide
    omega
  have hload := pmc_load_local_off hmps.1.2.2.1 hmps.1.2.2.2.1 hfr_hi hoff_fr8 hoff_fr_lt
  obtain ⟨hev, hmps'⟩ := pmcMarksPackState_store_other hmps hoff_out8 hoff_out_lt hoff_ne16
    hoff_ne48 hoff_ne80 hoff_ne88 hload
  unfold PmcMarksRun at htail ⊢
  rw [evaluateHOLFiniteState_seq_line780, hev]
  exact htail hmps'

theorem pmcMarksPackState_store48_then {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64} {logs : Nat} {z has48 has80 has88 : Bool}
    {tail : ProgHOL 64}
    (hmps : PmcMarksPackState entry s w_out w_fr logs z has48 has80 has88)
    (htail : let w_v := BitVec.ofNat 64 (memW s (w_fr.toNat + 128))
      PmcMarksPackState entry
        { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + 48)) w_v }
        w_out w_fr logs z true has80 has88 →
      PmcMarksRun entry tail
        { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + 48)) w_v }) :
    PmcMarksRun entry
      (.seq (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 48)])
                    (.load .one (.op .add [.var .local (ofString "frame"), .const (BitVec.ofNat 64 128)])))
            tail) s := by
  obtain ⟨hps, hfmp, hsp, h128, h208, h224, hle, h8, hex, _, h80, h88⟩ := hmps
  have hfr_hi : w_fr.toNat + 280 ≤ 2 ^ 64 := by
    have h1 : w_fr.toNat + 280 ≤ scratchEnd := hps.2.2.2.2.1.2
    have h2 : scratchEnd ≤ 2 ^ 64 := by decide
    omega
  have hload := pmc_load_local_off hps.2.2.1 hps.2.2.2.1 hfr_hi (by decide) (show 128 < 280 by decide)
  obtain ⟨hev, hps'⟩ := pmcPackState_store hps (off := 48) (by decide) (by decide) (by decide) hload
  have hAs : ArenaOK s := hps.2.1.2.1.1.2
  have hout_hp : w_out.toNat + 96 ≤ globN s "heap_ptr" := hps.2.1.2.2.2.2.1.2
  have hfr_in := hps.2.2.2.2.1
  have hw_in_sb : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
    ⟨le_trans hps.2.1.1.1.2.1 hps.2.1.2.2.2.2.1.1, hout_hp⟩
  have hw_hi : w_out.toNat + 96 ≤ 2 ^ 64 :=
    (ivl_allocated_bound hAs (Or.inl hw_in_sb)).2
  set w_v := BitVec.ofNat 64 (memW s (w_fr.toNat + 128))
  have hfr128 := pmc_frame_memW_store_out (w_fr := w_fr) (w_val := w_v) hAs hout_hp hfr_in (show 48 < 96 by decide) (show 128 < 280 by decide)
  have hfr208 := pmc_frame_memW_store_out (w_fr := w_fr) (w_val := w_v) hAs hout_hp hfr_in (show 48 < 96 by decide) (show 208 < 280 by decide)
  have hfr224 := pmc_frame_memW_store_out (w_fr := w_fr) (w_val := w_v) hAs hout_hp hfr_in (show 48 < 96 by decide) (show 224 < 280 by decide)
  have hlt128 : memW s (w_fr.toNat + 128) < 2 ^ 64 := by
    unfold memW; cases s.memory (BitVec.ofNat 64 (w_fr.toNat + 128)) with | word w => exact w.isLt
  have hout48 : memW { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + 48)) w_v }
      (w_out.toNat + 48) = memW s (w_fr.toNat + 128) := by
    rw [pmc_memW_updW_same s (w_out.toNat + 48) w_v]
    dsimp only [w_v]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt128]
  have hout80 := pmc_memW_updW_ne s (w_out.toNat + 48) (w_out.toNat + 80) w_v (by omega) (by omega) (by omega)
  have hout88 := pmc_memW_updW_ne s (w_out.toNat + 48) (w_out.toNat + 88) w_v (by omega) (by omega) (by omega)
  unfold PmcMarksRun at htail ⊢
  rw [evaluateHOLFiniteState_seq_line780, hev]
  apply htail
  refine ⟨hps', hfmp, hsp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr128]; exact h128
  · rw [hfr208]; exact h208
  · rw [hfr224]; exact h224
  · rw [hfr224, hfr208]; exact hle
  · rw [hfr208]; exact h8
  · intro hnz; rw [hfr208]; exact hex hnz
  · intro _; rw [hout48, hfr128]
  · intro ht; rw [hout80, hfr208]; exact h80 ht
  · intro ht; rw [hout88, hfr224]; exact h88 ht

theorem pmcMarksPackState_store80_then {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64} {logs : Nat} {z has48 has80 has88 : Bool}
    {tail : ProgHOL 64}
    (hmps : PmcMarksPackState entry s w_out w_fr logs z has48 has80 has88)
    (htail : let w_v := BitVec.ofNat 64 (memW s (w_fr.toNat + 208))
      PmcMarksPackState entry
        { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + 80)) w_v }
        w_out w_fr logs z has48 true has88 →
      PmcMarksRun entry tail
        { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + 80)) w_v }) :
    PmcMarksRun entry
      (.seq (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 80)])
                    (.load .one (.op .add [.var .local (ofString "frame"), .const (BitVec.ofNat 64 208)])))
            tail) s := by
  obtain ⟨hps, hfmp, hsp, h128, h208, h224, hle, h8, hex, h48, _, h88⟩ := hmps
  have hfr_hi : w_fr.toNat + 280 ≤ 2 ^ 64 := by
    have h1 : w_fr.toNat + 280 ≤ scratchEnd := hps.2.2.2.2.1.2
    have h2 : scratchEnd ≤ 2 ^ 64 := by decide
    omega
  have hload := pmc_load_local_off hps.2.2.1 hps.2.2.2.1 hfr_hi (by decide) (show 208 < 280 by decide)
  obtain ⟨hev, hps'⟩ := pmcPackState_store hps (off := 80) (by decide) (by decide) (by decide) hload
  have hAs : ArenaOK s := hps.2.1.2.1.1.2
  have hout_hp : w_out.toNat + 96 ≤ globN s "heap_ptr" := hps.2.1.2.2.2.2.1.2
  have hfr_in := hps.2.2.2.2.1
  have hw_in_sb : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
    ⟨le_trans hps.2.1.1.1.2.1 hps.2.1.2.2.2.2.1.1, hout_hp⟩
  have hw_hi : w_out.toNat + 96 ≤ 2 ^ 64 :=
    (ivl_allocated_bound hAs (Or.inl hw_in_sb)).2
  set w_v := BitVec.ofNat 64 (memW s (w_fr.toNat + 208))
  have hfr128 := pmc_frame_memW_store_out (w_fr := w_fr) (w_val := w_v) hAs hout_hp hfr_in (show 80 < 96 by decide) (show 128 < 280 by decide)
  have hfr208 := pmc_frame_memW_store_out (w_fr := w_fr) (w_val := w_v) hAs hout_hp hfr_in (show 80 < 96 by decide) (show 208 < 280 by decide)
  have hfr224 := pmc_frame_memW_store_out (w_fr := w_fr) (w_val := w_v) hAs hout_hp hfr_in (show 80 < 96 by decide) (show 224 < 280 by decide)
  have hlt208 : memW s (w_fr.toNat + 208) < 2 ^ 64 := by
    unfold memW; cases s.memory (BitVec.ofNat 64 (w_fr.toNat + 208)) with | word w => exact w.isLt
  have hout80 : memW { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + 80)) w_v }
      (w_out.toNat + 80) = memW s (w_fr.toNat + 208) := by
    rw [pmc_memW_updW_same s (w_out.toNat + 80) w_v]
    dsimp only [w_v]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt208]
  have hout48 := pmc_memW_updW_ne s (w_out.toNat + 80) (w_out.toNat + 48) w_v (by omega) (by omega) (by omega)
  have hout88 := pmc_memW_updW_ne s (w_out.toNat + 80) (w_out.toNat + 88) w_v (by omega) (by omega) (by omega)
  unfold PmcMarksRun at htail ⊢
  rw [evaluateHOLFiniteState_seq_line780, hev]
  apply htail
  refine ⟨hps', hfmp, hsp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr128]; exact h128
  · rw [hfr208]; exact h208
  · rw [hfr224]; exact h224
  · rw [hfr224, hfr208]; exact hle
  · rw [hfr208]; exact h8
  · intro hnz; rw [hfr208]; exact hex hnz
  · intro ht; rw [hout48, hfr128]; exact h48 ht
  · intro _; rw [hout80, hfr208]
  · intro ht; rw [hout88, hfr224]; exact h88 ht

theorem pmcMarksPackState_store88_then {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64} {logs : Nat} {z has48 has80 has88 : Bool}
    {tail : ProgHOL 64}
    (hmps : PmcMarksPackState entry s w_out w_fr logs z has48 has80 has88)
    (htail : let w_v := BitVec.ofNat 64 (memW s (w_fr.toNat + 224))
      PmcMarksPackState entry
        { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + 88)) w_v }
        w_out w_fr logs z has48 has80 true →
      PmcMarksRun entry tail
        { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + 88)) w_v }) :
    PmcMarksRun entry
      (.seq (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 88)])
                    (.load .one (.op .add [.var .local (ofString "frame"), .const (BitVec.ofNat 64 224)])))
            tail) s := by
  obtain ⟨hps, hfmp, hsp, h128, h208, h224, hle, h8, hex, h48, h80, _⟩ := hmps
  have hfr_hi : w_fr.toNat + 280 ≤ 2 ^ 64 := by
    have h1 : w_fr.toNat + 280 ≤ scratchEnd := hps.2.2.2.2.1.2
    have h2 : scratchEnd ≤ 2 ^ 64 := by decide
    omega
  have hload := pmc_load_local_off hps.2.2.1 hps.2.2.2.1 hfr_hi (by decide) (show 224 < 280 by decide)
  obtain ⟨hev, hps'⟩ := pmcPackState_store hps (off := 88) (by decide) (by decide) (by decide) hload
  have hAs : ArenaOK s := hps.2.1.2.1.1.2
  have hout_hp : w_out.toNat + 96 ≤ globN s "heap_ptr" := hps.2.1.2.2.2.2.1.2
  have hfr_in := hps.2.2.2.2.1
  have hw_in_sb : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
    ⟨le_trans hps.2.1.1.1.2.1 hps.2.1.2.2.2.2.1.1, hout_hp⟩
  have hw_hi : w_out.toNat + 96 ≤ 2 ^ 64 :=
    (ivl_allocated_bound hAs (Or.inl hw_in_sb)).2
  set w_v := BitVec.ofNat 64 (memW s (w_fr.toNat + 224))
  have hfr128 := pmc_frame_memW_store_out (w_fr := w_fr) (w_val := w_v) hAs hout_hp hfr_in (show 88 < 96 by decide) (show 128 < 280 by decide)
  have hfr208 := pmc_frame_memW_store_out (w_fr := w_fr) (w_val := w_v) hAs hout_hp hfr_in (show 88 < 96 by decide) (show 208 < 280 by decide)
  have hfr224 := pmc_frame_memW_store_out (w_fr := w_fr) (w_val := w_v) hAs hout_hp hfr_in (show 88 < 96 by decide) (show 224 < 280 by decide)
  have hlt224 : memW s (w_fr.toNat + 224) < 2 ^ 64 := by
    unfold memW; cases s.memory (BitVec.ofNat 64 (w_fr.toNat + 224)) with | word w => exact w.isLt
  have hout88 : memW { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + 88)) w_v }
      (w_out.toNat + 88) = memW s (w_fr.toNat + 224) := by
    rw [pmc_memW_updW_same s (w_out.toNat + 88) w_v]
    dsimp only [w_v]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt224]
  have hout48 := pmc_memW_updW_ne s (w_out.toNat + 88) (w_out.toNat + 48) w_v (by omega) (by omega) (by omega)
  have hout80 := pmc_memW_updW_ne s (w_out.toNat + 88) (w_out.toNat + 80) w_v (by omega) (by omega) (by omega)
  unfold PmcMarksRun at htail ⊢
  rw [evaluateHOLFiniteState_seq_line780, hev]
  apply htail
  refine ⟨hps', hfmp, hsp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr128]; exact h128
  · rw [hfr208]; exact h208
  · rw [hfr224]; exact h224
  · rw [hfr224, hfr208]; exact hle
  · rw [hfr208]; exact h8
  · intro hnz; rw [hfr208]; exact hex hnz
  · intro ht; rw [hout48, hfr128]; exact h48 ht
  · intro ht; rw [hout80, hfr208]; exact h80 ht
  · intro _; rw [hout88, hfr224]

theorem pmcMarksPackState_decCall_ro_then {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64} {logs : Nat} {z has48 has80 has88 : Bool}
    {name fname : MlS} {args : List (ExpHOL 64)} {values : List (ValueHOL 64)}
    {cont : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (hro : ReadOnlyFn fname)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values)
    (hne_out : ofString "out" ≠ name)
    (hne_fr : ofString "frame" ≠ name)
    (hmps : PmcMarksPackState entry s w_out w_fr logs z has48 has80 has88)
    (hcont : ∀ (w_res : BitVec 64) (s_next : PanSemStateFiniteExact 64 F),
      s_next.code = originalRuntimeCode →
      s_next.locals.lookup name = some (.val (.word w_res)) →
      PmcMarksPackState entry s_next w_out w_fr logs z has48 has80 has88 →
      PmcMarksRun entry cont s_next) :
    PmcMarksRun entry (.decCall name .one fname args cont) s := by
  unfold PmcMarksRun
  intro hres
  obtain ⟨params, body, ret, hlook, hspec⟩ := hro
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs] at hres ⊢
  dsimp only at hres ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
  · simp only [hl] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [hl] at hres ⊢
    by_cases hz : s.clock = 0
    · simp only [hz, ↓reduceIte] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hz, ↓reduceIte] at hres ⊢
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
      have hG : GuestInv s := hmps.1.2.1.2.1.1.1
      rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
      simp only [hrun] at hres ⊢
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
          dsimp only at hres ⊢
          have hro_eq := hspec (callEntryStateHOLFinite s callee) hcode
            (guestInv_callEntry s callee hG) hex (by rw [hrun]; simp) (by rw [hrun]; exact hres)
          rw [hrun] at hro_eq; dsimp only at hro_eq
          have hpost_eq : emptyLocalsHOLFinite post =
              { s with locals := HolFiniteMapExact.empty, clock := post.clock } := by
            have := R13.state_trans_locals_clock hentryEq hro_eq
            exact R13.state_eq_with_locals_clock this _ post.clock
          rw [hpost_eq]
          exact pmcMarksPost_not_returned (by intro _ h; cases h) hmps.2.1 hmps.2.2.1
        | returned val =>
          dsimp only at hres ⊢
          by_cases hsh : (shapeEqHOL (shapeOfHOLExact val) .one &&
              shapeEqHOL (shapeOfHOLExact val) ret') = true
          · simp only [hsh, ↓reduceIte] at hres ⊢
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
              simp [HolFiniteMapExact.update, FUPDATE, hne_out.symm, hmps.1.2.1.2.2.1]
            have hs_next_fr : s_next.locals.lookup (ofString "frame") = some (.val (.word w_fr)) := by
              dsimp only [s_next]; unfold setVarHOLFinite
              simp [HolFiniteMapExact.update, FUPDATE, hne_fr.symm, hmps.1.2.2.1]
            have hmps_next : PmcMarksPackState entry s_next w_out w_fr logs z has48 has80 has88 := by
              have hmps' := pmcMarksPackState_with_locals_clock s_next.locals post.clock
                hs_next_out hs_next_fr hmps
              rwa [← hs_next_eq] at hmps'
            have hcont_run := hcont w_res s_next hs_next_code hs_next_name hmps_next
            unfold PmcMarksRun at hcont_run
            rcases hc_run : evaluateHOLFiniteState s_next cont with ⟨cres, cpost⟩
            rw [hc_run] at hcont_run
            simp only [hc_run] at hres ⊢
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
                exact pmcMarksPost_with_locals_clock _ cpost.clock
                  (pmcMarksPost_with_locals_clock _ cpost.clock (hcont_run hres))
              | returned cval =>
                exact pmcMarksPost_with_locals_clock _ cpost.clock
                  (pmcMarksPost_with_locals_clock _ cpost.clock (hcont_run (Or.inl ⟨cval, rfl⟩)))
          · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hres
            exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

theorem pmcMarksPackState_ite160_step {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64} {logs : Nat} {z has48 has80 has88 : Bool} {tail : ProgHOL 64}
    (hmps : PmcMarksPackState entry s w_out w_fr logs z has48 has80 has88)
    (htail : ∀ (z' : Bool) (s_mid : PanSemStateFiniteExact 64 F),
      PmcMarksPackState entry s_mid w_out w_fr logs z' has48 has80 has88 →
      PmcMarksRun entry tail s_mid) :
    PmcMarksRun entry
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
  obtain ⟨hps, hfmp, hsp, h128, h208, h224, hle, h8, hex, h48, h80, h88⟩ := hmps
  have hfr_hi : w_fr.toNat + 280 ≤ 2 ^ 64 := by
    have h1 : w_fr.toNat + 280 ≤ scratchEnd := hps.2.2.2.2.1.2
    have h2 : scratchEnd ≤ 2 ^ 64 := by decide
    omega
  have hload160 := pmc_load_local_off hps.2.2.1 hps.2.2.2.1 hfr_hi (by decide) (show 160 < 280 by decide)
  set w160 := BitVec.ofNat 64 (memW s (w_fr.toNat + 160))
  unfold PmcMarksRun
  intro hres
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres ⊢
  have hcond160 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.load .one (.op .add [.var .local (ofString "frame"), .const 160#64])) (.const 0#64)) =
      some (.val (.word (if w160 = 0#64 then 1#64 else 0#64))) := by
    have hl160' : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "frame"), .const 160#64])) =
        some (.val (.word w160)) := hload160
    unfold evalHOLExact; rw [hl160']
    simp [evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcond160] at hres ⊢
  dsimp only at hres ⊢
  by_cases h160_eq : w160 = 0#64
  · rw [if_pos h160_eq, if_neg (show ¬ ((1#64 : BitVec 64) = 0) by decide)] at hres ⊢
    obtain ⟨hM0, hsr, hs_fr, hw_fr_ok, hfr_in, hlok, hdisj, hlogs_eq, _, _⟩ := hps
    have hAs : ArenaOK s := hsr.2.1.1.2
    have hgS : GuestInv s := hsr.2.1.1.1
    have hw_in_sb : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
      ⟨le_trans hsr.1.1.2.1 hsr.2.2.2.2.1.1, hsr.2.2.2.2.1.2⟩
    have hw_hi : w_out.toNat + 96 ≤ 2 ^ 64 :=
      (ivl_allocated_bound hAs (Or.inl hw_in_sb)).2
    have hload88 := pmc_load_local_off hs_fr hw_fr_ok hfr_hi (by decide) (show 88 < 280 by decide)
    obtain ⟨hev16, hsr1⟩ := pmcStoreReady_store
      (Q2 := fun _ _ st S' Nd' => PmcLogsLiveOwned st S' Nd' logs)
      hsr (off := 16) (by decide) (by decide) hload88
      (fun S' Nd' _ _ howned_eq _ hlive =>
        (pmc_logs_preserve_store_out hAs hgS hw_hi (by decide) (by decide) hlok hlive hdisj howned_eq).2.1)
    obtain ⟨S_en, Nd_en, hMA_en⟩ := R10Shards.Fast_GbodyC17ToC21.msgReadyAt_of_msgReady hM0
    have hT_en : ∀ t ∈ pmcTables entry, t ∈ S_en := by
      intro t ht; simp [pmcTables] at ht
      rcases ht with rfl | rfl
      · exact hMA_en.2.2.1
      · exact hMA_en.2.2.2.1
    have hD_en : IvlsDisj (pmcRegions entry) (worldTypedIvls entry S_en Nd_en) := by
      rw [pmcRegions_eq_bufRegions]
      intro x hx j hj
      rcases List.mem_cons.1 hx with rfl | hx_buf
      · exact hMA_en.2.2.2.2.2.2.2.2.2.2.2.1 j (worldTypedIvls_sub_worldOwned entry S_en Nd_en j hj)
      · exact validBufList_disj validBufList_pmcBufs hMA_en.2.1 x hx_buf j hj
    obtain ⟨S_p, Nd_p, _, hWT_p, _, _, hout_ow_p, hlive_p⟩ := hsr.2.1.2.2.2.2 S_en Nd_en hMA_en.2.1 hT_en hD_en
    have hx16_lt : w_out.toNat + 16 < 2 ^ 64 := by omega
    obtain ⟨_, hdom16, _⟩ := hsr.2.2.2.2.2.2.2 2 (by dsimp only at *; omega)
    have hk16_eq : w_out.toNat + 8 * 2 = w_out.toNat + 16 := by omega
    rw [hk16_eq] at hdom16
    set w88 := BitVec.ofNat 64 (memW s (w_fr.toNat + 88))
    set a16 := BitVec.ofNat 64 (w_out.toNat + 16)
    have hx16_in : w_out.toNat ≤ a16.toNat ∧ a16.toNat + 8 ≤ w_out.toNat + 96 := by
      dsimp only [a16]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx16_lt]; omega
    obtain ⟨_, _, howned_eq16, _, _, _⟩ :=
      worldTypedWith_store_word_disj
        (post := { s with memory := pmcUpdW s.memory a16 w88 })
        hsr.2.1.1 hdom16
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun a hne => by unfold pmcUpdW; exact if_neg hne⟩
        hWT_p
        (fun j hj => disj_of_inside_right (j' := (w_out.toNat, 96)) ⟨hx16_in.1, hx16_in.2⟩
          (hout_ow_p (w_out.toNat, 96) (by simp) j (worldTypedIvls_sub_worldOwned s S_p Nd_p j hj)).flip)
    obtain ⟨hlok1, _, hdisj1⟩ :=
      pmc_logs_preserve_store_out hAs hgS hw_hi (by decide) (show 16 < 96 by decide) hlok hlive_p hdisj howned_eq16
    have hfr88_1 : memW { s with memory := pmcUpdW s.memory a16 w88 } (w_fr.toNat + 88) = memW s (w_fr.toNat + 88) :=
      pmc_frame_memW_store_out hAs hsr.2.2.2.2.1.2 hfr_in (show 16 < 96 by decide) (by decide)
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
    have hfr128_1 := pmc_frame_memW_store_out (w_fr := w_fr) (w_val := w88) hAs hsr.2.2.2.2.1.2 hfr_in (show 16 < 96 by decide) (show 128 < 280 by decide)
    have hfr208_1 := pmc_frame_memW_store_out (w_fr := w_fr) (w_val := w88) hAs hsr.2.2.2.2.1.2 hfr_in (show 16 < 96 by decide) (show 208 < 280 by decide)
    have hfr224_1 := pmc_frame_memW_store_out (w_fr := w_fr) (w_val := w88) hAs hsr.2.2.2.2.1.2 hfr_in (show 16 < 96 by decide) (show 224 < 280 by decide)
    have hout48_1 := pmc_memW_updW_ne s (w_out.toNat + 16) (w_out.toNat + 48) w88 (by omega) (by omega) (by omega)
    have hout80_1 := pmc_memW_updW_ne s (w_out.toNat + 16) (w_out.toNat + 80) w88 (by omega) (by omega) (by omega)
    have hout88_1 := pmc_memW_updW_ne s (w_out.toNat + 16) (w_out.toNat + 88) w88 (by omega) (by omega) (by omega)
    have hmps1 : PmcMarksPackState entry s1 w_out w_fr logs false has48 has80 has88 := by
      refine ⟨hps1, hfmp, hsp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only [s1, a16]; rw [hfr128_1]; exact h128
      · dsimp only [s1, a16]; rw [hfr208_1]; exact h208
      · dsimp only [s1, a16]; rw [hfr224_1]; exact h224
      · dsimp only [s1, a16]; rw [hfr224_1, hfr208_1]; exact hle
      · dsimp only [s1, a16]; rw [hfr208_1]; exact h8
      · intro hnz; dsimp only [s1, a16]; rw [hfr208_1]; exact hex hnz
      · intro ht; dsimp only [s1, a16]; rw [hout48_1, hfr128_1]; exact h48 ht
      · intro ht; dsimp only [s1, a16]; rw [hout80_1, hfr208_1]; exact h80 ht
      · intro ht; dsimp only [s1, a16]; rw [hout88_1, hfr224_1]; exact h88 ht
    rw [evaluateHOLFiniteState_seq_line780, hev16] at hres ⊢
    dsimp only at hres ⊢
    have hload136 := pmc_load_local_off hps1.2.2.1 hps1.2.2.2.1 hfr_hi (by decide) (show 136 < 280 by decide)
    obtain ⟨hev24, hmps2⟩ := pmcMarksPackState_store_other hmps1 (off := 24) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hload136
    set w136 := BitVec.ofNat 64 (memW s1 (w_fr.toNat + 136))
    set a24 := BitVec.ofNat 64 (w_out.toNat + 24)
    set s2 := { s1 with memory := pmcUpdW s1.memory a24 w136 }
    rw [evaluateHOLFiniteState_seq_line780, hev24] at hres ⊢
    dsimp only at hres ⊢
    have hload96 := pmc_load_local_off hmps2.1.2.2.1 hmps2.1.2.2.2.1 hfr_hi (by decide) (show 96 < 280 by decide)
    set w96 := BitVec.ofNat 64 (memW s2 (w_fr.toNat + 96))
    rw [evaluateHOLFiniteState_dec_total] at hres ⊢
    dsimp only at hres ⊢
    have hsh_rc : shapeEqHOL .one (shapeOfHOLExact (.val (.word w96) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    have hl96' : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "frame"), .const 96#64])) =
        some (.val (.word w96)) := hload96
    rw [hl96'] at hres ⊢
    dsimp only at hres ⊢
    rw [if_pos hsh_rc] at hres ⊢
    set s3 := setVarHOLFinite (ofString "rc") (.val (.word w96)) s2
    have hs3_rc : s3.locals.lookup (ofString "rc") = some (.val (.word w96)) := by
      simp [s3, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
    have hs3_out : s3.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
      simp [s3, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "rc" ≠ ofString "out" by decide, hmps2.1.2.1.2.2.1]
    have hs3_fr : s3.locals.lookup (ofString "frame") = some (.val (.word w_fr)) := by
      simp [s3, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "rc" ≠ ofString "frame" by decide, hmps2.1.2.2.1]
    have hmps3 : PmcMarksPackState entry s3 w_out w_fr logs false has48 has80 has88 :=
      pmcMarksPackState_with_locals_clock s3.locals s2.clock hs3_out hs3_fr hmps2
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
        PmcMarksPackState entry s4 w_out w_fr logs false has48 has80 has88 := by
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
          rw [hs4_ne _ (by decide)]; exact hmps2.1.2.1.2.2.1
        have hs4_fr : s4.locals.lookup (ofString "frame") = some (.val (.word w_fr)) := by
          rw [hs4_ne _ (by decide)]; exact hmps2.1.2.2.1
        exact ⟨0#64, s4, rfl, hs4_rc, hs4_ne,
          pmcMarksPackState_with_locals_clock s4.locals s3.clock hs4_out hs4_fr hmps3⟩
      · rw [if_neg hslt, if_pos (show (0#64 : BitVec 64) = 0 by decide), evaluateHOLFiniteState_skip]
        have hs3_ne : ∀ x, x ≠ ofString "rc" → s3.locals.lookup x = s2.locals.lookup x := by
          intro x hx
          simp [s3, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hx.symm]
        exact ⟨w96, s3, rfl, hs3_rc, hs3_ne, hmps3⟩
    obtain ⟨w_rc', s4, hev_ite, hs4_rc, hs4_ne, hmps4⟩ := hite_rc
    have hev_rc_var : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
        (.var .local (ofString "rc")) = some (.val (.word w_rc')) := by
      simp [evalHOLExact, hs4_rc]
    obtain ⟨hev8, hmps5⟩ := pmcMarksPackState_store_other hmps4 (off := 8) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hev_rc_var
    set a8 := BitVec.ofNat 64 (w_out.toNat + 8)
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
    rw [hbody_dec] at hres ⊢
    dsimp only at hres ⊢
    set L_mid := HolFiniteMapExact.resVarEq s4.locals (ofString "rc", s2.locals.lookup (ofString "rc"))
    set s_mid := { s4 with memory := pmcUpdW s4.memory a8 w_rc', locals := L_mid }
    have hs_mid_out : s_mid.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
      dsimp only [s_mid, L_mid]
      rw [PanRunBounded.resVarEq_lookup, if_neg (show ofString "out" ≠ ofString "rc" by decide)]
      rw [hs4_ne _ (by decide)]; exact hmps2.1.2.1.2.2.1
    have hs_mid_fr : s_mid.locals.lookup (ofString "frame") = some (.val (.word w_fr)) := by
      dsimp only [s_mid, L_mid]
      rw [PanRunBounded.resVarEq_lookup, if_neg (show ofString "frame" ≠ ofString "rc" by decide)]
      rw [hs4_ne _ (by decide)]; exact hmps2.1.2.2.1
    have hmps_mid : PmcMarksPackState entry s_mid w_out w_fr logs false has48 has80 has88 :=
      pmcMarksPackState_with_locals_clock s_mid.locals s4.clock hs_mid_out hs_mid_fr hmps5
    exact htail false s_mid hmps_mid hres
  · rw [if_neg h160_eq, if_pos (show (0#64 : BitVec 64) = 0 by decide), evaluateHOLFiniteState_skip] at hres ⊢
    dsimp only at hres ⊢
    exact htail z s ⟨hps, hfmp, hsp, h128, h208, h224, hle, h8, hex, h48, h80, h88⟩ hres

theorem pmcMarksPackState_return {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out w_fr : BitVec 64} {logs : Nat} {z : Bool}
    (hmps : PmcMarksPackState entry s w_out w_fr logs z true true true) :
    PmcMarksRun entry (.return (.var .local (ofString "out"))) s := by
  unfold PmcMarksRun
  intro _
  obtain ⟨hps, hfmp, hsp, h128, h208, h224, hle, h8, hex, h48, h80, h88⟩ := hmps
  have hs_out := hps.2.1.2.2.1
  have hw_in := hps.2.1.2.2.2.2.1
  have hret_ev : evaluateHOLFiniteState s (.return (.var .local (ofString "out"))) =
      (some (.returned (.val (.word w_out))), emptyLocalsHOLFinite s) := by
    rw [evaluateHOLFiniteState_return]
    simp only [evalHOLExact, hs_out, shapeOfHOLExact, sizeOfShapeWithContextHOL,
      show (1 : Nat) ≤ 32 by decide, ↓reduceIte]
  rw [hret_ev]
  dsimp only
  apply pmcMarksPost_with_locals_clock _ (emptyLocalsHOLFinite s).clock
  refine ⟨hfmp, hsp, fun v hv => ?_⟩
  injection hv with hv'; injection hv' with hv''; subst v
  refine ⟨w_out, rfl, hw_in, ?_, fun hnz80 => ?_⟩
  · rw [h48 rfl]; exact h128
  · rw [h80 rfl, h88 rfl]
    exact ⟨h208, h224, hle, h8, hex⟩

theorem pmcMarksPack_cut {F : Type} (entry s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (ha2m : PmcMarksA2 entry s) :
    PmcMarksRun entry pmcPack s := by
  obtain ⟨ha2, hfmp, hsp, w_out_m, w_fr_m, hs_out_m, hs_fr_m, h128, h208, h224, hle, h8, hex⟩ := ha2m
  obtain ⟨hM0, w_out, w_fr, hstep, hs_out, hs_fr, hw_out8, hw_in, hw_ok, hz16,
    hw_fr_ok, hfr_in, hlok, hdisj⟩ := ha2
  rw [hs_out] at hs_out_m; injection hs_out_m with hs_out_m'; injection hs_out_m' with hw_out_eq
  injection hw_out_eq with hw_out_eq
  subst w_out_m
  rw [hs_fr] at hs_fr_m; injection hs_fr_m with hs_fr_m'; injection hs_fr_m' with hw_fr_eq
  injection hw_fr_eq with hw_fr_eq
  subst w_fr_m
  have hps0 := pmcPackState_of_a2 hM0 hstep hs_out hs_fr hw_out8 hw_in hw_ok hz16
    hw_fr_ok hfr_in hlok hdisj
  have hmps0 : PmcMarksPackState entry s w_out w_fr (memW s (w_fr.toNat + 88)) true false false false :=
    ⟨hps0, hfmp, hsp, h128, h208, h224, hle, h8, hex,
      fun h => Bool.noConfusion h, fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩
  have hfr_hi : w_fr.toNat + 280 ≤ 2 ^ 64 := by
    have h1 : w_fr.toNat + 280 ≤ scratchEnd := hfr_in.2
    have h2 : scratchEnd ≤ 2 ^ 64 := by decide
    omega
  have hst_fr : ∀ {s0 : PanSemStateFiniteExact 64 F} {z0 has48 has80 has88 : Bool}
      {off_out off_fr : Nat} {tail : ProgHOL 64},
      s0.code = originalRuntimeCode →
      PmcMarksPackState entry s0 w_out w_fr (memW s (w_fr.toNat + 88)) z0 has48 has80 has88 →
      off_out % 8 = 0 → off_out < 96 → off_out ≠ 16 →
      off_out ≠ 48 → off_out ≠ 80 → off_out ≠ 88 →
      off_fr % 8 = 0 → off_fr < 280 →
      (∀ s1 : PanSemStateFiniteExact 64 F,
        s1.code = originalRuntimeCode →
        PmcMarksPackState entry s1 w_out w_fr (memW s (w_fr.toNat + 88)) z0 has48 has80 has88 →
        PmcMarksRun entry tail s1) →
      PmcMarksRun entry
        (.seq (.store (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 off_out)])
                      (.load .one (.op .add [.var .local (ofString "frame"), .const (BitVec.ofNat 64 off_fr)])))
              tail) s0 :=
    fun hc0 hp0 ho8 holt hone ho48 ho80 ho88 hf8 hflt ht =>
      pmcMarksPackState_store_frame_other_then hp0 ho8 holt hone ho48 ho80 ho88 hf8 hflt (fun hp1 => ht _ hc0 hp1)
  unfold PmcMarksRun
  intro hres
  unfold pmcPack pmcCode at hres ⊢
  simp only [sourceFunctionEntry, Guest.Software.guestFn_process_message_call,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil,
    R13Shards.spineAt] at hres ⊢
  revert hres
  change PmcMarksRun entry _ s
  refine hst_fr hcode hmps0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (fun s1 hc1 hmps1 => ?_)
  refine hst_fr hc1 hmps1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (fun s2 hc2 hmps2 => ?_)
  refine hst_fr hc2 hmps2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (fun s3 hc3 hmps3 => ?_)
  refine pmcMarksPackState_store48_then hmps3 (fun hmps4 => ?_)
  have hc4 : ({ s3 with memory := pmcUpdW s3.memory (BitVec.ofNat 64 (w_out.toNat + 48)) (BitVec.ofNat 64 (memW s3 (w_fr.toNat + 128))) }).code = originalRuntimeCode := hc3
  refine hst_fr hc4 hmps4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (fun s5 hc5 hmps5 => ?_)
  refine hst_fr hc5 hmps5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (fun s6 hc6 hmps6 => ?_)
  have hargs6 : evalListHOLFinite s6 (h := fun a => Classical.propDecidable (s6.memaddrs a))
      [.var .local (ofString "frame")] = some [.val (.word w_fr)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact, hmps6.1.2.2.1]
  refine pmcMarksPackState_decCall_ro_then hc6 ro_frame_state_gas_used hargs6 (by decide) (by decide) hmps6
    (fun w_fsg s_fsg hc7 hs_fsg hmps7 => ?_)
  have hload200 := pmc_load_local_off hmps7.1.2.2.1 hmps7.1.2.2.2.1 hfr_hi (by decide) (show 200 < 280 by decide)
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
  obtain ⟨hev72, hmps8⟩ := pmcMarksPackState_store_other hmps7 (off := 72) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hval72
  unfold PmcMarksRun
  rw [evaluateHOLFiniteState_seq_line780, hev72]
  change PmcMarksRun entry _ _
  refine pmcMarksPackState_ite160_step hmps8 (fun _ s_post hmps9 => ?_)
  refine pmcMarksPackState_store80_then hmps9 (fun hmps10 => ?_)
  refine pmcMarksPackState_store88_then hmps10 (fun hmps11 => ?_)
  exact pmcMarksPackState_return hmps11

theorem wk_process_message_call_marks_of_callees
    (hpm : WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => [(locN s "msg", 176), (globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetFrameResultMarksExact (ofString "process_message"))
    (hpcm : WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => [(locN s "msg", 176), (globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetFrameResultMarks (ofString "process_create_message")) :
    WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => [(locN s "msg", 176), (globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetMessageOutputMarks (ofString "process_message_call") := by
  have hpm_s : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultStrong (ofString "process_message") :=
    worldKeepsIn_mono_extra (fun _ _ _ _ _ h => h.1.1) hpm
  have hpcm_s : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep
      RetFrameResultStrong (ofString "process_create_message") :=
    worldKeepsIn_mono_extra (fun _ _ _ _ _ h => h.1) hpcm
  refine ⟨_, _, _, pmc_lookup, ?_⟩
  intro F s hcode hready _hparams _hnt hres
  have hstrong_run := pmcInit_cut s _
    (pmcDispatch_cut hpm_s hpcm_s s _ (pmcPack_cut s)) s hcode (pmcA0_init s hready)
  rw [← pmc_phases_eq] at hstrong_run
  unfold PmcRelRunStrong pmcCode pmcTables pmcRegions ptxRegions pmcGlobals pmcKeep at hstrong_run
  have hws_strong := hstrong_run hres
  have hmarks_run := pmcMarksInit_cut s _
    (pmcMarksDispatch_cut hpm hpcm s _ (pmcMarksPack_cut s)) s hcode (pmcA0_init s hready)
  rw [← pmc_phases_eq] at hmarks_run
  unfold PmcMarksRun pmcCode at hmarks_run
  have hmarks := hmarks_run hres
  obtain ⟨hAp, hhp, hG, hK, hW⟩ := hws_strong
  refine ⟨hAp, hhp, hG, hK, fun S Nd hWT hTS hD => ?_⟩
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hQ⟩ := hW S Nd hWT hTS hD
  exact ⟨S', Nd', hsub, hWT', hOG, hFO, hQ, hmarks⟩

/-! ## 12. Strengthened `lst_push` and `wk_lst_push` -/

def RetListSlotStrong {F : Type}
    (s : PanSemStateFiniteExact 64 F) (r : Option (PanSemResultExact 64))
    (post : PanSemStateFiniteExact 64 F) (_S _Nd : List Nat) : Prop :=
  (∀ a : BitVec 64,
    ¬ CellHits a.toNat (locN s "l", 24) →
    ¬ CellHits a.toNat (InitECandidate.Solver.Wave8Contracts.M08.heapFree s) →
    post.memory a = s.memory a) ∧
  (∀ v, r = some (.returned v) →
    ∃ w : BitVec 64,
      v = .val (.word w) ∧
      w.toNat % 8 = 0 ∧
      Inside (w.toNat, 8) (memW post (locN s "l")) (memW post (locN s "l") + 8 * memW post (locN s "l" + 16)) ∧
      memW post (locN s "l" + 8) = memW s (locN s "l" + 8) + 1 ∧
      w.toNat = memW post (locN s "l") + 8 * memW s (locN s "l" + 8) ∧
      (memW s (locN s "l") ≠ 0 →
        ∀ k, k < memW s (locN s "l" + 8) →
          memW post (memW post (locN s "l") + 8 * k) = memW s (memW s (locN s "l") + 8 * k)))

private theorem dec_word_resumes_step {F : Type}
    {s : PanSemStateFiniteExact 64 F} {x : MlS} {e : ExpHOL 64} {cont : ProgHOL 64}
    (hres : Resumes (evaluateHOLFiniteState s (.dec x .one e cont)).1) :
    ∃ v : ValueHOL 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v ∧
      let s1 := setVarHOLFinite x v s
      Resumes (evaluateHOLFiniteState s1 cont).1 ∧
      (evaluateHOLFiniteState s (.dec x .one e cont)).1 = (evaluateHOLFiniteState s1 cont).1 ∧
      (evaluateHOLFiniteState s (.dec x .one e cont)).2 =
        { (evaluateHOLFiniteState s1 cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 cont).2.locals (x, s.locals.lookup x) } := by
  rw [evaluateHOLFiniteState_dec_total] at hres ⊢
  dsimp only at hres ⊢
  rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | v
  · rw [he] at hres; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
  · rw [he] at hres
    dsimp only at hres ⊢
    by_cases hsh : shapeEqHOL .one (shapeOfHOLExact v) = true
    · rw [if_pos hsh] at hres ⊢
      exact ⟨v, rfl, hres, rfl, rfl⟩
    · rw [if_neg hsh] at hres
      rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

private theorem memcpy_src_zero_pos_err {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 n0 : BitVec 64)
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hsrc : s.locals.lookup (ofString "src") = some (.val (.word 0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hn_ge8 : 8 ≤ n0.toNat)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memcpy)).1 ≠ some .timeOut) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memcpy)).1 = some .error := by
  have hnot_dom0 : ¬ ordinaryDomain (0 : BitVec 64) := by
    rw [M13.ordinaryDomain_iff]; simp
  have hnot_dom_al0 : ¬ ordinaryDomain (panByteAlignHOL (0 : BitVec 64)) := by
    have hal0 : panByteAlignHOL (0 : BitVec 64) = 0 := BitVec.eq_of_toNat_eq (by rw [panByteAlign_toNat64]; rfl)
    rw [hal0]; exact hnot_dom0
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  have hev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const (BitVec.ofNat 64 0)) = some (.val (.word 0)) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [hev0] at hnt ⊢; dsimp only at hnt ⊢; rw [if_pos hsh0] at hnt ⊢
  set s1 := setVarHOLFinite (ofString "i") (.val (.word 0)) s
  have hs1_dst : s1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
    have hne : ofString "i" ≠ ofString "dst" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hdst]
  have hs1_src : s1.locals.lookup (ofString "src") = some (.val (.word 0)) := by
    have hne : ofString "i" ≠ ofString "src" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hsrc]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word n0)) := by
    have hne : ofString "i" ≠ ofString "n" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hn]
  have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  change (evaluateHOLFiniteState s1 _).1 = some .error
  have hnt' : (evaluateHOLFiniteState s1 _).1 ≠ some .timeOut := hnt
  clear hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt' ⊢
  rw [evaluateHOLFiniteState_ite] at hnt' ⊢
  rcases hcond : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.cmp .equal (.op .and [.op .or [.var .local (ofString "dst"), .var .local (ofString "src")], .const (BitVec.ofNat 64 7)]) (.const (BitVec.ofNat 64 0))) with _ | cv
  · simp [hcond]
  · have hcv_w : ∃ cw : BitVec 64, cv = .val (.word cw) := by
      simp [evalHOLExact, evalListHOLExact, hs1_dst, hs1_src, wordOpHOL, wordOp, valueIsWord, valueWord,
        Compiler.Encoders.Asm.wordCmpHOL] at hcond
      exact ⟨_, hcond.symm⟩
    obtain ⟨cw, rfl⟩ := hcv_w
    simp only [hcond] at hnt' ⊢
    by_cases hcw0 : cw = 0
    · rw [if_pos hcw0, evaluateHOLFiniteState_skip] at hnt' ⊢
      dsimp only at hnt' ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hnt' ⊢
      rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt' ⊢
      have hc3 : @evalHOLFinite 64 F _ s1 (fun a => Classical.propDecidable (s1.memaddrs a))
          (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)])) =
          some (.val (.word 1)) := by
        rw [evalHOLFinite_eq_toExact]
        simp only [evalHOLExact, evalListHOLExact, hs1_n, hs1_i, wordOpHOL, wordOp, valueIsWord, valueWord,
          List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero,
          Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
        have h08 : (0 + (8#64 + 0)).toNat = 8 := by decide
        rw [h08]; simp [show ¬ (n0.toNat < 8) by omega]
      simp only [hc3] at hnt' ⊢
      have h10 : (1 : BitVec 64) ≠ 0 := by decide
      rw [if_pos h10] at hnt' ⊢
      by_cases hk0 : s1.clock = 0
      · simp [hk0] at hnt'
      · rw [if_neg hk0]
        have hsb0 : (evaluateHOLFiniteState (decClockHOLFinite s1)
            (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
              (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))).1 =
            some .error := by
          rw [evaluateHOLFiniteState_storeByte]
          have hd' : (decClockHOLFinite s1).locals.lookup (ofString "dst") = some (.val (.word dst0)) := hs1_dst
          have hs' : (decClockHOLFinite s1).locals.lookup (ofString "src") = some (.val (.word 0)) := hs1_src
          have hi' : (decClockHOLFinite s1).locals.lookup (ofString "i") = some (.val (.word 0)) := hs1_i
          have ha0 : @evalHOLExact 64 F _ (decClockHOLFinite s1).toExact
              (fun a => Classical.propDecidable ((decClockHOLFinite s1).memaddrs a))
              (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) =
              some (.val (.word (dst0 + 0))) := by
            simp [evalHOLExact, evalListHOLExact, decClockHOLExact, PanSemStateFiniteExact.toExact,
              hd', hi', wordOpHOL, wordOp, valueIsWord, valueWord]
          have hlb0 : @evalHOLExact 64 F _ (decClockHOLFinite s1).toExact
              (fun a => Classical.propDecidable ((decClockHOLFinite s1).memaddrs a))
              (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])) = none := by
            have hs0 : @evalHOLExact 64 F _ (decClockHOLFinite s1).toExact
                (fun a => Classical.propDecidable ((decClockHOLFinite s1).memaddrs a))
                (.op .add [.var .local (ofString "src"), .var .local (ofString "i")]) =
                some (.val (.word 0)) := by
              simp [evalHOLExact, evalListHOLExact, decClockHOLExact, PanSemStateFiniteExact.toExact,
                hs', hi', wordOpHOL, wordOp, valueIsWord, valueWord]
            have hnd : ¬ (decClockHOLFinite s1).memaddrs (panByteAlignHOL 0#64) := by
              change ¬ s.memaddrs (panByteAlignHOL (0 : BitVec 64)); rw [hma]; exact hnot_dom_al0
            rw [evalHOLExact, hs0]
            dsimp only
            unfold panMemLoadByteHOL
            cases (decClockHOLFinite s1).memory (panByteAlignHOL 0#64) with
            | word _ => simp [hnd]
          rw [ha0, hlb0]
        rw [evaluateHOLFiniteState_seq_line780]
        rcases hr0 : evaluateHOLFiniteState (decClockHOLFinite s1)
            (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
              (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")]))) with ⟨r0, m0⟩
        rw [hr0] at hsb0; dsimp only at hsb0; subst hsb0
        rfl
    · rw [if_neg hcw0] at hnt' ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hnt' ⊢
      by_cases hn32 : 32 ≤ n0.toNat
      · -- `lp1` enters on iteration 0 (`0 + 32 ≤ n0`) and its first `.store` loads `src + 0 = 0`, which is `none` -> `.error`!
        rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt' ⊢
        have hc1 : @evalHOLFinite 64 F _ s1 (fun a => Classical.propDecidable (s1.memaddrs a))
            (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 32)])) =
            some (.val (.word 1)) := by
          rw [evalHOLFinite_eq_toExact]
          simp only [evalHOLExact, evalListHOLExact, hs1_n, hs1_i, wordOpHOL, wordOp, valueIsWord, valueWord,
            List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero,
            Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
          have h032 : (0 + (32#64 + 0)).toNat = 32 := by decide
          rw [h032]; simp [show ¬ (n0.toNat < 32) by omega]
        simp only [hc1] at hnt' ⊢
        have h10 : (1 : BitVec 64) ≠ 0 := by decide
        rw [if_pos h10] at hnt' ⊢
        by_cases hk0 : s1.clock = 0
        · simp [hk0] at hnt'
        · rw [if_neg hk0]
          have hst0 : (evaluateHOLFiniteState (decClockHOLFinite s1)
              (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))).1 =
              some .error := by
            rw [evaluateHOLFiniteState_store]
            have hd' : (decClockHOLFinite s1).locals.lookup (ofString "dst") = some (.val (.word dst0)) := hs1_dst
            have hs' : (decClockHOLFinite s1).locals.lookup (ofString "src") = some (.val (.word 0)) := hs1_src
            have hi' : (decClockHOLFinite s1).locals.lookup (ofString "i") = some (.val (.word 0)) := hs1_i
            have ha0 : @evalHOLExact 64 F _ (decClockHOLFinite s1).toExact
                (fun a => Classical.propDecidable ((decClockHOLFinite s1).memaddrs a))
                (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) =
                some (.val (.word (dst0 + 0))) := by
              simp [evalHOLExact, evalListHOLExact, decClockHOLExact, PanSemStateFiniteExact.toExact,
                hd', hi', wordOpHOL, wordOp, valueIsWord, valueWord]
            have hl0 : @evalHOLExact 64 F _ (decClockHOLFinite s1).toExact
                (fun a => Classical.propDecidable ((decClockHOLFinite s1).memaddrs a))
                (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])) = none := by
              have hs0 : @evalHOLExact 64 F _ (decClockHOLFinite s1).toExact
                  (fun a => Classical.propDecidable ((decClockHOLFinite s1).memaddrs a))
                  (.op .add [.var .local (ofString "src"), .var .local (ofString "i")]) =
                  some (.val (.word 0)) := by
                simp [evalHOLExact, evalListHOLExact, decClockHOLExact, PanSemStateFiniteExact.toExact,
                  hs', hi', wordOpHOL, wordOp, valueIsWord, valueWord]
              have hnd : ¬ (decClockHOLFinite s1).memaddrs 0#64 := by
                change ¬ s.memaddrs (0 : BitVec 64); rw [hma]; exact hnot_dom0
              have hwf1 : isWfShapeExactHOL (decClockHOLFinite s1).toExact.structs ShapeHOL.one = true := rfl
              rw [evalHOLExact]; simp only [hwf1, ↓reduceIte]
              rw [hs0]; simp [memLoadHOLExact, panMemLoadHOL, hnd]
            rw [ha0, hl0]
          rw [evaluateHOLFiniteState_seq_line780]
          rcases hr0 : evaluateHOLFiniteState (decClockHOLFinite s1)
              (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")]))) with ⟨r0, m0⟩
          rw [hr0] at hst0; dsimp only at hst0; subst hst0
          rfl
      · -- `n0 < 32`, so `lp1` exits with `(none, s1)` and `lp2` (`8 ≤ n0`) enters and errors on `load (0 + 0)`!
        have hlp1 : evaluateHOLFiniteState s1
            (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 32)]))
              (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                      (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
                (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 8)])
                        (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 8)])))
                  (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 16)])
                          (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 16)])))
                    (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 24)])
                            (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 24)])))
                      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 32)]))))))) =
            (none, s1) := by
          rw [evaluateHOLFiniteState_while_fixClockRewrite]
          have hc1 : @evalHOLFinite 64 F _ s1 (fun a => Classical.propDecidable (s1.memaddrs a))
              (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 32)])) =
              some (.val (.word 0)) := by
            rw [evalHOLFinite_eq_toExact]
            simp only [evalHOLExact, evalListHOLExact, hs1_n, hs1_i, wordOpHOL, wordOp, valueIsWord, valueWord,
              List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero,
              Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
            have h032 : (0 + (32#64 + 0)).toNat = 32 := by decide
            rw [h032]; simp [show n0.toNat < 32 by omega]
          simp only [hc1]
          have h00 : ¬ ((0 : BitVec 64) ≠ 0) := by decide
          rw [if_neg h00]
        simp only [hlp1] at hnt' ⊢
        rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt' ⊢
        have hc2 : @evalHOLFinite 64 F _ s1 (fun a => Classical.propDecidable (s1.memaddrs a))
            (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)])) =
            some (.val (.word 1)) := by
          rw [evalHOLFinite_eq_toExact]
          simp only [evalHOLExact, evalListHOLExact, hs1_n, hs1_i, wordOpHOL, wordOp, valueIsWord, valueWord,
            List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero,
            Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
          have h08 : (0 + (8#64 + 0)).toNat = 8 := by decide
          rw [h08]; simp [show ¬ (n0.toNat < 8) by omega]
        simp only [hc2] at hnt' ⊢
        have h10 : (1 : BitVec 64) ≠ 0 := by decide
        rw [if_pos h10] at hnt' ⊢
        by_cases hk0 : s1.clock = 0
        · simp [hk0] at hnt'
        · rw [if_neg hk0]
          have hst0 : (evaluateHOLFiniteState (decClockHOLFinite s1)
              (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))).1 =
              some .error := by
            rw [evaluateHOLFiniteState_store]
            have hd' : (decClockHOLFinite s1).locals.lookup (ofString "dst") = some (.val (.word dst0)) := hs1_dst
            have hs' : (decClockHOLFinite s1).locals.lookup (ofString "src") = some (.val (.word 0)) := hs1_src
            have hi' : (decClockHOLFinite s1).locals.lookup (ofString "i") = some (.val (.word 0)) := hs1_i
            have ha0 : @evalHOLExact 64 F _ (decClockHOLFinite s1).toExact
                (fun a => Classical.propDecidable ((decClockHOLFinite s1).memaddrs a))
                (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) =
                some (.val (.word (dst0 + 0))) := by
              simp [evalHOLExact, evalListHOLExact, decClockHOLExact, PanSemStateFiniteExact.toExact,
                hd', hi', wordOpHOL, wordOp, valueIsWord, valueWord]
            have hl0 : @evalHOLExact 64 F _ (decClockHOLFinite s1).toExact
                (fun a => Classical.propDecidable ((decClockHOLFinite s1).memaddrs a))
                (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])) = none := by
              have hs0 : @evalHOLExact 64 F _ (decClockHOLFinite s1).toExact
                  (fun a => Classical.propDecidable ((decClockHOLFinite s1).memaddrs a))
                  (.op .add [.var .local (ofString "src"), .var .local (ofString "i")]) =
                  some (.val (.word 0)) := by
                simp [evalHOLExact, evalListHOLExact, decClockHOLExact, PanSemStateFiniteExact.toExact,
                  hs', hi', wordOpHOL, wordOp, valueIsWord, valueWord]
              have hnd : ¬ (decClockHOLFinite s1).memaddrs 0#64 := by
                change ¬ s.memaddrs (0 : BitVec 64); rw [hma]; exact hnot_dom0
              have hwf1 : isWfShapeExactHOL (decClockHOLFinite s1).toExact.structs ShapeHOL.one = true := rfl
              rw [evalHOLExact]; simp only [hwf1, ↓reduceIte]
              rw [hs0]; simp [memLoadHOLExact, panMemLoadHOL, hnd]
            rw [ha0, hl0]
          rw [evaluateHOLFiniteState_seq_line780]
          rcases hr0 : evaluateHOLFiniteState (decClockHOLFinite s1)
              (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")]))) with ⟨r0, m0⟩
          rw [hr0] at hst0; dsimp only at hst0; subst hst0
          rfl

private theorem call_memcpy_src_zero_pos_impossible {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (dstExp srcExp nExp : ExpHOL 64) (dst0 n0 : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp =
      some (.val (.word 0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hn_ge8 : 8 ≤ n0.toNat)
    (t : PanSemStateFiniteExact 64 F)
    (hcall : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) =
      (none, t)) : False := by
  rw [evaluateHOLFiniteState_call] at hcall
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, srcExp, nExp] = some [.val (.word dst0), .val (.word 0), .val (.word n0)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, hdst, hsrc, hn]
  have hlook := pan_three_word_lookup s.code.lookup (ofString "memcpy")
    (ofString "dst") (ofString "src") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_memcpy) dst0 0 n0
    (by decide) (by decide) (by decide) (by rw [hcode]; exact M11.lookup_memcpy)
  rw [hargs] at hcall; dsimp only at hcall; rw [hlook] at hcall; dsimp only at hcall
  split at hcall
  · simp at hcall
  · let cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
      ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
        (ofString "src", ValueHOL.val (.word 0))).update (ofString "n", ValueHOL.val (.word n0))
    let entry := callEntryStateHOLFinite s cmap
    have hent_dst : entry.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "dst" by decide, show ofString "src" ≠ ofString "dst" by decide]
    have hent_src : entry.locals.lookup (ofString "src") = some (.val (.word 0)) := by
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "src" by decide]
    have hent_n : entry.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    change (match evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_memcpy) with | _ => _) = (none, t) at hcall
    rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_memcpy) with ⟨br, bs⟩
    rw [hb] at hcall
    have hbr_nt : br ≠ some .timeOut := by
      rintro rfl; simp at hcall
    have herr := memcpy_src_zero_pos_err entry dst0 n0 hma hent_dst hent_src hent_n hn_ge8 (by rw [hb]; exact hbr_nt)
    rw [hb] at herr; dsimp only at herr; subst herr
    simp at hcall

private theorem lst_push_memcpy_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (dstExp srcExp nExp : ExpHOL 64) (dst0 src0 n0 : BitVec 64) (cont : ProgHOL 64)
    (hcode : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp =
      some (.val (.word src0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hres : (evaluateHOLFiniteState s
        (.seq (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) cont)).1 = none ∨
      Resumes (evaluateHOLFiniteState s
        (.seq (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) cont)).1) :
    ∃ t : PanSemStateFiniteExact 64 F,
      t.locals = s.locals ∧
      t.globals = s.globals ∧
      R13Shards.MemWriteFrame s t (dst0.toNat, n0.toNat) ∧
      R13Shards.BytesCopiedUpTo s t dst0 src0 n0.toNat n0.toNat ∧
      (8 ≤ n0.toNat → src0.toNat ≠ 0) ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) cont) =
        evaluateHOLFiniteState t cont := by
  rw [evaluateHOLFiniteState_seq_line780] at hres
  rcases hcall : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) with ⟨rc, t⟩
  rw [hcall] at hres
  cases rc with
  | none =>
    obtain ⟨hloc, hmwf, hcp, _⟩ :=
      R13Shards.call_memcpy_step s dstExp srcExp nExp dst0 src0 n0 hcode hG hdst hsrc hn t hcall
    have hsrc_nz : 8 ≤ n0.toNat → src0.toNat ≠ 0 := by
      intro hge8 hz
      have hsrc0 : src0 = 0 := BitVec.eq_of_toNat_eq hz
      subst hsrc0
      exact call_memcpy_src_zero_pos_impossible s dstExp srcExp nExp dst0 n0
        hcode hG.memaddrs hdst hsrc hn hge8 t hcall
    refine ⟨t, hloc, hmwf.2.2.2.2.2.1, hmwf, hcp, hsrc_nz, ?_⟩
    rw [evaluateHOLFiniteState_seq_line780, hcall]
  | some rc' =>
    exfalso
    dsimp only at hres
    rcases hres with hnone | hres'
    · simp at hnone
    · have hnt : (evaluateHOLFiniteState s
          (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).1 ≠ some .timeOut := by
        rw [hcall]
        rintro ⟨⟩
        rcases hres' with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      have hbre := M11.eval_call_memcpy_bre s dstExp srcExp nExp dst0 src0 n0 [(dst0.toNat, n0.toNat)]
        hcode hG.memaddrs hdst hsrc hn
        (fun _ => ⟨(dst0.toNat, n0.toNat), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩) hnt
      rw [hcall] at hbre
      exact hbre.2 (by simp) hres'

private theorem bo_l40_ne_l72 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hF : FixedTyped s) (hbo_nz : globN s "bo" ≠ 0)
    (h40_nz : memW s (globN s "bo" + 40) ≠ 0) :
    memW s (globN s "bo" + 40) ≠ memW s (globN s "bo" + 72) := by
  intro heq
  have h72_nz : memW s (globN s "bo" + 72) ≠ 0 := heq ▸ h40_nz
  obtain ⟨_, hbo_pw, _, _, _⟩ := R13Shards.fixedObjects_disj_parts hF
  have hlen : (blockOutObjects s).length = 7 := by
    unfold blockOutObjects
    simp [hbo_nz, h40_nz, h72_nz]
  have heq3 : (blockOutObjects s)[3]'(by omega) = (memW s (globN s "bo" + 40), 24) := by
    unfold blockOutObjects
    simp [hbo_nz, h40_nz, h72_nz]
  have heq5 : (blockOutObjects s)[5]'(by omega) = (memW s (globN s "bo" + 72), 24) := by
    unfold blockOutObjects
    simp [hbo_nz, h40_nz, h72_nz]
  have hget := (List.pairwise_iff_getElem.1 hbo_pw) 3 5 (by omega) (by omega) (by omega)
  rw [heq3, heq5, ← heq] at hget
  unfold Disj at hget
  dsimp only at hget
  omega

private theorem cellHits_disj_false {a : Nat} {i j : Ivl}
    (ha8 : a % 8 = 0) (hi0 : i.2 = 0 → i.1 % 8 = 0) (hj0 : j.2 = 0 → j.1 % 8 = 0)
    (hi8 : i.2 ≠ 0 → i.1 % 8 = 0 ∧ i.2 % 8 = 0)
    (hi : CellHits a i) (hj : CellHits a j) (hd : Disj i j) : False := by
  unfold CellHits at hi hj
  by_cases hiz : i.2 = 0
  · have := hi0 hiz; omega
  · obtain ⟨hi1, hi2⟩ := hi8 hiz
    rcases hd with h0 | h0 | h | h
    · exact hiz h0
    · have := hj0 h0; omega
    · omega
    · omega

private theorem nodeExtents_zero_or_allocated {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hNH : NodeHeap s Nd) {o : Ivl} (ho : o ∈ nodeExtents s Nd) :
    o = (0, 0) ∨ (o.2 ≠ 0 ∧ Allocated s o) := by
  unfold nodeExtents at ho
  obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
  rcases hno with rfl | rfl
  · exact Or.inr ⟨by unfold nodeIvl nodeSize; dsimp only; split_ifs <;> omega, (hNH.1 n hn).2.1⟩
  · unfold nodePath
    split
    · rename_i hcond
      rcases (hNH.1 n hn).2.2.2.2.2.2.1 hcond.1 with h0 | ⟨_, hal, _⟩
      · exact absurd h0 hcond.2
      · exact Or.inr ⟨hcond.2, hal⟩
    · exact Or.inl rfl

private theorem lst_push_bo_disj_fixed {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hWT : WorldTypedWith s S Nd) (hbo_nz : globN s "bo" ≠ 0)
    {l : Nat} (hl_nz : l ≠ 0)
    (hl_choice : l = memW s (globN s "bo" + 40) ∨ l = memW s (globN s "bo" + 72)) :
    (l, 24) ∈ blockOutObjects s ∧
    (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj i (l, 24)) ∧
    (globN s "ws" ≠ 0 → Disj (globN s "ws", 40) (l, 24)) ∧
    (globN s "bs" ≠ 0 → Disj (globN s "bs", 80) (l, 24)) ∧
    (globN s "ts" ≠ 0 → Disj (globN s "ts", 72) (l, 24)) ∧
    Disj (globN s "bo", 88) (l, 24) ∧
    (globN s "journal_cap" ≠ 0 → Disj (globN s "journal", 32 * globN s "journal_cap") (l, 24)) ∧
    (∀ i ∈ balObjects s, Disj i (l, 24)) ∧
    (∀ o ∈ nodeExtents s Nd, Disj o (l, 24)) := by
  obtain ⟨hT, _, hF, hTr⟩ := hWT
  have hl_bo : (l, 24) ∈ blockOutObjects s := by
    rcases hl_choice with h40 | h72
    · subst h40; unfold blockOutObjects; simp [hbo_nz, hl_nz]
    · subst h72; unfold blockOutObjects; simp [hbo_nz, hl_nz]
  have hl_fix : (l, 24) ∈ fixedObjects s := by
    unfold fixedObjects; apply List.mem_append_left; apply List.mem_append_right; exact hl_bo
  obtain ⟨_, _, hgb_rest, hjr_rest, hbo_bal⟩ := R13Shards.fixedObjects_disj_parts hF
  have hl_in_bo_bal : (l, 24) ∈ blockOutObjects s ++ balObjects s :=
    List.mem_append_left _ hl_bo
  have hl_in_all_rest : (l, 24) ∈
      [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
        blockOutObjects s ++ balObjects s := by
    simp only [List.mem_append]
    exact Or.inl (Or.inr hl_bo)
  have hgb_disj : ∀ (g : String) (sz : Nat), (g, sz) ∈ globalBuffers → globN s g ≠ 0 →
      Disj (globN s g, sz) (l, 24) := by
    intro g sz hgb hgnz
    have hm : (globN s g, sz) ∈ (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) :=
      List.mem_map.2 ⟨(g, sz), hgb, by simp [hgnz]⟩
    exact hgb_rest _ hm _ hl_in_all_rest
  refine ⟨hl_bo, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht i hi
    exact ((hT.2.1 t ht).2 i hi).2 _ hl_fix
  · exact hgb_disj "ws" 40 (by decide)
  · exact hgb_disj "bs" 80 (by decide)
  · exact hgb_disj "ts" 72 (by decide)
  · exact hgb_disj "bo" 88 (by decide) hbo_nz
  · intro hjnz
    exact hjr_rest _ (by simp [hjnz]) _ hl_in_bo_bal
  · intro i hi
    exact R13Shards.disj_symm (hbo_bal _ hl_bo _ hi)
  · intro o ho
    exact (hTr.2.1 o ho).2 _ hl_fix

private theorem lst_push_sameTypedCells_of_l_and_heap {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hW : WorldOK s) (hAp : ArenaReady post) (hWT : WorldTypedWith s S Nd)
    (hbo_nz : globN s "bo" ≠ 0) {l : Nat} (hl_nz : l ≠ 0)
    (hl_choice : l = memW s (globN s "bo" + 40) ∨ l = memW s (globN s "bo" + 72))
    (hbe : post.be = s.be)
    (hout_dom : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hmem_frame : ∀ a : BitVec 64,
      ¬ CellHits a.toNat (l, 24) →
      ¬ CellHits a.toNat (InitECandidate.Solver.Wave8Contracts.M08.heapFree s) →
      post.memory a = s.memory a)
    (hl_same : memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧
      memW post (l + 16) = memW s (l + 16))
    (hl_words : WordsOK s (l, 24))
    (hl_hi : l + 24 ≤ 2 ^ 64) :
    M13.SameTypedCells s post S Nd := by
  obtain ⟨_, htab_d, hws_d, hbs_d, hts_d, hbo_d, hjr_d, hbal_d, hnd_d⟩ :=
    lst_push_bo_disj_fixed hWT hbo_nz hl_nz hl_choice
  rcases hWT with ⟨hT, hJ, hF, hTr⟩
  have hu_of_disj : ∀ i : Ivl, (i.2 = 0 → i.1 = 0) →
      Disj i (l, 24) → Disj i (InitECandidate.Solver.Wave8Contracts.M08.heapFree s) →
      R13Shards.IvlUnhit s post i := by
    intro i hi0 hdl hdh a ha8 hhit
    have hi0_8 : i.2 = 0 → i.1 % 8 = 0 := fun hz => by simp [hi0 hz]
    have hhp8 : globN s "heap_ptr" % 8 = 0 := hW.1.2.2.2.2.2.2.1
    apply hmem_frame a
    · intro hl_hit
      exact cellHits_disj_false ha8 (by simp) hi0_8
        (fun _ => ⟨hl_words.1, by simp⟩) hl_hit hhit (R13Shards.disj_symm hdl)
    · intro hh_hit
      have hhf_align : (InitECandidate.Solver.Wave8Contracts.M08.heapFree s).2 ≠ 0 →
          (InitECandidate.Solver.Wave8Contracts.M08.heapFree s).1 % 8 = 0 ∧
          (InitECandidate.Solver.Wave8Contracts.M08.heapFree s).2 % 8 = 0 := by
        intro _
        dsimp [InitECandidate.Solver.Wave8Contracts.M08.heapFree]
        rw [M13.heapLimit_val]
        omega
      exact cellHits_disj_false ha8 (fun _ => hhp8) hi0_8
        hhf_align hh_hit hhit (R13Shards.disj_symm hdh)
  have hu_alloc_disj : ∀ i : Ivl, (i = (0, 0) ∨ (i.2 ≠ 0 ∧ Allocated s i)) → Disj i (l, 24) →
      R13Shards.IvlUnhit s post i := by
    intro i hal hdl
    rcases hal with rfl | ⟨hiz, hal'⟩
    · intro a _ hhit
      unfold CellHits at hhit
      dsimp only at hhit
      omega
    · exact hu_of_disj i (fun hz => absurd hz hiz) hdl (M13.allocated_disj_heapFree hW.1.2 hal')
  have hu_fixed_disj : ∀ i : Ivl, i ∈ fixedObjects s → Disj i (l, 24) →
      R13Shards.IvlUnhit s post i := by
    intro i hfix hdl
    have hi0 : i.2 = 0 → i.1 = 0 := R13Shards.fixedObjects_zero_aligned i hfix
    by_cases hiz : i.2 = 0
    · exact hu_alloc_disj i (Or.inl (Prod.ext (hi0 hiz) hiz)) hdl
    · exact hu_alloc_disj i (Or.inr ⟨hiz, ((hF.1 i hfix).resolve_left hiz).1⟩) hdl
  have hcell_not_in_l : ∀ i : Ivl, i ∈ worldTypedIvls s S Nd →
      i = (l, 24) ∨ R13Shards.IvlUnhit s post i := by
    intro i hi
    unfold worldTypedIvls at hi
    simp only [List.mem_append] at hi
    rcases hi with ((((hi_tab | hi_tr) | hi_jr) | hi_bo) | hi_bal) | hi_nd
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 hi_tab
      by_cases hiz : i.2 = 0
      · have hw1 : i.1 % 8 = 0 := ((hT.2.1 t ht).1.1 i hfp).2.1
        exact Or.inr (fun a ha8 hh => by unfold CellHits at hh; omega)
      · exact Or.inr (hu_alloc_disj i (Or.inr ⟨hiz, ((hT.2.1 t ht).2 i hfp).1⟩) (htab_d t ht i hfp))
    · obtain ⟨⟨g, sz⟩, hgsz, rfl⟩ := List.mem_map.1 hi_tr
      by_cases hgnz : globN s g = 0
      · simp only [hgnz, ↓reduceIte]
        exact Or.inr (fun _ _ hh => by unfold CellHits at hh; omega)
      · simp only [hgnz, ↓reduceIte]
        have hm_fix := R13Shards.typedRecord_mem_fixedObjects s hgsz
        simp only [hgnz, ↓reduceIte] at hm_fix
        have hdl : Disj (globN s g, sz) (l, 24) := by
          simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hgsz
          rcases hgsz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hws_d hgnz
          · exact hbs_d hgnz
          · exact hts_d hgnz
          · exact hbo_d
        exact Or.inr (hu_fixed_disj _ hm_fix hdl)
    · simp only [List.mem_singleton] at hi_jr
      subst hi_jr
      by_cases hjnz : globN s "journal_cap" = 0
      · simp only [hjnz, ↓reduceIte, Nat.mul_zero]
        exact Or.inr (hu_alloc_disj _ (Or.inl rfl) (Or.inl rfl))
      · simp only [hjnz, ↓reduceIte]
        rcases hJ.2.2.1 with h0 | ⟨hal, _⟩
        · exact absurd h0 hjnz
        · exact Or.inr (hu_alloc_disj _ (Or.inr ⟨by dsimp only; omega, hal⟩) (hjr_d hjnz))
    · -- `hi_bo : i ∈ blockOutObjects s`
      obtain ⟨_, hbo_pw, _, _, _⟩ := R13Shards.fixedObjects_disj_parts hF
      have hfix_i : i ∈ fixedObjects s := M13.blockOut_in_fixedObjects hi_bo
      -- Check whether `i = (l, 24)` or `Disj i (l, 24)` via `blockOutObjects` indices:
      have hlen_bo : (blockOutObjects s).length = 7 := by
        unfold blockOutObjects
        by_cases h40 : memW s (globN s "bo" + 40) = 0 <;>
          by_cases h72 : memW s (globN s "bo" + 72) = 0 <;>
          simp [hbo_nz, h40, h72]
      obtain ⟨idx, hidx_lt, rfl⟩ := List.getElem_of_mem hi_bo
      rcases hl_choice with h40 | h72
      · -- `l = bo+40`, which is index 3
        have h3_lt : 3 < (blockOutObjects s).length := by omega
        have h3_eq : (blockOutObjects s)[3] = (l, 24) := by
          have hl40_nz : memW s (globN s "bo" + 40) ≠ 0 := h40 ▸ hl_nz
          unfold blockOutObjects
          by_cases h72_z : memW s (globN s "bo" + 72) = 0 <;>
            simp [hbo_nz, hl40_nz, h72_z, h40]
        by_cases hidx3 : idx = 3
        · subst hidx3; exact Or.inl h3_eq
        · right
          apply hu_fixed_disj _ hfix_i
          rcases Nat.lt_or_gt_of_ne hidx3 with hlt | hgt
          · have hd := (List.pairwise_iff_getElem.1 hbo_pw) idx 3 hidx_lt h3_lt hlt
            rwa [h3_eq] at hd
          · have hd := (List.pairwise_iff_getElem.1 hbo_pw) 3 idx h3_lt hidx_lt hgt
            rw [h3_eq] at hd
            exact R13Shards.disj_symm hd
      · -- `l = bo+72`, which is index 5
        have h5_lt : 5 < (blockOutObjects s).length := by omega
        have h5_eq : (blockOutObjects s)[5] = (l, 24) := by
          have hl72_nz : memW s (globN s "bo" + 72) ≠ 0 := h72 ▸ hl_nz
          unfold blockOutObjects
          by_cases h40_z : memW s (globN s "bo" + 40) = 0 <;>
            simp [hbo_nz, h40_z, hl72_nz, h72]
        by_cases hidx5 : idx = 5
        · subst hidx5; exact Or.inl h5_eq
        · right
          apply hu_fixed_disj _ hfix_i
          rcases Nat.lt_or_gt_of_ne hidx5 with hlt | hgt
          · have hd := (List.pairwise_iff_getElem.1 hbo_pw) idx 5 hidx_lt h5_lt hlt
            rwa [h5_eq] at hd
          · have hd := (List.pairwise_iff_getElem.1 hbo_pw) 5 idx h5_lt hidx_lt hgt
            rw [h5_eq] at hd
            exact R13Shards.disj_symm hd
    · have hfix_i : i ∈ fixedObjects s := M13.bal_in_fixedObjects hi_bal
      exact Or.inr (hu_fixed_disj i hfix_i (hbal_d i hi_bal))
    · exact Or.inr (hu_alloc_disj i (nodeExtents_zero_or_allocated hTr.1 hi_nd) (hnd_d i hi_nd))
  have hl_mem_eq : ∀ off ∈ ([0, 8, 16] : List Nat),
      post.memory (BitVec.ofNat 64 (l + off)) = s.memory (BitVec.ofNat 64 (l + off)) := by
    intro off hoff
    have hw_eq : memW post (l + off) = memW s (l + off) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl
      · simpa using hl_same.1
      · exact hl_same.2.1
      · exact hl_same.2.2
    unfold memW at hw_eq
    rcases hm1 : post.memory (BitVec.ofNat 64 (l + off)) with ⟨w1⟩
    rcases hm2 : s.memory (BitVec.ofNat 64 (l + off)) with ⟨w2⟩
    rw [hm1, hm2] at hw_eq
    dsimp only at hw_eq
    congr 1
    exact BitVec.eq_of_toNat_eq hw_eq
  refine ⟨hbe, hAp.1.memaddrs.trans hW.1.1.memaddrs.symm, hW.1.1.memaddrs, ?_, ?_, ?_⟩
  · intro a hna
    exact hout_dom a (by rwa [hW.1.1.memaddrs])
  · intro a ha ha8 ⟨i, hi, ha1, ha2⟩
    rcases hcell_not_in_l i hi with rfl | hu
    · have hl8 : l % 8 = 0 := hl_words.1
      dsimp only at ha1 ha2
      have hoff : a = l + 0 ∨ a = l + 8 ∨ a = l + 16 := by omega
      rcases hoff with rfl | rfl | rfl
      · exact hl_mem_eq 0 (by simp)
      · exact hl_mem_eq 8 (by simp)
      · exact hl_mem_eq 16 (by simp)
    · exact hu (BitVec.ofNat 64 a)
        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]; exact ha8)
        (by unfold CellHits; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]; omega)
  · intro b hb ⟨i, hi, hb1, hb2⟩
    rcases hcell_not_in_l i hi with rfl | hu
    · have hl8 : l % 8 = 0 := hl_words.1
      dsimp only at hb1 hb2
      have hu_l : R13Shards.IvlUnhit s post (l, 24) := by
        intro c hc8 hchit
        unfold CellHits at hchit
        have hc_off : c.toNat = l + 0 ∨ c.toNat = l + 8 ∨ c.toNat = l + 16 := by omega
        have hc_eq : c = BitVec.ofNat 64 c.toNat := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt c.isLt]
        rw [hc_eq]
        rcases hc_off with h0 | h8 | h16
        · rw [h0]; exact hl_mem_eq 0 (by simp)
        · rw [h8]; exact hl_mem_eq 8 (by simp)
        · rw [h16]; exact hl_mem_eq 16 (by simp)
      exact R13Shards.memB_eq_of_ivlUnhit hu_l hbe hl_hi ⟨hb1, hb2⟩
    · have hhi_i : i.1 + i.2 ≤ 2 ^ 64 := by
        rcases M13.worldTypedIvls_allocated ⟨hT, hJ, hF, hTr⟩ hi with h0 | hal
        · omega
        · exact M13.allocated_le_2pow64 hW.1.2 hal
      exact R13Shards.memB_eq_of_ivlUnhit hu hbe hhi_i ⟨hb1, hb2⟩

private theorem lst_push_worldStep_of_bo {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hW : WorldOK s) (hAp : ArenaReady post)
    (hbo_nz : globN s "bo" ≠ 0) {l : Nat} (hl_nz : l ≠ 0)
    (hl_choice : l = memW s (globN s "bo" + 40) ∨ l = memW s (globN s "bo" + 72))
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hG : GlobalsKept ["heap_ptr"] s post)
    (hbe : post.be = s.be)
    (hout_dom : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hmem_frame : ∀ a : BitVec 64,
      ¬ CellHits a.toNat (l, 24) →
      ¬ CellHits a.toNat (InitECandidate.Solver.Wave8Contracts.M08.heapFree s) →
      post.memory a = s.memory a)
    (hl8_ok : 1 ≤ memW post (l + 16) ∧ memW post (l + 8) ≤ memW post (l + 16))
    (hl_arr : (memW post l = memW s l ∧ memW post (l + 16) = memW s (l + 16)) ∨
      (memW post l ≠ 0 ∧ memW post l % 8 = 0 ∧
        Inside (memW post l, 8 * memW post (l + 16)) (globN s "heap_ptr") (globN post "heap_ptr")))
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    (hQ : ∀ S Nd, WorldTypedWith s S Nd → WorldTypedWith post S Nd → Q s r post S Nd) :
    WorldStep (fun _ => []) ["heap_ptr"] M13.stdKeep Q s r post := by
  have hglob_nhp : ∀ nm : String, ofString nm ≠ ofString "heap_ptr" →
      s.globals.lookup (ofString nm) = post.globals.lookup (ofString nm) := by
    intro nm hne
    apply hG
    simp only [List.map, List.mem_cons, List.not_mem_nil, or_false]
    exact hne
  have hg_nhp : ∀ nm : String, ofString nm ≠ ofString "heap_ptr" → globN post nm = globN s nm :=
    fun nm hne => (M13.globN_eq_of_lookup_eq (hglob_nhp nm hne)).symm
  have hsc_eq : globN post "scratch_ptr" = globN s "scratch_ptr" := hg_nhp "scratch_ptr" (by decide)
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := le_of_eq hsc_eq
  have hg_core : ∀ g ∈ M13.coreWorldGlobals, globN post g = globN s g := by
    intro g hg
    have hne : ofString g ≠ ofString "heap_ptr" := by revert g hg; decide
    exact hg_nhp g hne
  -- Prove `RecordsKept (fun _ => []) M13.stdKeep s post`:
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  obtain ⟨_, _, hws_d0, hbs_d0, hts_d0, hbo_d0, _, _, _⟩ :=
    lst_push_bo_disj_fixed hWT0 hbo_nz hl_nz hl_choice
  have hstdKeep_tr : ∀ p ∈ M13.stdKeep, ∀ k ∈ p.2,
      (p.1, match p.1 with | "ws" => 40 | "bs" => 80 | "ts" => 72 | _ => 88) ∈ typedRecords ∧
      k + 8 ≤ (match p.1 with | "ws" => 40 | "bs" => 80 | "ts" => 72 | _ => 88) ∧ k % 8 = 0 := by
    unfold M13.stdKeep; decide
  have hRK : RecordsKept (fun _ => []) M13.stdKeep s post := by
    intro ⟨g, ks⟩ hgk hgnz k hk _
    dsimp only at hgnz hk ⊢
    have hmem_tr := hstdKeep_tr (g, ks) hgk k hk
    set sz := match g with | "ws" => 40 | "bs" => 80 | "ts" => 72 | _ => 88
    have hm_fix := R13Shards.typedRecord_mem_fixedObjects s hmem_tr.1
    simp only [hgnz, ↓reduceIte] at hm_fix
    obtain ⟨_, _, hF0, _⟩ := hWT0
    obtain ⟨hal, hw⟩ := (hF0.1 _ hm_fix).resolve_left (by
      have := hmem_tr.2.1; omega)
    have hhi := (R13Shards.ivl_allocated_bound hW.1.2 hal).2
    have hdl : Disj (globN s g, sz) (l, 24) := by
      have htr := hmem_tr.1
      simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at htr
      rcases htr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hws_d0 hgnz
      · exact hbs_d0 hgnz
      · exact hts_d0 hgnz
      · exact hbo_d0
    have hdh := M13.allocated_disj_heapFree hW.1.2 hal
    have hu : R13Shards.IvlUnhit s post (globN s g, sz) := by
      intro a ha8 hhit
      have hhp8 : globN s "heap_ptr" % 8 = 0 := hW.1.2.2.2.2.2.2.1
      apply hmem_frame a
      · intro hh; exact cellHits_disj_false ha8 (fun _ => hw.1) (by simp)
          (fun _ => ⟨hw.1, hw.2.1⟩) hhit hh hdl
      · intro hh; exact cellHits_disj_false ha8 (fun _ => hw.1) (fun _ => hhp8)
          (fun _ => ⟨hw.1, hw.2.1⟩) hhit hh hdh
    exact R13Shards.memW_eq_of_ivlUnhit hu (by have := hw.1; have := hmem_tr.2.2; omega) hhi
      ⟨by omega, by have := hmem_tr.2.1; omega⟩
  refine ⟨hAp, hhp, hG, hRK, fun S Nd hWT _ => ?_⟩
  obtain ⟨hl_bo, _, _, _, _, _, _, _, _⟩ :=
    lst_push_bo_disj_fixed hWT hbo_nz hl_nz hl_choice
  have ⟨hT, hJ, hF, hTr⟩ := hWT
  obtain ⟨hl_al, hl_words⟩ := (hF.1 (l, 24) (M13.blockOut_in_fixedObjects hl_bo)).resolve_left (by simp)
  have hl_hi : l + 24 ≤ 2 ^ 64 := M13.allocated_le_2pow64 hW.1.2 hl_al
  have hl8 : l % 8 = 0 := hl_words.1
  -- Build intermediate state `pm` with `post`'s memory except `l+0, l+8, l+16` restored from `s`:
  let m_mid := Wave8Contracts.M26.updW
    (Wave8Contracts.M26.updW
      (Wave8Contracts.M26.updW post.memory (BitVec.ofNat 64 l) (BitVec.ofNat 64 (memW s l)))
      (BitVec.ofNat 64 (l + 8)) (BitVec.ofNat 64 (memW s (l + 8))))
    (BitVec.ofNat 64 (l + 16)) (BitVec.ofNat 64 (memW s (l + 16)))
  let pm : PanSemStateFiniteExact 64 F := { post with memory := m_mid }
  have hg_pm : ∀ nm : String, ofString nm ≠ ofString "heap_ptr" → globN pm nm = globN s nm := hg_nhp
  have hg_core_pm : ∀ g ∈ M13.coreWorldGlobals, globN pm g = globN s g := hg_core
  have hhp_pm : globN s "heap_ptr" ≤ globN pm "heap_ptr" := hhp
  have hsc_pm : globN pm "scratch_ptr" ≤ globN s "scratch_ptr" := hsc
  have hAp_mid : ArenaReady pm := ⟨guestInv_congr (s := post) rfl rfl rfl rfl hAp.1, hAp.2⟩
  have hbv_ne : ∀ (o1 o2 : Nat), o1 < 24 → o2 < 24 → o1 ≠ o2 →
      BitVec.ofNat 64 (l + o1) ≠ BitVec.ofNat 64 (l + o2) := by
    intro o1 o2 h1 h2 hne heq
    have := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hm_w_lt : ∀ off : Nat, memW s (l + off) < 2 ^ 64 := by
    intro off; unfold memW
    cases s.memory (BitVec.ofNat 64 (l + off)) with | word w => exact w.isLt
  have hl_same_mid : memW pm l = memW s l ∧ memW pm (l + 8) = memW s (l + 8) ∧
      memW pm (l + 16) = memW s (l + 16) := by
    refine ⟨?_, ?_, ?_⟩
    · unfold memW
      change (match m_mid (BitVec.ofNat 64 (l + 0)) with | .word v => v.toNat) = memW s (l + 0)
      unfold m_mid Wave8Contracts.M26.updW
      rw [if_neg (hbv_ne 0 16 (by omega) (by omega) (by omega)),
          if_neg (hbv_ne 0 8 (by omega) (by omega) (by omega)),
          Nat.add_zero, if_pos rfl]
      dsimp only
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa using hm_w_lt 0)]
    · unfold memW
      change (match m_mid (BitVec.ofNat 64 (l + 8)) with | .word v => v.toNat) = memW s (l + 8)
      unfold m_mid Wave8Contracts.M26.updW
      rw [if_neg (hbv_ne 8 16 (by omega) (by omega) (by omega)), if_pos rfl]
      dsimp only
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hm_w_lt 8)]
    · unfold memW
      change (match m_mid (BitVec.ofNat 64 (l + 16)) with | .word v => v.toNat) = memW s (l + 16)
      unfold m_mid Wave8Contracts.M26.updW
      rw [if_pos rfl]
      dsimp only
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hm_w_lt 16)]
  have hout_dom_mid : ∀ a : BitVec 64, ¬ s.memaddrs a → pm.memory a = s.memory a := by
    intro a hna
    have hdom_k : ∀ k : Nat, k < 3 → s.memaddrs (BitVec.ofNat 64 (l + 8 * k)) := fun k hk =>
      (hl_words.2.2 k (by dsimp only; omega)).choose_spec.1
    have hne0 : a ≠ BitVec.ofNat 64 l := by
      rintro rfl; exact hna (by simpa using hdom_k 0 (by omega))
    have hne8 : a ≠ BitVec.ofNat 64 (l + 8) := by
      rintro rfl; exact hna (by simpa using hdom_k 1 (by omega))
    have hne16 : a ≠ BitVec.ofNat 64 (l + 16) := by
      rintro rfl; exact hna (by simpa using hdom_k 2 (by omega))
    change m_mid a = s.memory a
    unfold m_mid Wave8Contracts.M26.updW
    rw [if_neg hne16, if_neg hne8, if_neg hne0]
    exact hout_dom a hna
  have hmem_frame_mid : ∀ a : BitVec 64,
      ¬ CellHits a.toNat (l, 24) →
      ¬ CellHits a.toNat (InitECandidate.Solver.Wave8Contracts.M08.heapFree s) →
      pm.memory a = s.memory a := by
    intro a hnl hnh
    have hne_off : ∀ off : Nat, off + 8 ≤ 24 → a ≠ BitVec.ofNat 64 (l + off) := by
      intro off hoff heq
      subst heq
      apply hnl
      unfold CellHits
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      dsimp only; omega
    change m_mid a = s.memory a
    unfold m_mid Wave8Contracts.M26.updW
    rw [if_neg (hne_off 16 (by omega)), if_neg (hne_off 8 (by omega)),
        if_neg (by simpa using hne_off 0 (by omega))]
    exact hmem_frame a hnl hnh
  have hcell_mid : M13.SameTypedCells s pm S Nd :=
    lst_push_sameTypedCells_of_l_and_heap hW hAp_mid ⟨hT, hJ, hF, hTr⟩ hbo_nz hl_nz hl_choice
      hbe hout_dom_mid hmem_frame_mid hl_same_mid hl_words hl_hi
  have hfeq_mid : fixedObjects pm = fixedObjects s := by
    unfold fixedObjects
    rw [M13.blockOutObjects_eq hW.1.2 hF hcell_mid (hg_core_pm "bo" (by decide)),
        M13.balObjects_eq hW.1.2 hT hF hcell_mid (hg_core_pm "bal_accounts" (by decide)),
        hg_core_pm "journal" (by decide), hg_core_pm "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" := by revert gn hgn; decide
    rw [hg_pm gn.1 hne]
  have hFT_mid := M13.fixedTyped_of_eq hAp_mid hF hhp_pm hsc_pm hfeq_mid
  obtain ⟨hWT_mid, _⟩ := M13.worldTypedWith_congr_w1 hW.1 hAp_mid hhp_pm hsc_pm hg_core_pm hcell_mid
    ⟨hT, hJ, hF, hTr⟩ ⟨hFT_mid, fun o ho => Or.inl (by rw [← hfeq_mid]; exact ho)⟩
  -- Now compare `pm` and `post`! They have identical globals and memory everywhere outside `(l, 24)`!
  have hg_pm_post : ∀ name, globN post name = globN pm name := fun _ => rfl
  have hpm_post_unhit : ∀ i : Ivl, (i.2 = 0 → i.1 % 8 = 0) → Disj i (l, 24) →
      R13Shards.IvlUnhit pm post i := by
    intro i hi0 hdi a ha8 hhit
    have hne_off : ∀ off ∈ ([0, 8, 16] : List Nat), a ≠ BitVec.ofNat 64 (l + off) := by
      intro off hoff heq
      subst heq
      have hoff_ub : off + 8 ≤ 24 ∧ off % 8 = 0 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
        rcases hoff with rfl | rfl | rfl <;> omega
      have hat : (BitVec.ofNat 64 (l + off)).toNat = l + off := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [hat] at ha8 hhit
      exact R13Shards.not_cellHits_of_disj ha8 hi0
        ⟨by dsimp only; omega, by dsimp only; omega⟩ (R13Shards.disj_symm hdi) hhit
    symm
    change m_mid a = post.memory a
    unfold m_mid Wave8Contracts.M26.updW
    rw [if_neg (hne_off 16 (by simp)), if_neg (hne_off 8 (by simp)),
        if_neg (by simpa using hne_off 0 (by simp))]
  -- Transfer `WorldTypedWith pm S Nd` -> `WorldTypedWith post S Nd`:
  have hbo_post_nz : globN post "bo" ≠ 0 := by rwa [hg_core "bo" (by decide)]
  have hbo_pm_nz : globN pm "bo" ≠ 0 := hbo_post_nz
  have hl_choice_m : l = memW pm (globN pm "bo" + 40) ∨ l = memW pm (globN pm "bo" + 72) := by
    have hebo : globN pm "bo" = globN s "bo" := hg_core_pm "bo" (by decide)
    have he40 := M13.memW_typedRec_eq hW.1.2 hF hcell_mid (sz := 88) (by decide) hbo_nz (k := 40) (by omega)
    have he72 := M13.memW_typedRec_eq hW.1.2 hF hcell_mid (sz := 88) (by decide) hbo_nz (k := 72) (by omega)
    rw [hebo, he40, he72]; exact hl_choice
  obtain ⟨hl_bo_m, htab_dm, hws_dm, hbs_dm, hts_dm, hbo_dm, hjr_dm, hbal_dm, hnd_dm⟩ :=
    lst_push_bo_disj_fixed hWT_mid hbo_pm_nz hl_nz hl_choice_m
  rcases hWT_mid with ⟨hT_m, hJ_m, hF_m, hTr_m⟩
  -- Show `FixedTyped post` and `hfix_sub`:
  have hdisj_fresh : ∀ i : Ivl, (i.2 = 0 ∨ Allocated s i) →
      ∀ o : Ivl, Inside o (globN s "heap_ptr") (globN post "heap_ptr") → Disj i o := by
    intro i hi o ho
    rcases hi with h0 | hal
    · exact Or.inl h0
    · rcases hal with ⟨_, hi2⟩ | ⟨hi1, _⟩
      · exact Or.inr (Or.inr (Or.inl (le_trans hi2 ho.1)))
      · have hp_lim := hAp.2.2.1
        have hs_fr := hW.1.2.2.2.1
        have hs_gap := hW.1.2.2.2.2.1
        rw [M13.heapLimit_val] at hp_lim
        rw [M13.scratchStart_val] at hs_fr
        exact Or.inr (Or.inr (Or.inr (le_trans (le_trans ho.2 hp_lim) (le_trans hs_fr (le_trans hs_gap hi1)))))
  have hbo_words_pm_post : ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN pm "bo" + k) = memW pm (globN pm "bo" + k) := by
    intro k hk
    have hk_p : k % 8 = 0 ∧ k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    exact R13Shards.rec_word_eq_of_unhit (post := post) hAp_mid.2 hF_m "bo" 88 (by decide)
      (hg_pm_post "bo") hbo_pm_nz (hpm_post_unhit _ (by simp) hbo_dm) hk_p.1 hk_p.2
  have hother_lst_eq : ∀ k ∈ ([40, 72] : List Nat), memW pm (globN pm "bo" + k) ≠ 0 →
      memW pm (globN pm "bo" + k) ≠ l →
      memW post (memW pm (globN pm "bo" + k)) = memW pm (memW pm (globN pm "bo" + k)) ∧
      memW post (memW pm (globN pm "bo" + k) + 8) = memW pm (memW pm (globN pm "bo" + k) + 8) ∧
      memW post (memW pm (globN pm "bo" + k) + 16) = memW pm (memW pm (globN pm "bo" + k) + 16) := by
    intro k hk hknz hne_l
    obtain ⟨_, hbo_pw_m, _, _, _⟩ := R13Shards.fixedObjects_disj_parts hF_m
    have hdisj_kl : Disj (memW pm (globN pm "bo" + k), 24) (l, 24) := by
      have hlen_m : (blockOutObjects pm).length = 7 := by
        unfold blockOutObjects
        by_cases h40 : memW pm (globN pm "bo" + 40) = 0 <;>
          by_cases h72 : memW pm (globN pm "bo" + 72) = 0 <;>
          simp [hbo_pm_nz, h40, h72]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · rcases hl_choice_m with h40 | h72
        · exact absurd h40.symm hne_l
        · have h72_nz : memW pm (globN pm "bo" + 72) ≠ 0 := h72 ▸ hl_nz
          have hd := (List.pairwise_iff_getElem.1 hbo_pw_m) 3 5 (by omega) (by omega) (by omega)
          have h3 : (blockOutObjects pm)[3]'(by omega) = (memW pm (globN pm "bo" + 40), 24) := by
            unfold blockOutObjects; simp [hbo_pm_nz, hknz, h72_nz]
          have h5 : (blockOutObjects pm)[5]'(by omega) = (l, 24) := by
            unfold blockOutObjects; simp [hbo_pm_nz, hknz, h72_nz, h72]
          rwa [h3, h5] at hd
      · rcases hl_choice_m with h40 | h72
        · have h40_nz : memW pm (globN pm "bo" + 40) ≠ 0 := h40 ▸ hl_nz
          have hd := (List.pairwise_iff_getElem.1 hbo_pw_m) 3 5 (by omega) (by omega) (by omega)
          have h3 : (blockOutObjects pm)[3]'(by omega) = (l, 24) := by
            unfold blockOutObjects; simp [hbo_pm_nz, h40_nz, hknz, h40]
          have h5 : (blockOutObjects pm)[5]'(by omega) = (memW pm (globN pm "bo" + 72), 24) := by
            unfold blockOutObjects; simp [hbo_pm_nz, h40_nz, hknz]
          rw [h3, h5] at hd
          exact R13Shards.disj_symm hd
        · exact absurd h72.symm hne_l
    have hmem_bo_k : (memW pm (globN pm "bo" + k), 24) ∈ blockOutObjects pm := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> (unfold blockOutObjects; simp [hbo_pm_nz, hknz])
    obtain ⟨hal_k, hw_k⟩ := (hF_m.1 _ (M13.blockOut_in_fixedObjects hmem_bo_k)).resolve_left (by simp)
    have hhi_k := M13.allocated_le_2pow64 hAp_mid.2 hal_k
    have hk8 : memW pm (globN pm "bo" + k) % 8 = 0 := hw_k.1
    have hu_k := hpm_post_unhit _ (by simp) hdisj_kl
    exact ⟨by simpa using R13Shards.memW_eq_of_ivlUnhit hu_k (by omega) hhi_k ⟨by omega, by omega⟩,
      R13Shards.memW_eq_of_ivlUnhit hu_k (by omega) hhi_k ⟨by omega, by omega⟩,
      R13Shards.memW_eq_of_ivlUnhit hu_k (by omega) hhi_k ⟨by omega, by omega⟩⟩
  have hlo_l : sourceBase ≤ l := by
    rcases hl_al with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · have := hW.1.2.2.2.1; have := hW.1.2.2.2.2.1
      rw [M13.sourceBase_val]; rw [M13.scratchStart_val] at *; omega
  have hmem8_pm_post : memW post 8 = memW pm 8 := by
    have hsb : 16 < sourceBase := by decide
    have hd : Disj (8, 8) (l, 24) := Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
    exact R13Shards.memW_eq_of_ivlUnhit (post := post) (hpm_post_unhit (8, 8) (by simp) hd)
      (by omega) (by decide) ⟨by omega, by omega⟩
  have hmem16_pm_post : memW post 16 = memW pm 16 := by
    have hsb : 24 < sourceBase := by decide
    have hd : Disj (16, 8) (l, 24) := Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
    exact R13Shards.memW_eq_of_ivlUnhit (post := post) (hpm_post_unhit (16, 8) (by simp) hd)
      (by omega) (by decide) ⟨by omega, by omega⟩
  have hbal_part := R13Shards.balObjects_eq_of_same_globals (post := post) hAp_mid.2 hT_m hF_m
    (hg_pm_post "bal_accounts") ⟨hmem8_pm_post, hmem16_pm_post⟩
    (fun t ht i hi => hpm_post_unhit i (fun _ => ((hT_m.2.1 t ht).1.1 i hi).2.1) (htab_dm t ht i hi))
    (fun i hi => hpm_post_unhit i (fun hz => by
      simp [R13Shards.fixedObjects_zero_aligned i (M13.bal_in_fixedObjects hi) hz]) (hbal_dm i hi))
  -- Now split on `hl_arr`:
  have hfix_typed_and_sub :
      FixedTyped post ∧
      (∀ o ∈ fixedObjects post, o ∈ fixedObjects s ∨ o = (0, 0) ∨
        Inside o (globN s "heap_ptr") (globN post "heap_ptr")) := by
    rcases hl_arr with ⟨hp_eq, hc_eq⟩ | ⟨hp_nz, hp8, hin_hp⟩
    · -- Case 1: `memW post l = memW s l` and `memW post (l + 16) = memW s (l + 16)`
      have hbo_eq_post : blockOutObjects post = blockOutObjects pm := by
        unfold blockOutObjects
        have hg_bo : globN post "bo" = globN pm "bo" := rfl
        simp only [hg_bo, hbo_pm_nz, false_or,
          hbo_words_pm_post 24 (by simp), hbo_words_pm_post 32 (by simp),
          hbo_words_pm_post 40 (by simp), hbo_words_pm_post 56 (by simp),
          hbo_words_pm_post 72 (by simp), hbo_words_pm_post 80 (by simp)]
        congr 1; congr 1
        · by_cases h40 : memW pm (globN pm "bo" + 40) = 0
          · simp [h40]
          · by_cases heq40 : memW pm (globN pm "bo" + 40) = l
            · rw [heq40] at h40 ⊢
              simp [hl_nz, hp_eq, hc_eq, hl_same_mid.1, hl_same_mid.2.2]
            · obtain ⟨e0, _, e16⟩ := hother_lst_eq 40 (by simp) h40 heq40
              simp [h40, e0, e16]
        · by_cases h72 : memW pm (globN pm "bo" + 72) = 0
          · simp [h72]
          · by_cases heq72 : memW pm (globN pm "bo" + 72) = l
            · rw [heq72] at h72 ⊢
              simp [hl_nz, hp_eq, hc_eq, hl_same_mid.1, hl_same_mid.2.2]
            · obtain ⟨e0, _, e16⟩ := hother_lst_eq 72 (by simp) h72 heq72
              simp [h72, e0, e16]
      have hfix_eq_post : fixedObjects post = fixedObjects pm := by
        unfold fixedObjects
        rw [hbo_eq_post, hbal_part.2.1]; rfl
      refine ⟨M13.fixedTyped_of_eq hAp hF_m (le_refl _) (le_refl _) hfix_eq_post, ?_⟩
      intro o ho
      rw [hfix_eq_post, hfeq_mid] at ho
      exact Or.inl ho
    · -- Case 2: `l` reallocated to fresh heap `(memW post l, 8 * memW post (l + 16))`
      set new_arr : Ivl := (memW post l, 8 * memW post (l + 16))
      have hnew_sz_pos : 0 < 8 * memW post (l + 16) := by omega
      have hnew_al : Allocated post new_arr :=
        Or.inl ⟨le_trans hW.1.2.1 hin_hp.1, hin_hp.2⟩
      have hnew_words : WordsOK post new_arr :=
        M13.wordsOK_of_allocated hAp hnew_al hp8 (by dsimp [new_arr]; omega)
      -- Express `fixedObjects post` as `fixedObjects pm` with index `idx_arr` replaced by `new_arr`!
      obtain ⟨hgb_pw, hbo_pw_m, hgb_rest_m, hjr_rest_m, hbo_bal_m⟩ := R13Shards.fixedObjects_disj_parts hF_m
      -- Show `blockOutObjects post` has length 7 and agrees with `blockOutObjects pm` at every index except `4` (if `l = bo+40`) or `6` (if `l = bo+72`)!
      have hbo_len_m : (blockOutObjects pm).length = 7 := by
        unfold blockOutObjects
        by_cases h40 : memW pm (globN pm "bo" + 40) = 0 <;>
          by_cases h72 : memW pm (globN pm "bo" + 72) = 0 <;>
          simp [hbo_pm_nz, h40, h72]
      have hbo_len_post : (blockOutObjects post).length = 7 := by
        unfold blockOutObjects
        by_cases h40 : memW post (globN post "bo" + 40) = 0 <;>
          by_cases h72 : memW post (globN post "bo" + 72) = 0 <;>
          simp [hbo_post_nz, h40, h72]
      have hbo_idx_rel : ∃ aidx : Nat, aidx < 7 ∧
          ∀ (idx : Nat) (h1 : idx < (blockOutObjects post).length)
            (h2 : idx < (blockOutObjects pm).length),
            if idx = aidx then (blockOutObjects post)[idx] = new_arr
            else (blockOutObjects post)[idx] = (blockOutObjects pm)[idx] := by
        have hg_bo : globN post "bo" = globN pm "bo" := rfl
        have hnz_sz : 8 * memW post (l + 16) ≠ 0 := by omega
        rcases hl_choice_m with h40 | h72
        · refine ⟨4, by omega, fun idx h1 h2 => ?_⟩
          have h40_nz : memW pm (globN pm "bo" + 40) ≠ 0 := h40 ▸ hl_nz
          by_cases h72_z : memW pm (globN pm "bo" + 72) = 0
          · rw [hbo_len_post] at h1
            interval_cases idx <;>
              (unfold blockOutObjects;
               simp [hg_bo, hbo_pm_nz,
                 hbo_words_pm_post 24 (by simp), hbo_words_pm_post 32 (by simp),
                 hbo_words_pm_post 40 (by simp), hbo_words_pm_post 56 (by simp),
                 hbo_words_pm_post 72 (by simp), hbo_words_pm_post 80 (by simp),
                 ← h40, hl_nz, h72_z, hp_nz, hnz_sz, new_arr])
          · have hneq72 : memW pm (globN pm "bo" + 72) ≠ l := by
              rw [h40]; exact Ne.symm (bo_l40_ne_l72 hF_m hbo_pm_nz h40_nz)
            obtain ⟨e0_72, _, e16_72⟩ := hother_lst_eq 72 (by simp) h72_z hneq72
            rw [hbo_len_post] at h1
            interval_cases idx <;>
              (unfold blockOutObjects;
               simp [hg_bo, hbo_pm_nz,
                 hbo_words_pm_post 24 (by simp), hbo_words_pm_post 32 (by simp),
                 hbo_words_pm_post 40 (by simp), hbo_words_pm_post 56 (by simp),
                 hbo_words_pm_post 72 (by simp), hbo_words_pm_post 80 (by simp),
                 ← h40, hl_nz, h72_z, e0_72, e16_72, hp_nz, hnz_sz, new_arr])
        · refine ⟨6, by omega, fun idx h1 h2 => ?_⟩
          have h72_nz : memW pm (globN pm "bo" + 72) ≠ 0 := h72 ▸ hl_nz
          by_cases h40_z : memW pm (globN pm "bo" + 40) = 0
          · rw [hbo_len_post] at h1
            interval_cases idx <;>
              (unfold blockOutObjects;
               simp [hg_bo, hbo_pm_nz,
                 hbo_words_pm_post 24 (by simp), hbo_words_pm_post 32 (by simp),
                 hbo_words_pm_post 40 (by simp), hbo_words_pm_post 56 (by simp),
                 hbo_words_pm_post 72 (by simp), hbo_words_pm_post 80 (by simp),
                 ← h72, h40_z, hl_nz, hp_nz, hnz_sz, new_arr])
          · have hneq40 : memW pm (globN pm "bo" + 40) ≠ l := by
              rw [h72]; exact bo_l40_ne_l72 hF_m hbo_pm_nz h40_z
            obtain ⟨e0_40, _, e16_40⟩ := hother_lst_eq 40 (by simp) h40_z hneq40
            rw [hbo_len_post] at h1
            interval_cases idx <;>
              (unfold blockOutObjects;
               simp [hg_bo, hbo_pm_nz,
                 hbo_words_pm_post 24 (by simp), hbo_words_pm_post 32 (by simp),
                 hbo_words_pm_post 40 (by simp), hbo_words_pm_post 56 (by simp),
                 hbo_words_pm_post 72 (by simp), hbo_words_pm_post 80 (by simp),
                 ← h72, h40_z, hl_nz, e0_40, e16_40, hp_nz, hnz_sz, new_arr])
      obtain ⟨aidx, haidx_lt, hidx_spec⟩ := hbo_idx_rel
      have hbo_mem_post : ∀ o ∈ blockOutObjects post, o ∈ blockOutObjects pm ∨ o = new_arr := by
        intro o ho
        obtain ⟨idx, h1, rfl⟩ := List.getElem_of_mem ho
        have h2 : idx < (blockOutObjects pm).length := by omega
        have hsp := hidx_spec idx h1 h2
        by_cases he : idx = aidx
        · rw [if_pos he] at hsp; exact Or.inr hsp
        · rw [if_neg he] at hsp; exact Or.inl (hsp ▸ List.getElem_mem h2)
      have hfix_mem_post : ∀ o ∈ fixedObjects post, o ∈ fixedObjects s ∨ o = new_arr := by
        intro o ho
        unfold fixedObjects at ho
        simp only [List.mem_append] at ho
        rcases ho with ((ho_gb | ho_jr) | ho_bo) | ho_bal
        · left; rw [← hfeq_mid]; unfold fixedObjects
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ho_gb))
        · left; rw [← hfeq_mid]; unfold fixedObjects
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ho_jr))
        · rcases hbo_mem_post o ho_bo with ho_m | rfl
          · left; rw [← hfeq_mid]; exact M13.blockOut_in_fixedObjects ho_m
          · exact Or.inr rfl
        · left; rw [hbal_part.2.1] at ho_bal; rw [← hfeq_mid]; exact M13.bal_in_fixedObjects ho_bal
      have hold_disj_new : ∀ i ∈ fixedObjects s, Disj i new_arr := by
        intro i hi
        exact hdisj_fresh i ((hF.1 i hi).imp id And.left) new_arr hin_hp
      have hbo_pw_post : (blockOutObjects post).Pairwise Disj := by
        rw [List.pairwise_iff_getElem]
        intro i j hi hj hij
        have hi_m : i < (blockOutObjects pm).length := by omega
        have hj_m : j < (blockOutObjects pm).length := by omega
        have hsi := hidx_spec i hi hi_m
        have hsj := hidx_spec j hj hj_m
        by_cases hei : i = aidx
        · rw [if_pos hei] at hsi
          rw [if_neg (show j ≠ aidx by omega)] at hsj
          rw [hsi, hsj]
          exact R13Shards.disj_symm (hold_disj_new _ (by
            rw [← hfeq_mid]; exact M13.blockOut_in_fixedObjects (List.getElem_mem hj_m)))
        · rw [if_neg hei] at hsi
          by_cases hej : j = aidx
          · rw [if_pos hej] at hsj
            rw [hsi, hsj]
            exact hold_disj_new _ (by
              rw [← hfeq_mid]; exact M13.blockOut_in_fixedObjects (List.getElem_mem hi_m))
          · rw [if_neg hej] at hsj
            rw [hsi, hsj]
            exact (List.pairwise_iff_getElem.1 hbo_pw_m) i j hi_m hj_m hij
      have hpw_post : (fixedObjects post).Pairwise Disj := by
        -- `fixedObjects post = gb ++ jr ++ bo_post ++ bal_post`
        -- where `gb = gb_pm`, `jr = jr_pm`, `bal_post = bal_pm`.
        unfold fixedObjects
        rw [hbal_part.2.1]
        -- Group as `(gb ++ jr) ++ (bo_post ++ bal_pm)`:
        rw [List.append_assoc]
        apply List.pairwise_append.2
        refine ⟨?_, ?_, ?_⟩
        · -- `gb ++ jr` pairwise Disj (same as in `pm`)
          have hpw_m := hF_m.2
          unfold fixedObjects at hpw_m
          rw [List.append_assoc] at hpw_m
          exact (List.pairwise_append.1 hpw_m).1
        · apply List.pairwise_append.2
          refine ⟨hbo_pw_post, ?_, ?_⟩
          · have hpw_m := hF_m.2
            unfold fixedObjects at hpw_m
            exact (List.pairwise_append.1 hpw_m).2.1
          · intro x hx y hy
            rcases hbo_mem_post x hx with hx_m | rfl
            · exact hbo_bal_m x hx_m y hy
            · exact R13Shards.disj_symm (hold_disj_new y (by
                rw [← hfeq_mid]; exact M13.bal_in_fixedObjects hy))
        · intro x hx y hy
          simp only [List.mem_append] at hx hy
          rcases hx with hx_gb | hx_jr
          · rcases hy with hy_bo | hy_bal
            · rcases hbo_mem_post y hy_bo with hy_m | rfl
              · exact hgb_rest_m x hx_gb y (by simp [hy_m])
              · exact hold_disj_new x (by
                  rw [← hfeq_mid]; unfold fixedObjects
                  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hx_gb)))
            · exact hgb_rest_m x hx_gb y (by simp [hy_bal])
          · rcases hy with hy_bo | hy_bal
            · rcases hbo_mem_post y hy_bo with hy_m | rfl
              · exact hjr_rest_m x hx_jr y (List.mem_append_left _ hy_m)
              · exact hold_disj_new x (by
                  rw [← hfeq_mid]; unfold fixedObjects
                  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx_jr)))
            · exact hjr_rest_m x hx_jr y (List.mem_append_right _ hy_bal)
      refine ⟨⟨fun i hi => ?_, hpw_post⟩, fun o ho => ?_⟩
      · rcases hfix_mem_post i hi with hi_old | rfl
        · rcases hF.1 i hi_old with h0 | ⟨hal, hw⟩
          · exact Or.inl h0
          · have hal' := M13.allocated_mono hhp hsc hal
            exact Or.inr ⟨hal', M13.wordsOK_of_allocated hAp hal' hw.1 hw.2.1⟩
        · exact Or.inr ⟨hnew_al, hnew_words⟩
      · rcases hfix_mem_post o ho with ho_old | rfl
        · exact Or.inl ho_old
        · exact Or.inr (Or.inr hin_hp)
  have hg_pm_post : ∀ name, globN post name = globN pm name := fun _ => rfl
  have hu_tab_m : ∀ t ∈ S, ∀ i ∈ htabFootprint pm t, R13Shards.IvlUnhit pm post i :=
    fun t ht i hi => hpm_post_unhit i (fun _ => ((hT_m.2.1 t ht).1.1 i hi).2.1) (htab_dm t ht i hi)
  have hu_ws_m : globN pm "ws" ≠ 0 → R13Shards.IvlUnhit pm post (globN pm "ws", 40) :=
    fun h => hpm_post_unhit _ (by simp) (hws_dm h)
  have hu_bs_m : globN pm "bs" ≠ 0 → R13Shards.IvlUnhit pm post (globN pm "bs", 80) :=
    fun h => hpm_post_unhit _ (by simp) (hbs_dm h)
  have hu_ts_m : globN pm "ts" ≠ 0 → R13Shards.IvlUnhit pm post (globN pm "ts", 72) :=
    fun h => hpm_post_unhit _ (by simp) (hts_dm h)
  have hu_jr_m : globN pm "journal_cap" ≠ 0 → R13Shards.IvlUnhit pm post (globN pm "journal", 32 * globN pm "journal_cap") :=
    fun h => hpm_post_unhit _ (fun hz => by dsimp only at hz; omega) (hjr_dm h)
  have hu_bal_m : ∀ i ∈ balObjects pm, R13Shards.IvlUnhit pm post i :=
    fun i hi => hpm_post_unhit i (fun hz => by
      simp [R13Shards.fixedObjects_zero_aligned i (M13.bal_in_fixedObjects hi) hz]) (hbal_dm i hi)
  have hu_nd_m : ∀ o ∈ nodeExtents pm Nd, R13Shards.IvlUnhit pm post o :=
    fun o ho => hpm_post_unhit o (fun hz => by
      rcases nodeExtents_zero_or_allocated hTr_m.1 ho with rfl | ⟨hnez, _⟩
      · simp
      · exact absurd hz hnez) (hnd_dm o ho)
  have hrole_jr_eq : ∀ t, journalRole post t = journalRole pm t := fun t => by
    unfold journalRole
    by_cases h : globN pm "ts" = 0
    · simp [hg_pm_post "ts", h]
    · have hw16 := R13Shards.rec_word_eq_of_unhit hAp_mid.2 hF_m "ts" 72 (by decide) (hg_pm_post "ts") h (hu_ts_m h) (k := 16) (by omega) (by omega)
      have hw32 := R13Shards.rec_word_eq_of_unhit hAp_mid.2 hF_m "ts" 72 (by decide) (hg_pm_post "ts") h (hu_ts_m h) (k := 32) (by omega) (by omega)
      have hw48 := R13Shards.rec_word_eq_of_unhit hAp_mid.2 hF_m "ts" 72 (by decide) (hg_pm_post "ts") h (hu_ts_m h) (k := 48) (by omega) (by omega)
      have hw64 := R13Shards.rec_word_eq_of_unhit hAp_mid.2 hF_m "ts" 72 (by decide) (hg_pm_post "ts") h (hu_ts_m h) (k := 64) (by omega) (by omega)
      simp only [hg_pm_post "ts"] at hw16 hw32 hw48 hw64 ⊢
      rw [hw16, hw32, hw48, hw64]
  have hj_cells : ∀ i, i < globN pm "journal_n" →
      memW post (globN pm "journal" + 32 * i) = memW pm (globN pm "journal" + 32 * i) ∧
      memW post (globN pm "journal" + 32 * i + 16) = memW pm (globN pm "journal" + 32 * i + 16) ∧
      memW post (globN pm "journal" + 32 * i + 24) = memW pm (globN pm "journal" + 32 * i + 24) := by
    intro i hi
    have hcnz : globN pm "journal_cap" ≠ 0 := by have := hJ_m.1; omega
    rcases hJ_m.2.2.1 with h0 | ⟨hal, hwords⟩
    · exact absurd h0 hcnz
    · have hhi := (R13Shards.ivl_allocated_bound hAp_mid.2 hal).2
      have hj8 : (globN pm "journal") % 8 = 0 := hwords.1
      have huj := hu_jr_m hcnz
      have hle : i < globN pm "journal_cap" := lt_of_lt_of_le hi hJ_m.1
      exact ⟨R13Shards.memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩,
        R13Shards.memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩,
        R13Shards.memW_eq_of_ivlUnhit huj (by omega) hhi ⟨by omega, by omega⟩⟩
  have hjrs_eq : journalRoleSlots post = journalRoleSlots pm := by
    unfold journalRoleSlots
    rw [hg_pm_post "journal_n", hg_pm_post "journal"]
    apply List.flatMap_congr
    intro i hi
    rw [List.mem_range] at hi
    obtain ⟨hc0, hc16, hc24⟩ := hj_cells i hi
    simp only [hc0, hc16, hc24, hrole_jr_eq]
  have hJ_post : JournalTyped post S := by
    unfold JournalTyped
    rw [hg_pm_post "journal_n", hg_pm_post "journal_cap", hg_pm_post "journal"]
    refine ⟨hJ_m.1, hJ_m.2.1, ?_, fun i hi => ?_⟩
    · rcases hJ_m.2.2.1 with h0 | ⟨hal, hwords⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hal, R13Shards.wordsOK_transfer hAp_mid.1 hAp.1 hwords⟩
    · rw [(hj_cells i hi).1]; exact hJ_m.2.2.2 i hi
  have hwrs_eq : worldRoleSlots post = worldRoleSlots pm := by
    have hrec_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] =
        recRoles pm "ws" [(16, "ws+16"), (32, "ws+32")] := by
      unfold recRoles
      by_cases h : globN pm "ws" = 0
      · simp [hg_pm_post "ws", h]
      · have hw32 := R13Shards.rec_word_eq_of_unhit hAp_mid.2 hF_m "ws" 40 (by decide) (hg_pm_post "ws") h (hu_ws_m h) (k := 32) (by omega) (by omega)
        have hw16 := R13Shards.rec_word_eq_of_unhit hAp_mid.2 hF_m "ws" 40 (by decide) (hg_pm_post "ws") h (hu_ws_m h) (k := 16) (by omega) (by omega)
        simp only [hg_pm_post "ws"] at hw32 hw16 ⊢
        simp [h, hw32, hw16]
    have hrec_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
        (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
        recRoles pm "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
        (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
      unfold recRoles
      by_cases h : globN pm "bs" = 0
      · simp [hg_pm_post "bs", h]
      · simp only [hg_pm_post "bs", h, ↓reduceIte]
        apply List.map_congr_left
        intro ⟨k, rk⟩ hkr
        have hk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
          rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        have hw := R13Shards.rec_word_eq_of_unhit hAp_mid.2 hF_m "bs" 80 (by decide) (hg_pm_post "bs") h (hu_bs_m h) hk.1 hk.2
        rw [hg_pm_post "bs"] at hw
        simp [hw]
    have hrec_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
        recRoles pm "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
      unfold recRoles
      by_cases h : globN pm "ts" = 0
      · simp [hg_pm_post "ts", h]
      · simp only [hg_pm_post "ts", h, ↓reduceIte]
        apply List.map_congr_left
        intro ⟨k, rk⟩ hkr
        have hk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
          rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        have hw := R13Shards.rec_word_eq_of_unhit hAp_mid.2 hF_m "ts" 72 (by decide) (hg_pm_post "ts") h (hu_ts_m h) hk.1 hk.2
        rw [hg_pm_post "ts"] at hw
        simp [hw]
    have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles pm "bs" "bs.inner" := by
      unfold nestRoles
      by_cases h : globN pm "bs" = 0
      · simp [hg_pm_post "bs", h]
      · have hw32 := R13Shards.rec_word_eq_of_unhit hAp_mid.2 hF_m "bs" 80 (by decide) (hg_pm_post "bs") h (hu_bs_m h) (k := 32) (by omega) (by omega)
        rw [hg_pm_post "bs"] at hw32
        simp only [hg_pm_post "bs", h, ↓reduceIte, hw32]
        by_cases h32 : memW pm (globN pm "bs" + 32) = 0
        · simp [h32]
        · simp only [h32, ↓reduceIte]
          rcases hT_m.2.2.2.2.1 32 (by decide) h with h0 | hmS
          · exact absurd h0 h32
          · rw [R13Shards.htabValues_eq_of_unhit (hT_m.2.1 _ hmS).1 (hu_tab_m _ hmS)]
    have hnest_ts : nestRoles post "ts" "ts.inner" = nestRoles pm "ts" "ts.inner" := by
      unfold nestRoles
      by_cases h : globN pm "ts" = 0
      · simp [hg_pm_post "ts", h]
      · have hw32 := R13Shards.rec_word_eq_of_unhit hAp_mid.2 hF_m "ts" 72 (by decide) (hg_pm_post "ts") h (hu_ts_m h) (k := 32) (by omega) (by omega)
        rw [hg_pm_post "ts"] at hw32
        simp only [hg_pm_post "ts", h, ↓reduceIte, hw32]
        by_cases h32 : memW pm (globN pm "ts" + 32) = 0
        · simp [h32]
        · simp only [h32, ↓reduceIte]
          rcases hT_m.2.2.2.2.2.1 32 (by decide) h with h0 | hmS
          · exact absurd h0 h32
          · rw [R13Shards.htabValues_eq_of_unhit (hT_m.2.1 _ hmS).1 (hu_tab_m _ hmS)]
    unfold worldRoleSlots
    rw [hrec_ws, hrec_bs, hrec_ts, hg_pm_post "bal_accounts", hg_pm_post "bal_idx_accts",
      hg_pm_post "bal_idx_stor", hnest_bs, hnest_ts, hbal_part.1]
    congr 1; congr 1
    apply List.flatMap_congr
    intro ad had
    rw [← hbal_part.1] at had
    obtain ⟨h0, h8, _⟩ := hbal_part.2.2 ad had
    rw [h0, h8]
  have hnd_part := R13Shards.nodeHeap_congr_unhit (post := post) hAp_mid.1 hAp.1 rfl ⟨le_refl _, le_refl _⟩ hTr_m.1 hu_nd_m
  have htab_fp_hdr : ∀ t ∈ S, (∀ k, k < 11 → hdr post t k = hdr pm t k) ∧ htabFootprint post t = htabFootprint pm t := by
    intro t ht
    have hwf := (hT_m.2.1 t ht).1
    have ht_fp : (t, 88) ∈ htabFootprint pm t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have hhi : t + 88 ≤ 2 ^ 64 := by
      have h1 := (hwf.1 _ ht_fp).1.2; dsimp only at h1
      have h2 : heapEnd ≤ 2 ^ 64 := by decide
      omega
    exact R13Shards.htabFootprint_eq_of_hdr_unhit ht8 hhi (hu_tab_m t ht _ ht_fp)
  have hbo_lst_post : globN post "bo" ≠ 0 → ∀ k ∈ ([40, 72] : List Nat),
      memW post (globN post "bo" + k) ≠ 0 → LstOK post (memW post (globN post "bo" + k)) := by
    intro _ k hk hknz
    have hk_eq : memW post (globN pm "bo" + k) = memW pm (globN pm "bo" + k) :=
      hbo_words_pm_post k (by simp at hk; rcases hk with rfl | rfl <;> simp)
    change memW post (globN pm "bo" + k) ≠ 0 at hknz
    rw [hk_eq] at hknz
    change LstOK post (memW post (globN pm "bo" + k))
    rw [hk_eq]
    by_cases heq_l : memW pm (globN pm "bo" + k) = l
    · rw [heq_l]; exact hl8_ok
    · obtain ⟨_, e8, e16⟩ := hother_lst_eq k hk hknz heq_l
      unfold LstOK
      rw [e8, e16]
      exact hT_m.2.2.2.2.2.2.2.2.2.2.1 hbo_pm_nz k hk hknz
  have hT_post : TablesTyped post S := by
    obtain ⟨hndS, hTt_m, hTp_m, hwsR_m, hbsR_m, htsR_m, hgR_m, hbsN_m, htsN_m, hbalT_m, _, hroles_m⟩ := hT_m
    refine ⟨hndS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_lst_post, ?_⟩
    · intro t ht
      rw [(htab_fp_hdr t ht).2]
      have ht_eq_s : htabFootprint pm t = htabFootprint s t :=
        M13.htabFootprint_eq hcell_mid ht (hT.2.1 t ht).1
      refine ⟨R13Shards.htabWF_congr_unhit hAp_mid.1 hAp.1 (hTt_m t ht).1 (hu_tab_m t ht),
        fun i hi => ⟨((hTt_m t ht).2 i hi).1, fun j hj => ?_⟩⟩
      rcases hfix_typed_and_sub.2 j hj with hj_old | rfl | hj_fr
      · rw [← hfeq_mid] at hj_old
        exact ((hTt_m t ht).2 i hi).2 j hj_old
      · exact Or.inr (Or.inl rfl)
      · rw [ht_eq_s] at hi
        exact hdisj_fresh i (Or.inr ((hT.2.1 t ht).2 i hi).1) j hj_fr
    · intro t ht u hu_mem hne
      rw [(htab_fp_hdr t ht).2, (htab_fp_hdr u hu_mem).2]
      exact hTp_m t ht u hu_mem hne
    · intro k hk hnz
      have hwk : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp [wsTableSlots] at hk; rcases hk with rfl | rfl <;> omega
      rw [R13Shards.rec_word_eq_of_unhit hAp_mid.2 hF_m "ws" 40 (by decide) (hg_pm_post "ws") hnz (hu_ws_m hnz) hwk.1 hwk.2]
      exact hwsR_m k hk hnz
    · intro k hk hnz
      have hbk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [R13Shards.rec_word_eq_of_unhit hAp_mid.2 hF_m "bs" 80 (by decide) (hg_pm_post "bs") hnz (hu_bs_m hnz) hbk.1 hbk.2]
      exact hbsR_m k hk hnz
    · intro k hk hnz
      have htk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [R13Shards.rec_word_eq_of_unhit hAp_mid.2 hF_m "ts" 72 (by decide) (hg_pm_post "ts") hnz (hu_ts_m hnz) htk.1 htk.2]
      exact htsR_m k hk hnz
    · exact hgR_m
    · intro hnz hm
      have hw32 := R13Shards.rec_word_eq_of_unhit hAp_mid.2 hF_m "bs" 80 (by decide) (hg_pm_post "bs") hnz (hu_bs_m hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact R13Shards.htabValuesIn_congr_unhit (hTt_m _ hm).1 (hu_tab_m _ hm) (fun _ hx => hx) (hbsN_m hnz hm)
    · intro hnz hm
      have hw32 := R13Shards.rec_word_eq_of_unhit hAp_mid.2 hF_m "ts" 72 (by decide) (hg_pm_post "ts") hnz (hu_ts_m hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact R13Shards.htabValuesIn_congr_unhit (hTt_m _ hm).1 (hu_tab_m _ hm) (fun _ hx => hx) (htsN_m hnz hm)
    · intro ad had
      obtain ⟨h0, h8, _, hkl, hll⟩ := hbal_part.2.2 ad had
      rw [hbal_part.1] at had
      have had_old := hbalT_m ad had
      exact ⟨by rw [h0]; exact had_old.1, by rw [h8]; exact had_old.2.1, hkl, hll⟩
    · unfold RolesOK at hroles_m ⊢
      rw [hwrs_eq, hjrs_eq]
      refine ⟨fun a ha => ?_, hroles_m.2.1, hroles_m.2.2⟩
      obtain ⟨haS, hak⟩ := hroles_m.1 a ha
      rw [(htab_fp_hdr a.1 haS).1 0 (by omega)]
      exact ⟨haS, hak⟩
  have hTr_post : TriesTypedWith post S Nd := by
    refine ⟨hnd_part.1, ?_, ?_⟩
    · intro o ho
      rw [hnd_part.2] at ho
      have ho_eq_s : nodeExtents pm Nd = nodeExtents s Nd := M13.nodeExtents_eq hTr.1 hcell_mid
      refine ⟨fun t ht i hi => ?_, fun j hj => ?_⟩
      · rw [(htab_fp_hdr t ht).2] at hi
        exact (hTr_m.2.1 o ho).1 t ht i hi
      · rcases hfix_typed_and_sub.2 j hj with hj_old | rfl | hj_fr
        · rw [← hfeq_mid] at hj_old
          exact (hTr_m.2.1 o ho).2 j hj_old
        · exact Or.inr (Or.inl rfl)
        · rw [ho_eq_s] at ho
          have ho_al : o.2 = 0 ∨ Allocated s o := by
            rcases M13.worldTypedIvls_allocated hWT (M13.mem_worldTypedIvls_nodeExtents ho) with h0 | hal
            · exact Or.inl h0
            · exact Or.inr hal
          exact hdisj_fresh o ho_al j hj_fr
    · intro hnz
      have hw24 := R13Shards.rec_word_eq_of_unhit hAp_mid.2 hF_m "ws" 40 (by decide) (hg_pm_post "ws") hnz (hu_ws_m hnz) (k := 24) (by omega) (by omega)
      have hw32 := R13Shards.rec_word_eq_of_unhit hAp_mid.2 hF_m "ws" 40 (by decide) (hg_pm_post "ws") hnz (hu_ws_m hnz) (k := 32) (by omega) (by omega)
      rw [hw24, hw32]
      obtain ⟨hr24, hr32⟩ := hTr_m.2.2 hnz
      refine ⟨hr24, fun hm i hi => ?_⟩
      have hwf32 := (hT_m.2.1 _ hm).1
      have hu32 := hu_tab_m _ hm
      have hh32 := htab_fp_hdr _ hm
      rw [hh32.1 3 (by omega)] at hi
      have hvals := R13Shards.htabValues_eq_of_unhit hwf32 hu32
      have hget : (htabValues post (memW pm (globN pm "ws" + 32)))[i]? =
          (htabValues pm (memW pm (globN pm "ws" + 32)))[i]? := by rw [hvals]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hh32.1 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]
      exact hr32 hm i hi
  have hWT_post : WorldTypedWith post S Nd := ⟨hT_post, hJ_post, hfix_typed_and_sub.1, hTr_post⟩
  have hOG : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S Nd) := by
    intro o ho
    unfold worldOwned at ho
    simp only [List.mem_append] at ho
    rcases ho with (ho_tab | ho_fix) | ho_nd
    · obtain ⟨t, ht, hi⟩ := List.mem_flatMap.1 ho_tab
      rw [(htab_fp_hdr t ht).2, M13.htabFootprint_eq hcell_mid ht (hT.2.1 t ht).1] at hi
      refine Or.inr (Or.inl ⟨o, ?_, le_refl _, le_refl _⟩)
      unfold worldOwned
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t, ht, hi⟩))
    · rcases hfix_typed_and_sub.2 o ho_fix with ho_old | rfl | ho_fr
      · refine Or.inr (Or.inl ⟨o, ?_, le_refl _, le_refl _⟩)
        unfold worldOwned
        exact List.mem_append_left _ (List.mem_append_right _ ho_old)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ho_fr)
    · rw [hnd_part.2, M13.nodeExtents_eq hTr.1 hcell_mid] at ho_nd
      refine Or.inr (Or.inl ⟨o, ?_, le_refl _, le_refl _⟩)
      unfold worldOwned
      exact List.mem_append_right _ ho_nd
  have hFO : FrameOutside s post
      (worldOwned s S Nd ++ [] ++ [InitECandidate.Solver.Wave8Contracts.M08.freeGap s])
      (InitECandidate.Solver.Wave8Contracts.M08.heapFree s) := by
    intro a hnot_list hnot_hf
    apply hmem_frame a
    · intro hhit_l
      apply hnot_list (l, 24)
      · simp only [List.append_nil, List.mem_append]
        left
        unfold worldOwned
        exact List.mem_append_left _ (List.mem_append_right _ (M13.blockOut_in_fixedObjects hl_bo))
      · exact hhit_l
    · exact hnot_hf
  exact ⟨S, Nd, fun _ h => h, hWT_post, hOG, hFO, hQ S Nd hWT hWT_post⟩

private theorem lookupCode_two_word_params {F : Type}
    {s : PanSemStateFiniteExact 64 F} {fname p1 p2 : MlS} {body : ProgHOL 64} {ret : ShapeHOL}
    (hl : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], body, ret))
    (hcall : ∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
      some (body, s.locals, ret)) :
    ∃ w1 w2 : BitVec 64,
      s.locals.lookup p1 = some (.val (.word w1)) ∧
      s.locals.lookup p2 = some (.val (.word w2)) := by
  obtain ⟨values, hlook⟩ := hcall
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
  split at hlook
  · cases hlook
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hlook
    rcases Prod.mk.inj heq with ⟨_, hrest⟩
    rcases Prod.mk.inj hrest with ⟨hloc_eq, _⟩
    have hloc_fn : s.locals.lookup = exactLocals := (congrArg HolFiniteMapExact.lookup hloc_eq).symm
    unfold lookupCodeHOLExact at raw
    rw [hl] at raw
    dsimp only at raw
    split at raw
    · rename_i hcond
      have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨_, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨hloc2, _⟩
      subst hloc2
      obtain ⟨hnd, hlen, hshapes⟩ := hcond
      rcases values with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
      · simp at hlen
      · simp at hlen
      · simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
          List.not_mem_nil, or_false, List.zip, List.all, Bool.and_true, Bool.and_eq_true] at hnd hshapes
        rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact, shapeEqHOL] at hshapes
        rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact, shapeEqHOL] at hshapes
        refine ⟨w1, w2, ?_, ?_⟩
        · rw [hloc_fn]; simp [List.zip, List.foldl, hnd.1, FUPDATE]
        · rw [hloc_fn]; simp [List.zip, List.foldl, FUPDATE]
      · simp at hlen
    · cases raw

def BoListArgStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ BoListArg s ∧ memW s (locN s "l") ≠ 0

theorem lst_push_worldStep_strong {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hPre : BoListArgStrong s)
    (hcall : ∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "lst_push") values =
      some (sourceFnBody Guest.Software.guestFn_lst_push, s.locals, .one))
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_lst_push)).1) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_lst_push)
    WorldStep (fun _ => []) ["heap_ptr"] M13.stdKeep RetListSlotStrong s out.1 out.2 := by
  dsimp only
  obtain ⟨_, ⟨hW, hbo_nz, hl_choice, hesz_loc⟩, hp_old_nz0⟩ := hPre
  have hlook_fn : originalRuntimeCode.lookup (ofString "lst_push") =
      some ([(ofString "l", .one), (ofString "esz", .one)],
        sourceFnBody Guest.Software.guestFn_lst_push, .one) := R13Shards.lookup_lst_push
  obtain ⟨w_l, w_esz, hloc_l, hloc_esz⟩ := lookupCode_two_word_params hlook_fn hcall
  have hl_nat : locN s "l" = w_l.toNat := by unfold locN; rw [hloc_l]
  have hesz_nat : w_esz.toNat = 8 := by
    have : locN s "esz" = w_esz.toNat := by unfold locN; rw [hloc_esz]
    omega
  have hesz_bv : w_esz = 8#64 := BitVec.eq_of_toNat_eq hesz_nat
  subst hesz_bv
  have hbody : sourceFnBody Guest.Software.guestFn_lst_push =
      .dec (ofString "n") .one (.load .one (.op .add [.var .local (ofString "l"), .const 8]))
        (.dec (ofString "cap") .one (.load .one (.op .add [.var .local (ofString "l"), .const 16]))
          (.seq
            (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
              (.decCall (ofString "np") .one (ofString "alloc")
                [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
                (.seq
                  (.call (some (none, none)) (ofString "memcpy")
                    [.var .local (ofString "np"),
                     .load .one (.op .add [.var .local (ofString "l"), .const 0]),
                     .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
                  (.seq
                    (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
                    (.store (.op .add [.var .local (ofString "l"), .const 16])
                      (.panop .mul [.var .local (ofString "cap"), .const 2])))))
              .skip)
            (.seq
              (.store (.op .add [.var .local (ofString "l"), .const 8])
                (.op .add [.var .local (ofString "n"), .const 1]))
              (.return (.op .add
                [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
                 .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]))))) := rfl
  rw [hbody] at hres ⊢
  obtain ⟨vn, hev_n, hres1, heq_r_d1, heq_p_d1⟩ := dec_word_resumes_step hres
  have hdom_wl8 : s.memaddrs (w_l + 8#64) := by
    by_cases hd : s.memaddrs (w_l + 8#64)
    · exact hd
    · exfalso
      have hwf1 : isWfShapeExactHOL s.toExact.structs ShapeHOL.one = true := rfl
      have had : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.op .add [.var .local (ofString "l"), .const 8]) = some (.val (.word (w_l + 8#64))) := by
        simp [evalHOLExact, evalListHOLExact, hloc_l, valueIsWord, valueWord, wordOpHOL, wordOp]
      rw [evalHOLExact] at hev_n; simp only [hwf1, ↓reduceIte] at hev_n
      rw [had] at hev_n; simp [memLoadHOLExact, panMemLoadHOL, hd] at hev_n
  have hwl_nz : w_l.toNat ≠ 0 := by
    intro hz
    have hwl0 : w_l = 0 := BitVec.eq_of_toNat_eq hz
    rw [hwl0, hW.1.1.memaddrs, M13.ordinaryDomain_iff] at hdom_wl8
    have : ((0 : BitVec 64) + 8#64).toNat = 8 := by decide
    omega
  set l := w_l.toNat
  have hl_choice' : l = memW s (globN s "bo" + 40) ∨ l = memW s (globN s "bo" + 72) :=
    hl_nat ▸ hl_choice
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  obtain ⟨hT0, _, hF0, _⟩ := hWT0
  have hlstOK : LstOK s l := by
    rcases hl_choice' with h40 | h72
    · rw [h40]; exact hT0.2.2.2.2.2.2.2.2.2.2.1 hbo_nz 40 (by simp) (h40 ▸ hwl_nz)
    · rw [h72]; exact hT0.2.2.2.2.2.2.2.2.2.2.1 hbo_nz 72 (by simp) (h72 ▸ hwl_nz)
  have hl_bo : (l, 24) ∈ blockOutObjects s := by
    rcases hl_choice' with h40 | h72
    · unfold blockOutObjects; simp [hbo_nz, ← h40, hwl_nz]
    · unfold blockOutObjects; simp [hbo_nz, ← h72, hwl_nz]
  obtain ⟨hl_al, hl_words⟩ := (hF0.1 (l, 24) (M13.blockOut_in_fixedObjects hl_bo)).resolve_left (by simp)
  have hl_hi : l + 24 ≤ heapEnd ∧ l + 24 ≤ 2 ^ 64 := R13Shards.ivl_allocated_bound hW.1.2 hl_al
  have hl8 : l % 8 = 0 := hl_words.1
  set p_old := memW s l
  set n := memW s (l + 8)
  set cap := memW s (l + 16)
  have hp_old_nz : p_old ≠ 0 := by
    simpa [p_old, l, hl_nat] using hp_old_nz0
  have hcap_ge1 : 1 ≤ cap := hlstOK.1
  have hn_le_cap : n ≤ cap := hlstOK.2
  have hp_old_bo : p_old ≠ 0 → (p_old, 8 * cap) ∈ blockOutObjects s := by
    intro hp_nz
    have hsz_nz : 8 * cap ≠ 0 := by omega
    rcases hl_choice' with h40 | h72
    · unfold blockOutObjects
      have h40_nz : memW s (globN s "bo" + 40) ≠ 0 := h40 ▸ hwl_nz
      simp only [List.mem_append]
      left; right
      simp [hbo_nz, h40_nz, ← h40, hwl_nz, show memW s l ≠ 0 from hp_nz, show 8 * memW s (l + 16) ≠ 0 from hsz_nz, p_old, cap]
    · unfold blockOutObjects
      have h72_nz : memW s (globN s "bo" + 72) ≠ 0 := h72 ▸ hwl_nz
      simp only [List.mem_append]
      right
      simp [hbo_nz, h72_nz, ← h72, hwl_nz, show memW s l ≠ 0 from hp_nz, show 8 * memW s (l + 16) ≠ 0 from hsz_nz, p_old, cap]
  have hp_old_props : p_old ≠ 0 →
      Allocated s (p_old, 8 * cap) ∧ WordsOK s (p_old, 8 * cap) ∧ p_old + 8 * cap ≤ heapEnd ∧ p_old + 8 * cap ≤ 2 ^ 64 := by
    intro hp_nz
    obtain ⟨hal, hw⟩ := (hF0.1 (p_old, 8 * cap) (M13.blockOut_in_fixedObjects (hp_old_bo hp_nz))).resolve_left
      (by dsimp only; omega)
    exact ⟨hal, hw, R13Shards.ivl_allocated_bound hW.1.2 hal⟩
  obtain ⟨hp_old_al, hp_old_words, hp_old_hi_he, hp_old_hi264⟩ := hp_old_props hp_old_nz
  have hhe_lt_262 : heapEnd < 2 ^ 62 := by decide
  have h8cap_lt_264 : 8 * cap < 2 ^ 64 := by omega
  have h16cap_lt_264 : 16 * cap < 2 ^ 64 := by omega
  have hmul_lt_264 : n * 8 < 2 ^ 64 := by omega
  have hdisj_l_pold : p_old ≠ 0 → Disj (l, 24) (p_old, 8 * cap) := by
    intro hp_nz
    have hpw_bo : (blockOutObjects s).Pairwise Disj := by
      have hpw_fix := hF0.2
      unfold fixedObjects at hpw_fix
      exact (List.pairwise_append.1 (List.pairwise_append.1 hpw_fix).1).2.1
    have hsz_nz : 8 * cap ≠ 0 := by omega
    rcases hl_choice' with h40 | h72
    · have h40_nz : memW s (globN s "bo" + 40) ≠ 0 := h40 ▸ hwl_nz
      have hlen : (blockOutObjects s).length = 7 := by
        unfold blockOutObjects
        by_cases h72_z : memW s (globN s "bo" + 72) = 0
        · simp [hbo_nz, h40_nz, h72_z]
        · simp [hbo_nz, h40_nz, h72_z]
      have heq3 : (blockOutObjects s)[3]'(by omega) = (l, 24) := by
        unfold blockOutObjects
        by_cases h72_z : memW s (globN s "bo" + 72) = 0
        · simp [hbo_nz, h40_nz, h72_z, ← h40, hwl_nz]
        · simp [hbo_nz, h40_nz, h72_z, ← h40, hwl_nz]
      have heq4 : (blockOutObjects s)[4]'(by omega) = (p_old, 8 * cap) := by
        unfold blockOutObjects
        by_cases h72_z : memW s (globN s "bo" + 72) = 0
        · simp [hbo_nz, h40_nz, h72_z, ← h40, hwl_nz, show memW s l ≠ 0 from hp_nz, show 8 * memW s (l + 16) ≠ 0 from hsz_nz, p_old, cap]
        · simp [hbo_nz, h40_nz, h72_z, ← h40, hwl_nz, show memW s l ≠ 0 from hp_nz, show 8 * memW s (l + 16) ≠ 0 from hsz_nz, p_old, cap]
      have hget := (List.pairwise_iff_getElem.1 hpw_bo) 3 4 (by omega) (by omega) (by omega)
      rw [heq3, heq4] at hget
      exact hget
    · have h72_nz : memW s (globN s "bo" + 72) ≠ 0 := h72 ▸ hwl_nz
      have hlen : (blockOutObjects s).length = 7 := by
        unfold blockOutObjects
        by_cases h40_z : memW s (globN s "bo" + 40) = 0
        · simp [hbo_nz, h72_nz, h40_z]
        · simp [hbo_nz, h72_nz, h40_z]
      have heq5 : (blockOutObjects s)[5]'(by omega) = (l, 24) := by
        unfold blockOutObjects
        by_cases h40_z : memW s (globN s "bo" + 40) = 0
        · simp [hbo_nz, h72_nz, h40_z, ← h72, hwl_nz]
        · simp [hbo_nz, h72_nz, h40_z, ← h72, hwl_nz]
      have heq6 : (blockOutObjects s)[6]'(by omega) = (p_old, 8 * cap) := by
        unfold blockOutObjects
        by_cases h40_z : memW s (globN s "bo" + 40) = 0
        · simp [hbo_nz, h72_nz, h40_z, ← h72, hwl_nz, show memW s l ≠ 0 from hp_nz, show 8 * memW s (l + 16) ≠ 0 from hsz_nz, p_old, cap]
        · simp [hbo_nz, h72_nz, h40_z, ← h72, hwl_nz, show memW s l ≠ 0 from hp_nz, show 8 * memW s (l + 16) ≠ 0 from hsz_nz, p_old, cap]
      have hget := (List.pairwise_iff_getElem.1 hpw_bo) 5 6 (by omega) (by omega) (by omega)
      rw [heq5, heq6] at hget
      exact hget
  -- Word values in `s.memory` at `l + 0`, `l + 8`, `l + 16`:
  have hwl0_eq : w_l = BitVec.ofNat 64 l := by
    simp [l, BitVec.ofNat_toNat]
  have hwl8_eq : w_l + 8#64 = BitVec.ofNat 64 (l + 8) := by
    rw [hwl0_eq]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hwl16_eq : w_l + 16#64 = BitVec.ofNat 64 (l + 16) := by
    rw [hwl0_eq]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  obtain ⟨w_pold, hdom_l0, hm_l0⟩ := hl_words.2.2 0 (by omega)
  obtain ⟨w_n, hdom_l8, hm_l8⟩ := hl_words.2.2 1 (by omega)
  obtain ⟨w_cap, hdom_l16, hm_l16⟩ := hl_words.2.2 2 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at hdom_l0 hm_l0
  simp only [Nat.mul_one] at hdom_l8 hm_l8
  have hmul2_8 : 8 * 2 = 16 := rfl
  rw [hmul2_8] at hdom_l16 hm_l16
  have hdom_l16' : s.memaddrs (BitVec.ofNat 64 (l + 16)) := hdom_l16
  have hm_l16' : s.memory (BitVec.ofNat 64 (l + 16)) = .word w_cap := hm_l16
  have hw_pold_nat : w_pold.toNat = p_old := by unfold p_old memW; rw [hm_l0]
  have hw_n_nat : w_n.toNat = n := by unfold n memW; rw [hm_l8]
  have hw_cap_nat : w_cap.toNat = cap := by unfold cap memW; rw [hm_l16']
  have hvn_eq : vn = .val (.word w_n) := by
    have hwf1 : isWfShapeExactHOL s.toExact.structs ShapeHOL.one = true := rfl
    have had : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.op .add [.var .local (ofString "l"), .const 8]) = some (.val (.word (BitVec.ofNat 64 (l + 8)))) := by
      simp [evalHOLExact, evalListHOLExact, hloc_l, valueIsWord, valueWord, wordOpHOL, wordOp]
      exact hwl8_eq
    rw [evalHOLExact] at hev_n; simp only [hwf1, ↓reduceIte] at hev_n
    rw [had] at hev_n; simp [memLoadHOLExact, panMemLoadHOL, hdom_l8, hm_l8] at hev_n
    exact hev_n.symm
  subst hvn_eq
  set d1 := setVarHOLFinite (ofString "n") (.val (.word w_n)) s
  obtain ⟨vcap, hev_cap, hres2, heq_r_d2, heq_p_d2⟩ := dec_word_resumes_step hres1
  have hd1_l : d1.locals.lookup (ofString "l") = some (.val (.word w_l)) := by
    simp [d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "l" by decide, hloc_l]
  have hvcap_eq : vcap = .val (.word w_cap) := by
    have hwf1 : isWfShapeExactHOL d1.toExact.structs ShapeHOL.one = true := rfl
    have had : @evalHOLExact 64 F _ d1.toExact (fun a => Classical.propDecidable (d1.memaddrs a))
        (.op .add [.var .local (ofString "l"), .const 16]) = some (.val (.word (BitVec.ofNat 64 (l + 16)))) := by
      simp [evalHOLExact, evalListHOLExact, hd1_l, valueIsWord, valueWord, wordOpHOL, wordOp]
      exact hwl16_eq
    have hdom_d1 : d1.memaddrs (BitVec.ofNat 64 (l + 16)) := hdom_l16'
    have hm_d1 : d1.memory (BitVec.ofNat 64 (l + 16)) = .word w_cap := hm_l16'
    rw [evalHOLExact] at hev_cap; simp only [hwf1, ↓reduceIte] at hev_cap
    rw [had] at hev_cap; simp [memLoadHOLExact, panMemLoadHOL, hdom_d1, hm_d1] at hev_cap
    exact hev_cap.symm
  subst hvcap_eq
  set d2 := setVarHOLFinite (ofString "cap") (.val (.word w_cap)) d1
  have hd2_l : d2.locals.lookup (ofString "l") = some (.val (.word w_l)) := by
    simp [d2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "cap" ≠ ofString "l" by decide, hd1_l]
  have hd2_esz : d2.locals.lookup (ofString "esz") = some (.val (.word 8#64)) := by
    simp [d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "cap" ≠ ofString "esz" by decide,
      show ofString "n" ≠ ofString "esz" by decide, hloc_esz]
  have hd2_n : d2.locals.lookup (ofString "n") = some (.val (.word w_n)) := by
    simp [d2, d1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "cap" ≠ ofString "n" by decide]
  have hd2_cap : d2.locals.lookup (ofString "cap") = some (.val (.word w_cap)) := by
    simp [d2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hal0_ne8 : BitVec.ofNat 64 l ≠ BitVec.ofNat 64 (l + 8) := by
    intro h; have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hal0_ne16 : BitVec.ofNat 64 l ≠ BitVec.ofNat 64 (l + 16) := by
    intro h; have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hal8_ne16 : BitVec.ofNat 64 (l + 8) ≠ BitVec.ofNat 64 (l + 16) := by
    intro h; have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  by_cases hlt : n < cap
  · -- Branch 1: `n < cap` (`ite` takes `.skip`, no reallocation)
    have hcmp_ite : @evalHOLExact 64 F _ d2.toExact (fun a => Classical.propDecidable (d2.memaddrs a))
        (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap"))) =
        some (.val (.word 0)) := by
      simp [evalHOLExact, hd2_n, hd2_cap, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, hw_n_nat, hw_cap_nat, hlt]
    have hite_skip : evaluateHOLFiniteState d2
        (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
          (.decCall (ofString "np") .one (ofString "alloc")
            [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "np"),
                 .load .one (.op .add [.var .local (ofString "l"), .const 0]),
                 .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
              (.seq
                (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
                (.store (.op .add [.var .local (ofString "l"), .const 16])
                  (.panop .mul [.var .local (ofString "cap"), .const 2])))))
          .skip) = (none, d2) := by
      rw [evaluateHOLFiniteState_ite, hcmp_ite]; simp [evaluateHOLFiniteState_skip]
    have hd2_seq_eq : ∀ tail : ProgHOL 64,
        evaluateHOLFiniteState d2
          (.seq
            (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
              (.decCall (ofString "np") .one (ofString "alloc")
                [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
                (.seq
                  (.call (some (none, none)) (ofString "memcpy")
                    [.var .local (ofString "np"),
                     .load .one (.op .add [.var .local (ofString "l"), .const 0]),
                     .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
                  (.seq
                    (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
                    (.store (.op .add [.var .local (ofString "l"), .const 16])
                      (.panop .mul [.var .local (ofString "cap"), .const 2])))))
              .skip)
            tail) = evaluateHOLFiniteState d2 tail := by
      intro tail
      rw [evaluateHOLFiniteState_seq_line780, hite_skip]
    rw [hd2_seq_eq] at hres2
    have hev_l8_d2 : @evalHOLExact 64 F _ d2.toExact (fun a => Classical.propDecidable (d2.memaddrs a))
        (.op .add [.var .local (ofString "l"), .const 8]) = some (.val (.word (BitVec.ofNat 64 (l + 8)))) := by
      simp [evalHOLExact, evalListHOLExact, hd2_l, valueIsWord, valueWord, wordOpHOL, wordOp]
      exact hwl8_eq
    have hev_n1_d2 : @evalHOLExact 64 F _ d2.toExact (fun a => Classical.propDecidable (d2.memaddrs a))
        (.op .add [.var .local (ofString "n"), .const 1]) = some (.val (.word (w_n + 1#64))) := by
      simp [evalHOLExact, evalListHOLExact, hd2_n, valueIsWord, valueWord, wordOpHOL, wordOp]
    obtain ⟨_, hst8_d2⟩ := R13Wk06b.store_word_resumes_step (BitVec.ofNat 64 (l + 8)) (w_n + 1#64) hev_l8_d2 hev_n1_d2 hres2
    rw [hst8_d2] at hres2
    set m_post := Wave8Contracts.M26.updW s.memory (BitVec.ofNat 64 (l + 8)) (w_n + 1#64)
    let st_ret : PanSemStateFiniteExact 64 F := { d2 with memory := m_post }
    change Resumes (evaluateHOLFiniteState st_ret _).1 at hres2
    have hload_l0_ret : @evalHOLExact 64 F _ st_ret.toExact (fun a => Classical.propDecidable (st_ret.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "l"), .const 0])) = some (.val (.word w_pold)) := by
      have hwf1 : isWfShapeExactHOL st_ret.toExact.structs ShapeHOL.one = true := rfl
      have had : @evalHOLExact 64 F _ st_ret.toExact (fun a => Classical.propDecidable (st_ret.memaddrs a))
          (.op .add [.var .local (ofString "l"), .const 0]) = some (.val (.word (BitVec.ofNat 64 l))) := by
        simp [st_ret, evalHOLExact, evalListHOLExact, hd2_l, valueIsWord, valueWord, wordOpHOL, wordOp]
        exact hwl0_eq
      have hdom_st : st_ret.memaddrs (BitVec.ofNat 64 l) := hdom_l0
      have hm_st : st_ret.memory (BitVec.ofNat 64 l) = .word w_pold := by
        change m_post (BitVec.ofNat 64 l) = .word w_pold
        unfold m_post Wave8Contracts.M26.updW
        rw [if_neg hal0_ne8, hm_l0]
      rw [evalHOLExact]; simp only [hwf1, ↓reduceIte]
      rw [had]; simp [memLoadHOLExact, panMemLoadHOL, hdom_st, hm_st]
    have hev_mul_ret : @evalHOLExact 64 F _ st_ret.toExact (fun a => Classical.propDecidable (st_ret.memaddrs a))
        (.panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]) =
        some (.val (.word (w_n * 8#64))) := by
      rw [evalHOLExact]
      simp [st_ret, evalListHOLExact, evalHOLExact, hd2_n, hd2_esz, valueIsWord, valueWord, panOpHOL]
    have hret_eval : evaluateHOLFiniteState st_ret
        (.return (.op .add
          [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
           .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]])) =
        (some (.returned (.val (.word (w_pold + w_n * 8#64)))), emptyLocalsHOLFinite st_ret) := by
      rw [evaluateHOLFiniteState_return]
      have hadd_ret : @evalHOLExact 64 F _ st_ret.toExact (fun a => Classical.propDecidable (st_ret.memaddrs a))
          (.op .add
            [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
             .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]) =
          some (.val (.word (w_pold + w_n * 8#64))) := by
        rw [evalHOLExact]
        simp only [evalListHOLExact, hload_l0_ret, hev_mul_ret]
        simp [valueIsWord, valueWord, wordOpHOL, wordOp]
      rw [hadd_ret]
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    set out_prog := evaluateHOLFiniteState s
      (.dec (ofString "n") .one (.load .one (.op .add [.var .local (ofString "l"), .const 8]))
        (.dec (ofString "cap") .one (.load .one (.op .add [.var .local (ofString "l"), .const 16]))
          (.seq
            (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
              (.decCall (ofString "np") .one (ofString "alloc")
                [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
                (.seq
                  (.call (some (none, none)) (ofString "memcpy")
                    [.var .local (ofString "np"),
                     .load .one (.op .add [.var .local (ofString "l"), .const 0]),
                     .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
                  (.seq
                    (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
                    (.store (.op .add [.var .local (ofString "l"), .const 16])
                      (.panop .mul [.var .local (ofString "cap"), .const 2])))))
              .skip)
            (.seq
              (.store (.op .add [.var .local (ofString "l"), .const 8])
                (.op .add [.var .local (ofString "n"), .const 1]))
              (.return (.op .add
                [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
                 .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]))))))
    have hout_r : out_prog.1 = some (.returned (.val (.word (w_pold + w_n * 8#64)))) := by
      rw [heq_r_d1, heq_r_d2, hd2_seq_eq, hst8_d2]
      exact congrArg Prod.fst hret_eval
    have hout_mem : out_prog.2.memory = m_post := by
      rw [heq_p_d1]; dsimp only; rw [heq_p_d2]; dsimp only; rw [hd2_seq_eq, hst8_d2]
      change { (evaluateHOLFiniteState st_ret _).2 with locals := _ }.memory = m_post
      rw [hret_eval]; rfl
    have hout_glob : out_prog.2.globals = s.globals := by
      rw [heq_p_d1]; dsimp only; rw [heq_p_d2]; dsimp only; rw [hd2_seq_eq, hst8_d2]
      change { (evaluateHOLFiniteState st_ret _).2 with locals := _ }.globals = s.globals
      rw [hret_eval]; rfl
    have hout_be : out_prog.2.be = s.be := by
      rw [heq_p_d1]; dsimp only; rw [heq_p_d2]; dsimp only; rw [hd2_seq_eq, hst8_d2]
      change { (evaluateHOLFiniteState st_ret _).2 with locals := _ }.be = s.be
      rw [hret_eval]; rfl
    have hout_code : out_prog.2.code = s.code := by
      rw [heq_p_d1]; dsimp only; rw [heq_p_d2]; dsimp only; rw [hd2_seq_eq, hst8_d2]
      change { (evaluateHOLFiniteState st_ret _).2 with locals := _ }.code = s.code
      rw [hret_eval]; rfl
    have hout_ma : out_prog.2.memaddrs = s.memaddrs := by
      rw [heq_p_d1]; dsimp only; rw [heq_p_d2]; dsimp only; rw [hd2_seq_eq, hst8_d2]
      change { (evaluateHOLFiniteState st_ret _).2 with locals := _ }.memaddrs = s.memaddrs
      rw [hret_eval]; rfl
    have hout_sh : out_prog.2.shMemaddrs = s.shMemaddrs := by
      rw [heq_p_d1]; dsimp only; rw [heq_p_d2]; dsimp only; rw [hd2_seq_eq, hst8_d2]
      change { (evaluateHOLFiniteState st_ret _).2 with locals := _ }.shMemaddrs = s.shMemaddrs
      rw [hret_eval]; rfl
    have hout_ba : out_prog.2.baseAddr = s.baseAddr := by
      rw [heq_p_d1]; dsimp only; rw [heq_p_d2]; dsimp only; rw [hd2_seq_eq, hst8_d2]
      change { (evaluateHOLFiniteState st_ret _).2 with locals := _ }.baseAddr = s.baseAddr
      rw [hret_eval]; rfl
    have hA_post : ArenaReady out_prog.2 :=
      ⟨guestInv_congr hout_code hout_ma hout_sh hout_ba hW.1.1, arenaOK_congr hout_glob hW.1.2⟩
    have hhp_le : globN s "heap_ptr" ≤ globN out_prog.2 "heap_ptr" := by
      unfold globN; rw [hout_glob]
    have hGK : GlobalsKept ["heap_ptr"] s out_prog.2 := fun k _ => by rw [hout_glob]
    have hwn1_nat : (w_n + 1#64).toNat = n + 1 := by
      have hn_lt : n + 1 < 2 ^ 64 := by omega
      rw [BitVec.toNat_add_of_lt (by rw [hw_n_nat]; exact hn_lt), hw_n_nat]; rfl
    have hm_post_l0 : memW out_prog.2 l = p_old := by
      unfold memW; rw [hout_mem]; unfold m_post Wave8Contracts.M26.updW
      rw [if_neg hal0_ne8, hm_l0]; exact hw_pold_nat
    have hm_post_l8 : memW out_prog.2 (l + 8) = n + 1 := by
      unfold memW; rw [hout_mem]; unfold m_post Wave8Contracts.M26.updW
      rw [if_pos rfl]; exact hwn1_nat
    have hm_post_l16 : memW out_prog.2 (l + 16) = cap := by
      unfold memW; rw [hout_mem]; unfold m_post Wave8Contracts.M26.updW
      rw [if_neg hal8_ne16.symm, hm_l16']; exact hw_cap_nat
    have hout_dom : ∀ a : BitVec 64, ¬ s.memaddrs a → out_prog.2.memory a = s.memory a := by
      intro a hna
      rw [hout_mem]; unfold m_post Wave8Contracts.M26.updW
      rw [if_neg (by rintro rfl; exact hna hdom_l8)]
    have hmem_frame : ∀ a : BitVec 64,
        ¬ CellHits a.toNat (l, 24) →
        ¬ CellHits a.toNat (InitECandidate.Solver.Wave8Contracts.M08.heapFree s) →
        out_prog.2.memory a = s.memory a := by
      intro a hnl _
      rw [hout_mem]; unfold m_post Wave8Contracts.M26.updW
      apply if_neg
      rintro rfl
      apply hnl
      unfold CellHits
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      dsimp only; omega
    refine lst_push_worldStep_of_bo hW hA_post hbo_nz hwl_nz hl_choice' hhp_le hGK hout_be hout_dom hmem_frame
      ⟨by rw [hm_post_l16]; omega, by rw [hm_post_l8, hm_post_l16]; omega⟩
      (Or.inl ⟨hm_post_l0, hm_post_l16⟩)
      (fun S Nd hWT hWT' => ?_)
    refine ⟨?_, ?_⟩
    · intro a hnl hnhf
      exact hmem_frame a (hl_nat ▸ hnl) hnhf
    · intro v hv
      rw [hout_r] at hv
      injection hv with hv'
      injection hv' with hv''; subst hv''
      have hmul_bv_nat : (w_n * 8#64).toNat = 8 * n := by
        rw [BitVec.toNat_mul, hw_n_nat, show (8#64 : BitVec 64).toNat = 8 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        omega
      have hw_ret_nat : (w_pold + w_n * 8#64).toNat = p_old + 8 * n := by
        by_cases hpz : p_old = 0
        · have hwp0 : w_pold = 0#64 := BitVec.eq_of_toNat_eq (by rw [hw_pold_nat, hpz]; rfl)
          rw [hwp0, hpz, BitVec.zero_add, hmul_bv_nat]; omega
        · obtain ⟨_, _, _, hp_hi264⟩ := hp_old_props hpz
          rw [BitVec.toNat_add_of_lt (by rw [hw_pold_nat, hmul_bv_nat]; omega), hw_pold_nat, hmul_bv_nat]
      have hw_ret_al : (w_pold + w_n * 8#64).toNat % 8 = 0 := by
        rw [hw_ret_nat]
        by_cases hpz : p_old = 0
        · omega
        · have hp8 : p_old % 8 = 0 := (hp_old_props hpz).2.1.1
          omega
      refine ⟨w_pold + w_n * 8#64, rfl, hw_ret_al, ?_, ?_, ?_, ?_⟩
      · rw [hl_nat, hm_post_l0, hm_post_l16, hw_ret_nat]
        exact ⟨by omega, by omega⟩
      · rw [hl_nat, hm_post_l8]
      · rw [hl_nat, hm_post_l0, hw_ret_nat]
      · intro hp_nz k hk
        rw [hl_nat] at hp_nz hk
        rw [hl_nat, hm_post_l0]
        change p_old ≠ 0 at hp_nz
        change k < n at hk
        obtain ⟨_, _, _, hp_hi264⟩ := hp_old_props hp_nz
        have hdisj := hdisj_l_pold hp_nz
        have hne_addr : BitVec.ofNat 64 (p_old + 8 * k) ≠ BitVec.ofNat 64 (l + 8) := by
          intro heq
          have htn := congrArg BitVec.toNat heq
          rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at htn
          rcases hdisj with h0 | h0 | h | h
          · omega
          · omega
          · dsimp only at h; omega
          · dsimp only at h; omega
        unfold memW
        rw [hout_mem]; unfold m_post Wave8Contracts.M26.updW
        rw [if_neg hne_addr]
        rfl
  · -- Branch 2: `¬ (n < cap)`, i.e. `n = cap ≥ 1` (reallocation branch)
    have hn_eq_cap : n = cap := by omega
    have hwn_eq_wcap : w_n = w_cap := BitVec.eq_of_toNat_eq (by omega)
    have hcmp_ite : @evalHOLExact 64 F _ d2.toExact (fun a => Classical.propDecidable (d2.memaddrs a))
        (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap"))) =
        some (.val (.word 1)) := by
      simp [evalHOLExact, hd2_n, hd2_cap, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, hw_n_nat, hw_cap_nat, hlt]
    have hite_then : evaluateHOLFiniteState d2
        (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
          (.decCall (ofString "np") .one (ofString "alloc")
            [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "np"),
                 .load .one (.op .add [.var .local (ofString "l"), .const 0]),
                 .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
              (.seq
                (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
                (.store (.op .add [.var .local (ofString "l"), .const 16])
                  (.panop .mul [.var .local (ofString "cap"), .const 2])))))
          .skip) =
        evaluateHOLFiniteState d2
          (.decCall (ofString "np") .one (ofString "alloc")
            [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "np"),
                 .load .one (.op .add [.var .local (ofString "l"), .const 0]),
                 .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
              (.seq
                (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
                (.store (.op .add [.var .local (ofString "l"), .const 16])
                  (.panop .mul [.var .local (ofString "cap"), .const 2]))))) := by
      rw [evaluateHOLFiniteState_ite, hcmp_ite]; simp
    have harg_alloc : evalListHOLFinite d2
        (h := fun a => Classical.propDecidable (d2.memaddrs a))
        [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]] =
        some [.val (.word ((8#64 * w_cap) * 2#64))] := by
      rw [evalListHOLFinite_eq_toExact]
      simp [d2, evalListHOLExact, evalHOLExact, hd2_esz, hd2_cap, valueIsWord, valueWord, panOpHOL]
    have h8cap_bv_nat : (8#64 * w_cap).toNat = 8 * cap := by
      rw [BitVec.toNat_mul, show (8#64 : BitVec 64).toNat = 8 from rfl, hw_cap_nat, Nat.mod_eq_of_lt h8cap_lt_264]
    have h16cap_bv_nat : ((8#64 * w_cap) * 2#64).toNat = 16 * cap := by
      rw [BitVec.toNat_mul, h8cap_bv_nat, show (2#64 : BitVec 64).toNat = 2 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      omega
    obtain ⟨hp, _, _, hhp_lk, hhp_eq, _, _, _, _⟩ := Wave8Contracts.M26.arenaOK_globals s hW.1.2
    have hd2_code : d2.code = originalRuntimeCode := hcode
    have hd2_hp : d2.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)) := hhp_lk
    set nv_alloc : BitVec 64 := (8#64 * w_cap) * 2#64
    set q : BitVec 64 := (hp + (nv_alloc + 7)) &&& ((0 : BitVec 64) - 8)
    have halloc_step :
        ¬ ((cMax - hp).toNat < nv_alloc.toNat) ∧ ¬ (cMax.toNat < q.toNat) ∧
        ∃ (pa : PanSemStateFiniteExact 64 F),
          pa = { d2 with
            globals := d2.globals.update (ofString "heap_ptr", .val (.word q))
            locals := pa.locals
            clock := pa.clock } ∧
          let a1 := setVarHOLFinite (ofString "np") (.val (.word hp)) { pa with locals := d2.locals }
          (evaluateHOLFiniteState d2
            (.decCall (ofString "np") .one (ofString "alloc")
              [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
              (.seq
                (.call (some (none, none)) (ofString "memcpy")
                  [.var .local (ofString "np"),
                   .load .one (.op .add [.var .local (ofString "l"), .const 0]),
                   .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
                (.seq
                  (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
                  (.store (.op .add [.var .local (ofString "l"), .const 16])
                    (.panop .mul [.var .local (ofString "cap"), .const 2])))))).1 =
            (evaluateHOLFiniteState a1
              (.seq
                (.call (some (none, none)) (ofString "memcpy")
                  [.var .local (ofString "np"),
                   .load .one (.op .add [.var .local (ofString "l"), .const 0]),
                   .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
                (.seq
                  (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
                  (.store (.op .add [.var .local (ofString "l"), .const 16])
                    (.panop .mul [.var .local (ofString "cap"), .const 2]))))).1 ∧
          (evaluateHOLFiniteState d2
            (.decCall (ofString "np") .one (ofString "alloc")
              [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
              (.seq
                (.call (some (none, none)) (ofString "memcpy")
                  [.var .local (ofString "np"),
                   .load .one (.op .add [.var .local (ofString "l"), .const 0]),
                   .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
                (.seq
                  (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
                  (.store (.op .add [.var .local (ofString "l"), .const 16])
                    (.panop .mul [.var .local (ofString "cap"), .const 2])))))).2 =
            { (evaluateHOLFiniteState a1
                (.seq
                  (.call (some (none, none)) (ofString "memcpy")
                    [.var .local (ofString "np"),
                     .load .one (.op .add [.var .local (ofString "l"), .const 0]),
                     .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
                  (.seq
                    (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
                    (.store (.op .add [.var .local (ofString "l"), .const 16])
                      (.panop .mul [.var .local (ofString "cap"), .const 2]))))).2 with
              locals := HolFiniteMapExact.resVarEq
                (evaluateHOLFiniteState a1
                  (.seq
                    (.call (some (none, none)) (ofString "memcpy")
                      [.var .local (ofString "np"),
                       .load .one (.op .add [.var .local (ofString "l"), .const 0]),
                       .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
                    (.seq
                      (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
                      (.store (.op .add [.var .local (ofString "l"), .const 16])
                        (.panop .mul [.var .local (ofString "cap"), .const 2]))))).2.locals
                (ofString "np", d2.locals.lookup (ofString "np")) } := by
      have hres2_seq := hres2
      rw [evaluateHOLFiniteState_seq_line780, hite_then] at hres2_seq
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite, harg_alloc] at hres2_seq ⊢
      dsimp only at hres2_seq ⊢
      have hlk := pan_one_word_lookup d2.code.lookup (ofString "alloc") (ofString "n")
        (sourceFnBody Guest.Software.guestFn_alloc) nv_alloc
        (by rw [hd2_code]; exact InitECandidate.Solver.Wave8Contracts.M27.lookup_alloc_te)
      rw [hlk] at hres2_seq ⊢; dsimp only at hres2_seq ⊢
      by_cases hclk : d2.clock = 0
      · rw [if_pos hclk] at hres2_seq; rcases hres2_seq with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      · rw [if_neg hclk] at hres2_seq ⊢
        let entry := callEntryStateHOLFinite d2 (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv_alloc)))
        have hn_ent : entry.locals.lookup (ofString "n") = some (.val (.word nv_alloc)) := by
          simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hhp_ent : entry.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)) := hd2_hp
        have hcode_ent : entry.code = originalRuntimeCode := hd2_code
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite d2 (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv_alloc))))
            (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ar, pa⟩
        simp only [hb] at hres2_seq ⊢
        have har_res : Resumes ar := by
          cases ar with
          | none => rcases hres2_seq with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
          | some ar0 =>
            cases ar0 with
            | returned val => exact Or.inl ⟨val, rfl⟩
            | exception e v =>
              rcases hres2_seq with ⟨_, h⟩ | ⟨_, _, h, hne⟩
              · simp at h
              · simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨e, v, rfl, hne⟩
            | _ => rcases hres2_seq with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        obtain ⟨hret_a, hc1, hc2, hpa_f⟩ := R13Wk06b.alloc_body_resumes entry hp nv_alloc hcode_ent hhp_ent hn_ent
          (by dsimp only [entry]; rw [hb]; exact har_res)
        dsimp only [entry] at hret_a hpa_f
        rw [hb] at hret_a hpa_f; dsimp only at hret_a hpa_f
        subst hret_a
        dsimp only at hres2_seq ⊢
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word hp) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word hp) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh]
        refine ⟨hc1, hc2, pa, ?_, rfl, rfl⟩
        rw [hpa_f]; rfl
    obtain ⟨hcmp1_a, hcmp2_a, pa, hpa_eq, heq_r_a, heq_p_a⟩ := halloc_step
    have hres_a1 :
        (evaluateHOLFiniteState
          (setVarHOLFinite (ofString "np") (.val (.word hp)) { pa with locals := d2.locals })
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.var .local (ofString "np"),
               .load .one (.op .add [.var .local (ofString "l"), .const 0]),
               .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
            (.seq
              (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
              (.store (.op .add [.var .local (ofString "l"), .const 16])
                (.panop .mul [.var .local (ofString "cap"), .const 2]))))).1 = none ∨
        Resumes (evaluateHOLFiniteState
          (setVarHOLFinite (ofString "np") (.val (.word hp)) { pa with locals := d2.locals })
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.var .local (ofString "np"),
               .load .one (.op .add [.var .local (ofString "l"), .const 0]),
               .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
            (.seq
              (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
              (.store (.op .add [.var .local (ofString "l"), .const 16])
                (.panop .mul [.var .local (ofString "cap"), .const 2]))))).1 := by
      have hres2_seq := hres2
      rw [evaluateHOLFiniteState_seq_line780, hite_then] at hres2_seq
      rcases hr_dc : evaluateHOLFiniteState d2
          (.decCall (ofString "np") .one (ofString "alloc")
            [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "np"),
                 .load .one (.op .add [.var .local (ofString "l"), .const 0]),
                 .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
              (.seq
                (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
                (.store (.op .add [.var .local (ofString "l"), .const 16])
                  (.panop .mul [.var .local (ofString "cap"), .const 2]))))) with ⟨rc_dc, st_dc⟩
      rw [hr_dc] at hres2_seq heq_r_a; dsimp only at heq_r_a
      cases rc_dc with
      | none => exact Or.inl heq_r_a.symm
      | some rc' => exact Or.inr (heq_r_a ▸ hres2_seq)
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hW.1.2.2.1
    have hhp_al8 : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hW.1.2.2.2.2.2.2.1
    obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q⟩ :=
      Wave8Contracts.M26.alloc_arith hp nv_alloc hhp_hi hhp_al8 hcmp1_a hcmp2_a
    change q.toNat = _ at hq_eq
    change q.toNat ≤ heapLimit at hq_hi
    change q.toNat % 8 = 0 at hq_al
    change hp.toNat ≤ q.toNat at hp_le_q
    rw [h16cap_bv_nat, show (16 * cap + 7) / 8 * 8 = 16 * cap by omega] at hq_eq
    have hhp_nz : hp.toNat ≠ 0 := by
      have hsb : 0 < sourceBase := by decide
      have := hW.1.2.1
      omega
    set a1 := setVarHOLFinite (ofString "np") (.val (.word hp)) { pa with locals := d2.locals }
    have ha1_code : a1.code = originalRuntimeCode := by
      change pa.code = originalRuntimeCode; rw [hpa_eq]; exact hcode
    have ha1_G : GuestInv a1 := by
      exact guestInv_congr (by change pa.code = s.code; rw [hpa_eq]; rfl)
        (by change pa.memaddrs = s.memaddrs; rw [hpa_eq]; rfl)
        (by change pa.shMemaddrs = s.shMemaddrs; rw [hpa_eq]; rfl)
        (by change pa.baseAddr = s.baseAddr; rw [hpa_eq]; rfl) hW.1.1
    have ha1_mem : a1.memory = s.memory := by change pa.memory = s.memory; rw [hpa_eq]; rfl
    have ha1_ma : a1.memaddrs = s.memaddrs := by change pa.memaddrs = s.memaddrs; rw [hpa_eq]; rfl
    have ha1_be : a1.be = s.be := by change pa.be = s.be; rw [hpa_eq]; rfl
    have ha1_glob : a1.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) := by
      change pa.globals = _; rw [hpa_eq]; rfl
    have ha1_np : a1.locals.lookup (ofString "np") = some (.val (.word hp)) := by
      simp [a1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have ha1_l : a1.locals.lookup (ofString "l") = some (.val (.word w_l)) := by
      simp [a1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "np" ≠ ofString "l" by decide, hd2_l]
    have ha1_esz : a1.locals.lookup (ofString "esz") = some (.val (.word 8#64)) := by
      simp [a1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "np" ≠ ofString "esz" by decide, hd2_esz]
    have ha1_n : a1.locals.lookup (ofString "n") = some (.val (.word w_n)) := by
      simp [a1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "np" ≠ ofString "n" by decide, hd2_n]
    have ha1_cap : a1.locals.lookup (ofString "cap") = some (.val (.word w_cap)) := by
      simp [a1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "np" ≠ ofString "cap" by decide, hd2_cap]
    have hev_mc_dst : @evalHOLExact 64 F _ a1.toExact (fun a => Classical.propDecidable (a1.memaddrs a))
        (.var .local (ofString "np")) = some (.val (.word hp)) := by
      simp [evalHOLExact, ha1_np]
    have hev_mc_src : @evalHOLExact 64 F _ a1.toExact (fun a => Classical.propDecidable (a1.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "l"), .const 0])) = some (.val (.word w_pold)) := by
      have hwf1 : isWfShapeExactHOL a1.toExact.structs ShapeHOL.one = true := rfl
      have had : @evalHOLExact 64 F _ a1.toExact (fun a => Classical.propDecidable (a1.memaddrs a))
          (.op .add [.var .local (ofString "l"), .const 0]) = some (.val (.word (BitVec.ofNat 64 l))) := by
        simp [evalHOLExact, evalListHOLExact, ha1_l, valueIsWord, valueWord, wordOpHOL, wordOp]
        exact hwl0_eq
      have hdom_a1 : a1.memaddrs (BitVec.ofNat 64 l) := ha1_ma ▸ hdom_l0
      have hm_a1 : a1.memory (BitVec.ofNat 64 l) = .word w_pold := ha1_mem ▸ hm_l0
      rw [evalHOLExact]; simp only [hwf1, ↓reduceIte]
      rw [had]; simp [memLoadHOLExact, panMemLoadHOL, hdom_a1, hm_a1]
    have hev_mc_n : @evalHOLExact 64 F _ a1.toExact (fun a => Classical.propDecidable (a1.memaddrs a))
        (.panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]) =
        some (.val (.word (8#64 * w_n))) := by
      rw [evalHOLExact]
      simp [evalListHOLExact, evalHOLExact, ha1_esz, ha1_n, valueIsWord, valueWord, panOpHOL]
    obtain ⟨t_mc, ht_loc, ht_glob, hmwf_mc, hcp_mc, hsrc_nz_mc, hmc_step⟩ :=
      lst_push_memcpy_resumes a1
        (.var .local (ofString "np"))
        (.load .one (.op .add [.var .local (ofString "l"), .const 0]))
        (.panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")])
        hp w_pold (8#64 * w_n)
        (.seq
          (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
          (.store (.op .add [.var .local (ofString "l"), .const 16])
            (.panop .mul [.var .local (ofString "cap"), .const 2])))
        ha1_code ha1_G hev_mc_dst hev_mc_src hev_mc_n hres_a1
    have h8n_bv_nat : (8#64 * w_n).toNat = 8 * n := by
      rw [hwn_eq_wcap, h8cap_bv_nat, hn_eq_cap]
    rw [hmc_step] at hres_a1
    have ht_l : t_mc.locals.lookup (ofString "l") = some (.val (.word w_l)) := by rw [ht_loc]; exact ha1_l
    have ht_np : t_mc.locals.lookup (ofString "np") = some (.val (.word hp)) := by rw [ht_loc]; exact ha1_np
    have ht_cap : t_mc.locals.lookup (ofString "cap") = some (.val (.word w_cap)) := by rw [ht_loc]; exact ha1_cap
    have hev_t_l0 : @evalHOLExact 64 F _ t_mc.toExact (fun a => Classical.propDecidable (t_mc.memaddrs a))
        (.op .add [.var .local (ofString "l"), .const 0]) = some (.val (.word (BitVec.ofNat 64 l))) := by
      simp [evalHOLExact, evalListHOLExact, ht_l, valueIsWord, valueWord, wordOpHOL, wordOp]
      exact hwl0_eq
    have hev_t_np : @evalHOLExact 64 F _ t_mc.toExact (fun a => Classical.propDecidable (t_mc.memaddrs a))
        (.var .local (ofString "np")) = some (.val (.word hp)) := by
      simp [evalHOLExact, ht_np]
    have hst0_t : evaluateHOLFiniteState t_mc
        (.seq
          (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
          (.store (.op .add [.var .local (ofString "l"), .const 16])
            (.panop .mul [.var .local (ofString "cap"), .const 2]))) =
        evaluateHOLFiniteState
          { t_mc with memory := Wave8Contracts.M26.updW t_mc.memory (BitVec.ofNat 64 l) hp }
          (.store (.op .add [.var .local (ofString "l"), .const 16])
            (.panop .mul [.var .local (ofString "cap"), .const 2])) := by
      have hdom0_t : t_mc.memaddrs (BitVec.ofNat 64 l) := by
        rw [hmwf_mc.2.1, ha1_ma]; exact hdom_l0
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store, hev_t_l0, hev_t_np]
      simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom0_t]
      rfl
    set m_st0 := Wave8Contracts.M26.updW t_mc.memory (BitVec.ofNat 64 l) hp
    set st_mc1 : PanSemStateFiniteExact 64 F := { t_mc with memory := m_st0 }
    have hev_t_l16 : @evalHOLExact 64 F _ st_mc1.toExact (fun a => Classical.propDecidable (st_mc1.memaddrs a))
        (.op .add [.var .local (ofString "l"), .const 16]) = some (.val (.word (BitVec.ofNat 64 (l + 16)))) := by
      simp [st_mc1, evalHOLExact, evalListHOLExact, ht_l, valueIsWord, valueWord, wordOpHOL, wordOp]
      exact hwl16_eq
    have hev_t_cap2 : @evalHOLExact 64 F _ st_mc1.toExact (fun a => Classical.propDecidable (st_mc1.memaddrs a))
        (.panop .mul [.var .local (ofString "cap"), .const 2]) = some (.val (.word (w_cap * 2#64))) := by
      rw [evalHOLExact]
      simp [st_mc1, evalListHOLExact, evalHOLExact, ht_cap, valueIsWord, valueWord, panOpHOL]
    have hst16_t : evaluateHOLFiniteState st_mc1
        (.store (.op .add [.var .local (ofString "l"), .const 16])
          (.panop .mul [.var .local (ofString "cap"), .const 2])) =
        (none, { st_mc1 with memory := Wave8Contracts.M26.updW m_st0 (BitVec.ofNat 64 (l + 16)) (w_cap * 2#64) }) := by
      have hdom16_st : st_mc1.memaddrs (BitVec.ofNat 64 (l + 16)) := by
        change t_mc.memaddrs _; rw [hmwf_mc.2.1, ha1_ma]; exact hdom_l16'
      rw [evaluateHOLFiniteState_store, hev_t_l16, hev_t_cap2]
      simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom16_st]
      rfl
    set m_st16 := Wave8Contracts.M26.updW m_st0 (BitVec.ofNat 64 (l + 16)) (w_cap * 2#64)
    set st_ite_post : PanSemStateFiniteExact 64 F :=
      { st_mc1 with
        memory := m_st16
        locals := HolFiniteMapExact.resVarEq st_mc1.locals (ofString "np", d2.locals.lookup (ofString "np")) }
    have hite_full : evaluateHOLFiniteState d2
        (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
          (.decCall (ofString "np") .one (ofString "alloc")
            [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "np"),
                 .load .one (.op .add [.var .local (ofString "l"), .const 0]),
                 .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
              (.seq
                (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
                (.store (.op .add [.var .local (ofString "l"), .const 16])
                  (.panop .mul [.var .local (ofString "cap"), .const 2])))))
          .skip) = (none, st_ite_post) := by
      rw [hite_then]
      apply Prod.ext
      · rw [heq_r_a, hmc_step, hst0_t]
        change (evaluateHOLFiniteState st_mc1 _).1 = none
        rw [hst16_t]
      · rw [heq_p_a]; dsimp only
        rw [hmc_step, hst0_t]
        have hst16_t' : evaluateHOLFiniteState { t_mc with memory := m_st0 }
            (.store (.op .add [.var .local (ofString "l"), .const 16])
              (.panop .mul [.var .local (ofString "cap"), .const 2])) =
            (none, { st_mc1 with memory := m_st16 }) := hst16_t
        rw [hst16_t']
    have hd2_seq_eq : ∀ tail : ProgHOL 64,
        evaluateHOLFiniteState d2
          (.seq
            (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
              (.decCall (ofString "np") .one (ofString "alloc")
                [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
                (.seq
                  (.call (some (none, none)) (ofString "memcpy")
                    [.var .local (ofString "np"),
                     .load .one (.op .add [.var .local (ofString "l"), .const 0]),
                     .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
                  (.seq
                    (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
                    (.store (.op .add [.var .local (ofString "l"), .const 16])
                      (.panop .mul [.var .local (ofString "cap"), .const 2])))))
              .skip)
            tail) = evaluateHOLFiniteState st_ite_post tail := by
      intro tail
      rw [evaluateHOLFiniteState_seq_line780, hite_full]
    rw [hd2_seq_eq] at hres2
    have hpost_ite_loc : ∀ k, ofString "np" ≠ k → st_ite_post.locals.lookup k = d2.locals.lookup k := by
      intro k hne
      change (HolFiniteMapExact.resVarEq t_mc.locals (ofString "np", d2.locals.lookup (ofString "np"))).lookup k = _
      rw [ht_loc]
      change (HolFiniteMapExact.resVarEq (d2.locals.update (ofString "np", .val (.word hp)))
        (ofString "np", d2.locals.lookup (ofString "np"))).lookup k = _
      simp only [HolFiniteMapExact.resVarEq]
      cases d2.locals.lookup (ofString "np") <;>
        simp [FDOMSUB_HOL, FUPDATE_HOL, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
    have hip_l : st_ite_post.locals.lookup (ofString "l") = some (.val (.word w_l)) := by
      rw [hpost_ite_loc _ (by decide)]; exact hd2_l
    have hip_esz : st_ite_post.locals.lookup (ofString "esz") = some (.val (.word 8#64)) := by
      rw [hpost_ite_loc _ (by decide)]; exact hd2_esz
    have hip_n : st_ite_post.locals.lookup (ofString "n") = some (.val (.word w_n)) := by
      rw [hpost_ite_loc _ (by decide)]; exact hd2_n
    have hev_ip_l8 : @evalHOLExact 64 F _ st_ite_post.toExact (fun a => Classical.propDecidable (st_ite_post.memaddrs a))
        (.op .add [.var .local (ofString "l"), .const 8]) = some (.val (.word (BitVec.ofNat 64 (l + 8)))) := by
      simp [evalHOLExact, evalListHOLExact, hip_l, valueIsWord, valueWord, wordOpHOL, wordOp]
      exact hwl8_eq
    have hev_ip_n1 : @evalHOLExact 64 F _ st_ite_post.toExact (fun a => Classical.propDecidable (st_ite_post.memaddrs a))
        (.op .add [.var .local (ofString "n"), .const 1]) = some (.val (.word (w_n + 1#64))) := by
      simp [evalHOLExact, evalListHOLExact, hip_n, valueIsWord, valueWord, wordOpHOL, wordOp]
    obtain ⟨_, hst8_ip⟩ := R13Wk06b.store_word_resumes_step (BitVec.ofNat 64 (l + 8)) (w_n + 1#64) hev_ip_l8 hev_ip_n1 hres2
    rw [hst8_ip] at hres2
    set m_final := Wave8Contracts.M26.updW m_st16 (BitVec.ofNat 64 (l + 8)) (w_n + 1#64)
    let st_ret2 : PanSemStateFiniteExact 64 F := { st_ite_post with memory := m_final }
    change Resumes (evaluateHOLFiniteState st_ret2 _).1 at hres2
    have hload_l0_ret2 : @evalHOLExact 64 F _ st_ret2.toExact (fun a => Classical.propDecidable (st_ret2.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "l"), .const 0])) = some (.val (.word hp)) := by
      have hwf1 : isWfShapeExactHOL st_ret2.toExact.structs ShapeHOL.one = true := rfl
      have had : @evalHOLExact 64 F _ st_ret2.toExact (fun a => Classical.propDecidable (st_ret2.memaddrs a))
          (.op .add [.var .local (ofString "l"), .const 0]) = some (.val (.word (BitVec.ofNat 64 l))) := by
        simp [st_ret2, evalHOLExact, evalListHOLExact, hip_l, valueIsWord, valueWord, wordOpHOL, wordOp]
        exact hwl0_eq
      have hdom_st2 : st_ret2.memaddrs (BitVec.ofNat 64 l) := by
        change t_mc.memaddrs _; rw [hmwf_mc.2.1, ha1_ma]; exact hdom_l0
      have hm_st2 : st_ret2.memory (BitVec.ofNat 64 l) = .word hp := by
        change m_final (BitVec.ofNat 64 l) = .word hp
        unfold m_final m_st16 m_st0 Wave8Contracts.M26.updW
        rw [if_neg hal0_ne8, if_neg hal0_ne16, if_pos rfl]
      rw [evalHOLExact]; simp only [hwf1, ↓reduceIte]
      rw [had]; simp [memLoadHOLExact, panMemLoadHOL, hdom_st2, hm_st2]
    have hev_mul_ret2 : @evalHOLExact 64 F _ st_ret2.toExact (fun a => Classical.propDecidable (st_ret2.memaddrs a))
        (.panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]) =
        some (.val (.word (w_n * 8#64))) := by
      rw [evalHOLExact]
      simp [st_ret2, evalListHOLExact, evalHOLExact, hip_n, hip_esz, valueIsWord, valueWord, panOpHOL]
    have hret2_eval : evaluateHOLFiniteState st_ret2
        (.return (.op .add
          [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
           .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]])) =
        (some (.returned (.val (.word (hp + w_n * 8#64)))), emptyLocalsHOLFinite st_ret2) := by
      rw [evaluateHOLFiniteState_return]
      have hadd_ret2 : @evalHOLExact 64 F _ st_ret2.toExact (fun a => Classical.propDecidable (st_ret2.memaddrs a))
          (.op .add
            [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
             .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]) =
          some (.val (.word (hp + w_n * 8#64))) := by
        rw [evalHOLExact]
        simp only [evalListHOLExact, hload_l0_ret2, hev_mul_ret2]
        simp [valueIsWord, valueWord, wordOpHOL, wordOp]
      rw [hadd_ret2]
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    set out_prog := evaluateHOLFiniteState s
      (.dec (ofString "n") .one (.load .one (.op .add [.var .local (ofString "l"), .const 8]))
        (.dec (ofString "cap") .one (.load .one (.op .add [.var .local (ofString "l"), .const 16]))
          (.seq
            (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
              (.decCall (ofString "np") .one (ofString "alloc")
                [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2]]
                (.seq
                  (.call (some (none, none)) (ofString "memcpy")
                    [.var .local (ofString "np"),
                     .load .one (.op .add [.var .local (ofString "l"), .const 0]),
                     .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
                  (.seq
                    (.store (.op .add [.var .local (ofString "l"), .const 0]) (.var .local (ofString "np")))
                    (.store (.op .add [.var .local (ofString "l"), .const 16])
                      (.panop .mul [.var .local (ofString "cap"), .const 2])))))
              .skip)
            (.seq
              (.store (.op .add [.var .local (ofString "l"), .const 8])
                (.op .add [.var .local (ofString "n"), .const 1]))
              (.return (.op .add
                [.load .one (.op .add [.var .local (ofString "l"), .const 0]),
                 .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]))))))
    have hout_r : out_prog.1 = some (.returned (.val (.word (hp + w_n * 8#64)))) := by
      rw [heq_r_d1, heq_r_d2, hd2_seq_eq, hst8_ip]
      exact congrArg Prod.fst hret2_eval
    have hout_mem : out_prog.2.memory = m_final := by
      rw [heq_p_d1]; dsimp only; rw [heq_p_d2]; dsimp only; rw [hd2_seq_eq, hst8_ip]
      change { (evaluateHOLFiniteState st_ret2 _).2 with locals := _ }.memory = m_final
      rw [hret2_eval]; rfl
    have hout_glob : out_prog.2.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) := by
      rw [heq_p_d1]; dsimp only; rw [heq_p_d2]; dsimp only; rw [hd2_seq_eq, hst8_ip]
      change { (evaluateHOLFiniteState st_ret2 _).2 with locals := _ }.globals = _
      rw [hret2_eval]; change t_mc.globals = _; rw [ht_glob, ha1_glob]
    have hout_be : out_prog.2.be = s.be := by
      rw [heq_p_d1]; dsimp only; rw [heq_p_d2]; dsimp only; rw [hd2_seq_eq, hst8_ip]
      change { (evaluateHOLFiniteState st_ret2 _).2 with locals := _ }.be = s.be
      rw [hret2_eval]; change t_mc.be = s.be; rw [hmwf_mc.2.2.2.2.1, ha1_be]
    have hout_code : out_prog.2.code = s.code := by
      rw [heq_p_d1]; dsimp only; rw [heq_p_d2]; dsimp only; rw [hd2_seq_eq, hst8_ip]
      change { (evaluateHOLFiniteState st_ret2 _).2 with locals := _ }.code = s.code
      rw [hret2_eval]; change t_mc.code = s.code; rw [hmwf_mc.1, ha1_code, hcode]
    have hout_ma : out_prog.2.memaddrs = s.memaddrs := by
      rw [heq_p_d1]; dsimp only; rw [heq_p_d2]; dsimp only; rw [hd2_seq_eq, hst8_ip]
      change { (evaluateHOLFiniteState st_ret2 _).2 with locals := _ }.memaddrs = s.memaddrs
      rw [hret2_eval]; change t_mc.memaddrs = s.memaddrs; rw [hmwf_mc.2.1, ha1_ma]
    have hout_sh : out_prog.2.shMemaddrs = s.shMemaddrs := by
      rw [heq_p_d1]; dsimp only; rw [heq_p_d2]; dsimp only; rw [hd2_seq_eq, hst8_ip]
      change { (evaluateHOLFiniteState st_ret2 _).2 with locals := _ }.shMemaddrs = s.shMemaddrs
      rw [hret2_eval]; change t_mc.shMemaddrs = s.shMemaddrs; rw [hmwf_mc.2.2.1]
      change pa.shMemaddrs = s.shMemaddrs; rw [hpa_eq]; rfl
    have hout_ba : out_prog.2.baseAddr = s.baseAddr := by
      rw [heq_p_d1]; dsimp only; rw [heq_p_d2]; dsimp only; rw [hd2_seq_eq, hst8_ip]
      change { (evaluateHOLFiniteState st_ret2 _).2 with locals := _ }.baseAddr = s.baseAddr
      rw [hret2_eval]; change t_mc.baseAddr = s.baseAddr; rw [hmwf_mc.2.2.2.1]
      change pa.baseAddr = s.baseAddr; rw [hpa_eq]; rfl
    have hhp_post : globN out_prog.2 "heap_ptr" = q.toNat := by
      unfold globN; rw [hout_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hfp_post : globN out_prog.2 "frame_mem_ptr" = globN s "frame_mem_ptr" := by
      unfold globN; rw [hout_glob]
      simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
    have hsp_post : globN out_prog.2 "scratch_ptr" = globN s "scratch_ptr" := by
      unfold globN; rw [hout_glob]
      simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
    have hA_post : ArenaReady out_prog.2 := by
      refine ⟨guestInv_congr hout_code hout_ma hout_sh hout_ba hW.1.1, ?_⟩
      unfold ArenaOK
      rw [hhp_post, hfp_post, hsp_post]
      have hAs := hW.1.2
      have hsb_lo : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hAs.1
      exact ⟨by omega, hq_hi, hAs.2.2.1, hAs.2.2.2.1, hAs.2.2.2.2.1,
        hq_al, hAs.2.2.2.2.2.2.1, hAs.2.2.2.2.2.2.2.1,
        globalsWord_update (ofString "heap_ptr") q hout_glob hAs.2.2.2.2.2.2.2.2⟩
    have hhp_le : globN s "heap_ptr" ≤ globN out_prog.2 "heap_ptr" := by
      rw [hhp_post, ← hhp_eq]; exact hp_le_q
    have hGK : GlobalsKept ["heap_ptr"] s out_prog.2 := by
      intro k hk
      simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hk
      have hbeq : (ofString "heap_ptr" == k) = false := beq_eq_false_iff_ne.2 (Ne.symm hk)
      simp [hout_glob, HolFiniteMapExact.lookup_update, FUPDATE, hbeq]
    have hwn1_nat : (w_n + 1#64).toNat = n + 1 := by
      have hn_lt : n + 1 < 2 ^ 64 := by omega
      rw [BitVec.toNat_add_of_lt (by rw [hw_n_nat]; exact hn_lt), hw_n_nat]; rfl
    have hwcap2_nat : (w_cap * 2#64).toNat = 2 * cap := by
      rw [BitVec.toNat_mul, hw_cap_nat, show (2#64 : BitVec 64).toNat = 2 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      omega
    have hm_post_l0 : memW out_prog.2 l = hp.toNat := by
      unfold memW; rw [hout_mem]; unfold m_final m_st16 m_st0 Wave8Contracts.M26.updW
      rw [if_neg hal0_ne8, if_neg hal0_ne16, if_pos rfl]
    have hm_post_l8 : memW out_prog.2 (l + 8) = n + 1 := by
      unfold memW; rw [hout_mem]; unfold m_final Wave8Contracts.M26.updW
      rw [if_pos rfl]; exact hwn1_nat
    have hm_post_l16 : memW out_prog.2 (l + 16) = 2 * cap := by
      unfold memW; rw [hout_mem]; unfold m_final m_st16 Wave8Contracts.M26.updW
      rw [if_neg hal8_ne16.symm, if_pos rfl]; exact hwcap2_nat
    have h264_lim : heapLimit < 2 ^ 64 := by decide
    have hout_dom : ∀ a : BitVec 64, ¬ s.memaddrs a → out_prog.2.memory a = s.memory a := by
      intro a hna
      rw [hout_mem]; unfold m_final m_st16 m_st0 Wave8Contracts.M26.updW
      rw [if_neg (by rintro rfl; exact hna hdom_l8),
          if_neg (by rintro rfl; exact hna hdom_l16'),
          if_neg (by rintro rfl; exact hna hdom_l0)]
      by_cases hneq : t_mc.memory a = a1.memory a
      · rw [hneq, ha1_mem]
      · exfalso; exact hna (ha1_ma ▸ hmwf_mc.2.2.2.2.2.2.2.2 a hneq)
    have hmem_frame : ∀ a : BitVec 64,
        ¬ CellHits a.toNat (l, 24) →
        ¬ CellHits a.toNat (InitECandidate.Solver.Wave8Contracts.M08.heapFree s) →
        out_prog.2.memory a = s.memory a := by
      intro a hnl hnhf
      rw [hout_mem]; unfold m_final m_st16 m_st0 Wave8Contracts.M26.updW
      have hne8 : a ≠ BitVec.ofNat 64 (l + 8) := by
        rintro rfl; apply hnl; unfold CellHits
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; dsimp only; omega
      have hne16 : a ≠ BitVec.ofNat 64 (l + 16) := by
        rintro rfl; apply hnl; unfold CellHits
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; dsimp only; omega
      have hne0 : a ≠ BitVec.ofNat 64 l := by
        rintro rfl; apply hnl; unfold CellHits
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; dsimp only; omega
      rw [if_neg hne8, if_neg hne16, if_neg hne0]
      have hnot_mc : ¬ CellHits a.toNat (hp.toNat, (8#64 * w_n).toNat) := by
        intro hch
        apply hnhf
        unfold CellHits at hch
        unfold InitECandidate.Solver.Wave8Contracts.M08.heapFree CellHits
        rw [h8n_bv_nat] at hch
        dsimp only at hch ⊢
        omega
      have ht_eq := hmwf_mc.2.2.2.2.2.2.1 a
        (fun i hi => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          subst hi; exact hnot_mc)
        (by unfold CellHits; dsimp only; omega)
      rw [ht_eq, ha1_mem]
    refine lst_push_worldStep_of_bo hW hA_post hbo_nz hwl_nz hl_choice' hhp_le hGK hout_be hout_dom hmem_frame
      ⟨by rw [hm_post_l16]; omega, by rw [hm_post_l8, hm_post_l16]; omega⟩
      (Or.inr ⟨by rw [hm_post_l0]; exact hhp_nz,
               by rw [hm_post_l0]; exact hhp_al8,
               by rw [hm_post_l0, hm_post_l16, hhp_post, ← hhp_eq]; exact ⟨le_refl _, by omega⟩⟩)
      (fun S Nd hWT hWT' => ?_)
    refine ⟨?_, ?_⟩
    · intro a hnl hnhf
      exact hmem_frame a (hl_nat ▸ hnl) hnhf
    · intro v hv
      rw [hout_r] at hv
      injection hv with hv'
      injection hv' with hv''; subst hv''
      have hmul_bv_nat : (w_n * 8#64).toNat = 8 * n := by
        rw [BitVec.toNat_mul, hw_n_nat, show (8#64 : BitVec 64).toNat = 8 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        omega
      have hw_ret_nat : (hp + w_n * 8#64).toNat = hp.toNat + 8 * n := by
        rw [BitVec.toNat_add_of_lt (by rw [hmul_bv_nat]; omega), hmul_bv_nat]
      have hw_ret_al : (hp + w_n * 8#64).toNat % 8 = 0 := by
        rw [hw_ret_nat]; omega
      refine ⟨hp + w_n * 8#64, rfl, hw_ret_al, ?_, ?_, ?_, ?_⟩
      · rw [hl_nat, hm_post_l0, hm_post_l16, hw_ret_nat]
        exact ⟨by omega, by omega⟩
      · rw [hl_nat, hm_post_l8]
      · rw [hl_nat, hm_post_l0, hw_ret_nat]
      · intro _ k hk
        rw [hl_nat] at hk
        rw [hl_nat, hm_post_l0]
        change k < n at hk
        -- First: `memW out_prog.2 (hp.toNat + 8 * k) = memW t_mc (hp.toNat + 8 * k)` (since `(l, 24)` is disjoint from `heapFree s`):
        have hl_disj_hf : Disj (l, 24) (InitECandidate.Solver.Wave8Contracts.M08.heapFree s) :=
          InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_heapFree hW.1.2 hl_al
        have hhp_k_ne_l : ∀ off : Nat, off < 24 →
            BitVec.ofNat 64 (hp.toNat + 8 * k) ≠ BitVec.ofNat 64 (l + off) := by
          intro off hoff heq
          have htn := congrArg BitVec.toNat heq
          rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at htn
          unfold InitECandidate.Solver.Wave8Contracts.M08.heapFree at hl_disj_hf
          rcases hl_disj_hf with h0 | h0 | h | h
          · omega
          · dsimp only at h0; omega
          · dsimp only at h; omega
          · dsimp only at h; omega
        have hm_out_tmc : memW out_prog.2 (hp.toNat + 8 * k) = memW t_mc (hp.toNat + 8 * k) := by
          unfold memW
          rw [hout_mem]; unfold m_final m_st16 m_st0 Wave8Contracts.M26.updW
          rw [if_neg (hhp_k_ne_l 8 (by omega)),
              if_neg (hhp_k_ne_l 16 (by omega)),
              if_neg (by simpa using hhp_k_ne_l 0 (by omega))]
        -- Second: `memW t_mc (hp.toNat + 8 * k) = memW a1 (p_old + 8 * k)` via `BytesCopiedUpTo` + `memW_eq_of_memB_eq`:
        have hp_disj_hf : Disj (p_old, 8 * cap) (InitECandidate.Solver.Wave8Contracts.M08.heapFree s) :=
          InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_heapFree hW.1.2 hp_old_al
        have hdisj_copy : Disj (hp.toNat, (8#64 * w_n).toNat) (w_pold.toNat, (8#64 * w_n).toNat) := by
          rw [h8n_bv_nat, hw_pold_nat, hn_eq_cap]
          unfold InitECandidate.Solver.Wave8Contracts.M08.heapFree at hp_disj_hf
          rcases hp_disj_hf with h0 | h0 | h | h
          · omega
          · dsimp only at h0; omega
          · dsimp only at h; exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))
          · dsimp only at h; exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
        have hsrc_hi_copy : w_pold.toNat + (8#64 * w_n).toNat ≤ 2 ^ 64 := by
          rw [hw_pold_nat, h8n_bv_nat]; omega
        have htmc_a1 : memW t_mc (hp.toNat + 8 * k) = memW a1 (p_old + 8 * k) := by
          apply R13Shards.memW_eq_of_memB_eq t_mc a1 (hp.toNat + 8 * k) (p_old + 8 * k) hmwf_mc.2.2.2.2.1
            (by omega) (by have := hp_old_words.1; omega) (by omega) (by omega)
          intro r hr
          have hcp_byte := hcp_mc hdisj_copy hsrc_hi_copy (8 * k + r) (by rw [h8n_bv_nat]; omega)
          rw [hw_pold_nat] at hcp_byte
          simpa [Nat.add_assoc] using hcp_byte
        have ha1_s : memW a1 (p_old + 8 * k) = memW s (p_old + 8 * k) := by
          unfold memW; rw [ha1_mem]
        exact hm_out_tmc.trans (htmc_a1.trans ha1_s)

theorem wk_lst_push_strong :
    WorldKeeps BoListArgStrong (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
     ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetListSlotStrong (ofString "lst_push") := by
  refine ⟨_, _, _, R13Shards.lookup_lst_push, fun {F} s hcode hPre hcall _ hres => ?_⟩
  exact lst_push_worldStep_strong s hcode hPre hcall hres

theorem wk_lst_push_strong_boListArgStrong :
    WorldKeeps BoListArgStrong (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
     ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetListSlot (ofString "lst_push") := by
  rcases wk_lst_push_strong with ⟨ps, body, ret, hlook, hrun⟩
  refine ⟨ps, body, ret, hlook, fun {F} s hcode hPre hcall hnt hres => ?_⟩
  obtain ⟨hA, hhp, hG, hRK, hWT⟩ := hrun s hcode hPre hcall hnt hres
  refine ⟨hA, hhp, hG, hRK, fun S Nd hWTs hDisj => ?_⟩
  obtain ⟨S', Nd', hsub, hWTp, hOG, hFO, hStrong⟩ := hWT S Nd hWTs hDisj
  refine ⟨S', Nd', hsub, hWTp, hOG, hFO, fun v hv => ?_⟩
  obtain ⟨w, rfl, hal, hin, _, _, _⟩ := hStrong.2 v hv
  exact ⟨w, rfl, hal, hin⟩

theorem worldTypedWith_release_marks_ptx {F : Type}
    {s_pmc s_cur : PanSemStateFiniteExact 64 F}
    {S_pmc Nd_pmc S_cur Nd_cur : List Nat}
    {w_mark w_fmark : BitVec 64} {ck : Nat}
    (hA_pmc : ArenaReady s_pmc)
    (hA_cur : ArenaReady s_cur)
    (hWT_pmc : WorldTypedWith s_pmc S_pmc Nd_pmc)
    (hWT_cur : WorldTypedWith s_cur S_cur Nd_cur)
    (hOG : OwnedGrows s_pmc s_cur (worldOwned s_pmc S_pmc Nd_pmc) (worldOwned s_cur S_cur Nd_cur))
    (hhp_le : globN s_pmc "heap_ptr" ≤ globN s_cur "heap_ptr")
    (hmark_align : w_mark.toNat % 8 = 0)
    (hfmark_align : w_fmark.toNat % 8 = 0)
    (hfmark_lower : globN s_pmc "frame_mem_ptr" ≤ w_fmark.toNat)
    (hfmark_le_mark : w_fmark.toNat ≤ w_mark.toNat)
    (hmark_upper : w_mark.toNat ≤ globN s_pmc "scratch_ptr") :
    let s_rel : PanSemStateFiniteExact 64 F :=
      { s_cur with
        globals := (s_cur.globals.update (ofString "scratch_ptr", .val (.word w_mark))).update
          (ofString "frame_mem_ptr", .val (.word w_fmark))
        clock := ck }
    ArenaReady s_rel ∧
      WorldTypedWith s_rel S_cur Nd_cur ∧
      worldOwned s_rel S_cur Nd_cur = worldOwned s_cur S_cur Nd_cur := by
  intro s_rel
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT_cur
  have hgi_rel : GuestInv s_rel := guestInv_congr (s := s_cur) rfl rfl rfl rfl hA_cur.1
  have hgw1 : GlobalsWord { s_cur with globals := s_cur.globals.update (ofString "scratch_ptr", .val (.word w_mark)) } :=
    globalsWord_update (ofString "scratch_ptr") w_mark rfl hA_cur.2.2.2.2.2.2.2.2.2
  have hgw_rel : GlobalsWord s_rel :=
    globalsWord_update (ofString "frame_mem_ptr") w_fmark rfl hgw1
  have hg_ne : ∀ name : String,
      ofString name ≠ ofString "frame_mem_ptr" →
      ofString name ≠ ofString "scratch_ptr" →
      globN s_rel name = globN s_cur name := by
    intro name hne1 hne2
    simp [s_rel, globN, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne1, Ne.symm hne2]
  have hhp_rel : globN s_rel "heap_ptr" = globN s_cur "heap_ptr" :=
    hg_ne "heap_ptr" (by decide) (by decide)
  have hfmp_rel : globN s_rel "frame_mem_ptr" = w_fmark.toNat := by
    simp [s_rel, globN, HolFiniteMapExact.lookup_update, FUPDATE]
  have hsp_rel : globN s_rel "scratch_ptr" = w_mark.toNat := by
    have hne : ofString "scratch_ptr" ≠ ofString "frame_mem_ptr" := by decide
    simp [s_rel, globN, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
  have hA_rel : ArenaReady s_rel := by
    refine ⟨hgi_rel, ?_⟩
    unfold ArenaOK
    rw [hhp_rel, hfmp_rel, hsp_rel]
    exact ⟨hA_cur.2.1, hA_cur.2.2.1, le_trans hA_pmc.2.2.2.1 hfmark_lower, hfmark_le_mark,
      le_trans hmark_upper hA_pmc.2.2.2.2.2.1, hA_cur.2.2.2.2.2.2.1, hfmark_align, hmark_align, hgw_rel⟩
  have hmemW : memW s_rel = memW s_cur := rfl
  have hhdr : hdr s_rel = hdr s_cur := rfl
  have hnodeF : nodeF s_rel = nodeF s_cur := rfl
  have hfp : htabFootprint s_rel = htabFootprint s_cur := rfl
  have hhWF : ∀ t, HtabWF s_cur t → HtabWF s_rel t := fun t h =>
    InitECandidate.Solver.Wave8Contracts.M08.htabWF_congr_unhit hA_cur.1 hA_rel.1 h (fun _ _ _ _ _ _ => rfl)
  have hlstOK : ∀ l, LstOK s_rel l ↔ LstOK s_cur l := fun _ => Iff.rfl
  have hhVals : htabValues s_rel = htabValues s_cur := rfl
  have hwordsOK : ∀ i, WordsOK s_rel i ↔ WordsOK s_cur i := fun _ => Iff.rfl
  have hba_eq : globN s_rel "bal_accounts" = globN s_cur "bal_accounts" := hg_ne "bal_accounts" (by decide) (by decide)
  have hbia_eq : globN s_rel "bal_idx_accts" = globN s_cur "bal_idx_accts" := hg_ne "bal_idx_accts" (by decide) (by decide)
  have hbis_eq : globN s_rel "bal_idx_stor" = globN s_cur "bal_idx_stor" := hg_ne "bal_idx_stor" (by decide) (by decide)
  have hbo_eq : globN s_rel "bo" = globN s_cur "bo" := hg_ne "bo" (by decide) (by decide)
  have hws_eq : globN s_rel "ws" = globN s_cur "ws" := hg_ne "ws" (by decide) (by decide)
  have hbs_eq : globN s_rel "bs" = globN s_cur "bs" := hg_ne "bs" (by decide) (by decide)
  have hts_eq : globN s_rel "ts" = globN s_cur "ts" := hg_ne "ts" (by decide) (by decide)
  have hjc_eq : globN s_rel "journal_cap" = globN s_cur "journal_cap" := hg_ne "journal_cap" (by decide) (by decide)
  have hjr_eq : globN s_rel "journal" = globN s_cur "journal" := hg_ne "journal" (by decide) (by decide)
  have hjn_eq : globN s_rel "journal_n" = globN s_cur "journal_n" := hg_ne "journal_n" (by decide) (by decide)
  have hbalRecs : balRecords s_rel = balRecords s_cur := by
    simp only [balRecords, hba_eq, hhdr, hnodeF, hmemW]
  have hbalObjs : balObjects s_rel = balObjects s_cur := by
    simp only [balObjects, hbalRecs, lstObjects, hhVals, hmemW]
  have hboObjs : blockOutObjects s_rel = blockOutObjects s_cur := by
    simp only [blockOutObjects, hbo_eq, hmemW]
  have hgb_ne1 : ∀ gn ∈ globalBuffers, ofString gn.1 ≠ ofString "frame_mem_ptr" := by decide
  have hgb_ne2 : ∀ gn ∈ globalBuffers, ofString gn.1 ≠ ofString "scratch_ptr" := by decide
  have hgb_map :
      (globalBuffers.map fun gn => (globN s_rel gn.1, if globN s_rel gn.1 = 0 then 0 else gn.2)) =
      (globalBuffers.map fun gn => (globN s_cur gn.1, if globN s_cur gn.1 = 0 then 0 else gn.2)) := by
    apply List.map_congr_left
    intro gn hgn
    rw [hg_ne gn.1 (hgb_ne1 gn hgn) (hgb_ne2 gn hgn)]
  have hfixObjs : fixedObjects s_rel = fixedObjects s_cur := by
    simp only [fixedObjects, hgb_map, hjc_eq, hjr_eq, hboObjs, hbalObjs]
  have hnodeExt : nodeExtents s_rel Nd_cur = nodeExtents s_cur Nd_cur := rfl
  have hwo_eq : worldOwned s_rel S_cur Nd_cur = worldOwned s_cur S_cur Nd_cur := by
    simp only [worldOwned, hfp, hfixObjs, hnodeExt]
  have hss_pos : 0 < scratchStart := by decide
  have halloc_owned : ∀ i ∈ worldOwned s_cur S_cur Nd_cur, Allocated s_cur i → Allocated s_rel i := by
    intro i hi hal_cur
    rcases hOG i hi with rfl | ⟨j, hj, hin_ij⟩ | hin_fresh
    · rcases hal_cur with h_hp | h_sp
      · exact Or.inl ⟨h_hp.1, by rw [hhp_rel]; exact h_hp.2⟩
      · exfalso
        have : scratchStart ≤ 0 := le_trans (le_trans hA_cur.2.2.2.1 hA_cur.2.2.2.2.1) h_sp.1
        omega
    · rcases InitECandidate.Solver.Wave8GuestInv.R16Shards.worldOwned_zero_or_allocated hWT_pmc j hj with rfl | ⟨_, hal_j⟩
      · have hi_zero : i = (0, 0) := by
          rcases i with ⟨i1, i2⟩
          dsimp only [Inside] at hin_ij
          exact Prod.ext (by omega) (by omega)
        subst hi_zero
        rcases hal_cur with h_hp | h_sp
        · exact Or.inl ⟨h_hp.1, by rw [hhp_rel]; exact h_hp.2⟩
        · exfalso
          have : scratchStart ≤ 0 := le_trans (le_trans hA_cur.2.2.2.1 hA_cur.2.2.2.2.1) h_sp.1
          omega
      · rcases hal_j with hj_hp | hj_sp
        · exact Or.inl ⟨le_trans hj_hp.1 hin_ij.1,
            by rw [hhp_rel]; exact le_trans hin_ij.2 (le_trans hj_hp.2 hhp_le)⟩
        · exact Or.inr ⟨by rw [hsp_rel]; exact le_trans hmark_upper (le_trans hj_sp.1 hin_ij.1),
            le_trans hin_ij.2 hj_sp.2⟩
    · exact Or.inl ⟨le_trans hA_pmc.2.1 hin_fresh.1,
        by rw [hhp_rel]; exact hin_fresh.2⟩
  have hrecR_ws : ∀ ks, recRoles s_rel "ws" ks = recRoles s_cur "ws" ks := fun _ => by
    simp only [recRoles, hws_eq, hmemW]
  have hrecR_bs : ∀ ks, recRoles s_rel "bs" ks = recRoles s_cur "bs" ks := fun _ => by
    simp only [recRoles, hbs_eq, hmemW]
  have hrecR_ts : ∀ ks, recRoles s_rel "ts" ks = recRoles s_cur "ts" ks := fun _ => by
    simp only [recRoles, hts_eq, hmemW]
  have hnest_bs : nestRoles s_rel "bs" "bs.inner" = nestRoles s_cur "bs" "bs.inner" := by
    simp only [nestRoles, hbs_eq, hmemW, hhVals]
  have hnest_ts : nestRoles s_rel "ts" "ts.inner" = nestRoles s_cur "ts" "ts.inner" := by
    simp only [nestRoles, hts_eq, hmemW, hhVals]
  have hwrs : worldRoleSlots s_rel = worldRoleSlots s_cur := by
    simp only [worldRoleSlots, hrecR_ws, hrecR_bs, hrecR_ts, hba_eq, hbia_eq, hbis_eq,
      hnest_bs, hnest_ts, hbalRecs, hmemW]
  have hjRole : journalRole s_rel = journalRole s_cur := by
    funext t
    simp only [journalRole, hts_eq, hmemW]
  have hjrs : journalRoleSlots s_rel = journalRoleSlots s_cur := by
    simp only [journalRoleSlots, hjn_eq, hjr_eq, hjRole, hmemW]
  refine ⟨hA_rel, ⟨?_, ?_, ?_, ?_⟩, hwo_eq⟩
  · obtain ⟨hnd, htf, htp, hws_s, hbs_s, hts_s, hgt_s, hb_in, ht_in, hbal_t, hbo_t, hrol⟩ := hT
    refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      refine ⟨hhWF t (htf t ht).1, fun i hi => ?_⟩
      rw [hfp] at hi
      rw [hfixObjs]
      have hwo_i : i ∈ worldOwned s_cur S_cur Nd_cur :=
        List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t, ht, hi⟩))
      exact ⟨halloc_owned i hwo_i ((htf t ht).2 i hi).1, ((htf t ht).2 i hi).2⟩
    · simpa only [hfp] using htp
    · simpa only [hws_eq, hmemW] using hws_s
    · simpa only [hbs_eq, hmemW] using hbs_s
    · simpa only [hts_eq, hmemW] using hts_s
    · intro g hg
      have hg_ne1 : ofString g ≠ ofString "frame_mem_ptr" := by
        simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl <;> decide
      have hg_ne2 : ofString g ≠ ofString "scratch_ptr" := by
        simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl <;> decide
      rw [hg_ne g hg_ne1 hg_ne2]
      exact hgt_s g hg
    · simpa only [hbs_eq, hmemW, HtabValuesIn, hhdr, hnodeF] using hb_in
    · simpa only [hts_eq, hmemW, HtabValuesIn, hhdr, hnodeF] using ht_in
    · simpa only [hbalRecs, hmemW, hlstOK, hhVals] using hbal_t
    · simpa only [hbo_eq, hmemW, hlstOK] using hbo_t
    · simpa only [hwrs, hjrs, RolesOK, hhdr] using hrol
  · refine ⟨by rw [hjn_eq, hjc_eq]; exact hJ.1,
      by rw [hjc_eq]; exact hJ.2.1, ?_, ?_⟩
    · rw [hjc_eq, hjr_eq]
      rcases hJ.2.2.1 with h0 | ⟨ha, hw⟩
      · exact Or.inl h0
      · by_cases hcz : globN s_cur "journal_cap" = 0
        · exact Or.inl hcz
        · have hwo_j : (globN s_cur "journal", 32 * globN s_cur "journal_cap") ∈
              worldOwned s_cur S_cur Nd_cur := by
            apply List.mem_append_left; apply List.mem_append_right
            unfold fixedObjects
            apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
            simp [hcz]
          exact Or.inr ⟨halloc_owned _ hwo_j ha, (hwordsOK _).2 hw⟩
    · intro i hi
      rw [hjn_eq] at hi
      rw [hjr_eq, hmemW]
      exact hJ.2.2.2 i hi
  · unfold FixedTyped; rw [hfixObjs]
    refine ⟨fun i hi => ?_, hF.2⟩
    have hwo_i : i ∈ worldOwned s_cur S_cur Nd_cur :=
      List.mem_append_left _ (List.mem_append_right _ hi)
    exact (hF.1 i hi).elim Or.inl (fun h => Or.inr ⟨halloc_owned i hwo_i h.1, (hwordsOK i).2 h.2⟩)
  · unfold TriesTypedWith
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨fun n hn => ?_, by simpa only [nodeIvl, hmemW] using hTr.1.2⟩
      obtain ⟨hk, hal_n, hin_n, hw_n, hext, hbr, hkey, h16, h56, h168⟩ := hTr.1.1 n hn
      have hwo_n : nodeIvl s_cur n ∈ worldOwned s_cur S_cur Nd_cur := by
        apply List.mem_append_right
        exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
      refine ⟨hk, halloc_owned _ hwo_n hal_n, hin_n, hw_n, hext, hbr, ?_, h16, h56, h168⟩
      intro h12
      rcases hkey h12 with hlen0 | ⟨hnib, hal_k, hin_k, hdisj_k⟩
      · exact Or.inl hlen0
      · by_cases hlen_z : memW s_cur (n + 40) = 0
        · exact Or.inl hlen_z
        · have hwo_k : (memW s_cur (n + 32), memW s_cur (n + 40)) ∈ worldOwned s_cur S_cur Nd_cur := by
            apply List.mem_append_right
            have hnp : nodePath s_cur n = (memW s_cur (n + 32), memW s_cur (n + 40)) := by
              unfold nodePath; rw [if_pos ⟨h12, hlen_z⟩]
            exact List.mem_flatMap.2 ⟨n, hn, List.mem_cons_of_mem _ (List.mem_singleton.2 hnp.symm)⟩
          exact Or.inr ⟨hnib, halloc_owned _ hwo_k hal_k, hin_k, hdisj_k⟩
    · rw [hnodeExt, hfixObjs]; simpa only [hfp] using hTr.2.1
    · simpa only [hws_eq, hmemW, hfp, hhdr, hnodeF] using hTr.2.2

theorem lookup_frame_mem_release_ptx :
    originalRuntimeCode.lookup (ofString "frame_mem_release") =
      some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_frame_mem_release, .one) :=
  lookup_of_guestAst_getElem 12 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_frame_mem_release) rfl

theorem lookup_scratch_release_ptx :
    originalRuntimeCode.lookup (ofString "scratch_release") =
      some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_scratch_release, .one) :=
  lookup_of_guestAst_getElem 15 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_scratch_release) rfl

theorem scratch_release_call_exact_ptx {F : Type}
    (st : PanSemStateFiniteExact 64 F) (mExp : ExpHOL 64) (mw : BitVec 64)
    (hcode : st.code = originalRuntimeCode)
    (hA : ArenaReady st)
    (hm : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) mExp =
      some (.val (.word mw)))
    (hnt : (evaluateHOLFiniteState st (.call (some (none, none)) (ofString "scratch_release") [mExp])).1 ≠
      some .timeOut) :
    ∃ ck, evaluateHOLFiniteState st (.call (some (none, none)) (ofString "scratch_release") [mExp]) =
      (none, { st with
        globals := st.globals.update (ofString "scratch_ptr", .val (.word mw))
        clock := ck }) := by
  obtain ⟨spw, hsp⟩ := hA.2.2.2.2.2.2.2.2.2 "scratch_ptr" (by decide)
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) [mExp] =
      some [.val (.word mw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hm]
  have hl := pan_one_word_lookup st.code.lookup (ofString "scratch_release") (ofString "m")
    (sourceFnBody Guest.Software.guestFn_scratch_release) mw
    (by rw [hcode]; exact lookup_scratch_release_ptx)
  rw [hargs] at hnt ⊢; dsimp only at hnt ⊢; rw [hl] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hz : st.clock = 0
  · simp [hz] at hnt
  · rw [if_neg hz]
    let entry := callEntryStateHOLFinite st (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw)))
    have hb : sourceFnBody Guest.Software.guestFn_scratch_release =
        .seq (.assign .global (ofString "scratch_ptr") (.var .local (ofString "m"))) (.return (.const 0)) := rfl
    have hev_b : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_scratch_release) =
        (some (.returned (.val (.word 0))),
          emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word mw)) entry)) := by
      rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
      have hm_ent : entry.locals.lookup (ofString "m") = some (.val (.word mw)) := by
        simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hsp_ent : entry.globals.lookup (ofString "scratch_ptr") = some (.val (.word spw)) := hsp
      simp [evalHOLExact, hm_ent, isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLFinite, lookupKvarHOLExact,
        hsp_ent, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
        evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
    have hev_b' : evaluateHOLFiniteState
        (callEntryStateHOLFinite st (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw))))
        (sourceFnBody Guest.Software.guestFn_scratch_release) =
        (some (.returned (.val (.word 0))),
          emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word mw)) entry)) := hev_b
    rw [hev_b']; dsimp only
    have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh]
    exact ⟨st.clock - 1, rfl⟩

theorem frame_mem_release_call_exact_ptx {F : Type}
    (st : PanSemStateFiniteExact 64 F) (mExp : ExpHOL 64) (mw : BitVec 64)
    (hcode : st.code = originalRuntimeCode)
    (hA : ArenaReady st)
    (hm : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) mExp =
      some (.val (.word mw)))
    (hnt : (evaluateHOLFiniteState st (.call (some (none, none)) (ofString "frame_mem_release") [mExp])).1 ≠
      some .timeOut) :
    ∃ ck, evaluateHOLFiniteState st (.call (some (none, none)) (ofString "frame_mem_release") [mExp]) =
      (none, { st with
        globals := st.globals.update (ofString "frame_mem_ptr", .val (.word mw))
        clock := ck }) := by
  obtain ⟨fpw, hfp⟩ := hA.2.2.2.2.2.2.2.2.2 "frame_mem_ptr" (by decide)
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) [mExp] =
      some [.val (.word mw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hm]
  have hl := pan_one_word_lookup st.code.lookup (ofString "frame_mem_release") (ofString "m")
    (sourceFnBody Guest.Software.guestFn_frame_mem_release) mw
    (by rw [hcode]; exact lookup_frame_mem_release_ptx)
  rw [hargs] at hnt ⊢; dsimp only at hnt ⊢; rw [hl] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hz : st.clock = 0
  · simp [hz] at hnt
  · rw [if_neg hz]
    let entry := callEntryStateHOLFinite st (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw)))
    have hb : sourceFnBody Guest.Software.guestFn_frame_mem_release =
        .seq (.assign .global (ofString "frame_mem_ptr") (.var .local (ofString "m"))) (.return (.const 0)) := rfl
    have hev_b : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_frame_mem_release) =
        (some (.returned (.val (.word 0))),
          emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "frame_mem_ptr") (.val (.word mw)) entry)) := by
      rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
      have hm_ent : entry.locals.lookup (ofString "m") = some (.val (.word mw)) := by
        simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hfp_ent : entry.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fpw)) := hfp
      simp [evalHOLExact, hm_ent, isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLFinite, lookupKvarHOLExact,
        hfp_ent, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
        evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
    have hev_b' : evaluateHOLFiniteState
        (callEntryStateHOLFinite st (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw))))
        (sourceFnBody Guest.Software.guestFn_frame_mem_release) =
        (some (.returned (.val (.word 0))),
          emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "frame_mem_ptr") (.val (.word mw)) entry)) := hev_b
    rw [hev_b']; dsimp only
    have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh]
    exact ⟨st.clock - 1, rfl⟩

theorem frame_mem_release_call_exact_globalsWord_ptx {F : Type}
    (st : PanSemStateFiniteExact 64 F) (mExp : ExpHOL 64) (mw : BitVec 64)
    (hcode : st.code = originalRuntimeCode)
    (hgw : GlobalsWord st)
    (hm : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) mExp =
      some (.val (.word mw)))
    (hnt : (evaluateHOLFiniteState st (.call (some (none, none)) (ofString "frame_mem_release") [mExp])).1 ≠
      some .timeOut) :
    ∃ ck, evaluateHOLFiniteState st (.call (some (none, none)) (ofString "frame_mem_release") [mExp]) =
      (none, { st with
        globals := st.globals.update (ofString "frame_mem_ptr", .val (.word mw))
        clock := ck }) := by
  obtain ⟨fpw, hfp⟩ := hgw "frame_mem_ptr" (by decide)
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) [mExp] =
      some [.val (.word mw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hm]
  have hl := pan_one_word_lookup st.code.lookup (ofString "frame_mem_release") (ofString "m")
    (sourceFnBody Guest.Software.guestFn_frame_mem_release) mw
    (by rw [hcode]; exact lookup_frame_mem_release_ptx)
  rw [hargs] at hnt ⊢; dsimp only at hnt ⊢; rw [hl] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hz : st.clock = 0
  · simp [hz] at hnt
  · rw [if_neg hz]
    let entry := callEntryStateHOLFinite st (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw)))
    have hb : sourceFnBody Guest.Software.guestFn_frame_mem_release =
        .seq (.assign .global (ofString "frame_mem_ptr") (.var .local (ofString "m"))) (.return (.const 0)) := rfl
    have hev_b : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_frame_mem_release) =
        (some (.returned (.val (.word 0))),
          emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "frame_mem_ptr") (.val (.word mw)) entry)) := by
      rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
      have hm_ent : entry.locals.lookup (ofString "m") = some (.val (.word mw)) := by
        simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hfp_ent : entry.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fpw)) := hfp
      simp [evalHOLExact, hm_ent, isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLFinite, lookupKvarHOLExact,
        hfp_ent, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
        evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
    have hev_b' : evaluateHOLFiniteState
        (callEntryStateHOLFinite st (HolFiniteMapExact.empty.update (ofString "m", .val (.word mw))))
        (sourceFnBody Guest.Software.guestFn_frame_mem_release) =
        (some (.returned (.val (.word 0))),
          emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "frame_mem_ptr") (.val (.word mw)) entry)) := hev_b
    rw [hev_b']; dsimp only
    have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hsh]
    exact ⟨st.clock - 1, rfl⟩

theorem ptx_release_calls_exact {F : Type}
    (s_cur : PanSemStateFiniteExact 64 F) (mExp fExp : ExpHOL 64)
    (w_mark w_fmark : BitVec 64)
    (hcode : s_cur.code = originalRuntimeCode)
    (hA_cur : ArenaReady s_cur)
    (hm : @evalHOLExact 64 F _ s_cur.toExact
      (fun a => Classical.propDecidable (s_cur.memaddrs a)) mExp = some (.val (.word w_mark)))
    (hf : ∀ ck, @evalHOLExact 64 F _
      ({ s_cur with
        globals := s_cur.globals.update (ofString "scratch_ptr", .val (.word w_mark))
        clock := ck } : PanSemStateFiniteExact 64 F).toExact
      (fun a => Classical.propDecidable (s_cur.memaddrs a)) fExp = some (.val (.word w_fmark)))
    (hnt : (evaluateHOLFiniteState s_cur
      (.seq (.call (some (none, none)) (ofString "scratch_release") [mExp])
        (.call (some (none, none)) (ofString "frame_mem_release") [fExp]))).1 ≠ some .timeOut) :
    ∃ ck, evaluateHOLFiniteState s_cur
      (.seq (.call (some (none, none)) (ofString "scratch_release") [mExp])
        (.call (some (none, none)) (ofString "frame_mem_release") [fExp])) =
      (none, { s_cur with
        globals := (s_cur.globals.update (ofString "scratch_ptr", .val (.word w_mark))).update
          (ofString "frame_mem_ptr", .val (.word w_fmark))
        clock := ck }) := by
  have hnt_s : (evaluateHOLFiniteState s_cur
      (.call (some (none, none)) (ofString "scratch_release") [mExp])).1 ≠ some .timeOut := by
    intro ht
    rw [evaluateHOLFiniteState_seq_line780] at hnt
    rcases hs : evaluateHOLFiniteState s_cur
      (.call (some (none, none)) (ofString "scratch_release") [mExp]) with ⟨r, post⟩
    rw [hs] at ht hnt
    dsimp only at ht
    subst r
    exact hnt rfl
  obtain ⟨ck1, hs⟩ := scratch_release_call_exact_ptx s_cur mExp w_mark hcode hA_cur hm hnt_s
  rw [evaluateHOLFiniteState_seq_line780, hs] at hnt ⊢
  dsimp only at hnt ⊢
  have hgw : GlobalsWord
      ({ s_cur with
        globals := s_cur.globals.update (ofString "scratch_ptr", .val (.word w_mark))
        clock := ck1 } : PanSemStateFiniteExact 64 F) :=
    globalsWord_update (ofString "scratch_ptr") w_mark rfl hA_cur.2.2.2.2.2.2.2.2.2
  obtain ⟨ck2, hf2⟩ := frame_mem_release_call_exact_globalsWord_ptx
    { s_cur with
      globals := s_cur.globals.update (ofString "scratch_ptr", .val (.word w_mark))
      clock := ck1 } fExp w_fmark hcode hgw (hf ck1) hnt
  exact ⟨ck2, hf2⟩

theorem ptx_release_calls_worldTyped {F : Type}
    {s_pmc s_cur : PanSemStateFiniteExact 64 F}
    {S_pmc Nd_pmc S_cur Nd_cur : List Nat}
    (mExp fExp : ExpHOL 64) (w_mark w_fmark : BitVec 64)
    (hcode : s_cur.code = originalRuntimeCode)
    (hA_pmc : ArenaReady s_pmc)
    (hA_cur : ArenaReady s_cur)
    (hWT_pmc : WorldTypedWith s_pmc S_pmc Nd_pmc)
    (hWT_cur : WorldTypedWith s_cur S_cur Nd_cur)
    (hOG : OwnedGrows s_pmc s_cur (worldOwned s_pmc S_pmc Nd_pmc) (worldOwned s_cur S_cur Nd_cur))
    (hhp_le : globN s_pmc "heap_ptr" ≤ globN s_cur "heap_ptr")
    (hmark_align : w_mark.toNat % 8 = 0)
    (hfmark_align : w_fmark.toNat % 8 = 0)
    (hfmark_lower : globN s_pmc "frame_mem_ptr" ≤ w_fmark.toNat)
    (hfmark_le_mark : w_fmark.toNat ≤ w_mark.toNat)
    (hmark_upper : w_mark.toNat ≤ globN s_pmc "scratch_ptr")
    (hm : @evalHOLExact 64 F _ s_cur.toExact
      (fun a => Classical.propDecidable (s_cur.memaddrs a)) mExp = some (.val (.word w_mark)))
    (hf : ∀ ck, @evalHOLExact 64 F _
      ({ s_cur with
        globals := s_cur.globals.update (ofString "scratch_ptr", .val (.word w_mark))
        clock := ck } : PanSemStateFiniteExact 64 F).toExact
      (fun a => Classical.propDecidable (s_cur.memaddrs a)) fExp = some (.val (.word w_fmark)))
    (hnt : (evaluateHOLFiniteState s_cur
      (.seq (.call (some (none, none)) (ofString "scratch_release") [mExp])
        (.call (some (none, none)) (ofString "frame_mem_release") [fExp]))).1 ≠ some .timeOut) :
    ∃ ck, let s_rel : PanSemStateFiniteExact 64 F :=
      { s_cur with
        globals := (s_cur.globals.update (ofString "scratch_ptr", .val (.word w_mark))).update
          (ofString "frame_mem_ptr", .val (.word w_fmark))
        clock := ck }
      evaluateHOLFiniteState s_cur
        (.seq (.call (some (none, none)) (ofString "scratch_release") [mExp])
          (.call (some (none, none)) (ofString "frame_mem_release") [fExp])) = (none, s_rel) ∧
      ArenaReady s_rel ∧ WorldTypedWith s_rel S_cur Nd_cur ∧
        worldOwned s_rel S_cur Nd_cur = worldOwned s_cur S_cur Nd_cur := by
  obtain ⟨ck, heval⟩ := ptx_release_calls_exact s_cur mExp fExp w_mark w_fmark hcode hA_cur hm hf hnt
  exact ⟨ck, heval, worldTypedWith_release_marks_ptx hA_pmc hA_cur hWT_pmc hWT_cur hOG hhp_le
    hmark_align hfmark_align hfmark_lower hfmark_le_mark hmark_upper⟩

theorem ptx_release_calls_out88_worldTyped {F : Type}
    {s_pmc s_cur : PanSemStateFiniteExact 64 F}
    {S_pmc Nd_pmc S_cur Nd_cur : List Nat}
    (w_out w_mark w_fmark : BitVec 64)
    (hcode : s_cur.code = originalRuntimeCode)
    (hA_pmc : ArenaReady s_pmc)
    (hA_cur : ArenaReady s_cur)
    (hWT_pmc : WorldTypedWith s_pmc S_pmc Nd_pmc)
    (hWT_cur : WorldTypedWith s_cur S_cur Nd_cur)
    (hOG : OwnedGrows s_pmc s_cur (worldOwned s_pmc S_pmc Nd_pmc) (worldOwned s_cur S_cur Nd_cur))
    (hhp_le : globN s_pmc "heap_ptr" ≤ globN s_cur "heap_ptr")
    (hl_mark : s_cur.locals.lookup (ofString "tx_frame_mark") = some (.val (.word w_mark)))
    (hl_out : s_cur.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hdom88 : s_cur.memaddrs (w_out + BitVec.ofNat 64 88))
    (hmem88 : s_cur.memory (w_out + BitVec.ofNat 64 88) = .word w_fmark)
    (hmark_align : w_mark.toNat % 8 = 0)
    (hfmark_align : w_fmark.toNat % 8 = 0)
    (hfmark_lower : globN s_pmc "frame_mem_ptr" ≤ w_fmark.toNat)
    (hfmark_le_mark : w_fmark.toNat ≤ w_mark.toNat)
    (hmark_upper : w_mark.toNat ≤ globN s_pmc "scratch_ptr")
    (hnt : (evaluateHOLFiniteState s_cur
      (.seq (.call (some (none, none)) (ofString "scratch_release")
          [.var .local (ofString "tx_frame_mark")])
        (.call (some (none, none)) (ofString "frame_mem_release")
          [.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 88)])]))).1 ≠
      some .timeOut) :
    ∃ ck, let s_rel : PanSemStateFiniteExact 64 F :=
      { s_cur with
        globals := (s_cur.globals.update (ofString "scratch_ptr", .val (.word w_mark))).update
          (ofString "frame_mem_ptr", .val (.word w_fmark))
        clock := ck }
      evaluateHOLFiniteState s_cur
        (.seq (.call (some (none, none)) (ofString "scratch_release")
            [.var .local (ofString "tx_frame_mark")])
          (.call (some (none, none)) (ofString "frame_mem_release")
            [.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 88)])])) =
        (none, s_rel) ∧
      ArenaReady s_rel ∧ WorldTypedWith s_rel S_cur Nd_cur ∧
        worldOwned s_rel S_cur Nd_cur = worldOwned s_cur S_cur Nd_cur := by
  refine ptx_release_calls_worldTyped
    (.var .local (ofString "tx_frame_mark"))
    (.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 88)]))
    w_mark w_fmark hcode hA_pmc hA_cur hWT_pmc hWT_cur hOG hhp_le
    hmark_align hfmark_align hfmark_lower hfmark_le_mark hmark_upper ?_ ?_ hnt
  · simp [evalHOLExact, PanSemStateFiniteExact.toExact, hl_mark]
  · intro ck
    simp [evalHOLExact, evalListHOLExact, memLoadHOLExact, PanSemStateFiniteExact.toExact,
      hl_out, hdom88, hmem88, valueIsWord, valueWord, wordOpHOL, wordOp]

theorem memW_congr_memory_ptx {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hmem : post.memory = s.memory) :
    memW post = memW s := by
  funext a
  unfold memW
  rw [hmem]

theorem wordAt_congr_memory_dom_ptx {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hmem : post.memory = s.memory)
    (hdom : post.memaddrs = s.memaddrs) {a : Nat}
    (h : WordAt s a) :
    WordAt post a := by
  obtain ⟨w, hd, hm⟩ := h
  exact ⟨w, hdom ▸ hd, hmem ▸ hm⟩

theorem wordsOK_congr_memory_dom_ptx {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hmem : post.memory = s.memory)
    (hdom : post.memaddrs = s.memaddrs) {i : Ivl}
    (h : WordsOK s i) :
    WordsOK post i :=
  ⟨h.1, h.2.1, fun k hk => wordAt_congr_memory_dom_ptx hmem hdom (h.2.2 k hk)⟩

theorem logEntryOK_congr_memory_heap_ptx {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hmem : post.memory = s.memory)
    (hdom : post.memaddrs = s.memaddrs)
    (hhp : globN post "heap_ptr" = globN s "heap_ptr")
    {log : Nat}
    (hl : LogEntryOK s log) :
    LogEntryOK post log := by
  obtain ⟨hw, hin, h16, h32, hi0, hi8, hi24⟩ := hl
  have hmemW := memW_congr_memory_ptx hmem
  unfold LogEntryOK
  rw [hmemW, hhp]
  exact ⟨wordsOK_congr_memory_dom_ptx hmem hdom hw, hin, h16, h32, hi0, hi8, hi24⟩

theorem stableLogsOK_congr_memory_heap_ptx {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hmem : post.memory = s.memory)
    (hdom : post.memaddrs = s.memaddrs)
    (hhp : globN post "heap_ptr" = globN s "heap_ptr")
    {logs : Nat}
    (hs : StableLogsOK s logs) :
    StableLogsOK post logs := by
  obtain ⟨hL, hstab⟩ := hs
  have hmemW := memW_congr_memory_ptx hmem
  rcases hstab with rfl | ⟨hhdr_hp, harr_hp⟩
  · exact ⟨Or.inl rfl, Or.inl rfl⟩
  · rcases hL with rfl | ⟨hw, _hal, hlen28, hlen_cap, hent⟩
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · have hhdr_post : Inside (logs, 24) sourceBase (globN post "heap_ptr") := by
        rw [hhp]
        exact hhdr_hp
      have harr_post : Inside (memW post logs, 8 * memW post (logs + 16)) sourceBase (globN post "heap_ptr") := by
        rw [hmemW, hhp]
        exact harr_hp
      refine ⟨Or.inr ?_, Or.inr ⟨hhdr_post, harr_post⟩⟩
      rw [hmemW]
      refine ⟨wordsOK_congr_memory_dom_ptx hmem hdom hw, Or.inl hhdr_post, hlen28, hlen_cap, fun i hi => ?_⟩
      obtain ⟨hwa, hle⟩ := hent i hi
      exact ⟨wordAt_congr_memory_dom_ptx hmem hdom hwa,
        logEntryOK_congr_memory_heap_ptx hmem hdom hhp hle⟩

theorem retTransactionLogs_congr_memory_heap_bo_ptx {F : Type}
    {entry s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    {S Nd : List Nat}
    (hmem : post.memory = s.memory)
    (hdom : post.memaddrs = s.memaddrs)
    (hhp : globN post "heap_ptr" = globN s "heap_ptr")
    (hbo : globN post "bo" = globN s "bo")
    (hret : RetTransactionLogs entry r s S Nd) :
    RetTransactionLogs entry r post S Nd := by
  intro v hv
  have hmemW := memW_congr_memory_ptx hmem
  dsimp only
  rw [hbo, hmemW]
  intro i hlo hhi
  exact stableLogsOK_congr_memory_heap_ptx hmem hdom hhp (hret v hv i hlo hhi)

theorem stableLogsOK_release_marks_ptx {F : Type}
    {s_cur : PanSemStateFiniteExact 64 F}
    {w_mark w_fmark : BitVec 64} {ck logs : Nat}
    (hs : StableLogsOK s_cur logs) :
    StableLogsOK
      { s_cur with
        globals := (s_cur.globals.update (ofString "scratch_ptr", .val (.word w_mark))).update
          (ofString "frame_mem_ptr", .val (.word w_fmark))
        clock := ck }
      logs := by
  refine stableLogsOK_congr_memory_heap_ptx (s := s_cur)
    (post := { s_cur with
      globals := (s_cur.globals.update (ofString "scratch_ptr", .val (.word w_mark))).update
        (ofString "frame_mem_ptr", .val (.word w_fmark))
      clock := ck }) rfl rfl ?_ hs
  have hne1 : ofString "heap_ptr" ≠ ofString "frame_mem_ptr" := by decide
  have hne2 : ofString "heap_ptr" ≠ ofString "scratch_ptr" := by decide
  simp [globN, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne1, Ne.symm hne2]

theorem retTransactionLogs_release_marks_ptx {F : Type}
    {entry s_cur : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    {S Nd : List Nat}
    {w_mark w_fmark : BitVec 64} {ck : Nat}
    (hret : RetTransactionLogs entry r s_cur S Nd) :
    RetTransactionLogs entry r
      { s_cur with
        globals := (s_cur.globals.update (ofString "scratch_ptr", .val (.word w_mark))).update
          (ofString "frame_mem_ptr", .val (.word w_fmark))
        clock := ck }
      S Nd := by
  refine retTransactionLogs_congr_memory_heap_bo_ptx (s := s_cur) rfl rfl ?_ ?_ hret
  · have hne1 : ofString "heap_ptr" ≠ ofString "frame_mem_ptr" := by decide
    have hne2 : ofString "heap_ptr" ≠ ofString "scratch_ptr" := by decide
    simp [globN, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne1, Ne.symm hne2]
  · have hne1 : ofString "bo" ≠ ofString "frame_mem_ptr" := by decide
    have hne2 : ofString "bo" ≠ ofString "scratch_ptr" := by decide
    simp [globN, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne1, Ne.symm hne2]

def PtxRetSlices : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post _ _ => ∀ v, r = some (.returned v) →
    (∀ off ∈ ([24, 32] : List Nat), ∀ i, i < locN s "index" →
      memW post (memW post (globN post "bo" + off) + 16 * i + 8) =
        memW s (memW s (globN s "bo" + off) + 16 * i + 8)) ∧
    (∀ off ∈ ([24, 32] : List Nat),
      memW post (memW post (globN post "bo" + off) + 16 * locN s "index" + 8) < 2 ^ 40)

theorem ptxRetSlices_congr_memory_heap_bo {F : Type}
    {entry s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {S Nd : List Nat} (hmem : post.memory = s.memory)
    (_hdom : post.memaddrs = s.memaddrs)
    (_hhp : globN post "heap_ptr" = globN s "heap_ptr")
    (hbo : globN post "bo" = globN s "bo")
    (h : PtxRetSlices entry r s S Nd) : PtxRetSlices entry r post S Nd := by
  simpa only [PtxRetSlices, hbo, memW_congr_memory_ptx hmem] using h

def ptxPhase5ReleaseReturn : ProgHOL 64 :=
  .dec (ofString "tx_frame_mark") .one
    (.load .one (.op .add [.var .local (ofString "out"), .const 80#64]))
    (.seq
      (.ite (.cmp .notEqual (.var .local (ofString "tx_frame_mark")) (.const 0#64))
        (.seq
          (.call (some (none, none)) (ofString "scratch_release")
            [.var .local (ofString "tx_frame_mark")])
          (.call (some (none, none)) (ofString "frame_mem_release")
            [.load .one (.op .add [.var .local (ofString "out"), .const 88#64])]))
        .skip)
      (.return (.const 0#64)))

theorem ptxPhase5ReleaseReturn_eq_spine :
    ptxPhase5ReleaseReturn = R13Shards.spineAt 3 R13Shards.ptxPhase5 := by
  unfold R13Shards.ptxPhase5 R13Shards.ptxCode
  rfl

theorem evalHOLExact_load_word_in_block_ptx {F : Type}
    {s : PanSemStateFiniteExact 64 F} {w_out : BitVec 64} {off : Nat}
    (hhp : globN s "heap_ptr" ≤ heapLimit)
    (hl_out : s.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hw_out : WordsOK s (w_out.toNat, 96))
    (hin_out : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr"))
    (hoff8 : off % 8 = 0) (hoff_le : off + 8 ≤ 96) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "out"), .const (BitVec.ofNat 64 off)])) =
      some (.val (.word (BitVec.ofNat 64 (memW s (w_out.toNat + off))))) := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hin_bound : w_out.toNat + 96 ≤ 2 ^ 64 := by
    unfold Inside at hin_out; omega
  have hoff_lt : off < 2 ^ 64 := by omega
  have hsum_lt : w_out.toNat + off < 2 ^ 64 := by omega
  have haddr_nat : (w_out + BitVec.ofNat 64 off).toNat = w_out.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_lt, Nat.mod_eq_of_lt hsum_lt]
  have hk_lt : off / 8 < 96 / 8 := by omega
  have hk_eq : w_out.toNat + 8 * (off / 8) = w_out.toNat + off := by omega
  obtain ⟨wc, hdom, hm_eq⟩ := hw_out.2.2 (off / 8) hk_lt
  rw [hk_eq] at hdom hm_eq
  have haddr_eq : BitVec.ofNat 64 (w_out.toNat + off) = w_out + BitVec.ofNat 64 off := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsum_lt, haddr_nat]
  rw [haddr_eq] at hdom hm_eq
  have hmw : BitVec.ofNat 64 (memW s (w_out.toNat + off)) = wc := by
    unfold memW
    rw [haddr_eq, hm_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hmw]
  simp [evalHOLExact, evalListHOLExact, hl_out, valueIsWord, valueWord,
    wordOpHOL, wordOp, isWfShapeExactHOL, memLoadHOLExact, hdom, hm_eq]

def ptxReleasedGlobals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w_out : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  (s.globals.update (ofString "scratch_ptr",
    .val (.word (BitVec.ofNat 64 (memW s (w_out.toNat + 80)))))).update
    (ofString "frame_mem_ptr", .val (.word (BitVec.ofNat 64 (memW s (w_out.toNat + 88)))))

def ptxReleasedState {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w_out : BitVec 64) : PanSemStateFiniteExact 64 F :=
  if memW s (w_out.toNat + 80) = 0 then s else
    { s with globals := ptxReleasedGlobals s w_out }

theorem ptxPhase5_release_return_exact {F : Type}
    {s : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (hcode : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hl_out : s.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hw_out : WordsOK s (w_out.toNat, 96))
    (hin_out : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr"))
    (hres : Resumes (evaluateHOLFiniteState s ptxPhase5ReleaseReturn).1) :
    ∃ L ck, evaluateHOLFiniteState s ptxPhase5ReleaseReturn =
      (some (.returned (.val (.word 0#64))),
        { ptxReleasedState s w_out with locals := L, clock := ck }) := by
  have h80 := evalHOLExact_load_word_in_block_ptx hA.2.2.1 hl_out hw_out hin_out
    (off := 80) (by decide) (by decide)
  obtain ⟨v, hv, hr, heqr, heqp⟩ := dec_word_resumes_step hres
  rw [h80] at hv
  injection hv with hv
  subst v
  let wm := BitVec.ofNat 64 (memW s (w_out.toNat + 80))
  let wf := BitVec.ofNat 64 (memW s (w_out.toNat + 88))
  let st := setVarHOLFinite (ofString "tx_frame_mark") (.val (.word wm)) s
  have hmark : st.locals.lookup (ofString "tx_frame_mark") = some (.val (.word wm)) := by
    simp [st, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hout : st.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
    simp [st, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "tx_frame_mark" ≠ ofString "out" by decide, hl_out]
  have hcond : @evalHOLExact 64 F _ st.toExact
      (fun a => Classical.propDecidable (st.memaddrs a))
      (.cmp .notEqual (.var .local (ofString "tx_frame_mark")) (.const 0#64)) =
      some (.val (.word (if wm = 0#64 then 0#64 else 1#64))) := by
    simp [evalHOLExact, hmark, Compiler.Encoders.Asm.wordCmpHOL]
  have hwm_nat : wm.toNat = memW s (w_out.toNat + 80) := by
    have hb : memW s (w_out.toNat + 80) < 2 ^ 64 := by
      unfold memW; cases s.memory _ with | word w => exact w.isLt
    exact Nat.mod_eq_of_lt hb
  have hziff : wm = 0#64 ↔ memW s (w_out.toNat + 80) = 0 := by
    constructor
    · intro h; simpa [h] using hwm_nat.symm
    · intro h; apply BitVec.eq_of_toNat_eq; simpa [h] using hwm_nat
  change Resumes (evaluateHOLFiniteState st _).1 at hr
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond] at hr
  have hbody : ∃ L ck, evaluateHOLFiniteState st
      (.seq
        (.ite (.cmp .notEqual (.var .local (ofString "tx_frame_mark")) (.const 0#64))
          (.seq (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "tx_frame_mark")])
            (.call (some (none, none)) (ofString "frame_mem_release")
              [.load .one (.op .add [.var .local (ofString "out"), .const 88#64])])) .skip)
        (.return (.const 0#64))) =
      (some (.returned (.val (.word 0#64))),
        { ptxReleasedState s w_out with locals := L, clock := ck }) := by
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond]
    by_cases hz : wm = 0#64
    · rw [if_pos hz]
      simp only [show (0#64 : BitVec 64) = 0 from rfl, ↓reduceIte, evaluateHOLFiniteState_skip]
      rw [evaluateHOLFiniteState_return]
      simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL,
        show (1 : Nat) ≤ 32 by decide, ↓reduceIte]
      refine ⟨(emptyLocalsHOLFinite st).locals, s.clock, ?_⟩
      simp [ptxReleasedState, hziff.mp hz, st, setVarHOLFinite, emptyLocalsHOLFinite]
    · rw [if_neg hz] at hr ⊢
      simp only [show (1#64 : BitVec 64) ≠ 0 by decide, ↓reduceIte] at hr ⊢
      let calls : ProgHOL 64 :=
        .seq (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "tx_frame_mark")])
          (.call (some (none, none)) (ofString "frame_mem_release")
            [.load .one (.op .add [.var .local (ofString "out"), .const 88#64])])
      have hnt : (evaluateHOLFiniteState st calls).1 ≠ some .timeOut := by
        intro ht
        rcases he : evaluateHOLFiniteState st calls with ⟨r, post⟩
        rw [he] at ht
        dsimp only at ht
        subst r
        dsimp only [calls] at he
        rw [he] at hr
        rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      obtain ⟨ck, hc⟩ := ptx_release_calls_exact st
        (.var .local (ofString "tx_frame_mark"))
        (.load .one (.op .add [.var .local (ofString "out"), .const 88#64]))
        wm wf hcode (localsFree_arenaReady s st.locals s.clock hA)
        (by simp [evalHOLExact, hmark]) (fun ck => by
          let st1 : PanSemStateFiniteExact 64 F :=
            { st with
              globals := st.globals.update (ofString "scratch_ptr", .val (.word wm))
              clock := ck }
          have hhp_st1 : globN st1 "heap_ptr" = globN s "heap_ptr" := by
            simp [st1, st, setVarHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "scratch_ptr" ≠ ofString "heap_ptr" by decide]
          exact evalHOLExact_load_word_in_block_ptx (s := st1) (hhp_st1 ▸ hA.2.2.1) hout hw_out
            (hhp_st1 ▸ hin_out) (off := 88) (by decide) (by decide)) hnt
      rw [hc]
      simp only
      rw [evaluateHOLFiniteState_return]
      simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL,
        show (1 : Nat) ≤ 32 by decide, ↓reduceIte]
      refine ⟨(emptyLocalsHOLFinite st).locals, ck, ?_⟩
      have hnz : memW s (w_out.toNat + 80) ≠ 0 := fun h => hz (hziff.mpr h)
      rw [show ptxReleasedState s w_out = { s with globals := ptxReleasedGlobals s w_out } from by
        unfold ptxReleasedState; exact if_neg hnz]
      simp [ptxReleasedGlobals, st, setVarHOLFinite, emptyLocalsHOLFinite, wm, wf]
  obtain ⟨L, ck, hb⟩ := hbody
  refine ⟨HolFiniteMapExact.resVarEq L (ofString "tx_frame_mark", s.locals.lookup (ofString "tx_frame_mark")), ck, ?_⟩
  unfold ptxPhase5ReleaseReturn
  dsimp only [st, wm] at hb
  apply Prod.ext
  · rw [heqr, hb]
  · rw [heqp, hb]

theorem ptxPhase5_release_return_worldStep {F : Type}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {entry s_pmc s_cur : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (hQ_congr : ∀ {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat},
      post.memory = s.memory → post.memaddrs = s.memaddrs →
      globN post "heap_ptr" = globN s "heap_ptr" →
      globN post "bo" = globN s "bo" →
      Q entry (some (.returned (.val (.word 0#64)))) s S Nd →
      Q entry (some (.returned (.val (.word 0#64)))) post S Nd)
    (hcode : s_cur.code = originalRuntimeCode)
    (hA_pmc : ArenaReady s_pmc)
    (hA_cur : ArenaReady s_cur)
    (hhp_entry : globN entry "heap_ptr" ≤ globN s_cur "heap_ptr")
    (hhp_pmc : globN s_pmc "heap_ptr" ≤ globN s_cur "heap_ptr")
    (hG_cur : GlobalsKept ptxGlobals entry s_cur)
    (hK_cur : RecordsKept ptxRegions ptxKeep entry s_cur)
    (hl_out : s_cur.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hw_out : WordsOK s_cur (w_out.toNat, 96))
    (hin_out : Inside (w_out.toNat, 96) sourceBase (globN s_cur "heap_ptr"))
    (hmarks : memW s_cur (w_out.toNat + 80) ≠ 0 →
      memW s_cur (w_out.toNat + 80) % 8 = 0 ∧
      memW s_cur (w_out.toNat + 88) % 8 = 0 ∧
      globN s_pmc "frame_mem_ptr" ≤ memW s_cur (w_out.toNat + 88) ∧
      memW s_cur (w_out.toNat + 88) ≤ memW s_cur (w_out.toNat + 80) ∧
      memW s_cur (w_out.toNat + 80) ≤ globN s_pmc "scratch_ptr")
    (hW : ∀ S0 Nd0, WorldTypedWith entry S0 Nd0 →
      IvlsDisj (ptxRegions entry) (worldTypedIvls entry S0 Nd0) →
      ∃ S_pmc Nd_pmc S_cur Nd_cur,
        WorldTypedWith s_pmc S_pmc Nd_pmc ∧
        (∀ t ∈ S0, t ∈ S_cur) ∧
        WorldTypedWith s_cur S_cur Nd_cur ∧
        OwnedGrows s_pmc s_cur (worldOwned s_pmc S_pmc Nd_pmc) (worldOwned s_cur S_cur Nd_cur) ∧
        OwnedGrows entry s_cur (worldOwned entry S0 Nd0) (worldOwned s_cur S_cur Nd_cur) ∧
        FrameOutside entry s_cur (worldOwned entry S0 Nd0 ++ ptxRegions entry ++ [freeGap entry]) (heapFree entry) ∧
        Q entry (some (.returned (.val (.word 0#64)))) s_cur S_cur Nd_cur)
    (hres : Resumes (evaluateHOLFiniteState s_cur ptxPhase5ReleaseReturn).1) :
    WorldStep ptxRegions ptxGlobals ptxKeep Q entry
      (evaluateHOLFiniteState s_cur ptxPhase5ReleaseReturn).1
      (evaluateHOLFiniteState s_cur ptxPhase5ReleaseReturn).2 := by
  obtain ⟨L, ck, hev⟩ := ptxPhase5_release_return_exact hcode hA_cur hl_out hw_out hin_out hres
  rw [hev]
  dsimp only
  let s_rel := ptxReleasedState s_cur w_out
  let post : PanSemStateFiniteExact 64 F := { s_rel with locals := L, clock := ck }
  have hmem : post.memory = s_cur.memory := by
    by_cases hz : memW s_cur (w_out.toNat + 80) = 0 <;> simp [post, s_rel, ptxReleasedState, hz]
  have hdom : post.memaddrs = s_cur.memaddrs := by
    by_cases hz : memW s_cur (w_out.toNat + 80) = 0 <;> simp [post, s_rel, ptxReleasedState, hz]
  have hg_ne : ∀ nm : String,
      ofString nm ≠ ofString "frame_mem_ptr" →
      ofString nm ≠ ofString "scratch_ptr" →
      globN post nm = globN s_cur nm := by
    intro nm h1 h2
    by_cases hz : memW s_cur (w_out.toNat + 80) = 0
    · simp [post, s_rel, ptxReleasedState, hz, globN]
    · simp [post, s_rel, ptxReleasedState, ptxReleasedGlobals, hz, globN,
        HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h1, Ne.symm h2]
  have hhp_eq : globN post "heap_ptr" = globN s_cur "heap_ptr" :=
    hg_ne "heap_ptr" (by decide) (by decide)
  have hbo_eq : globN post "bo" = globN s_cur "bo" :=
    hg_ne "bo" (by decide) (by decide)
  have hG_post : GlobalsKept ptxGlobals entry post := by
    intro k hk
    have hk_cur := hG_cur k hk
    by_cases hz : memW s_cur (w_out.toNat + 80) = 0
    · simpa [post, s_rel, ptxReleasedState, hz] using hk_cur
    · have hkf : k ≠ ofString "frame_mem_ptr" := fun h => hk (by subst h; decide)
      have hks : k ≠ ofString "scratch_ptr" := fun h => hk (by subst h; decide)
      simpa [post, s_rel, ptxReleasedState, ptxReleasedGlobals, hz,
        HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hkf, Ne.symm hks] using hk_cur
  have hK_post : RecordsKept ptxRegions ptxKeep entry post := by
    intro r hr hnz k hk hno
    rw [memW_congr_memory_ptx hmem]
    exact hK_cur r hr hnz k hk hno
  have hA_post : ArenaReady post := by
    by_cases hz : memW s_cur (w_out.toNat + 80) = 0
    · simpa [post, s_rel, ptxReleasedState, hz] using localsFree_arenaReady s_cur L ck hA_cur
    · obtain ⟨hm80_al, hm88_al, hfmp_le, h88_le_80, h80_le_sp⟩ := hmarks hz
      let wm := BitVec.ofNat 64 (memW s_cur (w_out.toNat + 80))
      let wf := BitVec.ofNat 64 (memW s_cur (w_out.toNat + 88))
      have hwm_nat : wm.toNat = memW s_cur (w_out.toNat + 80) :=
        Nat.mod_eq_of_lt (by unfold memW; cases s_cur.memory _ with | word w => exact w.isLt)
      have hwf_nat : wf.toNat = memW s_cur (w_out.toNat + 88) :=
        Nat.mod_eq_of_lt (by unfold memW; cases s_cur.memory _ with | word w => exact w.isLt)
      have hgi : GuestInv post :=
        guestInv_congr (s := s_cur) (by simp [post, s_rel, ptxReleasedState, hz])
          hdom (by simp [post, s_rel, ptxReleasedState, hz])
          (by simp [post, s_rel, ptxReleasedState, hz]) hA_cur.1
      have hgw1 : GlobalsWord { s_cur with globals := s_cur.globals.update (ofString "scratch_ptr", .val (.word wm)) } :=
        globalsWord_update (ofString "scratch_ptr") wm rfl hA_cur.2.2.2.2.2.2.2.2.2
      have hgw2 : GlobalsWord s_rel := by
        simp only [s_rel, ptxReleasedState, ptxReleasedGlobals, hz, ↓reduceIte]
        exact globalsWord_update (ofString "frame_mem_ptr") wf rfl hgw1
      have hgw_post : GlobalsWord post := fun g hg => hgw2 g hg
      have hfmp_post : globN post "frame_mem_ptr" = wf.toNat := by
        simp [post, s_rel, ptxReleasedState, ptxReleasedGlobals, hz, globN,
          HolFiniteMapExact.lookup_update, FUPDATE, wf]
      have hsp_post : globN post "scratch_ptr" = wm.toNat := by
        have hne : ofString "scratch_ptr" ≠ ofString "frame_mem_ptr" := by decide
        simp [post, s_rel, ptxReleasedState, ptxReleasedGlobals, hz, globN,
          HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne, wm]
      refine ⟨hgi, ?_⟩
      unfold ArenaOK
      rw [hhp_eq, hfmp_post, hsp_post, hwm_nat, hwf_nat]
      exact ⟨hA_cur.2.1, hA_cur.2.2.1, le_trans hA_pmc.2.2.2.1 hfmp_le, h88_le_80,
        le_trans h80_le_sp hA_pmc.2.2.2.2.2.1, hA_cur.2.2.2.2.2.2.1, hm88_al, hm80_al, hgw_post⟩
  refine ⟨hA_post, hhp_eq ▸ hhp_entry, hG_post, hK_post, fun S0 Nd0 hWT0 hD0 => ?_⟩
  obtain ⟨S_pmc, Nd_pmc, S_cur, Nd_cur, hWT_pmc, hsub, hWT_cur, hOG_pmc, hOG_entry, hFO_entry, hQ_cur⟩ :=
    hW S0 Nd0 hWT0 hD0
  have hFO_post : FrameOutside entry post
      (worldOwned entry S0 Nd0 ++ ptxRegions entry ++ [freeGap entry]) (heapFree entry) := by
    intro a ha hhf
    rw [hmem]
    exact hFO_entry a ha hhf
  have hQ_post : Q entry (some (.returned (.val (.word 0#64)))) post S_cur Nd_cur :=
    hQ_congr hmem hdom hhp_eq hbo_eq hQ_cur
  by_cases hz : memW s_cur (w_out.toNat + 80) = 0
  · have hpost_eq : post = { s_cur with locals := L, clock := ck } := by
      simp [post, s_rel, ptxReleasedState, hz]
    have hWT_post : WorldTypedWith post S_cur Nd_cur := by
      rw [hpost_eq]
      exact (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals s_cur L ck S_cur Nd_cur).2 hWT_cur
    have hwo_post : worldOwned post S_cur Nd_cur = worldOwned s_cur S_cur Nd_cur := by
      rw [hpost_eq]
      rfl
    have hOG_post : OwnedGrows entry post (worldOwned entry S0 Nd0) (worldOwned post S_cur Nd_cur) := by
      rw [hwo_post]
      intro o ho
      simpa [hhp_eq] using hOG_entry o ho
    exact ⟨S_cur, Nd_cur, hsub, hWT_post, hOG_post, hFO_post, hQ_post⟩
  · obtain ⟨hm80_al, hm88_al, hfmp_le, h88_le_80, h80_le_sp⟩ := hmarks hz
    let wm := BitVec.ofNat 64 (memW s_cur (w_out.toNat + 80))
    let wf := BitVec.ofNat 64 (memW s_cur (w_out.toNat + 88))
    have hwm_nat : wm.toNat = memW s_cur (w_out.toNat + 80) :=
      Nat.mod_eq_of_lt (by unfold memW; cases s_cur.memory _ with | word w => exact w.isLt)
    have hwf_nat : wf.toNat = memW s_cur (w_out.toNat + 88) :=
      Nat.mod_eq_of_lt (by unfold memW; cases s_cur.memory _ with | word w => exact w.isLt)
    obtain ⟨_, hWT_rel0, hwo_rel0⟩ := worldTypedWith_release_marks_ptx
      (w_mark := wm) (w_fmark := wf) (ck := ck)
      hA_pmc hA_cur hWT_pmc hWT_cur hOG_pmc hhp_pmc
      (hwm_nat ▸ hm80_al) (hwf_nat ▸ hm88_al) (hwf_nat ▸ hfmp_le)
      (by rw [hwf_nat, hwm_nat]; exact h88_le_80) (hwm_nat ▸ h80_le_sp)
    let s_rel0 : PanSemStateFiniteExact 64 F :=
      { s_cur with
        globals := (s_cur.globals.update (ofString "scratch_ptr", .val (.word wm))).update
          (ofString "frame_mem_ptr", .val (.word wf))
        clock := ck }
    have hpost_eq : post = { s_rel0 with locals := L, clock := ck } := by
      simp [post, s_rel, s_rel0, ptxReleasedState, ptxReleasedGlobals, hz, wm, wf]
    have hWT_post : WorldTypedWith post S_cur Nd_cur := by
      rw [hpost_eq]
      exact (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals s_rel0 L ck S_cur Nd_cur).2 hWT_rel0
    have hwo_post : worldOwned post S_cur Nd_cur = worldOwned s_cur S_cur Nd_cur := by
      rw [hpost_eq]
      exact hwo_rel0
    have hOG_post : OwnedGrows entry post (worldOwned entry S0 Nd0) (worldOwned post S_cur Nd_cur) := by
      rw [hwo_post]
      intro o ho
      simpa [hhp_eq] using hOG_entry o ho
    exact ⟨S_cur, Nd_cur, hsub, hWT_post, hOG_post, hFO_post, hQ_post⟩

theorem ptxPhase5_tail_relRun {F : Type}
    {entry s_pmc s_cur : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (hcode : s_cur.code = originalRuntimeCode)
    (hA_pmc : ArenaReady s_pmc)
    (hA_cur : ArenaReady s_cur)
    (hhp_entry : globN entry "heap_ptr" ≤ globN s_cur "heap_ptr")
    (hhp_pmc : globN s_pmc "heap_ptr" ≤ globN s_cur "heap_ptr")
    (hG_cur : GlobalsKept ptxGlobals entry s_cur)
    (hK_cur : RecordsKept ptxRegions ptxKeep entry s_cur)
    (hl_out : s_cur.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hw_out : WordsOK s_cur (w_out.toNat, 96))
    (hin_out : Inside (w_out.toNat, 96) sourceBase (globN s_cur "heap_ptr"))
    (hmarks : memW s_cur (w_out.toNat + 80) ≠ 0 →
      memW s_cur (w_out.toNat + 80) % 8 = 0 ∧
      memW s_cur (w_out.toNat + 88) % 8 = 0 ∧
      globN s_pmc "frame_mem_ptr" ≤ memW s_cur (w_out.toNat + 88) ∧
      memW s_cur (w_out.toNat + 88) ≤ memW s_cur (w_out.toNat + 80) ∧
      memW s_cur (w_out.toNat + 80) ≤ globN s_pmc "scratch_ptr")
    (hW : ∀ S0 Nd0, WorldTypedWith entry S0 Nd0 →
      IvlsDisj (ptxRegions entry) (worldTypedIvls entry S0 Nd0) →
      ∃ S_pmc Nd_pmc S_cur Nd_cur,
        WorldTypedWith s_pmc S_pmc Nd_pmc ∧
        (∀ t ∈ S0, t ∈ S_cur) ∧
        WorldTypedWith s_cur S_cur Nd_cur ∧
        OwnedGrows s_pmc s_cur (worldOwned s_pmc S_pmc Nd_pmc) (worldOwned s_cur S_cur Nd_cur) ∧
        OwnedGrows entry s_cur (worldOwned entry S0 Nd0) (worldOwned s_cur S_cur Nd_cur) ∧
        FrameOutside entry s_cur (worldOwned entry S0 Nd0 ++ ptxRegions entry ++ [freeGap entry]) (heapFree entry) ∧
        RetTransactionLogs entry (some (.returned (.val (.word 0#64)))) s_cur S_cur Nd_cur) :
    PtxRelRun entry ptxPhase5ReleaseReturn s_cur :=
  ptxPhase5_release_return_worldStep
    (fun hmem hdom hhp hbo hret => retTransactionLogs_congr_memory_heap_bo_ptx hmem hdom hhp hbo hret)
    hcode hA_pmc hA_cur hhp_entry hhp_pmc hG_cur hK_cur hl_out hw_out hin_out hmarks hW

theorem ptxPhase5_release_return_logs_slices_worldStep {F : Type}
    {entry s_pmc s_cur : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (hcode : s_cur.code = originalRuntimeCode)
    (hA_pmc : ArenaReady s_pmc)
    (hA_cur : ArenaReady s_cur)
    (hhp_entry : globN entry "heap_ptr" ≤ globN s_cur "heap_ptr")
    (hhp_pmc : globN s_pmc "heap_ptr" ≤ globN s_cur "heap_ptr")
    (hG_cur : GlobalsKept ptxGlobals entry s_cur)
    (hK_cur : RecordsKept ptxRegions ptxKeep entry s_cur)
    (hl_out : s_cur.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hw_out : WordsOK s_cur (w_out.toNat, 96))
    (hin_out : Inside (w_out.toNat, 96) sourceBase (globN s_cur "heap_ptr"))
    (hmarks : memW s_cur (w_out.toNat + 80) ≠ 0 →
      memW s_cur (w_out.toNat + 80) % 8 = 0 ∧
      memW s_cur (w_out.toNat + 88) % 8 = 0 ∧
      globN s_pmc "frame_mem_ptr" ≤ memW s_cur (w_out.toNat + 88) ∧
      memW s_cur (w_out.toNat + 88) ≤ memW s_cur (w_out.toNat + 80) ∧
      memW s_cur (w_out.toNat + 80) ≤ globN s_pmc "scratch_ptr")
    (hW : ∀ S0 Nd0, WorldTypedWith entry S0 Nd0 →
      IvlsDisj (ptxRegions entry) (worldTypedIvls entry S0 Nd0) →
      ∃ S_pmc Nd_pmc S_cur Nd_cur,
        WorldTypedWith s_pmc S_pmc Nd_pmc ∧
        (∀ t ∈ S0, t ∈ S_cur) ∧
        WorldTypedWith s_cur S_cur Nd_cur ∧
        OwnedGrows s_pmc s_cur (worldOwned s_pmc S_pmc Nd_pmc) (worldOwned s_cur S_cur Nd_cur) ∧
        OwnedGrows entry s_cur (worldOwned entry S0 Nd0) (worldOwned s_cur S_cur Nd_cur) ∧
        FrameOutside entry s_cur (worldOwned entry S0 Nd0 ++ ptxRegions entry ++ [freeGap entry]) (heapFree entry) ∧
        (RetTransactionLogs entry (some (.returned (.val (.word 0#64)))) s_cur S_cur Nd_cur ∧
          PtxRetSlices entry (some (.returned (.val (.word 0#64)))) s_cur S_cur Nd_cur))
    (hres : Resumes (evaluateHOLFiniteState s_cur ptxPhase5ReleaseReturn).1) :
    WorldStep ptxRegions ptxGlobals ptxKeep
      (fun e r p S Nd => RetTransactionLogs e r p S Nd ∧ PtxRetSlices e r p S Nd)
      entry (evaluateHOLFiniteState s_cur ptxPhase5ReleaseReturn).1
      (evaluateHOLFiniteState s_cur ptxPhase5ReleaseReturn).2 :=
  ptxPhase5_release_return_worldStep
    (fun hmem hdom hhp hbo h =>
      ⟨retTransactionLogs_congr_memory_heap_bo_ptx hmem hdom hhp hbo h.1,
        ptxRetSlices_congr_memory_heap_bo hmem hdom hhp hbo h.2⟩)
    hcode hA_pmc hA_cur hhp_entry hhp_pmc hG_cur hK_cur hl_out hw_out hin_out hmarks hW hres

def PtxBlockOutUnhit {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ i ∈ blockOutObjects s, R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post i

theorem ptxBlockOutUnhit_refl {F : Type} (s : PanSemStateFiniteExact 64 F) :
    PtxBlockOutUnhit s s := by
  intro i hi a ha hh
  rfl

theorem ptxBlockOutUnhit_trans {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hsm : PtxBlockOutUnhit s mid) (hmp : PtxBlockOutUnhit mid post)
    (heq : blockOutObjects mid = blockOutObjects s) :
    PtxBlockOutUnhit s post := by
  intro i hi a ha hh
  exact (hmp i (heq.symm ▸ hi) a ha hh).trans (hsm i hi a ha hh)

private theorem blockOut_len_zero {F : Type}
    {s : PanSemStateFiniteExact 64 F} {i : Ivl}
    (hi : i ∈ blockOutObjects s) (hz : i.2 = 0) : i = (0, 0) := by
  unfold blockOutObjects at hi
  dsimp only at hi
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  have hobj : ∀ p len,
      (if globN s "bo" = 0 ∨ p = 0 ∨ len = 0 then (0, 0) else (p, len)).2 = 0 →
      (if globN s "bo" = 0 ∨ p = 0 ∨ len = 0 then (0, 0) else (p, len)) = (0, 0) := by
    intro p len hlen
    by_cases h : globN s "bo" = 0 ∨ p = 0 ∨ len = 0
    · simp [h]
    · simp [h] at hlen
      omega
  rcases hi with ((rfl | rfl | rfl) | hi40) | hi72
  · exact hobj _ _ hz
  · exact hobj _ _ hz
  · exact hobj _ _ hz
  · by_cases h40 : globN s "bo" = 0 ∨ memW s (globN s "bo" + 40) = 0
    · simp [h40] at hi40
      exact hi40
    · simp [h40] at hi40
      rcases hi40 with rfl | rfl
      · omega
      · by_cases hd : memW s (memW s (globN s "bo" + 40)) = 0 ∨
            memW s (memW s (globN s "bo" + 40) + 16) = 0
        · simp [hd]
        · push Not at h40 hd
          simp [h40.1, hd.1, hd.2] at hz
  · by_cases h72 : globN s "bo" = 0 ∨ memW s (globN s "bo" + 72) = 0
    · simp [h72] at hi72
      exact hi72
    · simp [h72] at hi72
      rcases hi72 with rfl | rfl
      · omega
      · by_cases hd : memW s (memW s (globN s "bo" + 72)) = 0 ∨
            memW s (memW s (globN s "bo" + 72) + 16) = 0
        · simp [hd]
        · push Not at h72 hd
          simp [h72.1, hd.1, hd.2] at hz

theorem ptxBlockOutUnhit_of_worldEff {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {R : List Ivl} {B : List (String × Nat)} {gw : List String}
    {S Nd : List Nat}
    (h : WorldEff s post R B gw)
    (hA : ArenaReady s) (hWT : WorldTypedWith s S Nd)
    (hR : ∀ j ∈ R, ∀ i ∈ blockOutObjects s, Disj i j)
    (hB : ∀ b ∈ B, ∀ i ∈ blockOutObjects s, Disj i (bufferRegion s b)) :
    PtxBlockOutUnhit s post := by
  intro i hi a ha hh
  have hfix : i ∈ fixedObjects s := by
    unfold fixedObjects
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hi)))
  rcases hWT.2.2.1.1 i hfix with hz | ⟨hal, hw⟩
  · rw [blockOut_len_zero hi hz] at hh
    exact absurd hh (R10Shards.Fast_GbodyC17ToC21.not_cellHits_zero a.toNat)
  · by_contra hmem
    have ha1 := hw.1
    have ha2 := hw.2.1
    have hh' : i.1 ≤ a.toNat ∧ a.toNat + 8 ≤ i.1 + i.2 := by
      unfold CellHits at hh
      omega
    have exclude :
        ∀ j, Disj i j → ¬ Fast_C08WkShard03.CellHitsPos a.toNat j := by
      intro j hd hc
      unfold Disj at hd
      simp only [Fast_C08WkShard03.CellHitsPos, CellHits] at hc
      rcases hd with hz | hz | hl | hr <;> omega
    rcases h.cell_frame _ hmem with ⟨j, hj, hc⟩ | ⟨b, hb, hc⟩ | hc | hc
    · exact exclude j (hR j hj i hi) hc
    · exact exclude _ (hB b hb i hi) hc
    · apply exclude _ _ hc
      unfold Allocated Inside at hal
      unfold Disj freeGap
      rcases hal with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
      · exact Or.inr (Or.inr (Or.inl (by
          rcases hA.2 with ⟨_, hp, hf, hsc, _⟩
          have sep : heapLimit ≤ InitE.scratchStart := by decide
          dsimp only
          omega)))
      · exact Or.inr (Or.inr (Or.inr (by
          rcases hA.2 with ⟨_, hp, hf, hsc, _⟩
          dsimp only
          omega)))
    · apply exclude _ _ hc
      unfold Allocated Inside at hal
      unfold Disj heapFree
      rcases hal with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
      · exact Or.inr (Or.inr (Or.inl hhi))
      · exact Or.inr (Or.inr (Or.inr (by
          rcases hA.2 with ⟨_, hp, hf, hsc, _⟩
          have sep : heapLimit ≤ InitE.scratchStart := by decide
          dsimp only
          omega)))

theorem blockOutObjects_eq_of_ptxBlockOutUnhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hA : ArenaReady s) (hWT : WorldTypedWith s S Nd)
    (hbo : globN post "bo" = globN s "bo")
    (hfields : ∀ off ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      globN s "bo" ≠ 0 →
      memW post (globN s "bo" + off) = memW s (globN s "bo" + off))
    (hu : PtxBlockOutUnhit s post) :
    blockOutObjects post = blockOutObjects s := by
  exact (R10Shards.Fast_GbodyC17ToC21.blockOutObjects_eq_of_bo_unhit
    hA.2 hWT.2.2.1 hbo hWT.1.2.2.2.2.2.2.2.2.2.2.1
    (hfields 24 (by simp)) (hfields 32 (by simp))
    (hfields 40 (by simp)) (hfields 56 (by simp))
    (hfields 72 (by simp)) (hfields 80 (by simp))
    (fun hb hl => hu _ (by simp [blockOutObjects, hb, hl]))
    (fun hb hl => hu _ (by simp [blockOutObjects, hb, hl]))).1

theorem memW_eq_of_ptxBlockOutUnhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {p len off : Nat}
    (hA : ArenaReady s) (hWT : WorldTypedWith s S Nd)
    (hu : PtxBlockOutUnhit s post) (hi : (p, len) ∈ blockOutObjects s)
    (hoff8 : off % 8 = 0) (hbound : off + 8 ≤ len) :
    memW post (p + off) = memW s (p + off) := by
  have hfix : (p, len) ∈ fixedObjects s := by
    unfold fixedObjects
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hi)))
  rcases hWT.2.2.1.1 _ hfix with hz | ⟨hal, hw⟩
  · dsimp at hz
    omega
  · have hp8 : p % 8 = 0 := hw.1
    exact R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit (hu _ hi)
      (by omega) (R10Shards.Fast_GbodyC17ToC21.ivl_allocated_bound hA.2 hal).2
      ⟨by omega, by dsimp; omega⟩

theorem ptx_slice_length_eq_of_blockOutUnhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {off i : Nat}
    (hA : ArenaReady s) (hWT : WorldTypedWith s S Nd)
    (hu : PtxBlockOutUnhit s post) (hbo : globN s "bo" ≠ 0)
    (hoff : off ∈ ([24, 32] : List Nat))
    (hp : memW s (globN s "bo" + off) ≠ 0)
    (hi : i ≤ memW s (globN s "bo" + 80)) :
    memW post (memW s (globN s "bo" + off) + 16 * i + 8) =
      memW s (memW s (globN s "bo" + off) + 16 * i + 8) := by
  have hm : (memW s (globN s "bo" + off), 16 * memW s (globN s "bo" + 80) + 16) ∈
      blockOutObjects s := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl <;> simp [blockOutObjects, hbo, hp]
  simpa only [Nat.add_assoc] using memW_eq_of_ptxBlockOutUnhit hA hWT hu hm
    (off := 16 * i + 8) (by omega) (by omega)

theorem ptx_receipt_header_eq_of_blockOutUnhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {off : Nat}
    (hA : ArenaReady s) (hWT : WorldTypedWith s S Nd)
    (hu : PtxBlockOutUnhit s post) (hbo : globN s "bo" ≠ 0)
    (hl : memW s (globN s "bo" + 72) ≠ 0)
    (hoff : off ∈ ([0, 8, 16] : List Nat)) :
    memW post (memW s (globN s "bo" + 72) + off) =
      memW s (memW s (globN s "bo" + 72) + off) := by
  have hm : (memW s (globN s "bo" + 72), 24) ∈ blockOutObjects s := by
    simp [blockOutObjects, hbo, hl]
  apply memW_eq_of_ptxBlockOutUnhit hA hWT hu hm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl <;> decide

theorem ptx_receipt_element_eq_of_blockOutUnhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {i : Nat}
    (hA : ArenaReady s) (hWT : WorldTypedWith s S Nd)
    (hu : PtxBlockOutUnhit s post) (hbo : globN s "bo" ≠ 0)
    (hl : memW s (globN s "bo" + 72) ≠ 0)
    (hp : memW s (memW s (globN s "bo" + 72)) ≠ 0)
    (hL : LstOK s (memW s (globN s "bo" + 72)))
    (hi : i < memW s (memW s (globN s "bo" + 72) + 16)) :
    memW post (memW s (memW s (globN s "bo" + 72)) + 8 * i) =
      memW s (memW s (memW s (globN s "bo" + 72)) + 8 * i) := by
  have hcap : 8 * memW s (memW s (globN s "bo" + 72) + 16) ≠ 0 := by
    have := hL.1
    omega
  have hm : (memW s (memW s (globN s "bo" + 72)),
      8 * memW s (memW s (globN s "bo" + 72) + 16)) ∈ blockOutObjects s := by
    simp [blockOutObjects, hbo, hl, hp, hcap]
  exact memW_eq_of_ptxBlockOutUnhit hA hWT hu hm (by omega) (by omega)

def StableLogsHeapDisj {F : Type} (s : PanSemStateFiniteExact 64 F)
    (owned : List Ivl) (logs : Nat) : Prop :=
  StableLogsOK s logs ∧ (logs ≠ 0 →
    (∀ o ∈ owned, Disj (logs, 24) o) ∧
    (∀ o ∈ owned, Disj (memW s logs, 8 * memW s (logs + 16)) o) ∧
    ∀ i, i < memW s (logs + 8) →
      (∀ o ∈ owned, Disj (memW s (memW s logs + 8 * i), 40) o) ∧
      IvlsDisj (logOwnedIvls s (memW s (memW s logs + 8 * i))) owned)

theorem stableLogsHeapDisj_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {old new R : List Ivl} {logs : Nat}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hold0 : ∀ j ∈ old, j.2 = 0 → j.1 % 8 = 0)
    (hR0 : ∀ j ∈ R, j.2 = 0 → j.1 % 8 = 0)
    (hog : OwnedGrows s post old new)
    (hfr : FrameOutside s post (old ++ R ++ [freeGap s]) (heapFree s))
    (hsys : globN post "vm_system_address" = globN s "vm_system_address")
    (h : StableLogsHeapDisj s old logs)
    (hR : logs ≠ 0 →
      (∀ o ∈ R, Disj (logs, 24) o) ∧
      (∀ o ∈ R, Disj (memW s logs, 8 * memW s (logs + 16)) o) ∧
      ∀ i, i < memW s (logs + 8) →
        ∀ o ∈ R, Disj (memW s (memW s logs + 8 * i), 40) o) :
    StableLogsHeapDisj post new logs := by
  by_cases hz : logs = 0
  · subst logs
    exact ⟨⟨Or.inl rfl, Or.inl rfl⟩, fun hn => (hn rfl).elim⟩
  obtain ⟨hstable, hd⟩ := h
  obtain ⟨hh, ha, he⟩ := hd hz
  obtain ⟨hrh, hra, hre⟩ := hR hz
  have hl : LogsListOK s logs := hstable.1
  rcases hl with hzero | hl
  · exact (hz hzero).elim
  have hheap := hstable.2.resolve_left hz
  have hhdr := R13Shards.heap_ivl_survives_step hAs.2 hhp hold0 hR0 hog hfr
    hl.1.1 (by decide : 24 % 8 = 0) hheap.1 hh hrh
  have hm : ∀ k ∈ ([0, 8, 16] : List Nat),
      memW post (logs + k) = memW s (logs + k) := by
    intro k hk
    have hlogs8 := hl.1.1
    apply R13Shards.memW_eq_of_ivlUnhit hhdr.2.2
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> omega
    · exact (R13Shards.ivl_allocated_bound hAs.2 (Or.inl hheap.1)).2
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> (constructor <;> omega)
  have hm0 : memW post logs = memW s logs := by simpa using hm 0 (by simp)
  have hm8 := hm 8 (by simp)
  have hm16 := hm 16 (by simp)
  have harr_in : Inside (memW s logs, 8 * memW s (logs + 16)) sourceBase (globN post "heap_ptr") :=
    ⟨hheap.2.1, Nat.le_trans hheap.2.2 hhp⟩
  have harr_disj : ∀ o ∈ new, Disj (memW s logs, 8 * memW s (logs + 16)) o :=
    PtxP34.allocated_disj_ownedGrows hAs.2 hAp.2 (Or.inl hheap.2) hog ha
  have hp : ∀ i, i < memW s (logs + 8) →
      memW post (memW s logs + 8 * i) = memW s (memW s logs + 8 * i) := by
    intro i hi
    have hlen_pos : 0 < memW s (logs + 8) := by omega
    have harr8 := PtxP34.logsListOK_array_aligned hAs.1 (Or.inr hl) hz hlen_pos
    have harr := R13Shards.heap_ivl_survives_step hAs.2 hhp hold0 hR0 hog hfr
      harr8 (by omega : (8 * memW s (logs + 16)) % 8 = 0) hheap.2 ha hra
    apply R13Shards.memW_eq_of_ivlUnhit harr.2.2
    · omega
    · exact (R13Shards.ivl_allocated_bound hAs.2 (Or.inl hheap.2)).2
    · have hc := hl.2.2.2.1
      constructor <;> dsimp <;> omega
  have hent : ∀ i, i < memW s (logs + 8) →
      Inside (memW s (memW s logs + 8 * i), 40) sourceBase (globN post "heap_ptr") ∧
      (∀ o ∈ new, Disj (memW s (memW s logs + 8 * i), 40) o) ∧
      R13Shards.IvlUnhit s post (memW s (memW s logs + 8 * i), 40) := by
    intro i hi
    have hle := (hl.2.2.2.2 i hi).2
    exact R13Shards.heap_ivl_survives_step hAs.2 hhp hold0 hR0 hog hfr
      hle.1.1 (by decide : 40 % 8 = 0) hle.2.1 (he i hi).1 (hre i hi)
  refine ⟨⟨?_, Or.inr ?_⟩, fun _ => ?_⟩
  · exact PtxP34.logsListOK_congr_header_unhit hAs.2 hAs.1 hAp.1 hhp (Or.inr hl)
      (fun _ => Or.inl hhdr.1) hhdr.2.2 hp (fun i hi => (hent i hi).2.2)
  · rw [hm0, hm16]
    exact ⟨hhdr.1, harr_in⟩
  · refine ⟨hhdr.2.1, ?_, ?_⟩
    · rw [hm0, hm16]
      exact harr_disj
    · intro i hi
      rw [hm8] at hi
      rw [hm0, hp i hi]
      exact ⟨(hent i hi).2.1,
        PtxP34.logOwnedIvls_disj_survives hAs.2 hAp.2 (hl.2.2.2.2 i hi).2
          (hent i hi).2.2 hsys hog (he i hi).2⟩

def ptxWithdrawalBufs : BufList :=
  [("bal_key_buf", 64), ("keccak_pad", 136), ("keccak_st", 200),
   ("mpt_nib_scratch", 64), ("sk_buf", 52)]

def ptxWithdrawalGlobals : List String := ["heap_ptr", "journal_n", "scratch_ptr", "ts"]

def ptxWithdrawalKeep : List (String × List Nat) :=
  [("ws", [0, 8, 16, 24, 32]),
   ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", []),
   ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]

theorem validBufList_ptxWithdrawalBufs : ValidBufList ptxWithdrawalBufs := by
  intro p hp
  simp only [ptxWithdrawalBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact ⟨64, by decide, by decide, le_rfl⟩
  · exact ⟨136, by decide, by decide, le_rfl⟩
  · exact ⟨200, by decide, by decide, le_rfl⟩
  · exact ⟨64, by decide, by decide, le_rfl⟩
  · exact ⟨64, by decide, by decide, by decide⟩

structure PtxAfterPhase4Data {F : Type}
    (entry s s_pmc : PanSemStateFiniteExact 64 F) (w_out : BitVec 64) : Prop where
  arena_pmc : ArenaReady s_pmc
  arena_entry : ArenaReady entry
  frame_entry : globN entry "frame_mem_ptr" ≤ globN s "frame_mem_ptr"
  scratch_entry : globN s "scratch_ptr" ≤ globN entry "scratch_ptr"
  world : WorldOK s
  heap_entry : globN entry "heap_ptr" ≤ globN s "heap_ptr"
  heap_pmc : globN s_pmc "heap_ptr" ≤ globN s "heap_ptr"
  globals : GlobalsKept ptxGlobals entry s
  records : RecordsKept ptxRegions ptxKeep entry s
  out_local : s.locals.lookup (ofString "out") = some (.val (.word w_out))
  out_words : WordsOK s (w_out.toNat, 96)
  out_inside : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr")
  marks : memW s (w_out.toNat + 80) ≠ 0 →
    memW s (w_out.toNat + 80) % 8 = 0 ∧
    memW s (w_out.toNat + 88) % 8 = 0 ∧
    globN s_pmc "frame_mem_ptr" ≤ memW s (w_out.toNat + 88) ∧
    memW s (w_out.toNat + 88) ≤ memW s (w_out.toNat + 80) ∧
    memW s (w_out.toNat + 80) ≤ globN s_pmc "scratch_ptr"
  index_word : ∃ w : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word w))
  rcpt_backing : memW s (memW s (globN s "bo" + 72)) ≠ 0
  typing : ∀ S0 Nd0, WorldTypedWith entry S0 Nd0 →
    IvlsDisj (ptxRegions entry) (worldTypedIvls entry S0 Nd0) →
    ∃ S_pmc Nd_pmc S_cur Nd_cur,
      WorldTypedWith s_pmc S_pmc Nd_pmc ∧
      (∀ t ∈ S0, t ∈ S_cur) ∧
      WorldTypedWith s S_cur Nd_cur ∧
      OwnedGrows s_pmc s (worldOwned s_pmc S_pmc Nd_pmc) (worldOwned s S_cur Nd_cur) ∧
      OwnedGrows entry s (worldOwned entry S0 Nd0) (worldOwned s S_cur Nd_cur) ∧
      FrameOutside entry s (worldOwned entry S0 Nd0 ++ ptxRegions entry ++ [freeGap entry]) (heapFree entry) ∧
      (∀ o ∈ worldOwned s S_cur Nd_cur, Disj (w_out.toNat, 96) o) ∧
      (∀ i, memW entry (memW entry (globN entry "bo" + 72) + 8) ≤ i →
        i < memW s (memW s (globN s "bo" + 72) + 8) →
        StableLogsHeapDisj s (worldOwned s S_cur Nd_cur)
          (memW s (memW s (memW s (globN s "bo" + 72)) + 8 * i))) ∧
      PtxRetSlices entry (some (.returned (.val (.word 0#64)))) s S_cur Nd_cur

def PtxAfterPhase4 {F : Type} (entry s : PanSemStateFiniteExact 64 F) : Prop :=
  TxReadyStrong entry ∧ ∃ s_pmc w_out, PtxAfterPhase4Data entry s s_pmc w_out

theorem ptxAfterPhase4_release_return_logs_slices {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (h : PtxAfterPhase4 entry s)
    (hres : Resumes (evaluateHOLFiniteState s ptxPhase5ReleaseReturn).1) :
    WorldStep ptxRegions ptxGlobals ptxKeep
      (fun e r p S Nd => RetTransactionLogs e r p S Nd ∧ PtxRetSlices e r p S Nd)
      entry (evaluateHOLFiniteState s ptxPhase5ReleaseReturn).1
        (evaluateHOLFiniteState s ptxPhase5ReleaseReturn).2 := by
  obtain ⟨_, s_pmc, w_out, h⟩ := h
  apply ptxPhase5_release_return_logs_slices_worldStep hc h.arena_pmc h.world.1
    h.heap_entry h.heap_pmc h.globals h.records h.out_local h.out_words h.out_inside h.marks
    _ hres
  intro S0 Nd0 hWT hD
  obtain ⟨Sp, Np, Sc, Nc, hWp, hsub, hWc, hOGp, hOGe, hFO, _, hlogs, hslices⟩ :=
    h.typing S0 Nd0 hWT hD
  refine ⟨Sp, Np, Sc, Nc, hWp, hsub, hWc, hOGp, hOGe, hFO, ?_⟩
  refine ⟨?_, hslices⟩
  intro v hv
  dsimp only
  intro i hlo hhi
  exact (hlogs i hlo hhi).1

theorem ptxAfterPhase4_tail_relRun {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (h : PtxAfterPhase4 entry s) :
    PtxRelRun entry ptxPhase5ReleaseReturn s := by
  intro hres
  have hs := ptxAfterPhase4_release_return_logs_slices hc h hres
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, fun S Nd hW hD => by
    obtain ⟨S', Nd', hsub, hWT, hOG, hFO, hQ⟩ := hs.2.2.2.2 S Nd hW hD
    exact ⟨S', Nd', hsub, hWT, hOG, hFO, hQ.1⟩⟩

theorem ptx_ownedGrows_trans {F : Type}
    {s1 s2 s3 : PanSemStateFiniteExact 64 F} {os1 os2 os3 : List Ivl}
    (hhp12 : globN s1 "heap_ptr" ≤ globN s2 "heap_ptr")
    (hhp23 : globN s2 "heap_ptr" ≤ globN s3 "heap_ptr")
    (h12 : OwnedGrows s1 s2 os1 os2) (h23 : OwnedGrows s2 s3 os2 os3) :
    OwnedGrows s1 s3 os1 os3 := by
  intro o ho
  rcases h23 o ho with rfl | ⟨j, hj, hin⟩ | hfresh
  · exact Or.inl rfl
  · rcases h12 j hj with rfl | ⟨k, hk, hjk⟩ | hjfresh
    · left
      rcases o with ⟨b, n⟩
      exact Prod.ext (by dsimp [Inside] at hin; omega) (by dsimp [Inside] at hin; omega)
    · exact Or.inr (Or.inl ⟨k, hk, le_trans hjk.1 hin.1, le_trans hin.2 hjk.2⟩)
    · exact Or.inr (Or.inr ⟨le_trans hjfresh.1 hin.1, le_trans hin.2 (le_trans hjfresh.2 hhp23)⟩)
  · exact Or.inr (Or.inr ⟨le_trans hhp12 hfresh.1, hfresh.2⟩)

theorem ptx_frameOutside_trans {F : Type}
    {entry s post : PanSemStateFiniteExact 64 F} {old cur R0 R : List Ivl}
    (hA0 : ArenaReady entry) (hAs : ArenaReady s)
    (hhp : globN entry "heap_ptr" ≤ globN s "heap_ptr")
    (hfp : globN entry "frame_mem_ptr" ≤ globN s "frame_mem_ptr")
    (hsp : globN s "scratch_ptr" ≤ globN entry "scratch_ptr")
    (hog : OwnedGrows entry s old cur)
    (hR : ∀ i ∈ R, i ∈ R0)
    (h01 : FrameOutside entry s (old ++ R0 ++ [freeGap entry]) (heapFree entry))
    (h12 : FrameOutside s post (cur ++ R ++ [freeGap s]) (heapFree s)) :
    FrameOutside entry post (old ++ R0 ++ [freeGap entry]) (heapFree entry) := by
  intro a ha hhf
  apply Eq.trans (h12 a ?_ ?_) (h01 a ha hhf)
  · intro i hi ⟨hc1, hc2⟩
    rcases List.mem_append.1 hi with hi | hi
    · rcases List.mem_append.1 hi with hi | hi
      · rcases hog i hi with rfl | ⟨j, hj, hin⟩ | hin
        · dsimp at hc2; omega
        · exact ha j (List.mem_append_left _ (List.mem_append_left _ hj))
            ⟨by dsimp [Inside] at hin; omega, by dsimp [Inside] at hin; omega⟩
        · have hlim := hAs.2.2.1
          exact hhf ⟨by dsimp [heapFree, Inside] at hin ⊢; omega,
            by dsimp [heapFree, Inside] at hin ⊢; omega⟩
      · exact ha i (List.mem_append_left _ (List.mem_append_right _ (hR i hi))) ⟨hc1, hc2⟩
    · simp only [List.mem_singleton] at hi
      subst i
      have h0 := hA0.2.2.2.2.1
      have h1 := hAs.2.2.2.2.1
      exact ha (freeGap entry) (List.mem_append_right _ (by simp))
        ⟨by dsimp [freeGap] at hc1 ⊢; omega, by dsimp [freeGap] at hc2 ⊢; omega⟩
  · intro ⟨hc1, hc2⟩
    have hlim := hAs.2.2.1
    exact hhf ⟨by dsimp [heapFree] at hc1 ⊢; omega, by dsimp [heapFree] at hc2 ⊢; omega⟩

theorem ptxAfterPhase4_worldStep {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} (h : PtxAfterPhase4 entry s)
    (r : Option (PanSemResultExact 64)) :
    WorldStep ptxRegions ptxGlobals ptxKeep NoExtra entry r s := by
  obtain ⟨_, sp, wo, h⟩ := h
  refine ⟨h.world.1, h.heap_entry, h.globals, h.records, ?_⟩
  intro S Nd hWT hD
  obtain ⟨Sp, Np, Sc, Nc, _, hsub, hWc, _, hOG, hFO, _⟩ := h.typing S Nd hWT hD
  exact ⟨Sc, Nc, hsub, hWc, hOG, hFO, trivial⟩

def ptxBufs : BufList :=
  [("b2_v", 128), ("bal_key_buf", 64), ("bn_expw", 352), ("bn_gamma", 384),
   ("evm_key_buf", 32), ("keccak_pad", 136), ("keccak_st", 200),
   ("mpt_nib_scratch", 64), ("pre_hdr_buf", 96), ("rmd_h", 40),
   ("rmd_pad", 128), ("rmd_x", 128), ("sha_pad", 128), ("sha_st", 64),
   ("sk_buf", 52), ("u256_ws", 640)]

theorem ptxRegions_eq_bufRegions {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ptxRegions s = bufRegions ptxBufs s := rfl

theorem validBufList_ptxBufs : ValidBufList ptxBufs := by
  intro p hp
  simp only [ptxBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨128, by decide, by decide, le_rfl⟩
  · exact ⟨64, by decide, by decide, le_rfl⟩
  · exact ⟨352, by decide, by decide, le_rfl⟩
  · exact ⟨384, by decide, by decide, le_rfl⟩
  · exact ⟨32, by decide, by decide, le_rfl⟩
  · exact ⟨136, by decide, by decide, le_rfl⟩
  · exact ⟨200, by decide, by decide, le_rfl⟩
  · exact ⟨64, by decide, by decide, le_rfl⟩
  · exact ⟨96, by decide, by decide, le_rfl⟩
  · exact ⟨40, by decide, by decide, le_rfl⟩
  · exact ⟨128, by decide, by decide, le_rfl⟩
  · exact ⟨128, by decide, by decide, le_rfl⟩
  · exact ⟨128, by decide, by decide, le_rfl⟩
  · exact ⟨64, by decide, by decide, le_rfl⟩
  · exact ⟨64, by decide, by decide, by decide⟩
  · exact ⟨640, by decide, by decide, le_rfl⟩

theorem ptxBufs_mem_of_not_in_ptxGlobals {p : String × Nat} (hp : p ∈ ptxBufs) :
    p.1 ∈ ptxGlobals ∨ ofString p.1 ∉ ptxGlobals.map ofString := by
  simp only [ptxBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (by decide)
  · exact Or.inr (by decide)
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inr (by decide)
  · exact Or.inr (by decide)
  · exact Or.inr (by decide)
  · exact Or.inr (by decide)
  · exact Or.inr (by decide)
  · exact Or.inr (by decide)
  · exact Or.inr (by decide)
  · exact Or.inr (by decide)
  · exact Or.inr (by decide)
  · exact Or.inr (by decide)
  · exact Or.inr (by decide)
  · exact Or.inr (by decide)

theorem ptx_bufRegions_zero_aligned {F : Type}
    {s : PanSemStateFiniteExact 64 F} {B : BufList}
    (hB : ValidBufList B) (hF : FixedTyped s) :
    ∀ j ∈ bufRegions B s, j.2 = 0 → j.1 % 8 = 0 := by
  intro j hj _
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
  obtain ⟨sz, hgb, _, _⟩ := hB p hp
  by_cases hz : globN s p.1 = 0
  · simp [bufferRegion, hz]
  · have hfix : bufferRegion s (p.1, sz) ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
    have hpos : 0 < sz := by
      have hgb' : ∀ gn ∈ globalBuffers, 0 < gn.2 := by decide
      exact hgb' (p.1, sz) hgb
    rcases hF.1 _ hfix with h0 | ⟨_, hw⟩
    · simp [bufferRegion, hz] at h0; omega
    · have h1 := hw.1
      simp only [bufferRegion, hz, ↓reduceIte] at h1 ⊢
      exact h1

theorem ptx_disj_bufRegions_of_disj_worldOwned {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {B : BufList} {b : Ivl}
    (hB : ValidBufList B) (hd : ∀ o ∈ worldOwned s S Nd, Disj b o) :
    ∀ j ∈ bufRegions B s, Disj b j := by
  intro j hj
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
  obtain ⟨sz, hgb, _, hle⟩ := hB p hp
  have hfix : bufferRegion s (p.1, sz) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
  have hdo := hd _ (List.mem_append_left _ (List.mem_append_right _ hfix))
  by_cases hz : globN s p.1 = 0
  · simp [bufferRegion, hz]
    exact R10Shards.Fast_GbodyC17ToC21.disj_zero_right b
  · simp only [bufferRegion, hz, ↓reduceIte] at hdo ⊢
    exact R10Shards.Fast_GbodyC17ToC21.disj_of_inside_right
      (j' := (globN s p.1, sz)) ⟨le_rfl, by dsimp; omega⟩ hdo

def PtxKeepSub (keep : List (String × List Nat)) : Prop :=
  ∀ rec ∈ ptxKeep, ∃ offs, (rec.1, offs) ∈ keep ∧ ∀ off ∈ rec.2, off ∈ offs

theorem ptxKeepSub_ptxWithdrawalKeep : PtxKeepSub ptxWithdrawalKeep := by
  intro rec hrec
  simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
  rcases hrec with rfl | rfl | rfl | rfl
  · exact ⟨[0, 8, 16, 24, 32], by simp [ptxWithdrawalKeep], fun _ h => h⟩
  · refine ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64, 72], by simp [ptxWithdrawalKeep], ?_⟩
    intro off hoff
    simp at hoff ⊢
    omega
  · exact ⟨[], by simp [ptxWithdrawalKeep], fun _ h => h⟩
  · refine ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80], by simp [ptxWithdrawalKeep], ?_⟩
    intro off hoff
    simp at hoff ⊢
    omega

theorem ptxKeepSub_stdKeep : PtxKeepSub stdKeep := by
  intro rec hrec
  simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
  rcases hrec with rfl | rfl | rfl | rfl
  · exact ⟨[0, 8, 16, 24, 32], by simp [stdKeep], fun _ h => h⟩
  · refine ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64, 72], by simp [stdKeep], ?_⟩
    intro off hoff
    simp at hoff ⊢
    omega
  · exact ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64], by simp [stdKeep], fun _ h => False.elim (by simp at h)⟩
  · refine ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80], by simp [stdKeep], ?_⟩
    intro off hoff
    simp at hoff ⊢
    omega

theorem ptxBufs_sub_entry {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {B : BufList}
    (hG : GlobalsKept ptxGlobals entry s)
    (hB : ∀ p ∈ B, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals) :
    ∀ i ∈ bufRegions B s, i ∈ ptxRegions entry := by
  rw [ptxRegions_eq_bufRegions]
  intro i hi
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
  obtain ⟨hptx, hng⟩ := hB p hp
  have hni : ofString p.1 ∉ ptxGlobals.map ofString := by
    rcases ptxBufs_mem_of_not_in_ptxGlobals hptx with hg | hni
    · exact absurd hg hng
    · exact hni
  have hgeq : globN s p.1 = globN entry p.1 :=
    globN_eq_of_lookup (hG (ofString p.1) hni)
  refine List.mem_map.2 ⟨p, hptx, ?_⟩
  simp [bufferRegion, hgeq]

theorem ptxAfterPhase4_step_worldStep {F : Type}
    {entry s post : PanSemStateFiniteExact 64 F} {B : BufList}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (h : PtxAfterPhase4 entry s)
    (hB : ValidBufList B)
    (hBsub : ∀ p ∈ B, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals)
    (hgw : ∀ g ∈ gw, g ∈ ptxGlobals)
    (_hfmp : ofString "frame_mem_ptr" ∉ gw.map ofString)
    (hkeep : PtxKeepSub keep)
    (_hrec : ∀ rec ∈ ptxKeep, ∀ off ∈ rec.2, ofString rec.1 ∉ gw.map ofString)
    (hstep : WorldStepSc (bufRegions B) gw keep Q s r post) :
    WorldStep ptxRegions ptxGlobals ptxKeep NoExtra entry r post := by
  obtain ⟨_, sp, wo, h⟩ := h
  have hRsub := ptxBufs_sub_entry h.globals hBsub
  refine ⟨hstep.1.1, le_trans h.heap_entry hstep.1.2.1, ?_, ?_, ?_⟩
  · intro k hk
    have hkg : k ∉ gw.map ofString := by
      intro hm
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
      exact hk (List.mem_map.2 ⟨g, hgw g hg, rfl⟩)
    exact (h.globals k hk).trans (hstep.1.2.2.1 k hkg)
  · intro rec hr hn off hoff hno
    obtain ⟨offs, hkr, hko⟩ := hkeep rec hr
    have heq : globN s rec.1 = globN entry rec.1 := by
      have hni : ofString rec.1 ∉ ptxGlobals.map ofString := by
        simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · decide
        · decide
        · simp at hoff
        · decide
      exact globN_eq_of_lookup (h.globals (ofString rec.1) hni)
    have hks := hstep.1.2.2.2.1 (rec.1, offs) hkr (by simpa only [heq] using hn)
      off (hko off hoff) (by
        intro i hi
        simpa only [heq] using hno i (hRsub i hi))
    rw [heq] at hks
    exact hks.trans (h.records rec hr hn off hoff hno)
  · intro S Nd hWT hD
    obtain ⟨Sp, Np, Sc, Nc, hWp, hsub, hWc, hOGp, hOG, hFO, hrest⟩ :=
      h.typing S Nd hWT hD
    obtain ⟨Sn, Nn, hsubn, hWn, hOGn, hFOn, _⟩ :=
      hstep.1.2.2.2.2 Sc Nc hWc (validBufList_disj hB hWc)
    refine ⟨Sn, Nn, fun t ht => hsubn t (hsub t ht), hWn,
      ptx_ownedGrows_trans h.heap_entry hstep.1.2.1 hOG hOGn, ?_, trivial⟩
    exact ptx_frameOutside_trans h.arena_entry h.world.1 h.heap_entry
      h.frame_entry h.scratch_entry hOG hRsub hFO hFOn

theorem ptxAfterPhase4_exception_worldStep {F : Type}
    {entry s post : PanSemStateFiniteExact 64 F} {B : BufList}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {eid : MlS} {v : ValueHOL 64}
    (h : PtxAfterPhase4 entry s)
    (hB : ValidBufList B)
    (hBsub : ∀ p ∈ B, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals)
    (hgw : ∀ g ∈ gw, g ∈ ptxGlobals)
    (hfmp : ofString "frame_mem_ptr" ∉ gw.map ofString)
    (hkeep : PtxKeepSub keep)
    (hrec : ∀ rec ∈ ptxKeep, ∀ off ∈ rec.2, ofString rec.1 ∉ gw.map ofString)
    (hstep : WorldStepSc (bufRegions B) gw keep Q s (some (.exception eid v)) post) :
    WorldStep ptxRegions ptxGlobals ptxKeep
      (fun e r p S Nd => RetTransactionLogs e r p S Nd ∧ PtxRetSlices e r p S Nd)
      entry (some (.exception eid v)) post := by
  have hb := ptxAfterPhase4_step_worldStep h hB hBsub hgw hfmp hkeep hrec hstep
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, ?_⟩
  intro S Nd hWT hD
  obtain ⟨Sn, Nn, hsub, hWn, hOG, hFO, _⟩ := hb.2.2.2.2 S Nd hWT hD
  exact ⟨Sn, Nn, hsub, hWn, hOG, hFO,
    (by intro val hv; cases hv), (by intro val hv; cases hv)⟩

theorem ptxAfterPhase4Data_with_locals {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : PtxAfterPhase4Data entry s s_pmc w_out)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (ck : Nat)
    (hout : L.lookup (ofString "out") = some (.val (.word w_out)))
    (hi : ∃ w : BitVec 64, L.lookup (ofString "i") = some (.val (.word w))) :
    PtxAfterPhase4Data entry { s with locals := L, clock := ck } s_pmc w_out := by
  refine ⟨h.arena_pmc, h.arena_entry, h.frame_entry, h.scratch_entry,
    localsFree_worldOK s L ck h.world, h.heap_entry, h.heap_pmc,
    h.globals, h.records, hout, h.out_words, h.out_inside, h.marks, hi, h.rcpt_backing, ?_⟩
  intro S0 Nd0 hWT hD
  obtain ⟨Sp, Np, Sc, Nc, hWp, hsub, hWc, hOGp, hOG, hFO, hd, hl, hs⟩ :=
    h.typing S0 Nd0 hWT hD
  exact ⟨Sp, Np, Sc, Nc, hWp, hsub,
    (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals s L ck Sc Nc).2 hWc,
    hOGp, hOG, hFO, hd, hl, hs⟩

theorem ptxRelRun_seq_of_cut {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {p1 tail : ProgHOL 64}
    {B : PanSemStateFiniteExact 64 F → Prop}
    (hc : s.code = originalRuntimeCode)
    (hfall : (evaluateHOLFiniteState s p1).1 = none →
      B (evaluateHOLFiniteState s p1).2)
    (hstop : PtxRelRun entry p1 s)
    (htail : ∀ mid : PanSemStateFiniteExact 64 F,
      mid.code = originalRuntimeCode → B mid → PtxRelRun entry tail mid) :
    PtxRelRun entry (.seq p1 tail) s := by
  intro hres
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s p1).1
  rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
  rcases he : evaluateHOLFiniteState s p1 with ⟨r, mid⟩
  simp only [he] at hmeta hres ⊢
  cases r with
  | none =>
    have hB : B mid := by
      have hb := hfall (by rw [he])
      simpa only [he] using hb
    exact htail mid (hmeta.trans hc) hB hres
  | some r =>
    have hs := hstop (by simpa only [he] using hres)
    simpa only [he] using hs

theorem ptxAfterPhase4Data_setVar {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : PtxAfterPhase4Data entry s s_pmc w_out)
    (x : MlS) (v : ValueHOL 64)
    (hxout : x ≠ ofString "out") (hxi : x ≠ ofString "i") :
    PtxAfterPhase4Data entry (setVarHOLFinite x v s) s_pmc w_out := by
  apply ptxAfterPhase4Data_with_locals h
  · simpa [HolFiniteMapExact.lookup_update, FUPDATE, hxout, Ne.symm hxout] using h.out_local
  · obtain ⟨w, hw⟩ := h.index_word
    exact ⟨w, by simpa [HolFiniteMapExact.lookup_update, FUPDATE, hxi, Ne.symm hxi] using hw⟩

theorem ptxAfterPhase4Data_setIndex {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : PtxAfterPhase4Data entry s s_pmc w_out) (w : BitVec 64) :
    PtxAfterPhase4Data entry
      (setVarHOLFinite (ofString "i") (.val (.word w)) s) s_pmc w_out := by
  apply ptxAfterPhase4Data_with_locals h
  · simpa [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "out" by decide] using h.out_local
  · exact ⟨w, by simp [HolFiniteMapExact.lookup_update, FUPDATE]⟩

theorem ptx_bo_field_eq_of_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {B : BufList} {keep : List (String × List Nat)} {offs : List Nat}
    (hB : ValidBufList B) (hWT : WorldTypedWith s S Nd)
    (hrec : RecordsKept (bufRegions B) keep s post)
    (hbo_keep : ("bo", offs) ∈ keep)
    (hbo_nz : globN s "bo" ≠ 0)
    {off : Nat} (hoff : off ∈ offs) (hoff8 : off % 8 = 0) (hoff_lt : off + 8 ≤ 88) :
    memW post (globN s "bo" + off) = memW s (globN s "bo" + off) := by
  apply hrec ("bo", offs) hbo_keep hbo_nz off hoff
  intro i hi hhit
  have hbo_wti : bufferRegion s ("bo", 88) ∈ worldTypedIvls s S Nd := by
    unfold worldTypedIvls
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_right
    exact List.mem_map.2 ⟨("bo", 88), by decide, rfl⟩
  have hdj := validBufList_disj hB hWT i hi _ hbo_wti
  simp only [bufferRegion, hbo_nz, ↓reduceIte] at hdj
  obtain ⟨hh1, hh2⟩ := hhit
  dsimp only at hh1 hh2
  have hi0 : i.2 = 0 → i.1 % 8 = 0 := ptx_bufRegions_zero_aligned hB hWT.2.2.1 i hi
  have hbo8 : globN s "bo" % 8 = 0 := by
    have hfix : bufferRegion s ("bo", 88) ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨("bo", 88), by decide, rfl⟩
    rcases hWT.2.2.1.1 _ hfix with h0 | ⟨_, hw⟩
    · simp [bufferRegion, hbo_nz] at h0
    · simpa [bufferRegion, hbo_nz] using hw.1
  rcases hdj with h0 | h0 | hhi | hlo
  · have := hi0 h0; omega
  · dsimp only at h0; omega
  · dsimp only at hhi; omega
  · dsimp only at hlo; omega

theorem ptx_entry_bo_field_eq {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {S0 Nd0 : List Nat}
    (hWT_e : WorldTypedWith entry S0 Nd0)
    (hglob : GlobalsKept ptxGlobals entry s)
    (hrec : RecordsKept ptxRegions ptxKeep entry s)
    (hbo_nz_e : globN entry "bo" ≠ 0)
    {off : Nat} (hoff : off ∈ ([24, 32, 40, 56, 64, 72, 80] : List Nat)) (hoff_lt : off + 8 ≤ 88) :
    memW s (globN s "bo" + off) = memW entry (globN entry "bo" + off) := by
  have hbo_s_entry : globN s "bo" = globN entry "bo" :=
    globN_eq_of_lookup (hglob (ofString "bo") (by decide))
  rw [hbo_s_entry]
  apply hrec ("bo", [24, 32, 40, 56, 64, 72, 80]) (by simp [ptxKeep]) hbo_nz_e off hoff
  intro i hi hhit
  change i ∈ ptxRegions entry at hi
  rw [ptxRegions_eq_bufRegions] at hi
  have hbo_wti : bufferRegion entry ("bo", 88) ∈ worldTypedIvls entry S0 Nd0 := by
    unfold worldTypedIvls
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_right
    exact List.mem_map.2 ⟨("bo", 88), by decide, rfl⟩
  have hdj := validBufList_disj validBufList_ptxBufs hWT_e i hi _ hbo_wti
  simp only [bufferRegion, hbo_nz_e, ↓reduceIte] at hdj
  obtain ⟨hh1, hh2⟩ := hhit
  dsimp only at hh1 hh2
  have hi0 : i.2 = 0 → i.1 % 8 = 0 :=
    ptx_bufRegions_zero_aligned validBufList_ptxBufs hWT_e.2.2.1 i hi
  have hbo8 : globN entry "bo" % 8 = 0 := by
    have hfix : bufferRegion entry ("bo", 88) ∈ fixedObjects entry := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨("bo", 88), by decide, rfl⟩
    rcases hWT_e.2.2.1.1 _ hfix with h0 | ⟨_, hw⟩
    · simp [bufferRegion, hbo_nz_e] at h0
    · simpa [bufferRegion, hbo_nz_e] using hw.1
  have hoff8 : off % 8 = 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rcases hdj with h0 | h0 | hhi | hlo
  · have := hi0 h0; omega
  · dsimp only at h0; omega
  · dsimp only at hhi; omega
  · dsimp only at hlo; omega

theorem ptxAfterPhase4Data_step_of_blockOutUnhit {F : Type}
    {entry s post s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    {B : BufList} {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (h : PtxAfterPhase4Data entry s s_pmc w_out)
    (he_ready : TxReadyStrong entry)
    (hB : ValidBufList B)
    (hBsub : ∀ p ∈ B, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals)
    (hgw : ∀ g ∈ gw, g ∈ ptxGlobals)
    (hfmp : ofString "frame_mem_ptr" ∉ gw.map ofString)
    (hsys : ofString "vm_system_address" ∉ gw.map ofString)
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hbo_keep : ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) ∈ keep)
    (hkeep : PtxKeepSub keep)
    (hstep : WorldStepSc (bufRegions B) gw keep Q s r post)
    (hbo_unhit : PtxBlockOutUnhit s post)
    (hout : post.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hi : ∃ w : BitVec 64, post.locals.lookup (ofString "i") = some (.val (.word w))) :
    PtxAfterPhase4Data entry post s_pmc w_out := by
  have hws_entry := ptxAfterPhase4_step_worldStep ⟨he_ready, s_pmc, w_out, h⟩ hB hBsub hgw hfmp hkeep
    (fun rec hr off hoff => by
      have hni : ofString rec.1 ∉ ptxGlobals.map ofString := by
        simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · decide
        · decide
        · simp at hoff
        · decide
      intro hm
      obtain ⟨g, hg, he⟩ := List.mem_map.1 hm
      exact hni (List.mem_map.2 ⟨g, hgw g hg, he⟩))
    hstep
  have hfmp_eq : globN s "frame_mem_ptr" = globN post "frame_mem_ptr" :=
    (globN_eq_of_lookup (hstep.1.2.2.1 _ hfmp)).symm
  have hsys_eq : globN post "vm_system_address" = globN s "vm_system_address" :=
    globN_eq_of_lookup (hstep.1.2.2.1 _ hsys)
  have hbo_eq : globN post "bo" = globN s "bo" :=
    globN_eq_of_lookup (hstep.1.2.2.1 _ hbo_gw)
  have hbo_s_entry : globN s "bo" = globN entry "bo" :=
    globN_eq_of_lookup (h.globals (ofString "bo") (by decide))
  obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, _, _, hbo72_nz_e, S_e, Nd_e, hWT_e, _⟩ := he_ready
  have hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e) := by
    rw [ptxRegions_eq_bufRegions]
    exact validBufList_disj validBufList_ptxBufs hWT_e
  have hbo_nz_s : globN s "bo" ≠ 0 := by rw [hbo_s_entry]; exact hbo_nz_e
  obtain ⟨_, _, S_w, Nd_w, _, _, hWT_w, _, _, _, hd_out_w, _, _⟩ := h.typing S_e Nd_e hWT_e hD_e
  obtain ⟨S_wp, Nd_wp, _, hWT_wp, hOG_wp, hFO_wp, _⟩ :=
    hstep.1.2.2.2.2 S_w Nd_w hWT_w (validBufList_disj hB hWT_w)
  have hout_surv := R13Shards.heap_ivl_survives_step h.world.1.2 hstep.1.2.1
    (R13Shards.worldOwned_zero_aligned hWT_w)
    (ptx_bufRegions_zero_aligned hB hWT_w.2.2.1)
    hOG_wp hFO_wp h.out_words.1 (by decide : 96 % 8 = 0) h.out_inside hd_out_w
    (ptx_disj_bufRegions_of_disj_worldOwned hB hd_out_w)
  have hout_words_post : WordsOK post (w_out.toNat, 96) :=
    R10Shards.Fast_GbodyC17ToC21.wordsOK_congr_unhit h.world.1.1 hstep.1.1.1 h.out_words
  have hout_hi : w_out.toNat + 96 ≤ 2 ^ 64 :=
    (R13Shards.ivl_allocated_bound h.world.1.2 (Or.inl h.out_inside)).2
  have hout80_eq : memW post (w_out.toNat + 80) = memW s (w_out.toNat + 80) :=
    R13Shards.memW_eq_of_ivlUnhit hout_surv.2.2
      (by have := h.out_words.1; omega) hout_hi ⟨by omega, by omega⟩
  have hout88_eq : memW post (w_out.toNat + 88) = memW s (w_out.toNat + 88) :=
    R13Shards.memW_eq_of_ivlUnhit hout_surv.2.2
      (by have := h.out_words.1; omega) hout_hi ⟨by omega, by omega⟩
  have hworld_post : WorldOK post :=
    ⟨hstep.1.1, S_wp, (worldTyped_iff_with post S_wp).2 ⟨Nd_wp, hWT_wp⟩⟩
  have hbo_field_s : ∀ off ∈ ([0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80] : List Nat),
      off % 8 = 0 → off + 8 ≤ 88 → memW post (globN s "bo" + off) = memW s (globN s "bo" + off) :=
    fun off hoff hoff8 hlt => ptx_bo_field_eq_of_step hB hWT_w hstep.1.2.2.2.1 hbo_keep hbo_nz_s hoff hoff8 hlt
  have hbo24_s : memW s (globN s "bo" + 24) = memW entry (globN entry "bo" + 24) :=
    ptx_entry_bo_field_eq hWT_e h.globals h.records hbo_nz_e (by simp) (by omega)
  have hbo32_s : memW s (globN s "bo" + 32) = memW entry (globN entry "bo" + 32) :=
    ptx_entry_bo_field_eq hWT_e h.globals h.records hbo_nz_e (by simp) (by omega)
  have hbo72_s : memW s (globN s "bo" + 72) = memW entry (globN entry "bo" + 72) :=
    ptx_entry_bo_field_eq hWT_e h.globals h.records hbo_nz_e (by simp) (by omega)
  have hbo80_s : memW s (globN s "bo" + 80) = memW entry (globN entry "bo" + 80) :=
    ptx_entry_bo_field_eq hWT_e h.globals h.records hbo_nz_e (by simp) (by omega)
  have hbo72_nz_s : memW s (globN s "bo" + 72) ≠ 0 := by rw [hbo72_s]; exact hbo72_nz_e
  have hbo72_post : memW post (globN post "bo" + 72) = memW s (globN s "bo" + 72) := by
    rw [hbo_eq]
    exact hbo_field_s 72 (by simp) (by decide) (by omega)
  have hrcpt_hdr8 : memW post (memW post (globN post "bo" + 72) + 8) =
      memW s (memW s (globN s "bo" + 72) + 8) := by
    rw [hbo72_post]
    exact ptx_receipt_header_eq_of_blockOutUnhit h.world.1 hWT_w hbo_unhit hbo_nz_s hbo72_nz_s (by simp)
  have hrcpt_hdr0 : memW post (memW post (globN post "bo" + 72)) =
      memW s (memW s (globN s "bo" + 72)) := by
    rw [hbo72_post]
    simpa using ptx_receipt_header_eq_of_blockOutUnhit h.world.1 hWT_w hbo_unhit hbo_nz_s hbo72_nz_s (off := 0) (by simp)
  have hrcpt_backing_post : memW post (memW post (globN post "bo" + 72)) ≠ 0 := by
    rw [hrcpt_hdr0]
    exact h.rcpt_backing
  refine ⟨h.arena_pmc, h.arena_entry, ?_, le_trans hstep.2 h.scratch_entry,
    hworld_post, hws_entry.2.1, le_trans h.heap_pmc hstep.1.2.1,
    hws_entry.2.2.1, hws_entry.2.2.2.1, hout, hout_words_post, hout_surv.1,
    ?_, hi, hrcpt_backing_post, ?_⟩
  · rw [← hfmp_eq]; exact h.frame_entry
  · intro hnz
    rw [hout80_eq] at hnz
    rw [hout80_eq, hout88_eq]
    exact h.marks hnz
  · intro S0 Nd0 hWT0 hD0
    obtain ⟨Sp, Np, Sc, Nc, hWp, hsub, hWc, hOGp, hOGe, hFOe, hd_out, hlogs, hslices⟩ :=
      h.typing S0 Nd0 hWT0 hD0
    obtain ⟨Sn, Nn, hsubn, hWn, hOGn, hFOn, _⟩ :=
      hstep.1.2.2.2.2 Sc Nc hWc (validBufList_disj hB hWc)
    have hout_surv_c := R13Shards.heap_ivl_survives_step h.world.1.2 hstep.1.2.1
      (R13Shards.worldOwned_zero_aligned hWc)
      (ptx_bufRegions_zero_aligned hB hWc.2.2.1)
      hOGn hFOn h.out_words.1 (by decide : 96 % 8 = 0) h.out_inside hd_out
      (ptx_disj_bufRegions_of_disj_worldOwned hB hd_out)
    refine ⟨Sp, Np, Sn, Nn, hWp, fun t ht => hsubn t (hsub t ht), hWn,
      ptx_ownedGrows_trans h.heap_pmc hstep.1.2.1 hOGp hOGn,
      ptx_ownedGrows_trans h.heap_entry hstep.1.2.1 hOGe hOGn,
      ptx_frameOutside_trans h.arena_entry h.world.1 h.heap_entry h.frame_entry h.scratch_entry
        hOGe (ptxBufs_sub_entry h.globals hBsub) hFOe hFOn,
      hout_surv_c.2.1, ?_, ?_⟩
    · intro i hlo hhi
      rw [hrcpt_hdr8] at hhi
      have hrcpt_lst : LstOK s (memW s (globN s "bo" + 72)) :=
        hWc.1.2.2.2.2.2.2.2.2.2.2.1 hbo_nz_s 72 (by simp) hbo72_nz_s
      have hhi_cap : i < memW s (memW s (globN s "bo" + 72) + 16) := by
        have := hrcpt_lst.2
        omega
      have helem_eq : memW post (memW post (memW post (globN post "bo" + 72)) + 8 * i) =
          memW s (memW s (memW s (globN s "bo" + 72)) + 8 * i) := by
        rw [hrcpt_hdr0]
        exact ptx_receipt_element_eq_of_blockOutUnhit h.world.1 hWc hbo_unhit hbo_nz_s hbo72_nz_s h.rcpt_backing hrcpt_lst hhi_cap
      rw [helem_eq]
      have hlog_s := hlogs i hlo hhi
      exact stableLogsHeapDisj_step h.world.1 hstep.1.1 hstep.1.2.1
        (R13Shards.worldOwned_zero_aligned hWc)
        (ptx_bufRegions_zero_aligned hB hWc.2.2.1)
        hOGn hFOn hsys_eq hlog_s
        (fun hlnz => by
          obtain ⟨hd1, hd2, hd3⟩ := hlog_s.2 hlnz
          exact ⟨ptx_disj_bufRegions_of_disj_worldOwned hB hd1,
            ptx_disj_bufRegions_of_disj_worldOwned hB hd2,
            fun k hk => ptx_disj_bufRegions_of_disj_worldOwned hB (hd3 k hk).1⟩)
    · intro v hv
      obtain ⟨hsl1, hsl2⟩ := hslices v hv
      have hsl_eq : ∀ off ∈ ([24, 32] : List Nat), ∀ k, k ≤ locN entry "index" →
          memW post (memW post (globN post "bo" + off) + 16 * k + 8) =
            memW s (memW s (globN s "bo" + off) + 16 * k + 8) := by
        intro off hoff k hk
        have hoff_in : off ∈ ([0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80] : List Nat) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
          rcases hoff with rfl | rfl <;> simp
        have hbo_off_eq : memW post (globN post "bo" + off) = memW s (globN s "bo" + off) := by
          rw [hbo_eq]
          apply hbo_field_s off hoff_in
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
            rcases hoff with rfl | rfl <;> decide
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
            rcases hoff with rfl | rfl <;> omega
        rw [hbo_off_eq]
        have hp_nz : memW s (globN s "bo" + off) ≠ 0 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
          rcases hoff with rfl | rfl
          · rw [hbo24_s]; exact hbo24_nz_e
          · rw [hbo32_s]; exact hbo32_nz_e
        apply ptx_slice_length_eq_of_blockOutUnhit h.world.1 hWc hbo_unhit hbo_nz_s hoff hp_nz
        rw [hbo80_s]
        omega
      refine ⟨?_, ?_⟩
      · intro off hoff k hk
        rw [hsl_eq off hoff k (Nat.le_of_lt hk)]
        exact hsl1 off hoff k hk
      · intro off hoff
        rw [hsl_eq off hoff (locN entry "index") le_rfl]
        exact hsl2 off hoff


def ptxPhase5Incorporate : ProgHOL 64 :=
  .call (some (none, none)) (ofString "incorporate_tx_into_block") []

def ptxPhase5Cleanup (tail : ProgHOL 64) : ProgHOL 64 :=
  R13Shards.spinePlug 2 R13Shards.ptxPhase5 tail

theorem ptxPhase5_eq_cleanup_incorporate_release :
    R13Shards.ptxPhase5 =
      ptxPhase5Cleanup (.seq ptxPhase5Incorporate ptxPhase5ReleaseReturn) := by
  unfold ptxPhase5Cleanup ptxPhase5Incorporate ptxPhase5ReleaseReturn
    R13Shards.ptxPhase5 R13Shards.ptxCode
  rfl

theorem ptxAfterPhase4_incorporate_release_relRun {F : Type}
    {entry s : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode)
    (hfall : (evaluateHOLFiniteState s ptxPhase5Incorporate).1 = none →
      PtxAfterPhase4 entry (evaluateHOLFiniteState s ptxPhase5Incorporate).2)
    (hstop : PtxRelRun entry ptxPhase5Incorporate s) :
    PtxRelRun entry (.seq ptxPhase5Incorporate ptxPhase5ReleaseReturn) s := by
  exact ptxRelRun_seq_of_cut hc hfall hstop
    (fun _ hcode hdata => ptxAfterPhase4_tail_relRun hcode hdata)

theorem ptxAfterPhase4_phase5_relRun_of_cuts
    (hcleanup : PtxRelCut ptxPhase5Cleanup PtxAfterPhase4 PtxAfterPhase4)
    (hincorporate : ∀ {F : Type} (entry s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → PtxAfterPhase4 entry s →
      ((evaluateHOLFiniteState s ptxPhase5Incorporate).1 = none →
        PtxAfterPhase4 entry (evaluateHOLFiniteState s ptxPhase5Incorporate).2) ∧
      PtxRelRun entry ptxPhase5Incorporate s)
    {F : Type} (entry s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (h : PtxAfterPhase4 entry s) :
    PtxRelRun entry R13Shards.ptxPhase5 s := by
  rw [ptxPhase5_eq_cleanup_incorporate_release]
  apply hcleanup entry _ _ s hc h
  intro mid hcode hdata
  obtain ⟨hfall, hstop⟩ := hincorporate entry mid hcode hdata
  exact ptxAfterPhase4_incorporate_release_relRun hcode hfall hstop

private def ptxCleanupBody : ProgHOL 64 :=
  .ite (.cmp .notEqual (.var .local (ofString "del")) (.const 0#64))
    (.dec (ofString "dcap") .one
      (.load .one (.op .add [.var .local (ofString "del"), .const 24#64]))
      (.seq (.assign .local (ofString "i") (.const 0#64))
        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "dcap")))
          (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item")
            [.var .local (ofString "del"), .var .local (ofString "i")]
            (.seq
              (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0#64))
                (.call (some (none, none)) (ofString "clear_account_preserving_balance")
                  [.rfield 1 (.var .local (ofString "s"))])
                .skip)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])))))))
    .skip

private theorem ptxPhase5Cleanup_eq (tail : ProgHOL 64) :
    ptxPhase5Cleanup tail = .dec (ofString "del") .one
      (.load .one (.op .add [.var .local (ofString "out"), .const 24#64]))
      (.seq ptxCleanupBody tail) := by
  unfold ptxPhase5Cleanup ptxCleanupBody R13Shards.ptxPhase5 R13Shards.ptxCode
  simp only [sourceFunctionEntry, Guest.Software.guestFn_process_transaction,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil, R13Shards.spineAt, R13Shards.spinePlug]

private theorem ptxCleanupBody_step {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hnt : (evaluateHOLFiniteState s ptxCleanupBody).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s ptxCleanupBody).1) :
    WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
      s (evaluateHOLFiniteState s ptxCleanupBody).1 (evaluateHOLFiniteState s ptxCleanupBody).2 := by
  revert hnt hfr
  unfold ptxCleanupBody
  have hB := validBufList_acctMutBufs
  have hgw : SafeStepGlobals ["heap_ptr", "journal_n", "scratch_ptr"] := by
    intro g hg; simp at hg; rcases hg with rfl | rfl | rfl <;> simp
  have hloop : ProgWStep acctMutBufs ["heap_ptr", "journal_n", "scratch_ptr"]
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "dcap")))
        (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item")
          [.var .local (ofString "del"), .var .local (ofString "i")]
          (.seq
            (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0#64))
              (.call (some (none, none)) (ofString "clear_account_preserving_balance")
                [.rfield 1 (.var .local (ofString "s"))])
              .skip)
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))))) := by
    refine progWStep_while hB hgw ?_
    refine progWStep_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
      (worldKeepsSc_of_readOnly ro_htab_item) ?_
    refine progWStep_seq hB hgw ?_ (progWStep_assign_local _ _ _ _)
    refine progWStep_ite ?_ (progWStep_skip _ _)
    exact progWStep_call0 (by intro p hp; exact hp) (by intro g hg; exact hg)
      wkSc_clear_account_preserving_balance
  have hyes : ProgWStep acctMutBufs ["heap_ptr", "journal_n", "scratch_ptr"]
      (.dec (ofString "dcap") .one
        (.load .one (.op .add [.var .local (ofString "del"), .const 24#64]))
        (.seq (.assign .local (ofString "i") (.const 0#64))
          (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "dcap")))
            (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item")
              [.var .local (ofString "del"), .var .local (ofString "i")]
              (.seq
                (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0#64))
                  (.call (some (none, none)) (ofString "clear_account_preserving_balance")
                    [.rfield 1 (.var .local (ofString "s"))])
                  .skip)
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))))))) := by
    refine progWStep_dec ?_
    exact progWStep_seq hB hgw (progWStep_assign_local _ _ _ _) hloop
  exact progWStep_ite hyes (progWStep_skip _ _) s hc hW

private theorem acctMut_sub_ptx : ∀ p ∈ acctMutBufs, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals := by
  intro p hp
  simp only [acctMutBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨by simp [ptxBufs], by decide⟩
  · exact ⟨by simp [ptxBufs], by decide⟩
  · exact ⟨by simp [ptxBufs], by decide⟩
  · exact ⟨by simp [ptxBufs], by decide⟩

private theorem acctMut_globals_sub : ∀ g ∈ ["heap_ptr", "journal_n", "scratch_ptr"], g ∈ ptxGlobals := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> decide

private theorem ptxKeep_not_acctMut_global :
    ∀ rec ∈ ptxKeep, ∀ off ∈ rec.2,
      ofString rec.1 ∉ (["heap_ptr", "journal_n", "scratch_ptr"] : List String).map ofString := by
  intro rec hrec off hoff hm
  have hni : ofString rec.1 ∉ ptxGlobals.map ofString := by
    simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
    rcases hrec with rfl | rfl | rfl | rfl
    · decide
    · decide
    · simp at hoff
    · decide
  obtain ⟨g, hg, he⟩ := List.mem_map.1 hm
  exact hni (List.mem_map.2 ⟨g, acctMut_globals_sub g hg, he⟩)

private def noReturnProg : ProgHOL 64 → Bool
  | .return _ => false
  | .seq first second => noReturnProg first && noReturnProg second
  | .ite _ yes no => noReturnProg yes && noReturnProg no
  | .dec _ _ _ body => noReturnProg body
  | .decCall _ _ _ _ cont => noReturnProg cont
  | .while _ body => noReturnProg body
  | .skip | .assign _ _ _ | .primitive _ _ _ | .store _ _ | .storeByte _ _ | .store32 _ _
  | .break | .continue | .raise _ _ | .annot _ _ | .call (some (_, none)) _ _ => true
  | _ => false

private theorem evaluate_noReturnProg {F : Type} (p : ProgHOL 64) (hp : noReturnProg p = true)
    (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s p).1 ≠ some (.returned v) := by
  cases hshape : p with
  | «return» _ => simp [hshape, noReturnProg] at hp
  | seq a b =>
    have hab : noReturnProg a = true ∧ noReturnProg b = true := by
      simpa only [hshape, noReturnProg, Bool.and_eq_true] using hp
    have hrem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noReturnProg a hab.1 s v
    cases hra : evaluateHOLFiniteState s a with
    | mk r1 mid =>
      rw [hra] at ha hrem
      cases r1 with
      | none => exact evaluate_noReturnProg b hab.2 mid v
      | some _ => exact ha
  | ite c yes no =>
    have hy : noReturnProg yes = true ∧ noReturnProg no = true := by
      simpa only [hshape, noReturnProg, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noReturnProg no hy.2 s v
      · exact evaluate_noReturnProg yes hy.1 s v
    · simp
  | dec nm sh init body =>
    have hb : noReturnProg body = true := by simpa only [hshape, noReturnProg] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_noReturnProg body hb _ v
      · simp
  | decCall nm sh fn args cont =>
    have hc : noReturnProg cont = true := by simpa only [hshape, noReturnProg] using hp
    rw [evaluateHOLFiniteState_decCall_total]
    cases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
    | none => simp
    | some vs =>
      dsimp only
      cases hlk : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fn vs with
      | none => simp
      | some inst =>
        obtain ⟨bbody, blocals, brs⟩ := inst
        dsimp only
        split
        · simp
        · have hrem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s blocals) bbody
          cases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s blocals) bbody with
          | mk r1 bpost =>
            rw [hb] at hrem
            have hfix : fixClockHOLFinite (callEntryStateHOLFinite s blocals) (r1, bpost) = (r1, bpost) := by
              simp [fixClockHOLFinite, Nat.not_lt.mpr hrem]
            rw [hfix]
            dsimp only
            rcases r1 with _ | (_ | _ | _ | _ | rv | _ | _)
            all_goals try (simp; done)
            simp only []
            split
            · have hclk_lt : (setVarHOLFinite nm rv {bpost with locals := s.locals}).clock < s.clock := by
                change bpost.clock < s.clock
                change bpost.clock ≤ s.clock - 1 at hrem
                omega
              exact evaluate_noReturnProg cont hc _ v
            · simp
  | «while» cond body =>
    have hb : noReturnProg body = true := by simpa only [hshape, noReturnProg] using hp
    intro hret
    rw [evaluateHOLFiniteState_while_total] at hret
    split at hret
    · split at hret
      · split at hret
        · simp at hret
        · dsimp only at hret
          rw [fixClockHOLFinite_evaluateState] at hret
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          cases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with
          | mk r1 mid =>
            rw [hbr] at hret hrem
            have hclk_lt : mid.clock < s.clock := by
              change mid.clock ≤ s.clock - 1 at hrem
              omega
            cases r1 with
            | none => exact evaluate_noReturnProg (.while cond body) (by simpa [noReturnProg] using hb) mid v hret
            | some r1' =>
              cases r1' with
              | «continue» =>
                exact evaluate_noReturnProg (.while cond body) (by simpa [noReturnProg] using hb) mid v hret
              | «break» => simp at hret
              | returned rv =>
                have hno := evaluate_noReturnProg body hb (decClockHOLFinite s) rv
                rw [hbr] at hno
                exact hno rfl
              | _ => simp at hret
      · simp at hret
    · simp at hret
  | skip => simp [evaluateHOLFiniteState_skip]
  | «break» => simp [evaluateHOLFiniteState_break]
  | «continue» => simp [evaluateHOLFiniteState_continue]
  | annot _ _ => simp [evaluateHOLFiniteState_annot]
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]; split
    · dsimp only; split <;> simp
    · simp
  | assign _ _ _ => rw [evaluateHOLFiniteState_assign]; repeat' first | split | simp
  | primitive _ _ _ => rw [evaluateHOLFiniteState_primitive]; repeat' first | split | simp
  | store d val => rcases (PanRunBounded.evaluate_store_control_frame s d val).1 with h | h <;> (rw [h]; simp)
  | storeByte d val => rcases (PanRunBounded.evaluate_storeByte_control_frame s d val).1 with h | h <;> (rw [h]; simp)
  | store32 _ _ => rw [evaluateHOLFiniteState_store32]; repeat' first | split | simp
  | call info fn args =>
    rcases info with _ | ⟨dest, _ | _⟩
    · simp [hshape, noReturnProg] at hp
    · rw [evaluateHOLFiniteState_call]
      repeat' first | split | simp_all
    · simp [hshape, noReturnProg] at hp
  | _ => simp [hshape, noReturnProg] at hp
termination_by (s.clock, sizeOf p)
decreasing_by all_goals (simp_all [decClockHOLFinite, setVarHOLFinite]; omega)

def PtxLogsAndSlices : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun e r p S Nd => RetTransactionLogs e r p S Nd ∧ PtxRetSlices e r p S Nd

def PtxRelRunStrong {F : Type} (entry : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) (s : PanSemStateFiniteExact 64 F) : Prop :=
  Resumes (evaluateHOLFiniteState s p).1 →
    WorldStep ptxRegions ptxGlobals ptxKeep PtxLogsAndSlices entry
      (evaluateHOLFiniteState s p).1 (evaluateHOLFiniteState s p).2

def PtxRelCutStrong (phase : ProgHOL 64 → ProgHOL 64)
    (A B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop) : Prop :=
  ∀ {F : Type} (entry : PanSemStateFiniteExact 64 F) (tail : ProgHOL 64),
    (∀ s : PanSemStateFiniteExact 64 F, s.code = originalRuntimeCode →
      B entry s → PtxRelRunStrong entry tail s) →
    ∀ s : PanSemStateFiniteExact 64 F, s.code = originalRuntimeCode →
      A entry s → PtxRelRunStrong entry (phase tail) s

theorem ptxRelRun_of_strong {F : Type} {entry s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    (h : PtxRelRunStrong entry p s) : PtxRelRun entry p s := by
  intro hres
  have hs := h hres
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, fun S Nd hW hD => by
    obtain ⟨S', Nd', hsub, hWT, hOG, hFO, hQ⟩ := hs.2.2.2.2 S Nd hW hD
    exact ⟨S', Nd', hsub, hWT, hOG, hFO, hQ.1⟩⟩

private theorem ptxWorldStep_strong_with_locals_right {F : Type}
    {entry post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (h : WorldStep ptxRegions ptxGlobals ptxKeep PtxLogsAndSlices entry r post) :
    WorldStep ptxRegions ptxGlobals ptxKeep PtxLogsAndSlices entry r { post with locals := L, clock := k } :=
  WkBal.worldStep_with_locals_right L k
    (fun _ _ hQ =>
      ⟨retTransactionLogs_congr_memory_heap_bo_ptx rfl rfl rfl rfl hQ.1,
        ptxRetSlices_congr_memory_heap_bo rfl rfl rfl rfl hQ.2⟩) h

private theorem ptxCleanupBody_avoids_out : avoidsLocal (ofString "out") ptxCleanupBody = true := by
  unfold ptxCleanupBody
  decide

theorem ptxPhase5Cleanup_cut_strong
    (hbo : ∀ {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)},
      WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
        s r post → PtxBlockOutUnhit s post) :
    PtxRelCutStrong ptxPhase5Cleanup PtxAfterPhase4 PtxAfterPhase4 := by
  intro F entry tail htail s hc hA hres
  obtain ⟨hready, s_pmc, w_out, hd⟩ := hA
  rw [ptxPhase5Cleanup_eq] at hres ⊢
  obtain ⟨vdel, hev, hres1, heqr, heqp⟩ := dec_word_resumes_step hres
  set s1 := setVarHOLFinite (ofString "del") vdel s
  have hd1 : PtxAfterPhase4Data entry s1 s_pmc w_out :=
    ptxAfterPhase4Data_setVar hd _ _ (by decide) (by decide)
  have hA1 : PtxAfterPhase4 entry s1 := ⟨hready, s_pmc, w_out, hd1⟩
  have hB := validBufList_acctMutBufs
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s1 ptxCleanupBody).1
  have hno_ret := evaluate_noReturnProg ptxCleanupBody (by unfold ptxCleanupBody; decide) s1
  rw [evaluateHOLFiniteState_seq_line780] at hres1
  rcases hr1 : evaluateHOLFiniteState s1 ptxCleanupBody with ⟨r1, mid⟩
  simp only [hr1] at hmeta hno_ret
  rw [hr1] at hres1
  have hW1 : WorldOK s1 := localsFree_worldOK s _ s.clock hd.world
  have hi1 : WordLocal (ofString "i") s1 := hd1.index_word
  cases r1 with
  | none =>
    dsimp only at hres1
    have hs1 := ptxCleanupBody_step s1 hc hW1 (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at hs1; dsimp only at hs1
    have houtm : mid.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
      have h := evaluate_avoidsLocal_flowing (ofString "out") ptxCleanupBody ptxCleanupBody_avoids_out s1
        (by rw [hr1]; exact Or.inl rfl)
      rw [hr1] at h
      simpa only [hd1.out_local] using h
    have him : ∃ w : BitVec 64, mid.locals.lookup (ofString "i") = some (.val (.word w)) := by
      have h := evaluate_wordLocal (ofString "i") ptxCleanupBody (by unfold ptxCleanupBody; decide) s1 hi1
        (by rw [hr1]; exact Or.inl rfl)
      unfold WordLocal at h
      simpa only [hr1] using h
    have hdata_mid : PtxAfterPhase4Data entry mid s_pmc w_out :=
      ptxAfterPhase4Data_step_of_blockOutUnhit hd1 hready hB acctMut_sub_ptx acctMut_globals_sub
        (by decide) (by decide) (by decide) (by simp [stdKeep]) ptxKeepSub_stdKeep
        hs1 (hbo hs1) houtm him
    have hmid := htail mid (hmeta.trans hc) ⟨hready, s_pmc, w_out, hdata_mid⟩ hres1
    have hseq : evaluateHOLFiniteState s1 (.seq ptxCleanupBody tail) = evaluateHOLFiniteState mid tail := by
      rw [evaluateHOLFiniteState_seq_line780, hr1]
    rw [heqr, heqp, hseq]
    exact ptxWorldStep_strong_with_locals_right
      (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid tail).2.locals
        (ofString "del", s.locals.lookup (ofString "del")))
      (evaluateHOLFiniteState mid tail).2.clock hmid
  | some r =>
    dsimp only at hres1
    have hseq : evaluateHOLFiniteState s1 (.seq ptxCleanupBody tail) = (some r, mid) := by
      rw [evaluateHOLFiniteState_seq_line780, hr1]
    have hnt : (some r : Option (PanSemResultExact 64)) ≠ some .timeOut := by
      intro ht; cases ht; rcases hres1 with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    have hfr : FlowingOrResumes (some r) := Or.inr (Or.inr (Or.inr hres1))
    have hs1 := ptxCleanupBody_step s1 hc hW1 (by rw [hr1]; exact hnt) (by rw [hr1]; exact hfr)
    rw [hr1] at hs1
    have hex : WorldStep ptxRegions ptxGlobals ptxKeep PtxLogsAndSlices entry (some r) mid := by
      cases r with
      | exception eid ev =>
        exact ptxAfterPhase4_exception_worldStep hA1 hB acctMut_sub_ptx acctMut_globals_sub
          (by decide) ptxKeepSub_stdKeep ptxKeep_not_acctMut_global hs1
      | returned v => exact False.elim (hno_ret v rfl)
      | timeOut => exact False.elim (hnt rfl)
      | error => rcases hres1 with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | «break» => rcases hres1 with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | «continue» => rcases hres1 with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | finalFfi ev => rcases hres1 with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    rw [heqr, heqp, hseq]
    exact ptxWorldStep_strong_with_locals_right
      (HolFiniteMapExact.resVarEq mid.locals (ofString "del", s.locals.lookup (ofString "del")))
      mid.clock hex

theorem ptxPhase5Cleanup_cut
    (hbo : ∀ {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)},
      WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
        s r post → PtxBlockOutUnhit s post) :
    PtxRelCut ptxPhase5Cleanup PtxAfterPhase4 PtxAfterPhase4 := by
  intro F entry tail htail s hc hA hres
  obtain ⟨hready, s_pmc, w_out, hd⟩ := hA
  rw [ptxPhase5Cleanup_eq] at hres ⊢
  obtain ⟨vdel, hev, hres1, heqr, heqp⟩ := dec_word_resumes_step hres
  set s1 := setVarHOLFinite (ofString "del") vdel s
  have hd1 : PtxAfterPhase4Data entry s1 s_pmc w_out :=
    ptxAfterPhase4Data_setVar hd _ _ (by decide) (by decide)
  have hA1 : PtxAfterPhase4 entry s1 := ⟨hready, s_pmc, w_out, hd1⟩
  have hB := validBufList_acctMutBufs
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s1 ptxCleanupBody).1
  have hno_ret := evaluate_noReturnProg ptxCleanupBody (by unfold ptxCleanupBody; decide) s1
  rw [evaluateHOLFiniteState_seq_line780] at hres1
  rcases hr1 : evaluateHOLFiniteState s1 ptxCleanupBody with ⟨r1, mid⟩
  simp only [hr1] at hmeta hno_ret
  rw [hr1] at hres1
  have hW1 : WorldOK s1 := localsFree_worldOK s _ s.clock hd.world
  have hi1 : WordLocal (ofString "i") s1 := hd1.index_word
  cases r1 with
  | none =>
    dsimp only at hres1
    have hs1 := ptxCleanupBody_step s1 hc hW1 (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at hs1; dsimp only at hs1
    have houtm : mid.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
      have h := evaluate_avoidsLocal_flowing (ofString "out") ptxCleanupBody ptxCleanupBody_avoids_out s1
        (by rw [hr1]; exact Or.inl rfl)
      rw [hr1] at h
      simpa only [hd1.out_local] using h
    have him : ∃ w : BitVec 64, mid.locals.lookup (ofString "i") = some (.val (.word w)) := by
      have h := evaluate_wordLocal (ofString "i") ptxCleanupBody (by unfold ptxCleanupBody; decide) s1 hi1
        (by rw [hr1]; exact Or.inl rfl)
      unfold WordLocal at h
      simpa only [hr1] using h
    have hdata_mid : PtxAfterPhase4Data entry mid s_pmc w_out :=
      ptxAfterPhase4Data_step_of_blockOutUnhit hd1 hready hB acctMut_sub_ptx acctMut_globals_sub
        (by decide) (by decide) (by decide) (by simp [stdKeep]) ptxKeepSub_stdKeep
        hs1 (hbo hs1) houtm him
    have hmid := htail mid (hmeta.trans hc) ⟨hready, s_pmc, w_out, hdata_mid⟩ hres1
    have hseq : evaluateHOLFiniteState s1 (.seq ptxCleanupBody tail) = evaluateHOLFiniteState mid tail := by
      rw [evaluateHOLFiniteState_seq_line780, hr1]
    rw [heqr, heqp, hseq]
    exact WkBal.worldStep_with_locals_right
      (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid tail).2.locals
        (ofString "del", s.locals.lookup (ofString "del")))
      (evaluateHOLFiniteState mid tail).2.clock
      (fun _ _ hQ => retTransactionLogs_congr_memory_heap_bo_ptx rfl rfl rfl rfl hQ) hmid
  | some r =>
    dsimp only at hres1
    have hseq : evaluateHOLFiniteState s1 (.seq ptxCleanupBody tail) = (some r, mid) := by
      rw [evaluateHOLFiniteState_seq_line780, hr1]
    have hnt : (some r : Option (PanSemResultExact 64)) ≠ some .timeOut := by
      intro ht; cases ht; rcases hres1 with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    have hfr : FlowingOrResumes (some r) := Or.inr (Or.inr (Or.inr hres1))
    have hs1 := ptxCleanupBody_step s1 hc hW1 (by rw [hr1]; exact hnt) (by rw [hr1]; exact hfr)
    rw [hr1] at hs1
    have hex : WorldStep ptxRegions ptxGlobals ptxKeep PtxLogsAndSlices entry (some r) mid := by
      cases r with
      | exception eid ev =>
        exact ptxAfterPhase4_exception_worldStep hA1 hB acctMut_sub_ptx acctMut_globals_sub
          (by decide) ptxKeepSub_stdKeep ptxKeep_not_acctMut_global hs1
      | returned v => exact False.elim (hno_ret v rfl)
      | timeOut => exact False.elim (hnt rfl)
      | error => rcases hres1 with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | «break» => rcases hres1 with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | «continue» => rcases hres1 with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | finalFfi ev => rcases hres1 with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    rw [heqr, heqp, hseq]
    have hex1 : WorldStep ptxRegions ptxGlobals ptxKeep RetTransactionLogs entry (some r) mid :=
      ⟨hex.1, hex.2.1, hex.2.2.1, hex.2.2.2.1, fun S Nd hW hD => by
        obtain ⟨S', Nd', hsub, hWT, hOG, hFO, hQ⟩ := hex.2.2.2.2 S Nd hW hD
        exact ⟨S', Nd', hsub, hWT, hOG, hFO, hQ.1⟩⟩
    exact WkBal.worldStep_with_locals_right
      (HolFiniteMapExact.resVarEq mid.locals (ofString "del", s.locals.lookup (ofString "del")))
      mid.clock
      (fun _ _ hQ => retTransactionLogs_congr_memory_heap_bo_ptx rfl rfl rfl rfl hQ) hex1

def ptxIncorpBufs : BufList :=
  [("bal_key_buf", 64), ("keccak_pad", 136), ("keccak_st", 200),
   ("mpt_nib_scratch", 64), ("sk_buf", 52)]

def ptxIncorpGlobals : List String := ["heap_ptr", "journal_n", "scratch_ptr", "ts"]

def ptxIncorpKeep : List (String × List Nat) :=
  [("ws", [0, 8, 16, 24, 32]),
   ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", []),
   ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]

private theorem validBufList_ptxIncorpBufs : ValidBufList ptxIncorpBufs := by
  intro p hp
  simp only [ptxIncorpBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact ⟨64, by decide, by decide, le_rfl⟩
  · exact ⟨136, by decide, by decide, le_rfl⟩
  · exact ⟨200, by decide, by decide, le_rfl⟩
  · exact ⟨64, by decide, by decide, le_rfl⟩
  · exact ⟨64, by decide, by decide, by decide⟩

private theorem ptxIncorpBufs_sub_ptx : ∀ p ∈ ptxIncorpBufs, p ∈ ptxBufs ∧ p.1 ∉ ptxGlobals := by
  intro p hp
  simp only [ptxIncorpBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by simp [ptxBufs], by decide⟩
  · exact ⟨by simp [ptxBufs], by decide⟩
  · exact ⟨by simp [ptxBufs], by decide⟩
  · exact ⟨by simp [ptxBufs], by decide⟩
  · exact ⟨by simp [ptxBufs], by decide⟩

private theorem ptxIncorpGlobals_sub_ptx : ∀ g ∈ ptxIncorpGlobals, g ∈ ptxGlobals := by
  intro g hg
  simp only [ptxIncorpGlobals, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> decide

private theorem ptxKeepSub_ptxIncorpKeep : PtxKeepSub ptxIncorpKeep := by
  intro rec hr
  simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨[0, 8, 16, 24, 32], by simp [ptxIncorpKeep], fun _ hk => hk⟩
  · exact ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64, 72], by simp [ptxIncorpKeep], by
      intro k hk; simp at hk ⊢; omega⟩
  · exact ⟨[], by simp [ptxIncorpKeep], fun _ hk => hk⟩
  · exact ⟨[0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80], by simp [ptxIncorpKeep], by
      intro k hk; simp at hk ⊢; omega⟩

private theorem ptxKeep_not_ptxIncorpGlobal :
    ∀ rec ∈ ptxKeep, ∀ off ∈ rec.2,
      ofString rec.1 ∉ ptxIncorpGlobals.map ofString := by
  intro rec hrec off hoff hm
  have hni : ofString rec.1 ∉ ptxGlobals.map ofString := by
    simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
    rcases hrec with rfl | rfl | rfl | rfl
    · decide
    · decide
    · simp at hoff
    · decide
  obtain ⟨g, hg, he⟩ := List.mem_map.1 hm
  exact hni (List.mem_map.2 ⟨g, ptxIncorpGlobals_sub_ptx g hg, he⟩)

private theorem call0_worldStepSc_keep {F : Type}
    {B : BufList} {gw : List String} {keep : List (String × List Nat)}
    {fname : MlS} {args : List (ExpHOL 64)}
    (hf : WorldKeepsSc WorldOK (bufRegions B) gw keep NoExtra fname)
    (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1) :
    WorldStepSc (bufRegions B) gw keep NoExtra
      s (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1
      (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2 := by
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
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
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
        simp only [ent] at hrun
        simp only [hrun] at hnt hfr ⊢
        have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro rfl; simp at hnt
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hfr ⊢
            split
            · have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
              simp only [ent, hrun] at hspec
              exact (hspec (Or.inl ⟨v, rfl⟩)).from_entry
            · rename_i hbad; simp [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
            simp only [ent, hrun] at hspec
            exact (hspec hres_ex).from_entry

theorem ptxPhase5Incorporate_step_strong
    (hinc : WorldKeepsSc WorldOK (bufRegions ptxIncorpBufs) ptxIncorpGlobals ptxIncorpKeep NoExtra
      (ofString "incorporate_tx_into_block"))
    (hbo_inc : ∀ {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)},
      WorldStepSc (bufRegions ptxIncorpBufs) ptxIncorpGlobals ptxIncorpKeep NoExtra s r post →
        PtxBlockOutUnhit s post)
    {F : Type} (entry s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hA : PtxAfterPhase4 entry s) :
    ((evaluateHOLFiniteState s ptxPhase5Incorporate).1 = none →
      PtxAfterPhase4 entry (evaluateHOLFiniteState s ptxPhase5Incorporate).2) ∧
    PtxRelRunStrong entry ptxPhase5Incorporate s := by
  obtain ⟨hready, s_pmc, w_out, hd⟩ := hA
  constructor
  · intro hnone
    have hs := call0_worldStepSc_keep hinc s hc hd.world
      (by rw [ptxPhase5Incorporate] at hnone; rw [hnone]; simp)
      (by rw [ptxPhase5Incorporate] at hnone; rw [hnone]; exact Or.inl rfl)
    change WorldStepSc _ _ _ _ s (evaluateHOLFiniteState s ptxPhase5Incorporate).1
      (evaluateHOLFiniteState s ptxPhase5Incorporate).2 at hs
    have hout_eq : (evaluateHOLFiniteState s ptxPhase5Incorporate).2.locals.lookup (ofString "out") =
        some (.val (.word w_out)) := by
      have h := evaluate_avoidsLocal_flowing (ofString "out") ptxPhase5Incorporate
        (by unfold ptxPhase5Incorporate; decide) s (Or.inl hnone)
      simpa only [hd.out_local] using h
    have hi_w : ∃ w : BitVec 64, (evaluateHOLFiniteState s ptxPhase5Incorporate).2.locals.lookup (ofString "i") =
        some (.val (.word w)) := by
      have h := evaluate_wordLocal (ofString "i") ptxPhase5Incorporate
        (by unfold ptxPhase5Incorporate; decide) s hd.index_word (Or.inl hnone)
      exact h
    exact ⟨hready, s_pmc, w_out,
      ptxAfterPhase4Data_step_of_blockOutUnhit hd hready validBufList_ptxIncorpBufs
        ptxIncorpBufs_sub_ptx ptxIncorpGlobals_sub_ptx
        (by decide) (by decide) (by decide) (by simp [ptxIncorpKeep]) ptxKeepSub_ptxIncorpKeep
        hs (hbo_inc hs) hout_eq hi_w⟩
  · intro hres
    have hno_ret := evaluate_noReturnProg ptxPhase5Incorporate (by unfold ptxPhase5Incorporate; decide) s
    rcases hr : evaluateHOLFiniteState s ptxPhase5Incorporate with ⟨r, post⟩
    rw [hr] at hres hno_ret
    dsimp only at hres hno_ret ⊢
    have hnt : r ≠ some .timeOut := by
      intro ht; subst ht; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    have hs := call0_worldStepSc_keep hinc s hc hd.world
      (by change (evaluateHOLFiniteState s ptxPhase5Incorporate).1 ≠ _; rw [hr]; exact hnt)
      (by change FlowingOrResumes (evaluateHOLFiniteState s ptxPhase5Incorporate).1; rw [hr]; exact Or.inr (Or.inr (Or.inr hres)))
    change WorldStepSc _ _ _ _ s (evaluateHOLFiniteState s ptxPhase5Incorporate).1
      (evaluateHOLFiniteState s ptxPhase5Incorporate).2 at hs
    rw [hr] at hs
    rcases hres with ⟨v, hv⟩ | ⟨eid, ev, hex_eq, _⟩
    · exact False.elim (hno_ret v hv)
    · subst hex_eq
      exact ptxAfterPhase4_exception_worldStep ⟨hready, s_pmc, w_out, hd⟩
        validBufList_ptxIncorpBufs ptxIncorpBufs_sub_ptx ptxIncorpGlobals_sub_ptx
        (by decide) ptxKeepSub_ptxIncorpKeep ptxKeep_not_ptxIncorpGlobal hs

theorem ptxRelRunStrong_seq_of_cut {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {p1 tail : ProgHOL 64}
    {B : PanSemStateFiniteExact 64 F → Prop}
    (hc : s.code = originalRuntimeCode)
    (hfall : (evaluateHOLFiniteState s p1).1 = none →
      B (evaluateHOLFiniteState s p1).2)
    (hstop : PtxRelRunStrong entry p1 s)
    (htail : ∀ mid : PanSemStateFiniteExact 64 F,
      mid.code = originalRuntimeCode → B mid → PtxRelRunStrong entry tail mid) :
    PtxRelRunStrong entry (.seq p1 tail) s := by
  intro hres
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s p1).1
  rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
  rcases he : evaluateHOLFiniteState s p1 with ⟨r, mid⟩
  simp only [he] at hmeta hres ⊢
  cases r with
  | none =>
    have hB : B mid := by
      have hb := hfall (by rw [he])
      simpa only [he] using hb
    exact htail mid (hmeta.trans hc) hB hres
  | some r =>
    have hs := hstop (by simpa only [he] using hres)
    simpa only [he] using hs

theorem ptxAfterPhase4_phase5_relRun_strong
    (hbo_clean : ∀ {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)},
      WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
        s r post → PtxBlockOutUnhit s post)
    (hinc : WorldKeepsSc WorldOK (bufRegions ptxIncorpBufs) ptxIncorpGlobals ptxIncorpKeep NoExtra
      (ofString "incorporate_tx_into_block"))
    (hbo_inc : ∀ {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)},
      WorldStepSc (bufRegions ptxIncorpBufs) ptxIncorpGlobals ptxIncorpKeep NoExtra s r post →
        PtxBlockOutUnhit s post)
    {F : Type} (entry s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (h : PtxAfterPhase4 entry s) :
    PtxRelRunStrong entry R13Shards.ptxPhase5 s := by
  rw [ptxPhase5_eq_cleanup_incorporate_release]
  apply ptxPhase5Cleanup_cut_strong hbo_clean entry _ _ s hc h
  intro mid hcode hdata
  obtain ⟨hfall, hstop⟩ := ptxPhase5Incorporate_step_strong hinc hbo_inc entry mid hcode hdata
  exact ptxRelRunStrong_seq_of_cut hcode hfall hstop
    (fun _ hc2 hd2 hres => ptxAfterPhase4_release_return_logs_slices hc2 hd2 hres)

theorem ptxAfterPhase4_phase5_relRun
    (hbo_clean : ∀ {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)},
      WorldStepSc (bufRegions acctMutBufs) ["heap_ptr", "journal_n", "scratch_ptr"] stdKeep NoExtra
        s r post → PtxBlockOutUnhit s post)
    (hinc : WorldKeepsSc WorldOK (bufRegions ptxIncorpBufs) ptxIncorpGlobals ptxIncorpKeep NoExtra
      (ofString "incorporate_tx_into_block"))
    (hbo_inc : ∀ {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)},
      WorldStepSc (bufRegions ptxIncorpBufs) ptxIncorpGlobals ptxIncorpKeep NoExtra s r post →
        PtxBlockOutUnhit s post)
    {F : Type} (entry s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (h : PtxAfterPhase4 entry s) :
    PtxRelRun entry R13Shards.ptxPhase5 s :=
  ptxRelRun_of_strong (ptxAfterPhase4_phase5_relRun_strong hbo_clean hinc hbo_inc entry s hc h)

theorem wk_process_transaction_strong_of
    (A0 A1 A2 A3 A4 : ∀ {F : Type},
      PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop)
    (hinit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), TxReadyStrong s → A0 s s)
    (h1 : PtxRelCutStrong R13Shards.ptxPhase1 A0 A1)
    (h2 : PtxRelCutStrong R13Shards.ptxPhase2 A1 A2)
    (h3 : PtxRelCutStrong R13Shards.ptxPhase3 A2 A3)
    (h4 : PtxRelCutStrong R13Shards.ptxPhase4 A3 A4)
    (h5 : ∀ {F : Type} (entry s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → A4 entry s → PtxRelRunStrong entry R13Shards.ptxPhase5 s) :
    WorldKeeps TxReadyStrong
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]
      (fun s r post S Nd => RetTransactionLogs s r post S Nd ∧ PtxRetSlices s r post S Nd)
      (ofString "process_transaction") := by
  refine ⟨_, _, _, R13Shards.ptx_lookup, ?_⟩
  intro F s hcode hready _hparams _hnt
  have hb := h1 s _ (h2 s _ (h3 s _ (h4 s _ (h5 s)))) s hcode (hinit s hready)
  rw [← R13Shards.ptx_phases_eq] at hb
  unfold PtxRelRunStrong PtxLogsAndSlices R13Shards.ptxCode ptxRegions ptxGlobals ptxKeep at hb
  exact hb

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
