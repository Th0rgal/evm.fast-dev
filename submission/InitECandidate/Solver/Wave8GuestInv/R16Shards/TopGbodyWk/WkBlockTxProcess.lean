import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.WkGetAccount
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.U256DivWs
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.U256WsSpecs
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_calculate_total_blob_gas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_fee_mul
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_min
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_sub
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.wk_memzero
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M29.zv_memzero
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01AllocMpt
import InitECandidate.Solver.Wave8GuestInv.R13Shards.PtxPhase45R11
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PayloadWorldHelpers

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

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
