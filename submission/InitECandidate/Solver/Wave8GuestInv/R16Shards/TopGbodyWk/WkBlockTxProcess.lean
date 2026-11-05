import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.WkGetAccount
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.U256DivWs
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.U256WsSpecs
import InitECandidate.Solver.Wave8GuestInv.R10Ports.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_min
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_sub
import InitECandidate.Solver.Wave8GuestInv.R13Shards.PtxPhase45R11

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
    (worldKeepsSc_of_readOnly R10Ports.ro_calculate_total_blob_gas) ?_ -- tx_blob_gas
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
  · refine progWStep_decCall hB hgw hB0 hgw0 (worldKeepsSc_of_readOnly R10Ports.ro_fee_mul) ?_
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
      refine progWStep_decCall hB hgw hB0 hgw0 (worldKeepsSc_of_readOnly R10Ports.ro_fee_mul) ?_
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

def RetFrameResultStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S Nd => RetFrameResult s r post S Nd ∧
    ∀ v, r = some (.returned v) → ∃ w : BitVec 64,
      v = .val (.word w) ∧
      IvlsDisj [(w.toNat, 280)] (worldOwned post S Nd) ∧
      PmcLogsLiveOwned post S Nd (memW post (w.toNat + 88))

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
  obtain ⟨w', hw', _, howned⟩ := h.2 v hr
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

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
