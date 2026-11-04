import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.U256DivWs
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.U256WsSpecs

/-!
# R16j `wk_calculate_blob_gas_price`

Complete proof of `wk_calculate_blob_gas_price` (`ContractParts/C08.lean`),
showing `u256_div`, `taylor_exponential`, and `calculate_blob_gas_price` only touch
`[(globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)]` on resuming paths.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers

/-! ## Section 1: Lookups and `WsSafe` combinators for `u256_div` and `taylor_exponential` -/

private theorem lookup_u256_div :
    originalRuntimeCode.lookup (ofString "u256_div") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]),
             (ofString "b", .comb [.one, .one, .one, .one])],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_u256_div).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 70 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_div) rfl

private theorem lookup_taylor_exponential :
    originalRuntimeCode.lookup (ofString "taylor_exponential") =
      some ([(ofString "factor", .one), (ofString "numerator", .one), (ofString "denominator", .one)],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_taylor_exponential).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 232 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_taylor_exponential) rfl

private theorem lookup_calculate_blob_gas_price :
    originalRuntimeCode.lookup (ofString "calculate_blob_gas_price") =
      some ([(ofString "excess_blob_gas", .one)],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_calculate_blob_gas_price).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 233 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_calculate_blob_gas_price) rfl

private theorem lookup_two_comb4_b {fname : MlS} {body0 : ProgHOL 64} {retSh : ShapeHOL}
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

private theorem call_u256_divmod_wsSafe' {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "u256_divmod") vals = some (body, callee, rs)) :
    WsSafe (callEntryStateHOLFinite s callee) (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body) := by
  rw [he.code] at hl
  obtain ⟨rfl, ⟨b0, b1, b2, b3, hb_c⟩⟩ := lookup_two_comb4_b lookup_u256_divmod hl
  exact u256_divmod_wsSafe (he.with_locals_clock callee _) hb_c

private theorem call_u256_div_wsSafe' {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "u256_div") vals = some (body, callee, rs)) :
    WsSafe (callEntryStateHOLFinite s callee) (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body) := by
  rw [he.code] at hl
  obtain ⟨rfl, _⟩ := lookup_two_comb4_b lookup_u256_div hl
  dsimp only [extractFn, Guest.Software.guestFn_u256_div,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map]
  refine WsSafe.decCall ?_ ?_
  · intro vals' body' callee' rs' _ hl' _
    exact call_u256_divmod_wsSafe' (he.with_locals_clock callee _) hl'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _
    exact WsSafe.return_exp _ _ _

private theorem wsSafe_call_local {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
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

private theorem WsSafe_while_wsEnv {F : Type} {cond : ExpHOL 64} {body : ProgHOL 64}
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

private theorem wsEnv_setVar {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) (nm : MlS) (v : ValueHOL 64) :
    WsEnv s0 (setVarHOLFinite nm v s) :=
  ⟨he.code, he.memaddrs, he.globals, he.ws_bnd⟩

private theorem taylor_exponential_wsSafe {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
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
  have he4a := wsEnv_setVar he4 (ofString "out") v_out
  refine WsSafe.dec fun v_i _ _ => ?_
  have he4b := wsEnv_setVar he4a (ofString "i") v_i
  refine WsSafe.dec fun v_zero _ _ => ?_
  have he5 := wsEnv_setVar he4b (ofString "zero") v_zero
  refine WsSafe.decCall_ro he5 (by decide) fun _ _ he6 _ _ => ?_
  refine WsSafe.seq (WsSafe_while_wsEnv (by decide) he6 fun t ht => ?_) ?_
  · refine WsSafe.seq (WsSafe.of_readOnly ht.code (by decide)) fun _ heff_a => ?_
    have ht1 := ht.step heff_a
    refine WsSafe.decCall_ro ht1 (by decide) fun _ _ ht2 _ _ => ?_
    refine WsSafe.seq (WsSafe.of_readOnly ht2.code (by decide)) fun _ heff_t => ?_
    have ht3 := ht2.step heff_t
    refine WsSafe.dec fun v_p _ _ => ?_
    have ht4 := wsEnv_setVar ht3 (ofString "p") v_p
    refine WsSafe.decCall_ro ht4 (by decide) fun _ _ ht5 _ _ => ?_
    refine WsSafe.seq (WsSafe.of_readOnly ht5.code (by decide)) fun _ heff_dm => ?_
    have ht6 := ht5.step heff_dm
    refine WsSafe.seq (wsSafe_call_local fun _ _ _ _ _ hl _ => call_u256_div_wsSafe' ht6 hl)
      fun _ heff_dv => ?_
    have ht7 := ht6.step heff_dv
    refine WsSafe.seq (WsSafe.assign_local _ _ _ _) fun _ heff_inc => ?_
    have ht8 := ht7.step heff_inc
    exact WsSafe.of_readOnly ht8.code (by decide)
  · intro _ heff_w
    have he7 := he6.step heff_w
    refine WsSafe.seq (wsSafe_call_local fun _ _ _ _ _ hl _ => call_u256_div_wsSafe' he7 hl)
      fun _ _ => ?_
    exact WsSafe.return_exp _ _ _

/-! ## Section 2: Lifting `M23.ByteRegionEffect` on `untypedGlobalBufIvls` to `WorldStep` -/

private theorem wsEnv_of_worldOK {F : Type} {s : PanSemStateFiniteExact 64 F}
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
    · have hhl : heapLimit ≤ 2 ^ 64 := by rw [heapLimit_val]; decide
      have hse : scratchEnd ≤ 2 ^ 64 := by rw [scratchEnd_val]; decide
      obtain ⟨_, hhp_hi, _, hfp_sp, _⟩ := hAR.2
      rcases hal with ⟨_, hhi⟩ | ⟨_, hhi⟩ <;> (dsimp only at hhi; exact Or.inr (by omega))

private theorem heapByteEff_of_m23_bre {F : Type} {s post : PanSemStateFiniteExact 64 F}
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
    have ha_ord := (ordinaryDomain_iff a).1 hdom
    have hhe_lt : heapEnd ≤ 2 ^ 64 := by rw [heapEnd_val]; decide
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

private theorem resumes_to_m23 {r : Option (PanSemResultExact 64)} (hr : Resumes r) :
    Wave8Contracts.M23.Resumes r :=
  hr

/-! ## Section 3: `wk_calculate_blob_gas_price` -/

theorem «wk_calculate_blob_gas_price» :
    WorldKeeps WorldOK (fun s => [(globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "calculate_blob_gas_price") := by
  refine ⟨_, _, _, lookup_calculate_blob_gas_price, fun {F} s hcode hW _ _ hres => ?_⟩
  have he0 : WsEnv s s := wsEnv_of_worldOK hcode hW
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
      simp only [lookupCodeHOLExact, lookup_taylor_exponential, List.length] at hraw
      rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩
      · simp at hraw
      · simp at hraw
      · simp at hraw
      · simp only [List.length, ↓reduceIte] at hraw
        split at hraw
        · have hb : body = _ := (Prod.mk.inj (Option.some.inj hraw)).1.symm
          subst hb
          exact taylor_exponential_wsSafe (he0.with_locals_clock callee _)
        · simp at hraw
      · simp [List.length] at hraw
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _
      exact WsSafe.return_exp _ _ _
  have heff_m23 := hsafe.2 (resumes_to_m23 hres)
  have heff_hb : HeapByteEff s
      (evaluateHOLFiniteState s
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
          (extractFn Guest.Software.guestFn_calculate_blob_gas_price).body)).2
      ([(globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)] ++
       [("sk_buf", 64), ("keccak_pad", 136), ("keccak_st", 200), ("mpt_nib_scratch", 64)].map (bufferRegion s)) [] :=
    heapByteEff_of_m23_bre hW.1 heff_m23
  exact HeapByteEff.to_worldStep
    [("sk_buf", 64), ("keccak_pad", 136), ("keccak_st", 200), ("mpt_nib_scratch", 64)]
    (by decide) (by simp) hW heff_hb (fun _ _ _ _ _ => trivial)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
