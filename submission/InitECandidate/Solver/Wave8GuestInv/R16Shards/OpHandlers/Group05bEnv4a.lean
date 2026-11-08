import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.U256WsSpecs

/-! # OpHandlerSpec Group 05bEnv4a (`OpHandlers-A`): `taylor_exponential_wsSafe` -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8Contracts.M23

private theorem WsSafe.call_local {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
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
        have he_ce : ByteRegionEffect s (callEntryStateHOLFinite s callee) Rl :=
          (ByteRegionEffect.refl s Rl).with_locals_clock callee (s.clock - 1)
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, cpost⟩
        rw [hrun] at hc
        cases rb with
        | none =>
          exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
        | some r0 =>
          cases r0 with
          | returned v =>
            have he_cp : ByteRegionEffect s cpost Rl := he_ce.trans (hc.2 (Or.inl ⟨v, rfl⟩))
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

private theorem WsSafe.decCall_ro' {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {nm : MlS} {sh : ShapeHOL} {fname : MlS}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hfn : opRoCallees fname = true)
    (hcont : ∀ u : PanSemStateFiniteExact 64 F, WsEnv s0 u →
      WsSafe u (untypedGlobalBufIvls s0) (evaluateHOLFiniteState u cont)) :
    WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s (.decCall nm sh fname args cont)) :=
  WsSafe.decCall_ro he hfn fun _ _ hu _ _ => hcont _ hu

private theorem WsSafe.dec_env {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {nm : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hbody : ∀ u : PanSemStateFiniteExact 64 F, WsEnv s0 u →
      WsSafe u (untypedGlobalBufIvls s0) (evaluateHOLFiniteState u body)) :
    WsSafe s (untypedGlobalBufIvls s0) (evaluateHOLFiniteState s (.dec nm sh init body)) :=
  WsSafe.dec fun v _ _ => hbody (setVarHOLFinite nm v s) (he.with_locals_clock _ s.clock)

private theorem lookup_u256_div_local :
    originalRuntimeCode.lookup (ofString "u256_div") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]), (ofString "b", .comb [.one, .one, .one, .one])],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_u256_div).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 70 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_div) rfl

private theorem lookup_two_comb4_b {fname : MlS} {body0 : ProgHOL 64} {rs0 : ShapeHOL}
    (hlook : originalRuntimeCode.lookup fname =
      some ([(ofString "a", .comb [.one, .one, .one, .one]),
             (ofString "b", .comb [.one, .one, .one, .one])], body0, rs0))
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs)) :
    body = body0 ∧ ∃ b0 b1 b2 b3 : BitVec 64,
      callee.lookup (ofString "b") =
        some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)]) := by
  have hraw := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body callee rs hl
  simp only [lookupCodeHOLExact, hlook] at hraw
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
      refine ⟨hb, b0, b1, b2, b3, ?_⟩
      simpa [FUPDATE_LIST, FUPDATE] using congrFun hfn (ofString "b")
    · simp at hraw
  · simp [List.length] at hraw

private theorem call_u256_div_wsSafe {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "u256_div") vals = some (body, callee, rs)) :
    WsSafe (callEntryStateHOLFinite s callee) (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body) := by
  rw [he.code] at hl
  obtain ⟨rfl, _⟩ := lookup_two_comb4_b lookup_u256_div_local hl
  have he_ce := he.with_locals_clock callee (s.clock - 1)
  dsimp only [extractFn, Guest.Software.guestFn_u256_div,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  refine WsSafe.decCall ?_ ?_
  · intro vals' body' callee' rs' _ hl' _
    have hl'_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "u256_divmod") vals' =
        some (body', callee', rs') := by
      simpa [callEntryStateHOLFinite, he.code] using hl'
    obtain ⟨rfl, b0, b1, b2, b3, hb_c⟩ := lookup_two_comb4_b lookup_u256_divmod hl'_orig
    exact u256_divmod_wsSafe (he_ce.with_locals_clock callee' _) hb_c
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _
    exact WsSafe.return_exp _ _ _

private theorem WsSafe.while_wsEnv {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {cond : ExpHOL 64} {body : ProgHOL 64}
    (hnb : noTopBreakContinue body = true)
    (hbody : ∀ t : PanSemStateFiniteExact 64 F, WsEnv s0 t →
      WsSafe t (untypedGlobalBufIvls s0) (evaluateHOLFiniteState t body))
    (s : PanSemStateFiniteExact 64 F) (hs : WsEnv s0 s) :
    WsSafe s (untypedGlobalBufIvls s0) (evaluateHOLFiniteState s (.while cond body)) :=
  WsSafe.while_loop hnb (fun u => WsEnv s0 u)
    (fun u hu => hu.with_locals_clock u.locals (u.clock - 1))
    (fun t _ ht _ _ =>
      let hsb := hbody (decClockHOLFinite t) ht
      ⟨hsb, fun hn => ht.step (hsb.1 hn)⟩)
    s hs

theorem taylor_exponential_wsSafe {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
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
  refine WsSafe.decCall_ro' he rfl fun _ he1 => ?_
  refine WsSafe.decCall_ro' he1 rfl fun _ he2 => ?_
  refine WsSafe.decCall_ro' he2 rfl fun _ he3 => ?_
  refine WsSafe.seq (WsSafe.of_readOnly he3.code rfl) fun _ heff4 => ?_
  refine WsSafe.dec_env (he3.step heff4) fun _ he4a => ?_
  refine WsSafe.dec_env he4a fun _ he4b => ?_
  refine WsSafe.dec_env he4b fun _ he4c => ?_
  refine WsSafe.decCall_ro' he4c rfl fun _ he5 => ?_
  refine WsSafe.seq ?_ ?_
  · refine WsSafe.while_wsEnv rfl (fun _ ht => ?_) _ he5
    refine WsSafe.seq (WsSafe.of_readOnly ht.code rfl) fun _ heff_a => ?_
    refine WsSafe.decCall_ro' (ht.step heff_a) rfl fun _ ht2 => ?_
    refine WsSafe.seq (WsSafe.of_readOnly ht2.code rfl) fun _ heff_b => ?_
    refine WsSafe.dec_env (ht2.step heff_b) fun _ ht3 => ?_
    refine WsSafe.decCall_ro' ht3 rfl fun _ ht4 => ?_
    refine WsSafe.seq (WsSafe.of_readOnly ht4.code rfl) fun _ heff_c => ?_
    have ht5 := ht4.step heff_c
    refine WsSafe.seq (WsSafe.call_local fun _ _ _ _ _ hl _ => call_u256_div_wsSafe ht5 hl)
      fun _ heff_d => ?_
    exact WsSafe.of_readOnly (ht5.step heff_d).code rfl
  · intro _ heff_w
    have he6 := he5.step heff_w
    refine WsSafe.seq (WsSafe.call_local fun _ _ _ _ _ hl _ => call_u256_div_wsSafe he6 hl)
      fun _ _ => WsSafe.return_exp _ _ _

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
