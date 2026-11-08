import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.StackPush
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group05bEnv2

/-! # OpHandlerSpec Group 05bEnv5 (`OpHandlers-A`): `block_env`, combinators, and first 5 block/env opcodes -/

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

theorem eps_block_env :
    EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post) (ofString "block_env") :=
  eps_of_readOnly 550 (by rw [guestAst_len]; decide) Guest.Software.guestFn_block_env rfl
    opRoCallees opRoCallees_good rfl

theorem return_ne_none_env {F : Type} (t : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    (evaluateHOLFiniteState t (.return e)).1 ≠ none := by
  rw [evaluateHOLFiniteState_return]
  split <;> [simp; (split <;> simp)]

theorem seq_ne_none_right_env {F : Type} (t : PanSemStateFiniteExact 64 F) (p q : ProgHOL 64)
    (hq : ∀ u : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState u q).1 ≠ none) :
    (evaluateHOLFiniteState t (.seq p q)).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState t p with ⟨rp, sp⟩
  cases rp with
  | none => exact hq sp
  | some _ => simp

theorem HandlerRun.seq_ite_nonfallthrough_skip {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {cond : ExpHOL 64} {yes cont : ProgHOL 64}
    (hnn : ∀ u : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState u yes).1 ≠ none)
    (hyes : HandlerRun s0 P charged yes)
    (hcont : HandlerRun s0 P charged cont) :
    HandlerRun s0 P charged (.seq (.ite cond yes .skip) cont) := by
  intro t hc hInv hlen hR hP hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split
  · rename_i w hw
    by_cases hw0 : w = 0
    · subst hw0; simp only [↓reduceIte, evaluateHOLFiniteState_skip]
      intro hnt; exact hcont t hc hInv hlen hR hP hnt
    · simp only [hw0, ↓reduceIte]
      have hy_nn := hnn t
      rcases hy : evaluateHOLFiniteState t yes with ⟨ry, sy⟩
      rw [hy] at hy_nn
      cases ry with
      | none => exact absurd rfl hy_nn
      | some r0 =>
        dsimp only; intro hnt
        have hr := hyes t hc hInv hlen hR hP (by rw [hy]; exact hnt)
        rw [hy] at hr; exact hr
  · intro _; exact opDispatchPost_error s0 t

theorem HandlerRun.seq_ite_other_skip {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {cond : ExpHOL 64} {eid : MlS} {errExp : ExpHOL 64} {cont : ProgHOL 64}
    (hne : eid ≠ ofString "EvmErr")
    (hcont : HandlerRun s0 P charged cont) :
    HandlerRun s0 P charged (.seq (.ite cond (.raise eid errExp) .skip) cont) := by
  refine HandlerRun.seq_ite_nonfallthrough_skip ?_ (HandlerRun.raise_other hne errExp) hcont
  intro u
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only; split <;> simp
  · simp

theorem HandlerRun.seq_ite_simple {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {cond : ExpHOL 64} {yes no cont : ProgHOL 64}
    (hyes : HandlerRun s0 (fun _ => True) charged (.seq yes cont))
    (hno : HandlerRun s0 (fun _ => True) charged (.seq no cont)) :
    HandlerRun s0 (fun _ => True) charged (.seq (.ite cond yes no) cont) := by
  intro t hc hInv hlen hR _ hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split
  · rename_i w hw
    by_cases hw0 : w = 0
    · subst hw0; simp only [↓reduceIte]
      rw [← evaluateHOLFiniteState_seq_line780]
      intro hnt; exact hno t hc hInv hlen hR trivial hnt
    · simp only [hw0, ↓reduceIte]
      rw [← evaluateHOLFiniteState_seq_line780]
      intro hnt; exact hyes t hc hInv hlen hR trivial hnt
  · intro _; exact opDispatchPost_error s0 t

private theorem rbound_step_local {charged : Bool} {r1 r2 r0 : Nat}
    (h1 : r2 ≤ r1) (h2 : if charged then r1 < r0 else r1 ≤ r0) :
    if charged then r2 < r0 else r2 ≤ r0 := by
  cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at h2 ⊢ <;> omega

private theorem rbound_to_le_local {charged : Bool} {r1 r0 : Nat}
    (h : if charged then r1 < r0 else r1 ≤ r0) : r1 ≤ r0 := by
  cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at h <;> omega

theorem HandlerRun.seq_decCall_call_simple {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {Q1 Q2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {nm : MlS} {sh : ShapeHOL} {fn1 fn2 : MlS} {args1 args2 : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf1 : EvmPreservingSpec (fun _ => True) Q1 fn1)
    (hf2 : EvmPreservingSpec (fun _ => True) Q2 fn2)
    (hcont : HandlerRun s0 (fun _ => True) charged cont) :
    HandlerRun s0 (fun _ => True) charged
      (.seq (.decCall nm sh fn1 args1 (.call (some (none, none)) fn2 args2)) cont) := by
  intro t hc hInv hlen hR _ hnt
  obtain ⟨params1, body1, ret1, hlook1, hspec1⟩ := hf1
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs1 : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args1 with _ | vals1
  · exact opDispatchPost_error s0 t
  · simp only [hargs1] at hnt ⊢
    rcases hl1 : lookupCodeHOLFinite t.code.lookup fn1 vals1 with _ | ⟨body1', callee1, ret1'⟩
    · exact opDispatchPost_error s0 t
    · simp only [hl1] at hnt ⊢
      by_cases hz1 : t.clock = 0
      · simp [hz1] at hnt
      · simp only [hz1, ↓reduceIte] at hnt ⊢
        have hb1 : body1' = body1 :=
          lookupCodeHOLFinite_installed_body t.code.lookup fn1 params1 body1 body1'
            ret1 ret1' vals1 callee1 (by rw [hc]; exact hlook1) hl1
        subst body1'
        have hr1 : ret1' = ret1 := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            t.code.lookup fn1 vals1 body1 callee1 ret1' hl1
          rw [hc] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook1] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret1'
        have hInv_ce1 : EvmInv (callEntryStateHOLFinite t callee1) :=
          localsFree_evmInv t callee1 (t.clock - 1) hInv
        have hl1_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fn1 vals1 =
            some (body1, callee1, ret1) := by rwa [← hc]
        have hmeta1 := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite t callee1) body1).1
        rcases hrun1 : evaluateHOLFiniteState (callEntryStateHOLFinite t callee1) body1 with ⟨res1, cpost1⟩
        simp only [hrun1] at hnt hmeta1 ⊢
        change cpost1.code = t.code at hmeta1
        have hc_ce1 := evm_congr (s := t) (t := callEntryStateHOLFinite t callee1) rfl rfl
        have hQ1 (hsafe : res1 ≠ some .timeOut) :
            (∀ v, res1 = some (.returned v) →
              EvmInv cpost1 ∧ evmChain cpost1 = evmChain (callEntryStateHOLFinite t callee1) ∧
              evmR cpost1 ≤ evmR (callEntryStateHOLFinite t callee1) ∧
              Q1 (callEntryStateHOLFinite t callee1) v cpost1) ∧
            (IsEvmErr res1 →
              EvmInv cpost1 ∧ evmChain cpost1 = evmChain (callEntryStateHOLFinite t callee1) ∧
              evmR cpost1 ≤ evmR (callEntryStateHOLFinite t callee1)) := by
          have hs := hspec1 (callEntryStateHOLFinite t callee1) hc hInv_ce1 trivial ⟨vals1, hl1_orig⟩
            (by rw [hrun1]; exact hsafe)
          dsimp only at hs; rw [hrun1] at hs; exact hs
        cases res1 with
        | none => exact opDispatchPost_error s0 cpost1
        | some r1 =>
          cases r1 with
          | timeOut => simp at hnt
          | returned v1 =>
            dsimp only at hnt ⊢
            by_cases hsh1 : (shapeEqHOL (shapeOfHOLExact v1) sh && shapeEqHOL (shapeOfHOLExact v1) ret1) = true
            · rw [if_pos hsh1] at hnt ⊢
              dsimp only at hnt ⊢
              obtain ⟨hInv_cp1, hch_cp1, hR_cp1, _⟩ := (hQ1 (by simp)).1 v1 rfl
              let u := setVarHOLFinite nm v1 { cpost1 with locals := t.locals }
              have hcode_u : u.code = originalRuntimeCode := hmeta1.trans hc
              have hInv_u : EvmInv u := localsFree_evmInv cpost1 u.locals cpost1.clock hInv_cp1
              have hc_u := evm_congr (s := cpost1) (t := u) rfl rfl
              have hlen_u : (evmChain u).length = (evmChain s0).length := by
                rw [hc_u.2.2.1, hch_cp1, hc_ce1.2.2.1]; exact hlen
              have hR_u : if charged then evmR u < evmR s0 else evmR u ≤ evmR s0 :=
                rbound_step_local (by rw [hc_u.2.1]; rw [hc_ce1.2.1] at hR_cp1; exact hR_cp1) hR
              have hcall_ret : HandlerRun s0 (fun _ => True) charged
                  (.seq (.call (some (none, none)) fn2 args2) (.raise (ofString "EvmErr") (.const 0))) :=
                HandlerRun.seq_call_simple hf2 (HandlerRun.raise_evmErr (.const 0))
              obtain ⟨params2, body2, ret2, hlook2, hspec2⟩ := hf2
              have hfold_u : setVarHOLFinite nm v1 { cpost1 with locals := t.locals } = u := rfl
              rw [hfold_u] at hnt ⊢
              rcases hev2 : evaluateHOLFiniteState u (.call (some (none, none)) fn2 args2) with ⟨r2, sp2⟩
              simp only [hev2] at hnt ⊢
              cases r2 with
              | some rr =>
                dsimp only at hnt ⊢
                have hcall := hcall_ret u hcode_u hInv_u hlen_u hR_u trivial
                rw [evaluateHOLFiniteState_seq_line780, hev2] at hcall
                dsimp only at hcall
                exact opDispatchPost_congr_lc rfl rfl rfl (hcall hnt)
              | none =>
                dsimp only at hnt ⊢
                rw [evaluateHOLFiniteState_call] at hev2
                rcases hargs2 : evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args2 with _ | vals2
                · rw [hargs2] at hev2; simp at hev2
                · rw [hargs2] at hev2; dsimp only at hev2
                  rcases hl2 : lookupCodeHOLFinite u.code.lookup fn2 vals2 with _ | ⟨body2', callee2, ret2'⟩
                  · rw [hl2] at hev2; simp at hev2
                  · rw [hl2] at hev2; dsimp only at hev2
                    by_cases hz2 : u.clock = 0
                    · rw [if_pos hz2] at hev2; simp at hev2
                    · rw [if_neg hz2] at hev2
                      have hb2 : body2' = body2 :=
                        lookupCodeHOLFinite_installed_body u.code.lookup fn2 params2 body2 body2'
                          ret2 ret2' vals2 callee2 (by rw [hcode_u]; exact hlook2) hl2
                      subst body2'
                      have hr2 : ret2' = ret2 := by
                        have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
                          u.code.lookup fn2 vals2 body2 callee2 ret2' hl2
                        rw [hcode_u] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook2] at hx
                        split at hx
                        · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
                        · cases hx
                      subst ret2'
                      have hInv_ce2 : EvmInv (callEntryStateHOLFinite u callee2) :=
                        localsFree_evmInv u callee2 (u.clock - 1) hInv_u
                      have hl2_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fn2 vals2 =
                          some (body2, callee2, ret2) := by rwa [← hcode_u]
                      have hmeta2 := (PanRunBounded.evaluateHOLFiniteState_metadata
                        (callEntryStateHOLFinite u callee2) body2).1
                      rcases hrun2 : evaluateHOLFiniteState (callEntryStateHOLFinite u callee2) body2 with ⟨res2, cpost2⟩
                      rw [hrun2] at hev2 hmeta2
                      change cpost2.code = u.code at hmeta2
                      cases res2 with
                      | none => simp at hev2
                      | some rr2 =>
                        cases rr2 with
                        | returned v2 =>
                          dsimp only at hev2
                          split at hev2
                          · injection hev2 with _ hsp2
                            subst sp2
                            have hs2 := hspec2 (callEntryStateHOLFinite u callee2) hcode_u hInv_ce2
                              trivial ⟨vals2, hl2_orig⟩ (by rw [hrun2]; simp)
                            dsimp only at hs2; rw [hrun2] at hs2
                            obtain ⟨hInv_cp2, hch_cp2, hR_cp2, _⟩ := hs2.1 v2 rfl
                            have hc_ce2 := evm_congr (s := u) (t := callEntryStateHOLFinite u callee2) rfl rfl
                            let restored : PanSemStateFiniteExact 64 F :=
                              { cpost2 with locals := HolFiniteMapExact.resVarEq u.locals (nm, t.locals.lookup nm) }
                            have hcode_rest : restored.code = originalRuntimeCode := hmeta2.trans hcode_u
                            have hInv_rest : EvmInv restored :=
                              localsFree_evmInv cpost2 restored.locals cpost2.clock hInv_cp2
                            have hc_rest := evm_congr (s := cpost2) (t := restored) rfl rfl
                            have hlen_rest : (evmChain restored).length = (evmChain s0).length := by
                              rw [hc_rest.2.2.1, hch_cp2, hc_ce2.2.2.1]; exact hlen_u
                            have hR_rest : if charged then evmR restored < evmR s0 else evmR restored ≤ evmR s0 :=
                              rbound_step_local (by rw [hc_rest.2.1]; rw [hc_ce2.2.1] at hR_cp2; exact hR_cp2) hR_u
                            exact hcont restored hcode_rest hInv_rest hlen_rest hR_rest trivial hnt
                          · simp at hev2
                        | timeOut | exception _ _ | «break» | «continue» | finalFfi _ | error => simp at hev2
            · rw [if_neg hsh1] at hnt ⊢
              exact opDispatchPost_error s0 cpost1
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp1, hch_cp1, hR_cp1⟩ := (hQ1 (by simp)).2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost1.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost1 _ cpost1.clock hInv_cp1
              have hc_el := evm_congr (s := cpost1) (t := cpost1.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp1, hc_ce1.2.2.1]; exact hlen
              · have := rbound_to_le_local hR; rw [hc_el.2.1]; rw [hc_ce1.2.1] at hR_cp1; omega
            · refine opDispatchPost_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPost_error s0 cpost1
          | «continue» => exact opDispatchPost_error s0 cpost1
          | finalFfi _ =>
            refine opDispatchPost_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPost_error s0 cpost1.emptyLocalsHOLFinite

theorem op_blockhash_spec : OpHandlerSpec (ofString "op_blockhash") := by
  refine opHandlerSpec_of_run 554 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_blockhash rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_blockhash, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.seq_charge_gas_const (by decide)
        (HandlerRun.decCall_simple eps_block_env
          (HandlerRun.dec_simple
            (HandlerRun.decCall_simple eps_sat_word
              (HandlerRun.seq_ite_nonfallthrough_skip
                (fun u => seq_ne_none_right_env u _ _ (fun u2 => seq_ne_none_right_env u2 _ _ (fun u3 => return_ne_none_env u3 _)))
                (HandlerRun.seq_call_simple eps_stack_push
                  (HandlerRun.seq_call_simple eps_pc_add
                    (HandlerRun.ret _)))
                (HandlerRun.dec_simple
                  (HandlerRun.dec_simple
                    (HandlerRun.seq_ite_other_skip (by decide)
                      (HandlerRun.decCall_simple eps_u256_from_be
                        (HandlerRun.seq_call_simple eps_track_ancestor_access
                          (HandlerRun.seq_call_simple eps_stack_push
                            (HandlerRun.seq_call_simple eps_pc_add
                              (HandlerRun.ret _)))))))))))))

theorem op_coinbase_spec : OpHandlerSpec (ofString "op_coinbase") := by
  refine opHandlerSpec_of_run 555 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_coinbase rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_coinbase, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.decCall_simple eps_block_env
        (HandlerRun.decCall_simple eps_address_to_u256
          (HandlerRun.seq_call_simple eps_stack_push
            (HandlerRun.seq_call_simple eps_pc_add
              (HandlerRun.ret _)))))

theorem op_timestamp_spec : OpHandlerSpec (ofString "op_timestamp") := by
  refine opHandlerSpec_of_run 556 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_timestamp rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_timestamp, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.decCall_simple eps_block_env
        (HandlerRun.seq_call_simple eps_stack_push_word
          (HandlerRun.seq_call_simple eps_pc_add
            (HandlerRun.ret _))))

theorem op_number_spec : OpHandlerSpec (ofString "op_number") := by
  refine opHandlerSpec_of_run 557 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_number rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_number, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.decCall_simple eps_block_env
        (HandlerRun.seq_call_simple eps_stack_push_word
          (HandlerRun.seq_call_simple eps_pc_add
            (HandlerRun.ret _))))

theorem op_prevrandao_spec : OpHandlerSpec (ofString "op_prevrandao") := by
  refine opHandlerSpec_of_run 560 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_prevrandao rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_prevrandao, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.decCall_simple eps_block_env
        (HandlerRun.decCall_simple eps_u256_from_be
          (HandlerRun.seq_call_simple eps_stack_push
            (HandlerRun.seq_call_simple eps_pc_add
              (HandlerRun.ret _)))))

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
