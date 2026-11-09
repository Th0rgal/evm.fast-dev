import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB3dExtCodeBounded

/-!
# Scratch Rung B3e: Account Chain & `ext_code_of` Bounded Return (`CodeBoundedCtxNz`)

Closes `acct_new`, `acct_empty`, `ws_get_account_optional`, `record_pre_state_read`,
`get_pre_state_account_optional`, `get_account_optional`, `get_account`, and `ext_code_of`
under `CodeBoundedCtxNz`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase
open InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas
open InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8M19.Htab
open InitECandidate.Solver.Wave8GuestInv.HtabC00Ports
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge

section ExtCodeChainBounded
open R10Shards.GbodyProcessMsg
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

theorem acct_new_params_b {vals : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "acct_new") vals =
      some (body, callee, rs)) :
    ∃ (wn wc : BitVec 64) (vb : ValueHOL 64),
      shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vb) = true ∧
      callee.lookup (ofString "nonce") = some (.val (.word wn)) ∧
      callee.lookup (ofString "balance") = some vb ∧
      callee.lookup (ofString "code_hash") = some (.val (.word wc)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "acct_new")
    vals body callee rs hl
  simp only [lookupCodeHOLExact, lookup_acct_new] at hx
  rcases vals with _ | ⟨vn, _ | ⟨vb, _ | ⟨vc, _ | _⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · rcases vn with ⟨⟨wn⟩⟩ | _ | _ <;> rcases vc with ⟨⟨wc⟩⟩ | _ | _ <;>
      try (simp [shapeOfHOLExact, shapeEqHOL] at hx)
    simp [shapeOfHOLExact, shapeEqHOL,
      show ofString "nonce" ≠ ofString "balance" by decide,
      show ofString "nonce" ≠ ofString "code_hash" by decide,
      show ofString "balance" ≠ ofString "code_hash" by decide] at hx
    obtain ⟨hsh_b, _, hL, _⟩ := hx
    refine ⟨wn, wc, vb, hsh_b, ?_, ?_, ?_⟩ <;>
      (rw [← hL]; simp [show ofString "nonce" ≠ ofString "balance" by decide,
        show ofString "nonce" ≠ ofString "code_hash" by decide,
        show ofString "balance" ≠ ofString "nonce" by decide,
        show ofString "balance" ≠ ofString "code_hash" by decide,
        show ofString "code_hash" ≠ ofString "nonce" by decide,
        show ofString "code_hash" ≠ ofString "balance" by decide])
  · simp at hx

theorem acct_new_execution_codeBoundedCtxNz {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "acct_new") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeBoundedCtxNz post S Nd := by
  have hc := hctx.2.2.2.1
  have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "acct_new") values =
      some (body, callee, ret) := by rwa [← hc]
  have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "acct_new")
    _ _ body _ ret values callee lookup_acct_new hl'
  subst hbody
  obtain ⟨wn, wc, vb, hsh_b, hlk_n, hlk_b, hlk_c⟩ := acct_new_params_b hl'
  have heff0 := worldEff_acct_new s (callEntryStateHOLFinite s callee) (Rl := []) (B := [])
    (gw := ["heap_ptr"]) (by decide)
    ((WorldEff.refl s [] [] ["heap_ptr"] hctx.1 hc).locals_clock _ _)
    hsh_b hlk_n hlk_b hlk_c (by rw [hb]; simp) (by rw [hb]; simp [Resumes])
  rw [hb] at heff0
  have heff : WorldEff s post [] wsBufs wsGw :=
    heff0.mono (by intro _ h; cases h) (by intro _ h; cases h)
      (by intro g hg; simp at hg; subst hg; simp [wsGw])
  exact codeBoundedCtxNz_of_witness_effect hctx heff

theorem ws_get_account_execution_codeBoundedCtxNz {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "ws_get_account_optional") values =
      some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeBoundedCtxNz post S Nd :=
  codeBoundedCtxNz_of_witness_effect hctx
    (ws_get_account_execution_effect s values body callee ret v post hctx.2.2.2.1 hctx.1 hl hb)

theorem acct_empty_execution_codeBoundedCtxNz {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "acct_empty") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeBoundedCtxNz post S Nd := by
  have hc := hctx.2.2.2.1
  have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "acct_empty") values =
      some (body, callee, ret) := by rwa [← hc]
  have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "acct_empty")
    _ _ body _ ret values callee lookup_acct_empty hl'
  have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_acct_empty) = (some (.returned v), post) := by
    rw [← hb, hbody]; rfl
  have hret : Ret (callEntryStateHOLFinite s callee) (sourceFnBody Guest.Software.guestFn_acct_empty)
      (fun _ p => CodeBoundedCtxNz p S Nd) := by
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_acct_empty,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      Option.map_none, Option.map_some, List.map_cons, List.map_nil]
    apply Ret.decCall_gen
    intro vals1 b1 cl1 r1 v1 m1 _ hl1 hb1
    have hs1 := codeBoundedCtxNz_setVar (ofString "a") v1
      (codeBoundedCtxNz_with_locals_clock (callEntryStateHOLFinite s callee).locals m1.clock
        (acct_new_execution_codeBoundedCtxNz (codeBoundedCtxNz_with_locals_clock callee (s.clock - 1) hctx) hl1 hb1))
    apply Ret.ret
    intro _ _
    exact codeBoundedCtxNz_resVar _ (codeBoundedCtxNz_emptyLocals hs1)
  have hres := hret v (by rw [hb'])
  rwa [hb'] at hres

theorem record_pre_state_read_execution_codeBoundedCtxNz {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "record_pre_state_read") values =
      some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeBoundedCtxNz post S Nd := by
  have hc := hctx.2.2.2.1
  have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "record_pre_state_read") values =
      some (body, callee, ret) := by rwa [← hc]
  have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
    (ofString "record_pre_state_read") _ _ body _ ret values callee lookup_record_pre_state_read hl'
  have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_record_pre_state_read) = (some (.returned v), post) := by
    rw [← hb, hbody]; rfl
  have hret : Ret (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_record_pre_state_read)
      (fun _ p => CodeBoundedCtxNz p S Nd) := by
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_record_pre_state_read,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      Option.map_none, Option.map_some, List.map_cons, List.map_nil]
    refine seq_call0_htab_set_bs72_codeBoundedCtxNz _ _ _
      (codeBoundedCtxNz_with_locals_clock callee (s.clock - 1) hctx) ?_
    intro cpost hcpost
    apply Ret.ret
    intro _ _
    exact codeBoundedCtxNz_emptyLocals hcpost
  have hres := hret v (by rw [hb'])
  rwa [hb'] at hres

theorem get_pre_state_account_optional_execution_codeBoundedCtxNz {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "get_pre_state_account_optional") values =
      some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeBoundedCtxNz post S Nd := by
  have hc := hctx.2.2.2.1
  have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "get_pre_state_account_optional") values = some (body, callee, ret) := by rwa [← hc]
  have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
    (ofString "get_pre_state_account_optional") _ _ body _ ret values callee
    lookup_get_pre_state_account_optional hl'
  have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_get_pre_state_account_optional) =
      (some (.returned v), post) := by
    rw [← hb, hbody]; rfl
  have hret : Ret (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_get_pre_state_account_optional)
      (fun _ p => CodeBoundedCtxNz p S Nd) := by
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_get_pre_state_account_optional,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      Option.map_none, Option.map_some, List.map_cons, List.map_nil]
    refine seq_call0_htab_set_ts8_codeBoundedCtxNz _ _ _
      (codeBoundedCtxNz_with_locals_clock callee (s.clock - 1) hctx) ?_
    intro s1 hs1
    apply Ret.decCall_gen
    intro vals2 b2 cl2 r2 v2 p2 _ hl2 hb2
    have hp2_ro := readonly_cache_call_state
      {s1 with locals := (callEntryStateHOLFinite s callee).locals} vals2 b2 cl2 r2 v2 p2 hs1.2.2.2.1 hl2 hb2
    have hs2 : CodeBoundedCtxNz (setVarHOLFinite (ofString "w") v2
        {p2 with locals := (callEntryStateHOLFinite s callee).locals}) S Nd := by
      have hp2_ctx : CodeBoundedCtxNz p2 S Nd := by
        rw [hp2_ro]; exact codeBoundedCtxNz_with_locals_clock p2.locals p2.clock hs1
      exact codeBoundedCtxNz_setVar (ofString "w") v2
        (codeBoundedCtxNz_with_locals_clock (callEntryStateHOLFinite s callee).locals p2.clock hp2_ctx)
    apply Ret.seq_ite
    intro w _
    refine ⟨fun _ => Ret.seq_return (fun _ _ => codeBoundedCtxNz_resVar _ (codeBoundedCtxNz_emptyLocals hs2)), fun _ => ?_⟩
    apply Ret.seq_skip
    apply Ret.seq_call00
    intro vals3 b3 cl3 r3 v3 p3 _ hl3 hb3
    have hs3 := codeBoundedCtxNz_with_locals_clock
      (setVarHOLFinite (ofString "w") v2 {p2 with locals := (callEntryStateHOLFinite s callee).locals}).locals
      p3.clock (record_pre_state_read_execution_codeBoundedCtxNz hs2 hl3 hb3)
    apply Ret.decCall_gen
    intro vals4 b4 cl4 r4 v4 p4 _ hl4 hb4
    have hs4 := codeBoundedCtxNz_setVar (ofString "a") v4
      (codeBoundedCtxNz_with_locals_clock
        (setVarHOLFinite (ofString "w") v2 {p2 with locals := (callEntryStateHOLFinite s callee).locals}).locals
        p4.clock (ws_get_account_execution_codeBoundedCtxNz hs3 hl4 hb4))
    apply Ret.ret
    intro _ _
    exact codeBoundedCtxNz_resVar _ (codeBoundedCtxNz_resVar _ (codeBoundedCtxNz_emptyLocals hs4))
  have hres := hret v (by rw [hb'])
  rwa [hb'] at hres

theorem get_account_optional_execution_codeBoundedCtxNz {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "get_account_optional") values =
      some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeBoundedCtxNz post S Nd := by
  have hc := hctx.2.2.2.1
  have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "get_account_optional") values = some (body, callee, ret) := by rwa [← hc]
  have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
    (ofString "get_account_optional") _ _ body _ ret values callee
    lookup_get_account_optional hl'
  have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_get_account_optional) = (some (.returned v), post) := by
    rw [← hb, hbody]; rfl
  have hret : Ret (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_get_account_optional)
      (fun _ p => CodeBoundedCtxNz p S Nd) := by
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_get_account_optional,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      Option.map_none, Option.map_some, List.map_cons, List.map_nil]
    refine seq_call0_htab_set_ts8_codeBoundedCtxNz _ _ _
      (codeBoundedCtxNz_with_locals_clock callee (s.clock - 1) hctx) ?_
    intro s1 hs1
    apply Ret.decCall_gen
    intro vals2 b2 cl2 r2 v2 p2 _ hl2 hb2
    have hp2_ro := readonly_cache_call_state
      {s1 with locals := (callEntryStateHOLFinite s callee).locals} vals2 b2 cl2 r2 v2 p2 hs1.2.2.2.1 hl2 hb2
    have hs2 : CodeBoundedCtxNz (setVarHOLFinite (ofString "w") v2
        {p2 with locals := (callEntryStateHOLFinite s callee).locals}) S Nd := by
      have hp2_ctx : CodeBoundedCtxNz p2 S Nd := by
        rw [hp2_ro]; exact codeBoundedCtxNz_with_locals_clock p2.locals p2.clock hs1
      exact codeBoundedCtxNz_setVar (ofString "w") v2
        (codeBoundedCtxNz_with_locals_clock (callEntryStateHOLFinite s callee).locals p2.clock hp2_ctx)
    apply Ret.seq_ite
    intro w _
    refine ⟨fun _ => Ret.seq_return (fun _ _ => codeBoundedCtxNz_resVar _ (codeBoundedCtxNz_emptyLocals hs2)), fun _ => ?_⟩
    apply Ret.seq_skip
    apply Ret.decCall_gen
    intro vals3 b3 cl3 r3 v3 p3 _ hl3 hb3
    have hs3 := codeBoundedCtxNz_setVar (ofString "a") v3
      (codeBoundedCtxNz_with_locals_clock
        (setVarHOLFinite (ofString "w") v2 {p2 with locals := (callEntryStateHOLFinite s callee).locals}).locals
        p3.clock (get_pre_state_account_optional_execution_codeBoundedCtxNz hs2 hl3 hb3))
    apply Ret.ret
    intro _ _
    exact codeBoundedCtxNz_resVar _ (codeBoundedCtxNz_resVar _ (codeBoundedCtxNz_emptyLocals hs3))
  have hres := hret v (by rw [hb'])
  rwa [hb'] at hres

theorem get_account_execution_codeBoundedCtxNz {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "get_account") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeBoundedCtxNz post S Nd := by
  have hc := hctx.2.2.2.1
  have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "get_account") values =
      some (body, callee, ret) := by rwa [← hc]
  have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
    (ofString "get_account") _ _ body _ ret values callee lookup_get_account hl'
  have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_get_account) = (some (.returned v), post) := by
    rw [← hb, hbody]; rfl
  have hret : Ret (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_get_account)
      (fun _ p => CodeBoundedCtxNz p S Nd) := by
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_get_account,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      Option.map_none, Option.map_some, List.map_cons, List.map_nil]
    apply Ret.decCall_gen
    intro vals1 b1 cl1 r1 v1 p1 _ hl1 hb1
    have hs1 := codeBoundedCtxNz_setVar (ofString "a") v1
      (codeBoundedCtxNz_with_locals_clock (callEntryStateHOLFinite s callee).locals p1.clock
        (get_account_optional_execution_codeBoundedCtxNz (codeBoundedCtxNz_with_locals_clock callee (s.clock - 1) hctx) hl1 hb1))
    apply Ret.seq_ite
    intro w _
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · apply Ret.seq_callAssign_gen
      intro vals2 b2 cl2 r2 v2 p2 _ hl2 hb2
      have hs2 := codeBoundedCtxNz_setVar (ofString "a") v2
        (codeBoundedCtxNz_with_locals_clock
          (setVarHOLFinite (ofString "a") v1 {p1 with locals := (callEntryStateHOLFinite s callee).locals}).locals
          p2.clock (acct_empty_execution_codeBoundedCtxNz hs1 hl2 hb2))
      apply Ret.ret
      intro _ _
      exact codeBoundedCtxNz_resVar _ (codeBoundedCtxNz_emptyLocals hs2)
    · apply Ret.seq_skip
      apply Ret.ret
      intro _ _
      exact codeBoundedCtxNz_resVar _ (codeBoundedCtxNz_emptyLocals hs1)
  have hres := hret v (by rw [hb'])
  rwa [hb'] at hres

theorem ext_code_of_return_of_codeBoundedCtxNz {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz s S Nd) :
    Ret s (sourceFnBody Guest.Software.guestFn_ext_code_of)
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  refine ext_code_of_return_of_cache_tail s hctx.2.2.2.1 ?_
  intro values body callee ret v post _ hl hb vals b cl r st _ _
  have hpost := get_account_execution_codeBoundedCtxNz hctx hl hb
  have hst : CodeBoundedCtxNz st S Nd := codeBoundedCtxNz_setVar (ofString "a") v
    (codeBoundedCtxNz_with_locals_clock s.locals post.clock hpost)
  exact getCodeCacheContinuationStrong_of_codeBoundedCtxNz
    (codeBoundedCtxNz_with_locals_clock cl (st.clock - 1) hst)

theorem ext_code_of_call_return_of_codeBoundedCtxNz {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "ext_code_of") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    ∃ code code_n : BitVec 64,
      v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40 := by
  have hc := hctx.2.2.2.1
  have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "ext_code_of") values =
      some (body, callee, ret) := by rwa [← hc]
  have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
    (ofString "ext_code_of") _ _ body _ ret values callee lookup_ext_code_of hl'
  have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_ext_code_of) = (some (.returned v), post) := by
    rw [← hb, hbody]; rfl
  exact ext_code_of_return_of_codeBoundedCtxNz
    (codeBoundedCtxNz_with_locals_clock callee (s.clock - 1) hctx) v (congrArg Prod.fst hb')

end ExtCodeChainBounded

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
