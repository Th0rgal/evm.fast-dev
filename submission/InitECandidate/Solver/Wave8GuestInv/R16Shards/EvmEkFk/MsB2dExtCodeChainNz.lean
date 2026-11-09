import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB2cAccountChainNz

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

section ExtCodeChainNz
open R10Shards.GbodyProcessMsg
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

theorem seq_call0_htab_set_ts8_codeStrongCtxNz {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (kExp vExp : ExpHOL 64) (cont : ProgHOL 64)
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hctx : CodeStrongCtxNz s S Nd)
    (hk : ∀ (cpost : PanSemStateFiniteExact 64 F), CodeStrongCtxNz {cpost with locals := s.locals} S Nd →
      Ret {cpost with locals := s.locals} cont Φ) :
    Ret s (.seq (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), kExp, vExp]) cont) Φ := by
  refine seq_call0_htab_set_codeStrongCtxNz "ts" "ts+8" 8 kExp vExp cont hctx
    (by decide) (by decide) (by decide) (by decide)
    (fun st hts ht0 => ?_)
    (fun st hT hts ht0 => nonValueSlot_ts8 st S hT hts ht0) hk
  have hc8 : (8 : BitVec 64).toNat = 8 := by decide
  rw [hc8] at ht0 ⊢
  apply mem_worldRoleSlots_recRole st "ts" 8 "ts+8" hts ht0
  apply List.mem_append.2; right
  unfold recRoles; simp [hts]

theorem seq_call0_htab_set_bs72_codeStrongCtxNz {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (kExp vExp : ExpHOL 64) (cont : ProgHOL 64)
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hctx : CodeStrongCtxNz s S Nd)
    (hk : ∀ (cpost : PanSemStateFiniteExact 64 F), CodeStrongCtxNz {cpost with locals := s.locals} S Nd →
      Ret {cpost with locals := s.locals} cont Φ) :
    Ret s (.seq (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "bs"), .const 72]), kExp, vExp]) cont) Φ := by
  refine seq_call0_htab_set_codeStrongCtxNz "bs" "bs+72" 72 kExp vExp cont hctx
    (by decide) (by decide) (by decide) (by decide)
    (fun st hbs ht0 => ?_)
    (fun st hT hbs ht0 => nonValueSlot_bs72 st S hT hbs ht0) hk
  have hc72 : (72 : BitVec 64).toNat = 72 := by decide
  rw [hc72] at ht0 ⊢
  apply mem_worldRoleSlots_recRole st "bs" 72 "bs+72" hbs ht0
  apply List.mem_append.2; left; apply List.mem_append.2; right
  unfold recRoles; simp [hbs]

theorem record_pre_state_read_execution_codeStrongCtxNz {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeStrongCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "record_pre_state_read") values =
      some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeStrongCtxNz post S Nd := by
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
      (fun _ p => CodeStrongCtxNz p S Nd) := by
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_record_pre_state_read,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      Option.map_none, Option.map_some, List.map_cons, List.map_nil]
    refine seq_call0_htab_set_bs72_codeStrongCtxNz _ _ _
      (codeStrongCtxNz_with_locals_clock callee (s.clock - 1) hctx) ?_
    intro cpost hcpost
    apply Ret.ret
    intro _ _
    exact codeStrongCtxNz_emptyLocals hcpost
  have hres := hret v (by rw [hb'])
  rwa [hb'] at hres

theorem get_pre_state_account_optional_execution_codeStrongCtxNz {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeStrongCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "get_pre_state_account_optional") values =
      some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeStrongCtxNz post S Nd := by
  have hc := hctx.2.2.2.1
  have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "get_pre_state_account_optional") values = some (body, callee, ret) := by rwa [← hc]
  have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
    (ofString "get_pre_state_account_optional") _ _ body _ ret values callee
    lookup_get_pre_state_account_optional hl'
  have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_get_pre_state_account_optional) = (some (.returned v), post) := by
    rw [← hb, hbody]; rfl
  have hret : Ret (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_get_pre_state_account_optional)
      (fun _ p => CodeStrongCtxNz p S Nd) := by
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_get_pre_state_account_optional,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      Option.map_none, Option.map_some, List.map_cons, List.map_nil]
    refine seq_call0_htab_set_ts8_codeStrongCtxNz _ _ _
      (codeStrongCtxNz_with_locals_clock callee (s.clock - 1) hctx) ?_
    intro s1 hs1
    apply Ret.decCall_gen
    intro vals2 b2 cl2 r2 v2 p2 _ hl2 hb2
    have hp2_ro := readonly_cache_call_state
      {s1 with locals := (callEntryStateHOLFinite s callee).locals} vals2 b2 cl2 r2 v2 p2 hs1.2.2.2.1 hl2 hb2
    have hs2 : CodeStrongCtxNz (setVarHOLFinite (ofString "w") v2
        {p2 with locals := (callEntryStateHOLFinite s callee).locals}) S Nd := by
      have hp2_ctx : CodeStrongCtxNz p2 S Nd := by
        rw [hp2_ro]; exact codeStrongCtxNz_with_locals_clock p2.locals p2.clock hs1
      exact codeStrongCtxNz_setVar (ofString "w") v2
        (codeStrongCtxNz_with_locals_clock (callEntryStateHOLFinite s callee).locals p2.clock hp2_ctx)
    apply Ret.seq_ite
    intro w _
    refine ⟨fun _ => Ret.seq_return (fun _ _ => codeStrongCtxNz_resVar _ (codeStrongCtxNz_emptyLocals hs2)), fun _ => ?_⟩
    apply Ret.seq_skip
    apply Ret.seq_call00
    intro vals3 b3 cl3 r3 v3 p3 _ hl3 hb3
    have hs3 := codeStrongCtxNz_with_locals_clock
      (setVarHOLFinite (ofString "w") v2 {p2 with locals := (callEntryStateHOLFinite s callee).locals}).locals
      p3.clock (record_pre_state_read_execution_codeStrongCtxNz hs2 hl3 hb3)
    apply Ret.decCall_gen
    intro vals4 b4 cl4 r4 v4 p4 _ hl4 hb4
    have hs4 := codeStrongCtxNz_setVar (ofString "a") v4
      (codeStrongCtxNz_with_locals_clock
        (setVarHOLFinite (ofString "w") v2 {p2 with locals := (callEntryStateHOLFinite s callee).locals}).locals
        p4.clock (ws_get_account_execution_codeStrongCtxNz hs3 hl4 hb4))
    apply Ret.ret
    intro _ _
    exact codeStrongCtxNz_resVar _ (codeStrongCtxNz_resVar _ (codeStrongCtxNz_emptyLocals hs4))
  have hres := hret v (by rw [hb'])
  rwa [hb'] at hres

theorem get_account_optional_execution_codeStrongCtxNz {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeStrongCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "get_account_optional") values =
      some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeStrongCtxNz post S Nd := by
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
      (fun _ p => CodeStrongCtxNz p S Nd) := by
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_get_account_optional,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      Option.map_none, Option.map_some, List.map_cons, List.map_nil]
    refine seq_call0_htab_set_ts8_codeStrongCtxNz _ _ _
      (codeStrongCtxNz_with_locals_clock callee (s.clock - 1) hctx) ?_
    intro s1 hs1
    apply Ret.decCall_gen
    intro vals2 b2 cl2 r2 v2 p2 _ hl2 hb2
    have hp2_ro := readonly_cache_call_state
      {s1 with locals := (callEntryStateHOLFinite s callee).locals} vals2 b2 cl2 r2 v2 p2 hs1.2.2.2.1 hl2 hb2
    have hs2 : CodeStrongCtxNz (setVarHOLFinite (ofString "w") v2
        {p2 with locals := (callEntryStateHOLFinite s callee).locals}) S Nd := by
      have hp2_ctx : CodeStrongCtxNz p2 S Nd := by
        rw [hp2_ro]; exact codeStrongCtxNz_with_locals_clock p2.locals p2.clock hs1
      exact codeStrongCtxNz_setVar (ofString "w") v2
        (codeStrongCtxNz_with_locals_clock (callEntryStateHOLFinite s callee).locals p2.clock hp2_ctx)
    apply Ret.seq_ite
    intro w _
    refine ⟨fun _ => Ret.seq_return (fun _ _ => codeStrongCtxNz_resVar _ (codeStrongCtxNz_emptyLocals hs2)), fun _ => ?_⟩
    apply Ret.seq_skip
    apply Ret.decCall_gen
    intro vals3 b3 cl3 r3 v3 p3 _ hl3 hb3
    have hs3 := codeStrongCtxNz_setVar (ofString "a") v3
      (codeStrongCtxNz_with_locals_clock
        (setVarHOLFinite (ofString "w") v2 {p2 with locals := (callEntryStateHOLFinite s callee).locals}).locals
        p3.clock (get_pre_state_account_optional_execution_codeStrongCtxNz hs2 hl3 hb3))
    apply Ret.ret
    intro _ _
    exact codeStrongCtxNz_resVar _ (codeStrongCtxNz_resVar _ (codeStrongCtxNz_emptyLocals hs3))
  have hres := hret v (by rw [hb'])
  rwa [hb'] at hres

theorem get_account_execution_codeStrongCtxNz {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeStrongCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "get_account") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeStrongCtxNz post S Nd := by
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
      (fun _ p => CodeStrongCtxNz p S Nd) := by
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
    have hs1 := codeStrongCtxNz_setVar (ofString "a") v1
      (codeStrongCtxNz_with_locals_clock (callEntryStateHOLFinite s callee).locals p1.clock
        (get_account_optional_execution_codeStrongCtxNz (codeStrongCtxNz_with_locals_clock callee (s.clock - 1) hctx) hl1 hb1))
    apply Ret.seq_ite
    intro w _
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · apply Ret.seq_callAssign_gen
      intro vals2 b2 cl2 r2 v2 p2 _ hl2 hb2
      have hs2 := codeStrongCtxNz_setVar (ofString "a") v2
        (codeStrongCtxNz_with_locals_clock
          (setVarHOLFinite (ofString "a") v1 {p1 with locals := (callEntryStateHOLFinite s callee).locals}).locals
          p2.clock (acct_empty_execution_codeStrongCtxNz hs1 hl2 hb2))
      apply Ret.ret
      intro _ _
      exact codeStrongCtxNz_resVar _ (codeStrongCtxNz_emptyLocals hs2)
    · apply Ret.seq_skip
      apply Ret.ret
      intro _ _
      exact codeStrongCtxNz_resVar _ (codeStrongCtxNz_emptyLocals hs1)
  have hres := hret v (by rw [hb'])
  rwa [hb'] at hres

/-- Unconditional `ext_code_of` bounded return under `CodeStrongCtxNz`! -/
theorem ext_code_of_return_of_codeStrongCtxNz {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hctx : CodeStrongCtxNz s S Nd) :
    Ret s (sourceFnBody Guest.Software.guestFn_ext_code_of)
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  refine ext_code_of_return_of_cache_tail s hctx.2.2.2.1 ?_
  intro values body callee ret v post _ hl hb vals b cl r st _ _
  have hpost := get_account_execution_codeStrongCtxNz hctx hl hb
  have hst : CodeStrongCtxNz st S Nd := codeStrongCtxNz_setVar (ofString "a") v
    (codeStrongCtxNz_with_locals_clock s.locals post.clock hpost)
  exact getCodeCacheContinuationStrong_of_codeStrongCtxNz
    (codeStrongCtxNz_with_locals_clock cl (st.clock - 1) hst)

/-- Unconditional installed-call wrapper for `ext_code_of` under `CodeStrongCtxNz`! -/
theorem ext_code_of_call_return_of_codeStrongCtxNz {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeStrongCtxNz s S Nd)
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
  exact ext_code_of_return_of_codeStrongCtxNz
    (codeStrongCtxNz_with_locals_clock callee (s.clock - 1) hctx) v (congrArg Prod.fst hb')

end ExtCodeChainNz

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
