import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB1Delta

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

section GetCodeUncond
open R10Shards.GbodyProcessMsg
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-- Strong world context without ANY nonzero global/root assumptions. -/
def CodeStrongCtxNz {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) : Prop :=
  ArenaReady s ∧
  WorldTypedWith s S Nd ∧
  CodeDbPayloadNonzero s S ∧
  s.code = originalRuntimeCode ∧
  s.eshapes.lookup (ofString "StateErr") = some .one

theorem codeStrongCtxNz_with_locals_clock {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (h : CodeStrongCtxNz s S Nd) :
    CodeStrongCtxNz {s with locals := L, clock := k} S Nd := by
  obtain ⟨hA, hWT, hCS, hc, hs⟩ := h
  refine ⟨localsFree_arenaReady s L k hA, ?_,
    (codeDbPayloadNonzero_with_locals_clock s S L k).2 hCS, hc, hs⟩
  exact ⟨(tablesTyped_with_locals s L k S).2 hWT.1, hWT.2.1, hWT.2.2.1, hWT.2.2.2⟩

theorem codeStrongCtxNz_setVar {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (x : MlS) (v : ValueHOL 64) (h : CodeStrongCtxNz s S Nd) :
    CodeStrongCtxNz (setVarHOLFinite x v s) S Nd := by
  have heq : setVarHOLFinite x v s = {s with locals := (setVarHOLFinite x v s).locals, clock := s.clock} := by
    cases s; rfl
  rw [heq]; exact codeStrongCtxNz_with_locals_clock _ _ h

theorem codeStrongCtxNz_emptyLocals {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (h : CodeStrongCtxNz s S Nd) :
    CodeStrongCtxNz (emptyLocalsHOLFinite s) S Nd := by
  have heq : emptyLocalsHOLFinite s = {s with locals := (emptyLocalsHOLFinite s).locals, clock := s.clock} := by
    cases s; rfl
  rw [heq]; exact codeStrongCtxNz_with_locals_clock _ _ h

theorem codeStrongCtxNz_resVar {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (L : HolFiniteMapExact MlS (ValueHOL 64))
    (h : CodeStrongCtxNz s S Nd) :
    CodeStrongCtxNz {s with locals := L} S Nd := by
  have heq : ({s with locals := L} : PanSemStateFiniteExact 64 F) = {s with locals := L, clock := s.clock} := by
    cases s; rfl
  rw [heq]; exact codeStrongCtxNz_with_locals_clock _ _ h

theorem evalList_two {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e1 e2 : ExpHOL 64) (values : List (ValueHOL 64))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [e1, e2] = some values) :
    ∃ v1 v2, evalAt s e1 = some v1 ∧ evalAt s e2 = some v2 ∧ values = [v1, v2] := by
  rw [evalListHOLFinite_eq_toExact] at ha
  simp only [evalListHOLExact] at ha
  rcases h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · simp [h1] at ha
  · rcases h2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
    · simp [h1, h2] at ha
    · simp only [h1, h2, Option.some.injEq] at ha
      exact ⟨v1, v2, h1, h2, ha.symm⟩

theorem ro_wsGetCodeCallee_state {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fn : MlS) (hfn : R16WkAcctWs.wsGetCodeCallees fn = true)
    (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup fn values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    post = {s with locals := post.locals, clock := post.clock} := by
  have hl' := hl; rw [hc] at hl'
  have hf := R16WkAcctWs.evaluate_roProgR16 R16WkAcctWs.wsGetCodeCallees
    R16WkAcctWs.wsGetCodeCallees_good body
    (R16WkAcctWs.wsGetCodeCallees_good fn hfn values body callee ret hl')
    (callEntryStateHOLFinite s callee) hc
  rw [hb] at hf
  simpa [R16WkAcctWs.LocFrameR16, callEntryStateHOLFinite] using hf

theorem htab_get_call_db_nonzero {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {db hash : BitVec 64}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64}
    (hG : GuestInv s)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_get")
      [.val (.word db), .val (.word hash)] = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    db ≠ 0 := by
  obtain ⟨hbody, ht⟩ := lookupCodeHOLFinite_param_at
    s.code.lookup (ofString "htab_get") [] (ofString "t") .one [(ofString "key", .one)]
    (sourceFnBody Guest.Software.guestFn_htab_get) (.comb [.one, .one])
    (by intro p hp; simp at hp; rw [hp]; decide)
    (by rw [hG.code]; exact WkBal.lookup_htab_get) (vpre := []) (by simp) hl
  obtain ⟨_, hk⟩ := lookupCodeHOLFinite_param_at
    s.code.lookup (ofString "htab_get") [(ofString "t", .one)] (ofString "key") .one []
    (sourceFnBody Guest.Software.guestFn_htab_get) (.comb [.one, .one])
    (by simp) (by rw [hG.code]; exact WkBal.lookup_htab_get)
    (vpre := [.val (.word db)]) (by simp) hl
  subst body
  exact WkBal.htab_get_t_nonzero (callEntryStateHOLFinite s callee) db hash
    (guestInv_callEntry s callee hG) ht hk v (congrArg Prod.fst hb)

theorem nodedb_lookup_call_db_nonzero {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {db hash : BitVec 64}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64}
    (hG : GuestInv s)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "nodedb_lookup")
      [.val (.word db), .val (.word hash)] = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    db ≠ 0 := by
  obtain ⟨hbody, hd⟩ := lookupCodeHOLFinite_param_at s.code.lookup (ofString "nodedb_lookup") []
    (ofString "db") .one [(ofString "hash", .one)] _ (.comb [.one, .one, .one])
    (by intro p hp; simp at hp; rw [hp]; decide)
    (by rw [hG.code]; exact lookup_nodedb_lookup_local) (vpre := []) (by simp) hl
  obtain ⟨_, hh⟩ := lookupCodeHOLFinite_param_at s.code.lookup (ofString "nodedb_lookup")
    [(ofString "db", .one)] (ofString "hash") .one [] _ (.comb [.one, .one, .one])
    (by simp) (by rw [hG.code]; exact lookup_nodedb_lookup_local)
    (vpre := [.val (.word db)]) (by simp) hl
  subst body
  let ce := callEntryStateHOLFinite s callee
  have hret_nd : Ret ce (sourceFnBody Guest.Software.guestFn_nodedb_lookup) (fun _ _ => db ≠ 0) := by
    change Ret ce (.decCall (ofString "r") (.comb [.one, .one]) (ofString "htab_get")
      [.var .local (ofString "db"), .var .local (ofString "hash")] _) _
    apply Ret.decCall_gen
    intro vals b cl r v' p' ha' hl' hb'
    obtain ⟨v1, v2, he1, he2, rfl⟩ := evalList_two ce _ _ vals ha'
    have hv1 : v1 = .val (.word db) := Option.some.inj (he1.symm.trans hd)
    have hv2 : v2 = .val (.word hash) := Option.some.inj (he2.symm.trans hh)
    subst hv1; subst hv2
    have hdb_nz := htab_get_call_db_nonzero (guestInv_callEntry s callee hG) hl' hb'
    exact fun _ _ => hdb_nz
  exact hret_nd v (congrArg Prod.fst hb)

theorem ws_get_code_return_of_codeStrongCtxNz {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hctx : CodeStrongCtxNz s S Nd) :
    Ret s (sourceFnBody Guest.Software.guestFn_ws_get_code)
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  apply ws_get_code_return_of_nodedb
  intro values body callee ret post _ hl hb
  have hpost := ro_wsGetCodeCallee_state s (ofString "memeq") (by decide)
    values body callee ret (.val (.word 0)) post hctx.2.2.2.1 hl hb
  let st := setVarHOLFinite (ofString "eq") (.val (.word 0)) {post with locals := s.locals}
  have hst_ctx : CodeStrongCtxNz st S Nd := by
    dsimp only [st]
    have hp_ctx : CodeStrongCtxNz post S Nd := by
      rw [hpost]; exact codeStrongCtxNz_with_locals_clock post.locals post.clock hctx
    exact codeStrongCtxNz_setVar _ _ (codeStrongCtxNz_resVar s.locals hp_ctx)
  refine ⟨hst_ctx.2.2.2.2, ?_⟩
  intro values' body' callee' ret' v' post' ha' hl' hb'
  obtain ⟨hA, hWT, hCS, hc, _⟩ := hst_ctx
  obtain ⟨v1, v2, he1, _, rfl⟩ := evalList_two st _ _ values' ha'
  obtain ⟨db, rfl, hdb_nat, hws_nz⟩ := evalAt_loadG_nz st hA.1 "ws" 16 (by decide) v1 he1
  have hc16 : (16 : BitVec 64).toNat = 16 := by decide
  rw [hc16] at hdb_nat
  have hv2_word : ∃ hash : BitVec 64, v2 = .val (.word hash) := by
    have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "nodedb_lookup")
      [.val (.word db), v2] body' callee' ret' (by rwa [← hc])
    simp only [lookupCodeHOLExact, lookup_nodedb_lookup_local] at hx
    rcases v2 with ⟨⟨hash⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
    exact ⟨hash, rfl⟩
  obtain ⟨hash, rfl⟩ := hv2_word
  have hdb_bv_nz : db ≠ 0 := nodedb_lookup_call_db_nonzero hA.1 hl' hb'
  have hdb_nz : memW st (globN st "ws" + 16) ≠ 0 := by
    rw [← hdb_nat]; exact fun h0 => hdb_bv_nz (BitVec.eq_of_toNat_eq h0)
  have hdb_S : db.toNat ∈ S := by
    rw [hdb_nat]
    rcases hWT.1.2.2.2.1 16 (by decide) hws_nz with h0 | hm
    · exact absurd h0 hdb_nz
    · exact hm
  have hWF_db : HtabWF st db.toNat := (hWT.1.2.1 _ hdb_S).1
  have hent_db : NodeDbEntriesStrong st db.toNat := by
    have hp := hCS "ws" 16 (by simp) hws_nz hdb_nz
    rw [← hdb_nat] at hp; exact hp.1
  exact nodedb_lookup_call_return_strong st db hash hc hA hWF_db hent_db body' callee' ret' v' post' hl' hb'

theorem ws_get_code_call_return_of_codeStrongCtxNz {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeStrongCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "ws_get_code") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    ∃ code code_n : BitVec 64,
      v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40 := by
  have hc := hctx.2.2.2.1
  have hbody := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "ws_get_code")
    _ _ body _ ret values callee (by rw [hc]; exact lookup_ws_get_code_local) hl
  subst body
  exact ws_get_code_return_of_codeStrongCtxNz
    (codeStrongCtxNz_with_locals_clock callee (s.clock - 1) hctx) v (congrArg Prod.fst hb)

theorem get_code_cache_step_uncond {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {owner : String} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64}
    (hctx : CodeStrongCtxNz s S Nd) (ho : owner = "ts" ∨ owner = "bs")
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (getCodeCacheArgs owner) = some values)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_get") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    post = {s with locals := post.locals, clock := post.clock} ∧
    ∃ found ptr : BitVec 64,
      v = .rStruct [.val (.word found), .val (.word ptr)] ∧
      (found ≠ 0 → WordsOK s (ptr.toNat, 16) ∧
        Inside (memW s ptr.toNat, memW s (ptr.toNat + 8)) sourceBase (globN s "heap_ptr")) := by
  obtain ⟨hA, hWT, hCS, hc, _⟩ := hctx
  have hW_s : WorldTyped s S := (worldTyped_iff_with _ _).2 ⟨Nd, hWT⟩
  obtain ⟨v1, v2, he1, _, rfl⟩ := evalList_two s _ _ values ha
  obtain ⟨db, rfl, hdb_nat, hown_nz⟩ := evalAt_loadG_nz s hA.1 owner 48 (by decide) v1 he1
  have hc48 : (48 : BitVec 64).toNat = 48 := by decide
  rw [hc48] at hdb_nat
  have hv2_word : ∃ hash : BitVec 64, v2 = .val (.word hash) := by
    have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "htab_get")
      [.val (.word db), v2] body callee ret (by rwa [← hc])
    simp only [lookupCodeHOLExact, WkBal.lookup_htab_get] at hx
    rcases v2 with ⟨⟨hash⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
    exact ⟨hash, rfl⟩
  obtain ⟨hash, rfl⟩ := hv2_word
  have hdb_bv_nz : db ≠ 0 := htab_get_call_db_nonzero hA.1 hl hb
  have hdb_nz : memW s (globN s owner + 48) ≠ 0 := by
    rw [← hdb_nat]; exact fun h0 => hdb_bv_nz (BitVec.eq_of_toNat_eq h0)
  have hdb_S : db.toNat ∈ S := by
    rw [hdb_nat]; exact code_cache_root_mem s S owner hW_s ho hown_nz hdb_nz
  have hWF_db : HtabWF s db.toNat := (hWT.1.2.1 _ hdb_S).1
  have hent_db : NodeDbEntriesStrong s db.toNat := by
    have hp := hCS owner 48 (by rcases ho with rfl | rfl <;> simp) hown_nz hdb_nz
    rw [← hdb_nat] at hp; exact hp.1
  exact get_code_cache_call_resume_strong s db hash body callee ret v post hc hWF_db hent_db hl hb

end GetCodeUncond
end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
