import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.Depth0FrameOpen
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB2GetCodeUncond
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB3CodeBounded

/-!
# Scratch Rung B3b: Bounded Code-DB Lookup & Preservation (`CodeBoundedCtxNz`)

Proves `nodedb_lookup`, `ws_get_code`, `get_code` cache steps, and preservation of
`CodeDbPayloadBounded` / `CodeBoundedCtxNz` across `WorldEff`, `sk_make`, and non-BAL `HtabExit`,
closing unconditional bounded `get_code` under `CodeBoundedCtxNz`.
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

section CodeBoundedLookup
open R10Shards.GbodyProcessMsg
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

theorem evalList_two_b {F : Type} (s : PanSemStateFiniteExact 64 F)
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

theorem nodedb_lookup_code_tail_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (found ptr : BitVec 64)
    (hr : s.locals.lookup (ofString "r") =
      some (.rStruct [.val (.word found), .val (.word ptr)]))
    (hfound : found ≠ 0) (hw : WordsOK s (ptr.toNat, 16)) (hb : memW s (ptr.toNat + 8) < 2 ^ 40) :
    Ret s
      (.seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0))
        (.return (.rstruct [.const 0, .const 0, .const 0])) .skip)
        (.return (.rstruct [.const 1,
          .load .one (.rfield 1 (.var .local (ofString "r"))),
          .load .one (.op .add [.rfield 1 (.var .local (ofString "r")), .const 8])])))
      (fun v post => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word 1), .val (.word code), .val (.word code_n)] ∧
        code_n.toNat < 2 ^ 40 ∧ post = {s with locals := post.locals, clock := post.clock}) := by
  have he : ev s (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0)) =
      some (.val (.word 0)) := by
    simp [ev, evalHOLExact, hr, Compiler.Encoders.Asm.wordCmpHOL]; exact hfound
  have hi : evaluateHOLFiniteState s
      (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0))
        (.return (.rstruct [.const 0, .const 0, .const 0])) .skip) = (none, s) := by
    rw [evaluateHOLFiniteState_ite]; unfold ev at he; rw [he]; simp [evaluateHOLFiniteState_skip]
  intro v hv
  rw [evaluateHOLFiniteState_seq_line780, hi] at hv ⊢
  exact nodedb_code_record_return_bounded s found ptr hr hw hb v hv

theorem nodedb_lookup_code_tail_cases_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (found ptr : BitVec 64)
    (hr : s.locals.lookup (ofString "r") =
      some (.rStruct [.val (.word found), .val (.word ptr)]))
    (hrecord : found ≠ 0 → WordsOK s (ptr.toNat, 16) ∧ memW s (ptr.toNat + 8) < 2 ^ 40) :
    Ret s
      (.seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0))
        (.return (.rstruct [.const 0, .const 0, .const 0])) .skip)
        (.return (.rstruct [.const 1,
          .load .one (.rfield 1 (.var .local (ofString "r"))),
          .load .one (.op .add [.rfield 1 (.var .local (ofString "r")), .const 8])])))
      (fun v post => ∃ flag code code_n : BitVec 64,
        v = .rStruct [.val (.word flag), .val (.word code), .val (.word code_n)] ∧
        code_n.toNat < 2 ^ 40 ∧ (flag = 0 ∨ flag = 1) ∧
        post = {s with locals := post.locals, clock := post.clock}) := by
  by_cases hf : found = 0
  · subst found
    intro v hv
    rw [nodedb_lookup_missing_tail s ptr hr] at hv ⊢
    cases hv
    exact ⟨0, 0, 0, rfl, by decide, Or.inl rfl, rfl⟩
  · intro v hv
    obtain ⟨hw, hb⟩ := hrecord hf
    obtain ⟨code, code_n, hv, hn, hp⟩ := nodedb_lookup_code_tail_bounded s found ptr hr hf hw hb v hv
    exact ⟨1, code, code_n, hv, hn, Or.inr rfl, hp⟩

theorem nodedb_lookup_return_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (db hash : BitVec 64) (hcode : s.code = originalRuntimeCode)
    (hdb : s.locals.lookup (ofString "db") = some (.val (.word db)))
    (hhash : s.locals.lookup (ofString "hash") = some (.val (.word hash)))
    (hW : HtabWF s db.toNat) (hentries : NodeDbEntriesBounded s db.toNat) :
    Ret s (sourceFnBody Guest.Software.guestFn_nodedb_lookup)
      (fun v _ => ∃ found code code_n : BitVec 64,
        v = .rStruct [.val (.word found), .val (.word code), .val (.word code_n)] ∧
        code_n.toNat < 2 ^ 40 ∧ (found = 0 ∨ found = 1)) := by
  change Ret s (.decCall (ofString "r") (.comb [.one, .one]) (ofString "htab_get")
    [.var .local (ofString "db"), .var .local (ofString "hash")] _) _
  apply Ret.decCall_gen
  intro values body callee ret v post ha hl hb
  have hvals : values = [.val (.word db), .val (.word hash)] := by
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hdb, hhash] using ha.symm
  subst values
  obtain ⟨hbody, ht⟩ := lookupCodeHOLFinite_param_at
    s.code.lookup (ofString "htab_get") [] (ofString "t") .one [(ofString "key", .one)]
    (sourceFnBody Guest.Software.guestFn_htab_get) (.comb [.one, .one])
    (by intro p hp; simp at hp; rw [hp]; decide)
    (by rw [hcode]; exact WkBal.lookup_htab_get) (vpre := []) (by simp) hl
  obtain ⟨_, hk⟩ := lookupCodeHOLFinite_param_at
    s.code.lookup (ofString "htab_get") [(ofString "t", .one)] (ofString "key") .one []
    (sourceFnBody Guest.Software.guestFn_htab_get) (.comb [.one, .one])
    (by simp) (by rw [hcode]; exact WkBal.lookup_htab_get)
    (vpre := [.val (.word db)]) (by simp) hl
  subst body
  let ce := callEntryStateHOLFinite s callee
  have hWce : HtabWF ce db.toNat := WkBal.htabWF_with_locals s callee (s.clock - 1) db.toNat |>.2 hW
  obtain ⟨found, ptr, hv, hm⟩ := WkBal.htab_get_ret_in_values ce db hash hcode ht hk hWce v
    (congrArg Prod.fst hb)
  have hframe := R16WkAcctWs.evaluate_roProgR16 R16WkAcctWs.wsGetCodeCallees
    R16WkAcctWs.wsGetCodeCallees_good (sourceFnBody Guest.Software.guestFn_htab_get)
    (by decide) ce hcode
  rw [hb] at hframe
  have hpost : post = {s with locals := post.locals, clock := post.clock} := by
    simpa [R16WkAcctWs.LocFrameR16, ce, callEntryStateHOLFinite] using hframe
  subst v
  let st := setVarHOLFinite (ofString "r")
    (.rStruct [.val (.word found), .val (.word ptr)]) {post with locals := s.locals}
  have hst : st = {s with locals := st.locals, clock := st.clock} := by
    dsimp only [st, setVarHOLFinite]; rw [hpost]
  have hr : st.locals.lookup (ofString "r") =
      some (.rStruct [.val (.word found), .val (.word ptr)]) := by
    simp [st, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hrecord : found ≠ 0 → WordsOK st (ptr.toNat, 16) ∧ memW st (ptr.toNat + 8) < 2 ^ 40 := by
    intro hf
    have hin : ptr.toNat ∈ htabValues s db.toNat := by
      simpa [ce, callEntryStateHOLFinite, htabValues, hdr, nodeF, memW] using hm hf
    have he := hentries ptr.toNat hin
    rw [hst]
    simpa [WordsOK, WordAt, memW] using he
  intro w hw
  obtain ⟨f, c, n, hv, hn, hf, _⟩ := nodedb_lookup_code_tail_cases_bounded st found ptr hr hrecord w hw
  exact ⟨f, c, n, hv, hn, hf⟩

theorem nodedb_lookup_call_return_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (db hash : BitVec 64) (hcode : s.code = originalRuntimeCode)
    (hW : HtabWF s db.toNat) (hentries : NodeDbEntriesBounded s db.toNat)
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "nodedb_lookup")
      [.val (.word db), .val (.word hash)] = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    post.eshapes = s.eshapes ∧ ∃ found code code_n : BitVec 64,
      v = .rStruct [.val (.word found), .val (.word code), .val (.word code_n)] ∧
      (found ≠ 0 → code_n.toNat < 2 ^ 40) := by
  obtain ⟨hbody, hd⟩ := lookupCodeHOLFinite_param_at s.code.lookup (ofString "nodedb_lookup") []
    (ofString "db") .one [(ofString "hash", .one)] _ (.comb [.one, .one, .one])
    (by intro p hp; simp at hp; rw [hp]; decide)
    (by rw [hcode]; exact lookup_nodedb_lookup_local) (vpre := []) (by simp) hl
  obtain ⟨_, hh⟩ := lookupCodeHOLFinite_param_at s.code.lookup (ofString "nodedb_lookup")
    [(ofString "db", .one)] (ofString "hash") .one [] _ (.comb [.one, .one, .one])
    (by simp) (by rw [hcode]; exact lookup_nodedb_lookup_local)
    (vpre := [.val (.word db)]) (by simp) hl
  subst body
  let ce := callEntryStateHOLFinite s callee
  have hWce : HtabWF ce db.toNat := (WkBal.htabWF_with_locals s _ _ _).2 hW
  have he : NodeDbEntriesBounded ce db.toNat := hentries
  obtain ⟨f, c, n, hv, hn, _⟩ := nodedb_lookup_return_bounded ce db hash hcode hd hh hWce he v
    (congrArg Prod.fst hb)
  refine ⟨?_, f, c, n, hv, fun _ => hn⟩
  have hm := PanRunBounded.evaluateHOLFiniteState_metadata ce (sourceFnBody Guest.Software.guestFn_nodedb_lookup)
  rw [hb] at hm; exact hm.2.2.2.2

theorem ws_get_code_return_of_codeBoundedCtxNz {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz s S Nd) :
    Ret s (sourceFnBody Guest.Software.guestFn_ws_get_code)
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  apply ws_get_code_return_of_nodedb
  intro values body callee ret post _ hl hb
  have hpost := ro_wsGetCodeCallee_state s (ofString "memeq") (by decide)
    values body callee ret (.val (.word 0)) post hctx.2.2.2.1 hl hb
  let st := setVarHOLFinite (ofString "eq") (.val (.word 0)) {post with locals := s.locals}
  have hst_ctx : CodeBoundedCtxNz st S Nd := by
    dsimp only [st]
    have hp_ctx : CodeBoundedCtxNz post S Nd := by
      rw [hpost]; exact codeBoundedCtxNz_with_locals_clock post.locals post.clock hctx
    exact codeBoundedCtxNz_setVar _ _ (codeBoundedCtxNz_resVar s.locals hp_ctx)
  refine ⟨hst_ctx.2.2.2.2, ?_⟩
  intro values' body' callee' ret' v' post' ha' hl' hb'
  obtain ⟨hA, hWT, hCB, hc, _⟩ := hst_ctx
  obtain ⟨v1, v2, he1, _, rfl⟩ := evalList_two_b st _ _ values' ha'
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
  have hent_db : NodeDbEntriesBounded st db.toNat := by
    have hp := hCB "ws" 16 (by simp) hws_nz hdb_nz
    rw [← hdb_nat] at hp; exact hp.1
  exact nodedb_lookup_call_return_bounded st db hash hc hWF_db hent_db _ _ _ _ _ hl' hb'

theorem ws_get_code_call_return_of_codeBoundedCtxNz {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "ws_get_code") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    ∃ code code_n : BitVec 64,
      v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40 := by
  have hc := hctx.2.2.2.1
  have hbody := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "ws_get_code")
    _ _ body _ ret values callee (by rw [hc]; exact lookup_ws_get_code_local) hl
  subst body
  exact ws_get_code_return_of_codeBoundedCtxNz
    (codeBoundedCtxNz_with_locals_clock callee (s.clock - 1) hctx) v (congrArg Prod.fst hb)

theorem get_code_cache_call_resume_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (db hash : BitVec 64) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (ret : ShapeHOL) (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hW : HtabWF s db.toNat)
    (hentries : NodeDbEntriesBounded s db.toNat)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_get")
      [.val (.word db), .val (.word hash)] = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    post = {s with locals := post.locals, clock := post.clock} ∧
      ∃ found ptr : BitVec 64, v = .rStruct [.val (.word found), .val (.word ptr)] ∧
        (found ≠ 0 → WordsOK s (ptr.toNat, 16) ∧ memW s (ptr.toNat + 8) < 2 ^ 40) := by
  obtain ⟨hbody, ht⟩ := lookupCodeHOLFinite_param_at
    s.code.lookup (ofString "htab_get") [] (ofString "t") .one [(ofString "key", .one)]
    (sourceFnBody Guest.Software.guestFn_htab_get) (.comb [.one, .one])
    (by intro p hp; simp at hp; rw [hp]; decide)
    (by rw [hcode]; exact WkBal.lookup_htab_get) (vpre := []) (by simp) hl
  obtain ⟨_, hk⟩ := lookupCodeHOLFinite_param_at
    s.code.lookup (ofString "htab_get") [(ofString "t", .one)] (ofString "key") .one []
    (sourceFnBody Guest.Software.guestFn_htab_get) (.comb [.one, .one])
    (by simp) (by rw [hcode]; exact WkBal.lookup_htab_get)
    (vpre := [.val (.word db)]) (by simp) hl
  subst body
  let ce := callEntryStateHOLFinite s callee
  have hWce : HtabWF ce db.toNat := WkBal.htabWF_with_locals s callee (s.clock - 1) db.toNat |>.2 hW
  obtain ⟨found, ptr, hv, hm⟩ := WkBal.htab_get_ret_in_values ce db hash hcode ht hk hWce v
    (congrArg Prod.fst hb)
  have hframe := R16WkAcctWs.evaluate_roProgR16 R16WkAcctWs.wsGetCodeCallees
    R16WkAcctWs.wsGetCodeCallees_good (sourceFnBody Guest.Software.guestFn_htab_get)
    (by decide) ce hcode
  rw [hb] at hframe
  refine ⟨?_, found, ptr, hv, fun hf => ?_⟩
  · simpa [R16WkAcctWs.LocFrameR16, ce, callEntryStateHOLFinite] using hframe
  · apply hentries ptr.toNat
    simpa [ce, callEntryStateHOLFinite, htabValues, hdr, nodeF, memW] using hm hf

theorem get_code_cache_step_bounded {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {owner : String} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64}
    (hctx : CodeBoundedCtxNz s S Nd) (ho : owner = "ts" ∨ owner = "bs")
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (getCodeCacheArgs owner) = some values)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_get") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    post = {s with locals := post.locals, clock := post.clock} ∧
    ∃ found ptr : BitVec 64,
      v = .rStruct [.val (.word found), .val (.word ptr)] ∧
      (found ≠ 0 → WordsOK s (ptr.toNat, 16) ∧ memW s (ptr.toNat + 8) < 2 ^ 40) := by
  obtain ⟨hA, hWT, hCB, hc, _⟩ := hctx
  have hW_s : WorldTyped s S := (worldTyped_iff_with _ _).2 ⟨Nd, hWT⟩
  obtain ⟨v1, v2, he1, _, rfl⟩ := evalList_two_b s _ _ values ha
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
  have hent_db : NodeDbEntriesBounded s db.toNat := by
    have hp := hCB owner 48 (by rcases ho with rfl | rfl <;> simp) hown_nz hdb_nz
    rw [← hdb_nat] at hp; exact hp.1
  exact get_code_cache_call_resume_bounded s db hash body callee ret v post hc hWF_db hent_db hl hb

end CodeBoundedLookup

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
