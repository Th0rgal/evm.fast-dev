import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB4c1GasWarmRo

/-!
# Scratch Rung B4c2a: `eshapes`-Free Bounded Code Callees (`CodeBoundedCtxNz0`)

`CodeBoundedCtxNz0` drops the `s.eshapes` conjunct of `CodeBoundedCtxNz`. Proves
`codeBoundedCtxNz0_of_sk_make` and the bounded return (`code_n.toNat < 2 ^ 40`) plus
`CodeBoundedCtxNz0` preservation for `ws_get_code`, `get_code`, `record_pre_state_read`,
`ws_get_account_optional`, `get_pre_state_account_optional`, `get_account_optional`,
`get_account`, and `ext_code_of`.
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
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
open R10Shards.GbodyProcessMsg
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-- `CodeBoundedCtxNz` without any `s.eshapes` assumption. -/
def CodeBoundedCtxNz0 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) : Prop :=
  ArenaReady s ∧ WorldTypedWith s S Nd ∧ CodeDbPayloadBoundedNz s S ∧
    s.code = originalRuntimeCode

theorem codeBoundedCtxNz0_with_locals_clock {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (h : CodeBoundedCtxNz0 s S Nd) :
    CodeBoundedCtxNz0 {s with locals := locals, clock := clock} S Nd := by
  obtain ⟨hA, hWT, hCB, hc⟩ := h
  refine ⟨localsFree_arenaReady s locals clock hA,
    ⟨(tablesTyped_with_locals s locals clock S).2 hWT.1, hWT.2.1, hWT.2.2.1, hWT.2.2.2⟩,
    (codeDbPayloadBoundedNz_with_locals_clock s S locals clock).2 hCB, hc⟩

theorem codeBoundedCtxNz0_setVar {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (x : MlS) (v : ValueHOL 64) (h : CodeBoundedCtxNz0 s S Nd) :
    CodeBoundedCtxNz0 (setVarHOLFinite x v s) S Nd := by
  have heq : setVarHOLFinite x v s =
      {s with locals := (setVarHOLFinite x v s).locals, clock := s.clock} := by
    cases s; rfl
  rw [heq]; exact codeBoundedCtxNz0_with_locals_clock _ _ h

theorem codeBoundedCtxNz0_emptyLocals {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (h : CodeBoundedCtxNz0 s S Nd) :
    CodeBoundedCtxNz0 (emptyLocalsHOLFinite s) S Nd := by
  have heq : emptyLocalsHOLFinite s =
      {s with locals := (emptyLocalsHOLFinite s).locals, clock := s.clock} := by
    cases s; rfl
  rw [heq]; exact codeBoundedCtxNz0_with_locals_clock _ _ h

theorem codeBoundedCtxNz0_resVar {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (h : CodeBoundedCtxNz0 s S Nd) :
    CodeBoundedCtxNz0 {s with locals := L} S Nd :=
  codeBoundedCtxNz0_with_locals_clock L s.clock h


/-- Raising `StateErr` never returns or falls through, regardless of `s.eshapes`. -/
theorem raise_not_none_or_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (eid : MlS) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.raise eid e)).1 ≠ none ∧
    ∀ v, (evaluateHOLFiniteState s (.raise eid e)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_raise]
  rcases s.eshapes.lookup eid with _ | sh
  · simp
  · dsimp only
    rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | val
    · simp
    · dsimp only
      split <;> simp

theorem ws_get_code_tail_return_cases0 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (found code code_n : BitVec 64)
    (hr : s.locals.lookup (ofString "r") =
      some (.rStruct [.val (.word found), .val (.word code), .val (.word code_n)]))
    (hn : found ≠ 0 → code_n.toNat < 2 ^ 40) :
    Ret s
      (.seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0))
        (.raise (ofString "StateErr") (.const 2)) .skip)
        (.return (.rstruct [.rfield 1 (.var .local (ofString "r")),
          .rfield 2 (.var .local (ofString "r"))])))
      (fun v post => found ≠ 0 ∧
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧
        code_n.toNat < 2 ^ 40 ∧ post = {s with locals := post.locals, clock := post.clock}) := by
  by_cases hf : found = 0
  · subst found
    intro v hv
    have he : ev s (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0)) =
        some (.val (.word 1)) := by
      simp [ev, evalHOLExact, hr, Compiler.Encoders.Asm.wordCmpHOL]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hv
    unfold ev at he
    rw [he] at hv
    dsimp only at hv
    obtain ⟨hne, hret⟩ := raise_not_none_or_returned s (ofString "StateErr") (.const 2)
    rcases hr1 : evaluateHOLFiniteState s (.raise (ofString "StateErr") (.const 2)) with ⟨r1, s1⟩
    rw [hr1] at hne hret hv
    cases r1 with
    | none => exact absurd rfl hne
    | some r1' => exact absurd hv (hret v)
  · intro v hv
    exact ⟨hf, ws_get_code_tail_return s found code code_n hr (hn hf) hf v hv⟩

theorem ws_get_code_nodedb_return0 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (args : List (ExpHOL 64))
    (hcallee : ∀ values body callee ret v post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "nodedb_lookup") values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      ∃ found code code_n : BitVec 64,
        v = .rStruct [.val (.word found), .val (.word code), .val (.word code_n)] ∧
        (found ≠ 0 → code_n.toNat < 2 ^ 40)) :
    Ret s (.decCall (ofString "r") (.comb [.one, .one, .one]) (ofString "nodedb_lookup") args
      (.seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0))
        (.raise (ofString "StateErr") (.const 2)) .skip)
        (.return (.rstruct [.rfield 1 (.var .local (ofString "r")),
          .rfield 2 (.var .local (ofString "r"))]))))
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  apply Ret.decCall_gen
  intro values body callee ret v post ha hl hb
  obtain ⟨found, code, code_n, hv, hn⟩ := hcallee values body callee ret v post ha hl hb
  subst v
  let st := setVarHOLFinite (ofString "r")
    (.rStruct [.val (.word found), .val (.word code), .val (.word code_n)]) {post with locals := s.locals}
  have hr : st.locals.lookup (ofString "r") =
      some (.rStruct [.val (.word found), .val (.word code), .val (.word code_n)]) := by
    simp [st, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  intro w hw
  obtain ⟨_, hv', hb', _⟩ := ws_get_code_tail_return_cases0 st found code code_n hr hn w hw
  exact ⟨code, code_n, hv', hb'⟩

theorem ws_get_code_return_of_nodedb0 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hnodedb : ∀ values body callee ret post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "code_hash"), .var .global (ofString "empty_code_hash"),
          .const 32] = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "memeq") values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned (.val (.word 0))), post) →
      let st := setVarHOLFinite (ofString "eq") (.val (.word 0)) {post with locals := s.locals}
      ∀ values' body' callee' ret' v' post',
        evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
          [.load .one (.op .add [.var .global (ofString "ws"), .const 16]),
            .var .local (ofString "code_hash")] = some values' →
        lookupCodeHOLFinite st.code.lookup (ofString "nodedb_lookup") values' =
          some (body', callee', ret') →
        evaluateHOLFiniteState (callEntryStateHOLFinite st callee') body' =
          (some (.returned v'), post') →
        ∃ found code code_n : BitVec 64,
          v' = .rStruct [.val (.word found), .val (.word code), .val (.word code_n)] ∧
          (found ≠ 0 → code_n.toNat < 2 ^ 40)) :
    Ret s (sourceFnBody Guest.Software.guestFn_ws_get_code)
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  rw [ws_get_code_body_eq]
  apply ws_get_code_compare_return_of_tail
  intro values body callee ret eqw post ha hl hb hz
  subst eqw
  exact ws_get_code_nodedb_return0 _ _ (hnodedb values body callee ret post ha hl hb)

theorem ws_get_code_return_of_codeBoundedCtxNz0 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz0 s S Nd) :
    Ret s (sourceFnBody Guest.Software.guestFn_ws_get_code)
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  apply ws_get_code_return_of_nodedb0
  intro values body callee ret post _ hl hb st values' body' callee' ret' v' post' ha' hl' hb'
  have hpost := ro_wsGetCodeCallee_state s (ofString "memeq") (by decide)
    values body callee ret (.val (.word 0)) post hctx.2.2.2 hl hb
  have hst_ctx : CodeBoundedCtxNz0 st S Nd := by
    dsimp only [st]
    have hp_ctx : CodeBoundedCtxNz0 post S Nd := by
      rw [hpost]; exact codeBoundedCtxNz0_with_locals_clock post.locals post.clock hctx
    exact codeBoundedCtxNz0_setVar _ _ (codeBoundedCtxNz0_resVar s.locals hp_ctx)
  obtain ⟨hA, hWT, hCB, hc⟩ := hst_ctx
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
  exact (nodedb_lookup_call_return_bounded st db hash hc hWF_db hent_db _ _ _ _ _ hl' hb').2

theorem ws_get_code_call_return_of_codeBoundedCtxNz0 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz0 s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "ws_get_code") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    ∃ code code_n : BitVec 64,
      v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40 := by
  have hc := hctx.2.2.2
  have hbody := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "ws_get_code")
    _ _ body _ ret values callee (by rw [hc]; exact lookup_ws_get_code_local) hl
  subst body
  exact ws_get_code_return_of_codeBoundedCtxNz0
    (codeBoundedCtxNz0_with_locals_clock callee (s.clock - 1) hctx) v (congrArg Prod.fst hb)


theorem get_code_cache_step_bounded0 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {owner : String} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64}
    (hctx : CodeBoundedCtxNz0 s S Nd) (ho : owner = "ts" ∨ owner = "bs")
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (getCodeCacheArgs owner) = some values)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_get") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    post = {s with locals := post.locals, clock := post.clock} ∧
    ∃ found ptr : BitVec 64,
      v = .rStruct [.val (.word found), .val (.word ptr)] ∧
      (found ≠ 0 → WordsOK s (ptr.toNat, 16) ∧ memW s (ptr.toNat + 8) < 2 ^ 40) := by
  obtain ⟨hA, hWT, hCB, hc⟩ := hctx
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
  exact get_code_cache_call_resume_bounded s db hash body callee ret v post
    hc hWF_db hent_db hl hb

theorem codeBoundedCtxNz0_after_sk_call {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz0 s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "sk_make") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeBoundedCtxNz0 post S Nd := by
  obtain ⟨hAs, hWT, hCB, hc⟩ := hctx
  have hbody := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "sk_make")
    _ _ _ _ _ values callee (by rw [hc]; exact lookup_sk_make) hl
  subst body
  let ce := callEntryStateHOLFinite s callee
  have hAce : ArenaReady ce := localsFree_arenaReady s _ _ hAs
  have hWTce : WorldTypedWith ce S Nd :=
    ⟨(tablesTyped_with_locals s callee (s.clock - 1) S).2 hWT.1, hWT.2.1, hWT.2.2.1, hWT.2.2.2⟩
  have hWce : WorldTyped ce S := (worldTyped_iff_with _ _).2 ⟨Nd, hWTce⟩
  have hfit : ∀ (_ : globN ce "sk_buf" ≠ 0), globN ce "sk_buf" + 52 ≤ 2 ^ 64 :=
    fun hn => key_buffer_fit_of_world s hAs hWT.2.2.1 hn
  have hr : Resumes (evaluateHOLFiniteState ce (sourceFnBody Guest.Software.guestFn_sk_make)).1 := by
    rw [hb]; exact Or.inl ⟨v, rfl⟩
  obtain ⟨_, _, _, hsk_nz, heff⟩ := eval_sk_make_body_evm ce hc hAs.1.memaddrs hfit (by rw [hb]; simp) hr
  rw [hb] at heff
  have hd : ∀ i ∈ worldTypedIvls ce S Nd, Disj i (globN ce "sk_buf", 52) := fun i hi => by
    have hd0 := bufferRegion_disj_le hWTce ("sk_buf", 64) (by decide) (by decide) 52 (by decide) i hi
    simpa [bufferRegion, hsk_nz] using Disj.flip hd0
  have hAp := arenaReady_of_sk_make hAce hc hAs.1.memaddrs hfit v hb
  obtain ⟨hWp, hfixed⟩ := worldTypedWith_of_sk_make hAce hAp hWTce hc hAs.1.memaddrs hfit v hb hd
  have hp_tabs := typed_tables_preserved_of_sk_make hWce hc hAs.1.memaddrs hfit v hb
  have hcells := @sameTypedCells_of_sk_make F ce post S Nd hc hAs.1.memaddrs hfit v hb hd
  have hm := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata ce
    (sourceFnBody Guest.Software.guestFn_sk_make)
  rw [hb] at hm
  have hg : ∀ name, globN post name = globN s name := fun name => by
    change globN post name = globN ce name; unfold globN; rw [heff.globals]
  refine ⟨hAp, hWp, ?_, hm.1.trans hc⟩
  intro g k hgk hgnz hdb_nz
  have hgnz_s : globN s g ≠ 0 := by rwa [hg g] at hgnz
  have hrec_eq : memW post (globN post g + k) = memW s (globN s g + k) := by
    rw [hg g]
    have hrec_sz : ∃ sz, (g, sz) ∈ typedRecords ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
      rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨40, by decide, by decide, by decide⟩
      · exact ⟨80, by decide, by decide, by decide⟩
      · exact ⟨72, by decide, by decide, by decide⟩
    obtain ⟨sz, htr, _, _⟩ := hrec_sz
    have hce_g : globN ce g = globN s g := rfl
    have hrec_ivl : (globN ce g, sz) ∈ worldTypedIvls ce S Nd := by
      unfold worldTypedIvls; simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.2 ⟨(g, sz), htr, by rw [hce_g]; simp [hgnz_s]⟩)))))
    have hf : (globN s g, sz) ∈ fixedObjects s := by
      unfold fixedObjects
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.2 ⟨(g, sz), (show ∀ r ∈ typedRecords, r ∈ globalBuffers by decide) _ htr, by simp [hgnz_s]⟩)))
    have ha_lt : globN s g + k < 2 ^ 64 := by
      rcases hWT.2.2.1.1 _ hf with hz | ⟨ha, _⟩
      · dsimp at hz; omega
      · have hb0 := allocated_le_2pow64 hAs.2 ha; dsimp only at hb0; omega
    unfold memW
    rw [hcells.2.2.2.2.1 (globN s g + k) ha_lt ⟨(globN ce g, sz), hrec_ivl, by rw [hce_g]; omega, by rw [hce_g]; omega⟩]
    rfl
  rw [hrec_eq] at hdb_nz ⊢
  have hdb_S : memW s (globN s g + k) ∈ S := by
    have hrin : RootIn S (memW s (globN s g + k)) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
      rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hWT.1.2.2.2.1 16 (by decide) hgnz_s
      · exact hWT.1.2.2.2.2.1 48 (by decide) hgnz_s
      · exact hWT.1.2.2.2.2.2.1 48 (by decide) hgnz_s
    exact hrin.resolve_left hdb_nz
  exact codeDbPayloadBounded_of_sk_make (memW s (globN s g + k))
    ((codeDbPayloadBounded_with_locals_clock s S _ callee (s.clock - 1)).2 (hCB g k hgk hgnz_s hdb_nz))
    hc hAs.1.memaddrs hfit v hb hAce hAp (hp_tabs _ hdb_S).1 (fun t ht => (hp_tabs t ht).2) hfixed

theorem seq_call0_htab_set_codeBoundedCtxNz0 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (recName roleName : String) (off : BitVec 64)
    (kExp vExp : ExpHOL 64) (cont : ProgHOL 64)
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hctx : CodeBoundedCtxNz0 s S Nd)
    (hoff_lt : off.toNat < sourceBase)
    (hrole_ne_ws16 : "ws+16" ≠ roleName)
    (hrole_ne_bs48 : "bs+48" ≠ roleName)
    (hrole_ne_ts48 : "ts+48" ≠ roleName)
    (hwrs : ∀ (st : PanSemStateFiniteExact 64 F),
      globN st recName ≠ 0 → memW st (globN st recName + off.toNat) ≠ 0 →
      (memW st (globN st recName + off.toNat), roleName) ∈ worldRoleSlots st)
    (hslot_nonVal : ∀ (st : PanSemStateFiniteExact 64 F),
      TablesTyped st S → globN st recName ≠ 0 → memW st (globN st recName + off.toNat) ≠ 0 →
      memW st (globN st recName + off.toNat) ∈ S ∧
      (globN st "bs" ≠ 0 → memW st (globN st "bs" + 32) ≠ memW st (globN st recName + off.toNat)) ∧
      (globN st "ts" ≠ 0 → memW st (globN st "ts" + 32) ≠ memW st (globN st recName + off.toNat)) ∧
      globN st "bal_accounts" ≠ memW st (globN st recName + off.toNat) ∧
      (∀ ad ∈ balRecords st, memW st ad ≠ memW st (globN st recName + off.toNat)) ∧
      (globN st "ws" ≠ 0 → memW st (globN st "ws" + 32) ≠ memW st (globN st recName + off.toNat)))
    (hk : ∀ (cpost : PanSemStateFiniteExact 64 F), CodeBoundedCtxNz0 {cpost with locals := s.locals} S Nd →
      Ret {cpost with locals := s.locals} cont Φ) :
    Ret s (.seq (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString recName), .const off]), kExp, vExp]) cont) Φ := by
  apply Ret.seq_call00
  intro values body' callee ret' v cpost hargs hl hrun
  obtain ⟨hAs, hWT, hCB, hc⟩ := hctx
  have hW_s : WorldTyped s S := (worldTyped_iff_with _ _).2 ⟨Nd, hWT⟩
  obtain ⟨v1, _, _, he1, _, _, hc_t, _, _⟩ := callee_param_three s (ofString "htab_set")
    (ofString "t") (ofString "key") (ofString "value") .one .one .one _ _
    (by rw [hc]; exact EvmFrameSpecs.lookup_htab_set) _ _ _ values body' callee ret' hargs hl
  obtain ⟨tw, rfl, htw_nat, hrec_nz⟩ := evalAt_loadG_nz s hAs.1 recName off hoff_lt v1 he1
  let entry := callEntryStateHOLFinite s callee
  have hloc_t : locN entry "t" = memW s (globN s recName + off.toNat) := by
    simp [entry, locN, callEntryStateHOLFinite, hc_t, htw_nat]
  have hnz_at := FunSpec.at_lookup EvmFrameSpecs.nz_htab_set s hc values body' callee ret' hl
    (guestInv_callEntry s callee hAs.1) (by rw [hrun]; simp)
  rw [hrun] at hnz_at
  have ht0_nz : memW s (globN s recName + off.toNat) ≠ 0 := by
    rw [← hloc_t]; exact hnz_at (Or.inl ⟨v, rfl⟩)
  have hnv := hslot_nonVal s hWT.1 hrec_nz ht0_nz
  have hArgWF : HtabArgWF entry := by
    refine ⟨localsFree_arenaReady s _ _ hAs, ?_, ?_⟩
    · rw [hloc_t]; exact (htabWF_with_locals s callee (s.clock - 1) _).2 (hWT.1.2.1 _ hnv.1).1
    · rw [hloc_t]; exact fun i hi => ((hWT.1.2.1 _ hnv.1).2 i hi).1
  have hexit := FunSpec.at_lookup htab_set_spec s hc values body' callee ret' hl
    hArgWF (by rw [hrun]; simp)
  rw [hrun] at hexit
  have hex : HtabExit entry cpost := hexit v rfl
  have hm_meta := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata entry body'
  rw [hrun] at hm_meta
  have hex_copy : HtabExit entry cpost := hex
  obtain ⟨hAp, hwf_t0, hh0, _, hhp, hfp_t0, hfr_t0, hg_t0⟩ := hex
  rw [hloc_t] at hwf_t0 hh0 hfp_t0 hfr_t0
  have hhp_entry : globN entry "heap_ptr" = globN s "heap_ptr" := rfl
  rw [hhp_entry] at hhp hfp_t0 hfr_t0
  have hfp_s : htabFootprint entry (memW s (globN s recName + off.toNat)) =
      htabFootprint s (memW s (globN s recName + off.toNat)) := rfl
  rw [hfp_s] at hfp_t0 hfr_t0
  obtain ⟨hWT_post, hrk⟩ := worldTypedWith_of_htabExit_nonValue hAs hWT hm_meta.2.2.1 hg_t0 hnv
    hAp hwf_t0 hh0 hhp hfp_t0 hfr_t0
  have hg_kept : GlobalsKept ["heap_ptr", "scratch_ptr"] s cpost := fun k hk_in =>
    hg_t0 k (fun hm => by
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm hk_in
      exact hk_in (Or.inl hm))
  have hroots := code_roots_kept_of_recordsKept hrk hg_kept (by intro g k hm i hi; cases hi)
  have hg_eq : ∀ g ∈ (["ws", "ts", "bs"] : List String), globN cpost g = globN s g := fun g hg => by
    have hn : ofString g ∉ (["heap_ptr"] : List String).map ofString := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> decide
    exact globN_eq_of_lookup (hg_t0 (ofString g) hn)
  have hCB_post : CodeDbPayloadBoundedNz cpost S := by
    intro g k hgk hgnz hdb_ne0
    have hg_g : globN cpost g = globN s g := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
      rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hg_eq "ws" (by decide)
      · exact hg_eq "bs" (by decide)
      · exact hg_eq "ts" (by decide)
    have hgnz_s : globN s g ≠ 0 := by rwa [← hg_g]
    have hroot_eq : memW cpost (globN cpost g + k) = memW s (globN s g + k) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
      rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hroots "ws" 16 (by decide) hgnz_s
      · exact hroots "bs" 48 (by decide) hgnz_s
      · exact hroots "ts" 48 (by decide) hgnz_s
    rw [hroot_eq] at hdb_ne0 ⊢
    have hdb_S : memW s (globN s g + k) ∈ S := by
      have hroot_in : RootIn S (memW s (globN s g + k)) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
        rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hWT.1.2.2.2.1 16 (by decide) hgnz_s
        · exact hWT.1.2.2.2.2.1 48 (by decide) hgnz_s
        · exact hWT.1.2.2.2.2.2.1 48 (by decide) hgnz_s
      exact hroot_in.resolve_left hdb_ne0
    have hdb_ne_t0 : memW s (globN s g + k) ≠ locN entry "t" := by
      rw [hloc_t]
      have ht0_wrs := hwrs s hrec_nz ht0_nz
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
      rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hdb_wrs : (memW s (globN s "ws" + 16), "ws+16") ∈ worldRoleSlots s := by
          apply mem_worldRoleSlots_recRole s "ws" 16 "ws+16" hgnz_s hdb_ne0
          apply List.mem_append.2; left; apply List.mem_append.2; left; unfold recRoles; simp [hgnz_s]
        exact slot_ne_of_diff_nonshared_role hWT.1.2.2.2.2.2.2.2.2.2.2.2 hdb_wrs ht0_wrs hrole_ne_ws16
      · have hdb_wrs : (memW s (globN s "bs" + 48), "bs+48") ∈ worldRoleSlots s := by
          apply mem_worldRoleSlots_recRole s "bs" 48 "bs+48" hgnz_s hdb_ne0
          apply List.mem_append.2; left; apply List.mem_append.2; right; unfold recRoles; simp [hgnz_s]
        exact slot_ne_of_diff_nonshared_role hWT.1.2.2.2.2.2.2.2.2.2.2.2 hdb_wrs ht0_wrs hrole_ne_bs48
      · have hdb_wrs : (memW s (globN s "ts" + 48), "ts+48") ∈ worldRoleSlots s := by
          apply mem_worldRoleSlots_recRole s "ts" 48 "ts+48" hgnz_s hdb_ne0
          apply List.mem_append.2; right; unfold recRoles; simp [hgnz_s]
        exact slot_ne_of_diff_nonshared_role hWT.1.2.2.2.2.2.2.2.2.2.2.2 hdb_wrs ht0_wrs hrole_ne_ts48
    have hCB_entry : CodeDbPayloadBounded entry S (memW s (globN s g + k)) :=
      (codeDbPayloadBounded_with_locals_clock s S _ callee (s.clock - 1)).2 (hCB g k hgk hgnz_s hdb_ne0)
    have hW_entry : WorldTyped entry S :=
      (worldTyped_with_locals s callee (s.clock - 1) S).2 hW_s
    have hbal_entry : globN entry "bal_accounts" ≠ locN entry "t" ∧
        ∀ ad ∈ balRecords entry, memW entry ad ≠ locN entry "t" := by
      rw [hloc_t]; exact ⟨hnv.2.2.2.1, hnv.2.2.2.2.1⟩
    exact codeDbPayloadBounded_of_nonbal_htab_exit (memW s (globN s g + k)) hCB_entry
      (localsFree_arenaReady s _ _ hAs) hW_entry hdb_S (by rw [hloc_t]; exact hnv.1)
      hdb_ne_t0 hex_copy hbal_entry
  exact hk cpost (codeBoundedCtxNz0_resVar s.locals ⟨hAp, hWT_post, hCB_post, hm_meta.1.trans hc⟩)

theorem seq_call0_htab_set_ts40_codeBoundedCtxNz0 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (kExp vExp : ExpHOL 64) (cont : ProgHOL 64)
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hctx : CodeBoundedCtxNz0 s S Nd)
    (hk : ∀ (cpost : PanSemStateFiniteExact 64 F), CodeBoundedCtxNz0 {cpost with locals := s.locals} S Nd →
      Ret {cpost with locals := s.locals} cont Φ) :
    Ret s (.seq (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "ts"), .const 40]), kExp, vExp]) cont) Φ := by
  refine seq_call0_htab_set_codeBoundedCtxNz0 "ts" "ts+40" 40 kExp vExp cont hctx
    (by decide) (by decide) (by decide) (by decide)
    (fun st hts ht0 => ?_) (fun st hT hts ht0 => nonValueSlot_ts40 st S hT hts ht0) hk
  have hc40 : (40 : BitVec 64).toNat = 40 := by decide
  rw [hc40] at ht0 ⊢
  apply mem_worldRoleSlots_recRole st "ts" 40 "ts+40" hts ht0
  apply List.mem_append.2; right; unfold recRoles; simp [hts]

theorem seq_call0_htab_set_ts8_codeBoundedCtxNz0 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (kExp vExp : ExpHOL 64) (cont : ProgHOL 64)
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hctx : CodeBoundedCtxNz0 s S Nd)
    (hk : ∀ (cpost : PanSemStateFiniteExact 64 F), CodeBoundedCtxNz0 {cpost with locals := s.locals} S Nd →
      Ret {cpost with locals := s.locals} cont Φ) :
    Ret s (.seq (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), kExp, vExp]) cont) Φ := by
  refine seq_call0_htab_set_codeBoundedCtxNz0 "ts" "ts+8" 8 kExp vExp cont hctx
    (by decide) (by decide) (by decide) (by decide)
    (fun st hts ht0 => ?_) (fun st hT hts ht0 => nonValueSlot_ts8 st S hT hts ht0) hk
  have hc8 : (8 : BitVec 64).toNat = 8 := by decide
  rw [hc8] at ht0 ⊢
  apply mem_worldRoleSlots_recRole st "ts" 8 "ts+8" hts ht0
  apply List.mem_append.2; right; unfold recRoles; simp [hts]

theorem seq_call0_htab_set_bs72_codeBoundedCtxNz0 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (kExp vExp : ExpHOL 64) (cont : ProgHOL 64)
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hctx : CodeBoundedCtxNz0 s S Nd)
    (hk : ∀ (cpost : PanSemStateFiniteExact 64 F), CodeBoundedCtxNz0 {cpost with locals := s.locals} S Nd →
      Ret {cpost with locals := s.locals} cont Φ) :
    Ret s (.seq (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "bs"), .const 72]), kExp, vExp]) cont) Φ := by
  refine seq_call0_htab_set_codeBoundedCtxNz0 "bs" "bs+72" 72 kExp vExp cont hctx
    (by decide) (by decide) (by decide) (by decide)
    (fun st hbs ht0 => ?_) (fun st hT hbs ht0 => nonValueSlot_bs72 st S hT hbs ht0) hk
  have hc72 : (72 : BitVec 64).toNat = 72 := by decide
  rw [hc72] at ht0 ⊢
  apply mem_worldRoleSlots_recRole st "bs" 72 "bs+72" hbs ht0
  apply List.mem_append.2; left; apply List.mem_append.2; right; unfold recRoles; simp [hbs]

theorem get_code_access_tail_return_of_codeBoundedCtxNz0 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz0 s S Nd) :
    Ret s getCodeAccessTail (fun v _ => ∃ code code_n : BitVec 64,
      v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  unfold getCodeAccessTail
  apply Ret.decCall_gen
  intro values body callee ret v post _ hl hb
  have hst := codeBoundedCtxNz0_setVar (ofString "k") v
    (codeBoundedCtxNz0_resVar s.locals (codeBoundedCtxNz0_after_sk_call hctx hl hb))
  refine seq_call0_htab_set_ts40_codeBoundedCtxNz0 _ _ _ hst ?_
  intro cpost hcpost
  apply Ret.decCall_gen
  intro vals2 b2 cl2 r2 v2 p2 _ hl2 hb2
  obtain ⟨code, code_n, rfl, hlt⟩ := ws_get_code_call_return_of_codeBoundedCtxNz0 hcpost hl2 hb2
  apply Ret.ret
  intro vr hvr
  simp [evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] at hvr
  exact ⟨code, code_n, hvr.symm, hlt⟩

theorem get_code_cache_tail_return_of_codeBoundedCtxNz0 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz0 s S Nd) :
    Ret s getCodeCacheTail
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  unfold getCodeCacheTail getCodeCacheBranch
  apply Ret.decCall_gen
  intro vals1 b1 cl1 r1 v1 p1 ha1 hl1 hb1
  obtain ⟨hp1_ro, found1, ptr1, hv1, hrec1⟩ :=
    get_code_cache_step_bounded0 hctx (Or.inl rfl) ha1 hl1 hb1
  subst v1
  let st1 := setVarHOLFinite (ofString "w")
    (.rStruct [.val (.word found1), .val (.word ptr1)]) {p1 with locals := s.locals}
  have hst1_ctx : CodeBoundedCtxNz0 st1 S Nd := by
    have hp1_ctx : CodeBoundedCtxNz0 p1 S Nd := by
      rw [hp1_ro]; exact codeBoundedCtxNz0_with_locals_clock p1.locals p1.clock hctx
    exact codeBoundedCtxNz0_setVar (ofString "w") _
      (codeBoundedCtxNz0_with_locals_clock s.locals p1.clock hp1_ctx)
  have hw1 : st1.locals.lookup (ofString "w") =
      some (.rStruct [.val (.word found1), .val (.word ptr1)]) := by
    simp [st1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hrec1' : found1 ≠ 0 → WordsOK st1 (ptr1.toNat, 16) ∧ memW st1 (ptr1.toNat + 8) < 2 ^ 40 := by
    intro hfnz
    have hst1_eq : st1 = {s with locals := st1.locals, clock := p1.clock} := by
      simp only [st1, setVarHOLFinite]; rw [hp1_ro]
    rw [hst1_eq]; exact hrec1 hfnz
  apply get_code_cache_branch_return_bounded st1 found1 ptr1 _ hw1 hrec1'
  intro _
  apply Ret.seq_callAssign_gen
  intro vals2 b2 cl2 r2 v2 p2 ha2 hl2 hb2
  obtain ⟨hp2_ro, found2, ptr2, hv2, hrec2⟩ :=
    get_code_cache_step_bounded0 hst1_ctx (Or.inr rfl) ha2 hl2 hb2
  subst v2
  let st2 := setVarHOLFinite (ofString "w")
    (.rStruct [.val (.word found2), .val (.word ptr2)]) {p2 with locals := st1.locals}
  have hst2_ctx : CodeBoundedCtxNz0 st2 S Nd := by
    have hp2_ctx : CodeBoundedCtxNz0 p2 S Nd := by
      rw [hp2_ro]; exact codeBoundedCtxNz0_with_locals_clock p2.locals p2.clock hst1_ctx
    exact codeBoundedCtxNz0_setVar (ofString "w") _
      (codeBoundedCtxNz0_with_locals_clock st1.locals p2.clock hp2_ctx)
  have hw2 : st2.locals.lookup (ofString "w") =
      some (.rStruct [.val (.word found2), .val (.word ptr2)]) := by
    simp [st2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hrec2' : found2 ≠ 0 → WordsOK st2 (ptr2.toNat, 16) ∧ memW st2 (ptr2.toNat + 8) < 2 ^ 40 := by
    intro hfnz
    have hst2_eq : st2 = {st1 with locals := st2.locals, clock := p2.clock} := by
      simp only [st2, setVarHOLFinite]; rw [hp2_ro]
    rw [hst2_eq]; exact hrec2 hfnz
  apply get_code_cache_branch_return_bounded st2 found2 ptr2 _ hw2 hrec2'
  intro _
  exact get_code_access_tail_return_of_codeBoundedCtxNz0 hst2_ctx

theorem getCodeCacheContinuationStrong_of_codeBoundedCtxNz0 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz0 s S Nd) :
    GetCodeCacheContinuationStrong s := by
  intro values body callee ret post _ hl hb
  have hpost_ro := ro_wsGetCodeCallee_state s (ofString "memeq") (by decide)
    values body callee ret (.val (.word 0)) post hctx.2.2.2 hl hb
  have hpost_ctx : CodeBoundedCtxNz0 post S Nd := by
    rw [hpost_ro]; exact codeBoundedCtxNz0_with_locals_clock post.locals post.clock hctx
  exact get_code_cache_tail_return_of_codeBoundedCtxNz0
    (codeBoundedCtxNz0_setVar (ofString "eq") (.val (.word 0))
      (codeBoundedCtxNz0_with_locals_clock s.locals post.clock hpost_ctx))

theorem get_code_call_return_of_codeBoundedCtxNz0 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz0 s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "get_code") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    ∃ code code_n : BitVec 64,
      v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40 :=
  get_code_call_return_of_cache_tail s values body callee ret v post hctx.2.2.2
    (getCodeCacheContinuationStrong_of_codeBoundedCtxNz0
      (codeBoundedCtxNz0_with_locals_clock callee (s.clock - 1) hctx)) hl hb

theorem codeBoundedCtxNz0_of_witness_effect {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz0 s S Nd) (heff : WorldEff s post [] wsBufs wsGw) :
    CodeBoundedCtxNz0 post S Nd := by
  obtain ⟨hA, hWT, hCB, _⟩ := hctx
  have hg_kept : ∀ g ∈ (["ws", "ts", "bs"] : List String), globN post g = globN s g := fun g hg => by
    have hn : ofString g ∉ wsGw.map ofString := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> decide
    unfold globN; rw [heff.gw_kept _ hn]
  have hroots := code_roots_kept_of_witness_effect hWT hA heff
  refine ⟨heff.arena, worldTypedWith_of_witness_effect hWT hA heff, ?_, heff.code⟩
  intro g k hgk hgnz hdb_nz
  have hg_eq : globN post g = globN s g := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
    rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hg_kept "ws" (by decide)
    · exact hg_kept "bs" (by decide)
    · exact hg_kept "ts" (by decide)
  have hgnz_s : globN s g ≠ 0 := by rwa [← hg_eq]
  have hroot_eq : memW post (globN post g + k) = memW s (globN s g + k) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
    rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hroots "ws" 16 (by decide) hgnz_s
    · exact hroots "bs" 48 (by decide) hgnz_s
    · exact hroots "ts" 48 (by decide) hgnz_s
  rw [hroot_eq] at hdb_nz ⊢
  have hdb_S : memW s (globN s g + k) ∈ S := by
    have hroot_in : RootIn S (memW s (globN s g + k)) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
      rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hWT.1.2.2.2.1 16 (by decide) hgnz_s
      · exact hWT.1.2.2.2.2.1 48 (by decide) hgnz_s
      · exact hWT.1.2.2.2.2.2.1 48 (by decide) hgnz_s
    exact hroot_in.resolve_left hdb_nz
  exact codeDbPayloadBounded_of_witness_effect (hCB g k hgk hgnz_s hdb_nz) hWT hA heff hdb_S

theorem acct_new_execution_codeBoundedCtxNz0 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz0 s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "acct_new") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeBoundedCtxNz0 post S Nd := by
  have hc := hctx.2.2.2
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
  exact codeBoundedCtxNz0_of_witness_effect hctx heff

theorem ws_get_account_execution_codeBoundedCtxNz0 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz0 s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "ws_get_account_optional") values =
      some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeBoundedCtxNz0 post S Nd :=
  codeBoundedCtxNz0_of_witness_effect hctx
    (ws_get_account_execution_effect s values body callee ret v post hctx.2.2.2 hctx.1 hl hb)

theorem acct_empty_execution_codeBoundedCtxNz0 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz0 s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "acct_empty") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeBoundedCtxNz0 post S Nd := by
  have hc := hctx.2.2.2
  have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "acct_empty") values =
      some (body, callee, ret) := by rwa [← hc]
  have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "acct_empty")
    _ _ body _ ret values callee lookup_acct_empty hl'
  have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_acct_empty) = (some (.returned v), post) := by
    rw [← hb, hbody]; rfl
  have hret : Ret (callEntryStateHOLFinite s callee) (sourceFnBody Guest.Software.guestFn_acct_empty)
      (fun _ p => CodeBoundedCtxNz0 p S Nd) := by
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
    have hs1 := codeBoundedCtxNz0_setVar (ofString "a") v1
      (codeBoundedCtxNz0_with_locals_clock (callEntryStateHOLFinite s callee).locals m1.clock
        (acct_new_execution_codeBoundedCtxNz0 (codeBoundedCtxNz0_with_locals_clock callee (s.clock - 1) hctx) hl1 hb1))
    apply Ret.ret
    intro _ _
    exact codeBoundedCtxNz0_resVar _ (codeBoundedCtxNz0_emptyLocals hs1)
  have hres := hret v (by rw [hb'])
  rwa [hb'] at hres

theorem record_pre_state_read_execution_codeBoundedCtxNz0 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz0 s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "record_pre_state_read") values =
      some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeBoundedCtxNz0 post S Nd := by
  have hc := hctx.2.2.2
  have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "record_pre_state_read") values =
      some (body, callee, ret) := by rwa [← hc]
  have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
    (ofString "record_pre_state_read") _ _ body _ ret values callee lookup_record_pre_state_read hl'
  have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_record_pre_state_read) = (some (.returned v), post) := by
    rw [← hb, hbody]; rfl
  have hret : Ret (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_record_pre_state_read)
      (fun _ p => CodeBoundedCtxNz0 p S Nd) := by
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_record_pre_state_read,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      Option.map_none, Option.map_some, List.map_cons, List.map_nil]
    refine seq_call0_htab_set_bs72_codeBoundedCtxNz0 _ _ _
      (codeBoundedCtxNz0_with_locals_clock callee (s.clock - 1) hctx) ?_
    intro cpost hcpost
    apply Ret.ret
    intro _ _
    exact codeBoundedCtxNz0_emptyLocals hcpost
  have hres := hret v (by rw [hb'])
  rwa [hb'] at hres

theorem get_pre_state_account_optional_execution_codeBoundedCtxNz0 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz0 s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "get_pre_state_account_optional") values =
      some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeBoundedCtxNz0 post S Nd := by
  have hc := hctx.2.2.2
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
      (fun _ p => CodeBoundedCtxNz0 p S Nd) := by
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_get_pre_state_account_optional,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      Option.map_none, Option.map_some, List.map_cons, List.map_nil]
    refine seq_call0_htab_set_ts8_codeBoundedCtxNz0 _ _ _
      (codeBoundedCtxNz0_with_locals_clock callee (s.clock - 1) hctx) ?_
    intro s1 hs1
    apply Ret.decCall_gen
    intro vals2 b2 cl2 r2 v2 p2 _ hl2 hb2
    have hp2_ro := readonly_cache_call_state
      {s1 with locals := (callEntryStateHOLFinite s callee).locals} vals2 b2 cl2 r2 v2 p2 hs1.2.2.2 hl2 hb2
    have hs2 : CodeBoundedCtxNz0 (setVarHOLFinite (ofString "w") v2
        {p2 with locals := (callEntryStateHOLFinite s callee).locals}) S Nd := by
      have hp2_ctx : CodeBoundedCtxNz0 p2 S Nd := by
        rw [hp2_ro]; exact codeBoundedCtxNz0_with_locals_clock p2.locals p2.clock hs1
      exact codeBoundedCtxNz0_setVar (ofString "w") v2
        (codeBoundedCtxNz0_with_locals_clock (callEntryStateHOLFinite s callee).locals p2.clock hp2_ctx)
    apply Ret.seq_ite
    intro w _
    refine ⟨fun _ => Ret.seq_return (fun _ _ => codeBoundedCtxNz0_resVar _ (codeBoundedCtxNz0_emptyLocals hs2)), fun _ => ?_⟩
    apply Ret.seq_skip
    apply Ret.seq_call00
    intro vals3 b3 cl3 r3 v3 p3 _ hl3 hb3
    have hs3 := codeBoundedCtxNz0_with_locals_clock
      (setVarHOLFinite (ofString "w") v2 {p2 with locals := (callEntryStateHOLFinite s callee).locals}).locals
      p3.clock (record_pre_state_read_execution_codeBoundedCtxNz0 hs2 hl3 hb3)
    apply Ret.decCall_gen
    intro vals4 b4 cl4 r4 v4 p4 _ hl4 hb4
    have hs4 := codeBoundedCtxNz0_setVar (ofString "a") v4
      (codeBoundedCtxNz0_with_locals_clock
        (setVarHOLFinite (ofString "w") v2 {p2 with locals := (callEntryStateHOLFinite s callee).locals}).locals
        p4.clock (ws_get_account_execution_codeBoundedCtxNz0 hs3 hl4 hb4))
    apply Ret.ret
    intro _ _
    exact codeBoundedCtxNz0_resVar _ (codeBoundedCtxNz0_resVar _ (codeBoundedCtxNz0_emptyLocals hs4))
  have hres := hret v (by rw [hb'])
  rwa [hb'] at hres

theorem get_account_optional_execution_codeBoundedCtxNz0 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz0 s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "get_account_optional") values =
      some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeBoundedCtxNz0 post S Nd := by
  have hc := hctx.2.2.2
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
      (fun _ p => CodeBoundedCtxNz0 p S Nd) := by
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_get_account_optional,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      Option.map_none, Option.map_some, List.map_cons, List.map_nil]
    refine seq_call0_htab_set_ts8_codeBoundedCtxNz0 _ _ _
      (codeBoundedCtxNz0_with_locals_clock callee (s.clock - 1) hctx) ?_
    intro s1 hs1
    apply Ret.decCall_gen
    intro vals2 b2 cl2 r2 v2 p2 _ hl2 hb2
    have hp2_ro := readonly_cache_call_state
      {s1 with locals := (callEntryStateHOLFinite s callee).locals} vals2 b2 cl2 r2 v2 p2 hs1.2.2.2 hl2 hb2
    have hs2 : CodeBoundedCtxNz0 (setVarHOLFinite (ofString "w") v2
        {p2 with locals := (callEntryStateHOLFinite s callee).locals}) S Nd := by
      have hp2_ctx : CodeBoundedCtxNz0 p2 S Nd := by
        rw [hp2_ro]; exact codeBoundedCtxNz0_with_locals_clock p2.locals p2.clock hs1
      exact codeBoundedCtxNz0_setVar (ofString "w") v2
        (codeBoundedCtxNz0_with_locals_clock (callEntryStateHOLFinite s callee).locals p2.clock hp2_ctx)
    apply Ret.seq_ite
    intro w _
    refine ⟨fun _ => Ret.seq_return (fun _ _ => codeBoundedCtxNz0_resVar _ (codeBoundedCtxNz0_emptyLocals hs2)), fun _ => ?_⟩
    apply Ret.seq_skip
    apply Ret.decCall_gen
    intro vals3 b3 cl3 r3 v3 p3 _ hl3 hb3
    have hs3 := codeBoundedCtxNz0_setVar (ofString "a") v3
      (codeBoundedCtxNz0_with_locals_clock
        (setVarHOLFinite (ofString "w") v2 {p2 with locals := (callEntryStateHOLFinite s callee).locals}).locals
        p3.clock (get_pre_state_account_optional_execution_codeBoundedCtxNz0 hs2 hl3 hb3))
    apply Ret.ret
    intro _ _
    exact codeBoundedCtxNz0_resVar _ (codeBoundedCtxNz0_resVar _ (codeBoundedCtxNz0_emptyLocals hs3))
  have hres := hret v (by rw [hb'])
  rwa [hb'] at hres

theorem get_account_execution_codeBoundedCtxNz0 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz0 s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "get_account") values =
      some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeBoundedCtxNz0 post S Nd := by
  have hc := hctx.2.2.2
  have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "get_account") values = some (body, callee, ret) := by rwa [← hc]
  have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
    (ofString "get_account") _ _ body _ ret values callee lookup_get_account hl'
  have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_get_account) = (some (.returned v), post) := by
    rw [← hb, hbody]; rfl
  have hret : Ret (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_get_account)
      (fun _ p => CodeBoundedCtxNz0 p S Nd) := by
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
    have hs1 := codeBoundedCtxNz0_setVar (ofString "a") v1
      (codeBoundedCtxNz0_with_locals_clock (callEntryStateHOLFinite s callee).locals p1.clock
        (get_account_optional_execution_codeBoundedCtxNz0 (codeBoundedCtxNz0_with_locals_clock callee (s.clock - 1) hctx) hl1 hb1))
    apply Ret.seq_ite
    intro w _
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · apply Ret.seq_callAssign_gen
      intro vals2 b2 cl2 r2 v2 p2 _ hl2 hb2
      have hs2 := codeBoundedCtxNz0_setVar (ofString "a") v2
        (codeBoundedCtxNz0_with_locals_clock
          (setVarHOLFinite (ofString "a") v1 {p1 with locals := (callEntryStateHOLFinite s callee).locals}).locals
          p2.clock (acct_empty_execution_codeBoundedCtxNz0 hs1 hl2 hb2))
      apply Ret.ret
      intro _ _
      exact codeBoundedCtxNz0_resVar _ (codeBoundedCtxNz0_emptyLocals hs2)
    · apply Ret.seq_skip
      apply Ret.ret
      intro _ _
      exact codeBoundedCtxNz0_resVar _ (codeBoundedCtxNz0_emptyLocals hs1)
  have hres := hret v (by rw [hb'])
  rwa [hb'] at hres

theorem ext_code_of_return_of_codeBoundedCtxNz0 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz0 s S Nd) :
    Ret s (sourceFnBody Guest.Software.guestFn_ext_code_of)
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  refine ext_code_of_return_of_cache_tail s hctx.2.2.2 ?_
  intro values body callee ret v post _ hl hb vals b cl r st _ _
  have hpost := get_account_execution_codeBoundedCtxNz0 hctx hl hb
  have hst : CodeBoundedCtxNz0 st S Nd := codeBoundedCtxNz0_setVar (ofString "a") v
    (codeBoundedCtxNz0_with_locals_clock s.locals post.clock hpost)
  exact getCodeCacheContinuationStrong_of_codeBoundedCtxNz0
    (codeBoundedCtxNz0_with_locals_clock cl (st.clock - 1) hst)

theorem ext_code_of_call_return_of_codeBoundedCtxNz0 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz0 s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "ext_code_of") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    ∃ code code_n : BitVec 64,
      v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40 := by
  have hc := hctx.2.2.2
  have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "ext_code_of") values =
      some (body, callee, ret) := by rwa [← hc]
  have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
    (ofString "ext_code_of") _ _ body _ ret values callee lookup_ext_code_of hl'
  have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_ext_code_of) = (some (.returned v), post) := by
    rw [← hb, hbody]; rfl
  exact ext_code_of_return_of_codeBoundedCtxNz0
    (codeBoundedCtxNz0_with_locals_clock callee (s.clock - 1) hctx) v (congrArg Prod.fst hb')

