import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB2bExtCodeUncond

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

section AccountChainNz
open R10Shards.GbodyProcessMsg
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-- Unconditional `getCodeCacheTail` return under `CodeStrongCtxNz`. -/
theorem get_code_cache_tail_return_of_codeStrongCtxNz {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hctx : CodeStrongCtxNz s S Nd) :
    Ret s getCodeCacheTail
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  unfold getCodeCacheTail getCodeCacheBranch
  apply Ret.decCall_gen
  intro vals1 b1 cl1 r1 v1 p1 ha1 hl1 hb1
  obtain ⟨hp1_ro, found1, ptr1, hv1, hrec1⟩ :=
    get_code_cache_step_uncond hctx (Or.inl rfl) ha1 hl1 hb1
  subst v1
  let st1 := setVarHOLFinite (ofString "w")
    (.rStruct [.val (.word found1), .val (.word ptr1)]) {p1 with locals := s.locals}
  have hst1_ctx : CodeStrongCtxNz st1 S Nd := by
    have hp1_ctx : CodeStrongCtxNz p1 S Nd := by
      rw [hp1_ro]; exact codeStrongCtxNz_with_locals_clock p1.locals p1.clock hctx
    exact codeStrongCtxNz_setVar (ofString "w") _
      (codeStrongCtxNz_with_locals_clock s.locals p1.clock hp1_ctx)
  have hw1 : st1.locals.lookup (ofString "w") =
      some (.rStruct [.val (.word found1), .val (.word ptr1)]) := by
    simp [st1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hrec1' : found1 ≠ 0 → WordsOK st1 (ptr1.toNat, 16) ∧
      Inside (memW st1 ptr1.toNat, memW st1 (ptr1.toNat + 8)) sourceBase (globN st1 "heap_ptr") := by
    intro hfnz
    have hst1_eq : st1 = {s with locals := st1.locals, clock := p1.clock} := by
      simp only [st1, setVarHOLFinite]; rw [hp1_ro]
    rw [hst1_eq]
    exact hrec1 hfnz
  apply get_code_cache_branch_return st1 hst1_ctx.1 found1 ptr1 _ hw1 hrec1'
  intro _
  apply Ret.seq_callAssign_gen
  intro vals2 b2 cl2 r2 v2 p2 ha2 hl2 hb2
  obtain ⟨hp2_ro, found2, ptr2, hv2, hrec2⟩ :=
    get_code_cache_step_uncond hst1_ctx (Or.inr rfl) ha2 hl2 hb2
  subst v2
  let st2 := setVarHOLFinite (ofString "w")
    (.rStruct [.val (.word found2), .val (.word ptr2)]) {p2 with locals := st1.locals}
  have hst2_ctx : CodeStrongCtxNz st2 S Nd := by
    have hp2_ctx : CodeStrongCtxNz p2 S Nd := by
      rw [hp2_ro]; exact codeStrongCtxNz_with_locals_clock p2.locals p2.clock hst1_ctx
    exact codeStrongCtxNz_setVar (ofString "w") _
      (codeStrongCtxNz_with_locals_clock st1.locals p2.clock hp2_ctx)
  have hw2 : st2.locals.lookup (ofString "w") =
      some (.rStruct [.val (.word found2), .val (.word ptr2)]) := by
    simp [st2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hrec2' : found2 ≠ 0 → WordsOK st2 (ptr2.toNat, 16) ∧
      Inside (memW st2 ptr2.toNat, memW st2 (ptr2.toNat + 8)) sourceBase (globN st2 "heap_ptr") := by
    intro hfnz
    have hst2_eq : st2 = {st1 with locals := st2.locals, clock := p2.clock} := by
      simp only [st2, setVarHOLFinite]; rw [hp2_ro]
    rw [hst2_eq]
    exact hrec2 hfnz
  apply get_code_cache_branch_return st2 hst2_ctx.1 found2 ptr2 _ hw2 hrec2'
  intro _
  exact get_code_access_tail_return_of_codeStrongCtxNz hst2_ctx

/-- Unconditional `GetCodeCacheContinuationStrong` under `CodeStrongCtxNz`. -/
theorem getCodeCacheContinuationStrong_of_codeStrongCtxNz {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hctx : CodeStrongCtxNz s S Nd) :
    GetCodeCacheContinuationStrong s := by
  intro values body callee ret post _ hl hb
  have hpost_ro := ro_wsGetCodeCallee_state s (ofString "memeq") (by decide)
    values body callee ret (.val (.word 0)) post hctx.2.2.2.1 hl hb
  have hpost_ctx : CodeStrongCtxNz post S Nd := by
    rw [hpost_ro]; exact codeStrongCtxNz_with_locals_clock post.locals post.clock hctx
  have hst_ctx := codeStrongCtxNz_setVar (ofString "eq") (.val (.word 0))
    (codeStrongCtxNz_with_locals_clock s.locals post.clock hpost_ctx)
  exact get_code_cache_tail_return_of_codeStrongCtxNz hst_ctx

theorem get_code_return_of_codeStrongCtxNz {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hctx : CodeStrongCtxNz s S Nd) :
    Ret s (sourceFnBody Guest.Software.guestFn_get_code)
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) :=
  get_code_return_of_cache_tail s (getCodeCacheContinuationStrong_of_codeStrongCtxNz hctx)

theorem get_code_call_return_of_codeStrongCtxNz {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeStrongCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "get_code") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    ∃ code code_n : BitVec 64,
      v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40 :=
  get_code_call_return_of_cache_tail s values body callee ret v post hctx.2.2.2.1
    (getCodeCacheContinuationStrong_of_codeStrongCtxNz
      (codeStrongCtxNz_with_locals_clock callee (s.clock - 1) hctx)) hl hb

/-- Any `WorldEff s post [] wsBufs wsGw` preserves `CodeStrongCtxNz` on `(S, Nd)`. -/
theorem codeStrongCtxNz_of_witness_effect {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hctx : CodeStrongCtxNz s S Nd)
    (heff : WorldEff s post [] wsBufs wsGw) :
    CodeStrongCtxNz post S Nd := by
  obtain ⟨hA, hWT, hCS, _hc, hs⟩ := hctx
  have hWT' := worldTypedWith_of_witness_effect hWT hA heff
  have hg_kept : ∀ g ∈ (["ws", "ts", "bs"] : List String), globN post g = globN s g := by
    intro g hg
    have hn : ofString g ∉ wsGw.map ofString := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> decide
    unfold globN; rw [heff.gw_kept _ hn]
  have hroots := code_roots_kept_of_witness_effect hWT hA heff
  refine ⟨heff.arena, hWT', ?_, heff.code, heff.eshapes.symm ▸ hs⟩
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
    rcases hroot_in with h0 | hm
    · exact absurd h0 hdb_nz
    · exact hm
  exact codeDbPayloadStrong_of_witness_effect (hCS g k hgk hgnz_s hdb_nz) hWT hA heff hdb_S

theorem acct_new_params_nz {vals : List (ValueHOL 64)}
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

theorem acct_new_execution_codeStrongCtxNz {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeStrongCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "acct_new") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeStrongCtxNz post S Nd := by
  have hc := hctx.2.2.2.1
  have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "acct_new") values =
      some (body, callee, ret) := by rwa [← hc]
  have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "acct_new")
    _ _ body _ ret values callee lookup_acct_new hl'
  subst hbody
  obtain ⟨wn, wc, vb, hsh_b, hlk_n, hlk_b, hlk_c⟩ := acct_new_params_nz hl'
  have heff0 := worldEff_acct_new s (callEntryStateHOLFinite s callee) (Rl := []) (B := [])
    (gw := ["heap_ptr"]) (by decide)
    ((WorldEff.refl s [] [] ["heap_ptr"] hctx.1 hc).locals_clock _ _)
    hsh_b hlk_n hlk_b hlk_c (by rw [hb]; simp) (by rw [hb]; simp [Resumes])
  rw [hb] at heff0
  have heff : WorldEff s post [] wsBufs wsGw :=
    heff0.mono (by intro _ h; cases h) (by intro _ h; cases h)
      (by intro g hg; simp at hg; subst hg; simp [wsGw])
  exact codeStrongCtxNz_of_witness_effect hctx heff

theorem ws_get_account_execution_codeStrongCtxNz {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeStrongCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "ws_get_account_optional") values =
      some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeStrongCtxNz post S Nd :=
  codeStrongCtxNz_of_witness_effect hctx
    (ws_get_account_execution_effect s values body callee ret v post hctx.2.2.2.1 hctx.1 hl hb)

theorem acct_empty_execution_codeStrongCtxNz {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeStrongCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "acct_empty") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeStrongCtxNz post S Nd := by
  have hc := hctx.2.2.2.1
  have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "acct_empty") values =
      some (body, callee, ret) := by rwa [← hc]
  have hbody := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup (ofString "acct_empty")
    _ _ body _ ret values callee lookup_acct_empty hl'
  have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_acct_empty) = (some (.returned v), post) := by
    rw [← hb, hbody]; rfl
  have hret : Ret (callEntryStateHOLFinite s callee) (sourceFnBody Guest.Software.guestFn_acct_empty)
      (fun _ p => CodeStrongCtxNz p S Nd) := by
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
    have hs1 := codeStrongCtxNz_setVar (ofString "a") v1
      (codeStrongCtxNz_with_locals_clock (callEntryStateHOLFinite s callee).locals m1.clock
        (acct_new_execution_codeStrongCtxNz (codeStrongCtxNz_with_locals_clock callee (s.clock - 1) hctx) hl1 hb1))
    apply Ret.ret
    intro _ _
    exact codeStrongCtxNz_resVar _ (codeStrongCtxNz_emptyLocals hs1)
  have hres := hret v (by rw [hb'])
  rwa [hb'] at hres

end AccountChainNz

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
