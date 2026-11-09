import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB3cCodeBoundedPres

/-!
# Scratch Rung B3d: `get_code` & `ext_code_of` Bounded Return (`CodeBoundedCtxNz`)

Closes `seq_call0_htab_set_codeBoundedCtxNz`, `get_code`, `acct_new`, `acct_empty`,
`ws_get_account_optional`, `record_pre_state_read`, `get_pre_state_account_optional`,
`get_account_optional`, `get_account`, and `ext_code_of` under `CodeBoundedCtxNz`.
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

section ExtCodeBounded
open R10Shards.GbodyProcessMsg
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

theorem seq_call0_htab_set_codeBoundedCtxNz {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (recName roleName : String) (off : BitVec 64)
    (kExp vExp : ExpHOL 64) (cont : ProgHOL 64)
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hctx : CodeBoundedCtxNz s S Nd)
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
    (hk : ∀ (cpost : PanSemStateFiniteExact 64 F), CodeBoundedCtxNz {cpost with locals := s.locals} S Nd →
      Ret {cpost with locals := s.locals} cont Φ) :
    Ret s (.seq (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString recName), .const off]), kExp, vExp]) cont) Φ := by
  apply Ret.seq_call00
  intro values body' callee ret' v cpost hargs hl hrun
  obtain ⟨hAs, hWT, hCB, hc, hs⟩ := hctx
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
  exact hk cpost (codeBoundedCtxNz_resVar s.locals ⟨hAp, hWT_post, hCB_post, hm_meta.1.trans hc, hm_meta.2.2.2.2 ▸ hs⟩)

theorem seq_call0_htab_set_ts40_codeBoundedCtxNz {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (kExp vExp : ExpHOL 64) (cont : ProgHOL 64)
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hctx : CodeBoundedCtxNz s S Nd)
    (hk : ∀ (cpost : PanSemStateFiniteExact 64 F), CodeBoundedCtxNz {cpost with locals := s.locals} S Nd →
      Ret {cpost with locals := s.locals} cont Φ) :
    Ret s (.seq (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "ts"), .const 40]), kExp, vExp]) cont) Φ := by
  refine seq_call0_htab_set_codeBoundedCtxNz "ts" "ts+40" 40 kExp vExp cont hctx
    (by decide) (by decide) (by decide) (by decide)
    (fun st hts ht0 => ?_) (fun st hT hts ht0 => nonValueSlot_ts40 st S hT hts ht0) hk
  have hc40 : (40 : BitVec 64).toNat = 40 := by decide
  rw [hc40] at ht0 ⊢
  apply mem_worldRoleSlots_recRole st "ts" 40 "ts+40" hts ht0
  apply List.mem_append.2; right; unfold recRoles; simp [hts]

theorem seq_call0_htab_set_ts8_codeBoundedCtxNz {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (kExp vExp : ExpHOL 64) (cont : ProgHOL 64)
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hctx : CodeBoundedCtxNz s S Nd)
    (hk : ∀ (cpost : PanSemStateFiniteExact 64 F), CodeBoundedCtxNz {cpost with locals := s.locals} S Nd →
      Ret {cpost with locals := s.locals} cont Φ) :
    Ret s (.seq (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), kExp, vExp]) cont) Φ := by
  refine seq_call0_htab_set_codeBoundedCtxNz "ts" "ts+8" 8 kExp vExp cont hctx
    (by decide) (by decide) (by decide) (by decide)
    (fun st hts ht0 => ?_) (fun st hT hts ht0 => nonValueSlot_ts8 st S hT hts ht0) hk
  have hc8 : (8 : BitVec 64).toNat = 8 := by decide
  rw [hc8] at ht0 ⊢
  apply mem_worldRoleSlots_recRole st "ts" 8 "ts+8" hts ht0
  apply List.mem_append.2; right; unfold recRoles; simp [hts]

theorem seq_call0_htab_set_bs72_codeBoundedCtxNz {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (kExp vExp : ExpHOL 64) (cont : ProgHOL 64)
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hctx : CodeBoundedCtxNz s S Nd)
    (hk : ∀ (cpost : PanSemStateFiniteExact 64 F), CodeBoundedCtxNz {cpost with locals := s.locals} S Nd →
      Ret {cpost with locals := s.locals} cont Φ) :
    Ret s (.seq (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "bs"), .const 72]), kExp, vExp]) cont) Φ := by
  refine seq_call0_htab_set_codeBoundedCtxNz "bs" "bs+72" 72 kExp vExp cont hctx
    (by decide) (by decide) (by decide) (by decide)
    (fun st hbs ht0 => ?_) (fun st hT hbs ht0 => nonValueSlot_bs72 st S hT hbs ht0) hk
  have hc72 : (72 : BitVec 64).toNat = 72 := by decide
  rw [hc72] at ht0 ⊢
  apply mem_worldRoleSlots_recRole st "bs" 72 "bs+72" hbs ht0
  apply List.mem_append.2; left; apply List.mem_append.2; right; unfold recRoles; simp [hbs]

theorem get_code_access_tail_return_of_codeBoundedCtxNz {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz s S Nd) :
    Ret s getCodeAccessTail (fun v _ => ∃ code code_n : BitVec 64,
      v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  unfold getCodeAccessTail
  apply Ret.decCall_gen
  intro values body callee ret v post _ hl hb
  have hst := codeBoundedCtxNz_setVar (ofString "k") v
    (codeBoundedCtxNz_resVar s.locals (codeBoundedCtxNz_after_sk_call hctx hl hb))
  refine seq_call0_htab_set_ts40_codeBoundedCtxNz _ _ _ hst ?_
  intro cpost hcpost
  apply Ret.decCall_gen
  intro vals2 b2 cl2 r2 v2 p2 _ hl2 hb2
  obtain ⟨code, code_n, rfl, hlt⟩ := ws_get_code_call_return_of_codeBoundedCtxNz hcpost hl2 hb2
  apply Ret.ret
  intro vr hvr
  simp [evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] at hvr
  exact ⟨code, code_n, hvr.symm, hlt⟩

theorem get_code_cache_tail_return_of_codeBoundedCtxNz {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz s S Nd) :
    Ret s getCodeCacheTail
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  unfold getCodeCacheTail getCodeCacheBranch
  apply Ret.decCall_gen
  intro vals1 b1 cl1 r1 v1 p1 ha1 hl1 hb1
  obtain ⟨hp1_ro, found1, ptr1, hv1, hrec1⟩ :=
    get_code_cache_step_bounded hctx (Or.inl rfl) ha1 hl1 hb1
  subst v1
  let st1 := setVarHOLFinite (ofString "w")
    (.rStruct [.val (.word found1), .val (.word ptr1)]) {p1 with locals := s.locals}
  have hst1_ctx : CodeBoundedCtxNz st1 S Nd := by
    have hp1_ctx : CodeBoundedCtxNz p1 S Nd := by
      rw [hp1_ro]; exact codeBoundedCtxNz_with_locals_clock p1.locals p1.clock hctx
    exact codeBoundedCtxNz_setVar (ofString "w") _
      (codeBoundedCtxNz_with_locals_clock s.locals p1.clock hp1_ctx)
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
    get_code_cache_step_bounded hst1_ctx (Or.inr rfl) ha2 hl2 hb2
  subst v2
  let st2 := setVarHOLFinite (ofString "w")
    (.rStruct [.val (.word found2), .val (.word ptr2)]) {p2 with locals := st1.locals}
  have hst2_ctx : CodeBoundedCtxNz st2 S Nd := by
    have hp2_ctx : CodeBoundedCtxNz p2 S Nd := by
      rw [hp2_ro]; exact codeBoundedCtxNz_with_locals_clock p2.locals p2.clock hst1_ctx
    exact codeBoundedCtxNz_setVar (ofString "w") _
      (codeBoundedCtxNz_with_locals_clock st1.locals p2.clock hp2_ctx)
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
  exact get_code_access_tail_return_of_codeBoundedCtxNz hst2_ctx

theorem getCodeCacheContinuationStrong_of_codeBoundedCtxNz {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz s S Nd) :
    GetCodeCacheContinuationStrong s := by
  intro values body callee ret post _ hl hb
  have hpost_ro := ro_wsGetCodeCallee_state s (ofString "memeq") (by decide)
    values body callee ret (.val (.word 0)) post hctx.2.2.2.1 hl hb
  have hpost_ctx : CodeBoundedCtxNz post S Nd := by
    rw [hpost_ro]; exact codeBoundedCtxNz_with_locals_clock post.locals post.clock hctx
  exact get_code_cache_tail_return_of_codeBoundedCtxNz
    (codeBoundedCtxNz_setVar (ofString "eq") (.val (.word 0))
      (codeBoundedCtxNz_with_locals_clock s.locals post.clock hpost_ctx))

theorem get_code_call_return_of_codeBoundedCtxNz {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {ret : ShapeHOL} {v : ValueHOL 64} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "get_code") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    ∃ code code_n : BitVec 64,
      v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40 :=
  get_code_call_return_of_cache_tail s values body callee ret v post hctx.2.2.2.1
    (getCodeCacheContinuationStrong_of_codeBoundedCtxNz
      (codeBoundedCtxNz_with_locals_clock callee (s.clock - 1) hctx)) hl hb

theorem codeBoundedCtxNz_of_witness_effect {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hctx : CodeBoundedCtxNz s S Nd) (heff : WorldEff s post [] wsBufs wsGw) :
    CodeBoundedCtxNz post S Nd := by
  obtain ⟨hA, hWT, hCB, _, hs⟩ := hctx
  have hg_kept : ∀ g ∈ (["ws", "ts", "bs"] : List String), globN post g = globN s g := fun g hg => by
    have hn : ofString g ∉ wsGw.map ofString := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> decide
    unfold globN; rw [heff.gw_kept _ hn]
  have hroots := code_roots_kept_of_witness_effect hWT hA heff
  refine ⟨heff.arena, worldTypedWith_of_witness_effect hWT hA heff, ?_, heff.code, heff.eshapes.symm ▸ hs⟩
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

end ExtCodeBounded

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
