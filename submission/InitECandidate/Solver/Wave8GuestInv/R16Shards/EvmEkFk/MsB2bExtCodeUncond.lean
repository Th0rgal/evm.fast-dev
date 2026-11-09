import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB2GetCodeUncond

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

section ExtCodeUncond
open R10Shards.GbodyProcessMsg
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-- `sk_make` call execution preserves `CodeStrongCtxNz`. -/
theorem codeStrongCtxNz_after_sk_call {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret : ShapeHOL} {v : ValueHOL 64}
    (hctx : CodeStrongCtxNz s S Nd)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "sk_make") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    CodeStrongCtxNz post S Nd := by
  obtain ⟨hAs, hWT, hCS, hc, hs⟩ := hctx
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
  have hd : ∀ i ∈ worldTypedIvls ce S Nd, Disj i (globN ce "sk_buf", 52) := by
    intro i hi
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
  refine ⟨hAp, hWp, ?_, hm.1.trans hc, hm.2.2.2.2 ▸ hs⟩
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
    obtain ⟨sz, htr, hk8, hksz⟩ := hrec_sz
    have hce_g : globN ce g = globN s g := rfl
    have hrec_ivl : (globN ce g, sz) ∈ worldTypedIvls ce S Nd := by
      unfold worldTypedIvls
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.2 ⟨(g, sz), htr, by rw [hce_g]; simp [hgnz_s]⟩)))))
    have hf : (globN s g, sz) ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      exact List.mem_map.2 ⟨(g, sz), (show ∀ r ∈ typedRecords, r ∈ globalBuffers by decide) _ htr, by simp [hgnz_s]⟩
    have ha_lt : globN s g + k < 2 ^ 64 := by
      rcases hWT.2.2.1.1 _ hf with hz | ⟨ha, _⟩
      · dsimp at hz; omega
      · have hb := allocated_le_2pow64 hAs.2 ha
        dsimp only at hb
        omega
    unfold memW
    have hmem_eq := hcells.2.2.2.2.1 (globN s g + k) ha_lt
      ⟨(globN ce g, sz), hrec_ivl, by rw [hce_g]; omega, by rw [hce_g]; omega⟩
    rw [hmem_eq]
    rfl
  rw [hrec_eq] at hdb_nz ⊢
  have hdb_S : memW s (globN s g + k) ∈ S := by
    have hrin : RootIn S (memW s (globN s g + k)) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
      rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hWT.1.2.2.2.1 16 (by decide) hgnz_s
      · exact hWT.1.2.2.2.2.1 48 (by decide) hgnz_s
      · exact hWT.1.2.2.2.2.2.1 48 (by decide) hgnz_s
    rcases hrin with h0 | hm_s
    · exact absurd h0 hdb_nz
    · exact hm_s
  have hCS_ce : CodeDbPayloadStrong ce S (memW s (globN s g + k)) :=
    (codeDbPayloadStrong_with_locals_clock s S _ callee (s.clock - 1)).2 (hCS g k hgk hgnz_s hdb_nz)
  exact codeDbPayloadStrong_of_sk_make (memW s (globN s g + k)) hCS_ce hc hAs.1.memaddrs hfit v hb
    hAce hAp (hp_tabs _ hdb_S).1 (fun t ht => (hp_tabs t ht).2) hfixed

/-- `htab_set(*(recName + off), kExp, vExp)` on a non-value role distinct from code DBs preserves `CodeStrongCtxNz`. -/
theorem seq_call0_htab_set_codeStrongCtxNz {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (recName roleName : String) (off : BitVec 64)
    (kExp vExp : ExpHOL 64) (cont : ProgHOL 64)
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hctx : CodeStrongCtxNz s S Nd)
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
    (hk : ∀ (cpost : PanSemStateFiniteExact 64 F), CodeStrongCtxNz {cpost with locals := s.locals} S Nd →
      Ret {cpost with locals := s.locals} cont Φ) :
    Ret s (.seq (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString recName), .const off]), kExp, vExp]) cont) Φ := by
  apply Ret.seq_call00
  intro values body' callee ret' v cpost hargs hl hrun
  obtain ⟨hAs, hWT, hCS, hc, hs⟩ := hctx
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
  have hbe_post : cpost.be = s.be := hm_meta.2.2.1
  have hc_post : cpost.code = originalRuntimeCode := hm_meta.1.trans hc
  have hs_post : cpost.eshapes.lookup (ofString "StateErr") = some .one := hm_meta.2.2.2.2 ▸ hs
  have hex_copy : HtabExit entry cpost := hex
  obtain ⟨hAp, hwf_t0, hh0, _, hhp, hfp_t0, hfr_t0, hg_t0⟩ := hex
  rw [hloc_t] at hwf_t0 hh0 hfp_t0 hfr_t0
  have hhp_entry : globN entry "heap_ptr" = globN s "heap_ptr" := rfl
  rw [hhp_entry] at hhp hfp_t0 hfr_t0
  have hh0_s : hdr cpost (memW s (globN s recName + off.toNat)) 0 = hdr s (memW s (globN s recName + off.toNat)) 0 := hh0
  have hfp_s : htabFootprint entry (memW s (globN s recName + off.toNat)) =
      htabFootprint s (memW s (globN s recName + off.toNat)) := rfl
  rw [hfp_s] at hfp_t0 hfr_t0
  have hfr_s : FrameOutside s cpost (htabFootprint s (memW s (globN s recName + off.toNat)))
      (globN s "heap_ptr", globN cpost "heap_ptr" - globN s "heap_ptr") := hfr_t0
  have hg_s : ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s.globals.lookup k = cpost.globals.lookup k := hg_t0
  obtain ⟨hWT_post, hrk⟩ := worldTypedWith_of_htabExit_nonValue hAs hWT hbe_post hg_s hnv
    hAp hwf_t0 hh0_s hhp hfp_t0 hfr_s
  have hg_kept : GlobalsKept ["heap_ptr", "scratch_ptr"] s cpost := fun k hk =>
    hg_s k (fun hm => by
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm hk
      exact hk (Or.inl hm))
  have hroots := code_roots_kept_of_recordsKept hrk hg_kept (by intro g k hm i hi; cases hi)
  have hg_eq : ∀ g ∈ (["ws", "ts", "bs"] : List String), globN cpost g = globN s g := fun g hg => by
    have hn : ofString g ∉ (["heap_ptr"] : List String).map ofString := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> decide
    exact globN_eq_of_lookup (hg_s (ofString g) hn)
  have hCS_post : CodeDbPayloadNonzero cpost S := by
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
      rcases hroot_in with h0 | hm
      · exact absurd h0 hdb_ne0
      · exact hm
    have hdb_ne_t0 : memW s (globN s g + k) ≠ locN entry "t" := by
      rw [hloc_t]
      have ht0_wrs := hwrs s hrec_nz ht0_nz
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hgk
      rcases hgk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hdb_wrs : (memW s (globN s "ws" + 16), "ws+16") ∈ worldRoleSlots s := by
          apply mem_worldRoleSlots_recRole s "ws" 16 "ws+16" hgnz_s hdb_ne0
          apply List.mem_append.2; left; apply List.mem_append.2; left
          unfold recRoles; simp [hgnz_s]
        exact slot_ne_of_diff_nonshared_role hWT.1.2.2.2.2.2.2.2.2.2.2.2 hdb_wrs ht0_wrs hrole_ne_ws16
      · have hdb_wrs : (memW s (globN s "bs" + 48), "bs+48") ∈ worldRoleSlots s := by
          apply mem_worldRoleSlots_recRole s "bs" 48 "bs+48" hgnz_s hdb_ne0
          apply List.mem_append.2; left; apply List.mem_append.2; right
          unfold recRoles; simp [hgnz_s]
        exact slot_ne_of_diff_nonshared_role hWT.1.2.2.2.2.2.2.2.2.2.2.2 hdb_wrs ht0_wrs hrole_ne_bs48
      · have hdb_wrs : (memW s (globN s "ts" + 48), "ts+48") ∈ worldRoleSlots s := by
          apply mem_worldRoleSlots_recRole s "ts" 48 "ts+48" hgnz_s hdb_ne0
          apply List.mem_append.2; right
          unfold recRoles; simp [hgnz_s]
        exact slot_ne_of_diff_nonshared_role hWT.1.2.2.2.2.2.2.2.2.2.2.2 hdb_wrs ht0_wrs hrole_ne_ts48
    have hCS_entry : CodeDbPayloadStrong entry S (memW s (globN s g + k)) :=
      (codeDbPayloadStrong_with_locals_clock s S (memW s (globN s g + k)) callee (s.clock - 1)).2
        (hCS g k hgk hgnz_s hdb_ne0)
    have hW_entry : WorldTyped entry S :=
      (worldTyped_with_locals s callee (s.clock - 1) S).2 hW_s
    have hbal_entry : globN entry "bal_accounts" ≠ locN entry "t" ∧
        ∀ ad ∈ balRecords entry, memW entry ad ≠ locN entry "t" := by
      rw [hloc_t]; exact ⟨hnv.2.2.2.1, hnv.2.2.2.2.1⟩
    exact codeDbPayloadStrong_of_nonbal_htab_exit (memW s (globN s g + k)) hCS_entry
      (localsFree_arenaReady s _ _ hAs) hW_entry hdb_S (by rw [hloc_t]; exact hnv.1)
      hdb_ne_t0 hex_copy hbal_entry
  have hctx_cpost : CodeStrongCtxNz cpost S Nd := ⟨hAp, hWT_post, hCS_post, hc_post, hs_post⟩
  exact hk cpost (codeStrongCtxNz_resVar s.locals hctx_cpost)

theorem seq_call0_htab_set_ts40_codeStrongCtxNz {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (kExp vExp : ExpHOL 64) (cont : ProgHOL 64)
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hctx : CodeStrongCtxNz s S Nd)
    (hk : ∀ (cpost : PanSemStateFiniteExact 64 F), CodeStrongCtxNz {cpost with locals := s.locals} S Nd →
      Ret {cpost with locals := s.locals} cont Φ) :
    Ret s (.seq (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "ts"), .const 40]), kExp, vExp]) cont) Φ := by
  refine seq_call0_htab_set_codeStrongCtxNz "ts" "ts+40" 40 kExp vExp cont hctx
    (by decide) (by decide) (by decide) (by decide)
    (fun st hts ht0 => ?_)
    (fun st hT hts ht0 => nonValueSlot_ts40 st S hT hts ht0) hk
  have hc40 : (40 : BitVec 64).toNat = 40 := by decide
  rw [hc40] at ht0 ⊢
  apply mem_worldRoleSlots_recRole st "ts" 40 "ts+40" hts ht0
  apply List.mem_append.2; right
  unfold recRoles; simp [hts]

/-- Unconditional `getCodeAccessTail` bounded return under `CodeStrongCtxNz`. -/
theorem get_code_access_tail_return_of_codeStrongCtxNz {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hctx : CodeStrongCtxNz s S Nd) :
    Ret s getCodeAccessTail (fun v _ => ∃ code code_n : BitVec 64,
      v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  unfold getCodeAccessTail
  apply Ret.decCall_gen
  intro values body callee ret v post _ hl hb
  have hsk_post := codeStrongCtxNz_after_sk_call hctx hl hb
  have hst : CodeStrongCtxNz (setVarHOLFinite (ofString "k") v {post with locals := s.locals}) S Nd :=
    codeStrongCtxNz_setVar _ _ (codeStrongCtxNz_resVar s.locals hsk_post)
  refine seq_call0_htab_set_ts40_codeStrongCtxNz _ _ _ hst ?_
  intro cpost hcpost
  apply Ret.decCall_gen
  intro vals2 b2 cl2 r2 v2 p2 _ hl2 hb2
  obtain ⟨code, code_n, rfl, hn⟩ := ws_get_code_call_return_of_codeStrongCtxNz hcpost hl2 hb2
  apply Ret.ret
  intro w hw
  simp [ev, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] at hw
  exact ⟨code, code_n, hw.symm, hn⟩

end ExtCodeUncond
end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
