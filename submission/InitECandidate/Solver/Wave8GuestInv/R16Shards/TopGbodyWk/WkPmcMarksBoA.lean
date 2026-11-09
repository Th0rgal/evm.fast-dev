import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxRelBasePhase3

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8Leaves.Rlp

open private wk_alloc_local rt_alloc_local zv_memzero_local
  from InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkBlockTxProcess

/-! # `PmcMarksBoStrong`: Block-Output Preservation for `process_message_call` -/

/-! ## 1. `WorldKeepsScBo` for `ws_account_has_storage`, `account_has_storage`, `account_deployable` -/

theorem wkScBo_ws_account_has_storage :
    WorldKeepsScBo WorldOK (bufRegions wsAcctBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      (ofString "ws_account_has_storage") := by
  have hB := validBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsScBo_of_progWStepBo lookup_ws_account_has_storage ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_ws_account_has_storage,
    FrontendCodecComputation.declToHOLStructural,
    FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural,
    FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural,
    FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepBo_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkScBo_ws_storage_root_of ?_
  refine progWStepBo_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsScBo_of_readOnly EvmFrameSpecs.ro_memeq) ?_
  refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_return _ _ _) (progWStepBo_skip _ _)) ?_
  exact progWStepBo_return _ _ _

theorem wkScBo_account_has_storage :
    WorldKeepsScBo WorldOK (bufRegions wsAcctBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      (ofString "account_has_storage") := by
  have hB := validBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsScBo_of_progWStepBo lookup_account_has_storage ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_account_has_storage,
    FrontendCodecComputation.declToHOLStructural,
    FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural,
    FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural,
    FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepBo_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsScBo_of_readOnly EvmFrameSpecs.ro_htab_get) ?_
  refine progWStepBo_seq hB hgw
    (progWStepBo_ite (progWStepBo_ite (progWStepBo_return _ _ _) (progWStepBo_skip _ _)) (progWStepBo_skip _ _)) ?_
  refine progWStepBo_seq hB hgw
    (progWStepBo_call_local (by intro p hp; cases hp) (by intro g hg; cases hg)
      (worldKeepsScBo_of_readOnly EvmFrameSpecs.ro_htab_get)) ?_
  refine progWStepBo_seq hB hgw
    (progWStepBo_ite (progWStepBo_ite (progWStepBo_return _ _ _) (progWStepBo_skip _ _)) (progWStepBo_skip _ _)) ?_
  refine progWStepBo_seq hB hgw
    (progWStepBo_call0 (by intro p hp; cases hp) (by intro g hg; simp at hg; subst hg; simp)
      wkScBo_record_pre_state_read) ?_
  refine progWStepBo_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkScBo_ws_account_has_storage ?_
  exact progWStepBo_return _ _ _

theorem wkScBo_account_deployable :
    WorldKeepsScBo WorldOK (bufRegions wsAcctBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      (ofString "account_deployable") := by
  have hB := validBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsScBo_of_progWStepBo lookup_account_deployable ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_account_deployable,
    FrontendCodecComputation.declToHOLStructural,
    FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural,
    FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural,
    FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStepBo_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkScBo_get_account ?_
  refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_return _ _ _) (progWStepBo_skip _ _)) ?_
  refine progWStepBo_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsScBo_of_readOnly EvmFrameSpecs.ro_memeq) ?_
  refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_return _ _ _) (progWStepBo_skip _ _)) ?_
  refine progWStepBo_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkScBo_account_has_storage ?_
  refine progWStepBo_seq hB hgw (progWStepBo_ite (progWStepBo_return _ _ _) (progWStepBo_skip _ _)) ?_
  exact progWStepBo_return _ _ _

/-! ## 2. Callee Contracts with Block-Output Unhit & Helper Lemmas -/

def RetFrameResultMarksBo : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S Nd =>
    RetFrameResultMarks s r post S Nd ∧ (NonExResult r → PtxBlockOutUnhit s post)

def RetFrameResultMarksExactBo : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S Nd =>
    RetFrameResultMarksExact s r post S Nd ∧ (NonExResult r → PtxBlockOutUnhit s post)

def PmcBoRun {F : Type} (entry : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) (s : PanSemStateFiniteExact 64 F) : Prop :=
  Resumes (evaluateHOLFiniteState s p).1 →
    NonExResult (evaluateHOLFiniteState s p).1 →
    PtxBlockOutUnhit entry (evaluateHOLFiniteState s p).2

def PmcBoCut (phase : ProgHOL 64 → ProgHOL 64)
    (A B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop) : Prop :=
  ∀ {F : Type} (entry : PanSemStateFiniteExact 64 F) (tail : ProgHOL 64),
    (∀ s : PanSemStateFiniteExact 64 F, s.code = originalRuntimeCode →
      B entry s → PmcBoRun entry tail s) →
    ∀ s : PanSemStateFiniteExact 64 F, s.code = originalRuntimeCode →
      A entry s → PmcBoRun entry (phase tail) s

def PmcBoA1 {F : Type} (entry s : PanSemStateFiniteExact 64 F) : Prop :=
  PmcA1 entry s ∧
  PtxBlockOutUnhit entry s ∧
  blockOutObjects s = blockOutObjects entry

def PmcBoA2 {F : Type} (entry s : PanSemStateFiniteExact 64 F) : Prop :=
  PmcA2 entry s ∧
  PtxBlockOutUnhit entry s

theorem nonExResult_not_exception {r : Option (PanSemResultExact 64)}
    {eid : MlS} {ev : ValueHOL 64}
    (h : r = some (.exception eid ev)) : ¬ NonExResult r := by
  subst h
  rintro (h0 | h0 | h0 | ⟨_, h0⟩) <;> cases h0

theorem ptxBlockOutUnhit_of_pmcUpdW {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {w_out w_val : BitVec 64} {off : Nat}
    (hM0 : MsgReady entry) (hAs : ArenaOK s)
    (hw_in : Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s "heap_ptr"))
    (hoff_lt : off < 96)
    (hu : PtxBlockOutUnhit entry s) :
    PtxBlockOutUnhit entry
      { s with memory := pmcUpdW s.memory (BitVec.ofNat 64 (w_out.toNat + off)) w_val } := by
  obtain ⟨S_en, Nd_en, hMA_en⟩ := R10Shards.Fast_GbodyC17ToC21.msgReadyAt_of_msgReady hM0
  have hWT_en := hMA_en.2.1
  have hw_in_sb : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
    ⟨le_trans hM0.1.2.1 hw_in.1, hw_in.2⟩
  have hw_hi : w_out.toNat + 96 ≤ 2 ^ 64 :=
    (R10Shards.Fast_GbodyC17ToC21.ivl_allocated_bound hAs (Or.inl hw_in_sb)).2
  have hx_lt : w_out.toNat + off < 2 ^ 64 := by omega
  apply ptxBlockOutUnhit_of_nonempty
  intro i hi hpos a ha8 hch
  obtain ⟨_, hal_i, _, _⟩ := blockOut_allocated_words hWT_en hi hpos
  have hne : a ≠ BitVec.ofNat 64 (w_out.toNat + off) := by
    intro heq
    have ha_eq : a.toNat = w_out.toNat + off := by
      rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx_lt]
    unfold CellHits at hch
    unfold Inside at hw_in
    have hsep : heapLimit ≤ scratchStart := by decide
    have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.1
    have hsc_lo : scratchStart ≤ globN entry "scratch_ptr" :=
      le_trans hM0.1.2.2.2.1 hM0.1.2.2.2.2.1
    rcases hal_i with ⟨_, hhi_i⟩ | ⟨hlo_i, _⟩ <;> omega
  dsimp only [pmcUpdW]
  rw [if_neg hne]
  exact hu i hi a ha8 hch

theorem pmc_bo_fields_eq_of_recordsKept {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hWT : WorldTypedWith s S Nd)
    (hm_disj : ∀ o ∈ worldOwned s S Nd, Disj (locN s "msg", 176) o)
    (hK : RecordsKept pmcRegions pmcKeep s post) :
    ∀ off ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      globN s "bo" ≠ 0 → memW post (globN s "bo" + off) = memW s (globN s "bo" + off) := by
  intro off hoff hnz
  have hK_buf : RecordsKept (bufRegions pmcBufs) pmcKeep s post := by
    intro rec hrec hnz_r off' hoff' hno_buf
    apply hK rec hrec hnz_r off' hoff'
    intro j hj hch
    dsimp only at hj
    rw [pmcRegions_eq_bufRegions] at hj
    rcases List.mem_cons.1 hj with rfl | hj_buf
    · have hrec_eq : rec.1 = "ws" ∨ rec.1 = "bs" ∨ rec.1 = "ts" ∨ rec.1 = "bo" := by
        simp [pmcKeep] at hrec
        rcases hrec with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
      have hoff_lt_rec : off' + 8 ≤
          (if rec.1 = "ws" then 40 else if rec.1 = "bs" then 80 else if rec.1 = "ts" then 72 else 88) := by
        simp [pmcKeep] at hrec
        rcases hrec with rfl | rfl | rfl | rfl
        · simp at hoff' ⊢; omega
        · simp at hoff' ⊢; omega
        · simp at hoff' ⊢; omega
        · simp at hoff' ⊢; omega
      have hfix_rec : (globN s rec.1,
          if rec.1 = "ws" then 40 else if rec.1 = "bs" then 80 else if rec.1 = "ts" then 72 else 88) ∈
          fixedObjects s := by
        rcases hrec_eq with heq | heq | heq | heq <;> rw [heq] at hnz_r ⊢
        · have hm : (globN s "ws", if globN s "ws" = 0 then 0 else 40) ∈ fixedObjects s := by
            unfold fixedObjects; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
            exact List.mem_map.2 ⟨("ws", 40), by decide, rfl⟩
          simpa [hnz_r] using hm
        · have hm : (globN s "bs", if globN s "bs" = 0 then 0 else 80) ∈ fixedObjects s := by
            unfold fixedObjects; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
            exact List.mem_map.2 ⟨("bs", 80), by decide, rfl⟩
          simpa [hnz_r] using hm
        · have hm : (globN s "ts", if globN s "ts" = 0 then 0 else 72) ∈ fixedObjects s := by
            unfold fixedObjects; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
            exact List.mem_map.2 ⟨("ts", 72), by decide, rfl⟩
          simpa [hnz_r] using hm
        · have hm : (globN s "bo", if globN s "bo" = 0 then 0 else 88) ∈ fixedObjects s := by
            unfold fixedObjects; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
            exact List.mem_map.2 ⟨("bo", 88), by decide, rfl⟩
          simpa [hnz_r] using hm
      have hd := hm_disj _ (by unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix_rec))))
      unfold CellHits at hch; unfold Disj at hd
      rcases hd with h0 | h0 | hl | hr <;> dsimp only at * <;> omega
    · exact hno_buf j hj_buf hch
  exact ptx_bo_field_eq_of_step validBufList_pmcBufs hWT hK_buf
    (offs := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp [pmcKeep]) hnz
    (by simp at hoff ⊢; omega)
    (by simp at hoff; rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp at hoff; rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

/-! ## 3. Phase 1 (`pmcInit`): Block-Output Preservation -/

theorem pmcBoInit_cut : PmcBoCut pmcInit PmcA0 PmcBoA1 := by
  intro F entry tail htail s hcode ⟨hs_eq, hM0⟩
  cases hs_eq
  unfold PmcBoRun
  intro hres hnex
  unfold pmcInit pmcCode at hres hnex ⊢
  simp only [sourceFunctionEntry, Guest.Software.guestFn_process_message_call,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil,
    R13Shards.spinePlug] at hres hnex ⊢
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_skip] at hres hnex ⊢
  dsimp only at hres hnex ⊢
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hres hnex ⊢
  have hargs_al : evalListHOLFinite entry (h := fun a => Classical.propDecidable (entry.memaddrs a))
      [.const 96#64] = some [.val (.word 96#64)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact]
  simp only [hargs_al] at hres hnex ⊢
  rcases hl_al : lookupCodeHOLFinite entry.code.lookup (ofString "alloc") [.val (.word 96#64)]
      with _ | ⟨body_al, callee_al, ret_al⟩
  · simp only [hl_al] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [hl_al] at hres hnex ⊢
    by_cases hclk0 : entry.clock = 0
    · simp only [hclk0, ↓reduceIte] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hclk0, ↓reduceIte] at hres hnex ⊢
      have hpc_al := R10Shards.Fast_GbodyC17ToC21.callee_param_one_exp entry (ofString "alloc")
        (ofString "n") .one _ _ (by rw [hcode]; exact R10Shards.Fast_GbodyC17ToC21.lookup_alloc_fn)
        (.const 96#64) (.val (.word 96#64)) [.val (.word 96#64)] body_al callee_al ret_al rfl hargs_al hl_al
      have hn_al : locN (callEntryStateHOLFinite entry callee_al) "n" = 96 := by
        simp [locN, callEntryStateHOLFinite, hpc_al.2]
      have hl_al_rt : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "alloc") [.val (.word 96#64)] =
          some (body_al, callee_al, ret_al) := by rwa [← hcode]
      have hraw_al := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "alloc")
        [.val (.word 96#64)] body_al callee_al ret_al hl_al_rt
      have hbody_al_eq : body_al = sourceFnBody Guest.Software.guestFn_alloc := by
        unfold lookupCodeHOLExact at hraw_al
        rw [R13Shards.lookup_alloc_r13] at hraw_al
        dsimp only at hraw_al
        split at hraw_al
        · injection hraw_al with hp; exact (Prod.mk.inj hp).1.symm
        · cases hraw_al
      rcases hrun_al : evaluateHOLFiniteState (callEntryStateHOLFinite entry callee_al) body_al with ⟨res_al, post_al⟩
      simp only [hrun_al] at hres hnex ⊢
      have hWOK_en : WorldOK entry := msgReady_worldOK entry hM0
      cases res_al with
      | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      | some br_al =>
        cases br_al with
        | timeOut => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | error => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | «break» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | «continue» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | finalFfi _ => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | exception eid eval =>
          dsimp only at hnex
          exact absurd hnex (nonExResult_not_exception rfl)
        | returned val_al =>
          dsimp only at hres hnex ⊢
          by_cases hsh_al : (shapeEqHOL (shapeOfHOLExact val_al) .one && shapeEqHOL (shapeOfHOLExact val_al) ret_al) = true
          · simp only [hsh_al, ↓reduceIte] at hres hnex ⊢
            have hab_al := R13Shards.alloc_body_resumes_props (callEntryStateHOLFinite entry callee_al)
              hcode (localsFree_arenaReady entry callee_al (entry.clock - 1) hM0.1)
              (by rw [← hbody_al_eq, hrun_al]; exact Or.inl ⟨val_al, rfl⟩)
            dsimp only at hab_al
            rw [← hbody_al_eq, hrun_al] at hab_al
            obtain ⟨_, q_al, _, _, _, _, _, _, hpost_al_g, hpost_al_m, _, _, _, _, _⟩ := hab_al
            have hstep_al := FunSpec.at_lookup wk_alloc_local entry hcode _ body_al callee_al ret_al hl_al
              (localsFree_worldOK entry callee_al (entry.clock - 1) hWOK_en)
              (by rw [hrun_al]; simp)
            rw [hrun_al] at hstep_al
            have hws_al := hstep_al (Or.inl ⟨val_al, rfl⟩)
            have hrt_al := FunSpec.at_lookup rt_alloc_local entry hcode _ body_al callee_al ret_al hl_al
              (localsFree_arenaReady entry callee_al (entry.clock - 1) hM0.1)
              (by rw [hrun_al]; simp)
            rw [hrun_al] at hrt_al
            obtain ⟨w_out, rfl, hAR_al, hAG_al, hw_out8, hw_in_al, hw_ok_al⟩ := hrt_al val_al rfl
            rw [hn_al] at hw_in_al hw_ok_al
            change Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN post_al "heap_ptr") at hw_in_al
            change WordsOK post_al (w_out.toNat, 96) at hw_ok_al
            set s1 := setVarHOLFinite (ofString "out") (.val (.word w_out)) { post_al with locals := entry.locals }
            have hs1_code : s1.code = originalRuntimeCode := hAR_al.1.code
            have hs1_out : s1.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
              simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
            have hs1_msg : s1.locals.lookup (ofString "msg") = entry.locals.lookup (ofString "msg") := by
              simp [s1, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
                show ofString "out" ≠ ofString "msg" by decide]
            obtain ⟨S_en, Nd_en, hMA_en⟩ := R10Shards.Fast_GbodyC17ToC21.msgReadyAt_of_msgReady hM0
            have hu_s1 : PtxBlockOutUnhit entry s1 := by
              intro i hi a ha8 hch
              change post_al.memory a = entry.memory a
              rw [hpost_al_m]; rfl
            have hbo_glob_s1 : globN s1 "bo" = globN entry "bo" := by
              change globN post_al "bo" = globN entry "bo"
              unfold globN; rw [hpost_al_g]
              simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "heap_ptr" ≠ ofString "bo" by decide]
            have hbo_eq_s1 : blockOutObjects s1 = blockOutObjects entry :=
              blockOutObjects_eq_of_ptxBlockOutUnhit hM0.1 hMA_en.2.1 hbo_glob_s1
                (fun off _ _ => by
                  change memW post_al (globN entry "bo" + off) = memW entry (globN entry "bo" + off)
                  unfold memW; rw [hpost_al_m]; rfl)
                hu_s1
            have hws_al_av : WorldStep (fun _ => []) ["heap_ptr"] stdKeep
                (fun _ r' post' S' Nd' => ∀ v', r' = some (.returned v') → ∃ w : BitVec 64,
                  v' = .val (.word w) ∧ IvlsDisj [(w.toNat, 96)] (worldOwned post' S' Nd'))
                entry (some (.returned (.val (.word w_out)))) post_al := by
              obtain ⟨a1, a2, a3, a4, a5⟩ := hws_al
              refine ⟨a1, a2, a3, a4, fun S_x Nd_x hW_x _ => ?_⟩
              obtain ⟨S', Nd', hs, hw', hog, hfo, hq⟩ :=
                a5 S_x Nd_x ((R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals _ _ _ _ _).2 hW_x)
                  (fun x hx => by simp at hx)
              refine ⟨S', Nd', hs, hw', hog, hfo, fun v' hv' => ?_⟩
              obtain ⟨w, hw_eq, hav⟩ := hq v' hv'
              dsimp only at hav; rw [hn_al] at hav
              exact ⟨w, hw_eq, hav⟩
            obtain ⟨S0_s1, Nd_s1, hMA_post_al, hQ0_al, hfp_al⟩ :=
              R10Shards.Fast_GbodyC17ToC21.WorldStep.preserves_msgReadyAt hMA_en hws_al_av
                (fun j hj => by simp at hj) (fun x hx => by simp at hx)
            obtain ⟨w_out', hw_eq, hav0_al⟩ := hQ0_al (.val (.word w_out)) rfl
            injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
            have hMA_s1 : R10Shards.Fast_GbodyC17ToC21.MsgReadyAt s1
                (S0_s1 ++ [memW entry (locN entry "msg" + 152), memW entry (locN entry "msg" + 160)]) Nd_s1 :=
              R10Shards.Fast_GbodyC17ToC21.msgReadyAt_with_locals
                (s := { post_al with locals := entry.locals })
                (by simp [HolFiniteMapExact.update, FUPDATE, show ofString "out" ≠ ofString "msg" by decide])
                hMA_post_al
            have hM_s1 : MsgReady s1 :=
              R10Shards.Fast_GbodyC17ToC21.msgReadyAt_msgReady hMA_s1
            have hWOK_s1 : WorldOK s1 := msgReady_worldOK s1 hM_s1
            have hsp_s1 : globN s1 "scratch_ptr" ≤ globN entry "scratch_ptr" := hAG_al.2
            have hw_in_s1 : Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s1 "heap_ptr") := hw_in_al
            have hw_ok_s1 : WordsOK s1 (w_out.toNat, 96) := hw_ok_al
            have hm_in_en : Inside (locN entry "msg", 176) sourceBase (globN entry "heap_ptr") :=
              hMA_en.2.2.2.2.2.2.2.2.2.2.1
            have hout_ow_s1_at : IvlsDisj [(w_out.toNat, 96)]
                (worldOwned s1 (S0_s1 ++ [memW entry (locN entry "msg" + 152), memW entry (locN entry "msg" + 160)]) Nd_s1) := by
              intro x hx j hj
              simp only [List.mem_singleton] at hx; subst hx
              change j ∈ worldOwned post_al _ Nd_s1 at hj
              unfold worldOwned at hj
              rcases List.mem_append.1 hj with h1 | hnd
              · rcases List.mem_append.1 h1 with htab | hfix
                · rw [List.flatMap_append] at htab
                  rcases List.mem_append.1 htab with htab0 | htab_loc
                  · apply hav0_al (w_out.toNat, 96) (by simp) j
                    unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl htab0)))
                  · obtain ⟨u, hu_loc, hj_fp⟩ := List.mem_flatMap.1 htab_loc
                    rw [hfp_al u hu_loc] at hj_fp
                    have hu_S : u ∈ S_en := by
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_loc
                      rcases hu_loc with rfl | rfl
                      · exact hMA_en.2.2.1
                      · exact hMA_en.2.2.2.1
                    have hal_j : Allocated entry j := ((hMA_en.2.1.1.2.1 u hu_S).2 j hj_fp).1
                    have hsep : heapLimit ≤ scratchStart := by decide
                    obtain ⟨_, _, h2_s, h3_s, _⟩ := hMA_en.1.2
                    rcases hal_j with ⟨_, hhi_j⟩ | ⟨hlo_j, _⟩
                    · exact Or.inr (Or.inr (Or.inr (Nat.le_trans hhi_j hw_in_al.1)))
                    · exact Or.inr (Or.inr (Or.inl (by
                        have hhp_lim : globN post_al "heap_ptr" ≤ heapLimit := hAR_al.2.2.1
                        have hsc_lo : scratchStart ≤ globN entry "scratch_ptr" :=
                          Nat.le_trans h2_s h3_s
                        unfold Inside at hw_in_al; omega)))
                · apply hav0_al (w_out.toNat, 96) (by simp) j
                  unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
              · apply hav0_al (w_out.toNat, 96) (by simp) j
                unfold worldOwned; exact List.mem_append.2 (Or.inr hnd)
            have hws_s1 : WorldStep (fun _ => []) ["heap_ptr", "scratch_ptr"] pmcKeep
                (fun _ _ st S' Nd' => IvlsDisj [(w_out.toNat, 96)] (worldOwned st S' Nd'))
                entry none s1 := by
              have h1 : WorldStep (fun _ => []) ["heap_ptr"] stdKeep
                  (fun _ _ st S' Nd' => IvlsDisj [(w_out.toNat, 96)] (worldOwned st S' Nd'))
                  entry (some (.returned (.val (.word w_out)))) post_al := by
                obtain ⟨a1, a2, a3, a4, a5⟩ := hws_al_av
                refine ⟨a1, a2, a3, a4, fun S_x Nd_x hW_x hD_x => ?_⟩
                obtain ⟨S', Nd', hs, hw', hog, hfo, hq⟩ := a5 S_x Nd_x hW_x hD_x
                obtain ⟨w', hw_eq, hav⟩ := hq (.val (.word w_out)) rfl
                injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
                exact ⟨S', Nd', hs, hw', hog, hfo, hav⟩
              exact worldStep_pmcKeep_with_locals_clock_Q
                (worldStep_pmcKeep_of_stdKeep (by intro g hg; simp at hg; subst hg; decide) h1)
                s1.locals post_al.clock
            rw [evaluateHOLFiniteState_seq_line780] at hres hnex ⊢
            rw [evaluateHOLFiniteState_call] at hres hnex ⊢
            have hargs_mz : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
                [.var .local (ofString "out"), .const 96#64] = some [.val (.word w_out), .val (.word 96#64)] := by
              rw [evalListHOLFinite_eq_toExact]
              simp [evalListHOLExact, evalHOLExact, hs1_out]
            simp only [hargs_mz] at hres hnex ⊢
            rcases hl_mz : lookupCodeHOLFinite s1.code.lookup (ofString "memzero")
                [.val (.word w_out), .val (.word 96#64)] with _ | ⟨body_mz, callee_mz, ret_mz⟩
            · simp only [hl_mz] at hres
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
            · simp only [hl_mz] at hres hnex ⊢
              by_cases hclk1 : s1.clock = 0
              · simp only [hclk1, ↓reduceIte] at hres
                exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
              · simp only [hclk1, ↓reduceIte] at hres hnex ⊢
                have hl_mz_rt : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "memzero")
                    [.val (.word w_out), .val (.word 96#64)] = some (body_mz, callee_mz, ret_mz) := by
                  rwa [← hs1_code]
                have hraw_mz := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "memzero")
                  [.val (.word w_out), .val (.word 96#64)] body_mz callee_mz ret_mz hl_mz_rt
                have hlook_mz_fn := R10Shards.Fast_GbodyC17ToC21.lookup_memzero_fn
                have hbody_mz_eq : body_mz = sourceFnBody Guest.Software.guestFn_memzero ∧ ret_mz = .one := by
                  unfold lookupCodeHOLExact at hraw_mz
                  rw [hlook_mz_fn] at hraw_mz
                  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memzero,
                    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
                    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
                    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural] at hraw_mz ⊢
                  split at hraw_mz
                  · injection hraw_mz with hp
                    exact ⟨(Prod.mk.inj hp).1.symm, (Prod.mk.inj (Prod.mk.inj hp).2).2.symm⟩
                  · cases hraw_mz
                have hp2_mz := R10Shards.Fast_GbodyC17ToC21.callee_param_two s1 (ofString "memzero")
                  (ofString "dst") (ofString "n") .one .one _ _
                  (by rw [hs1_code]; exact hlook_mz_fn)
                  (.var .local (ofString "out")) (.const 96#64) (.val (.word w_out)) (.val (.word 96#64))
                  [.val (.word w_out), .val (.word 96#64)] body_mz callee_mz ret_mz
                  (by simp [evalAt, evalHOLExact, hs1_out]) rfl hargs_mz hl_mz
                have hdst_mz : locN (callEntryStateHOLFinite s1 callee_mz) "dst" = w_out.toNat := by
                  simp [locN, callEntryStateHOLFinite, hp2_mz.2.1]
                have hn_mz : locN (callEntryStateHOLFinite s1 callee_mz) "n" = 96 := by
                  simp [locN, callEntryStateHOLFinite, hp2_mz.2.2]
                rcases hrun_mz : evaluateHOLFiniteState (callEntryStateHOLFinite s1 callee_mz) body_mz with ⟨res_mz, post_mz⟩
                simp only [hrun_mz] at hres hnex ⊢
                have hres_mz_body : Resumes res_mz →
                    Wave8Contracts.M08.RegionWriteFrame (callEntryStateHOLFinite s1 callee_mz) post_mz (w_out.toNat, 96) := by
                  intro hr_mz
                  have hce_code : (callEntryStateHOLFinite s1 callee_mz).code = originalRuntimeCode := hs1_code
                  have hce_G : GuestInv (callEntryStateHOLFinite s1 callee_mz) :=
                    (localsFree_arenaReady s1 callee_mz (s1.clock - 1) hM_s1.1).1
                  have hr_m08 : Wave8Contracts.M08.Resumes res_mz := by
                    rcases hr_mz with ⟨v, hv⟩ | ⟨e, v, hv, ht⟩
                    · exact Or.inl ⟨v, hv⟩
                    · exact Or.inr ⟨e, v, hv, ht⟩
                  have hmwf := Wave8Contracts.M08.memzero_body_frame (callEntryStateHOLFinite s1 callee_mz)
                    hce_code hce_G (by rw [← hbody_mz_eq.1, hrun_mz]; exact hr_m08)
                  rw [← hbody_mz_eq.1, hrun_mz, hdst_mz, hn_mz] at hmwf
                  exact hmwf
                cases res_mz with
                | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                | some br_mz =>
                  cases br_mz with
                  | timeOut => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                  | error => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                  | «break» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                  | «continue» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                  | finalFfi _ => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                  | exception eid eval =>
                    dsimp only at hnex
                    exact absurd hnex (nonExResult_not_exception rfl)
                  | returned val_mz =>
                    dsimp only at hres hnex ⊢
                    by_cases hsh_mz : shapeEqHOL (shapeOfHOLExact val_mz) ret_mz
                    · simp only [hsh_mz, ↓reduceIte] at hres hnex ⊢
                      have hmwf := hres_mz_body (Or.inl ⟨val_mz, rfl⟩)
                      obtain ⟨hws_mz_raw, hcore_mz⟩ :=
                        worldStep_of_region_writes_ownedEq (s := s1) (post := post_mz)
                          (r := some (.returned val_mz)) (R := fun _ => [(w_out.toNat, 96)])
                          hWOK_s1
                          ⟨hmwf.1, hmwf.2.1, hmwf.2.2.1, hmwf.2.2.2.1, hmwf.2.2.2.2.1, hmwf.2.2.2.2.2.1⟩
                          hmwf.2.2.2.2.2.2.1
                          (fun a ha_lt hnot => hmwf.2.2.2.2.2.2.2.1 a ha_lt (fun hin => hnot _ (List.mem_singleton.2 rfl) hin))
                          hmwf.2.2.2.2.2.2.2.2
                      have hzf := FunSpec.at_lookup zv_memzero_local s1 hs1_code _ body_mz callee_mz ret_mz hl_mz
                        (localsFree_arenaReady s1 callee_mz (s1.clock - 1) hM_s1.1)
                        (by rw [hrun_mz]; simp)
                      rw [hrun_mz] at hzf
                      have hmem16_zero : memW post_mz (w_out.toNat + 16) = 0 :=
                        hzf val_mz rfl (w_out.toNat + 16) (by rw [hdst_mz]; omega) (by rw [hdst_mz, hn_mz]; omega) (by omega)
                      set s2_pre : PanSemStateFiniteExact 64 F := { post_mz with locals := s1.locals }
                      rw [evaluateHOLFiniteState_dec_total] at hres hnex ⊢
                      simp only [evalHOLExact, shapeEqHOL, shapeOfHOLExact, ↓reduceIte] at hres hnex ⊢
                      set s2 := setVarHOLFinite (ofString "frame") (.val (.word 0#64)) s2_pre
                      have hhp_mz_eq : globN s2 "heap_ptr" = globN s1 "heap_ptr" :=
                        Wave8Contracts.M08.globN_congr hmwf.2.2.2.2.2.1 "heap_ptr"
                      have hsp_mz_eq : globN s2 "scratch_ptr" = globN s1 "scratch_ptr" :=
                        Wave8Contracts.M08.globN_congr hmwf.2.2.2.2.2.1 "scratch_ptr"
                      have hs2_code : s2.code = originalRuntimeCode := by
                        change post_mz.code = originalRuntimeCode
                        rw [hmwf.1]; exact hs1_code
                      have hs2_msg : s2.locals.lookup (ofString "msg") = entry.locals.lookup (ofString "msg") := by
                        simp [s2, s2_pre, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hs1_msg,
                          show ofString "frame" ≠ ofString "msg" by decide]
                      have hs2_out : s2.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
                        simp [s2, s2_pre, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hs1_out,
                          show ofString "frame" ≠ ofString "out" by decide]
                      have hs2_fr : s2.locals.lookup (ofString "frame") = some (.val (.word 0#64)) := by
                        simp [s2, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
                      -- Bo unhit across memzero:
                      have hu_s1_s2 : PtxBlockOutUnhit s1 s2 := by
                        apply ptxBlockOutUnhit_of_nonempty
                        intro i hi hpos a ha8 hch
                        have hi_en : i ∈ blockOutObjects entry := by rwa [← hbo_eq_s1]
                        obtain ⟨_, hal_i, _, _⟩ := blockOut_allocated_words hMA_en.2.1 hi_en hpos
                        apply hmwf.2.2.2.2.2.2.1 a
                        · intro j hj hchj
                          simp only [List.mem_singleton] at hj; subst hj
                          dsimp only [CellHits] at hch hchj
                          unfold Inside at hw_in_s1
                          have hsep : heapLimit ≤ scratchStart := by decide
                          have hhp_lim : globN s1 "heap_ptr" ≤ heapLimit := hM_s1.1.2.2.1
                          have hsc_lo : scratchStart ≤ globN entry "scratch_ptr" :=
                            le_trans hM0.1.2.2.2.1 hM0.1.2.2.2.2.1
                          rcases hal_i with ⟨_, hhi_i⟩ | ⟨hlo_i, _⟩ <;> omega
                        · intro hch0; dsimp only [CellHits] at hch0; omega
                      have hu_s2 : PtxBlockOutUnhit entry s2 :=
                        ptxBlockOutUnhit_trans hu_s1 hu_s1_s2 hbo_eq_s1
                      have hbo_glob_mz : globN s2 "bo" = globN s1 "bo" :=
                        Wave8Contracts.M08.globN_congr hmwf.2.2.2.2.2.1 "bo"
                      have hbo_eq_s2 : blockOutObjects s2 = blockOutObjects entry := by
                        have hbo_s2_s1 : blockOutObjects s2 = blockOutObjects s1 :=
                          blockOutObjects_eq_of_ptxBlockOutUnhit hM_s1.1 hMA_s1.2.1 hbo_glob_mz
                            (fun off hoff hnz_bo => by
                              have hbo_fix : (globN s1 "bo", 88) ∈ fixedObjects s1 := by
                                have hm : (globN s1 "bo", if globN s1 "bo" = 0 then 0 else 88) ∈ fixedObjects s1 := by
                                  unfold fixedObjects; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
                                  exact List.mem_map.2 ⟨("bo", 88), by decide, rfl⟩
                                simpa [hnz_bo] using hm
                              have hd_bo := hout_ow_s1_at (w_out.toNat, 96) (by simp) (globN s1 "bo", 88)
                                (by unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hbo_fix))))
                              rcases hMA_s1.2.1.2.2.1.1 _ hbo_fix with h0 | ⟨_, hwbo⟩
                              · simp at h0
                              · have hbo_hi : globN s1 "bo" + 88 ≤ 2 ^ 64 := by
                                  rcases EvmBase.fixedObject_le_2pow64 hM_s1.1.2 hMA_s1.2.1.2.2.1 hbo_fix with h0 | hbnd
                                  · simp at h0
                                  · exact hbnd
                                have hoff8 : off % 8 = 0 := by
                                  simp at hoff; rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
                                have hoff_lt : off + 8 ≤ 88 := by
                                  simp at hoff; rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
                                have hcell_u : R10Shards.Fast_GbodyC17ToC21.IvlUnhit s1 s2 (globN s1 "bo", 88) := by
                                  intro a ha8 hch
                                  apply hmwf.2.2.2.2.2.2.1 a
                                  · intro j hj hchj
                                    simp only [List.mem_singleton] at hj; subst hj
                                    unfold CellHits at hch hchj; unfold Disj at hd_bo
                                    rcases hd_bo with h0 | h0 | hl | hr <;> dsimp only at * <;> omega
                                  · intro hch0; dsimp only [CellHits] at hch0; omega
                                exact R13Shards.memW_eq_of_ivlUnhit hcell_u (by have := hwbo.1; omega) hbo_hi (by omega))
                            hu_s1_s2
                        exact hbo_s2_s1.trans hbo_eq_s1
                      set S_s1_full := S0_s1 ++ [memW entry (locN entry "msg" + 152), memW entry (locN entry "msg" + 160)]
                      have hdisj_mz_all : IvlsDisj [(w_out.toNat, 96)]
                          ((locN s1 "msg", 176) :: worldTypedIvls s1 S_s1_full Nd_s1) := by
                        intro x hx j hj
                        simp only [List.mem_singleton] at hx; subst hx
                        rcases List.mem_cons.1 hj with rfl | hj_wti
                        · have hm_eq_loc : locN s1 "msg" = locN entry "msg" := by simp [locN, hs1_msg]
                          rw [hm_eq_loc]
                          exact Or.inr (Or.inr (Or.inr (Nat.le_trans hm_in_en.2 hw_in_s1.1)))
                        · exact hout_ow_s1_at _ (by simp) j (worldTypedIvls_sub_worldOwned _ _ _ j hj_wti)
                      have hws_mz_av : WorldStep (fun _ => [(w_out.toNat, 96)]) [] stdKeep
                          (fun _ _ post0 S' Nd' => IvlsDisj [(w_out.toNat, 96)] (worldOwned post0 S' Nd'))
                          s1 (some (.returned val_mz)) post_mz := by
                        obtain ⟨a1, a2, a3, a4, _⟩ := hws_mz_raw
                        refine ⟨a1, a2, a3, a4, fun S_x Nd_x hW_x hD_x => ?_⟩
                        obtain ⟨hWT_post, howned_eq⟩ := hcore_mz S_x Nd_x hW_x hD_x
                        refine ⟨S_x, Nd_x, fun _ ht => ht, hWT_post,
                          by rw [howned_eq]; exact Wave8Contracts.M08.ownedGrows_refl s1 post_mz _,
                          fun a hkeep _ => hmwf.2.2.2.2.2.2.1 a
                            (fun j hj => hkeep j (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hj)))))
                            (fun hc => by unfold CellHits at hc; omega), ?_⟩
                        dsimp only
                        rw [howned_eq]
                        intro x hx j hj
                        unfold worldOwned at hj
                        rcases List.mem_append.1 hj with h1 | hnd
                        · rcases List.mem_append.1 h1 with htab | hfix
                          · apply hD_x x hx j
                            unfold worldTypedIvls
                            apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
                            apply List.mem_append.2; left; exact List.mem_append.2 (Or.inl htab)
                          · apply hout_ow_s1_at x hx j
                            unfold worldOwned
                            exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
                        · apply hD_x x hx j
                          unfold worldTypedIvls
                          exact List.mem_append.2 (Or.inr hnd)
                      obtain ⟨S0_s2, Nd_s2, hMA_s2_pre, hav0_mz, hfp_mz⟩ :=
                        R10Shards.Fast_GbodyC17ToC21.WorldStep.preserves_msgReadyAt hMA_s1 hws_mz_av
                          (fun x hx h0 => by simp at hx; subst hx; simp at h0) hdisj_mz_all
                      have hMA_s2 : R10Shards.Fast_GbodyC17ToC21.MsgReadyAt s2
                          (S0_s2 ++ [memW s1 (locN s1 "msg" + 152), memW s1 (locN s1 "msg" + 160)]) Nd_s2 :=
                        R10Shards.Fast_GbodyC17ToC21.msgReadyAt_with_locals
                          (s := s2_pre)
                          (by simp [HolFiniteMapExact.update, FUPDATE, show ofString "frame" ≠ ofString "msg" by decide])
                          hMA_s2_pre
                      have hM_s2 : MsgReady s2 :=
                        R10Shards.Fast_GbodyC17ToC21.msgReadyAt_msgReady hMA_s2
                      have hout_ow_s2_at : IvlsDisj [(w_out.toNat, 96)]
                          (worldOwned s2 (S0_s2 ++ [memW s1 (locN s1 "msg" + 152), memW s1 (locN s1 "msg" + 160)]) Nd_s2) := by
                        intro x hx j hj
                        simp only [List.mem_singleton] at hx; subst hx
                        change j ∈ worldOwned post_mz _ Nd_s2 at hj
                        unfold worldOwned at hj
                        rcases List.mem_append.1 hj with h1 | hnd
                        · rcases List.mem_append.1 h1 with htab | hfix
                          · rw [List.flatMap_append] at htab
                            rcases List.mem_append.1 htab with htab0 | htab_loc
                            · apply hav0_mz (w_out.toNat, 96) (by simp) j
                              unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl htab0)))
                            · obtain ⟨u, hu_loc, hj_fp⟩ := List.mem_flatMap.1 htab_loc
                              rw [hfp_mz u hu_loc] at hj_fp
                              have hu_S : u ∈ S_s1_full := by
                                simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_loc
                                rcases hu_loc with rfl | rfl
                                · exact hMA_s1.2.2.1
                                · exact hMA_s1.2.2.2.1
                              apply hout_ow_s1_at (w_out.toNat, 96) (by simp) j
                              unfold worldOwned
                              exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨u, hu_S, hj_fp⟩))))
                          · apply hav0_mz (w_out.toNat, 96) (by simp) j
                            unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix)))
                        · apply hav0_mz (w_out.toNat, 96) (by simp) j
                          unfold worldOwned; exact List.mem_append.2 (Or.inr hnd)
                      have hws_s1_s2 : WorldStep (fun _ => [(w_out.toNat, 96)]) ["heap_ptr", "scratch_ptr"] pmcKeep
                          (fun _ _ st S' Nd' => IvlsDisj [(w_out.toNat, 96)] (worldOwned st S' Nd'))
                          s1 none s2 :=
                        worldStep_pmcKeep_with_locals_clock_Q
                          (worldStep_pmcKeep_of_stdKeep (fun _ hg => False.elim (List.not_mem_nil hg)) hws_mz_av)
                          s2.locals post_mz.clock
                      have hws_en_s2 := worldStep_pmcPrefix_trans (w_out := w_out)
                        (Q2 := fun _ _ st S' Nd' => IvlsDisj [(w_out.toNat, 96)] (worldOwned st S' Nd'))
                        hM0.1 hWOK_en
                        (fun j hj => by simp at hj)
                        (fun j hj => by simp at hj; subst hj; right; rw [hhp_mz_eq]; exact hw_in_s1)
                        (fun _ _ h => h)
                        (fun S2 Nd2 _ hout2 x hx j hj => by
                          simp at hx; subst hx
                          exact hout2 _ (by simp) j (worldTypedIvls_sub_worldOwned _ _ _ j hj))
                        hws_s1 hsp_s1 hws_s1_s2
                        (fun _ _ _ _ _ _ _ _ hq2 => hq2)
                      have hw_in_s2 : Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s2 "heap_ptr") := by
                        rw [hhp_mz_eq]; exact hw_in_s1
                      have hw_ok_s2 : WordsOK s2 (w_out.toNat, 96) :=
                        wordsOK_transfer hM_s1.1.1 hM_s2.1.1 hw_ok_s1
                      have hsp_s2 : globN s2 "scratch_ptr" ≤ globN entry "scratch_ptr" := by
                        rw [hsp_mz_eq]; exact hsp_s1
                      have hp1 : PmcBoA1 entry s2 :=
                        ⟨⟨hM0, hM_s2, hs2_msg, hsp_s2, w_out, hws_en_s2, hs2_out, hs2_fr, hw_out8,
                          hw_in_s2, hw_ok_s2, hmem16_zero, _, _, hMA_s2, hout_ow_s2_at⟩,
                         hu_s2, hbo_eq_s2⟩
                      have htail_run := htail s2 hs2_code hp1
                      unfold PmcBoRun at htail_run
                      rcases hrun_tail : evaluateHOLFiniteState s2 tail with ⟨res_t, post_t⟩
                      rw [hrun_tail] at htail_run
                      simp only [hrun_tail] at hres hnex ⊢
                      cases res_t with
                      | none => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                      | some br_t =>
                        cases br_t with
                        | timeOut => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                        | error => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                        | «break» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                        | «continue» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                        | finalFfi _ => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
                        | exception eid eval =>
                          exact absurd hnex (nonExResult_not_exception rfl)
                        | returned val_t =>
                          exact ptxBlockOutUnhit_with_locals_clock _ post_t.clock
                            (ptxBlockOutUnhit_with_locals_clock _ post_t.clock
                              (htail_run (Or.inl ⟨val_t, rfl⟩) (Or.inr (Or.inr (Or.inr ⟨val_t, rfl⟩)))))
                    · simp only [hsh_mz, Bool.false_eq_true, ↓reduceIte] at hres
                      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          · simp only [hsh_al, Bool.false_eq_true, ↓reduceIte] at hres
            exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

/-! ## 4. Phase 2 (`pmcDispatch`): Block-Output Preservation -/

theorem pmcBo_call_frame_callee {F : Type}
    {fname : MlS} {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {entry s : PanSemStateFiniteExact 64 F}
    {w_out : BitVec 64} {tail : ProgHOL 64}
    {restL : HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64)}
    (hcall_spec : WorldKeepsIn MsgReady pmcTables pmcRegions pmcGlobals pmcKeep Q fname)
    (hQ_bo : ∀ {F' : Type} (s0 : PanSemStateFiniteExact 64 F') r0 post0 S0 Nd0,
      Q s0 r0 post0 S0 Nd0 →
      RetFrameResultStrong s0 r0 post0 S0 Nd0 ∧ (NonExResult r0 → PtxBlockOutUnhit s0 post0))
    (hlook_rt : ∃ b r, originalRuntimeCode.lookup fname =
      some ([(ofString "msg", .one)], b, r))
    (hrest_out : ∀ m, (restL m).lookup (ofString "out") = m.lookup (ofString "out"))
    (hrest_fr : ∀ m, (restL m).lookup (ofString "frame") = m.lookup (ofString "frame"))
    (htail : ∀ s' : PanSemStateFiniteExact 64 F,
      s'.code = originalRuntimeCode → PmcBoA2 entry s' → PmcBoRun entry tail s')
    (hcode : s.code = originalRuntimeCode)
    (hM0 : MsgReady entry)
    (hM_s : MsgReady s)
    (hs_msg : s.locals.lookup (ofString "msg") = entry.locals.lookup (ofString "msg"))
    (hsp_s : globN s "scratch_ptr" ≤ globN entry "scratch_ptr")
    (hws_s : WorldStep (fun st => bufRegions pmcBufs st ++ [(globN entry "heap_ptr", globN s "heap_ptr" - globN entry "heap_ptr")])
      ["heap_ptr", "scratch_ptr"] pmcKeep
      (fun _ _ st S Nd => IvlsDisj [(w_out.toNat, 96)] (worldOwned st S Nd))
      entry none s)
    (hs_out : s.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hs_fr : s.locals.lookup (ofString "frame") = some (.val (.word 0#64)))
    (hw_out8 : w_out.toNat % 8 = 0)
    (hw_in_s : Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s "heap_ptr"))
    (hw_ok_s : WordsOK s (w_out.toNat, 96))
    (hmem16_s : memW s (w_out.toNat + 16) = 0)
    (hMA_s : ∃ S_s Nd_s,
      R10Shards.Fast_GbodyC17ToC21.MsgReadyAt s S_s Nd_s ∧
      IvlsDisj [(w_out.toNat, 96)] (worldOwned s S_s Nd_s))
    (hu_s : PtxBlockOutUnhit entry s)
    (hbo_eq_s : blockOutObjects s = blockOutObjects entry) :
    let out1 := evaluateHOLFiniteState s
      (.call (some ((some (.local, ofString "frame")), none)) fname [.var .local (ofString "msg")])
    let out := match out1.1 with
      | none => evaluateHOLFiniteState { out1.2 with locals := restL out1.2.locals } tail
      | some _ => (out1.1, { out1.2 with locals := restL out1.2.locals })
    Resumes out.1 → NonExResult out.1 → PtxBlockOutUnhit entry out.2 := by
  dsimp only
  intro hres hnex
  rw [evaluateHOLFiniteState_call] at hres hnex ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "msg")] with _ | vals
  · simp only [hargs] at hres
    exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  · simp only [hargs] at hres hnex ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body_c, callee_c, ret_c⟩
    · simp only [hl] at hres
      exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
    · simp only [hl] at hres hnex ⊢
      by_cases hclk : s.clock = 0
      · simp only [hclk, ↓reduceIte] at hres
        exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
      · simp only [hclk, ↓reduceIte] at hres hnex ⊢
        obtain ⟨b_rt, r_rt, hlook_fn⟩ := hlook_rt
        have hpc_msg : callee_c.lookup (ofString "msg") = s.locals.lookup (ofString "msg") :=
          callee_param_one s fname (ofString "msg") .one b_rt r_rt
            (by rw [hcode]; exact hlook_fn) vals body_c callee_c ret_c hargs hl
        let ent := callEntryStateHOLFinite s callee_c
        have hM_ent : MsgReady ent :=
          localsOnly_msgReady s callee_c (s.clock - 1)
            (fun n hn => by simp at hn; subst hn; exact hpc_msg) hM_s
        have hmeta_c := (evaluateHOLFiniteState_metadata ent body_c).1
        rcases hrun_c : evaluateHOLFiniteState ent body_c with ⟨res_c, post_c⟩
        dsimp only [ent] at hrun_c hmeta_c
        rw [hrun_c] at hmeta_c
        dsimp only at hmeta_c
        simp only [hrun_c] at hres hnex ⊢
        have hnt_c : (evaluateHOLFiniteState ent body_c).1 ≠ some .timeOut := by
          dsimp only [ent]; rw [hrun_c]
          rintro rfl
          exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        have hspec := FunSpec.at_lookup hcall_spec s hcode vals body_c callee_c ret_c hl hM_ent hnt_c
        dsimp only [ent] at hspec
        rw [hrun_c] at hspec
        dsimp only at hspec
        obtain ⟨_, _, hMA_en⟩ := R10Shards.Fast_GbodyC17ToC21.msgReadyAt_of_msgReady hM0
        have hm8_en : locN entry "msg" % 8 = 0 := hMA_en.2.2.2.2.2.2.2.2.2.1
        have hm_in_en : Inside (locN entry "msg", 176) sourceBase (globN entry "heap_ptr") :=
          hMA_en.2.2.2.2.2.2.2.2.2.2.1
        have hm_fix_en : ∀ j ∈ fixedObjects entry, Disj (locN entry "msg", 176) j := by
          intro j hj
          apply hMA_en.2.2.2.2.2.2.2.2.2.2.2.1 j
          unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hj)))
        have hmsg_loc_s : locN s "msg" = locN entry "msg" := by simp [locN, hs_msg]
        have hmsg_loc_ent : locN ent "msg" = locN s "msg" := by
          simp [ent, callEntryStateHOLFinite, locN, hpc_msg]
        have hR1_z : ∀ j ∈ bufRegions pmcBufs entry ++ [(globN entry "heap_ptr", globN s "heap_ptr" - globN entry "heap_ptr")],
            j.2 = 0 → j.1 % 8 = 0 := by
          intro j hj hz
          rcases List.mem_append.1 hj with hj_buf | hj_fr
          · exact pmcRegions_zero_aligned hm8_en j
              (by rw [pmcRegions_eq_bufRegions]; exact List.mem_cons_of_mem _ hj_buf) hz
          · simp only [List.mem_singleton] at hj_fr; subst hj_fr
            exact hM0.1.2.2.2.2.2.2.1
        have hR1_sub : ∀ j ∈ bufRegions pmcBufs entry ++ [(globN entry "heap_ptr", globN s "heap_ptr" - globN entry "heap_ptr")],
            j ∈ bufRegions pmcBufs entry ∨ Inside j (globN entry "heap_ptr") (globN s "heap_ptr") := by
          intro j hj
          rcases List.mem_append.1 hj with hj_buf | hj_fr
          · exact Or.inl hj_buf
          · simp only [List.mem_singleton] at hj_fr; subst hj_fr
            exact Or.inr ⟨le_rfl, by have := hws_s.2.1; omega⟩
        obtain ⟨S_s, Nd_s, hMAs, hout_ow_s⟩ := hMA_s
        have htabs_ent : pmcTables ent = pmcTables s := by
          unfold pmcTables; rw [hmsg_loc_ent]; rfl
        have hreg_ent : pmcRegions ent = pmcRegions s :=
          pmcRegions_eq_of_msg_locals hmsg_loc_ent
        have hT_ent0 : ∀ t ∈ pmcTables ent, t ∈ S_s := by
          rw [htabs_ent]
          intro t ht
          simp only [pmcTables, List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact hMAs.2.2.1
          · exact hMAs.2.2.2.1
        have hD_ent0 : IvlsDisj (pmcRegions ent) (worldTypedIvls ent S_s Nd_s) := by
          have hwti : worldTypedIvls ent S_s Nd_s = worldTypedIvls s S_s Nd_s := rfl
          rw [hreg_ent, hwti]
          exact pmcRegions_disj_of_msgReady hMAs.2.1 hMAs.2.2.2.2.2.2.2.2.2.2.2.1
        cases res_c with
        | none =>
          exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
        | some br_c =>
          cases br_c with
          | timeOut => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | error => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | «break» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | «continue» => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | finalFfi _ => exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
          | exception eid eval =>
            exact absurd hnex (nonExResult_not_exception rfl)
          | returned val_c =>
            dsimp only at hres hnex ⊢
            by_cases hsh1 : shapeEqHOL (shapeOfHOLExact val_c) ret_c = true
            · simp only [hsh1, ↓reduceIte] at hres hnex ⊢
              simp only [isValidValueHOLExact, lookupKvarHOLExact, hs_fr] at hres hnex ⊢
              by_cases hsh2 : shapeEqHOL (shapeOfHOLExact val_c) (shapeOfHOLExact (.val (.word 0#64))) = true
              · simp only [hsh2, ↓reduceIte, setKvarHOLFinite] at hres hnex ⊢
                have hstep_ret := hspec (Or.inl ⟨val_c, rfl⟩)
                obtain ⟨S_p0, Nd_p0, _, hWT_p0, _, _, hQ0⟩ :=
                  hstep_ret.2.2.2.2 S_s Nd_s
                    ((R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals _ _ _ _ _).2 hMAs.2.1)
                    hT_ent0 hD_ent0
                obtain ⟨⟨hret0, hstrong0⟩, hbo_c⟩ := hQ_bo _ _ _ _ _ hQ0
                have hu_ent_post_c : PtxBlockOutUnhit ent post_c :=
                  hbo_c (Or.inr (Or.inr (Or.inr ⟨val_c, rfl⟩)))
                obtain ⟨w_fr, hvc_eq, hw_fr_ok0, _, hlok0⟩ := hret0 val_c rfl
                obtain ⟨w_fr', hvc_eq', hin_fr0, _, hlive0, hdisj_out0⟩ := hstrong0 val_c rfl
                rw [hvc_eq] at hvc_eq'; injection hvc_eq' with hvc_eq''; injection hvc_eq'' with hw_fr_eq; subst hw_fr_eq
                subst hvc_eq
                set s_next := setVarHOLFinite (ofString "frame") (.val (.word w_fr))
                  { post_c with locals := s.locals, clock := post_c.clock }
                have hs_next_code : s_next.code = originalRuntimeCode := hmeta_c.trans hcode
                have hs_next_out : s_next.locals.lookup (ofString "out") = some (.val (.word w_out)) := by
                  simp [s_next, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hs_out,
                    show ofString "frame" ≠ ofString "out" by decide]
                have hs_next_fr : s_next.locals.lookup (ofString "frame") = some (.val (.word w_fr)) := by
                  simp [s_next, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
                have hu_s_next : PtxBlockOutUnhit entry s_next := by
                  have hu_step : PtxBlockOutUnhit s s_next := hu_ent_post_c
                  exact ptxBlockOutUnhit_trans hu_s hu_step hbo_eq_s
                have hstep_s_next : WorldStepIn pmcTables pmcRegions pmcGlobals pmcKeep
                    (fun _ _ post S' Nd' => PmcLogsLiveOwned post S' Nd' (memW post (w_fr.toNat + 88)))
                    s none s_next := by
                  obtain ⟨hAp, hhp, hG, hK, hW⟩ := hstep_ret
                  refine ⟨localsFree_arenaReady post_c s_next.locals post_c.clock hAp, hhp, hG,
                    pmc_recordsKept_with_locals hmsg_loc_ent hK,
                    fun S_x Nd_x hWT_x hT_x hD_x => ?_⟩
                  have hT_ent : ∀ t ∈ pmcTables ent, t ∈ S_x := by rwa [htabs_ent]
                  have hD_ent : IvlsDisj (pmcRegions ent) (worldTypedIvls ent S_x Nd_x) := by
                    have hwti : worldTypedIvls ent S_x Nd_s = worldTypedIvls s S_x Nd_s := rfl
                    have hwti' : worldTypedIvls ent S_x Nd_x = worldTypedIvls s S_x Nd_x := rfl
                    rwa [hreg_ent, hwti']
                  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hQ_x⟩ :=
                    hW S_x Nd_x ((R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals _ _ _ _ _).2 hWT_x) hT_ent hD_ent
                  obtain ⟨⟨hret_x, hstrong_x⟩, _⟩ := hQ_bo _ _ _ _ _ hQ_x
                  obtain ⟨w_fr_x, hvc_x, _, _, hlive_x, _⟩ := hstrong_x (.val (.word w_fr)) rfl
                  injection hvc_x with hvc_x'; injection hvc_x' with hw_x; subst hw_x
                  obtain ⟨w_fr_y, hvc_y, _, _, hlok_x⟩ := hret_x (.val (.word w_fr)) rfl
                  injection hvc_y with hvc_y'; injection hvc_y' with hw_y; subst hw_y
                  exact ⟨S', Nd', hsub,
                    (R10Shards.Fast_GbodyC17ToC21.worldTypedWith_with_locals post_c s_next.locals post_c.clock S' Nd').2 hWT',
                    hOG, pmc_frameOutside_with_locals hmsg_loc_ent hFO,
                    pmcLogsLiveOwned_congr_live hAp.2 hlok_x hlive_x rfl rfl
                      (fun a => a) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)⟩
                have hws_en_next := worldStepIn_pmc_trans_prefix (w_out := w_out)
                  (Q := fun _ _ post S' Nd' => PmcLogsLiveOwned post S' Nd' (memW post (w_fr.toNat + 88)))
                  (Q_out := fun _ _ post S' Nd' =>
                    IvlsDisj [(w_out.toNat, 96)] (worldOwned post S' Nd') ∧
                    PmcLogsLiveOwned post S' Nd' (memW post (w_fr.toNat + 88)))
                  hmsg_loc_s hm8_en hm_in_en hm_fix_en hM0.1 (msgReady_worldOK entry hM0)
                  hR1_z hR1_sub hw_out8 hw_in_s (fun _ _ h => h) hws_s hsp_s hstep_s_next
                  (fun _ _ hout_ow3 _ hlive3 => ⟨hout_ow3, hlive3⟩)
                have hout_in2 : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
                  ⟨le_trans hM0.1.2.1 hw_in_s.1, hw_in_s.2⟩
                have hout_disj_R2 : ∀ j ∈ pmcRegions s, Disj (w_out.toNat, 96) j := by
                  rw [pmcRegions_eq_bufRegions]
                  intro j hj
                  rcases List.mem_cons.1 hj with rfl | hj_buf
                  · rw [hmsg_loc_s]
                    exact Or.inr (Or.inr (Or.inr (Nat.le_trans hm_in_en.2 hw_in_s.1)))
                  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj_buf
                    obtain ⟨sz, hgb, _, hle⟩ := validBufList_pmcBufs p hp
                    have hfix_p : bufferRegion s (p.1, sz) ∈ fixedObjects s := by
                      unfold fixedObjects
                      apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
                      exact List.mem_map.2 ⟨(p.1, sz), hgb, rfl⟩
                    have hd_sz := hout_ow_s (w_out.toNat, 96) (by simp) _
                      (by unfold worldOwned; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hfix_p))))
                    by_cases h0 : globN s p.1 = 0
                    · simp [bufferRegion, h0]; exact disj_zero_right _
                    · simp only [bufferRegion, h0, ↓reduceIte] at hd_sz ⊢
                      exact disj_of_inside_right (j' := (globN s p.1, sz))
                        ⟨le_rfl, by dsimp; omega⟩ hd_sz
                obtain ⟨_, _, _, _, hOG_at, hFO_at, _⟩ :=
                  hstep_s_next.2.2.2.2 S_s Nd_s hMAs.2.1
                    (by
                      intro t ht
                      simp only [pmcTables, List.mem_cons, List.not_mem_nil, or_false] at ht
                      rcases ht with rfl | rfl
                      · exact hMAs.2.2.1
                      · exact hMAs.2.2.2.1)
                    (pmcRegions_disj_of_msgReady hMAs.2.1 hMAs.2.2.2.2.2.2.2.2.2.2.2.1)
                obtain ⟨_, _, hout_u_s_next⟩ :=
                  heap_ivl_survives_step (b := (w_out.toNat, 96))
                    hM_s.1.2 hstep_s_next.2.1 hOG_at hFO_at
                    (worldOwned_zero_aligned hMAs.2.1)
                    (pmcRegions_zero_aligned (by rw [hmsg_loc_s]; exact hm8_en))
                    hw_out8 (by dsimp) hout_in2
                    (fun j hj => hout_ow_s (w_out.toNat, 96) (by simp) j hj)
                    hout_disj_R2
                have hw_hi_s : w_out.toNat + 96 ≤ 2 ^ 64 :=
                  (ivl_allocated_bound hM_s.1.2 (Or.inl hout_in2)).2
                have hmem16_next : memW s_next (w_out.toNat + 16) = 0 := by
                  rw [memW_eq_of_ivlUnhit hout_u_s_next (by omega) hw_hi_s ⟨by dsimp; omega, by dsimp; omega⟩]
                  exact hmem16_s
                have hw_in_next : Inside (w_out.toNat, 96) (globN entry "heap_ptr") (globN s_next "heap_ptr") :=
                  ⟨hw_in_s.1, le_trans hw_in_s.2 hstep_s_next.2.1⟩
                have hw_ok_next : WordsOK s_next (w_out.toNat, 96) :=
                  wordsOK_transfer hM_s.1.1 hws_en_next.1.1 hw_ok_s
                have hw_fr_ok_next : WordsOK s_next (w_fr.toNat, 280) :=
                  wordsOK_transfer hstep_ret.1.1 hws_en_next.1.1 hw_fr_ok0
                have hlok_next : LogsListOK s_next (memW s_next (w_fr.toNat + 88)) :=
                  pmc_logsListOK_congr_live hstep_ret.1.2 hstep_ret.1.1 hws_en_next.1.1 le_rfl hlok0
                    (fun a => a) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)
                have hdisj_logs_out : memW s_next (w_fr.toNat + 88) ≠ 0 →
                    Disj (memW s_next (w_fr.toNat + 88), 24) (w_out.toNat, 96) ∧
                    Disj (memW s_next (memW s_next (w_fr.toNat + 88)),
                      8 * memW s_next (memW s_next (w_fr.toNat + 88) + 8)) (w_out.toNat, 96) ∧
                    ∀ i, i < memW s_next (memW s_next (w_fr.toNat + 88) + 8) →
                      Disj (memW s_next (memW s_next (memW s_next (w_fr.toNat + 88)) + 8 * i), 40) (w_out.toNat, 96) := by
                  intro hnz
                  have hhp_ent_s : globN ent "heap_ptr" = globN s "heap_ptr" := rfl
                  have hmem_s_next_eq : ∀ a : Nat, memW s_next a = memW post_c a := fun _ => rfl
                  simp only [hmem_s_next_eq] at hnz ⊢
                  obtain ⟨hd_hd, hd_arr, hd_ent⟩ := hdisj_out0 hnz
                  have hsep : heapLimit ≤ scratchStart := by decide
                  have hhp_lim : globN post_c "heap_ptr" ≤ heapLimit := hstep_ret.1.2.2.1
                  have hsc_lo : scratchStart ≤ globN post_c "scratch_ptr" :=
                    le_trans hstep_ret.1.2.2.2.1 hstep_ret.1.2.2.2.2.1
                  have hw_hi_s_hp : w_out.toNat + 96 ≤ globN s "heap_ptr" := hw_in_s.2
                  have hhp_s_le : globN s "heap_ptr" ≤ globN post_c "heap_ptr" := hstep_ret.2.1
                  refine ⟨?_, ?_, ?_⟩
                  · rcases hd_hd with hin_sc | hin_hp
                    · exact Or.inr (Or.inr (Or.inr (by unfold Inside at hin_sc; dsimp only at *; omega)))
                    · rw [hhp_ent_s] at hin_hp
                      exact Or.inr (Or.inr (Or.inr (le_trans hw_hi_s_hp hin_hp.1)))
                  · rcases hd_arr with hin_sc | hin_hp
                    · exact Or.inr (Or.inr (Or.inr (by unfold Inside at hin_sc; dsimp only at *; omega)))
                    · rw [hhp_ent_s] at hin_hp
                      exact Or.inr (Or.inr (Or.inr (le_trans hw_hi_s_hp hin_hp.1)))
                  · intro i hi
                    have hin_hp := hd_ent i hi
                    rw [hhp_ent_s] at hin_hp
                    exact Or.inr (Or.inr (Or.inr (le_trans hw_hi_s_hp hin_hp.1)))
                have hp2 : PmcBoA2 entry { s_next with locals := restL s_next.locals } :=
                  ⟨pmcA2_with_locals (hrest_out s_next.locals) (hrest_fr s_next.locals)
                    ⟨hM0, w_out, w_fr, hws_en_next, hs_next_out, hs_next_fr, hw_out8,
                      hw_in_next, hw_ok_next, hmem16_next, hw_fr_ok_next, hin_fr0, hlok_next, hdisj_logs_out⟩,
                   hu_s_next⟩
                exact htail { s_next with locals := restL s_next.locals } hs_next_code hp2 hres hnex
              · simp only [hsh2, Bool.false_eq_true, ↓reduceIte] at hres
                exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
            · simp only [hsh1, ↓reduceIte] at hres
              exact absurd hres (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
