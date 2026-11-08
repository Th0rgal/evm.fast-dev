import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.WkGetAccount
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_stor_lookup
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalStateInit.SetLstNew
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalRemove

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalStateInit

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

theorem lookup_get_pre_tx_account :
    originalRuntimeCode.lookup (ofString "get_pre_tx_account") =
      some ((sourceFunctionEntry Guest.Software.guestFn_get_pre_tx_account).2) :=
  lookup_of_guestAst_getElem 420 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_get_pre_tx_account) rfl

theorem lookup_get_pre_tx_storage :
    originalRuntimeCode.lookup (ofString "get_pre_tx_storage") =
      some ((sourceFunctionEntry Guest.Software.guestFn_get_pre_tx_storage).2) :=
  lookup_of_guestAst_getElem 421 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_get_pre_tx_storage) rfl

theorem lookup_idx_start_account :
    originalRuntimeCode.lookup (ofString "idx_start_account") =
      some ((sourceFunctionEntry Guest.Software.guestFn_idx_start_account).2) :=
  lookup_of_guestAst_getElem 422 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_idx_start_account) rfl

theorem lookup_idx_start_storage :
    originalRuntimeCode.lookup (ofString "idx_start_storage") =
      some ((sourceFunctionEntry Guest.Software.guestFn_idx_start_storage).2) :=
  lookup_of_guestAst_getElem 423 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_idx_start_storage) rfl

theorem lookup_st_le64_local :
    originalRuntimeCode.lookup (ofString "st_le64") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_le64, .one) :=
  lookup_of_guestAst_getElem 26 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_st_le64) rfl

theorem lookup_st_le32_local :
    originalRuntimeCode.lookup (ofString "st_le32") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_le32, .one) :=
  lookup_of_guestAst_getElem 25 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_st_le32) rfl

theorem lookup_memcpy_local :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
  lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

theorem lookup_memzero_local :
    originalRuntimeCode.lookup (ofString "memzero") =
      some ([(ofString "dst", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memzero, .one) :=
  lookup_of_guestAst_getElem 17 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memzero) rfl

abbrev idxBufs : BufList :=
  [("bal_key_buf", 64), ("keccak_pad", 136), ("keccak_st", 200), ("mpt_nib_scratch", 64)]

theorem validBufList_idxBufs : ValidBufList idxBufs := by
  intro p hp
  simp only [idxBufs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨64, by decide, by decide, by decide⟩
  · exact ⟨136, by decide, by decide, by decide⟩
  · exact ⟨200, by decide, by decide, by decide⟩
  · exact ⟨64, by decide, by decide, by decide⟩

theorem nonValueSlot_bal_idx_accts {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S) (ht0_nz : globN s "bal_idx_accts" ≠ 0) :
    let t0 := globN s "bal_idx_accts"
    t0 ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) := by
  have ht0_S : globN s "bal_idx_accts" ∈ S := by
    rcases hT.2.2.2.2.2.2.1 "bal_idx_accts" (by simp [globalTableRoots]) with h0 | hm
    · exact absurd h0 ht0_nz
    · exact hm
  have ht0_wrs : (globN s "bal_idx_accts", "bal_idx_accts") ∈ worldRoleSlots s := by
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [ht0_nz]⟩
    apply List.mem_append.2; left; apply List.mem_append.2; left
    apply List.mem_append.2; left; apply List.mem_append.2; right; simp
  exact nonValueSlot_of_wrs s S _ "bal_idx_accts" hT ht0_nz ht0_S ht0_wrs
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nonValueSlot_bal_idx_stor {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S) (ht0_nz : globN s "bal_idx_stor" ≠ 0) :
    let t0 := globN s "bal_idx_stor"
    t0 ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) := by
  have ht0_S : globN s "bal_idx_stor" ∈ S := by
    rcases hT.2.2.2.2.2.2.1 "bal_idx_stor" (by simp [globalTableRoots]) with h0 | hm
    · exact absurd h0 ht0_nz
    · exact hm
  have ht0_wrs : (globN s "bal_idx_stor", "bal_idx_stor") ∈ worldRoleSlots s := by
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [ht0_nz]⟩
    apply List.mem_append.2; left; apply List.mem_append.2; left
    apply List.mem_append.2; left; apply List.mem_append.2; right; simp
  exact nonValueSlot_of_wrs s S _ "bal_idx_stor" hT ht0_nz ht0_S ht0_wrs
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem progWStep_call0_htab_set_global {B : BufList} {gw : List String}
    (gName : String) (kExp vExp : ExpHOL 64)
    (hhp_in : "heap_ptr" ∈ gw)
    (hslot_nonVal : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat),
      TablesTyped s S → globN s gName ≠ 0 →
      globN s gName ∈ S ∧
      (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ globN s gName) ∧
      (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ globN s gName) ∧
      globN s "bal_accounts" ≠ globN s gName ∧
      (∀ ad ∈ balRecords s, memW s ad ≠ globN s gName) ∧
      (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ globN s gName)) :
    ProgWStep B gw
      (.call (some (none, none)) (ofString "htab_set")
        [.var .global (ofString gName), kExp, vExp]) := by
  intro F s hcode hW hnt hfr
  set argsL : List (ExpHOL 64) := [.var .global (ofString gName), kExp, vExp]
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) argsL with _ | values
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    have hargs_fin : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) argsL = some values := by
      rwa [evalListHOLFinite_eq_toExact]
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_set") values with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        obtain ⟨v1, _, _, he1, _, _, hc_t, _, _⟩ := callee_param_three s (ofString "htab_set")
          (ofString "t") (ofString "key") (ofString "value") .one .one .one _ _
          (by rw [hcode]; exact EvmFrameSpecs.lookup_htab_set) _ _ _ values body' callee ret' hargs_fin hl
        have hloc_t : locN (callEntryStateHOLFinite s callee) "t" = globN s gName := by
          simp only [evalAt, evalHOLExact, toExact] at he1
          unfold globN locN callEntryStateHOLFinite
          dsimp only
          rw [hc_t, he1]
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        have hbe_post : post.be = s.be := by
          have inv := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body').2.2.1
          rw [hrun] at inv; exact inv
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | exception eid ev =>
            exfalso
            have hne : eid ≠ ofString "TrapErr" := by
              rcases hfr with h | h | h | ⟨_, h⟩ | ⟨e', v', h, hne⟩ <;> try simp at h
              obtain ⟨rfl, _⟩ := h; exact hne
            have hbody_ok : noCatchableRaise trapOnlyCallees body' = true :=
              trapOnlyCallees_good (ofString "htab_set") (by decide) values body' callee ret' (by rwa [← hcode])
            have hno := evaluate_noCatchableRaise trapOnlyCallees trapOnlyCallees_good
              body' hbody_ok (callEntryStateHOLFinite s callee) hcode eid ev hne
            rw [hrun] at hno; exact hno rfl
          | returned v =>
            dsimp only at hfr ⊢
            split
            · have hnz_at := FunSpec.at_lookup EvmFrameSpecs.nz_htab_set s hcode values body' callee ret' hl
                (guestInv_callEntry s callee hW.1.1) (by rw [hrun]; simp)
              rw [hrun] at hnz_at
              have ht0_nz : globN s gName ≠ 0 := by
                rw [← hloc_t]; exact hnz_at (Or.inl ⟨v, rfl⟩)
              have hArgWF : HtabArgWF (callEntryStateHOLFinite s callee) := by
                obtain ⟨hAs, S, hT, _⟩ := hW
                have ht0_S := (hslot_nonVal s S hT ht0_nz).1
                refine ⟨localsFree_arenaReady s _ _ hAs, ?_, ?_⟩
                · rw [hloc_t]; exact (htabWF_with_locals s callee (s.clock - 1) _).2 (hT.2.1 _ ht0_S).1
                · rw [hloc_t]; exact fun i hi => ((hT.2.1 _ ht0_S).2 i hi).1
              have hexit := FunSpec.at_lookup htab_set_spec s hcode values body' callee ret' hl
                hArgWF (by rw [hrun]; simp)
              rw [hrun] at hexit
              have hex := hexit v rfl
              dsimp only [HtabExit] at hex
              rw [hloc_t] at hex
              change let t := globN s gName
                let fresh : Ivl := (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")
                ArenaReady post ∧ HtabWF post t ∧ hdr post t 0 = hdr s t 0 ∧ hdr post t 1 = hdr s t 1 ∧
                globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
                (∀ i ∈ htabFootprint post t, Allocated post i ∧
                  ((∃ j ∈ htabFootprint s t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
                FrameOutside s post (htabFootprint s t) fresh ∧
                (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
                  s.globals.lookup k = post.globals.lookup k) at hex
              obtain ⟨hAp, hwf_t0, hh0, _, hhp, hfp_t0, hfr_t0, hg_t0⟩ := hex
              have hstep0 : WorldStepSc (bufRegions []) ["heap_ptr"] stdKeep NoExtra s none post :=
                worldStepSc_of_htabExit_nonValue hW hbe_post hg_t0 hg_t0
                  (fun S hT => hslot_nonVal s S hT ht0_nz)
                  hAp hwf_t0 hh0 hhp hfp_t0 hfr_t0
              exact (hstep0.with_locals_clock s.locals post.clock).mono_bufs
                (fun _ h => by cases h)
                (fun g hg => by simp at hg; subst hg; exact hhp_in)
            · rename_i hbad; simp [hbad] at hfr; exact absurd hfr not_flowingOrResumes_error

theorem wkSc_get_pre_tx_account :
    WorldKeepsSc WorldOK (bufRegions wsAcctBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      (ofString "get_pre_tx_account") := by
  have hB := validBufList_wsAcctBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsSc_of_progWStep lookup_get_pre_tx_account ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_get_pre_tx_account,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_decCall hB hgw (by intro p hp; simp at hp) (by intro g hg; simp at hg)
    (worldKeepsSc_of_readOnly EvmFrameSpecs.ro_htab_get) ?_
  refine progWStep_seq hB hgw (progWStep_ite (progWStep_return _ _ _) (progWStep_skip _ _)) ?_
  refine progWStep_seq hB hgw
    (progWStep_call0 (by intro p hp; simp at hp) (by intro g hg; simp at hg; subst hg; simp)
      wkSc_record_pre_state_read) ?_
  refine progWStep_decCall hB hgw (fun _ h => h) (fun _ h => h)
    wkSc_ws_get_account_optional ?_
  exact progWStep_return _ _ _

private theorem call0_or_resumes_local {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fname : MlS) (args : List (ExpHOL 64))
    (hcr : ContOrRes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none ∨
    Resumes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 := by
  rcases hcr with h | h | h | hr
  · exact Or.inl h
  · exfalso
    rw [evaluateHOLFiniteState_call] at h
    revert h; split <;> [simp; (split <;> [simp; (split <;> [simp; skip])])]
    rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨rc, _⟩
    rcases rc with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
  · exfalso
    rw [evaluateHOLFiniteState_call] at h
    revert h; split <;> [simp; (split <;> [simp; (split <;> [simp; skip])])]
    rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨rc, _⟩
    rcases rc with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
  · exact Or.inr hr

private theorem worldEff_call0_funByteEff_local {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    {fname : MlS} {argR : List (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → List Ivl}
    (hf : Fast_C08WkShard03.FunByteEff fname argR)
    (args : List (ExpHOL 64)) (Sub : List Ivl)
    (hsub_args : ∀ vals,
      evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args = some vals →
      ∀ i ∈ argR vals cur.globals, 0 < i.2 → ∃ j ∈ Sub, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2)
    (hsub_world : ∀ iv ∈ Sub, 0 < iv.2 →
      (∃ j ∈ Rl, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2) ∨
      (∃ gs ∈ B, (bufferRegion s gs).1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ (bufferRegion s gs).1 + (bufferRegion s gs).2) ∨
      (globN s "frame_mem_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ heapLimit))
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).1) :
    WorldEff s (evaluateHOLFiniteState cur (.call (some (none, none)) fname args)).2 Rl B gw :=
  h.of_byteEff
    (Fast_C08WkShard03.call0_byteEff hf cur args Sub h.code h.arena.1 hsub_args hnt
      (call0_or_resumes_local cur fname args hcr))
    hsub_world

private theorem call0_none_locals_local {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fn : MlS) (args : List (ExpHOL 64))
    (hnone : (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).1 = none) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).2.locals = s.locals := by
  rw [evaluateHOLFiniteState_call] at hnone ⊢
  unfold evalListHOLFinite at hnone ⊢
  rcases h1 : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [h1] at hnone
  · simp only [h1] at hnone ⊢
    rcases h2 : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fn vs with _ | ⟨b, c, r⟩
    · simp [h2] at hnone
    · simp only [h2] at hnone ⊢
      split at hnone
      · simp at hnone
      · rename_i hcz; rw [if_neg hcz]
        rcases h3 : evaluateHOLFiniteState (callEntryStateHOLFinite s c) b with ⟨rb, sb⟩
        simp only [h3] at hnone ⊢
        rcases rb with _ | rb'
        · simp at hnone
        · cases rb' with
          | returned rv =>
            dsimp only at hnone ⊢
            split at hnone
            · rename_i hsh; rw [if_pos hsh]
            · simp at hnone
          | _ => simp at hnone

private theorem call0_two_word_resumes_local {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname p1 p2 : MlS) (body : ProgHOL 64) (a1 a2 : ExpHOL 64) (w1 w2 : BitVec 64)
    (h12 : p1 ≠ p2)
    (hc : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], body, .one))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [a1, a2] =
      some [.val (.word w1), .val (.word w2)])
    (hor : (evaluateHOLFiniteState s (.call (some (none, none)) fname [a1, a2])).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none, none)) fname [a1, a2])).1) :
    Resumes (evaluateHOLFiniteState
      (callEntryStateHOLFinite s
        ((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))))
      body).1 := by
  have hl := pan_two_word_lookup s.code.lookup fname p1 p2 body w1 w2 h12 (by rw [hc]; exact hlook)
  rw [evaluateHOLFiniteState_call, ha] at hor
  dsimp only at hor
  rw [hl] at hor; dsimp only at hor
  split at hor
  · rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
  · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s _) body with ⟨rc, _⟩
    rw [hrun] at hor
    cases rc with
    | none => rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    | some r1 =>
      cases r1 with
      | returned rv => exact Or.inl ⟨rv, rfl⟩
      | exception eid ev =>
        rcases hor with h | ⟨_, h⟩ | ⟨e', v', h, hne⟩
        · simp at h
        · simp at h
        · simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨eid, ev, rfl, hne⟩
      | _ => rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

private theorem st_le64_resumes_lo {F : Type}
    (entry : PanSemStateFiniteExact 64 F) (p v : BitVec 64)
    (hc : entry.code = originalRuntimeCode) (hG : GuestInv entry)
    (hp : entry.locals.lookup (ofString "p") = some (.val (.word p)))
    (hv : entry.locals.lookup (ofString "v") = some (.val (.word v)))
    (hres : Resumes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_st_le64)).1) :
    sourceBase ≤ p.toNat := by
  have hbody : sourceFnBody Guest.Software.guestFn_st_le64 =
      .seq (.call (some (none, none)) (ofString "st_le32")
          [.var .local (ofString "p"), .var .local (ofString "v")])
        (.seq (.call (some (none, none)) (ofString "st_le32")
            [.op .add [.var .local (ofString "p"), .const 4],
              .shift .lsr (.var .local (ofString "v")) (.const 32)])
          (.return (.const 0))) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780] at hres
  rcases hc1 : evaluateHOLFiniteState entry
      (.call (some (none, none)) (ofString "st_le32")
        [.var .local (ofString "p"), .var .local (ofString "v")]) with ⟨r1, s1⟩
  rw [hc1] at hres
  have hargs1 : evalListHOLFinite entry (h := fun a => Classical.propDecidable (entry.memaddrs a))
      [.var .local (ofString "p"), .var .local (ofString "v")] = some [.val (.word p), .val (.word v)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp, hv]
  have hor1 : r1 = none ∨ Resumes r1 := by
    cases r1 with
    | none => exact Or.inl rfl
    | some _ => exact Or.inr hres
  have hres32 := call0_two_word_resumes_local entry (ofString "st_le32") (ofString "p") (ofString "v")
    (sourceFnBody Guest.Software.guestFn_st_le32) _ _ p v (by decide) hc lookup_st_le32_local hargs1
    (by rwa [hc1])
  exact (Fast_C08WkShard03.st_le32_body_eff _ p (guestInv_callEntry entry _ hG)
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "v" ≠ ofString "p" by decide])
    hres32).2.1

private theorem bal_key_buf_upper_local {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hW : WorldOK s) (hnz : globN s "bal_key_buf" ≠ 0) :
    globN s "bal_key_buf" + 64 ≤ scratchEnd := by
  obtain ⟨hA, S, hS⟩ := hW
  obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with s S).1 hS
  have hmem : (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨("bal_key_buf", 64), by decide, rfl⟩
  have hft := hWT.2.2.1.1 _ hmem
  simp only [hnz, ↓reduceIte] at hft
  rcases hft with h0 | ⟨halloc, _⟩
  · omega
  · rcases halloc with hheap | hscr
    · have hhl : heapLimit ≤ scratchEnd := by decide
      have hp := hA.2.2.1
      have hi := hheap.2
      dsimp only at hi
      omega
    · exact hscr.2

private theorem worldEff_st_le64_kb {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {gw : List String}
    (h : WorldEff s cur Rl idxBufs gw)
    (hkb : cur.locals.lookup (ofString "kb") = s.globals.lookup (ofString "bal_key_buf"))
    (hnt : (evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "st_le64")
        [.var .local (ofString "kb"), .var .global (ofString "bal_index")])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "st_le64")
        [.var .local (ofString "kb"), .var .global (ofString "bal_index")])).1) :
    WorldEff s (evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "st_le64")
        [.var .local (ofString "kb"), .var .global (ofString "bal_index")])).2 Rl idxBufs gw ∧
    ((evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "st_le64")
        [.var .local (ofString "kb"), .var .global (ofString "bal_index")])).1 = none →
      globN s "bal_key_buf" ≠ 0) := by
  set callP : ProgHOL 64 := .call (some (none, none)) (ofString "st_le64")
    [.var .local (ofString "kb"), .var .global (ofString "bal_index")]
  have hor := call0_or_resumes_local cur (ofString "st_le64")
    [.var .local (ofString "kb"), .var .global (ofString "bal_index")] hcr
  have hnz_of_args : ∀ wkb wbi : BitVec 64,
      evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a))
        [.var .local (ofString "kb"), .var .global (ofString "bal_index")] =
        some [.val (.word wkb), .val (.word wbi)] →
      cur.locals.lookup (ofString "kb") = some (.val (.word wkb)) →
      globN s "bal_key_buf" ≠ 0 := by
    intro wkb wbi hargs hkb_w
    have hres64 := call0_two_word_resumes_local cur (ofString "st_le64") (ofString "p") (ofString "v")
      (sourceFnBody Guest.Software.guestFn_st_le64) _ _ wkb wbi (by decide) h.code lookup_st_le64_local
      hargs hor
    let cent := callEntryStateHOLFinite cur
      ((HolFiniteMapExact.empty.update (ofString "p", .val (.word wkb))).update (ofString "v", .val (.word wbi)))
    have hlo := st_le64_resumes_lo cent wkb wbi h.code (guestInv_callEntry cur _ h.arena.1)
      (by simp [cent, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "v" ≠ ofString "p" by decide])
      (by simp [cent, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      hres64
    have hsb_pos : 0 < sourceBase := by rw [sourceBase_val]; decide
    have hwkb_eq : globN s "bal_key_buf" = wkb.toNat := by
      have hg_s : s.globals.lookup (ofString "bal_key_buf") = some (.val (.word wkb)) := by
        rw [← hkb]; exact hkb_w
      simp [globN, hg_s]
    omega
  refine ⟨worldEff_call0_funByteEff_local h Fast_C08WkShard03.funByteEff_st_le64 _
    [bufferRegion s ("bal_key_buf", 64)]
    (fun vals hargs i hi _ => by
      have hargs_orig := hargs
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact, evalHOLExact, toExact] at hargs
      rcases hkb_l : cur.locals.lookup (ofString "kb") with _ | vkb
      · simp [hkb_l] at hargs
      · rcases hbi_g : cur.globals.lookup (ofString "bal_index") with _ | vbi
        · simp [hkb_l, hbi_g] at hargs
        · simp only [hkb_l, hbi_g] at hargs
          injection hargs with hargs_eq; subst hargs_eq
          have hwords : ∃ (wkb wbi : BitVec 64), vkb = .val (.word wkb) ∧ vbi = .val (.word wbi) := by
            rcases hlk_c : PanSemStateFiniteExact.lookupCodeHOLFinite cur.code.lookup (ofString "st_le64") [vkb, vbi] with
              _ | ⟨b', c', r'⟩
            · exfalso
              rw [evaluateHOLFiniteState_call, hargs_orig] at hor
              dsimp only at hor
              rw [hlk_c] at hor
              rcases hor with h0 | ⟨_, h0⟩ | ⟨_, _, h0, _⟩ <;> simp at h0
            · have hsame := lookupCodeHOLFinite_installed_body cur.code.lookup (ofString "st_le64") _ _ b'
                _ r' [vkb, vbi] c' (by rw [h.code]; exact lookup_st_le64_local) hlk_c
              subst hsame
              have hret_eq := lookupCodeHOLFinite_installed_return cur (ofString "st_le64") _ _ _
                _ r' [vkb, vbi] c' (by rw [h.code]; exact lookup_st_le64_local) hlk_c
              subst hret_eq
              obtain ⟨wkb, wbi, heq, _, _⟩ := Fast_C08WkShard03.lookupCode_two_words (by decide)
                lookup_st_le64_local (by rw [← h.code]; exact hlk_c)
              injection heq with hv1 hv2
              injection hv2 with hv2 _
              exact ⟨wkb, wbi, hv1, hv2⟩
          obtain ⟨wkb, wbi, rfl, rfl⟩ := hwords
          have hnz := hnz_of_args wkb wbi hargs_orig hkb_l
          have hwkb_eq : wkb.toNat = globN s "bal_key_buf" := by
            have hg_s : s.globals.lookup (ofString "bal_key_buf") = some (.val (.word wkb)) := by
              rw [← hkb]; exact hkb_l
            simp [globN, hg_s]
          simp only [List.mem_singleton] at hi; subst hi
          refine ⟨bufferRegion s ("bal_key_buf", 64), List.mem_singleton.2 rfl, ?_, ?_⟩
          · simp [bufferRegion, Fast_C08WkShard03.valWordNat, hwkb_eq]
          · simp [bufferRegion, Fast_C08WkShard03.valWordNat, hwkb_eq, if_neg hnz])
    (fun iv hiv _ => by
      simp only [List.mem_singleton] at hiv; subst hiv
      exact Or.inr (Or.inl ⟨("bal_key_buf", 64), by decide, le_rfl, le_rfl⟩))
    hnt hcr, ?_⟩
  intro hnone
  have hnone' := hnone
  rw [evaluateHOLFiniteState_call] at hnone'
  unfold evalListHOLFinite at hnone'
  rcases hargs : @evalListHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      [.var .local (ofString "kb"), .var .global (ofString "bal_index")] with _ | vals
  · simp [hargs] at hnone'
  · simp only [hargs] at hnone'
    rcases hl : PanSemStateFiniteExact.lookupCodeHOLFinite cur.code.lookup (ofString "st_le64") vals with _ | ⟨b', c', r'⟩
    · simp [hl] at hnone'
    · have hsame := lookupCodeHOLFinite_installed_body cur.code.lookup (ofString "st_le64") _ _ b'
        _ r' vals c' (by rw [h.code]; exact lookup_st_le64_local) hl
      subst hsame
      have hret_eq := lookupCodeHOLFinite_installed_return cur (ofString "st_le64") _ _ _
        _ r' vals c' (by rw [h.code]; exact lookup_st_le64_local) hl
      subst hret_eq
      obtain ⟨wkb, wbi, rfl, _, _⟩ := Fast_C08WkShard03.lookupCode_two_words (by decide)
        lookup_st_le64_local (by rw [← h.code]; exact hl)
      have hargs_fin : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a))
          [.var .local (ofString "kb"), .var .global (ofString "bal_index")] =
          some [.val (.word wkb), .val (.word wbi)] := by
        rw [evalListHOLFinite_eq_toExact]; exact hargs
      have hargs_ex := hargs
      simp only [evalListHOLExact, evalHOLExact, toExact] at hargs_ex
      rcases hkb_l : cur.locals.lookup (ofString "kb") with _ | vkb
      · simp [hkb_l] at hargs_ex
      · rcases hbi_g : cur.globals.lookup (ofString "bal_index") with _ | vbi
        · simp [hkb_l, hbi_g] at hargs_ex
        · simp only [hkb_l, hbi_g] at hargs_ex
          injection hargs_ex with hargs_eq
          injection hargs_eq with hv1 _
          subst hv1
          exact hnz_of_args wkb wbi hargs_fin hkb_l

private theorem worldEff_memcpy_kb_off {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {gw : List String}
    (hW : WorldOK s)
    (h : WorldEff s cur Rl idxBufs gw)
    (hkb : cur.locals.lookup (ofString "kb") = s.globals.lookup (ofString "bal_key_buf"))
    (hnz : globN s "bal_key_buf" ≠ 0)
    (src : ExpHOL 64) (off len : BitVec 64)
    (hle : off.toNat + len.toNat ≤ 64)
    (hnt : (evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "kb"), .const off], src, .const len])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "kb"), .const off], src, .const len])).1) :
    WorldEff s (evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "kb"), .const off], src, .const len])).2 Rl idxBufs gw := by
  have hbound := bal_key_buf_upper_local hW hnz
  have hse : scratchEnd < 2 ^ 64 := by decide
  exact worldEff_call0_funByteEff_local h Fast_C08WkShard03.funByteEff_memcpy _
    [bufferRegion s ("bal_key_buf", 64)]
    (fun vals hargs i hi _ => by
      rw [evalListHOLFinite_eq_toExact] at hargs
      rcases he1 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
          (.op .add [.var .local (ofString "kb"), .const off]) with _ | v1
      · simp [evalListHOLExact, he1] at hargs
      · rcases he2 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
            src with _ | v2
        · simp [evalListHOLExact, he1, he2] at hargs
        · have he3 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
              (.const len) = some (.val (.word len)) := rfl
          have hargs' : @evalListHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
              [.op .add [.var .local (ofString "kb"), .const off], src, .const len] =
              some [v1, v2, .val (.word len)] := by
            unfold evalListHOLExact
            rw [he1]
            unfold evalListHOLExact
            rw [he2]
            unfold evalListHOLExact
            rw [he3]
            rfl
          rw [hargs'] at hargs
          injection hargs with hargs_eq; subst hargs_eq
          simp only [evalHOLExact, evalListHOLExact, toExact] at he1
          rcases hkb_l : cur.locals.lookup (ofString "kb") with _ | vkb
          · simp [hkb_l] at he1
          · rcases vkb with ⟨⟨wkb⟩⟩ | _ | _
            · simp [hkb_l, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp] at he1
              subst he1
              have hwkb : wkb.toNat = globN s "bal_key_buf" := by
                have hg_s : s.globals.lookup (ofString "bal_key_buf") = some (.val (.word wkb)) := by
                  rw [← hkb]; exact hkb_l
                simp [globN, hg_s]
              have hadd : (wkb + off).toNat = globN s "bal_key_buf" + off.toNat := by
                rw [BitVec.toNat_add, hwkb]
                exact Nat.mod_eq_of_lt (by omega)
              simp only [List.mem_singleton] at hi; subst hi
              refine ⟨bufferRegion s ("bal_key_buf", 64), List.mem_singleton.2 rfl, ?_, ?_⟩
              · simp [bufferRegion, Fast_C08WkShard03.valWordNat, hadd, if_neg hnz]
              · simp [bufferRegion, Fast_C08WkShard03.valWordNat, hadd, if_neg hnz]; omega
            · simp [hkb_l, valueIsWord] at he1
            · simp [hkb_l, valueIsWord] at he1)
    (fun iv hiv _ => by
      simp only [List.mem_singleton] at hiv; subst hiv
      exact Or.inr (Or.inl ⟨("bal_key_buf", 64), by decide, le_rfl, le_rfl⟩))
    hnt hcr

private theorem worldEff_to_worldStepSc_idx {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hW : WorldOK s)
    (heff : WorldEff s post [] idxBufs ["heap_ptr", "scratch_ptr"]) :
    WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra s r post := by
  have heff' : WorldEff s post (bufRegions idxBufs s) idxBufs ["heap_ptr", "scratch_ptr"] :=
    heff.mono (fun _ hiv => by cases hiv) (fun _ h => h) (fun _ h => h)
  refine ⟨heff'.to_worldStep_Q hW (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial), heff.sp_hi⟩

private theorem contOrRes_of_flowingOrResumes {r : Option (PanSemResultExact 64)}
    (hfr : FlowingOrResumes r) : ContOrRes r := by
  rcases hfr with h | h | h | hr
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr hr))

private theorem worldEff_memzero_alloc {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (h : WorldEff s cur Rl idxBufs gw)
    (pw : BitVec 64) (sz : BitVec 64)
    (hrec : cur.locals.lookup (ofString "rec") = some (.val (.word pw)))
    (hpw_lo : globN s "heap_ptr" ≤ pw.toNat)
    (hpw_hi : pw.toNat + sz.toNat ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "rec"), .const sz])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "rec"), .const sz])).1) :
    WorldEff s (evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "rec"), .const sz])).2 Rl idxBufs gw :=
  worldEff_call0_funByteEff_local h Fast_C08WkShard03.funByteEff_memzero _
    [(pw.toNat, sz.toNat)]
    (fun vals hargs i hi _ => by
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact, evalHOLExact, toExact, hrec] at hargs
      injection hargs with hargs_eq; subst hargs_eq
      simp only [List.mem_singleton] at hi; subst hi
      exact ⟨(pw.toNat, sz.toNat), List.mem_singleton.2 rfl,
        by simp [Fast_C08WkShard03.valWordNat], by simp [Fast_C08WkShard03.valWordNat]⟩)
    (fun iv hiv _ => by
      simp only [List.mem_singleton] at hiv; subst hiv
      exact Or.inr (Or.inr (Or.inr ⟨hpw_lo, hpw_hi⟩)))
    hnt hcr

private theorem worldEff_memcpy_alloc_off {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (h : WorldEff s cur Rl idxBufs gw)
    (pw : BitVec 64) (off len : BitVec 64) (src : ExpHOL 64)
    (hrec : cur.locals.lookup (ofString "rec") = some (.val (.word pw)))
    (hpw_lo : globN s "heap_ptr" ≤ pw.toNat)
    (hpw_hi : pw.toNat + off.toNat + len.toNat ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "rec"), .const off], src, .const len])).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "rec"), .const off], src, .const len])).1) :
    WorldEff s (evaluateHOLFiniteState cur
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "rec"), .const off], src, .const len])).2 Rl idxBufs gw := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  exact worldEff_call0_funByteEff_local h Fast_C08WkShard03.funByteEff_memcpy _
    [(pw.toNat + off.toNat, len.toNat)]
    (fun vals hargs i hi _ => by
      rw [evalListHOLFinite_eq_toExact] at hargs
      rcases he2 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
          src with _ | v2
      · simp [evalListHOLExact, evalHOLExact, toExact, hrec, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp, he2] at hargs
      · have he1 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
            (.op .add [.var .local (ofString "rec"), .const off]) = some (.val (.word (pw + off))) := by
          simp [evalHOLExact, evalListHOLExact, toExact, hrec, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]
        have he3 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
            (.const len) = some (.val (.word len)) := rfl
        have hargs' : @evalListHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
            [.op .add [.var .local (ofString "rec"), .const off], src, .const len] =
            some [.val (.word (pw + off)), v2, .val (.word len)] := by
          unfold evalListHOLExact; rw [he1]; unfold evalListHOLExact; rw [he2]; unfold evalListHOLExact; rw [he3]; rfl
        rw [hargs'] at hargs
        injection hargs with hargs_eq; subst hargs_eq
        have hadd : (pw + off).toNat = pw.toNat + off.toNat := by
          rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
        simp only [List.mem_singleton] at hi; subst hi
        exact ⟨(pw.toNat + off.toNat, len.toNat), List.mem_singleton.2 rfl,
          by simp [Fast_C08WkShard03.valWordNat, hadd], by simp [Fast_C08WkShard03.valWordNat, hadd]⟩)
    (fun iv hiv _ => by
      simp only [List.mem_singleton] at hiv; subst hiv
      exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
    hnt hcr

private theorem eval_load_u256_len {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load (.comb [.one, .one, .one, .one]) e) = some v → (flattenHOL v).length = 4 := by
  intro v hv
  simp only [evalHOLExact, isWfShapeExactHOL, ↓reduceIte] at hv
  rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | ev
  · simp [he] at hv
  · rcases ev with ⟨⟨a⟩⟩ | _ | _
    · simp only [he] at hv
      have hone : ∀ {b : BitVec 64} {v1 : ValueHOL 64},
          @memLoadHOLExact 64 _ .one b s.memaddrs (fun x => Classical.propDecidable (s.memaddrs x))
            s.memory s.structs = some v1 → (flattenHOL v1).length = 1 := by
        intro b v1 h1
        unfold memLoadHOLExact at h1
        split_ifs at h1
        simp only [Option.some.injEq] at h1
        subst h1
        simp [flattenHOL]
      unfold memLoadHOLExact at hv
      rcases hm0 : @memLoadsHOLExact 64 _ [.one, .one, .one, .one] a s.memaddrs
          (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | vs0
      · rw [hm0] at hv; simp at hv
      · rw [hm0] at hv
        split_ifs at hv
        simp only [Option.some.injEq] at hv
        subst hv
        unfold memLoadsHOLExact at hm0
        rcases hl1 : @memLoadHOLExact 64 _ .one a s.memaddrs
            (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | v1
        · rw [hl1] at hm0; simp at hm0
        · rw [hl1] at hm0
          rcases hm1 : @memLoadsHOLExact 64 _ [.one, .one, .one] _ s.memaddrs
              (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | vs1
          · rw [hm1] at hm0; simp at hm0
          · rw [hm1] at hm0
            simp only [Option.some.injEq] at hm0
            subst hm0
            unfold memLoadsHOLExact at hm1
            rcases hl2 : @memLoadHOLExact 64 _ .one _ s.memaddrs
                (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | v2
            · rw [hl2] at hm1; simp at hm1
            · rw [hl2] at hm1
              rcases hm2 : @memLoadsHOLExact 64 _ [.one, .one] _ s.memaddrs
                  (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | vs2
              · rw [hm2] at hm1; simp at hm1
              · rw [hm2] at hm1
                simp only [Option.some.injEq] at hm1
                subst hm1
                unfold memLoadsHOLExact at hm2
                rcases hl3 : @memLoadHOLExact 64 _ .one _ s.memaddrs
                    (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | v3
                · rw [hl3] at hm2; simp at hm2
                · rw [hl3] at hm2
                  rcases hm3 : @memLoadsHOLExact 64 _ [.one] _ s.memaddrs
                      (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | vs3
                  · rw [hm3] at hm2; simp at hm2
                  · rw [hm3] at hm2
                    simp only [Option.some.injEq] at hm2
                    subst hm2
                    unfold memLoadsHOLExact at hm3
                    rcases hl4 : @memLoadHOLExact 64 _ .one _ s.memaddrs
                        (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | v4
                    · rw [hl4] at hm3; simp at hm3
                    · rw [hl4] at hm3
                      rcases hm4 : @memLoadsHOLExact 64 _ [] _ s.memaddrs
                          (fun x => Classical.propDecidable (s.memaddrs x)) s.memory s.structs with _ | vs4
                      · rw [hm4] at hm3; simp at hm3
                      · rw [hm4] at hm3
                        simp only [Option.some.injEq] at hm3
                        subst hm3
                        unfold memLoadsHOLExact at hm4
                        simp only [Option.some.injEq] at hm4
                        subst hm4
                        have c1 := hone hl1
                        have c2 := hone hl2
                        have c3 := hone hl3
                        have c4 := hone hl4
                        conv_lhs => unfold flattenHOL
                        simp [c1, c2, c3, c4]
    · simp [he] at hv
    · simp [he] at hv

private theorem flattenHOL_shape_u256_local {v : ValueHOL 64}
    (hsh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v) = true) :
    (flattenHOL v).length = 4 := by
  rcases v with _ | fs | _
  · simp [shapeOfHOLExact, shapeEqHOL] at hsh
  · rcases fs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩⟩ <;>
      try (simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh)
    rcases v0 with ⟨⟨a⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨b⟩⟩ | _ | _ <;>
      rcases v2 with ⟨⟨c⟩⟩ | _ | _ <;> rcases v3 with ⟨⟨d⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hsh
    simp [flattenHOL]
  · simp [shapeOfHOLExact, shapeEqHOL] at hsh

private theorem progWStep_seq_worldEff_idx {p1 p2 : ProgHOL 64} {F : Type}
    {s : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (heff1 : (evaluateHOLFiniteState s p1).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState s p1).1 →
      WorldEff s (evaluateHOLFiniteState s p1).2 [] idxBufs ["heap_ptr", "scratch_ptr"])
    (h2 : ∀ mid, evaluateHOLFiniteState s p1 = (none, mid) →
      mid.code = originalRuntimeCode → WorldOK mid →
      WorldEff s mid [] idxBufs ["heap_ptr", "scratch_ptr"] →
      (evaluateHOLFiniteState mid p2).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState mid p2).1 →
      WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
        mid (evaluateHOLFiniteState mid p2).1 (evaluateHOLFiniteState mid p2).2)
    (hnt : (evaluateHOLFiniteState s (.seq p1 p2)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s (.seq p1 p2)).1) :
    WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      s (evaluateHOLFiniteState s (.seq p1 p2)).1 (evaluateHOLFiniteState s (.seq p1 p2)).2 := by
  have hB := validBufList_idxBufs
  have hgw := safeStepGlobals_hp_sp
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, mid⟩
  simp only [hr1] at hnt hfr ⊢
  cases r1 with
  | none =>
    have he1 := heff1 (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at he1; dsimp only at he1
    have hs1 : WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra s none mid :=
      worldEff_to_worldStepSc_idx hW he1
    have hW_mid : WorldOK mid := hs1.worldOK_bufs hB hW
    have hs2 := h2 mid hr1 he1.code hW_mid he1 hnt hfr
    exact WorldStepSc.trans hB hgw hs1 hs2
  | some r =>
    have he1 := heff1 (by rw [hr1]; exact hnt) (by rw [hr1]; exact contOrRes_of_flowingOrResumes hfr)
    rw [hr1] at he1; dsimp only at he1
    exact worldEff_to_worldStepSc_idx hW he1

private theorem progWStep_decCall_alloc_seq_idx {sz : BitVec 64} {pWrite pRest : ProgHOL 64} {F : Type}
    {s : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hWrite : ∀ (pw : BitVec 64) (m1 : PanSemStateFiniteExact 64 F),
      m1.locals = s.locals.update (ofString "rec", .val (.word pw)) →
      (∀ k : MlS, k ≠ ofString "heap_ptr" → m1.globals.lookup k = s.globals.lookup k) →
      WorldEff s m1 [] idxBufs ["heap_ptr", "scratch_ptr"] →
      globN s "heap_ptr" ≤ pw.toNat →
      pw.toNat + (sz.toNat + 7) / 8 * 8 = globN m1 "heap_ptr" →
      globN m1 "heap_ptr" ≤ heapLimit →
      (evaluateHOLFiniteState m1 pWrite).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState m1 pWrite).1 →
      WorldEff s (evaluateHOLFiniteState m1 pWrite).2 [] idxBufs ["heap_ptr", "scratch_ptr"])
    (hRest : ProgWStep idxBufs ["heap_ptr", "scratch_ptr"] pRest)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString "rec") .one (ofString "alloc") [.const sz] (.seq pWrite pRest))).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.decCall (ofString "rec") .one (ofString "alloc") [.const sz] (.seq pWrite pRest))).1) :
    WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      s (evaluateHOLFiniteState s
        (.decCall (ofString "rec") .one (ofString "alloc") [.const sz] (.seq pWrite pRest))).1
      (evaluateHOLFiniteState s
        (.decCall (ofString "rec") .one (ofString "alloc") [.const sz] (.seq pWrite pRest))).2 := by
  have hB := validBufList_idxBufs
  have hgw := safeStepGlobals_hp_sp
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const sz] =
      some [.val (.word sz)] := rfl
  simp only [hargs] at hnt hfr ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") [.val (.word sz)] with
    _ | ⟨body', callee, ret'⟩
  · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hl] at hnt hfr ⊢
    by_cases hz : s.clock = 0
    · simp [hz] at hnt
    · rw [if_neg hz] at hnt hfr ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "alloc") _ _ body'
        _ ret' [.val (.word sz)] callee (by rw [hc]; exact lookup_alloc) hl
      subst hsame
      have hret_eq := lookupCodeHOLFinite_installed_return s (ofString "alloc") _ _ _
        _ ret' [.val (.word sz)] callee (by rw [hc]; exact lookup_alloc) hl
      subst hret_eq
      obtain ⟨nw, hnw_eq, hnw_callee⟩ := Fast_C08WkShard03.lookupCode_one_word lookup_alloc (by rw [← hc]; exact hl)
      injection hnw_eq with hnw_eq'; injection hnw_eq' with hnw_eq'; injection hnw_eq' with hnw_eq'; subst hnw_eq'
      obtain ⟨pw, hpw_lk⟩ : ∃ pw : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) :=
        globalWord_of_globN_pos s "heap_ptr" (by have := hW.1.2.1; rw [sourceBase_val] at this; omega)
      let entry := callEntryStateHOLFinite s callee
      rcases hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_alloc) with ⟨res, pa⟩
      dsimp only [entry] at hrun
      simp only [hrun] at hnt hfr ⊢
      have hcr_outer := contOrRes_of_flowingOrResumes hfr
      have hres_a : Resumes res := by
        cases res with
        | none => rcases hcr_outer with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
        | some r1 =>
          cases r1 with
          | returned rv => exact Or.inl ⟨rv, rfl⟩
          | exception eid ev =>
            rcases hcr_outer with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨e', v', hc0, hne⟩⟩
            · simp at hc0
            · simp at hc0
            · simp at hc0
            · simp at hc0
            · change some (PanSemResultExact.exception eid ev) = some (PanSemResultExact.exception e' v') at hc0
              injection hc0 with hc0'; injection hc0' with he1 he2; subst he1 he2
              exact Or.inr ⟨eid, ev, rfl, hne⟩
          | timeOut => simp at hnt
          | _ => rcases hcr_outer with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
      have hal := InitECandidate.Solver.Wave8GuestInv.R13.alloc_body_resumes entry pw hc hpw_lk
        (by dsimp only [entry]; rw [hrun]; exact hres_a)
      dsimp only [entry] at hal
      rw [hrun] at hal
      obtain ⟨nw', hnw'_lk, hrv_eq, hcmp1, hcmp2, hpa_eq⟩ := hal
      have hnw_eq2 : sz = nw' := by
        have : entry.locals.lookup (ofString "n") = some (.val (.word sz)) := hnw_callee
        rw [this] at hnw'_lk; injection hnw'_lk with h'; injection h' with h'; injection h'
      subst hnw_eq2
      dsimp only at hrv_eq hpa_eq
      subst hrv_eq
      dsimp only at hnt hfr ⊢
      have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      rw [if_pos hsh] at hnt hfr ⊢
      dsimp only at hnt hfr ⊢
      set m1 := setVarHOLFinite (ofString "rec") (.val (.word pw)) { pa with locals := s.locals }
      have hm1_next : m1 = { s with
          globals := s.globals.update (ofString "heap_ptr", .val (.word ((pw + (sz + 7)) &&& ((0 : BitVec 64) - 8)))),
          locals := m1.locals, clock := m1.clock } := by
        dsimp only [m1, setVarHOLFinite]; rw [hpa_eq]; rfl
      have heff_s : WorldEff s s [] idxBufs ["heap_ptr", "scratch_ptr"] :=
        WorldEff.refl s [] idxBufs ["heap_ptr", "scratch_ptr"] hW.1 hc
      obtain ⟨heff_m1, _, _, _, hp_lo_s, hp_add, hp_hi, _⟩ :=
        worldEff_alloc_step heff_s (by decide) hpw_lk hcmp1 hcmp2 hm1_next
      have hm1_loc : m1.locals = s.locals.update (ofString "rec", .val (.word pw)) := rfl
      have hm1_g : ∀ k : MlS, k ≠ ofString "heap_ptr" → m1.globals.lookup k = s.globals.lookup k := by
        intro k hk; rw [hm1_next]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
      rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
      rcases hrw : evaluateHOLFiniteState m1 pWrite with ⟨rw1, m2⟩
      simp only [hrw] at hnt hfr ⊢
      cases rw1 with
      | none =>
        have heff_m2 := hWrite pw m1 hm1_loc hm1_g heff_m1 hp_lo_s hp_add hp_hi
          (by rw [hrw]; simp) (by rw [hrw]; exact Or.inl rfl)
        rw [hrw] at heff_m2; dsimp only at heff_m2
        have hs12 : WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra s none m2 :=
          worldEff_to_worldStepSc_idx hW heff_m2
        have hW_m2 : WorldOK m2 := hs12.worldOK_bufs hB hW
        have hs23 := hRest m2 heff_m2.code hW_m2 hnt hfr
        have hs23' := hs23.with_locals_clock (r' := (evaluateHOLFiniteState m2 pRest).1)
          (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState m2 pRest).2.locals
            (ofString "rec", s.locals.lookup (ofString "rec")))
          (evaluateHOLFiniteState m2 pRest).2.clock
        exact WorldStepSc.trans hB hgw hs12 hs23'
      | some r =>
        have heff_m2 := hWrite pw m1 hm1_loc hm1_g heff_m1 hp_lo_s hp_add hp_hi
          (by rw [hrw]; exact hnt) (by rw [hrw]; exact contOrRes_of_flowingOrResumes hfr)
        rw [hrw] at heff_m2; dsimp only at heff_m2
        have hs12 : WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra s (some r) m2 :=
          worldEff_to_worldStepSc_idx hW heff_m2
        exact hs12.with_locals_clock (r' := some r)
          (HolFiniteMapExact.resVarEq m2.locals (ofString "rec", s.locals.lookup (ofString "rec")))
          m2.clock

private theorem locals_eq_of_avoidsLocal {F : Type}
    (s : PanSemStateFiniteExact 64 F) (prog : ProgHOL 64)
    (hav : ∀ k : MlS, avoidsLocal k prog = true)
    (hnone : (evaluateHOLFiniteState s prog).1 = none) :
    (evaluateHOLFiniteState s prog).2.locals = s.locals := by
  apply HolFiniteMapExact.ext
  funext k
  exact evaluate_avoidsLocal_flowing k prog (hav k) s (Or.inl hnone)

private theorem worldEff_kb_st_memcpy20 {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (hW : WorldOK s)
    (h : WorldEff s cur Rl idxBufs gw)
    (hkb : cur.locals.lookup (ofString "kb") = s.globals.lookup (ofString "bal_key_buf"))
    (hnt : (evaluateHOLFiniteState cur
      (.seq
        (.call (some (none, none)) (ofString "st_le64")
          [.var .local (ofString "kb"), .var .global (ofString "bal_index")])
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "kb"), .const 8#64],
            .var .local (ofString "addr"), .const 20#64]))).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur
      (.seq
        (.call (some (none, none)) (ofString "st_le64")
          [.var .local (ofString "kb"), .var .global (ofString "bal_index")])
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "kb"), .const 8#64],
            .var .local (ofString "addr"), .const 20#64]))).1) :
    WorldEff s (evaluateHOLFiniteState cur
      (.seq
        (.call (some (none, none)) (ofString "st_le64")
          [.var .local (ofString "kb"), .var .global (ofString "bal_index")])
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "kb"), .const 8#64],
            .var .local (ofString "addr"), .const 20#64]))).2 Rl idxBufs gw := by
  refine worldEff_seq hnt hcr
    (fun hnt1 hcr1 => (worldEff_st_le64_kb h hkb hnt1 hcr1).1)
    (fun mid hmid heff_mid hnt2 hcr2 => ?_)
  have hnz := (worldEff_st_le64_kb h
    hkb (by rw [hmid]; simp) (by rw [hmid]; exact Or.inl rfl)).2 (by rw [hmid])
  have hmid_loc : mid.locals = cur.locals := by
    have := call0_none_locals_local cur (ofString "st_le64")
      [.var .local (ofString "kb"), .var .global (ofString "bal_index")] (by rw [hmid])
    rwa [hmid] at this
  exact worldEff_memcpy_kb_off hW heff_mid (by rw [hmid_loc]; exact hkb) hnz _ 8#64 20#64 (by decide) hnt2 hcr2

private theorem worldEff_kb_st_memcpy20_32 {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (hW : WorldOK s)
    (h : WorldEff s cur Rl idxBufs gw)
    (hkb : cur.locals.lookup (ofString "kb") = s.globals.lookup (ofString "bal_key_buf"))
    (hnt : (evaluateHOLFiniteState cur
      (.seq
        (.call (some (none, none)) (ofString "st_le64")
          [.var .local (ofString "kb"), .var .global (ofString "bal_index")])
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "kb"), .const 8#64],
              .var .local (ofString "addr"), .const 20#64])
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "kb"), .const 28#64],
              .var .local (ofString "key"), .const 32#64])))).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur
      (.seq
        (.call (some (none, none)) (ofString "st_le64")
          [.var .local (ofString "kb"), .var .global (ofString "bal_index")])
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "kb"), .const 8#64],
              .var .local (ofString "addr"), .const 20#64])
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "kb"), .const 28#64],
              .var .local (ofString "key"), .const 32#64])))).1) :
    WorldEff s (evaluateHOLFiniteState cur
      (.seq
        (.call (some (none, none)) (ofString "st_le64")
          [.var .local (ofString "kb"), .var .global (ofString "bal_index")])
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "kb"), .const 8#64],
              .var .local (ofString "addr"), .const 20#64])
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "kb"), .const 28#64],
              .var .local (ofString "key"), .const 32#64])))).2 Rl idxBufs gw := by
  refine worldEff_seq hnt hcr
    (fun hnt1 hcr1 => (worldEff_st_le64_kb h hkb hnt1 hcr1).1)
    (fun m1 hm1 heff_m1 hnt2 hcr2 => ?_)
  have hnz := (worldEff_st_le64_kb h
    hkb (by rw [hm1]; simp) (by rw [hm1]; exact Or.inl rfl)).2 (by rw [hm1])
  have hm1_loc : m1.locals = cur.locals := by
    have := call0_none_locals_local cur (ofString "st_le64")
      [.var .local (ofString "kb"), .var .global (ofString "bal_index")] (by rw [hm1])
    rwa [hm1] at this
  refine worldEff_seq hnt2 hcr2
    (fun hnt2a hcr2a =>
      worldEff_memcpy_kb_off hW heff_m1 (by rw [hm1_loc]; exact hkb) hnz _ 8#64 20#64 (by decide) hnt2a hcr2a)
    (fun m2 hm2 heff_m2 hnt3 hcr3 => ?_)
  have hm2_loc : m2.locals = m1.locals := by
    have := call0_none_locals_local m1 (ofString "memcpy") _ (by rw [hm2])
    rwa [hm2] at this
  exact worldEff_memcpy_kb_off hW heff_m2 (by rw [hm2_loc, hm1_loc]; exact hkb) hnz _ 28#64 32#64 (by decide) hnt3 hcr3

private theorem seq_reassoc_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b c : ProgHOL 64) :
    evaluateHOLFiniteState s (.seq a (.seq b c)) = evaluateHOLFiniteState s (.seq (.seq a b) c) := by
  simp only [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s a with ⟨ra, ma⟩
  cases ra <;> rfl

private theorem progWStep_reassoc {B : BufList} {gw : List String}
    {a b c : ProgHOL 64}
    (h : ProgWStep B gw (.seq (.seq a b) c)) :
    ProgWStep B gw (.seq a (.seq b c)) := by
  intro F s hc hW hnt hfr
  rw [seq_reassoc_eval] at hnt hfr ⊢
  exact h s hc hW hnt hfr

private theorem evaluate_reassoc_worldEff {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    {a b c : ProgHOL 64}
    (h : (evaluateHOLFiniteState cur (.seq (.seq a b) c)).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState cur (.seq (.seq a b) c)).1 →
      WorldEff s (evaluateHOLFiniteState cur (.seq (.seq a b) c)).2 Rl B gw)
    (hnt : (evaluateHOLFiniteState cur (.seq a (.seq b c))).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.seq a (.seq b c))).1) :
    WorldEff s (evaluateHOLFiniteState cur (.seq a (.seq b c))).2 Rl B gw := by
  rw [seq_reassoc_eval] at hnt hcr ⊢
  exact h hnt hcr

private theorem progWStep_dec_kb {body : ProgHOL 64}
    (hb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → WorldOK s →
      s.locals.lookup (ofString "kb") = s.globals.lookup (ofString "bal_key_buf") →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState s body).1 →
      WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
        s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2) :
    ProgWStep idxBufs ["heap_ptr", "scratch_ptr"]
      (.dec (ofString "kb") .one (.var .global (ofString "bal_key_buf")) body) := by
  intro F s hc hW hnt hfr
  rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .global (ofString "bal_key_buf")) with _ | val
  · simp [hev] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hev] at hnt hfr ⊢
    by_cases hok : shapeEqHOL .one (shapeOfHOLExact val) = true
    · simp only [hok, ↓reduceIte] at hnt hfr ⊢
      set s1 := setVarHOLFinite (ofString "kb") val s
      have hW1 : WorldOK s1 := localsFree_worldOK s _ s.clock hW
      have hkb1 : s1.locals.lookup (ofString "kb") = s1.globals.lookup (ofString "bal_key_buf") := by
        simp only [evalHOLExact, toExact] at hev
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hev]
      have hstep := hb s1 hc hW1 hkb1 hnt hfr
      exact (WorldStepSc.of_pre_locals_clock hstep).with_locals_clock _ (evaluateHOLFiniteState s1 body).2.clock
    · simp [hok] at hfr; exact absurd hfr not_flowingOrResumes_error

private theorem progWStep_decCall_keep_kb {x : MlS} {sh : ShapeHOL} {fname : MlS}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64} {B1 : BufList} {gw1 : List String}
    (hx_ne : x ≠ ofString "kb")
    (hB : ∀ p ∈ B1, p ∈ idxBufs)
    (hgw : ∀ g ∈ gw1, g ∈ ["heap_ptr", "scratch_ptr"])
    (hf : WorldKeepsSc WorldOK (bufRegions B1) gw1 stdKeep NoExtra fname)
    (hcont : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → WorldOK s →
      s.locals.lookup (ofString "kb") = s.globals.lookup (ofString "bal_key_buf") →
      (evaluateHOLFiniteState s cont).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState s cont).1 →
      WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
        s (evaluateHOLFiniteState s cont).1 (evaluateHOLFiniteState s cont).2) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → WorldOK s →
      s.locals.lookup (ofString "kb") = s.globals.lookup (ofString "bal_key_buf") →
      (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1 →
      WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
        s (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1
        (evaluateHOLFiniteState s (.decCall x sh fname args cont)).2 := by
  intro F s hc hW hkb hnt hfr
  have hBvalid := validBufList_idxBufs
  have hgwSafe := safeStepGlobals_hp_sp
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        let ent := callEntryStateHOLFinite s callee
        have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata ent body').1
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
        simp only [ent] at hrun hmeta
        simp only [hrun] at hmeta hnt hfr ⊢
        have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro rfl; simp at hnt
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh && shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
              simp only [ent, hrun] at hspec
              have hstep1 := (hspec (Or.inl ⟨v, rfl⟩)).mono_bufs hB hgw
              set s1 := setVarHOLFinite x v { cpost with locals := s.locals }
              have hs1_step : WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra s none s1 :=
                hstep1.from_entry
              have hWs1 : WorldOK s1 := hs1_step.worldOK_bufs hBvalid hW
              have hs1_code : s1.code = originalRuntimeCode := hmeta.trans hc
              have hg_keep : s1.globals.lookup (ofString "bal_key_buf") = s.globals.lookup (ofString "bal_key_buf") :=
                (hs1_step.1.2.2.1 (ofString "bal_key_buf") (by decide)).symm
              have hs1_kb : s1.locals.lookup (ofString "kb") = s1.globals.lookup (ofString "bal_key_buf") := by
                rw [hg_keep]
                simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hx_ne, hkb]
              have hstep2 := hcont s1 hs1_code hWs1 hs1_kb hnt hfr
              have hstep2' := hstep2.with_locals_clock (r' := (evaluateHOLFiniteState s1 cont).1)
                (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 cont).2.locals (x, s.locals.lookup x))
                (evaluateHOLFiniteState s1 cont).2.clock
              exact WorldStepSc.trans hBvalid hgwSafe hs1_step hstep2'
            · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
            simp only [ent, hrun] at hspec
            have hstep := (hspec hres_ex).mono_bufs hB hgw
            exact hstep.from_entry

private theorem progWStep_decCall_alloc_idx {sz : BitVec 64} {cont : ProgHOL 64} {F : Type}
    {s : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (hW : WorldOK s)
    (hCont : ∀ (pw : BitVec 64) (m1 : PanSemStateFiniteExact 64 F),
      m1.code = originalRuntimeCode → WorldOK m1 →
      m1.locals = s.locals.update (ofString "rec", .val (.word pw)) →
      (∀ k : MlS, k ≠ ofString "heap_ptr" → m1.globals.lookup k = s.globals.lookup k) →
      WorldEff s m1 [] idxBufs ["heap_ptr", "scratch_ptr"] →
      globN s "heap_ptr" ≤ pw.toNat →
      pw.toNat + (sz.toNat + 7) / 8 * 8 = globN m1 "heap_ptr" →
      globN m1 "heap_ptr" ≤ heapLimit →
      (evaluateHOLFiniteState m1 cont).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState m1 cont).1 →
      WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
        s (evaluateHOLFiniteState m1 cont).1 (evaluateHOLFiniteState m1 cont).2)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString "rec") .one (ofString "alloc") [.const sz] cont)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.decCall (ofString "rec") .one (ofString "alloc") [.const sz] cont)).1) :
    WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      s (evaluateHOLFiniteState s
        (.decCall (ofString "rec") .one (ofString "alloc") [.const sz] cont)).1
      (evaluateHOLFiniteState s
        (.decCall (ofString "rec") .one (ofString "alloc") [.const sz] cont)).2 := by
  have hB := validBufList_idxBufs
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const sz] =
      some [.val (.word sz)] := rfl
  simp only [hargs] at hnt hfr ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") [.val (.word sz)] with
    _ | ⟨body', callee, ret'⟩
  · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hl] at hnt hfr ⊢
    by_cases hz : s.clock = 0
    · simp [hz] at hnt
    · rw [if_neg hz] at hnt hfr ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "alloc") _ _ body'
        _ ret' [.val (.word sz)] callee (by rw [hc]; exact lookup_alloc) hl
      subst hsame
      have hret_eq := lookupCodeHOLFinite_installed_return s (ofString "alloc") _ _ _
        _ ret' [.val (.word sz)] callee (by rw [hc]; exact lookup_alloc) hl
      subst hret_eq
      obtain ⟨nw, hnw_eq, hnw_callee⟩ := Fast_C08WkShard03.lookupCode_one_word lookup_alloc (by rw [← hc]; exact hl)
      injection hnw_eq with hnw_eq'; injection hnw_eq' with hnw_eq'; injection hnw_eq' with hnw_eq'; subst hnw_eq'
      obtain ⟨pw, hpw_lk⟩ : ∃ pw : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word pw)) :=
        globalWord_of_globN_pos s "heap_ptr" (by have := hW.1.2.1; rw [sourceBase_val] at this; omega)
      let entry := callEntryStateHOLFinite s callee
      rcases hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_alloc) with ⟨res, pa⟩
      dsimp only [entry] at hrun
      simp only [hrun] at hnt hfr ⊢
      have hcr_outer := contOrRes_of_flowingOrResumes hfr
      have hres_a : Resumes res := by
        cases res with
        | none => rcases hcr_outer with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
        | some r1 =>
          cases r1 with
          | returned rv => exact Or.inl ⟨rv, rfl⟩
          | exception eid ev =>
            rcases hcr_outer with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨e', v', hc0, hne⟩⟩
            · simp at hc0
            · simp at hc0
            · simp at hc0
            · simp at hc0
            · change some (PanSemResultExact.exception eid ev) = some (PanSemResultExact.exception e' v') at hc0
              injection hc0 with hc0'; injection hc0' with he1 he2; subst he1 he2
              exact Or.inr ⟨eid, ev, rfl, hne⟩
          | timeOut => simp at hnt
          | _ => rcases hcr_outer with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
      have hal := InitECandidate.Solver.Wave8GuestInv.R13.alloc_body_resumes entry pw hc hpw_lk
        (by dsimp only [entry]; rw [hrun]; exact hres_a)
      dsimp only [entry] at hal
      rw [hrun] at hal
      obtain ⟨nw', hnw'_lk, hrv_eq, hcmp1, hcmp2, hpa_eq⟩ := hal
      have hnw_eq2 : sz = nw' := by
        have : entry.locals.lookup (ofString "n") = some (.val (.word sz)) := hnw_callee
        rw [this] at hnw'_lk; injection hnw'_lk with h'; injection h' with h'; injection h'
      subst hnw_eq2
      dsimp only at hrv_eq hpa_eq
      subst hrv_eq
      dsimp only at hnt hfr ⊢
      have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word pw))) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      rw [if_pos hsh] at hnt hfr ⊢
      dsimp only at hnt hfr ⊢
      set m1 := setVarHOLFinite (ofString "rec") (.val (.word pw)) { pa with locals := s.locals }
      have hm1_next : m1 = { s with
          globals := s.globals.update (ofString "heap_ptr", .val (.word ((pw + (sz + 7)) &&& ((0 : BitVec 64) - 8)))),
          locals := m1.locals, clock := m1.clock } := by
        dsimp only [m1, setVarHOLFinite]; rw [hpa_eq]; rfl
      have heff_s : WorldEff s s [] idxBufs ["heap_ptr", "scratch_ptr"] :=
        WorldEff.refl s [] idxBufs ["heap_ptr", "scratch_ptr"] hW.1 hc
      obtain ⟨heff_m1, _, _, _, hp_lo_s, hp_add, hp_hi, _⟩ :=
        worldEff_alloc_step heff_s (by decide) hpw_lk hcmp1 hcmp2 hm1_next
      have hs_m1 : WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra s none m1 :=
        worldEff_to_worldStepSc_idx hW heff_m1
      have hW_m1 : WorldOK m1 := hs_m1.worldOK_bufs hB hW
      have hm1_loc : m1.locals = s.locals.update (ofString "rec", .val (.word pw)) := rfl
      have hm1_g : ∀ k : MlS, k ≠ ofString "heap_ptr" → m1.globals.lookup k = s.globals.lookup k := by
        intro k hk; rw [hm1_next]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
      have hstep := hCont pw m1 heff_m1.code hW_m1 hm1_loc hm1_g heff_m1 hp_lo_s hp_add hp_hi hnt hfr
      exact hstep.with_locals_clock (r' := (evaluateHOLFiniteState m1 cont).1)
        (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState m1 cont).2.locals
          (ofString "rec", s.locals.lookup (ofString "rec")))
        (evaluateHOLFiniteState m1 cont).2.clock

private theorem progWStep_seq_worldEff_from {p1 p2 : ProgHOL 64} {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F}
    (hW0 : WorldOK s0)
    (heff1 : (evaluateHOLFiniteState cur p1).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState cur p1).1 →
      WorldEff s0 (evaluateHOLFiniteState cur p1).2 [] idxBufs ["heap_ptr", "scratch_ptr"])
    (h2 : ∀ mid, evaluateHOLFiniteState cur p1 = (none, mid) →
      mid.code = originalRuntimeCode → WorldOK mid →
      WorldEff s0 mid [] idxBufs ["heap_ptr", "scratch_ptr"] →
      (evaluateHOLFiniteState mid p2).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState mid p2).1 →
      WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
        s0 (evaluateHOLFiniteState mid p2).1 (evaluateHOLFiniteState mid p2).2)
    (hnt : (evaluateHOLFiniteState cur (.seq p1 p2)).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState cur (.seq p1 p2)).1) :
    WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      s0 (evaluateHOLFiniteState cur (.seq p1 p2)).1 (evaluateHOLFiniteState cur (.seq p1 p2)).2 := by
  have hB := validBufList_idxBufs
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hr1 : evaluateHOLFiniteState cur p1 with ⟨r1, mid⟩
  simp only [hr1] at hnt hfr ⊢
  cases r1 with
  | none =>
    have he1 := heff1 (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at he1; dsimp only at he1
    have hs1 : WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra s0 none mid :=
      worldEff_to_worldStepSc_idx hW0 he1
    have hW_mid : WorldOK mid := hs1.worldOK_bufs hB hW0
    exact h2 mid hr1 he1.code hW_mid he1 hnt hfr
  | some r =>
    have he1 := heff1 (by rw [hr1]; exact hnt) (by rw [hr1]; exact contOrRes_of_flowingOrResumes hfr)
    rw [hr1] at he1; dsimp only at he1
    exact worldEff_to_worldStepSc_idx hW0 he1

private theorem worldEff_ite_pre_rec {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (h : WorldEff s cur Rl idxBufs gw)
    (pw : BitVec 64)
    (hrec : cur.locals.lookup (ofString "rec") = some (.val (.word pw)))
    (hpw_lo : globN s "heap_ptr" ≤ pw.toNat)
    (hpw_hi : pw.toNat + 80 ≤ heapLimit)
    (hnt : (evaluateHOLFiniteState cur
      (.ite (.cmp .notEqual (.var .local (ofString "pre")) (.const 1#64))
        (.seq
          (.store (.var .local (ofString "rec")) (.const 1#64))
          (.seq
            (.store (.op .add [.var .local (ofString "rec"), .const 8#64])
              (.load .one (.op .add [.var .local (ofString "pre"), .const 0#64])))
            (.seq
              (.store (.op .add [.var .local (ofString "rec"), .const 16#64])
                (.load (.comb [.one, .one, .one, .one])
                  (.op .add [.var .local (ofString "pre"), .const 8#64])))
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "rec"), .const 48#64],
                  .load .one (.op .add [.var .local (ofString "pre"), .const 48#64]),
                  .const 32#64]))))
        .skip)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur
      (.ite (.cmp .notEqual (.var .local (ofString "pre")) (.const 1#64))
        (.seq
          (.store (.var .local (ofString "rec")) (.const 1#64))
          (.seq
            (.store (.op .add [.var .local (ofString "rec"), .const 8#64])
              (.load .one (.op .add [.var .local (ofString "pre"), .const 0#64])))
            (.seq
              (.store (.op .add [.var .local (ofString "rec"), .const 16#64])
                (.load (.comb [.one, .one, .one, .one])
                  (.op .add [.var .local (ofString "pre"), .const 8#64])))
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "rec"), .const 48#64],
                  .load .one (.op .add [.var .local (ofString "pre"), .const 48#64]),
                  .const 32#64]))))
        .skip)).1) :
    WorldEff s (evaluateHOLFiniteState cur
      (.ite (.cmp .notEqual (.var .local (ofString "pre")) (.const 1#64))
        (.seq
          (.store (.var .local (ofString "rec")) (.const 1#64))
          (.seq
            (.store (.op .add [.var .local (ofString "rec"), .const 8#64])
              (.load .one (.op .add [.var .local (ofString "pre"), .const 0#64])))
            (.seq
              (.store (.op .add [.var .local (ofString "rec"), .const 16#64])
                (.load (.comb [.one, .one, .one, .one])
                  (.op .add [.var .local (ofString "pre"), .const 8#64])))
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "rec"), .const 48#64],
                  .load .one (.op .add [.var .local (ofString "pre"), .const 48#64]),
                  .const 32#64]))))
        .skip)).2 Rl idxBufs gw := by
  have hhl_he : heapLimit ≤ heapEnd := by decide
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  refine worldEff_ite h _ hnt hcr
    (fun cw _ _ hnt_y hcr_y => ?_)
    (fun _ _ _ => worldEff_skip h)
  -- Store 1: `*rec := 1`
  refine worldEff_seq hnt_y hcr_y
    (fun _ _ => worldEff_store_word h _ _
      (fun v hv => by simp [evalHOLExact] at hv; exact ⟨1#64, hv.symm⟩)
      (fun x hx _ => by
        simp [evalHOLExact, toExact, hrec] at hx
        subst hx
        exact Or.inr (Or.inr (Or.inr ⟨hpw_lo, by omega⟩))))
    (fun a1 ha1 heff_a1 hnt_a1 hcr_a1 => ?_)
  have ha1_loc : a1.locals = cur.locals := by
    have hk := locals_eq_of_avoidsLocal cur _ (fun _ => rfl) (by rw [ha1])
    rwa [ha1] at hk
  -- Store 2: `*(rec + 8) := *(pre + 0)`
  refine worldEff_seq hnt_a1 hcr_a1
    (fun _ _ => worldEff_store_word heff_a1 _ _
      (fun v hv => Fast_C08WkShard03.eval_load_one_word a1 _ v hv)
      (fun x hx _ => by
        simp [evalHOLExact, evalListHOLExact, toExact, ha1_loc, hrec, panOpHOL, wordOpHOL, wordOp,
          valueIsWord, valueWord] at hx
        subst hx
        have hx8 : (pw + 8#64).toNat = pw.toNat + 8 := by
          apply BitVec.toNat_add_of_lt; change pw.toNat + 8 < 2 ^ 64; omega
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
    (fun a2 ha2 heff_a2 hnt_a2 hcr_a2 => ?_)
  have ha2_loc : a2.locals = cur.locals := by
    have hk := locals_eq_of_avoidsLocal a1 _ (fun _ => rfl) (by rw [ha2])
    rw [ha2] at hk; exact hk.trans ha1_loc
  -- Store 3: `*(rec + 16) := u256(*(pre + 8))` (4 words)
  refine worldEff_seq hnt_a2 hcr_a2
    (fun _ _ => worldEff_store_multi heff_a2 _ _ 4 (by decide)
      (fun v hv => eval_load_u256_len a2 _ v hv)
      (fun x hx => by
        simp [evalHOLExact, evalListHOLExact, toExact, ha2_loc, hrec, panOpHOL, wordOpHOL, wordOp,
          valueIsWord, valueWord] at hx
        subst hx
        have hx16 : (pw + 16#64).toNat = pw.toNat + 16 := by
          apply BitVec.toNat_add_of_lt; change pw.toNat + 16 < 2 ^ 64; omega
        exact ⟨by omega, Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))⟩))
    (fun a3 ha3 heff_a3 hnt_a3 hcr_a3 => ?_)
  have ha3_loc : a3.locals = cur.locals := by
    have hk := locals_eq_of_avoidsLocal a2 _ (fun _ => rfl) (by rw [ha3])
    rw [ha3] at hk; exact hk.trans ha2_loc
  -- Call 4: `memcpy(rec + 48, *(pre + 48), 32)`
  exact worldEff_memcpy_alloc_off heff_a3 pw 48#64 32#64 _
    (by rw [ha3_loc]; exact hrec) hpw_lo (by change pw.toNat + 48 + 32 ≤ heapLimit; omega) hnt_a3 hcr_a3

private theorem lookup_rlp_decode_fully_ws :
    originalRuntimeCode.lookup (ofString "rlp_decode_fully") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_decode_fully, .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 108 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_decode_fully) rfl

private theorem lookup_trie_lookup_ws :
    originalRuntimeCode.lookup (ofString "trie_lookup") =
      some ([(ofString "root", .one), (ofString "key_hash32", .one)],
        sourceFnBody Guest.Software.guestFn_trie_lookup, .comb [.one, .one, .one]) :=
  lookup_of_guestAst_getElem 267 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_trie_lookup) rfl

private theorem lookup_heap_mark_ws :
    originalRuntimeCode.lookup (ofString "heap_mark") =
      some ([], sourceFnBody Guest.Software.guestFn_heap_mark, .one) :=
  lookup_of_guestAst_getElem 8 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_heap_mark) rfl

private theorem lookup_ws_get_storage_ws :
    originalRuntimeCode.lookup (ofString "ws_get_storage") =
      some ((sourceFunctionEntry Guest.Software.guestFn_ws_get_storage).2) :=
  lookup_of_guestAst_getElem 369 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ws_get_storage) rfl

private theorem lookup_bswap64_ws :
    originalRuntimeCode.lookup (ofString "bswap64") =
      some ((sourceFunctionEntry Guest.Software.guestFn_bswap64).2) :=
  lookup_of_guestAst_getElem 23 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bswap64) rfl

private theorem ro_u256_from_be_ws : ReadOnlyFn (ofString "u256_from_be") := by
  change M17.ReadOnlyFn (ofString "u256_from_be")
  refine M17.readOnlyFn_of_guestAst_roProg 86 Guest.Software.guestFn_u256_from_be
    (fun f => f == ofString "bswap64") ?_ (by rw [guestAst_len]; decide) rfl (by decide)
  intro fname hgood values body callee rs hfound
  simp only [beq_iff_eq] at hgood
  subst hgood
  rw [M17.body_eq_of_lookupCode lookup_bswap64_ws hfound]
  decide

private theorem progWStep_mark_alloc_keccak_lookup_release_ws {cont : ProgHOL 64}
    (hCont : ProgWStep idxBufs ["heap_ptr", "scratch_ptr"] cont) :
    ProgWStep idxBufs ["heap_ptr", "scratch_ptr"]
      (.decCall (ofString "mark") .one (ofString "heap_mark") []
        (.decCall (ofString "h") .one (ofString "alloc") [.const 32#64]
          (.seq
            (.call (some (none, none)) (ofString "keccak256")
              [.var .local (ofString "key"), .const 32#64, .var .local (ofString "h")])
            (.decCall (ofString "r") (.comb [.one, .one, .one]) (ofString "trie_lookup")
              [.var .local (ofString "node"), .var .local (ofString "h")]
              (.seq
                (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
                cont))))) := by
  have hB := validBufList_idxBufs
  have hgw := safeStepGlobals_hp_sp
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  intro F s hc hW hnt hfr
  have hAs : ArenaOK s := hW.1.2
  have heff0 : WorldEff s s [] wsBufs wsGw := WorldEff.refl s [] wsBufs wsGw hW.1 hc
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  have hargs_hm : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [] = some [] := rfl
  have hl_hm : lookupCodeHOLFinite s.code.lookup (ofString "heap_mark") [] =
      some (sourceFnBody Guest.Software.guestFn_heap_mark, HolFiniteMapExact.empty, .one) := by
    rw [hc]
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite
    have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "heap_mark") [] =
        some (sourceFnBody Guest.Software.guestFn_heap_mark, FEMPTY, .one) := by
      simp only [lookupCodeHOLExact, lookup_heap_mark_ws, List.length_nil, List.zip_nil_left, List.all_nil]
      rfl
    split
    · rename_i hnone; rw [hraw] at hnone; cases hnone
    · rename_i b' l' r' hsome
      have heq := Option.some.inj (hsome.symm.trans hraw)
      obtain ⟨rfl, hrest⟩ := Prod.mk.inj heq
      obtain ⟨hl_eq, rfl⟩ := Prod.mk.inj hrest
      refine congrArg some (Prod.ext rfl (Prod.ext ?_ rfl))
      apply HolFiniteMapExact.ext; funext k
      simp [HolFiniteMapExact.empty, hl_eq]; rfl
  simp only [hargs_hm, hl_hm] at hnt hfr ⊢
  by_cases hz0 : s.clock = 0
  · simp [hz0] at hnt
  · rw [if_neg hz0] at hnt hfr ⊢
    obtain ⟨hpm, hhpm_lk⟩ : ∃ hpm : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word hpm)) :=
      globalWord_of_globN_pos s "heap_ptr" (by have := hAs.1; rw [sourceBase_val] at this; omega)
    have hhm_run : evaluateHOLFiniteState (callEntryStateHOLFinite s HolFiniteMapExact.empty)
        (sourceFnBody Guest.Software.guestFn_heap_mark) =
        (some (.returned (.val (.word hpm))), emptyLocalsHOLFinite (callEntryStateHOLFinite s HolFiniteMapExact.empty)) := by
      have hbhm : sourceFnBody Guest.Software.guestFn_heap_mark = .return (.var .global (ofString "heap_ptr")) := rfl
      rw [hbhm, evaluateHOLFiniteState_return]
      have hg_hp : (callEntryStateHOLFinite s HolFiniteMapExact.empty).globals.lookup (ofString "heap_ptr") =
          some (.val (.word hpm)) := hhpm_lk
      simp [evalHOLExact, hg_hp, shapeOfHOLExact]
    simp only [hhm_run] at hnt hfr ⊢
    have hsh_hpm : (shapeEqHOL (shapeOfHOLExact (.val (.word hpm) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word hpm) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hsh_hpm, ↓reduceIte] at hnt hfr ⊢
    set m1 := setVarHOLFinite (ofString "mark") (.val (.word hpm))
      { (emptyLocalsHOLFinite (callEntryStateHOLFinite s HolFiniteMapExact.empty)) with locals := s.locals }
    have hm1_eq : m1 = { s with locals := s.locals.update (ofString "mark", .val (.word hpm)), clock := s.clock - 1 } := rfl
    have hhpm_glob : hpm.toNat = globN s "heap_ptr" := by simp [globN, hhpm_lk]
    have hhpm_al : hpm.toNat % 8 = 0 := by rw [hhpm_glob]; exact hAs.2.2.2.2.2.1
    have hhpm_lo : globN s "heap_ptr" ≤ hpm.toNat := by omega
    have hhpm_hi : hpm.toNat ≤ heapLimit := by rw [hhpm_glob]; exact hAs.2.1
    have heff_m1 : WorldEff s m1 [] idxBufs ["heap_ptr", "scratch_ptr"] := by
      rw [hm1_eq]; exact (WorldEff.refl s [] idxBufs ["heap_ptr", "scratch_ptr"] hW.1 hc).locals_clock _ _
    have hm1_W : WorldOK m1 := by rw [hm1_eq]; exact localsFree_worldOK s _ _ hW
    have hm1_mark : m1.locals.lookup (ofString "mark") = some (.val (.word hpm)) := by
      rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    -- Now step `decCall "h" .one "alloc" [32] ...` from `m1`
    suffices hstep_m1 : WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra m1
        (evaluateHOLFiniteState m1
          (.decCall (ofString "h") .one (ofString "alloc") [.const 32#64]
            (.seq
              (.call (some (none, none)) (ofString "keccak256")
                [.var .local (ofString "key"), .const 32#64, .var .local (ofString "h")])
              (.decCall (ofString "r") (.comb [.one, .one, .one]) (ofString "trie_lookup")
                [.var .local (ofString "node"), .var .local (ofString "h")]
                (.seq
                  (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
                  cont))))).1
        (evaluateHOLFiniteState m1
          (.decCall (ofString "h") .one (ofString "alloc") [.const 32#64]
            (.seq
              (.call (some (none, none)) (ofString "keccak256")
                [.var .local (ofString "key"), .const 32#64, .var .local (ofString "h")])
              (.decCall (ofString "r") (.comb [.one, .one, .one]) (ofString "trie_lookup")
                [.var .local (ofString "node"), .var .local (ofString "h")]
                (.seq
                  (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
                  cont))))).2 by
      exact (WorldStepSc.of_pre_locals_clock (s := s) hstep_m1).with_locals_clock _ _
    -- Prove `WorldEff m1 m5` across `alloc` + `keccak256` + `trie_lookup` + `heap_release`, then `hCont`!
    -- Wait: `r` is bound in `decCall "r" ... (.seq (heap_release) cont)`, so `cont` uses `r`!
    -- Let's step `alloc` + `keccak256` + `decCall "r"` explicitly, then `seq (heap_release) cont`.
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
    have hargs_al : evalListHOLFinite m1 (h := fun a => Classical.propDecidable (m1.memaddrs a)) [.const 32#64] =
        some [.val (.word 32#64)] := rfl
    simp only [hargs_al] at hnt hfr ⊢
    rcases hl_al : lookupCodeHOLFinite m1.code.lookup (ofString "alloc") [.val (.word 32#64)] with
      _ | ⟨body_a, callee_a, ret_a⟩
    · simp [hl_al] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl_al] at hnt hfr ⊢
      by_cases hz1 : m1.clock = 0
      · simp [hz1] at hnt
      · rw [if_neg hz1] at hnt hfr ⊢
        have hm1_code : m1.code = originalRuntimeCode := heff_m1.code
        have hsame_a := lookupCodeHOLFinite_installed_body m1.code.lookup (ofString "alloc") _ _ body_a
          _ ret_a [.val (.word 32#64)] callee_a (by rw [hm1_code]; exact lookup_alloc) hl_al
        subst hsame_a
        have hret_a := lookupCodeHOLFinite_installed_return m1 (ofString "alloc") _ _ _
          _ ret_a [.val (.word 32#64)] callee_a (by rw [hm1_code]; exact lookup_alloc) hl_al
        subst hret_a
        obtain ⟨nw, hnw_eq, hnw_callee⟩ := Fast_C08WkShard03.lookupCode_one_word lookup_alloc
          (by rw [← hm1_code]; exact hl_al)
        injection hnw_eq with hnw_eq'; injection hnw_eq' with hnw_eq'; injection hnw_eq' with hnw_eq'; subst hnw_eq'
        have hm1_hp_lk : m1.globals.lookup (ofString "heap_ptr") = some (.val (.word hpm)) := by
          rw [hm1_eq]; exact hhpm_lk
        let ent_a := callEntryStateHOLFinite m1 callee_a
        rcases hrun_a : evaluateHOLFiniteState ent_a (sourceFnBody Guest.Software.guestFn_alloc) with ⟨res_a, pa⟩
        dsimp only [ent_a] at hrun_a
        simp only [hrun_a] at hnt hfr ⊢
        have hcr_outer1 := contOrRes_of_flowingOrResumes hfr
        have hres_al : Resumes res_a := by
          cases res_a with
          | none => rcases hcr_outer1 with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
          | some r1 =>
            cases r1 with
            | returned rv => exact Or.inl ⟨rv, rfl⟩
            | exception eid ev =>
              rcases hcr_outer1 with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨e', v', hc0, hne⟩⟩ <;> try simp at hc0
              obtain ⟨he1, he2⟩ := hc0
              subst he1 he2
              exact Or.inr ⟨eid, ev, rfl, hne⟩
            | timeOut => simp at hnt
            | _ => rcases hcr_outer1 with hc0 | hc0 | hc0 | ⟨⟨_, hc0⟩ | ⟨_, _, hc0, _⟩⟩ <;> simp at hc0
        have hal := InitECandidate.Solver.Wave8GuestInv.R13.alloc_body_resumes ent_a hpm hm1_code hm1_hp_lk
          (by dsimp only [ent_a]; rw [hrun_a]; exact hres_al)
        dsimp only [ent_a] at hal; rw [hrun_a] at hal
        obtain ⟨nw', hnw'_lk, hrv_eq, hcmp1, hcmp2, hpa_eq⟩ := hal
        have hnw_eq2 : (32#64 : BitVec 64) = nw' := by
          have : ent_a.locals.lookup (ofString "n") = some (.val (.word 32#64)) := hnw_callee
          rw [this] at hnw'_lk; injection hnw'_lk with h'; injection h' with h'; injection h'
        subst hnw_eq2
        dsimp only at hrv_eq hpa_eq; subst hrv_eq
        dsimp only at hnt hfr ⊢
        have hsh_a : (shapeEqHOL (shapeOfHOLExact (.val (.word hpm))) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word hpm))) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh_a] at hnt hfr ⊢
        dsimp only at hnt hfr ⊢
        set m2 := setVarHOLFinite (ofString "h") (.val (.word hpm)) { pa with locals := m1.locals }
        have hm2_next : m2 = { m1 with
            globals := m1.globals.update (ofString "heap_ptr", .val (.word ((hpm + (32#64 + 7)) &&& ((0 : BitVec 64) - 8)))),
            locals := m2.locals, clock := m2.clock } := by
          dsimp only [m2, setVarHOLFinite]; rw [hpa_eq]; rfl
        have heff_m1_self : WorldEff m1 m1 [] idxBufs ["heap_ptr", "scratch_ptr"] :=
          WorldEff.refl m1 [] idxBufs ["heap_ptr", "scratch_ptr"] hm1_W.1 hm1_code
        obtain ⟨heff_m2, _, _, _, hp_lo_m1, hp_add_m2, hp_hi_m2, _⟩ :=
          worldEff_alloc_step heff_m1_self (by decide) hm1_hp_lk hcmp1 hcmp2 hm2_next
        have hwh_hi : hpm.toNat + 32 ≤ heapLimit := by
          change hpm.toNat + (32 + 7) / 8 * 8 = globN m2 "heap_ptr" at hp_add_m2; omega
        have hm2_mark : m2.locals.lookup (ofString "mark") = some (.val (.word hpm)) := by
          dsimp only [m2, setVarHOLFinite]
          simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_mark, show ofString "h" ≠ ofString "mark" by decide]
        have hm2_h : m2.locals.lookup (ofString "h") = some (.val (.word hpm)) := by
          dsimp only [m2, setVarHOLFinite]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        have hkpad_m2 : Fast_C08WkShard03.globMapN m2.globals "keccak_pad" = globN m1 "keccak_pad" :=
          globN_eq_of_lookup (heff_m2.gw_kept (ofString "keccak_pad") (by decide))
        have hkst_m2 : Fast_C08WkShard03.globMapN m2.globals "keccak_st" = globN m1 "keccak_st" :=
          globN_eq_of_lookup (heff_m2.gw_kept (ofString "keccak_st") (by decide))
        -- Step `seq (keccak256) (decCall "r" ...)` from `m2`, keeping anchor `m1`
        suffices hstep_m2 : WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra m1
            (evaluateHOLFiniteState m2
              (.seq
                (.call (some (none, none)) (ofString "keccak256")
                  [.var .local (ofString "key"), .const 32#64, .var .local (ofString "h")])
                (.decCall (ofString "r") (.comb [.one, .one, .one]) (ofString "trie_lookup")
                  [.var .local (ofString "node"), .var .local (ofString "h")]
                  (.seq
                    (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
                    cont)))).1
            (evaluateHOLFiniteState m2
              (.seq
                (.call (some (none, none)) (ofString "keccak256")
                  [.var .local (ofString "key"), .const 32#64, .var .local (ofString "h")])
                (.decCall (ofString "r") (.comb [.one, .one, .one]) (ofString "trie_lookup")
                  [.var .local (ofString "node"), .var .local (ofString "h")]
                  (.seq
                    (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
                    cont)))).2 by
          exact hstep_m2.with_locals_clock _ _
        refine progWStep_seq_worldEff_from hm1_W
          (fun hnt_k hcr_k =>
            worldEff_call0_funByteEff_local heff_m2 Fast_C08WkShard03.funByteEff_keccak256 _
              [bufferRegion m1 ("keccak_st", 200), bufferRegion m1 ("keccak_pad", 136), (hpm.toNat, 32)]
              (fun vals hargs i hi hpos => by
                rw [evalListHOLFinite_eq_toExact] at hargs
                simp only [evalListHOLExact] at hargs
                rcases hk0 : m2.locals.lookup (ofString "key") with _ | vk0
                · simp [evalHOLExact, toExact, hk0] at hargs
                · simp only [evalHOLExact, toExact, hk0, hm2_h] at hargs
                  injection hargs with hargs_eq; subst hargs_eq
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with rfl | rfl | rfl
                  · refine ⟨bufferRegion m1 ("keccak_st", 200), List.mem_cons_self, ?_, ?_⟩ <;>
                      simp [Fast_C08WkShard03.globBufIvl, bufferRegion, hkst_m2] at hpos ⊢
                  · refine ⟨bufferRegion m1 ("keccak_pad", 136), List.mem_cons_of_mem _ List.mem_cons_self, ?_, ?_⟩ <;>
                      simp [Fast_C08WkShard03.globBufIvl, bufferRegion, hkpad_m2] at hpos ⊢
                  · refine ⟨(hpm.toNat, 32), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_, ?_⟩ <;>
                      simp [Fast_C08WkShard03.valWordNat])
              (fun iv hiv _ => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv
                rcases hiv with rfl | rfl | rfl
                · exact Or.inr (Or.inl ⟨("keccak_st", 200), by decide, le_rfl, le_rfl⟩)
                · exact Or.inr (Or.inl ⟨("keccak_pad", 136), by decide, le_rfl, le_rfl⟩)
                · exact Or.inr (Or.inr (Or.inr ⟨hp_lo_m1, hwh_hi⟩)))
              hnt_k hcr_k)
          (fun m3 hm3 hm3_code hW_m3 heff_m3 hnt3 hfr3 => ?_) hnt hfr
        have hm3_loc : m3.locals = m2.locals := by
          have := call0_none_locals_local m2 (ofString "keccak256") _ (by rw [hm3])
          rwa [hm3] at this
        have hm3_mark : m3.locals.lookup (ofString "mark") = some (.val (.word hpm)) := by
          rw [hm3_loc]; exact hm2_mark
        -- Step `decCall "r" (.comb [.one, .one, .one]) "trie_lookup" ...` from `m3`
        rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt3 hfr3 ⊢
        rcases hargs_tl : @evalListHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a))
            [.var .local (ofString "node"), .var .local (ofString "h")] with _ | vals_tl
        · simp [evalListHOLFinite, hargs_tl] at hfr3; exact absurd hfr3 not_flowingOrResumes_error
        · simp only [evalListHOLFinite, hargs_tl] at hnt3 hfr3 ⊢
          rcases hl_tl : lookupCodeHOLFinite m3.code.lookup (ofString "trie_lookup") vals_tl with
            _ | ⟨body_tl, callee_tl, ret_tl⟩
          · simp [hl_tl] at hfr3; exact absurd hfr3 not_flowingOrResumes_error
          · simp only [hl_tl] at hnt3 hfr3 ⊢
            have hsame_tl := lookupCodeHOLFinite_installed_body m3.code.lookup (ofString "trie_lookup") _ _ body_tl
              _ ret_tl vals_tl callee_tl (by rw [hm3_code]; exact lookup_trie_lookup_ws) hl_tl
            subst hsame_tl
            have hret_tl := lookupCodeHOLFinite_installed_return m3 (ofString "trie_lookup") _ _ _
              _ ret_tl vals_tl callee_tl (by rw [hm3_code]; exact lookup_trie_lookup_ws) hl_tl
            subst hret_tl
            by_cases hz3 : m3.clock = 0
            · simp [hz3] at hnt3
            · rw [if_neg hz3] at hnt3 hfr3 ⊢
              let ent_tl := callEntryStateHOLFinite m3 callee_tl
              rcases hrun_tl : evaluateHOLFiniteState ent_tl (sourceFnBody Guest.Software.guestFn_trie_lookup) with ⟨res_tl, cpost_tl⟩
              dsimp only [ent_tl] at hrun_tl
              simp only [hrun_tl] at hnt3 hfr3 ⊢
              have hnt_tl : (evaluateHOLFiniteState ent_tl (sourceFnBody Guest.Software.guestFn_trie_lookup)).1 ≠ some .timeOut := by
                dsimp only [ent_tl]; rw [hrun_tl]; rintro rfl; simp at hnt3
              have heff_ent_ws : WorldEff m3 ent_tl [] wsBufs wsGw :=
                (WorldEff.refl m3 [] wsBufs wsGw hW_m3.1 hm3_code).locals_clock _ _
              cases res_tl with
              | none => exact absurd hfr3 not_flowingOrResumes_error
              | some cr_tl =>
                cases cr_tl with
                | timeOut => simp at hnt3
                | error | «break» | «continue» => exact absurd hfr3 not_flowingOrResumes_error
                | finalFfi _ => exact absurd hfr3 not_flowingOrResumes_finalFfi
                | exception eid ev =>
                  dsimp only at hfr3 ⊢
                  have hres_ex : Resumes (some (.exception eid ev)) := by
                    rcases hfr3 with h | h | h | hr <;> try simp at h
                    exact hr
                  have heff_tl := (worldEff_trie_lookup m3 ent_tl heff_ent_ws hnt_tl
                    (by dsimp only [ent_tl]; rw [hrun_tl]; exact hres_ex)).mono (R2 := []) (B2 := idxBufs)
                    (fun _ h => by cases h) (by intro p hp; simp [wsBufs, idxBufs] at hp ⊢; exact Or.inr hp) (fun _ h => h)
                  dsimp only [ent_tl] at heff_tl; rw [hrun_tl] at heff_tl; dsimp only at heff_tl
                  have heff_tot : WorldEff m1 cpost_tl.emptyLocalsHOLFinite [] idxBufs ["heap_ptr", "scratch_ptr"] :=
                    (heff_m3.trans_noBuf heff_tl (by decide) (by decide)).locals_clock _ _
                  exact worldEff_to_worldStepSc_idx hm1_W heff_tot
                | returned rv_tl =>
                  dsimp only at hnt3 hfr3 ⊢
                  by_cases hsh_tl : (shapeEqHOL (shapeOfHOLExact rv_tl) (.comb [.one, .one, .one]) &&
                      shapeEqHOL (shapeOfHOLExact rv_tl) (.comb [.one, .one, .one])) = true
                  · simp only [hsh_tl, ↓reduceIte] at hnt3 hfr3 ⊢
                    have heff_tl := (worldEff_trie_lookup m3 ent_tl heff_ent_ws hnt_tl
                      (by dsimp only [ent_tl]; rw [hrun_tl]; exact Or.inl ⟨rv_tl, rfl⟩)).mono (R2 := []) (B2 := idxBufs)
                      (fun _ h => by cases h) (by intro p hp; simp [wsBufs, idxBufs] at hp ⊢; exact Or.inr hp) (fun _ h => h)
                    dsimp only [ent_tl] at heff_tl; rw [hrun_tl] at heff_tl; dsimp only at heff_tl
                    set m4 := setVarHOLFinite (ofString "r") rv_tl { cpost_tl with locals := m3.locals }
                    have heff_m4 : WorldEff m1 m4 [] idxBufs ["heap_ptr", "scratch_ptr"] :=
                      ((heff_m3.trans_noBuf heff_tl (by decide) (by decide)).locals_clock m3.locals cpost_tl.clock).locals_clock _ _
                    have hm4_mark : m4.locals.lookup (ofString "mark") = some (.val (.word hpm)) := by
                      dsimp only [m4, setVarHOLFinite]
                      simp [HolFiniteMapExact.lookup_update, FUPDATE, hm3_mark,
                        show ofString "r" ≠ ofString "mark" by decide]
                    -- Now step `seq (heap_release mark) cont` from `m4`!
                    suffices hstep_m4 : WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra m1
                        (evaluateHOLFiniteState m4
                          (.seq
                            (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
                            cont)).1
                        (evaluateHOLFiniteState m4
                          (.seq
                            (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
                            cont)).2 by
                      exact hstep_m4.with_locals_clock _ _
                    have hm1_hp_lo : globN m1 "heap_ptr" ≤ hpm.toNat := by
                      rw [hm1_eq]; exact hhpm_lo
                    refine progWStep_seq_worldEff_from hm1_W
                      (fun hnt_hr _ =>
                        (worldEff_call0_heap_release hm1_W.1.2 heff_m4 (by decide) (by decide)
                          (.var .local (ofString "mark")) hpm
                          (by simp [evalHOLExact, toExact, hm4_mark])
                          hm1_hp_lo hhpm_hi hhpm_al hnt_hr).2.choose_spec.2)
                      (fun m5 _ hm5_code hW_m5 heff_m5 hnt5 hfr5 => ?_) hnt3 hfr3
                    have hs15 : WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra m1 none m5 :=
                      worldEff_to_worldStepSc_idx hm1_W heff_m5
                    exact WorldStepSc.trans hB hgw hs15 (hCont m5 hm5_code hW_m5 hnt5 hfr5)
                  · rw [if_neg hsh_tl] at hfr3; exact absurd hfr3 not_flowingOrResumes_error

private theorem wkSc_rlp_decode_fully :
    WorldKeepsSc WorldOK (bufRegions wsBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      (ofString "rlp_decode_fully") := by
  refine ⟨_, _, _, lookup_rlp_decode_fully_ws, fun s hc hW hex hnt hres => ?_⟩
  obtain ⟨vals, hl⟩ := hex
  have heff := worldEff_rlp_decode_fully s vals hc hW.1 hl hnt hres
  have heff' : WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_decode_fully)).2
      (bufRegions wsBufs s) wsBufs wsGw :=
    heff.mono (fun _ hiv => by cases hiv) (fun _ h => h) (fun _ h => h)
  exact ⟨heff'.to_worldStep_Q hW (by decide) (by decide) (fun _ _ _ _ _ _ _ _ => trivial), heff.sp_hi⟩

theorem wkSc_ws_get_storage_of_ws_storage_trie
    (htrie : WorldKeepsSc WorldOK (bufRegions idxBufs)
      ["heap_ptr", "scratch_ptr"] stdKeep NoExtra (ofString "ws_storage_trie")) :
    WorldKeepsSc WorldOK (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      (ofString "ws_get_storage") := by
  have hB := validBufList_idxBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsSc_of_progWStep lookup_ws_get_storage_ws ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_ws_get_storage,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_decCall hB hgw
    (by intro p hp; simp [wsAcctBufs, idxBufs] at hp ⊢; exact Or.inr hp)
    (fun _ h => h)
    wkSc_ws_storage_root_of ?_
  refine progWStep_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsSc_of_readOnly EvmFrameSpecs.ro_memeq) ?_
  refine progWStep_seq hB hgw
    (progWStep_ite (progWStep_return _ _ _) (progWStep_skip _ _)) ?_
  refine progWStep_decCall hB hgw (fun _ h => h) (fun _ h => h)
    htrie ?_
  refine progWStep_mark_alloc_keccak_lookup_release_ws ?_
  refine progWStep_seq hB hgw
    (progWStep_ite (progWStep_return _ _ _) (progWStep_skip _ _)) ?_
  refine progWStep_decCall hB hgw
    (by intro p hp; simp [wsBufs, idxBufs] at hp ⊢; exact Or.inr hp)
    (fun _ h => h)
    wkSc_rlp_decode_fully ?_
  refine progWStep_seq hB hgw
    (progWStep_ite (progWStep_return _ _ _) (progWStep_skip _ _)) ?_
  refine progWStep_seq hB hgw
    (progWStep_ite (progWStep_raise _ _ _ _) (progWStep_skip _ _)) ?_
  exact progWStep_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsSc_of_readOnly ro_u256_from_be_ws)
    (progWStep_return _ _ _)

private theorem progWStep_decCall_keep_kb_shaped {x : MlS} {sh : ShapeHOL} {fname : MlS}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64} {B1 : BufList} {gw1 : List String}
    (hx_ne : x ≠ ofString "kb")
    (hB : ∀ p ∈ B1, p ∈ idxBufs)
    (hgw : ∀ g ∈ gw1, g ∈ ["heap_ptr", "scratch_ptr"])
    (hf : WorldKeepsSc WorldOK (bufRegions B1) gw1 stdKeep NoExtra fname)
    (hcont : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      s.code = originalRuntimeCode → WorldOK s →
      s.locals.lookup (ofString "kb") = s.globals.lookup (ofString "bal_key_buf") →
      s.locals.lookup x = some v →
      shapeEqHOL (shapeOfHOLExact v) sh = true →
      (evaluateHOLFiniteState s cont).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState s cont).1 →
      WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
        s (evaluateHOLFiniteState s cont).1 (evaluateHOLFiniteState s cont).2) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → WorldOK s →
      s.locals.lookup (ofString "kb") = s.globals.lookup (ofString "bal_key_buf") →
      (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1 ≠ some .timeOut →
      FlowingOrResumes (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1 →
      WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
        s (evaluateHOLFiniteState s (.decCall x sh fname args cont)).1
        (evaluateHOLFiniteState s (.decCall x sh fname args cont)).2 := by
  intro F s hc hW hkb hnt hfr
  have hBvalid := validBufList_idxBufs
  have hgwSafe := safeStepGlobals_hp_sp
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        let ent := callEntryStateHOLFinite s callee
        have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hW
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata ent body').1
        rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
        simp only [ent] at hrun hmeta
        simp only [hrun] at hmeta hnt hfr ⊢
        have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
          simp only [ent, hrun]; rintro rfl; simp at hnt
        cases res with
        | none => exact absurd hfr not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh && shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hsh1 : shapeEqHOL (shapeOfHOLExact v) sh = true := (Bool.and_eq_true _ _ ▸ hsh).1
              have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
              simp only [ent, hrun] at hspec
              have hstep1 := (hspec (Or.inl ⟨v, rfl⟩)).mono_bufs hB hgw
              set s1 := setVarHOLFinite x v { cpost with locals := s.locals }
              have hs1_step : WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra s none s1 :=
                hstep1.from_entry
              have hWs1 : WorldOK s1 := hs1_step.worldOK_bufs hBvalid hW
              have hs1_code : s1.code = originalRuntimeCode := hmeta.trans hc
              have hg_keep : s1.globals.lookup (ofString "bal_key_buf") = s.globals.lookup (ofString "bal_key_buf") :=
                (hs1_step.1.2.2.1 (ofString "bal_key_buf") (by decide)).symm
              have hs1_kb : s1.locals.lookup (ofString "kb") = s1.globals.lookup (ofString "bal_key_buf") := by
                rw [hg_keep]
                simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hx_ne, hkb]
              have hs1_x : s1.locals.lookup x = some v := by
                simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              have hstep2 := hcont s1 v hs1_code hWs1 hs1_kb hs1_x hsh1 hnt hfr
              have hstep2' := hstep2.with_locals_clock (r' := (evaluateHOLFiniteState s1 cont).1)
                (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s1 cont).2.locals (x, s.locals.lookup x))
                (evaluateHOLFiniteState s1 cont).2.clock
              exact WorldStepSc.trans hBvalid hgwSafe hs1_step hstep2'
            · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error
          | exception eid ev =>
            dsimp only at hfr ⊢
            have hres_ex : Resumes (some (.exception eid ev)) := by
              rcases hfr with h | h | h | hr <;> try simp at h
              exact hr
            have hspec := FunSpec.at_lookup hf s hc vs body' callee ret' hl hWent hnt_c
            simp only [ent, hrun] at hspec
            have hstep := (hspec hres_ex).mono_bufs hB hgw
            exact hstep.from_entry

theorem wkSc_get_pre_tx_storage_of_ws_get_storage
    (hstorage : WorldKeepsSc WorldOK (bufRegions idxBufs)
      ["heap_ptr", "scratch_ptr"] stdKeep NoExtra (ofString "ws_get_storage")) :
    WorldKeepsSc WorldOK (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      (ofString "get_pre_tx_storage") := by
  have hB := validBufList_idxBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsSc_of_progWStep lookup_get_pre_tx_storage ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_get_pre_tx_storage,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsSc_of_readOnly M17.ro_stor_lookup) ?_
  refine progWStep_seq hB hgw
    (progWStep_ite (progWStep_return _ _ _) (progWStep_skip _ _)) ?_
  refine progWStep_seq hB hgw
    (progWStep_call0 (by intro p hp; cases hp)
      (by intro g hg; simp only [List.mem_singleton] at hg; subst g; simp)
      wkSc_record_pre_state_read) ?_
  exact progWStep_decCall hB hgw (fun _ h => h) (fun _ h => h)
    hstorage (progWStep_return _ _ _)

theorem wkSc_idx_start_storage_of_ws_storage_trie
    (htrie : WorldKeepsSc WorldOK (bufRegions idxBufs)
      ["heap_ptr", "scratch_ptr"] stdKeep NoExtra (ofString "ws_storage_trie")) :
    WorldKeepsSc WorldOK (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      (ofString "idx_start_storage") := by
  have hB := validBufList_idxBufs
  have hgw := safeStepGlobals_hp_sp
  have hpre := wkSc_get_pre_tx_storage_of_ws_get_storage
    (wkSc_ws_get_storage_of_ws_storage_trie htrie)
  refine worldKeepsSc_of_progWStep lookup_idx_start_storage ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_idx_start_storage,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_dec_kb (fun s hc hW hkb hnt hfr => ?_)
  have hre1 : ∀ (a b c d : ProgHOL 64),
      evaluateHOLFiniteState s (.seq a (.seq b (.seq c d))) =
        evaluateHOLFiniteState s (.seq (.seq a (.seq b c)) d) := by
    intro a b c d
    simp only [evaluateHOLFiniteState_seq_line780]
    rcases evaluateHOLFiniteState s a with ⟨ra, ma⟩
    cases ra
    · rcases evaluateHOLFiniteState ma b with ⟨rb, mb⟩
      cases rb <;> rfl
    · rfl
  rw [hre1] at hnt hfr ⊢
  refine progWStep_seq_worldEff_idx hc hW
    (fun hnt1 hcr1 =>
      worldEff_kb_st_memcpy20_32 hW (WorldEff.refl s [] idxBufs ["heap_ptr", "scratch_ptr"] hW.1 hc) hkb hnt1 hcr1)
    (fun s1 hs1 hc1 hW1 heff1 hnt1 hcr1 => ?_) hnt hfr
  have hs1_loc : s1.locals = s.locals := by
    have hk := locals_eq_of_avoidsLocal s _ (fun _ => rfl) (by rw [hs1])
    rwa [hs1] at hk
  have hs1_kb : s1.locals.lookup (ofString "kb") = s1.globals.lookup (ofString "bal_key_buf") := by
    rw [hs1_loc, hkb, heff1.gw_kept (ofString "bal_key_buf") (by decide)]
  refine progWStep_decCall_keep_kb (by decide)
    (by intro _ hp; cases hp) (by intro _ hg; cases hg)
    (worldKeepsSc_of_readOnly EvmFrameSpecs.ro_htab_get)
    (fun s2 hc2 hW2 hkb2 hnt2 hfr2 => ?_) s1 hc1 hW1 hs1_kb hnt1 hcr1
  have hite : ProgWStep idxBufs ["heap_ptr", "scratch_ptr"]
      (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
        (.return (.load (.comb [.one, .one, .one, .one]) (.rfield 1 (.var .local (ofString "m")))))
        .skip) :=
    progWStep_ite (progWStep_return _ _ _) (progWStep_skip _ _)
  rw [evaluateHOLFiniteState_seq_line780] at hnt2 hfr2 ⊢
  rcases hri : evaluateHOLFiniteState s2
      (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
        (.return (.load (.comb [.one, .one, .one, .one]) (.rfield 1 (.var .local (ofString "m")))))
        .skip) with ⟨ri, s3⟩
  simp only [hri] at hnt2 hfr2 ⊢
  cases ri with
  | some r =>
    have hsi := hite s2 hc2 hW2 (by rw [hri]; exact hnt2) (by rw [hri]; exact hfr2)
    rwa [hri] at hsi
  | none =>
    have hsi := hite s2 hc2 hW2 (by rw [hri]; simp) (by rw [hri]; exact Or.inl rfl)
    rw [hri] at hsi; dsimp only at hsi
    have hW3 : WorldOK s3 := hsi.worldOK_bufs hB hW2
    have hc3 : s3.code = originalRuntimeCode :=
      ((PanRunBounded.evaluateHOLFiniteState_metadata s2 _).1.trans hc2 |> fun h => by rwa [hri] at h)
    have hs3_loc : s3.locals = s2.locals := by
      have hk := locals_eq_of_avoidsLocal s2 _ (fun _ => rfl) (by rw [hri])
      rwa [hri] at hk
    have hs3_kb : s3.locals.lookup (ofString "kb") = s3.globals.lookup (ofString "bal_key_buf") := by
      rw [hs3_loc, hkb2, (hsi.1.2.2.1 (ofString "bal_key_buf") (by decide)).symm]
    refine WorldStepSc.trans hB hgw hsi ?_
    refine progWStep_decCall_keep_kb_shaped (by decide)
      (fun _ h => h) (fun _ h => h)
      hpre
      (fun s4 vv hc4 hW4 hkb4 hv_lk hv_sh hnt4 hfr4 => ?_) s3 hc3 hW3 hs3_kb hnt2 hfr2
    have hv_sh_sym : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vv) = true := by
      rcases vv with _ | fs | _
      · simp [shapeOfHOLExact, shapeEqHOL] at hv_sh
      · rcases fs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩⟩ <;>
          try (simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hv_sh)
        rcases v0 with ⟨⟨a⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨b⟩⟩ | _ | _ <;>
          rcases v2 with ⟨⟨c⟩⟩ | _ | _ <;> rcases v3 with ⟨⟨d⟩⟩ | _ | _ <;>
          simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at hv_sh ⊢
      · simp [shapeOfHOLExact, shapeEqHOL] at hv_sh
    have hv_len : (flattenHOL vv).length = 4 := flattenHOL_shape_u256_local hv_sh_sym
    refine progWStep_decCall_alloc_idx hc4 hW4
      (fun pw m1 hm1_code hW_m1 hm1_loc hm1_g heff_m1 hp_lo hp_add hp_hi hnt_m1 hfr_m1 => ?_) hnt4 hfr4
    have hp_hi32 : pw.toNat + 32 ≤ heapLimit := by
      change pw.toNat + (32 + 7) / 8 * 8 = globN m1 "heap_ptr" at hp_add
      omega
    have hm1_rec : m1.locals.lookup (ofString "rec") = some (.val (.word pw)) := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hm1_v : m1.locals.lookup (ofString "v") = some vv := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hv_lk,
        show ofString "rec" ≠ ofString "v" by decide]
    have hm1_kb : m1.locals.lookup (ofString "kb") = s4.globals.lookup (ofString "bal_key_buf") := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hkb4,
        show ofString "rec" ≠ ofString "kb" by decide]
    have hhl264 : heapLimit < 2 ^ 64 := by decide
    have hhl_he : heapLimit ≤ heapEnd := by decide
    refine progWStep_seq_worldEff_from hW4
      (fun _ _ =>
        worldEff_store_multi heff_m1 (.var .local (ofString "rec")) (.var .local (ofString "v")) 4 (by decide)
          (fun v hv => by
            simp [evalHOLExact, toExact, hm1_v] at hv
            subst hv
            exact hv_len)
          (fun x hx => by
            simp [evalHOLExact, toExact, hm1_rec] at hx
            subst hx
            exact ⟨by omega, Or.inr (Or.inr (Or.inr ⟨hp_lo, hp_hi32⟩))⟩))
      (fun m2 hm2 hm2_code hW_m2 heff_m2 hnt_m2 hfr_m2 => ?_) hnt_m1 hfr_m1
    have hm2_loc : m2.locals = m1.locals := by
      have hk := locals_eq_of_avoidsLocal m1 _ (fun _ => rfl) (by rw [hm2])
      rwa [hm2] at hk
    have hre2 : ∀ (a b c d : ProgHOL 64),
        evaluateHOLFiniteState m2 (.seq a (.seq b (.seq c d))) =
          evaluateHOLFiniteState m2 (.seq (.seq a (.seq b c)) d) := by
      intro a b c d
      simp only [evaluateHOLFiniteState_seq_line780]
      rcases evaluateHOLFiniteState m2 a with ⟨ra, ma⟩
      cases ra
      · rcases evaluateHOLFiniteState ma b with ⟨rb, mb⟩
        cases rb <;> rfl
      · rfl
    rw [hre2] at hnt_m2 hfr_m2 ⊢
    refine progWStep_seq_worldEff_from hW4
      (fun hnt_c hcr_c =>
        worldEff_kb_st_memcpy20_32 hW4 heff_m2 (by rw [hm2_loc]; exact hm1_kb) hnt_c hcr_c)
      (fun m3 hm3 hm3_code hW_m3 heff_m3 hnt_m3 hfr_m3 => ?_) hnt_m2 hfr_m2
    have hs43 : WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra s4 none m3 :=
      worldEff_to_worldStepSc_idx hW4 heff_m3
    have hp_end : ProgWStep idxBufs ["heap_ptr", "scratch_ptr"]
        (.seq
          (.call (some (none, none)) (ofString "htab_set")
            [.var .global (ofString "bal_idx_stor"), .var .local (ofString "kb"), .var .local (ofString "rec")])
          (.return (.var .local (ofString "v")))) :=
      progWStep_seq hB hgw
        (progWStep_call0_htab_set_global "bal_idx_stor" _ _ (by decide) @nonValueSlot_bal_idx_stor)
        (progWStep_return _ _ _)
    exact WorldStepSc.trans hB hgw hs43 (hp_end m3 hm3_code hW_m3 hnt_m3 hfr_m3)

theorem wk_idx_start_storage_of_ws_storage_trie
    (htrie : WorldKeepsSc WorldOK (bufRegions idxBufs)
      ["heap_ptr", "scratch_ptr"] stdKeep NoExtra (ofString "ws_storage_trie")) :
    WorldKeeps WorldOK
      (fun s => [(globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "idx_start_storage") :=
  (wkSc_idx_start_storage_of_ws_storage_trie htrie).to_worldKeeps

theorem wkSc_idx_start_account :
    WorldKeepsSc WorldOK (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      (ofString "idx_start_account") := by
  have hB := validBufList_idxBufs
  have hgw := safeStepGlobals_hp_sp
  refine worldKeepsSc_of_progWStep lookup_idx_start_account ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_idx_start_account,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_dec_kb (fun s hc hW hkb hnt hfr => ?_)
  -- Reassociate `seq st_le64 (seq memcpy rest)` -> `seq (seq st_le64 memcpy) rest`
  rw [seq_reassoc_eval] at hnt hfr ⊢
  refine progWStep_seq_worldEff_idx hc hW
    (fun hnt1 hcr1 =>
      worldEff_kb_st_memcpy20 hW (WorldEff.refl s [] idxBufs ["heap_ptr", "scratch_ptr"] hW.1 hc) hkb hnt1 hcr1)
    (fun s1 hs1 hc1 hW1 heff1 hnt1 hcr1 => ?_) hnt hfr
  have hs1_loc : s1.locals = s.locals := by
    have hk := locals_eq_of_avoidsLocal s _ (fun _ => rfl) (by rw [hs1])
    rwa [hs1] at hk
  have hs1_kb : s1.locals.lookup (ofString "kb") = s1.globals.lookup (ofString "bal_key_buf") := by
    rw [hs1_loc, hkb, heff1.gw_kept (ofString "bal_key_buf") (by decide)]
  -- `decCall "m" ... "htab_get" ...`
  refine progWStep_decCall_keep_kb (by decide)
    (by intro _ hp; cases hp) (by intro _ hg; cases hg)
    (worldKeepsSc_of_readOnly EvmFrameSpecs.ro_htab_get)
    (fun s2 hc2 hW2 hkb2 hnt2 hfr2 => ?_) s1 hc1 hW1 hs1_kb hnt1 hcr1
  -- `seq (ite ...) (decCall "pre" ...)`
  have hite : ProgWStep idxBufs ["heap_ptr", "scratch_ptr"]
      (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
        (.return (.rfield 1 (.var .local (ofString "m"))))
        .skip) :=
    progWStep_ite (progWStep_return _ _ _) (progWStep_skip _ _)
  -- Step `ite`: on `none`, `skip` preserves `locals` and `globals`!
  rw [evaluateHOLFiniteState_seq_line780] at hnt2 hfr2 ⊢
  rcases hri : evaluateHOLFiniteState s2
      (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
        (.return (.rfield 1 (.var .local (ofString "m"))))
        .skip) with ⟨ri, s3⟩
  simp only [hri] at hnt2 hfr2 ⊢
  cases ri with
  | some r =>
    have hsi := hite s2 hc2 hW2 (by rw [hri]; exact hnt2) (by rw [hri]; exact hfr2)
    rwa [hri] at hsi
  | none =>
    have hsi := hite s2 hc2 hW2 (by rw [hri]; simp) (by rw [hri]; exact Or.inl rfl)
    rw [hri] at hsi; dsimp only at hsi
    have hW3 : WorldOK s3 := hsi.worldOK_bufs hB hW2
    have hc3 : s3.code = originalRuntimeCode :=
      ((PanRunBounded.evaluateHOLFiniteState_metadata s2 _).1.trans hc2 |> fun h => by rwa [hri] at h)
    have hs3_loc : s3.locals = s2.locals := by
      have hk := locals_eq_of_avoidsLocal s2 _ (fun _ => rfl) (by rw [hri])
      rwa [hri] at hk
    have hs3_kb : s3.locals.lookup (ofString "kb") = s3.globals.lookup (ofString "bal_key_buf") := by
      rw [hs3_loc, hkb2, (hsi.1.2.2.1 (ofString "bal_key_buf") (by decide)).symm]
    refine WorldStepSc.trans hB hgw hsi ?_
    -- `decCall "pre" .one "get_pre_tx_account" ...`
    refine progWStep_decCall_keep_kb (by decide)
      (by intro p hp; simp [wsAcctBufs, idxBufs] at hp ⊢; exact Or.inr hp)
      (fun _ hg => hg)
      wkSc_get_pre_tx_account
      (fun s4 hc4 hW4 hkb4 hnt4 hfr4 => ?_) s3 hc3 hW3 hs3_kb hnt2 hfr2
    -- `decCall "rec" .one "alloc" [80] ...`
    refine progWStep_decCall_alloc_idx hc4 hW4
      (fun pw m1 hm1_code hW_m1 hm1_loc hm1_g heff_m1 hp_lo hp_add hp_hi hnt_m1 hfr_m1 => ?_) hnt4 hfr4
    have hp_hi80 : pw.toNat + 80 ≤ heapLimit := by
      change pw.toNat + (80 + 7) / 8 * 8 = globN m1 "heap_ptr" at hp_add
      omega
    have hm1_rec : m1.locals.lookup (ofString "rec") = some (.val (.word pw)) := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hm1_kb : m1.locals.lookup (ofString "kb") = s4.globals.lookup (ofString "bal_key_buf") := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hkb4,
        show ofString "rec" ≠ ofString "kb" by decide]
    -- Step 1 after alloc: `memzero(rec, 80)`
    refine progWStep_seq_worldEff_from hW4
      (fun hnt_c hcr_c => worldEff_memzero_alloc heff_m1 pw 80#64 hm1_rec hp_lo hp_hi80 hnt_c hcr_c)
      (fun m2 hm2 hm2_code hW_m2 heff_m2 hnt_m2 hfr_m2 => ?_) hnt_m1 hfr_m1
    have hm2_loc : m2.locals = m1.locals := by
      have hk := locals_eq_of_avoidsLocal m1 _ (fun _ => rfl) (by rw [hm2])
      rwa [hm2] at hk
    -- Step 2: `memcpy(rec + 48, empty_code_hash, 32)`
    refine progWStep_seq_worldEff_from hW4
      (fun hnt_c hcr_c => worldEff_memcpy_alloc_off heff_m2 pw 48#64 32#64 _
        (by rw [hm2_loc]; exact hm1_rec) hp_lo (by change pw.toNat + 48 + 32 ≤ heapLimit; omega) hnt_c hcr_c)
      (fun m3 hm3 hm3_code hW_m3 heff_m3 hnt_m3 hfr_m3 => ?_) hnt_m2 hfr_m2
    have hm3_loc : m3.locals = m1.locals := by
      have hk := locals_eq_of_avoidsLocal m2 _ (fun _ => rfl) (by rw [hm3])
      rw [hm3] at hk; exact hk.trans hm2_loc
    -- Step 3: `ite (pre != 1) (...) skip`
    refine progWStep_seq_worldEff_from hW4
      (fun hnt_c hcr_c => worldEff_ite_pre_rec heff_m3 pw (by rw [hm3_loc]; exact hm1_rec) hp_lo hp_hi80 hnt_c hcr_c)
      (fun m4 hm4 hm4_code hW_m4 heff_m4 hnt_m4 hfr_m4 => ?_) hnt_m3 hfr_m3
    have hm4_loc : m4.locals = m1.locals := by
      have hk := locals_eq_of_avoidsLocal m3 _ (fun _ => rfl) (by rw [hm4])
      rw [hm4] at hk; exact hk.trans hm3_loc
    -- Step 4+5: reassociate `seq st_le64 (seq memcpy (seq htab_set return))` -> `seq (seq st_le64 memcpy) (seq htab_set return)`
    rw [seq_reassoc_eval] at hnt_m4 hfr_m4 ⊢
    refine progWStep_seq_worldEff_from hW4
      (fun hnt_c hcr_c =>
        worldEff_kb_st_memcpy20 hW4 heff_m4 (by rw [hm4_loc]; exact hm1_kb) hnt_c hcr_c)
      (fun m5 hm5 hm5_code hW_m5 heff_m5 hnt_m5 hfr_m5 => ?_) hnt_m4 hfr_m4
    -- Now transition from `WorldEff s4 m5` to `WorldStepSc ... s4 none m5` + `WorldStepSc ... m5 ...`!
    have hs45 : WorldStepSc (bufRegions idxBufs) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra s4 none m5 :=
      worldEff_to_worldStepSc_idx hW4 heff_m5
    have hp_end : ProgWStep idxBufs ["heap_ptr", "scratch_ptr"]
        (.seq
          (.call (some (none, none)) (ofString "htab_set")
            [.var .global (ofString "bal_idx_accts"), .var .local (ofString "kb"), .var .local (ofString "rec")])
          (.return (.var .local (ofString "rec")))) :=
      progWStep_seq hB hgw
        (progWStep_call0_htab_set_global "bal_idx_accts" _ _ (by decide) @nonValueSlot_bal_idx_accts)
        (progWStep_return _ _ _)
    exact WorldStepSc.trans hB hgw hs45 (hp_end m5 hm5_code hW_m5 hnt_m5 hfr_m5)

theorem «wk_idx_start_account» :
    WorldKeeps WorldOK
      (fun s => [(globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "idx_start_account") :=
  wkSc_idx_start_account.to_worldKeeps

end InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalStateInit

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBal

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Contracts.M08
open InitECandidate.Solver.Wave8GuestInv.M11
open InitECandidate.Solver.Wave8GuestInv.SoloHtabSet

private theorem bal_stor_slot_unique_ad {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hT : TablesTyped s S)
    {ad0 ad : Nat} (had0 : ad0 ∈ balRecords s) (had : ad ∈ balRecords s)
    (ht0_nz : memW s ad0 ≠ 0) (heq : memW s ad = memW s ad0) :
    ad = ad0 := by
  by_contra hne
  have hroles := hT.2.2.2.2.2.2.2.2.2.2.2
  have hp := hroles.2.1
  unfold worldRoleSlots at hp
  rw [List.filter_append] at hp
  have hbal := (List.pairwise_append.1 hp).2.1
  rw [List.filter_flatMap, List.pairwise_flatMap] at hbal
  obtain ⟨i0, hi0, he0⟩ := List.mem_iff_getElem.1 had0
  obtain ⟨i, hi, hei⟩ := List.mem_iff_getElem.1 had
  have hidx : i ≠ i0 := by
    intro h
    subst i
    exact hne (hei.symm.trans he0)
  have hmem0 : (memW s ad0, "bal.stor") ∈
      ([(memW s ad0, "bal.stor"), (memW s (ad0 + 8), "bal.reads")].filter
        fun a => a.1 != 0) := by
    simp [ht0_nz]
  have hnz : memW s ad ≠ 0 := by rw [heq]; exact ht0_nz
  have hmem : (memW s ad, "bal.stor") ∈
      ([(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")].filter
        fun a => a.1 != 0) := by
    simp [hnz]
  rcases Nat.lt_or_gt_of_ne hidx with hlt | hgt
  · have hc := List.pairwise_iff_getElem.1 hbal.2 i i0 hi hi0 hlt
    rw [hei, he0] at hc
    have hshared := (hc _ hmem _ hmem0 heq).2
    simp [sharedRoles] at hshared
  · have hc := List.pairwise_iff_getElem.1 hbal.2 i0 i hi0 hi hgt
    rw [he0, hei] at hc
    have hshared := (hc _ hmem0 _ hmem heq.symm).2
    simp [sharedRoles] at hshared


private theorem lookup_lst_push_add :
    originalRuntimeCode.lookup (ofString "lst_push") =
      some ([(ofString "l", .one), (ofString "esz", .one)],
        sourceFnBody Guest.Software.guestFn_lst_push, .one) :=
  lookup_of_guestAst_getElem 410 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_lst_push) rfl

private theorem lookup_bal_ensure_account_add :
    originalRuntimeCode.lookup (ofString "bal_ensure_account") =
      some ([(ofString "addr", .one)],
        sourceFnBody Guest.Software.guestFn_bal_ensure_account, .one) :=
  lookup_of_guestAst_getElem 412 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bal_ensure_account) rfl

private theorem lookup_lst_upsert_idx_add :
    originalRuntimeCode.lookup (ofString "lst_upsert_idx") =
      some ([(ofString "l", .one), (ofString "esz", .one), (ofString "idx", .one)],
        sourceFnBody Guest.Software.guestFn_lst_upsert_idx, .one) :=
  lookup_of_guestAst_getElem 413 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_lst_upsert_idx) rfl

private theorem lookup_add_storage_write_add :
    originalRuntimeCode.lookup (ofString "add_storage_write") =
      some ([(ofString "addr", .one), (ofString "slot", .one), (ofString "idx", .one),
             (ofString "new_value", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_add_storage_write, .one) :=
  lookup_of_guestAst_getElem 414 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_add_storage_write) rfl

private theorem lookup_add_balance_change_add :
    originalRuntimeCode.lookup (ofString "add_balance_change") =
      some ([(ofString "addr", .one), (ofString "idx", .one),
             (ofString "post_balance", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_add_balance_change, .one) :=
  lookup_of_guestAst_getElem 416 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_add_balance_change) rfl

private theorem lookup_add_nonce_change_add :
    originalRuntimeCode.lookup (ofString "add_nonce_change") =
      some ([(ofString "addr", .one), (ofString "idx", .one), (ofString "new_nonce", .one)],
        sourceFnBody Guest.Software.guestFn_add_nonce_change, .one) :=
  lookup_of_guestAst_getElem 417 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_add_nonce_change) rfl

private theorem lookup_add_code_change_add :
    originalRuntimeCode.lookup (ofString "add_code_change") =
      some ([(ofString "addr", .one), (ofString "idx", .one),
             (ofString "code", .one), (ofString "code_len", .one)],
        sourceFnBody Guest.Software.guestFn_add_code_change, .one) :=
  lookup_of_guestAst_getElem 418 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_add_code_change) rfl

private def balAddCallees (f : MlS) : Bool :=
  htabSetCallees f ||
  f == ofString "htab_get" ||
  f == ofString "htab_new" ||
  f == ofString "lst_new" ||
  f == ofString "lst_push" ||
  f == ofString "bal_ensure_account" ||
  f == ofString "lst_upsert_idx"

private theorem noCatchableRaise_mono {g1 g2 : MlS → Bool}
    (hsub : ∀ f, g1 f = true → g2 f = true) :
    (p : ProgHOL 64) → noCatchableRaise g1 p = true → noCatchableRaise g2 p = true
  | .dec _ _ _ b, h => noCatchableRaise_mono hsub b h
  | .seq a b, h => by
    simp only [noCatchableRaise, Bool.and_eq_true] at h ⊢
    exact ⟨noCatchableRaise_mono hsub a h.1, noCatchableRaise_mono hsub b h.2⟩
  | .ite _ a b, h => by
    simp only [noCatchableRaise, Bool.and_eq_true] at h ⊢
    exact ⟨noCatchableRaise_mono hsub a h.1, noCatchableRaise_mono hsub b h.2⟩
  | .while _ b, h => noCatchableRaise_mono hsub b h
  | .decCall _ _ f _ cont, h => by
    simp only [noCatchableRaise, Bool.and_eq_true] at h ⊢
    exact ⟨hsub f h.1, noCatchableRaise_mono hsub cont h.2⟩
  | .call (some (_, none)) f _, h => hsub f h
  | .call none _ _, h => by simp [noCatchableRaise] at h
  | .call (some (_, some _)) _ _, h => by simp [noCatchableRaise] at h
  | .raise _ _, h => h
  | .skip, _ | .break, _ | .continue, _ | .annot _ _, _ | .return _, _
  | .assign _ _ _, _ | .store _ _, _ | .storeByte _ _, _ | .store32 _ _, _
  | .shMemStore _ _ _, _ | .extCall _ _ _ _ _, _ => rfl
  | .shMemLoad _ _ _ _, h => by simp [noCatchableRaise] at h

private theorem balAddCallees_noCatchableRaise :
    ∀ f, balAddCallees f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      noCatchableRaise balAddCallees body = true := by
  have hsub_set : ∀ g, htabSetCallees g = true → balAddCallees g = true := by
    intro g hg; simp [balAddCallees, hg]
  intro f hf values body callee rs hfound
  simp only [balAddCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with (((((hf_set | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
  · exact noCatchableRaise_mono hsub_set body
      (htabSetCallees_noCatchableRaise f hf_set values body callee rs hfound)
  · obtain ⟨_, _, hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    rw [lookup_htab_get] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · obtain ⟨_, _, hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    rw [R10Shards.SoloHtabNew.lookup_htab_new] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · obtain ⟨_, _, hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    rw [lookup_lst_new_wk] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · obtain ⟨_, _, hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    rw [lookup_lst_push_add] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · obtain ⟨_, _, hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    rw [lookup_bal_ensure_account_add] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl
  · obtain ⟨_, _, hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    rw [lookup_lst_upsert_idx_add] at hinst
    rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; rfl

private theorem lst_push_no_catchable_exn_add {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (e : MlS) (v : ValueHOL 64)
    (hne : e ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_lst_push)).1 ≠
      some (.exception e v) :=
  evaluate_noCatchableRaise balAddCallees balAddCallees_noCatchableRaise
    (sourceFnBody Guest.Software.guestFn_lst_push) rfl s hcode e v hne

private theorem bal_ensure_account_no_catchable_exn_add {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (e : MlS) (v : ValueHOL 64)
    (hne : e ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bal_ensure_account)).1 ≠
      some (.exception e v) :=
  evaluate_noCatchableRaise balAddCallees balAddCallees_noCatchableRaise
    (sourceFnBody Guest.Software.guestFn_bal_ensure_account) rfl s hcode e v hne

private theorem lst_upsert_idx_no_catchable_exn_add {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (e : MlS) (v : ValueHOL 64)
    (hne : e ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_lst_upsert_idx)).1 ≠
      some (.exception e v) :=
  evaluate_noCatchableRaise balAddCallees balAddCallees_noCatchableRaise
    (sourceFnBody Guest.Software.guestFn_lst_upsert_idx) rfl s hcode e v hne

/-! ## 2. `WorldStep` composition helpers for `["heap_ptr"]` -/

private theorem worldStep_hp_trans {F : Type}
    {s m post : PanSemStateFiniteExact 64 F}
    {r1 r2 : Option (PanSemResultExact 64)}
    (hAs : ArenaOK s)
    (h1 : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s r1 m)
    (h2 : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra m r2 post) :
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s r2 post := by
  have hsp_eq : globN m "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (h1.2.2.1 (ofString "scratch_ptr") (by decide))
  exact worldStep_trans_bufs hAs h1 h2 (by rw [hsp_eq]) rfl
    (fun _ _ _ _ hx => False.elim (List.not_mem_nil hx))
    (fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun _ _ _ _ _ _ => trivial)

private theorem worldStep_nil_to_hp {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (h : WorldStep (fun _ => []) [] stdKeep NoExtra s r post) :
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s r post :=
  worldStep_weaken (fun _ hg => False.elim (List.not_mem_nil hg))
    (fun _ _ _ hD => hD) (fun _ _ _ _ _ hno => hno)
    (fun _ _ _ _ hi => False.elim (List.not_mem_nil hi)) (fun _ _ _ => trivial) h

private theorem worldOK_of_step {F : Type}
    {s m : PanSemStateFiniteExact 64 F} {gw : List String} {r : Option (PanSemResultExact 64)}
    (hW : WorldOK s)
    (hstep : WorldStep (fun _ => []) gw stdKeep NoExtra s r m) :
    WorldOK m := by
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  obtain ⟨Sm, Ndm, _, hWTm, _, _, _⟩ :=
    hstep.2.2.2.2 S0 Nd0 hWT0 (fun _ hx => False.elim (List.not_mem_nil hx))
  exact ⟨hstep.1, ⟨Sm, (worldTyped_iff_with m Sm).2 ⟨Ndm, hWTm⟩⟩⟩

/-! ## 3. Multi-word `panMemStoresHOL` `ByteRegionEffect` and `lst_push` on `BalListSlice` -/

private theorem panMemStoresHOL_frame_add {dom : BitVec 64 → Prop} {dec : DecidablePred dom} :
    ∀ (ws : List (HolWordLab 64)) (x : BitVec 64) (mem mem' : BitVec 64 → HolWordLab 64),
      @panMemStoresHOL 64 _ x ws dom dec mem = some mem' →
      ∀ a : BitVec 64, (∀ k, k < ws.length → a ≠ x + BitVec.ofNat 64 (8 * k)) → mem' a = mem a
  | [], _, mem, mem', hst, a, _ => by
    simp only [panMemStoresHOL, Option.some.injEq] at hst
    rw [← hst]
  | w :: ws, x, mem, mem', hst, a, hne => by
    unfold panMemStoresHOL panMemStoreHOL at hst
    split_ifs at hst with hdom
    have hbw : (panBytesInWord 64 : BitVec 64) = BitVec.ofNat 64 8 := by decide
    have ih := panMemStoresHOL_frame_add ws (x + panBytesInWord 64)
      (fun current => if current = x then w else mem current) mem' hst a (fun k hk => by
        have hk1 : k + 1 < (w :: ws).length := by simp; omega
        have hne1 := hne (k + 1) hk1
        rw [hbw]
        intro heq
        apply hne1
        rw [heq, BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega)
    rw [ih]
    exact if_neg (by simpa using hne 0 (by simp))

private theorem panMemStoresHOL_dom_all_add {dom : BitVec 64 → Prop} {dec : DecidablePred dom} :
    ∀ (ws : List (HolWordLab 64)) (x : BitVec 64) (mem mem' : BitVec 64 → HolWordLab 64),
      @panMemStoresHOL 64 _ x ws dom dec mem = some mem' →
      ∀ k, k < ws.length → dom (x + BitVec.ofNat 64 (8 * k))
  | [], _, _, _, _, k, hk => by simp at hk
  | w :: ws, x, mem, mem', hst, k, hk => by
    unfold panMemStoresHOL panMemStoreHOL at hst
    split_ifs at hst with hdom
    cases k with
    | zero => simpa using hdom
    | succ k' =>
      have hbw : (panBytesInWord 64 : BitVec 64) = BitVec.ofNat 64 8 := by decide
      have hk' : k' < ws.length := by simp at hk; omega
      have ih := panMemStoresHOL_dom_all_add ws (x + panBytesInWord 64)
        (fun current => if current = x then w else mem current) mem' hst k' hk'
      rw [hbw, BitVec.add_assoc] at ih
      have heq : (8#64 + BitVec.ofNat 64 (8 * k') : BitVec 64) = BitVec.ofNat 64 (8 * (k' + 1)) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      rwa [heq] at ih

private theorem bre_of_store_multi {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {Rl : List Ivl} {nw : Nat}
    (hma_ord : s.memaddrs = ordinaryDomain)
    (hnw_pos : 1 ≤ nw)
    (hrun : evaluateHOLFiniteState s (.store dst val) = (none, post))
    (hval_len : ∀ v : ValueHOL 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val = some v →
      (flattenHOL v).length = nw)
    (hin : ∀ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
        some (.val (.word addr)) →
      s.memaddrs addr →
      addr.toNat + 8 * nw ≤ 2 ^ 64 ∧
      ∃ i ∈ Rl, i.1 ≤ addr.toNat ∧ addr.toNat + 8 * nw ≤ i.1 + i.2) :
    ByteRegionEffect s post Rl ∧ post.locals = s.locals := by
  rw [evaluateHOLFiniteState_store] at hrun
  revert hrun
  rcases hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with
    _ | dv
  · simp
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with
        _ | v
      · simp
      · have hlen := hval_len v hv
        dsimp only
        split
        · rename_i m' hst
          intro hrun
          injection hrun with _ hpost
          subst hpost
          have hdom0 : s.memaddrs addr := by
            have := panMemStoresHOL_dom_all_add (flattenHOL v) addr s.memory m' hst 0 (by omega)
            simpa using this
          obtain ⟨hfit, i, hi, h1, h2⟩ := hin addr hdst hdom0
          have ha8 : addr.toNat % 8 = 0 := by
            have hdom' := hma_ord ▸ hdom0
            rw [Wave8Contracts.M08.ordinaryDomain_iff] at hdom'; exact hdom'.1
          have hstep_toNat : ∀ k, k < nw →
              (addr + BitVec.ofNat 64 (8 * k)).toNat = addr.toNat + 8 * k := by
            intro k hk
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)]
          refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩, rfl⟩
          · intro a hna
            apply panMemStoresHOL_frame_add (flattenHOL v) addr s.memory m' hst a
            intro k hk rfl
            exact hna (panMemStoresHOL_dom_all_add (flattenHOL v) addr s.memory m' hst k hk)
          · intro a hna
            apply panMemStoresHOL_frame_add (flattenHOL v) addr s.memory m' hst a
            intro k hk heq
            have hk_lt : k < nw := by omega
            have htn := hstep_toNat k hk_lt
            rw [← heq] at htn
            exact hna i hi ⟨by omega, by omega⟩
          · intro b hb hno
            unfold memB
            dsimp only
            have hm_eq : m' (panByteAlignHOL (BitVec.ofNat 64 b)) =
                s.memory (panByteAlignHOL (BitVec.ofNat 64 b)) := by
              apply panMemStoresHOL_frame_add (flattenHOL v) addr s.memory m' hst
              intro k hk heq
              have hk_lt : k < nw := by omega
              have hal_b : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
                rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
              rw [heq, hstep_toNat k hk_lt] at hal_b
              exact hno i hi ⟨by omega, by omega⟩
            rw [hm_eq]
        · simp
    · simp
    · simp

/-! ## 3b. `bal_list_grow_worldStep` and `lst_push` on `BalListSlice` -/

private def BalListOrigin {F : Type} (s : PanSemStateFiniteExact 64 F) (l esz : Nat) : Prop :=
  (∃ ad ∈ balRecords s,
    ((memW s (ad + 16) = l ∧ esz = 40) ∨
     (memW s (ad + 24) = l ∧ esz = 16) ∨
     (memW s (ad + 32) = l ∧ esz = 24))) ∨
  (∃ ad ∈ balRecords s, l ∈ htabValues s (memW s ad) ∧ esz = 40)

private theorem balListOrigin_slice {F : Type} {s : PanSemStateFiniteExact 64 F}
    {l esz : Nat} (horig : BalListOrigin s l esz) :
    BalListSlice s l esz := by
  rcases horig with ⟨ad, had, hwe⟩ | ⟨ad, had, hl, rfl⟩
  · rcases hwe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact bal_list_slice_of_ad_field had (Or.inl ⟨rfl, rfl⟩)
    · exact bal_list_slice_of_ad_field had (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact bal_list_slice_of_ad_field had (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · exact bal_list_slice_of_stor_val had hl

private theorem not_disj_self_24 (l : Nat) : ¬ Disj (l, 24) (l, 24) := by
  intro hdj; rcases hdj with d | d | d | d <;> dsimp only at d <;> omega

private theorem bal_list_grow_worldStep {F : Type}
    {s0 m post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {l esz np cap : Nat}
    (hW : WorldOK s0)
    (hl_nz : l ≠ 0) (hesz : esz = 16 ∨ esz = 24 ∨ esz = 40)
    (horig_all : ∀ S Nd, WorldTypedWith s0 S Nd → LstOK s0 l ∧ BalListOrigin s0 l esz)
    (hcap_eq : memW s0 (l + 16) = cap)
    (hAm : ArenaReady m)
    (hm_mem : m.memory = s0.memory)
    (hm_be : m.be = s0.be)
    (hm_gl : ∀ k : MlS, k ≠ ofString "heap_ptr" → s0.globals.lookup k = m.globals.lookup k)
    (hnp_eq : np = globN s0 "heap_ptr")
    (hhp_m : globN m "heap_ptr" = np + 2 * esz * cap)
    (heff : M11.ByteRegionEffect m post [(np, 2 * esz * cap), (l, 24)])
    (hl0_post : memW post l = np)
    (hl8_post : memW post (l + 8) ≤ 2 * cap)
    (hl16_post : memW post (l + 16) = 2 * cap) :
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s0 r post := by
  have hslice_all : ∀ S Nd, WorldTypedWith s0 S Nd → LstOK s0 l ∧ BalListSlice s0 l esz :=
    fun S Nd h => ⟨(horig_all S Nd h).1, balListOrigin_slice (horig_all S Nd h).2⟩
  have hAs := hW.1
  have hinv_post : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAm.1
  have hAp : ArenaReady post := ⟨hinv_post, arenaOK_congr heff.globals hAm.2⟩
  have hglob_mp : ∀ nm, globN post nm = globN m nm := fun nm => by simp [globN, heff.globals]
  have hhp_post : globN post "heap_ptr" = np + 2 * esz * cap := by rw [hglob_mp, hhp_m]
  have hhp_le : globN s0 "heap_ptr" ≤ globN post "heap_ptr" := by omega
  have hsp_eq : globN post "scratch_ptr" = globN s0 "scratch_ptr" := by
    rw [hglob_mp]
    exact Wave8Contracts.M08.globN_eq_of_lookup (hm_gl (ofString "scratch_ptr") (by decide))
  have hag : AllocatorGrows s0 post := ⟨hhp_le, by rw [hsp_eq]⟩
  have hG : GlobalsKept ["heap_ptr"] s0 post := by
    intro g hg
    have hg_ne : g ≠ ofString "heap_ptr" := by
      intro rfl; exact hg (List.mem_singleton.2 rfl)
    rw [heff.globals]
    exact hm_gl g hg_ne
  have hgs : Wave8Contracts.M08.WorldGlobalsSame s0 post :=
    Wave8Contracts.M08.worldGlobalsSame_of_kept hG (by decide)
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s0 S0).1 hWT0_ex
  obtain ⟨hlst0, hslice0⟩ := hslice_all S0 Nd0 hWT0
  obtain ⟨hl_fix0, hp_fix0, _, _, _, _⟩ :=
    bal_list_slice_props hWT0.2.2.1 hl_nz hesz hlst0 hslice0
  have hesz_pos : 0 < esz := by rcases hesz with rfl | rfl | rfl <;> decide
  have hcap_pos : 1 ≤ cap := by rw [← hcap_eq]; exact hlst0.1
  have hpos_arr : esz * memW s0 (l + 16) ≠ 0 :=
    ne_of_gt (Nat.mul_pos hesz_pos (by omega))
  have hpos_new : esz * (2 * cap) ≠ 0 :=
    ne_of_gt (Nat.mul_pos hesz_pos (by omega))
  rcases hWT0.2.2.1.1 _ hl_fix0 with h0 | ⟨hal_l0, hw_l0⟩
  · simp at h0
  have hl_hi : l + 24 ≤ 2 ^ 64 :=
    (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_l0).2
  have hnew_sz_eq : 2 * esz * cap = esz * (2 * cap) := by ring
  have hin_new : Inside (np, esz * (2 * cap)) (globN s0 "heap_ptr") (globN post "heap_ptr") := by
    refine ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hal_new : Allocated post (np, esz * (2 * cap)) := by
    left
    refine ⟨le_trans hAs.2.1 (by dsimp only; omega), by dsimp only; omega⟩
  have hnp8 : np % 8 = 0 := by rw [hnp_eq]; exact hAs.2.2.2.2.2.2.1
  have hsz8 : (esz * (2 * cap)) % 8 = 0 := by
    rcases hesz with rfl | rfl | rfl <;> omega
  have hw_new : WordsOK post (np, esz * (2 * cap)) :=
    M13.wordsOK_of_allocated hAp hal_new hnp8 hsz8
  have hdj_new_l : Disj (l, 24) (np, esz * (2 * cap)) :=
    disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_l0 hin_new)
  have hunhit_of_disj : ∀ i : Ivl, Allocated s0 i → Disj i (l, 24) →
      M08IvlUnhit s0 post i := by
    intro i hal_i hdj_l a ha8 hi1 hi2
    have hdj_n : Disj i (np, 2 * esz * cap) := by
      rw [hnew_sz_eq]
      exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_i hin_new)
    have hm_a := heff.cell_frame a (fun x hx hch => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨hc1, hc2⟩ := hch
      rcases hx with rfl | rfl
      · dsimp only at hc1 hc2; rcases hdj_n with d | d | d | d <;> omega
      · dsimp only at hc1 hc2; rcases hdj_l with d | d | d | d <;> omega)
    rw [hm_a, hm_mem]
  have hRK : RecordsKept (fun _ => []) stdKeep s0 post := by
    intro ⟨rec_nm, rec_ks⟩ hrec hgnz k hk _
    have hrec_sz : ∃ sz, (rec_nm, sz) ∈ typedRecords ∧ sz ≠ 0 ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [stdKeep, M13.stdKeep, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrec
      rcases hrec with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨40, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨80, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨72, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨88, by decide, by decide, ?_⟩; simp at hk; omega
    obtain ⟨sz, htr, hsz_nz, hk8, hksz⟩ := hrec_sz
    have hmf := M11.typedRec_in_fixedObjects s0 htr
    simp only [hgnz, ↓reduceIte] at hmf
    have hgb_mem : (globN s0 rec_nm, sz) ∈
        (globalBuffers.map fun gn => (globN s0 gn.1, if globN s0 gn.1 = 0 then 0 else gn.2)) ++
        [(if globN s0 "journal_cap" = 0 then 0 else globN s0 "journal", 32 * globN s0 "journal_cap")] ++
        blockOutObjects s0 := by
      apply List.mem_append_left; apply List.mem_append_left
      have hr_gb : (rec_nm, sz) ∈ globalBuffers :=
        Wave8Contracts.M08.typedRecord_mem_globalBuffers htr
      have hm : (globN s0 rec_nm, if globN s0 rec_nm = 0 then 0 else sz) ∈
          globalBuffers.map fun gn => (globN s0 gn.1, if globN s0 gn.1 = 0 then 0 else gn.2) :=
        List.mem_map.2 ⟨(rec_nm, sz), hr_gb, rfl⟩
      rwa [if_neg hgnz] at hm
    have hpw_top := List.pairwise_append.1 hWT0.2.2.1.2
    have hl_bal0 : (l, 24) ∈ balObjects s0 := by
      obtain ⟨L1, L2, hb, _⟩ := hslice0; rw [hb]; simp [lstObjects, hl_nz]
    have hdj_l : Disj (globN s0 rec_nm, sz) (l, 24) := hpw_top.2.2 _ hgb_mem _ hl_bal0
    rcases hWT0.2.2.1.1 _ hmf with h0 | ⟨hal_r, hw_r⟩
    · exact absurd h0 hsz_nz
    have hhi_r := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_r).2
    have hg8 : (globN s0 rec_nm) % 8 = 0 := hw_r.1
    change memW post (globN s0 rec_nm + k) = memW s0 (globN s0 rec_nm + k)
    exact Wave8Contracts.M08.memW_eq_of_ivlUnhit
      (hunhit_of_disj _ hal_r hdj_l) (by omega) hhi_r ⟨by omega, by omega⟩
  refine ⟨hAp, hhp_le, hG, hRK, fun S Nd hWT _ => ?_⟩
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  obtain ⟨hlst, hslice⟩ := hslice_all S Nd ⟨hT, hJ, hF, hTr⟩
  obtain ⟨hl_fix, hp_fix, hdj_lp, had_dj, hfk_dj, hst_dj⟩ :=
    bal_list_slice_props hF hl_nz hesz hlst hslice
  have hl_bal : (l, 24) ∈ balObjects s0 := by
    obtain ⟨L1, L2, hb, _⟩ := hslice; rw [hb]; simp [lstObjects, hl_nz]
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s0 t, M08IvlUnhit s0 post i := fun t ht i hi =>
    hunhit_of_disj i ((hT.2.1 t ht).2 i hi).1 (((hT.2.1 t ht).2 i hi).2 _ hl_fix)
  have hu_prefix : ∀ i ∈
      (globalBuffers.map fun gn => (globN s0 gn.1, if globN s0 gn.1 = 0 then 0 else gn.2)) ++
      [(if globN s0 "journal_cap" = 0 then 0 else globN s0 "journal", 32 * globN s0 "journal_cap")] ++
      blockOutObjects s0, M08IvlUnhit s0 post i := by
    intro i hi
    have hi_fix : i ∈ fixedObjects s0 := List.mem_append.2 (Or.inl hi)
    rcases hF.1 i hi_fix with h0 | ⟨hal_i, _⟩
    · intro a _ ha1 ha2; omega
    · exact hunhit_of_disj i hal_i ((List.pairwise_append.1 hF.2).2.2 i hi _ hl_bal)
  have hmem_gb_prefix : ∀ (nm : String) (sz : Nat), (nm, sz) ∈ globalBuffers → globN s0 nm ≠ 0 →
      (globN s0 nm, sz) ∈
        (globalBuffers.map fun gn => (globN s0 gn.1, if globN s0 gn.1 = 0 then 0 else gn.2)) ++
        [(if globN s0 "journal_cap" = 0 then 0 else globN s0 "journal", 32 * globN s0 "journal_cap")] ++
        blockOutObjects s0 := fun nm sz hgb hnz => by
    apply List.mem_append_left; apply List.mem_append_left
    have hm_in : (globN s0 nm, if globN s0 nm = 0 then 0 else sz) ∈
        globalBuffers.map fun gn => (globN s0 gn.1, if globN s0 gn.1 = 0 then 0 else gn.2) :=
      List.mem_map.2 ⟨(nm, sz), hgb, rfl⟩
    rwa [if_neg hnz] at hm_in
  have hu_ws : globN s0 "ws" ≠ 0 → M08IvlUnhit s0 post (globN s0 "ws", 40) := fun hnz =>
    hu_prefix _ (hmem_gb_prefix "ws" 40 (by decide) hnz)
  have hu_bs : globN s0 "bs" ≠ 0 → M08IvlUnhit s0 post (globN s0 "bs", 80) := fun hnz =>
    hu_prefix _ (hmem_gb_prefix "bs" 80 (by decide) hnz)
  have hu_ts : globN s0 "ts" ≠ 0 → M08IvlUnhit s0 post (globN s0 "ts", 72) := fun hnz =>
    hu_prefix _ (hmem_gb_prefix "ts" 72 (by decide) hnz)
  have hu_bo : globN s0 "bo" ≠ 0 → M08IvlUnhit s0 post (globN s0 "bo", 88) := fun hnz =>
    hu_prefix _ (hmem_gb_prefix "bo" 88 (by decide) hnz)
  have hu_jr : globN s0 "journal_cap" ≠ 0 →
      M08IvlUnhit s0 post (globN s0 "journal", 32 * globN s0 "journal_cap") := fun hnz =>
    hu_prefix _ (List.mem_append_left _ (List.mem_append_right _ (by simp [hnz])))
  have hu_bo_lst : ∀ i ∈ blockOutObjects s0, i.2 = 24 → M08IvlUnhit s0 post i := fun i hi _ =>
    hu_prefix _ (List.mem_append_right _ hi)
  have hm0 : memW post 0 = memW s0 0 ∧ memW post 8 = memW s0 8 ∧ memW post 16 = memW s0 16 := by
    have hdom_writes : ∀ a : BitVec 64, post.memory a ≠ s0.memory a → s0.memaddrs a := by
      intro a hne
      apply Classical.byContradiction
      intro hna
      have hna_m : ¬ m.memaddrs a := by
        rw [hAm.1.memaddrs, ← hAs.1.memaddrs]
        exact hna
      have heq := heff.out_dom a hna_m
      rw [hm_mem] at heq
      exact hne heq
    exact Wave8Contracts.M08.mem0_8_16_eq_of_domain_writes hdom_writes hAs.1
  have hlst_l_post : LstOK post l := by
    unfold LstOK
    rw [hl16_post]
    exact ⟨by omega, hl8_post⟩
  have hlst_l_objs_post : ∀ esz_k, esz_k = esz →
      lstObjects post l esz_k = [(l, 24), (np, esz * (2 * cap))] := by
    intro esz_k rfl
    simp [lstObjects, hl_nz, hl0_post, hl16_post, hpos_new]
  have hba_g : globN post "bal_accounts" = globN s0 "bal_accounts" :=
    hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  have hrecs_bal : balRecords post = balRecords s0 :=
    Wave8Contracts.M08.balRecords_eq_of_unhit hT hba_g (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_tab _ hm)
  have hlst_hdr_unhit_eq : ∀ (x esz_x : Nat), x ≠ 0 → (x, 24) ∈ fixedObjects s0 →
      Disj (x, 24) (l, 24) →
      lstObjects post x esz_x = lstObjects s0 x esz_x ∧ (LstOK s0 x → LstOK post x) := by
    intro x esz_x hx_nz hx_fix hdj1
    rcases hF.1 _ hx_fix with h0 | ⟨hal_x, hw_x⟩
    · simp at h0
    have hhi_x := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_x).2
    have hx8 : x % 8 = 0 := hw_x.1
    have hux := hunhit_of_disj _ hal_x hdj1
    have hw0 : memW post x = memW s0 x := by
      simpa using Wave8Contracts.M08.memW_eq_of_ivlUnhit hux (by omega) hhi_x ⟨by omega, by omega⟩
    have hw8 : memW post (x + 8) = memW s0 (x + 8) :=
      Wave8Contracts.M08.memW_eq_of_ivlUnhit hux (by omega) hhi_x ⟨by omega, by omega⟩
    have hw16 : memW post (x + 16) = memW s0 (x + 16) :=
      Wave8Contracts.M08.memW_eq_of_ivlUnhit hux (by omega) hhi_x ⟨by omega, by omega⟩
    refine ⟨by simp [lstObjects, hx_nz, hw0, hw16], fun hx_ok => ?_⟩
    unfold LstOK at hx_ok ⊢; rw [hw8, hw16]; exact hx_ok
  have had_all : ∀ ad ∈ balRecords s0,
      (∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s0 (ad + off)) ∧
      htabValues post (memW s0 ad) = htabValues s0 (memW s0 ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW s0 (ad + k))) ∧
      (∀ l' ∈ htabValues s0 (memW s0 ad), LstOK post l') := by
    intro ad had
    have had_fix : (ad, 40) ∈ fixedObjects s0 :=
      List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨ad, had, by simp⟩))
    rcases hF.1 _ had_fix with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_ad).2
    have had8 : ad % 8 = 0 := hw_ad.1
    have hu_ad := hunhit_of_disj _ hal_ad (had_dj ad had).1
    have hoff : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s0 (ad + off) := by
      intro off hoff_m
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff_m
      rcases hoff_m with rfl | rfl | rfl | rfl | rfl <;>
        exact Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_ad (by omega) hhi_ad ⟨by omega, by omega⟩
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have hvals_ad : htabValues post (memW s0 ad) = htabValues s0 (memW s0 ad) :=
      Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ had_T.1).1 (hu_tab _ had_T.1)
    refine ⟨hoff, hvals_ad, ?_, ?_⟩
    · intro k hk
      by_cases hkz : memW s0 (ad + k) = 0
      · have h_old := had_T.2.2.1 k hk
        unfold LstOK at h_old ⊢; rw [hkz, hm0.2.1, hm0.2.2]; simpa [hkz] using h_old
      · by_cases hkl : memW s0 (ad + k) = l
        · rw [hkl]; exact hlst_l_post
        · have hmem_bal := (bal_chunk_mem_of_record s0 had).2.1 k hk hkz
          exact (hlst_hdr_unhit_eq _ 40 hkz (List.mem_append.2 (Or.inr hmem_bal))
            (hfk_dj ad had k hk hkz hkl).1).2 (had_T.2.2.1 k hk)
    · intro l' hl'
      by_cases hlz : l' = 0
      · subst hlz
        have h_old := had_T.2.2.2 0 hl'
        unfold LstOK at h_old ⊢; rw [hm0.2.1, hm0.2.2]; exact h_old
      · by_cases hll : l' = l
        · subst hll; exact hlst_l_post
        · have hmem_bal := (bal_chunk_mem_of_record s0 had).2.2 l' hl' hlz
          exact (hlst_hdr_unhit_eq _ 40 hlz (List.mem_append.2 (Or.inr hmem_bal))
            (hst_dj ad had l' hl' hlz hll).1).2 (had_T.2.2.2 l' hl')
  have hpw_bal_s0 : (balObjects s0).Pairwise Disj := (List.pairwise_append.1 hF.2).2.1
  have hlst_other_bal : ∀ x esz_x, x ≠ l →
      (x ≠ 0 → (x, 24) ∈ fixedObjects s0 ∧ Disj (x, 24) (l, 24)) →
      lstObjects post x esz_x = lstObjects s0 x esz_x := by
    intro x esz_x hxl hcond
    by_cases hxz : x = 0
    · subst hxz; simp [lstObjects]
    · obtain ⟨hxf, hdj1⟩ := hcond hxz
      exact (hlst_hdr_unhit_eq x esz_x hxz hxf hdj1).1
  have horig := (horig_all S Nd ⟨hT, hJ, hF, hTr⟩).2
  -- Strengthen `balObjects_replace_of_origin` inline using `had_all` and `hlst_other_bal`:
  have flatMap_eq_of_off : ∀ {α β : Type} {xs : List α} {f g : α → List β},
      (∀ x ∈ xs, f x = g x) → xs.flatMap f = xs.flatMap g := fun h => List.flatMap_congr h
  let f0 := fun a : Nat => (a, 40) :: lstObjects s0 (memW s0 (a + 16)) 40 ++
    lstObjects s0 (memW s0 (a + 24)) 16 ++ lstObjects s0 (memW s0 (a + 32)) 24 ++
    (htabValues s0 (memW s0 a)).flatMap (fun x => lstObjects s0 x 40)
  let fp := fun a : Nat => (a, 40) :: lstObjects post (memW post (a + 16)) 40 ++
    lstObjects post (memW post (a + 24)) 16 ++ lstObjects post (memW post (a + 32)) 24 ++
    (htabValues post (memW post a)).flatMap (fun x => lstObjects post x 40)
  have hslice_both : ∃ L1 L2,
      balObjects s0 = L1 ++ lstObjects s0 l esz ++ L2 ∧
      balObjects post = L1 ++ lstObjects post l esz ++ L2 := by
    have hmem_head_of_eq : ∀ {y esz_y : Nat}, y = l → (l, 24) ∈ lstObjects s0 y esz_y := by
      intro y esz_y hy; subst hy; exact lstObjects_head_mem s0 hl_nz
    have hf_eq_of_not_mem : ∀ a ∈ balRecords s0, (l, 24) ∉ f0 a → fp a = f0 a := by
      intro a ha hnin
      have hp := had_all a ha
      have e0 : memW post a = memW s0 a := by simpa using hp.1 0 (by simp)
      have e16 := hp.1 16 (by simp)
      have e24 := hp.1 24 (by simp)
      have e32 := hp.1 32 (by simp)
      have hne16 : memW s0 (a + 16) ≠ l := fun he =>
        hnin (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_cons_of_mem _ (hmem_head_of_eq he)))))
      have hne24 : memW s0 (a + 24) ≠ l := fun he =>
        hnin (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (hmem_head_of_eq he))))
      have hne32 : memW s0 (a + 32) ≠ l := fun he =>
        hnin (List.mem_append_left _ (List.mem_append_right _
          (hmem_head_of_eq he)))
      have hne_st : ∀ x ∈ htabValues s0 (memW s0 a), x ≠ l := fun x hx he =>
        hnin (List.mem_append_right _ (List.mem_flatMap.2 ⟨x, hx, hmem_head_of_eq he⟩))
      have ho16 := hlst_other_bal (memW s0 (a + 16)) 40 hne16 fun hnz =>
        ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 ha).2.1 16 (by simp) hnz)),
         (hfk_dj a ha 16 (by simp) hnz hne16).1⟩
      have ho24 := hlst_other_bal (memW s0 (a + 24)) 16 hne24 fun hnz =>
        ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 ha).2.1 24 (by simp) hnz)),
         (hfk_dj a ha 24 (by simp) hnz hne24).1⟩
      have ho32 := hlst_other_bal (memW s0 (a + 32)) 24 hne32 fun hnz =>
        ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 ha).2.1 32 (by simp) hnz)),
         (hfk_dj a ha 32 (by simp) hnz hne32).1⟩
      dsimp only [fp, f0]
      rw [e0, e16, e24, e32, hp.2.1, ho16, ho24, ho32]
      congr 1
      apply List.flatMap_congr; intro x hx
      exact hlst_other_bal x 40 (hne_st x hx) fun hnz =>
        ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 ha).2.2 x hx hnz)),
         (hst_dj a ha x hx hnz (hne_st x hx)).1⟩
    rcases horig with ⟨ad, had, hwe⟩ | ⟨ad, had, hl_in, rfl⟩
    · obtain ⟨R1, R2, hrec⟩ := List.append_of_mem had
      have hbal0 : balObjects s0 = R1.flatMap f0 ++ f0 ad ++ R2.flatMap f0 := by
        change (balRecords s0).flatMap f0 = _
        rw [hrec]; simp [List.flatMap_append, List.flatMap_cons, List.append_assoc]
      have hbalp : balObjects post = R1.flatMap fp ++ fp ad ++ R2.flatMap fp := by
        change (balRecords post).flatMap fp = _
        rw [hrecs_bal, hrec]; simp [List.flatMap_append, List.flatMap_cons, List.append_assoc]
      have hl_in_fad : (l, 24) ∈ f0 ad := by
        rcases hwe with ⟨h16, _⟩ | ⟨h24, _⟩ | ⟨h32, _⟩
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_cons_of_mem _ (hmem_head_of_eq h16))))
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
            (hmem_head_of_eq h24)))
        · exact List.mem_append_left _ (List.mem_append_right _
            (hmem_head_of_eq h32))
      have hpw3 := hbal0 ▸ hpw_bal_s0
      have hR1_eq : R1.flatMap fp = R1.flatMap f0 := by
        apply List.flatMap_congr; intro a ha
        refine hf_eq_of_not_mem a (by rw [hrec]; exact List.mem_append_left _ ha) fun hin => ?_
        exact not_disj_self_24 l (pairwise_disj_outside_slice hpw3
          (Or.inl (List.mem_flatMap.2 ⟨a, ha, hin⟩)) hl_in_fad)
      have hR2_eq : R2.flatMap fp = R2.flatMap f0 := by
        apply List.flatMap_congr; intro a ha
        refine hf_eq_of_not_mem a (by rw [hrec]; exact List.mem_append_right _ (List.mem_cons_of_mem _ ha)) fun hin => ?_
        exact not_disj_self_24 l (pairwise_disj_outside_slice hpw3
          (Or.inr (List.mem_flatMap.2 ⟨a, ha, hin⟩)) hl_in_fad)
      have hpw_fad : (f0 ad).Pairwise Disj :=
        (List.pairwise_append.1 (List.pairwise_append.1 hpw3).1).2.1
      have hp := had_all ad had
      have e0 : memW post ad = memW s0 ad := by simpa using hp.1 0 (by simp)
      have e16 := hp.1 16 (by simp)
      have e24 := hp.1 24 (by simp)
      have e32 := hp.1 32 (by simp)
      rcases hwe with ⟨h16, rfl⟩ | ⟨h24, rfl⟩ | ⟨h32, rfl⟩
      · have hpw_sub : (([(ad, 40)]) ++ lstObjects s0 l 40 ++
            (lstObjects s0 (memW s0 (ad + 24)) 16 ++ lstObjects s0 (memW s0 (ad + 32)) 24 ++
              (htabValues s0 (memW s0 ad)).flatMap (fun x => lstObjects s0 x 40))).Pairwise Disj := by
          simpa [f0, h16, List.append_assoc] using hpw_fad
        have hne24 : memW s0 (ad + 24) ≠ l := fun he =>
          not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
            (Or.inr (List.mem_append_left _ (List.mem_append_left _ (hmem_head_of_eq he))))
            (lstObjects_head_mem s0 hl_nz))
        have hne32 : memW s0 (ad + 32) ≠ l := fun he =>
          not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
            (Or.inr (List.mem_append_left _ (List.mem_append_right _ (hmem_head_of_eq he))))
            (lstObjects_head_mem s0 hl_nz))
        have hne_st : ∀ x ∈ htabValues s0 (memW s0 ad), x ≠ l := fun x hx he =>
          not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
            (Or.inr (List.mem_append_right _ (List.mem_flatMap.2 ⟨x, hx, hmem_head_of_eq he⟩)))
            (lstObjects_head_mem s0 hl_nz))
        have ho24 := hlst_other_bal (memW s0 (ad + 24)) 16 hne24 fun hnz =>
          ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.1 24 (by simp) hnz)),
           (hfk_dj ad had 24 (by simp) hnz hne24).1⟩
        have ho32 := hlst_other_bal (memW s0 (ad + 32)) 24 hne32 fun hnz =>
          ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.1 32 (by simp) hnz)),
           (hfk_dj ad had 32 (by simp) hnz hne32).1⟩
        refine ⟨R1.flatMap f0 ++ [(ad, 40)],
          lstObjects s0 (memW s0 (ad + 24)) 16 ++ lstObjects s0 (memW s0 (ad + 32)) 24 ++
            (htabValues s0 (memW s0 ad)).flatMap (fun x => lstObjects s0 x 40) ++ R2.flatMap f0,
          by rw [hbal0]; simp [f0, h16, List.append_assoc], ?_⟩
        rw [hbalp, hR1_eq, hR2_eq]; dsimp only [fp]
        rw [e0, e16, e24, e32, hp.2.1, h16, ho24, ho32,
          flatMap_eq_of_off fun x hx => hlst_other_bal x 40 (hne_st x hx) fun hnz =>
            ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.2 x hx hnz)),
             (hst_dj ad had x hx hnz (hne_st x hx)).1⟩]
        simp [List.append_assoc]
      · have hpw_sub : (([(ad, 40)] ++ lstObjects s0 (memW s0 (ad + 16)) 40) ++ lstObjects s0 l 16 ++
            (lstObjects s0 (memW s0 (ad + 32)) 24 ++
              (htabValues s0 (memW s0 ad)).flatMap (fun x => lstObjects s0 x 40))).Pairwise Disj := by
          simpa [f0, h24, List.append_assoc] using hpw_fad
        have hne16 : memW s0 (ad + 16) ≠ l := fun he =>
          not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
            (Or.inl (List.mem_append_right _ (hmem_head_of_eq he)))
            (lstObjects_head_mem s0 hl_nz))
        have hne32 : memW s0 (ad + 32) ≠ l := fun he =>
          not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
            (Or.inr (List.mem_append_left _ (hmem_head_of_eq he)))
            (lstObjects_head_mem s0 hl_nz))
        have hne_st : ∀ x ∈ htabValues s0 (memW s0 ad), x ≠ l := fun x hx he =>
          not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
            (Or.inr (List.mem_append_right _ (List.mem_flatMap.2 ⟨x, hx, hmem_head_of_eq he⟩)))
            (lstObjects_head_mem s0 hl_nz))
        have ho16 := hlst_other_bal (memW s0 (ad + 16)) 40 hne16 fun hnz =>
          ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.1 16 (by simp) hnz)),
           (hfk_dj ad had 16 (by simp) hnz hne16).1⟩
        have ho32 := hlst_other_bal (memW s0 (ad + 32)) 24 hne32 fun hnz =>
          ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.1 32 (by simp) hnz)),
           (hfk_dj ad had 32 (by simp) hnz hne32).1⟩
        refine ⟨R1.flatMap f0 ++ [(ad, 40)] ++ lstObjects s0 (memW s0 (ad + 16)) 40,
          lstObjects s0 (memW s0 (ad + 32)) 24 ++
            (htabValues s0 (memW s0 ad)).flatMap (fun x => lstObjects s0 x 40) ++ R2.flatMap f0,
          by rw [hbal0]; simp [f0, h24, List.append_assoc], ?_⟩
        rw [hbalp, hR1_eq, hR2_eq]; dsimp only [fp]
        rw [e0, e16, e24, e32, hp.2.1, h24, ho16, ho32,
          flatMap_eq_of_off fun x hx => hlst_other_bal x 40 (hne_st x hx) fun hnz =>
            ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.2 x hx hnz)),
             (hst_dj ad had x hx hnz (hne_st x hx)).1⟩]
        simp [List.append_assoc]
      · have hpw_sub : (([(ad, 40)] ++ lstObjects s0 (memW s0 (ad + 16)) 40 ++
              lstObjects s0 (memW s0 (ad + 24)) 16) ++ lstObjects s0 l 24 ++
            (htabValues s0 (memW s0 ad)).flatMap (fun x => lstObjects s0 x 40)).Pairwise Disj := by
          simpa [f0, h32, List.append_assoc] using hpw_fad
        have hne16 : memW s0 (ad + 16) ≠ l := fun he =>
          not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
            (Or.inl (List.mem_append_left _ (List.mem_append_right _ (hmem_head_of_eq he))))
            (lstObjects_head_mem s0 hl_nz))
        have hne24 : memW s0 (ad + 24) ≠ l := fun he =>
          not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
            (Or.inl (List.mem_append_right _ (hmem_head_of_eq he)))
            (lstObjects_head_mem s0 hl_nz))
        have hne_st : ∀ x ∈ htabValues s0 (memW s0 ad), x ≠ l := fun x hx he =>
          not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
            (Or.inr (List.mem_flatMap.2 ⟨x, hx, hmem_head_of_eq he⟩))
            (lstObjects_head_mem s0 hl_nz))
        have ho16 := hlst_other_bal (memW s0 (ad + 16)) 40 hne16 fun hnz =>
          ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.1 16 (by simp) hnz)),
           (hfk_dj ad had 16 (by simp) hnz hne16).1⟩
        have ho24 := hlst_other_bal (memW s0 (ad + 24)) 16 hne24 fun hnz =>
          ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.1 24 (by simp) hnz)),
           (hfk_dj ad had 24 (by simp) hnz hne24).1⟩
        refine ⟨R1.flatMap f0 ++ [(ad, 40)] ++ lstObjects s0 (memW s0 (ad + 16)) 40 ++
            lstObjects s0 (memW s0 (ad + 24)) 16,
          (htabValues s0 (memW s0 ad)).flatMap (fun x => lstObjects s0 x 40) ++ R2.flatMap f0,
          by rw [hbal0]; simp [f0, h32, List.append_assoc], ?_⟩
        rw [hbalp, hR1_eq, hR2_eq]; dsimp only [fp]
        rw [e0, e16, e24, e32, hp.2.1, h32, ho16, ho24,
          flatMap_eq_of_off fun x hx => hlst_other_bal x 40 (hne_st x hx) fun hnz =>
            ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.2 x hx hnz)),
             (hst_dj ad had x hx hnz (hne_st x hx)).1⟩]
        simp [List.append_assoc]
    · obtain ⟨R1, R2, hrec⟩ := List.append_of_mem had
      obtain ⟨V1, V2, hval⟩ := List.append_of_mem hl_in
      have hbal0 : balObjects s0 = R1.flatMap f0 ++ f0 ad ++ R2.flatMap f0 := by
        change (balRecords s0).flatMap f0 = _
        rw [hrec]; simp [List.flatMap_append, List.flatMap_cons, List.append_assoc]
      have hbalp : balObjects post = R1.flatMap fp ++ fp ad ++ R2.flatMap fp := by
        change (balRecords post).flatMap fp = _
        rw [hrecs_bal, hrec]; simp [List.flatMap_append, List.flatMap_cons, List.append_assoc]
      have hl_in_fad : (l, 24) ∈ f0 ad :=
        List.mem_append_right _ (List.mem_flatMap.2 ⟨l, hl_in, lstObjects_head_mem s0 hl_nz⟩)
      have hpw3 := hbal0 ▸ hpw_bal_s0
      have hR1_eq : R1.flatMap fp = R1.flatMap f0 := by
        apply List.flatMap_congr; intro a ha
        refine hf_eq_of_not_mem a (by rw [hrec]; exact List.mem_append_left _ ha) fun hin => ?_
        exact not_disj_self_24 l (pairwise_disj_outside_slice hpw3
          (Or.inl (List.mem_flatMap.2 ⟨a, ha, hin⟩)) hl_in_fad)
      have hR2_eq : R2.flatMap fp = R2.flatMap f0 := by
        apply List.flatMap_congr; intro a ha
        refine hf_eq_of_not_mem a (by rw [hrec]; exact List.mem_append_right _ (List.mem_cons_of_mem _ ha)) fun hin => ?_
        exact not_disj_self_24 l (pairwise_disj_outside_slice hpw3
          (Or.inr (List.mem_flatMap.2 ⟨a, ha, hin⟩)) hl_in_fad)
      have hpw_fad : (f0 ad).Pairwise Disj :=
        (List.pairwise_append.1 (List.pairwise_append.1 hpw3).1).2.1
      have hp := had_all ad had
      have e0 : memW post ad = memW s0 ad := by simpa using hp.1 0 (by simp)
      have e16 := hp.1 16 (by simp)
      have e24 := hp.1 24 (by simp)
      have e32 := hp.1 32 (by simp)
      have hpw_sub : (([(ad, 40)] ++ lstObjects s0 (memW s0 (ad + 16)) 40 ++
          lstObjects s0 (memW s0 (ad + 24)) 16 ++ lstObjects s0 (memW s0 (ad + 32)) 24 ++
          V1.flatMap (fun x => lstObjects s0 x 40)) ++ lstObjects s0 l 40 ++
          V2.flatMap (fun x => lstObjects s0 x 40)).Pairwise Disj := by
        dsimp only [f0] at hpw_fad
        rw [hval] at hpw_fad
        simpa [List.flatMap_append, List.flatMap_cons, List.append_assoc] using hpw_fad
      have hne16 : memW s0 (ad + 16) ≠ l := fun he =>
        not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
          (Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_right _ (hmem_head_of_eq he))))))
          (lstObjects_head_mem s0 hl_nz))
      have hne24 : memW s0 (ad + 24) ≠ l := fun he =>
        not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
          (Or.inl (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_right _ (hmem_head_of_eq he)))))
          (lstObjects_head_mem s0 hl_nz))
      have hne32 : memW s0 (ad + 32) ≠ l := fun he =>
        not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
          (Or.inl (List.mem_append_left _ (List.mem_append_right _ (hmem_head_of_eq he))))
          (lstObjects_head_mem s0 hl_nz))
      have hne_V1 : ∀ x ∈ V1, x ≠ l := fun x hx he =>
        not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
          (Or.inl (List.mem_append_right _ (List.mem_flatMap.2 ⟨x, hx, hmem_head_of_eq he⟩)))
          (lstObjects_head_mem s0 hl_nz))
      have hne_V2 : ∀ x ∈ V2, x ≠ l := fun x hx he =>
        not_disj_self_24 l (pairwise_disj_outside_slice hpw_sub
          (Or.inr (List.mem_flatMap.2 ⟨x, hx, hmem_head_of_eq he⟩))
          (lstObjects_head_mem s0 hl_nz))
      have ho16 := hlst_other_bal (memW s0 (ad + 16)) 40 hne16 fun hnz =>
        ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.1 16 (by simp) hnz)),
         (hfk_dj ad had 16 (by simp) hnz hne16).1⟩
      have ho24 := hlst_other_bal (memW s0 (ad + 24)) 16 hne24 fun hnz =>
        ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.1 24 (by simp) hnz)),
         (hfk_dj ad had 24 (by simp) hnz hne24).1⟩
      have ho32 := hlst_other_bal (memW s0 (ad + 32)) 24 hne32 fun hnz =>
        ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.1 32 (by simp) hnz)),
         (hfk_dj ad had 32 (by simp) hnz hne32).1⟩
      refine ⟨R1.flatMap f0 ++ [(ad, 40)] ++ lstObjects s0 (memW s0 (ad + 16)) 40 ++
          lstObjects s0 (memW s0 (ad + 24)) 16 ++ lstObjects s0 (memW s0 (ad + 32)) 24 ++
          V1.flatMap (fun x => lstObjects s0 x 40),
        V2.flatMap (fun x => lstObjects s0 x 40) ++ R2.flatMap f0,
        by rw [hbal0]; dsimp only [f0]; rw [hval]
           simp [List.flatMap_append, List.flatMap_cons, List.append_assoc], ?_⟩
      rw [hbalp, hR1_eq, hR2_eq]; dsimp only [fp]
      rw [e0, e16, e24, e32, hp.2.1, hval, ho16, ho24, ho32]
      simp only [List.flatMap_append, List.flatMap_cons]
      rw [flatMap_eq_of_off fun x hx => hlst_other_bal x 40 (hne_V1 x hx) fun hnz =>
            ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.2 x
              (by rw [hval]; exact List.mem_append_left _ hx) hnz)),
             (hst_dj ad had x (by rw [hval]; exact List.mem_append_left _ hx) hnz (hne_V1 x hx)).1⟩,
          flatMap_eq_of_off fun x hx => hlst_other_bal x 40 (hne_V2 x hx) fun hnz =>
            ⟨List.mem_append.2 (Or.inr ((bal_chunk_mem_of_record s0 had).2.2 x
              (by rw [hval]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)) hnz)),
             (hst_dj ad had x (by rw [hval]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)) hnz (hne_V2 x hx)).1⟩]
      simp [List.append_assoc]
  obtain ⟨L1, L2, hbal_s0_eq, hbal_post_eq⟩ := hslice_both
  have hlst_post_eq : lstObjects post l esz = [(l, 24), (np, esz * (2 * cap))] :=
    hlst_l_objs_post esz rfl
  have hbo_g : globN post "bo" = globN s0 "bo" := hgs.1 ("bo", 88) (by simp [globalBuffers])
  have hws_g : globN post "ws" = globN s0 "ws" := hgs.1 ("ws", 40) (by simp [globalBuffers])
  have hbs_g : globN post "bs" = globN s0 "bs" := hgs.1 ("bs", 80) (by simp [globalBuffers])
  have hts_g : globN post "ts" = globN s0 "ts" := hgs.1 ("ts", 72) (by simp [globalBuffers])
  have hbia_g : globN post "bal_idx_accts" = globN s0 "bal_idx_accts" :=
    hgs.2.1 "bal_idx_accts" (by simp [globalTableRoots])
  have hbis_g : globN post "bal_idx_stor" = globN s0 "bal_idx_stor" :=
    hgs.2.1 "bal_idx_stor" (by simp [globalTableRoots])
  have htr_ws : ("ws", 40) ∈ Wave8Contracts.M08.typedRecords := by decide
  have htr_bs : ("bs", 80) ∈ Wave8Contracts.M08.typedRecords := by decide
  have htr_ts : ("ts", 72) ∈ Wave8Contracts.M08.typedRecords := by decide
  have htr_bo : ("bo", 88) ∈ Wave8Contracts.M08.typedRecords := by decide
  have hbo_words : globN s0 "bo" ≠ 0 → ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN s0 "bo" + k) = memW s0 (globN s0 "bo" + k) := fun hnz k hk => by
    have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    simpa [hbo_g] using Wave8Contracts.M08.rec_word_eq_of_unhit
      hAs.2 hF "bo" 88 htr_bo hbo_g hnz (hu_bo hnz) hk_in.1 hk_in.2
  have hbo_part := Wave8Contracts.M08.blockOutObjects_eq_of_bo_unhit
    hAs.2 hF hbo_g hT.2.2.2.2.2.2.2.2.2.2.1
    (fun h => hbo_words h 24 (by simp))
    (fun h => hbo_words h 32 (by simp))
    (fun h => hbo_words h 40 (by simp))
    (fun h => hbo_words h 56 (by simp))
    (fun h => hbo_words h 72 (by simp))
    (fun h => hbo_words h 80 (by simp))
    (fun _ _ => by simp [hm0.1, hm0.2.2])
    (fun _ _ => by simp [hm0.1, hm0.2.2])
    (fun h h40 => hu_bo_lst (memW s0 (globN s0 "bo" + 40), 24) (by simp [blockOutObjects, h, h40]) rfl)
    (fun h h72 => hu_bo_lst (memW s0 (globN s0 "bo" + 72), 24) (by simp [blockOutObjects, h, h72]) rfl)
  let pref0 := (globalBuffers.map fun gn => (globN s0 gn.1, if globN s0 gn.1 = 0 then 0 else gn.2)) ++
    [(if globN s0 "journal_cap" = 0 then 0 else globN s0 "journal", 32 * globN s0 "journal_cap")] ++
    blockOutObjects s0
  have hfix_post_eq : fixedObjects post = pref0 ++ (L1 ++ lstObjects post l esz ++ L2) := by
    unfold fixedObjects
    rw [hbo_part.1, hbal_post_eq, hgs.2.2.1, hgs.2.2.2.1]
    congr 1; congr 1; congr 1
    apply List.map_congr_left; intro gn hgn; rw [hgs.1 gn hgn]
  have hfix_s0_eq : fixedObjects s0 = pref0 ++ (L1 ++ lstObjects s0 l esz ++ L2) := by
    unfold fixedObjects; rw [hbal_s0_eq]
  have hfix_from : ∀ x ∈ fixedObjects post,
      x ∈ fixedObjects s0 ∨ x = (np, esz * (2 * cap)) := by
    intro x hx
    rw [hfix_post_eq, hlst_post_eq] at hx
    rcases List.mem_append.1 hx with hxp | hxb
    · exact Or.inl (List.mem_append.2 (Or.inl hxp))
    · rcases List.mem_append.1 hxb with hxb1 | hx2
      · rcases List.mem_append.1 hxb1 with hx1 | hxm
        · exact Or.inl (by rw [hfix_s0_eq]; exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ hx1)))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxm
          rcases hxm with rfl | rfl
          · exact Or.inl hl_fix
          · exact Or.inr rfl
      · exact Or.inl (by rw [hfix_s0_eq]; exact List.mem_append_right _ (List.mem_append_right _ hx2))
  have hdisj_old_new : ∀ x ∈ fixedObjects s0, Disj x (np, esz * (2 * cap)) := by
    intro x hx
    rcases hF.1 x hx with h0 | ⟨hal_x, _⟩
    · exact Or.inl h0
    · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_x hin_new)
  have hF_post : FixedTyped post := by
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases hfix_from x hx with hx_s | rfl
      · rcases hF.1 x hx_s with h0 | ⟨hal_x, hw_x⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hag.allocated hal_x, Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 hw_x⟩
      · exact Or.inr ⟨hal_new, hw_new⟩
    · rw [hfix_post_eq, hlst_post_eq]
      have hpw_f0 := hfix_s0_eq ▸ hF.2
      have hpw_f0' : ((pref0 ++ L1) ++ lstObjects s0 l esz ++ L2).Pairwise Disj := by
        simpa [List.append_assoc] using hpw_f0
      have hpw_rep := pairwise_disj_replace_slice hpw_f0'
        (List.pairwise_cons.2 ⟨fun y hy => by simp at hy; subst hy; exact hdj_new_l, List.pairwise_singleton _ _⟩)
        (fun x hx y hy => by
          have hx_f0 : x ∈ fixedObjects s0 := by
            rw [hfix_s0_eq]
            rcases List.mem_append.1 hx with hxp | hx1
            · exact List.mem_append_left _ hxp
            · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ hx1))
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl
          · exact pairwise_disj_outside_slice hpw_f0' (Or.inl hx) (lstObjects_head_mem s0 hl_nz)
          · exact hdisj_old_new x hx_f0)
        (fun x hx y hy => by
          have hy_f0 : y ∈ fixedObjects s0 := by
            rw [hfix_s0_eq]; exact List.mem_append_right _ (List.mem_append_right _ hy)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact disj_flip (pairwise_disj_outside_slice hpw_f0' (Or.inr hy) (lstObjects_head_mem s0 hl_nz))
          · exact disj_flip (hdisj_old_new y hy_f0))
      simpa [List.append_assoc] using hpw_rep
  have hjr_part := Wave8Contracts.M08.journalRoleSlots_eq_of_unhit
    hAs.1 hAp.1 hAs.2 hag (fun _ hx => hx) hJ hF hgs hu_ts hu_jr
  have hwrs_eq : worldRoleSlots post = worldRoleSlots s0 := by
    have hrec_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] =
        recRoles s0 "ws" [(16, "ws+16"), (32, "ws+32")] := by
      unfold recRoles
      by_cases h : globN s0 "ws" = 0
      · simp [hws_g, h]
      · have hw16 := Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ws" 40 htr_ws hws_g h (hu_ws h) (k := 16) (by omega) (by omega)
        have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ws" 40 htr_ws hws_g h (hu_ws h) (k := 32) (by omega) (by omega)
        simp only [hws_g] at hw16 hw32 ⊢
        simp [h, hw16, hw32]
    have hrec_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
        (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
        recRoles s0 "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
        (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
      unfold recRoles
      by_cases h : globN s0 "bs" = 0
      · simp [hbs_g, h]
      · simp only [hbs_g, h, ↓reduceIte]
        apply List.map_congr_left
        intro ⟨k, r0⟩ hkr
        have hk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
          rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        have hw := Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "bs" 80 htr_bs hbs_g h (hu_bs h) hk.1 hk.2
        simp only [hbs_g] at hw; simp [hw]
    have hrec_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
        recRoles s0 "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
      unfold recRoles
      by_cases h : globN s0 "ts" = 0
      · simp [hts_g, h]
      · simp only [hts_g, h, ↓reduceIte]
        apply List.map_congr_left
        intro ⟨k, r0⟩ hkr
        have hk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
          rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        have hw := Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ts" 72 htr_ts hts_g h (hu_ts h) hk.1 hk.2
        simp only [hts_g] at hw; simp [hw]
    have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s0 "bs" "bs.inner" := by
      unfold nestRoles
      by_cases h : globN s0 "bs" = 0
      · simp [hbs_g, h]
      · have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "bs" 80 htr_bs hbs_g h (hu_bs h) (k := 32) (by omega) (by omega)
        simp only [hbs_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
        by_cases h32 : memW s0 (globN s0 "bs" + 32) = 0
        · simp [h32]
        · simp only [h32, ↓reduceIte]
          have hmS : memW s0 (globN s0 "bs" + 32) ∈ S := by
            rcases hT.2.2.2.2.1 32 (by simp [bsTableSlots]) h with h0 | hm
            · exact absurd h0 h32
            · exact hm
          rw [Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
    have hnest_ts : nestRoles post "ts" "ts.inner" = nestRoles s0 "ts" "ts.inner" := by
      unfold nestRoles
      by_cases h : globN s0 "ts" = 0
      · simp [hts_g, h]
      · have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ts" 72 htr_ts hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
        simp only [hts_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
        by_cases h32 : memW s0 (globN s0 "ts" + 32) = 0
        · simp [h32]
        · simp only [h32, ↓reduceIte]
          have hmS : memW s0 (globN s0 "ts" + 32) ∈ S := by
            rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) h with h0 | hm
            · exact absurd h0 h32
            · exact hm
          rw [Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_tab _ hmS)]
    unfold worldRoleSlots
    rw [hrec_ws, hrec_bs, hrec_ts, hba_g, hbia_g, hbis_g, hnest_bs, hnest_ts, hrecs_bal]
    congr 1; congr 1
    apply List.flatMap_congr; intro ad had
    have had0 : memW post ad = memW s0 ad := by simpa using (had_all ad had).1 0 (by simp)
    have had8 : memW post (ad + 8) = memW s0 (ad + 8) := (had_all ad had).1 8 (by simp)
    rw [had0, had8]
  have hu_nd_rec : ∀ n ∈ Nd, M08IvlUnhit s0 post (nodeIvl s0 n) := fun n hn => by
    have hne_mem : nodeIvl s0 n ∈ nodeExtents s0 Nd :=
      List.mem_flatMap.2 ⟨n, hn, List.mem_cons_self⟩
    exact hunhit_of_disj _ (hTr.1.1 n hn).2.1 ((hTr.2.1 _ hne_mem).2 _ hl_fix)
  have hu_nd_byte : ∀ n ∈ Nd, (memW s0 n = 1 ∨ memW s0 n = 2) → memW s0 (n + 40) ≠ 0 →
      ∀ k, k < memW s0 (n + 40) → memB post (memW s0 (n + 32) + k) = memB s0 (memW s0 (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    have hnp_mem : nodePath s0 n ∈ nodeExtents s0 Nd :=
      List.mem_flatMap.2 ⟨n, hn, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)⟩
    have hnp_eq : nodePath s0 n = (memW s0 (n + 32), memW s0 (n + 40)) := by
      simp [nodePath, h12, hlen0]
    have hdj_l : Disj (memW s0 (n + 32), memW s0 (n + 40)) (l, 24) := by
      rw [← hnp_eq]; exact (hTr.2.1 _ hnp_mem).2 _ hl_fix
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_np, hin_p, _⟩
    · exact absurd h0 hlen0
    have hdj_n : Disj (memW s0 (n + 32), memW s0 (n + 40)) (np, 2 * esz * cap) := by
      rw [hnew_sz_eq]
      exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_np hin_new)
    have hlim264 : heapLimit ≤ 2 ^ 64 := by decide
    have hbk_lt : memW s0 (n + 32) + k < 2 ^ 64 := by
      have := hin_p.2; dsimp at this; omega
    have hb_eq := heff.byte_frame (memW s0 (n + 32) + k) hbk_lt (fun x hx hbi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨hb1, hb2⟩ := hbi
      rcases hx with rfl | rfl
      · dsimp only at hb1 hb2; rcases hdj_n with d | d | d | d <;> omega
      · dsimp only at hb1 hb2; rcases hdj_l with d | d | d | d <;> omega)
    rw [hb_eq]
    unfold memB
    rw [hm_mem, hm_be]
  have hnd_part := Wave8Contracts.M08.nodeHeap_congr_bytes
    hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_byte
  have htab_fp_hdr : ∀ t ∈ S, (∀ k, k < 11 → hdr post t k = hdr s0 t k) ∧
      htabFootprint post t = htabFootprint s0 t := by
    have h264_he : heapEnd ≤ 2 ^ 64 := by decide
    intro t ht
    have hwf := (hT.2.1 t ht).1
    have ht_fp : (t, 88) ∈ htabFootprint s0 t := by simp [htabFootprint]
    have ht8 : t % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have hhi : t + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; dsimp at this; omega
    exact Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit
      ht8 hhi (hu_tab t ht _ ht_fp)
  have hflat_fp : S.flatMap (htabFootprint post) = S.flatMap (htabFootprint s0) :=
    List.flatMap_congr fun t ht => (htab_fp_hdr t ht).2
  have hT_post : TablesTyped post S := by
    obtain ⟨hndS, hTt, hTp, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, hboT, hroles⟩ := hT
    refine ⟨hndS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_part.2, ?_⟩
    · intro t ht
      rw [(htab_fp_hdr t ht).2]
      refine ⟨Wave8Contracts.M08.htabWF_congr_unhit hAs.1 hAp.1 (hTt t ht).1 (hu_tab t ht),
        fun i hi => ⟨hag.allocated ((hTt t ht).2 i hi).1, fun j hj => ?_⟩⟩
      rcases hfix_from j hj with hj_s | rfl
      · exact ((hTt t ht).2 i hi).2 j hj_s
      · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 ((hTt t ht).2 i hi).1 hin_new)
    · intro t ht u hu_mem hne
      rw [(htab_fp_hdr t ht).2, (htab_fp_hdr u hu_mem).2]
      exact hTp t ht u hu_mem hne
    · intro k hk hnz
      rw [hws_g] at hnz
      have hwk : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ws" 40 htr_ws hws_g hnz (hu_ws hnz) hwk.1 hwk.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [hbs_g] at hnz
      have hbk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "bs" 80 htr_bs hbs_g hnz (hu_bs hnz) hbk.1 hbk.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [hts_g] at hnz
      have htk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ts" 72 htr_ts hts_g hnz (hu_ts hnz) htk.1 htk.2]
      exact htsR k hk hnz
    · intro g hg; rw [hgs.2.1 g hg]; exact hgR g hg
    · intro hnz hm
      rw [hbs_g] at hnz
      have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "bs" 80 htr_bs hbs_g hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact Wave8Contracts.M08.htabValuesIn_congr_unhit
        (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (hbsN hnz hm)
    · intro hnz hm
      rw [hts_g] at hnz
      have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "ts" 72 htr_ts hts_g hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [hw32] at hm ⊢
      exact Wave8Contracts.M08.htabValuesIn_congr_unhit
        (hTt _ hm).1 (hu_tab _ hm) (fun _ hx => hx) (htsN hnz hm)
    · intro ad had
      rw [hrecs_bal] at had
      have hp := had_all ad had
      have h0 : memW post ad = memW s0 ad := by simpa using hp.1 0 (by simp)
      have h8 : memW post (ad + 8) = memW s0 (ad + 8) := hp.1 8 (by simp)
      have had_old := hbalT ad had
      refine ⟨by rw [h0]; exact had_old.1, by rw [h8]; exact had_old.2.1, ?_, ?_⟩
      · intro k hk
        have hk5 : k ∈ ([0, 8, 16, 24, 32] : List Nat) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
          rcases hk with rfl | rfl | rfl <;> simp
        rw [hp.1 k hk5]; exact hp.2.2.1 k hk
      · intro l' hl'; rw [h0, hp.2.1] at hl'; exact hp.2.2.2 l' hl'
    · unfold RolesOK at hroles ⊢
      rw [hwrs_eq, hjr_part.1]
      refine ⟨fun a ha => ?_, hroles.2.1, hroles.2.2⟩
      obtain ⟨haS, hak⟩ := hroles.1 a ha
      rw [(htab_fp_hdr a.1 haS).1 0 (by omega)]
      exact ⟨haS, hak⟩
  have hTr_post : TriesTypedWith post S Nd := by
    refine ⟨hnd_part.1, ?_, ?_⟩
    · intro o ho
      rw [hnd_part.2] at ho
      have ho_alloc : o = (0, 0) ∨ Allocated s0 o := by
        unfold nodeExtents at ho
        obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
        rcases hno with rfl | rfl
        · exact Or.inr (hTr.1.1 n hn).2.1
        · unfold nodePath
          split
          · rename_i hcond
            rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hcond.1 with h0 | ⟨_, hal, _⟩
            · exact absurd h0 hcond.2
            · exact Or.inr hal
          · exact Or.inl rfl
      refine ⟨fun t ht i hi => ?_, fun j hj => ?_⟩
      · rw [(htab_fp_hdr t ht).2] at hi
        exact (hTr.2.1 o ho).1 t ht i hi
      · rcases hfix_from j hj with hj_s | rfl
        · exact (hTr.2.1 o ho).2 j hj_s
        · rcases ho_alloc with rfl | hal_o
          · exact Or.inl rfl
          · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_o hin_new)
    · intro hnz
      rw [hws_g] at hnz
      have hw24 := Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "ws" 40 htr_ws hws_g hnz (hu_ws hnz) (k := 24) (by omega) (by omega)
      have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit
        hAs.2 hF "ws" 40 htr_ws hws_g hnz (hu_ws hnz) (k := 32) (by omega) (by omega)
      rw [hw24, hw32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hnz
      refine ⟨hr24, fun hm i hi => ?_⟩
      have hwf32 := (hT.2.1 _ hm).1
      have hu32 := hu_tab _ hm
      have hh32 := htab_fp_hdr _ hm
      rw [hh32.1 3 (by omega)] at hi
      have hvals := Wave8Contracts.M08.htabValues_eq_of_unhit hwf32 hu32
      have hget : (htabValues post (memW s0 (globN s0 "ws" + 32)))[i]? =
          (htabValues s0 (memW s0 (globN s0 "ws" + 32)))[i]? := by rw [hvals]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hh32.1 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]
      exact hr32 hm i hi
  have hfr : FrameOutside s0 post (worldOwned s0 S Nd ++ ([] : List Ivl) ++ [freeGap s0]) (heapFree s0) := by
    intro a ha hnhf
    have hm_a := heff.cell_frame a (fun x hx hch => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨hc1, hc2⟩ := hch
      have hl_ow : (l, 24) ∈ worldOwned s0 S Nd ++ ([] : List Ivl) ++ [freeGap s0] := by
        apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_append_left _ (List.mem_append_right _ hl_fix)
      rcases hx with rfl | rfl
      · dsimp only at hc1 hc2
        have hlim : np + 2 * esz * cap ≤ heapLimit := by
          have := hAp.2.2.1; omega
        exact hnhf ⟨by unfold heapFree M13.heapFree; dsimp only; omega,
                    by unfold heapFree M13.heapFree; dsimp only; omega⟩
      · exact ha (l, 24) hl_ow ⟨hc1, hc2⟩)
    rw [hm_a, hm_mem]
  have hOG : OwnedGrows s0 post (worldOwned s0 S Nd) (worldOwned post S Nd) := by
    intro o ho
    unfold worldOwned M13.worldOwned at ho
    simp only [List.mem_append] at ho
    rcases ho with (ho_tab | ho_fix) | ho_nd
    · rw [hflat_fp] at ho_tab
      refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
      unfold worldOwned M13.worldOwned
      exact List.mem_append_left _ (List.mem_append_left _ ho_tab)
    · rcases hfix_from o ho_fix with ho_s | rfl
      · refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
        unfold worldOwned M13.worldOwned
        exact List.mem_append_left _ (List.mem_append_right _ ho_s)
      · exact Or.inr (Or.inr hin_new)
    · rw [hnd_part.2] at ho_nd
      refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
      unfold worldOwned M13.worldOwned
      exact List.mem_append_right _ ho_nd
  exact ⟨S, Nd, fun _ hx => hx, ⟨hT_post, hjr_part.2, hF_post, hTr_post⟩, hOG, hfr, trivial⟩

/-! ## 4. `BalListOrigin` preservation and `decCall` stepper for `lst_push` -/

private theorem balListOrigin_preserved_of_grow {F : Type}
    {s0 m post : PanSemStateFiniteExact 64 F}
    {l esz np cap : Nat}
    (hW : WorldOK s0)
    (hl_nz : l ≠ 0) (hesz : esz = 16 ∨ esz = 24 ∨ esz = 40)
    (horig_all : ∀ S Nd, WorldTypedWith s0 S Nd → LstOK s0 l ∧ BalListOrigin s0 l esz)
    (hAm : ArenaReady m)
    (hm_mem : m.memory = s0.memory)
    (hm_gl : ∀ k : MlS, k ≠ ofString "heap_ptr" → s0.globals.lookup k = m.globals.lookup k)
    (hnp_eq : np = globN s0 "heap_ptr")
    (hhp_m : globN m "heap_ptr" = np + 2 * esz * cap)
    (heff : M11.ByteRegionEffect m post [(np, 2 * esz * cap), (l, 24)])
    (S Nd : List Nat) (hWT : WorldTypedWith s0 S Nd) :
    BalListOrigin post l esz := by
  have hAs := hW.1
  have hinv_post : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAm.1
  have hAp : ArenaReady post := ⟨hinv_post, arenaOK_congr heff.globals hAm.2⟩
  have hglob_mp : ∀ nm, globN post nm = globN m nm := fun nm => by simp [globN, heff.globals]
  have hhp_post : globN post "heap_ptr" = np + 2 * esz * cap := by rw [hglob_mp, hhp_m]
  have hG : GlobalsKept ["heap_ptr"] s0 post := by
    intro g hg
    have hg_ne : g ≠ ofString "heap_ptr" := fun rfl => hg (List.mem_singleton.2 rfl)
    rw [heff.globals]; exact hm_gl g hg_ne
  have hgs : Wave8Contracts.M08.WorldGlobalsSame s0 post :=
    Wave8Contracts.M08.worldGlobalsSame_of_kept hG (by decide)
  obtain ⟨hlst, horig⟩ := horig_all S Nd hWT
  have hslice := balListOrigin_slice horig
  obtain ⟨hT, _, hF, _⟩ := hWT
  obtain ⟨hl_fix, _, _, had_dj, _, _⟩ := bal_list_slice_props hF hl_nz hesz hlst hslice
  have hnew_sz_eq : 2 * esz * cap = esz * (2 * cap) := by ring
  have hin_new : Inside (np, esz * (2 * cap)) (globN s0 "heap_ptr") (globN post "heap_ptr") :=
    ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hnp8 : np % 8 = 0 := by rw [hnp_eq]; exact hAs.2.2.2.2.2.2.1
  have hunhit_of_disj : ∀ i : Ivl, Allocated s0 i → Disj i (l, 24) →
      M08IvlUnhit s0 post i := by
    intro i hal_i hdj_l a ha8 hi1 hi2
    have hdj_n : Disj i (np, 2 * esz * cap) := by
      rw [hnew_sz_eq]
      exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_i hin_new)
    have hm_a := heff.cell_frame a (fun x hx hch => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨hc1, hc2⟩ := hch
      rcases hx with rfl | rfl
      · dsimp only at hc1 hc2; rcases hdj_n with d | d | d | d <;> omega
      · dsimp only at hc1 hc2; rcases hdj_l with d | d | d | d <;> omega)
    rw [hm_a, hm_mem]
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s0 t, M08IvlUnhit s0 post i := fun t ht i hi =>
    hunhit_of_disj i ((hT.2.1 t ht).2 i hi).1 (((hT.2.1 t ht).2 i hi).2 _ hl_fix)
  have hba_g : globN post "bal_accounts" = globN s0 "bal_accounts" :=
    hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  have hrecs_bal : balRecords post = balRecords s0 :=
    Wave8Contracts.M08.balRecords_eq_of_unhit hT hba_g (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_tab _ hm)
  have had_words : ∀ ad ∈ balRecords s0,
      (∀ off ∈ ([0, 16, 24, 32] : List Nat), memW post (ad + off) = memW s0 (ad + off)) ∧
      htabValues post (memW s0 ad) = htabValues s0 (memW s0 ad) := by
    intro ad had
    have had_fix : (ad, 40) ∈ fixedObjects s0 :=
      List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨ad, had, by simp⟩))
    rcases hF.1 _ had_fix with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_ad).2
    have had8 : ad % 8 = 0 := hw_ad.1
    have hu_ad := hunhit_of_disj _ hal_ad (had_dj ad had).1
    refine ⟨?_, Wave8Contracts.M08.htabValues_eq_of_unhit
      (hT.2.1 _ (hT.2.2.2.2.2.2.2.2.2.1 ad had).1).1
      (hu_tab _ (hT.2.2.2.2.2.2.2.2.2.1 ad had).1)⟩
    intro off hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl <;>
      exact Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_ad (by omega) hhi_ad ⟨by omega, by omega⟩
  rcases horig with ⟨ad, had, hwe⟩ | ⟨ad, had, hl_in, rfl⟩
  · left
    refine ⟨ad, by rw [hrecs_bal]; exact had, ?_⟩
    obtain ⟨hw, _⟩ := had_words ad had
    rw [hw 16 (by simp), hw 24 (by simp), hw 32 (by simp)]
    exact hwe
  · right
    obtain ⟨hw, hv⟩ := had_words ad had
    have hw0 : memW post ad = memW s0 ad := by simpa using hw 0 (by simp)
    exact ⟨ad, by rw [hrecs_bal]; exact had, by rw [hw0, hv]; exact hl_in, rfl⟩

private theorem balListOrigin_preserved_of_nogrow {F : Type}
    {s0 post : PanSemStateFiniteExact 64 F}
    {l esz : Nat}
    (hW : WorldOK s0)
    (hl_nz : l ≠ 0) (hesz : esz = 16 ∨ esz = 24 ∨ esz = 40)
    (horig_all : ∀ S Nd, WorldTypedWith s0 S Nd → LstOK s0 l ∧ BalListOrigin s0 l esz)
    (heff : M11.ByteRegionEffect s0 post [(l + 8, 8), (memW s0 l, esz * memW s0 (l + 16))])
    (S Nd : List Nat) (hWT : WorldTypedWith s0 S Nd) :
    BalListOrigin post l esz := by
  have hAs := hW.1
  have hG : GlobalsKept [] s0 post := fun _ _ => by rw [heff.globals]
  have hgs : Wave8Contracts.M08.WorldGlobalsSame s0 post :=
    Wave8Contracts.M08.worldGlobalsSame_of_kept hG (by simp)
  obtain ⟨hlst, horig⟩ := horig_all S Nd hWT
  have hslice := balListOrigin_slice horig
  obtain ⟨hT, _, hF, _⟩ := hWT
  obtain ⟨hl_fix, hp_fix, _, had_dj, _, _⟩ := bal_list_slice_props hF hl_nz hesz hlst hslice
  have hesz_pos : 0 < esz := by rcases hesz with rfl | rfl | rfl <;> decide
  have hpos_arr : esz * memW s0 (l + 16) ≠ 0 :=
    ne_of_gt (Nat.mul_pos hesz_pos (by have := hlst.1; omega))
  rcases hF.1 _ hp_fix with h0 | ⟨_, hw_p⟩
  · exact absurd h0 hpos_arr
  have hp8 : memW s0 l % 8 = 0 := hw_p.1
  have hunhit_of_disj : ∀ i : Ivl, Disj i (l, 24) → Disj i (memW s0 l, esz * memW s0 (l + 16)) →
      M08IvlUnhit s0 post i := by
    intro i hdj1 hdj2 a ha8 hi1 hi2
    exact heff.cell_frame a (fun x hx hch => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      obtain ⟨hc1, hc2⟩ := hch
      rcases hx with rfl | rfl
      · dsimp only at hc1 hc2; rcases hdj1 with d | d | d | d <;> omega
      · dsimp only at hc1 hc2; rcases hdj2 with d | d | d | d <;> omega)
  have hu_tab : ∀ t ∈ S, ∀ i ∈ htabFootprint s0 t, M08IvlUnhit s0 post i := fun t ht i hi =>
    hunhit_of_disj i (((hT.2.1 t ht).2 i hi).2 _ hl_fix) (((hT.2.1 t ht).2 i hi).2 _ hp_fix)
  have hba_g : globN post "bal_accounts" = globN s0 "bal_accounts" :=
    hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  have hrecs_bal : balRecords post = balRecords s0 :=
    Wave8Contracts.M08.balRecords_eq_of_unhit hT hba_g (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_tab _ hm)
  have had_words : ∀ ad ∈ balRecords s0,
      (∀ off ∈ ([0, 16, 24, 32] : List Nat), memW post (ad + off) = memW s0 (ad + off)) ∧
      htabValues post (memW s0 ad) = htabValues s0 (memW s0 ad) := by
    intro ad had
    have had_fix : (ad, 40) ∈ fixedObjects s0 :=
      List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨ad, had, by simp⟩))
    rcases hF.1 _ had_fix with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_ad).2
    have had8 : ad % 8 = 0 := hw_ad.1
    have hu_ad := hunhit_of_disj _ (had_dj ad had).1 (had_dj ad had).2
    refine ⟨?_, Wave8Contracts.M08.htabValues_eq_of_unhit
      (hT.2.1 _ (hT.2.2.2.2.2.2.2.2.2.1 ad had).1).1
      (hu_tab _ (hT.2.2.2.2.2.2.2.2.2.1 ad had).1)⟩
    intro off hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl <;>
      exact Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_ad (by omega) hhi_ad ⟨by omega, by omega⟩
  rcases horig with ⟨ad, had, hwe⟩ | ⟨ad, had, hl_in, rfl⟩
  · left
    refine ⟨ad, by rw [hrecs_bal]; exact had, ?_⟩
    obtain ⟨hw, _⟩ := had_words ad had
    rw [hw 16 (by simp), hw 24 (by simp), hw 32 (by simp)]
    exact hwe
  · right
    obtain ⟨hw, hv⟩ := had_words ad had
    have hw0 : memW post ad = memW s0 ad := by simpa using hw 0 (by simp)
    exact ⟨ad, by rw [hrecs_bal]; exact had, by rw [hw0, hv]; exact hl_in, rfl⟩

private theorem decCall_lst_push_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (x : MlS) (lExp eszExp : ExpHOL 64) (lw eszw : BitVec 64) (cont : ProgHOL 64)
    (hW : WorldOK s)
    (hev_l : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) lExp =
      some (.val (.word lw)))
    (hev_e : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) eszExp =
      some (.val (.word eszw)))
    (hesz : eszw.toNat = 16 ∨ eszw.toNat = 24 ∨ eszw.toNat = 40)
    (horig_nz : lw ≠ 0 → ∀ S Nd, WorldTypedWith s S Nd →
      LstOK s lw.toNat ∧ BalListOrigin s lw.toNat eszw.toNat)
    (hnt : (evaluateHOLFiniteState s
      (.decCall x .one (ofString "lst_push") [lExp, eszExp] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall x .one (ofString "lst_push") [lExp, eszExp] cont)).1) :
    ∃ (ew : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      lw ≠ 0 ∧
      WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid ∧
      WorldOK mid ∧
      (∀ S' Nd', WorldTypedWith mid S' Nd' →
        LstOK mid lw.toNat ∧ BalListOrigin mid lw.toNat eszw.toNat) ∧
      ew.toNat % 8 = 0 ∧
      sourceBase ≤ ew.toNat ∧
      ew.toNat + eszw.toNat ≤ heapEnd ∧
      memW mid lw.toNat ≤ ew.toNat ∧
      ew.toNat + eszw.toNat ≤ memW mid lw.toNat + eszw.toNat * memW mid (lw.toNat + 16) ∧
      mid.locals.lookup x = some (.val (.word ew)) ∧
      (∀ y, y ≠ x → mid.locals.lookup y = s.locals.lookup y) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "lst_push") [lExp, eszExp] cont)).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "lst_push") [lExp, eszExp] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) } := by
  have hG := hW.1.1
  have hAs := hW.1
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [lExp, eszExp] = some [.val (.word lw), .val (.word eszw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hev_l, hev_e]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "lst_push")
    (ofString "l") (ofString "esz") (sourceFnBody Guest.Software.guestFn_lst_push) lw eszw
    (by decide) (by rw [hG.code]; exact lookup_lst_push_add)
  rw [hargs] at hnt hres; dsimp only at hnt hres
  rw [hlk] at hnt hres; dsimp only at hnt hres
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at hnt; exact absurd rfl hnt
  · rw [if_neg hcz] at hnt hres
    let cmap := (HolFiniteMapExact.empty.update (ofString "l", ValueHOL.val (.word lw))).update
      (ofString "esz", ValueHOL.val (.word eszw))
    let ent := callEntryStateHOLFinite s cmap
    have hent_eq : ent = { s with locals := cmap, clock := s.clock - 1 } := rfl
    have hent_AR : ArenaReady ent := (arenaReady_with_locals s cmap (s.clock - 1)).2 hAs
    have hent_code : ent.code = originalRuntimeCode := hG.code
    have hent_ma : ent.memaddrs = ordinaryDomain := hG.memaddrs
    have hent_l : ent.locals.lookup (ofString "l") = some (.val (.word lw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "esz" ≠ ofString "l" by decide]
    have hent_e : ent.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    by_cases hlw0 : lw = 0
    · have hnot8 : ¬ ent.memaddrs 8#64 := by
        rw [hent_ma, Wave8Contracts.M08.ordinaryDomain_iff]
        have hsb : sourceBase = 2701131776 := rfl
        simp [hsb]
      have hbody_err : (evaluateHOLFiniteState ent
          (sourceFnBody Guest.Software.guestFn_lst_push)).1 = some .error := by
        dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_lst_push,
          InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
        rw [evaluateHOLFiniteState_dec_total]; dsimp only
        have hz_8 : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
        have hl0 : ent.locals.lookup (ofString "l") = some (.val (.word 0#64)) := by
          subst hlw0; exact hent_l
        have hev8 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "l"), .const 8#64])) = none := by
          simp [evalHOLExact, evalListHOLExact, hl0, valueIsWord, valueWord, wordOpHOL, wordOp,
            List.foldr, hz_8, memLoadHOLExact, hnot8]
        rw [hev8]
      rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_push) with ⟨rb, sb⟩
      rw [hrun] at hbody_err hres; dsimp only at hbody_err hres
      subst hbody_err
      exact absurd hres not_resumes_error
    · have hlw_nz_nat : lw.toNat ≠ 0 := fun h => hlw0 (BitVec.eq_of_toNat_eq (by simpa using h))
      obtain ⟨S0, hWT0_ex⟩ := hW.2
      obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
      obtain ⟨hlst0, horig0⟩ := horig_nz hlw0 S0 Nd0 hWT0
      have hslice0 := balListOrigin_slice horig0
      obtain ⟨hl_fix0, hp_fix0, _, _, _, _⟩ :=
        bal_list_slice_props hWT0.2.2.1 hlw_nz_nat hesz hlst0 hslice0
      have hesz_pos : 0 < eszw.toNat := by rcases hesz with h | h | h <;> omega
      have hpos_arr : eszw.toNat * memW s (lw.toNat + 16) ≠ 0 :=
        ne_of_gt (Nat.mul_pos hesz_pos (by have := hlst0.1; omega))
      rcases hWT0.2.2.1.1 _ hl_fix0 with h0 | ⟨hal_l, hw_l⟩
      · simp at h0
      rcases hWT0.2.2.1.1 _ hp_fix0 with h0 | ⟨hal_p, hw_p⟩
      · exact absurd h0 hpos_arr
      have hhe_264 : heapEnd < 2 ^ 64 := by decide
      have hlim_he : heapLimit ≤ heapEnd := by decide
      have hsb_ss : sourceBase ≤ scratchStart := by decide
      have hl_bnd : sourceBase ≤ lw.toNat ∧ lw.toNat + 24 ≤ heapEnd := by
        have hup := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_l).1
        rcases hal_l with h | h
        · exact ⟨h.1, hup⟩
        · exact ⟨le_trans hsb_ss (le_trans hAs.2.2.2.1 (le_trans hAs.2.2.2.2.1 h.1)), hup⟩
      have hp_bnd : sourceBase ≤ memW s lw.toNat ∧
          memW s lw.toNat + eszw.toNat * memW s (lw.toNat + 16) ≤ heapEnd := by
        have hup := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_p).1
        rcases hal_p with h | h
        · exact ⟨h.1, hup⟩
        · exact ⟨le_trans hsb_ss (le_trans hAs.2.2.2.1 (le_trans hAs.2.2.2.2.1 h.1)), hup⟩
      have hcap_mul_le : 1 * memW s (lw.toNat + 16) ≤ eszw.toNat * memW s (lw.toNat + 16) :=
        Nat.mul_le_mul_right _ hesz_pos
      let nw : BitVec 64 := BitVec.ofNat 64 (memW s (lw.toNat + 8))
      let capw : BitVec 64 := BitVec.ofNat 64 (memW s (lw.toNat + 16))
      let pw0 : BitVec 64 := BitVec.ofNat 64 (memW s lw.toNat)
      have hnw_toNat : nw.toNat = memW s (lw.toNat + 8) := by
        dsimp [nw]; rw [BitVec.toNat_ofNat]
        have := hlst0.2
        exact Nat.mod_eq_of_lt (by omega)
      have hcapw_toNat : capw.toNat = memW s (lw.toNat + 16) := by
        dsimp [capw]; rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by omega)
      have hpw0_toNat : pw0.toNat = memW s lw.toNat := by
        dsimp [pw0]; rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by omega)
      have hl0_bv : lw + 0#64 = BitVec.ofNat 64 lw.toNat := by simp
      have hl8_bv : lw + 8#64 = BitVec.ofNat 64 (lw.toNat + 8) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        rfl
      have hl16_bv : lw + 16#64 = BitVec.ofNat 64 (lw.toNat + 16) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        rfl
      have hl8_toNat : (lw + 8#64).toNat = lw.toNat + 8 := by
        rw [hl8_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hl16_toNat : (lw + 16#64).toNat = lw.toNat + 16 := by
        rw [hl16_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hdom_l0 : ent.memaddrs (lw + 0#64) := by
        rw [hent_ma, Wave8Contracts.M08.ordinaryDomain_iff]
        have : (lw + 0#64).toNat = lw.toNat := by simp
        rw [this]; exact ⟨hw_l.1, by omega, by omega⟩
      have hdom_l8 : ent.memaddrs (lw + 8#64) := by
        rw [hent_ma, Wave8Contracts.M08.ordinaryDomain_iff, hl8_toNat]
        exact ⟨by have := hw_l.1; omega, by omega, by omega⟩
      have hdom_l16 : ent.memaddrs (lw + 16#64) := by
        rw [hent_ma, Wave8Contracts.M08.ordinaryDomain_iff, hl16_toNat]
        exact ⟨by have := hw_l.1; omega, by omega, by omega⟩
      have hm_l0 : ent.memory (lw + 0#64) = .word pw0 := by
        change s.memory (lw + 0#64) = .word pw0
        rw [hl0_bv]; dsimp [pw0]; unfold memW
        rcases s.memory (BitVec.ofNat 64 lw.toNat) with ⟨w⟩; simp
      have hm_l8 : ent.memory (lw + 8#64) = .word nw := by
        change s.memory (lw + 8#64) = .word nw
        rw [hl8_bv]; dsimp [nw]; unfold memW
        rcases s.memory (BitVec.ofNat 64 (lw.toNat + 8)) with ⟨w⟩; simp
      have hm_l16 : ent.memory (lw + 16#64) = .word capw := by
        change s.memory (lw + 16#64) = .word capw
        rw [hl16_bv]; dsimp [capw]; unfold memW
        rcases s.memory (BitVec.ofNat 64 (lw.toNat + 16)) with ⟨w⟩; simp
      rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_push) with ⟨rb, sb⟩
      have hrun' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
          (sourceFnBody Guest.Software.guestFn_lst_push) = (rb, sb) := hrun
      rw [hrun'] at hnt hres
      cases rb with
      | none => exact absurd hres not_resumes_error
      | some rb' =>
        cases rb' with
        | timeOut => exact absurd rfl hnt
        | «break» | «continue» | error => exact absurd hres not_resumes_error
        | finalFfi _ =>
          exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        | exception e ev =>
          exfalso
          rcases hres with ⟨_, h⟩ | ⟨e', ev', h, hne⟩
          · simp at h
          · dsimp only at h; injection h with h'; injection h' with he1 he2; subst he1 he2
            exact lst_push_no_catchable_exn_add ent hent_code e ev hne (congrArg Prod.fst hrun)
        | returned vb =>
          -- Unfold the two `dec` headers (`n`, `cap`) of `guestFn_lst_push` on `hrun`:
          let e1 := setVarHOLFinite (ofString "n") (.val (.word nw)) ent
          let e2 := setVarHOLFinite (ofString "cap") (.val (.word capw)) e1
          let growProg : ProgHOL 64 :=
            .decCall (ofString "np") .one (ofString "alloc")
              [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2#64]]
              (.seq
                (.call (some (none, none)) (ofString "memcpy")
                  [.var .local (ofString "np"),
                   .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                   .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
                (.seq
                  (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np")))
                  (.store (.op .add [.var .local (ofString "l"), .const 16#64])
                    (.panop .mul [.var .local (ofString "cap"), .const 2#64]))))
          let tailProg : ProgHOL 64 :=
            .seq
              (.store (.op .add [.var .local (ofString "l"), .const 8#64])
                (.op .add [.var .local (ofString "n"), .const 1#64]))
              (.return (.op .add
                [.load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                 .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]))
          have hbody_e2 : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_push) =
              (let out := evaluateHOLFiniteState e2
                (.seq (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
                        growProg .skip)
                      tailProg);
               (out.1, { out.2 with
                 locals := HolFiniteMapExact.resVarEq
                   (HolFiniteMapExact.resVarEq out.2.locals (ofString "cap", e1.locals.lookup (ofString "cap")))
                   (ofString "n", ent.locals.lookup (ofString "n")) })) := by
            dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_lst_push,
              InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
              InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
              InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
              InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
              InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
              InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
            rw [evaluateHOLFiniteState_dec_total]; dsimp only
            have hz_8 : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
            have hz_16 : (16#64 : BitVec 64) + 0 = 16#64 := BitVec.add_zero _
            have hev1 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
                (.load .one (.op .add [.var .local (ofString "l"), .const 8#64])) =
                some (.val (.word nw)) := by
              simp only [evalHOLExact, evalListHOLExact, hent_l, valueIsWord, valueWord,
                wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_8,
                memLoadHOLExact, isWfShapeExactHOL, hdom_l8, hm_l8, ↓reduceIte]
            rw [hev1]; dsimp only
            rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
            have he1_def : setVarHOLFinite (ofString "n") (.val (.word nw)) ent = e1 := rfl
            rw [he1_def, evaluateHOLFiniteState_dec_total]; dsimp only
            have he1_l : e1.locals.lookup (ofString "l") = some (.val (.word lw)) := by
              simp [e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "n" ≠ ofString "l" by decide, hent_l]
            have he1_dom16 : e1.memaddrs (lw + 16#64) := hdom_l16
            have he1_m16 : e1.memory (lw + 16#64) = .word capw := hm_l16
            have hev2 : @evalHOLExact 64 F _ e1.toExact (fun a => Classical.propDecidable (e1.memaddrs a))
                (.load .one (.op .add [.var .local (ofString "l"), .const 16#64])) =
                some (.val (.word capw)) := by
              simp only [evalHOLExact, evalListHOLExact, he1_l, valueIsWord, valueWord,
                wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_16,
                memLoadHOLExact, isWfShapeExactHOL, he1_dom16, he1_m16, ↓reduceIte]
            rw [hev2]; dsimp only
            rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
          rw [hbody_e2] at hrun
          dsimp only at hrun
          rcases hout_e2 : evaluateHOLFiniteState e2
              (.seq (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
                      growProg .skip)
                    tailProg) with ⟨ro2, so2⟩
          rw [hout_e2] at hrun
          injection hrun with hro2 hsb_eq
          subst hro2
          have he2_eq : e2 = { s with locals := e2.locals, clock := s.clock - 1 } := by
            simp [e2, e1, setVarHOLFinite, hent_eq]
          have he2_AR : ArenaReady e2 := (arenaReady_with_locals s e2.locals (s.clock - 1)).2 hAs
          have he2_l : e2.locals.lookup (ofString "l") = some (.val (.word lw)) := by
            simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "cap" ≠ ofString "l" by decide,
              show ofString "n" ≠ ofString "l" by decide, hent_l]
          have he2_e : e2.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
            simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "cap" ≠ ofString "esz" by decide,
              show ofString "n" ≠ ofString "esz" by decide, hent_e]
          have he2_n : e2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
            simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "cap" ≠ ofString "n" by decide]
          have he2_c : e2.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
            simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hcmp_nl : @evalHOLExact 64 F _ e2.toExact (fun a => Classical.propDecidable (e2.memaddrs a))
              (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap"))) =
              some (.val (.word (if capw.toNat ≤ nw.toNat then 1#64 else 0#64))) := by
            simp only [evalHOLExact, he2_n, he2_c, Compiler.Encoders.Asm.wordCmpHOL,
              BitVec.ult, decide_eq_true_eq]
            by_cases hle : capw.toNat ≤ nw.toNat
            · have hlt_f : ¬ (nw < capw) := fun h => by
                have := (BitVec.lt_def).1 h; omega
              simp [hle, hlt_f]
            · have hlt_bv : nw < capw := (BitVec.lt_def).2 (by omega)
              simp [hle, hlt_bv]
          rw [evaluateHOLFiniteState_seq_line780] at hout_e2
          rcases hite_out : evaluateHOLFiniteState e2
              (.ite (.cmp .notLower (.var .local (ofString "n")) (.var .local (ofString "cap")))
                growProg .skip) with ⟨ri, si⟩
          rw [hite_out] at hout_e2
          cases ri with
          | some ri' =>
            dsimp only at hout_e2
            injection hout_e2 with hri _
            -- Neither `growProg` nor `skip` has a `return` statement!
            exfalso
            rw [evaluateHOLFiniteState_ite, hcmp_nl] at hite_out
            dsimp only at hite_out
            by_cases hgrow_cond : capw.toNat ≤ nw.toNat
            · rw [if_pos hgrow_cond, if_neg (by decide : (1#64 : BitVec 64) ≠ 0)] at hite_out
              -- Show `growProg` cannot return `some (.returned vb)` because its body ends in `.store`, not `.return`:
              have hgrow_nret : (evaluateHOLFiniteState e2 growProg).1 ≠ some (.returned vb) := by
                intro hgr
                have hgr_nt : (evaluateHOLFiniteState e2 growProg).1 ≠ some .timeOut := by
                  rw [hgr]; simp
                have hgr_res : Resumes (evaluateHOLFiniteState e2 growProg).1 :=
                  Or.inl ⟨vb, hgr⟩
                have hmul2_ev : @evalHOLExact 64 F _ e2.toExact
                    (fun a => Classical.propDecidable (e2.memaddrs a))
                    (.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2#64]) =
                    some (.val (.word (eszw * capw * 2#64))) := by
                  simp [evalHOLExact, evalListHOLExact, he2_e, he2_c, valueIsWord, valueWord, panOpHOL]
                obtain ⟨_, _, mid_a, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hg_eq1, _⟩ :=
                  decCall_alloc_resumes e2 (ofString "np") _ (eszw * capw * 2#64) _ he2_AR hmul2_ev hgr_nt hgr_res
                rw [hg_eq1] at hgr
                rw [evaluateHOLFiniteState_seq_line780] at hgr
                rcases hmc_o : evaluateHOLFiniteState mid_a
                  (.call (some (none, none)) (ofString "memcpy")
                    [.var .local (ofString "np"),
                     .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                     .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]]) with ⟨rmc, smc⟩
                rw [hmc_o] at hgr
                cases rmc with
                | some rmc' =>
                  dsimp only at hgr
                  -- void `.call (some (none, none))` never produces `some (.returned _)`!
                  rw [evaluateHOLFiniteState_call] at hmc_o
                  split at hmc_o <;> try (injection hmc_o with hr _; rw [← hr] at hgr; simp at hgr)
                  split at hmc_o <;> try (injection hmc_o with hr _; rw [← hr] at hgr; simp at hgr)
                  split at hmc_o <;> try (injection hmc_o with hr _; rw [← hr] at hgr; simp at hgr)
                  split at hmc_o <;> try (injection hmc_o with hr _; rw [← hr] at hgr; simp at hgr)
                  split at hmc_o <;> try (injection hmc_o with hr _; rw [← hr] at hgr; simp at hgr)
                  · rename_i hnotret _ _ _
                    exact hnotret vb hgr
                | none =>
                  dsimp only at hgr
                  rw [evaluateHOLFiniteState_seq_line780] at hgr
                  rcases hst1_o : evaluateHOLFiniteState smc
                    (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np"))) with ⟨rst1, sst1⟩
                  rw [hst1_o] at hgr
                  cases rst1 with
                  | some _ =>
                    dsimp only at hgr
                    rw [evaluateHOLFiniteState_store] at hst1_o
                    split at hst1_o <;> try (injection hst1_o with hr _; rw [← hr] at hgr; simp at hgr)
                    split at hst1_o <;> try (injection hst1_o with hr _; rw [← hr] at hgr; simp at hgr)
                    split at hst1_o <;> try (injection hst1_o with hr _; rw [← hr] at hgr; simp at hgr)
                  | none =>
                    dsimp only at hgr
                    rw [evaluateHOLFiniteState_store] at hgr
                    split at hgr <;> try simp at hgr
                    split at hgr <;> try simp at hgr
                    split at hgr <;> try simp at hgr
              exact hgrow_nret (by rw [hite_out, hri])
            · rw [if_neg hgrow_cond, if_pos (by decide : (0#64 : BitVec 64) = 0), evaluateHOLFiniteState_skip] at hite_out
              simp at hite_out
          | none =>
            dsimp only at hout_e2
            -- `hite_out` succeeded with `(none, si)` and `hout_e2 : evaluateHOLFiniteState si tailProg = (some (.returned vb), so2)`!
            rw [evaluateHOLFiniteState_ite, hcmp_nl] at hite_out
            dsimp only at hite_out
            by_cases hgrow_cond : capw.toNat ≤ nw.toNat
            · -- GROW BRANCH: `capw.toNat = nw.toNat` (since `nw.toNat ≤ capw.toNat` by `LstOK`)
              have hn_eq_cap : nw.toNat = capw.toNat := by
                have := hlst0.2; omega
              have hnw_eq_capw : nw = capw := BitVec.eq_of_toNat_eq hn_eq_cap
              rw [if_pos hgrow_cond, if_neg (by decide : (1#64 : BitVec 64) ≠ 0)] at hite_out
              -- Unfold `growProg` (`decCall "np" "alloc"` followed by `memcpy`, `[l+0]:=np`, `[l+16]:=cap*2`):
              change evaluateHOLFiniteState e2
                (.decCall (ofString "np") .one (ofString "alloc")
                  [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2#64]]
                  (.seq
                    (.call (some (none, none)) (ofString "memcpy")
                      [.var .local (ofString "np"),
                       .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                       .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
                    (.seq
                      (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np")))
                      (.store (.op .add [.var .local (ofString "l"), .const 16#64])
                        (.panop .mul [.var .local (ofString "cap"), .const 2#64]))))) = (none, si) at hite_out
              rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hite_out
              have hev_alloc : evalListHOLFinite e2 (h := fun a => Classical.propDecidable (e2.memaddrs a))
                  [.panop .mul [.panop .mul [.var .local (ofString "esz"), .var .local (ofString "cap")], .const 2#64]] =
                  some [.val (.word (eszw * capw * 2#64))] := by
                simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, he2_e, he2_c,
                  valueIsWord, valueWord, panOpHOL]
              have hlk_alloc := pan_one_word_lookup e2.code.lookup (ofString "alloc") (ofString "n")
                (sourceFnBody Guest.Software.guestFn_alloc) (eszw * capw * 2#64)
                (by rw [he2_AR.1.code]; exact R13Shards.lookup_alloc_r13)
              rw [hev_alloc] at hite_out; dsimp only at hite_out
              rw [hlk_alloc] at hite_out; dsimp only at hite_out
              by_cases hc_e2 : e2.clock = 0
              · rw [if_pos hc_e2] at hite_out; simp at hite_out
              · rw [if_neg hc_e2] at hite_out
                let cmap_a := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word (eszw * capw * 2#64)))
                let ent_a := callEntryStateHOLFinite e2 cmap_a
                have hent_a_AR : ArenaReady ent_a := (arenaReady_with_locals e2 cmap_a (e2.clock - 1)).2 he2_AR
                have hent_a_n : locN ent_a "n" = (eszw * capw * 2#64).toNat := by
                  simp [ent_a, cmap_a, locN, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                rcases hrun_a : evaluateHOLFiniteState ent_a (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ra, sa⟩
                have hrun_a' : evaluateHOLFiniteState (callEntryStateHOLFinite e2 cmap_a)
                    (sourceFnBody Guest.Software.guestFn_alloc) = (ra, sa) := hrun_a
                rw [hrun_a'] at hite_out
                cases ra with
                | none => simp at hite_out
                | some ra' =>
                  cases ra' with
                  | timeOut | «break» | «continue» | error | finalFfi _ | exception _ _ =>
                    simp at hite_out
                  | returned va =>
                    have hres_enta : Wave8Contracts.M12.Resumes
                        (evaluateHOLFiniteState ent_a (sourceFnBody Guest.Software.guestFn_alloc)).1 :=
                      Or.inl ⟨va, congrArg Prod.fst hrun_a⟩
                    obtain ⟨npw, qw, hrv_a, hnpw_eq, hqw_eq, hqw_lim, hqw8, hnpw_le_qw,
                      hsa_g, hsa_m, hsa_be, hsa_ma, hAsa, hsa_hp, hsa_sp⟩ :=
                      R13Shards.alloc_body_resumes_props ent_a he2_AR.1.code hent_a_AR hres_enta
                    rw [hrun_a] at hrv_a hsa_g hsa_m hsa_be hsa_ma hAsa hsa_hp hsa_sp
                    dsimp only at hrv_a hsa_g hsa_m hsa_be hsa_ma hAsa hsa_hp hsa_sp hite_out
                    injection hrv_a with hva; injection hva with hva'; subst hva'
                    rw [hent_a_n] at hqw_eq
                    have hsh_a : (shapeEqHOL (shapeOfHOLExact (.val (.word npw) : ValueHOL 64)) .one &&
                        shapeEqHOL (shapeOfHOLExact (.val (.word npw) : ValueHOL 64)) .one) = true := by
                      simp [shapeOfHOLExact, shapeEqHOL]
                    rw [if_pos hsh_a] at hite_out
                    let ma := setVarHOLFinite (ofString "np") (.val (.word npw)) { sa with locals := e2.locals }
                    have hma_AR : ArenaReady ma := (arenaReady_with_locals sa _ sa.clock).2 hAsa
                    have hma_m : ma.memory = s.memory := hsa_m
                    have hma_be : ma.be = s.be := hsa_be
                    have hma_ma : ma.memaddrs = ordinaryDomain := hsa_ma.trans hent_ma
                    have hma_code : ma.code = originalRuntimeCode := hma_AR.1.code
                    have hma_gl : ∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = ma.globals.lookup k := by
                      intro k hk1
                      change s.globals.lookup k = sa.globals.lookup k
                      have hent_a_gl : ent_a.globals = s.globals := rfl
                      rw [hsa_g, hent_a_gl]
                      simp [HolFiniteMapExact.lookup_update, FUPDATE, hk1, Ne.symm hk1]
                    have hnpw_eq_s : npw.toNat = globN s "heap_ptr" := hnpw_eq
                    have hnpw8 : npw.toNat % 8 = 0 := by rw [hnpw_eq_s]; exact hAs.2.2.2.2.2.2.1
                    -- Arithmetic: `eszw * capw < 2^64` (from `hp_bnd`), and `(eszw * capw * 2#64).toNat = 2 * eszw.toNat * capw.toNat`!
                    have hmul_ec_lt : eszw.toNat * capw.toNat < 2 ^ 64 := by
                      rw [hcapw_toNat]; omega
                    have hec_bv : (eszw * capw).toNat = eszw.toNat * capw.toNat := by
                      rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hmul_ec_lt]
                    have hmul2_lt : eszw.toNat * capw.toNat * 2 < 2 ^ 64 := by
                      rw [hcapw_toNat]
                      have hhe_val : heapEnd = 33806089704 := by decide
                      omega
                    have hmul2_toNat : (eszw * capw * 2#64).toNat = 2 * eszw.toNat * capw.toNat := by
                      rw [BitVec.toNat_mul, hec_bv]
                      have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
                      rw [h2, Nat.mod_eq_of_lt hmul2_lt]
                      ring
                    have hmul2_div : (2 * eszw.toNat * capw.toNat + 7) / 8 * 8 = 2 * eszw.toNat * capw.toNat := by
                      rcases hesz with h | h | h <;> (rw [h]; omega)
                    have hma_hp : globN ma "heap_ptr" = npw.toNat + 2 * eszw.toNat * capw.toNat := by
                      change globN sa "heap_ptr" = _
                      rw [hsa_hp, hqw_eq, hmul2_toNat, hmul2_div]
                    -- Step through `memcpy` + `[l+0] := np` + `[l+16] := cap * 2` on `ma`:
                    rcases hma_cont : evaluateHOLFiniteState ma
                      (.seq
                        (.call (some (none, none)) (ofString "memcpy")
                          [.var .local (ofString "np"),
                           .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                           .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])
                        (.seq
                          (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np")))
                          (.store (.op .add [.var .local (ofString "l"), .const 16#64])
                            (.panop .mul [.var .local (ofString "cap"), .const 2#64])))) with ⟨rg1, sg1⟩
                    rw [hma_cont] at hite_out
                    dsimp only at hite_out
                    injection hite_out with hrg1 hsi_eq
                    subst hrg1
                    rw [evaluateHOLFiniteState_seq_line780] at hma_cont
                    rcases hmc_out : evaluateHOLFiniteState ma
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "np"),
                         .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                         .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]]) with ⟨rmc, smc⟩
                    rw [hmc_out] at hma_cont
                    cases rmc with
                    | some _ => dsimp only at hma_cont; simp at hma_cont
                    | none =>
                      dsimp only at hma_cont
                      have hma_np : ma.locals.lookup (ofString "np") = some (.val (.word npw)) := by
                        simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                      have hma_l : ma.locals.lookup (ofString "l") = some (.val (.word lw)) := by
                        simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                          show ofString "np" ≠ ofString "l" by decide, he2_l]
                      have hma_e : ma.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
                        simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                          show ofString "np" ≠ ofString "esz" by decide, he2_e]
                      have hma_n : ma.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                        simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                          show ofString "np" ≠ ofString "n" by decide, he2_n]
                      have hma_c : ma.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
                        simp [ma, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                          show ofString "np" ≠ ofString "cap" by decide, he2_c]
                      have hma_dom0 : ma.memaddrs (lw + 0#64) := by rw [hma_ma, ← hent_ma]; exact hdom_l0
                      have hma_m0 : ma.memory (lw + 0#64) = .word pw0 := by rw [hma_m]; exact hm_l0
                      have hz_0 : (0#64 : BitVec 64) + 0 = 0#64 := rfl
                      have hev_mc_dst : @evalHOLExact 64 F _ ma.toExact (fun a => Classical.propDecidable (ma.memaddrs a))
                          (.var .local (ofString "np")) = some (.val (.word npw)) := by
                        simp [evalHOLExact, hma_np]
                      have hev_mc_src : @evalHOLExact 64 F _ ma.toExact (fun a => Classical.propDecidable (ma.memaddrs a))
                          (.load .one (.op .add [.var .local (ofString "l"), .const 0#64])) =
                          some (.val (.word pw0)) := by
                        simp only [evalHOLExact, evalListHOLExact, hma_l, valueIsWord, valueWord,
                          wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_0,
                          memLoadHOLExact, isWfShapeExactHOL, hma_dom0, hma_m0, ↓reduceIte]
                      have hev_mc_n : @evalHOLExact 64 F _ ma.toExact (fun a => Classical.propDecidable (ma.memaddrs a))
                          (.panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]) =
                          some (.val (.word (eszw * nw))) := by
                        simp [evalHOLExact, evalListHOLExact, hma_e, hma_n, valueIsWord, valueWord, panOpHOL]
                      let Rg : List Ivl := [(npw.toNat, 2 * eszw.toNat * capw.toNat), (lw.toNat, 24)]
                      have hmc_nt : (evaluateHOLFiniteState ma
                          (.call (some (none, none)) (ofString "memcpy")
                            [.var .local (ofString "np"),
                             .load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                             .panop .mul [.var .local (ofString "esz"), .var .local (ofString "n")]])).1 ≠
                          some .timeOut := by
                        rw [hmc_out]; simp
                      have hmc_bre_all := M11.eval_call_memcpy_bre ma _ _ _ npw pw0 (eszw * nw) Rg
                        hma_code hma_ma hev_mc_dst hev_mc_src hev_mc_n
                        (fun _ => by
                          refine ⟨(npw.toNat, 2 * eszw.toNat * capw.toNat), by simp [Rg], le_refl _, ?_⟩
                          dsimp only
                          rw [hnw_eq_capw, hec_bv]
                          nlinarith)
                        hmc_nt
                      obtain ⟨heff_mc, hsmc_loc⟩ := hmc_bre_all.1 (by rw [hmc_out])
                      rw [hmc_out] at heff_mc hsmc_loc
                      dsimp only at heff_mc hsmc_loc
                      -- Now `[l+0] := np` and `[l+16] := cap * 2` on `smc`:
                      rw [evaluateHOLFiniteState_seq_line780] at hma_cont
                      rcases hst0_out : evaluateHOLFiniteState smc
                        (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np"))) with ⟨rst0, sst0⟩
                      rw [hst0_out] at hma_cont
                      cases rst0 with
                      | some _ => dsimp only at hma_cont; simp at hma_cont
                      | none =>
                        dsimp only at hma_cont
                        have hsmc_ma : smc.memaddrs = ordinaryDomain := heff_mc.memaddrs.trans hma_ma
                        have hsmc_l : smc.locals.lookup (ofString "l") = some (.val (.word lw)) := by
                          rw [hsmc_loc]; exact hma_l
                        have hsmc_np : smc.locals.lookup (ofString "np") = some (.val (.word npw)) := by
                          rw [hsmc_loc]; exact hma_np
                        have hsmc_dom0 : smc.memaddrs (lw + 0#64) := by rw [hsmc_ma, ← hent_ma]; exact hdom_l0
                        have hsmc_dom0' : smc.memaddrs lw := by simpa using hsmc_dom0
                        have hev_st0_d : @evalHOLExact 64 F _ smc.toExact (fun a => Classical.propDecidable (smc.memaddrs a))
                            (.op .add [.var .local (ofString "l"), .const 0#64]) =
                            some (.val (.word (lw + 0#64))) := by
                          simp [evalHOLExact, evalListHOLExact, hsmc_l, valueIsWord, valueWord, wordOpHOL, wordOp]
                        have hev_st0_v : @evalHOLExact 64 F _ smc.toExact (fun a => Classical.propDecidable (smc.memaddrs a))
                            (.var .local (ofString "np")) = some (.val (.word npw)) := by
                          simp [evalHOLExact, hsmc_np]
                        have hst0_eq : evaluateHOLFiniteState smc
                            (.store (.op .add [.var .local (ofString "l"), .const 0#64]) (.var .local (ofString "np"))) =
                            (none, { smc with memory := fun a => if a = lw + 0#64 then .word npw else smc.memory a }) := by
                          rw [evaluateHOLFiniteState_store, hev_st0_d, hev_st0_v]; dsimp only
                          simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hsmc_dom0', FUPDATE]
                        obtain ⟨heff_st0, _⟩ := M11.ByteRegionEffect.of_store_word (Rl := Rg) hsmc_ma hst0_out
                          (fun v hv => by rw [hev_st0_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
                          (fun addr hdst _ => by
                            rw [hev_st0_d] at hdst; injection hdst with hd1; injection hd1 with hd2; injection hd2 with hd3
                            subst hd3
                            have : (lw + 0#64).toNat = lw.toNat := by simp
                            exact ⟨(lw.toNat, 24), by simp [Rg], by dsimp only; omega, by dsimp only; omega⟩)
                        have hsst0_eq : sst0 = { smc with memory := fun a => if a = lw + 0#64 then .word npw else smc.memory a } := by
                          rw [hst0_out] at hst0_eq; exact (Prod.mk.inj hst0_eq).2
                        have hsst0_ma : sst0.memaddrs = ordinaryDomain := heff_st0.memaddrs.trans hsmc_ma
                        have hsst0_loc : sst0.locals = ma.locals := by rw [hsst0_eq]; exact hsmc_loc
                        have hsst0_l : sst0.locals.lookup (ofString "l") = some (.val (.word lw)) := by
                          rw [hsst0_loc]; exact hma_l
                        have hsst0_c : sst0.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
                          rw [hsst0_loc]; exact hma_c
                        have hsst0_dom16 : sst0.memaddrs (lw + 16#64) := by rw [hsst0_ma, ← hent_ma]; exact hdom_l16
                        have hev_st16_d : @evalHOLExact 64 F _ sst0.toExact (fun a => Classical.propDecidable (sst0.memaddrs a))
                            (.op .add [.var .local (ofString "l"), .const 16#64]) =
                            some (.val (.word (lw + 16#64))) := by
                          simp [evalHOLExact, evalListHOLExact, hsst0_l, valueIsWord, valueWord, wordOpHOL, wordOp]
                        have hev_st16_v : @evalHOLExact 64 F _ sst0.toExact (fun a => Classical.propDecidable (sst0.memaddrs a))
                            (.panop .mul [.var .local (ofString "cap"), .const 2#64]) =
                            some (.val (.word (capw * 2#64))) := by
                          simp [evalHOLExact, evalListHOLExact, hsst0_c, valueIsWord, valueWord, panOpHOL]
                        have hst16_eq : evaluateHOLFiniteState sst0
                            (.store (.op .add [.var .local (ofString "l"), .const 16#64])
                              (.panop .mul [.var .local (ofString "cap"), .const 2#64])) =
                            (none, { sst0 with memory := fun a => if a = lw + 16#64 then .word (capw * 2#64) else sst0.memory a }) := by
                          rw [evaluateHOLFiniteState_store, hev_st16_d, hev_st16_v]; dsimp only
                          simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hsst0_dom16, FUPDATE]
                        obtain ⟨heff_st16, _⟩ := M11.ByteRegionEffect.of_store_word (Rl := Rg) hsst0_ma hma_cont
                          (fun v hv => by rw [hev_st16_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
                          (fun addr hdst _ => by
                            rw [hev_st16_d] at hdst; injection hdst with hd1; injection hd1 with hd2; injection hd2 with hd3
                            subst hd3
                            exact ⟨(lw.toNat, 24), by simp [Rg], by dsimp only; omega, by dsimp only; omega⟩)
                        have hsg1_eq : sg1 = { sst0 with memory := fun a => if a = lw + 16#64 then .word (capw * 2#64) else sst0.memory a } := by
                          rw [hma_cont] at hst16_eq; exact (Prod.mk.inj hst16_eq).2
                        -- Now step `tailProg` (`[l+8] := n + 1; return [l+0] + n * esz`) on `si`!
                        have hsi_ma : si.memaddrs = ordinaryDomain := by
                          rw [← hsi_eq]; exact heff_st16.memaddrs.trans hsst0_ma
                        have hsi_l : si.locals.lookup (ofString "l") = some (.val (.word lw)) := by
                          rw [← hsi_eq]; dsimp only
                          rw [PanRunBounded.resVarEq_lookup, if_neg (by decide), hsg1_eq]; exact hsst0_l
                        have hsi_n : si.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                          rw [← hsi_eq]; dsimp only
                          rw [PanRunBounded.resVarEq_lookup, if_neg (by decide), hsg1_eq, hsst0_loc]; exact hma_n
                        have hsi_e : si.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
                          rw [← hsi_eq]; dsimp only
                          rw [PanRunBounded.resVarEq_lookup, if_neg (by decide), hsg1_eq, hsst0_loc]; exact hma_e
                        have hsi_dom8 : si.memaddrs (lw + 8#64) := by rw [hsi_ma, ← hent_ma]; exact hdom_l8
                        have hsi_dom0 : si.memaddrs (lw + 0#64) := by rw [hsi_ma, ← hent_ma]; exact hdom_l0
                        dsimp only [tailProg] at hout_e2
                        rw [evaluateHOLFiniteState_seq_line780] at hout_e2
                        have hev_st8_d : @evalHOLExact 64 F _ si.toExact (fun a => Classical.propDecidable (si.memaddrs a))
                            (.op .add [.var .local (ofString "l"), .const 8#64]) =
                            some (.val (.word (lw + 8#64))) := by
                          simp [evalHOLExact, evalListHOLExact, hsi_l, valueIsWord, valueWord, wordOpHOL, wordOp]
                        have hev_st8_v : @evalHOLExact 64 F _ si.toExact (fun a => Classical.propDecidable (si.memaddrs a))
                            (.op .add [.var .local (ofString "n"), .const 1#64]) =
                            some (.val (.word (nw + 1#64))) := by
                          simp [evalHOLExact, evalListHOLExact, hsi_n, valueIsWord, valueWord, wordOpHOL, wordOp]
                        have hst8_eq : evaluateHOLFiniteState si
                            (.store (.op .add [.var .local (ofString "l"), .const 8#64])
                              (.op .add [.var .local (ofString "n"), .const 1#64])) =
                            (none, { si with memory := fun a => if a = lw + 8#64 then .word (nw + 1#64) else si.memory a }) := by
                          rw [evaluateHOLFiniteState_store, hev_st8_d, hev_st8_v]; dsimp only
                          simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hsi_dom8, FUPDATE]
                        rw [hst8_eq] at hout_e2
                        dsimp only at hout_e2
                        obtain ⟨heff_st8, _⟩ := M11.ByteRegionEffect.of_store_word (Rl := Rg) hsi_ma hst8_eq
                          (fun v hv => by rw [hev_st8_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
                          (fun addr hdst _ => by
                            rw [hev_st8_d] at hdst; injection hdst with hd1; injection hd1 with hd2; injection hd2 with hd3
                            subst hd3
                            exact ⟨(lw.toNat, 24), by simp [Rg], by dsimp only; omega, by dsimp only; omega⟩)
                        let st8 : PanSemStateFiniteExact 64 F :=
                          { si with memory := fun a => if a = lw + 8#64 then .word (nw + 1#64) else si.memory a }
                        have hne_0_16 : lw + 0#64 ≠ lw + 16#64 := by
                          intro h; have := congrArg BitVec.toNat h
                          have h0 : (lw + 0#64).toNat = lw.toNat := by simp
                          omega
                        have hne_0_8 : lw + 0#64 ≠ lw + 8#64 := by
                          intro h; have := congrArg BitVec.toNat h
                          have h0 : (lw + 0#64).toNat = lw.toNat := by simp
                          omega
                        have hne_16_8 : lw + 16#64 ≠ lw + 8#64 := by
                          intro h; have := congrArg BitVec.toNat h; omega
                        have hst8_m0 : st8.memory (lw + 0#64) = .word npw := by
                          dsimp [st8]; rw [if_neg hne_0_8, ← hsi_eq]; dsimp only
                          rw [hsg1_eq]; dsimp only; rw [if_neg hne_0_16, hsst0_eq]; simp
                        have hst8_m8 : st8.memory (lw + 8#64) = .word (nw + 1#64) := by
                          dsimp [st8]; simp
                        have hst8_m16 : st8.memory (lw + 16#64) = .word (capw * 2#64) := by
                          dsimp [st8]; rw [if_neg hne_16_8, ← hsi_eq]; dsimp only
                          rw [hsg1_eq]; simp
                        have hst8_dom0 : st8.memaddrs (lw + 0#64) := hsi_dom0
                        have hev_ret : @evalHOLExact 64 F _ st8.toExact (fun a => Classical.propDecidable (st8.memaddrs a))
                            (.op .add
                              [.load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                               .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]) =
                            some (.val (.word (npw + nw * eszw))) := by
                          have hz_0 : (0#64 : BitVec 64) + 0 = 0#64 := rfl
                          have hst8_l : st8.locals.lookup (ofString "l") = some (.val (.word lw)) := hsi_l
                          have hst8_n : st8.locals.lookup (ofString "n") = some (.val (.word nw)) := hsi_n
                          have hst8_e : st8.locals.lookup (ofString "esz") = some (.val (.word eszw)) := hsi_e
                          simp only [evalHOLExact, evalListHOLExact, hst8_l, hst8_n, hst8_e,
                            valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
                            List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_0,
                            memLoadHOLExact, isWfShapeExactHOL, hst8_dom0, hst8_m0, ↓reduceIte]
                          simp
                        rw [evaluateHOLFiniteState_return, hev_ret] at hout_e2
                        dsimp only at hout_e2
                        rw [if_pos (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])] at hout_e2
                        injection hout_e2 with hvb_eq hso2_eq
                        injection hvb_eq with hvb_ret
                        injection hvb_ret with hvb_val
                        subst hvb_val
                        let ew := npw + nw * eszw
                        have hsh_ew : (shapeEqHOL (shapeOfHOLExact (.val (.word ew) : ValueHOL 64)) .one &&
                            shapeEqHOL (shapeOfHOLExact (.val (.word ew) : ValueHOL 64)) .one) = true := by
                          simp [shapeOfHOLExact, shapeEqHOL]
                        dsimp only at hnt hres
                        rw [if_pos hsh_ew] at hnt hres
                        let mid := setVarHOLFinite x (.val (.word ew)) { sb with locals := s.locals }
                        -- Total `ByteRegionEffect ma mid Rg`:
                        have heff_si : M11.ByteRegionEffect ma si Rg := by
                          rw [← hsi_eq]
                          exact ((heff_mc.trans heff_st0).trans heff_st16).with_locals_clock _ sg1.clock
                        have heff_mid : M11.ByteRegionEffect ma mid Rg := by
                          have hmid_mem : mid = { st8 with locals := mid.locals, clock := mid.clock } := by
                            dsimp [mid]; rw [← hsb_eq, ← hso2_eq]; rfl
                          rw [hmid_mem]
                          exact (heff_si.trans heff_st8).with_locals_clock mid.locals mid.clock
                        have hmid_m0 : memW mid lw.toNat = npw.toNat := by
                          unfold memW; rw [← hl0_bv]
                          have hm_eq : mid.memory = st8.memory := by
                            dsimp [mid]; rw [← hsb_eq, ← hso2_eq]; rfl
                          rw [hm_eq, hst8_m0]
                        have hcap2_toNat : (capw * 2#64).toNat = 2 * capw.toNat := by
                          have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
                          have hc2_lt : capw.toNat * 2 < 2 ^ 64 := by
                            have : capw.toNat * 2 ≤ eszw.toNat * capw.toNat * 2 := by
                              have := Nat.mul_le_mul_right capw.toNat (show 1 ≤ eszw.toNat by omega)
                              omega
                            omega
                          rw [BitVec.toNat_mul, h2, Nat.mod_eq_of_lt hc2_lt]; omega
                        have hnp1_toNat : (nw + 1#64).toNat = nw.toNat + 1 := by
                          have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
                          have hn1_lt : nw.toNat + 1 < 2 ^ 64 := by omega
                          rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt hn1_lt]
                        have hmid_m8 : memW mid (lw.toNat + 8) = nw.toNat + 1 := by
                          unfold memW; rw [← hl8_bv]
                          have hm_eq : mid.memory = st8.memory := by
                            dsimp [mid]; rw [← hsb_eq, ← hso2_eq]; rfl
                          rw [hm_eq, hst8_m8]; exact hnp1_toNat
                        have hmid_m16 : memW mid (lw.toNat + 16) = 2 * capw.toNat := by
                          unfold memW; rw [← hl16_bv]
                          have hm_eq : mid.memory = st8.memory := by
                            dsimp [mid]; rw [← hsb_eq, ← hso2_eq]; rfl
                          rw [hm_eq, hst8_m16]; exact hcap2_toNat
                        have hcap_pos0 : 1 ≤ capw.toNat := by rw [hcapw_toNat]; exact hlst0.1
                        have hws_mid : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid :=
                          bal_list_grow_worldStep hW hlw_nz_nat hesz (horig_nz hlw0) hcapw_toNat.symm
                            hma_AR hma_m hma_be hma_gl hnpw_eq_s hma_hp heff_mid
                            hmid_m0 (by rw [hmid_m8, hn_eq_cap]; omega) hmid_m16
                        have hW_mid : WorldOK mid := worldOK_of_step hW hws_mid
                        have horig_mid : ∀ S' Nd', WorldTypedWith mid S' Nd' →
                            LstOK mid lw.toNat ∧ BalListOrigin mid lw.toNat eszw.toNat := by
                          intro S' Nd' hWT_m
                          -- Wait: `balListOrigin_preserved_of_grow` took `hWT : WorldTypedWith s0 S Nd`!
                          -- Is `BalListOrigin mid lw.toNat eszw.toNat` independent of `(S', Nd')`?
                          -- LOOK AT `BalListOrigin`: `BalListOrigin mid l esz` depends ONLY on `mid` (`balRecords mid`, `memW mid`, `htabValues mid`) — NOT on `S'` or `Nd'`!!
                          -- And `LstOK mid lw.toNat` ALSO depends ONLY on `mid` (`1 ≤ memW mid (l+16) ∧ memW mid (l+8) ≤ memW mid (l+16)`)!
                          refine ⟨⟨by rw [hmid_m16]; omega, by rw [hmid_m8, hmid_m16, hn_eq_cap]; omega⟩, ?_⟩
                          exact balListOrigin_preserved_of_grow hW hlw_nz_nat hesz (horig_nz hlw0)
                            hma_AR hma_m hma_gl hnpw_eq_s hma_hp heff_mid S0 Nd0 hWT0
                        -- Check `ew` bounds & alignment:
                        have hne_mul_toNat : (nw * eszw).toNat = nw.toNat * eszw.toNat := by
                          rw [BitVec.toNat_mul, hn_eq_cap, Nat.mul_comm, Nat.mod_eq_of_lt hmul_ec_lt]
                        have hnpw_hi_lim : npw.toNat + 2 * eszw.toNat * capw.toNat ≤ heapLimit := by
                          rw [← hma_hp]; exact hma_AR.2.2.1
                        have hce2_eq : capw.toNat * eszw.toNat + eszw.toNat ≤ 2 * eszw.toNat * capw.toNat := by
                          have hc1 : 1 ≤ capw.toNat := hcap_pos0
                          nlinarith
                        have hew_toNat : ew.toNat = npw.toNat + nw.toNat * eszw.toNat := by
                          change (npw + nw * eszw).toNat = _
                          rw [BitVec.toNat_add, hne_mul_toNat, Nat.mod_eq_of_lt (by rw [hn_eq_cap]; omega)]
                        have hew8 : ew.toNat % 8 = 0 := by
                          rw [hew_toNat]
                          have hmul8 : nw.toNat * eszw.toNat % 8 = 0 := by
                            rcases hesz with h | h | h <;> (rw [h]; omega)
                          omega
                        have hew_sb : sourceBase ≤ ew.toNat := by
                          rw [hew_toNat, hnpw_eq_s]; have := hAs.2.1; omega
                        have hew_he : ew.toNat + eszw.toNat ≤ heapEnd := by
                          rw [hew_toNat, hn_eq_cap]; omega
                        have hew_lo : memW mid lw.toNat ≤ ew.toNat := by
                          rw [hmid_m0, hew_toNat]; omega
                        have hew_hi : ew.toNat + eszw.toNat ≤
                            memW mid lw.toNat + eszw.toNat * memW mid (lw.toNat + 16) := by
                          rw [hmid_m0, hmid_m16, hew_toNat, hn_eq_cap]; nlinarith
                        have heval_eq : evaluateHOLFiniteState s
                            (.decCall x .one (ofString "lst_push") [lExp, eszExp] cont) =
                            ((evaluateHOLFiniteState mid cont).1,
                              { (evaluateHOLFiniteState mid cont).2 with
                                locals := HolFiniteMapExact.resVarEq
                                  (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) }) := by
                          rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]
                          dsimp only; rw [hlk]; dsimp only
                          rw [if_neg hcz, hrun']; dsimp only
                          rw [if_pos hsh_ew]
                        refine ⟨ew, mid, hlw0, hws_mid, hW_mid, horig_mid, hew8, hew_sb, hew_he,
                          hew_lo, hew_hi,
                          by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
                          fun y hy => by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hy, Ne.symm hy],
                          by intro hto; rw [hto] at hnt; exact hnt rfl,
                          hres, by rw [heval_eq], by rw [heval_eq]⟩
            · -- NO-GROW BRANCH (`nw.toNat < capw.toNat`):
              have hn_lt_cap : nw.toNat < capw.toNat := by omega
              rw [if_neg hgrow_cond, if_pos (by decide : (0#64 : BitVec 64) = 0), evaluateHOLFiniteState_skip] at hite_out
              injection hite_out with _ hsi_eq
              subst hsi_eq
              -- Step `tailProg` (`[l+8] := n + 1; return [l+0] + n * esz`) directly on `e2`:
              let Rn : List Ivl := [(lw.toNat + 8, 8), (memW s lw.toNat, eszw.toNat * memW s (lw.toNat + 16))]
              have he2_ma : e2.memaddrs = ordinaryDomain := hent_ma
              have he2_dom8 : e2.memaddrs (lw + 8#64) := hdom_l8
              have he2_dom0 : e2.memaddrs (lw + 0#64) := hdom_l0
              dsimp only [tailProg] at hout_e2
              rw [evaluateHOLFiniteState_seq_line780] at hout_e2
              have hev_st8_d : @evalHOLExact 64 F _ e2.toExact (fun a => Classical.propDecidable (e2.memaddrs a))
                  (.op .add [.var .local (ofString "l"), .const 8#64]) =
                  some (.val (.word (lw + 8#64))) := by
                simp [evalHOLExact, evalListHOLExact, he2_l, valueIsWord, valueWord, wordOpHOL, wordOp]
              have hev_st8_v : @evalHOLExact 64 F _ e2.toExact (fun a => Classical.propDecidable (e2.memaddrs a))
                  (.op .add [.var .local (ofString "n"), .const 1#64]) =
                  some (.val (.word (nw + 1#64))) := by
                simp [evalHOLExact, evalListHOLExact, he2_n, valueIsWord, valueWord, wordOpHOL, wordOp]
              have hst8_eq : evaluateHOLFiniteState e2
                  (.store (.op .add [.var .local (ofString "l"), .const 8#64])
                    (.op .add [.var .local (ofString "n"), .const 1#64])) =
                  (none, { e2 with memory := fun a => if a = lw + 8#64 then .word (nw + 1#64) else e2.memory a }) := by
                rw [evaluateHOLFiniteState_store, hev_st8_d, hev_st8_v]; dsimp only
                simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, he2_dom8, FUPDATE]
              rw [hst8_eq] at hout_e2
              dsimp only at hout_e2
              obtain ⟨heff_st8, _⟩ := M11.ByteRegionEffect.of_store_word (Rl := Rn) he2_ma hst8_eq
                (fun v hv => by rw [hev_st8_v] at hv; injection hv with hv'; exact ⟨_, hv'.symm⟩)
                (fun addr hdst _ => by
                  rw [hev_st8_d] at hdst; injection hdst with hd1; injection hd1 with hd2; injection hd2 with hd3
                  subst hd3
                  exact ⟨(lw.toNat + 8, 8), by simp [Rn], by dsimp only; omega, by dsimp only; omega⟩)
              let st8 : PanSemStateFiniteExact 64 F :=
                { e2 with memory := fun a => if a = lw + 8#64 then .word (nw + 1#64) else e2.memory a }
              have hne_0_8 : lw + 0#64 ≠ lw + 8#64 := by
                intro h; have := congrArg BitVec.toNat h
                have h0 : (lw + 0#64).toNat = lw.toNat := by simp
                omega
              have hne_16_8 : lw + 16#64 ≠ lw + 8#64 := by
                intro h; have := congrArg BitVec.toNat h; omega
              have hst8_m0 : st8.memory (lw + 0#64) = .word pw0 := by
                dsimp [st8]; rw [if_neg hne_0_8]; exact hm_l0
              have hst8_m8 : st8.memory (lw + 8#64) = .word (nw + 1#64) := by
                dsimp [st8]; simp
              have hst8_m16 : st8.memory (lw + 16#64) = .word capw := by
                dsimp [st8]; rw [if_neg hne_16_8]; exact hm_l16
              have hst8_dom0 : st8.memaddrs (lw + 0#64) := he2_dom0
              have hev_ret : @evalHOLExact 64 F _ st8.toExact (fun a => Classical.propDecidable (st8.memaddrs a))
                  (.op .add
                    [.load .one (.op .add [.var .local (ofString "l"), .const 0#64]),
                     .panop .mul [.var .local (ofString "n"), .var .local (ofString "esz")]]) =
                  some (.val (.word (pw0 + nw * eszw))) := by
                have hz_0 : (0#64 : BitVec 64) + 0 = 0#64 := rfl
                have hst8_l : st8.locals.lookup (ofString "l") = some (.val (.word lw)) := he2_l
                have hst8_n : st8.locals.lookup (ofString "n") = some (.val (.word nw)) := he2_n
                have hst8_e : st8.locals.lookup (ofString "esz") = some (.val (.word eszw)) := he2_e
                simp only [evalHOLExact, evalListHOLExact, hst8_l, hst8_n, hst8_e,
                  valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
                  List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_0,
                  memLoadHOLExact, isWfShapeExactHOL, hst8_dom0, hst8_m0, ↓reduceIte]
                simp
              rw [evaluateHOLFiniteState_return, hev_ret] at hout_e2
              dsimp only at hout_e2
              rw [if_pos (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])] at hout_e2
              injection hout_e2 with hvb_eq hso2_eq
              injection hvb_eq with hvb_ret
              injection hvb_ret with hvb_val
              subst hvb_val
              let ew := pw0 + nw * eszw
              have hsh_ew : (shapeEqHOL (shapeOfHOLExact (.val (.word ew) : ValueHOL 64)) .one &&
                  shapeEqHOL (shapeOfHOLExact (.val (.word ew) : ValueHOL 64)) .one) = true := by
                simp [shapeOfHOLExact, shapeEqHOL]
              dsimp only at hnt hres
              rw [if_pos hsh_ew] at hnt hres
              let mid := setVarHOLFinite x (.val (.word ew)) { sb with locals := s.locals }
              have heff_e2_mid : M11.ByteRegionEffect e2 mid Rn := by
                have hmid_mem : mid = { st8 with locals := mid.locals, clock := mid.clock } := by
                  dsimp [mid]; rw [← hsb_eq, ← hso2_eq]; rfl
                rw [hmid_mem]
                exact heff_st8.with_locals_clock mid.locals mid.clock
              have heff_s_e2 : M11.ByteRegionEffect s e2 Rn := by
                rw [he2_eq]
                exact (M11.ByteRegionEffect.refl s Rn).with_locals_clock e2.locals (s.clock - 1)
              have heff_mid : M11.ByteRegionEffect s mid Rn := heff_s_e2.trans heff_e2_mid
              have hnp1_toNat : (nw + 1#64).toNat = nw.toNat + 1 := by
                have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
                have hn1_lt : nw.toNat + 1 < 2 ^ 64 := by omega
                rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt hn1_lt]
              have hmid_m0 : memW mid lw.toNat = pw0.toNat := by
                unfold memW; rw [← hl0_bv]
                have hm_eq : mid.memory = st8.memory := by
                  dsimp [mid]; rw [← hsb_eq, ← hso2_eq]; rfl
                rw [hm_eq, hst8_m0]
              have hmid_m8 : memW mid (lw.toNat + 8) = nw.toNat + 1 := by
                unfold memW; rw [← hl8_bv]
                have hm_eq : mid.memory = st8.memory := by
                  dsimp [mid]; rw [← hsb_eq, ← hso2_eq]; rfl
                rw [hm_eq, hst8_m8]; exact hnp1_toNat
              have hmid_m16 : memW mid (lw.toNat + 16) = capw.toNat := by
                unfold memW; rw [← hl16_bv]
                have hm_eq : mid.memory = st8.memory := by
                  dsimp [mid]; rw [← hsb_eq, ← hso2_eq]; rfl
                rw [hm_eq, hst8_m16]
              have hslice_s : ∀ S Nd, WorldTypedWith s S Nd → LstOK s lw.toNat ∧ BalListSlice s lw.toNat eszw.toNat :=
                fun S Nd h => ⟨(horig_nz hlw0 S Nd h).1, balListOrigin_slice (horig_nz hlw0 S Nd h).2⟩
              have hws_nil : WorldStep (fun _ => []) [] stdKeep NoExtra s none mid :=
                bal_list_store_len_and_arr_worldStep hW hlw_nz_nat hesz hslice_s heff_mid
                  (by rw [← hcapw_toNat]; omega) hmid_m8
              have hws_mid : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid :=
                worldStep_nil_to_hp hws_nil
              have hW_mid : WorldOK mid := worldOK_of_step hW hws_mid
              have horig_mid : ∀ S' Nd', WorldTypedWith mid S' Nd' →
                  LstOK mid lw.toNat ∧ BalListOrigin mid lw.toNat eszw.toNat := by
                intro _ _ _
                refine ⟨⟨by rw [hmid_m16, hcapw_toNat]; exact hlst0.1,
                  by rw [hmid_m8, hmid_m16]; omega⟩, ?_⟩
                exact balListOrigin_preserved_of_nogrow hW hlw_nz_nat hesz (horig_nz hlw0)
                  heff_mid S0 Nd0 hWT0
              have hne_mul_lt : nw.toNat * eszw.toNat < eszw.toNat * memW s (lw.toNat + 16) := by
                rw [Nat.mul_comm]; exact Nat.mul_lt_mul_of_pos_left (by rw [← hcapw_toNat]; exact hn_lt_cap) hesz_pos
              have hne_mul_toNat : (nw * eszw).toNat = nw.toNat * eszw.toNat := by
                rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega)]
              have hew_hi_arr : pw0.toNat + nw.toNat * eszw.toNat + eszw.toNat ≤
                  memW s lw.toNat + eszw.toNat * memW s (lw.toNat + 16) := by
                rw [hpw0_toNat]
                have hle1 : nw.toNat + 1 ≤ memW s (lw.toNat + 16) := by rw [← hcapw_toNat]; omega
                have hmul1 : eszw.toNat * (nw.toNat + 1) ≤ eszw.toNat * memW s (lw.toNat + 16) :=
                  Nat.mul_le_mul_left _ hle1
                nlinarith
              have hew_toNat : ew.toNat = pw0.toNat + nw.toNat * eszw.toNat := by
                change (pw0 + nw * eszw).toNat = _
                rw [BitVec.toNat_add, hne_mul_toNat, Nat.mod_eq_of_lt (by rw [hpw0_toNat]; omega)]
              have hew8 : ew.toNat % 8 = 0 := by
                rw [hew_toNat, hpw0_toNat]
                have hp8 : memW s lw.toNat % 8 = 0 := hw_p.1
                have hmul8 : nw.toNat * eszw.toNat % 8 = 0 := by
                  rcases hesz with h | h | h <;> (rw [h]; omega)
                omega
              have hew_sb : sourceBase ≤ ew.toNat := by
                rw [hew_toNat, hpw0_toNat]; omega
              have hew_he : ew.toNat + eszw.toNat ≤ heapEnd := by
                rw [hew_toNat]; omega
              have hew_lo : memW mid lw.toNat ≤ ew.toNat := by
                rw [hmid_m0, hew_toNat]; omega
              have hew_hi : ew.toNat + eszw.toNat ≤
                  memW mid lw.toNat + eszw.toNat * memW mid (lw.toNat + 16) := by
                rw [hmid_m0, hmid_m16, hcapw_toNat, hew_toNat, hpw0_toNat]
                rw [hpw0_toNat] at hew_hi_arr; exact hew_hi_arr
              have heval_eq : evaluateHOLFiniteState s
                  (.decCall x .one (ofString "lst_push") [lExp, eszExp] cont) =
                  ((evaluateHOLFiniteState mid cont).1,
                    { (evaluateHOLFiniteState mid cont).2 with
                      locals := HolFiniteMapExact.resVarEq
                        (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) }) := by
                rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]
                dsimp only; rw [hlk]; dsimp only
                rw [if_neg hcz, hrun']; dsimp only
                rw [if_pos hsh_ew]
              refine ⟨ew, mid, hlw0, hws_mid, hW_mid, horig_mid, hew8, hew_sb, hew_he,
                hew_lo, hew_hi,
                by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
                fun y hy => by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hy, Ne.symm hy],
                by intro hto; rw [hto] at hnt; exact hnt rfl,
                hres, by rw [heval_eq], by rw [heval_eq]⟩

private theorem bal_list_store_arr_worldStep {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {l esz : Nat}
    (hW : WorldOK s)
    (hl_nz : l ≠ 0) (hesz : esz = 16 ∨ esz = 24 ∨ esz = 40)
    (horig_all : ∀ S Nd, WorldTypedWith s S Nd → LstOK s l ∧ BalListOrigin s l esz)
    (heff : M11.ByteRegionEffect s post [(memW s l, esz * memW s (l + 16))]) :
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s r post ∧
    WorldOK post ∧
    (∀ S Nd, WorldTypedWith post S Nd → LstOK post l ∧ BalListOrigin post l esz) := by
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  obtain ⟨hlst, horig⟩ := horig_all S0 Nd0 hWT0
  obtain ⟨hl_fix, hp_fix, hdj, _, _, _⟩ :=
    bal_list_slice_props hWT0.2.2.1 hl_nz hesz hlst (balListOrigin_slice horig)
  have hl_hi : l + 24 ≤ 2 ^ 64 := by
    rcases hWT0.2.2.1.1 _ hl_fix with h0 | ⟨hal, _⟩
    · simp at h0
    · exact (ivl_allocated_bound hW.1.2 hal).2
  have hl8 : l % 8 = 0 := by
    rcases hWT0.2.2.1.1 _ hl_fix with h0 | ⟨_, hw⟩
    · simp at h0
    · exact hw.1
  have hu : M08IvlUnhit s post (l, 24) := by
    intro a ha8 ha1 ha2
    apply heff.cell_frame a
    intro i hi hc
    have hi_eq := List.mem_singleton.1 hi
    subst i
    have hp8 : memW s l % 8 = 0 := by
      rcases hWT0.2.2.1.1 _ hp_fix with h0 | ⟨_, hw⟩
      · have hp : 0 < esz * memW s (l + 16) := by
          have he : 0 < esz := by rcases hesz with rfl | rfl | rfl <;> decide
          exact Nat.mul_pos he (by have := hlst.1; omega)
        omega
      · exact hw.1
    exact not_cellHits_of_disj ha8 hp8 ⟨ha1, ha2⟩ hdj hc
  have hm8 : memW post (l + 8) = memW s (l + 8) :=
    memW_eq_of_ivlUnhit hu (by omega) hl_hi ⟨by omega, by omega⟩
  have hm16 : memW post (l + 16) = memW s (l + 16) :=
    memW_eq_of_ivlUnhit hu (by omega) hl_hi ⟨by omega, by omega⟩
  have heff' : M11.ByteRegionEffect s post
      [(l + 8, 8), (memW s l, esz * memW s (l + 16))] :=
    heff.mono (by
      intro i hi
      exact ⟨i, List.mem_cons_of_mem _ hi, le_rfl, le_rfl⟩)
  have hstep : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s r post :=
    worldStep_nil_to_hp (bal_list_store_len_and_arr_worldStep hW hl_nz hesz
      (fun S Nd h => ⟨(horig_all S Nd h).1, balListOrigin_slice (horig_all S Nd h).2⟩)
      heff' hlst.2 hm8)
  refine ⟨hstep, worldOK_of_step hW hstep, fun _ _ _ => ⟨?_, ?_⟩⟩
  · exact ⟨by rw [hm16]; exact hlst.1, by rw [hm8, hm16]; exact hlst.2⟩
  · exact balListOrigin_preserved_of_nogrow hW hl_nz hesz horig_all heff' S0 Nd0 hWT0

/-! ## 4. `lst_upsert_idx` loop and `decCall` stepper -/

private def lstUpsertLoopBody : ProgHOL 64 :=
  .seq
    (.ite (.cmp .equal
        (.load .one (.op .add [.var .local (ofString "p"),
          .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
        (.var .local (ofString "idx")))
      (.return (.op .add [.var .local (ofString "p"),
        .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
      .skip)
    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))

private def lstUpsertLoop : ProgHOL 64 :=
  .while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) lstUpsertLoopBody

private theorem lst_upsert_loop_eval {F : Type}
    (s0 : PanSemStateFiniteExact 64 F)
    (lw nw pw eszw idxw : BitVec 64)
    (hcode0 : s0.code = originalRuntimeCode)
    (hma0 : s0.memaddrs = ordinaryDomain)
    (hesz : eszw.toNat = 16 ∨ eszw.toNat = 24 ∨ eszw.toNat = 40)
    (hlst : LstOK s0 lw.toNat)
    (hp_al : pw.toNat % 8 = 0 ∧ sourceBase ≤ pw.toNat ∧
      pw.toNat + eszw.toNat * memW s0 (lw.toNat + 16) ≤ heapEnd)
    (hn_eq : nw.toNat = memW s0 (lw.toNat + 8)) :
    ∀ (k : Nat) (t : PanSemStateFiniteExact 64 F) (iw : BitVec 64),
      t.clock = k →
      t = { s0 with locals := t.locals, clock := k } →
      iw.toNat ≤ nw.toNat →
      t.locals.lookup (ofString "n") = some (.val (.word nw)) →
      t.locals.lookup (ofString "p") = some (.val (.word pw)) →
      t.locals.lookup (ofString "esz") = some (.val (.word eszw)) →
      t.locals.lookup (ofString "idx") = some (.val (.word idxw)) →
      t.locals.lookup (ofString "i") = some (.val (.word iw)) →
      (evaluateHOLFiniteState t lstUpsertLoop).1 ≠ some .timeOut →
        ((evaluateHOLFiniteState t lstUpsertLoop).1 = none →
          (evaluateHOLFiniteState t lstUpsertLoop).2 =
            { s0 with locals := (evaluateHOLFiniteState t lstUpsertLoop).2.locals,
                      clock := (evaluateHOLFiniteState t lstUpsertLoop).2.clock } ∧
          (∀ y, y ≠ ofString "i" →
            (evaluateHOLFiniteState t lstUpsertLoop).2.locals.lookup y = t.locals.lookup y)) ∧
        (∀ rv, (evaluateHOLFiniteState t lstUpsertLoop).1 = some (.returned rv) →
          ∃ ew : BitVec 64, rv = .val (.word ew) ∧
            ew.toNat % 8 = 0 ∧
            sourceBase ≤ ew.toNat ∧
            ew.toNat + eszw.toNat ≤ heapEnd ∧
            pw.toNat ≤ ew.toNat ∧
            ew.toNat + eszw.toNat ≤ pw.toNat + eszw.toNat * memW s0 (lw.toNat + 16) ∧
            (evaluateHOLFiniteState t lstUpsertLoop).2 =
              { s0 with locals := HolFiniteMapExact.empty,
                        clock := (evaluateHOLFiniteState t lstUpsertLoop).2.clock }) ∧
        (∀ r, (evaluateHOLFiniteState t lstUpsertLoop).1 = some r →
          (∀ rv, r ≠ .returned rv) → ¬ Resumes (some r)) := by
  have hhe_263 : heapEnd < 2 ^ 63 := by decide
  have hhe_264 : heapEnd ≤ 2 ^ 64 := by decide
  have hesz_pos : 0 < eszw.toNat := by rcases hesz with h | h | h <;> omega
  have hcap_lt : memW s0 (lw.toNat + 16) < 2 ^ 63 := by
    have : 1 * memW s0 (lw.toNat + 16) ≤ eszw.toNat * memW s0 (lw.toNat + 16) :=
      Nat.mul_le_mul_right _ hesz_pos
    omega
  have hlst2 := hlst.2
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro t iw hclk ht_eq hi_le_n h_n h_p h_esz h_idx h_i hnt
    have ht_ma : t.memaddrs = ordinaryDomain := by rw [ht_eq]; exact hma0
    dsimp only [lstUpsertLoop] at hnt ⊢
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    have hcond : @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iw.toNat < nw.toNat then 1#64 else 0#64))) := by
      rw [evalHOLFinite_eq_toExact]
      simp only [evalHOLExact, h_i, h_n, Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small iw nw (by omega) (by omega), decide_eq_true_eq]
      by_cases hlt : iw.toNat < nw.toNat <;> simp [hlt]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hi_lt_n : iw.toNat < nw.toNat
    · rw [if_pos hi_lt_n] at hnt ⊢
      have h1nz : (1#64 : BitVec 64) ≠ 0 := by decide
      rw [if_pos h1nz] at hnt ⊢
      by_cases hk0 : t.clock = 0
      · rw [if_pos hk0] at hnt; exact absurd rfl hnt
      · rw [if_neg hk0] at hnt ⊢
        let td := decClockHOLFinite t
        have htd_eq : td = { s0 with locals := t.locals, clock := k - 1 } := by
          change decClockHOLFinite t = _; rw [ht_eq]; rfl
        have htd_ma : td.memaddrs = ordinaryDomain := by rw [htd_eq]; exact hma0
        have hmul_ie : (iw * eszw).toNat = iw.toNat * eszw.toNat := by
          rw [BitVec.toNat_mul]
          have : iw.toNat * eszw.toNat ≤ eszw.toNat * memW s0 (lw.toNat + 16) := by
            rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
          exact Nat.mod_eq_of_lt (by omega)
        have haddr_i : (pw + iw * eszw).toNat = pw.toNat + iw.toNat * eszw.toNat := by
          rw [BitVec.toNat_add, hmul_ie]
          have : iw.toNat * eszw.toNat ≤ eszw.toNat * memW s0 (lw.toNat + 16) := by
            rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
          exact Nat.mod_eq_of_lt (by omega)
        have hmul8 : (iw.toNat * eszw.toNat) % 8 = 0 := by
          rcases hesz with h | h | h <;> (rw [h]; omega)
        have hal_i : (pw + iw * eszw).toNat % 8 = 0 := by
          rw [haddr_i]; have := hp_al.1; omega
        have hi_hi : pw.toNat + iw.toNat * eszw.toNat + eszw.toNat ≤
            pw.toNat + eszw.toNat * memW s0 (lw.toNat + 16) := by
          have h1 : (iw.toNat + 1) * eszw.toNat ≤ memW s0 (lw.toNat + 16) * eszw.toNat :=
            Nat.mul_le_mul_right _ (by omega)
          nlinarith
        have hdom_i : td.memaddrs (pw + iw * eszw) := by
          rw [htd_ma, Wave8Contracts.M08.ordinaryDomain_iff]
          exact ⟨hal_i, by rw [haddr_i]; omega, by rw [haddr_i]; omega⟩
        obtain ⟨cw, hcw⟩ : ∃ cw, td.memory (pw + iw * eszw) = .word cw := by
          cases td.memory (pw + iw * eszw) with | word cw => exact ⟨cw, rfl⟩
        have hl_p : td.locals.lookup (ofString "p") = some (.val (.word pw)) := h_p
        have hl_i : td.locals.lookup (ofString "i") = some (.val (.word iw)) := h_i
        have hl_e : td.locals.lookup (ofString "esz") = some (.val (.word eszw)) := h_esz
        have hl_x : td.locals.lookup (ofString "idx") = some (.val (.word idxw)) := h_idx
        have hz_ie : iw * eszw + 0 = iw * eszw := BitVec.add_zero _
        have hev_addr : @evalHOLExact 64 F _ td.toExact (fun a => Classical.propDecidable (td.memaddrs a))
            (.op .add [.var .local (ofString "p"),
              .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]) =
            some (.val (.word (pw + iw * eszw))) := by
          simp only [evalHOLExact, evalListHOLExact, hl_p, hl_i, hl_e,
            valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
            List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, hz_ie]
        have hev_cmp : @evalHOLExact 64 F _ td.toExact (fun a => Classical.propDecidable (td.memaddrs a))
            (.cmp .equal (.load .one (.op .add [.var .local (ofString "p"),
              .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
              (.var .local (ofString "idx"))) =
            some (.val (.word (if cw = idxw then 1#64 else 0#64))) := by
          simp only [evalHOLExact, evalListHOLExact, hl_p, hl_i, hl_e, hl_x,
            valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
            memLoadHOLExact, isWfShapeExactHOL, List.all, List.map, Option.map,
            Bool.and_self, List.foldr, hz_ie, hdom_i, hcw, ↓reduceIte,
            Compiler.Encoders.Asm.wordCmpHOL, decide_eq_true_eq]
          by_cases hci : cw = idxw <;> simp [hci]
        have hbody_unfold := evaluateHOLFiniteState_seq_line780 td
          (.ite (.cmp .equal
              (.load .one (.op .add [.var .local (ofString "p"),
                .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
              (.var .local (ofString "idx")))
            (.return (.op .add [.var .local (ofString "p"),
              .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
            .skip)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))
        by_cases hmatch : cw = idxw
        · have hite1 : evaluateHOLFiniteState td
              (.ite (.cmp .equal
                  (.load .one (.op .add [.var .local (ofString "p"),
                    .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
                  (.var .local (ofString "idx")))
                (.return (.op .add [.var .local (ofString "p"),
                  .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
                .skip) =
              (some (.returned (.val (.word (pw + iw * eszw)))), emptyLocalsHOLFinite td) := by
            rw [evaluateHOLFiniteState_ite, hev_cmp, if_pos hmatch]
            dsimp only
            have h0ne : (1#64 : BitVec 64) ≠ 0 := by decide
            rw [if_neg (by decide : ¬ (1#64 : BitVec 64) = 0)]
            rw [evaluateHOLFiniteState_return, hev_addr]; dsimp only
            rw [if_pos (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])]
          have hbody_ret : evaluateHOLFiniteState td lstUpsertLoopBody =
              (some (.returned (.val (.word (pw + iw * eszw)))), emptyLocalsHOLFinite td) := by
            dsimp only [lstUpsertLoopBody]; rw [hbody_unfold, hite1]
          rw [show t.decClockHOLFinite = td from rfl, hbody_ret]
          dsimp only
          refine ⟨fun h => by simp at h, fun rv hrv => ?_, fun r hr hne => ?_⟩
          · injection hrv with hrv'; injection hrv' with hrv''; subst hrv''
            refine ⟨pw + iw * eszw, rfl, hal_i, by rw [haddr_i]; omega, by rw [haddr_i]; omega,
              by rw [haddr_i]; omega, by rw [haddr_i]; exact hi_hi, ?_⟩
            simp only [emptyLocalsHOLFinite]; rw [htd_eq]; rfl
          · injection hr with hr'; subst hr'; exact absurd rfl (hne _)
        · have hite0 : evaluateHOLFiniteState td
              (.ite (.cmp .equal
                  (.load .one (.op .add [.var .local (ofString "p"),
                    .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
                  (.var .local (ofString "idx")))
                (.return (.op .add [.var .local (ofString "p"),
                  .panop .mul [.var .local (ofString "i"), .var .local (ofString "esz")]]))
                .skip) = (none, td) := by
            rw [evaluateHOLFiniteState_ite, hev_cmp, if_neg hmatch]
            dsimp only
            rw [if_pos (by decide : (0#64 : BitVec 64) = 0)]
            exact evaluateHOLFiniteState_skip td
          have hasgn : evaluateHOLFiniteState td
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])) =
              (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) td) := by
            rw [evaluateHOLFiniteState_assign]
            have hz_1 : (1#64 : BitVec 64) + 0 = 1#64 := BitVec.add_zero _
            have hev_add : @evalHOLExact 64 F _ td.toExact (fun a => Classical.propDecidable (td.memaddrs a))
                (.op .add [.var .local (ofString "i"), .const 1#64]) =
                some (.val (.word (iw + 1#64))) := by
              simp only [evalHOLExact, evalListHOLExact, hl_i, valueIsWord, valueWord,
                wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte,
                List.foldr, hz_1]
            rw [hev_add]; dsimp only
            have hval_i : isValidValueHOLFinite td .local (ofString "i") (.val (.word (iw + 1#64))) = true := by
              simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hl_i, shapeEqHOL, shapeOfHOLExact]
            rw [if_pos hval_i]; rfl
          have hbody_step : evaluateHOLFiniteState td lstUpsertLoopBody =
              (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) td) := by
            dsimp only [lstUpsertLoopBody]; rw [hbody_unfold, hite0]; exact hasgn
          rw [show t.decClockHOLFinite = td from rfl, hbody_step] at hnt ⊢; dsimp only at hnt ⊢
          let t' : PanSemStateFiniteExact 64 F :=
            setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) td
          have ht'_clk : t'.clock < k := by
            simp [t', setVarHOLFinite, td, decClockHOLFinite, hclk]; omega
          have ht'_eq : t' = { s0 with locals := t'.locals, clock := t'.clock } := by
            simp [t', setVarHOLFinite, htd_eq]
          have hiw1_le : (iw + 1#64).toNat ≤ nw.toNat := by
            rw [BitVec.toNat_add]; change (iw.toNat + 1) % 2 ^ 64 ≤ nw.toNat
            rw [Nat.mod_eq_of_lt (by omega)]; omega
          have hrec := ih t'.clock ht'_clk t' (iw + 1#64) rfl ht'_eq hiw1_le
            (by simp [t', setVarHOLFinite, td, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "n" by decide, h_n])
            (by simp [t', setVarHOLFinite, td, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "p" by decide, h_p])
            (by simp [t', setVarHOLFinite, td, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "esz" by decide, h_esz])
            (by simp [t', setVarHOLFinite, td, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "idx" by decide, h_idx])
            (by simp [t', setVarHOLFinite, td, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
            hnt
          refine ⟨fun hnone => ?_, hrec.2.1, hrec.2.2⟩
          obtain ⟨heq_st, hloc_y⟩ := hrec.1 hnone
          refine ⟨heq_st, fun y hy => (hloc_y y hy).trans ?_⟩
          simp [t', setVarHOLFinite, td, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            hy, Ne.symm hy]
    · rw [if_neg hi_lt_n] at hnt ⊢
      rw [if_neg (by decide)] at hnt ⊢
      exact ⟨fun _ => ⟨by rw [← hclk] at ht_eq; exact ht_eq, fun _ _ => rfl⟩,
        fun _ h => by simp at h, fun _ h => by simp at h⟩

private theorem decCall_lst_upsert_idx_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (x : MlS) (lExp eszExp idxExp : ExpHOL 64) (lw eszw idxw : BitVec 64) (cont : ProgHOL 64)
    (hW : WorldOK s)
    (hev_l : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) lExp =
      some (.val (.word lw)))
    (hev_e : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) eszExp =
      some (.val (.word eszw)))
    (hev_i : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) idxExp =
      some (.val (.word idxw)))
    (hesz : eszw.toNat = 16 ∨ eszw.toNat = 24 ∨ eszw.toNat = 40)
    (horig_nz : lw ≠ 0 → ∀ S Nd, WorldTypedWith s S Nd →
      LstOK s lw.toNat ∧ BalListOrigin s lw.toNat eszw.toNat)
    (hnt : (evaluateHOLFiniteState s
      (.decCall x .one (ofString "lst_upsert_idx") [lExp, eszExp, idxExp] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall x .one (ofString "lst_upsert_idx") [lExp, eszExp, idxExp] cont)).1) :
    ∃ (ew : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      lw ≠ 0 ∧
      WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid ∧
      WorldOK mid ∧
      (∀ S' Nd', WorldTypedWith mid S' Nd' →
        LstOK mid lw.toNat ∧ BalListOrigin mid lw.toNat eszw.toNat) ∧
      ew.toNat % 8 = 0 ∧
      sourceBase ≤ ew.toNat ∧
      ew.toNat + eszw.toNat ≤ heapEnd ∧
      memW mid lw.toNat ≤ ew.toNat ∧
      ew.toNat + eszw.toNat ≤ memW mid lw.toNat + eszw.toNat * memW mid (lw.toNat + 16) ∧
      mid.locals.lookup x = some (.val (.word ew)) ∧
      (∀ y, y ≠ x → mid.locals.lookup y = s.locals.lookup y) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "lst_upsert_idx") [lExp, eszExp, idxExp] cont)).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "lst_upsert_idx") [lExp, eszExp, idxExp] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) } := by
  have hG := hW.1.1
  have hAs := hW.1
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [lExp, eszExp, idxExp] = some [.val (.word lw), .val (.word eszw), .val (.word idxw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hev_l, hev_e, hev_i]
  have hlk := pan_three_word_lookup s.code.lookup (ofString "lst_upsert_idx")
    (ofString "l") (ofString "esz") (ofString "idx")
    (sourceFnBody Guest.Software.guestFn_lst_upsert_idx) lw eszw idxw
    (by decide) (by decide) (by decide) (by rw [hG.code]; exact lookup_lst_upsert_idx_add)
  rw [hargs] at hnt hres; dsimp only at hnt hres
  rw [hlk] at hnt hres; dsimp only at hnt hres
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at hnt; exact absurd rfl hnt
  · rw [if_neg hcz] at hnt hres
    let cmap := ((HolFiniteMapExact.empty.update (ofString "l", ValueHOL.val (.word lw))).update
      (ofString "esz", ValueHOL.val (.word eszw))).update
      (ofString "idx", ValueHOL.val (.word idxw))
    let ent := callEntryStateHOLFinite s cmap
    have hent_eq : ent = { s with locals := cmap, clock := s.clock - 1 } := rfl
    have hent_ma : ent.memaddrs = ordinaryDomain := hG.memaddrs
    have hent_l : ent.locals.lookup (ofString "l") = some (.val (.word lw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "idx" ≠ ofString "l" by decide, show ofString "esz" ≠ ofString "l" by decide]
    have hent_e : ent.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "idx" ≠ ofString "esz" by decide]
    have hent_i : ent.locals.lookup (ofString "idx") = some (.val (.word idxw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    by_cases hlw0 : lw = 0
    · have hnot8 : ¬ ent.memaddrs 8#64 := by
        rw [hent_ma, Wave8Contracts.M08.ordinaryDomain_iff]
        have hsb : sourceBase = 2701131776 := rfl
        simp [hsb]
      have hbody_err : (evaluateHOLFiniteState ent
          (sourceFnBody Guest.Software.guestFn_lst_upsert_idx)).1 = some .error := by
        dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_lst_upsert_idx,
          InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
        rw [evaluateHOLFiniteState_dec_total]; dsimp only
        have hz_8 : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
        have hl0 : ent.locals.lookup (ofString "l") = some (.val (.word 0#64)) := by
          subst hlw0; exact hent_l
        have hev8 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "l"), .const 8#64])) = none := by
          simp [evalHOLExact, evalListHOLExact, hl0, valueIsWord, valueWord, wordOpHOL, wordOp,
            List.foldr, hz_8, memLoadHOLExact, hnot8]
        rw [hev8]
      rcases hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_upsert_idx) with ⟨rb, sb⟩
      have hrun' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
          (sourceFnBody Guest.Software.guestFn_lst_upsert_idx) = (rb, sb) := hrun
      rw [hrun] at hbody_err; rw [hrun'] at hres; dsimp only at hbody_err hres
      subst rb; exact absurd hres not_resumes_error
    · have hlw_nz_nat : lw.toNat ≠ 0 := fun h => hlw0 (BitVec.eq_of_toNat_eq (by simpa using h))
      obtain ⟨S0, hWT0_ex⟩ := hW.2
      obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
      obtain ⟨hlst0, horig0⟩ := horig_nz hlw0 S0 Nd0 hWT0
      obtain ⟨hl_fix0, hp_fix0, _, _, _, _⟩ :=
        bal_list_slice_props hWT0.2.2.1 hlw_nz_nat hesz hlst0 (balListOrigin_slice horig0)
      have hesz_pos : 0 < eszw.toNat := by rcases hesz with h | h | h <;> omega
      have hpos_arr : eszw.toNat * memW s (lw.toNat + 16) ≠ 0 :=
        ne_of_gt (Nat.mul_pos hesz_pos (by have := hlst0.1; omega))
      rcases hWT0.2.2.1.1 _ hl_fix0 with h0 | ⟨hal_l, hw_l⟩
      · simp at h0
      rcases hWT0.2.2.1.1 _ hp_fix0 with h0 | ⟨hal_p, hw_p⟩
      · exact absurd h0 hpos_arr
      have hhe_264 : heapEnd < 2 ^ 64 := by decide
      have hsb_ss : sourceBase ≤ scratchStart := by decide
      have hl_bnd : sourceBase ≤ lw.toNat ∧ lw.toNat + 24 ≤ heapEnd := by
        have hup := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_l).1
        rcases hal_l with h | h
        · exact ⟨h.1, hup⟩
        · exact ⟨le_trans hsb_ss (le_trans hAs.2.2.2.1 (le_trans hAs.2.2.2.2.1 h.1)), hup⟩
      have hp_bnd : sourceBase ≤ memW s lw.toNat ∧
          memW s lw.toNat + eszw.toNat * memW s (lw.toNat + 16) ≤ heapEnd := by
        have hup := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_p).1
        rcases hal_p with h | h
        · exact ⟨h.1, hup⟩
        · exact ⟨le_trans hsb_ss (le_trans hAs.2.2.2.1 (le_trans hAs.2.2.2.2.1 h.1)), hup⟩
      have hcap_mul_le : 1 * memW s (lw.toNat + 16) ≤ eszw.toNat * memW s (lw.toNat + 16) :=
        Nat.mul_le_mul_right _ hesz_pos
      let nw : BitVec 64 := BitVec.ofNat 64 (memW s (lw.toNat + 8))
      let pw0 : BitVec 64 := BitVec.ofNat 64 (memW s lw.toNat)
      have hnw_toNat : nw.toNat = memW s (lw.toNat + 8) := by
        dsimp [nw]; rw [BitVec.toNat_ofNat]
        have := hlst0.2; exact Nat.mod_eq_of_lt (by omega)
      have hpw0_toNat : pw0.toNat = memW s lw.toNat := by
        dsimp [pw0]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have hl0_bv : lw + 0#64 = BitVec.ofNat 64 lw.toNat := by simp
      have hl8_bv : lw + 8#64 = BitVec.ofNat 64 (lw.toNat + 8) := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; rfl
      have hl8_toNat : (lw + 8#64).toNat = lw.toNat + 8 := by
        rw [hl8_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hdom_l0 : ent.memaddrs (lw + 0#64) := by
        rw [hent_ma, Wave8Contracts.M08.ordinaryDomain_iff]
        have : (lw + 0#64).toNat = lw.toNat := by simp
        rw [this]; exact ⟨hw_l.1, by omega, by omega⟩
      have hdom_l8 : ent.memaddrs (lw + 8#64) := by
        rw [hent_ma, Wave8Contracts.M08.ordinaryDomain_iff, hl8_toNat]
        exact ⟨by have := hw_l.1; omega, by omega, by omega⟩
      have hm_l0 : ent.memory (lw + 0#64) = .word pw0 := by
        change s.memory (lw + 0#64) = .word pw0
        rw [hl0_bv]; dsimp [pw0]; unfold memW
        rcases s.memory (BitVec.ofNat 64 lw.toNat) with ⟨w⟩; simp
      have hm_l8 : ent.memory (lw + 8#64) = .word nw := by
        change s.memory (lw + 8#64) = .word nw
        rw [hl8_bv]; dsimp [nw]; unfold memW
        rcases s.memory (BitVec.ofNat 64 (lw.toNat + 8)) with ⟨w⟩; simp
      -- Step `dec "n"`, `dec "p"`, `dec "i"` on `ent`:
      let s_n : PanSemStateFiniteExact 64 F := setVarHOLFinite (ofString "n") (.val (.word nw)) ent
      let s_p : PanSemStateFiniteExact 64 F := setVarHOLFinite (ofString "p") (.val (.word pw0)) s_n
      let s_dec : PanSemStateFiniteExact 64 F := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s_p
      let tailProg : ProgHOL 64 :=
        .seq lstUpsertLoop
          (.decCall (ofString "e") .one (ofString "lst_push")
            [.var .local (ofString "l"), .var .local (ofString "esz")]
            (.seq (.store (.var .local (ofString "e")) (.var .local (ofString "idx")))
              (.return (.var .local (ofString "e")))))
      have hbody_step : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_upsert_idx) =
          (let out := evaluateHOLFiniteState s_dec tailProg;
           (out.1,
            { out.2 with
              locals := HolFiniteMapExact.resVarEq
                (HolFiniteMapExact.resVarEq
                  (HolFiniteMapExact.resVarEq out.2.locals (ofString "i", s_p.locals.lookup (ofString "i")))
                  (ofString "p", s_n.locals.lookup (ofString "p")))
                (ofString "n", ent.locals.lookup (ofString "n")) })) := by
        dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_lst_upsert_idx,
          InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
        rw [evaluateHOLFiniteState_dec_total]; dsimp only
        have hz_8 : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
        have hz_0 : (0#64 : BitVec 64) + 0 = 0#64 := BitVec.add_zero _
        have hev_n : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "l"), .const 8#64])) = some (.val (.word nw)) := by
          simp only [evalHOLExact, evalListHOLExact, hent_l, valueIsWord, valueWord, wordOpHOL, wordOp,
            List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_8, memLoadHOLExact,
            isWfShapeExactHOL, hdom_l8, hm_l8, ↓reduceIte]
        rw [hev_n]; dsimp only
        rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
        have hs_n_def : setVarHOLFinite (ofString "n") (.val (.word nw)) ent = s_n := rfl
        rw [hs_n_def, evaluateHOLFiniteState_dec_total]; dsimp only
        have hl_sn : s_n.locals.lookup (ofString "l") = some (.val (.word lw)) := by
          simp [s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "n" ≠ ofString "l" by decide, hent_l]
        have hev_p : @evalHOLExact 64 F _ s_n.toExact (fun a => Classical.propDecidable (s_n.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "l"), .const 0#64])) = some (.val (.word pw0)) := by
          have hd0 : s_n.memaddrs (lw + 0#64) := hdom_l0
          have hm0 : s_n.memory (lw + 0#64) = .word pw0 := hm_l0
          simp only [evalHOLExact, evalListHOLExact, hl_sn, valueIsWord, valueWord, wordOpHOL, wordOp,
            List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_0, memLoadHOLExact,
            isWfShapeExactHOL, hd0, hm0, ↓reduceIte]
        rw [hev_p]; dsimp only
        rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
        have hs_p_def : setVarHOLFinite (ofString "p") (.val (.word pw0)) s_n = s_p := rfl
        rw [hs_p_def, evaluateHOLFiniteState_dec_total]; dsimp only
        have hev_i0 : @evalHOLExact 64 F _ s_p.toExact (fun a => Classical.propDecidable (s_p.memaddrs a))
            (.const 0#64) = some (.val (.word 0#64)) := rfl
        rw [hev_i0]; dsimp only
        rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
        rfl
      have hrun' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
          (sourceFnBody Guest.Software.guestFn_lst_upsert_idx) =
          evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_lst_upsert_idx) := rfl
      have hnt_tail : (evaluateHOLFiniteState s_dec tailProg).1 ≠ some .timeOut := by
        intro hto
        have hfst : (evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
            (sourceFnBody Guest.Software.guestFn_lst_upsert_idx)).1 = some .timeOut := by
          rw [hrun', hbody_step]; dsimp only; exact hto
        rw [hfst] at hnt; exact hnt rfl
      have hnt_loop : (evaluateHOLFiniteState s_dec lstUpsertLoop).1 ≠ some .timeOut := by
        intro hto
        apply hnt_tail
        dsimp only [tailProg]; rw [evaluateHOLFiniteState_seq_line780]
        rcases hlp0 : evaluateHOLFiniteState s_dec lstUpsertLoop with ⟨rl0, sl0⟩
        rw [hlp0] at hto; dsimp only at hto; subst rl0; rfl
      have hs_dec_eq : s_dec = { s with locals := s_dec.locals, clock := s_dec.clock } := by
        simp [s_dec, s_p, s_n, setVarHOLFinite, hent_eq]
      have hloop := lst_upsert_loop_eval s lw nw pw0 eszw idxw hG.code hG.memaddrs hesz hlst0
        ⟨by simpa [hpw0_toNat] using hw_p.1,
         by simpa [hpw0_toNat] using hp_bnd.1,
         by simpa [hpw0_toNat] using hp_bnd.2⟩
        hnw_toNat s_dec.clock s_dec 0#64 rfl hs_dec_eq (by simp)
        (by simp [s_dec, s_p, s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "n" by decide, show ofString "p" ≠ ofString "n" by decide])
        (by simp [s_dec, s_p, s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "p" by decide])
        (by simp [s_dec, s_p, s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "esz" by decide, show ofString "p" ≠ ofString "esz" by decide,
          show ofString "n" ≠ ofString "esz" by decide, hent_e])
        (by simp [s_dec, s_p, s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "idx" by decide, show ofString "p" ≠ ofString "idx" by decide,
          show ofString "n" ≠ ofString "idx" by decide, hent_i])
        (by simp [s_dec, s_p, s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        hnt_loop
      rcases hlp_ev : evaluateHOLFiniteState s_dec lstUpsertLoop with ⟨rl, sl⟩
      rw [hlp_ev] at hloop; dsimp only at hloop
      cases rl with
      | some rl' =>
        -- Either loop returned `ew`, or non-resumable error
        have htail_ev : evaluateHOLFiniteState s_dec tailProg = (some rl', sl) := by
          dsimp only [tailProg]; rw [evaluateHOLFiniteState_seq_line780, hlp_ev]
        by_cases hret : ∃ rv, rl' = .returned rv
        · rcases hret with ⟨rv, rfl⟩
          obtain ⟨ew, rfl, hew8, hew_sb, hew_he, hew_lo, hew_hi, hsl_eq⟩ := hloop.2.1 rv rfl
          let sl_rest : PanSemStateFiniteExact 64 F :=
            { sl with
              locals := HolFiniteMapExact.resVarEq
                (HolFiniteMapExact.resVarEq
                  (HolFiniteMapExact.resVarEq sl.locals (ofString "i", s_p.locals.lookup (ofString "i")))
                  (ofString "p", s_n.locals.lookup (ofString "p")))
                (ofString "n", ent.locals.lookup (ofString "n")) }
          have hbody_ret : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
              (sourceFnBody Guest.Software.guestFn_lst_upsert_idx) =
              (some (.returned (.val (.word ew))), sl_rest) := by
            rw [hrun', hbody_step]; dsimp only; rw [htail_ev]
          let mid := setVarHOLFinite x (.val (.word ew)) { s with clock := sl.clock }
          have hsl_rest_s : { sl_rest with locals := s.locals } = { s with clock := sl.clock } := by
            dsimp only [sl_rest]; rw [hsl_eq]
          have hmid_eq : setVarHOLFinite x (.val (.word ew)) { sl_rest with locals := s.locals } = mid := by
            rw [hsl_rest_s]
          have hsh_ew : (shapeEqHOL (shapeOfHOLExact (.val (.word ew) : ValueHOL 64)) .one &&
              shapeEqHOL (shapeOfHOLExact (.val (.word ew) : ValueHOL 64)) .one) = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          have heval_eq : evaluateHOLFiniteState s
              (.decCall x .one (ofString "lst_upsert_idx") [lExp, eszExp, idxExp] cont) =
              ((evaluateHOLFiniteState mid cont).1,
                { (evaluateHOLFiniteState mid cont).2 with
                  locals := HolFiniteMapExact.resVarEq
                    (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) }) := by
            rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]; dsimp only
            rw [hlk]; dsimp only; rw [if_neg hcz, hbody_ret]; dsimp only
            rw [if_pos hsh_ew, hmid_eq]
          have hws_mid : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid :=
            worldStep_refl (fun _ => []) ["heap_ptr"] hAs (by simp [mid, setVarHOLFinite])
          have hmid_memW : ∀ a, memW mid a = memW s a := fun _ => rfl
          refine ⟨ew, mid, hlw0, hws_mid, worldOK_of_step hW hws_mid,
            fun S' Nd' h => by
              have hs' : WorldTypedWith s S' Nd' :=
                (worldTypedWith_with_locals s (s.locals.update (x, .val (.word ew))) sl.clock S' Nd').1 h
              exact horig_nz hlw0 S' Nd' hs',
            hew8, hew_sb, hew_he,
            by rw [hmid_memW, ← hpw0_toNat]; exact hew_lo,
            by rw [hmid_memW, hmid_memW, ← hpw0_toNat]; exact hew_hi,
            by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
            fun y hy => by simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hy, Ne.symm hy],
            by rw [hbody_ret] at hnt; dsimp only at hnt; rw [if_pos hsh_ew, hmid_eq] at hnt; exact hnt,
            by rw [hbody_ret] at hres; dsimp only at hres; rw [if_pos hsh_ew, hmid_eq] at hres; exact hres,
            by rw [heval_eq], by rw [heval_eq]⟩
        · have hnr := hloop.2.2 rl' rfl (fun rv h => hret ⟨rv, h⟩)
          have hbody_nr : (evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
              (sourceFnBody Guest.Software.guestFn_lst_upsert_idx)).1 = some rl' := by
            rw [hrun', hbody_step]; dsimp only; rw [htail_ev]
          rw [hbody_nr] at hres
          exfalso
          cases rl' with
          | timeOut => exact absurd (congrArg Prod.fst hlp_ev) hnt_loop
          | «break» | «continue» | error => exact not_resumes_error hres
          | finalFfi _ => rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
          | exception e ev => exact hnr hres
          | returned rv => exact hret ⟨rv, rfl⟩
      | none =>
        -- Loop fell through without finding `idx`: runs `decCall "e" .one "lst_push" ...`
        obtain ⟨hsl_eq, hsl_loc⟩ := hloop.1 rfl
        have htail_ev : evaluateHOLFiniteState s_dec tailProg =
            evaluateHOLFiniteState sl
              (.decCall (ofString "e") .one (ofString "lst_push")
                [.var .local (ofString "l"), .var .local (ofString "esz")]
                (.seq (.store (.var .local (ofString "e")) (.var .local (ofString "idx")))
                  (.return (.var .local (ofString "e"))))) := by
          dsimp only [tailProg]; rw [evaluateHOLFiniteState_seq_line780, hlp_ev]
        have hsl_W : WorldOK sl := by
          rw [hsl_eq]
          exact (worldOK_with_locals s sl.locals sl.clock).2 hW
        have hsl_l : sl.locals.lookup (ofString "l") = some (.val (.word lw)) := by
          rw [hsl_loc _ (by decide)]
          simp [s_dec, s_p, s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "l" by decide, show ofString "p" ≠ ofString "l" by decide,
            show ofString "n" ≠ ofString "l" by decide, hent_l]
        have hsl_e : sl.locals.lookup (ofString "esz") = some (.val (.word eszw)) := by
          rw [hsl_loc _ (by decide)]
          simp [s_dec, s_p, s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "esz" by decide, show ofString "p" ≠ ofString "esz" by decide,
            show ofString "n" ≠ ofString "esz" by decide, hent_e]
        have hsl_idx : sl.locals.lookup (ofString "idx") = some (.val (.word idxw)) := by
          rw [hsl_loc _ (by decide)]
          simp [s_dec, s_p, s_n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "idx" by decide, show ofString "p" ≠ ofString "idx" by decide,
            show ofString "n" ≠ ofString "idx" by decide, hent_i]
        have horig_sl : lw ≠ 0 → ∀ S Nd, WorldTypedWith sl S Nd →
            LstOK sl lw.toNat ∧ BalListOrigin sl lw.toNat eszw.toNat := by
          intro hnz S Nd hWT_sl
          have hWT_s : WorldTypedWith s S Nd := by
            rw [hsl_eq] at hWT_sl
            exact (worldTypedWith_with_locals s sl.locals sl.clock S Nd).1 hWT_sl
          rw [hsl_eq]
          exact horig_nz hnz S Nd hWT_s
        have hbody_eq : (evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
            (sourceFnBody Guest.Software.guestFn_lst_upsert_idx)).1 =
            (evaluateHOLFiniteState sl
              (.decCall (ofString "e") .one (ofString "lst_push")
                [.var .local (ofString "l"), .var .local (ofString "esz")]
                (.seq (.store (.var .local (ofString "e")) (.var .local (ofString "idx")))
                  (.return (.var .local (ofString "e")))))).1 := by
          rw [hrun', hbody_step]; dsimp only; rw [htail_ev]
        have hpush_nt : (evaluateHOLFiniteState sl
            (.decCall (ofString "e") .one (ofString "lst_push")
              [.var .local (ofString "l"), .var .local (ofString "esz")]
              (.seq (.store (.var .local (ofString "e")) (.var .local (ofString "idx")))
                (.return (.var .local (ofString "e")))))).1 ≠ some .timeOut := by
          rw [← htail_ev]; exact hnt_tail
        -- Check whether the body itself `Resumes` so we can step `decCall_lst_push_resumes`:
        rcases hbody_out : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
            (sourceFnBody Guest.Software.guestFn_lst_upsert_idx) with ⟨rb, sb⟩
        rw [hbody_out] at hnt hres hbody_eq
        have hpush_res : Resumes (evaluateHOLFiniteState sl
            (.decCall (ofString "e") .one (ofString "lst_push")
              [.var .local (ofString "l"), .var .local (ofString "esz")]
              (.seq (.store (.var .local (ofString "e")) (.var .local (ofString "idx")))
                (.return (.var .local (ofString "e")))))).1 := by
          rw [← hbody_eq]
          cases rb with
          | none => exact absurd hres not_resumes_error
          | some rb' =>
            cases rb' with
            | timeOut => exact absurd rfl hnt
            | «break» | «continue» | error => exact absurd hres not_resumes_error
            | finalFfi _ => exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
            | exception e ev =>
              exfalso
              rcases hres with ⟨_, h⟩ | ⟨e', ev', h, hne⟩
              · simp at h
              · dsimp only at h; injection h with h'; injection h' with he1 he2; subst he1 he2
                exact lst_upsert_idx_no_catchable_exn_add ent hG.code e ev hne
                  (by rw [← hrun', hbody_out])
            | returned vb => exact Or.inl ⟨vb, rfl⟩
        obtain ⟨ew, mid_p, _, hws_p, hW_p, horig_p, hew8, hew_sb, hew_he, hew_lo, hew_hi,
            hmid_e, hmid_other, hcont_nt, hcont_res, hpush_fst, hpush_snd⟩ :=
          decCall_lst_push_resumes sl (ofString "e")
            (.var .local (ofString "l")) (.var .local (ofString "esz")) lw eszw
            (.seq (.store (.var .local (ofString "e")) (.var .local (ofString "idx")))
              (.return (.var .local (ofString "e"))))
            hsl_W
            (by simp [evalHOLExact, hsl_l])
            (by simp [evalHOLExact, hsl_e])
            hesz horig_sl hpush_nt hpush_res
        -- Step `store e idx; return e` on `mid_p`:
        have hmid_idx : mid_p.locals.lookup (ofString "idx") = some (.val (.word idxw)) := by
          rw [hmid_other _ (by decide)]; exact hsl_idx
        have hdom_ew : mid_p.memaddrs ew := by
          rw [hW_p.1.1.memaddrs, Wave8Contracts.M08.ordinaryDomain_iff]
          exact ⟨hew8, hew_sb, by have := hesz_pos; rcases hesz with h | h | h <;> omega⟩
        let mid_st : PanSemStateFiniteExact 64 F :=
          { mid_p with memory := fun a => if a = ew then .word idxw else mid_p.memory a }
        have hst_only : evaluateHOLFiniteState mid_p
            (.store (.var .local (ofString "e")) (.var .local (ofString "idx"))) =
            (none, mid_st) := by
          rw [evaluateHOLFiniteState_store]
          have hev1 : @evalHOLExact 64 F _ mid_p.toExact (fun a => Classical.propDecidable (mid_p.memaddrs a))
              (.var .local (ofString "e")) = some (.val (.word ew)) := by
            simp [evalHOLExact, hmid_e]
          have hev2 : @evalHOLExact 64 F _ mid_p.toExact (fun a => Classical.propDecidable (mid_p.memaddrs a))
              (.var .local (ofString "idx")) = some (.val (.word idxw)) := by
            simp [evalHOLExact, hmid_idx]
          rw [hev1, hev2]; simp only [flattenHOL]
          unfold panMemStoresHOL panMemStoreHOL
          rw [if_pos hdom_ew]; rfl
        have hst_ew : evaluateHOLFiniteState mid_p
            (.seq (.store (.var .local (ofString "e")) (.var .local (ofString "idx")))
              (.return (.var .local (ofString "e")))) =
            (some (.returned (.val (.word ew))), emptyLocalsHOLFinite mid_st) := by
          rw [evaluateHOLFiniteState_seq_line780, hst_only]; dsimp only
          rw [evaluateHOLFiniteState_return]
          have hev3 : @evalHOLExact 64 F _ mid_st.toExact (fun a => Classical.propDecidable (mid_st.memaddrs a))
              (.var .local (ofString "e")) = some (.val (.word ew)) := by
            simp [evalHOLExact, mid_st, hmid_e]
          rw [hev3]; dsimp only
          rw [if_pos (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])]
        have hbre_st : ByteRegionEffect mid_p mid_st
            [(memW mid_p lw.toNat, eszw.toNat * memW mid_p (lw.toNat + 16))] := by
          refine (bre_of_store_multi hW_p.1.1.memaddrs (nw := 1) (by omega) hst_only
            (fun v hv => by
              have hev2 : @evalHOLExact 64 F _ mid_p.toExact (fun a => Classical.propDecidable (mid_p.memaddrs a))
                  (.var .local (ofString "idx")) = some (.val (.word idxw)) := by
                simp [evalHOLExact, hmid_idx]
              rw [hev2] at hv; injection hv with hv'; subst hv'; simp [flattenHOL])
            (fun addr hdst _ => ?_)).1
          have hev1 : @evalHOLExact 64 F _ mid_p.toExact (fun a => Classical.propDecidable (mid_p.memaddrs a))
              (.var .local (ofString "e")) = some (.val (.word ew)) := by
            simp [evalHOLExact, hmid_e]
          rw [hev1] at hdst; injection hdst with hd; injection hd with hd'; injection hd' with hd''; subst hd''
          refine ⟨by rcases hesz with h | h | h <;> omega,
            (memW mid_p lw.toNat, eszw.toNat * memW mid_p (lw.toNat + 16)), List.mem_singleton.2 rfl,
            hew_lo, by dsimp only; rcases hesz with h | h | h <;> omega⟩
        -- Preserve `memW _ lw.toNat` and `memW _ (lw.toNat + 16)` across `mid_p -> mid_st`:
        obtain ⟨Sp0, hWTp_ex⟩ := hW_p.2
        obtain ⟨Ndp0, hWTp⟩ := (worldTyped_iff_with mid_p Sp0).1 hWTp_ex
        obtain ⟨hlst_p, horig_p0⟩ := horig_p Sp0 Ndp0 hWTp
        obtain ⟨hl_fix_p, hp_fix_p, hdj_p, _, _, _⟩ :=
          bal_list_slice_props hWTp.2.2.1 hlw_nz_nat hesz hlst_p (balListOrigin_slice horig_p0)
        rcases hWTp.2.2.1.1 _ hl_fix_p with h0 | ⟨hal_lp, hw_lp⟩
        · simp at h0
        rcases hWTp.2.2.1.1 _ hp_fix_p with h0 | ⟨_, hw_pp⟩
        · exfalso; exact absurd h0 (ne_of_gt (Nat.mul_pos hesz_pos (by have := hlst_p.1; omega)))
        have hu_hdr_p : M08IvlUnhit mid_p mid_st (lw.toNat, 24) := by
          intro a ha8 ha1 ha2
          apply hbre_st.cell_frame a
          intro i hi hc
          have hi_eq := List.mem_singleton.1 hi; subst i
          exact not_cellHits_of_disj ha8 hw_pp.1 ⟨ha1, ha2⟩ hdj_p hc
        have hl_hi_p : lw.toNat + 24 ≤ 2 ^ 64 := (ivl_allocated_bound hW_p.1.2 hal_lp).2
        have hm0_st : memW mid_st lw.toNat = memW mid_p lw.toNat :=
          memW_eq_of_ivlUnhit hu_hdr_p hw_lp.1 hl_hi_p ⟨by omega, by omega⟩
        have hm16_st : memW mid_st (lw.toNat + 16) = memW mid_p (lw.toNat + 16) :=
          memW_eq_of_ivlUnhit hu_hdr_p (by have := hw_lp.1; dsimp only at this; omega) hl_hi_p ⟨by omega, by omega⟩
        -- Finalize `mid` after `decCall` restores `s.locals` and binds `x := ew`:
        let mid : PanSemStateFiniteExact 64 F :=
          setVarHOLFinite x (.val (.word ew)) { sb with locals := s.locals }
        have hrb_eq : rb = some (.returned (.val (.word ew))) := by
          dsimp only at hbody_eq; rw [hbody_eq, hpush_fst, hst_ew]
        have hsb_eq : sb =
            { emptyLocalsHOLFinite mid_st with
              locals := HolFiniteMapExact.resVarEq
                (HolFiniteMapExact.resVarEq
                  (HolFiniteMapExact.resVarEq
                    (HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite mid_st).locals
                      (ofString "e", sl.locals.lookup (ofString "e")))
                    (ofString "i", s_p.locals.lookup (ofString "i")))
                  (ofString "p", s_n.locals.lookup (ofString "p")))
                (ofString "n", ent.locals.lookup (ofString "n")) } := by
          have hsnd := congrArg Prod.snd hbody_out
          rw [hrun', hbody_step] at hsnd; dsimp only at hsnd
          rw [htail_ev, hpush_snd, hst_ew] at hsnd
          exact hsnd.symm
        have hmid_from_st : mid = { mid_st with locals := s.locals.update (x, .val (.word ew)) } := by
          simp [mid, hsb_eq, setVarHOLFinite, emptyLocalsHOLFinite]
        have hbre_mid : ByteRegionEffect mid_p mid
            [(memW mid_p lw.toNat, eszw.toNat * memW mid_p (lw.toNat + 16))] := by
          rw [hmid_from_st]
          exact hbre_st.with_locals_clock (s.locals.update (x, .val (.word ew))) mid_st.clock
        obtain ⟨hws_st, hW_mid, horig_mid⟩ :=
          bal_list_store_arr_worldStep (r := none) hW_p hlw_nz_nat hesz horig_p hbre_mid
        have hws_s_sl : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none sl :=
          worldStep_refl (fun _ => []) ["heap_ptr"] hAs hsl_eq
        have hws_sl_mid : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra sl none mid :=
          worldStep_hp_trans hsl_W.1.2 hws_p hws_st
        have hws_total : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid :=
          worldStep_hp_trans hAs.2 hws_s_sl hws_sl_mid
        have hsh_ew : (shapeEqHOL (shapeOfHOLExact (.val (.word ew) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word ew) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        subst rb
        dsimp only at hnt hres
        rw [if_pos hsh_ew] at hnt hres
        have heval_eq : evaluateHOLFiniteState s
            (.decCall x .one (ofString "lst_upsert_idx") [lExp, eszExp, idxExp] cont) =
            ((evaluateHOLFiniteState mid cont).1,
              { (evaluateHOLFiniteState mid cont).2 with
                locals := HolFiniteMapExact.resVarEq
                  (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) }) := by
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]; dsimp only
          rw [hlk]; dsimp only; rw [if_neg hcz, hbody_out]; dsimp only
          rw [if_pos hsh_ew]
        have hm0_mid : memW mid lw.toNat = memW mid_p lw.toNat := by
          rw [hmid_from_st]; exact hm0_st
        have hm16_mid : memW mid (lw.toNat + 16) = memW mid_p (lw.toNat + 16) := by
          rw [hmid_from_st]; exact hm16_st
        refine ⟨ew, mid, hlw0, hws_total, hW_mid, horig_mid, hew8, hew_sb, hew_he,
          by rw [hm0_mid]; exact hew_lo,
          by rw [hm0_mid, hm16_mid]; exact hew_hi,
          by simp [hmid_from_st, HolFiniteMapExact.lookup_update, FUPDATE],
          fun y hy => by simp [hmid_from_st, HolFiniteMapExact.lookup_update, FUPDATE, hy, Ne.symm hy],
          hnt, hres, by rw [heval_eq], by rw [heval_eq]⟩

private theorem mem_list_set_old_or_new {α : Type} (xs : List α) (i : Nat) (v a : α)
    (ha : a ∈ xs.set i v) : a ∈ xs ∨ a = v := by
  induction xs generalizing i with
  | nil => simp at ha
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact Or.inr rfl
      · exact Or.inl (List.mem_cons_of_mem x ha)
    | succ i =>
      simp only [List.set_cons_succ, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact Or.inl (List.mem_cons_self)
      · rcases ih i ha with ha | ha
        · exact Or.inl (List.mem_cons_of_mem x ha)
        · exact Or.inr ha

private theorem htabSetValuesPost_mem {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {t v a : Nat}
    (h : HtabSetValuesPost s post t v)
    (ha : a ∈ htabValues post t) : a ∈ htabValues s t ∨ a = v := by
  rcases h with h | ⟨i, hi, h⟩
  · rw [h] at ha
    simpa only [List.mem_append, List.mem_singleton] using ha
  · rw [h] at ha
    exact mem_list_set_old_or_new _ i v a ha

private theorem htabSetValuesPost_value_mem {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {t v : Nat}
    (h : HtabSetValuesPost s post t v) :
    v ∈ htabValues post t := by
  rcases h with h | ⟨i, hi, h⟩
  · rw [h]; exact List.mem_append_right _ (List.mem_singleton.2 rfl)
  · rw [h]; exact List.mem_set hi v

private theorem pairwise_flatMap_set_fresh {α β : Type}
    {R : β → β → Prop} (f : α → List β) (xs : List α) (i : Nat) (v : α)
    (hpw : (xs.flatMap f).Pairwise R)
    (hnew : (f v).Pairwise R)
    (hleft : ∀ a ∈ xs.flatMap f, ∀ b ∈ f v, R a b)
    (hright : ∀ a ∈ f v, ∀ b ∈ xs.flatMap f, R a b) :
    ((xs.set i v).flatMap f).Pairwise R := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons] at hpw hleft hright
    obtain ⟨hx, hxs, hcross⟩ := List.pairwise_append.1 hpw
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.flatMap_cons]
      exact List.pairwise_append.2 ⟨hnew, hxs,
        fun a ha b hb => hright a ha b (List.mem_append_right _ hb)⟩
    | succ i =>
      simp only [List.set_cons_succ, List.flatMap_cons]
      refine List.pairwise_append.2 ⟨hx, ih i hxs
        (fun a ha b hb => hleft a (List.mem_append_right _ ha) b hb)
        (fun a ha b hb => hright a ha b (List.mem_append_right _ hb)), ?_⟩
      intro a ha b hb
      obtain ⟨y, hy, hby⟩ := List.mem_flatMap.1 hb
      rcases mem_list_set_old_or_new xs i v y hy with hy | rfl
      · exact hcross a ha b (List.mem_flatMap.2 ⟨y, hy, hby⟩)
      · exact hleft a (List.mem_append_left _ ha) b hby

private theorem pairwise_htabSetValuesPost_flatMap {F α : Type}
    {s post : PanSemStateFiniteExact 64 F} {t v : Nat}
    {R : α → α → Prop} (f : Nat → List α)
    (h : HtabSetValuesPost s post t v)
    (hpw : ((htabValues s t).flatMap f).Pairwise R)
    (hnew : (f v).Pairwise R)
    (hleft : ∀ a ∈ (htabValues s t).flatMap f, ∀ b ∈ f v, R a b)
    (hright : ∀ a ∈ f v, ∀ b ∈ (htabValues s t).flatMap f, R a b) :
    ((htabValues post t).flatMap f).Pairwise R := by
  rcases h with h | ⟨i, hi, h⟩
  · rw [h, List.flatMap_append]
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using
      List.pairwise_append.2 ⟨hpw, hnew, hleft⟩
  · rw [h]
    exact pairwise_flatMap_set_fresh f _ i v hpw hnew hleft hright

private theorem balRecords_eq_htabValues_add {F : Type}
    {s : PanSemStateFiniteExact 64 F} (h : globN s "bal_accounts" ≠ 0) :
    balRecords s = htabValues s (globN s "bal_accounts") := by
  simp only [balRecords, h, if_false, htabValues]

private theorem balRecords_set_values_add {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {v : Nat}
    (hroot : globN post "bal_accounts" = globN s "bal_accounts")
    (hnz : globN s "bal_accounts" ≠ 0)
    (h : HtabSetValuesPost s post (globN s "bal_accounts") v) :
    (balRecords post = balRecords s ++ [v] ∨
      ∃ i < (balRecords s).length, balRecords post = (balRecords s).set i v) ∧
    v ∈ balRecords post ∧
    (∀ ad ∈ balRecords post, ad ∈ balRecords s ∨ ad = v) := by
  have hnzp : globN post "bal_accounts" ≠ 0 := by rw [hroot]; exact hnz
  rw [balRecords_eq_htabValues_add hnzp, hroot, balRecords_eq_htabValues_add hnz]
  exact ⟨h, htabSetValuesPost_value_mem h, fun ad had => htabSetValuesPost_mem h had⟩

private theorem pairwise_balObjects_set_values_add {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {v : Nat}
    (hroot : globN post "bal_accounts" = globN s "bal_accounts")
    (hnz : globN s "bal_accounts" ≠ 0)
    (h : HtabSetValuesPost s post (globN s "bal_accounts") v)
    (objects : Nat → List Ivl)
    (hobjects : ∀ ad ∈ balRecords post,
      (ad, 40) :: lstObjects post (memW post (ad + 16)) 40 ++
        lstObjects post (memW post (ad + 24)) 16 ++
        lstObjects post (memW post (ad + 32)) 24 ++
        (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) = objects ad)
    (hpw : ((balRecords s).flatMap objects).Pairwise Disj)
    (hnew : (objects v).Pairwise Disj)
    (hleft : ∀ a ∈ (balRecords s).flatMap objects, ∀ b ∈ objects v, Disj a b)
    (hright : ∀ a ∈ objects v, ∀ b ∈ (balRecords s).flatMap objects, Disj a b) :
    (balObjects post).Pairwise Disj := by
  have hobj : balObjects post = (balRecords post).flatMap objects := by
    unfold balObjects
    exact List.flatMap_congr hobjects
  rw [hobj]
  have hnzp : globN post "bal_accounts" ≠ 0 := by rw [hroot]; exact hnz
  rw [balRecords_eq_htabValues_add hnzp, hroot]
  rw [balRecords_eq_htabValues_add hnz] at hpw hleft hright
  exact pairwise_htabSetValuesPost_flatMap objects h hpw hnew hleft hright

private theorem pairwise_filter_comm {α : Type}
    {R : α → α → Prop} {p : α → Bool} {xs : List α}
    (h : xs.Pairwise R) : (xs.filter p).Pairwise R :=
  h.sublist List.filter_sublist

private theorem filter_append_three {α : Type} (p : α → Bool) (a b c : List α) :
    (a ++ b ++ c).filter p = a.filter p ++ b.filter p ++ c.filter p := by
  rw [List.filter_append, List.filter_append]

private theorem fixedTyped_of_sublist_old_fresh_add {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {fresh : List Ivl}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hag : AllocatorGrows s post) (hF : FixedTyped s)
    (hsub : (fixedObjects post).Sublist (fixedObjects s ++ fresh))
    (hfresh : ∀ i ∈ fresh,
      Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∧ WordsOK post i)
    (hpw : fresh.Pairwise Disj) :
    FixedTyped post ∧
    (∀ o ∈ fixedObjects post, o ∈ fixedObjects s ∨ o = (0, 0) ∨
      Inside o (globN s "heap_ptr") (globN post "heap_ptr")) := by
  have hclass : ∀ o ∈ fixedObjects post, o ∈ fixedObjects s ∨ o ∈ fresh := by
    intro o ho
    exact List.mem_append.1 (hsub.subset ho)
  constructor
  · constructor
    · intro i hi
      rcases hclass i hi with hold | hnew
      · rcases hF.1 i hold with hz | ⟨hal, hw⟩
        · exact Or.inl hz
        · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hAs.1 hAp.1 hw⟩
      · obtain ⟨hin, hw⟩ := hfresh i hnew
        exact Or.inr ⟨Or.inl ⟨le_trans hAs.2.1 hin.1, hin.2⟩, hw⟩
    · apply list_sublist_pairwise hsub
      apply List.pairwise_append.2
      refine ⟨hF.2, hpw, ?_⟩
      intro a ha b hb
      rcases hF.1 a ha with hz | ⟨hal, _⟩
      · exact Or.inl hz
      · exact disj_flip (disj_allocated_fresh_heap hAs.2 hAp.2 hal (hfresh b hb).1)
  · intro o ho
    rcases hclass o ho with hold | hnew
    · exact Or.inl hold
    · exact Or.inr (Or.inr (hfresh o hnew).1)

private theorem bal_ensure_existing_tail {F : Type}
    (s : PanSemStateFiniteExact 64 F) (f0 f1 : BitVec 64) (fresh : ProgHOL 64)
    (hW : WorldOK s)
    (hm : s.locals.lookup (ofString "m") =
      some (.rStruct [.val (.word f0), .val (.word f1)]))
    (hf0 : f0 ≠ 0) :
    evaluateHOLFiniteState s
      (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
        (.return (.rfield 1 (.var .local (ofString "m")))) .skip) fresh) =
      (some (.returned (.val (.word f1))), emptyLocalsHOLFinite s) ∧
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s
      (some (.returned (.val (.word f1)))) (emptyLocalsHOLFinite s) := by
  have hf0_64 : f0 ≠ 0#64 := hf0
  have hcmp : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notEqual (.rfield 0 (.var .local (ofString "m"))) (.const 0#64)) =
      some (.val (.word 1#64)) := by
    simp [evalHOLExact, hm, Compiler.Encoders.Asm.wordCmpHOL, hf0_64]
  have hite : evaluateHOLFiniteState s
      (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
        (.return (.rfield 1 (.var .local (ofString "m")))) .skip) =
      (some (.returned (.val (.word f1))), emptyLocalsHOLFinite s) := by
    rw [evaluateHOLFiniteState_ite, hcmp]
    dsimp only
    rw [if_neg (by decide), evaluateHOLFiniteState_return]
    simp [evalHOLExact, hm, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  constructor
  · rw [evaluateHOLFiniteState_seq_line780, hite]
  · exact worldStep_refl (fun _ => []) ["heap_ptr"] hW.1 rfl

private theorem bal_lookup_value_record {F : Type}
    {s : PanSemStateFiniteExact 64 F} {tw f0 f1 : BitVec 64}
    (hroot : globN s "bal_accounts" = tw.toNat)
    (htw : tw ≠ 0) (hf0 : f0 ≠ 0)
    (hvalue : HtabWF s tw.toNat → f0 ≠ 0 → f1.toNat ∈ htabValues s tw.toNat)
    {S Nd : List Nat} (hWT : WorldTypedWith s S Nd) :
    f1.toNat ∈ balRecords s := by
  have hnz : globN s "bal_accounts" ≠ 0 := by
    rw [hroot]
    exact fun h => htw (BitVec.eq_of_toNat_eq (by simpa using h))
  have htS : globN s "bal_accounts" ∈ S := by
    rcases hWT.1.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h | h
    · exact absurd h hnz
    · exact h
  have hwf : HtabWF s tw.toNat := by
    rw [← hroot]
    exact (hWT.1.2.1 _ htS).1
  rw [balRecords_eq_htabValues_add hnz, hroot]
  exact hvalue hwf hf0

private theorem seq_store_bal_record_slot {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pw off vw : BitVec 64)
    (valExp : ExpHOL 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (had : s.locals.lookup (ofString "ad") = some (.val (.word pw)))
    (hlo : sourceBase ≤ pw.toNat) (hhi : pw.toNat + 40 ≤ globN s "heap_ptr")
    (hp8 : pw.toNat % 8 = 0) (hoff8 : off.toNat % 8 = 0)
    (hoff : off.toNat + 8 ≤ 40)
    (hval : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) valExp = some (.val (.word vw))) :
    let mid : PanSemStateFiniteExact 64 F :=
      { s with memory := fun a => if a = pw + off then .word vw else s.memory a }
    evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .local (ofString "ad"), .const off]) valExp) cont) =
      evaluateHOLFiniteState mid cont ∧
    ArenaReady mid ∧
    memW mid (pw.toNat + off.toNat) = vw.toNat ∧
    (∀ k, k ≠ pw.toNat + off.toNat → k < 2 ^ 64 → memW mid k = memW s k) ∧
    FrameOutside s mid [] (pw.toNat, 40) := by
  dsimp only
  have hhplim := hAR.2.2.1
  have hlim : heapLimit < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
  have haddr : (pw + off).toNat = pw.toNat + off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hdom : s.memaddrs (pw + off) := by
    rw [hAR.1.memaddrs, Wave8Contracts.M08.ordinaryDomain_iff, haddr]
    exact ⟨by omega, by omega, by omega⟩
  have hdst : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "ad"), .const off]) =
      some (.val (.word (pw + off))) := by
    simp [evalHOLExact, evalListHOLExact, had, wordOpHOL, wordOp, valueIsWord, valueWord]
  have hstore : evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "ad"), .const off]) valExp) =
      (none, { s with memory := fun a => if a = pw + off then .word vw else s.memory a }) := by
    rw [evaluateHOLFiniteState_store, hdst, hval]
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom, ↓reduceIte]
  refine ⟨by rw [evaluateHOLFiniteState_seq_line780, hstore],
    ⟨guestInv_congr (s := s) rfl rfl rfl rfl hAR.1, hAR.2⟩, ?_, ?_, ?_⟩
  · have hb : BitVec.ofNat 64 (pw.toNat + off.toNat) = pw + off := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), haddr]
    simp [memW, hb]
  · intro k hne hk
    have hb : BitVec.ofNat 64 k ≠ pw + off := by
      intro heq
      have he := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, haddr] at he
      exact hne he
    simp [memW, hb]
  · intro a _ hno
    have hne : a ≠ pw + off := by
      rintro rfl
      exact hno ⟨by dsimp only; omega, by dsimp only; omega⟩
    simp [hne]

private theorem bal_ensure_missing_tail {F : Type}
    (s : PanSemStateFiniteExact 64 F) (f1 : BitVec 64) (fresh : ProgHOL 64)
    (hm : s.locals.lookup (ofString "m") =
      some (.rStruct [.val (.word 0#64), .val (.word f1)])) :
    evaluateHOLFiniteState s
      (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
        (.return (.rfield 1 (.var .local (ofString "m")))) .skip) fresh) =
      evaluateHOLFiniteState s fresh := by
  have hcmp : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notEqual (.rfield 0 (.var .local (ofString "m"))) (.const 0#64)) =
      some (.val (.word 0#64)) := by
    simp [evalHOLExact, hm, Compiler.Encoders.Asm.wordCmpHOL]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcmp]
  simp [evaluateHOLFiniteState_skip]

private theorem bal_ensure_insert_return {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw addrw adw : BitVec 64)
    (hAR : ArenaReady s)
    (hroot : s.globals.lookup (ofString "bal_accounts") = some (.val (.word tw)))
    (haddr : s.locals.lookup (ofString "addr") = some (.val (.word addrw)))
    (had : s.locals.lookup (ofString "ad") = some (.val (.word adw)))
    (htnz : tw.toNat ≠ 0)
    (hWF : HtabWF s tw.toNat)
    (hal : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "htab_set")
        [.var .global (ofString "bal_accounts"), .var .local (ofString "addr"),
          .var .local (ofString "ad")])
        (.return (.var .local (ofString "ad"))))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (none, none)) (ofString "htab_set")
        [.var .global (ofString "bal_accounts"), .var .local (ofString "addr"),
          .var .local (ofString "ad")])
        (.return (.var .local (ofString "ad"))))).1) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      HtabExitAt tw.toNat s mid ∧
      HtabSetValuesPost s mid tw.toNat adw.toNat ∧
      mid.be = s.be ∧ mid.locals = s.locals ∧
      adw.toNat ∈ balRecords mid ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (none, none)) (ofString "htab_set")
          [.var .global (ofString "bal_accounts"), .var .local (ofString "addr"),
            .var .local (ofString "ad")])
          (.return (.var .local (ofString "ad")))) =
        (some (.returned (.val (.word adw))), emptyLocalsHOLFinite mid) := by
  obtain ⟨mid, hexit, hvalues, hbe, hlocals, hsp, hfmp, hnt', hres', heval⟩ :=
    seq_call_htab_set_void_resumes s
      (.var .global (ofString "bal_accounts")) (.var .local (ofString "addr"))
      (.var .local (ofString "ad")) (.return (.var .local (ofString "ad")))
      tw addrw adw
      (by simpa [evalAt, evalHOLExact] using hroot)
      (by simpa [evalAt, evalHOLExact] using haddr)
      (by simpa [evalAt, evalHOLExact] using had)
      hAR hWF hal hnt hres
  have hroots : globN s "bal_accounts" = tw.toNat := by simp [globN, hroot]
  have hrootm : globN mid "bal_accounts" = tw.toNat := by
    rw [globN_eq_of_lookup (hexit.2.2.2.2.2.2.2 (ofString "bal_accounts") (by decide))]
    exact hroots
  have hmem : adw.toNat ∈ balRecords mid := by
    rw [balRecords_eq_htabValues_add (by rw [hrootm]; exact htnz), hrootm]
    exact htabSetValuesPost_value_mem hvalues
  refine ⟨mid, hexit, hvalues, hbe, hlocals, hmem, ?_⟩
  rw [heval, evaluateHOLFiniteState_return]
  simp [evalHOLExact, hlocals, had, shapeOfHOLExact, sizeOfShapeWithContextHOL]

private theorem seq_htab_new_store_bal_slot {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (pw off : BitVec 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (had : s.locals.lookup (ofString "ad") = some (.val (.word pw)))
    (hlo : sourceBase ≤ pw.toNat) (hhi : pw.toNat + 40 ≤ globN s "heap_ptr")
    (hp8 : pw.toNat % 8 = 0) (hoff8 : off.toNat % 8 = 0)
    (hoff : off.toNat + 8 ≤ 40)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64])
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
          (.var .local (ofString "t"))) cont))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new")
        [.const 32#64, .const 8#64])
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
          (.var .local (ofString "t"))) cont))).1) :
    ∃ (tw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      globN s "heap_ptr" ≤ tw.toNat ∧
      tw.toNat + 88 ≤ globN mid "heap_ptr" ∧
      ArenaReady mid ∧ mid.be = s.be ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      HtabWF mid tw.toNat ∧ hdr mid tw.toNat 3 = 0 ∧ hdr mid tw.toNat 0 = 32 ∧
      (∀ i ∈ htabFootprint mid tw.toNat,
        Allocated mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) ∧
      memW mid (pw.toNat + off.toNat) = tw.toNat ∧
      (∀ off' : Nat, off' + 8 ≤ 40 → off' ≠ off.toNat →
        memW mid (pw.toNat + off') = memW s (pw.toNat + off')) ∧
      FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
        (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") ∧
      mid.locals.lookup (ofString "t") = some (.val (.word tw)) ∧
      (∀ y, y ≠ ofString "t" → mid.locals.lookup y = s.locals.lookup y) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new")
          [.const 32#64, .const 8#64])
          (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
            (.var .local (ofString "t"))) cont)) = evaluateHOLFiniteState mid cont := by
  obtain ⟨tw, m1, htlo, hthi, hA1, hbe1, hsp1, hfmp1, hwf1, hcnt1, hkey1,
    hfp1, hfr1, hl1, hg1, hnt1, hres1, heq1⟩ :=
    seq_call_htab_new_resumes s .local (ofString "t") 32#64 8#64 _ hAR
      (by decide) (by decide) (fun h => by cases h) hnt hres
  obtain ⟨ht, hloc, hgl⟩ := hl1 rfl
  have had1 : m1.locals.lookup (ofString "ad") = some (.val (.word pw)) :=
    (hloc _ (by decide)).trans had
  have hp_hi : pw.toNat + 40 ≤ globN m1 "heap_ptr" := by omega
  obtain ⟨heq2, hA2, hword, hother, hfr2⟩ :=
    seq_store_bal_record_slot m1 pw off tw (.var .local (ofString "t")) cont
      hA1 had1 hlo hp_hi hp8 hoff8 hoff ht
  let mid : PanSemStateFiniteExact 64 F :=
    { m1 with memory := fun a => if a = pw + off then .word tw else m1.memory a }
  have haddr : (pw + off).toNat = pw.toNat + off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
      have := hA1.2.2.1
      have hlim : heapLimit < 2 ^ 64 := by decide
      omega)]
  have hu : ∀ i ∈ htabFootprint m1 tw.toNat, M08IvlUnhit m1 mid i := by
    intro i hi a _ ha _
    have hin := (hfp1 i hi).2
    have hne : a ≠ pw + off := by
      rintro rfl
      rw [haddr] at ha
      dsimp only [Inside] at hin
      omega
    simp [mid, hne]
  obtain ⟨hwf2, hfp2, hhdr2⟩ := htabWF_transfer_unhit hA1 hA2 hwf1 hu
    (fun i hi => (hfp1 i hi).1)
  have hfr : FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") := by
    intro a hno hnf
    exact (hfr2 a (fun _ h => by cases h) (hno _ (by simp))).trans
      (hfr1 a (fun j hj => hno j (by
        rcases List.mem_singleton.1 hj with rfl
        exact List.mem_cons_self)) hnf)
  rw [heq2] at hnt1 hres1
  refine ⟨tw, mid, htlo, hthi, hA2, hbe1, hsp1, hwf2,
    (hhdr2 3 (by omega)).trans hcnt1, (hhdr2 0 (by omega)).trans hkey1,
    fun i hi => by rw [hfp2] at hi; exact hfp1 i hi,
    hword, ?_, hfr, ht, hloc, hgl, hnt1, hres1, heq1.trans heq2⟩
  intro off' hoff'_hi hoff'_ne
  have h264 : heapLimit < 2 ^ 64 := by decide
  have hk64 : pw.toNat + off' < 2 ^ 64 := by have := hAR.2.2.1; omega
  rw [hother (pw.toNat + off') (by omega) hk64]
  unfold memW
  have hm_eq := hfr1 (BitVec.ofNat 64 (pw.toNat + off'))
    (fun j hj ⟨c1, c2⟩ => by
      rcases List.mem_singleton.1 hj with rfl
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      have hsep : heapLimit ≤ scratchStart := by decide
      have := hAR.2.2.1; have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
      omega)
    (fun ⟨c1, c2⟩ => by
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      omega)
  rw [hm_eq]

private theorem decCall_htab_new_store_bal_slot {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (pw off : BitVec 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (had : s.locals.lookup (ofString "ad") = some (.val (.word pw)))
    (hlo : sourceBase ≤ pw.toNat) (hhi : pw.toNat + 40 ≤ globN s "heap_ptr")
    (hp8 : pw.toNat % 8 = 0) (hoff8 : off.toNat % 8 = 0)
    (hoff : off.toNat + 8 ≤ 40)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString "t") .one (ofString "htab_new") [.const 32#64, .const 8#64]
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
          (.var .local (ofString "t"))) cont))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString "t") .one (ofString "htab_new") [.const 32#64, .const 8#64]
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
          (.var .local (ofString "t"))) cont))).1) :
    ∃ (tw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      globN s "heap_ptr" ≤ tw.toNat ∧
      tw.toNat + 88 ≤ globN mid "heap_ptr" ∧
      ArenaReady mid ∧ mid.be = s.be ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      HtabWF mid tw.toNat ∧ hdr mid tw.toNat 3 = 0 ∧ hdr mid tw.toNat 0 = 32 ∧
      (∀ i ∈ htabFootprint mid tw.toNat,
        Allocated mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) ∧
      memW mid (pw.toNat + off.toNat) = tw.toNat ∧
      (∀ off' : Nat, off' + 8 ≤ 40 → off' ≠ off.toNat →
        memW mid (pw.toNat + off') = memW s (pw.toNat + off')) ∧
      FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
        (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") ∧
      mid.locals.lookup (ofString "t") = some (.val (.word tw)) ∧
      (∀ y, y ≠ ofString "t" → mid.locals.lookup y = s.locals.lookup y) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "t") .one (ofString "htab_new") [.const 32#64, .const 8#64]
          (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
            (.var .local (ofString "t"))) cont))).1 = (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "t") .one (ofString "htab_new") [.const 32#64, .const 8#64]
          (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
            (.var .local (ofString "t"))) cont))).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState mid cont).2.locals
            (ofString "t", s.locals.lookup (ofString "t")) } := by
  obtain ⟨tw, m1, htlo, hthi, hA1, hbe1, hsp1, hfmp1, hwf1, hcnt1, hkey1,
    hfp1, hfr1, ht, hloc, hgl, hnt1, hres1, heq1_fst, heq1_snd⟩ :=
    decCall_htab_new_resumes s (ofString "t") 32#64 8#64 _ hAR
      (by decide) (by decide) hnt hres
  have had1 : m1.locals.lookup (ofString "ad") = some (.val (.word pw)) :=
    (hloc _ (by decide)).trans had
  have hp_hi : pw.toNat + 40 ≤ globN m1 "heap_ptr" := by omega
  obtain ⟨heq2, hA2, hword, hother, hfr2⟩ :=
    seq_store_bal_record_slot m1 pw off tw (.var .local (ofString "t")) cont
      hA1 had1 hlo hp_hi hp8 hoff8 hoff ht
  let mid : PanSemStateFiniteExact 64 F :=
    { m1 with memory := fun a => if a = pw + off then .word tw else m1.memory a }
  have haddr : (pw + off).toNat = pw.toNat + off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
      have := hA1.2.2.1
      have hlim : heapLimit < 2 ^ 64 := by decide
      omega)]
  have hu : ∀ i ∈ htabFootprint m1 tw.toNat, M08IvlUnhit m1 mid i := by
    intro i hi a _ ha _
    have hin := (hfp1 i hi).2
    have hne : a ≠ pw + off := by
      rintro rfl
      rw [haddr] at ha
      dsimp only [Inside] at hin
      omega
    simp [mid, hne]
  obtain ⟨hwf2, hfp2, hhdr2⟩ := htabWF_transfer_unhit hA1 hA2 hwf1 hu
    (fun i hi => (hfp1 i hi).1)
  have hfr : FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") := by
    intro a hno hnf
    exact (hfr2 a (fun _ h => by cases h) (hno _ (by simp))).trans
      (hfr1 a (fun j hj => hno j (by
        rcases List.mem_singleton.1 hj with rfl
        exact List.mem_cons_self)) hnf)
  rw [heq2] at hnt1 hres1 heq1_fst heq1_snd
  refine ⟨tw, mid, htlo, hthi, hA2, hbe1, hsp1, hwf2,
    (hhdr2 3 (by omega)).trans hcnt1, (hhdr2 0 (by omega)).trans hkey1,
    fun i hi => by rw [hfp2] at hi; exact hfp1 i hi,
    hword, ?_, hfr, ht, hloc, hgl, hnt1, hres1, heq1_fst, heq1_snd⟩
  intro off' hoff'_hi hoff'_ne
  have h264 : heapLimit < 2 ^ 64 := by decide
  have hk64 : pw.toNat + off' < 2 ^ 64 := by have := hAR.2.2.1; omega
  rw [hother (pw.toNat + off') (by omega) hk64]
  unfold memW
  have hm_eq := hfr1 (BitVec.ofNat 64 (pw.toNat + off'))
    (fun j hj ⟨c1, c2⟩ => by
      rcases List.mem_singleton.1 hj with rfl
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      have hsep : heapLimit ≤ scratchStart := by decide
      have := hAR.2.2.1; have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
      omega)
    (fun ⟨c1, c2⟩ => by
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      omega)
  rw [hm_eq]

private theorem decCall_lst_new_store_bal_slot {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (pw off eszw capw : BitVec 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (had : s.locals.lookup (ofString "ad") = some (.val (.word pw)))
    (hlo : sourceBase ≤ pw.toNat) (hhi : pw.toNat + 40 ≤ globN s "heap_ptr")
    (hp8 : pw.toNat % 8 = 0) (hoff8 : off.toNat % 8 = 0)
    (hoff : off.toNat + 8 ≤ 40)
    (hesz_pos : 1 ≤ eszw.toNat)
    (hmul_lt : eszw.toNat * capw.toNat < 2 ^ 64)
    (hmul_al : (eszw.toNat * capw.toNat) % 8 = 0)
    (hcap_pos : 1 ≤ capw.toNat)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString "l") .one (ofString "lst_new") [.const eszw, .const capw]
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
          (.var .local (ofString "l"))) cont))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString "l") .one (ofString "lst_new") [.const eszw, .const capw]
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
          (.var .local (ofString "l"))) cont))).1) :
    ∃ (lw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      lw.toNat = globN s "heap_ptr" ∧
      lw.toNat % 8 = 0 ∧ lw.toNat ≠ 0 ∧
      globN mid "heap_ptr" = lw.toNat + 24 + eszw.toNat * capw.toNat ∧
      globN s "heap_ptr" < globN mid "heap_ptr" ∧
      ArenaReady mid ∧ mid.be = s.be ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      LstOK mid lw.toNat ∧
      lstObjects mid lw.toNat eszw.toNat =
        [(lw.toNat, 24), (lw.toNat + 24, eszw.toNat * capw.toNat)] ∧
      Disj (lw.toNat, 24) (lw.toNat + 24, eszw.toNat * capw.toNat) ∧
      (∀ i ∈ lstObjects mid lw.toNat eszw.toNat,
        Allocated mid i ∧ WordsOK mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) ∧
      memW mid (pw.toNat + off.toNat) = lw.toNat ∧
      (∀ off' : Nat, off' + 8 ≤ 40 → off' ≠ off.toNat →
        memW mid (pw.toNat + off') = memW s (pw.toNat + off')) ∧
      FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
        (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") ∧
      mid.locals.lookup (ofString "l") = some (.val (.word lw)) ∧
      (∀ y, y ≠ ofString "l" → mid.locals.lookup y = s.locals.lookup y) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "l") .one (ofString "lst_new") [.const eszw, .const capw]
          (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
            (.var .local (ofString "l"))) cont))).1 = (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "l") .one (ofString "lst_new") [.const eszw, .const capw]
          (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
            (.var .local (ofString "l"))) cont))).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState mid cont).2.locals
            (ofString "l", s.locals.lookup (ofString "l")) } := by
  obtain ⟨lw, m1, hlw_eq, hlw8, hlw_nz, hm0, hm8, hm16, hhp_m1, hhp_lt,
    hA1, hbe1, hsp1, hfmp1, hlst1, hobjs1, hdisj1, hobjs_p1, hfr1,
    hl, hloc, hgl, hnt1, hres1, heq1_fst, heq1_snd⟩ :=
    decCall_lst_new_resumes s (ofString "l") eszw capw _ hAR
      hesz_pos hmul_lt hmul_al hcap_pos hnt hres
  have had1 : m1.locals.lookup (ofString "ad") = some (.val (.word pw)) :=
    (hloc _ (by decide)).trans had
  have hp_hi : pw.toNat + 40 ≤ globN m1 "heap_ptr" := by omega
  obtain ⟨heq2, hA2, hword, hother, hfr2⟩ :=
    seq_store_bal_record_slot m1 pw off lw (.var .local (ofString "l")) cont
      hA1 had1 hlo hp_hi hp8 hoff8 hoff hl
  let mid : PanSemStateFiniteExact 64 F :=
    { m1 with memory := fun a => if a = pw + off then .word lw else m1.memory a }
  have h264 : heapLimit < 2 ^ 64 := by decide
  have hlw24_lt : lw.toNat + 24 < 2 ^ 64 := by have := hA1.2.2.1; omega
  have hm0_mid : memW mid lw.toNat = lw.toNat + 24 := by
    rw [hother lw.toNat (by omega) (by omega)]; exact hm0
  have hm8_mid : memW mid (lw.toNat + 8) = 0 := by
    rw [hother (lw.toNat + 8) (by omega) (by omega)]; exact hm8
  have hm16_mid : memW mid (lw.toNat + 16) = capw.toNat := by
    rw [hother (lw.toNat + 16) (by omega) (by omega)]; exact hm16
  have hlst_mid : LstOK mid lw.toNat := ⟨by rw [hm16_mid]; exact hcap_pos, by rw [hm8_mid, hm16_mid]; omega⟩
  have hmul_pos : 0 < eszw.toNat * capw.toNat := Nat.mul_pos (by omega) (by omega)
  have hobjs_mid : lstObjects mid lw.toNat eszw.toNat =
      [(lw.toNat, 24), (lw.toNat + 24, eszw.toNat * capw.toNat)] := by
    unfold lstObjects
    rw [if_neg hlw_nz, hm0_mid, hm16_mid, if_neg (by omega)]
  have hobjs_p_mid : ∀ i ∈ lstObjects mid lw.toNat eszw.toNat,
      Allocated mid i ∧ WordsOK mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr") := by
    intro i hi
    rw [hobjs_mid, ← hobjs1] at hi
    obtain ⟨hal, hw, hin⟩ := hobjs_p1 i hi
    exact ⟨hal, wordsOK_transfer hA1.1 hA2.1 hw, hin⟩
  have hfr : FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") := by
    intro a hno hnf
    exact (hfr2 a (fun _ h => by cases h) (hno _ (by simp))).trans
      (hfr1 a (fun j hj => hno j (by
        rcases List.mem_singleton.1 hj with rfl
        exact List.mem_cons_self)) hnf)
  rw [heq2] at hnt1 hres1 heq1_fst heq1_snd
  refine ⟨lw, mid, hlw_eq, hlw8, hlw_nz, hhp_m1, hhp_lt, hA2, hbe1, hsp1,
    hlst_mid, hobjs_mid, hdisj1, hobjs_p_mid, hword, ?_, hfr, hl, hloc, hgl,
    hnt1, hres1, heq1_fst, heq1_snd⟩
  intro off' hoff'_hi hoff'_ne
  have hk64 : pw.toNat + off' < 2 ^ 64 := by have := hAR.2.2.1; omega
  rw [hother (pw.toNat + off') (by omega) hk64]
  unfold memW
  have hm_eq := hfr1 (BitVec.ofNat 64 (pw.toNat + off'))
    (fun j hj ⟨c1, c2⟩ => by
      rcases List.mem_singleton.1 hj with rfl
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      have hsep : heapLimit ≤ scratchStart := by decide
      have := hAR.2.2.1; have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
      omega)
    (fun ⟨c1, c2⟩ => by
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      omega)
  rw [hm_eq]

private theorem seq_lst_new_store_bal_slot {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (pw off eszw capw : BitVec 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (had : s.locals.lookup (ofString "ad") = some (.val (.word pw)))
    (hlo : sourceBase ≤ pw.toNat) (hhi : pw.toNat + 40 ≤ globN s "heap_ptr")
    (hp8 : pw.toNat % 8 = 0) (hoff8 : off.toNat % 8 = 0)
    (hoff : off.toNat + 8 ≤ 40)
    (hesz_pos : 1 ≤ eszw.toNat)
    (hmul_lt : eszw.toNat * capw.toNat < 2 ^ 64)
    (hmul_al : (eszw.toNat * capw.toNat) % 8 = 0)
    (hcap_pos : 1 ≤ capw.toNat)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (.local, ofString "l"), none)) (ofString "lst_new")
        [.const eszw, .const capw])
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
          (.var .local (ofString "l"))) cont))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (some (.local, ofString "l"), none)) (ofString "lst_new")
        [.const eszw, .const capw])
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
          (.var .local (ofString "l"))) cont))).1) :
    ∃ (lw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      lw.toNat = globN s "heap_ptr" ∧
      lw.toNat % 8 = 0 ∧ lw.toNat ≠ 0 ∧
      globN mid "heap_ptr" = lw.toNat + 24 + eszw.toNat * capw.toNat ∧
      globN s "heap_ptr" < globN mid "heap_ptr" ∧
      ArenaReady mid ∧ mid.be = s.be ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      LstOK mid lw.toNat ∧
      lstObjects mid lw.toNat eszw.toNat =
        [(lw.toNat, 24), (lw.toNat + 24, eszw.toNat * capw.toNat)] ∧
      Disj (lw.toNat, 24) (lw.toNat + 24, eszw.toNat * capw.toNat) ∧
      (∀ i ∈ lstObjects mid lw.toNat eszw.toNat,
        Allocated mid i ∧ WordsOK mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) ∧
      memW mid (pw.toNat + off.toNat) = lw.toNat ∧
      (∀ off' : Nat, off' + 8 ≤ 40 → off' ≠ off.toNat →
        memW mid (pw.toNat + off') = memW s (pw.toNat + off')) ∧
      FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
        (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") ∧
      mid.locals.lookup (ofString "l") = some (.val (.word lw)) ∧
      (∀ y, y ≠ ofString "l" → mid.locals.lookup y = s.locals.lookup y) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (some (.local, ofString "l"), none)) (ofString "lst_new")
          [.const eszw, .const capw])
          (.seq (.store (.op .add [.var .local (ofString "ad"), .const off])
            (.var .local (ofString "l"))) cont)) = evaluateHOLFiniteState mid cont := by
  obtain ⟨lw, m1, hlw_eq, hlw8, hlw_nz, hm0, hm8, hm16, hhp_m1, hhp_lt,
    hA1, hbe1, hsp1, hfmp1, hlst1, hobjs1, hdisj1, hobjs_p1, hfr1,
    hl, hloc, hgl, hnt1, hres1, heq1⟩ :=
    seq_call_lst_new_local_resumes s (ofString "l") eszw capw _ hAR
      hesz_pos hmul_lt hmul_al hcap_pos hnt hres
  have had1 : m1.locals.lookup (ofString "ad") = some (.val (.word pw)) :=
    (hloc _ (by decide)).trans had
  have hp_hi : pw.toNat + 40 ≤ globN m1 "heap_ptr" := by omega
  obtain ⟨heq2, hA2, hword, hother, hfr2⟩ :=
    seq_store_bal_record_slot m1 pw off lw (.var .local (ofString "l")) cont
      hA1 had1 hlo hp_hi hp8 hoff8 hoff hl
  let mid : PanSemStateFiniteExact 64 F :=
    { m1 with memory := fun a => if a = pw + off then .word lw else m1.memory a }
  have h264 : heapLimit < 2 ^ 64 := by decide
  have hm0_mid : memW mid lw.toNat = lw.toNat + 24 := by
    rw [hother lw.toNat (by omega) (by have := hA1.2.2.1; omega)]; exact hm0
  have hm8_mid : memW mid (lw.toNat + 8) = 0 := by
    rw [hother (lw.toNat + 8) (by omega) (by have := hA1.2.2.1; omega)]; exact hm8
  have hm16_mid : memW mid (lw.toNat + 16) = capw.toNat := by
    rw [hother (lw.toNat + 16) (by omega) (by have := hA1.2.2.1; omega)]; exact hm16
  have hlst_mid : LstOK mid lw.toNat := ⟨by rw [hm16_mid]; exact hcap_pos, by rw [hm8_mid, hm16_mid]; omega⟩
  have hmul_pos : 0 < eszw.toNat * capw.toNat := Nat.mul_pos (by omega) (by omega)
  have hobjs_mid : lstObjects mid lw.toNat eszw.toNat =
      [(lw.toNat, 24), (lw.toNat + 24, eszw.toNat * capw.toNat)] := by
    unfold lstObjects
    rw [if_neg hlw_nz, hm0_mid, hm16_mid, if_neg (by omega)]
  have hobjs_p_mid : ∀ i ∈ lstObjects mid lw.toNat eszw.toNat,
      Allocated mid i ∧ WordsOK mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr") := by
    intro i hi
    rw [hobjs_mid, ← hobjs1] at hi
    obtain ⟨hal, hw, hin⟩ := hobjs_p1 i hi
    exact ⟨hal, wordsOK_transfer hA1.1 hA2.1 hw, hin⟩
  have hfr : FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") := by
    intro a hno hnf
    exact (hfr2 a (fun _ h => by cases h) (hno _ (by simp))).trans
      (hfr1 a (fun j hj => hno j (by
        rcases List.mem_singleton.1 hj with rfl
        exact List.mem_cons_self)) hnf)
  rw [heq2] at hnt1 hres1
  refine ⟨lw, mid, hlw_eq, hlw8, hlw_nz, hhp_m1, hhp_lt, hA2, hbe1, hsp1,
    hlst_mid, hobjs_mid, hdisj1, hobjs_p_mid, hword, ?_, hfr, hl, hloc, hgl,
    hnt1, hres1, heq1.trans heq2⟩
  intro off' hoff'_hi hoff'_ne
  have hk64 : pw.toNat + off' < 2 ^ 64 := by have := hAR.2.2.1; omega
  rw [hother (pw.toNat + off') (by omega) hk64]
  unfold memW
  have hm_eq := hfr1 (BitVec.ofNat 64 (pw.toNat + off'))
    (fun j hj ⟨c1, c2⟩ => by
      rcases List.mem_singleton.1 hj with rfl
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      have hsep : heapLimit ≤ scratchStart := by decide
      have := hAR.2.2.1; have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
      omega)
    (fun ⟨c1, c2⟩ => by
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      omega)
  rw [hm_eq]

private theorem mem_worldRoleSlots_recRole {F : Type} (s : PanSemStateFiniteExact 64 F)
    (g : String) (k : Nat) (r : String)
    (_hgnz : globN s g ≠ 0) (htnz : memW s (globN s g + k) ≠ 0)
    (hmem : (memW s (globN s g + k), r) ∈
      recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] ++
      recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"),
        (48, "bs+48"), (72, "bs+72")] ++
      recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"),
        (48, "ts+48"), (56, "ts+56"), (64, "ts+64")]) :
    (memW s (globN s g + k), r) ∈ worldRoleSlots s := by
  unfold worldRoleSlots
  refine List.mem_filter.2 ⟨?_, by simp [htnz]⟩
  apply List.mem_append.2; left; apply List.mem_append.2; left
  apply List.mem_append.2; left; apply List.mem_append.2; left
  exact hmem

private theorem slot_ne_of_diff_nonshared_role {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hroles : RolesOK s S (worldRoleSlots s) (journalRoleSlots s))
    {t1 t2 : Nat} {r1 r2 : String}
    (h1 : (t1, r1) ∈ worldRoleSlots s) (h2 : (t2, r2) ∈ worldRoleSlots s)
    (hne_r : r1 ≠ r2) : t1 ≠ t2 := by
  intro heq
  subst heq
  obtain ⟨i1, hi1, heq1⟩ := List.mem_iff_getElem.1 h1
  obtain ⟨i2, hi2, heq2⟩ := List.mem_iff_getElem.1 h2
  rcases Nat.lt_trichotomy i1 i2 with hlt | rfl | hgt
  · have hp := List.pairwise_iff_getElem.1 hroles.2.1 i1 i2 hi1 hi2 hlt
    rw [heq1, heq2] at hp
    exact hne_r (hp rfl).1
  · rw [heq1] at heq2
    exact hne_r (Prod.mk.inj heq2).2
  · have hp := List.pairwise_iff_getElem.1 hroles.2.1 i2 i1 hi2 hi1 hgt
    rw [heq1, heq2] at hp
    exact hne_r (hp rfl).1.symm

private theorem bal_accounts_role_props {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hT : TablesTyped s S) (hnz : globN s "bal_accounts" ≠ 0) :
    let t0 := globN s "bal_accounts"
    t0 ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) := by
  dsimp only
  set t0 := globN s "bal_accounts"
  have ht0_S : t0 ∈ S := by
    rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
    · exact absurd h0 hnz
    · exact hm
  have hroles := hT.2.2.2.2.2.2.2.2.2.2.2
  have ht0_wrs : (t0, "bal_accounts") ∈ worldRoleSlots s := by
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [t0, hnz]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    exact List.mem_append_right _ (by simp [t0])
  refine ⟨ht0_S, ?_, ?_, ?_, ?_⟩
  · intro hbs h_eq
    have hw_wrs : (memW s (globN s "bs" + 32), "bs+32") ∈ worldRoleSlots s := by
      apply mem_worldRoleSlots_recRole s "bs" 32 "bs+32" hbs (by rw [h_eq]; exact hnz)
      apply List.mem_append_left; apply List.mem_append_right
      simp [recRoles, hbs]
    exact slot_ne_of_diff_nonshared_role hroles hw_wrs ht0_wrs (by decide) h_eq
  · intro hts h_eq
    have hw_wrs : (memW s (globN s "ts" + 32), "ts+32") ∈ worldRoleSlots s := by
      apply mem_worldRoleSlots_recRole s "ts" 32 "ts+32" hts (by rw [h_eq]; exact hnz)
      apply List.mem_append_right
      simp [recRoles, hts]
    exact slot_ne_of_diff_nonshared_role hroles hw_wrs ht0_wrs (by decide) h_eq
  · intro ad had h_eq
    have had_wrs : (memW s ad, "bal.stor") ∈ worldRoleSlots s := by
      unfold worldRoleSlots
      refine List.mem_filter.2 ⟨?_, by simp [h_eq, hnz]⟩
      exact List.mem_append_right _ (List.mem_flatMap.2 ⟨ad, had, by simp⟩)
    exact slot_ne_of_diff_nonshared_role hroles had_wrs ht0_wrs (by decide) h_eq
  · intro hws h_eq
    have hw_wrs : (memW s (globN s "ws" + 32), "ws+32") ∈ worldRoleSlots s := by
      apply mem_worldRoleSlots_recRole s "ws" 32 "ws+32" hws (by rw [h_eq]; exact hnz)
      apply List.mem_append_left; apply List.mem_append_left
      simp [recRoles, hws]
    exact slot_ne_of_diff_nonshared_role hroles hw_wrs ht0_wrs (by decide) h_eq

private theorem old_balAccount_congr_of_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hA : ArenaOK s) (hT : TablesTyped s S) (hF : FixedTyped s)
    {t0 : Nat}
    (hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint s u, M08IvlUnhit s post i)
    (ht0_not_ad : ∀ ad ∈ balRecords s, memW s ad ≠ t0)
    (hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → M08IvlUnhit s post i)
    (hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16)
    {ad : Nat} (had : ad ∈ balRecords s) :
    ((ad, 40) :: lstObjects post (memW post (ad + 16)) 40 ++
      lstObjects post (memW post (ad + 24)) 16 ++
      lstObjects post (memW post (ad + 32)) 24 ++
      (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) =
    (ad, 40) :: lstObjects s (memW s (ad + 16)) 40 ++
      lstObjects s (memW s (ad + 24)) 16 ++
      lstObjects s (memW s (ad + 32)) 24 ++
      (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40)) ∧
    memW post ad = memW s ad ∧
    memW post (ad + 8) = memW s (ad + 8) ∧
    htabValues post (memW post ad) = htabValues s (memW s ad) ∧
    (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW post (ad + k))) ∧
    (∀ l ∈ htabValues post (memW post ad), LstOK post l) := by
  have hmem_fix_of_bal : ∀ i ∈ balObjects s, i ∈ fixedObjects s := fun i hi => by
    unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)
  have had_bal : (ad, 40) ∈ balObjects s := by
    unfold balObjects; exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
  rcases hF.1 _ (hmem_fix_of_bal _ had_bal) with h0 | ⟨hal_ad, hw_ad⟩
  · simp at h0
  have hhi_ad := (Wave8Contracts.M08.ivl_allocated_bound hA hal_ad).2
  have had8 : ad % 8 = 0 := hw_ad.1
  have hoff_eq : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off) := by
    intro off hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
      exact Wave8Contracts.M08.memW_eq_of_ivlUnhit (hu_bal _ had_bal (by simp)) (by omega) hhi_ad ⟨by omega, by omega⟩
  have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
  have hvals_ad : htabValues post (memW s ad) = htabValues s (memW s ad) :=
    Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ had_T.1).1 (hu_other _ had_T.1 (ht0_not_ad ad had))
  have hlst_eq : ∀ l, (l, 24) ∈ balObjects s →
      memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16) := by
    intro l hl_bal
    rcases hF.1 _ (hmem_fix_of_bal _ hl_bal) with h0 | ⟨hal_l, hw_l⟩
    · simp at h0
    have hhi_l := (Wave8Contracts.M08.ivl_allocated_bound hA hal_l).2
    have hl8 : l % 8 = 0 := hw_l.1
    have hul := hu_bal _ hl_bal (by simp)
    refine ⟨?_, ?_, ?_⟩
    · simpa using Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
    · exact Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
    · exact Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
  have hklst : ∀ k ∈ ([16, 24, 32] : List Nat),
      memW post (memW s (ad + k)) = memW s (memW s (ad + k)) ∧
      memW post (memW s (ad + k) + 8) = memW s (memW s (ad + k) + 8) ∧
      memW post (memW s (ad + k) + 16) = memW s (memW s (ad + k) + 16) := by
    intro k hk
    by_cases hk0 : memW s (ad + k) = 0
    · simp [hk0, hm0.1, hm0.2.1, hm0.2.2]
    · apply hlst_eq
      unfold balObjects
      refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> simp [lstObjects, hk0]
  have hllst : ∀ l ∈ htabValues s (memW s ad),
      memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧ memW post (l + 16) = memW s (l + 16) := by
    intro l hl
    by_cases hl0 : l = 0
    · subst hl0; simp [hm0.1, hm0.2.1, hm0.2.2]
    · apply hlst_eq
      unfold balObjects
      refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
      apply List.mem_cons_of_mem
      apply List.mem_append.2; right
      exact List.mem_flatMap.2 ⟨l, hl, by simp [lstObjects, hl0]⟩
  have h0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at h0
  have h8 := hoff_eq 8 (by simp)
  have h16 := hoff_eq 16 (by simp)
  have h24 := hoff_eq 24 (by simp)
  have h32 := hoff_eq 32 (by simp)
  obtain ⟨hk16_0, _, hk16_16⟩ := hklst 16 (by simp)
  obtain ⟨hk24_0, _, hk24_16⟩ := hklst 24 (by simp)
  obtain ⟨hk32_0, _, hk32_16⟩ := hklst 32 (by simp)
  have htail : (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) =
      (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40) := by
    rw [h0, hvals_ad]
    apply List.flatMap_congr
    intro l hl
    obtain ⟨hl0, _, hl16⟩ := hllst l hl
    simp [lstObjects, hl0, hl16]
  refine ⟨?_, h0, h8, by rw [h0, hvals_ad], ?_, ?_⟩
  · rw [htail, h16, h24, h32]
    simp [lstObjects, hk16_0, hk16_16, hk24_0, hk24_16, hk32_0, hk32_16]
  · intro k hk
    have hk_in : k ∈ ([0, 8, 16, 24, 32] : List Nat) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl <;> simp
    rw [hoff_eq k hk_in]
    obtain ⟨_, hk8, hk16⟩ := hklst k hk
    unfold LstOK; rw [hk8, hk16]; exact had_T.2.2.1 k hk
  · intro l hl
    rw [h0, hvals_ad] at hl
    obtain ⟨_, hl8, hl16⟩ := hllst l hl
    unfold LstOK; rw [hl8, hl16]; exact had_T.2.2.2 l hl

private theorem frameOutside_keep_absorb_fresh {F : Type}
    {a b c : PanSemStateFiniteExact 64 F} {sp pw : Nat}
    (hpw_in : pw = globN a "heap_ptr" ∧ pw + 40 ≤ globN b "heap_ptr")
    (hhb : globN b "heap_ptr" ≤ globN c "heap_ptr")
    (h1 : FrameOutside a b [(sp, 0)] (globN a "heap_ptr", globN b "heap_ptr" - globN a "heap_ptr"))
    (h2 : FrameOutside b c [(sp, 0), (pw, 40)] (globN b "heap_ptr", globN c "heap_ptr" - globN b "heap_ptr")) :
    FrameOutside a c [(sp, 0)] (globN a "heap_ptr", globN c "heap_ptr" - globN a "heap_ptr") := by
  intro x hno hnf
  have hnf1 : ¬ CellHits x.toNat (globN a "heap_ptr", globN b "heap_ptr" - globN a "heap_ptr") := by
    intro ⟨c1, c2⟩; dsimp only at c1 c2
    exact hnf ⟨c1, by dsimp only; omega⟩
  have hnf2 : ¬ CellHits x.toNat (globN b "heap_ptr", globN c "heap_ptr" - globN b "heap_ptr") := by
    intro ⟨c1, c2⟩; dsimp only at c1 c2
    exact hnf ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hno2 : ∀ j ∈ ([(sp, 0), (pw, 40)] : List Ivl), ¬ CellHits x.toNat j := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact hno _ (by simp)
    · intro ⟨c1, c2⟩; dsimp only at c1 c2
      exact hnf ⟨by dsimp only; omega, by dsimp only; omega⟩
  exact (h2 x hno2 hnf2).trans (h1 x hno hnf1)

private theorem ivlUnhit_of_fresh_sub {F : Type}
    {a b c : PanSemStateFiniteExact 64 F} {sp pw : Nat} {i : Ivl}
    (hbA : ArenaOK b) (hcA : ArenaOK c)
    (hi_in : Inside i (globN a "heap_ptr") (globN b "heap_ptr"))
    (hhb : globN b "heap_ptr" ≤ globN c "heap_ptr")
    (hsp8 : sp % 8 = 0)
    (hpw_hi : pw + 40 ≤ globN a "heap_ptr") (hpw8 : pw % 8 = 0)
    (hfr : FrameOutside b c [(sp, 0), (pw, 40)] (globN b "heap_ptr", globN c "heap_ptr" - globN b "heap_ptr")) :
    M08IvlUnhit b c i := by
  intro x hx8 hx1 hx2
  apply hfr x
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact Wave8Contracts.M08.not_cellHits_of_disj hx8 hsp8 ⟨hx1, hx2⟩ (Or.inr (Or.inl rfl))
    · exact Wave8Contracts.M08.not_cellHits_of_disj hx8 hpw8 ⟨hx1, hx2⟩
        (Or.inr (Or.inr (Or.inr (by have := hi_in.1; omega))))
  · exact Wave8Contracts.M08.not_cellHits_of_disj hx8 hbA.2.2.2.2.2.1 ⟨hx1, hx2⟩
      (Or.inr (Or.inr (Or.inl (by have := hi_in.2; dsimp; omega))))

private theorem lstOK_objects_transfer_unhit {F : Type}
    {s0 b c : PanSemStateFiniteExact 64 F} {lw esz cap : Nat}
    (hb : ArenaReady b) (hc : ArenaReady c)
    (hlw8 : lw % 8 = 0) (hlw_nz : lw ≠ 0) (hcap : 1 ≤ cap) (hesz : 1 ≤ esz)
    (hlw_hi : lw + 24 ≤ globN b "heap_ptr")
    (hu : M08IvlUnhit b c (lw, 24))
    (hlst_b : LstOK b lw)
    (hobjs_b : lstObjects b lw esz = [(lw, 24), (lw + 24, esz * cap)])
    (hp_b : ∀ i ∈ lstObjects b lw esz, Inside i (globN s0 "heap_ptr") (globN b "heap_ptr") ∧ WordsOK b i)
    (hs0_lo : sourceBase ≤ globN s0 "heap_ptr")
    (hhb : globN b "heap_ptr" ≤ globN c "heap_ptr") :
    LstOK c lw ∧
    lstObjects c lw esz = [(lw, 24), (lw + 24, esz * cap)] ∧
    (∀ i ∈ lstObjects c lw esz, Allocated c i ∧ WordsOK c i ∧
      Inside i (globN s0 "heap_ptr") (globN b "heap_ptr")) := by
  have h264 : heapLimit < 2 ^ 64 := by decide
  have hb_lim := hb.2.2.1
  have hm0 : memW c lw = memW b lw := by
    simpa using Wave8Contracts.M08.memW_eq_of_ivlUnhit hu hlw8 (by omega) ⟨by omega, by omega⟩
  have hm8 : memW c (lw + 8) = memW b (lw + 8) :=
    Wave8Contracts.M08.memW_eq_of_ivlUnhit hu (by omega) (by omega) ⟨by omega, by omega⟩
  have hm16 : memW c (lw + 16) = memW b (lw + 16) :=
    Wave8Contracts.M08.memW_eq_of_ivlUnhit hu (by omega) (by omega) ⟨by omega, by omega⟩
  have hlst_c : LstOK c lw := by
    unfold LstOK at hlst_b ⊢; rw [hm8, hm16]; exact hlst_b
  have hobjs_c : lstObjects c lw esz = [(lw, 24), (lw + 24, esz * cap)] := by
    have heq : lstObjects c lw esz = lstObjects b lw esz := by
      unfold lstObjects; rw [hm0, hm16]
    exact heq.trans hobjs_b
  refine ⟨hlst_c, hobjs_c, fun i hi => ?_⟩
  rw [hobjs_c, ← hobjs_b] at hi
  obtain ⟨hin, hw⟩ := hp_b i hi
  exact ⟨Or.inl ⟨le_trans hs0_lo hin.1, le_trans hin.2 hhb⟩, wordsOK_transfer hb.1 hc.1 hw, hin⟩

private def balEnsureAllocProg : ProgHOL 64 :=
  .decCall (ofString "ad") .one (ofString "alloc") [.const 40#64]
    (.decCall (ofString "t") .one (ofString "htab_new") [.const 32#64, .const 8#64]
      (.seq (.store (.op .add [.var .local (ofString "ad"), .const 0#64]) (.var .local (ofString "t")))
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 32#64, .const 8#64])
      (.seq (.store (.op .add [.var .local (ofString "ad"), .const 8#64]) (.var .local (ofString "t")))
      (.decCall (ofString "l") .one (ofString "lst_new") [.const 40#64, .const 4#64]
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const 16#64]) (.var .local (ofString "l")))
        (.seq (.call (some (some (.local, ofString "l"), none)) (ofString "lst_new") [.const 16#64, .const 4#64])
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const 24#64]) (.var .local (ofString "l")))
        (.seq (.call (some (some (.local, ofString "l"), none)) (ofString "lst_new") [.const 24#64, .const 2#64])
        (.seq (.store (.op .add [.var .local (ofString "ad"), .const 32#64]) (.var .local (ofString "l")))
        (.seq (.call (some (none, none)) (ofString "htab_set")
          [.var .global (ofString "bal_accounts"), .var .local (ofString "addr"), .var .local (ofString "ad")])
          (.return (.var .local (ofString "ad"))))))))))))))

private theorem balEnsureAlloc_eval {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw addrw : BitVec 64)
    (hAR : ArenaReady s)
    (hroot : s.globals.lookup (ofString "bal_accounts") = some (.val (.word tw)))
    (haddr : s.locals.lookup (ofString "addr") = some (.val (.word addrw)))
    (htnz : tw.toNat ≠ 0)
    (hWF_tw : HtabWF s tw.toNat)
    (hal_tw : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i)
    (hnt : (evaluateHOLFiniteState s balEnsureAllocProg).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s balEnsureAllocProg).1) :
    ∃ (pw t0w t8w l16w l24w l32w : BitVec 64) (s1 s5 mid : PanSemStateFiniteExact 64 F),
      pw.toNat = globN s "heap_ptr" ∧
      pw.toNat % 8 = 0 ∧ pw.toNat ≠ 0 ∧
      pw.toNat + 40 ≤ t0w.toNat ∧
      t0w.toNat + 88 ≤ globN s1 "heap_ptr" ∧
      globN s1 "heap_ptr" ≤ t8w.toNat ∧
      t8w.toNat + 88 ≤ l16w.toNat ∧
      l16w.toNat + 24 + 160 = l24w.toNat ∧
      l24w.toNat + 24 + 64 = l32w.toNat ∧
      l32w.toNat + 24 + 48 = globN s5 "heap_ptr" ∧
      ArenaReady s5 ∧ s5.be = s.be ∧
      globN s5 "scratch_ptr" = globN s "scratch_ptr" ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = s5.globals.lookup k) ∧
      FrameOutside s s5 [(globN s "scratch_ptr", 0)]
        (globN s "heap_ptr", globN s5 "heap_ptr" - globN s "heap_ptr") ∧
      HtabWF s5 t0w.toNat ∧ hdr s5 t0w.toNat 3 = 0 ∧ hdr s5 t0w.toNat 0 = 32 ∧
      (∀ i ∈ htabFootprint s5 t0w.toNat, Allocated s5 i ∧ Inside i (pw.toNat + 40) (globN s1 "heap_ptr")) ∧
      HtabWF s5 t8w.toNat ∧ hdr s5 t8w.toNat 3 = 0 ∧ hdr s5 t8w.toNat 0 = 32 ∧
      (∀ i ∈ htabFootprint s5 t8w.toNat, Allocated s5 i ∧ Inside i (globN s1 "heap_ptr") l16w.toNat) ∧
      (∀ t ∈ ([t0w.toNat, t8w.toNat] : List Nat), ∀ u ∈ ([t0w.toNat, t8w.toNat] : List Nat),
        t ≠ u → ∀ i ∈ htabFootprint s5 t, ∀ j ∈ htabFootprint s5 u, Disj i j) ∧
      memW s5 pw.toNat = t0w.toNat ∧
      memW s5 (pw.toNat + 8) = t8w.toNat ∧
      memW s5 (pw.toNat + 16) = l16w.toNat ∧
      memW s5 (pw.toNat + 24) = l24w.toNat ∧
      memW s5 (pw.toNat + 32) = l32w.toNat ∧
      LstOK s5 l16w.toNat ∧ lstObjects s5 l16w.toNat 40 = [(l16w.toNat, 24), (l16w.toNat + 24, 160)] ∧
      LstOK s5 l24w.toNat ∧ lstObjects s5 l24w.toNat 16 = [(l24w.toNat, 24), (l24w.toNat + 24, 64)] ∧
      LstOK s5 l32w.toNat ∧ lstObjects s5 l32w.toNat 24 = [(l32w.toNat, 24), (l32w.toNat + 24, 48)] ∧
      HtabExitAt tw.toNat s5 mid ∧
      HtabSetValuesPost s5 mid tw.toNat pw.toNat ∧
      mid.be = s5.be ∧ pw.toNat ∈ balRecords mid ∧
      (evaluateHOLFiniteState s balEnsureAllocProg).1 = some (.returned (.val (.word pw))) ∧
      ∃ L_out, (evaluateHOLFiniteState s balEnsureAllocProg).2 =
        { mid with locals := L_out } := by
  unfold balEnsureAllocProg at hnt hres ⊢
  have hsp8 : (globN s "scratch_ptr") % 8 = 0 := hAR.2.2.2.2.2.2.2.2.1
  have hs_lo : sourceBase ≤ globN s "heap_ptr" := hAR.2.1
  have hsb_pos : 0 < sourceBase := by decide
  obtain ⟨pw, qw, s0, hpw_eq, hqw_eq, hqw_lim, hpw_le_qw, hpw8, _, hhp_s0, hsp_s0, _,
    hA0, hmem0, _, hbe0, _, had0, hloc0, hgl0, hnt0, hres0, heq0_fst, heq0_snd⟩ :=
    decCall_alloc_resumes s (ofString "ad") (.const 40#64) 40#64 _ hAR
      (by simp [evalHOLExact]) hnt hres
  have hhp_s0' : globN s0 "heap_ptr" = pw.toNat + 40 := by
    rw [hhp_s0, hqw_eq]
    rfl
  have hpw_lo : sourceBase ≤ pw.toNat := by omega
  have hpw_nz : pw.toNat ≠ 0 := by omega
  have hfr_s_s0 : FrameOutside s s0 [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN s0 "heap_ptr" - globN s "heap_ptr") :=
    fun a _ _ => by rw [hmem0]
  obtain ⟨t0w, s1, ht0_lo, ht0_hi, hA1, hbe1, hsp1, hwf_t0_1, hcnt_t0_1, hkey_t0_1,
    hfp_t0_1, hm0_1, _, hfr01, _, hloc1, hgl1, hnt1, hres1, heq1_fst, heq1_snd⟩ :=
    decCall_htab_new_store_bal_slot s0 pw 0#64 _ hA0 had0 hpw_lo (by omega) hpw8
      (by decide) (by decide) hnt0 hres0
  have had1 : s1.locals.lookup (ofString "ad") = some (.val (.word pw)) :=
    (hloc1 _ (by decide)).trans had0
  have hsp1' : globN s1 "scratch_ptr" = globN s "scratch_ptr" := hsp1.trans hsp_s0
  obtain ⟨t8w, s2, ht8_lo, ht8_hi, hA2, hbe2, hsp2, hwf_t8_2, hcnt_t8_2, hkey_t8_2,
    hfp_t8_2, hm8_2, hoth2, hfr12, _, hloc2, hgl2, hnt2, hres2, heq2⟩ :=
    seq_htab_new_store_bal_slot s1 pw 8#64 _ hA1 had1 hpw_lo (by omega) hpw8
      (by decide) (by decide) hnt1 hres1
  have had2 : s2.locals.lookup (ofString "ad") = some (.val (.word pw)) :=
    (hloc2 _ (by decide)).trans had1
  have hsp2' : globN s2 "scratch_ptr" = globN s "scratch_ptr" := hsp2.trans hsp1'
  obtain ⟨l16w, s3, hl16_eq, hl16_8, hl16_nz, hhp_s3, hlt_23, hA3, hbe3, hsp3,
    hlst16_3, hobjs16_3, _, hp16_3, hm16_3, hoth3, hfr23, _, hloc3, hgl3, hnt3, hres3,
    heq3_fst, heq3_snd⟩ :=
    decCall_lst_new_store_bal_slot s2 pw 16#64 40#64 4#64 _ hA2 had2 hpw_lo (by omega) hpw8
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hnt2 hres2
  have had3 : s3.locals.lookup (ofString "ad") = some (.val (.word pw)) :=
    (hloc3 _ (by decide)).trans had2
  have hsp3' : globN s3 "scratch_ptr" = globN s "scratch_ptr" := hsp3.trans hsp2'
  obtain ⟨l24w, s4, hl24_eq, hl24_8, hl24_nz, hhp_s4, hlt_34, hA4, hbe4, hsp4,
    hlst24_4, hobjs24_4, _, hp24_4, hm24_4, hoth4, hfr34, _, hloc4, hgl4, hnt4, hres4, heq4⟩ :=
    seq_lst_new_store_bal_slot s3 pw 24#64 16#64 4#64 _ hA3 had3 hpw_lo (by omega) hpw8
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hnt3 hres3
  have had4 : s4.locals.lookup (ofString "ad") = some (.val (.word pw)) :=
    (hloc4 _ (by decide)).trans had3
  have hsp4' : globN s4 "scratch_ptr" = globN s "scratch_ptr" := hsp4.trans hsp3'
  obtain ⟨l32w, s5, hl32_eq, hl32_8, hl32_nz, hhp_s5, hlt_45, hA5, hbe5, hsp5,
    hlst32_5, hobjs32_5, _, hp32_5, hm32_5, hoth5, hfr45, _, hloc5, hgl5, hnt5, hres5, heq5⟩ :=
    seq_lst_new_store_bal_slot s4 pw 32#64 24#64 2#64 _ hA4 had4 hpw_lo (by omega) hpw8
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hnt4 hres4
  have had5 : s5.locals.lookup (ofString "ad") = some (.val (.word pw)) :=
    (hloc5 _ (by decide)).trans had4
  have haddr5 : s5.locals.lookup (ofString "addr") = some (.val (.word addrw)) := by
    rw [hloc5 _ (by decide), hloc4 _ (by decide), hloc3 _ (by decide),
        hloc2 _ (by decide), hloc1 _ (by decide), hloc0 _ (by decide)]
    exact haddr
  have hsp5' : globN s5 "scratch_ptr" = globN s "scratch_ptr" := hsp5.trans hsp4'
  have hgl_s5 : ∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = s5.globals.lookup k :=
    fun k hk => (hgl0 k hk).trans ((hgl1 k hk).trans ((hgl2 k hk).trans
      ((hgl3 k hk).trans ((hgl4 k hk).trans (hgl5 k hk)))))
  have hbe_s5 : s5.be = s.be := hbe5.trans (hbe4.trans (hbe3.trans (hbe2.trans (hbe1.trans hbe0))))
  -- Arithmetic on fresh bounds
  have hc16 : (40#64 : BitVec 64).toNat * (4#64 : BitVec 64).toNat = 160 := rfl
  have hc24 : (16#64 : BitVec 64).toNat * (4#64 : BitVec 64).toNat = 64 := rfl
  have hc32 : (24#64 : BitVec 64).toNat * (2#64 : BitVec 64).toNat = 48 := rfl
  have hesz40 : (40#64 : BitVec 64).toNat = 40 := rfl
  have hesz16 : (16#64 : BitVec 64).toNat = 16 := rfl
  have hesz24 : (24#64 : BitVec 64).toNat = 24 := rfl
  rw [hc16] at hhp_s3 hobjs16_3
  rw [hc24] at hhp_s4 hobjs24_4
  rw [hc32] at hhp_s5 hobjs32_5
  rw [hesz40] at hobjs16_3 hp16_3
  rw [hesz16] at hobjs24_4 hp24_4
  rw [hesz24] at hobjs32_5 hp32_5
  have ho0 : (0#64 : BitVec 64).toNat = 0 := rfl
  have ho8 : (8#64 : BitVec 64).toNat = 8 := rfl
  have ho16 : (16#64 : BitVec 64).toNat = 16 := rfl
  have ho24 : (24#64 : BitVec 64).toNat = 24 := rfl
  have ho32 : (32#64 : BitVec 64).toNat = 32 := rfl
  rw [ho0, Nat.add_zero] at hm0_1
  rw [ho8] at hm8_2 hoth2
  rw [ho16] at hm16_3 hoth3
  rw [ho24] at hm24_4 hoth4
  rw [ho32] at hm32_5 hoth5
  -- Compose FrameOutside s1..s5 with [(sp, 0), (pw, 40)] and absorb into FrameOutside s..s5
  rw [hsp_s0] at hfr01
  rw [hsp1'] at hfr12
  rw [hsp2'] at hfr23
  rw [hsp3'] at hfr34
  rw [hsp4'] at hfr45
  have hfr_s_s1 := frameOutside_keep_absorb_fresh ⟨hpw_eq, by omega⟩ (by omega) hfr_s_s0 hfr01
  have hfr_s_s2 := frameOutside_keep_absorb_fresh ⟨hpw_eq, by omega⟩ (by omega) hfr_s_s1 hfr12
  have hfr_s_s3 := frameOutside_keep_absorb_fresh ⟨hpw_eq, by omega⟩ (by omega) hfr_s_s2 hfr23
  have hfr_s_s4 := frameOutside_keep_absorb_fresh ⟨hpw_eq, by omega⟩ (by omega) hfr_s_s3 hfr34
  have hfr_s_s5 := frameOutside_keep_absorb_fresh ⟨hpw_eq, by omega⟩ (by omega) hfr_s_s4 hfr45
  -- Transfer tw HtabWF from s to s5
  have hu_tw_s5 : ∀ i ∈ htabFootprint s tw.toNat, M08IvlUnhit s s5 i := fun i hi =>
    ivlUnhit_of_allocated_heap_sp0 hAR.2 hA5.2 (hal_tw i hi)
      (fun j hj => by rcases List.mem_singleton.1 hj with rfl; exact ⟨_, rfl, hsp8⟩)
      hfr_s_s5
  have hag_s_s5 : AllocatorGrows s s5 := ⟨by omega, by rw [hsp5']⟩
  obtain ⟨hwf_tw_5, hfp_tw_eq, _⟩ := htabWF_transfer_unhit hAR hA5 hWF_tw hu_tw_s5
    (fun i hi => hag_s_s5.allocated (hal_tw i hi))
  have hal_tw_5 : ∀ i ∈ htabFootprint s5 tw.toNat, Allocated s5 i := by
    rw [hfp_tw_eq]; exact fun i hi => hag_s_s5.allocated (hal_tw i hi)
  have hroot5 : s5.globals.lookup (ofString "bal_accounts") = some (.val (.word tw)) :=
    (hgl_s5 _ (by decide)).symm.trans hroot
  -- Execute final htab_set + return
  obtain ⟨mid, hexit, hvalues, hbe_mid, _, hmem_rec, heval_ins⟩ :=
    bal_ensure_insert_return s5 tw addrw pw hA5 hroot5 haddr5 had5 htnz hwf_tw_5 hal_tw_5 hnt5 hres5
  -- Compose sub-frames across intermediate steps (for preserving t0w, t8w, l16w, l24w, pw slots)
  have hfr_1_5 : FrameOutside s1 s5 [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
      (globN s1 "heap_ptr", globN s5 "heap_ptr" - globN s1 "heap_ptr") := by
    intro x hno hnf
    have hnf12 : ¬ CellHits x.toNat (globN s1 "heap_ptr", globN s2 "heap_ptr" - globN s1 "heap_ptr") :=
      fun ⟨c1, c2⟩ => hnf ⟨c1, by dsimp at c1 c2 ⊢; omega⟩
    have hnf23 : ¬ CellHits x.toNat (globN s2 "heap_ptr", globN s3 "heap_ptr" - globN s2 "heap_ptr") :=
      fun ⟨c1, c2⟩ => hnf ⟨by dsimp at c1 c2 ⊢; omega, by dsimp at c1 c2 ⊢; omega⟩
    have hnf34 : ¬ CellHits x.toNat (globN s3 "heap_ptr", globN s4 "heap_ptr" - globN s3 "heap_ptr") :=
      fun ⟨c1, c2⟩ => hnf ⟨by dsimp at c1 c2 ⊢; omega, by dsimp at c1 c2 ⊢; omega⟩
    have hnf45 : ¬ CellHits x.toNat (globN s4 "heap_ptr", globN s5 "heap_ptr" - globN s4 "heap_ptr") :=
      fun ⟨c1, c2⟩ => hnf ⟨by dsimp at c1 c2 ⊢; omega, by dsimp at c1 c2 ⊢; omega⟩
    exact (hfr45 x hno hnf45).trans ((hfr34 x hno hnf34).trans
      ((hfr23 x hno hnf23).trans (hfr12 x hno hnf12)))
  have hfr_2_5 : FrameOutside s2 s5 [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
      (globN s2 "heap_ptr", globN s5 "heap_ptr" - globN s2 "heap_ptr") := by
    intro x hno hnf
    have hnf23 : ¬ CellHits x.toNat (globN s2 "heap_ptr", globN s3 "heap_ptr" - globN s2 "heap_ptr") :=
      fun ⟨c1, c2⟩ => hnf ⟨c1, by dsimp at c1 c2 ⊢; omega⟩
    have hnf34 : ¬ CellHits x.toNat (globN s3 "heap_ptr", globN s4 "heap_ptr" - globN s3 "heap_ptr") :=
      fun ⟨c1, c2⟩ => hnf ⟨by dsimp at c1 c2 ⊢; omega, by dsimp at c1 c2 ⊢; omega⟩
    have hnf45 : ¬ CellHits x.toNat (globN s4 "heap_ptr", globN s5 "heap_ptr" - globN s4 "heap_ptr") :=
      fun ⟨c1, c2⟩ => hnf ⟨by dsimp at c1 c2 ⊢; omega, by dsimp at c1 c2 ⊢; omega⟩
    exact (hfr45 x hno hnf45).trans ((hfr34 x hno hnf34).trans (hfr23 x hno hnf23))
  have hfr_3_5 : FrameOutside s3 s5 [(globN s "scratch_ptr", 0), (pw.toNat, 40)]
      (globN s3 "heap_ptr", globN s5 "heap_ptr" - globN s3 "heap_ptr") := by
    intro x hno hnf
    have hnf34 : ¬ CellHits x.toNat (globN s3 "heap_ptr", globN s4 "heap_ptr" - globN s3 "heap_ptr") :=
      fun ⟨c1, c2⟩ => hnf ⟨c1, by dsimp at c1 c2 ⊢; omega⟩
    have hnf45 : ¬ CellHits x.toNat (globN s4 "heap_ptr", globN s5 "heap_ptr" - globN s4 "heap_ptr") :=
      fun ⟨c1, c2⟩ => hnf ⟨by dsimp at c1 c2 ⊢; omega, by dsimp at c1 c2 ⊢; omega⟩
    exact (hfr45 x hno hnf45).trans (hfr34 x hno hnf34)
  -- Transfer t0w from s1 to s5
  have hu_t0 : ∀ i ∈ htabFootprint s1 t0w.toNat, M08IvlUnhit s1 s5 i := fun i hi =>
    ivlUnhit_of_fresh_sub (a := s0) hA1.2 hA5.2 (hfp_t0_1 i hi).2 (by omega) hsp8 (by omega) hpw8 hfr_1_5
  have hag_1_5 : AllocatorGrows s1 s5 := ⟨by omega, by rw [hsp5', hsp1']⟩
  obtain ⟨hwf_t0_5, hfp_t0_eq, hhdr_t0_5⟩ := htabWF_transfer_unhit hA1 hA5 hwf_t0_1 hu_t0
    (fun i hi => hag_1_5.allocated (hfp_t0_1 i hi).1)
  have hcnt_t0_5 : hdr s5 t0w.toNat 3 = 0 := (hhdr_t0_5 3 (by omega)).trans hcnt_t0_1
  have hkey_t0_5 : hdr s5 t0w.toNat 0 = 32 := (hhdr_t0_5 0 (by omega)).trans hkey_t0_1
  have hfp_t0_5 : ∀ i ∈ htabFootprint s5 t0w.toNat, Allocated s5 i ∧ Inside i (pw.toNat + 40) (globN s1 "heap_ptr") := by
    rw [hfp_t0_eq]
    intro i hi
    obtain ⟨hal, hin⟩ := hfp_t0_1 i hi
    exact ⟨hag_1_5.allocated hal, ⟨by have := hin.1; omega, hin.2⟩⟩
  -- Transfer t8w from s2 to s5
  have hu_t8 : ∀ i ∈ htabFootprint s2 t8w.toNat, M08IvlUnhit s2 s5 i := fun i hi =>
    ivlUnhit_of_fresh_sub (a := s1) hA2.2 hA5.2 (hfp_t8_2 i hi).2 (by omega) hsp8 (by omega) hpw8 hfr_2_5
  have hag_2_5 : AllocatorGrows s2 s5 := ⟨by omega, by rw [hsp5', hsp2']⟩
  obtain ⟨hwf_t8_5, hfp_t8_eq, hhdr_t8_5⟩ := htabWF_transfer_unhit hA2 hA5 hwf_t8_2 hu_t8
    (fun i hi => hag_2_5.allocated (hfp_t8_2 i hi).1)
  have hcnt_t8_5 : hdr s5 t8w.toNat 3 = 0 := (hhdr_t8_5 3 (by omega)).trans hcnt_t8_2
  have hkey_t8_5 : hdr s5 t8w.toNat 0 = 32 := (hhdr_t8_5 0 (by omega)).trans hkey_t8_2
  have hfp_t8_5 : ∀ i ∈ htabFootprint s5 t8w.toNat, Allocated s5 i ∧ Inside i (globN s1 "heap_ptr") l16w.toNat := by
    rw [hfp_t8_eq]
    intro i hi
    obtain ⟨hal, hin⟩ := hfp_t8_2 i hi
    exact ⟨hag_2_5.allocated hal, ⟨hin.1, by have := hin.2; omega⟩⟩
  have hpw_tabs : ∀ t ∈ ([t0w.toNat, t8w.toNat] : List Nat), ∀ u ∈ ([t0w.toNat, t8w.toNat] : List Nat),
      t ≠ u → ∀ i ∈ htabFootprint s5 t, ∀ j ∈ htabFootprint s5 u, Disj i j := by
    intro t ht u hu hne i hi j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht hu
    rcases ht with rfl | rfl <;> rcases hu with rfl | rfl
    · exact absurd rfl hne
    · exact disj_fresh_sub (hfp_t0_5 i hi).2 (hfp_t8_5 j hj).2 le_rfl
    · exact disj_flip (disj_fresh_sub (hfp_t0_5 j hj).2 (hfp_t8_5 i hi).2 le_rfl)
    · exact absurd rfl hne
  -- Transfer l16w from s3 to s5, and l24w from s4 to s5
  have hu_l16 : M08IvlUnhit s3 s5 (l16w.toNat, 24) :=
    ivlUnhit_of_fresh_sub (a := s2) hA3.2 hA5.2 ⟨by omega, by omega⟩ (by omega) hsp8 (by omega) hpw8 hfr_3_5
  obtain ⟨hlst16_5, hobjs16_5, _⟩ := lstOK_objects_transfer_unhit (s0 := s2) (lw := l16w.toNat) (esz := 40) (cap := 4)
    hA3 hA5 hl16_8 hl16_nz (by decide) (by decide) (by omega) hu_l16 hlst16_3 hobjs16_3
    (fun i hi => ⟨(hp16_3 i hi).2.2, (hp16_3 i hi).2.1⟩) hA2.2.1 (by omega)
  have hu_l24 : M08IvlUnhit s4 s5 (l24w.toNat, 24) :=
    ivlUnhit_of_fresh_sub (a := s3) hA4.2 hA5.2 ⟨by omega, by omega⟩ (by omega) hsp8 (by omega) hpw8 hfr45
  obtain ⟨hlst24_5, hobjs24_5, _⟩ := lstOK_objects_transfer_unhit (s0 := s3) (lw := l24w.toNat) (esz := 16) (cap := 4)
    hA4 hA5 hl24_8 hl24_nz (by decide) (by decide) (by omega) hu_l24 hlst24_4 hobjs24_4
    (fun i hi => ⟨(hp24_4 i hi).2.2, (hp24_4 i hi).2.1⟩) hA3.2.1 (by omega)
  -- Slot values at pw + 0, 8, 16, 24, 32 in s5
  have hm0_5 : memW s5 pw.toNat = t0w.toNat := by
    have h0 := (hoth5 0 (by omega) (by omega)).trans ((hoth4 0 (by omega) (by omega)).trans
      ((hoth3 0 (by omega) (by omega)).trans (hoth2 0 (by omega) (by omega))))
    simpa using h0.trans hm0_1
  have hm8_5 : memW s5 (pw.toNat + 8) = t8w.toNat :=
    ((hoth5 8 (by omega) (by omega)).trans ((hoth4 8 (by omega) (by omega)).trans
      (hoth3 8 (by omega) (by omega)))).trans hm8_2
  have hm16_5 : memW s5 (pw.toNat + 16) = l16w.toNat :=
    ((hoth5 16 (by omega) (by omega)).trans (hoth4 16 (by omega) (by omega))).trans hm16_3
  have hm24_5 : memW s5 (pw.toNat + 24) = l24w.toNat :=
    (hoth5 24 (by omega) (by omega)).trans hm24_4
  -- Chain evaluation
  have hev_fst : (evaluateHOLFiniteState s balEnsureAllocProg).1 =
      some (.returned (.val (.word pw))) := by
    unfold balEnsureAllocProg
    rw [heq0_fst, heq1_fst, heq2, heq3_fst, heq4, heq5, heval_ins]
  have hev_snd : ∃ L_out, (evaluateHOLFiniteState s balEnsureAllocProg).2 =
      { mid with locals := L_out } := by
    let L_final :=
      HolFiniteMapExact.resVarEq
        (HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq (mid.emptyLocalsHOLFinite).locals
            (ofString "l", s2.locals.lookup (ofString "l")))
          (ofString "t", s0.locals.lookup (ofString "t")))
        (ofString "ad", s.locals.lookup (ofString "ad"))
    refine ⟨L_final, ?_⟩
    unfold balEnsureAllocProg
    rw [heq0_snd, heq1_snd, heq2, heq3_snd, heq4, heq5, heval_ins]
    rfl
  refine ⟨pw, t0w, t8w, l16w, l24w, l32w, s1, s5, mid,
    hpw_eq, hpw8, hpw_nz,
    by omega, ht0_hi, ht8_lo, by omega, by omega, by omega, hhp_s5.symm,
    hA5, hbe_s5, hsp5', hgl_s5, hfr_s_s5,
    hwf_t0_5, hcnt_t0_5, hkey_t0_5, hfp_t0_5,
    hwf_t8_5, hcnt_t8_5, hkey_t8_5, hfp_t8_5, hpw_tabs,
    hm0_5, hm8_5, hm16_5, hm24_5, hm32_5,
    hlst16_5, by simpa using hobjs16_5, hlst24_5, by simpa using hobjs24_5, hlst32_5, hobjs32_5,
    hexit, hvalues, hbe_mid, hmem_rec, hev_fst, hev_snd⟩

private theorem disj_fresh_of_zero_or_allocated_add {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hAp : ArenaOK post) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {j : Ivl} (hj : j.2 = 0 ∨ Allocated s j) :
    Disj j (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
  have hsep : heapLimit ≤ scratchStart := by decide
  obtain ⟨_, hs_hp, hs_fm, hs_sc, _⟩ := hAs
  obtain ⟨_, hp_hp, _, _, _⟩ := hAp
  rcases hj with hz | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · exact Or.inl hz
  · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
  · exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))

private theorem m08_ivlUnhit_of_frameOutside_add {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh i : Ivl}
    (hfr : FrameOutside s post keep fresh)
    (hk_al : ∀ j ∈ keep, j.1 % 8 = 0)
    (hf_al : fresh.1 % 8 = 0)
    (hk : ∀ j ∈ keep, Disj i j) (hf : Disj i fresh) :
    M08IvlUnhit s post i := by
  intro a ha8 h1 h2
  apply hfr a
  · intro j hj hcj
    exact absurd hcj (Wave8Contracts.M08.not_cellHits_of_disj ha8 (hk_al j hj) ⟨h1, h2⟩ (hk j hj))
  · intro hcf
    exact absurd hcf (Wave8Contracts.M08.not_cellHits_of_disj ha8 hf_al ⟨h1, h2⟩ hf)

private theorem fixedTyped_of_balObjects_set_values_add {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {v : Nat} {fresh : List Ivl}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hag : AllocatorGrows s post) (hF : FixedTyped s)
    (hgs : Wave8Contracts.M08.WorldGlobalsSame s post)
    (hbo_eq : blockOutObjects post = blockOutObjects s)
    (hnz : globN s "bal_accounts" ≠ 0)
    (hval : HtabSetValuesPost s post (globN s "bal_accounts") v)
    (hold_obj : ∀ ad ∈ balRecords s,
      (ad, 40) :: lstObjects post (memW post (ad + 16)) 40 ++
        lstObjects post (memW post (ad + 24)) 16 ++
        lstObjects post (memW post (ad + 32)) 24 ++
        (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) =
      (ad, 40) :: lstObjects s (memW s (ad + 16)) 40 ++
        lstObjects s (memW s (ad + 24)) 16 ++
        lstObjects s (memW s (ad + 32)) 24 ++
        (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40))
    (hv_obj : (v, 40) :: lstObjects post (memW post (v + 16)) 40 ++
        lstObjects post (memW post (v + 24)) 16 ++
        lstObjects post (memW post (v + 32)) 24 ++
        (htabValues post (memW post v)).flatMap (fun l => lstObjects post l 40) = fresh)
    (hfresh : ∀ i ∈ fresh,
      Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∧ WordsOK post i)
    (hpw_fresh : fresh.Pairwise Disj) :
    FixedTyped post ∧
    (∀ o ∈ fixedObjects post, o ∈ fixedObjects s ∨ o = (0, 0) ∨
      Inside o (globN s "heap_ptr") (globN post "heap_ptr")) := by
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" :=
    hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  obtain ⟨_, _, hbal_mem⟩ := balRecords_set_values_add hba_g hnz hval
  have hbal_class : ∀ i ∈ balObjects post, i ∈ balObjects s ∨ i ∈ fresh := by
    intro i hi
    unfold balObjects at hi
    obtain ⟨ad, had, hi_ad⟩ := List.mem_flatMap.1 hi
    rcases hbal_mem ad had with had_s | rfl
    · left
      rw [hold_obj ad had_s] at hi_ad
      unfold balObjects
      exact List.mem_flatMap.2 ⟨ad, had_s, hi_ad⟩
    · right
      rwa [hv_obj] at hi_ad
  have hprefix_eq :
      (globalBuffers.map fun gn => (globN post gn.1, if globN post gn.1 = 0 then 0 else gn.2)) ++
        [(if globN post "journal_cap" = 0 then 0 else globN post "journal", 32 * globN post "journal_cap")] ++
        blockOutObjects post =
      (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++
        [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
        blockOutObjects s := by
    have hgb : (globalBuffers.map fun gn => (globN post gn.1, if globN post gn.1 = 0 then 0 else gn.2)) =
        (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
      apply List.map_congr_left
      intro gn hgn
      rw [hgs.1 gn hgn]
    rw [hgb, hgs.2.2.1, hgs.2.2.2.1, hbo_eq]
  have hfix_class : ∀ o ∈ fixedObjects post, o ∈ fixedObjects s ∨ o ∈ fresh := by
    intro o ho
    unfold fixedObjects at ho
    rw [hprefix_eq] at ho
    rcases List.mem_append.1 ho with hpre | hbal
    · left; unfold fixedObjects; exact List.mem_append_left _ hpre
    · rcases hbal_class o hbal with hb_s | hfr
      · left; unfold fixedObjects; exact List.mem_append_right _ hb_s
      · exact Or.inr hfr
  let objects : Nat → List Ivl := fun ad =>
    if ad = v then fresh
    else (ad, 40) :: lstObjects s (memW s (ad + 16)) 40 ++
      lstObjects s (memW s (ad + 24)) 16 ++
      lstObjects s (memW s (ad + 32)) 24 ++
      (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40)
  have hv_not_old : v ∉ balRecords s := by
    intro hv_s
    have hv_bal : (v, 40) ∈ balObjects s := by
      unfold balObjects; exact List.mem_flatMap.2 ⟨v, hv_s, by simp⟩
    have hv_fix : (v, 40) ∈ fixedObjects s := by
      unfold fixedObjects; exact List.mem_append_right _ hv_bal
    rcases hF.1 _ hv_fix with h0 | ⟨hal_v, _⟩
    · simp at h0
    · have hv_fr : (v, 40) ∈ fresh := by rw [← hv_obj]; simp
      have hd := Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_v (hfresh _ hv_fr).1
      rcases hd with h | h | h | h <;> dsimp at h <;> omega
  have hold_eq_objects : (balRecords s).flatMap objects = balObjects s := by
    unfold balObjects
    apply List.flatMap_congr
    intro ad had
    have hne : ad ≠ v := fun heq => hv_not_old (heq ▸ had)
    simp [objects, hne]
  have hpost_objects : ∀ ad ∈ balRecords post,
      (ad, 40) :: lstObjects post (memW post (ad + 16)) 40 ++
        lstObjects post (memW post (ad + 24)) 16 ++
        lstObjects post (memW post (ad + 32)) 24 ++
        (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) = objects ad := by
    intro ad had
    rcases hbal_mem ad had with had_s | rfl
    · have hne : ad ≠ v := fun heq => hv_not_old (heq ▸ had_s)
      simp only [objects, if_neg hne]
      exact hold_obj ad had_s
    · simp only [objects, if_true]
      exact hv_obj
  obtain ⟨hpw_pre, hpw_bal_s, hcross_pre_bal⟩ := by
    have h := hF.2
    unfold fixedObjects at h
    exact List.pairwise_append.1 h
  have hpw_bal_post : (balObjects post).Pairwise Disj := by
    apply pairwise_balObjects_set_values_add hba_g hnz hval objects hpost_objects
    · rw [hold_eq_objects]; exact hpw_bal_s
    · simp only [objects, if_true]; exact hpw_fresh
    · intro a ha b hb
      rw [hold_eq_objects] at ha
      simp only [objects, if_true] at hb
      have ha_fix : a ∈ fixedObjects s := by unfold fixedObjects; exact List.mem_append_right _ ha
      rcases hF.1 a ha_fix with hz | ⟨hal_a, _⟩
      · exact Or.inl hz
      · exact disj_flip (disj_allocated_fresh_heap hAs.2 hAp.2 hal_a (hfresh b hb).1)
    · intro a ha b hb
      simp only [objects, if_true] at ha
      rw [hold_eq_objects] at hb
      have hb_fix : b ∈ fixedObjects s := by unfold fixedObjects; exact List.mem_append_right _ hb
      rcases hF.1 b hb_fix with hz | ⟨hal_b, _⟩
      · exact Or.inr (Or.inl hz)
      · exact disj_allocated_fresh_heap hAs.2 hAp.2 hal_b (hfresh a ha).1
  refine ⟨⟨?_, ?_⟩, fun o ho => ?_⟩
  · intro i hi
    rcases hfix_class i hi with hold | hnew
    · rcases hF.1 i hold with hz | ⟨hal, hw⟩
      · exact Or.inl hz
      · exact Or.inr ⟨hag.allocated hal, wordsOK_transfer hAs.1 hAp.1 hw⟩
    · obtain ⟨hin, hw⟩ := hfresh i hnew
      exact Or.inr ⟨Or.inl ⟨le_trans hAs.2.1 hin.1, hin.2⟩, hw⟩
  · unfold fixedObjects
    rw [hprefix_eq]
    refine List.pairwise_append.2 ⟨hpw_pre, hpw_bal_post, fun a ha b hb => ?_⟩
    rcases hbal_class b hb with hb_s | hb_fr
    · exact hcross_pre_bal a ha b hb_s
    · have ha_fix : a ∈ fixedObjects s := by unfold fixedObjects; exact List.mem_append_left _ ha
      rcases hF.1 a ha_fix with hz | ⟨hal_a, _⟩
      · exact Or.inl hz
      · exact disj_flip (disj_allocated_fresh_heap hAs.2 hAp.2 hal_a (hfresh b hb_fr).1)
  · rcases hfix_class o ho with hold | hnew
    · exact Or.inl hold
    · exact Or.inr (Or.inr (hfresh o hnew).1)

private theorem rolesOK_balEnsureAlloc {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    {v t0 t8 : Nat}
    (hA : ArenaOK s) (hT : TablesTyped s S) (hF : FixedTyped s)
    (hgs : Wave8Contracts.M08.WorldGlobalsSame s post)
    (hnz : globN s "bal_accounts" ≠ 0)
    (hval : HtabSetValuesPost s post (globN s "bal_accounts") v)
    (hu_other : ∀ u ∈ S, u ≠ globN s "bal_accounts" → ∀ i ∈ htabFootprint s u, M08IvlUnhit s post i)
    (hu_ws : globN s "ws" ≠ 0 → M08IvlUnhit s post (globN s "ws", 40))
    (hu_bs : globN s "bs" ≠ 0 → M08IvlUnhit s post (globN s "bs", 80))
    (hu_ts : globN s "ts" ≠ 0 → M08IvlUnhit s post (globN s "ts", 72))
    (hold_slots : ∀ ad ∈ balRecords s, memW post ad = memW s ad ∧ memW post (ad + 8) = memW s (ad + 8))
    (hv_slots : memW post v = t0 ∧ memW post (v + 8) = t8)
    (ht0_nz : t0 ≠ 0) (ht8_nz : t8 ≠ 0) (ht08_ne : t0 ≠ t8)
    (hhdr_t0 : hdr post t0 0 = 32) (hhdr_t8 : hdr post t8 0 = 32)
    (hhdr0_S : ∀ t ∈ S, hdr post t 0 = hdr s t 0)
    (hT_disj_S : ∀ t ∈ ([t0, t8] : List Nat), t ∉ S)
    (hjr_eq : journalRoleSlots post = journalRoleSlots s) :
    RolesOK post (S ++ [t0, t8]) (worldRoleSlots post) (journalRoleSlots post) := by
  have hws_g := hgs.1 ("ws", 40) (by simp [globalBuffers])
  have hbs_g := hgs.1 ("bs", 80) (by simp [globalBuffers])
  have hts_g := hgs.1 ("ts", 72) (by simp [globalBuffers])
  have hba_g := hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  have hbia_g := hgs.2.1 "bal_idx_accts" (by simp [globalTableRoots])
  have hbis_g := hgs.2.1 "bal_idx_stor" (by simp [globalTableRoots])
  obtain ⟨_, hno_bs32, hno_ts32, _, _⟩ := bal_accounts_role_props hT hnz
  have hrec_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] =
      recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
    unfold recRoles
    by_cases h : globN s "ws" = 0
    · simp [hws_g, h]
    · have hw16 := Wave8Contracts.M08.rec_word_eq_of_unhit hA hF "ws" 40 (by decide) hws_g h (hu_ws h) (k := 16) (by omega) (by omega)
      have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit hA hF "ws" 40 (by decide) hws_g h (hu_ws h) (k := 32) (by omega) (by omega)
      simp only [hws_g] at hw16 hw32 ⊢
      simp [h, hw16, hw32]
  have hrec_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
      recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
      (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
    unfold recRoles
    by_cases h : globN s "bs" = 0
    · simp [hbs_g, h]
    · simp only [hbs_g, h, ↓reduceIte]
      apply List.map_congr_left
      intro ⟨k, r0⟩ hkr
      have hk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
        rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact ⟨by omega, by omega⟩
      have hw := Wave8Contracts.M08.rec_word_eq_of_unhit hA hF "bs" 80 (by decide) hbs_g h (hu_bs h) hk.1 hk.2
      simp only [hbs_g] at hw; simp [hw]
  have hrec_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
      (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
      recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
      (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
    unfold recRoles
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · simp only [hts_g, h, ↓reduceIte]
      apply List.map_congr_left
      intro ⟨k, r0⟩ hkr
      have hk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
        rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact ⟨by omega, by omega⟩
      have hw := Wave8Contracts.M08.rec_word_eq_of_unhit hA hF "ts" 72 (by decide) hts_g h (hu_ts h) hk.1 hk.2
      simp only [hts_g] at hw; simp [hw]
  have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
    unfold nestRoles
    by_cases h : globN s "bs" = 0
    · simp [hbs_g, h]
    · have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit hA hF "bs" 80 (by decide) hbs_g h (hu_bs h) (k := 32) (by omega) (by omega)
      simp only [hbs_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
      by_cases h32 : memW s (globN s "bs" + 32) = 0
      · simp [h32]
      · simp only [h32, ↓reduceIte]
        have hmS : memW s (globN s "bs" + 32) ∈ S := by
          rcases hT.2.2.2.2.1 32 (by simp [bsTableSlots]) h with h0 | hm
          · exact absurd h0 h32
          · exact hm
        rw [Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_other _ hmS (hno_bs32 h))]
  have hnest_ts : nestRoles post "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
    unfold nestRoles
    by_cases h : globN s "ts" = 0
    · simp [hts_g, h]
    · have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit hA hF "ts" 72 (by decide) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
      simp only [hts_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
      by_cases h32 : memW s (globN s "ts" + 32) = 0
      · simp [h32]
      · simp only [h32, ↓reduceIte]
        have hmS : memW s (globN s "ts" + 32) ∈ S := by
          rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) h with h0 | hm
          · exact absurd h0 h32
          · exact hm
        rw [Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ hmS).1 (hu_other _ hmS (hno_ts32 h))]
  let nonbal_raw :=
    recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] ++
      recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"),
        (48, "bs+48"), (72, "bs+72")] ++
      recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"),
        (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] ++
      [(globN s "bal_accounts", "bal_accounts"), (globN s "bal_idx_accts", "bal_idx_accts"),
        (globN s "bal_idx_stor", "bal_idx_stor")] ++
      nestRoles s "bs" "bs.inner" ++ nestRoles s "ts" "ts.inner"
  let bal_fn_s : Nat → List (Nat × String) := fun ad => [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")]
  let bal_fn_p : Nat → List (Nat × String) := fun ad => [(memW post ad, "bal.stor"), (memW post (ad + 8), "bal.reads")]
  have hold_fn : ∀ ad ∈ balRecords s, bal_fn_p ad = bal_fn_s ad := by
    intro ad had
    obtain ⟨e0, e8⟩ := hold_slots ad had
    simp [bal_fn_p, bal_fn_s, e0, e8]
  have hv_fn_f : (bal_fn_p v).filter (fun a => a.1 != 0) = [(t0, "bal.stor"), (t8, "bal.reads")] := by
    simp [bal_fn_p, hv_slots.1, hv_slots.2, ht0_nz, ht8_nz]
  obtain ⟨hrecs_or, _, _⟩ := balRecords_set_values_add hba_g hnz hval
  rw [hjr_eq]
  refine rolesOK_adjoin_fresh_slots hT.2.2.2.2.2.2.2.2.2.2.2 hhdr0_S ?_ hT_disj_S
  have hwrs_s_eq : worldRoleSlots s =
      (nonbal_raw ++ (balRecords s).flatMap bal_fn_s).filter (fun a => a.1 != 0) := rfl
  have hwrs_p_eq : worldRoleSlots post =
      (nonbal_raw ++ (balRecords post).flatMap bal_fn_p).filter (fun a => a.1 != 0) := by
    unfold worldRoleSlots
    rw [hrec_ws, hrec_bs, hrec_ts, hba_g, hbia_g, hbis_g, hnest_bs, hnest_ts]
  rcases hrecs_or with h_app | ⟨idx, hidx_lt, h_set⟩
  · -- Append case
    have hfm_app : (balRecords post).flatMap bal_fn_p =
        (balRecords s).flatMap bal_fn_s ++ bal_fn_p v := by
      rw [h_app, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [List.flatMap_congr hold_fn]
    refine ⟨worldRoleSlots s, [(t0, "bal.stor"), (t8, "bal.reads")], [], ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwrs_p_eq, hfm_app, ← List.append_assoc, List.filter_append, hv_fn_f, List.append_nil, ← hwrs_s_eq]
    · intro a ha; rw [List.append_nil] at ha; exact ha
    · rw [List.append_nil]; exact hT.2.2.2.2.2.2.2.2.2.2.2.2.1
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨by simp, hhdr_t0.trans (show 32 = roleKeyLen "bal.stor" by decide)⟩
      · exact ⟨by simp, hhdr_t8.trans (show 32 = roleKeyLen "bal.reads" by decide)⟩
    · simp [ht08_ne]
  · -- Overwrite case (`balRecords post = (balRecords s).set idx v`)
    let pre_ads := (balRecords s).take idx
    let suf_ads := (balRecords s).drop (idx + 1)
    have hsplit_s : balRecords s = pre_ads ++ (balRecords s)[idx] :: suf_ads := by
      have h1 := (List.take_append_drop idx (balRecords s)).symm
      have h2 : (balRecords s).drop idx = (balRecords s)[idx] :: (balRecords s).drop (idx + 1) :=
        List.drop_eq_getElem_cons hidx_lt
      rw [h2] at h1
      exact h1
    have hsplit_set : (balRecords s).set idx v = pre_ads ++ v :: suf_ads := by
      rw [List.set_eq_take_append_cons_drop, if_pos hidx_lt]
    have hpre_sub : ∀ ad ∈ pre_ads, ad ∈ balRecords s := fun ad had => List.mem_of_mem_take had
    have hsuf_sub : ∀ ad ∈ suf_ads, ad ∈ balRecords s := fun ad had => List.mem_of_mem_drop had
    have hfm_set : (balRecords post).flatMap bal_fn_p =
        pre_ads.flatMap bal_fn_s ++ bal_fn_p v ++ suf_ads.flatMap bal_fn_s := by
      rw [h_set, hsplit_set, List.flatMap_append, List.flatMap_cons, ← List.append_assoc]
      rw [List.flatMap_congr (fun ad had => hold_fn ad (hpre_sub ad had)),
          List.flatMap_congr (fun ad had => hold_fn ad (hsuf_sub ad had))]
    let pre_sl := (nonbal_raw ++ pre_ads.flatMap bal_fn_s).filter (fun a => a.1 != 0)
    let suf_sl := (suf_ads.flatMap bal_fn_s).filter (fun a => a.1 != 0)
    have hsub_s : (pre_sl ++ suf_sl).Sublist (worldRoleSlots s) := by
      rw [hwrs_s_eq, hsplit_s, List.flatMap_append, List.flatMap_cons]
      simp only [pre_sl, suf_sl, ← List.filter_append]
      rw [← List.append_assoc]
      apply List.Sublist.filter
      apply List.Sublist.append_left
      exact List.Sublist.append (List.nil_sublist _) (List.Sublist.refl _)
    refine ⟨pre_sl, [(t0, "bal.stor"), (t8, "bal.reads")], suf_sl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwrs_p_eq, hfm_set]
      have hassoc : nonbal_raw ++ (pre_ads.flatMap bal_fn_s ++ bal_fn_p v ++ suf_ads.flatMap bal_fn_s) =
          (nonbal_raw ++ pre_ads.flatMap bal_fn_s) ++ bal_fn_p v ++ suf_ads.flatMap bal_fn_s := by
        simp [List.append_assoc]
      rw [hassoc, filter_append_three, hv_fn_f]
    · intro a ha; exact hsub_s.subset ha
    · exact hT.2.2.2.2.2.2.2.2.2.2.2.2.1.sublist hsub_s
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨by simp, hhdr_t0.trans (show 32 = roleKeyLen "bal.stor" by decide)⟩
      · exact ⟨by simp, hhdr_t8.trans (show 32 = roleKeyLen "bal.reads" by decide)⟩
    · simp [ht08_ne]

private theorem balEnsureAlloc_worldStep_finish {F : Type}
    {s s1 s5 mid : PanSemStateFiniteExact 64 F}
    {tw pw t0w t8w l16w l24w l32w : BitVec 64}
    {S Nd : List Nat}
    (hAR : ArenaReady s) (hAm : ArenaReady mid)
    (hag : AllocatorGrows s mid)
    (hT : TablesTyped s S) (hF : FixedTyped s) (hTr : TriesTypedWith s S Nd)
    (hgs : Wave8Contracts.M08.WorldGlobalsSame s mid)
    (ht_eq : tw.toNat = globN s "bal_accounts")
    (hba_nz : globN s "bal_accounts" ≠ 0)
    (hba_S : tw.toNat ∈ S)
    (hhp_05 : globN s "heap_ptr" ≤ globN s5 "heap_ptr")
    (hhp_5m : globN s5 "heap_ptr" ≤ globN mid "heap_ptr")
    (hpw_eq : pw.toNat = globN s "heap_ptr")
    (hpw_t0 : pw.toNat + 40 ≤ t0w.toNat)
    (ht0_s1 : t0w.toNat + 88 ≤ globN s1 "heap_ptr")
    (hs1_t8 : globN s1 "heap_ptr" ≤ t8w.toNat)
    (ht8_l16 : t8w.toNat + 88 ≤ l16w.toNat)
    (hl16_l24 : l16w.toNat + 24 + 160 = l24w.toNat)
    (hl24_l32 : l24w.toNat + 24 + 64 = l32w.toNat)
    (hl32_s5 : l32w.toNat + 24 + 48 = globN s5 "heap_ptr")
    (hfr_0m : FrameOutside s mid
      ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat)
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr"))
    (hfp_tw_5 : htabFootprint s5 tw.toNat = htabFootprint s tw.toNat)
    (hhdr0_tw_m : hdr mid tw.toNat 0 = hdr s tw.toNat 0)
    (hwf_tw_m : HtabWF mid tw.toNat)
    (hfp_tw_m : ∀ i ∈ htabFootprint mid tw.toNat, Allocated mid i ∧
      ((∃ j ∈ htabFootprint s5 tw.toNat, Inside i j.1 (j.1 + j.2)) ∨
        Inside i (globN s5 "heap_ptr") (globN s5 "heap_ptr" + (globN mid "heap_ptr" - globN s5 "heap_ptr"))))
    (hvalues_0m : HtabSetValuesPost s mid (globN s "bal_accounts") pw.toNat)
    (hwf_t0_m : HtabWF mid t0w.toNat)
    (hwf_t8_m : HtabWF mid t8w.toNat)
    (hfp_t0_m : htabFootprint mid t0w.toNat = htabFootprint s5 t0w.toNat)
    (hfp_t8_m : htabFootprint mid t8w.toNat = htabFootprint s5 t8w.toNat)
    (hfp_t0_5 : ∀ i ∈ htabFootprint s5 t0w.toNat, Allocated s5 i ∧ Inside i (pw.toNat + 40) (globN s1 "heap_ptr"))
    (hfp_t8_5 : ∀ i ∈ htabFootprint s5 t8w.toNat, Allocated s5 i ∧ Inside i (globN s1 "heap_ptr") l16w.toNat)
    (hpw_tabs_5 : ∀ t ∈ ([t0w.toNat, t8w.toNat] : List Nat), ∀ u ∈ ([t0w.toNat, t8w.toNat] : List Nat),
      t ≠ u → ∀ i ∈ htabFootprint s5 t, ∀ j ∈ htabFootprint s5 u, Disj i j)
    (hkey_t0_m : hdr mid t0w.toNat 0 = 32)
    (hkey_t8_m : hdr mid t8w.toNat 0 = 32)
    (hvals_t0_m : htabValues mid t0w.toNat = [])
    (hm0_m : memW mid pw.toNat = t0w.toNat)
    (hm8_m : memW mid (pw.toNat + 8) = t8w.toNat)
    (hm16_m : memW mid (pw.toNat + 16) = l16w.toNat)
    (hm24_m : memW mid (pw.toNat + 24) = l24w.toNat)
    (hm32_m : memW mid (pw.toNat + 32) = l32w.toNat)
    (hlst16_m : LstOK mid l16w.toNat)
    (hobjs16_m : lstObjects mid l16w.toNat 40 = [(l16w.toNat, 24), (l16w.toNat + 24, 160)])
    (hlst24_m : LstOK mid l24w.toNat)
    (hobjs24_m : lstObjects mid l24w.toNat 16 = [(l24w.toNat, 24), (l24w.toNat + 24, 64)])
    (hlst32_m : LstOK mid l32w.toNat)
    (hobjs32_m : lstObjects mid l32w.toNat 24 = [(l32w.toNat, 24), (l32w.toNat + 24, 48)])
    (hmem_rec : pw.toNat ∈ balRecords mid)
    (hno_bs32 : globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ globN s "bal_accounts")
    (hno_ts32 : globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ globN s "bal_accounts")
    (hno_ws32 : globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ globN s "bal_accounts")
    (hu_ws : globN s "ws" ≠ 0 → M08IvlUnhit s mid (globN s "ws", 40))
    (hu_bs : globN s "bs" ≠ 0 → M08IvlUnhit s mid (globN s "bs", 80))
    (hu_ts : globN s "ts" ≠ 0 → M08IvlUnhit s mid (globN s "ts", 72))
    (hu_other : ∀ u ∈ S, u ≠ tw.toNat → ∀ i ∈ htabFootprint s u, M08IvlUnhit s mid i)
    (hu_other_ba : ∀ u ∈ S, u ≠ globN s "bal_accounts" → ∀ i ∈ htabFootprint s u, M08IvlUnhit s mid i)
    (hother_fp : ∀ u ∈ S, u ≠ tw.toNat →
      (∀ k, k < 11 → hdr mid u k = hdr s u k) ∧ htabFootprint mid u = htabFootprint s u)
    (hbo_part : blockOutObjects mid = blockOutObjects s ∧
      (globN mid "bo" ≠ 0 → ∀ k ∈ ([40, 72] : List Nat),
        memW mid (globN mid "bo" + k) ≠ 0 → LstOK mid (memW mid (globN mid "bo" + k))))
    (hold_acc : ∀ ad ∈ balRecords s,
      ((ad, 40) :: lstObjects mid (memW mid (ad + 16)) 40 ++
        lstObjects mid (memW mid (ad + 24)) 16 ++
        lstObjects mid (memW mid (ad + 32)) 24 ++
        (htabValues mid (memW mid ad)).flatMap (fun l => lstObjects mid l 40) =
      (ad, 40) :: lstObjects s (memW s (ad + 16)) 40 ++
        lstObjects s (memW s (ad + 24)) 16 ++
        lstObjects s (memW s (ad + 32)) 24 ++
        (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40)) ∧
      memW mid ad = memW s ad ∧
      memW mid (ad + 8) = memW s (ad + 8) ∧
      htabValues mid (memW mid ad) = htabValues s (memW s ad) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK mid (memW mid (ad + k))) ∧
      (∀ l ∈ htabValues mid (memW mid ad), LstOK mid l))
    (hF_mid : FixedTyped mid)
    (hfix_from : ∀ o ∈ fixedObjects mid, o ∈ fixedObjects s ∨ o = (0, 0) ∨
      Inside o (globN s "heap_ptr") (globN mid "heap_ptr"))
    (hjr_eq : journalRoleSlots mid = journalRoleSlots s)
    (hJ_mid : JournalTyped mid (S ++ [t0w.toNat, t8w.toNat]))
    (hnd_alloc : ∀ o ∈ nodeExtents s Nd, o = (0, 0) ∨ Allocated s o)
    (hNH_mid : NodeHeap mid Nd)
    (hnd_eq : nodeExtents mid Nd = nodeExtents s Nd) :
    ∃ S' Nd',
      (∀ t ∈ S, t ∈ S') ∧
      WorldTypedWith mid S' Nd' ∧
      OwnedGrows s mid (worldOwned s S Nd) (worldOwned mid S' Nd') ∧
      FrameOutside s mid (worldOwned s S Nd ++ ([] : List Ivl) ++ [freeGap s]) (heapFree s) ∧
      pw.toNat ∈ balRecords mid := by
  have hs_lo : sourceBase ≤ globN s "heap_ptr" := hAR.2.1
  have hsb_pos : 0 < sourceBase := by decide
  have hm_hi : globN mid "heap_ptr" ≤ heapLimit := hAm.2.2.1
  have hsub : ∀ t ∈ S, t ∈ S ++ [t0w.toNat, t8w.toNat] :=
    fun t ht => List.mem_append_left _ ht
  let fresh_pw : List Ivl :=
    [(pw.toNat, 40), (l16w.toNat, 24), (l16w.toNat + 24, 160),
      (l24w.toNat, 24), (l24w.toNat + 24, 64), (l32w.toNat, 24), (l32w.toNat + 24, 48)]
  have hpw_obj_eq :
      (pw.toNat, 40) :: lstObjects mid (memW mid (pw.toNat + 16)) 40 ++
        lstObjects mid (memW mid (pw.toNat + 24)) 16 ++
        lstObjects mid (memW mid (pw.toNat + 32)) 24 ++
        (htabValues mid (memW mid pw.toNat)).flatMap (fun l => lstObjects mid l 40) = fresh_pw := by
    rw [hm0_m, hm16_m, hm24_m, hm32_m, hvals_t0_m, hobjs16_m, hobjs24_m, hobjs32_m]
    rfl
  have hfresh_pw_in5 : ∀ i ∈ fresh_pw, Inside i (globN s "heap_ptr") (globN s5 "heap_ptr") := by
    intro i hi
    simp only [fresh_pw, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by dsimp; omega, by dsimp; omega⟩
  have ht0_nz : t0w.toNat ≠ 0 := by omega
  have ht8_nz : t8w.toNat ≠ 0 := by omega
  have ht08_ne : t0w.toNat ≠ t8w.toNat := by omega
  have hT_nd : ([t0w.toNat, t8w.toNat] : List Nat).Nodup := by simp [ht08_ne]
  have hT_wf : ∀ t ∈ ([t0w.toNat, t8w.toNat] : List Nat), HtabWF mid t ∧
      ∀ i ∈ htabFootprint mid t, Allocated mid i ∧
        Inside i (globN s "heap_ptr") (globN mid "heap_ptr") ∧
        (∀ j ∈ fixedObjects mid, Disj i j) := by
    intro t ht
    have hdisj_fresh_pw : ∀ i : Ivl,
        (Inside i (pw.toNat + 40) (globN s1 "heap_ptr") ∨ Inside i (globN s1 "heap_ptr") l16w.toNat) →
        ∀ j ∈ fresh_pw, Disj i j := by
      intro i hi_in j hj
      simp only [fresh_pw, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hi_in with ⟨hi1_lo, hi1_hi⟩ | ⟨hi2_lo, hi2_hi⟩ <;>
        (rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
    have hfix_mid_class : ∀ j ∈ fixedObjects mid, j ∈ fixedObjects s ∨ j ∈ fresh_pw := by
      intro j hj
      unfold fixedObjects at hj
      have hgb : (globalBuffers.map fun gn => (globN mid gn.1, if globN mid gn.1 = 0 then 0 else gn.2)) =
          (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
        apply List.map_congr_left; intro gn hgn; rw [hgs.1 gn hgn]
      rw [hgb, hgs.2.2.1, hgs.2.2.2.1, hbo_part.1] at hj
      rcases List.mem_append.1 hj with hpre | hbal
      · left; unfold fixedObjects; exact List.mem_append_left _ hpre
      · unfold balObjects at hbal
        obtain ⟨ad, had, hj_ad⟩ := List.mem_flatMap.1 hbal
        obtain ⟨_, _, hbal_mem⟩ := balRecords_set_values_add
          (hgs.2.1 "bal_accounts" (by simp [globalTableRoots])) hba_nz hvalues_0m
        rcases hbal_mem ad had with had_s | rfl
        · left
          rw [(hold_acc ad had_s).1] at hj_ad
          unfold fixedObjects
          exact List.mem_append_right _ (List.mem_flatMap.2 ⟨ad, had_s, hj_ad⟩)
        · right; rwa [hpw_obj_eq] at hj_ad
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · refine ⟨hwf_t0_m, fun i hi => ?_⟩
      rw [hfp_t0_m] at hi
      have hin5 := (hfp_t0_5 i hi).2
      have hin0m : Inside i (globN s "heap_ptr") (globN mid "heap_ptr") :=
        ⟨by have := hin5.1; omega, by have := hin5.2; omega⟩
      refine ⟨Or.inl ⟨by have := hin0m.1; omega, by have := hin0m.2; omega⟩, hin0m, fun j hj => ?_⟩
      rcases hfix_mid_class j hj with hj_s | hj_fr
      · rcases hF.1 j hj_s with hz | ⟨hal_j, _⟩
        · exact Or.inr (Or.inl hz)
        · exact Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2 hal_j hin0m
      · exact hdisj_fresh_pw i (Or.inl hin5) j hj_fr
    · refine ⟨hwf_t8_m, fun i hi => ?_⟩
      rw [hfp_t8_m] at hi
      have hin5 := (hfp_t8_5 i hi).2
      have hin0m : Inside i (globN s "heap_ptr") (globN mid "heap_ptr") :=
        ⟨by have := hin5.1; omega, by have := hin5.2; omega⟩
      refine ⟨Or.inl ⟨by have := hin0m.1; omega, by have := hin0m.2; omega⟩, hin0m, fun j hj => ?_⟩
      rcases hfix_mid_class j hj with hj_s | hj_fr
      · rcases hF.1 j hj_s with hz | ⟨hal_j, _⟩
        · exact Or.inr (Or.inl hz)
        · exact Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2 hal_j hin0m
      · exact hdisj_fresh_pw i (Or.inr hin5) j hj_fr
  have hT_disj_S : ∀ t ∈ ([t0w.toNat, t8w.toNat] : List Nat), t ∉ S := by
    intro t ht htS
    have ht_in := ((hT_wf t ht).2 (t, 88) (by simp [htabFootprint])).2.1
    have hal_s := ((hT.2.1 t htS).2 (t, 88) (by simp [htabFootprint])).1
    have hd := Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2 hal_s ht_in
    rcases hd with h | h | h | h <;> dsimp at h <;> omega
  have hT_pw_new : ∀ t ∈ ([t0w.toNat, t8w.toNat] : List Nat),
      ∀ u ∈ ([t0w.toNat, t8w.toNat] : List Nat), t ≠ u →
      ∀ i ∈ htabFootprint mid t, ∀ j ∈ htabFootprint mid u, Disj i j := by
    intro t ht u hu hne i hi j hj
    have hfp_eq : ∀ x ∈ ([t0w.toNat, t8w.toNat] : List Nat), htabFootprint mid x = htabFootprint s5 x := by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl; exact hfp_t0_m; exact hfp_t8_m
    rw [hfp_eq t ht] at hi; rw [hfp_eq u hu] at hj
    exact hpw_tabs_5 t ht u hu hne i hi j hj
  have htw_disj : ∀ i ∈ htabFootprint mid tw.toNat,
      (∀ u ∈ S, u ≠ tw.toNat → ∀ j ∈ htabFootprint s u, Disj i j) ∧
      (∀ j ∈ fixedObjects mid, Disj i j) ∧
      (∀ o ∈ nodeExtents s Nd, Disj i o) ∧
      (∀ t ∈ ([t0w.toNat, t8w.toNat] : List Nat), ∀ j ∈ htabFootprint mid t, Disj i j) := by
    intro i hi
    rcases (hfp_tw_m i hi).2 with ⟨k, hk5, hin⟩ | hfresh5m
    · rw [hfp_tw_5] at hk5
      refine ⟨fun u hu hne j hj =>
          Wave8Contracts.M08.disj_of_inside_left hin (hT.2.2.1 tw.toNat hba_S u hu hne.symm k hk5 j hj),
        fun j hj => ?_,
        fun o ho => Wave8Contracts.M08.disj_of_inside_left hin (disj_flip ((hTr.2.1 o ho).1 tw.toNat hba_S k hk5)),
        fun t ht j hj => Wave8Contracts.M08.disj_of_inside_left hin
          (disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2
            (((hT.2.1 tw.toNat hba_S).2 k hk5).1) (((hT_wf t ht).2 j hj).2.1)))⟩
      rcases hfix_from j hj with hj_s | rfl | hj_fr
      · exact Wave8Contracts.M08.disj_of_inside_left hin (((hT.2.1 tw.toNat hba_S).2 k hk5).2 j hj_s)
      · exact Or.inr (Or.inl rfl)
      · exact Wave8Contracts.M08.disj_of_inside_left hin
          (disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2
            (((hT.2.1 tw.toNat hba_S).2 k hk5).1) hj_fr))
    · have hfresh5m' : Inside i (globN s5 "heap_ptr") (globN mid "heap_ptr") :=
        ⟨hfresh5m.1, by have := hfresh5m.2; omega⟩
      have hfresh0m : Inside i (globN s "heap_ptr") (globN mid "heap_ptr") :=
        ⟨le_trans hhp_05 hfresh5m'.1, hfresh5m'.2⟩
      refine ⟨fun u hu _ j hj => Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2
          (((hT.2.1 u hu).2 j hj).1) hfresh0m,
        fun j hj => ?_,
        fun o ho => ?_,
        fun t ht j hj => ?_⟩
      · unfold fixedObjects at hj
        have hgb : (globalBuffers.map fun gn => (globN mid gn.1, if globN mid gn.1 = 0 then 0 else gn.2)) =
            (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
          apply List.map_congr_left; intro gn hgn; rw [hgs.1 gn hgn]
        rw [hgb, hgs.2.2.1, hgs.2.2.2.1, hbo_part.1] at hj
        rcases List.mem_append.1 hj with hpre | hbal
        · have hj_s : j ∈ fixedObjects s := by unfold fixedObjects; exact List.mem_append_left _ hpre
          rcases hF.1 j hj_s with hz | ⟨hal_j, _⟩
          · exact Or.inr (Or.inl hz)
          · exact Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2 hal_j hfresh0m
        · unfold balObjects at hbal
          obtain ⟨ad, had, hj_ad⟩ := List.mem_flatMap.1 hbal
          obtain ⟨_, _, hbal_mem⟩ := balRecords_set_values_add
            (hgs.2.1 "bal_accounts" (by simp [globalTableRoots])) hba_nz hvalues_0m
          rcases hbal_mem ad had with had_s | rfl
          · rw [(hold_acc ad had_s).1] at hj_ad
            have hj_s : j ∈ fixedObjects s := by
              unfold fixedObjects
              exact List.mem_append_right _ (List.mem_flatMap.2 ⟨ad, had_s, hj_ad⟩)
            rcases hF.1 j hj_s with hz | ⟨hal_j, _⟩
            · exact Or.inr (Or.inl hz)
            · exact Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2 hal_j hfresh0m
          · rw [hpw_obj_eq] at hj_ad
            have hj5 := (hfresh_pw_in5 j hj_ad).2
            exact Or.inr (Or.inr (Or.inr (by have := hfresh5m'.1; omega)))
      · rcases hnd_alloc o ho with rfl | hal_o
        · exact Or.inr (Or.inl rfl)
        · exact Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2 hal_o hfresh0m
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · rw [hfp_t0_m] at hj
          have hj5 := (hfp_t0_5 j hj).2.2
          exact Or.inr (Or.inr (Or.inr (by have := hfresh5m'.1; omega)))
        · rw [hfp_t8_m] at hj
          have hj5 := (hfp_t8_5 j hj).2.2
          exact Or.inr (Or.inr (Or.inr (by have := hfresh5m'.1; omega)))
  have hhdr0_S : ∀ t ∈ S, hdr mid t 0 = hdr s t 0 := by
    intro t ht
    by_cases htw : t = tw.toNat
    · subst htw; exact hhdr0_tw_m
    · exact (hother_fp t ht htw).1 0 (by omega)
  have hroles_mid : RolesOK mid (S ++ [t0w.toNat, t8w.toNat]) (worldRoleSlots mid) (journalRoleSlots mid) :=
    rolesOK_balEnsureAlloc hAR.2 hT hF hgs hba_nz hvalues_0m hu_other_ba hu_ws hu_bs hu_ts
      (fun ad had => ⟨(hold_acc ad had).2.1, (hold_acc ad had).2.2.1⟩)
      ⟨hm0_m, hm8_m⟩ ht0_nz ht8_nz ht08_ne hkey_t0_m hkey_t8_m hhdr0_S hT_disj_S hjr_eq
  have hroot_S : ∀ {v}, RootIn S v → RootIn (S ++ [t0w.toNat, t8w.toNat]) v := by
    rintro v (rfl | hv); exact Or.inl rfl; exact Or.inr (hsub v hv)
  have hT_mid : TablesTyped mid (S ++ [t0w.toNat, t8w.toNat]) := by
    obtain ⟨hndS, htwf, htpw, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, _, _⟩ := hT
    have ews := hgs.1 ("ws", 40) (by simp [globalBuffers])
    have ebs := hgs.1 ("bs", 80) (by simp [globalBuffers])
    have ets := hgs.1 ("ts", 72) (by simp [globalBuffers])
    refine ⟨List.nodup_append.2 ⟨hndS, hT_nd, fun u hu v hv heq => by subst heq; exact hT_disj_S u hv hu⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_part.2, hroles_mid⟩
    · intro u hu
      rcases List.mem_append.1 hu with huS | huN
      · by_cases hu_tw : u = tw.toNat
        · subst hu_tw
          exact ⟨hwf_tw_m, fun i hi => ⟨(hfp_tw_m i hi).1, (htw_disj i hi).2.1⟩⟩
        · rw [(hother_fp u huS hu_tw).2]
          refine ⟨Wave8Contracts.M08.htabWF_congr_unhit hAR.1 hAm.1 (htwf u huS).1 (hu_other u huS hu_tw),
            fun i hi => ⟨hag.allocated ((htwf u huS).2 i hi).1, fun j hj => ?_⟩⟩
          rcases hfix_from j hj with hj_s | rfl | hj_fr
          · exact ((htwf u huS).2 i hi).2 j hj_s
          · exact Or.inr (Or.inl rfl)
          · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2
              (((htwf u huS).2 i hi).1) hj_fr)
      · exact ⟨(hT_wf u huN).1, fun i hi => ⟨((hT_wf u huN).2 i hi).1, ((hT_wf u huN).2 i hi).2.2⟩⟩
    · intro u hu v hv hne i hi j hj
      rcases List.mem_append.1 hu with huS | huN <;> rcases List.mem_append.1 hv with hvS | hvN
      · by_cases hu_tw : u = tw.toNat
        · subst hu_tw
          rw [(hother_fp v hvS hne.symm).2] at hj
          exact (htw_disj i hi).1 v hvS hne.symm j hj
        · by_cases hv_tw : v = tw.toNat
          · subst hv_tw
            rw [(hother_fp u huS hu_tw).2] at hi
            exact disj_flip ((htw_disj j hj).1 u huS hu_tw i hi)
          · rw [(hother_fp u huS hu_tw).2] at hi; rw [(hother_fp v hvS hv_tw).2] at hj
            exact htpw u huS v hvS hne i hi j hj
      · by_cases hu_tw : u = tw.toNat
        · subst hu_tw
          exact (htw_disj i hi).2.2.2 v hvN j hj
        · rw [(hother_fp u huS hu_tw).2] at hi
          exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2
            (((htwf u huS).2 i hi).1) (((hT_wf v hvN).2 j hj).2.1))
      · by_cases hv_tw : v = tw.toNat
        · subst hv_tw
          exact disj_flip ((htw_disj j hj).2.2.2 u huN i hi)
        · rw [(hother_fp v hvS hv_tw).2] at hj
          exact Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2
            (((htwf v hvS).2 j hj).1) (((hT_wf u huN).2 i hi).2.1)
      · exact hT_pw_new u huN v hvN hne i hi j hj
    · intro k hk hnz
      rw [ews] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> exact ⟨by omega, by omega⟩
      rw [Wave8Contracts.M08.rec_word_eq_of_unhit hAR.2 hF "ws" 40 (by decide) ews hnz (hu_ws hnz) hk8.1 hk8.2]
      exact hroot_S (hwsR k hk hnz)
    · intro k hk hnz
      rw [ebs] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
      rw [Wave8Contracts.M08.rec_word_eq_of_unhit hAR.2 hF "bs" 80 (by decide) ebs hnz (hu_bs hnz) hk8.1 hk8.2]
      exact hroot_S (hbsR k hk hnz)
    · intro k hk hnz
      rw [ets] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
      rw [Wave8Contracts.M08.rec_word_eq_of_unhit hAR.2 hF "ts" 72 (by decide) ets hnz (hu_ts hnz) hk8.1 hk8.2]
      exact hroot_S (htsR k hk hnz)
    · intro g hg_mem; rw [hgs.2.1 g hg_mem]; exact hroot_S (hgR g hg_mem)
    · intro hnz hm
      rw [ebs] at hnz
      have ew := Wave8Contracts.M08.rec_word_eq_of_unhit hAR.2 hF "bs" 80 (by decide) ebs hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hm ⊢
      rcases List.mem_append.1 hm with hmS | hmN
      · exact Wave8Contracts.M08.htabValuesIn_congr_unhit (htwf _ hmS).1
          (hu_other_ba _ hmS (hno_bs32 hnz)) hsub (hbsN hnz hmS)
      · rcases hbsR 32 (by simp [bsTableSlots]) hnz with h0 | hmS
        · exact absurd (h0 ▸ hmN) (fun h0N => htab_nonzero_of_wf (hT_wf 0 h0N).1 rfl)
        · exact absurd hmS (hT_disj_S _ hmN)
    · intro hnz hm
      rw [ets] at hnz
      have ew := Wave8Contracts.M08.rec_word_eq_of_unhit hAR.2 hF "ts" 72 (by decide) ets hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hm ⊢
      rcases List.mem_append.1 hm with hmS | hmN
      · exact Wave8Contracts.M08.htabValuesIn_congr_unhit (htwf _ hmS).1
          (hu_other_ba _ hmS (hno_ts32 hnz)) hsub (htsN hnz hmS)
      · rcases htsR 32 (by simp [tsTableSlots]) hnz with h0 | hmS
        · exact absurd (h0 ▸ hmN) (fun h0N => htab_nonzero_of_wf (hT_wf 0 h0N).1 rfl)
        · exact absurd hmS (hT_disj_S _ hmN)
    · intro ad had
      obtain ⟨_, _, hbal_mem⟩ := balRecords_set_values_add
        (hgs.2.1 "bal_accounts" (by simp [globalTableRoots])) hba_nz hvalues_0m
      rcases hbal_mem ad had with had_s | rfl
      · obtain ⟨_, e0, e8, _, hkl, hll⟩ := hold_acc ad had_s
        exact ⟨e0 ▸ hsub _ (hbalT ad had_s).1, e8 ▸ hsub _ (hbalT ad had_s).2.1, hkl, hll⟩
      · refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hm0_m]; exact List.mem_append_right _ (by simp)
        · rw [hm8_m]; exact List.mem_append_right _ (by simp)
        · intro k hk
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl
          · rw [hm16_m]; exact hlst16_m
          · rw [hm24_m]; exact hlst24_m
          · rw [hm32_m]; exact hlst32_m
        · intro l hl
          rw [hm0_m, hvals_t0_m] at hl
          cases hl
  have hTr_mid : TriesTypedWith mid (S ++ [t0w.toNat, t8w.toNat]) Nd := by
    have ews := hgs.1 ("ws", 40) (by simp [globalBuffers])
    refine ⟨hNH_mid, ?_, ?_⟩
    · intro o ho
      rw [hnd_eq] at ho
      refine ⟨fun u hu i hi => ?_, fun j hj => ?_⟩
      · rcases List.mem_append.1 hu with huS | huN
        · by_cases hu_tw : u = tw.toNat
          · subst hu_tw; exact disj_flip ((htw_disj i hi).2.2.1 o ho)
          · rw [(hother_fp u huS hu_tw).2] at hi
            exact (hTr.2.1 o ho).1 u huS i hi
        · rcases hnd_alloc o ho with rfl | hal_o
          · exact Or.inl rfl
          · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2
              hal_o (((hT_wf u huN).2 i hi).2.1))
      · rcases hfix_from j hj with hj_s | rfl | hj_fr
        · exact (hTr.2.1 o ho).2 j hj_s
        · exact Or.inr (Or.inl rfl)
        · rcases hnd_alloc o ho with rfl | hal_o
          · exact Or.inl rfl
          · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hAm.2 hal_o hj_fr)
    · intro hws_nz
      rw [ews] at hws_nz
      have e24 := Wave8Contracts.M08.rec_word_eq_of_unhit hAR.2 hF "ws" 40 (by decide) ews hws_nz (hu_ws hws_nz) (k := 24) (by omega) (by omega)
      have e32 := Wave8Contracts.M08.rec_word_eq_of_unhit hAR.2 hF "ws" 40 (by decide) ews hws_nz (hu_ws hws_nz) (k := 32) (by omega) (by omega)
      rw [e24, e32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hws_nz
      refine ⟨hr24, fun hm i hi => ?_⟩
      rcases List.mem_append.1 hm with hmS | hmN
      · have hne32 : memW s (globN s "ws" + 32) ≠ tw.toNat := by
          rw [ht_eq]; exact hno_ws32 hws_nz
        have hu32 := hu_other _ hmS hne32
        have hwf32 := (hT.2.1 _ hmS).1
        have hvals_eq := Wave8Contracts.M08.htabValues_eq_of_unhit hwf32 hu32
        obtain ⟨hhdr32, _⟩ := hother_fp _ hmS hne32
        rw [hhdr32 3 (by omega)] at hi
        have hget : (htabValues mid (memW s (globN s "ws" + 32)))[i]? =
            (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals_eq]
        simp only [htabValues, List.getElem?_map, List.getElem?_range, hhdr32 3 (by omega), hi,
          Option.map_some, Option.some.injEq] at hget
        rw [hget]; exact hr32 hmS i hi
      · rcases hT.2.2.2.1 32 (by simp [wsTableSlots]) hws_nz with h0 | hmS
        · exact absurd (h0 ▸ hmN) (fun h0N => htab_nonzero_of_wf (hT_wf 0 h0N).1 rfl)
        · exact absurd hmS (hT_disj_S _ hmN)
  refine ⟨S ++ [t0w.toNat, t8w.toNat], Nd, hsub, ⟨hT_mid, hJ_mid, hF_mid, hTr_mid⟩, ?_, ?_, hmem_rec⟩
  · intro o ho
    unfold worldOwned M13.worldOwned at ho
    rcases List.mem_append.1 ho with ho12 | ho_nd
    · rcases List.mem_append.1 ho12 with ho_tab | ho_fix
      · rw [List.flatMap_append] at ho_tab
        rcases List.mem_append.1 ho_tab with ho_S | ho_N
        · obtain ⟨u, huS, hi⟩ := List.mem_flatMap.1 ho_S
          by_cases hu_tw : u = tw.toNat
          · subst hu_tw
            rcases (hfp_tw_m o hi).2 with ⟨j, hj5, hin⟩ | hfresh5m
            · rw [hfp_tw_5] at hj5
              refine Or.inr (Or.inl ⟨j, ?_, hin⟩)
              unfold worldOwned M13.worldOwned
              exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨tw.toNat, hba_S, hj5⟩))
            · exact Or.inr (Or.inr ⟨le_trans hhp_05 hfresh5m.1, by have := hfresh5m.2; omega⟩)
          · rw [(hother_fp u huS hu_tw).2] at hi
            refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
            unfold worldOwned M13.worldOwned
            exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u, huS, hi⟩))
        · obtain ⟨t, htN, hi⟩ := List.mem_flatMap.1 ho_N
          exact Or.inr (Or.inr ((hT_wf t htN).2 o hi).2.1)
      · rcases hfix_from o ho_fix with ho_s | rfl | ho_fr
        · refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
          unfold worldOwned M13.worldOwned
          exact List.mem_append_left _ (List.mem_append_right _ ho_s)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ho_fr)
    · rw [hnd_eq] at ho_nd
      refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
      unfold worldOwned M13.worldOwned
      exact List.mem_append_right _ ho_nd
  · intro a hkeep hnot_hf
    apply hfr_0m a
    · intro j hj hcj
      rcases List.mem_cons.1 hj with rfl | hj_fp
      · exact hkeep (freeGap s)
          (List.mem_append_right _ (List.mem_singleton.2 rfl))
          (cellHits_sp0_imp_freeGap hAR.2 hcj)
      · apply hkeep j
        · apply List.mem_append_left; apply List.mem_append_left
          unfold worldOwned M13.worldOwned
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨tw.toNat, hba_S, hj_fp⟩))
        · exact hcj
    · intro ⟨c1, c2⟩
      apply hnot_hf
      dsimp only at c1 c2
      unfold heapFree M13.heapFree CellHits
      dsimp only
      omega

private theorem balEnsureAlloc_worldStep_core {F : Type}
    {s s1 s5 mid : PanSemStateFiniteExact 64 F}
    {tw pw t0w t8w l16w l24w l32w : BitVec 64}
    {S Nd : List Nat}
    (hAR : ArenaReady s) (hA5 : ArenaReady s5) (hAm : ArenaReady mid)
    (hWT : WorldTypedWith s S Nd)
    (ht_eq : tw.toNat = globN s "bal_accounts")
    (hba_nz : globN s "bal_accounts" ≠ 0)
    (hgk : GlobalsKept ["heap_ptr"] s mid)
    (hsp_mid : globN mid "scratch_ptr" = globN s "scratch_ptr")
    (hhp_05 : globN s "heap_ptr" ≤ globN s5 "heap_ptr")
    (hhp_5m : globN s5 "heap_ptr" ≤ globN mid "heap_ptr")
    (hbe_0m : mid.be = s.be)
    (hpw_eq : pw.toNat = globN s "heap_ptr")
    (hpw8 : pw.toNat % 8 = 0)
    (hpw_t0 : pw.toNat + 40 ≤ t0w.toNat)
    (ht0_s1 : t0w.toNat + 88 ≤ globN s1 "heap_ptr")
    (hs1_t8 : globN s1 "heap_ptr" ≤ t8w.toNat)
    (ht8_l16 : t8w.toNat + 88 ≤ l16w.toNat)
    (hl16_l24 : l16w.toNat + 24 + 160 = l24w.toNat)
    (hl24_l32 : l24w.toNat + 24 + 64 = l32w.toNat)
    (hl32_s5 : l32w.toNat + 24 + 48 = globN s5 "heap_ptr")
    (hfr_0m : FrameOutside s mid
      ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat)
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr"))
    (hfp_tw_5 : htabFootprint s5 tw.toNat = htabFootprint s tw.toNat)
    (hhdr0_tw_m : hdr mid tw.toNat 0 = hdr s tw.toNat 0)
    (hwf_tw_m : HtabWF mid tw.toNat)
    (hfp_tw_m : ∀ i ∈ htabFootprint mid tw.toNat, Allocated mid i ∧
      ((∃ j ∈ htabFootprint s5 tw.toNat, Inside i j.1 (j.1 + j.2)) ∨
        Inside i (globN s5 "heap_ptr") (globN s5 "heap_ptr" + (globN mid "heap_ptr" - globN s5 "heap_ptr"))))
    (hvalues_0m : HtabSetValuesPost s mid (globN s "bal_accounts") pw.toNat)
    (hwf_t0_m : HtabWF mid t0w.toNat)
    (hwf_t8_m : HtabWF mid t8w.toNat)
    (hfp_t0_m : htabFootprint mid t0w.toNat = htabFootprint s5 t0w.toNat)
    (hfp_t8_m : htabFootprint mid t8w.toNat = htabFootprint s5 t8w.toNat)
    (hfp_t0_5 : ∀ i ∈ htabFootprint s5 t0w.toNat, Allocated s5 i ∧ Inside i (pw.toNat + 40) (globN s1 "heap_ptr"))
    (hfp_t8_5 : ∀ i ∈ htabFootprint s5 t8w.toNat, Allocated s5 i ∧ Inside i (globN s1 "heap_ptr") l16w.toNat)
    (hpw_tabs_5 : ∀ t ∈ ([t0w.toNat, t8w.toNat] : List Nat), ∀ u ∈ ([t0w.toNat, t8w.toNat] : List Nat),
      t ≠ u → ∀ i ∈ htabFootprint s5 t, ∀ j ∈ htabFootprint s5 u, Disj i j)
    (hkey_t0_m : hdr mid t0w.toNat 0 = 32)
    (hkey_t8_m : hdr mid t8w.toNat 0 = 32)
    (hvals_t0_m : htabValues mid t0w.toNat = [])
    (hm0_m : memW mid pw.toNat = t0w.toNat)
    (hm8_m : memW mid (pw.toNat + 8) = t8w.toNat)
    (hm16_m : memW mid (pw.toNat + 16) = l16w.toNat)
    (hm24_m : memW mid (pw.toNat + 24) = l24w.toNat)
    (hm32_m : memW mid (pw.toNat + 32) = l32w.toNat)
    (hlst16_m : LstOK mid l16w.toNat)
    (hobjs16_m : lstObjects mid l16w.toNat 40 = [(l16w.toNat, 24), (l16w.toNat + 24, 160)])
    (hlst24_m : LstOK mid l24w.toNat)
    (hobjs24_m : lstObjects mid l24w.toNat 16 = [(l24w.toNat, 24), (l24w.toNat + 24, 64)])
    (hlst32_m : LstOK mid l32w.toNat)
    (hobjs32_m : lstObjects mid l32w.toNat 24 = [(l32w.toNat, 24), (l32w.toNat + 24, 48)])
    (hm0_8_16 : memW mid 0 = memW s 0 ∧ memW mid 8 = memW s 8 ∧ memW mid 16 = memW s 16)
    (hmem_rec : pw.toNat ∈ balRecords mid) :
    ∃ S' Nd',
      (∀ t ∈ S, t ∈ S') ∧
      WorldTypedWith mid S' Nd' ∧
      OwnedGrows s mid (worldOwned s S Nd) (worldOwned mid S' Nd') ∧
      FrameOutside s mid (worldOwned s S Nd ++ ([] : List Ivl) ++ [freeGap s]) (heapFree s) ∧
      pw.toNat ∈ balRecords mid := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  have hsp8 : (globN s "scratch_ptr") % 8 = 0 := hAR.2.2.2.2.2.2.2.2.1
  have hhp_0m : globN s "heap_ptr" ≤ globN mid "heap_ptr" := le_trans hhp_05 hhp_5m
  have hag : AllocatorGrows s mid := ⟨hhp_0m, by omega⟩
  have hgs : Wave8Contracts.M08.WorldGlobalsSame s mid :=
    Wave8Contracts.M08.worldGlobalsSame_of_kept hgk (fun name h => Or.inl (by simpa using h))
  have hs_lo : sourceBase ≤ globN s "heap_ptr" := hAR.2.1
  have hsb_pos : 0 < sourceBase := by decide
  have hba_S : tw.toNat ∈ S := by
    rw [ht_eq]
    rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
    · exact absurd h0 hba_nz
    · exact hm
  have hWF_tw : HtabWF s tw.toNat := (hT.2.1 _ hba_S).1
  have hk_al_0m : ∀ j ∈ ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat), j.1 % 8 = 0 := by
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj_fp
    · exact hsp8
    · exact (hWF_tw.1 j hj_fp).2.1
  have hl32_8 : l32w.toNat % 8 = 0 := by
    have h := hA5.2.2.2.2.2.2.1; omega
  have hl24_8 : l24w.toNat % 8 = 0 := by omega
  have hl16_8 : l16w.toNat % 8 = 0 := by omega
  let fresh_pw : List Ivl :=
    [(pw.toNat, 40), (l16w.toNat, 24), (l16w.toNat + 24, 160),
      (l24w.toNat, 24), (l24w.toNat + 24, 64), (l32w.toNat, 24), (l32w.toNat + 24, 48)]
  have hpw_obj_eq :
      (pw.toNat, 40) :: lstObjects mid (memW mid (pw.toNat + 16)) 40 ++
        lstObjects mid (memW mid (pw.toNat + 24)) 16 ++
        lstObjects mid (memW mid (pw.toNat + 32)) 24 ++
        (htabValues mid (memW mid pw.toNat)).flatMap (fun l => lstObjects mid l 40) = fresh_pw := by
    rw [hm0_m, hm16_m, hm24_m, hm32_m, hvals_t0_m, hobjs16_m, hobjs24_m, hobjs32_m]
    rfl
  have hfresh_pw_props : ∀ i ∈ fresh_pw,
      Inside i (globN s "heap_ptr") (globN s5 "heap_ptr") ∧ WordsOK mid i := by
    intro i hi
    simp only [fresh_pw, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      exact ⟨⟨by dsimp; omega, by dsimp; omega⟩,
        Wave8Contracts.M08.wordsOK_fresh_heap hAm.1 (by omega) (by decide) (by omega)
          (by have := hA5.2.2.1; omega)⟩
  have hpw_fresh_pw : fresh_pw.Pairwise Disj := by
    simp only [fresh_pw, List.pairwise_cons, List.Pairwise.nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, and_true, imp_false, not_true_eq_false]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
      ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, fun _ h => False.elim h⟩
    all_goals exact Or.inr (Or.inr (Or.inl (by omega)))
  have hu_fix : ∀ i ∈ fixedObjects s, M08IvlUnhit s mid i := by
    intro i hi
    apply m08_ivlUnhit_of_frameOutside_add hfr_0m hk_al_0m hAR.2.2.2.2.2.2.1
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj_fp
      · exact Or.inr (Or.inl rfl)
      · exact disj_flip (((hT.2.1 _ hba_S).2 j hj_fp).2 i hi)
    · rcases hF.1 i hi with hz | ⟨hal, _⟩
      · exact disj_fresh_of_zero_or_allocated_add hAR.2 hAm.2 hhp_0m (Or.inl hz)
      · exact disj_fresh_of_zero_or_allocated_add hAR.2 hAm.2 hhp_0m (Or.inr hal)
  obtain ⟨_, hno_bs32, hno_ts32, hno_ad0, hno_ws32⟩ := bal_accounts_role_props hT hba_nz
  have hu_ws : globN s "ws" ≠ 0 → M08IvlUnhit s mid (globN s "ws", 40) := fun h => by
    have hm := Wave8Contracts.M08.typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by decide)
    exact hu_fix _ (by simpa [h] using hm)
  have hu_bs : globN s "bs" ≠ 0 → M08IvlUnhit s mid (globN s "bs", 80) := fun h => by
    have hm := Wave8Contracts.M08.typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by decide)
    exact hu_fix _ (by simpa [h] using hm)
  have hu_ts : globN s "ts" ≠ 0 → M08IvlUnhit s mid (globN s "ts", 72) := fun h => by
    have hm := Wave8Contracts.M08.typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by decide)
    exact hu_fix _ (by simpa [h] using hm)
  have hu_bo : globN s "bo" ≠ 0 → M08IvlUnhit s mid (globN s "bo", 88) := fun h => by
    have hm := Wave8Contracts.M08.typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
    exact hu_fix _ (by simpa [h] using hm)
  have hu_jr : globN s "journal_cap" ≠ 0 → M08IvlUnhit s mid (globN s "journal", 32 * globN s "journal_cap") := fun h => by
    have hm : (globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
      simp [h]
    exact hu_fix _ hm
  have hu_other : ∀ u ∈ S, u ≠ tw.toNat → ∀ i ∈ htabFootprint s u, M08IvlUnhit s mid i := by
    intro u hu hne i hi
    apply m08_ivlUnhit_of_frameOutside_add hfr_0m hk_al_0m hAR.2.2.2.2.2.2.1
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj_fp
      · exact Or.inr (Or.inl rfl)
      · exact hT.2.2.1 u hu tw.toNat hba_S hne i hi j hj_fp
    · exact disj_fresh_of_zero_or_allocated_add hAR.2 hAm.2 hhp_0m (Or.inr ((hT.2.1 u hu).2 i hi).1)
  have hu_other_ba : ∀ u ∈ S, u ≠ globN s "bal_accounts" → ∀ i ∈ htabFootprint s u, M08IvlUnhit s mid i := by
    rw [← ht_eq]; exact hu_other
  have hother_fp : ∀ u ∈ S, u ≠ tw.toNat →
      (∀ k, k < 11 → hdr mid u k = hdr s u k) ∧ htabFootprint mid u = htabFootprint s u := by
    intro u hu hne
    have hwf := (hT.2.1 u hu).1
    have ht_fp : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
    have hu8 : u % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have h264' : heapEnd ≤ 2 ^ 64 := by decide
    have hhi : u + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; dsimp at this; omega
    exact Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit hu8 hhi (hu_other u hu hne _ ht_fp)
  have hbo_g : globN mid "bo" = globN s "bo" := hgs.1 ("bo", 88) (by simp [globalBuffers])
  have hbo_words : globN s "bo" ≠ 0 → ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW mid (globN s "bo" + k) = memW s (globN s "bo" + k) := fun hnz k hk => by
    have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    simpa [hbo_g] using Wave8Contracts.M08.rec_word_eq_of_unhit hAR.2 hF "bo" 88 (by decide) hbo_g hnz (hu_bo hnz) hk_in.1 hk_in.2
  have hbo_part := Wave8Contracts.M08.blockOutObjects_eq_of_bo_unhit hAR.2 hF hbo_g hT.2.2.2.2.2.2.2.2.2.2.1
    (fun h => hbo_words h 24 (by simp))
    (fun h => hbo_words h 32 (by simp))
    (fun h => hbo_words h 40 (by simp))
    (fun h => hbo_words h 56 (by simp))
    (fun h => hbo_words h 72 (by simp))
    (fun h => hbo_words h 80 (by simp))
    (fun _ _ => by simp [hm0_8_16.1, hm0_8_16.2.2])
    (fun _ _ => by simp [hm0_8_16.1, hm0_8_16.2.2])
    (fun h h40 => hu_fix (memW s (globN s "bo" + 40), 24) (by
      unfold fixedObjects; apply List.mem_append_left; apply List.mem_append_right
      simp [blockOutObjects, h, h40]))
    (fun h h72 => hu_fix (memW s (globN s "bo" + 72), 24) (by
      unfold fixedObjects; apply List.mem_append_left; apply List.mem_append_right
      simp [blockOutObjects, h, h72]))
  have hold_acc := fun ad (had : ad ∈ balRecords s) =>
    old_balAccount_congr_of_unhit hAR.2 hT hF hu_other_ba hno_ad0
      (fun i hi _ => hu_fix i (by unfold fixedObjects; exact List.mem_append_right _ hi))
      hm0_8_16 had
  obtain ⟨hF_mid, hfix_from⟩ := fixedTyped_of_balObjects_set_values_add
    hAR hAm hag hF hgs hbo_part.1 hba_nz hvalues_0m
    (fun ad had => (hold_acc ad had).1)
    hpw_obj_eq
    (fun i hi => ⟨⟨(hfresh_pw_props i hi).1.1, le_trans (hfresh_pw_props i hi).1.2 hhp_5m⟩, (hfresh_pw_props i hi).2⟩)
    hpw_fresh_pw
  have hsub : ∀ t ∈ S, t ∈ S ++ [t0w.toNat, t8w.toNat] :=
    fun t ht => List.mem_append_left _ ht
  obtain ⟨hjr_eq, hJ_mid⟩ := Wave8Contracts.M08.journalRoleSlots_eq_of_unhit
    hAR.1 hAm.1 hAR.2 hag hsub hJ hF hgs hu_ts hu_jr
  have hnd_alloc : ∀ o ∈ nodeExtents s Nd, o = (0, 0) ∨ Allocated s o := by
    intro o ho
    obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
    rcases hno with rfl | rfl
    · exact Or.inr (hTr.1.1 n hn).2.1
    · unfold nodePath
      split_ifs with hp
      · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hp.1 with h0 | ⟨_, hal, _⟩
        · exact absurd h0 hp.2
        · exact Or.inr hal
      · exact Or.inl rfl
  have hu_nd : ∀ o ∈ nodeExtents s Nd, M08IvlUnhit s mid o := by
    intro o ho
    apply m08_ivlUnhit_of_frameOutside_add hfr_0m hk_al_0m hAR.2.2.2.2.2.2.1
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj_fp
      · exact Or.inr (Or.inl rfl)
      · exact (hTr.2.1 o ho).1 tw.toNat hba_S j hj_fp
    · rcases hnd_alloc o ho with rfl | hal
      · exact Or.inl rfl
      · exact disj_fresh_of_zero_or_allocated_add hAR.2 hAm.2 hhp_0m (Or.inr hal)
  have hu_nd_rec : ∀ n ∈ Nd, M08IvlUnhit s mid (nodeIvl s n) := by
    intro n hn
    exact hu_nd _ (List.mem_flatMap.2 ⟨n, hn, by simp⟩)
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB mid (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hnz k hk
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, hin_p, _⟩
    · exact absurd h0 hnz
    · have h264 : heapLimit < 2 ^ 64 := by decide
      have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by
        have := hin_p.2; dsimp at this; omega
      let c := panByteAlignHOL (BitVec.ofNat 64 (memW s (n + 32) + k))
      have hc_nat : c.toNat = (memW s (n + 32) + k) / 8 * 8 := by
        have hal8 : 2 ^ ((64 : Nat) / 8).log2 = 8 := by decide
        change (BitVec.ofNat 64 ((BitVec.ofNat 64 (memW s (n + 32) + k)).toNat / 2 ^ ((64 : Nat) / 8).log2 *
          2 ^ ((64 : Nat) / 8).log2)).toNat = (memW s (n + 32) + k) / 8 * 8
        rw [hal8, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt,
          Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self _ 8) ha_lt)]
      have hp_mem : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
        have hp_eq : nodePath s n = (memW s (n + 32), memW s (n + 40)) := by simp [nodePath, h12, hnz]
        rw [← hp_eq]
        exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
      have hmem := hfr_0m c
        (fun j hj hcj => by
          obtain ⟨c1, c2⟩ := hcj
          rw [hc_nat] at c1 c2
          rcases List.mem_cons.1 hj with rfl | hj_fp
          · dsimp at c1 c2; omega
          · have hj_al := ((hT.2.1 _ hba_S).1.1 j hj_fp).2
            have hj1 := hj_al.1; have hj2 := hj_al.2.1
            have hdj := (hTr.2.1 _ hp_mem).1 tw.toNat hba_S j hj_fp
            rcases hdj with d | d | d | d <;> (try dsimp at c1 c2) <;> (try dsimp at d) <;> omega)
        (fun ⟨c1, c2⟩ => by
          dsimp at c1 c2; rw [hc_nat] at c1 c2
          have hp_hp8 : (globN s "heap_ptr") % 8 = 0 := hAR.2.2.2.2.2.2.1
          have hm_hp8 : (globN mid "heap_ptr") % 8 = 0 := hAm.2.2.2.2.2.2.1
          have hdj := disj_fresh_of_zero_or_allocated_add hAR.2 hAm.2 hhp_0m (Or.inr hal_p)
          rcases hdj with d | d | d | d <;> (try dsimp at d) <;> omega)
      unfold memB
      change (match mid.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v mid.be).toNat) =
             (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v s.be).toNat)
      rw [hmem, hbe_0m]
  obtain ⟨hNH_mid, hnd_eq⟩ := Wave8Contracts.M08.nodeHeap_congr_bytes
    hAR.1 hAm.1 hag hTr.1 hu_nd_rec hu_nd_byte
  exact balEnsureAlloc_worldStep_finish hAR hAm hag hT hF hTr hgs ht_eq hba_nz hba_S
    hhp_05 hhp_5m hpw_eq hpw_t0 ht0_s1 hs1_t8 ht8_l16 hl16_l24 hl24_l32 hl32_s5
    hfr_0m hfp_tw_5 hhdr0_tw_m hwf_tw_m hfp_tw_m hvalues_0m
    hwf_t0_m hwf_t8_m hfp_t0_m hfp_t8_m hfp_t0_5 hfp_t8_5 hpw_tabs_5
    hkey_t0_m hkey_t8_m hvals_t0_m hm0_m hm8_m hm16_m hm24_m hm32_m
    hlst16_m hobjs16_m hlst24_m hobjs24_m hlst32_m hobjs32_m hmem_rec
    hno_bs32 hno_ts32 hno_ws32 hu_ws hu_bs hu_ts hu_other hu_other_ba hother_fp
    hbo_part hold_acc hF_mid hfix_from hjr_eq hJ_mid hnd_alloc hNH_mid hnd_eq

private theorem balEnsureAlloc_recordsKept {F : Type}
    {s mid : PanSemStateFiniteExact 64 F} {tw : BitVec 64} {S0 : List Nat} {Nd0 : List Nat}
    (hAR : ArenaReady s) (hAm : ArenaReady mid) (hW0 : WorldTypedWith s S0 Nd0)
    (ht_eq : tw.toNat = globN s "bal_accounts")
    (hba_nz : globN s "bal_accounts" ≠ 0)
    (hgs : Wave8Contracts.M08.WorldGlobalsSame s mid)
    (hhp_0m : globN s "heap_ptr" ≤ globN mid "heap_ptr")
    (hWF_tw : HtabWF s tw.toNat)
    (hfr_0m : FrameOutside s mid
      ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat)
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr")) :
    RecordsKept (fun _ => []) stdKeep s mid := by
  have hk_al_0m : ∀ j ∈ ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat), j.1 % 8 = 0 := by
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj_fp
    · exact hAR.2.2.2.2.2.2.2.2.1
    · exact (hWF_tw.1 j hj_fp).2.1
  have hu_fixed_0m : ∀ i ∈ fixedObjects s, M08IvlUnhit s mid i := by
    intro i hi
    apply m08_ivlUnhit_of_frameOutside_add hfr_0m hk_al_0m hAR.2.2.2.2.2.2.1
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj_fp
      · exact Or.inr (Or.inl rfl)
      · have hba_S0 : tw.toNat ∈ S0 := by
          rw [ht_eq]
          rcases hW0.1.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
          · exact absurd h0 hba_nz
          · exact hm
        exact disj_flip (((hW0.1.2.1 _ hba_S0).2 j hj_fp).2 i hi)
    · rcases hW0.2.2.1.1 i hi with hz | ⟨hal, _⟩
      · exact disj_fresh_of_zero_or_allocated_add hAR.2 hAm.2 hhp_0m (Or.inl hz)
      · exact disj_fresh_of_zero_or_allocated_add hAR.2 hAm.2 hhp_0m (Or.inr hal)
  intro rec hrec hnz k hk _
  have hrec_tr : rec.1 ∈ ["ws", "bs", "ts", "bo"] ∧
      ∃ sz, (rec.1, sz) ∈ typedRecords ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
    simp only [stdKeep, M13.stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
    rcases hrec with rfl | rfl | rfl | rfl
    · refine ⟨by simp, 40, by decide, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    · refine ⟨by simp, 80, by decide, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    · refine ⟨by simp, 72, by decide, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    · refine ⟨by simp, 88, by decide, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
  obtain ⟨_, sz, htr, hk8, hksz⟩ := hrec_tr
  have hg_eq : globN mid rec.1 = globN s rec.1 :=
    hgs.1 (rec.1, sz) (Wave8Contracts.M08.typedRecord_mem_globalBuffers htr)
  have hfix_rec : (globN s rec.1, sz) ∈ fixedObjects s := by
    have hm := Wave8Contracts.M08.typedRecord_mem_fixedObjects s htr
    simpa [hnz] using hm
  have hu_rec : M08IvlUnhit s mid (globN s rec.1, sz) := hu_fixed_0m _ hfix_rec
  simpa [hg_eq] using Wave8Contracts.M08.rec_word_eq_of_unhit hAR.2 hW0.2.2.1 rec.1 sz htr hg_eq hnz hu_rec hk8 hksz

private theorem balEnsureAlloc_lst_mid {F : Type}
    {s5 mid : PanSemStateFiniteExact 64 F} (lw esz cap : Nat)
    (h5_hi : globN s5 "heap_ptr" ≤ heapLimit)
    (h8 : lw % 8 = 0) (hnz : lw ≠ 0) (hhi_lw : lw + 24 + esz * cap ≤ globN s5 "heap_ptr")
    (hu_lw : M08IvlUnhit s5 mid (lw, 24))
    (hok5 : LstOK s5 lw) (hobj5 : lstObjects s5 lw esz = [(lw, 24), (lw + 24, esz * cap)]) :
    LstOK mid lw ∧ lstObjects mid lw esz = [(lw, 24), (lw + 24, esz * cap)] := by
  have h264 : heapLimit < 2 ^ 64 := by decide
  have e0 : memW mid lw = memW s5 lw := by
    simpa using Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_lw h8 (by omega) ⟨by omega, by omega⟩
  have e8 : memW mid (lw + 8) = memW s5 (lw + 8) :=
    Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_lw (by omega) (by omega) ⟨by omega, by omega⟩
  have e16 : memW mid (lw + 16) = memW s5 (lw + 16) :=
    Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_lw (by omega) (by omega) ⟨by omega, by omega⟩
  refine ⟨?_, ?_⟩
  · unfold LstOK at hok5 ⊢; rw [e8, e16]; exact hok5
  · have heq : lstObjects mid lw esz = lstObjects s5 lw esz := by
      unfold lstObjects; rw [e0, e16]
    exact heq.trans hobj5

private theorem balEnsureAlloc_low_words {F : Type}
    {s mid : PanSemStateFiniteExact 64 F} {tw : BitVec 64}
    (hAR : ArenaReady s)
    (hWF_tw : HtabWF s tw.toNat)
    (hal_tw : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i)
    (hfr_0m : FrameOutside s mid
      ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat)
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr")) :
    memW mid 0 = memW s 0 ∧ memW mid 8 = memW s 8 ∧ memW mid 16 = memW s 16 := by
  have hs_lo : sourceBase ≤ globN s "heap_ptr" := hAR.2.1
  have hsb24 : 24 < sourceBase := by decide
  have hsc_lo : sourceBase ≤ scratchStart := by decide
  have hk_al_0m : ∀ j ∈ ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat), j.1 % 8 = 0 := by
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj_fp
    · exact hAR.2.2.2.2.2.2.2.2.1
    · exact (hWF_tw.1 j hj_fp).2.1
  have hu_low : M08IvlUnhit s mid (0, 24) := by
    apply m08_ivlUnhit_of_frameOutside_add hfr_0m hk_al_0m hAR.2.2.2.2.2.2.1
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj_fp
      · exact Or.inr (Or.inl rfl)
      · have hj_lo : sourceBase ≤ j.1 := by
          rcases hal_tw j hj_fp with hh | hh
          · exact hh.1
          · exact le_trans (le_trans hsc_lo hAR.2.2.2.1) (le_trans hAR.2.2.2.2.1 hh.1)
        exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
    · exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
  exact
    ⟨by simpa using Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_low (by omega) (by decide) ⟨by omega, by omega⟩,
     Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_low (by omega) (by decide) ⟨by omega, by omega⟩,
     Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_low (by omega) (by decide) ⟨by omega, by omega⟩⟩

private theorem balEnsureAlloc_pw_slots_mid {F : Type}
    {s5 mid : PanSemStateFiniteExact 64 F} {pw t0w t8w l16w l24w l32w : BitVec 64}
    (h5_hi : globN s5 "heap_ptr" ≤ heapLimit)
    (hpw8 : pw.toNat % 8 = 0) (hpw_hi : pw.toNat + 40 ≤ globN s5 "heap_ptr")
    (hu_pw_5m : M08IvlUnhit s5 mid (pw.toNat, 40))
    (hm0_5 : memW s5 pw.toNat = t0w.toNat) (hm8_5 : memW s5 (pw.toNat + 8) = t8w.toNat)
    (hm16_5 : memW s5 (pw.toNat + 16) = l16w.toNat) (hm24_5 : memW s5 (pw.toNat + 24) = l24w.toNat)
    (hm32_5 : memW s5 (pw.toNat + 32) = l32w.toNat) :
    memW mid pw.toNat = t0w.toNat ∧
    memW mid (pw.toNat + 8) = t8w.toNat ∧
    memW mid (pw.toNat + 16) = l16w.toNat ∧
    memW mid (pw.toNat + 24) = l24w.toNat ∧
    memW mid (pw.toNat + 32) = l32w.toNat := by
  have h264 : heapLimit < 2 ^ 64 := by decide
  exact ⟨(by simpa using Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_pw_5m hpw8 (by omega) ⟨by omega, by omega⟩ :
      memW mid pw.toNat = memW s5 pw.toNat).trans hm0_5,
    (Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_pw_5m (by omega) (by omega) ⟨by omega, by omega⟩).trans hm8_5,
    (Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_pw_5m (by omega) (by omega) ⟨by omega, by omega⟩).trans hm16_5,
    (Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_pw_5m (by omega) (by omega) ⟨by omega, by omega⟩).trans hm24_5,
    (Wave8Contracts.M08.memW_eq_of_ivlUnhit hu_pw_5m (by omega) (by omega) ⟨by omega, by omega⟩).trans hm32_5⟩

private theorem balEnsureAlloc_transfer {F : Type}
    {s s1 s5 mid : PanSemStateFiniteExact 64 F}
    {tw pw t0w t8w l16w l24w l32w : BitVec 64} {S0 Nd0 : List Nat}
    (hAR : ArenaReady s) (hA5 : ArenaReady s5) (hAm : ArenaReady mid)
    (hW0 : WorldTypedWith s S0 Nd0)
    (ht_eq : tw.toNat = globN s "bal_accounts")
    (hba_nz : globN s "bal_accounts" ≠ 0)
    (hWF_tw : HtabWF s tw.toNat)
    (hal_tw : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i)
    (hpw_eq : pw.toNat = globN s "heap_ptr") (hpw8 : pw.toNat % 8 = 0)
    (hpw_t0 : pw.toNat + 40 ≤ t0w.toNat) (ht0_s1 : t0w.toNat + 88 ≤ globN s1 "heap_ptr")
    (hs1_t8 : globN s1 "heap_ptr" ≤ t8w.toNat) (ht8_l16 : t8w.toNat + 88 ≤ l16w.toNat)
    (hl16_l24 : l16w.toNat + 24 + 160 = l24w.toNat)
    (hl24_l32 : l24w.toNat + 24 + 64 = l32w.toNat)
    (hl32_s5 : l32w.toNat + 24 + 48 = globN s5 "heap_ptr")
    (hbe5 : s5.be = s.be) (hsp5 : globN s5 "scratch_ptr" = globN s "scratch_ptr")
    (hgl5 : ∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = s5.globals.lookup k)
    (hfr_05 : FrameOutside s s5 [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN s5 "heap_ptr" - globN s "heap_ptr"))
    (hwf_t0_5 : HtabWF s5 t0w.toNat) (hcnt_t0_5 : hdr s5 t0w.toNat 3 = 0)
    (hkey_t0_5 : hdr s5 t0w.toNat 0 = 32)
    (hfp_t0_5 : ∀ i ∈ htabFootprint s5 t0w.toNat, Allocated s5 i ∧ Inside i (pw.toNat + 40) (globN s1 "heap_ptr"))
    (hwf_t8_5 : HtabWF s5 t8w.toNat)
    (hkey_t8_5 : hdr s5 t8w.toNat 0 = 32)
    (hfp_t8_5 : ∀ i ∈ htabFootprint s5 t8w.toNat, Allocated s5 i ∧ Inside i (globN s1 "heap_ptr") l16w.toNat)
    (hpw_tabs_5 : ∀ t ∈ ([t0w.toNat, t8w.toNat] : List Nat), ∀ u ∈ ([t0w.toNat, t8w.toNat] : List Nat),
      t ≠ u → ∀ i ∈ htabFootprint s5 t, ∀ j ∈ htabFootprint s5 u, Disj i j)
    (hm0_5 : memW s5 pw.toNat = t0w.toNat) (hm8_5 : memW s5 (pw.toNat + 8) = t8w.toNat)
    (hm16_5 : memW s5 (pw.toNat + 16) = l16w.toNat) (hm24_5 : memW s5 (pw.toNat + 24) = l24w.toNat)
    (hm32_5 : memW s5 (pw.toNat + 32) = l32w.toNat)
    (hlst16_5 : LstOK s5 l16w.toNat) (hobjs16_5 : lstObjects s5 l16w.toNat 40 = [(l16w.toNat, 24), (l16w.toNat + 24, 160)])
    (hlst24_5 : LstOK s5 l24w.toNat) (hobjs24_5 : lstObjects s5 l24w.toNat 16 = [(l24w.toNat, 24), (l24w.toNat + 24, 64)])
    (hlst32_5 : LstOK s5 l32w.toNat) (hobjs32_5 : lstObjects s5 l32w.toNat 24 = [(l32w.toNat, 24), (l32w.toNat + 24, 48)])
    (hexit : HtabExitAt tw.toNat s5 mid)
    (hvalues_5m : HtabSetValuesPost s5 mid tw.toNat pw.toNat)
    (hbe_mid : mid.be = s5.be) (hmem_rec : pw.toNat ∈ balRecords mid) :
    globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep
      (fun _ _ post _ _ => pw.toNat ∈ balRecords post) s
      (some (.returned (.val (.word pw)))) mid := by
  obtain ⟨hAm_exit, hwf_tw_m, hhdr0_tw_5m, _, hhp_5m, hfp_tw_m, hfr_5m, hgl_5m⟩ := hexit
  have hsp8 : (globN s "scratch_ptr") % 8 = 0 := hAR.2.2.2.2.2.2.2.2.1
  have hhp_05 : globN s "heap_ptr" ≤ globN s5 "heap_ptr" := by omega
  have hhp_0m : globN s "heap_ptr" ≤ globN mid "heap_ptr" := le_trans hhp_05 hhp_5m
  have hgk : GlobalsKept ["heap_ptr"] s mid := by
    intro k hk
    have hk' : k ≠ ofString "heap_ptr" := fun heq => hk (by simp [heq])
    exact (hgl5 k hk').trans (hgl_5m k hk)
  have hgs : Wave8Contracts.M08.WorldGlobalsSame s mid :=
    Wave8Contracts.M08.worldGlobalsSame_of_kept hgk (fun name h => Or.inl (by simpa using h))
  have hsp_mid : globN mid "scratch_ptr" = globN s "scratch_ptr" :=
    Wave8Contracts.M08.globN_eq_of_lookup (hgk (ofString "scratch_ptr") (by decide))
  have hfmp_s5 : globN s5 "frame_mem_ptr" = globN s "frame_mem_ptr" :=
    Wave8Contracts.M08.globN_eq_of_lookup (hgl5 (ofString "frame_mem_ptr") (by decide))
  have hbe_0m : mid.be = s.be := hbe_mid.trans hbe5
  have hu_tw_05 : ∀ i ∈ htabFootprint s tw.toNat, M08IvlUnhit s s5 i := by
    intro i hi
    apply m08_ivlUnhit_of_frameOutside_add hfr_05
    · intro j hj; simp only [List.mem_singleton] at hj; subst hj; exact hsp8
    · exact hAR.2.2.2.2.2.2.1
    · intro j hj; simp only [List.mem_singleton] at hj; subst hj; exact Or.inr (Or.inl rfl)
    · exact disj_fresh_of_zero_or_allocated_add hAR.2 hA5.2 hhp_05 (Or.inr (hal_tw i hi))
  obtain ⟨hwf_tw_5, hfp_tw_5, hhdr_tw_05⟩ :=
    htabWF_transfer_unhit hAR hA5 hWF_tw hu_tw_05
      (fun i hi => AllocatorGrows.allocated (show AllocatorGrows s s5 from ⟨hhp_05, by omega⟩) (hal_tw i hi))
  have hhdr0_tw_m : hdr mid tw.toNat 0 = hdr s tw.toNat 0 :=
    hhdr0_tw_5m.trans (hhdr_tw_05 0 (by omega))
  have hvals_tw_05 : htabValues s5 tw.toNat = htabValues s tw.toNat :=
    Wave8Contracts.M08.htabValues_eq_of_unhit hWF_tw hu_tw_05
  have hvalues_0m : HtabSetValuesPost s mid (globN s "bal_accounts") pw.toNat := by
    unfold HtabSetValuesPost at hvalues_5m ⊢
    rw [← ht_eq, ← hvals_tw_05]
    exact hvalues_5m
  have hfr_0m : FrameOutside s mid
      ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat)
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") := by
    intro a hkeep hfresh
    have h1 := hfr_5m a (fun j hj => by
      rw [hfp_tw_5] at hj
      exact hkeep j (List.mem_cons_of_mem _ hj))
      (fun ⟨hc1, hc2⟩ => hfresh ⟨by dsimp at hc1 ⊢; omega, by dsimp at hc2 ⊢; omega⟩)
    have h2 := hfr_05 a (fun j hj => by
      simp only [List.mem_singleton] at hj; subst hj
      exact hkeep _ List.mem_cons_self)
      (fun ⟨hc1, hc2⟩ => hfresh ⟨by dsimp at hc1 ⊢; omega, by dsimp at hc2 ⊢; omega⟩)
    exact h1.trans h2
  have hk_al_0m : ∀ j ∈ ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat), j.1 % 8 = 0 := by
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj_fp
    · exact hsp8
    · exact (hWF_tw.1 j hj_fp).2.1
  have hu_5m_of_fresh05 : ∀ {i : Ivl},
      Inside i (globN s "heap_ptr") (globN s5 "heap_ptr") → M08IvlUnhit s5 mid i := by
    intro i hi_in
    apply m08_ivlUnhit_of_frameOutside_add hfr_5m
    · intro j hj; exact (hwf_tw_5.1 j hj).2.1
    · exact hA5.2.2.2.2.2.2.1
    · intro j hj
      rw [hfp_tw_5] at hj
      exact Wave8Contracts.M08.disj_allocated_fresh_heap hAR.2 hA5.2 (hal_tw j hj) hi_in
    · exact Or.inr (Or.inr (Or.inl (by have := hi_in.2; dsimp; omega)))
  have hs_lo : sourceBase ≤ globN s "heap_ptr" := hAR.2.1
  have h5_hi : globN s5 "heap_ptr" ≤ heapLimit := hA5.2.2.1
  obtain ⟨hm0_m, hm8_m, hm16_m, hm24_m, hm32_m⟩ :=
    balEnsureAlloc_pw_slots_mid h5_hi hpw8 (by omega)
      (hu_5m_of_fresh05 ⟨by dsimp; omega, by dsimp; omega⟩)
      hm0_5 hm8_5 hm16_5 hm24_5 hm32_5
  obtain ⟨hwf_t0_m, hfp_t0_m, hhdr_t0_m⟩ :=
    htabWF_transfer_unhit hA5 hAm hwf_t0_5
      (fun i hi => hu_5m_of_fresh05 ⟨le_trans (by omega) (hfp_t0_5 i hi).2.1, le_trans (hfp_t0_5 i hi).2.2 (by omega)⟩)
      (fun i hi => Or.inl ⟨by have := (hfp_t0_5 i hi).2.1; omega, by have := (hfp_t0_5 i hi).2.2; omega⟩)
  obtain ⟨hwf_t8_m, hfp_t8_m, hhdr_t8_m⟩ :=
    htabWF_transfer_unhit hA5 hAm hwf_t8_5
      (fun i hi => hu_5m_of_fresh05 ⟨le_trans (by omega) (hfp_t8_5 i hi).2.1, le_trans (hfp_t8_5 i hi).2.2 (by omega)⟩)
      (fun i hi => Or.inl ⟨by have := (hfp_t8_5 i hi).2.1; omega, by have := (hfp_t8_5 i hi).2.2; omega⟩)
  have hcnt_t0_m : hdr mid t0w.toNat 3 = 0 := (hhdr_t0_m 3 (by omega)).trans hcnt_t0_5
  have hkey_t0_m : hdr mid t0w.toNat 0 = 32 := (hhdr_t0_m 0 (by omega)).trans hkey_t0_5
  have hkey_t8_m : hdr mid t8w.toNat 0 = 32 := (hhdr_t8_m 0 (by omega)).trans hkey_t8_5
  have hvals_t0_m : htabValues mid t0w.toNat = [] := by
    unfold htabValues; rw [hcnt_t0_m]; rfl
  have hl32_8 : l32w.toNat % 8 = 0 := by
    have h := hA5.2.2.2.2.2.2.1; omega
  have hl24_8 : l24w.toNat % 8 = 0 := by omega
  have hl16_8 : l16w.toNat % 8 = 0 := by omega
  obtain ⟨hlst16_m, hobjs16_m⟩ := balEnsureAlloc_lst_mid l16w.toNat 40 4 h5_hi hl16_8 (by omega) (by omega)
    (hu_5m_of_fresh05 ⟨by dsimp; omega, by dsimp; omega⟩) hlst16_5 hobjs16_5
  obtain ⟨hlst24_m, hobjs24_m⟩ := balEnsureAlloc_lst_mid l24w.toNat 16 4 h5_hi hl24_8 (by omega) (by omega)
    (hu_5m_of_fresh05 ⟨by dsimp; omega, by dsimp; omega⟩) hlst24_5 hobjs24_5
  obtain ⟨hlst32_m, hobjs32_m⟩ := balEnsureAlloc_lst_mid l32w.toNat 24 2 h5_hi hl32_8 (by omega) (by omega)
    (hu_5m_of_fresh05 ⟨by dsimp; omega, by dsimp; omega⟩) hlst32_5 hobjs32_5
  have hm0_8_16 := balEnsureAlloc_low_words hAR hWF_tw hal_tw hfr_0m
  refine ⟨hsp_mid, hAm, hhp_0m, hgk,
    balEnsureAlloc_recordsKept hAR hAm hW0 ht_eq hba_nz hgs hhp_0m hWF_tw hfr_0m, ?_⟩
  intro S Nd hWT _
  exact balEnsureAlloc_worldStep_core hAR hA5 hAm hWT ht_eq hba_nz hgk hsp_mid hhp_05 hhp_5m
    hbe_0m hpw_eq hpw8 hpw_t0 ht0_s1 hs1_t8 ht8_l16 hl16_l24 hl24_l32 hl32_s5
    hfr_0m hfp_tw_5 hhdr0_tw_m hwf_tw_m hfp_tw_m hvalues_0m
    hwf_t0_m hwf_t8_m hfp_t0_m hfp_t8_m hfp_t0_5 hfp_t8_5 hpw_tabs_5
    hkey_t0_m hkey_t8_m hvals_t0_m hm0_m hm8_m hm16_m hm24_m hm32_m
    hlst16_m hobjs16_m hlst24_m hobjs24_m hlst32_m hobjs32_m hm0_8_16 hmem_rec

private theorem balEnsureAlloc_worldStep {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (tw kw : BitVec 64)
    (hWOK : WorldOK s)
    (hroot : s.globals.lookup (ofString "bal_accounts") = some (.val (.word tw)))
    (ht_nz : tw ≠ 0)
    (hak : s.locals.lookup (ofString "addr") = some (.val (.word kw)))
    (hnt : (evaluateHOLFiniteState s balEnsureAllocProg).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s balEnsureAllocProg).1) :
    ∃ (pw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s balEnsureAllocProg).1 = some (.returned (.val (.word pw))) ∧
      (∃ L_out, (evaluateHOLFiniteState s balEnsureAllocProg).2 = { mid with locals := L_out }) ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      WorldStep (fun _ => []) ["heap_ptr"] stdKeep
        (fun _ _ post _ _ => pw.toNat ∈ balRecords post) s
        (some (.returned (.val (.word pw)))) mid := by
  have hAR : ArenaReady s := hWOK.1
  have ht_eq : tw.toNat = globN s "bal_accounts" := by
    simp [globN, hroot]
  obtain ⟨S0, hWT0⟩ := hWOK.2
  obtain ⟨Nd0, hW0⟩ := (worldTyped_iff_with s S0).1 hWT0
  have hba_nz : globN s "bal_accounts" ≠ 0 := by
    intro h0; apply ht_nz; apply BitVec.eq_of_toNat_eq; simp [ht_eq, h0]
  have htw_nz : tw.toNat ≠ 0 := by rw [ht_eq]; exact hba_nz
  have hba_S0 : tw.toNat ∈ S0 := by
    rw [ht_eq]
    rcases hW0.1.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
    · exact absurd h0 hba_nz
    · exact hm
  have hWF_tw : HtabWF s tw.toNat := (hW0.1.2.1 _ hba_S0).1
  have hal_tw : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i :=
    fun i hi => ((hW0.1.2.1 _ hba_S0).2 i hi).1
  obtain ⟨pw, t0w, t8w, l16w, l24w, l32w, s1, s5, mid,
    hpw_eq, hpw8, _,
    hpw_t0, ht0_s1, hs1_t8, ht8_l16, hl16_l24, hl24_l32, hl32_s5,
    hA5, hbe5, hsp5, hgl5, hfr_05,
    hwf_t0_5, hcnt_t0_5, hkey_t0_5, hfp_t0_5,
    hwf_t8_5, _, hkey_t8_5, hfp_t8_5, hpw_tabs_5,
    hm0_5, hm8_5, hm16_5, hm24_5, hm32_5,
    hlst16_5, hobjs16_5, hlst24_5, hobjs24_5, hlst32_5, hobjs32_5,
    hexit, hvalues_5m, hbe_mid, hmem_rec, hev_fst, hev_snd⟩ :=
    balEnsureAlloc_eval s tw kw hAR hroot hak htw_nz hWF_tw hal_tw hnt hres
  obtain ⟨hsp_mid, hWS⟩ := balEnsureAlloc_transfer hAR hA5 hexit.1 hW0 ht_eq hba_nz hWF_tw hal_tw
    hpw_eq hpw8 hpw_t0 ht0_s1 hs1_t8 ht8_l16 hl16_l24 hl24_l32 hl32_s5
    hbe5 hsp5 hgl5 hfr_05 hwf_t0_5 hcnt_t0_5 hkey_t0_5 hfp_t0_5
    hwf_t8_5 hkey_t8_5 hfp_t8_5 hpw_tabs_5 hm0_5 hm8_5 hm16_5 hm24_5 hm32_5
    hlst16_5 hobjs16_5 hlst24_5 hobjs24_5 hlst32_5 hobjs32_5
    hexit hvalues_5m hbe_mid hmem_rec
  exact ⟨pw, mid, hev_fst, hev_snd, hsp_mid, hWS⟩

private theorem balRecord_slot_load {F : Type}
    (s : PanSemStateFiniteExact 64 F) (adw off : BitVec 64) (adExp : ExpHOL 64)
    (hW : WorldOK s)
    (had_rec : adw.toNat ∈ balRecords s)
    (hev_ad : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) adExp =
      some (.val (.word adw)))
    (hoff8 : off.toNat % 8 = 0)
    (hoff_hi : off.toNat + 8 ≤ 40) :
    adw ≠ 0 ∧ adw.toNat % 8 = 0 ∧ sourceBase ≤ adw.toNat ∧ adw.toNat + 40 ≤ heapEnd ∧
    ∃ fw : BitVec 64,
      fw.toNat = memW s (adw.toNat + off.toNat) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [adExp, .const off])) = some (.val (.word fw)) := by
  have hAR : ArenaReady s := hW.1
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  have had_fix : (adw.toNat, 40) ∈ fixedObjects s := by
    unfold fixedObjects; apply List.mem_append_right; unfold balObjects
    exact List.mem_flatMap.2 ⟨adw.toNat, had_rec, List.mem_cons_self⟩
  rcases hWT0.2.2.1.1 _ had_fix with h0 | ⟨hal_ad, hw_ad⟩
  · cases h0
  have had_bnd : adw.toNat + 40 ≤ heapEnd ∧ adw.toNat + 40 ≤ 2 ^ 64 :=
    ivl_allocated_bound hAR.2 hal_ad
  have had_lo : sourceBase ≤ adw.toNat := by
    rcases hal_ad with h | h
    · exact h.1
    · have h1 := hAR.2.2.2.1; have h2 := hAR.2.2.2.2.1
      have h3 : sourceBase ≤ scratchStart := by decide
      exact le_trans h3 (le_trans h1 (le_trans h2 h.1))
  have hsb_pos : 0 < sourceBase := by decide
  have had_nz : adw ≠ 0 := by
    intro h0; subst h0; simp at had_lo; omega
  have had_align : adw.toNat % 8 = 0 := hw_ad.1
  have had_add_lt : adw.toNat + off.toNat < 2 ^ 64 := by omega
  have had_add_bv : adw + off = BitVec.ofNat 64 (adw.toNat + off.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hdom : s.memaddrs (adw + off) := by
    rw [hAR.1.memaddrs, Wave8Contracts.M08.ordinaryDomain_iff, had_add_bv,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt had_add_lt]
    exact ⟨by omega, by omega, by omega⟩
  obtain ⟨fw, _, hfw_mem0⟩ := hw_ad.2.2 (off.toNat / 8) (Nat.div_lt_of_lt_mul (by omega))
  have hfw_mem : s.memory (adw + off) = .word fw := by
    have heq_addr : BitVec.ofNat 64 (adw.toNat + 8 * (off.toNat / 8)) = adw + off := by
      rw [had_add_bv]; apply congrArg (BitVec.ofNat 64)
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hoff8)]
    rw [← heq_addr]; exact hfw_mem0
  have hfw_nat : fw.toNat = memW s (adw.toNat + off.toNat) := by
    change fw.toNat = (match s.memory (BitVec.ofNat 64 (adw.toNat + off.toNat)) with | .word w => w.toNat)
    rw [← had_add_bv, hfw_mem]
  have hz_off : off + 0 = off := BitVec.add_zero _
  refine ⟨had_nz, had_align, had_lo, had_bnd.1, fw, hfw_nat, ?_⟩
  simp [evalHOLExact, evalListHOLExact, hev_ad, valueIsWord, valueWord, wordOpHOL, wordOp,
    hz_off, memLoadHOLExact, isWfShapeExactHOL, hdom, hfw_mem]

theorem decCall_bal_ensure_account_resumes_idx {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (x : MlS) (addrExp : ExpHOL 64) (addrw : BitVec 64) (cont : ProgHOL 64)
    (hW : WorldOK s)
    (hev_addr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp =
      some (.val (.word addrw)))
    (hnt : (evaluateHOLFiniteState s
      (.decCall x .one (ofString "bal_ensure_account") [addrExp] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall x .one (ofString "bal_ensure_account") [addrExp] cont)).1) :
    ∃ (adw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      adw ≠ 0 ∧
      adw.toNat % 8 = 0 ∧
      sourceBase ≤ adw.toNat ∧
      adw.toNat + 40 ≤ heapEnd ∧
      WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid ∧
      WorldOK mid ∧
      adw.toNat ∈ balRecords mid ∧
      (∀ off : BitVec 64, off.toNat % 8 = 0 → off.toNat + 8 ≤ 40 →
        ∃ fw : BitVec 64,
          fw.toNat = memW mid (adw.toNat + off.toNat) ∧
          @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
            (.load .one (.op .add [.var .local x, .const off])) = some (.val (.word fw))) ∧
      mid.locals.lookup x = some (.val (.word adw)) ∧
      (∀ y, y ≠ x → mid.locals.lookup y = s.locals.lookup y) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "bal_ensure_account") [addrExp] cont)).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall x .one (ofString "bal_ensure_account") [addrExp] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) } := by
  have hAs := hW.1
  have hG := hAs.1
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [addrExp] = some [.val (.word addrw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hev_addr]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "bal_ensure_account")
    (ofString "addr") (sourceFnBody Guest.Software.guestFn_bal_ensure_account) addrw
    (by rw [hG.code]; exact lookup_bal_ensure_account_add)
  rw [hargs] at hnt hres; dsimp only at hnt hres
  rw [hlk] at hnt hres; dsimp only at hnt hres
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at hnt; exact absurd rfl hnt
  · rw [if_neg hcz] at hnt hres
    let cmap := HolFiniteMapExact.empty.update (ofString "addr", ValueHOL.val (.word addrw))
    let ent := callEntryStateHOLFinite s cmap
    have hent_eq : ent = { s with locals := cmap, clock := s.clock - 1 } := rfl
    have hent_W : WorldOK ent := (worldOK_with_locals s cmap (s.clock - 1)).2 hW
    have hent_G : GuestInv ent := hent_W.1.1
    have hent_addr : ent.locals.lookup (ofString "addr") = some (.val (.word addrw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hbody_out : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_bal_ensure_account) with ⟨rb, sb⟩
    have hbody_out' : evaluateHOLFiniteState ent
        (sourceFnBody Guest.Software.guestFn_bal_ensure_account) = (rb, sb) := hbody_out
    rw [hbody_out] at hnt hres
    have hbody_nt : (evaluateHOLFiniteState ent
        (sourceFnBody Guest.Software.guestFn_bal_ensure_account)).1 ≠ some .timeOut := by
      rw [hbody_out']; intro hto; dsimp only at hto; subst hto; exact hnt rfl
    have hbody_res : Resumes (evaluateHOLFiniteState ent
        (sourceFnBody Guest.Software.guestFn_bal_ensure_account)).1 := by
      rw [hbody_out']; dsimp only
      cases rb with
      | none => exact absurd hres not_resumes_error
      | some rb' =>
        cases rb' with
        | timeOut => exact absurd rfl hnt
        | «break» | «continue» | error => exact absurd hres not_resumes_error
        | finalFfi _ => exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        | exception e ev =>
          exfalso
          rcases hres with ⟨_, h⟩ | ⟨e', ev', h, hne⟩
          · simp at h
          · dsimp only at h; injection h with h'; injection h' with he1 he2; subst he1 he2
            exact bal_ensure_account_no_catchable_exn_add ent hG.code e ev hne
              (congrArg Prod.fst hbody_out')
        | returned vb => exact Or.inl ⟨vb, rfl⟩
    set cont_m : ProgHOL 64 :=
      .seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
              (.return (.rfield 1 (.var .local (ofString "m")))) .skip)
        balEnsureAllocProg
    have hfn_eq : sourceFnBody Guest.Software.guestFn_bal_ensure_account =
        .decCall (ofString "m") (.comb [.one, .one]) (ofString "htab_get")
          [.var .global (ofString "bal_accounts"), .var .local (ofString "addr")] cont_m := rfl
    rw [hfn_eq] at hbody_nt hbody_res hbody_out'
    obtain ⟨tw, kw, f0, f1, ck, hev_t, hev_k, htw_nz, hf1_val, hnt1, hres1, heq1_r, heq1_s⟩ :=
      decCall_htab_get_resumes ent (ofString "m")
        (.var .global (ofString "bal_accounts")) (.var .local (ofString "addr")) cont_m
        hent_G hbody_nt hbody_res
    set s1 := setVarHOLFinite (ofString "m") (.rStruct [.val (.word f0), .val (.word f1)])
      { ent with clock := ck }
    have hs1_eq : s1 = { s with locals := s1.locals, clock := ck } := rfl
    have hs1_W : WorldOK s1 := (worldOK_with_locals s s1.locals ck).2 hW
    have hs1_m : s1.locals.lookup (ofString "m") = some (.rStruct [.val (.word f0), .val (.word f1)]) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs1_addr : s1.locals.lookup (ofString "addr") = some (.val (.word addrw)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "m" ≠ ofString "addr" by decide, hent_addr]
    obtain ⟨baw, hbaw⟩ := hAs.2.2.2.2.2.2.2.2.2 "bal_accounts" (by decide)
    have hbaw_s : s.globals.lookup (ofString "bal_accounts") = some (.val (.word baw)) := hbaw
    have htw_eq : tw = baw := by
      have hbaw_ent : ent.globals.lookup (ofString "bal_accounts") = some (.val (.word baw)) := hbaw_s
      simp [evalHOLExact, hbaw_ent] at hev_t; exact hev_t.symm
    subst htw_eq
    have hroot_nat : globN s "bal_accounts" = tw.toNat := by simp [globN, hbaw_s]
    by_cases hf0 : f0 = 0
    · subst hf0
      have hmiss := bal_ensure_missing_tail s1 f1 balEnsureAllocProg hs1_m
      change evaluateHOLFiniteState s1 cont_m = evaluateHOLFiniteState s1 balEnsureAllocProg at hmiss
      rw [hmiss] at hnt1 hres1 heq1_r heq1_s
      obtain ⟨adw, mid_a, ha_fst, ⟨L_out, ha_snd⟩, _, hws_a⟩ :=
        balEnsureAlloc_worldStep s1 tw addrw hs1_W hbaw_s htw_nz hs1_addr hnt1 hres1
      let mid : PanSemStateFiniteExact 64 F :=
        setVarHOLFinite x (.val (.word adw)) { sb with locals := s.locals }
      have hrb_eq : rb = some (.returned (.val (.word adw))) := by
        have h1 := congrArg Prod.fst hbody_out'
        dsimp only at h1; rw [← h1, heq1_r, ha_fst]
      have hsb_eq : sb =
          { mid_a with
            locals := HolFiniteMapExact.resVarEq L_out
              (ofString "m", ent.locals.lookup (ofString "m")) } := by
        have h2 := congrArg Prod.snd hbody_out'
        dsimp only at h2; rw [← h2, heq1_s, ha_snd]
      have hmid_eq : mid = { mid_a with locals := s.locals.update (x, .val (.word adw)) } := by
        simp [mid, hsb_eq, setVarHOLFinite]
      have hws_s_mid_a : WorldStep (fun _ => []) ["heap_ptr"] stdKeep
          (fun _ _ post _ _ => adw.toNat ∈ balRecords post) s none mid_a :=
        worldStep_with_locals_left hs1_eq rfl (fun _ _ h => h) hws_a
      have hws_s_mid_rec : WorldStep (fun _ => []) ["heap_ptr"] stdKeep
          (fun _ _ post _ _ => adw.toNat ∈ balRecords post) s none mid := by
        rw [hmid_eq]
        exact worldStep_with_locals_right _ mid_a.clock (fun _ _ h => h) hws_s_mid_a
      have hws_total : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid :=
        worldStep_weaken (fun _ h => h) (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
          (fun _ _ _ _ hi => False.elim (List.not_mem_nil hi)) (fun _ _ _ => trivial) hws_s_mid_rec
      have hW_mid : WorldOK mid := worldOK_of_step hW hws_total
      obtain ⟨S0, hWT0_ex⟩ := hW.2
      obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
      obtain ⟨_, _, _, _, _, _, had_rec⟩ :=
        hws_s_mid_rec.2.2.2.2 S0 Nd0 hWT0 (fun _ hi => False.elim (List.not_mem_nil hi))
      have hmid_x : mid.locals.lookup x = some (.val (.word adw)) := by
        simp [hmid_eq, HolFiniteMapExact.lookup_update, FUPDATE]
      have hmid_other : ∀ y, y ≠ x → mid.locals.lookup y = s.locals.lookup y := by
        intro y hy; simp [hmid_eq, HolFiniteMapExact.lookup_update, FUPDATE, hy, Ne.symm hy]
      have hev_x : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
          (.var .local x) = some (.val (.word adw)) := by
        simp [evalHOLExact, hmid_x]
      obtain ⟨had_nz, had8, had_lo, had_hi, _⟩ :=
        balRecord_slot_load mid adw 0#64 (.var .local x) hW_mid had_rec hev_x (by decide) (by decide)
      have hsh_ad : (shapeEqHOL (shapeOfHOLExact (.val (.word adw) : ValueHOL 64)) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word adw) : ValueHOL 64)) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      subst rb
      dsimp only at hnt hres
      rw [if_pos hsh_ad] at hnt hres
      have heval_eq : evaluateHOLFiniteState s
          (.decCall x .one (ofString "bal_ensure_account") [addrExp] cont) =
          ((evaluateHOLFiniteState mid cont).1,
            { (evaluateHOLFiniteState mid cont).2 with
              locals := HolFiniteMapExact.resVarEq
                (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) }) := by
        rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]; dsimp only
        rw [hlk]; dsimp only; rw [if_neg hcz, hbody_out]; dsimp only
        rw [if_pos hsh_ad]
      refine ⟨adw, mid, had_nz, had8, had_lo, had_hi, hws_total, hW_mid, had_rec,
        fun off hoff8 hoff_hi =>
          (balRecord_slot_load mid adw off (.var .local x) hW_mid had_rec hev_x hoff8 hoff_hi).2.2.2.2,
        hmid_x, hmid_other, hnt, hres, by rw [heval_eq], by rw [heval_eq]⟩
    · obtain ⟨hex_ev, _⟩ := bal_ensure_existing_tail s1 f0 f1 balEnsureAllocProg hs1_W hs1_m hf0
      change evaluateHOLFiniteState s1 cont_m =
        (some (.returned (.val (.word f1))), emptyLocalsHOLFinite s1) at hex_ev
      let mid : PanSemStateFiniteExact 64 F :=
        setVarHOLFinite x (.val (.word f1)) { sb with locals := s.locals }
      have hrb_eq : rb = some (.returned (.val (.word f1))) := by
        have h1 := congrArg Prod.fst hbody_out'
        dsimp only at h1; rw [← h1, heq1_r, hex_ev]
      have hsb_eq : sb =
          { emptyLocalsHOLFinite s1 with
            locals := HolFiniteMapExact.resVarEq
              (emptyLocalsHOLFinite s1).locals (ofString "m", ent.locals.lookup (ofString "m")) } := by
        have h2 := congrArg Prod.snd hbody_out'
        dsimp only at h2; rw [← h2, heq1_s, hex_ev]
      have hmid_eq : mid = { s with locals := s.locals.update (x, .val (.word f1)), clock := ck } := by
        dsimp only [mid]
        rw [hsb_eq]
        dsimp only [setVarHOLFinite, emptyLocalsHOLFinite]
        rw [hs1_eq]
      have hws_total : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid :=
        worldStep_refl (fun _ => []) ["heap_ptr"] hAs (by rw [hmid_eq])
      have hW_mid : WorldOK mid := by rw [hmid_eq]; exact (worldOK_with_locals s _ ck).2 hW
      obtain ⟨S0, hWT0_ex⟩ := hW.2
      obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
      have hf1_rec_s : f1.toNat ∈ balRecords s :=
        bal_lookup_value_record hroot_nat htw_nz hf0
          (fun hwf_s => hf1_val ((htabWF_with_locals s cmap (s.clock - 1) tw.toNat).2 hwf_s)) hWT0
      have hf1_rec : f1.toNat ∈ balRecords mid := by
        have hbr : balRecords mid = balRecords s := by
          rw [hmid_eq]; rfl
        rw [hbr]; exact hf1_rec_s
      have hmid_x : mid.locals.lookup x = some (.val (.word f1)) := by
        simp [hmid_eq, HolFiniteMapExact.lookup_update, FUPDATE]
      have hmid_other : ∀ y, y ≠ x → mid.locals.lookup y = s.locals.lookup y := by
        intro y hy; simp [hmid_eq, HolFiniteMapExact.lookup_update, FUPDATE, hy, Ne.symm hy]
      have hev_x : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
          (.var .local x) = some (.val (.word f1)) := by
        simp [evalHOLExact, hmid_x]
      obtain ⟨had_nz, had8, had_lo, had_hi, _⟩ :=
        balRecord_slot_load mid f1 0#64 (.var .local x) hW_mid hf1_rec hev_x (by decide) (by decide)
      have hsh_f1 : (shapeEqHOL (shapeOfHOLExact (.val (.word f1) : ValueHOL 64)) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word f1) : ValueHOL 64)) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      subst rb
      dsimp only at hnt hres
      rw [if_pos hsh_f1] at hnt hres
      have heval_eq : evaluateHOLFiniteState s
          (.decCall x .one (ofString "bal_ensure_account") [addrExp] cont) =
          ((evaluateHOLFiniteState mid cont).1,
            { (evaluateHOLFiniteState mid cont).2 with
              locals := HolFiniteMapExact.resVarEq
                (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) }) := by
        rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]; dsimp only
        rw [hlk]; dsimp only; rw [if_neg hcz, hbody_out]; dsimp only
        rw [if_pos hsh_f1]
      refine ⟨f1, mid, had_nz, had8, had_lo, had_hi, hws_total, hW_mid, hf1_rec,
        fun off hoff8 hoff_hi =>
          (balRecord_slot_load mid f1 off (.var .local x) hW_mid hf1_rec hev_x hoff8 hoff_hi).2.2.2.2,
        hmid_x, hmid_other, hnt, hres, by rw [heval_eq], by rw [heval_eq]⟩

private theorem shapeOne_eq_word {v : ValueHOL 64}
    (h : shapeEqHOL .one (shapeOfHOLExact v) = true) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  rcases v with ⟨⟨w⟩⟩ | _ | _
  · exact ⟨w, rfl⟩
  · simp [shapeOfHOLExact, shapeEqHOL] at h
  · simp [shapeOfHOLExact, shapeEqHOL] at h

private theorem ite_some_eq_some {α : Type} {P : Prop} [Decidable P] {a b : α}
    (h : (if P then some a else none) = some b) : P ∧ a = b := by
  by_cases hp : P
  · rw [if_pos hp] at h; exact ⟨hp, Option.some.inj h⟩
  · rw [if_neg hp] at h; cases h

private theorem shapeComb4_eq_words {v : ValueHOL 64}
    (h : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v) = true) :
    ∃ w0 w1 w2 w3 : BitVec 64,
      v = .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)] := by
  cases v with
  | val _ => simp [shapeOfHOLExact, shapeEqHOL] at h
  | nStruct _ _ => simp [shapeOfHOLExact, shapeEqHOL] at h
  | rStruct fields =>
    cases fields with
    | nil => simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
    | cons v0 tail =>
      cases tail with
      | nil => simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
      | cons v1 tail =>
        cases tail with
        | nil => simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
        | cons v2 tail =>
          cases tail with
          | nil => simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
          | cons v3 tail =>
            cases tail with
            | cons _ _ => simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
            | nil =>
              simp only [shapeOfHOLExact, List.map_cons, List.map_nil,
                shapeEqHOL, shapeEqHOL.shapeEqListHOL, Bool.and_eq_true, and_true] at h
              obtain ⟨w0, rfl⟩ := shapeOne_eq_word h.1
              obtain ⟨w1, rfl⟩ := shapeOne_eq_word h.2.1
              obtain ⟨w2, rfl⟩ := shapeOne_eq_word h.2.2.1
              obtain ⟨w3, rfl⟩ := shapeOne_eq_word h.2.2.2
              exact ⟨w0, w1, w2, w3, rfl⟩


private theorem lookupCode_three_word_comb4
    {codeLookup : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    {fname p1 p2 p3 p4 : MlS} {body : ProgHOL 64} {rs : ShapeHOL}
    {vals : List (ValueHOL 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hne12 : p1 ≠ p2) (hne13 : p1 ≠ p3) (hne14 : p1 ≠ p4)
    (hne23 : p2 ≠ p3) (hne24 : p2 ≠ p4) (hne34 : p3 ≠ p4)
    (hlook : codeLookup fname =
      some ([(p1, .one), (p2, .one), (p3, .one), (p4, .comb [.one, .one, .one, .one])], body, rs))
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite codeLookup fname vals =
      some (body, L, rs)) :
    ∃ (w1 w2 w3 nv0 nv1 nv2 nv3 : BitVec 64),
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) ∧
      L.lookup p3 = some (.val (.word w3)) ∧
      L.lookup p4 = some (.rStruct [.val (.word nv0), .val (.word nv1), .val (.word nv2), .val (.word nv3)]) := by
  have hx := lookupCodeHOLFinite_eq_some codeLookup fname vals body L rs hl
  unfold lookupCodeHOLExact at hx
  rw [hlook] at hx; dsimp only at hx
  obtain ⟨⟨_, hlen, hall⟩, heq⟩ := ite_some_eq_some hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | _⟩⟩⟩⟩
  · cases hlen
  · cases hlen
  · cases hlen
  · cases hlen
  · simp only [List.zip, List.zipWith, List.all, Bool.and_eq_true, Bool.and_true] at hall
    obtain ⟨w1, rfl⟩ := shapeOne_eq_word hall.1
    obtain ⟨w2, rfl⟩ := shapeOne_eq_word hall.2.1
    obtain ⟨w3, rfl⟩ := shapeOne_eq_word hall.2.2.1
    obtain ⟨nv0, nv1, nv2, nv3, rfl⟩ := shapeComb4_eq_words hall.2.2.2
    have hL_eq : (List.foldl
        (fun map (entry : MlS × ValueHOL 64) current =>
          if current = entry.1 then some entry.2 else map current)
        (fun _ => none)
        [(p1, .val (.word w1)), (p2, .val (.word w2)), (p3, .val (.word w3)),
         (p4, .rStruct [.val (.word nv0), .val (.word nv1), .val (.word nv2), .val (.word nv3)])]) = L.lookup :=
      (Prod.mk.inj (Prod.mk.inj heq).2).1
    dsimp only [List.foldl] at hL_eq
    refine ⟨w1, w2, w3, nv0, nv1, nv2, nv3, ?_, ?_, ?_, ?_⟩
    · have := congrFun hL_eq p1
      rw [← this, if_neg hne14, if_neg hne13, if_neg hne12, if_pos rfl]
    · have := congrFun hL_eq p2
      rw [← this, if_neg hne24, if_neg hne23, if_pos rfl]
    · have := congrFun hL_eq p3
      rw [← this, if_neg hne34, if_pos rfl]
    · have := congrFun hL_eq p4
      rw [← this, if_pos rfl]
  · cases hlen

private def addStorageWriteTailProg : ProgHOL 64 :=
  .seq
    (.store (.op .add [.var .local (ofString "e"), .const 8#64]) (.var .local (ofString "new_value")))
    (.return (.const 0#64))

private theorem add_storage_write_tail_worldStep {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (lw ew nv0 nv1 nv2 nv3 : BitVec 64)
    (hW : WorldOK s)
    (hlw_nz : lw ≠ 0)
    (horig : ∀ S Nd, WorldTypedWith s S Nd → LstOK s lw.toNat ∧ BalListOrigin s lw.toNat 40)
    (hew8 : ew.toNat % 8 = 0)
    (hew_sb : sourceBase ≤ ew.toNat)
    (hew_he : ew.toNat + 40 ≤ heapEnd)
    (hew_lo : memW s lw.toNat ≤ ew.toNat)
    (hew_hi : ew.toNat + 40 ≤ memW s lw.toNat + 40 * memW s (lw.toNat + 16))
    (hs_e : s.locals.lookup (ofString "e") = some (.val (.word ew)))
    (hs_nv : s.locals.lookup (ofString "new_value") =
      some (.rStruct [.val (.word nv0), .val (.word nv1), .val (.word nv2), .val (.word nv3)])) :
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s
      (evaluateHOLFiniteState s addStorageWriteTailProg).1
      (evaluateHOLFiniteState s addStorageWriteTailProg).2 := by
  have hhe : heapEnd ≤ 2 ^ 64 := by decide
  have he8_toNat : (ew + 8#64).toNat = ew.toNat + 8 := by
    rw [BitVec.toNat_add]
    change (ew.toNat + 8) % 2 ^ 64 = ew.toNat + 8
    exact Nat.mod_eq_of_lt (by omega)
  have he16_toNat : (ew + 8#64 + 8#64).toNat = ew.toNat + 16 := by
    rw [BitVec.toNat_add, he8_toNat]
    change (ew.toNat + 8 + 8) % 2 ^ 64 = ew.toNat + 16
    exact Nat.mod_eq_of_lt (by omega)
  have he24_toNat : (ew + 8#64 + 8#64 + 8#64).toNat = ew.toNat + 24 := by
    rw [BitVec.toNat_add, he16_toNat]
    change (ew.toNat + 16 + 8) % 2 ^ 64 = ew.toNat + 24
    exact Nat.mod_eq_of_lt (by omega)
  have he32_toNat : (ew + 8#64 + 8#64 + 8#64 + 8#64).toNat = ew.toNat + 32 := by
    rw [BitVec.toNat_add, he24_toNat]
    change (ew.toNat + 24 + 8) % 2 ^ 64 = ew.toNat + 32
    exact Nat.mod_eq_of_lt (by omega)
  have hbw : (panBytesInWord 64 : BitVec 64) = 8#64 := by decide
  have hdom8 : s.memaddrs (ew + 8#64) := by
    rw [hW.1.1.memaddrs, Wave8Contracts.M08.ordinaryDomain_iff, he8_toNat]
    exact ⟨by omega, by omega, by omega⟩
  have hdom16 : s.memaddrs (ew + 8#64 + panBytesInWord 64) := by
    rw [hbw, hW.1.1.memaddrs, Wave8Contracts.M08.ordinaryDomain_iff, he16_toNat]
    exact ⟨by omega, by omega, by omega⟩
  have hdom24 : s.memaddrs (ew + 8#64 + panBytesInWord 64 + panBytesInWord 64) := by
    rw [hbw, hW.1.1.memaddrs, Wave8Contracts.M08.ordinaryDomain_iff, he24_toNat]
    exact ⟨by omega, by omega, by omega⟩
  have hdom32 : s.memaddrs (ew + 8#64 + panBytesInWord 64 + panBytesInWord 64 + panBytesInWord 64) := by
    rw [hbw, hW.1.1.memaddrs, Wave8Contracts.M08.ordinaryDomain_iff, he32_toNat]
    exact ⟨by omega, by omega, by omega⟩
  have hz8 : (8#64 : BitVec 64) + 0 = 8#64 := BitVec.add_zero _
  have hev_dst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "e"), .const 8#64]) = some (.val (.word (ew + 8#64))) := by
    simp [evalHOLExact, evalListHOLExact, hs_e, valueIsWord, valueWord, wordOpHOL, wordOp, hz8]
  have hev_val : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString "new_value")) =
      some (.rStruct [.val (.word nv0), .val (.word nv1), .val (.word nv2), .val (.word nv3)]) := by
    simp [evalHOLExact, hs_nv]
  let m0 := s.memory
  let m1 := fun a => if a = ew + 8#64 then HolWordLab.word nv0 else m0 a
  let m2 := fun a => if a = ew + 8#64 + panBytesInWord 64 then HolWordLab.word nv1 else m1 a
  let m3 := fun a => if a = ew + 8#64 + panBytesInWord 64 + panBytesInWord 64 then HolWordLab.word nv2 else m2 a
  let m4 := fun a => if a = ew + 8#64 + panBytesInWord 64 + panBytesInWord 64 + panBytesInWord 64 then HolWordLab.word nv3 else m3 a
  let st1 : PanSemStateFiniteExact 64 F := { s with memory := m4 }
  have hst1 : evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "e"), .const 8#64]) (.var .local (ofString "new_value"))) =
      (none, st1) := by
    rw [evaluateHOLFiniteState_store, hev_dst, hev_val]
    simp only [flattenHOL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.singleton_append,
      panMemStoresHOL, panMemStoreHOL, hdom8, hdom16, hdom24, hdom32, ↓reduceIte]
    rfl
  have hret : evaluateHOLFiniteState st1 (.return (.const 0#64)) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite st1) := by
    rw [evaluateHOLFiniteState_return]
    simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos (by decide)]
  have htot : evaluateHOLFiniteState s addStorageWriteTailProg =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite st1) := by
    dsimp only [addStorageWriteTailProg]
    rw [evaluateHOLFiniteState_seq_line780, hst1]; dsimp only
    exact hret
  let Rl : List Ivl := [(memW s lw.toNat, 40 * memW s (lw.toNat + 16))]
  have hbre1 : ByteRegionEffect s st1 Rl := by
    refine (bre_of_store_multi hW.1.1.memaddrs (nw := 4) (by omega) hst1
      (fun v hv => by
        rw [hev_val] at hv; injection hv with hv'; subst hv'; simp [flattenHOL])
      (fun addr hdst _ => ?_)).1
    rw [hev_dst] at hdst; injection hdst with hd; injection hd with hd'; injection hd' with hd''; subst hd''
    refine ⟨by rw [he8_toNat]; omega, (memW s lw.toNat, 40 * memW s (lw.toNat + 16)),
      List.mem_singleton.2 rfl, by rw [he8_toNat]; omega, by dsimp only; rw [he8_toNat]; omega⟩
  have hbre_emp : ByteRegionEffect s (emptyLocalsHOLFinite st1) Rl :=
    hbre1.with_locals_clock (emptyLocalsHOLFinite st1).locals st1.clock
  have hlw_nz_nat : lw.toNat ≠ 0 := fun h => hlw_nz (BitVec.eq_of_toNat_eq (by simpa using h))
  rw [htot]; dsimp only
  exact (bal_list_store_arr_worldStep
    (r := some (.returned (.val (.word 0#64))))
    hW hlw_nz_nat (Or.inr (Or.inr rfl)) horig hbre_emp).1

private theorem bal_stor_lst_new_htab_set_core {F : Type}
    {s m1 post : PanSemStateFiniteExact 64 F}
    {tw lw : BitVec 64} {S Nd : List Nat}
    (hAs : ArenaReady s) (hA1 : ArenaReady m1) (hAp : ArenaReady post)
    (hWT : WorldTypedWith s S Nd)
    (htw_nz : tw.toNat ≠ 0)
    (htw_bal : ∃ ad0 ∈ balRecords s, memW s ad0 = tw.toNat)
    (hgk : GlobalsKept ["heap_ptr"] s post)
    (hsp_post : globN post "scratch_ptr" = globN s "scratch_ptr")
    (hhp_01 : globN s "heap_ptr" ≤ globN m1 "heap_ptr")
    (hhp_1p : globN m1 "heap_ptr" ≤ globN post "heap_ptr")
    (hbe_0p : post.be = s.be)
    (hlw_eq : lw.toNat = globN s "heap_ptr")
    (hlw8 : lw.toNat % 8 = 0)
    (hlw_nz : lw.toNat ≠ 0)
    (hhp_m1 : globN m1 "heap_ptr" = lw.toNat + 24 + 80)
    (hfr_0p : FrameOutside s post
      ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat)
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hfp_tw_1 : htabFootprint m1 tw.toNat = htabFootprint s tw.toNat)
    (hhdr0_tw_p : hdr post tw.toNat 0 = hdr s tw.toNat 0)
    (hwf_tw_p : HtabWF post tw.toNat)
    (hfp_tw_p : ∀ i ∈ htabFootprint post tw.toNat, Allocated post i ∧
      ((∃ j ∈ htabFootprint m1 tw.toNat, Inside i j.1 (j.1 + j.2)) ∨
        Inside i (globN m1 "heap_ptr") (globN m1 "heap_ptr" + (globN post "heap_ptr" - globN m1 "heap_ptr"))))
    (hvalues_0p : HtabSetValuesPost s post tw.toNat lw.toNat)
    (hlst_p : LstOK post lw.toNat)
    (hobjs_p : lstObjects post lw.toNat 40 = [(lw.toNat, 24), (lw.toNat + 24, 80)])
    (hm0_8_16 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16) :
    ∃ S' Nd',
      (∀ t ∈ S, t ∈ S') ∧
      WorldTypedWith post S' Nd' ∧
      OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd') ∧
      FrameOutside s post (worldOwned s S Nd ++ ([] : List Ivl) ++ [freeGap s]) (heapFree s) := by
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  obtain ⟨ad0, had0, had0_eq⟩ := htw_bal
  have had0_nz : memW s ad0 ≠ 0 := by rw [had0_eq]; exact htw_nz
  obtain ⟨htw_S, hno_bs32, hno_ts32, hno_ba, hno_ws32⟩ := by
    have hd := bal_stor_slot_distinct hT had0 had0_nz
    change memW s ad0 ∈ S ∧ _ at hd
    rw [had0_eq] at hd
    exact hd
  have hsp8 : (globN s "scratch_ptr") % 8 = 0 := hAs.2.2.2.2.2.2.2.2.1
  have hhp_0p : globN s "heap_ptr" ≤ globN post "heap_ptr" := le_trans hhp_01 hhp_1p
  have hag : AllocatorGrows s post := ⟨hhp_0p, by omega⟩
  have hgs : Wave8Contracts.M08.WorldGlobalsSame s post :=
    Wave8Contracts.M08.worldGlobalsSame_of_kept hgk (fun name h => Or.inl (by simpa using h))
  have hWF_tw : HtabWF s tw.toNat := (hT.2.1 _ htw_S).1
  have hk_al_0p : ∀ j ∈ ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat), j.1 % 8 = 0 := by
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj_fp
    · exact hsp8
    · exact (hWF_tw.1 j hj_fp).2.1
  let fresh_lw : List Ivl := [(lw.toNat, 24), (lw.toNat + 24, 80)]
  have hsb_le_lw : sourceBase ≤ lw.toNat := by have := hAs.2.1; omega
  have hfresh_lw_props : ∀ i ∈ fresh_lw,
      Inside i (globN s "heap_ptr") (globN m1 "heap_ptr") ∧ WordsOK post i := by
    intro i hi
    simp only [fresh_lw, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    all_goals
      exact ⟨⟨by dsimp; omega, by dsimp; omega⟩,
        Wave8Contracts.M08.wordsOK_fresh_heap hAp.1 (by omega) (by decide) (by omega)
          (by have := hA1.2.2.1; omega)⟩
  have hpw_fresh_lw : fresh_lw.Pairwise Disj := by
    simp only [fresh_lw, List.pairwise_cons, List.Pairwise.nil, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq, and_true, imp_false, not_true_eq_false]
    exact ⟨Or.inr (Or.inr (Or.inl (by omega))), fun _ h => False.elim h⟩
  have hu_fix : ∀ i ∈ fixedObjects s, M08IvlUnhit s post i := by
    intro i hi
    apply m08_ivlUnhit_of_frameOutside_add hfr_0p hk_al_0p hAs.2.2.2.2.2.2.1
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj_fp
      · exact Or.inr (Or.inl rfl)
      · exact disj_flip (((hT.2.1 _ htw_S).2 j hj_fp).2 i hi)
    · rcases hF.1 i hi with hz | ⟨hal, _⟩
      · exact disj_fresh_of_zero_or_allocated_add hAs.2 hAp.2 hhp_0p (Or.inl hz)
      · exact disj_fresh_of_zero_or_allocated_add hAs.2 hAp.2 hhp_0p (Or.inr hal)
  have hu_ws : globN s "ws" ≠ 0 → M08IvlUnhit s post (globN s "ws", 40) := fun h => by
    have hm := Wave8Contracts.M08.typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by decide)
    exact hu_fix _ (by simpa [h] using hm)
  have hu_bs : globN s "bs" ≠ 0 → M08IvlUnhit s post (globN s "bs", 80) := fun h => by
    have hm := Wave8Contracts.M08.typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by decide)
    exact hu_fix _ (by simpa [h] using hm)
  have hu_ts : globN s "ts" ≠ 0 → M08IvlUnhit s post (globN s "ts", 72) := fun h => by
    have hm := Wave8Contracts.M08.typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by decide)
    exact hu_fix _ (by simpa [h] using hm)
  have hu_bo : globN s "bo" ≠ 0 → M08IvlUnhit s post (globN s "bo", 88) := fun h => by
    have hm := Wave8Contracts.M08.typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
    exact hu_fix _ (by simpa [h] using hm)
  have hu_jr : globN s "journal_cap" ≠ 0 → M08IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := fun h => by
    have hm : (globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
      simp [h]
    exact hu_fix _ hm
  have hu_other : ∀ u ∈ S, u ≠ tw.toNat → ∀ i ∈ htabFootprint s u, M08IvlUnhit s post i := by
    intro u hu hne i hi
    apply m08_ivlUnhit_of_frameOutside_add hfr_0p hk_al_0p hAs.2.2.2.2.2.2.1
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj_fp
      · exact Or.inr (Or.inl rfl)
      · exact hT.2.2.1 u hu tw.toNat htw_S hne i hi j hj_fp
    · exact disj_fresh_of_zero_or_allocated_add hAs.2 hAp.2 hhp_0p (Or.inr ((hT.2.1 u hu).2 i hi).1)
  have hother_fp : ∀ u ∈ S, u ≠ tw.toNat →
      (∀ k, k < 11 → hdr post u k = hdr s u k) ∧ htabFootprint post u = htabFootprint s u := by
    intro u hu hne
    have hwf := (hT.2.1 u hu).1
    have ht_fp : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
    have hu8 : u % 8 = 0 := (hwf.1 _ ht_fp).2.1
    have h264' : heapEnd ≤ 2 ^ 64 := by decide
    have hhi : u + 88 ≤ 2 ^ 64 := by have := (hwf.1 _ ht_fp).1.2; dsimp at this; omega
    exact Wave8Contracts.M08.htabFootprint_eq_of_hdr_unhit hu8 hhi (hu_other u hu hne _ ht_fp)
  have hbo_g : globN post "bo" = globN s "bo" := hgs.1 ("bo", 88) (by simp [globalBuffers])
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" :=
    hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  have hbo_words : globN s "bo" ≠ 0 → ∀ k ∈ ([24, 32, 40, 56, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := fun hnz k hk => by
    have hk_in : k % 8 = 0 ∧ k + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    simpa [hbo_g] using Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "bo" 88 (by decide) hbo_g hnz (hu_bo hnz) hk_in.1 hk_in.2
  have hbo_part := Wave8Contracts.M08.blockOutObjects_eq_of_bo_unhit hAs.2 hF hbo_g hT.2.2.2.2.2.2.2.2.2.2.1
    (fun h => hbo_words h 24 (by simp))
    (fun h => hbo_words h 32 (by simp))
    (fun h => hbo_words h 40 (by simp))
    (fun h => hbo_words h 56 (by simp))
    (fun h => hbo_words h 72 (by simp))
    (fun h => hbo_words h 80 (by simp))
    (fun _ _ => by simp [hm0_8_16.1, hm0_8_16.2.2])
    (fun _ _ => by simp [hm0_8_16.1, hm0_8_16.2.2])
    (fun h h40 => hu_fix (memW s (globN s "bo" + 40), 24) (by
      unfold fixedObjects; apply List.mem_append_left; apply List.mem_append_right
      simp [blockOutObjects, h, h40]))
    (fun h h72 => hu_fix (memW s (globN s "bo" + 72), 24) (by
      unfold fixedObjects; apply List.mem_append_left; apply List.mem_append_right
      simp [blockOutObjects, h, h72]))
  have hrecs_bal : balRecords post = balRecords s :=
    Wave8Contracts.M08.balRecords_eq_of_unhit hT hba_g (fun hnz => by
      rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · exact hu_other _ hm hno_ba)
  have hmem_fix_of_bal : ∀ i ∈ balObjects s, i ∈ fixedObjects s := fun i hi => by
    unfold fixedObjects; exact List.mem_append_right _ hi
  have hlst_eq_bal : ∀ l, (l, 24) ∈ balObjects s →
      memW post l = memW s l ∧ memW post (l + 8) = memW s (l + 8) ∧
      memW post (l + 16) = memW s (l + 16) := by
    intro l hl_bal
    rcases hF.1 _ (hmem_fix_of_bal _ hl_bal) with h0 | ⟨hal_l, hw_l⟩
    · simp at h0
    have hhi_l := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_l).2
    have hl8 : l % 8 = 0 := hw_l.1
    have hul := hu_fix _ (hmem_fix_of_bal _ hl_bal)
    have e0 : memW post l = memW s l := by
      simpa using Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
    have e8 : memW post (l + 8) = memW s (l + 8) :=
      Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
    have e16 : memW post (l + 16) = memW s (l + 16) :=
      Wave8Contracts.M08.memW_eq_of_ivlUnhit hul (by omega) hhi_l ⟨by omega, by omega⟩
    exact ⟨e0, e8, e16⟩
  have hlw_not_old_stor : ∀ ad ∈ balRecords s, lw.toNat ∉ htabValues s (memW s ad) := by
    intro ad had hlw_in
    have hlw_bal : (lw.toNat, 24) ∈ balObjects s := by
      unfold balObjects
      refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
      apply List.mem_cons_of_mem
      apply List.mem_append_right
      exact List.mem_flatMap.2 ⟨lw.toNat, hlw_in, by simp [lstObjects, hlw_nz]⟩
    rcases hF.1 _ (hmem_fix_of_bal _ hlw_bal) with h0 | ⟨hal_lw, _⟩
    · simp at h0
    · have hd := Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_lw
        (f := (lw.toNat, 24)) ⟨by omega, by omega⟩
      rcases hd with h | h | h | h <;> (try dsimp at h) <;> omega
  have had_props : ∀ ad ∈ balRecords s,
      memW post ad = memW s ad ∧
      memW post (ad + 8) = memW s (ad + 8) ∧
      (ad ≠ ad0 →
        (ad, 40) :: lstObjects post (memW post (ad + 16)) 40 ++
          lstObjects post (memW post (ad + 24)) 16 ++
          lstObjects post (memW post (ad + 32)) 24 ++
          (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) =
        (ad, 40) :: lstObjects s (memW s (ad + 16)) 40 ++
          lstObjects s (memW s (ad + 24)) 16 ++
          lstObjects s (memW s (ad + 32)) 24 ++
          (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40)) ∧
      ((ad, 40) :: lstObjects post (memW post (ad + 16)) 40 ++
        lstObjects post (memW post (ad + 24)) 16 ++
        lstObjects post (memW post (ad + 32)) 24 =
       (ad, 40) :: lstObjects s (memW s (ad + 16)) 40 ++
        lstObjects s (memW s (ad + 24)) 16 ++
        lstObjects s (memW s (ad + 32)) 24) ∧
      (∀ l ∈ htabValues s (memW s ad),
        lstObjects post l 40 = lstObjects s l 40 ∧ LstOK post l) ∧
      (∀ k ∈ ([16, 24, 32] : List Nat), LstOK post (memW post (ad + k))) ∧
      (∀ l ∈ htabValues post (memW post ad), LstOK post l) := by
    intro ad had
    have had_bal : (ad, 40) ∈ balObjects s :=
      List.mem_flatMap.2 ⟨ad, had, by simp⟩
    rcases hF.1 _ (hmem_fix_of_bal _ had_bal) with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_ad).2
    have had8 : ad % 8 = 0 := hw_ad.1
    have hul_ad := hu_fix _ (hmem_fix_of_bal _ had_bal)
    have hoff_eq : ∀ off ∈ ([0, 8, 16, 24, 32] : List Nat), memW post (ad + off) = memW s (ad + off) := by
      intro off hoff
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
        exact Wave8Contracts.M08.memW_eq_of_ivlUnhit hul_ad (by omega) hhi_ad ⟨by omega, by omega⟩
    have e0 := hoff_eq 0 (by simp); simp only [Nat.add_zero] at e0
    have e8 := hoff_eq 8 (by simp)
    have e16 := hoff_eq 16 (by simp)
    have e24 := hoff_eq 24 (by simp)
    have e32 := hoff_eq 32 (by simp)
    have had_T := hT.2.2.2.2.2.2.2.2.2.1 ad had
    have hklst : ∀ k ∈ ([16, 24, 32] : List Nat), ∀ esz,
        lstObjects post (memW s (ad + k)) esz = lstObjects s (memW s (ad + k)) esz ∧
        LstOK post (memW s (ad + k)) := by
      intro k hk esz
      by_cases hk0 : memW s (ad + k) = 0
      · refine ⟨by simp [lstObjects, hk0], ?_⟩
        have hok := had_T.2.2.1 k hk
        unfold LstOK at hok ⊢; rw [hk0] at hok ⊢; rw [hm0_8_16.2.1, hm0_8_16.2.2]; exact hok
      · have hmem_b : (memW s (ad + k), 24) ∈ balObjects s := by
          unfold balObjects
          refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl <;> simp [lstObjects, hk0]
        obtain ⟨l0, l8, l16⟩ := hlst_eq_bal _ hmem_b
        refine ⟨by simp [lstObjects, hk0, l0, l16], ?_⟩
        have hok := had_T.2.2.1 k hk
        unfold LstOK at hok ⊢; rw [l8, l16]; exact hok
    have hllst : ∀ l ∈ htabValues s (memW s ad),
        lstObjects post l 40 = lstObjects s l 40 ∧ LstOK post l := by
      intro l hl
      by_cases hl0 : l = 0
      · subst hl0
        refine ⟨by simp [lstObjects], ?_⟩
        have hok := had_T.2.2.2 0 hl
        unfold LstOK at hok ⊢; rw [hm0_8_16.2.1, hm0_8_16.2.2]; exact hok
      · have hmem_b : (l, 24) ∈ balObjects s := by
          unfold balObjects
          refine List.mem_flatMap.2 ⟨ad, had, ?_⟩
          apply List.mem_cons_of_mem; apply List.mem_append_right
          exact List.mem_flatMap.2 ⟨l, hl, by simp [lstObjects, hl0]⟩
        obtain ⟨l0, l8, l16⟩ := hlst_eq_bal l hmem_b
        refine ⟨by simp [lstObjects, hl0, l0, l16], ?_⟩
        have hok := had_T.2.2.2 l hl
        unfold LstOK at hok ⊢; rw [l8, l16]; exact hok
    have hhead_eq :
        (ad, 40) :: lstObjects post (memW post (ad + 16)) 40 ++
          lstObjects post (memW post (ad + 24)) 16 ++
          lstObjects post (memW post (ad + 32)) 24 =
        (ad, 40) :: lstObjects s (memW s (ad + 16)) 40 ++
          lstObjects s (memW s (ad + 24)) 16 ++
          lstObjects s (memW s (ad + 32)) 24 := by
      rw [e16, e24, e32, (hklst 16 (by simp) 40).1, (hklst 24 (by simp) 16).1, (hklst 32 (by simp) 24).1]
    refine ⟨e0, e8, fun hne_ad => ?_, hhead_eq, hllst, ?_, ?_⟩
    · have hne_tw : memW s ad ≠ tw.toNat := by
        intro heq_t
        exact hne_ad (bal_stor_slot_unique_ad hT had0 had had0_nz (heq_t.trans had0_eq.symm))
      have hveq := Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ had_T.1).1 (hu_other _ had_T.1 hne_tw)
      have htail : (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40) =
          (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40) := by
        rw [e0, hveq]
        exact List.flatMap_congr (fun l hl => (hllst l hl).1)
      rw [htail]
      exact congrArg (· ++ (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40)) hhead_eq
    · intro k hk
      have hk_in : k ∈ ([0, 8, 16, 24, 32] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        rcases hk with rfl | rfl | rfl <;> simp
      rw [hoff_eq k hk_in]
      exact (hklst k hk 40).2
    · intro l hl
      by_cases had_eq : ad = ad0
      · subst had_eq
        rw [e0, had0_eq] at hl
        rcases htabSetValuesPost_mem hvalues_0p hl with hl_old | rfl
        · rw [← had0_eq] at hl_old
          exact (hllst l hl_old).2
        · exact hlst_p
      · have hne_tw : memW s ad ≠ tw.toNat := by
          intro heq_t
          exact had_eq (bal_stor_slot_unique_ad hT had0 had had0_nz (heq_t.trans had0_eq.symm))
        have hveq := Wave8Contracts.M08.htabValues_eq_of_unhit (hT.2.1 _ had_T.1).1 (hu_other _ had_T.1 hne_tw)
        rw [e0, hveq] at hl
        exact (hllst l hl).2
  have hprefix_eq :
      (globalBuffers.map fun gn => (globN post gn.1, if globN post gn.1 = 0 then 0 else gn.2)) ++
        [(if globN post "journal_cap" = 0 then 0 else globN post "journal", 32 * globN post "journal_cap")] ++
        blockOutObjects post =
      (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++
        [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++
        blockOutObjects s := by
    have hgb : (globalBuffers.map fun gn => (globN post gn.1, if globN post gn.1 = 0 then 0 else gn.2)) =
        (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
      apply List.map_congr_left; intro gn hgn; rw [hgs.1 gn hgn]
    rw [hgb, hgs.2.2.1, hgs.2.2.2.1, hbo_part.1]
  have hbal_class_ad : ∀ ad ∈ balRecords s,
      ∀ o ∈ (ad, 40) :: lstObjects post (memW post (ad + 16)) 40 ++
        lstObjects post (memW post (ad + 24)) 16 ++
        lstObjects post (memW post (ad + 32)) 24 ++
        (htabValues post (memW post ad)).flatMap (fun l => lstObjects post l 40),
      (o ∈ (ad, 40) :: lstObjects s (memW s (ad + 16)) 40 ++
        lstObjects s (memW s (ad + 24)) 16 ++
        lstObjects s (memW s (ad + 32)) 24 ++
        (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40)) ∨ o ∈ fresh_lw := by
    intro ad had o ho
    by_cases had_eq : ad = ad0
    · subst had_eq
      have hp0 := had_props ad had
      have hhead := hp0.2.2.2.1
      rcases List.mem_append.1 ho with ho_head | ho_tail
      · rw [hhead] at ho_head
        exact Or.inl (List.mem_append_left _ ho_head)
      · rw [hp0.1, had0_eq] at ho_tail
        obtain ⟨l, hl, ho_l⟩ := List.mem_flatMap.1 ho_tail
        rcases htabSetValuesPost_mem hvalues_0p hl with hl_old | rfl
        · rw [← had0_eq] at hl_old
          rw [(hp0.2.2.2.2.1 l hl_old).1] at ho_l
          exact Or.inl (List.mem_append_right _ (List.mem_flatMap.2 ⟨l, hl_old, ho_l⟩))
        · rw [hobjs_p] at ho_l
          exact Or.inr ho_l
    · rw [(had_props ad had).2.2.1 had_eq] at ho
      exact Or.inl ho
  have hbal_class : ∀ o ∈ balObjects post, o ∈ balObjects s ∨ o ∈ fresh_lw := by
    intro o ho
    unfold balObjects at ho
    rw [hrecs_bal] at ho
    obtain ⟨ad, had, ho_ad⟩ := List.mem_flatMap.1 ho
    rcases hbal_class_ad ad had o ho_ad with ho_old | ho_fr
    · left; unfold balObjects; exact List.mem_flatMap.2 ⟨ad, had, ho_old⟩
    · exact Or.inr ho_fr
  have hfix_class : ∀ o ∈ fixedObjects post, o ∈ fixedObjects s ∨ o ∈ fresh_lw := by
    intro o ho
    unfold fixedObjects at ho
    rw [hprefix_eq] at ho
    rcases List.mem_append.1 ho with hpre | hbal
    · left; unfold fixedObjects; exact List.mem_append_left _ hpre
    · rcases hbal_class o hbal with hb_s | hfr
      · left; unfold fixedObjects; exact List.mem_append_right _ hb_s
      · exact Or.inr hfr
  obtain ⟨hpw_pre, hpw_bal_s, hcross_pre_bal⟩ := by
    have h := hF.2; unfold fixedObjects at h; exact List.pairwise_append.1 h
  have hpw_bal_post : (balObjects post).Pairwise Disj := by
    unfold balObjects at hpw_bal_s ⊢
    rw [hrecs_bal]
    rw [List.pairwise_flatMap] at hpw_bal_s ⊢
    refine ⟨fun ad had => ?_, ?_⟩
    · by_cases had_eq : ad = ad0
      · subst had_eq
        have hp_ad0 := hpw_bal_s.1 ad had
        have hp0 := had_props ad had
        have hhead := hp0.2.2.2.1
        rw [hhead]
        obtain ⟨hp_head, hp_tail_s, hcross_ht⟩ := List.pairwise_append.1 hp_ad0
        refine List.pairwise_append.2 ⟨hp_head, ?_, ?_⟩
        · rw [hp0.1, had0_eq]
          let f_stor : Nat → List Ivl := fun l =>
            if l = lw.toNat then fresh_lw else lstObjects s l 40
          have hpost_f : ∀ l ∈ htabValues post tw.toNat, lstObjects post l 40 = f_stor l := by
            intro l hl
            rcases htabSetValuesPost_mem hvalues_0p hl with hl_old | rfl
            · rw [← had0_eq] at hl_old
              have hne : l ≠ lw.toNat := fun heq => hlw_not_old_stor ad had (heq ▸ hl_old)
              simp only [f_stor, if_neg hne]
              exact (hp0.2.2.2.2.1 l hl_old).1
            · simp only [f_stor, if_true]
              exact hobjs_p
          have hold_f : (htabValues s tw.toNat).flatMap f_stor =
              (htabValues s (memW s ad)).flatMap (fun l => lstObjects s l 40) := by
            rw [← had0_eq]
            apply List.flatMap_congr
            intro l hl
            have hne : l ≠ lw.toNat := fun heq => hlw_not_old_stor ad had (heq ▸ hl)
            simp [f_stor, hne]
          rw [List.flatMap_congr hpost_f]
          apply pairwise_htabSetValuesPost_flatMap f_stor hvalues_0p
          · rw [hold_f]; exact hp_tail_s
          · simp only [f_stor, if_true]; exact hpw_fresh_lw
          · intro a ha b hb
            rw [hold_f] at ha
            simp only [f_stor, if_true] at hb
            have ha_fix : a ∈ fixedObjects s := by
              unfold fixedObjects; apply List.mem_append_right; unfold balObjects
              exact List.mem_flatMap.2 ⟨ad, had, List.mem_append_right _ ha⟩
            rcases hF.1 a ha_fix with hz | ⟨hal_a, _⟩
            · exact Or.inl hz
            · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_a
                ⟨(hfresh_lw_props b hb).1.1, le_trans (hfresh_lw_props b hb).1.2 hhp_1p⟩)
          · intro a ha b hb
            simp only [f_stor, if_true] at ha
            rw [hold_f] at hb
            have hb_fix : b ∈ fixedObjects s := by
              unfold fixedObjects; apply List.mem_append_right; unfold balObjects
              exact List.mem_flatMap.2 ⟨ad, had, List.mem_append_right _ hb⟩
            rcases hF.1 b hb_fix with hz | ⟨hal_b, _⟩
            · exact Or.inr (Or.inl hz)
            · exact Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_b
                ⟨(hfresh_lw_props a ha).1.1, le_trans (hfresh_lw_props a ha).1.2 hhp_1p⟩
        · intro a ha b hb
          rw [hp0.1, had0_eq] at hb
          obtain ⟨l, hl, hb_l⟩ := List.mem_flatMap.1 hb
          rcases htabSetValuesPost_mem hvalues_0p hl with hl_old | rfl
          · rw [← had0_eq] at hl_old
            rw [(hp0.2.2.2.2.1 l hl_old).1] at hb_l
            exact hcross_ht a ha b (List.mem_flatMap.2 ⟨l, hl_old, hb_l⟩)
          · rw [hobjs_p] at hb_l
            have ha_fix : a ∈ fixedObjects s := by
              unfold fixedObjects; apply List.mem_append_right; unfold balObjects
              exact List.mem_flatMap.2 ⟨ad, had, List.mem_append_left _ ha⟩
            rcases hF.1 a ha_fix with hz | ⟨hal_a, _⟩
            · exact Or.inl hz
            · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_a
                ⟨(hfresh_lw_props b hb_l).1.1, le_trans (hfresh_lw_props b hb_l).1.2 hhp_1p⟩)
      · rw [(had_props ad had).2.2.1 had_eq]
        exact hpw_bal_s.1 ad had
    · rw [List.pairwise_iff_getElem] at *
      intro i1 i2 hi1 hi2 hlt a ha b hb
      have had1 : (balRecords s)[i1] ∈ balRecords s := List.getElem_mem hi1
      have had2 : (balRecords s)[i2] ∈ balRecords s := List.getElem_mem hi2
      rcases hbal_class_ad _ had1 a ha with ha_old | ha_fr
      · rcases hbal_class_ad _ had2 b hb with hb_old | hb_fr
        · exact hpw_bal_s.2 i1 i2 hi1 hi2 hlt a ha_old b hb_old
        · have ha_fix : a ∈ fixedObjects s := by
            unfold fixedObjects; apply List.mem_append_right; unfold balObjects
            exact List.mem_flatMap.2 ⟨_, had1, ha_old⟩
          rcases hF.1 a ha_fix with hz | ⟨hal_a, _⟩
          · exact Or.inl hz
          · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_a
              ⟨(hfresh_lw_props b hb_fr).1.1, le_trans (hfresh_lw_props b hb_fr).1.2 hhp_1p⟩)
      · rcases hbal_class_ad _ had2 b hb with hb_old | hb_fr
        · have hb_fix : b ∈ fixedObjects s := by
            unfold fixedObjects; apply List.mem_append_right; unfold balObjects
            exact List.mem_flatMap.2 ⟨_, had2, hb_old⟩
          rcases hF.1 b hb_fix with hz | ⟨hal_b, _⟩
          · exact Or.inr (Or.inl hz)
          · exact Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_b
              ⟨(hfresh_lw_props a ha_fr).1.1, le_trans (hfresh_lw_props a ha_fr).1.2 hhp_1p⟩
        · -- Cannot both be in ad0 since `(balRecords s)[i1] ≠ (balRecords s)[i2]`!
          have heq1 : (balRecords s)[i1] = ad0 := by
            by_contra hne1
            rw [(had_props _ had1).2.2.1 hne1] at ha
            have ha_fix : a ∈ fixedObjects s := by
              unfold fixedObjects; apply List.mem_append_right; unfold balObjects
              exact List.mem_flatMap.2 ⟨_, had1, ha⟩
            rcases hF.1 a ha_fix with hz | ⟨hal_a, _⟩
            · simp only [fresh_lw, List.mem_cons, List.not_mem_nil, or_false] at ha_fr
              rcases ha_fr with rfl | rfl <;> simp at hz
            · have hd := Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_a
                ⟨(hfresh_lw_props a ha_fr).1.1, le_trans (hfresh_lw_props a ha_fr).1.2 hhp_1p⟩
              simp only [fresh_lw, List.mem_cons, List.not_mem_nil, or_false] at ha_fr
              rcases ha_fr with rfl | rfl <;> (rcases hd with d | d | d | d <;> dsimp at d <;> omega)
          have heq2 : (balRecords s)[i2] = ad0 := by
            by_contra hne2
            rw [(had_props _ had2).2.2.1 hne2] at hb
            have hb_fix : b ∈ fixedObjects s := by
              unfold fixedObjects; apply List.mem_append_right; unfold balObjects
              exact List.mem_flatMap.2 ⟨_, had2, hb⟩
            rcases hF.1 b hb_fix with hz | ⟨hal_b, _⟩
            · simp only [fresh_lw, List.mem_cons, List.not_mem_nil, or_false] at hb_fr
              rcases hb_fr with rfl | rfl <;> simp at hz
            · have hd := Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_b
                ⟨(hfresh_lw_props b hb_fr).1.1, le_trans (hfresh_lw_props b hb_fr).1.2 hhp_1p⟩
              simp only [fresh_lw, List.mem_cons, List.not_mem_nil, or_false] at hb_fr
              rcases hb_fr with rfl | rfl <;> (rcases hd with d | d | d | d <;> dsimp at d <;> omega)
          have hdj_ad := hpw_bal_s.2 i1 i2 hi1 hi2 hlt
            ((balRecords s)[i1], 40) (by simp) ((balRecords s)[i2], 40) (by simp)
          rw [heq1, heq2] at hdj_ad
          rcases hdj_ad with d | d | d | d <;> dsimp at d <;> omega
  have hF_post : FixedTyped post := by
    refine ⟨fun i hi => ?_, ?_⟩
    · rcases hfix_class i hi with hold | hnew
      · rcases hF.1 i hold with hz | ⟨hal, hw⟩
        · exact Or.inl hz
        · exact Or.inr ⟨hag.allocated hal, Wave8Contracts.M08.wordsOK_transfer hAs.1 hAp.1 hw⟩
      · obtain ⟨hin, hw⟩ := hfresh_lw_props i hnew
        exact Or.inr ⟨Or.inl ⟨le_trans hAs.2.1 hin.1, le_trans hin.2 hhp_1p⟩, hw⟩
    · unfold fixedObjects
      rw [hprefix_eq]
      refine List.pairwise_append.2 ⟨hpw_pre, hpw_bal_post, fun a ha b hb => ?_⟩
      rcases hbal_class b hb with hb_s | hb_fr
      · exact hcross_pre_bal a ha b hb_s
      · have ha_fix : a ∈ fixedObjects s := by unfold fixedObjects; exact List.mem_append_left _ ha
        rcases hF.1 a ha_fix with hz | ⟨hal_a, _⟩
        · exact Or.inl hz
        · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_a
            ⟨(hfresh_lw_props b hb_fr).1.1, le_trans (hfresh_lw_props b hb_fr).1.2 hhp_1p⟩)
  obtain ⟨hjr_eq, hJ_post⟩ := Wave8Contracts.M08.journalRoleSlots_eq_of_unhit
    hAs.1 hAp.1 hAs.2 hag (fun _ hx => hx) hJ hF hgs hu_ts hu_jr
  have hws_g : globN post "ws" = globN s "ws" := hgs.1 ("ws", 40) (by simp [globalBuffers])
  have hbs_g : globN post "bs" = globN s "bs" := hgs.1 ("bs", 80) (by simp [globalBuffers])
  have hts_g : globN post "ts" = globN s "ts" := hgs.1 ("ts", 72) (by simp [globalBuffers])
  have hbia_g : globN post "bal_idx_accts" = globN s "bal_idx_accts" :=
    hgs.2.1 "bal_idx_accts" (by simp [globalTableRoots])
  have hbis_g : globN post "bal_idx_stor" = globN s "bal_idx_stor" :=
    hgs.2.1 "bal_idx_stor" (by simp [globalTableRoots])
  have hwrs_eq : worldRoleSlots post = worldRoleSlots s := by
    have hrec_ws : recRoles post "ws" [(16, "ws+16"), (32, "ws+32")] =
        recRoles s "ws" [(16, "ws+16"), (32, "ws+32")] := by
      unfold recRoles
      by_cases h : globN s "ws" = 0
      · simp [hws_g, h]
      · have hw16 := Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ws" 40 (by decide) hws_g h (hu_ws h) (k := 16) (by omega) (by omega)
        have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ws" 40 (by decide) hws_g h (hu_ws h) (k := 32) (by omega) (by omega)
        simp only [hws_g] at hw16 hw32 ⊢; simp [h, hw16, hw32]
    have hrec_bs : recRoles post "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
        (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] =
        recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"),
        (40, "bs+40"), (48, "bs+48"), (72, "bs+72")] := by
      unfold recRoles
      by_cases h : globN s "bs" = 0
      · simp [hbs_g, h]
      · simp only [hbs_g, h, ↓reduceIte]
        apply List.map_congr_left
        intro ⟨k, r0⟩ hkr
        have hk : k % 8 = 0 ∧ k + 8 ≤ 80 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
          rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        have hw := Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "bs" 80 (by decide) hbs_g h (hu_bs h) hk.1 hk.2
        simp only [hbs_g] at hw; simp [hw]
    have hrec_ts : recRoles post "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] =
        recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
        (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] := by
      unfold recRoles
      by_cases h : globN s "ts" = 0
      · simp [hts_g, h]
      · simp only [hts_g, h, ↓reduceIte]
        apply List.map_congr_left
        intro ⟨k, r0⟩ hkr
        have hk : k % 8 = 0 ∧ k + 8 ≤ 72 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkr
          rcases hkr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        have hw := Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ts" 72 (by decide) hts_g h (hu_ts h) hk.1 hk.2
        simp only [hts_g] at hw; simp [hw]
    have hnest_bs : nestRoles post "bs" "bs.inner" = nestRoles s "bs" "bs.inner" := by
      unfold nestRoles
      by_cases h : globN s "bs" = 0
      · simp [hbs_g, h]
      · have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "bs" 80 (by decide) hbs_g h (hu_bs h) (k := 32) (by omega) (by omega)
        simp only [hbs_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
        by_cases h32 : memW s (globN s "bs" + 32) = 0
        · simp [h32]
        · simp only [h32, ↓reduceIte]
          have hmS : memW s (globN s "bs" + 32) ∈ S := by
            rcases hT.2.2.2.2.1 32 (by simp [bsTableSlots]) h with h0 | hm
            · exact absurd h0 h32
            · exact hm
          rw [Wave8Contracts.M08.htabValues_eq_of_unhit
            (hT.2.1 _ hmS).1 (hu_other _ hmS (hno_bs32 h))]
    have hnest_ts : nestRoles post "ts" "ts.inner" = nestRoles s "ts" "ts.inner" := by
      unfold nestRoles
      by_cases h : globN s "ts" = 0
      · simp [hts_g, h]
      · have hw32 := Wave8Contracts.M08.rec_word_eq_of_unhit
          hAs.2 hF "ts" 72 (by decide) hts_g h (hu_ts h) (k := 32) (by omega) (by omega)
        simp only [hts_g] at hw32 ⊢; simp only [h, ↓reduceIte, hw32]
        by_cases h32 : memW s (globN s "ts" + 32) = 0
        · simp [h32]
        · simp only [h32, ↓reduceIte]
          have hmS : memW s (globN s "ts" + 32) ∈ S := by
            rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) h with h0 | hm
            · exact absurd h0 h32
            · exact hm
          rw [Wave8Contracts.M08.htabValues_eq_of_unhit
            (hT.2.1 _ hmS).1 (hu_other _ hmS (hno_ts32 h))]
    unfold worldRoleSlots
    rw [hrec_ws, hrec_bs, hrec_ts, hba_g, hbia_g, hbis_g, hnest_bs, hnest_ts, hrecs_bal]
    congr 1; congr 1
    apply List.flatMap_congr
    intro ad had
    obtain ⟨e0, e8, _⟩ := had_props ad had
    rw [e0, e8]
  have hnd_alloc : ∀ o ∈ nodeExtents s Nd, o = (0, 0) ∨ Allocated s o := by
    intro o ho
    obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
    rcases hno with rfl | rfl
    · exact Or.inr (hTr.1.1 n hn).2.1
    · unfold nodePath
      split_ifs with hp
      · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hp.1 with h0 | ⟨_, hal, _⟩
        · exact absurd h0 hp.2
        · exact Or.inr hal
      · exact Or.inl rfl
  have hu_nd : ∀ o ∈ nodeExtents s Nd, M08IvlUnhit s post o := by
    intro o ho
    apply m08_ivlUnhit_of_frameOutside_add hfr_0p hk_al_0p hAs.2.2.2.2.2.2.1
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj_fp
      · exact Or.inr (Or.inl rfl)
      · exact (hTr.2.1 o ho).1 tw.toNat htw_S j hj_fp
    · rcases hnd_alloc o ho with rfl | hal
      · exact Or.inl rfl
      · exact disj_fresh_of_zero_or_allocated_add hAs.2 hAp.2 hhp_0p (Or.inr hal)
  have hu_nd_rec : ∀ n ∈ Nd, M08IvlUnhit s post (nodeIvl s n) := fun n hn =>
    hu_nd _ (List.mem_flatMap.2 ⟨n, hn, by simp⟩)
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hnz k hk
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_np, hin_p, _⟩
    · exact absurd h0 hnz
    · have h264 : heapLimit < 2 ^ 64 := by decide
      have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by have := hin_p.2; dsimp at this; omega
      let c := panByteAlignHOL (BitVec.ofNat 64 (memW s (n + 32) + k))
      have hc_nat : c.toNat = (memW s (n + 32) + k) / 8 * 8 := by
        have hal8 : 2 ^ ((64 : Nat) / 8).log2 = 8 := by decide
        change (BitVec.ofNat 64 ((BitVec.ofNat 64 (memW s (n + 32) + k)).toNat / 2 ^ ((64 : Nat) / 8).log2 *
          2 ^ ((64 : Nat) / 8).log2)).toNat = (memW s (n + 32) + k) / 8 * 8
        rw [hal8, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt,
          Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self _ 8) ha_lt)]
      have hp_mem : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hnz]⟩
      have hmem_c : post.memory c = s.memory c := hfr_0p c
        (fun j hj hcj => by
          obtain ⟨h1, h2⟩ := hcj
          rw [hc_nat] at h1 h2
          rcases List.mem_cons.1 hj with rfl | hj_fp
          · dsimp at h1 h2; omega
          · have hj_al := (hWF_tw.1 j hj_fp).2
            have hj1 := hj_al.1; have hj2 := hj_al.2.1
            have hdj := (hTr.2.1 _ hp_mem).1 tw.toNat htw_S j hj_fp
            rcases hdj with d | d | d | d <;> (try dsimp at d) <;> omega)
        (fun hcf => by
          obtain ⟨h1, h2⟩ := hcf
          dsimp at h1 h2
          rw [hc_nat] at h1 h2
          have hp_hp8 : (globN post "heap_ptr") % 8 = 0 := hAp.2.2.2.2.2.2.1
          have hs_hp8 : (globN s "heap_ptr") % 8 = 0 := hAs.2.2.2.2.2.2.1
          have hdj := disj_fresh_of_zero_or_allocated_add hAs.2 hAp.2 hhp_0p (Or.inr hal_np)
          rcases hdj with d | d | d | d <;> (try dsimp at d) <;> omega)
      unfold memB
      change (match post.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v post.be).toNat) =
             (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v s.be).toNat)
      rw [hmem_c, hbe_0p]
  obtain ⟨hNH_post, hne_eq⟩ := Wave8Contracts.M08.nodeHeap_congr_bytes
    hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_byte
  have htw_disj : ∀ i ∈ htabFootprint post tw.toNat,
      (∀ u ∈ S, u ≠ tw.toNat → ∀ j ∈ htabFootprint s u, Disj i j) ∧
      (∀ j ∈ fixedObjects post, Disj i j) ∧
      (∀ o ∈ nodeExtents s Nd, Disj i o) := by
    intro i hi
    rcases (hfp_tw_p i hi).2 with ⟨j0, hj0, hin0⟩ | hfresh1p
    · rw [hfp_tw_1] at hj0
      refine ⟨fun u hu hne j hj => Wave8Contracts.M08.disj_of_inside_left hin0
                (hT.2.2.1 tw.toNat htw_S u hu hne.symm j0 hj0 j hj),
              fun j hj => ?_,
              fun o ho => Wave8Contracts.M08.disj_of_inside_left hin0
                (disj_flip ((hTr.2.1 o ho).1 tw.toNat htw_S j0 hj0))⟩
      rcases hfix_class j hj with hj_old | hj_fr
      · exact Wave8Contracts.M08.disj_of_inside_left hin0
          (((hT.2.1 tw.toNat htw_S).2 j0 hj0).2 j hj_old)
      · exact Wave8Contracts.M08.disj_of_inside_left hin0
          (disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2
            (((hT.2.1 tw.toNat htw_S).2 j0 hj0).1)
            ⟨(hfresh_lw_props j hj_fr).1.1, le_trans (hfresh_lw_props j hj_fr).1.2 hhp_1p⟩))
    · have hin_s1p : Inside i (globN m1 "heap_ptr") (globN post "heap_ptr") :=
        ⟨hfresh1p.1, by have := hfresh1p.2; omega⟩
      have hin_0p : Inside i (globN s "heap_ptr") (globN post "heap_ptr") :=
        ⟨le_trans hhp_01 hin_s1p.1, hin_s1p.2⟩
      refine ⟨fun u hu _ j hj => Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2
                (((hT.2.1 u hu).2 j hj).1) hin_0p,
              fun j hj => ?_,
              fun o ho => ?_⟩
      · rcases hfix_class j hj with hj_old | hj_fr
        · rcases hF.1 j hj_old with hz | ⟨hal_j, _⟩
          · exact Or.inr (Or.inl hz)
          · exact Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_j hin_0p
        · have hj_in1 : Inside j (globN s "heap_ptr") (globN m1 "heap_ptr") :=
            (hfresh_lw_props j hj_fr).1
          exact Or.inr (Or.inr (Or.inr (by have := hj_in1.2; have := hin_s1p.1; omega)))
      · rcases hnd_alloc o ho with rfl | hal_o
        · exact Or.inr (Or.inl rfl)
        · exact Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_o hin_0p
  have hT_post : TablesTyped post S := by
    obtain ⟨hnd, htwf, htpw, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, _, hroles⟩ := hT
    refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_part.2, ?_⟩
    · intro u hu
      by_cases heq : u = tw.toNat
      · subst heq
        exact ⟨hwf_tw_p, fun i hi => ⟨(hfp_tw_p i hi).1, (htw_disj i hi).2.1⟩⟩
      · rw [(hother_fp u hu heq).2]
        refine ⟨Wave8Contracts.M08.htabWF_congr_unhit hAs.1 hAp.1 (htwf u hu).1 (hu_other u hu heq),
          fun i hi => ⟨hag.allocated ((htwf u hu).2 i hi).1, fun j hj => ?_⟩⟩
        rcases hfix_class j hj with hj_old | hj_fr
        · exact ((htwf u hu).2 i hi).2 j hj_old
        · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2
            ((htwf u hu).2 i hi).1
            ⟨(hfresh_lw_props j hj_fr).1.1, le_trans (hfresh_lw_props j hj_fr).1.2 hhp_1p⟩)
    · intro u hu v hv hne i hi j hj
      by_cases hu0 : u = tw.toNat
      · subst hu0; rw [(hother_fp v hv hne.symm).2] at hj
        exact (htw_disj i hi).1 v hv hne.symm j hj
      · by_cases hv0 : v = tw.toNat
        · subst hv0; rw [(hother_fp u hu hu0).2] at hi
          exact disj_flip ((htw_disj j hj).1 u hu hu0 i hi)
        · rw [(hother_fp u hu hu0).2] at hi; rw [(hother_fp v hv hv0).2] at hj
          exact htpw u hu v hv hne i hi j hj
    · intro k hk hnz
      rw [hws_g] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by decide) hws_g hnz (hu_ws hnz) hk8.1 hk8.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [hbs_g] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by decide) hbs_g hnz (hu_bs hnz) hk8.1 hk8.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [hts_g] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by decide) hts_g hnz (hu_ts hnz) hk8.1 hk8.2]
      exact htsR k hk hnz
    · intro g hg_mem; rw [hgs.2.1 g hg_mem]; exact hgR g hg_mem
    · intro hnz hmem
      rw [hbs_g] at hnz
      have ew := Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by decide) hbs_g hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact Wave8Contracts.M08.htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_other _ hmem (hno_bs32 hnz)) (fun _ hx => hx) (hbsN hnz hmem)
    · intro hnz hmem
      rw [hts_g] at hnz
      have ew := Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by decide) hts_g hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact Wave8Contracts.M08.htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_other _ hmem (hno_ts32 hnz)) (fun _ hx => hx) (htsN hnz hmem)
    · intro ad had
      have had_s : ad ∈ balRecords s := by rwa [← hrecs_bal]
      obtain ⟨e0, e8, _, _, _, hkl, hll⟩ := had_props ad had_s
      exact ⟨e0 ▸ (hbalT ad had_s).1, e8 ▸ (hbalT ad had_s).2.1, hkl, hll⟩
    · unfold RolesOK at hroles ⊢
      rw [hwrs_eq, hjr_eq]
      refine ⟨fun a ha => ?_, hroles.2⟩
      obtain ⟨haS, hkl⟩ := hroles.1 a ha
      by_cases ha0 : a.1 = tw.toNat
      · rw [ha0] at hkl ⊢; exact ⟨htw_S, hhdr0_tw_p.trans hkl⟩
      · exact ⟨haS, ((hother_fp a.1 haS ha0).1 0 (by omega)).trans hkl⟩
  have hTr_post : TriesTypedWith post S Nd := by
    refine ⟨hNH_post, ?_, ?_⟩
    · rw [hne_eq]
      intro o ho
      refine ⟨fun u hu i hi => ?_, fun j hj => ?_⟩
      · by_cases hu0 : u = tw.toNat
        · subst hu0; exact disj_flip ((htw_disj i hi).2.2 o ho)
        · rw [(hother_fp u hu hu0).2] at hi; exact (hTr.2.1 o ho).1 u hu i hi
      · rcases hfix_class j hj with hj_old | hj_fr
        · exact (hTr.2.1 o ho).2 j hj_old
        · rcases hnd_alloc o ho with rfl | hal_o
          · exact Or.inl rfl
          · exact disj_flip (Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_o
              ⟨(hfresh_lw_props j hj_fr).1.1, le_trans (hfresh_lw_props j hj_fr).1.2 hhp_1p⟩)
    · intro hws_nz
      rw [hws_g] at hws_nz
      have e24 := Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by decide) hws_g hws_nz (hu_ws hws_nz) (k := 24) (by omega) (by omega)
      have e32 := Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by decide) hws_g hws_nz (hu_ws hws_nz) (k := 32) (by omega) (by omega)
      rw [e24, e32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hws_nz
      refine ⟨hr24, fun htS i hi => ?_⟩
      have hne32 := hno_ws32 hws_nz
      have hu32 := hu_other _ htS hne32
      have hwf32 := (hT.2.1 _ htS).1
      have hvals_eq := Wave8Contracts.M08.htabValues_eq_of_unhit hwf32 hu32
      obtain ⟨hhdr32, _⟩ := hother_fp _ htS hne32
      rw [hhdr32 3 (by omega)] at hi
      have hget : (htabValues post (memW s (globN s "ws" + 32)))[i]? =
          (htabValues s (memW s (globN s "ws" + 32)))[i]? := by rw [hvals_eq]
      simp only [htabValues, List.getElem?_map, List.getElem?_range, hhdr32 3 (by omega), hi,
        Option.map_some, Option.some.injEq] at hget
      rw [hget]; exact hr32 htS i hi
  refine ⟨S, Nd, fun _ h => h, ⟨hT_post, hJ_post, hF_post, hTr_post⟩, ?_, ?_⟩
  · intro o ho
    unfold worldOwned M13.worldOwned at ho
    rcases List.mem_append.1 ho with ho12 | ho_nd
    · rcases List.mem_append.1 ho12 with ho_tab | ho_fix
      · obtain ⟨u, huS, hi⟩ := List.mem_flatMap.1 ho_tab
        by_cases hu_tw : u = tw.toNat
        · subst hu_tw
          rcases (hfp_tw_p o hi).2 with ⟨j, hj1, hin⟩ | hfresh1p
          · rw [hfp_tw_1] at hj1
            refine Or.inr (Or.inl ⟨j, ?_, hin⟩)
            unfold worldOwned M13.worldOwned
            exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨tw.toNat, htw_S, hj1⟩))
          · exact Or.inr (Or.inr ⟨le_trans hhp_01 hfresh1p.1, by have := hfresh1p.2; omega⟩)
        · rw [(hother_fp u huS hu_tw).2] at hi
          refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
          unfold worldOwned M13.worldOwned
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u, huS, hi⟩))
      · rcases hfix_class o ho_fix with ho_s | ho_fr
        · refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
          unfold worldOwned M13.worldOwned
          exact List.mem_append_left _ (List.mem_append_right _ ho_s)
        · exact Or.inr (Or.inr ⟨(hfresh_lw_props o ho_fr).1.1, le_trans (hfresh_lw_props o ho_fr).1.2 hhp_1p⟩)
    · rw [hne_eq] at ho_nd
      refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
      unfold worldOwned M13.worldOwned
      exact List.mem_append_right _ ho_nd
  · intro a hkeep hnot_hf
    apply hfr_0p a
    · intro j hj hcj
      rcases List.mem_cons.1 hj with rfl | hj_fp
      · exact hkeep (freeGap s)
          (List.mem_append_right _ (List.mem_singleton.2 rfl))
          (cellHits_sp0_imp_freeGap hAs.2 hcj)
      · apply hkeep j
        · apply List.mem_append_left; apply List.mem_append_left
          unfold worldOwned M13.worldOwned
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨tw.toNat, htw_S, hj_fp⟩))
        · exact hcj
    · intro ⟨c1, c2⟩
      apply hnot_hf
      dsimp only at c1 c2
      have hhp_lim : globN post "heap_ptr" ≤ heapLimit := hAp.2.2.1
      unfold heapFree M13.heapFree CellHits
      dsimp only
      omega

private theorem bal_stor_recordsKept {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {tw : BitVec 64} {S0 Nd0 : List Nat}
    (hAs : ArenaReady s) (hAp : ArenaReady post) (hW0 : WorldTypedWith s S0 Nd0)
    (htw_S0 : tw.toNat ∈ S0)
    (hgs : Wave8Contracts.M08.WorldGlobalsSame s post)
    (hhp_0p : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hWF_tw : HtabWF s tw.toNat)
    (hfr_0p : FrameOutside s post
      ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat)
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    RecordsKept (fun _ => []) stdKeep s post := by
  have hk_al_0p : ∀ j ∈ ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat), j.1 % 8 = 0 := by
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj_fp
    · exact hAs.2.2.2.2.2.2.2.2.1
    · exact (hWF_tw.1 j hj_fp).2.1
  have hu_fixed_0p : ∀ i ∈ fixedObjects s, M08IvlUnhit s post i := by
    intro i hi
    apply m08_ivlUnhit_of_frameOutside_add hfr_0p hk_al_0p hAs.2.2.2.2.2.2.1
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj_fp
      · exact Or.inr (Or.inl rfl)
      · exact disj_flip (((hW0.1.2.1 _ htw_S0).2 j hj_fp).2 i hi)
    · rcases hW0.2.2.1.1 i hi with hz | ⟨hal, _⟩
      · exact disj_fresh_of_zero_or_allocated_add hAs.2 hAp.2 hhp_0p (Or.inl hz)
      · exact disj_fresh_of_zero_or_allocated_add hAs.2 hAp.2 hhp_0p (Or.inr hal)
  intro rec hrec hnz k hk _
  have hrec_tr : rec.1 ∈ ["ws", "bs", "ts", "bo"] ∧
      ∃ sz, (rec.1, sz) ∈ typedRecords ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
    simp only [stdKeep, M13.stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
    rcases hrec with rfl | rfl | rfl | rfl
    · refine ⟨by simp, 40, by decide, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    · refine ⟨by simp, 80, by decide, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    · refine ⟨by simp, 72, by decide, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    · refine ⟨by simp, 88, by decide, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
  obtain ⟨_, sz, htr, hk8, hksz⟩ := hrec_tr
  have hg_eq : globN post rec.1 = globN s rec.1 :=
    hgs.1 (rec.1, sz) (Wave8Contracts.M08.typedRecord_mem_globalBuffers htr)
  have hfix_rec : (globN s rec.1, sz) ∈ fixedObjects s := by
    have hm := Wave8Contracts.M08.typedRecord_mem_fixedObjects s htr
    simpa [hnz] using hm
  have hu_rec : M08IvlUnhit s post (globN s rec.1, sz) := hu_fixed_0p _ hfix_rec
  simpa [hg_eq] using Wave8Contracts.M08.rec_word_eq_of_unhit hAs.2 hW0.2.2.1 rec.1 sz htr hg_eq hnz hu_rec hk8 hksz

private def storNewBranchProg : ProgHOL 64 :=
  .seq
    (.call (some (some (.local, ofString "l"), none)) (ofString "lst_new")
      [.const 40#64, .const 2#64])
    (.call (some (none, none)) (ofString "htab_set")
      [.var .local (ofString "t"), .var .local (ofString "slot"), .var .local (ofString "l")])

private theorem bal_stor_lst_new_htab_set_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (adw tw slotw : BitVec 64) (cont : ProgHOL 64)
    (hW : WorldOK s)
    (had_rec : adw.toNat ∈ balRecords s)
    (htw_ad : memW s adw.toNat = tw.toNat)
    (htw_nz : tw ≠ 0)
    (hs_t : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hs_slot : s.locals.lookup (ofString "slot") = some (.val (.word slotw)))
    (hnt : (evaluateHOLFiniteState s (.seq storNewBranchProg cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (.seq storNewBranchProg cont)).1) :
    ∃ (lw : BitVec 64) (post : PanSemStateFiniteExact 64 F),
      lw ≠ 0 ∧
      WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none post ∧
      WorldOK post ∧
      (∀ S Nd, WorldTypedWith post S Nd → LstOK post lw.toNat ∧ BalListOrigin post lw.toNat 40) ∧
      post.locals.lookup (ofString "l") = some (.val (.word lw)) ∧
      (∀ y, y ≠ ofString "l" → post.locals.lookup y = s.locals.lookup y) ∧
      (evaluateHOLFiniteState post cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState post cont).1 ∧
      evaluateHOLFiniteState s (.seq storNewBranchProg cont) = evaluateHOLFiniteState post cont := by
  have hAs : ArenaReady s := hW.1
  have htw_nz_nat : tw.toNat ≠ 0 := fun h => htw_nz (BitVec.eq_of_toNat_eq (by simpa using h))
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  have htw_S0 : tw.toNat ∈ S0 := by
    have h0 := (hWT0.1.2.2.2.2.2.2.2.2.2.1 adw.toNat had_rec).1
    rwa [htw_ad] at h0
  have hWF_tw_0 : HtabWF s tw.toNat := (hWT0.1.2.1 tw.toNat htw_S0).1
  have hal_tw_0 : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i :=
    fun i hi => ((hWT0.1.2.1 tw.toNat htw_S0).2 i hi).1
  have hseq_assoc : evaluateHOLFiniteState s (.seq storNewBranchProg cont) =
      evaluateHOLFiniteState s
        (.seq (.call (some (some (.local, ofString "l"), none)) (ofString "lst_new")
            [.const 40#64, .const 2#64])
          (.seq (.call (some (none, none)) (ofString "htab_set")
              [.var .local (ofString "t"), .var .local (ofString "slot"), .var .local (ofString "l")])
            cont)) := by
    unfold storNewBranchProg
    simp only [evaluateHOLFiniteState_seq_line780]
    rcases evaluateHOLFiniteState s
      (.call (some (some (.local, ofString "l"), none)) (ofString "lst_new") [.const 40#64, .const 2#64]) with ⟨r1, st1⟩
    cases r1 <;> rfl
  rw [hseq_assoc] at hnt hres ⊢
  obtain ⟨lw, m1, hlw_eq, hlw8, hlw_nz_nat, _, _, _, hhp_m1, hhp_lt_01,
      hA1, hbe1, hsp1, _, hlst_1, hobjs_1, _, hp_1, hfr_01,
      hm1_l, hm1_other, hgl_01, hnt1, hres1, heval1⟩ :=
    seq_call_lst_new_local_resumes s (ofString "l") 40#64 2#64 _
      hAs (by decide) (by decide) (by decide) (by decide) hnt hres
  have h40 : (40#64 : BitVec 64).toNat = 40 := rfl
  have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
  rw [h40, h2] at hhp_m1 hobjs_1
  rw [h40] at hp_1
  simp only [show 40 * 2 = 80 from rfl] at hhp_m1 hobjs_1
  have hhp_01 : globN s "heap_ptr" ≤ globN m1 "heap_ptr" := le_of_lt hhp_lt_01
  have hsp8 : (globN s "scratch_ptr") % 8 = 0 := hAs.2.2.2.2.2.2.2.2.1
  have hu_tw_01 : ∀ i ∈ htabFootprint s tw.toNat, M08IvlUnhit s m1 i := by
    intro i hi
    apply m08_ivlUnhit_of_frameOutside_add hfr_01
    · intro j hj; simp only [List.mem_singleton] at hj; subst hj; exact hsp8
    · exact hAs.2.2.2.2.2.2.1
    · intro j hj; simp only [List.mem_singleton] at hj; subst hj; exact Or.inr (Or.inl rfl)
    · exact disj_fresh_of_zero_or_allocated_add hAs.2 hA1.2 hhp_01 (Or.inr (hal_tw_0 i hi))
  have hal_tw_1 : ∀ i ∈ htabFootprint s tw.toNat, Allocated m1 i :=
    fun i hi => AllocatorGrows.allocated (show AllocatorGrows s m1 from ⟨hhp_01, by omega⟩) (hal_tw_0 i hi)
  obtain ⟨hwf_tw_1, hfp_tw_1, hhdr_tw_01⟩ :=
    htabWF_transfer_unhit hAs hA1 hWF_tw_0 hu_tw_01 hal_tw_1
  have hm1_t : m1.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    rw [hm1_other _ (by decide)]; exact hs_t
  have hm1_slot : m1.locals.lookup (ofString "slot") = some (.val (.word slotw)) := by
    rw [hm1_other _ (by decide)]; exact hs_slot
  obtain ⟨post, hexit, hvalues_1p, hbe_1p, hloc_1p, hsp_1p, _, hnt2, hres2, heval2⟩ :=
    seq_call_htab_set_void_resumes m1
      (.var .local (ofString "t")) (.var .local (ofString "slot")) (.var .local (ofString "l"))
      cont tw slotw lw
      (by simp [evalAt, evalHOLExact, hm1_t])
      (by simp [evalAt, evalHOLExact, hm1_slot])
      (by simp [evalAt, evalHOLExact, hm1_l])
      hA1 hwf_tw_1 (by rwa [hfp_tw_1]) hnt1 hres1
  obtain ⟨hAp, hwf_tw_p, hhdr0_tw_1p, _, hhp_1p, hfp_tw_p, hfr_1p, hgl_1p⟩ := hexit
  have hhp_0p : globN s "heap_ptr" ≤ globN post "heap_ptr" := le_trans hhp_01 hhp_1p
  have hgk : GlobalsKept ["heap_ptr"] s post := by
    intro k hk
    have hk' : k ≠ ofString "heap_ptr" := fun heq => hk (by simp [heq])
    exact (hgl_01 k hk').trans (hgl_1p k hk)
  have hgs : Wave8Contracts.M08.WorldGlobalsSame s post :=
    Wave8Contracts.M08.worldGlobalsSame_of_kept hgk (fun name h => Or.inl (by simpa using h))
  have hsp_post : globN post "scratch_ptr" = globN s "scratch_ptr" := hsp_1p.trans hsp1
  have hbe_0p : post.be = s.be := hbe_1p.trans hbe1
  have hhdr0_tw_p : hdr post tw.toNat 0 = hdr s tw.toNat 0 :=
    hhdr0_tw_1p.trans (hhdr_tw_01 0 (by omega))
  have hvals_tw_01 : htabValues m1 tw.toNat = htabValues s tw.toNat :=
    Wave8Contracts.M08.htabValues_eq_of_unhit hWF_tw_0 hu_tw_01
  have hvalues_0p : HtabSetValuesPost s post tw.toNat lw.toNat := by
    unfold HtabSetValuesPost at hvalues_1p ⊢
    rw [← hvals_tw_01]
    exact hvalues_1p
  have hfr_0p : FrameOutside s post
      ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat)
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
    intro a hkeep hfresh
    have h1 := hfr_1p a (fun j hj => by
      rw [hfp_tw_1] at hj
      exact hkeep j (List.mem_cons_of_mem _ hj))
      (fun ⟨hc1, hc2⟩ => hfresh ⟨by dsimp at hc1 ⊢; omega, by dsimp at hc2 ⊢; omega⟩)
    have h2 := hfr_01 a (fun j hj => by
      simp only [List.mem_singleton] at hj; subst hj
      exact hkeep _ List.mem_cons_self)
      (fun ⟨hc1, hc2⟩ => hfresh ⟨by dsimp at hc1 ⊢; omega, by dsimp at hc2 ⊢; omega⟩)
    exact h1.trans h2
  have hu_1p_of_fresh01 : ∀ {i : Ivl},
      Inside i (globN s "heap_ptr") (globN m1 "heap_ptr") → M08IvlUnhit m1 post i := by
    intro i hi_in
    apply m08_ivlUnhit_of_frameOutside_add hfr_1p
    · intro j hj; exact (hwf_tw_1.1 j hj).2.1
    · exact hA1.2.2.2.2.2.2.1
    · intro j hj
      rw [hfp_tw_1] at hj
      exact Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hA1.2 (hal_tw_0 j hj) hi_in
    · exact Or.inr (Or.inr (Or.inl (by have := hi_in.2; dsimp; omega)))
  obtain ⟨hlst_p, hobjs_p⟩ := balEnsureAlloc_lst_mid lw.toNat 40 2 hA1.2.2.1 hlw8 hlw_nz_nat
    (by omega) (hu_1p_of_fresh01 ⟨by dsimp; omega, by dsimp; omega⟩) hlst_1 hobjs_1
  have hm0_8_16 := balEnsureAlloc_low_words hAs hWF_tw_0 hal_tw_0 hfr_0p
  have hws : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none post := by
    refine ⟨hAp, hhp_0p, hgk,
      bal_stor_recordsKept hAs hAp hWT0 htw_S0 hgs hhp_0p hWF_tw_0 hfr_0p, ?_⟩
    intro S Nd hWT _
    have htw_S : tw.toNat ∈ S := by
      have h0 := (hWT.1.2.2.2.2.2.2.2.2.2.1 adw.toNat had_rec).1
      rwa [htw_ad] at h0
    have hWF_tw : HtabWF s tw.toNat := (hWT.1.2.1 tw.toNat htw_S).1
    have hal_tw : ∀ i ∈ htabFootprint s tw.toNat, Allocated s i :=
      fun i hi => ((hWT.1.2.1 tw.toNat htw_S).2 i hi).1
    obtain ⟨S', Nd', hsub, hWT_p, hog, hfr_world⟩ :=
      bal_stor_lst_new_htab_set_core hAs hA1 hAp hWT htw_nz_nat ⟨adw.toNat, had_rec, htw_ad⟩
        hgk hsp_post hhp_01 hhp_1p hbe_0p hlw_eq hlw8 hlw_nz_nat hhp_m1
        hfr_0p hfp_tw_1 hhdr0_tw_p hwf_tw_p hfp_tw_p hvalues_0p hlst_p hobjs_p hm0_8_16
    exact ⟨S', Nd', hsub, hWT_p, hog, hfr_world, trivial⟩
  have hW_post : WorldOK post := worldOK_of_step hW hws
  have hba_g : globN post "bal_accounts" = globN s "bal_accounts" :=
    hgs.2.1 "bal_accounts" (by simp [globalTableRoots])
  have hno_ba : globN s "bal_accounts" ≠ tw.toNat := by
    have hd := (bal_stor_slot_distinct hWT0.1 had_rec
      (by rw [htw_ad]; exact htw_nz_nat)).2.2.2.1
    rwa [htw_ad] at hd
  have hk_al_0p : ∀ j ∈ ((globN s "scratch_ptr", 0) :: htabFootprint s tw.toNat), j.1 % 8 = 0 := by
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj_fp
    · exact hsp8
    · exact (hWF_tw_0.1 j hj_fp).2.1
  have hrecs_post : balRecords post = balRecords s :=
    Wave8Contracts.M08.balRecords_eq_of_unhit hWT0.1 hba_g (fun hnz => by
      rcases hWT0.1.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
      · exact absurd h0 hnz
      · intro i hi
        apply m08_ivlUnhit_of_frameOutside_add hfr_0p hk_al_0p hAs.2.2.2.2.2.2.1
        · intro j hj
          rcases List.mem_cons.1 hj with rfl | hj_fp
          · exact Or.inr (Or.inl rfl)
          · exact hWT0.1.2.2.1 _ hm tw.toNat htw_S0 hno_ba i hi j hj_fp
        · exact disj_fresh_of_zero_or_allocated_add hAs.2 hAp.2 hhp_0p
            (Or.inr ((hWT0.1.2.1 _ hm).2 i hi).1))
  have had_unhit_post : M08IvlUnhit s post (adw.toNat, 40) := by
    have had_fix : (adw.toNat, 40) ∈ fixedObjects s := by
      unfold fixedObjects; apply List.mem_append_right; unfold balObjects
      exact List.mem_flatMap.2 ⟨adw.toNat, had_rec, by simp⟩
    apply m08_ivlUnhit_of_frameOutside_add hfr_0p hk_al_0p hAs.2.2.2.2.2.2.1
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj_fp
      · exact Or.inr (Or.inl rfl)
      · exact disj_flip (((hWT0.1.2.1 _ htw_S0).2 j hj_fp).2 _ had_fix)
    · rcases hWT0.2.2.1.1 _ had_fix with hz | ⟨hal, _⟩
      · exact disj_fresh_of_zero_or_allocated_add hAs.2 hAp.2 hhp_0p (Or.inl hz)
      · exact disj_fresh_of_zero_or_allocated_add hAs.2 hAp.2 hhp_0p (Or.inr hal)
  have htw_ad_post : memW post adw.toNat = tw.toNat := by
    have had_fix : (adw.toNat, 40) ∈ fixedObjects s := by
      unfold fixedObjects; apply List.mem_append_right; unfold balObjects
      exact List.mem_flatMap.2 ⟨adw.toNat, had_rec, by simp⟩
    rcases hWT0.2.2.1.1 _ had_fix with h0 | ⟨hal_ad, hw_ad⟩
    · simp at h0
    have hhi_ad := (Wave8Contracts.M08.ivl_allocated_bound hAs.2 hal_ad).2
    have e0 : memW post adw.toNat = memW s adw.toNat := by
      simpa using Wave8Contracts.M08.memW_eq_of_ivlUnhit had_unhit_post hw_ad.1 hhi_ad ⟨by omega, by omega⟩
    exact e0.trans htw_ad
  have hlw_in_post : lw.toNat ∈ htabValues post tw.toNat :=
    htabSetValuesPost_value_mem hvalues_0p
  have hlw_nz : lw ≠ 0 := fun h => hlw_nz_nat (by subst h; rfl)
  refine ⟨lw, post, hlw_nz, hws, hW_post, ?_, ?_, ?_, hnt2, hres2, heval1.trans heval2⟩
  · intro S Nd _
    refine ⟨hlst_p, Or.inr ⟨adw.toNat, ?_, ?_, rfl⟩⟩
    · rwa [hrecs_post]
    · rwa [htw_ad_post]
  · rw [hloc_1p]; exact hm1_l
  · intro y hy; rw [hloc_1p]; exact hm1_other y hy

private theorem add_storage_write_body_worldStep {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (addrw slotw idxw nv0 nv1 nv2 nv3 : BitVec 64)
    (hW : WorldOK s)
    (hs_addr : s.locals.lookup (ofString "addr") = some (.val (.word addrw)))
    (hs_slot : s.locals.lookup (ofString "slot") = some (.val (.word slotw)))
    (hs_idx : s.locals.lookup (ofString "idx") = some (.val (.word idxw)))
    (hs_nv : s.locals.lookup (ofString "new_value") =
      some (.rStruct [.val (.word nv0), .val (.word nv1), .val (.word nv2), .val (.word nv3)]))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_storage_write)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_storage_write)).1) :
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_storage_write)).1
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_storage_write)).2 := by
  have hAR0 : ArenaReady s := hW.1
  set upsertProg : ProgHOL 64 :=
    .decCall (ofString "e") .one (ofString "lst_upsert_idx")
      [.var .local (ofString "l"), .const 40#64, .var .local (ofString "idx")]
      addStorageWriteTailProg
  set iteProg : ProgHOL 64 :=
    .seq
      (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
        storNewBranchProg
        (.assign .local (ofString "l") (.rfield 1 (.var .local (ofString "m")))))
      upsertProg
  set decLProg : ProgHOL 64 :=
    .dec (ofString "l") .one (.const 0#64) iteProg
  set getProg : ProgHOL 64 :=
    .decCall (ofString "m") (.comb [.one, .one]) (ofString "htab_get")
      [.var .local (ofString "t"), .var .local (ofString "slot")]
      decLProg
  set decTProg : ProgHOL 64 :=
    .dec (ofString "t") .one
      (.load .one (.op .add [.var .local (ofString "ad"), .const 0#64]))
      getProg
  have hbody_eq : sourceFnBody Guest.Software.guestFn_add_storage_write =
      .decCall (ofString "ad") .one (ofString "bal_ensure_account")
        [.var .local (ofString "addr")] decTProg := rfl
  rw [hbody_eq] at hnt hres ⊢
  -- Step 1: `bal_ensure_account`
  obtain ⟨adw, mid1, _, _, _, _, hws1, hW1, had_rec1, hslot1,
      _, hmid1_other, hnt1, hres1, heq1_r, heq1_s⟩ :=
    decCall_bal_ensure_account_resumes_idx s (ofString "ad")
      (.var .local (ofString "addr")) addrw decTProg hW
      (by simp [evalHOLExact, hs_addr]) hnt hres
  obtain ⟨tw, htw_nat, hev_t⟩ := hslot1 0#64 (by decide) (by decide)
  have htw_ad1 : memW mid1 adw.toNat = tw.toNat := by
    have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
    simpa [h0] using htw_nat.symm
  have hmid1_slot : mid1.locals.lookup (ofString "slot") = some (.val (.word slotw)) := by
    rw [hmid1_other _ (by decide)]; exact hs_slot
  have hmid1_idx : mid1.locals.lookup (ofString "idx") = some (.val (.word idxw)) := by
    rw [hmid1_other _ (by decide)]; exact hs_idx
  have hmid1_nv : mid1.locals.lookup (ofString "new_value") =
      some (.rStruct [.val (.word nv0), .val (.word nv1), .val (.word nv2), .val (.word nv3)]) := by
    rw [hmid1_other _ (by decide)]; exact hs_nv
  -- Step 2: `dec "t" .one (load .one (ad + 0))`
  dsimp only [decTProg] at hnt1 hres1
  have heval_decT : evaluateHOLFiniteState mid1 decTProg =
      ((evaluateHOLFiniteState (setVarHOLFinite (ofString "t") (.val (.word tw)) mid1) getProg).1,
        { (evaluateHOLFiniteState (setVarHOLFinite (ofString "t") (.val (.word tw)) mid1) getProg).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState (setVarHOLFinite (ofString "t") (.val (.word tw)) mid1) getProg).2.locals
            (ofString "t", mid1.locals.lookup (ofString "t")) }) := by
    dsimp only [decTProg]
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    rw [hev_t]; dsimp only
    rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
  let sT := setVarHOLFinite (ofString "t") (.val (.word tw)) mid1
  have hsT_W : WorldOK sT := localsFree_worldOK mid1 _ mid1.clock hW1
  have hsT_eq : sT = { mid1 with locals := sT.locals, clock := mid1.clock } := rfl
  have hnt_sT : (evaluateHOLFiniteState sT getProg).1 ≠ some .timeOut := by
    intro hto; apply hnt1
    have h1 := congrArg Prod.fst heval_decT
    dsimp only [decTProg] at h1; rw [h1]; exact hto
  have hres_sT : Resumes (evaluateHOLFiniteState sT getProg).1 := by
    have h1 := congrArg Prod.fst heval_decT
    dsimp only [decTProg] at h1; rwa [← h1]
  have hsT_t : sT.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [sT, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hsT_slot : sT.locals.lookup (ofString "slot") = some (.val (.word slotw)) := by
    simp [sT, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "t" ≠ ofString "slot" by decide, hmid1_slot]
  have hsT_idx : sT.locals.lookup (ofString "idx") = some (.val (.word idxw)) := by
    simp [sT, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "t" ≠ ofString "idx" by decide, hmid1_idx]
  have hsT_nv : sT.locals.lookup (ofString "new_value") =
      some (.rStruct [.val (.word nv0), .val (.word nv1), .val (.word nv2), .val (.word nv3)]) := by
    simp [sT, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "t" ≠ ofString "new_value" by decide, hmid1_nv]
  -- Step 3: `decCall "m" (.comb [.one, .one]) "htab_get" [var "t", var "slot"]`
  obtain ⟨tw', kw', f0, f1, ck, hev_tw', _, htw_nz', hval_in, hnt_sM, hres_sM, heqM_r, heqM_s⟩ :=
    decCall_htab_get_resumes sT (ofString "m")
      (.var .local (ofString "t")) (.var .local (ofString "slot")) decLProg
      hsT_W.1.1 hnt_sT hres_sT
  have htw_eq : tw' = tw := by
    simp [evalHOLExact, hsT_t] at hev_tw'
    exact hev_tw'.symm
  let sM := setVarHOLFinite (ofString "m") (.rStruct [.val (.word f0), .val (.word f1)])
    { sT with clock := ck }
  have hsM_W : WorldOK sM := localsFree_worldOK mid1 _ ck hW1
  have hsM_m : sM.locals.lookup (ofString "m") =
      some (.rStruct [.val (.word f0), .val (.word f1)]) := by
    simp [sM, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hsM_t : sM.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [sM, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "m" ≠ ofString "t" by decide, hsT_t]
  have hsM_slot : sM.locals.lookup (ofString "slot") = some (.val (.word slotw)) := by
    simp [sM, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "m" ≠ ofString "slot" by decide, hsT_slot]
  have hsM_idx : sM.locals.lookup (ofString "idx") = some (.val (.word idxw)) := by
    simp [sM, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "m" ≠ ofString "idx" by decide, hsT_idx]
  have hsM_nv : sM.locals.lookup (ofString "new_value") =
      some (.rStruct [.val (.word nv0), .val (.word nv1), .val (.word nv2), .val (.word nv3)]) := by
    simp [sM, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "m" ≠ ofString "new_value" by decide, hsT_nv]
  -- Step 4: `dec "l" .one 0`
  let sL := setVarHOLFinite (ofString "l") (.val (.word 0#64)) sM
  have heval_decL : evaluateHOLFiniteState sM decLProg =
      ((evaluateHOLFiniteState sL iteProg).1,
        { (evaluateHOLFiniteState sL iteProg).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState sL iteProg).2.locals
            (ofString "l", sM.locals.lookup (ofString "l")) }) := by
    dsimp only [decLProg]
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    have hc0 : @evalHOLExact 64 F _ sM.toExact (fun a => Classical.propDecidable (sM.memaddrs a))
        (.const 0#64) = some (.val (.word 0#64)) := rfl
    rw [hc0]; dsimp only
    rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
  have hsL_W : WorldOK sL := localsFree_worldOK mid1 _ ck hW1
  have hsL_eq_mid1 : sL = { mid1 with locals := sL.locals, clock := ck } := rfl
  have hnt_sL : (evaluateHOLFiniteState sL iteProg).1 ≠ some .timeOut := by
    intro hto; apply hnt_sM
    rw [heval_decL]; exact hto
  have hres_sL : Resumes (evaluateHOLFiniteState sL iteProg).1 := by
    rw [heval_decL] at hres_sM; exact hres_sM
  have hsL_l : sL.locals.lookup (ofString "l") = some (.val (.word 0#64)) := by
    simp [sL, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hsL_m : sL.locals.lookup (ofString "m") =
      some (.rStruct [.val (.word f0), .val (.word f1)]) := by
    simp [sL, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "l" ≠ ofString "m" by decide, hsM_m]
  have hsL_t : sL.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [sL, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "l" ≠ ofString "t" by decide, hsM_t]
  have hsL_slot : sL.locals.lookup (ofString "slot") = some (.val (.word slotw)) := by
    simp [sL, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "l" ≠ ofString "slot" by decide, hsM_slot]
  have hsL_idx : sL.locals.lookup (ofString "idx") = some (.val (.word idxw)) := by
    simp [sL, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "l" ≠ ofString "idx" by decide, hsM_idx]
  have hsL_nv : sL.locals.lookup (ofString "new_value") =
      some (.rStruct [.val (.word nv0), .val (.word nv1), .val (.word nv2), .val (.word nv3)]) := by
    simp [sL, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "l" ≠ ofString "new_value" by decide, hsM_nv]
  have had_rec_sL : adw.toNat ∈ balRecords sL := had_rec1
  have htw_ad_sL : memW sL adw.toNat = tw.toNat := htw_ad1
  -- Step 5: `ite (m.0 == 0) (lst_new; htab_set) (l := m.1)` producing unified `midB`
  have hbranch : ∃ (lw : BitVec 64) (midB : PanSemStateFiniteExact 64 F),
      WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra mid1 none midB ∧
      WorldOK midB ∧
      (lw ≠ 0 → ∀ S Nd, WorldTypedWith midB S Nd → LstOK midB lw.toNat ∧ BalListOrigin midB lw.toNat 40) ∧
      midB.locals.lookup (ofString "l") = some (.val (.word lw)) ∧
      midB.locals.lookup (ofString "idx") = some (.val (.word idxw)) ∧
      midB.locals.lookup (ofString "new_value") =
        some (.rStruct [.val (.word nv0), .val (.word nv1), .val (.word nv2), .val (.word nv3)]) ∧
      (evaluateHOLFiniteState midB upsertProg).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState midB upsertProg).1 ∧
      evaluateHOLFiniteState sL iteProg = evaluateHOLFiniteState midB upsertProg := by
    by_cases hf0 : f0 = 0
    · subst hf0
      have hcmp : @evalHOLExact 64 F _ sL.toExact (fun a => Classical.propDecidable (sL.memaddrs a))
          (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64)) =
          some (.val (.word 1#64)) := by
        simp [evalHOLExact, hsL_m, Compiler.Encoders.Asm.wordCmpHOL]
      have hite_eq : evaluateHOLFiniteState sL iteProg =
          evaluateHOLFiniteState sL (.seq storNewBranchProg upsertProg) := by
        dsimp only [iteProg]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcmp]
        dsimp only
        rw [if_neg (by decide : ¬ (1#64 : BitVec 64) = 0)]
        rw [evaluateHOLFiniteState_seq_line780]
      rw [hite_eq] at hnt_sL hres_sL
      obtain ⟨lw, midB, _, hwsB_sL, hWB, horigB, hB_l, hB_other, hntB, hresB, hevalB⟩ :=
        bal_stor_lst_new_htab_set_resumes sL adw tw slotw upsertProg hsL_W had_rec_sL htw_ad_sL
          (htw_eq ▸ htw_nz') hsL_t hsL_slot hnt_sL hres_sL
      have hwsB_mid1 : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra mid1 none midB :=
        worldStep_with_locals_left hsL_eq_mid1 rfl (fun _ _ _ => trivial) hwsB_sL
      refine ⟨lw, midB, hwsB_mid1, hWB, fun _ => horigB, hB_l,
        by rw [hB_other _ (by decide)]; exact hsL_idx,
        by rw [hB_other _ (by decide)]; exact hsL_nv,
        hntB, hresB, hite_eq.trans hevalB⟩
    · have hf0' : f0 ≠ 0#64 := hf0
      have hcmp : @evalHOLExact 64 F _ sL.toExact (fun a => Classical.propDecidable (sL.memaddrs a))
          (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0#64)) =
          some (.val (.word 0#64)) := by
        simp [evalHOLExact, hsL_m, Compiler.Encoders.Asm.wordCmpHOL, hf0']
      let midB := setVarHOLFinite (ofString "l") (.val (.word f1)) sL
      have hasgn : evaluateHOLFiniteState sL
          (.assign .local (ofString "l") (.rfield 1 (.var .local (ofString "m")))) =
          (none, midB) := by
        rw [evaluateHOLFiniteState_assign]
        have hev_f1 : @evalHOLExact 64 F _ sL.toExact (fun a => Classical.propDecidable (sL.memaddrs a))
            (.rfield 1 (.var .local (ofString "m"))) = some (.val (.word f1)) := by
          simp [evalHOLExact, hsL_m]
        rw [hev_f1]; dsimp only
        have hval_l : isValidValueHOLFinite sL .local (ofString "l") (.val (.word f1)) = true := by
          simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hsL_l,
            shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hval_l]; rfl
      have hite_eq : evaluateHOLFiniteState sL iteProg =
          evaluateHOLFiniteState midB upsertProg := by
        dsimp only [iteProg]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcmp]
        dsimp only
        rw [if_pos (by decide : (0#64 : BitVec 64) = 0), hasgn]
      rw [hite_eq] at hnt_sL hres_sL
      have hmidB_eq_mid1 : midB = { mid1 with locals := midB.locals, clock := ck } := rfl
      have hwsB_mid1 : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra mid1 none midB :=
        worldStep_refl (fun _ => []) ["heap_ptr"] hW1.1 (by rw [hmidB_eq_mid1])
      have hWB : WorldOK midB := localsFree_worldOK mid1 _ ck hW1
      have horigB : f1 ≠ 0 → ∀ S Nd, WorldTypedWith midB S Nd →
          LstOK midB f1.toNat ∧ BalListOrigin midB f1.toNat 40 := by
        intro _ S Nd hWTB
        have hWT_sT : WorldTypedWith sT S Nd := by
          have hsT_midB : sT = { midB with locals := sT.locals, clock := mid1.clock } := rfl
          rw [hsT_midB]
          exact (worldTypedWith_with_locals midB sT.locals mid1.clock S Nd).2 hWTB
        have htw_S : tw.toNat ∈ S := by
          have h0 := (hWT_sT.1.2.2.2.2.2.2.2.2.2.1 adw.toNat had_rec1).1
          have hm_sT : memW sT adw.toNat = tw.toNat := htw_ad1
          rwa [hm_sT] at h0
        have hWF_sT : HtabWF sT tw.toNat := (hWT_sT.1.2.1 tw.toNat htw_S).1
        have hf1_in_sT : f1.toNat ∈ htabValues sT tw.toNat :=
          htw_eq ▸ (hval_in (htw_eq.symm ▸ hWF_sT) hf0)
        have hf1_in_B : f1.toNat ∈ htabValues midB tw.toNat := hf1_in_sT
        have htw_ad_B : memW midB adw.toNat = tw.toNat := htw_ad1
        have had_rec_B : adw.toNat ∈ balRecords midB := had_rec1
        have hlst_B : LstOK midB f1.toNat :=
          (hWTB.1.2.2.2.2.2.2.2.2.2.1 adw.toNat had_rec_B).2.2.2 f1.toNat (by rwa [htw_ad_B])
        exact ⟨hlst_B, Or.inr ⟨adw.toNat, had_rec_B, by rwa [htw_ad_B], rfl⟩⟩
      refine ⟨f1, midB, hwsB_mid1, hWB, horigB,
        by simp [midB, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
        by simp [midB, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "l" ≠ ofString "idx" by decide, hsL_idx],
        by simp [midB, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "l" ≠ ofString "new_value" by decide, hsL_nv],
        hnt_sL, hres_sL, hite_eq⟩
  obtain ⟨lw, midB, hwsB, hWB, horigB, hB_l, hB_idx, hB_nv, hntB, hresB, hevalB⟩ := hbranch
  -- Step 6: `decCall "e" .one "lst_upsert_idx" [var "l", 40, var "idx"]`
  obtain ⟨ew, mid2, hlw_nz, hws2, hW2, horig2, hew8, hew_sb, hew_he, hew_lo, hew_hi,
      hmid2_e, hmid2_other, _, _, heq2_r, heq2_s⟩ :=
    decCall_lst_upsert_idx_resumes midB (ofString "e")
      (.var .local (ofString "l")) (.const 40#64) (.var .local (ofString "idx"))
      lw 40#64 idxw addStorageWriteTailProg hWB
      (by simp [evalHOLExact, hB_l]) rfl (by simp [evalHOLExact, hB_idx])
      (Or.inr (Or.inr rfl)) horigB hntB hresB
  have hmid2_nv : mid2.locals.lookup (ofString "new_value") =
      some (.rStruct [.val (.word nv0), .val (.word nv1), .val (.word nv2), .val (.word nv3)]) := by
    rw [hmid2_other _ (by decide)]; exact hB_nv
  -- Step 7: `store (e + 8) new_value; return 0`
  have hws3 := add_storage_write_tail_worldStep mid2 lw ew nv0 nv1 nv2 nv3 hW2 hlw_nz horig2
    hew8 hew_sb hew_he hew_lo hew_hi hmid2_e hmid2_nv
  have hws1B : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none midB :=
    worldStep_hp_trans hAR0.2 hws1 hwsB
  have hws1B2 : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s none mid2 :=
    worldStep_hp_trans hAR0.2 hws1B hws2
  have hws_all : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s
      (evaluateHOLFiniteState mid2 addStorageWriteTailProg).1
      (evaluateHOLFiniteState mid2 addStorageWriteTailProg).2 :=
    worldStep_hp_trans hAR0.2 hws1B2 hws3
  -- Relate final result and state up to locals
  have hfst_eq : (evaluateHOLFiniteState s
      (.decCall (ofString "ad") .one (ofString "bal_ensure_account")
        [.var .local (ofString "addr")] decTProg)).1 =
      (evaluateHOLFiniteState mid2 addStorageWriteTailProg).1 := by
    rw [heq1_r, heval_decT]; dsimp only
    rw [heqM_r, heval_decL]; dsimp only
    rw [hevalB]; dsimp only [upsertProg]
    rw [heq2_r]
  have hsnd_ex : ∃ L_final,
      (evaluateHOLFiniteState s
        (.decCall (ofString "ad") .one (ofString "bal_ensure_account")
          [.var .local (ofString "addr")] decTProg)).2 =
        { (evaluateHOLFiniteState mid2 addStorageWriteTailProg).2 with
          locals := L_final
          clock := (evaluateHOLFiniteState mid2 addStorageWriteTailProg).2.clock } := by
    rw [heq1_s, heval_decT]; dsimp only
    rw [heqM_s, heval_decL]; dsimp only
    rw [hevalB]; dsimp only [upsertProg]
    rw [heq2_s]
    exact ⟨_, rfl⟩
  obtain ⟨L_final, hsnd_eq⟩ := hsnd_ex
  rw [hfst_eq, hsnd_eq]
  exact worldStep_with_locals_right L_final
    (evaluateHOLFiniteState mid2 addStorageWriteTailProg).2.clock
    (fun _ _ _ => trivial) hws_all

theorem wk_add_storage_write_impl :
    WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "add_storage_write") := by
  refine ⟨_, _, _, lookup_add_storage_write_add, ?_⟩
  intro F s _ hW hvalid hnt hres
  obtain ⟨values, hlook_fn⟩ := hvalid
  obtain ⟨addrw, slotw, idxw, nv0, nv1, nv2, nv3, hs_addr, hs_slot, hs_idx, hs_nv⟩ :=
    lookupCode_three_word_comb4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      lookup_add_storage_write_add hlook_fn
  exact add_storage_write_body_worldStep s addrw slotw idxw nv0 nv1 nv2 nv3 hW
    hs_addr hs_slot hs_idx hs_nv hnt hres

private theorem lookup_add_storage_read_add :
    originalRuntimeCode.lookup (ofString "add_storage_read") =
      some ([(ofString "addr", .one), (ofString "slot", .one)],
        sourceFnBody Guest.Software.guestFn_add_storage_read, .one) :=
  lookup_of_guestAst_getElem 415 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_add_storage_read) rfl

private theorem nonValueSlot_bal_reads {F : Type}
    (s : PanSemStateFiniteExact 64 F) (S : List Nat) (ad : Nat)
    (hT : TablesTyped s S) (had : ad ∈ balRecords s)
    (ht0_nz : memW s (ad + 8) ≠ 0) :
    let t0 := memW s (ad + 8)
    t0 ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad' ∈ balRecords s, memW s ad' ≠ t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) := by
  have ht0_S : memW s (ad + 8) ∈ S :=
    (hT.2.2.2.2.2.2.2.2.2.1 ad had).2.1
  have ht0_wrs : (memW s (ad + 8), "bal.reads") ∈ worldRoleSlots s := by
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [ht0_nz]⟩
    apply List.mem_append.2; right
    exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
  exact R16WkAcctWs.nonValueSlot_of_wrs s S _ "bal.reads" hT ht0_nz ht0_S ht0_wrs
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem progWStep_call0_htab_set_bal_reads {F : Type}
    (s : PanSemStateFiniteExact 64 F) (adw : BitVec 64)
    (kExp vExp : ExpHOL 64)
    (hcode : s.code = originalRuntimeCode)
    (hW : WorldOK s)
    (had : adw.toNat ∈ balRecords s)
    (hs_ad : s.locals.lookup (ofString "ad") = some (.val (.word adw)))
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .local (ofString "ad"), .const 8#64]), kExp, vExp])).1 ≠ some .timeOut)
    (hfr : R16WkAcctWs.FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .local (ofString "ad"), .const 8#64]), kExp, vExp])).1) :
    R16WkAcctWs.WorldStepSc (R16WkAcctWs.bufRegions []) ["heap_ptr"] stdKeep NoExtra
      s
      (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .local (ofString "ad"), .const 8#64]), kExp, vExp])).1
      (evaluateHOLFiniteState s
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .local (ofString "ad"), .const 8#64]), kExp, vExp])).2 := by
  set tExp : ExpHOL 64 := .load .one (.op .add [.var .local (ofString "ad"), .const 8#64])
  set argsL : List (ExpHOL 64) := [tExp, kExp, vExp]
  obtain ⟨_, _, _, _, tw, htw_nat, hev_t⟩ :=
    balRecord_slot_load s adw 8#64 (.var .local (ofString "ad")) hW had
      (by simp [evalHOLExact, hs_ad]) (by decide) (by decide)
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) argsL with _ | values
  · simp [evalListHOLFinite, hargs] at hfr; exact absurd hfr R16WkAcctWs.not_flowingOrResumes_error
  · simp only [evalListHOLFinite, hargs] at hnt hfr ⊢
    have hargs_fin : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) argsL = some values := by
      rwa [evalListHOLFinite_eq_toExact]
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_set") values with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hfr; exact absurd hfr R16WkAcctWs.not_flowingOrResumes_error
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · rw [if_neg hz] at hnt hfr ⊢
        obtain ⟨v1, _, _, he1, _, _, hc_t, _, _⟩ := R16WkAcctWs.callee_param_three s (ofString "htab_set")
          (ofString "t") (ofString "key") (ofString "value") .one .one .one _ _
          (by rw [hcode]; exact EvmFrameSpecs.lookup_htab_set) _ _ _ values body' callee ret' hargs_fin hl
        have hv1_eq : v1 = .val (.word tw) := by
          unfold evalAt at he1
          rw [hev_t] at he1
          exact Option.some.inj he1.symm
        subst hv1_eq
        have hloc_t : locN (callEntryStateHOLFinite s callee) "t" = memW s (adw.toNat + 8) := by
          simp [locN, callEntryStateHOLFinite, hc_t, htw_nat]
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        have hbe_post : post.be = s.be := by
          have inv := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body').2.2.1
          rw [hrun] at inv; exact inv
        cases res with
        | none => exact absurd hfr R16WkAcctWs.not_flowingOrResumes_error
        | some cr =>
          cases cr with
          | timeOut => simp at hnt
          | error | «break» | «continue» => exact absurd hfr R16WkAcctWs.not_flowingOrResumes_error
          | finalFfi _ => exact absurd hfr R16WkAcctWs.not_flowingOrResumes_finalFfi
          | exception eid ev =>
            exfalso
            have hne : eid ≠ ofString "TrapErr" := by
              rcases hfr with h | h | h | ⟨_, h⟩ | ⟨e', v', h, hne⟩ <;> try simp at h
              obtain ⟨rfl, _⟩ := h; exact hne
            have hbody_ok : R16WkAcctWs.noCatchableRaise R16WkAcctWs.trapOnlyCallees body' = true :=
              R16WkAcctWs.trapOnlyCallees_good (ofString "htab_set") (by decide) values body' callee ret' (by rwa [← hcode])
            have hno := R16WkAcctWs.evaluate_noCatchableRaise R16WkAcctWs.trapOnlyCallees R16WkAcctWs.trapOnlyCallees_good
              body' hbody_ok (callEntryStateHOLFinite s callee) hcode eid ev hne
            rw [hrun] at hno; exact hno rfl
          | returned v =>
            dsimp only at hfr ⊢
            split
            · have hnz_at := FunSpec.at_lookup EvmFrameSpecs.nz_htab_set s hcode values body' callee ret' hl
                (guestInv_callEntry s callee hW.1.1) (by rw [hrun]; simp)
              rw [hrun] at hnz_at
              have ht0_nz : memW s (adw.toNat + 8) ≠ 0 := by
                rw [← hloc_t]; exact hnz_at (Or.inl ⟨v, rfl⟩)
              have hArgWF : HtabArgWF (callEntryStateHOLFinite s callee) := by
                obtain ⟨hAs, S, hT, _⟩ := hW
                have ht0_S := (nonValueSlot_bal_reads s S adw.toNat hT had ht0_nz).1
                refine ⟨localsFree_arenaReady s _ _ hAs, ?_, ?_⟩
                · rw [hloc_t]; exact (htabWF_with_locals s callee (s.clock - 1) _).2 (hT.2.1 _ ht0_S).1
                · rw [hloc_t]; exact fun i hi => ((hT.2.1 _ ht0_S).2 i hi).1
              have hexit := FunSpec.at_lookup htab_set_spec s hcode values body' callee ret' hl
                hArgWF (by rw [hrun]; simp)
              rw [hrun] at hexit
              have hex := hexit v rfl
              dsimp only [HtabExit] at hex
              rw [hloc_t] at hex
              change let t := memW s (adw.toNat + 8)
                let fresh : Ivl := (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")
                ArenaReady post ∧ HtabWF post t ∧ hdr post t 0 = hdr s t 0 ∧ hdr post t 1 = hdr s t 1 ∧
                globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
                (∀ i ∈ htabFootprint post t, Allocated post i ∧
                  ((∃ j ∈ htabFootprint s t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
                FrameOutside s post (htabFootprint s t) fresh ∧
                (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
                  s.globals.lookup k = post.globals.lookup k) at hex
              obtain ⟨hAp, hwf_t0, hh0, _, hhp, hfp_t0, hfr_t0, hg_t0⟩ := hex
              have hstep0 : R16WkAcctWs.WorldStepSc (R16WkAcctWs.bufRegions []) ["heap_ptr"] stdKeep NoExtra s none post :=
                R16WkAcctWs.worldStepSc_of_htabExit_nonValue hW hbe_post hg_t0 hg_t0
                  (fun S hT => nonValueSlot_bal_reads s S adw.toNat hT had ht0_nz)
                  hAp hwf_t0 hh0 hhp hfp_t0 hfr_t0
              exact hstep0.with_locals_clock s.locals post.clock
            · rename_i hbad; simp [hbad] at hfr; exact absurd hfr R16WkAcctWs.not_flowingOrResumes_error

private def addStorageReadTailProg : ProgHOL 64 :=
  .seq
    (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .local (ofString "ad"), .const 8#64]),
       .var .local (ofString "slot"), .const 1#64])
    (.return (.const 0#64))

private theorem add_storage_read_body_worldStep {F : Type}
    (s : PanSemStateFiniteExact 64 F) (addrw slotw : BitVec 64)
    (hW : WorldOK s)
    (hs_addr : s.locals.lookup (ofString "addr") = some (.val (.word addrw)))
    (hs_slot : s.locals.lookup (ofString "slot") = some (.val (.word slotw)))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_storage_read)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_storage_read)).1) :
    WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra
      s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_storage_read)).1
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_storage_read)).2 := by
  have _ := hs_slot
  have hAR0 := hW.1
  have hbody_eq : sourceFnBody Guest.Software.guestFn_add_storage_read =
      .decCall (ofString "ad") .one (ofString "bal_ensure_account")
        [.var .local (ofString "addr")] addStorageReadTailProg := rfl
  rw [hbody_eq] at hnt hres ⊢
  obtain ⟨adw, mid, _, _, _, _, hws1, hW1, had_rec1, _, hmid_ad, _, hnt1, hres1, heq1_r, heq1_s⟩ :=
    decCall_bal_ensure_account_resumes_idx s (ofString "ad") (.var .local (ofString "addr"))
      addrw addStorageReadTailProg hW (by simp [evalHOLExact, hs_addr]) hnt hres
  have hB : R16WkAcctWs.ValidBufList [] := fun _ hp => by cases hp
  have hgw : R16WkAcctWs.SafeStepGlobals ["heap_ptr"] := fun g hg => by
    simp at hg; subst hg; decide
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata mid
    (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .local (ofString "ad"), .const 8#64]),
       .var .local (ofString "slot"), .const 1#64])).1
  have hnt_t := hnt1
  have hfr_t : R16WkAcctWs.FlowingOrResumes (evaluateHOLFiniteState mid addStorageReadTailProg).1 :=
    Or.inr (Or.inr (Or.inr hres1))
  dsimp only [addStorageReadTailProg] at hnt_t hfr_t
  rw [evaluateHOLFiniteState_seq_line780] at hnt_t hfr_t
  rcases hr1 : evaluateHOLFiniteState mid
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .local (ofString "ad"), .const 8#64]),
         .var .local (ofString "slot"), .const 1#64]) with ⟨r1, m2⟩
  simp only [hr1] at hmeta hnt_t hfr_t
  have hstep_tail : R16WkAcctWs.WorldStepSc (R16WkAcctWs.bufRegions []) ["heap_ptr"] stdKeep NoExtra
      mid (evaluateHOLFiniteState mid addStorageReadTailProg).1
      (evaluateHOLFiniteState mid addStorageReadTailProg).2 := by
    dsimp only [addStorageReadTailProg]
    rw [evaluateHOLFiniteState_seq_line780, hr1]
    cases r1 with
    | none =>
      have hs1 := progWStep_call0_htab_set_bal_reads mid adw
        (.var .local (ofString "slot")) (.const 1#64)
        hW1.1.1.code hW1 had_rec1 hmid_ad
        (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
      rw [hr1] at hs1; dsimp only at hs1
      have hW_m2 : WorldOK m2 := hs1.worldOK_bufs hB hW1
      have hs2 := R16WkAcctWs.progWStep_return [] ["heap_ptr"] (.const 0#64)
        m2 (hmeta.trans hW1.1.1.code) hW_m2 hnt_t hfr_t
      exact R16WkAcctWs.WorldStepSc.trans hB hgw hs1 hs2
    | some r =>
      have hs1 := progWStep_call0_htab_set_bal_reads mid adw
        (.var .local (ofString "slot")) (.const 1#64)
        hW1.1.1.code hW1 had_rec1 hmid_ad
        (by rw [hr1]; exact hnt_t) (by rw [hr1]; exact hfr_t)
      rw [hr1] at hs1
      exact hs1
  have hws2 : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra mid
      (evaluateHOLFiniteState mid addStorageReadTailProg).1
      (evaluateHOLFiniteState mid addStorageReadTailProg).2 := hstep_tail.1
  have hws_all : WorldStep (fun _ => []) ["heap_ptr"] stdKeep NoExtra s
      (evaluateHOLFiniteState mid addStorageReadTailProg).1
      (evaluateHOLFiniteState mid addStorageReadTailProg).2 :=
    worldStep_hp_trans hAR0.2 hws1 hws2
  rw [heq1_r, heq1_s]
  exact worldStep_with_locals_right
    (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid addStorageReadTailProg).2.locals
      (ofString "ad", s.locals.lookup (ofString "ad")))
    (evaluateHOLFiniteState mid addStorageReadTailProg).2.clock
    (fun _ _ _ => trivial) hws_all

theorem wk_add_storage_read_impl :
    WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "add_storage_read") := by
  refine ⟨_, _, _, lookup_add_storage_read_add, ?_⟩
  intro F s _ hW hvalid hnt hres
  obtain ⟨values, hlook_fn⟩ := hvalid
  obtain ⟨addrw, slotw, _, hs_addr, hs_slot⟩ :=
    R10Shards.P26_P28.lookupCode_two_words (by decide)
      lookup_add_storage_read_add hlook_fn
  exact add_storage_read_body_worldStep s addrw slotw hW hs_addr hs_slot hnt hres

end InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBal

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalStateInit

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.SoloHtabSet

/-! ## Conditional `DecodeWitnessToMptSpec` and `wk_ws_storage_trie` -/

/-- Entry-weak relational specification for `decode_witness_to_mpt(db, root_hash)`:
only requires `ArenaReady s` and a pre-existing typed `NodeHeap s Nd` below `heap_ptr`
(so both `state_init` — before `ws + 24` / `ws + 32` are initialized — and `ws_storage_trie`
can invoke it). On every `Resumes` outcome (including `MptErr` / `RlpErr`), it preserves
`ArenaReady`, restores `scratch_ptr`, modifies at most `heap_ptr` (monotonically) and
`scratch_ptr` (restored), and writes exclusively to fresh heap `[s.heap_ptr, post.heap_ptr)`.
On normal return, it returns a word `w` extending `Nd` to `Nd'` in fresh heap with `RootIn Nd' w`. -/
def DecodeWitnessToMptSpec (ExtraGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat → Prop) : Prop :=
  FunSpec
    (fun s => ArenaReady s ∧ ExtraGuard s (locN s "db"))
    (fun s r post => Resumes r →
      ArenaReady post ∧
      post.be = s.be ∧
      globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
      globN post "scratch_ptr" = globN s "scratch_ptr" ∧
      GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧
      FrameOutside s post [freeGap s] (heapFree s) ∧
      ∀ Nd, NodeHeap s Nd →
        (∀ o ∈ nodeExtents s Nd, o.2 = 0 ∨ Allocated s o) →
        ∀ v, r = some (.returned v) →
          ∃ (w : BitVec 64) (Nd' : List Nat),
            v = .val (.word w) ∧
            (∀ n ∈ Nd, n ∈ Nd') ∧
            (∀ n ∈ Nd', n ∈ Nd ∨
              (Inside (nodeIvl post n) (globN s "heap_ptr") (globN post "heap_ptr") ∧
               (nodePath post n = (0, 0) ∨
                Inside (nodePath post n) (globN s "heap_ptr") (globN post "heap_ptr")))) ∧
            NodeHeap post Nd' ∧
            RootIn Nd' w.toNat)
    (ofString "decode_witness_to_mpt")

private theorem allocated_disj_free_regions_local {F : Type}
    {s : PanSemStateFiniteExact 64 F} {o : Ivl}
    (hA : ArenaOK s) (ho : Allocated s o) :
    Disj o (freeGap s) ∧ Disj o (heapFree s) := by
  have hsep : heapLimit ≤ scratchStart := by decide
  have hhp : globN s "heap_ptr" ≤ heapLimit := hA.2.1
  have hfm : scratchStart ≤ globN s "frame_mem_ptr" := hA.2.2.1
  have hsc : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hA.2.2.2.1
  rcases ho with ⟨_, hhi⟩ | ⟨hlo, _⟩
  · constructor
    · right; right; left; unfold freeGap; dsimp only; omega
    · right; right; left; unfold heapFree; exact hhi
  · constructor
    · right; right; right; unfold freeGap; dsimp only; omega
    · right; right; right; unfold heapFree; dsimp only; omega

private theorem unhit_p26_of_free_frame_local {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {i : Ivl}
    (hAs : ArenaOK s)
    (hfr : FrameOutside s post [freeGap s] (heapFree s))
    (hpos : i.2 ≠ 0)
    (hal : Allocated s i) :
    R10Shards.P26_P28.IvlUnhit s post i := by
  obtain ⟨hgap, hheap⟩ := allocated_disj_free_regions_local hAs hal
  have hhl8 : heapLimit % 8 = 0 := by decide
  have hhp8 : globN s "heap_ptr" % 8 = 0 := hAs.2.2.2.2.2.1
  have hfm8 : globN s "frame_mem_ptr" % 8 = 0 := hAs.2.2.2.2.2.2.1
  have hsc8 : globN s "scratch_ptr" % 8 = 0 := hAs.2.2.2.2.2.2.2.1
  exact R10Shards.P26_P28.ivlUnhit_of_frameOutside_aligned hpos hfr
    (fun j hj => by
      rw [List.mem_singleton.1 hj]
      unfold freeGap; dsimp only; omega)
    (by unfold heapFree; dsimp only; omega)
    (fun j hj => by rw [List.mem_singleton.1 hj]; exact hgap)
    hheap

private theorem ws32_roleSlot_disj {F : Type}
    (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S)
    (hws_nz : globN s "ws" ≠ 0)
    (ht0_nz : memW s (globN s "ws" + 32) ≠ 0) :
    let t0 := memW s (globN s "ws" + 32)
    t0 ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) := by
  have ht0_S : memW s (globN s "ws" + 32) ∈ S := by
    rcases hT.2.2.2.1 32 (by simp [wsTableSlots]) hws_nz with h0 | hm
    · exact absurd h0 ht0_nz
    · exact hm
  have ht0_wrs : (memW s (globN s "ws" + 32), "ws+32") ∈ worldRoleSlots s := by
    apply mem_worldRoleSlots_recRole s "ws" 32 "ws+32" hws_nz ht0_nz
    apply List.mem_append_left; apply List.mem_append_left
    simp [recRoles, hws_nz]
  have hroles := hT.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨ht0_S, ?_, ?_, ?_, ?_⟩
  · intro hbs h_eq
    have hw_wrs : (memW s (globN s "bs" + 32), "bs+32") ∈ worldRoleSlots s := by
      apply mem_worldRoleSlots_recRole s "bs" 32 "bs+32" hbs (by rw [h_eq]; exact ht0_nz)
      apply List.mem_append_left; apply List.mem_append_right
      simp [recRoles, hbs]
    exact slot_ne_of_diff_nonshared_role hroles hw_wrs ht0_wrs (by decide) h_eq
  · intro hts h_eq
    have hw_wrs : (memW s (globN s "ts" + 32), "ts+32") ∈ worldRoleSlots s := by
      apply mem_worldRoleSlots_recRole s "ts" 32 "ts+32" hts (by rw [h_eq]; exact ht0_nz)
      apply List.mem_append_right
      simp [recRoles, hts]
    exact slot_ne_of_diff_nonshared_role hroles hw_wrs ht0_wrs (by decide) h_eq
  · intro h_eq
    have hba_wrs : (globN s "bal_accounts", "bal_accounts") ∈ worldRoleSlots s := by
      unfold worldRoleSlots
      refine List.mem_filter.2 ⟨?_, by simp [h_eq, ht0_nz]⟩
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_append_right _ (by simp)
    exact slot_ne_of_diff_nonshared_role hroles hba_wrs ht0_wrs (by decide) h_eq
  · intro ad had h_eq
    have had_wrs : (memW s ad, "bal.stor") ∈ worldRoleSlots s := by
      unfold worldRoleSlots
      refine List.mem_filter.2 ⟨?_, by simp [h_eq, ht0_nz]⟩
      exact List.mem_append_right _ (List.mem_flatMap.2 ⟨ad, had, by simp⟩)
    exact slot_ne_of_diff_nonshared_role hroles had_wrs ht0_wrs (by decide) h_eq

private theorem worldStepSc_of_ws32_htabExit_for_Nd {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {S Nd : List Nat} {nodew : BitVec 64}
    (hAs : ArenaReady s) (hAp : ArenaReady post) (hbe : post.be = s.be)
    (hg_nonHeap : ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s.globals.lookup k = post.globals.lookup k)
    (hws_nz : globN s "ws" ≠ 0)
    (ht0_nz : memW s (globN s "ws" + 32) ≠ 0)
    (hwf_t0 : HtabWF post (memW s (globN s "ws" + 32)))
    (hhdr0_t0 : hdr post (memW s (globN s "ws" + 32)) 0 = hdr s (memW s (globN s "ws" + 32)) 0)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hfp_t0 : ∀ i ∈ htabFootprint post (memW s (globN s "ws" + 32)), Allocated post i ∧
      ((∃ j ∈ htabFootprint s (memW s (globN s "ws" + 32)), Inside i j.1 (j.1 + j.2)) ∨
        Inside i (globN s "heap_ptr") (globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr"))))
    (hfr : FrameOutside s post (htabFootprint s (memW s (globN s "ws" + 32)))
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hvalues : WkBal.HtabSetValuesPost s post (memW s (globN s "ws" + 32)) (nodew + 1#64).toNat)
    (hWT : WorldTypedWith s S Nd)
    (hnd_root : RootIn Nd nodew.toNat) :
    WorldTypedWith post S Nd ∧
    OwnedGrows s post (worldOwned s S Nd) (worldOwned post S Nd) ∧
    FrameOutside s post (worldOwned s S Nd ++ R16WkAcctWs.bufRegions [] s ++ [freeGap s]) (heapFree s) := by
  set t0 := memW s (globN s "ws" + 32)
  have hsp_eq : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    globN_eq_of_lookup (hg_nonHeap (ofString "scratch_ptr") (by decide))
  have hag : AllocatorGrows s post := ⟨hhp, by rw [hsp_eq]⟩
  have hcore : ∀ g ∈ R10Shards.P26_P28.coreWorldGlobals, globN post g = globN s g := fun g hg => by
    have hne : ofString g ∉ (["heap_ptr"] : List String).map ofString := by revert g hg; decide
    exact globN_eq_of_lookup (hg_nonHeap (ofString g) hne)
  have hbuf_same : R10Shards.P26_P28.FreshBufsOK s post := by
    refine ⟨fun gn hgn => Or.inl ?_, List.pairwise_iff_getElem.2 fun i j _ _ _ ha _ => absurd ?_ ha.1⟩
    · have hne : ofString gn.1 ∉ (["heap_ptr"] : List String).map ofString := by revert gn hgn; decide
      exact globN_eq_of_lookup (hg_nonHeap (ofString gn.1) hne)
    · have hgm := List.getElem_mem ‹i < globalBuffers.length›
      have hne : ofString globalBuffers[i].1 ∉ (["heap_ptr"] : List String).map ofString := by
        revert hgm; generalize globalBuffers[i] = gp; intro hgm; revert gp hgm; decide
      exact globN_eq_of_lookup (hg_nonHeap (ofString globalBuffers[i].1) hne)
  have hf_al : (globN s "heap_ptr") % 8 = 0 ∧ (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
    have h1 := hAs.2.2.2.2.2.2.1
    have h2 := hAp.2.2.2.2.2.2.1
    omega
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  obtain ⟨ht0_S, hno_bs32, hno_ts32, hno_ba, hno_ad⟩ := ws32_roleSlot_disj s S hT hws_nz ht0_nz
  have ht0_al : ∀ j ∈ htabFootprint s t0, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
    have hw := ((hT.2.1 t0 ht0_S).1.1 j hj).2
    exact ⟨hw.1, hw.2.1⟩
  have hunhit_disj : ∀ i : Ivl, i.2 ≠ 0 → (∀ j ∈ htabFootprint s t0, Disj i j) →
      Allocated s i → R10Shards.P26_P28.IvlUnhit s post i := fun i hipos hdi hal =>
    R10Shards.P26_P28.ivlUnhit_of_frameOutside_aligned hipos hfr ht0_al hf_al hdi
      (R16WkAcctWs.disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (Or.inr hal))
  have hu_other : ∀ u ∈ S, u ≠ t0 → ∀ i ∈ htabFootprint s u, R10Shards.P26_P28.IvlUnhit s post i := fun u hu hne i hi =>
    hunhit_disj i (R16WkAcctWs.htabFootprint_len_pos (hT.2.1 u hu).1 hi)
      (fun j hj => hT.2.2.1 u hu t0 ht0_S hne i hi j hj)
      (((hT.2.1 u hu).2 i hi).1)
  have hu_fix : ∀ i ∈ fixedObjects s, i.2 ≠ 0 → R10Shards.P26_P28.IvlUnhit s post i := fun i hi hipos =>
    hunhit_disj i hipos (fun j hj => (((hT.2.1 t0 ht0_S).2 j hj).2 i hi).flip)
      (by
        rcases hF.1 i hi with h0 | ⟨hal, _⟩
        · exact absurd h0 hipos
        · exact hal)
  have hu_nd_rec : ∀ n ∈ Nd, R10Shards.P26_P28.IvlUnhit s post (nodeIvl s n) := fun n hn => by
    have hmem : nodeIvl s n ∈ nodeExtents s Nd := by
      unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩
    have hpos : (nodeIvl s n).2 ≠ 0 := by
      dsimp [nodeIvl]; unfold nodeSize; split_ifs <;> decide
    exact hunhit_disj _ hpos (fun j hj => (hTr.2.1 _ hmem).1 t0 ht0_S j hj)
      ((hTr.1.1 n hn).2.1)
  have hu_nd_byte : ∀ n ∈ Nd, (memW s n = 1 ∨ memW s n = 2) → memW s (n + 40) ≠ 0 →
      ∀ k, k < memW s (n + 40) → memB post (memW s (n + 32) + k) = memB s (memW s (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    have h264 : heapLimit ≤ 2 ^ 64 := by decide
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, hin_p, _⟩
    · exact absurd h0 hlen0
    · have hp_ne : (memW s (n + 32), memW s (n + 40)) ∈ nodeExtents s Nd := by
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
      have ha_lt : memW s (n + 32) + k < 2 ^ 64 := by have := hin_p.2; omega
      let c := panByteAlignHOL (BitVec.ofNat 64 (memW s (n + 32) + k))
      have hc_nat : c.toNat = (memW s (n + 32) + k) / 8 * 8 := by
        rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
      have hmem := hfr c
        (fun j hj hcj => by
          obtain ⟨h1, h2⟩ := hcj
          rw [hc_nat] at h1 h2
          have hj_al := ((hT.2.1 t0 ht0_S).1.1 j hj).2
          have hj1 := hj_al.1; have hj2 := hj_al.2.1
          have hdj := (hTr.2.1 _ hp_ne).1 t0 ht0_S j hj
          rcases hdj with d | d | d | d <;> omega)
        (fun hcf => by
          obtain ⟨h1, h2⟩ := hcf
          dsimp at h1 h2
          rw [hc_nat] at h1 h2
          have hp_hp8 : (globN post "heap_ptr") % 8 = 0 := hAp.2.2.2.2.2.2.1
          have hdj := R16WkAcctWs.disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (Or.inr hal_p)
          try dsimp at hdj
          rcases hdj with d | d | d | d <;> omega)
      unfold memB
      change (match post.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v post.be).toNat) =
             (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 (memW s (n + 32) + k)) v s.be).toNat)
      rw [hmem, hbe]
  have hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    have hlow : ∀ a : Nat, a + 8 ≤ sourceBase → memW post a = memW s a := fun a ha => by
      have hsb_lt : sourceBase < 2 ^ 64 := by decide
      have ha_lt : a < 2 ^ 64 := lt_of_le_of_lt (by omega) hsb_lt
      have hm := hfr (BitVec.ofNat 64 a)
        (fun j hj hcj => by
          obtain ⟨h1, _⟩ := hcj
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have hlo := ((hT.2.1 t0 ht0_S).1.1 j hj).1.1
          omega)
        (fun hcf => by
          obtain ⟨h1, _⟩ := hcf
          dsimp at h1
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have hlo := hAs.2.1
          omega)
      unfold memW; rw [hm]
    exact ⟨hlow 0 (by decide), hlow 8 (by decide), hlow 16 (by decide)⟩
  have hu_ws : globN s "ws" ≠ 0 → R10Shards.P26_P28.IvlUnhit s post (globN s "ws", 40) := fun hnz => by
    have hm := R10Shards.P26_P28.typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by decide)
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_bs : globN s "bs" ≠ 0 → R10Shards.P26_P28.IvlUnhit s post (globN s "bs", 80) := fun hnz => by
    have hm := R10Shards.P26_P28.typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by decide)
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_ts : globN s "ts" ≠ 0 → R10Shards.P26_P28.IvlUnhit s post (globN s "ts", 72) := fun hnz => by
    have hm := R10Shards.P26_P28.typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by decide)
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_bo : globN s "bo" ≠ 0 → R10Shards.P26_P28.IvlUnhit s post (globN s "bo", 88) := fun hnz => by
    have hm := R10Shards.P26_P28.typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_jr : globN s "journal_cap" ≠ 0 → R10Shards.P26_P28.IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := fun hnz => by
    apply hu_fix _ _ (by dsimp only; omega)
    unfold fixedObjects
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
    simp [hnz]
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → R10Shards.P26_P28.IvlUnhit s post i := fun i hi h24 =>
    hu_fix i (by unfold fixedObjects; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hi)))) (by omega)
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → R10Shards.P26_P28.IvlUnhit s post i := fun i hi hipos =>
    hu_fix i (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)) hipos
  have hbo_eq := R10Shards.P26_P28.blockOutObjects_eq_of_bo_unhit hAs.2 hF (hcore "bo" (by decide))
    hT.2.2.2.2.2.2.2.2.2.2.1 hu_bo hu_bo_lst
  have hbal_eq := R16WkAcctWs.balObjects_eq_of_unhit_except hAs.2 hT hF
    (hcore "bal_accounts" (by decide)) hu_other ⟨hno_ba, hno_ad⟩ hu_bal hm0
  obtain ⟨hF_post, _⟩ := R10Shards.P26_P28.fixedTyped_of_freshBufsOK hAs hAp hag hF
    (hcore "journal" (by decide)) (hcore "journal_cap" (by decide)) hbo_eq.1 hbal_eq.1 hbuf_same
  have hfix_eq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [hbo_eq.1, hbal_eq.1, hcore "journal" (by decide), hcore "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ∉ (["heap_ptr"] : List String).map ofString := by revert gn hgn; decide
    have hg_eq : globN post gn.1 = globN s gn.1 := globN_eq_of_lookup (hg_nonHeap (ofString gn.1) hne)
    simp [hg_eq]
  obtain ⟨hjr_eq, hJ_post⟩ := R10Shards.P26_P28.journalRoleSlots_eq_of_unhit
    hAs.1 hAp.1 hAs.2 hag (fun _ hx => hx) hJ hF hcore hu_ts hu_jr
  have hwrs_eq := R16WkAcctWs.worldRoleSlots_eq_of_unhit_except hAs.2 hT hF hcore hu_other
    ⟨hno_bs32, hno_ts32, hno_ba, hno_ad⟩ hu_ws hu_bs hu_ts hu_bal hm0
  obtain ⟨hNH_post, hne_eq⟩ := R10Shards.P26_P28.nodeHeap_congr_bytes
    hAs.1 hAp.1 hag hTr.1 hu_nd_rec hu_nd_byte
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hother_fp : ∀ u ∈ S, u ≠ t0 →
      (∀ k, k < 11 → hdr post u k = hdr s u k) ∧ htabFootprint post u = htabFootprint s u := by
    intro u hu hne
    have hfp := (hT.2.1 u hu).1.1
    have ht_fp : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
    exact R10Shards.P26_P28.htabFootprint_eq_of_hdr_unhit ((hfp _ ht_fp).2.1)
      (by have := (hfp _ ht_fp).1.2; dsimp at this; omega) (hu_other u hu hne _ ht_fp)
  have ht0_disj_other : ∀ i ∈ htabFootprint post t0,
      (∀ u ∈ S, u ≠ t0 → ∀ j ∈ htabFootprint s u, Disj i j) ∧
      (∀ j ∈ fixedObjects s, Disj i j) ∧
      (∀ o ∈ nodeExtents s Nd, Disj i o) := by
    intro i hi
    rcases (hfp_t0 i hi).2 with ⟨k, hk, hin⟩ | hfresh
    · refine ⟨fun u hu hne j hj => R10Shards.P26_P28.disj_of_inside_left hin (hT.2.2.1 t0 ht0_S u hu hne.symm k hk j hj),
              fun j hj => R10Shards.P26_P28.disj_of_inside_left hin (((hT.2.1 t0 ht0_S).2 k hk).2 j hj),
              fun o ho => R10Shards.P26_P28.disj_of_inside_left hin ((hTr.2.1 o ho).1 t0 ht0_S k hk).flip⟩
    · refine ⟨fun u hu _ j hj => (R10Shards.P26_P28.disj_of_inside_right hfresh
                (R16WkAcctWs.disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (Or.inr ((hT.2.1 u hu).2 j hj).1))).flip,
              fun j hj => (R10Shards.P26_P28.disj_of_inside_right hfresh
                (R16WkAcctWs.disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp
                  (by rcases hF.1 j hj with h0 | ⟨hal, _⟩; exact Or.inl h0; exact Or.inr hal))).flip,
              fun o ho => (R10Shards.P26_P28.disj_of_inside_right hfresh
                (R16WkAcctWs.disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (by
                  unfold nodeExtents at ho
                  obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
                  rcases hno with rfl | rfl
                  · exact Or.inr (hTr.1.1 n hn).2.1
                  · unfold nodePath; split_ifs with hc
                    · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hc.1 with h0 | ⟨_, hal, _⟩
                      · exact absurd h0 hc.2
                      · exact Or.inr hal
                    · exact Or.inl rfl))).flip⟩
  have hT_post : TablesTyped post S := by
    have hT0 := hT
    obtain ⟨hnd, htwf, htpw, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, _, hroles⟩ := hT
    have ews := hcore "ws" (by decide)
    have ebs := hcore "bs" (by decide)
    have ets := hcore "ts" (by decide)
    refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_eq.2, ?_⟩
    · intro u hu
      by_cases heq : u = t0
      · subst heq; rw [hfix_eq]
        exact ⟨hwf_t0, fun i hi => ⟨(hfp_t0 i hi).1, (ht0_disj_other i hi).2.1⟩⟩
      · rw [(hother_fp u hu heq).2, hfix_eq]
        exact ⟨R10Shards.P26_P28.htabWF_congr_unhit hAs.1 hAp.1 (htwf u hu).1 (hu_other u hu heq),
          fun i hi => ⟨hag.allocated ((htwf u hu).2 i hi).1, ((htwf u hu).2 i hi).2⟩⟩
    · intro u hu v hv hne i hi j hj
      by_cases hu0 : u = t0
      · subst hu0; rw [(hother_fp v hv hne.symm).2] at hj
        exact (ht0_disj_other i hi).1 v hv hne.symm j hj
      · by_cases hv0 : v = t0
        · subst hv0; rw [(hother_fp u hu hu0).2] at hi
          exact ((ht0_disj_other j hj).1 u hu hu0 i hi).flip
        · rw [(hother_fp u hu hu0).2] at hi; rw [(hother_fp v hv hv0).2] at hj
          exact htpw u hu v hv hne i hi j hj
    · intro k hk hnz
      rw [ews] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [R10Shards.P26_P28.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by decide) ews hnz (hu_ws hnz) hk8.1 hk8.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [ebs] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [R10Shards.P26_P28.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by decide) ebs hnz (hu_bs hnz) hk8.1 hk8.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [ets] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [R10Shards.P26_P28.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by decide) ets hnz (hu_ts hnz) hk8.1 hk8.2]
      exact htsR k hk hnz
    · intro g hg_mem; rw [hcore g (by simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg_mem; rcases hg_mem with rfl | rfl | rfl <;> decide)]; exact hgR g hg_mem
    · intro hnz hmem
      rw [ebs] at hnz
      have ew := R10Shards.P26_P28.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by decide) ebs hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact R10Shards.P26_P28.htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_other _ hmem (hno_bs32 hnz)) (fun _ hx => hx) (hbsN hnz hmem)
    · intro hnz hmem
      rw [ets] at hnz
      have ew := R10Shards.P26_P28.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by decide) ets hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact R10Shards.P26_P28.htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_other _ hmem (hno_ts32 hnz)) (fun _ hx => hx) (htsN hnz hmem)
    · intro ad had
      have had_s : ad ∈ balRecords s := by
        rwa [R10Shards.P26_P28.balRecords_eq_of_unhit hT0 (hcore "bal_accounts" (by decide)) (fun hnz => by
          rcases hgR "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
          · exact absurd h0 hnz
          · exact hu_other _ hm hno_ba)] at had
      obtain ⟨e0, e8, _, hkl, hll⟩ := hbal_eq.2 ad had
      exact ⟨e0 ▸ (hbalT ad had_s).1, e8 ▸ (hbalT ad had_s).2.1, hkl, hll⟩
    · unfold RolesOK at hroles ⊢
      rw [hwrs_eq, hjr_eq]
      refine ⟨fun a ha => ?_, hroles.2⟩
      obtain ⟨haS, hkl⟩ := hroles.1 a ha
      by_cases ha0 : a.1 = t0
      · rw [ha0] at hkl ⊢; exact ⟨ht0_S, hhdr0_t0.trans hkl⟩
      · exact ⟨haS, ((hother_fp a.1 haS ha0).1 0 (by omega)).trans hkl⟩
  have hTr_post : TriesTypedWith post S Nd := by
    have ews := hcore "ws" (by decide)
    refine ⟨hNH_post, ?_, ?_⟩
    · rw [hne_eq, hfix_eq]
      intro o ho
      refine ⟨fun u hu i hi => ?_, (hTr.2.1 o ho).2⟩
      by_cases hu0 : u = t0
      · subst hu0; exact ((ht0_disj_other i hi).2.2 o ho).flip
      · rw [(hother_fp u hu hu0).2] at hi; exact (hTr.2.1 o ho).1 u hu i hi
    · intro hws_nz_p
      rw [ews] at hws_nz_p
      have e24 := R10Shards.P26_P28.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by decide) ews hws_nz_p (hu_ws hws_nz_p) (k := 24) (by omega) (by omega)
      have e32 := R10Shards.P26_P28.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by decide) ews hws_nz_p (hu_ws hws_nz_p) (k := 32) (by omega) (by omega)
      rw [e24, e32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hws_nz_p
      refine ⟨hr24, fun htS i hi => ?_⟩
      set v_i := nodeF post (hdr post t0 5) (memW post (hdr post t0 6 + 8 * i)) 8
      have hvi_mem : v_i ∈ htabValues post t0 := by
        unfold htabValues
        exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
      rcases WkBal.htabSetValuesPost_mem hvalues hvi_mem with hold | hnew
      · unfold htabValues at hold
        obtain ⟨j, hj_rng, hj_eq⟩ := List.mem_map.1 hold
        rw [← hj_eq]
        exact hr32 htS j (List.mem_range.1 hj_rng)
      · have hnw_lt : nodew.toNat < 2 ^ 64 - 1 := by
          have hlim : heapLimit < 2 ^ 64 - 1 := by decide
          rcases hnd_root with h0 | hn_mem
          · omega
          · have hin := (hTr.1.1 _ hn_mem).2.2.1
            have hsz : 32 ≤ nodeSize (memW s nodew.toNat) := by unfold nodeSize; split_ifs <;> omega
            dsimp [nodeIvl, Inside] at hin
            omega
        have hadd1 : (nodew + 1#64).toNat = nodew.toNat + 1 := by
          rw [BitVec.toNat_add]
          change (nodew.toNat + 1) % 2 ^ 64 = nodew.toNat + 1
          exact Nat.mod_eq_of_lt (by omega)
        rw [hnew, hadd1, Nat.add_sub_cancel]
        exact hnd_root
  refine ⟨⟨hT_post, hJ_post, hF_post, hTr_post⟩, ?_, ?_⟩
  · intro o ho
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with ho12 | ho_nd
    · rcases List.mem_append.1 ho12 with ho_tab | ho_fix
      · obtain ⟨u, hu, hi⟩ := List.mem_flatMap.1 ho_tab
        by_cases hu0 : u = t0
        · subst hu0
          rcases (hfp_t0 o hi).2 with ⟨j, hj, hin⟩ | hfresh
          · refine Or.inr (Or.inl ⟨j, ?_, hin⟩)
            unfold worldOwned
            exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t0, hu, hj⟩))
          · exact Or.inr (Or.inr ⟨hfresh.1, by have := hfresh.2; omega⟩)
        · rw [(hother_fp u hu hu0).2] at hi
          refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
          unfold worldOwned
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u, hu, hi⟩))
      · rw [hfix_eq] at ho_fix
        refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
        unfold worldOwned
        exact List.mem_append_left _ (List.mem_append_right _ ho_fix)
    · rw [hne_eq] at ho_nd
      refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
      unfold worldOwned
      exact List.mem_append_right _ ho_nd
  · intro a hkeep hnot_hf
    apply hfr a
    · intro j hj
      apply hkeep j
      apply List.mem_append_left; apply List.mem_append_left
      unfold worldOwned
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t0, ht0_S, hj⟩))
    · intro hcf
      obtain ⟨h1, h2⟩ := hcf
      apply hnot_hf
      unfold heapFree CellHits at *
      dsimp at h1 h2 ⊢
      have := hAp.2.2.1
      omega

private theorem worldStepSc_of_decode_witness_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hW0 : WorldOK s)
    (hAp : ArenaReady post)
    (hbe : post.be = s.be)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsp : globN post "scratch_ptr" = globN s "scratch_ptr")
    (hgk : GlobalsKept ["heap_ptr", "scratch_ptr"] s post)
    (hfr : FrameOutside s post [freeGap s] (heapFree s))
    (hext : ∀ Nd, NodeHeap s Nd →
      (∀ o ∈ nodeExtents s Nd, o.2 = 0 ∨ Allocated s o) →
      ∃ Nd', (∀ n ∈ Nd, n ∈ Nd') ∧
        (∀ n ∈ Nd', n ∈ Nd ∨
          (Inside (nodeIvl post n) (globN s "heap_ptr") (globN post "heap_ptr") ∧
           (nodePath post n = (0, 0) ∨
            Inside (nodePath post n) (globN s "heap_ptr") (globN post "heap_ptr")))) ∧
        NodeHeap post Nd' ∧
        (∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat)) :
    R16WkAcctWs.WorldStepSc (R16WkAcctWs.bufRegions []) ["heap_ptr", "scratch_ptr"] stdKeep
      (fun _ r' _ _ Nd' => ∀ v, r' = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat)
      s r post := by
  have hAs := hW0.1
  have hag : AllocatorGrows s post := ⟨hhp, by rw [hsp]⟩
  have hcore : ∀ g ∈ R10Shards.P26_P28.coreWorldGlobals, globN post g = globN s g := fun g hg => by
    have hne : ofString g ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString := by revert g hg; decide
    exact globN_eq_of_lookup (hgk (ofString g) hne)
  have hbuf_same : R10Shards.P26_P28.FreshBufsOK s post := by
    refine ⟨fun gn hgn => Or.inl ?_, List.pairwise_iff_getElem.2 fun i j _ _ _ ha _ => absurd ?_ ha.1⟩
    · have hne : ofString gn.1 ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString := by revert gn hgn; decide
      exact globN_eq_of_lookup (hgk (ofString gn.1) hne)
    · have hgm := List.getElem_mem ‹i < globalBuffers.length›
      have hne : ofString globalBuffers[i].1 ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString := by
        revert hgm; generalize globalBuffers[i] = gp; intro hgm; revert gp hgm; decide
      exact globN_eq_of_lookup (hgk (ofString globalBuffers[i].1) hne)
  have hf_al : (globN s "heap_ptr") % 8 = 0 ∧ (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
    have h1 := hAs.2.2.2.2.2.2.1
    have h2 := hAp.2.2.2.2.2.2.1
    omega
  have hunhit_alloc : ∀ i : Ivl, i.2 ≠ 0 → Allocated s i → R10Shards.P26_P28.IvlUnhit s post i :=
    fun _ hipos hal => unhit_p26_of_free_frame_local hAs.2 hfr hipos hal
  obtain ⟨S0, hWT0_ex⟩ := hW0.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  have hrk : RecordsKept (R16WkAcctWs.bufRegions []) stdKeep s post := by
    intro rec hrec hgnz k hk _
    have hrec_sz : ∃ sz, (rec.1, sz) ∈ typedRecords ∧ sz ≠ 0 ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      dsimp only [stdKeep] at hrec
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨80, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨72, by decide, by decide, ?_⟩; simp at hk; omega
      · refine ⟨88, by decide, by decide, ?_⟩; simp at hk; omega
    obtain ⟨sz, htr, hsz_nz, hk8, hksz⟩ := hrec_sz
    have hmf := R10Shards.P26_P28.typedRecord_mem_fixedObjects s htr
    simp only [hgnz, ↓reduceIte] at hmf
    rcases hWT0.2.2.1.1 _ hmf with h0 | ⟨hal, hwords⟩
    · omega
    · have hhi := (ivl_allocated_bound hAs.2 hal).2
      have hg8 : (globN s rec.1) % 8 = 0 := hwords.1
      exact R10Shards.P26_P28.memW_eq_of_ivlUnhit (hunhit_alloc _ hsz_nz hal) (by omega) hhi ⟨by omega, by omega⟩
  refine ⟨⟨hAp, hhp, hgk, hrk, fun S Nd hWT _ => ?_⟩, by rw [hsp]⟩
  obtain ⟨hT, hJ, hF, hTr⟩ := hWT
  have hnd_alloc : ∀ o ∈ nodeExtents s Nd, o.2 = 0 ∨ Allocated s o := by
    intro o ho
    unfold nodeExtents at ho
    obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
    rcases hno with rfl | rfl
    · exact Or.inr (hTr.1.1 n hn).2.1
    · unfold nodePath; split_ifs with hc
      · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hc.1 with h0 | ⟨_, hal, _⟩
        · exact absurd h0 hc.2
        · exact Or.inr hal
      · exact Or.inl rfl
  obtain ⟨Nd', hNd_sub, hNd_cls, hNH_post, hQ_post⟩ := hext Nd hTr.1 hnd_alloc
  have hu_all : ∀ u ∈ S, ∀ i ∈ htabFootprint s u, R10Shards.P26_P28.IvlUnhit s post i := fun u hu i hi =>
    hunhit_alloc i (R16WkAcctWs.htabFootprint_len_pos (hT.2.1 u hu).1 hi) (((hT.2.1 u hu).2 i hi).1)
  have hu_fix : ∀ i ∈ fixedObjects s, i.2 ≠ 0 → R10Shards.P26_P28.IvlUnhit s post i := fun i hi hipos =>
    hunhit_alloc i hipos (by
      rcases hF.1 i hi with h0 | ⟨hal, _⟩
      · exact absurd h0 hipos
      · exact hal)
  have hm0 : memW post 0 = memW s 0 ∧ memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    have hlow : ∀ a : Nat, a + 8 ≤ sourceBase → memW post a = memW s a := fun a ha => by
      have hsb_lt : sourceBase < 2 ^ 64 := by decide
      have ha_lt : a < 2 ^ 64 := lt_of_le_of_lt (by omega) hsb_lt
      have hm := hfr (BitVec.ofNat 64 a)
        (fun j hj hcj => by
          rw [List.mem_singleton.1 hj] at hcj
          obtain ⟨h1, _⟩ := hcj
          unfold freeGap at h1; dsimp at h1
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have h1' := hAs.2.1; have h2' := hAs.2.2.1; have h3' := hAs.2.2.2.1
          have hsep : heapLimit ≤ scratchStart := by decide
          omega)
        (fun hcf => by
          obtain ⟨h1, _⟩ := hcf
          unfold heapFree at h1; dsimp at h1
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at h1
          have hlo := hAs.2.1
          omega)
      unfold memW; rw [hm]
    exact ⟨hlow 0 (by decide), hlow 8 (by decide), hlow 16 (by decide)⟩
  have hu_ws : globN s "ws" ≠ 0 → R10Shards.P26_P28.IvlUnhit s post (globN s "ws", 40) := fun hnz => by
    have hm := R10Shards.P26_P28.typedRecord_mem_fixedObjects s (r := ("ws", 40)) (by decide)
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_bs : globN s "bs" ≠ 0 → R10Shards.P26_P28.IvlUnhit s post (globN s "bs", 80) := fun hnz => by
    have hm := R10Shards.P26_P28.typedRecord_mem_fixedObjects s (r := ("bs", 80)) (by decide)
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_ts : globN s "ts" ≠ 0 → R10Shards.P26_P28.IvlUnhit s post (globN s "ts", 72) := fun hnz => by
    have hm := R10Shards.P26_P28.typedRecord_mem_fixedObjects s (r := ("ts", 72)) (by decide)
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_bo : globN s "bo" ≠ 0 → R10Shards.P26_P28.IvlUnhit s post (globN s "bo", 88) := fun hnz => by
    have hm := R10Shards.P26_P28.typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
    simp only [hnz, ↓reduceIte] at hm; exact hu_fix _ hm (by dsimp only; omega)
  have hu_jr : globN s "journal_cap" ≠ 0 → R10Shards.P26_P28.IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := fun hnz => by
    apply hu_fix _ _ (by dsimp only; omega)
    unfold fixedObjects
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
    simp [hnz]
  have hu_bo_lst : ∀ i ∈ blockOutObjects s, i.2 = 24 → R10Shards.P26_P28.IvlUnhit s post i := fun i hi h24 =>
    hu_fix i (by unfold fixedObjects; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hi)))) (by omega)
  have hu_bal : ∀ i ∈ balObjects s, i.2 ≠ 0 → R10Shards.P26_P28.IvlUnhit s post i := fun i hi hipos =>
    hu_fix i (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)) hipos
  have hbo_eq := R10Shards.P26_P28.blockOutObjects_eq_of_bo_unhit hAs.2 hF (hcore "bo" (by decide))
    hT.2.2.2.2.2.2.2.2.2.2.1 hu_bo hu_bo_lst
  have h0_not_S : 0 ∉ S := fun h0 => by
    have hlo := (((hT.2.1 0 h0).1.1 (0, 88) (by simp [htabFootprint])).1).1
    have hsb : 0 < sourceBase := by decide
    omega
  have hu_other1 : ∀ u ∈ S, u ≠ 1 → ∀ i ∈ htabFootprint s u, R10Shards.P26_P28.IvlUnhit s post i :=
    fun u hu _ i hi => hu_all u hu i hi
  have h1_not_S : 1 ∉ S := fun h1 => by
    have hlo := (((hT.2.1 1 h1).1.1 (1, 88) (by simp [htabFootprint])).1).1
    have hsb : 1 < sourceBase := by decide
    omega
  have h1_not_ba : globN s "bal_accounts" ≠ 1 := by
    intro h1
    rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
    · omega
    · rw [h1] at hm; exact h1_not_S hm
  have h1_not_ad : ∀ ad ∈ balRecords s, memW s ad ≠ 1 := fun ad had h1 => by
    have hm := (hT.2.2.2.2.2.2.2.2.2.1 ad had).1
    rw [h1] at hm; exact h1_not_S hm
  have h1_not_bs32 : globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ 1 := fun hnz h1 => by
    rcases hT.2.2.2.2.1 32 (by simp [bsTableSlots]) hnz with h0 | hm
    · omega
    · rw [h1] at hm; exact h1_not_S hm
  have h1_not_ts32 : globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ 1 := fun hnz h1 => by
    rcases hT.2.2.2.2.2.1 32 (by simp [tsTableSlots]) hnz with h0 | hm
    · omega
    · rw [h1] at hm; exact h1_not_S hm
  have hbal_eq := R16WkAcctWs.balObjects_eq_of_unhit_except (t0 := 1) hAs.2 hT hF
    (hcore "bal_accounts" (by decide)) hu_other1 ⟨h1_not_ba, h1_not_ad⟩ hu_bal hm0
  obtain ⟨hF_post, _⟩ := R10Shards.P26_P28.fixedTyped_of_freshBufsOK hAs hAp hag hF
    (hcore "journal" (by decide)) (hcore "journal_cap" (by decide)) hbo_eq.1 hbal_eq.1 hbuf_same
  have hfix_eq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [hbo_eq.1, hbal_eq.1, hcore "journal" (by decide), hcore "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString := by revert gn hgn; decide
    have hg_eq : globN post gn.1 = globN s gn.1 := globN_eq_of_lookup (hgk (ofString gn.1) hne)
    simp [hg_eq]
  obtain ⟨hjr_eq, hJ_post⟩ := R10Shards.P26_P28.journalRoleSlots_eq_of_unhit
    hAs.1 hAp.1 hAs.2 hag (fun _ hx => hx) hJ hF hcore hu_ts hu_jr
  have hwrs_eq := R16WkAcctWs.worldRoleSlots_eq_of_unhit_except (t0 := 1) hAs.2 hT hF hcore hu_other1
    ⟨h1_not_bs32, h1_not_ts32, h1_not_ba, h1_not_ad⟩ hu_ws hu_bs hu_ts hu_bal hm0
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  have hall_fp : ∀ u ∈ S,
      (∀ k, k < 11 → hdr post u k = hdr s u k) ∧ htabFootprint post u = htabFootprint s u := by
    intro u hu
    have hfp := (hT.2.1 u hu).1.1
    have ht_fp : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
    exact R10Shards.P26_P28.htabFootprint_eq_of_hdr_unhit ((hfp _ ht_fp).2.1)
      (by have := (hfp _ ht_fp).1.2; dsimp at this; omega) (hu_all u hu _ ht_fp)
  have hT_post : TablesTyped post S := by
    have hT0 := hT
    obtain ⟨hnd, htwf, htpw, hwsR, hbsR, htsR, hgR, hbsN, htsN, hbalT, _, hroles⟩ := hT
    have ews := hcore "ws" (by decide)
    have ebs := hcore "bs" (by decide)
    have ets := hcore "ts" (by decide)
    refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_eq.2, ?_⟩
    · intro u hu
      rw [(hall_fp u hu).2, hfix_eq]
      exact ⟨htabWF_congr_unhit hAs.1 hAp.1 (htwf u hu).1 (hu_all u hu),
        fun i hi => ⟨hag.allocated ((htwf u hu).2 i hi).1, ((htwf u hu).2 i hi).2⟩⟩
    · intro u hu v hv hne i hi j hj
      rw [(hall_fp u hu).2] at hi; rw [(hall_fp v hv).2] at hj
      exact htpw u hu v hv hne i hi j hj
    · intro k hk hnz
      rw [ews] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      rw [R10Shards.P26_P28.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by simp [typedRecords]) ews hnz (hu_ws hnz) hk8.1 hk8.2]
      exact hwsR k hk hnz
    · intro k hk hnz
      rw [ebs] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [R10Shards.P26_P28.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) ebs hnz (hu_bs hnz) hk8.1 hk8.2]
      exact hbsR k hk hnz
    · intro k hk hnz
      rw [ets] at hnz
      have hk8 : k % 8 = 0 ∧ k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [R10Shards.P26_P28.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) ets hnz (hu_ts hnz) hk8.1 hk8.2]
      exact htsR k hk hnz
    · intro g hg_mem
      rw [hcore g (by simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg_mem; rcases hg_mem with rfl | rfl | rfl <;> decide)]
      exact hgR g hg_mem
    · intro hnz hmem
      rw [ebs] at hnz
      have ew := R10Shards.P26_P28.rec_word_eq_of_unhit hAs.2 hF "bs" 80 (by simp [typedRecords]) ebs hnz (hu_bs hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_all _ hmem) (fun _ hx => hx) (hbsN hnz hmem)
    · intro hnz hmem
      rw [ets] at hnz
      have ew := R10Shards.P26_P28.rec_word_eq_of_unhit hAs.2 hF "ts" 72 (by simp [typedRecords]) ets hnz (hu_ts hnz) (k := 32) (by omega) (by omega)
      rw [ew] at hmem ⊢
      exact htabValuesIn_congr_unhit (htwf _ hmem).1 (hu_all _ hmem) (fun _ hx => hx) (htsN hnz hmem)
    · intro ad had
      have had_s : ad ∈ balRecords s := by
        rwa [R10Shards.P26_P28.balRecords_eq_of_unhit hT0 (hcore "bal_accounts" (by decide)) (fun hnz => by
          rcases hgR "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
          · exact absurd h0 hnz
          · exact hu_all _ hm)] at had
      obtain ⟨e0, e8, _, hkl, hll⟩ := hbal_eq.2 ad had
      exact ⟨e0 ▸ (hbalT ad had_s).1, e8 ▸ (hbalT ad had_s).2.1, hkl, hll⟩
    · unfold RolesOK at hroles ⊢
      rw [hwrs_eq, hjr_eq]
      refine ⟨fun a ha => ?_, hroles.2⟩
      obtain ⟨haS, hkl⟩ := hroles.1 a ha
      exact ⟨haS, ((hall_fp a.1 haS).1 0 (by omega)).trans hkl⟩
  have hold_ivl_eq : ∀ n ∈ Nd, nodeIvl post n = nodeIvl s n ∧ nodePath post n = nodePath s n := by
    intro n hn
    have hpos : (nodeIvl s n).2 ≠ 0 := by
      dsimp [nodeIvl]; unfold nodeSize; split_ifs <;> decide
    have hu_n : R10Shards.P26_P28.IvlUnhit s post (n, nodeSize (memW s n)) :=
      hunhit_alloc _ hpos ((hTr.1.1 n hn).2.1)
    have hn8 : n % 8 = 0 := (hTr.1.1 n hn).2.2.2.1.1
    have hhi_n : n + nodeSize (memW s n) ≤ 2 ^ 64 := (ivl_allocated_bound hAs.2 (hTr.1.1 n hn).2.1).2
    have hsz32 : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
    have hw0 : memW post n = memW s n :=
      memW_eq_of_ivlUnhit hu_n hn8 hhi_n ⟨by dsimp; omega, by dsimp; omega⟩
    have hivl : nodeIvl post n = nodeIvl s n := by
      unfold nodeIvl; rw [hw0]
    refine ⟨hivl, ?_⟩
    by_cases h12 : memW s n = 1 ∨ memW s n = 2
    · have hsz56 : 56 ≤ nodeSize (memW s n) := by
        unfold nodeSize; rcases h12 with h1 | h2 <;> simp [*]
      have hw32 : memW post (n + 32) = memW s (n + 32) :=
        memW_eq_of_ivlUnhit hu_n (by omega) hhi_n ⟨by dsimp; omega, by dsimp; omega⟩
      have hw40 : memW post (n + 40) = memW s (n + 40) :=
        memW_eq_of_ivlUnhit hu_n (by omega) hhi_n ⟨by dsimp; omega, by dsimp; omega⟩
      unfold nodePath
      rw [hw0, hw32, hw40]
    · unfold nodePath
      rw [hw0]
      simp [h12]
  have hnd'_cls : ∀ o ∈ nodeExtents post Nd',
      o = (0, 0) ∨ o ∈ nodeExtents s Nd ∨ Inside o (globN s "heap_ptr") (globN post "heap_ptr") := by
    intro o ho
    unfold nodeExtents at ho
    obtain ⟨n, hn', hno⟩ := List.mem_flatMap.1 ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
    rcases hNd_cls n hn' with hn_old | ⟨hin_ivl, hpath_cls⟩
    · obtain ⟨e_ivl, e_p⟩ := hold_ivl_eq n hn_old
      right; left
      unfold nodeExtents
      refine List.mem_flatMap.2 ⟨n, hn_old, ?_⟩
      rcases hno with rfl | rfl
      · rw [e_ivl]; simp
      · rw [e_p]; simp
    · rcases hno with rfl | rfl
      · exact Or.inr (Or.inr hin_ivl)
      · rcases hpath_cls with hp0 | hin_p
        · exact Or.inl hp0
        · exact Or.inr (Or.inr hin_p)
  have hTr_post : TriesTypedWith post S Nd' := by
    have ews := hcore "ws" (by decide)
    refine ⟨hNH_post, ?_, ?_⟩
    · intro o ho
      rw [hfix_eq]
      rcases hnd'_cls o ho with rfl | ho_old | ho_fresh
      · exact ⟨fun _ _ _ _ => Or.inl rfl, fun _ _ => Or.inl rfl⟩
      · refine ⟨fun u hu i hi => ?_, (hTr.2.1 o ho_old).2⟩
        rw [(hall_fp u hu).2] at hi
        exact (hTr.2.1 o ho_old).1 u hu i hi
      · have ho_in' : Inside o (globN s "heap_ptr") (globN s "heap_ptr" + (globN post "heap_ptr" - globN s "heap_ptr")) := by
          dsimp [Inside] at ho_fresh ⊢; omega
        refine ⟨fun u hu i hi => ?_, fun j hj => ?_⟩
        · rw [(hall_fp u hu).2] at hi
          exact (R10Shards.P26_P28.disj_of_inside_right ho_in'
            (R16WkAcctWs.disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp (Or.inr ((hT.2.1 u hu).2 i hi).1))).flip
        · exact (R10Shards.P26_P28.disj_of_inside_right ho_in'
            (R16WkAcctWs.disj_fresh_of_zero_or_allocated hAs.2 hAp.2 hhp
              (by rcases hF.1 j hj with h0 | ⟨hal, _⟩; exact Or.inl h0; exact Or.inr hal))).flip
    · intro hws_nz_p
      rw [ews] at hws_nz_p
      have e24 := R10Shards.P26_P28.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by decide) ews hws_nz_p (hu_ws hws_nz_p) (k := 24) (by omega) (by omega)
      have e32 := R10Shards.P26_P28.rec_word_eq_of_unhit hAs.2 hF "ws" 40 (by decide) ews hws_nz_p (hu_ws hws_nz_p) (k := 32) (by omega) (by omega)
      rw [e24, e32]
      obtain ⟨hr24, hr32⟩ := hTr.2.2 hws_nz_p
      have hr24' : RootIn Nd' (memW s (globN s "ws" + 24)) := by
        rcases hr24 with h0 | hm
        · exact Or.inl h0
        · exact Or.inr (hNd_sub _ hm)
      refine ⟨hr24', fun htS i hi => ?_⟩
      set u32 := memW s (globN s "ws" + 32)
      have hvals_eq := R10Shards.P26_P28.htabValues_eq_of_unhit (hT.2.1 u32 htS).1 (hu_all u32 htS)
      have hh3_eq := (hall_fp u32 htS).1 3 (by omega)
      rw [hh3_eq] at hi
      have hmem_v : nodeF post (hdr post u32 5) (memW post (hdr post u32 6 + 8 * i)) 8 ∈ htabValues post u32 := by
        unfold htabValues; exact List.mem_map.2 ⟨i, List.mem_range.2 (by rwa [hh3_eq]), rfl⟩
      rw [hvals_eq] at hmem_v
      unfold htabValues at hmem_v
      obtain ⟨j, hj_rng, hj_eq⟩ := List.mem_map.1 hmem_v
      rw [← hj_eq]
      rcases hr32 htS j (List.mem_range.1 hj_rng) with h0 | hm
      · exact Or.inl h0
      · exact Or.inr (hNd_sub _ hm)
  refine ⟨S, Nd', fun _ h => h, ⟨hT_post, hJ_post, hF_post, hTr_post⟩, ?_, ?_, hQ_post⟩
  · intro o ho
    unfold worldOwned at ho
    rcases List.mem_append.1 ho with ho12 | ho_nd
    · rcases List.mem_append.1 ho12 with ho_tab | ho_fix
      · obtain ⟨u, hu, hi⟩ := List.mem_flatMap.1 ho_tab
        rw [(hall_fp u hu).2] at hi
        refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
        unfold worldOwned
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u, hu, hi⟩))
      · rw [hfix_eq] at ho_fix
        refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
        unfold worldOwned
        exact List.mem_append_left _ (List.mem_append_right _ ho_fix)
    · rcases hnd'_cls o ho_nd with rfl | ho_old | ho_fresh
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
        unfold worldOwned
        exact List.mem_append_right _ ho_old
      · exact Or.inr (Or.inr ho_fresh)
  · intro a ha hnot_hf
    exact hfr a (fun j hj => ha j (List.mem_append_right _ hj)) hnot_hf

private theorem lookup_ws_storage_trie_add :
    originalRuntimeCode.lookup (ofString "ws_storage_trie") =
      some ([(ofString "root", .one)],
        sourceFnBody Guest.Software.guestFn_ws_storage_trie, .one) :=
  lookup_of_guestAst_getElem 368 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ws_storage_trie) rfl

private theorem lookup_decode_witness_to_mpt_add :
    originalRuntimeCode.lookup (ofString "decode_witness_to_mpt") =
      some ([(ofString "db", .one), (ofString "root_hash", .one)],
        sourceFnBody Guest.Software.guestFn_decode_witness_to_mpt, .one) :=
  lookup_of_guestAst_getElem 265 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_witness_to_mpt) rfl

private def wsStorageTrieSetProg : ProgHOL 64 :=
  .seq
    (.call (some (none, none)) (ofString "htab_set")
      [.var .local (ofString "t"), .var .local (ofString "root"),
       .op .add [.var .local (ofString "node"), .const 1#64]])
    (.return (.var .local (ofString "node")))

private def wsStorageTrieDecodeProg : ProgHOL 64 :=
  .decCall (ofString "node") .one (ofString "decode_witness_to_mpt")
    [.load .one (.op .add [.var .global (ofString "ws"), .const 0#64]),
     .var .local (ofString "root")]
    wsStorageTrieSetProg

private def wsStorageTrieIteProg : ProgHOL 64 :=
  .seq
    (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "m"))) (.const 0#64))
      (.return (.op .sub [.rfield 1 (.var .local (ofString "m")), .const 1#64]))
      .skip)
    wsStorageTrieDecodeProg

private def wsStorageTrieGetProg : ProgHOL 64 :=
  .decCall (ofString "m") (.comb [.one, .one]) (ofString "htab_get")
    [.var .local (ofString "t"), .var .local (ofString "root")]
    wsStorageTrieIteProg

private theorem ws_storage_trie_body_worldStepSc {F : Type}
    {ExtraGuard : ∀ {F' : Type}, PanSemStateFiniteExact 64 F' → Nat → Prop}
    (hdw : DecodeWitnessToMptSpec @ExtraGuard)
    (hdb_ok : ∀ {F' : Type} (st : PanSemStateFiniteExact 64 F'),
      WorldOK st → globN st "ws" ≠ 0 → ExtraGuard st (memW st (globN st "ws")))
    (s : PanSemStateFiniteExact 64 F) (rootw : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hW : WorldOK s)
    (hs_root : s.locals.lookup (ofString "root") = some (.val (.word rootw)))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ws_storage_trie)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ws_storage_trie)).1) :
    R16WkAcctWs.WorldStepSc (R16WkAcctWs.bufRegions []) ["heap_ptr", "scratch_ptr"] stdKeep NoExtra
      s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ws_storage_trie)).1
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ws_storage_trie)).2 := by
  have hB : R16WkAcctWs.ValidBufList [] := fun _ hp => by cases hp
  have hgw : R16WkAcctWs.SafeStepGlobals ["heap_ptr", "scratch_ptr"] := fun g hg => by
    simp at hg; rcases hg with rfl | rfl <;> decide
  have hbody_eq : sourceFnBody Guest.Software.guestFn_ws_storage_trie =
      .dec (ofString "t") .one
        (.load .one (.op .add [.var .global (ofString "ws"), .const 32#64]))
        wsStorageTrieGetProg := rfl
  rw [hbody_eq] at hnt hres ⊢
  -- Step 1: `dec "t" .one (load .one (ws + 32))`
  rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
  rcases hev_t : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ws"), .const 32#64])) with _ | tv
  · simp [hev_t] at hres; cases hres with | inl h => obtain ⟨_, h⟩ := h; simp at h | inr h => obtain ⟨_, _, h, _⟩ := h; simp at h
  · obtain ⟨tw, rfl, htw_nat, hws_nz⟩ := R16WkAcctWs.evalAt_loadG_nz s hW.1.1 "ws" 32#64 (by decide) tv hev_t
    have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
    rw [h32] at htw_nat
    simp only [hev_t] at hnt hres ⊢
    rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])] at hnt hres ⊢
    let sT := setVarHOLFinite (ofString "t") (.val (.word tw)) s
    have hsT_W : WorldOK sT := localsFree_worldOK s _ s.clock hW
    have hsT_code : sT.code = originalRuntimeCode := hcode
    have hsT_t : sT.locals.lookup (ofString "t") = some (.val (.word tw)) := by
      simp [sT, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hsT_root : sT.locals.lookup (ofString "root") = some (.val (.word rootw)) := by
      simp [sT, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "t" ≠ ofString "root" by decide, hs_root]
    -- Step 2: `decCall "m" (.comb [.one, .one]) "htab_get" [t, root]`
    have hres_wk : WkBal.Resumes (evaluateHOLFiniteState sT wsStorageTrieGetProg).1 := by
      rcases hres with ⟨v, hv⟩ | ⟨eid, ev, he, hne⟩
      · exact Or.inl ⟨v, hv⟩
      · exact Or.inr ⟨eid, ev, he, hne⟩
    obtain ⟨tw', kw', f0, f1, ck, hev_tw', _, htw_nz', _, hnt_sM, hres_sM_wk, heqM_r, heqM_s⟩ :=
      WkBal.decCall_htab_get_resumes sT (ofString "m")
        (.var .local (ofString "t")) (.var .local (ofString "root")) wsStorageTrieIteProg
        hsT_W.1.1 hnt hres_wk
    have hres_sM : Resumes (evaluateHOLFiniteState
        (setVarHOLFinite (ofString "m") (.rStruct [.val (.word f0), .val (.word f1)])
          { sT with clock := ck }) wsStorageTrieIteProg).1 := by
      rcases hres_sM_wk with ⟨v, hv⟩ | ⟨eid, ev, he, hne⟩
      · exact Or.inl ⟨v, hv⟩
      · exact Or.inr ⟨eid, ev, he, hne⟩
    have htw_eq : tw' = tw := by
      simp [evalHOLExact, hsT_t] at hev_tw'; exact hev_tw'.symm
    subst tw'
    let sM := setVarHOLFinite (ofString "m") (.rStruct [.val (.word f0), .val (.word f1)])
      { sT with clock := ck }
    have hsM_W : WorldOK sM := localsFree_worldOK s _ ck hW
    have hsM_m : sM.locals.lookup (ofString "m") =
        some (.rStruct [.val (.word f0), .val (.word f1)]) := by
      simp [sM, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hsM_t : sM.locals.lookup (ofString "t") = some (.val (.word tw)) := by
      simp [sM, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "m" ≠ ofString "t" by decide, hsT_t]
    have hsM_root : sM.locals.lookup (ofString "root") = some (.val (.word rootw)) := by
      simp [sM, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "m" ≠ ofString "root" by decide, hsT_root]
    -- Step 3: `ite (m.0 != 0) (return (m.1 - 1)) skip`
    by_cases hf0 : f0 = 0
    · subst hf0
      have hcmp : @evalHOLExact 64 F _ sM.toExact (fun a => Classical.propDecidable (sM.memaddrs a))
          (.cmp .notEqual (.rfield 0 (.var .local (ofString "m"))) (.const 0#64)) =
          some (.val (.word 0#64)) := by
        simp [evalHOLExact, hsM_m, Compiler.Encoders.Asm.wordCmpHOL]
      have hite_eq : evaluateHOLFiniteState sM wsStorageTrieIteProg =
          evaluateHOLFiniteState sM wsStorageTrieDecodeProg := by
        dsimp only [wsStorageTrieIteProg]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcmp]
        simp [evaluateHOLFiniteState_skip]
      rw [hite_eq] at hnt_sM hres_sM
      -- Step 4: `decCall "node" .one "decode_witness_to_mpt" [load (ws + 0), root] wsStorageTrieSetProg`
      have hnt_dw := hnt_sM
      have hres_dw := hres_sM
      dsimp only [wsStorageTrieDecodeProg] at hnt_dw hres_dw
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt_dw hres_dw
      -- Evaluate `[load (ws + 0), root]` on `sM`
      rcases hargs_dw : @evalListHOLExact 64 F _ sM.toExact (fun a => Classical.propDecidable (sM.memaddrs a))
          [.load .one (.op .add [.var .global (ofString "ws"), .const 0#64]),
           .var .local (ofString "root")] with _ | vs_dw
      · simp [evalListHOLFinite, hargs_dw] at hres_dw
        cases hres_dw with | inl h => obtain ⟨_, h⟩ := h; simp at h | inr h => obtain ⟨_, _, h, _⟩ := h; simp at h
      · have hargs_dw_fin : evalListHOLFinite sM (h := fun a => Classical.propDecidable (sM.memaddrs a))
            [.load .one (.op .add [.var .global (ofString "ws"), .const 0#64]),
             .var .local (ofString "root")] = some vs_dw := by
          rwa [evalListHOLFinite_eq_toExact]
        -- Extract `dbw` from `vs_dw`
        have hex_db : ∃ dbw : BitVec 64,
            vs_dw = [.val (.word dbw), .val (.word rootw)] ∧
            dbw.toNat = memW s (globN s "ws") := by
          have ha_ex := hargs_dw
          simp only [evalListHOLExact] at ha_ex
          rcases he1 : @evalHOLExact 64 F _ sM.toExact (fun a => Classical.propDecidable (sM.memaddrs a))
              (.load .one (.op .add [.var .global (ofString "ws"), .const 0#64])) with _ | v1
          · simp [he1] at ha_ex
          · obtain ⟨dbw, rfl, hdb_nat, _⟩ := R16WkAcctWs.evalAt_loadG_nz sM hsM_W.1.1 "ws" 0#64 (by decide) v1 he1
            have h2 : @evalHOLExact 64 F _ sM.toExact (fun a => Classical.propDecidable (sM.memaddrs a))
                (.var .local (ofString "root")) = some (.val (.word rootw)) := by
              simp [evalHOLExact, hsM_root]
            rw [he1, h2] at ha_ex
            injection ha_ex with hv_eq
            have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
            rw [h0, Nat.add_zero] at hdb_nat
            exact ⟨dbw, hv_eq.symm, hdb_nat⟩
        obtain ⟨dbw, rfl, hdbw_nat⟩ := hex_db
        have hsM_code : sM.code = originalRuntimeCode := hcode
        have hlk_dw := pan_two_word_lookup sM.code.lookup (ofString "decode_witness_to_mpt")
          (ofString "db") (ofString "root_hash")
          (sourceFnBody Guest.Software.guestFn_decode_witness_to_mpt) dbw rootw
          (by decide) (by rw [hsM_code]; exact lookup_decode_witness_to_mpt_add)
        simp only [hargs_dw_fin, hlk_dw] at hnt_dw hres_dw
        by_cases hcz : sM.clock = 0
        · simp [hcz] at hnt_dw
        · rw [if_neg hcz] at hnt_dw hres_dw
          let cmap_dw := ((HolFiniteMapExact.empty.update (ofString "db", ValueHOL.val (.word dbw))).update
            (ofString "root_hash", ValueHOL.val (.word rootw)))
          let ent_dw := callEntryStateHOLFinite sM cmap_dw
          have hent_db : locN ent_dw "db" = memW s (globN s "ws") := by
            have hl_db : cmap_dw.lookup (ofString "db") = some (.val (.word dbw)) := by
              simp [cmap_dw, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "root_hash" ≠ ofString "db" by decide]
            simp [locN, ent_dw, callEntryStateHOLFinite, hl_db, hdbw_nat]
          have hent_guard : ArenaReady ent_dw ∧ ExtraGuard ent_dw (locN ent_dw "db") := by
            refine ⟨localsFree_arenaReady sM _ _ hsM_W.1, ?_⟩
            rw [hent_db]
            exact hdb_ok ent_dw (localsFree_worldOK s _ _ hW) hws_nz
          have hmeta_dw := (PanRunBounded.evaluateHOLFiniteState_metadata ent_dw
            (sourceFnBody Guest.Software.guestFn_decode_witness_to_mpt)).1
          rcases hrun_dw : evaluateHOLFiniteState ent_dw
              (sourceFnBody Guest.Software.guestFn_decode_witness_to_mpt) with ⟨res_dw, cpost_dw⟩
          simp only [ent_dw, cmap_dw] at hrun_dw hmeta_dw
          simp only [hrun_dw] at hmeta_dw hnt_dw hres_dw
          have hnt_ent_dw : (evaluateHOLFiniteState ent_dw
              (sourceFnBody Guest.Software.guestFn_decode_witness_to_mpt)).1 ≠ some .timeOut := by
            simp only [ent_dw, cmap_dw, hrun_dw]; rintro rfl; simp at hnt_dw
          have hspec_dw := FunSpec.at_lookup hdw sM hcode
            [.val (.word dbw), .val (.word rootw)]
            (sourceFnBody Guest.Software.guestFn_decode_witness_to_mpt) cmap_dw .one hlk_dw
            hent_guard hnt_ent_dw
          simp only [ent_dw, cmap_dw, hrun_dw] at hspec_dw
          cases res_dw with
          | none =>
            cases hres_dw with | inl h => obtain ⟨_, h⟩ := h; simp at h | inr h => obtain ⟨_, _, h, _⟩ := h; simp at h
          | some cr =>
            cases cr with
            | timeOut => simp at hnt_dw
            | error | «break» | «continue» | finalFfi _ =>
              cases hres_dw with | inl h => obtain ⟨_, h⟩ := h; simp at h | inr h => obtain ⟨_, _, h, _⟩ := h; simp at h
            | exception eid ev =>
              obtain ⟨hAp_dw, hbe_dw, hhp_dw, hsp_dw, hgk_dw, hfr_dw, _⟩ := hspec_dw hres_dw
              have hstep_ent : R16WkAcctWs.WorldStepSc (R16WkAcctWs.bufRegions []) ["heap_ptr", "scratch_ptr"]
                  stdKeep NoExtra ent_dw (some (.exception eid ev)) cpost_dw := by
                have h0 := worldStepSc_of_decode_witness_frame (s := ent_dw) (post := cpost_dw)
                  (r := some (.exception eid ev)) (localsFree_worldOK s _ _ hW)
                  hAp_dw hbe_dw hhp_dw hsp_dw hgk_dw hfr_dw
                  (fun Nd hNH hal => by
                    have hAs : ArenaReady ent_dw := hent_guard.1
                    have hag : AllocatorGrows ent_dw cpost_dw := by
                      refine ⟨hhp_dw, ?_⟩
                      rw [hsp_dw]
                    have hf_al : (globN ent_dw "heap_ptr") % 8 = 0 ∧
                        (globN cpost_dw "heap_ptr" - globN ent_dw "heap_ptr") % 8 = 0 := by
                      have h1 := hAs.2.2.2.2.2.2.1
                      have h2 := hAp_dw.2.2.2.2.2.2.1
                      omega
                    have hu_dw_alloc : ∀ i : Ivl, i.2 ≠ 0 → Allocated ent_dw i → R10Shards.P26_P28.IvlUnhit ent_dw cpost_dw i :=
                      fun _ hpos_i hal_i => unhit_p26_of_free_frame_local hAs.2 hfr_dw hpos_i hal_i
                    have hNH' : NodeHeap cpost_dw Nd :=
                      (R10Shards.P26_P28.nodeHeap_congr_bytes hAs.1 hAp_dw.1 hag hNH
                        (fun n hn => hu_dw_alloc _ (by unfold nodeIvl nodeSize; dsimp only; split_ifs <;> omega) (hNH.1 n hn).2.1)
                        (fun n hn h12 hp_nz k hk => by
                          rcases (hNH.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, _⟩
                          · exact absurd h0 hp_nz
                          · have hhi := (ivl_allocated_bound hAs.2 hal_p).2
                            have hu_p := hu_dw_alloc _ hp_nz hal_p
                            exact R10Shards.P26_P28.memB_eq_of_ivlUnhit hu_p hbe_dw hhi
                              ⟨by dsimp; omega, by dsimp; omega⟩)).1
                    exact ⟨Nd, fun _ h => h, fun _ h => Or.inl h, hNH', fun _ h => by simp at h⟩)
                refine ⟨⟨h0.1.1, h0.1.2.1, h0.1.2.2.1, h0.1.2.2.2.1, fun S Nd hWT hD => ?_⟩, h0.2⟩
                obtain ⟨S', Nd', hsub, hWT', hog, hfr, _⟩ := h0.1.2.2.2.2 S Nd hWT hD
                exact ⟨S', Nd', hsub, hWT', hog, hfr, trivial⟩
              have hstep_from_s : R16WkAcctWs.WorldStepSc (R16WkAcctWs.bufRegions []) ["heap_ptr", "scratch_ptr"]
                  stdKeep NoExtra s (some (.exception eid ev))
                  ({ cpost_dw with
                    locals := HolFiniteMapExact.resVarEq
                      (HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite cpost_dw).locals
                        (ofString "m", sT.locals.lookup (ofString "m")))
                      (ofString "t", s.locals.lookup (ofString "t")) } : PanSemStateFiniteExact 64 F) := by
                have h1 : R16WkAcctWs.WorldStepSc (R16WkAcctWs.bufRegions []) ["heap_ptr", "scratch_ptr"]
                    stdKeep NoExtra sM (some (.exception eid ev))
                    ({ cpost_dw with
                      locals := HolFiniteMapExact.resVarEq
                        (HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite cpost_dw).locals
                          (ofString "m", sT.locals.lookup (ofString "m")))
                        (ofString "t", s.locals.lookup (ofString "t")) } : PanSemStateFiniteExact 64 F) :=
                  hstep_ent.from_entry (L := _) (k := cpost_dw.clock)
                exact WorldStepSc.of_pre_locals_clock (s := s) (L := sM.locals) (k := ck) h1
              have heval_all_r : (evaluateHOLFiniteState sT wsStorageTrieGetProg).1 = some (.exception eid ev) := by
                dsimp only [wsStorageTrieGetProg]
                rw [heqM_r, hite_eq]
                dsimp only [wsStorageTrieDecodeProg]
                rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs_dw_fin]
                dsimp only; rw [hlk_dw]; dsimp only
                rw [if_neg hcz, hrun_dw]
              have heval_all_s : ({ (evaluateHOLFiniteState sT wsStorageTrieGetProg).2 with
                  locals := HolFiniteMapExact.resVarEq
                    (evaluateHOLFiniteState sT wsStorageTrieGetProg).2.locals
                    (ofString "t", s.locals.lookup (ofString "t")) } : PanSemStateFiniteExact 64 F) =
                  ({ cpost_dw with
                    locals := HolFiniteMapExact.resVarEq
                      (HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite cpost_dw).locals
                        (ofString "m", sT.locals.lookup (ofString "m")))
                      (ofString "t", s.locals.lookup (ofString "t")) } : PanSemStateFiniteExact 64 F) := by
                dsimp only [wsStorageTrieGetProg]
                rw [heqM_s, hite_eq]
                dsimp only [wsStorageTrieDecodeProg]
                rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs_dw_fin]
                dsimp only; rw [hlk_dw]; dsimp only
                rw [if_neg hcz, hrun_dw]
                rfl
              rw [heval_all_r, heval_all_s]
              exact hstep_from_s
            | returned v_dw =>
              obtain ⟨hAp_dw, hbe_dw, hhp_dw, hsp_dw, hgk_dw, hfr_dw, hret_dw⟩ :=
                hspec_dw (Or.inl ⟨v_dw, rfl⟩)
              -- Extract the returned word `nodew` using `(S0, Nd0)` from `hW`
              obtain ⟨S0, hWT0_ex⟩ := hW.2
              obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
              have hWT0_ent : WorldTypedWith ent_dw S0 Nd0 :=
                ⟨(tablesTyped_with_locals s cmap_dw (sM.clock - 1) S0).2 hWT0.1,
                 hWT0.2.1, hWT0.2.2.1, hWT0.2.2.2.1, hWT0.2.2.2.2.1, hWT0.2.2.2.2.2⟩
              have hnd0_alloc : ∀ o ∈ nodeExtents ent_dw Nd0, o.2 = 0 ∨ Allocated ent_dw o := by
                intro o ho
                unfold nodeExtents at ho
                obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
                rcases hno with rfl | rfl
                · exact Or.inr (hWT0_ent.2.2.2.1.1 n hn).2.1
                · unfold nodePath; split_ifs with hc
                  · rcases (hWT0_ent.2.2.2.1.1 n hn).2.2.2.2.2.2.1 hc.1 with h0 | ⟨_, hal, _⟩
                    · exact absurd h0 hc.2
                    · exact Or.inr hal
                  · exact Or.inl rfl
              obtain ⟨nodew, _, rfl, _, _, _, _⟩ := hret_dw Nd0 hWT0_ent.2.2.2.1 hnd0_alloc v_dw rfl
              have hsh_nw : (shapeEqHOL (shapeOfHOLExact (.val (.word nodew) : ValueHOL 64)) .one &&
                  shapeEqHOL (shapeOfHOLExact (.val (.word nodew) : ValueHOL 64)) .one) = true := by
                simp [shapeOfHOLExact, shapeEqHOL]
              dsimp only at hnt_dw hres_dw
              rw [if_pos hsh_nw] at hnt_dw hres_dw
              let sN := setVarHOLFinite (ofString "node") (.val (.word nodew))
                { cpost_dw with locals := sM.locals }
              have hres_dw_wk : WkBal.Resumes (evaluateHOLFiniteState sN wsStorageTrieSetProg).1 := by
                rcases hres_dw with ⟨v, hv⟩ | ⟨eid, ev, he, hne⟩
                · exact Or.inl ⟨v, hv⟩
                · exact Or.inr ⟨eid, ev, he, hne⟩
              have hsN_step_q : R16WkAcctWs.WorldStepSc (R16WkAcctWs.bufRegions []) ["heap_ptr", "scratch_ptr"]
                  stdKeep
                  (fun _ _ _ _ Nd' => RootIn Nd' nodew.toNat)
                  ent_dw (some (.returned (.val (.word nodew)))) cpost_dw := by
                have h0 := worldStepSc_of_decode_witness_frame (s := ent_dw) (post := cpost_dw)
                  (r := some (.returned (.val (.word nodew)))) (localsFree_worldOK s _ _ hW)
                  hAp_dw hbe_dw hhp_dw hsp_dw hgk_dw hfr_dw
                  (fun Nd hNH hal => by
                    obtain ⟨w', Nd', hw_eq, hsub, hcls, hNH', hroot'⟩ := hret_dw Nd hNH hal (.val (.word nodew)) rfl
                    injection hw_eq with hw_eq; injection hw_eq with hw_eq; subst hw_eq
                    exact ⟨Nd', hsub, hcls, hNH', fun v hv => by
                      injection hv with hv; injection hv with hv; subst hv
                      exact ⟨nodew, rfl, hroot'⟩⟩)
                refine ⟨⟨h0.1.1, h0.1.2.1, h0.1.2.2.1, h0.1.2.2.2.1, fun S Nd hWT hD => ?_⟩, h0.2⟩
                obtain ⟨S', Nd', hsub, hWT', hog, hfr, hq⟩ := h0.1.2.2.2.2 S Nd hWT hD
                refine ⟨S', Nd', hsub, hWT', hog, hfr, ?_⟩
                obtain ⟨w', hw_eq, hroot'⟩ := hq (.val (.word nodew)) rfl
                injection hw_eq with hw_eq; injection hw_eq with hw_eq; subst hw_eq
                exact hroot'
              have hsN_W : WorldOK sN :=
                localsFree_worldOK cpost_dw _ cpost_dw.clock
                  (hsN_step_q.worldOK_bufs hB (localsFree_worldOK s _ _ hW))
              have hsN_code : sN.code = originalRuntimeCode := hmeta_dw.trans hcode
              have hsN_node : sN.locals.lookup (ofString "node") = some (.val (.word nodew)) := by
                simp [sN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              have hsN_t : sN.locals.lookup (ofString "t") = some (.val (.word tw)) := by
                simp [sN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "node" ≠ ofString "t" by decide, hsM_t]
              have hsN_root : sN.locals.lookup (ofString "root") = some (.val (.word rootw)) := by
                simp [sN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "node" ≠ ofString "root" by decide, hsM_root]
              have hsN_ws_eq : globN sN "ws" = globN s "ws" := by
                have hlk_ws : s.globals.lookup (ofString "ws") = sN.globals.lookup (ofString "ws") :=
                  hgk_dw (ofString "ws") (by decide)
                exact globN_eq_of_lookup (s := s) (post := sN) hlk_ws
              have hsN_ws32_eq : memW sN (globN sN "ws" + 32) = memW s (globN s "ws" + 32) := by
                have hrk := hsN_step_q.1.2.2.2.1 ("ws", [0, 8, 16, 24, 32]) (by simp [stdKeep])
                  hws_nz 32 (by simp) (fun _ hi => by cases hi)
                have hrk' : memW cpost_dw (globN s "ws" + 32) = memW s (globN s "ws" + 32) := hrk
                have hmem_sN : memW sN (globN sN "ws" + 32) = memW cpost_dw (globN s "ws" + 32) := by
                  rw [hsN_ws_eq]; rfl
                exact hmem_sN.trans hrk'
              have hsN_tw_nat : tw.toNat = memW sN (globN sN "ws" + 32) :=
                htw_nat.trans hsN_ws32_eq.symm
              obtain ⟨S1, hWT1_ex⟩ := hsN_W.2
              obtain ⟨Nd1, hWT1⟩ := (worldTyped_iff_with sN S1).1 hWT1_ex
              have htw_nz_nat : memW sN (globN sN "ws" + 32) ≠ 0 := by
                rw [← hsN_tw_nat]; intro h0; exact htw_nz' (BitVec.eq_of_toNat_eq h0)
              have hsN_ws_nz : globN sN "ws" ≠ 0 := by rwa [hsN_ws_eq]
              have htw_S1 : tw.toNat ∈ S1 := by
                rw [hsN_tw_nat]
                exact (ws32_roleSlot_disj sN S1 hWT1.1 hsN_ws_nz htw_nz_nat).1
              have hsN_WF : HtabWF sN tw.toNat := (hWT1.1.2.1 tw.toNat htw_S1).1
              have hsN_hal : ∀ i ∈ htabFootprint sN tw.toNat, Allocated sN i :=
                fun i hi => ((hWT1.1.2.1 tw.toNat htw_S1).2 i hi).1
              have hev_et : evalAt sN (.var .local (ofString "t")) = some (.val (.word tw)) := by
                simp [evalAt, evalHOLExact, hsN_t]
              have hev_ekey : evalAt sN (.var .local (ofString "root")) = some (.val (.word rootw)) := by
                simp [evalAt, evalHOLExact, hsN_root]
              have hev_eval : evalAt sN (.op .add [.var .local (ofString "node"), .const 1#64]) =
                  some (.val (.word (nodew + 1#64))) := by
                simp [evalAt, evalHOLExact, evalListHOLExact, hsN_node, wordOpHOL, wordOp, valueIsWord, valueWord]
              obtain ⟨mid, hexit_mid, hval_mid, hbe_mid, hloc_mid, hsp_mid, _, hnt_ret, hres_ret, heq_mid⟩ :=
                WkBal.seq_call_htab_set_void_resumes sN
                  (.var .local (ofString "t")) (.var .local (ofString "root"))
                  (.op .add [.var .local (ofString "node"), .const 1#64])
                  (.return (.var .local (ofString "node")))
                  tw rootw (nodew + 1#64)
                  hev_et hev_ekey hev_eval hsN_W.1 hsN_WF hsN_hal hnt_dw hres_dw_wk
              have hmid_node : mid.locals.lookup (ofString "node") = some (.val (.word nodew)) := by
                rw [hloc_mid]; exact hsN_node
              have hret_eval : evaluateHOLFiniteState mid (.return (.var .local (ofString "node"))) =
                  (some (.returned (.val (.word nodew))), emptyLocalsHOLFinite mid) := by
                rw [evaluateHOLFiniteState_return]
                simp [evalHOLFinite, evalHOLExact, hmid_node, shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapeHOL]
              -- Build the combined `WorldStepSc` from `s` to `{ emptyLocalsHOLFinite mid with locals := s.locals }`
              have hhp_mid : globN sN "heap_ptr" ≤ globN mid "heap_ptr" := hexit_mid.2.2.2.2.1
              have hfp_mid := hexit_mid.2.2.2.2.2.1
              have hfr_mid : FrameOutside sN mid (htabFootprint sN tw.toNat)
                  (globN sN "heap_ptr", globN mid "heap_ptr" - globN sN "heap_ptr") :=
                hexit_mid.2.2.2.2.2.2.1
              have hg_mid : ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
                  sN.globals.lookup k = mid.globals.lookup k := hexit_mid.2.2.2.2.2.2.2
              have hgk_all : GlobalsKept ["heap_ptr", "scratch_ptr"] s mid := by
                intro k hk
                have hk1 : k ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString := hk
                have hk2 : k ∉ (["heap_ptr"] : List String).map ofString := fun hm =>
                  hk1 (by simp at hm; simp [hm])
                exact (hgk_dw k hk1).trans (hg_mid k hk2)
              have hrk_mid : RecordsKept (R16WkAcctWs.bufRegions []) stdKeep sN mid := by
                have hf_al_m : (globN sN "heap_ptr") % 8 = 0 ∧ (globN mid "heap_ptr" - globN sN "heap_ptr") % 8 = 0 := by
                  have h1 := hsN_W.1.2.2.2.2.2.2.1
                  have h2 := hexit_mid.1.2.2.2.2.2.2.1
                  omega
                have ht0_al_m : ∀ j ∈ htabFootprint sN tw.toNat, j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
                  have hw := ((hWT1.1.2.1 tw.toNat htw_S1).1.1 j hj).2
                  exact ⟨hw.1, hw.2.1⟩
                intro rec hrec hgnz k hk _
                have hrec_sz : ∃ sz, (rec.1, sz) ∈ typedRecords ∧ sz ≠ 0 ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
                  simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
                  rcases hrec with rfl | rfl | rfl | rfl
                  · refine ⟨40, by simp [typedRecords], by decide, ?_⟩; simp at hk; omega
                  · refine ⟨80, by simp [typedRecords], by decide, ?_⟩; simp at hk; omega
                  · refine ⟨72, by simp [typedRecords], by decide, ?_⟩; simp at hk; omega
                  · refine ⟨88, by simp [typedRecords], by decide, ?_⟩; simp at hk; omega
                obtain ⟨sz, htr, hsz_nz, hk8, hksz⟩ := hrec_sz
                have hmf := typedRecord_mem_fixedObjects sN htr
                simp only [hgnz, ↓reduceIte] at hmf
                rcases hWT1.2.2.1.1 _ hmf with h0 | ⟨hal, hwords⟩
                · omega
                · have hhi := (ivl_allocated_bound hsN_W.1.2 hal).2
                  have hg8 : (globN sN rec.1) % 8 = 0 := hwords.1
                  have hu_rec : IvlUnhit sN mid (globN sN rec.1, sz) :=
                    R10Shards.P26_P28.ivlUnhit_of_frameOutside_aligned hsz_nz hfr_mid ht0_al_m hf_al_m
                      (fun j hj => (((hWT1.1.2.1 tw.toNat htw_S1).2 j hj).2 _ hmf).flip)
                      (R16WkAcctWs.disj_fresh_of_zero_or_allocated hsN_W.1.2 hexit_mid.1.2 hhp_mid (Or.inr hal))
                  exact memW_eq_of_ivlUnhit hu_rec (by omega) hhi ⟨by omega, by omega⟩
              have hrk_all : RecordsKept (R16WkAcctWs.bufRegions []) stdKeep s mid := by
                intro rec hrec hgnz k hk hno
                have hrec_not : ofString rec.1 ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString := by
                  simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
                  rcases hrec with rfl | rfl | rfl | rfl <;> decide
                have hg_rec : globN sN rec.1 = globN s rec.1 := by
                  have hlk_rec : s.globals.lookup (ofString rec.1) = sN.globals.lookup (ofString rec.1) :=
                    hgk_dw (ofString rec.1) hrec_not
                  exact globN_eq_of_lookup (s := s) (post := sN) hlk_rec
                have h2 := hrk_mid rec hrec (by rw [hg_rec]; exact hgnz) k hk (fun _ hi => by cases hi)
                rw [hg_rec] at h2
                exact h2.trans (hsN_step_q.1.2.2.2.1 rec hrec hgnz k hk hno)
              have hhp_ent_eq : globN ent_dw "heap_ptr" = globN s "heap_ptr" := rfl
              have hhp_sN_eq : globN sN "heap_ptr" = globN cpost_dw "heap_ptr" := rfl
              have hhp_dw_s : globN s "heap_ptr" ≤ globN cpost_dw "heap_ptr" := hhp_dw
              have hstep_s_mid : R16WkAcctWs.WorldStepSc (R16WkAcctWs.bufRegions []) ["heap_ptr", "scratch_ptr"]
                  stdKeep NoExtra s (some (.returned (.val (.word nodew)))) mid := by
                refine ⟨⟨hexit_mid.1, le_trans hhp_dw_s hhp_mid, hgk_all, hrk_all, ?_⟩, ?_⟩
                · intro S Nd hWT_s hD_s
                  have hWT_ent : WorldTypedWith ent_dw S Nd := by
                    obtain ⟨hT, hJ, hF, hNH, hndisj, hws_tr⟩ := hWT_s
                    exact ⟨(tablesTyped_with_locals s cmap_dw (sM.clock - 1) S).2 hT, hJ, hF, hNH, hndisj, hws_tr⟩
                  obtain ⟨S2, Nd2, hsub12, hWT2, hOG12, hFO12, hroot2⟩ :=
                    hsN_step_q.1.2.2.2.2 S Nd hWT_ent hD_s
                  have hWT2_sN : WorldTypedWith sN S2 Nd2 := by
                    obtain ⟨hT, hJ, hF, hNH, hndisj, hws_tr⟩ := hWT2
                    exact ⟨(tablesTyped_with_locals cpost_dw (setVarHOLFinite (ofString "node") (.val (.word nodew))
                      { cpost_dw with locals := sM.locals }).locals cpost_dw.clock S2).2 hT, hJ, hF, hNH, hndisj, hws_tr⟩
                  obtain ⟨hWT3, hOG23, hFO23⟩ := worldStepSc_of_ws32_htabExit_for_Nd
                    (r := some (.returned (.val (.word nodew))))
                    hsN_W.1 hexit_mid.1 hbe_mid hg_mid hsN_ws_nz htw_nz_nat
                    (by rw [← hsN_tw_nat]; exact hexit_mid.2.1)
                    (by rw [← hsN_tw_nat]; exact hexit_mid.2.2.1)
                    hhp_mid
                    (by rw [← hsN_tw_nat]; exact hfp_mid)
                    (by rw [← hsN_tw_nat]; exact hfr_mid)
                    (by rw [← hsN_tw_nat]; exact hval_mid)
                    hWT2_sN hroot2
                  refine ⟨S2, Nd2, hsub12, hWT3, ?_, ?_, trivial⟩
                  · intro o ho
                    rcases hOG23 o ho with rfl | ⟨j, hj, hin_oj⟩ | hin_o23
                    · exact Or.inl rfl
                    · rcases hOG12 j hj with rfl | ⟨k, hk, hin_jk⟩ | hin_j12
                      · left
                        rcases o with ⟨o1, o2⟩
                        dsimp only [Inside] at hin_oj
                        have ho1 : o1 = 0 := by omega
                        have ho2 : o2 = 0 := by omega
                        rw [ho1, ho2]
                      · exact Or.inr (Or.inl ⟨k, hk, le_trans hin_jk.1 hin_oj.1, le_trans hin_oj.2 hin_jk.2⟩)
                      · exact Or.inr (Or.inr ⟨le_trans hin_j12.1 hin_oj.1,
                          le_trans hin_oj.2 (le_trans hin_j12.2 hhp_mid)⟩)
                    · exact Or.inr (Or.inr ⟨le_trans hhp_dw_s hin_o23.1, hin_o23.2⟩)
                  · intro a ha hhf
                    have hm12 : cpost_dw.memory a = s.memory a := hFO12 a ha hhf
                    have hm23 : mid.memory a = sN.memory a := by
                      apply hFO23 a
                      · intro i hi hch
                        obtain ⟨hc1, hc2⟩ := hch
                        rcases List.mem_append.1 hi with hi1 | hfg2
                        · rcases List.mem_append.1 hi1 with hwo2 | hR2
                          · rcases hOG12 i hwo2 with rfl | ⟨k, hk, hin_ik⟩ | hin_i12
                            · dsimp only at hc2; omega
                            · exact ha k (List.mem_append_left _ (List.mem_append_left _ hk))
                                ⟨by dsimp only [Inside] at hin_ik; omega,
                                 by dsimp only [Inside] at hin_ik; omega⟩
                            · have hp2_lim : globN cpost_dw "heap_ptr" ≤ heapLimit := hAp_dw.2.2.1
                              rw [hhp_ent_eq] at hin_i12
                              exact hhf ⟨by unfold heapFree; dsimp only [Inside] at hin_i12 ⊢; omega,
                                         by unfold heapFree; dsimp only [Inside] at hin_i12 ⊢; omega⟩
                          · cases hR2
                        · simp only [List.mem_singleton] at hfg2
                          subst hfg2
                          have hfmp21 : globN sN "frame_mem_ptr" = globN s "frame_mem_ptr" := by
                            have hlk_fmp : s.globals.lookup (ofString "frame_mem_ptr") = sN.globals.lookup (ofString "frame_mem_ptr") :=
                              hgk_dw (ofString "frame_mem_ptr") (by decide)
                            exact globN_eq_of_lookup (s := s) (post := sN) hlk_fmp
                          have hsp21 : globN sN "scratch_ptr" = globN s "scratch_ptr" := hsp_dw
                          exact ha (freeGap s) (List.mem_append_right _ (List.mem_singleton.2 rfl))
                            ⟨by unfold freeGap at hc1 ⊢; dsimp only at hc1 ⊢; omega,
                             by unfold freeGap at hc2 ⊢; dsimp only at hc2 ⊢; omega⟩
                      · intro ⟨hc1, hc2⟩
                        have hp2_lim : globN sN "heap_ptr" ≤ heapLimit := hsN_W.1.2.2.1
                        exact hhf ⟨by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega,
                                   by unfold heapFree at hc1 hc2 ⊢; dsimp only at hc1 hc2 ⊢; omega⟩
                    exact hm23.trans hm12
                · rw [hsp_mid]
                  have hsp21 : globN sN "scratch_ptr" = globN s "scratch_ptr" := hsp_dw
                  omega
              have hp_eq : evaluateHOLFiniteState sN wsStorageTrieSetProg =
                  (some (.returned (.val (.word nodew))), emptyLocalsHOLFinite mid) :=
                heq_mid.trans hret_eval
              have heval_all_r : (evaluateHOLFiniteState sT wsStorageTrieGetProg).1 =
                  some (.returned (.val (.word nodew))) := by
                dsimp only [wsStorageTrieGetProg]
                rw [heqM_r, hite_eq]
                dsimp only [wsStorageTrieDecodeProg]
                rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs_dw_fin]
                dsimp only; rw [hlk_dw]; dsimp only
                rw [if_neg hcz, hrun_dw]; dsimp only
                rw [if_pos hsh_nw]
                change (evaluateHOLFiniteState sN wsStorageTrieSetProg).1 = _
                rw [hp_eq]
              let dec_loc := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite mid).locals
                (ofString "node", sM.locals.lookup (ofString "node"))
              let final_loc := HolFiniteMapExact.resVarEq
                (HolFiniteMapExact.resVarEq dec_loc
                  (ofString "m", sT.locals.lookup (ofString "m")))
                (ofString "t", s.locals.lookup (ofString "t"))
              have hdec_s : (evaluateHOLFiniteState sM wsStorageTrieDecodeProg).2 =
                  { mid with locals := dec_loc } := by
                dsimp only [wsStorageTrieDecodeProg]
                rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hargs_dw_fin]
                dsimp only; rw [hlk_dw]; dsimp only
                rw [if_neg hcz, hrun_dw]; dsimp only
                rw [if_pos hsh_nw]
                change ({ (evaluateHOLFiniteState sN wsStorageTrieSetProg).2 with
                  locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState sN wsStorageTrieSetProg).2.locals
                    (ofString "node", sM.locals.lookup (ofString "node")) } : PanSemStateFiniteExact 64 F) = _
                rw [hp_eq]
                rfl
              have heval_all_s : ({ (evaluateHOLFiniteState sT wsStorageTrieGetProg).2 with
                  locals := HolFiniteMapExact.resVarEq
                    (evaluateHOLFiniteState sT wsStorageTrieGetProg).2.locals
                    (ofString "t", s.locals.lookup (ofString "t")) } : PanSemStateFiniteExact 64 F) =
                  { mid with locals := final_loc } := by
                dsimp only [wsStorageTrieGetProg]
                rw [heqM_s, hite_eq, hdec_s]
              rw [heval_all_r, heval_all_s]
              exact hstep_s_mid.with_locals_clock final_loc mid.clock
    · -- Cache hit (`f0 ≠ 0`): `return (f1 - 1)`
      have hf0_ne : f0 ≠ 0#64 := hf0
      have hcmp : @evalHOLExact 64 F _ sM.toExact (fun a => Classical.propDecidable (sM.memaddrs a))
          (.cmp .notEqual (.rfield 0 (.var .local (ofString "m"))) (.const 0#64)) =
          some (.val (.word 1#64)) := by
        simp [evalHOLExact, hsM_m, Compiler.Encoders.Asm.wordCmpHOL, hf0_ne]
      have hret_m : evaluateHOLFiniteState sM wsStorageTrieIteProg =
          (some (.returned (.val (.word (f1 - 1#64)))), emptyLocalsHOLFinite sM) := by
        dsimp only [wsStorageTrieIteProg]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcmp]
        dsimp only
        rw [if_neg (by decide), evaluateHOLFiniteState_return]
        simp [evalHOLFinite, evalHOLExact, evalListHOLExact, hsM_m, wordOpHOL, wordOp,
          valueIsWord, valueWord, shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapeHOL]
      have heval_hit_r : (evaluateHOLFiniteState sT wsStorageTrieGetProg).1 =
          some (.returned (.val (.word (f1 - 1#64)))) := by
        dsimp only [wsStorageTrieGetProg]
        rw [heqM_r, hret_m]
      let hit_loc := HolFiniteMapExact.resVarEq
        (HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite sM).locals
          (ofString "m", sT.locals.lookup (ofString "m")))
        (ofString "t", s.locals.lookup (ofString "t"))
      have heval_hit_s : ({ (evaluateHOLFiniteState sT wsStorageTrieGetProg).2 with
          locals := HolFiniteMapExact.resVarEq
            (evaluateHOLFiniteState sT wsStorageTrieGetProg).2.locals
            (ofString "t", s.locals.lookup (ofString "t")) } : PanSemStateFiniteExact 64 F) =
          { s with locals := hit_loc, clock := ck } := by
        dsimp only [wsStorageTrieGetProg]
        rw [heqM_s, hret_m]
        rfl
      rw [heval_hit_r, heval_hit_s]
      exact (R16WkAcctWs.WorldStepSc.refl s (some (.returned (.val (.word (f1 - 1#64))))) hW.1).with_locals_clock hit_loc ck

theorem wkSc_ws_storage_trie_of_decode_witness
    {ExtraGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat → Prop}
    (hdw : DecodeWitnessToMptSpec @ExtraGuard)
    (hdb_ok : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 → ExtraGuard s (memW s (globN s "ws"))) :
    R16WkAcctWs.WorldKeepsSc WorldOK (R16WkAcctWs.bufRegions [])
      ["heap_ptr", "scratch_ptr"] stdKeep NoExtra (ofString "ws_storage_trie") := by
  refine ⟨_, _, _, lookup_ws_storage_trie_add, ?_⟩
  intro F s hc hW hvalid hnt hres
  obtain ⟨values, hlook_fn⟩ := hvalid
  obtain ⟨rootw, _, hs_root⟩ :=
    R10Shards.P26_P28.lookupCode_one_word lookup_ws_storage_trie_add hlook_fn
  exact ws_storage_trie_body_worldStepSc hdw hdb_ok s rootw hc hW hs_root hnt hres

theorem wkSc_ws_storage_trie_idxBufs_of_decode_witness
    {ExtraGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat → Prop}
    (hdw : DecodeWitnessToMptSpec @ExtraGuard)
    (hdb_ok : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 → ExtraGuard s (memW s (globN s "ws"))) :
    R16WkAcctWs.WorldKeepsSc WorldOK (R16WkAcctWs.bufRegions idxBufs)
      ["heap_ptr", "scratch_ptr"] stdKeep NoExtra (ofString "ws_storage_trie") := by
  obtain ⟨ps, body, ret, hl, hb⟩ := wkSc_ws_storage_trie_of_decode_witness hdw hdb_ok
  exact ⟨ps, body, ret, hl, fun s hc hW hex hnt hres =>
    (hb s hc hW hex hnt hres).mono_bufs (B1 := []) (B2 := idxBufs)
      (fun _ hp => by cases hp) (fun _ h => h)⟩

theorem wk_ws_storage_trie_of_decode_witness
    {ExtraGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat → Prop}
    (hdw : DecodeWitnessToMptSpec @ExtraGuard)
    (hdb_ok : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 → ExtraGuard s (memW s (globN s "ws"))) :
    WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "ws_storage_trie") :=
  (wkSc_ws_storage_trie_of_decode_witness hdw hdb_ok).to_worldKeeps

theorem «wk_add_storage_write» :
    WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "add_storage_write") :=
  InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBal.wk_add_storage_write_impl

theorem «wk_add_storage_read» :
    WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "add_storage_read") :=
  InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBal.wk_add_storage_read_impl

abbrev wk_idx_add_storage := «wk_add_storage_read»

theorem wk_idx_start_storage_of_decode_witness
    {ExtraGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat → Prop}
    (hdw : DecodeWitnessToMptSpec @ExtraGuard)
    (hdb_ok : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 → ExtraGuard s (memW s (globN s "ws"))) :
    WorldKeeps WorldOK
      (fun s => [(globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "idx_start_storage") :=
  wk_idx_start_storage_of_ws_storage_trie
    (wkSc_ws_storage_trie_idxBufs_of_decode_witness hdw hdb_ok)

/-! ## Conditional `wk_state_init_of_decode_witness` (Milestone B) -/

private theorem lookup_state_init_add :
    originalRuntimeCode.lookup (ofString "state_init") =
      some ([(ofString "nodedb", .one), (ofString "state_root", .one), (ofString "codedb", .one)],
        sourceFnBody Guest.Software.guestFn_state_init, .one) :=
  lookup_of_guestAst_getElem 354 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_state_init) rfl

private theorem seq_store_global_rec_slot {F : Type}
    (s : PanSemStateFiniteExact 64 F) (gname : MlS) (sz : Nat)
    (pw off vw : BitVec 64) (valExp : ExpHOL 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (hg_lk : s.globals.lookup gname = some (.val (.word pw)))
    (hpw_lo : sourceBase ≤ pw.toNat)
    (hpw_hi : pw.toNat + sz ≤ heapLimit)
    (hpw8 : pw.toNat % 8 = 0)
    (hoff8 : off.toNat % 8 = 0)
    (hoff_hi : off.toNat + 8 ≤ sz)
    (hval_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some (.val (.word vw))) :
    let addr := pw + off
    let mid : PanSemStateFiniteExact 64 F :=
      { s with memory := fun a => if a = addr then .word vw else s.memory a }
    evaluateHOLFiniteState s
      (.seq (.store (.op .add [.var .global gname, .const off]) valExp) cont) =
      evaluateHOLFiniteState mid cont ∧
    ArenaReady mid ∧
    mid.globals = s.globals ∧
    mid.locals = s.locals ∧
    mid.be = s.be ∧
    addr.toNat = pw.toNat + off.toNat ∧
    memW mid (pw.toNat + off.toNat) = vw.toNat ∧
    (∀ k : Nat, k ≠ pw.toNat + off.toNat → k < 2 ^ 64 → memW mid k = memW s k) ∧
    FrameOutside s mid [] (pw.toNat, sz) := by
  dsimp only
  have h264 : heapLimit < 2 ^ 64 ∧ heapLimit ≤ heapEnd := ⟨by decide, by decide⟩
  have haddr_nat : (pw + off).toNat = pw.toNat + off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hdom : s.memaddrs (pw + off) := by
    rw [hAR.1.memaddrs, InitECandidate.Solver.Wave8Contracts.M08.ordinaryDomain_iff, haddr_nat]
    exact ⟨by omega, by omega, by omega⟩
  have hdst_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .global gname, .const off]) = some (.val (.word (pw + off))) := by
    simp [evalHOLExact, evalListHOLExact, hg_lk, wordOpHOL, wordOp, valueIsWord, valueWord]
  have hst_eval : evaluateHOLFiniteState s
      (.store (.op .add [.var .global gname, .const off]) valExp) =
      (none, { s with memory := fun a => if a = pw + off then .word vw else s.memory a }) := by
    rw [evaluateHOLFiniteState_store, hdst_ev, hval_ev]
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom, ↓reduceIte]
  set mid : PanSemStateFiniteExact 64 F :=
    { s with memory := fun a => if a = pw + off then .word vw else s.memory a }
  have hAR_mid : ArenaReady mid := ⟨guestInv_congr (s := s) rfl rfl rfl rfl hAR.1, hAR.2⟩
  have hmw_eq : memW mid (pw.toNat + off.toNat) = vw.toNat := by
    unfold memW
    have hb_eq : BitVec.ofNat 64 (pw.toNat + off.toNat) = pw + off := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), haddr_nat]
    simp [mid, hb_eq]
  have hmw_ne : ∀ k : Nat, k ≠ pw.toNat + off.toNat → k < 2 ^ 64 → memW mid k = memW s k := by
    intro k hne hk64
    unfold memW
    have hb_ne : BitVec.ofNat 64 k ≠ pw + off := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64, haddr_nat] at this
      exact hne this
    simp [mid, hb_ne]
  have hfr : FrameOutside s mid [] (pw.toNat, sz) := by
    intro a _ hno
    have hne : a ≠ pw + off := by
      rintro rfl
      exact hno ⟨by dsimp only; omega, by dsimp only; omega⟩
    simp [mid, hne]
  exact ⟨by rw [evaluateHOLFiniteState_seq_line780, hst_eval],
    hAR_mid, rfl, rfl, rfl, haddr_nat, hmw_eq, hmw_ne, hfr⟩

private theorem seq_htab_new_store_global_slot {F : Type}
    (s : PanSemStateFiniteExact 64 F) (gname : MlS) (sz : Nat)
    (pw off kw capw : BitVec 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (hp0_le : pw.toNat + sz ≤ globN s "heap_ptr")
    (hpw_lo : sourceBase ≤ pw.toNat)
    (hpw8 : pw.toNat % 8 = 0)
    (hoff8 : off.toNat % 8 = 0)
    (hoff_hi : off.toNat + 8 ≤ sz)
    (hgname_ne : gname ≠ ofString "heap_ptr")
    (hg_lk : s.globals.lookup gname = some (.val (.word pw)))
    (hkl : kw.toNat ∈ htabKeyLens)
    (hcl : capw.toNat ≤ htabCapMax)
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const kw, .const capw])
      (.seq (.store (.op .add [.var .global gname, .const off]) (.var .local (ofString "t")))
        cont))).1 ≠ some .timeOut)
    (hres : WkBal.Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const kw, .const capw])
      (.seq (.store (.op .add [.var .global gname, .const off]) (.var .local (ofString "t")))
        cont))).1) :
    ∃ (tw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      globN s "heap_ptr" ≤ tw.toNat ∧
      tw.toNat + 88 ≤ globN mid "heap_ptr" ∧
      ArenaReady mid ∧
      mid.be = s.be ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" ∧
      HtabWF mid tw.toNat ∧
      hdr mid tw.toNat 3 = 0 ∧
      hdr mid tw.toNat 0 = kw.toNat ∧
      (∀ i ∈ htabFootprint mid tw.toNat,
        Allocated mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) ∧
      memW mid (pw.toNat + off.toNat) = tw.toNat ∧
      (∀ off' : Nat, off' + 8 ≤ sz → off' ≠ off.toNat →
        memW mid (pw.toNat + off') = memW s (pw.toNat + off')) ∧
      FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, sz)]
        (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") ∧
      mid.locals.lookup (ofString "t") = some (.val (.word tw)) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      WkBal.Resumes (evaluateHOLFiniteState mid cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const kw, .const capw])
        (.seq (.store (.op .add [.var .global gname, .const off]) (.var .local (ofString "t")))
          cont)) = evaluateHOLFiniteState mid cont := by
  obtain ⟨tw, m1, htw_lo, htw_hi, hAR1, hbe1, hsp1, hfmp1, hwf1, hcnt1, hhdr1, hfp1, hfr1, hl1, _, hnt1, hres1, heq1⟩ :=
    WkBal.seq_call_htab_new_resumes s .local (ofString "t") kw capw _ hAR hkl hcl
      (fun h => by cases h) hnt hres
  obtain ⟨hm1_t, _, hm1_gl⟩ := hl1 rfl
  have hg_m1 : m1.globals.lookup gname = some (.val (.word pw)) :=
    (hm1_gl gname hgname_ne).symm.trans hg_lk
  have hpw_hi : pw.toNat + sz ≤ heapLimit := le_trans hp0_le hAR.2.2.1
  have ht_ev : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
      (.var .local (ofString "t")) = some (.val (.word tw)) := hm1_t
  obtain ⟨heq2, hAR2, hm2_g, hm2_l, hm2_be, haddr_nat, hmw_eq, hmw_ne, hfr2⟩ :=
    seq_store_global_rec_slot m1 gname sz pw off tw (.var .local (ofString "t")) cont hAR1 hg_m1
      hpw_lo hpw_hi hpw8 hoff8 hoff_hi ht_ev
  set mid : PanSemStateFiniteExact 64 F :=
    { m1 with memory := fun a => if a = pw + off then .word tw else m1.memory a }
  rw [heq2] at hnt1 hres1
  have hu_t : ∀ i ∈ htabFootprint m1 tw.toNat, WkBal.M08IvlUnhit m1 mid i := by
    intro i hi a _ h1 _
    have hin := (hfp1 i hi).2
    have hne : a ≠ pw + off := by
      rintro rfl
      rw [haddr_nat] at h1
      dsimp only [Inside] at hin
      omega
    simp [mid, hne]
  obtain ⟨hwf2, hfp2_eq, hhdr2_eq⟩ := WkBal.htabWF_transfer_unhit hAR1 hAR2 hwf1 hu_t
    (fun i hi => (hfp1 i hi).1)
  have hfr_comb : FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, sz)]
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") := by
    intro a hno hnhf
    have hno_pw : ¬ CellHits a.toNat (pw.toNat, sz) :=
      hno (pw.toNat, sz) (by simp)
    have hno_sp : ∀ j ∈ [(globN s "scratch_ptr", 0)], ¬ CellHits a.toNat j :=
      fun j hj => hno j (by simp only [List.mem_singleton] at hj; subst hj; simp)
    have h1 := hfr2 a (fun _ h => by cases h) hno_pw
    have h2 := hfr1 a hno_sp hnhf
    exact h1.trans h2
  refine ⟨tw, mid, htw_lo, htw_hi, hAR2, hm2_be.trans hbe1, hsp1, hfmp1,
    hwf2, (hhdr2_eq 3 (by omega)).trans hcnt1, (hhdr2_eq 0 (by omega)).trans hhdr1,
    fun i hi => by rw [hfp2_eq] at hi; exact hfp1 i hi,
    hmw_eq, ?_, hfr_comb, hm1_t, hm1_gl, hnt1, hres1, heq1.trans heq2⟩
  intro off' hoff'_hi hoff'_ne
  have h264 : heapLimit < 2 ^ 64 := by decide
  have hk64 : pw.toNat + off' < 2 ^ 64 := by omega
  rw [hmw_ne (pw.toNat + off') (by omega) hk64]
  unfold memW
  have hm_eq := hfr1 (BitVec.ofNat 64 (pw.toNat + off'))
    (fun j hj ⟨c1, c2⟩ => by
      simp only [List.mem_singleton] at hj; subst hj
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      have hsep : heapLimit ≤ scratchStart := by decide
      have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
      omega)
    (fun ⟨c1, c2⟩ => by
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      omega)
  rw [hm_eq]

private theorem decCall_htab_new_store_global_slot {F : Type}
    (s : PanSemStateFiniteExact 64 F) (gname : MlS) (sz : Nat)
    (pw off kw capw : BitVec 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (hp0_le : pw.toNat + sz ≤ globN s "heap_ptr")
    (hpw_lo : sourceBase ≤ pw.toNat)
    (hpw8 : pw.toNat % 8 = 0)
    (hoff8 : off.toNat % 8 = 0)
    (hoff_hi : off.toNat + 8 ≤ sz)
    (hgname_ne : gname ≠ ofString "heap_ptr")
    (hg_lk : s.globals.lookup gname = some (.val (.word pw)))
    (hkl : kw.toNat ∈ htabKeyLens)
    (hcl : capw.toNat ≤ htabCapMax)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString "t") .one (ofString "htab_new") [.const kw, .const capw]
        (.seq (.store (.op .add [.var .global gname, .const off]) (.var .local (ofString "t")))
          cont))).1 ≠ some .timeOut)
    (hres : WkBal.Resumes (evaluateHOLFiniteState s
      (.decCall (ofString "t") .one (ofString "htab_new") [.const kw, .const capw]
        (.seq (.store (.op .add [.var .global gname, .const off]) (.var .local (ofString "t")))
          cont))).1) :
    ∃ (tw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      globN s "heap_ptr" ≤ tw.toNat ∧
      tw.toNat + 88 ≤ globN mid "heap_ptr" ∧
      ArenaReady mid ∧
      mid.be = s.be ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" ∧
      HtabWF mid tw.toNat ∧
      hdr mid tw.toNat 3 = 0 ∧
      hdr mid tw.toNat 0 = kw.toNat ∧
      (∀ i ∈ htabFootprint mid tw.toNat,
        Allocated mid i ∧ Inside i (globN s "heap_ptr") (globN mid "heap_ptr")) ∧
      memW mid (pw.toNat + off.toNat) = tw.toNat ∧
      (∀ off' : Nat, off' + 8 ≤ sz → off' ≠ off.toNat →
        memW mid (pw.toNat + off') = memW s (pw.toNat + off')) ∧
      FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, sz)]
        (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") ∧
      mid.locals.lookup (ofString "t") = some (.val (.word tw)) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → s.globals.lookup k = mid.globals.lookup k) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      WkBal.Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "t") .one (ofString "htab_new") [.const kw, .const capw]
          (.seq (.store (.op .add [.var .global gname, .const off]) (.var .local (ofString "t")))
            cont))).1 = (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString "t") .one (ofString "htab_new") [.const kw, .const capw]
          (.seq (.store (.op .add [.var .global gname, .const off]) (.var .local (ofString "t")))
            cont))).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
            (ofString "t", s.locals.lookup (ofString "t")) } := by
  obtain ⟨tw, m1, htw_lo, htw_hi, hAR1, hbe1, hsp1, hfmp1, hwf1, hcnt1, hhdr1, hfp1, hfr1, hm1_t, _, hm1_gl, hnt1, hres1, heq1_1, heq1_2⟩ :=
    WkBal.decCall_htab_new_resumes s (ofString "t") kw capw _ hAR hkl hcl hnt hres
  have hg_m1 : m1.globals.lookup gname = some (.val (.word pw)) :=
    (hm1_gl gname hgname_ne).symm.trans hg_lk
  have hpw_hi : pw.toNat + sz ≤ heapLimit := le_trans hp0_le hAR.2.2.1
  have ht_ev : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
      (.var .local (ofString "t")) = some (.val (.word tw)) := hm1_t
  obtain ⟨heq2, hAR2, hm2_g, hm2_l, hm2_be, haddr_nat, hmw_eq, hmw_ne, hfr2⟩ :=
    seq_store_global_rec_slot m1 gname sz pw off tw (.var .local (ofString "t")) cont hAR1 hg_m1
      hpw_lo hpw_hi hpw8 hoff8 hoff_hi ht_ev
  set mid : PanSemStateFiniteExact 64 F :=
    { m1 with memory := fun a => if a = pw + off then .word tw else m1.memory a }
  rw [heq2] at hnt1 hres1 heq1_1 heq1_2
  have hu_t : ∀ i ∈ htabFootprint m1 tw.toNat, WkBal.M08IvlUnhit m1 mid i := by
    intro i hi a _ h1 _
    have hin := (hfp1 i hi).2
    have hne : a ≠ pw + off := by
      rintro rfl
      rw [haddr_nat] at h1
      dsimp only [Inside] at hin
      omega
    simp [mid, hne]
  obtain ⟨hwf2, hfp2_eq, hhdr2_eq⟩ := WkBal.htabWF_transfer_unhit hAR1 hAR2 hwf1 hu_t
    (fun i hi => (hfp1 i hi).1)
  have hfr_comb : FrameOutside s mid [(globN s "scratch_ptr", 0), (pw.toNat, sz)]
      (globN s "heap_ptr", globN mid "heap_ptr" - globN s "heap_ptr") := by
    intro a hno hnhf
    have hno_pw : ¬ CellHits a.toNat (pw.toNat, sz) :=
      hno (pw.toNat, sz) (by simp)
    have hno_sp : ∀ j ∈ [(globN s "scratch_ptr", 0)], ¬ CellHits a.toNat j :=
      fun j hj => hno j (by simp only [List.mem_singleton] at hj; subst hj; simp)
    have h1 := hfr2 a (fun _ h => by cases h) hno_pw
    have h2 := hfr1 a hno_sp hnhf
    exact h1.trans h2
  refine ⟨tw, mid, htw_lo, htw_hi, hAR2, hm2_be.trans hbe1, hsp1, hfmp1,
    hwf2, (hhdr2_eq 3 (by omega)).trans hcnt1, (hhdr2_eq 0 (by omega)).trans hhdr1,
    fun i hi => by rw [hfp2_eq] at hi; exact hfp1 i hi,
    hmw_eq, ?_, hfr_comb, hm1_t, hm1_gl, hnt1, hres1, heq1_1, heq1_2⟩
  intro off' hoff'_hi hoff'_ne
  have h264 : heapLimit < 2 ^ 64 := by decide
  have hk64 : pw.toNat + off' < 2 ^ 64 := by omega
  rw [hmw_ne (pw.toNat + off') (by omega) hk64]
  unfold memW
  have hm_eq := hfr1 (BitVec.ofNat 64 (pw.toNat + off'))
    (fun j hj ⟨c1, c2⟩ => by
      simp only [List.mem_singleton] at hj; subst hj
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      have hsep : heapLimit ≤ scratchStart := by decide
      have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
      omega)
    (fun ⟨c1, c2⟩ => by
      dsimp only at c1 c2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
      omega)
  rw [hm_eq]

private theorem frameOutside_collapse_rec_sp {F : Type} (s a b : PanSemStateFiniteExact 64 F)
    (pw sz : Nat)
    (hpw_lo : globN s "heap_ptr" ≤ pw)
    (hpw_hi : pw + sz ≤ globN a "heap_ptr")
    (hh_ab : globN a "heap_ptr" ≤ globN b "heap_ptr")
    (h1 : FrameOutside s a [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN a "heap_ptr" - globN s "heap_ptr"))
    (h2 : FrameOutside a b [(globN s "scratch_ptr", 0), (pw, sz)]
      (globN a "heap_ptr", globN b "heap_ptr" - globN a "heap_ptr")) :
    FrameOutside s b [(globN s "scratch_ptr", 0)]
      (globN s "heap_ptr", globN b "heap_ptr" - globN s "heap_ptr") := by
  intro x hno_sp hnhf
  have hno_sp_x : ¬ CellHits x.toNat (globN s "scratch_ptr", 0) :=
    hno_sp _ (List.mem_singleton.2 rfl)
  have hno_pw_x : ¬ CellHits x.toNat (pw, sz) := by
    intro ⟨c1, c2⟩; dsimp only at c1 c2
    exact hnhf ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hnhf_ab : ¬ CellHits x.toNat (globN a "heap_ptr", globN b "heap_ptr" - globN a "heap_ptr") := by
    intro ⟨c1, c2⟩; dsimp only at c1 c2
    exact hnhf ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hnhf_sa : ¬ CellHits x.toNat (globN s "heap_ptr", globN a "heap_ptr" - globN s "heap_ptr") := by
    intro ⟨c1, c2⟩; dsimp only at c1 c2
    exact hnhf ⟨c1, by dsimp only; omega⟩
  have hm2 := h2 x (fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact hno_sp_x
    · exact hno_pw_x) hnhf_ab
  exact hm2.trans (h1 x hno_sp hnhf_sa)

private theorem seq_assign_global_word {F : Type}
    (s : PanSemStateFiniteExact 64 F) (gname : MlS) (vw : BitVec 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (hg_mem : ∃ gn ∈ guestGlobalNames, ofString gn = gname)
    (hnot_arena : gname ≠ ofString "heap_ptr" ∧ gname ≠ ofString "scratch_ptr" ∧ gname ≠ ofString "frame_mem_ptr") :
    let mid := setGlobalHOLFinite gname (.val (.word vw)) s
    evaluateHOLFiniteState s (.seq (.assign .global gname (.const vw)) cont) =
      evaluateHOLFiniteState mid cont ∧
    ArenaReady mid ∧
    mid.memory = s.memory ∧
    mid.memaddrs = s.memaddrs ∧
    mid.be = s.be ∧
    mid.locals = s.locals ∧
    globN mid "heap_ptr" = globN s "heap_ptr" ∧
    globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
    globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" ∧
    mid.globals.lookup gname = some (.val (.word vw)) ∧
    (∀ k : MlS, k ≠ gname → s.globals.lookup k = mid.globals.lookup k) := by
  dsimp only
  obtain ⟨gn, hgn_in, hgn_eq⟩ := hg_mem
  obtain ⟨w0, hw0⟩ := hAR.2.2.2.2.2.2.2.2.2 gn hgn_in
  unfold GlobalWord at hw0
  rw [hgn_eq] at hw0
  have heval : evaluateHOLFiniteState s (.seq (.assign .global gname (.const vw)) cont) =
      evaluateHOLFiniteState (setGlobalHOLFinite gname (.val (.word vw)) s) cont := by
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
    simp [evalHOLExact, isValidValueHOLFinite, isValidValueHOLExact,
      lookupKvarHOLFinite, lookupKvarHOLExact, hw0,
      shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite]
  obtain ⟨hne1, hne2, hne3⟩ := hnot_arena
  set mid := setGlobalHOLFinite gname (.val (.word vw)) s
  have e1 : globN mid "heap_ptr" = globN s "heap_ptr" := by
    simp [mid, setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne1]
  have e2 : globN mid "scratch_ptr" = globN s "scratch_ptr" := by
    simp [mid, setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne2]
  have e3 : globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    simp [mid, setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE, hne3]
  have hAR_mid : ArenaReady mid := by
    refine ⟨guestInv_congr (s := s) rfl rfl rfl rfl hAR.1, ?_⟩
    unfold ArenaOK
    rw [e1, e3, e2]
    refine ⟨hAR.2.1, hAR.2.2.1, hAR.2.2.2.1, hAR.2.2.2.2.1, hAR.2.2.2.2.2.1,
      hAR.2.2.2.2.2.2.1, hAR.2.2.2.2.2.2.2.1, hAR.2.2.2.2.2.2.2.2.1, ?_⟩
    intro g hg
    by_cases hgv : ofString g = gname
    · exact ⟨vw, by simp [mid, GlobalWord, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hgv]⟩
    · obtain ⟨wg, hwg⟩ := hAR.2.2.2.2.2.2.2.2.2 g hg
      exact ⟨wg, by simp [mid, GlobalWord, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hgv, Ne.symm hgv]; exact hwg⟩
  exact ⟨heval, hAR_mid, rfl, rfl, rfl, rfl, e1, e2, e3,
    by simp [mid, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
    fun k hk => by simp [mid, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk, Ne.symm hk]⟩

private theorem seq_call_alloc_global_exp_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (gname : MlS) (argExp : ExpHOL 64) (nw : BitVec 64) (cont : ProgHOL 64)
    (hAR : ArenaReady s)
    (harg_ev : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [argExp] = some [.val (.word nw)])
    (hnot_arena : gname ≠ ofString "heap_ptr" ∧ gname ≠ ofString "scratch_ptr" ∧ gname ≠ ofString "frame_mem_ptr")
    (hnt : (evaluateHOLFiniteState s
      (.seq (.call (some (some (.global, gname), none)) (ofString "alloc") [argExp])
        cont)).1 ≠ some .timeOut)
    (hres : WkBal.Resumes (evaluateHOLFiniteState s
      (.seq (.call (some (some (.global, gname), none)) (ofString "alloc") [argExp])
        cont)).1) :
    ∃ (pw qw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      pw.toNat = globN s "heap_ptr" ∧
      qw.toNat = pw.toNat + (nw.toNat + 7) / 8 * 8 ∧
      globN mid "heap_ptr" = qw.toNat ∧
      pw.toNat ≤ qw.toNat ∧
      pw.toNat % 8 = 0 ∧
      ArenaReady mid ∧
      mid.memory = s.memory ∧
      mid.memaddrs = s.memaddrs ∧
      mid.be = s.be ∧
      mid.locals = s.locals ∧
      globN mid "scratch_ptr" = globN s "scratch_ptr" ∧
      globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" ∧
      mid.globals.lookup gname = some (.val (.word pw)) ∧
      (∀ k : MlS, k ≠ ofString "heap_ptr" → k ≠ gname → s.globals.lookup k = mid.globals.lookup k) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      WkBal.Resumes (evaluateHOLFiniteState mid cont).1 ∧
      evaluateHOLFiniteState s
        (.seq (.call (some (some (.global, gname), none)) (ofString "alloc") [argExp])
          cont) = evaluateHOLFiniteState mid cont := by
  have hcall_eq : evaluateHOLFiniteState s
      (.call (some (some (.global, gname), none)) (ofString "alloc") [argExp]) =
      evaluateHOLFiniteState s
        (.call (some (some (.global, gname), none)) (ofString "alloc") [.const nw]) := by
    have hconst_ev : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.const nw] = some [.val (.word nw)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
    rw [evaluateHOLFiniteState_call, evaluateHOLFiniteState_call, harg_ev, hconst_ev]
  have hseq_eq : evaluateHOLFiniteState s
      (.seq (.call (some (some (.global, gname), none)) (ofString "alloc") [argExp]) cont) =
      evaluateHOLFiniteState s
        (.seq (.call (some (some (.global, gname), none)) (ofString "alloc") [.const nw]) cont) := by
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_seq_line780, hcall_eq]
  rw [hseq_eq] at hnt hres ⊢
  exact WkBal.seq_call_alloc_global_resumes s gname nw cont hAR hnot_arena hnt hres

private theorem worldStepIn_with_locals_right {F : Type}
    {T : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (hQ : ∀ S' Nd', Q s r post S' Nd' → Q s r { post with locals := L, clock := k } S' Nd')
    (h : WorldStepIn T R gw keep Q s r post) :
    WorldStepIn T R gw keep Q s r { post with locals := L, clock := k } := by
  obtain ⟨hAp, hhp, hgk, hrk, hW⟩ := h
  refine ⟨(arenaReady_with_locals post L k).2 hAp, hhp, hgk, hrk, fun S Nd hWT hTS hD => ?_⟩
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hq⟩ := hW S Nd hWT hTS hD
  have hWT_L : WorldTypedWith { post with locals := L, clock := k } S' Nd' :=
    ⟨(tablesTyped_with_locals post L k S').2 hWT'.1, hWT'.2.1, hWT'.2.2.1, hWT'.2.2.2⟩
  exact ⟨S', Nd', hsub, hWT_L, hOG, hFO, hQ S' Nd' hq⟩

private theorem fixedTyped_state_init {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hag : AllocatorGrows s post)
    (hF : FixedTyped s)
    (hbuf : R10Shards.P26_P28.FreshBufsOK s post)
    (hjc_nz : globN post "journal_cap" ≠ 0)
    (hj_8 : (globN post "journal") % 8 = 0)
    (hj_in : Inside (globN post "journal", 32 * globN post "journal_cap")
      (globN s "heap_ptr") (globN post "heap_ptr"))
    (hdisj_buf_jr : ∀ gn ∈ globalBuffers,
      (globN post gn.1 ≠ globN s gn.1 ∧ globN post gn.1 ≠ 0) →
      Disj (globN post gn.1, gn.2) (globN post "journal", 32 * globN post "journal_cap"))
    (hbo_eq : blockOutObjects post = blockOutObjects s)
    (hbal_eq : balObjects post = balObjects s) :
    FixedTyped post ∧
    (∀ o ∈ fixedObjects post, o ∈ fixedObjects s ∨ o = (0, 0) ∨
      Inside o (globN s "heap_ptr") (globN post "heap_ptr")) := by
  let post_j : PanSemStateFiniteExact 64 F :=
    setGlobalHOLFinite (ofString "journal_cap") (.val (.word (BitVec.ofNat 64 (globN s "journal_cap"))))
      (setGlobalHOLFinite (ofString "journal") (.val (.word (BitVec.ofNat 64 (globN s "journal")))) post)
  have hlt_jc_s : globN s "journal_cap" < 2 ^ 64 := by
    obtain ⟨w, hw⟩ := hAs.2.2.2.2.2.2.2.2.2 "journal_cap" (by decide)
    unfold GlobalWord at hw; unfold globN; rw [hw]; exact w.isLt
  have hlt_j_s : globN s "journal" < 2 ^ 64 := by
    obtain ⟨w, hw⟩ := hAs.2.2.2.2.2.2.2.2.2 "journal" (by decide)
    unfold GlobalWord at hw; unfold globN; rw [hw]; exact w.isLt
  have hpj_hp : globN post_j "heap_ptr" = globN post "heap_ptr" := by
    simp [post_j, setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "journal_cap" ≠ ofString "heap_ptr" by decide,
      show ofString "journal" ≠ ofString "heap_ptr" by decide]
  have hpj_sp : globN post_j "scratch_ptr" = globN post "scratch_ptr" := by
    simp [post_j, setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "journal_cap" ≠ ofString "scratch_ptr" by decide,
      show ofString "journal" ≠ ofString "scratch_ptr" by decide]
  have hpj_fmp : globN post_j "frame_mem_ptr" = globN post "frame_mem_ptr" := by
    simp [post_j, setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "journal_cap" ≠ ofString "frame_mem_ptr" by decide,
      show ofString "journal" ≠ ofString "frame_mem_ptr" by decide]
  have hAp_j : ArenaReady post_j := by
    refine ⟨guestInv_congr (s := post) rfl rfl rfl rfl hAp.1, ?_⟩
    unfold ArenaOK
    rw [hpj_hp, hpj_fmp, hpj_sp]
    refine ⟨hAp.2.1, hAp.2.2.1, hAp.2.2.2.1, hAp.2.2.2.2.1, hAp.2.2.2.2.2.1,
      hAp.2.2.2.2.2.2.1, hAp.2.2.2.2.2.2.2.1, hAp.2.2.2.2.2.2.2.2.1, ?_⟩
    intro g hg
    by_cases h1 : ofString g = ofString "journal_cap"
    · exact ⟨BitVec.ofNat 64 (globN s "journal_cap"),
        by simp [post_j, GlobalWord, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1]⟩
    · by_cases h2 : ofString g = ofString "journal"
      · exact ⟨BitVec.ofNat 64 (globN s "journal"),
          by simp [post_j, GlobalWord, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            h1, Ne.symm h1, h2, show ofString "journal_cap" ≠ ofString "journal" by decide]⟩
      · obtain ⟨wg, hwg⟩ := hAp.2.2.2.2.2.2.2.2.2 g hg
        exact ⟨wg, by simp [post_j, GlobalWord, setGlobalHOLFinite, HolFiniteMapExact.lookup_update,
          FUPDATE, h1, Ne.symm h1, h2, Ne.symm h2]; exact hwg⟩
  have hag_j : AllocatorGrows s post_j := by
    refine ⟨by rw [hpj_hp]; exact hag.1, by rw [hpj_sp]; exact hag.2⟩
  have hpj_jc : globN post_j "journal_cap" = globN s "journal_cap" := by
    simp only [post_j, setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE, ↓reduceIte,
      BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hlt_jc_s
  have hpj_j : globN post_j "journal" = globN s "journal" := by
    simp only [post_j, setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "journal_cap" ≠ ofString "journal" by decide, ↓reduceIte, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hlt_j_s
  have hpj_gb : ∀ gn ∈ globalBuffers, globN post_j gn.1 = globN post gn.1 := by
    intro gn hgn
    have h1 : ofString "journal_cap" ≠ ofString gn.1 := by revert gn hgn; decide
    have h2 : ofString "journal" ≠ ofString gn.1 := by revert gn hgn; decide
    simp [post_j, setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2]
  have hpj_bo : blockOutObjects post_j = blockOutObjects post := by
    have hbo_g : globN post_j "bo" = globN post "bo" := hpj_gb ("bo", 88) (by decide)
    have hm_eq : ∀ a, memW post_j a = memW post a := fun _ => rfl
    simp only [blockOutObjects, hbo_g, hm_eq]
  have hpj_bal : balObjects post_j = balObjects post := by
    have hba_g : globN post_j "bal_accounts" = globN post "bal_accounts" := by
      simp [post_j, setGlobalHOLFinite, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "journal_cap" ≠ ofString "bal_accounts" by decide,
        show ofString "journal" ≠ ofString "bal_accounts" by decide]
    have hm_eq : ∀ a, memW post_j a = memW post a := fun _ => rfl
    have hbr : balRecords post_j = balRecords post := by
      change (if globN post_j "bal_accounts" = 0 then _ else _) = (if globN post "bal_accounts" = 0 then _ else _)
      rw [hba_g]; rfl
    have htv : ∀ t, htabValues post_j t = htabValues post t := fun _ => rfl
    have hlo : ∀ l esz, lstObjects post_j l esz = lstObjects post l esz := fun _ _ => rfl
    simp only [balObjects, hbr, hm_eq, htv, hlo]
  have hbuf_j : R10Shards.P26_P28.FreshBufsOK s post_j := by
    refine ⟨fun gn hgn => ?_, ?_⟩
    · rw [hpj_gb gn hgn, hpj_hp]; exact hbuf.1 gn hgn
    · rw [List.pairwise_iff_getElem]
      have hpw := List.pairwise_iff_getElem.1 hbuf.2
      intro i1 i2 hi1 hi2 hlt
      have hg1 := hpj_gb globalBuffers[i1] (List.getElem_mem hi1)
      have hg2 := hpj_gb globalBuffers[i2] (List.getElem_mem hi2)
      rw [hg1, hg2]
      exact hpw i1 i2 hi1 hi2 hlt
  obtain ⟨hF_pj, hfrom_pj⟩ := R10Shards.P26_P28.fixedTyped_of_freshBufsOK hAs hAp_j hag_j hF
    hpj_j hpj_jc (hpj_bo.trans hbo_eq) (hpj_bal.trans hbal_eq) hbuf_j
  let gbs_post := globalBuffers.map (fun gn => (globN post gn.1, if globN post gn.1 = 0 then 0 else gn.2))
  let gbs_pj := globalBuffers.map (fun gn => (globN post_j gn.1, if globN post_j gn.1 = 0 then 0 else gn.2))
  have hgbs_eq : gbs_post = gbs_pj := by
    apply List.map_congr_left
    intro gn hgn; simp [hpj_gb gn hgn]
  let jr_post : Ivl := (globN post "journal", 32 * globN post "journal_cap")
  let jr_s : Ivl := (if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")
  have hfix_post_eq : fixedObjects post = gbs_post ++ [jr_post] ++ (blockOutObjects s ++ balObjects s) := by
    unfold fixedObjects
    simp only [hjc_nz, ↓reduceIte, hbo_eq, hbal_eq, List.append_assoc]
    rfl
  have hfix_pj_eq : fixedObjects post_j = gbs_pj ++ [jr_s] ++ (blockOutObjects s ++ balObjects s) := by
    unfold fixedObjects
    simp only [hpj_jc, hpj_j, hpj_bo, hpj_bal, hbo_eq, hbal_eq, List.append_assoc]
    rfl
  have hal_jr : Allocated post jr_post ∧ WordsOK post jr_post := by
    have hhl_he : heapLimit ≤ heapEnd := by decide
    have hlo : sourceBase ≤ jr_post.1 := le_trans hAs.2.1 hj_in.1
    have hhi : jr_post.1 + jr_post.2 ≤ heapEnd := le_trans hj_in.2 (le_trans hAp.2.2.1 hhl_he)
    exact ⟨Or.inl ⟨hlo, hj_in.2⟩,
      R10Shards.P26_P28.wordsOK_of_inside_heap hAp.1 hj_8 (show (32 * globN post "journal_cap") % 8 = 0 by omega) hlo hhi⟩
  have hfrom_post : ∀ o ∈ fixedObjects post, o ∈ fixedObjects s ∨ o = (0, 0) ∨
      Inside o (globN s "heap_ptr") (globN post "heap_ptr") := by
    intro o ho
    rw [hfix_post_eq] at ho
    rcases List.mem_append.1 ho with ho12 | ho_bb
    · rcases List.mem_append.1 ho12 with ho_gb | ho_jr
      · have hm_pj : o ∈ fixedObjects post_j := by
          rw [hfix_pj_eq, ← hgbs_eq]
          exact List.mem_append_left _ (List.mem_append_left _ ho_gb)
        rw [← hpj_hp]
        exact hfrom_pj o hm_pj
      · simp only [List.mem_singleton] at ho_jr; subst ho_jr
        exact Or.inr (Or.inr hj_in)
    · left
      unfold fixedObjects
      rcases List.mem_append.1 ho_bb with ho_bo | ho_bal
      · exact List.mem_append_left _ (List.mem_append_right _ ho_bo)
      · exact List.mem_append_right _ ho_bal
  refine ⟨⟨?_, ?_⟩, hfrom_post⟩
  · intro i hi
    rw [hfix_post_eq] at hi
    rcases List.mem_append.1 hi with hi12 | hi_bb
    · rcases List.mem_append.1 hi12 with hi_gb | hi_jr
      · have hm_pj : i ∈ fixedObjects post_j := by
          rw [hfix_pj_eq, ← hgbs_eq]
          exact List.mem_append_left _ (List.mem_append_left _ hi_gb)
        rcases hF_pj.1 i hm_pj with h0 | ⟨hal, hw⟩
        · exact Or.inl h0
        · have hal' : Allocated post i := by
            unfold Allocated at hal ⊢; rw [hpj_hp, hpj_sp] at hal; exact hal
          exact Or.inr ⟨hal', R10Shards.P26_P28.wordsOK_transfer hAp_j.1 hAp.1 hw⟩
      · simp only [List.mem_singleton] at hi_jr; subst hi_jr
        exact Or.inr hal_jr
    · have hm_pj : i ∈ fixedObjects post_j := by
        rw [hfix_pj_eq]
        exact List.mem_append_right _ hi_bb
      rcases hF_pj.1 i hm_pj with h0 | ⟨hal, hw⟩
      · exact Or.inl h0
      · have hal' : Allocated post i := by
          unfold Allocated at hal ⊢; rw [hpj_hp, hpj_sp] at hal; exact hal
        exact Or.inr ⟨hal', R10Shards.P26_P28.wordsOK_transfer hAp_j.1 hAp.1 hw⟩
  · have hpw_pj := hF_pj.2
    rw [hfix_pj_eq, ← hgbs_eq] at hpw_pj
    obtain ⟨hpw_12, hpw_bb, hcross_12_bb⟩ := List.pairwise_append.1 hpw_pj
    obtain ⟨hpw_gb, _, _⟩ := List.pairwise_append.1 hpw_12
    rw [hfix_post_eq]
    refine List.pairwise_append.2 ⟨List.pairwise_append.2 ⟨hpw_gb, List.pairwise_singleton _ _, ?_⟩, hpw_bb, ?_⟩
    · intro x hx y hy
      simp only [List.mem_singleton] at hy; subst hy
      obtain ⟨gn, hgn, rfl⟩ := List.mem_map.1 hx
      by_cases hsame : globN post gn.1 = globN s gn.1
      · rw [hsame]
        have hm_s : (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2) ∈ fixedObjects s := by
          unfold fixedObjects
          apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
          exact List.mem_map.2 ⟨gn, hgn, rfl⟩
        rcases hF.1 _ hm_s with h0 | ⟨hal_s, _⟩
        · exact Or.inl h0
        · exact (InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_s hj_in).flip
      · by_cases hz : globN post gn.1 = 0
        · exact Or.inl (by simp [hz])
        · simpa [hz] using hdisj_buf_jr gn hgn ⟨hsame, hz⟩
    · intro x hx y hy
      rcases List.mem_append.1 hx with hx_gb | hx_jr
      · exact hcross_12_bb x (List.mem_append_left _ hx_gb) y hy
      · simp only [List.mem_singleton] at hx_jr; subst hx_jr
        have hy_s : y ∈ fixedObjects s := by
          unfold fixedObjects
          rcases List.mem_append.1 hy with hy_bo | hy_bal
          · exact List.mem_append_left _ (List.mem_append_right _ hy_bo)
          · exact List.mem_append_right _ hy_bal
        rcases hF.1 y hy_s with hy0 | ⟨hal_y, _⟩
        · exact Or.inr (Or.inl hy0)
        · exact InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAs.2 hAp.2 hal_y hj_in

private abbrev stateInitAfterDwProg (tVar rootVar : MlS) : ProgHOL 64 :=
  .seq (.store (.op .add [.var .global (ofString "ws"), .const 24#64]) (.var .local rootVar))
    (.decCall tVar .one (ofString "htab_new") [.const 32#64, .const 64#64]
      (.seq (.store (.op .add [.var .global (ofString "ws"), .const 32#64]) (.var .local tVar))
      (.seq (.call (some (some (.global, ofString "bs"), none)) (ofString "alloc") [.const 80#64])
      (.seq (.store (.op .add [.var .global (ofString "bs"), .const 0#64]) (.var .global (ofString "ws")))
      (.seq (.call (some (some (.local, tVar), none)) (ofString "htab_new") [.const 20#64, .const 256#64])
      (.seq (.store (.op .add [.var .global (ofString "bs"), .const 8#64]) (.var .local tVar))
      (.seq (.call (some (some (.local, tVar), none)) (ofString "htab_new") [.const 20#64, .const 256#64])
      (.seq (.store (.op .add [.var .global (ofString "bs"), .const 16#64]) (.var .local tVar))
      (.seq (.call (some (some (.local, tVar), none)) (ofString "htab_new") [.const 52#64, .const 256#64])
      (.seq (.store (.op .add [.var .global (ofString "bs"), .const 24#64]) (.var .local tVar))
      (.seq (.call (some (some (.local, tVar), none)) (ofString "htab_new") [.const 20#64, .const 64#64])
      (.seq (.store (.op .add [.var .global (ofString "bs"), .const 32#64]) (.var .local tVar))
      (.seq (.call (some (some (.local, tVar), none)) (ofString "htab_new") [.const 52#64, .const 64#64])
      (.seq (.store (.op .add [.var .global (ofString "bs"), .const 40#64]) (.var .local tVar))
      (.seq (.call (some (some (.local, tVar), none)) (ofString "htab_new") [.const 32#64, .const 64#64])
      (.seq (.store (.op .add [.var .global (ofString "bs"), .const 48#64]) (.var .local tVar))
      (.seq (.store (.op .add [.var .global (ofString "bs"), .const 56#64]) (.const 0#64))
      (.seq (.store (.op .add [.var .global (ofString "bs"), .const 64#64]) (.const 0#64))
      (.seq (.call (some (some (.local, tVar), none)) (ofString "htab_new") [.const 20#64, .const 256#64])
      (.seq (.store (.op .add [.var .global (ofString "bs"), .const 72#64]) (.var .local tVar))
      (.seq (.call (some (some (.global, ofString "sk_buf"), none)) (ofString "alloc") [.const 64#64])
      (.seq (.assign .global (ofString "journal_cap") (.const 524288#64))
      (.seq (.call (some (some (.global, ofString "journal"), none)) (ofString "alloc")
              [.panop .mul [.var .global (ofString "journal_cap"), .const 32#64]])
      (.seq (.assign .global (ofString "journal_n") (.const 0#64))
      (.seq (.assign .global (ofString "ts") (.const 0#64))
            (.return (.const 0#64)))))))))))))))))))))))))))

private theorem state_init_body_eq :
    sourceFnBody Guest.Software.guestFn_state_init =
      .seq (.call (some (some (.global, ofString "ws"), none)) (ofString "alloc") [.const 40#64])
      (.seq (.store (.op .add [.var .global (ofString "ws"), .const 0#64]) (.var .local (ofString "nodedb")))
      (.seq (.store (.op .add [.var .global (ofString "ws"), .const 8#64]) (.var .local (ofString "state_root")))
      (.seq (.store (.op .add [.var .global (ofString "ws"), .const 16#64]) (.var .local (ofString "codedb")))
        (.decCall (ofString "root") .one (ofString "decode_witness_to_mpt")
          [.var .local (ofString "nodedb"), .var .local (ofString "state_root")]
          (stateInitAfterDwProg (ofString "t") (ofString "root")))))) := by
  simp only [sourceFnBody, Guest.Software.guestFn_state_init,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  rfl

theorem wk_state_init_of_decode_witness
    {ExtraGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat → Prop}
    (hdw : DecodeWitnessToMptSpec @ExtraGuard)
    (heg_tr : ∀ {F : Type} (s b : PanSemStateFiniteExact 64 F) (db : Nat),
      ArenaReady s → ArenaReady b → b.be = s.be →
      globN s "heap_ptr" ≤ globN b "heap_ptr" →
      FrameOutside s b [freeGap s] (heapFree s) →
      ExtraGuard s db → ExtraGuard b db) :
    WorldReturnsIn
      (fun s => StateInitReady s ∧ ExtraGuard s (locN s "nodedb"))
      (fun s => if locN s "codedb" = 0 then [] else [locN s "codedb"])
      (fun _ => [])
      ["bs", "heap_ptr", "journal", "journal_cap", "journal_n", "scratch_ptr", "sk_buf", "ts", "ws"]
      [("ws", []), ("bs", []),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetStateInit (ofString "state_init") := by
  refine ⟨_, _, _, lookup_state_init_add, ?_⟩
  intro F s hcode ⟨hSIR, hEG_s⟩ hvalid hnt hret_ex
  obtain ⟨values, hlook_fn⟩ := hvalid
  obtain ⟨dbw, srw, cdw, _, hs_db, hs_sr, hs_cd⟩ :=
    R10Shards.P26_P28.lookupCode_three_words (by decide) (by decide) (by decide)
      lookup_state_init_add hlook_fn
  have hdb_nat : locN s "nodedb" = dbw.toNat := by simp [locN, hs_db]
  have hcd_nat : locN s "codedb" = cdw.toNat := by simp [locN, hs_cd]
  have hAR0 : ArenaReady s := hSIR.1
  have hWOK0 : WorldOK s := stateInitReady_worldOK s hSIR
  obtain ⟨S_sir, Nd_sir, hWT_sir, hcd_sir⟩ := hSIR.2
  obtain ⟨v_ret_outer, hv_ret_outer⟩ := hret_ex
  have hres0_wk : WkBal.Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_state_init)).1 :=
    Or.inl ⟨v_ret_outer, hv_ret_outer⟩
  rw [state_init_body_eq] at hnt hres0_wk hv_ret_outer ⊢
  -- Step 1: `ws := alloc(40)`
  obtain ⟨pws, qws, s0, hpws_eq, hqws_eq, hs0_hp, hpws_le_qws, hpws8, hAR_s0,
      hs0_m, hs0_ma, hs0_be, hs0_l, hs0_sp, hs0_fmp, hs0_ws, hg_s0, hnt_s0, hres_s0, heq_s0⟩ :=
    WkBal.seq_call_alloc_global_resumes s (ofString "ws") 40#64 _ hAR0
      ⟨by decide, by decide, by decide⟩ hnt hres0_wk
  have hqws_val : qws.toNat = pws.toNat + 40 := by
    have h40 : ((40#64 : BitVec 64).toNat + 7) / 8 * 8 = 40 := by decide
    rw [hqws_eq, h40]
  have hpws_lo : sourceBase ≤ pws.toNat := by rw [hpws_eq]; exact hAR0.2.1
  have hpws_hi : pws.toNat + 40 ≤ heapLimit := by
    have := hAR_s0.2.2.1; omega
  -- Step 2: `store(ws + 0, nodedb)`
  have hs0_db_ev : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
      (.var .local (ofString "nodedb")) = some (.val (.word dbw)) := by
    simp [evalHOLExact, hs0_l, hs_db]
  obtain ⟨heq_s0a, hAR_s0a, hs0a_g, hs0a_l, hs0a_be, _, hmw_ws0, hmw_ne_s0a, hfr_s0a⟩ :=
    seq_store_global_rec_slot s0 (ofString "ws") 40 pws 0#64 dbw (.var .local (ofString "nodedb")) _
      hAR_s0 hs0_ws hpws_lo hpws_hi hpws8 (by decide) (by decide) hs0_db_ev
  set s0a : PanSemStateFiniteExact 64 F :=
    { s0 with memory := fun a => if a = pws + 0#64 then .word dbw else s0.memory a }
  rw [heq_s0a] at hnt_s0 hres_s0
  -- Step 3: `store(ws + 8, state_root)`
  have hs0a_ws : s0a.globals.lookup (ofString "ws") = some (.val (.word pws)) := by rw [hs0a_g]; exact hs0_ws
  have hs0a_sr_ev : @evalHOLExact 64 F _ s0a.toExact (fun a => Classical.propDecidable (s0a.memaddrs a))
      (.var .local (ofString "state_root")) = some (.val (.word srw)) := by
    simp [evalHOLExact, hs0a_l, hs0_l, hs_sr]
  obtain ⟨heq_s0b, hAR_s0b, hs0b_g, hs0b_l, hs0b_be, _, hmw_ws8, hmw_ne_s0b, hfr_s0b⟩ :=
    seq_store_global_rec_slot s0a (ofString "ws") 40 pws 8#64 srw (.var .local (ofString "state_root")) _
      hAR_s0a hs0a_ws hpws_lo hpws_hi hpws8 (by decide) (by decide) hs0a_sr_ev
  set s0b : PanSemStateFiniteExact 64 F :=
    { s0a with memory := fun a => if a = pws + 8#64 then .word srw else s0a.memory a }
  rw [heq_s0b] at hnt_s0 hres_s0
  -- Step 4: `store(ws + 16, codedb)`
  have hs0b_ws : s0b.globals.lookup (ofString "ws") = some (.val (.word pws)) := by rw [hs0b_g]; exact hs0a_ws
  have hs0b_cd_ev : @evalHOLExact 64 F _ s0b.toExact (fun a => Classical.propDecidable (s0b.memaddrs a))
      (.var .local (ofString "codedb")) = some (.val (.word cdw)) := by
    simp [evalHOLExact, hs0b_l, hs0a_l, hs0_l, hs_cd]
  obtain ⟨heq_s0c, hAR_s0c, hs0c_g, hs0c_l, hs0c_be, _, hmw_ws16, hmw_ne_s0c, hfr_s0c⟩ :=
    seq_store_global_rec_slot s0b (ofString "ws") 40 pws 16#64 cdw (.var .local (ofString "codedb")) _
      hAR_s0b hs0b_ws hpws_lo hpws_hi hpws8 (by decide) (by decide) hs0b_cd_ev
  set s0c : PanSemStateFiniteExact 64 F :=
    { s0b with memory := fun a => if a = pws + 16#64 then .word cdw else s0b.memory a }
  rw [heq_s0c] at hnt_s0 hres_s0
  have hs0c_ws : s0c.globals.lookup (ofString "ws") = some (.val (.word pws)) := by rw [hs0c_g]; exact hs0b_ws
  have hs0c_hp : globN s0c "heap_ptr" = qws.toNat := hs0_hp
  have hs0c_sp : globN s0c "scratch_ptr" = globN s "scratch_ptr" := hs0_sp
  have hs0c_fmp : globN s0c "frame_mem_ptr" = globN s "frame_mem_ptr" := hs0_fmp
  have hs0c_be : s0c.be = s.be := hs0c_be.trans (hs0b_be.trans (hs0a_be.trans hs0_be))
  have hhp_0_s0c : globN s "heap_ptr" ≤ globN s0c "heap_ptr" := by omega
  have hfr_s_s0c : FrameOutside s s0c [] (globN s "heap_ptr", globN s0c "heap_ptr" - globN s "heap_ptr") := by
    intro a _ hnhf
    have hno_ws : ¬ CellHits a.toNat (pws.toNat, 40) := by
      intro ⟨c1, c2⟩; dsimp only at c1 c2
      exact hnhf ⟨by dsimp only; omega, by dsimp only; omega⟩
    have hm1 := hfr_s0c a (fun _ h => by cases h) hno_ws
    have hm2 := hfr_s0b a (fun _ h => by cases h) hno_ws
    have hm3 := hfr_s0a a (fun _ h => by cases h) hno_ws
    exact hm1.trans (hm2.trans (hm3.trans (congrFun hs0_m a)))
  have hunhit_s_s0c : ∀ i : Ivl, i.2 ≠ 0 → Allocated s i → R10Shards.P26_P28.IvlUnhit s s0c i := by
    intro i hipos hal
    have hd_hf : Disj i (globN s "heap_ptr", globN s0c "heap_ptr" - globN s "heap_ptr") :=
      (InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAR0.2 hAR_s0c.2 hal
        ⟨le_rfl, by omega⟩).flip
    exact ivlUnhit_of_frameOutside_aligned hipos hfr_s_s0c (fun _ h => by cases h)
      ⟨hAR0.2.2.2.2.2.2.1, by dsimp only; rw [hs0c_hp, hqws_val, hpws_eq]; omega⟩
      (fun _ h => by cases h) hd_hf
  -- Step 5: `decCall "root" .one "decode_witness_to_mpt" [nodedb, state_root]`
  have hs0c_code : s0c.code = originalRuntimeCode := hAR_s0c.1.code
  have hs0c_args : evalListHOLFinite s0c (h := fun a => Classical.propDecidable (s0c.memaddrs a))
      [.var .local (ofString "nodedb"), .var .local (ofString "state_root")] =
      some [.val (.word dbw), .val (.word srw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs0c_l, hs0b_l, hs0a_l, hs0_l, hs_db, hs_sr]
  have hlk_dw := pan_two_word_lookup s0c.code.lookup (ofString "decode_witness_to_mpt")
    (ofString "db") (ofString "root_hash")
    (sourceFnBody Guest.Software.guestFn_decode_witness_to_mpt) dbw srw
    (by decide) (by rw [hs0c_code]; exact lookup_decode_witness_to_mpt_add)
  have heq_pre_dw : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_state_init) =
      evaluateHOLFiniteState s0c
        (.decCall (ofString "root") .one (ofString "decode_witness_to_mpt")
          [.var .local (ofString "nodedb"), .var .local (ofString "state_root")]
          (stateInitAfterDwProg (ofString "t") (ofString "root"))) := by
    rw [state_init_body_eq, heq_s0, heq_s0a, heq_s0b, heq_s0c]
  have hnt_dc := hnt_s0
  have hret_dc : (evaluateHOLFiniteState s0c
      (.decCall (ofString "root") .one (ofString "decode_witness_to_mpt")
        [.var .local (ofString "nodedb"), .var .local (ofString "state_root")]
        (stateInitAfterDwProg (ofString "t") (ofString "root")))).1 = some (.returned v_ret_outer) := by
    rw [← heq_pre_dw, state_init_body_eq]; exact hv_ret_outer
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hs0c_args] at hnt_dc hret_dc
  dsimp only at hnt_dc hret_dc
  rw [hlk_dw] at hnt_dc hret_dc
  dsimp only at hnt_dc hret_dc
  by_cases hcz : s0c.clock = 0
  · rw [if_pos hcz] at hnt_dc; exact absurd rfl hnt_dc
  · rw [if_neg hcz] at hnt_dc hret_dc
    let cmap_dw := ((HolFiniteMapExact.empty.update (ofString "db", ValueHOL.val (.word dbw))).update
      (ofString "root_hash", ValueHOL.val (.word srw)))
    let ent_dw := callEntryStateHOLFinite s0c cmap_dw
    have hent_db : locN ent_dw "db" = dbw.toNat := by
      have hl_db : cmap_dw.lookup (ofString "db") = some (.val (.word dbw)) := by
        simp [cmap_dw, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "root_hash" ≠ ofString "db" by decide]
      simp [locN, ent_dw, callEntryStateHOLFinite, hl_db]
    have hAR_ent : ArenaReady ent_dw :=
      (arenaReady_with_locals s0c cmap_dw (s0c.clock - 1)).2 hAR_s0c
    have hent_guard : ArenaReady ent_dw ∧ ExtraGuard ent_dw (locN ent_dw "db") := by
      refine ⟨hAR_ent, ?_⟩
      rw [hent_db, ← hdb_nat]
      refine heg_tr s ent_dw (locN s "nodedb") hAR0 hAR_ent hs0c_be hhp_0_s0c ?_ hEG_s
      intro a _ hnhf
      exact hfr_s_s0c a (fun _ h => by cases h) (fun ⟨c1, c2⟩ => by
        dsimp only at c1 c2
        exact hnhf ⟨c1, by unfold heapFree; dsimp only; have := hAR_s0c.2.2.1; omega⟩)
    rcases hrun_dw : evaluateHOLFiniteState ent_dw
        (sourceFnBody Guest.Software.guestFn_decode_witness_to_mpt) with ⟨res_dw, cpost_dw⟩
    simp only [ent_dw, cmap_dw] at hrun_dw
    simp only [hrun_dw] at hnt_dc hret_dc
    have hnt_ent_dw : (evaluateHOLFiniteState ent_dw
        (sourceFnBody Guest.Software.guestFn_decode_witness_to_mpt)).1 ≠ some .timeOut := by
      simp only [ent_dw, cmap_dw, hrun_dw]; rintro rfl; simp at hnt_dc
    have hspec_dw := FunSpec.at_lookup hdw s0c hs0c_code
      [.val (.word dbw), .val (.word srw)]
      (sourceFnBody Guest.Software.guestFn_decode_witness_to_mpt) cmap_dw .one hlk_dw
      hent_guard hnt_ent_dw
    simp only [ent_dw, cmap_dw, hrun_dw] at hspec_dw
    cases res_dw with
    | none => simp at hret_dc
    | some cr =>
      cases cr with
      | timeOut => simp at hnt_dc
      | error | «break» | «continue» | finalFfi _ | exception _ _ => simp at hret_dc
      | returned v_dw =>
        obtain ⟨hAp_dw, hbe_dw, hhp_dw, hsp_dw, hgk_dw, hfr_dw, hret_dw⟩ :=
          hspec_dw (Or.inl ⟨v_dw, rfl⟩)
        -- Obtain `rootw` from `hret_dw` instantiated at `Nd_sir`:
        have hNH_sir_ent : NodeHeap ent_dw Nd_sir := by
          have hag_0_ent : AllocatorGrows s ent_dw := ⟨hhp_0_s0c, by change globN s0c "scratch_ptr" ≤ _; omega⟩
          exact (R10Shards.P26_P28.nodeHeap_congr_bytes hAR0.1 hAR_ent.1 hag_0_ent hWT_sir.2.2.2.1
            (fun n hn => hunhit_s_s0c _ (by unfold nodeIvl nodeSize; split_ifs <;> omega) (hWT_sir.2.2.2.1.1 n hn).2.1)
            (fun n hn h12 hp_nz k hk => by
              rcases (hWT_sir.2.2.2.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, _, _⟩
              · exact absurd h0 hp_nz
              · exact R10Shards.P26_P28.memB_eq_of_ivlUnhit (hunhit_s_s0c _ hp_nz hal_p) hs0c_be
                  (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hAR0.2 hal_p).2
                  ⟨by dsimp; omega, by dsimp; omega⟩)).1
        have hnd_sir_alloc : ∀ o ∈ nodeExtents ent_dw Nd_sir, o.2 = 0 ∨ Allocated ent_dw o := by
          intro o ho
          unfold nodeExtents at ho
          obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
          rcases hno with rfl | rfl
          · exact Or.inr (hNH_sir_ent.1 n hn).2.1
          · unfold nodePath; split_ifs with hc
            · rcases (hNH_sir_ent.1 n hn).2.2.2.2.2.2.1 hc.1 with h0 | ⟨_, hal, _⟩
              · exact absurd h0 hc.2
              · exact Or.inr hal
            · exact Or.inl rfl
        obtain ⟨rootw, _, hv_dw0, _, _, _, _⟩ := hret_dw Nd_sir hNH_sir_ent hnd_sir_alloc v_dw rfl
        subst hv_dw0
        have hsh_rw : (shapeEqHOL (shapeOfHOLExact (.val (.word rootw) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word rootw) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        dsimp only at hnt_dc hret_dc
        rw [if_pos hsh_rw] at hnt_dc hret_dc
        set s1 := setVarHOLFinite (ofString "root") (.val (.word rootw))
          { cpost_dw with locals := s0c.locals }
        have heq_dc_r : (evaluateHOLFiniteState s0c
            (.decCall (ofString "root") .one (ofString "decode_witness_to_mpt")
              [.var .local (ofString "nodedb"), .var .local (ofString "state_root")]
              (stateInitAfterDwProg (ofString "t") (ofString "root")))).1 =
            (evaluateHOLFiniteState s1 (stateInitAfterDwProg (ofString "t") (ofString "root"))).1 := by
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hs0c_args]
          dsimp only; rw [hlk_dw]; dsimp only
          rw [if_neg hcz, hrun_dw]
          dsimp only; rw [if_pos hsh_rw]
        have heq_dc_s : (evaluateHOLFiniteState s0c
            (.decCall (ofString "root") .one (ofString "decode_witness_to_mpt")
              [.var .local (ofString "nodedb"), .var .local (ofString "state_root")]
              (stateInitAfterDwProg (ofString "t") (ofString "root")))).2 =
            { (evaluateHOLFiniteState s1 (stateInitAfterDwProg (ofString "t") (ofString "root"))).2 with
              locals := HolFiniteMapExact.resVarEq
                (evaluateHOLFiniteState s1 (stateInitAfterDwProg (ofString "t") (ofString "root"))).2.locals
                (ofString "root", s0c.locals.lookup (ofString "root")) } := by
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite, hs0c_args]
          dsimp only; rw [hlk_dw]; dsimp only
          rw [if_neg hcz, hrun_dw]
          dsimp only; rw [if_pos hsh_rw]
        have hAR_s1 : ArenaReady s1 :=
          (arenaReady_with_locals cpost_dw s1.locals cpost_dw.clock).2 hAp_dw
        have hs1_be : s1.be = s.be := hbe_dw.trans hs0c_be
        have hs1_sp : globN s1 "scratch_ptr" = globN s "scratch_ptr" := hsp_dw.trans hs0c_sp
        have hs1_fmp : globN s1 "frame_mem_ptr" = globN s "frame_mem_ptr" := by
          have hfmp_dw : globN cpost_dw "frame_mem_ptr" = globN s0c "frame_mem_ptr" :=
            globN_eq_of_lookup (hgk_dw (ofString "frame_mem_ptr") (by decide))
          exact hfmp_dw.trans hs0c_fmp
        have hs1_ws : s1.globals.lookup (ofString "ws") = some (.val (.word pws)) :=
          (hgk_dw (ofString "ws") (by decide)).symm.trans hs0c_ws
        have hhp_s0c_s1 : globN s0c "heap_ptr" ≤ globN s1 "heap_ptr" := by
          change globN s0c "heap_ptr" ≤ globN cpost_dw "heap_ptr"
          exact hhp_dw
        have hnt_s1 : (evaluateHOLFiniteState s1 (stateInitAfterDwProg (ofString "t") (ofString "root"))).1 ≠ some .timeOut :=
          hnt_dc
        have hres_s1 : WkBal.Resumes (evaluateHOLFiniteState s1 (stateInitAfterDwProg (ofString "t") (ofString "root"))).1 :=
          Or.inl ⟨v_ret_outer, hret_dc⟩
        -- Step 6: `store(ws + 24, root)`
        have hs1_root_ev : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
            (.var .local (ofString "root")) = some (.val (.word rootw)) := by
          simp [evalHOLExact, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        dsimp only [stateInitAfterDwProg] at hnt_s1 hres_s1 hret_dc heq_dc_r heq_dc_s
        obtain ⟨heq_s1a, hAR_s1a, hs1a_g, hs1a_l, hs1a_be, _, hmw_ws24, hmw_ne_s1a, hfr_s1a⟩ :=
          seq_store_global_rec_slot s1 (ofString "ws") 40 pws 24#64 rootw (.var .local (ofString "root")) _
            hAR_s1 hs1_ws hpws_lo hpws_hi hpws8 (by decide) (by decide) hs1_root_ev
        set s1a : PanSemStateFiniteExact 64 F :=
          { s1 with memory := fun a => if a = pws + 24#64 then .word rootw else s1.memory a }
        rw [heq_s1a] at hnt_s1 hres_s1 hret_dc heq_dc_r heq_dc_s
        have hs1a_ws : s1a.globals.lookup (ofString "ws") = some (.val (.word pws)) := by rw [hs1a_g]; exact hs1_ws
        have hpws40_s1a : pws.toNat + 40 ≤ globN s1a "heap_ptr" := by
          change pws.toNat + 40 ≤ globN s1 "heap_ptr"
          omega
        -- Step 7: `decCall "t" .one "htab_new" [32, 64]` + `store(ws + 32, t)`
        obtain ⟨tw_ws, s2, htws_lo, htws_hi, hAR_s2, hs2_be, hs2_sp, hs2_fmp,
            hwf_tws, hcnt_tws, hhdr_tws, hfp_tws, hmw_ws32, hmw_ws_other, hfr_s1a_s2,
            _, hg_s2, hnt_s2, hres_s2, heq_s2_r, heq_s2_s⟩ :=
          decCall_htab_new_store_global_slot s1a (ofString "ws") 40 pws 32#64 32#64 64#64 _
            hAR_s1a hpws40_s1a hpws_lo hpws8 (by decide) (by decide) (by decide) hs1a_ws
            (by decide) (by decide) hnt_s1 hres_s1
        -- Step 8: `bs := alloc(80)`
        obtain ⟨pbs, qbs, s3, hpbs_eq, hqbs_eq, hs3_hp, hpbs_le_qbs, hpbs8, hAR_s3,
            hs3_m, hs3_ma, hs3_be, hs3_l, hs3_sp, hs3_fmp, hs3_bs, hg_s3, hnt_s3, hres_s3, heq_s3⟩ :=
          WkBal.seq_call_alloc_global_resumes s2 (ofString "bs") 80#64 _ hAR_s2
            ⟨by decide, by decide, by decide⟩ hnt_s2 hres_s2
        have hqbs_val : qbs.toNat = pbs.toNat + 80 := by
          have h80 : ((80#64 : BitVec 64).toNat + 7) / 8 * 8 = 80 := by decide
          rw [hqbs_eq, h80]
        have hpbs_lo : sourceBase ≤ pbs.toNat := by rw [hpbs_eq]; exact hAR_s2.2.1
        have hpbs_hi : pbs.toNat + 80 ≤ heapLimit := by
          have := hAR_s3.2.2.1; omega
        -- Step 9: `store(bs + 0, ws)`
        have hs3_ws : s3.globals.lookup (ofString "ws") = some (.val (.word pws)) :=
          (hg_s3 (ofString "ws") (by decide) (by decide)).symm.trans
            ((hg_s2 (ofString "ws") (by decide)).symm.trans hs1a_ws)
        have hs3_ws_ev : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
            (.var .global (ofString "ws")) = some (.val (.word pws)) := by
          simp [evalHOLExact, hs3_ws]
        obtain ⟨heq_s3a, hAR_s3a, hs3a_g, hs3a_l, hs3a_be, _, hmw_bs0, _, hfr_s3a⟩ :=
          seq_store_global_rec_slot s3 (ofString "bs") 80 pbs 0#64 pws (.var .global (ofString "ws")) _
            hAR_s3 hs3_bs hpbs_lo hpbs_hi hpbs8 (by decide) (by decide) hs3_ws_ev
        set s3a : PanSemStateFiniteExact 64 F :=
          { s3 with memory := fun a => if a = pbs + 0#64 then .word pws else s3.memory a }
        rw [heq_s3a] at hnt_s3 hres_s3 heq_s3
        have hs3a_bs : s3a.globals.lookup (ofString "bs") = some (.val (.word pbs)) := by rw [hs3a_g]; exact hs3_bs
        have hpbs80_s3a : pbs.toNat + 80 ≤ globN s3a "heap_ptr" := by
          change pbs.toNat + 80 ≤ globN s3 "heap_ptr"; omega
        -- Step 10: `bs + 8 := htab_new(20, 256)`
        obtain ⟨tb8, s4, htb8_lo, htb8_hi, hAR_s4, hs4_be, hs4_sp, hs4_fmp,
            hwf_tb8, hcnt_tb8, hhdr_tb8, hfp_tb8, hmw_bs8, hmw_bs_o4, hfr_s3a_s4,
            _, hg_s4, hnt_s4, hres_s4, heq_s4⟩ :=
          seq_htab_new_store_global_slot s3a (ofString "bs") 80 pbs 8#64 20#64 256#64 _
            hAR_s3a hpbs80_s3a hpbs_lo hpbs8 (by decide) (by decide) (by decide) hs3a_bs
            (by decide) (by decide) hnt_s3 hres_s3
        have hs4_bs : s4.globals.lookup (ofString "bs") = some (.val (.word pbs)) :=
          (hg_s4 (ofString "bs") (by decide)).symm.trans hs3a_bs
        -- Step 11: `bs + 16 := htab_new(20, 256)`
        obtain ⟨tb16, s5, htb16_lo, htb16_hi, hAR_s5, hs5_be, hs5_sp, hs5_fmp,
            hwf_tb16, hcnt_tb16, hhdr_tb16, hfp_tb16, hmw_bs16, hmw_bs_o5, hfr_s4_s5,
            _, hg_s5, hnt_s5, hres_s5, heq_s5⟩ :=
          seq_htab_new_store_global_slot s4 (ofString "bs") 80 pbs 16#64 20#64 256#64 _
            hAR_s4 (by omega) hpbs_lo hpbs8 (by decide) (by decide) (by decide) hs4_bs
            (by decide) (by decide) hnt_s4 hres_s4
        have hs5_bs : s5.globals.lookup (ofString "bs") = some (.val (.word pbs)) :=
          (hg_s5 (ofString "bs") (by decide)).symm.trans hs4_bs
        -- Step 12: `bs + 24 := htab_new(52, 256)`
        obtain ⟨tb24, s6, htb24_lo, htb24_hi, hAR_s6, hs6_be, hs6_sp, hs6_fmp,
            hwf_tb24, hcnt_tb24, hhdr_tb24, hfp_tb24, hmw_bs24, hmw_bs_o6, hfr_s5_s6,
            _, hg_s6, hnt_s6, hres_s6, heq_s6⟩ :=
          seq_htab_new_store_global_slot s5 (ofString "bs") 80 pbs 24#64 52#64 256#64 _
            hAR_s5 (by omega) hpbs_lo hpbs8 (by decide) (by decide) (by decide) hs5_bs
            (by decide) (by decide) hnt_s5 hres_s5
        have hs6_bs : s6.globals.lookup (ofString "bs") = some (.val (.word pbs)) :=
          (hg_s6 (ofString "bs") (by decide)).symm.trans hs5_bs
        -- Step 13: `bs + 32 := htab_new(20, 64)`
        obtain ⟨tb32, s7, htb32_lo, htb32_hi, hAR_s7, hs7_be, hs7_sp, hs7_fmp,
            hwf_tb32, hcnt_tb32, hhdr_tb32, hfp_tb32, hmw_bs32, hmw_bs_o7, hfr_s6_s7,
            _, hg_s7, hnt_s7, hres_s7, heq_s7⟩ :=
          seq_htab_new_store_global_slot s6 (ofString "bs") 80 pbs 32#64 20#64 64#64 _
            hAR_s6 (by omega) hpbs_lo hpbs8 (by decide) (by decide) (by decide) hs6_bs
            (by decide) (by decide) hnt_s6 hres_s6
        have hs7_bs : s7.globals.lookup (ofString "bs") = some (.val (.word pbs)) :=
          (hg_s7 (ofString "bs") (by decide)).symm.trans hs6_bs
        -- Step 14: `bs + 40 := htab_new(52, 64)`
        obtain ⟨tb40, s8, htb40_lo, htb40_hi, hAR_s8, hs8_be, hs8_sp, hs8_fmp,
            hwf_tb40, hcnt_tb40, hhdr_tb40, hfp_tb40, hmw_bs40, hmw_bs_o8, hfr_s7_s8,
            _, hg_s8, hnt_s8, hres_s8, heq_s8⟩ :=
          seq_htab_new_store_global_slot s7 (ofString "bs") 80 pbs 40#64 52#64 64#64 _
            hAR_s7 (by omega) hpbs_lo hpbs8 (by decide) (by decide) (by decide) hs7_bs
            (by decide) (by decide) hnt_s7 hres_s7
        have hs8_bs : s8.globals.lookup (ofString "bs") = some (.val (.word pbs)) :=
          (hg_s8 (ofString "bs") (by decide)).symm.trans hs7_bs
        -- Step 15: `bs + 48 := htab_new(32, 64)`
        obtain ⟨tb48, s9, htb48_lo, htb48_hi, hAR_s9, hs9_be, hs9_sp, hs9_fmp,
            hwf_tb48, hcnt_tb48, hhdr_tb48, hfp_tb48, hmw_bs48, hmw_bs_o9, hfr_s8_s9,
            _, hg_s9, hnt_s9, hres_s9, heq_s9⟩ :=
          seq_htab_new_store_global_slot s8 (ofString "bs") 80 pbs 48#64 32#64 64#64 _
            hAR_s8 (by omega) hpbs_lo hpbs8 (by decide) (by decide) (by decide) hs8_bs
            (by decide) (by decide) hnt_s8 hres_s8
        have hs9_bs : s9.globals.lookup (ofString "bs") = some (.val (.word pbs)) :=
          (hg_s9 (ofString "bs") (by decide)).symm.trans hs8_bs
        -- Step 16: `store(bs + 56, 0)` and `store(bs + 64, 0)`
        obtain ⟨heq_s9a, hAR_s9a, hs9a_g, hs9a_l, hs9a_be, _, _, hmw_ne_s9a, hfr_s9a⟩ :=
          seq_store_global_rec_slot s9 (ofString "bs") 80 pbs 56#64 0#64 (.const 0#64) _
            hAR_s9 hs9_bs hpbs_lo hpbs_hi hpbs8 (by decide) (by decide) rfl
        set s9a : PanSemStateFiniteExact 64 F :=
          { s9 with memory := fun a => if a = pbs + 56#64 then .word 0#64 else s9.memory a }
        rw [heq_s9a] at hnt_s9 hres_s9 heq_s9
        have hs9a_bs : s9a.globals.lookup (ofString "bs") = some (.val (.word pbs)) := by rw [hs9a_g]; exact hs9_bs
        obtain ⟨heq_s9b, hAR_s9b, hs9b_g, hs9b_l, hs9b_be, _, _, hmw_ne_s9b, hfr_s9b⟩ :=
          seq_store_global_rec_slot s9a (ofString "bs") 80 pbs 64#64 0#64 (.const 0#64) _
            hAR_s9a hs9a_bs hpbs_lo hpbs_hi hpbs8 (by decide) (by decide) rfl
        set s9b : PanSemStateFiniteExact 64 F :=
          { s9a with memory := fun a => if a = pbs + 64#64 then .word 0#64 else s9a.memory a }
        rw [heq_s9b] at hnt_s9 hres_s9 heq_s9
        have hs9b_bs : s9b.globals.lookup (ofString "bs") = some (.val (.word pbs)) := by rw [hs9b_g]; exact hs9a_bs
        -- Step 17: `bs + 72 := htab_new(20, 256)`
        obtain ⟨tb72, s10, htb72_lo, htb72_hi, hAR_s10, hs10_be, hs10_sp, hs10_fmp,
            hwf_tb72, hcnt_tb72, hhdr_tb72, hfp_tb72, hmw_bs72, hmw_bs_o10, hfr_s9b_s10,
            _, hg_s10, hnt_s10, hres_s10, heq_s10⟩ :=
          seq_htab_new_store_global_slot s9b (ofString "bs") 80 pbs 72#64 20#64 256#64 _
            hAR_s9b (by change pbs.toNat + 80 ≤ globN s9 "heap_ptr"; omega) hpbs_lo hpbs8
            (by decide) (by decide) (by decide) hs9b_bs (by decide) (by decide) hnt_s9 hres_s9
        -- Step 18: `sk_buf := alloc(64)`
        obtain ⟨psk, qsk, s11, hpsk_eq, hqsk_eq, hs11_hp, hpsk_le_qsk, hpsk8, hAR_s11,
            hs11_m, hs11_ma, hs11_be, hs11_l, hs11_sp, hs11_fmp, hs11_sk, hg_s11, hnt_s11, hres_s11, heq_s11⟩ :=
          WkBal.seq_call_alloc_global_resumes s10 (ofString "sk_buf") 64#64 _ hAR_s10
            ⟨by decide, by decide, by decide⟩ hnt_s10 hres_s10
        have hqsk_val : qsk.toNat = psk.toNat + 64 := by
          have h64 : ((64#64 : BitVec 64).toNat + 7) / 8 * 8 = 64 := by decide
          rw [hqsk_eq, h64]
        -- Step 19: `journal_cap := 524288`
        obtain ⟨heq_s12, hAR_s12, hs12_m, hs12_ma, hs12_be, hs12_l, hs12_hp, hs12_sp, hs12_fmp,
            hs12_jc, hg_s12⟩ :=
          seq_assign_global_word s11 (ofString "journal_cap") 524288#64 _ hAR_s11
            ⟨"journal_cap", by decide, rfl⟩ ⟨by decide, by decide, by decide⟩
        set s12 := setGlobalHOLFinite (ofString "journal_cap") (.val (.word 524288#64)) s11
        rw [heq_s12] at hnt_s11 hres_s11 heq_s11
        -- Step 20: `journal := alloc(journal_cap * 32)`
        have hs12_arg : evalListHOLFinite s12 (h := fun a => Classical.propDecidable (s12.memaddrs a))
            [.panop .mul [.var .global (ofString "journal_cap"), .const 32#64]] =
            some [.val (.word 16777216#64)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs12_jc, panOpHOL]
          rfl
        obtain ⟨pjr, qjr, s13, hpjr_eq, hqjr_eq, hs13_hp, hpjr_le_qjr, hpjr8, hAR_s13,
            hs13_m, hs13_ma, hs13_be, hs13_l, hs13_sp, hs13_fmp, hs13_jr, hg_s13, hnt_s13, hres_s13, heq_s13⟩ :=
          seq_call_alloc_global_exp_resumes s12 (ofString "journal")
            (.panop .mul [.var .global (ofString "journal_cap"), .const 32#64]) 16777216#64 _
            hAR_s12 hs12_arg ⟨by decide, by decide, by decide⟩ hnt_s11 hres_s11
        have hqjr_val : qjr.toNat = pjr.toNat + 16777216 := by
          have h16m : ((16777216#64 : BitVec 64).toNat + 7) / 8 * 8 = 16777216 := by decide
          rw [hqjr_eq, h16m]
        -- Step 21: `journal_n := 0`
        obtain ⟨heq_s14, hAR_s14, hs14_m, hs14_ma, hs14_be, hs14_l, hs14_hp, hs14_sp, hs14_fmp,
            hs14_jn, hg_s14⟩ :=
          seq_assign_global_word s13 (ofString "journal_n") 0#64 _ hAR_s13
            ⟨"journal_n", by decide, rfl⟩ ⟨by decide, by decide, by decide⟩
        set s14 := setGlobalHOLFinite (ofString "journal_n") (.val (.word 0#64)) s13
        rw [heq_s14] at hnt_s13 hres_s13 heq_s13
        -- Step 22: `ts := 0; return 0`
        obtain ⟨heq_s15, hAR_s15, hs15_m, hs15_ma, hs15_be, hs15_hp, hs15_sp, hs15_fmp,
            hs15_ts, hg_s15⟩ :=
          WkBal.seq_assign_global_zero_return_zero s14 (ofString "ts") hAR_s14
            ⟨"ts", by decide, rfl⟩ ⟨by decide, by decide, by decide⟩
        set s15 := emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "ts") (.val (.word 0)) s14)
        have heq_s15' : evaluateHOLFiniteState s14
            (.seq (.assign .global (ofString "ts") (.const 0#64)) (.return (.const 0#64))) =
            (some (.returned (.val (.word 0#64))), s15) := heq_s15
        have hchain_s2 : evaluateHOLFiniteState s2
            (ProgHOL.seq (.call (some (some (.global, ofString "bs"), none)) (ofString "alloc") [.const 80#64])
            (.seq (.store (.op .add [.var .global (ofString "bs"), .const 0#64]) (.var .global (ofString "ws")))
            (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 20#64, .const 256#64])
            (.seq (.store (.op .add [.var .global (ofString "bs"), .const 8#64]) (.var .local (ofString "t")))
            (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 20#64, .const 256#64])
            (.seq (.store (.op .add [.var .global (ofString "bs"), .const 16#64]) (.var .local (ofString "t")))
            (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 52#64, .const 256#64])
            (.seq (.store (.op .add [.var .global (ofString "bs"), .const 24#64]) (.var .local (ofString "t")))
            (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 20#64, .const 64#64])
            (.seq (.store (.op .add [.var .global (ofString "bs"), .const 32#64]) (.var .local (ofString "t")))
            (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 52#64, .const 64#64])
            (.seq (.store (.op .add [.var .global (ofString "bs"), .const 40#64]) (.var .local (ofString "t")))
            (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 32#64, .const 64#64])
            (.seq (.store (.op .add [.var .global (ofString "bs"), .const 48#64]) (.var .local (ofString "t")))
            (.seq (.store (.op .add [.var .global (ofString "bs"), .const 56#64]) (.const 0#64))
            (.seq (.store (.op .add [.var .global (ofString "bs"), .const 64#64]) (.const 0#64))
            (.seq (.call (some (some (.local, ofString "t"), none)) (ofString "htab_new") [.const 20#64, .const 256#64])
            (.seq (.store (.op .add [.var .global (ofString "bs"), .const 72#64]) (.var .local (ofString "t")))
            (.seq (.call (some (some (.global, ofString "sk_buf"), none)) (ofString "alloc") [.const 64#64])
            (.seq (.assign .global (ofString "journal_cap") (.const 524288#64))
            (.seq (.call (some (some (.global, ofString "journal"), none)) (ofString "alloc")
                    [.panop .mul [.var .global (ofString "journal_cap"), .const 32#64]])
            (.seq (.assign .global (ofString "journal_n") (.const 0#64))
            (.seq (.assign .global (ofString "ts") (.const 0#64))
                  (.return (.const 0#64))))))))))))))))))))))))) =
            (some (.returned (.val (.word 0#64))), s15) := by
          rw [heq_s3, heq_s4, heq_s5, heq_s6, heq_s7, heq_s8, heq_s9, heq_s10, heq_s11, heq_s13, heq_s15']
        have hchain_s2_r := congrArg Prod.fst hchain_s2
        have hchain_s2_s := congrArg Prod.snd hchain_s2
        dsimp only at hchain_s2_r hchain_s2_s
        set L_final := HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq s15.locals (ofString "t", s1a.locals.lookup (ofString "t")))
          (ofString "root", s0c.locals.lookup (ofString "root"))
        have heval_total : evaluateHOLFiniteState s
            (ProgHOL.seq (.call (some (some (.global, ofString "ws"), none)) (ofString "alloc") [.const 40#64])
            (.seq (.store (.op .add [.var .global (ofString "ws"), .const 0#64]) (.var .local (ofString "nodedb")))
            (.seq (.store (.op .add [.var .global (ofString "ws"), .const 8#64]) (.var .local (ofString "state_root")))
            (.seq (.store (.op .add [.var .global (ofString "ws"), .const 16#64]) (.var .local (ofString "codedb")))
              (.decCall (ofString "root") .one (ofString "decode_witness_to_mpt")
                [.var .local (ofString "nodedb"), .var .local (ofString "state_root")]
                (stateInitAfterDwProg (ofString "t") (ofString "root"))))))) =
            (some (.returned (.val (.word 0#64))), { s15 with locals := L_final, clock := s15.clock }) := by
          rw [← state_init_body_eq, heq_pre_dw]
          exact Prod.ext
            (heq_dc_r.trans (heq_s2_r.trans hchain_s2_r))
            (heq_dc_s.trans (by rw [heq_s2_s, hchain_s2_s]))
        rw [heval_total]
        apply worldStepIn_with_locals_right L_final s15.clock (fun _ _ hq => hq)
        have hs3a_hp : globN s3a "heap_ptr" = globN s3 "heap_ptr" := rfl
        have hs9b_hp : globN s9b "heap_ptr" = globN s9 "heap_ptr" := rfl
        have hs1a_hp : globN s1a "heap_ptr" = globN s1 "heap_ptr" := rfl
        have hhp_s_s0c : globN s "heap_ptr" + 40 = globN s0c "heap_ptr" := by
          rw [hs0c_hp, hqws_val, hpws_eq]
        have hhp_s0c_s1 : globN s0c "heap_ptr" ≤ globN s1 "heap_ptr" := hhp_dw
        have hhp_s1a_s2 : globN s1a "heap_ptr" ≤ globN s2 "heap_ptr" := by omega
        have hhp_s2_s3 : globN s2 "heap_ptr" + 80 = globN s3 "heap_ptr" := by
          rw [hs3_hp, hqbs_val, hpbs_eq]
        have hhp_s3a_s10 : globN s3a "heap_ptr" ≤ globN s10 "heap_ptr" := by
          rw [hs3a_hp]
          have := hs9b_hp
          omega
        have hs10_hp_eq : globN s15 "heap_ptr" = globN s10 "heap_ptr" + 64 + 16777216 := by
          rw [hs15_hp, hs14_hp, hs13_hp, hqjr_val, hpjr_eq, hs12_hp, hs11_hp, hqsk_val, hpsk_eq]
        have hhp_15 : globN s "heap_ptr" ≤ globN s15 "heap_ptr" := by omega
        have hsp_15 : globN s15 "scratch_ptr" = globN s "scratch_ptr" := by
          rw [hs15_sp, hs14_sp, hs13_sp, hs12_sp, hs11_sp, hs10_sp]
          change globN s9 "scratch_ptr" = globN s "scratch_ptr"
          rw [hs9_sp, hs8_sp, hs7_sp, hs6_sp, hs5_sp, hs4_sp]
          change globN s3 "scratch_ptr" = globN s "scratch_ptr"
          rw [hs3_sp, hs2_sp]
          exact hs1_sp
        have hjcap_15 : globN s15 "journal_cap" = 524288 := by
          have h13 := hg_s13 (ofString "journal_cap") (by decide) (by decide)
          have h14 := hg_s14 (ofString "journal_cap") (by decide)
          have h15 := hg_s15 (ofString "journal_cap") (by decide)
          unfold globN
          rw [← h15, ← h14, ← h13, hs12_jc]
          rfl
        have hws_15 : globN s15 "ws" = pws.toNat := by
          have h15 := hg_s15 (ofString "ws") (by decide)
          have h14 := hg_s14 (ofString "ws") (by decide)
          have h13 := hg_s13 (ofString "ws") (by decide) (by decide)
          have h12 := hg_s12 (ofString "ws") (by decide)
          have h11 := hg_s11 (ofString "ws") (by decide) (by decide)
          have h10 := hg_s10 (ofString "ws") (by decide)
          have h9 := hg_s9 (ofString "ws") (by decide)
          have h8 := hg_s8 (ofString "ws") (by decide)
          have h7 := hg_s7 (ofString "ws") (by decide)
          have h6 := hg_s6 (ofString "ws") (by decide)
          have h5 := hg_s5 (ofString "ws") (by decide)
          have h4 := hg_s4 (ofString "ws") (by decide)
          unfold globN
          change (match s15.globals.lookup (ofString "ws") with | some (.val (.word w)) => w.toNat | _ => 0) = pws.toNat
          rw [← h15, ← h14, ← h13, ← h12, ← h11, ← h10]
          change (match s9.globals.lookup (ofString "ws") with | some (.val (.word w)) => w.toNat | _ => 0) = pws.toNat
          rw [← h9, ← h8, ← h7, ← h6, ← h5, ← h4]
          change (match s3.globals.lookup (ofString "ws") with | some (.val (.word w)) => w.toNat | _ => 0) = pws.toNat
          rw [hs3_ws]
        have hbs_15 : globN s15 "bs" = pbs.toNat := by
          have h15 := hg_s15 (ofString "bs") (by decide)
          have h14 := hg_s14 (ofString "bs") (by decide)
          have h13 := hg_s13 (ofString "bs") (by decide) (by decide)
          have h12 := hg_s12 (ofString "bs") (by decide)
          have h11 := hg_s11 (ofString "bs") (by decide) (by decide)
          have h10 := hg_s10 (ofString "bs") (by decide)
          unfold globN
          change (match s15.globals.lookup (ofString "bs") with | some (.val (.word w)) => w.toNat | _ => 0) = pbs.toNat
          rw [← h15, ← h14, ← h13, ← h12, ← h11, ← h10, hs9b_bs]
        have hsk_15 : globN s15 "sk_buf" = psk.toNat := by
          have h15 := hg_s15 (ofString "sk_buf") (by decide)
          have h14 := hg_s14 (ofString "sk_buf") (by decide)
          have h13 := hg_s13 (ofString "sk_buf") (by decide) (by decide)
          have h12 := hg_s12 (ofString "sk_buf") (by decide)
          unfold globN
          change (match s15.globals.lookup (ofString "sk_buf") with | some (.val (.word w)) => w.toNat | _ => 0) = psk.toNat
          rw [← h15, ← h14, ← h13, ← h12, hs11_sk]
        have hjr_15 : globN s15 "journal" = pjr.toNat := by
          have h15 := hg_s15 (ofString "journal") (by decide)
          have h14 := hg_s14 (ofString "journal") (by decide)
          unfold globN
          change (match s15.globals.lookup (ofString "journal") with | some (.val (.word w)) => w.toNat | _ => 0) = pjr.toNat
          rw [← h15, ← h14, hs13_jr]
        have hjn_15 : globN s15 "journal_n" = 0 := by
          have h15 := hg_s15 (ofString "journal_n") (by decide)
          unfold globN
          change (match s15.globals.lookup (ofString "journal_n") with | some (.val (.word w)) => w.toNat | _ => 0) = 0
          rw [← h15, hs14_jn]
          rfl
        have hts_15 : globN s15 "ts" = 0 := by
          unfold globN
          rw [hs15_ts]
          rfl
        have hgk_15 : GlobalsKept
            ["bs", "heap_ptr", "journal", "journal_cap", "journal_n", "scratch_ptr", "sk_buf", "ts", "ws"]
            s s15 := by
          intro k hk
          have hne_bs : k ≠ ofString "bs" := fun h => hk (by subst h; decide)
          have hne_hp : k ≠ ofString "heap_ptr" := fun h => hk (by subst h; decide)
          have hne_jr : k ≠ ofString "journal" := fun h => hk (by subst h; decide)
          have hne_jc : k ≠ ofString "journal_cap" := fun h => hk (by subst h; decide)
          have hne_jn : k ≠ ofString "journal_n" := fun h => hk (by subst h; decide)
          have hne_sp : k ≠ ofString "scratch_ptr" := fun h => hk (by subst h; decide)
          have hne_sk : k ≠ ofString "sk_buf" := fun h => hk (by subst h; decide)
          have hne_ts : k ≠ ofString "ts" := fun h => hk (by subst h; decide)
          have hne_ws : k ≠ ofString "ws" := fun h => hk (by subst h; decide)
          have hnot_dw : k ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString := by
            simp only [List.map, List.mem_cons, List.not_mem_nil, or_false, not_or]
            exact ⟨hne_hp, hne_sp⟩
          calc s.globals.lookup k
            _ = s0.globals.lookup k := hg_s0 k hne_hp hne_ws
            _ = s0c.globals.lookup k := by rw [hs0c_g, hs0b_g, hs0a_g]
            _ = s1.globals.lookup k := hgk_dw k hnot_dw
            _ = s1a.globals.lookup k := by rw [hs1a_g]
            _ = s2.globals.lookup k := hg_s2 k hne_hp
            _ = s3.globals.lookup k := hg_s3 k hne_hp hne_bs
            _ = s3a.globals.lookup k := by rw [hs3a_g]
            _ = s4.globals.lookup k := hg_s4 k hne_hp
            _ = s5.globals.lookup k := hg_s5 k hne_hp
            _ = s6.globals.lookup k := hg_s6 k hne_hp
            _ = s7.globals.lookup k := hg_s7 k hne_hp
            _ = s8.globals.lookup k := hg_s8 k hne_hp
            _ = s9.globals.lookup k := hg_s9 k hne_hp
            _ = s9b.globals.lookup k := by rw [hs9b_g, hs9a_g]
            _ = s10.globals.lookup k := hg_s10 k hne_hp
            _ = s11.globals.lookup k := hg_s11 k hne_hp hne_sk
            _ = s12.globals.lookup k := hg_s12 k hne_jc
            _ = s13.globals.lookup k := hg_s13 k hne_hp hne_jr
            _ = s14.globals.lookup k := hg_s14 k hne_jn
            _ = s15.globals.lookup k := hg_s15 k hne_ts
        have hbe_15 : s15.be = s.be := by
          rw [hs15_be, hs14_be, hs13_be, hs12_be, hs11_be, hs10_be, hs9b_be, hs9a_be,
              hs9_be, hs8_be, hs7_be, hs6_be, hs5_be, hs4_be, hs3a_be, hs3_be, hs2_be, hs1a_be, hs1_be]
        have hs15_m_s10 : s15.memory = s10.memory := by
          rw [hs15_m, hs14_m, hs13_m, hs12_m, hs11_m]
        -- Build FrameOutside `s -> s1` and `s -> s15` keeping `[freeGap s]` and fresh `heapFree s`:
        have hfg_ent_eq : freeGap ent_dw = freeGap s := by
          unfold freeGap
          have h1 : globN ent_dw "frame_mem_ptr" = globN s "frame_mem_ptr" := hs0c_fmp
          have h2 : globN ent_dw "scratch_ptr" = globN s "scratch_ptr" := hs0c_sp
          rw [h1, h2]
        have hfr_s_s1 : FrameOutside s s1 [freeGap s] (heapFree s) := by
          intro x hno hnhf
          have hno_ent : ∀ j ∈ [freeGap ent_dw], ¬ CellHits x.toNat j := by
            intro j hj
            rw [List.mem_singleton.1 hj, hfg_ent_eq]
            exact hno _ (List.mem_singleton.2 rfl)
          have hnhf_ent : ¬ CellHits x.toNat (heapFree ent_dw) := by
            intro ⟨c1, c2⟩
            unfold heapFree at c1 c2; dsimp only at c1 c2
            have hent_hp : globN ent_dw "heap_ptr" = globN s0c "heap_ptr" := rfl
            rw [hent_hp] at c1 c2
            exact hnhf ⟨by unfold heapFree; dsimp only; omega, by unfold heapFree; dsimp only; omega⟩
          have hnhf_0c : ¬ CellHits x.toNat (globN s "heap_ptr", globN s0c "heap_ptr" - globN s "heap_ptr") := by
            intro ⟨c1, c2⟩; dsimp only at c1 c2
            exact hnhf ⟨c1, by unfold heapFree; dsimp only; have := hAR_s0c.2.2.1; omega⟩
          have hm12 : s1.memory x = s0c.memory x := hfr_dw x hno_ent hnhf_ent
          exact hm12.trans (hfr_s_s0c x (fun _ h => by cases h) hnhf_0c)
        have hfr_s1a_s2' : FrameOutside s1a s2 [(globN s "scratch_ptr", 0), (pws.toNat, 40)]
            (globN s1a "heap_ptr", globN s2 "heap_ptr" - globN s1a "heap_ptr") := by
          have hsp_1a : globN s1a "scratch_ptr" = globN s "scratch_ptr" := hs1_sp
          rw [hsp_1a] at hfr_s1a_s2; exact hfr_s1a_s2
        -- Chain `s3a -> s4 -> s5 -> s6 -> s7 -> s8 -> s9 -> s9b -> s10` keeping `[(sp, 0), (pbs, 80)]`:
        have hfr_bs_step : ∀ {a b c : PanSemStateFiniteExact 64 F}
            (hab : globN a "heap_ptr" ≤ globN b "heap_ptr")
            (hbc : globN b "heap_ptr" ≤ globN c "heap_ptr")
            (h1 : FrameOutside a b [(globN s "scratch_ptr", 0), (pbs.toNat, 80)]
              (globN a "heap_ptr", globN b "heap_ptr" - globN a "heap_ptr"))
            (h2 : FrameOutside b c [(globN s "scratch_ptr", 0), (pbs.toNat, 80)]
              (globN b "heap_ptr", globN c "heap_ptr" - globN b "heap_ptr")),
            FrameOutside a c [(globN s "scratch_ptr", 0), (pbs.toNat, 80)]
              (globN a "heap_ptr", globN c "heap_ptr" - globN a "heap_ptr") := by
          intro a b c hab hbc h1 h2 x hno hnhf
          have hnhf1 : ¬ CellHits x.toNat (globN a "heap_ptr", globN b "heap_ptr" - globN a "heap_ptr") :=
            fun ⟨c1, c2⟩ => hnhf ⟨c1, by dsimp only at c2 ⊢; omega⟩
          have hnhf2 : ¬ CellHits x.toNat (globN b "heap_ptr", globN c "heap_ptr" - globN b "heap_ptr") :=
            fun ⟨c1, c2⟩ => hnhf ⟨by dsimp only at c1 ⊢; omega, by dsimp only at c2 ⊢; omega⟩
          exact (h2 x hno hnhf2).trans (h1 x hno hnhf1)
        have hsp_3a : globN s3a "scratch_ptr" = globN s "scratch_ptr" := by
          change globN s3 "scratch_ptr" = globN s "scratch_ptr"
          rw [hs3_sp, hs2_sp]
          exact hs1_sp
        have hsp_4 : globN s4 "scratch_ptr" = globN s "scratch_ptr" := hs4_sp.trans hsp_3a
        have hsp_5 : globN s5 "scratch_ptr" = globN s "scratch_ptr" := hs5_sp.trans hsp_4
        have hsp_6 : globN s6 "scratch_ptr" = globN s "scratch_ptr" := hs6_sp.trans hsp_5
        have hsp_7 : globN s7 "scratch_ptr" = globN s "scratch_ptr" := hs7_sp.trans hsp_6
        have hsp_8 : globN s8 "scratch_ptr" = globN s "scratch_ptr" := hs8_sp.trans hsp_7
        have hsp_9 : globN s9 "scratch_ptr" = globN s "scratch_ptr" := hs9_sp.trans hsp_8
        have hsp_9b : globN s9b "scratch_ptr" = globN s "scratch_ptr" := hsp_9
        have hfr_3a_4 : FrameOutside s3a s4 [(globN s "scratch_ptr", 0), (pbs.toNat, 80)]
            (globN s3a "heap_ptr", globN s4 "heap_ptr" - globN s3a "heap_ptr") := by
          rw [hsp_3a] at hfr_s3a_s4; exact hfr_s3a_s4
        have hfr_4_5 : FrameOutside s4 s5 [(globN s "scratch_ptr", 0), (pbs.toNat, 80)]
            (globN s4 "heap_ptr", globN s5 "heap_ptr" - globN s4 "heap_ptr") := by
          rw [hsp_4] at hfr_s4_s5; exact hfr_s4_s5
        have hfr_5_6 : FrameOutside s5 s6 [(globN s "scratch_ptr", 0), (pbs.toNat, 80)]
            (globN s5 "heap_ptr", globN s6 "heap_ptr" - globN s5 "heap_ptr") := by
          rw [hsp_5] at hfr_s5_s6; exact hfr_s5_s6
        have hfr_6_7 : FrameOutside s6 s7 [(globN s "scratch_ptr", 0), (pbs.toNat, 80)]
            (globN s6 "heap_ptr", globN s7 "heap_ptr" - globN s6 "heap_ptr") := by
          rw [hsp_6] at hfr_s6_s7; exact hfr_s6_s7
        have hfr_7_8 : FrameOutside s7 s8 [(globN s "scratch_ptr", 0), (pbs.toNat, 80)]
            (globN s7 "heap_ptr", globN s8 "heap_ptr" - globN s7 "heap_ptr") := by
          rw [hsp_7] at hfr_s7_s8; exact hfr_s7_s8
        have hfr_8_9 : FrameOutside s8 s9 [(globN s "scratch_ptr", 0), (pbs.toNat, 80)]
            (globN s8 "heap_ptr", globN s9 "heap_ptr" - globN s8 "heap_ptr") := by
          rw [hsp_8] at hfr_s8_s9; exact hfr_s8_s9
        have hfr_9_9b : FrameOutside s9 s9b [(globN s "scratch_ptr", 0), (pbs.toNat, 80)]
            (globN s9 "heap_ptr", globN s9b "heap_ptr" - globN s9 "heap_ptr") := by
          intro x hno _
          have hno_bs := hno (pbs.toNat, 80) (by simp)
          exact (hfr_s9b x (fun _ h => by cases h) hno_bs).trans (hfr_s9a x (fun _ h => by cases h) hno_bs)
        have hfr_9b_10 : FrameOutside s9b s10 [(globN s "scratch_ptr", 0), (pbs.toNat, 80)]
            (globN s9b "heap_ptr", globN s10 "heap_ptr" - globN s9b "heap_ptr") := by
          rw [hsp_9b] at hfr_s9b_s10; exact hfr_s9b_s10
        have hfr_9_10 := hfr_bs_step (a := s9) (b := s9b) (c := s10) (le_of_eq hs9b_hp.symm) (by omega) hfr_9_9b hfr_9b_10
        have hfr_8_10 := hfr_bs_step (by omega) (by omega) hfr_8_9 hfr_9_10
        have hfr_7_10 := hfr_bs_step (by omega) (by omega) hfr_7_8 hfr_8_10
        have hfr_6_10 := hfr_bs_step (by omega) (by omega) hfr_6_7 hfr_7_10
        have hfr_5_10 := hfr_bs_step (by omega) (by omega) hfr_5_6 hfr_6_10
        have hfr_4_10 := hfr_bs_step (by omega) (by omega) hfr_4_5 hfr_5_10
        have hfr_3a_10 := hfr_bs_step (by omega) (by omega) hfr_3a_4 hfr_4_10
        have hsp_2 : globN s2 "scratch_ptr" = globN s "scratch_ptr" := hs2_sp.trans hs1_sp
        have hfr_s2_s10 : FrameOutside s2 s10 [(globN s "scratch_ptr", 0)]
            (globN s2 "heap_ptr", globN s10 "heap_ptr" - globN s2 "heap_ptr") := by
          have h2_3a : FrameOutside s2 s3a [(globN s2 "scratch_ptr", 0)]
              (globN s2 "heap_ptr", globN s3a "heap_ptr" - globN s2 "heap_ptr") := by
            intro x _ hnhf
            have hno_bs : ¬ CellHits x.toNat (pbs.toNat, 80) := by
              intro ⟨c1, c2⟩; dsimp only at c1 c2
              exact hnhf ⟨by dsimp only; omega, by dsimp only; omega⟩
            exact (hfr_s3a x (fun _ h => by cases h) hno_bs).trans (congrFun hs3_m x)
          have hcol := frameOutside_collapse_rec_sp s2 s3a s10 pbs.toNat 80 (by omega) hpbs80_s3a
            (by omega) h2_3a (by rw [hsp_2]; exact hfr_3a_10)
          rw [hsp_2] at hcol
          exact hcol
        have hfr_s1_s15 : FrameOutside s1 s15 [(globN s "scratch_ptr", 0), (pws.toNat, 40)]
            (globN s1 "heap_ptr", globN s15 "heap_ptr" - globN s1 "heap_ptr") := by
          intro x hno hnhf
          have hno_sp_x : ∀ j ∈ [(globN s "scratch_ptr", 0)], ¬ CellHits x.toNat j :=
            fun j hj => hno j (by simp only [List.mem_singleton] at hj; subst hj; simp)
          have hno_ws_x : ¬ CellHits x.toNat (pws.toNat, 40) := hno (pws.toNat, 40) (by simp)
          have hnhf_2_10 : ¬ CellHits x.toNat (globN s2 "heap_ptr", globN s10 "heap_ptr" - globN s2 "heap_ptr") :=
            fun ⟨c1, c2⟩ => hnhf ⟨by dsimp only at c1 ⊢; omega, by dsimp only at c2 ⊢; omega⟩
          have hnhf_1a_2 : ¬ CellHits x.toNat (globN s1a "heap_ptr", globN s2 "heap_ptr" - globN s1a "heap_ptr") :=
            fun ⟨c1, c2⟩ => hnhf ⟨by dsimp only at c1 ⊢; omega, by dsimp only at c2 ⊢; omega⟩
          rw [hs15_m_s10]
          exact (hfr_s2_s10 x hno_sp_x hnhf_2_10).trans
            ((hfr_s1a_s2' x hno hnhf_1a_2).trans
              (hfr_s1a x (fun _ h => by cases h) hno_ws_x))
        have hfr_s_s15 : FrameOutside s s15 [freeGap s] (heapFree s) := by
          intro x hno hnhf
          have hno_1_15 : ∀ j ∈ [(globN s "scratch_ptr", 0), (pws.toNat, 40)], ¬ CellHits x.toNat j := by
            intro j hj hcj
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
            rcases hj with rfl | rfl
            · have hfg_eq : WkBal.freeGap s = freeGap s := rfl
              have hhit := WkBal.cellHits_sp0_imp_freeGap hAR0.2 hcj
              rw [hfg_eq] at hhit
              exact hno _ (List.mem_singleton.2 rfl) hhit
            · obtain ⟨c1, c2⟩ := hcj; dsimp only at c1 c2
              exact hnhf ⟨by unfold heapFree; dsimp only; omega, by unfold heapFree; dsimp only; omega⟩
          have hnhf_1_15 : ¬ CellHits x.toNat (globN s1 "heap_ptr", globN s15 "heap_ptr" - globN s1 "heap_ptr") := by
            intro ⟨c1, c2⟩; dsimp only at c1 c2
            have := hAR_s15.2.2.1
            exact hnhf ⟨by unfold heapFree; dsimp only; omega, by unfold heapFree; dsimp only; omega⟩
          exact (hfr_s1_s15 x hno_1_15 hnhf_1_15).trans (hfr_s_s1 x hno hnhf)
        have hsp8_s : (globN s "scratch_ptr") % 8 = 0 := hAR0.2.2.2.2.2.2.2.2.1
        have hunhit_s_s15 : ∀ i : Ivl, i.2 ≠ 0 → Allocated s i → R10Shards.P26_P28.IvlUnhit s s15 i :=
          fun _ hipos hal => unhit_p26_of_free_frame_local hAR0.2 hfr_s_s15 hipos hal
        have hrk_15 : RecordsKept (fun _ => [])
            [("ws", []), ("bs", []),
             ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
             ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])] s s15 := by
          intro rec hrec hgnz k hk _
          have hrec_sz : ∃ sz, (rec.1, sz) ∈ typedRecords ∧ sz ≠ 0 ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hrec
            rcases hrec with rfl | rfl | rfl | rfl
            · cases hk
            · cases hk
            · refine ⟨72, by decide, by decide, ?_⟩; simp at hk; omega
            · refine ⟨88, by decide, by decide, ?_⟩; simp at hk; omega
          obtain ⟨sz, htr, hsz_nz, hk8, hksz⟩ := hrec_sz
          have hmf := R10Shards.P26_P28.typedRecord_mem_fixedObjects s htr
          simp only [hgnz, ↓reduceIte] at hmf
          rcases hWT_sir.2.2.1.1 _ hmf with h0 | ⟨hal, hwords⟩
          · omega
          · have hhi := (ivl_allocated_bound hAR0.2 hal).2
            have hg8 : (globN s rec.1) % 8 = 0 := hwords.1
            exact R10Shards.P26_P28.memW_eq_of_ivlUnhit (hunhit_s_s15 _ hsz_nz hal)
              (by omega) hhi ⟨by omega, by omega⟩
        refine ⟨hAR_s15, hhp_15, hgk_15, hrk_15, ?_⟩
        · -- Step A: Transfer `pws` words (`16, 24, 32`) and `pbs` words (`8, 16, 24, 32, 40, 48, 72`) to `s15`,
          -- and transfer `tw_ws, tb8, tb16, tb24, tb32, tb40, tb48, tb72` to `s15`:
          have h264_lim : heapLimit < 2 ^ 64 := by decide
          have hmw_s2_s15 : ∀ k : Nat, k % 8 = 0 → k + 8 ≤ globN s2 "heap_ptr" → memW s15 k = memW s2 k := by
            intro k hk8 hk_hi
            have hk64 : k < 2 ^ 64 := by have := hAR_s2.2.2.1; omega
            unfold memW
            rw [hs15_m_s10]
            have hm := hfr_s2_s10 (BitVec.ofNat 64 k)
              (fun j hj ⟨c1, c2⟩ => by
                simp only [List.mem_singleton] at hj; subst hj
                dsimp only at c1 c2
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
                have hsep : heapLimit ≤ scratchStart := by decide
                have := hAR_s2.2.2.1; have := hAR0.2.2.2.2.1
                omega)
              (fun ⟨c1, c2⟩ => by
                dsimp only at c1 c2
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at c1 c2
                omega)
            rw [hm]
          have hmw15_ws16 : memW s15 (pws.toNat + 16) = cdw.toNat := by
            have h24_nat : (24#64 : BitVec 64).toNat = 24 := rfl
            rw [hmw_s2_s15 (pws.toNat + 16) (by omega) (by omega),
                hmw_ws_other 16 (by omega) (by decide),
                hmw_ne_s1a (pws.toNat + 16) (by rw [h24_nat]; omega) (by omega)]
            have hm_dw := hfr_dw (BitVec.ofNat 64 (pws.toNat + 16))
              (fun j hj ⟨c1, c2⟩ => by
                rw [List.mem_singleton.1 hj, hfg_ent_eq] at c1
                unfold freeGap at c1; dsimp only at c1
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at c1
                have hsep : heapLimit ≤ scratchStart := by decide
                have := hAR0.2.2.2.1
                omega)
              (fun ⟨c1, c2⟩ => by
                unfold heapFree at c1; dsimp only at c1
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at c1
                have hent_hp : globN ent_dw "heap_ptr" = qws.toNat := hs0c_hp
                rw [hent_hp] at c1
                omega)
            have hs1_m_eq : memW s1 (pws.toNat + 16) = memW s0c (pws.toNat + 16) := by
              unfold memW
              change (match cpost_dw.memory _ with | .word v => v.toNat) =
                     (match ent_dw.memory _ with | .word v => v.toNat)
              rw [hm_dw]
            exact hs1_m_eq.trans hmw_ws16
          have hmw15_ws24 : memW s15 (pws.toNat + 24) = rootw.toNat := by
            rw [hmw_s2_s15 (pws.toNat + 24) (by omega) (by omega),
                hmw_ws_other 24 (by omega) (by decide)]
            exact hmw_ws24
          have hmw15_ws32 : memW s15 (pws.toNat + 32) = tw_ws.toNat := by
            rw [hmw_s2_s15 (pws.toNat + 32) (by omega) (by omega)]
            exact hmw_ws32
          -- `pbs` slot values at `s15`:
          have hmw9b_ne : ∀ off : Nat, off + 8 ≤ 80 → off ≠ 56 → off ≠ 64 →
              memW s9b (pbs.toNat + off) = memW s9 (pbs.toNat + off) := by
            intro off hoff h56 h64
            have hk64 : pbs.toNat + off < 2 ^ 64 := by omega
            have h56_nat : (56#64 : BitVec 64).toNat = 56 := rfl
            have h64_nat : (64#64 : BitVec 64).toNat = 64 := rfl
            exact (hmw_ne_s9b (pbs.toNat + off) (by rw [h64_nat]; omega) hk64).trans
                  (hmw_ne_s9a (pbs.toNat + off) (by rw [h56_nat]; omega) hk64)
          have hmw_s10_s15 : ∀ k : Nat, memW s15 k = memW s10 k := fun k => by
            unfold memW; rw [hs15_m_s10]
          have hmw15_bs8 : memW s15 (pbs.toNat + 8) = tb8.toNat := by
            rw [hmw_s10_s15, hmw_bs_o10 8 (by omega) (by decide),
                hmw9b_ne 8 (by omega) (by decide) (by decide),
                hmw_bs_o9 8 (by omega) (by decide),
                hmw_bs_o8 8 (by omega) (by decide),
                hmw_bs_o7 8 (by omega) (by decide),
                hmw_bs_o6 8 (by omega) (by decide),
                hmw_bs_o5 8 (by omega) (by decide)]
            exact hmw_bs8
          have hmw15_bs16 : memW s15 (pbs.toNat + 16) = tb16.toNat := by
            rw [hmw_s10_s15, hmw_bs_o10 16 (by omega) (by decide),
                hmw9b_ne 16 (by omega) (by decide) (by decide),
                hmw_bs_o9 16 (by omega) (by decide),
                hmw_bs_o8 16 (by omega) (by decide),
                hmw_bs_o7 16 (by omega) (by decide),
                hmw_bs_o6 16 (by omega) (by decide)]
            exact hmw_bs16
          have hmw15_bs24 : memW s15 (pbs.toNat + 24) = tb24.toNat := by
            rw [hmw_s10_s15, hmw_bs_o10 24 (by omega) (by decide),
                hmw9b_ne 24 (by omega) (by decide) (by decide),
                hmw_bs_o9 24 (by omega) (by decide),
                hmw_bs_o8 24 (by omega) (by decide),
                hmw_bs_o7 24 (by omega) (by decide)]
            exact hmw_bs24
          have hmw15_bs32 : memW s15 (pbs.toNat + 32) = tb32.toNat := by
            rw [hmw_s10_s15, hmw_bs_o10 32 (by omega) (by decide),
                hmw9b_ne 32 (by omega) (by decide) (by decide),
                hmw_bs_o9 32 (by omega) (by decide),
                hmw_bs_o8 32 (by omega) (by decide)]
            exact hmw_bs32
          have hmw15_bs40 : memW s15 (pbs.toNat + 40) = tb40.toNat := by
            rw [hmw_s10_s15, hmw_bs_o10 40 (by omega) (by decide),
                hmw9b_ne 40 (by omega) (by decide) (by decide),
                hmw_bs_o9 40 (by omega) (by decide)]
            exact hmw_bs40
          have hmw15_bs48 : memW s15 (pbs.toNat + 48) = tb48.toNat := by
            rw [hmw_s10_s15, hmw_bs_o10 48 (by omega) (by decide),
                hmw9b_ne 48 (by omega) (by decide) (by decide)]
            exact hmw_bs48
          have hmw15_bs72 : memW s15 (pbs.toNat + 72) = tb72.toNat := by
            rw [hmw_s10_s15]; exact hmw_bs72
          -- Transfer `tw_ws, tb8, tb16, tb24, tb32, tb40, tb48, tb72` to `s15`:
          have hag_0_15 : AllocatorGrows s s15 := ⟨hhp_15, by rw [hsp_15]⟩
          have hag_s2_s15 : AllocatorGrows s2 s15 := ⟨by omega, by rw [hsp_15, hsp_2]⟩
          obtain ⟨hwf_tws_p, hfp_tws_eq, hhdr_tws_eq⟩ := WkBal.htabWF_transfer_unhit hAR_s2 hAR_s15 hwf_tws
            (fun i hi a ha8 h1 h2 => by
              rw [hs15_m_s10]
              have hin := (hfp_tws i hi).2
              apply hfr_s2_s10 a
              · intro j hj hcj
                simp only [List.mem_singleton] at hj; subst hj
                exact InitECandidate.Solver.Wave8Contracts.M08.not_cellHits_of_disj ha8 hsp8_s ⟨h1, h2⟩
                  (Or.inr (Or.inl rfl)) hcj
              · exact InitECandidate.Solver.Wave8Contracts.M08.not_cellHits_of_disj ha8 hAR_s2.2.2.2.2.2.2.1
                  ⟨h1, h2⟩ (Or.inr (Or.inr (Or.inl hin.2))))
            (fun i hi => AllocatorGrows.allocated hag_s2_s15 (hfp_tws i hi).1)
          have hu_bs_tab : ∀ {si : PanSemStateFiniteExact 64 F} {lo : Nat} {i : Ivl},
              ArenaOK si → pbs.toNat + 80 ≤ lo → Inside i lo (globN si "heap_ptr") →
              FrameOutside si s10 [(globN s "scratch_ptr", 0), (pbs.toNat, 80)]
                (globN si "heap_ptr", globN s10 "heap_ptr" - globN si "heap_ptr") →
              WkBal.M08IvlUnhit si s15 i := by
            intro si lo i hAsi hlo hin hfr_si a ha8 h1 h2
            rw [hs15_m_s10]
            apply hfr_si a
            · intro j hj hcj
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
              rcases hj with rfl | rfl
              · exact InitECandidate.Solver.Wave8Contracts.M08.not_cellHits_of_disj ha8 hsp8_s ⟨h1, h2⟩
                  (Or.inr (Or.inl rfl)) hcj
              · exact InitECandidate.Solver.Wave8Contracts.M08.not_cellHits_of_disj ha8 hpbs8 ⟨h1, h2⟩
                  (Or.inr (Or.inr (Or.inr (le_trans hlo hin.1)))) hcj
            · exact InitECandidate.Solver.Wave8Contracts.M08.not_cellHits_of_disj ha8 hAsi.2.2.2.2.2.1
                ⟨h1, h2⟩ (Or.inr (Or.inr (Or.inl hin.2)))
          obtain ⟨hwf_tb8_p, hfp_tb8_eq, hhdr_tb8_eq⟩ := WkBal.htabWF_transfer_unhit hAR_s4 hAR_s15 hwf_tb8
            (fun i hi => hu_bs_tab hAR_s4.2 (by omega) (hfp_tb8 i hi).2 hfr_4_10)
            (fun i hi => AllocatorGrows.allocated ⟨by omega, by rw [hsp_15, hsp_4]⟩ (hfp_tb8 i hi).1)
          obtain ⟨hwf_tb16_p, hfp_tb16_eq, hhdr_tb16_eq⟩ := WkBal.htabWF_transfer_unhit hAR_s5 hAR_s15 hwf_tb16
            (fun i hi => hu_bs_tab hAR_s5.2 (by omega) (hfp_tb16 i hi).2 hfr_5_10)
            (fun i hi => AllocatorGrows.allocated ⟨by omega, by rw [hsp_15, hsp_5]⟩ (hfp_tb16 i hi).1)
          obtain ⟨hwf_tb24_p, hfp_tb24_eq, hhdr_tb24_eq⟩ := WkBal.htabWF_transfer_unhit hAR_s6 hAR_s15 hwf_tb24
            (fun i hi => hu_bs_tab hAR_s6.2 (by omega) (hfp_tb24 i hi).2 hfr_6_10)
            (fun i hi => AllocatorGrows.allocated ⟨by omega, by rw [hsp_15, hsp_6]⟩ (hfp_tb24 i hi).1)
          obtain ⟨hwf_tb32_p, hfp_tb32_eq, hhdr_tb32_eq⟩ := WkBal.htabWF_transfer_unhit hAR_s7 hAR_s15 hwf_tb32
            (fun i hi => hu_bs_tab hAR_s7.2 (by omega) (hfp_tb32 i hi).2 hfr_7_10)
            (fun i hi => AllocatorGrows.allocated ⟨by omega, by rw [hsp_15, hsp_7]⟩ (hfp_tb32 i hi).1)
          obtain ⟨hwf_tb40_p, hfp_tb40_eq, hhdr_tb40_eq⟩ := WkBal.htabWF_transfer_unhit hAR_s8 hAR_s15 hwf_tb40
            (fun i hi => hu_bs_tab hAR_s8.2 (by omega) (hfp_tb40 i hi).2 hfr_8_10)
            (fun i hi => AllocatorGrows.allocated ⟨by omega, by rw [hsp_15, hsp_8]⟩ (hfp_tb40 i hi).1)
          obtain ⟨hwf_tb48_p, hfp_tb48_eq, hhdr_tb48_eq⟩ := WkBal.htabWF_transfer_unhit hAR_s9 hAR_s15 hwf_tb48
            (fun i hi => hu_bs_tab hAR_s9.2 (by omega) (hfp_tb48 i hi).2 hfr_9_10)
            (fun i hi => AllocatorGrows.allocated ⟨by omega, by rw [hsp_15, hsp_9]⟩ (hfp_tb48 i hi).1)
          obtain ⟨hwf_tb72_p, hfp_tb72_eq, hhdr_tb72_eq⟩ := WkBal.htabWF_transfer_unhit hAR_s10 hAR_s15 hwf_tb72
            (fun _ _ _ _ _ _ => by rw [hs15_m_s10])
            (fun i hi => AllocatorGrows.allocated ⟨by omega, by rw [hsp_15, hs10_sp, hsp_9b]⟩ (hfp_tb72 i hi).1)
          -- Package `T_new = [tw_ws.toNat, tb8.toNat, tb16.toNat, tb24.toNat, tb32.toNat, tb40.toNat, tb48.toNat, tb72.toNat]`:
          let T_new : List Nat :=
            [tw_ws.toNat, tb8.toNat, tb16.toNat, tb24.toNat, tb32.toNat, tb40.toNat, tb48.toNat, tb72.toNat]
          have ht_chain : pws.toNat + 40 ≤ tw_ws.toNat ∧ tw_ws.toNat + 88 ≤ pbs.toNat ∧
              pbs.toNat + 80 ≤ tb8.toNat ∧ tb8.toNat + 88 ≤ tb16.toNat ∧
              tb16.toNat + 88 ≤ tb24.toNat ∧ tb24.toNat + 88 ≤ tb32.toNat ∧
              tb32.toNat + 88 ≤ tb40.toNat ∧ tb40.toNat + 88 ≤ tb48.toNat ∧
              tb48.toNat + 88 ≤ tb72.toNat ∧ tb72.toNat + 88 ≤ psk.toNat :=
            ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
          have hT_nd : T_new.Nodup := by
            obtain ⟨_, c01, c12, c23, c34, c45, c56, c67, c78, _⟩ := ht_chain
            dsimp only [T_new]
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
            refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩,
                    ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩,
                    ⟨by omega, by omega, by omega, by omega, by omega⟩,
                    ⟨by omega, by omega, by omega, by omega⟩,
                    ⟨by omega, by omega, by omega⟩,
                    ⟨by omega, by omega⟩,
                    ⟨by omega, not_false⟩⟩
          have hT_ivls : ∀ t ∈ T_new, ∃ lo hi : Nat,
              HtabWF s15 t ∧ globN s1 "heap_ptr" ≤ lo ∧ hi ≤ globN s10 "heap_ptr" ∧
              (∀ i ∈ htabFootprint s15 t, Allocated s15 i ∧ Inside i lo hi ∧
                Disj i (pws.toNat, 40) ∧ Disj i (pbs.toNat, 80) ∧
                Disj i (psk.toNat, 64) ∧ Disj i (pjr.toNat, 32 * 524288)) := by
            have hdisj_of_bounds : ∀ {i : Ivl} {lo hi : Nat},
                Inside i lo hi →
                pws.toNat + 40 ≤ lo →
                (hi ≤ pbs.toNat ∨ pbs.toNat + 80 ≤ lo) →
                hi ≤ globN s10 "heap_ptr" →
                Disj i (pws.toNat, 40) ∧ Disj i (pbs.toNat, 80) ∧
                Disj i (psk.toNat, 64) ∧ Disj i (pjr.toNat, 32 * 524288) := by
              intro i lo hi hin hws_le hbs_or hhi10
              refine ⟨Or.inr (Or.inr (Or.inr (le_trans hws_le hin.1))), ?_, ?_, ?_⟩
              · rcases hbs_or with hle_bs | hbs_le
                · exact Or.inr (Or.inr (Or.inl (le_trans hin.2 hle_bs)))
                · exact Or.inr (Or.inr (Or.inr (le_trans hbs_le hin.1)))
              · exact Or.inr (Or.inr (Or.inl (le_trans hin.2 (by omega))))
              · exact Or.inr (Or.inr (Or.inl (le_trans hin.2 (by omega))))
            intro t ht
            simp only [T_new, List.mem_cons, List.not_mem_nil, or_false] at ht
            rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · refine ⟨globN s1a "heap_ptr", globN s2 "heap_ptr", hwf_tws_p, by omega, by omega, fun i hi => ?_⟩
              rw [hfp_tws_eq] at hi
              have hin := (hfp_tws i hi).2
              exact ⟨AllocatorGrows.allocated hag_s2_s15 (hfp_tws i hi).1,
                hin, hdisj_of_bounds hin (by omega) (Or.inl (by omega)) (by omega)⟩
            · refine ⟨globN s3a "heap_ptr", globN s4 "heap_ptr", hwf_tb8_p, by omega, by omega, fun i hi => ?_⟩
              rw [hfp_tb8_eq] at hi
              have hin := (hfp_tb8 i hi).2
              exact ⟨AllocatorGrows.allocated ⟨by omega, by rw [hsp_15, hsp_4]⟩ (hfp_tb8 i hi).1,
                hin, hdisj_of_bounds hin (by omega) (Or.inr (by omega)) (by omega)⟩
            · refine ⟨globN s4 "heap_ptr", globN s5 "heap_ptr", hwf_tb16_p, by omega, by omega, fun i hi => ?_⟩
              rw [hfp_tb16_eq] at hi
              have hin := (hfp_tb16 i hi).2
              exact ⟨AllocatorGrows.allocated ⟨by omega, by rw [hsp_15, hsp_5]⟩ (hfp_tb16 i hi).1,
                hin, hdisj_of_bounds hin (by omega) (Or.inr (by omega)) (by omega)⟩
            · refine ⟨globN s5 "heap_ptr", globN s6 "heap_ptr", hwf_tb24_p, by omega, by omega, fun i hi => ?_⟩
              rw [hfp_tb24_eq] at hi
              have hin := (hfp_tb24 i hi).2
              exact ⟨AllocatorGrows.allocated ⟨by omega, by rw [hsp_15, hsp_6]⟩ (hfp_tb24 i hi).1,
                hin, hdisj_of_bounds hin (by omega) (Or.inr (by omega)) (by omega)⟩
            · refine ⟨globN s6 "heap_ptr", globN s7 "heap_ptr", hwf_tb32_p, by omega, by omega, fun i hi => ?_⟩
              rw [hfp_tb32_eq] at hi
              have hin := (hfp_tb32 i hi).2
              exact ⟨AllocatorGrows.allocated ⟨by omega, by rw [hsp_15, hsp_7]⟩ (hfp_tb32 i hi).1,
                hin, hdisj_of_bounds hin (by omega) (Or.inr (by omega)) (by omega)⟩
            · refine ⟨globN s7 "heap_ptr", globN s8 "heap_ptr", hwf_tb40_p, by omega, by omega, fun i hi => ?_⟩
              rw [hfp_tb40_eq] at hi
              have hin := (hfp_tb40 i hi).2
              exact ⟨AllocatorGrows.allocated ⟨by omega, by rw [hsp_15, hsp_8]⟩ (hfp_tb40 i hi).1,
                hin, hdisj_of_bounds hin (by omega) (Or.inr (by omega)) (by omega)⟩
            · refine ⟨globN s8 "heap_ptr", globN s9 "heap_ptr", hwf_tb48_p, by omega, by omega, fun i hi => ?_⟩
              rw [hfp_tb48_eq] at hi
              have hin := (hfp_tb48 i hi).2
              exact ⟨AllocatorGrows.allocated ⟨by omega, by rw [hsp_15, hsp_9]⟩ (hfp_tb48 i hi).1,
                hin, hdisj_of_bounds hin (by omega) (Or.inr (by omega)) (by omega)⟩
            · refine ⟨globN s9b "heap_ptr", globN s10 "heap_ptr", hwf_tb72_p, by omega, le_rfl, fun i hi => ?_⟩
              rw [hfp_tb72_eq] at hi
              have hin := (hfp_tb72 i hi).2
              exact ⟨AllocatorGrows.allocated ⟨by omega, by rw [hsp_15, hs10_sp, hsp_9b]⟩ (hfp_tb72 i hi).1,
                hin, hdisj_of_bounds hin (by omega) (Or.inr (by omega)) le_rfl⟩
          have hT_pw : ∀ t ∈ T_new, ∀ u ∈ T_new, t ≠ u →
              ∀ i ∈ htabFootprint s15 t, ∀ j ∈ htabFootprint s15 u, Disj i j := by
            have hpw_ord : T_new.Pairwise (fun t u =>
                ∀ i ∈ htabFootprint s15 t, ∀ j ∈ htabFootprint s15 u, Disj i j) := by
              have hstep_disj : ∀ {t u lo1 hi1 lo2 hi2 : Nat},
                  hi1 ≤ lo2 →
                  (∀ i ∈ htabFootprint s15 t, Inside i lo1 hi1) →
                  (∀ j ∈ htabFootprint s15 u, Inside j lo2 hi2) →
                  ∀ i ∈ htabFootprint s15 t, ∀ j ∈ htabFootprint s15 u, Disj i j :=
                fun hle h1 h2 i hi j hj => WkBal.disj_fresh_sub (h1 i hi) (h2 j hj) hle
              have hi0 : ∀ i ∈ htabFootprint s15 tw_ws.toNat, Inside i (globN s1a "heap_ptr") (globN s2 "heap_ptr") :=
                fun i hi => (hfp_tws i (hfp_tws_eq ▸ hi)).2
              have hi1 : ∀ i ∈ htabFootprint s15 tb8.toNat, Inside i (globN s3a "heap_ptr") (globN s4 "heap_ptr") :=
                fun i hi => (hfp_tb8 i (hfp_tb8_eq ▸ hi)).2
              have hi2 : ∀ i ∈ htabFootprint s15 tb16.toNat, Inside i (globN s4 "heap_ptr") (globN s5 "heap_ptr") :=
                fun i hi => (hfp_tb16 i (hfp_tb16_eq ▸ hi)).2
              have hi3 : ∀ i ∈ htabFootprint s15 tb24.toNat, Inside i (globN s5 "heap_ptr") (globN s6 "heap_ptr") :=
                fun i hi => (hfp_tb24 i (hfp_tb24_eq ▸ hi)).2
              have hi4 : ∀ i ∈ htabFootprint s15 tb32.toNat, Inside i (globN s6 "heap_ptr") (globN s7 "heap_ptr") :=
                fun i hi => (hfp_tb32 i (hfp_tb32_eq ▸ hi)).2
              have hi5 : ∀ i ∈ htabFootprint s15 tb40.toNat, Inside i (globN s7 "heap_ptr") (globN s8 "heap_ptr") :=
                fun i hi => (hfp_tb40 i (hfp_tb40_eq ▸ hi)).2
              have hi6 : ∀ i ∈ htabFootprint s15 tb48.toNat, Inside i (globN s8 "heap_ptr") (globN s9 "heap_ptr") :=
                fun i hi => (hfp_tb48 i (hfp_tb48_eq ▸ hi)).2
              have hi7 : ∀ i ∈ htabFootprint s15 tb72.toNat, Inside i (globN s9b "heap_ptr") (globN s10 "heap_ptr") :=
                fun i hi => (hfp_tb72 i (hfp_tb72_eq ▸ hi)).2
              dsimp only [T_new]
              simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, List.Pairwise.nil, and_true, forall_eq_or_imp, forall_eq, false_implies, true_and]
              refine ⟨⟨hstep_disj (by omega) hi0 hi1, hstep_disj (by omega) hi0 hi2, hstep_disj (by omega) hi0 hi3,
                       hstep_disj (by omega) hi0 hi4, hstep_disj (by omega) hi0 hi5, hstep_disj (by omega) hi0 hi6,
                       hstep_disj (by omega) hi0 hi7⟩,
                      ⟨hstep_disj (by omega) hi1 hi2, hstep_disj (by omega) hi1 hi3, hstep_disj (by omega) hi1 hi4,
                       hstep_disj (by omega) hi1 hi5, hstep_disj (by omega) hi1 hi6, hstep_disj (by omega) hi1 hi7⟩,
                      ⟨hstep_disj (by omega) hi2 hi3, hstep_disj (by omega) hi2 hi4, hstep_disj (by omega) hi2 hi5,
                       hstep_disj (by omega) hi2 hi6, hstep_disj (by omega) hi2 hi7⟩,
                      ⟨hstep_disj (by omega) hi3 hi4, hstep_disj (by omega) hi3 hi5, hstep_disj (by omega) hi3 hi6,
                       hstep_disj (by omega) hi3 hi7⟩,
                      ⟨hstep_disj (by omega) hi4 hi5, hstep_disj (by omega) hi4 hi6, hstep_disj (by omega) hi4 hi7⟩,
                      ⟨hstep_disj (by omega) hi5 hi6, hstep_disj (by omega) hi5 hi7⟩,
                      hstep_disj (by omega) hi6 hi7, fun _ => trivial⟩
            intro t ht u hu hne i hi j hj
            obtain ⟨k1, hk1, rfl⟩ := List.mem_iff_getElem.1 ht
            obtain ⟨k2, hk2, rfl⟩ := List.mem_iff_getElem.1 hu
            have hkne : k1 ≠ k2 := fun h => hne (by subst h; rfl)
            have hget := List.pairwise_iff_getElem.1 hpw_ord
            rcases Nat.lt_or_gt_of_ne hkne with hlt | hgt
            · exact hget k1 k2 hk1 hk2 hlt i hi j hj
            · exact (hget k2 k1 hk2 hk1 hgt j hj i hi).flip
          -- Low memory words `0, 8, 16` preserved from `s` to `s15`:
          have hm0_15 : memW s15 0 = memW s 0 ∧ memW s15 8 = memW s 8 ∧ memW s15 16 = memW s 16 := by
            have hlow : ∀ a : Nat, a + 8 ≤ sourceBase → memW s15 a = memW s a := fun a ha => by
              have hsb_lt : sourceBase < 2 ^ 64 := by decide
              have ha_lt : a < 2 ^ 64 := lt_of_le_of_lt (by omega) hsb_lt
              have hm := hfr_s_s15 (BitVec.ofNat 64 a)
                (fun j hj hcj => by
                  rw [List.mem_singleton.1 hj] at hcj
                  obtain ⟨c1, _⟩ := hcj
                  unfold freeGap at c1; dsimp at c1
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at c1
                  have hsep : sourceBase ≤ scratchStart := by decide
                  have := hAR0.2.2.2.1; omega)
                (fun hcf => by
                  obtain ⟨c1, _⟩ := hcf
                  unfold heapFree at c1; dsimp at c1
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at c1
                  have := hAR0.2.1; omega)
              unfold memW; rw [hm]
            exact ⟨hlow 0 (by decide), hlow 8 (by decide), hlow 16 (by decide)⟩
          -- Fact from `StateInitReady`: if `cdw.toNat ≠ 0`, `cdw.toNat ∉ S_sir` and `cdw.toNat` is distinct from all `bal` tables in `s`!
          have hcd_not_bal : cdw.toNat ≠ 0 →
              cdw.toNat ≠ globN s "bal_accounts" ∧
              cdw.toNat ≠ globN s "bal_idx_accts" ∧
              cdw.toNat ≠ globN s "bal_idx_stor" ∧
              ∀ ad ∈ balRecords s, cdw.toNat ≠ memW s ad ∧ cdw.toNat ≠ memW s (ad + 8) := by
            intro hcd_nz
            rcases hcd_sir with hcd0 | ⟨hwf_cd, _, _, hdisj_cd_sir⟩
            · exact absurd (hcd_nat.symm.trans hcd0) hcd_nz
            · have hcd_not_Ssir : cdw.toNat ∉ S_sir := by
                intro hmem
                have hfp_88 : (cdw.toNat, 88) ∈ htabFootprint s cdw.toNat := by simp [htabFootprint]
                have hown_88 : (cdw.toNat, 88) ∈ worldOwned s S_sir Nd_sir := by
                  unfold worldOwned
                  exact List.mem_append_left _ (List.mem_append_left _
                    (List.mem_flatMap.2 ⟨cdw.toNat, hmem, hfp_88⟩))
                have hd := hdisj_cd_sir _ (by rw [hcd_nat]; exact hfp_88) _ hown_88
                rcases hd with h | h | h | h <;> dsimp at h <;> omega
              have hne_g : ∀ g ∈ globalTableRoots, cdw.toNat ≠ globN s g := by
                intro g hg heq
                rcases hWT_sir.1.2.2.2.2.2.2.1 g hg with h0 | hm
                · exact hcd_nz (heq.trans h0)
                · exact hcd_not_Ssir (heq.symm ▸ hm)
              refine ⟨hne_g "bal_accounts" (by simp [globalTableRoots]),
                      hne_g "bal_idx_accts" (by simp [globalTableRoots]),
                      hne_g "bal_idx_stor" (by simp [globalTableRoots]),
                      fun ad had => ⟨?_, ?_⟩⟩
              · intro heq; exact hcd_not_Ssir (heq.symm ▸ (hWT_sir.1.2.2.2.2.2.2.2.2.2.1 ad had).1)
              · intro heq; exact hcd_not_Ssir (heq.symm ▸ (hWT_sir.1.2.2.2.2.2.2.2.2.2.1 ad had).2.1)
          -- Now enter the `∀ S Nd` quantifier of `WorldStepIn`:
          intro S Nd hWT hTS _
          obtain ⟨hT, hJ, hF, hTr⟩ := hWT
          -- Step B: Obtain `Nd'` from `hret_dw` at `(S, Nd)` and transfer `NodeHeap` to `s15`:
          have hNH_ent : NodeHeap ent_dw Nd := by
            have hag_0_ent : AllocatorGrows s ent_dw := ⟨hhp_0_s0c, by change globN s0c "scratch_ptr" ≤ _; omega⟩
            exact (R10Shards.P26_P28.nodeHeap_congr_bytes hAR0.1 hAR_ent.1 hag_0_ent hTr.1
              (fun n hn => hunhit_s_s0c _ (by unfold nodeIvl nodeSize; split_ifs <;> omega) (hTr.1.1 n hn).2.1)
              (fun n hn h12 hp_nz k hk => by
                rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, _, _⟩
                · exact absurd h0 hp_nz
                · exact R10Shards.P26_P28.memB_eq_of_ivlUnhit (hunhit_s_s0c _ hp_nz hal_p) hs0c_be
                    (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hAR0.2 hal_p).2
                    ⟨by dsimp; omega, by dsimp; omega⟩)).1
          have hnd_ent_alloc : ∀ o ∈ nodeExtents ent_dw Nd, o.2 = 0 ∨ Allocated ent_dw o := by
            intro o ho
            unfold nodeExtents at ho
            obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
            rcases hno with rfl | rfl
            · exact Or.inr (hNH_ent.1 n hn).2.1
            · unfold nodePath; split_ifs with hc
              · rcases (hNH_ent.1 n hn).2.2.2.2.2.2.1 hc.1 with h0 | ⟨_, hal, _⟩
                · exact absurd h0 hc.2
                · exact Or.inr hal
              · exact Or.inl rfl
          obtain ⟨rootw2, Nd', hv_dw2, hNd_sub, hNd_cls_dw, hNH_dw, hroot_Nd'⟩ :=
            hret_dw Nd hNH_ent hnd_ent_alloc (.val (.word rootw)) rfl
          have hrootw_eq : rootw2 = rootw := by
            cases hv_dw2; rfl
          subst hrootw_eq
          have hNH_s1 : NodeHeap s1 Nd' := hNH_dw
          have hunhit_s1_s15_disj : ∀ i : Ivl, i.2 ≠ 0 → Allocated s1 i → Disj i (pws.toNat, 40) →
              R10Shards.P26_P28.IvlUnhit s1 s15 i := by
            intro i hipos hal_i hd_ws
            have hd_hf : Disj i (globN s1 "heap_ptr", globN s15 "heap_ptr" - globN s1 "heap_ptr") :=
              (InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAR_s1.2 hAR_s15.2 hal_i
                ⟨le_rfl, by omega⟩).flip
            have h40_mod8 : (40 : Nat) % 8 = 0 := by decide
            exact ivlUnhit_of_frameOutside_aligned hipos hfr_s1_s15
              (fun j hj => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                rcases hj with rfl | rfl
                · exact ⟨hsp8_s, rfl⟩
                · exact ⟨hpws8, h40_mod8⟩)
              ⟨hAR_s1.2.2.2.2.2.2.1, by have := hAR_s1.2.2.2.2.2.2.1; have := hAR_s15.2.2.2.2.2.2.1; omega⟩
              (fun j hj => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                rcases hj with rfl | rfl
                · exact Or.inr (Or.inl rfl)
                · exact hd_ws)
              hd_hf
          -- Classify `Nd'` intervals at `s1`: every `nodeIvl s1 n` and `nodePath s1 n` is `(0, 0)`, in `nodeExtents s Nd`, or `Inside _ (globN s0c "heap_ptr") (globN s1 "heap_ptr")`!
          have hold_ivl_s1 : ∀ n ∈ Nd, nodeIvl s1 n = nodeIvl s n ∧ nodePath s1 n = nodePath s n := by
            intro n hn
            have hpos : (nodeIvl s n).2 ≠ 0 := by dsimp [nodeIvl]; unfold nodeSize; split_ifs <;> decide
            have hun_0_1 : R10Shards.P26_P28.IvlUnhit s s1 (n, nodeSize (memW s n)) :=
              unhit_p26_of_free_frame_local hAR0.2 hfr_s_s1 hpos (hTr.1.1 n hn).2.1
            have hn8 : n % 8 = 0 := (hTr.1.1 n hn).2.2.2.1.1
            have hhi_n : n + nodeSize (memW s n) ≤ 2 ^ 64 := (ivl_allocated_bound hAR0.2 (hTr.1.1 n hn).2.1).2
            have hsz32 : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
            have hw0 : memW s1 n = memW s n :=
              R10Shards.P26_P28.memW_eq_of_ivlUnhit hun_0_1 hn8 hhi_n ⟨by dsimp; omega, by dsimp; omega⟩
            refine ⟨by unfold nodeIvl; rw [hw0], ?_⟩
            by_cases h12 : memW s n = 1 ∨ memW s n = 2
            · have hsz56 : 56 ≤ nodeSize (memW s n) := by
                unfold nodeSize; rcases h12 with h1 | h2 <;> simp [*]
              have hw32 : memW s1 (n + 32) = memW s (n + 32) :=
                R10Shards.P26_P28.memW_eq_of_ivlUnhit hun_0_1 (by omega) hhi_n ⟨by dsimp; omega, by dsimp; omega⟩
              have hw40 : memW s1 (n + 40) = memW s (n + 40) :=
                R10Shards.P26_P28.memW_eq_of_ivlUnhit hun_0_1 (by omega) hhi_n ⟨by dsimp; omega, by dsimp; omega⟩
              unfold nodePath; rw [hw0, hw32, hw40]
            · unfold nodePath; rw [hw0]; simp [h12]
          have hnd'_s1_cls : ∀ o ∈ nodeExtents s1 Nd',
              o = (0, 0) ∨ o ∈ nodeExtents s Nd ∨ Inside o (globN s0c "heap_ptr") (globN s1 "heap_ptr") := by
            intro o ho
            unfold nodeExtents at ho
            obtain ⟨n, hn', hno⟩ := List.mem_flatMap.1 ho
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
            rcases hNd_cls_dw n hn' with hn_old | ⟨hin_ivl, hpath_cls⟩
            · obtain ⟨e_ivl, e_p⟩ := hold_ivl_s1 n hn_old
              right; left; unfold nodeExtents
              refine List.mem_flatMap.2 ⟨n, hn_old, ?_⟩
              rcases hno with rfl | rfl
              · rw [e_ivl]; simp
              · rw [e_p]; simp
            · rcases hno with rfl | rfl
              · exact Or.inr (Or.inr hin_ivl)
              · rcases hpath_cls with hp0 | hin_p
                · exact Or.inl hp0
                · exact Or.inr (Or.inr hin_p)
          have hnd'_disj_ws : ∀ o ∈ nodeExtents s1 Nd', Disj o (pws.toNat, 40) := by
            intro o ho
            rcases hnd'_s1_cls o ho with rfl | ho_old | ho_fresh
            · exact Or.inl rfl
            · unfold nodeExtents at ho_old
              obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho_old
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
              have hal_or_0 : o.2 = 0 ∨ Allocated s o := by
                rcases hno with rfl | rfl
                · exact Or.inr (hTr.1.1 n hn).2.1
                · unfold nodePath; split_ifs with hc
                  · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hc.1 with h0 | ⟨_, hal, _⟩
                    · exact absurd h0 hc.2
                    · exact Or.inr hal
                  · exact Or.inl rfl
              rcases hal_or_0 with h0 | hal_o
              · exact Or.inl h0
              · exact (InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAR0.2 hAR_s0c.2 hal_o
                  ⟨by rw [hpws_eq], by rw [hs0c_hp, hqws_val]⟩).flip
            · exact Or.inr (Or.inr (Or.inr (by dsimp [Inside] at ho_fresh; omega)))
          obtain ⟨hNH_15, hne_15_eq⟩ := R10Shards.P26_P28.nodeHeap_congr_bytes hAR_s1.1 hAR_s15.1
            ⟨by omega, by rw [hsp_15, hs1_sp]⟩ hNH_s1
            (fun n hn => hunhit_s1_s15_disj _ (by unfold nodeIvl nodeSize; split_ifs <;> omega)
              (hNH_s1.1 n hn).2.1
              (hnd'_disj_ws _ (by unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp⟩)))
            (fun n hn h12 hp_nz k hk => by
              rcases (hNH_s1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, _, _⟩
              · exact absurd h0 hp_nz
              · have hp_mem : (memW s1 (n + 32), memW s1 (n + 40)) ∈ nodeExtents s1 Nd' := by
                  unfold nodeExtents
                  refine List.mem_flatMap.2 ⟨n, hn, ?_⟩
                  simp [nodePath, h12, hp_nz]
                exact R10Shards.P26_P28.memB_eq_of_ivlUnhit
                  (hunhit_s1_s15_disj _ hp_nz hal_p (hnd'_disj_ws _ hp_mem))
                  (hbe_15.trans hs1_be.symm)
                  (InitECandidate.Solver.Wave8Contracts.M08.ivl_allocated_bound hAR_s1.2 hal_p).2
                  ⟨by dsimp; omega, by dsimp; omega⟩)
          -- Step C: `FixedTyped s15`, `JournalTyped s15 (S ++ T_new)`, `TablesTyped s15 (S ++ T_new)`, `TriesTypedWith s15 (S ++ T_new) Nd'`!
          have hu_tab_s : ∀ u ∈ S, ∀ i ∈ htabFootprint s u, R10Shards.P26_P28.IvlUnhit s s15 i :=
            fun u hu i hi => hunhit_s_s15 i (R16WkAcctWs.htabFootprint_len_pos (hT.2.1 u hu).1 hi) (((hT.2.1 u hu).2 i hi).1)
          have hu_fix_s : ∀ i ∈ fixedObjects s, i.2 ≠ 0 → R10Shards.P26_P28.IvlUnhit s s15 i :=
            fun i hi hipos => hunhit_s_s15 i hipos (by
              rcases hF.1 i hi with h0 | ⟨hal, _⟩
              · exact absurd h0 hipos
              · exact hal)
          have hcore_kept : ∀ g ∈ (["bo", "bal_accounts", "bal_idx_accts", "bal_idx_stor"] : List String),
              globN s15 g = globN s g := by
            intro g hg
            have hnot : ofString g ∉
                (["bs", "heap_ptr", "journal", "journal_cap", "journal_n", "scratch_ptr", "sk_buf", "ts", "ws"] : List String).map ofString := by
              revert g hg; decide
            exact globN_eq_of_lookup (hgk_15 (ofString g) hnot)
          have hu_bo_s : globN s "bo" ≠ 0 → R10Shards.P26_P28.IvlUnhit s s15 (globN s "bo", 88) := fun hnz => by
            have hm := R10Shards.P26_P28.typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
            simp only [hnz, ↓reduceIte] at hm
            have h88_ne : (88 : Nat) ≠ 0 := by decide
            exact hu_fix_s _ hm h88_ne
          have hu_bo_lst_s : ∀ i ∈ blockOutObjects s, i.2 = 24 → R10Shards.P26_P28.IvlUnhit s s15 i :=
            fun i hi h24 => hu_fix_s i (by unfold fixedObjects; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hi)))) (by omega)
          have hu_bal_s : ∀ i ∈ balObjects s, i.2 ≠ 0 → R10Shards.P26_P28.IvlUnhit s s15 i :=
            fun i hi hipos => hu_fix_s i (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)) hipos
          have hbo_eq_15 := R10Shards.P26_P28.blockOutObjects_eq_of_bo_unhit hAR0.2 hF
            (hcore_kept "bo" (by decide)) hT.2.2.2.2.2.2.2.2.2.2.1 hu_bo_s hu_bo_lst_s
          have hbal_eq_15 := R10Shards.P26_P28.balObjects_eq_of_unhit hAR0.2 hT hF
            (hcore_kept "bal_accounts" (by decide)) hu_tab_s hu_bal_s ⟨hm0_15.2.1, hm0_15.2.2⟩
          -- `FreshBufsOK s s15` and `fixedTyped_state_init`:
          have hbuf_classify : ∀ gn ∈ globalBuffers,
              (gn.1 = "ws" ∧ gn.2 = 40) ∨ (gn.1 = "bs" ∧ gn.2 = 80) ∨
              (gn.1 = "sk_buf" ∧ gn.2 = 64) ∨ (gn.1 = "ts" ∧ gn.2 = 72) ∨
              globN s15 gn.1 = globN s gn.1 := by
            have hgb_ws : ("ws", 40) ∈ globalBuffers := by decide
            have hgb_bs : ("bs", 80) ∈ globalBuffers := by decide
            have hgb_sk : ("sk_buf", 64) ∈ globalBuffers := by decide
            have hgb_ts : ("ts", 72) ∈ globalBuffers := by decide
            have hnodup_gb : (globalBuffers.map Prod.fst).Nodup := by decide
            have hgb_unique : ∀ {a b : String × Nat}, a ∈ globalBuffers → b ∈ globalBuffers → a.1 = b.1 → a.2 = b.2 := by
              intro a b ha hb heq
              obtain ⟨i1, hi1, he1⟩ := List.mem_iff_getElem.1 ha
              obtain ⟨i2, hi2, he2⟩ := List.mem_iff_getElem.1 hb
              have hinj := List.nodup_iff_injective_getElem.1 hnodup_gb
              have hfin : (⟨i1, by simpa using hi1⟩ : Fin (globalBuffers.map Prod.fst).length) =
                  ⟨i2, by simpa using hi2⟩ :=
                hinj (by simp only [List.getElem_map]; rw [he1, he2]; exact heq)
              have hi_eq : i1 = i2 := congrArg Fin.val hfin
              subst hi_eq; rw [he1] at he2; exact congrArg Prod.snd he2
            intro gn hgn
            by_cases h1 : gn.1 = "ws"
            · exact Or.inl ⟨h1, hgb_unique hgn hgb_ws h1⟩
            · by_cases h2 : gn.1 = "bs"
              · exact Or.inr (Or.inl ⟨h2, hgb_unique hgn hgb_bs h2⟩)
              · by_cases h3 : gn.1 = "sk_buf"
                · exact Or.inr (Or.inr (Or.inl ⟨h3, hgb_unique hgn hgb_sk h3⟩))
                · by_cases h4 : gn.1 = "ts"
                  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h4, hgb_unique hgn hgb_ts h4⟩)))
                  · right; right; right; right
                    have hnot : ofString gn.1 ∉
                        (["bs", "heap_ptr", "journal", "journal_cap", "journal_n", "scratch_ptr", "sk_buf", "ts", "ws"] : List String).map ofString := by
                      revert gn hgn h1 h2 h3 h4
                      decide
                    exact globN_eq_of_lookup (hgk_15 (ofString gn.1) hnot)
          have hbuf_15 : R10Shards.P26_P28.FreshBufsOK s s15 := by
            have hnodup_gb : (globalBuffers.map Prod.fst).Nodup := by decide
            refine ⟨fun gn hgn => ?_, List.pairwise_iff_getElem.2 fun idx1 idx2 hi1 hi2 hlt ha hb => ?_⟩
            · rcases hbuf_classify gn hgn with ⟨h, hsz⟩ | ⟨h, hsz⟩ | ⟨h, hsz⟩ | ⟨h, _⟩ | hsame
              · right; right; rw [h, hsz, hws_15]
                exact ⟨hpws8, by dsimp [Inside]; omega, by dsimp [Inside]; omega⟩
              · right; right; rw [h, hsz, hbs_15]
                exact ⟨hpbs8, by dsimp [Inside]; omega, by dsimp [Inside]; omega⟩
              · right; right; rw [h, hsz, hsk_15]
                exact ⟨hpsk8, by dsimp [Inside]; omega, by dsimp [Inside]; omega⟩
              · right; left; rw [h, hts_15]
              · exact Or.inl hsame
            · have hm1 := List.getElem_mem hi1
              have hm2 := List.getElem_mem hi2
              have hne_gn : globalBuffers[idx1].1 ≠ globalBuffers[idx2].1 := by
                have hpw_gb := List.pairwise_iff_getElem.1 hnodup_gb
                have hraw := hpw_gb idx1 idx2 (by simpa using hi1) (by simpa using hi2) hlt
                simpa only [List.getElem_map] using hraw
              rcases hbuf_classify _ hm1 with ⟨e1, z1⟩ | ⟨e1, z1⟩ | ⟨e1, z1⟩ | ⟨e1, _⟩ | hs1_eq
              · rcases hbuf_classify _ hm2 with ⟨e2, _⟩ | ⟨e2, z2⟩ | ⟨e2, z2⟩ | ⟨e2, _⟩ | hs2_eq
                · exact absurd (e1.trans e2.symm) hne_gn
                · rw [e1, z1, e2, z2, hws_15, hbs_15]; exact Or.inr (Or.inr (Or.inl (by omega)))
                · rw [e1, z1, e2, z2, hws_15, hsk_15]; exact Or.inr (Or.inr (Or.inl (by omega)))
                · exact absurd (e2 ▸ hb.2) (by rw [hts_15]; exact not_not.2 rfl)
                · exact absurd hs2_eq hb.1
              · rcases hbuf_classify _ hm2 with ⟨e2, z2⟩ | ⟨e2, _⟩ | ⟨e2, z2⟩ | ⟨e2, _⟩ | hs2_eq
                · rw [e1, z1, e2, z2, hbs_15, hws_15]; exact Or.inr (Or.inr (Or.inr (by omega)))
                · exact absurd (e1.trans e2.symm) hne_gn
                · rw [e1, z1, e2, z2, hbs_15, hsk_15]; exact Or.inr (Or.inr (Or.inl (by omega)))
                · exact absurd (e2 ▸ hb.2) (by rw [hts_15]; exact not_not.2 rfl)
                · exact absurd hs2_eq hb.1
              · rcases hbuf_classify _ hm2 with ⟨e2, z2⟩ | ⟨e2, z2⟩ | ⟨e2, _⟩ | ⟨e2, _⟩ | hs2_eq
                · rw [e1, z1, e2, z2, hsk_15, hws_15]; exact Or.inr (Or.inr (Or.inr (by omega)))
                · rw [e1, z1, e2, z2, hsk_15, hbs_15]; exact Or.inr (Or.inr (Or.inr (by omega)))
                · exact absurd (e1.trans e2.symm) hne_gn
                · exact absurd (e2 ▸ hb.2) (by rw [hts_15]; exact not_not.2 rfl)
                · exact absurd hs2_eq hb.1
              · exact absurd (e1 ▸ ha.2) (by rw [hts_15]; exact not_not.2 rfl)
              · exact absurd hs1_eq ha.1
          obtain ⟨hF_15, hfix_15_cls⟩ := fixedTyped_state_init hAR0 hAR_s15 hag_0_15 hF hbuf_15
            (by rw [hjcap_15]; decide)
            (by rw [hjr_15]; exact hpjr8)
            (by rw [hjr_15, hjcap_15]; exact ⟨by dsimp [Inside]; omega, by dsimp [Inside]; omega⟩)
            (fun gn hgn ⟨hne_g, hnz_g⟩ => by
              rw [hjr_15, hjcap_15]
              rcases hbuf_classify gn hgn with ⟨e, z⟩ | ⟨e, z⟩ | ⟨e, z⟩ | ⟨e, _⟩ | hsame
              · rw [e, z, hws_15]; exact Or.inr (Or.inr (Or.inl (by omega)))
              · rw [e, z, hbs_15]; exact Or.inr (Or.inr (Or.inl (by omega)))
              · rw [e, z, hsk_15]; exact Or.inr (Or.inr (Or.inl (by omega)))
              · rw [e, hts_15] at hnz_g; exact absurd rfl hnz_g
              · exact absurd hsame hne_g)
            hbo_eq_15.1 hbal_eq_15.1
          -- Also refine classification of `fixedObjects s15` into exact intervals so `T_new` and `Nd'` are disjoint from them!
          have hfix_15_exact : ∀ j ∈ fixedObjects s15,
              j ∈ fixedObjects s ∨ j = (0, 0) ∨ j = (pws.toNat, 40) ∨ j = (pbs.toNat, 80) ∨
              j = (psk.toNat, 64) ∨ j = (pjr.toNat, 32 * 524288) := by
            intro j hj
            unfold fixedObjects at hj
            rcases List.mem_append.1 hj with hj123 | hj_bal
            · rcases List.mem_append.1 hj123 with hj12 | hj_bo
              · rcases List.mem_append.1 hj12 with hj_gb | hj_jr
                · obtain ⟨gn, hgn, rfl⟩ := List.mem_map.1 hj_gb
                  rcases hbuf_classify gn hgn with ⟨e, z⟩ | ⟨e, z⟩ | ⟨e, z⟩ | ⟨e, _⟩ | hsame
                  · have hpws_nz : pws.toNat ≠ 0 := by
                      have hsb : 0 < sourceBase := by decide
                      exact Nat.ne_of_gt (lt_of_lt_of_le hsb hpws_lo)
                    rw [e, z, hws_15, if_neg hpws_nz]; exact Or.inr (Or.inr (Or.inl rfl))
                  · have hpbs_nz : pbs.toNat ≠ 0 := by
                      have hsb : 0 < sourceBase := by decide
                      exact Nat.ne_of_gt (lt_of_lt_of_le hsb hpbs_lo)
                    rw [e, z, hbs_15, if_neg hpbs_nz]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
                  · have hpsk_nz : psk.toNat ≠ 0 := by
                      have hsb : 0 < sourceBase := by decide
                      have hpsk_lo : sourceBase ≤ psk.toNat := by rw [hpsk_eq]; exact hAR_s10.2.1
                      exact Nat.ne_of_gt (lt_of_lt_of_le hsb hpsk_lo)
                    rw [e, z, hsk_15, if_neg hpsk_nz]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                  · rw [e, hts_15, if_pos rfl]; exact Or.inr (Or.inl rfl)
                  · left; rw [hsame]; unfold fixedObjects
                    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨gn, hgn, rfl⟩)))
                · simp only [List.mem_singleton] at hj_jr; subst hj_jr
                  rw [hjcap_15, hjr_15]
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp)))))
              · left; rw [hbo_eq_15.1] at hj_bo
                unfold fixedObjects; exact List.mem_append_left _ (List.mem_append_right _ hj_bo)
            · left; rw [hbal_eq_15.1] at hj_bal
              unfold fixedObjects; exact List.mem_append_right _ hj_bal
          -- Step D: `JournalTyped s15 (S ++ T_new)`:
          have hJ_15 : JournalTyped s15 (S ++ T_new) := by
            refine ⟨by rw [hjn_15]; omega, by rw [hjcap_15]; decide, ?_, fun i hi => by rw [hjn_15] at hi; omega⟩
            right
            have hjr_mem_fix : (globN s15 "journal", 32 * globN s15 "journal_cap") ∈ fixedObjects s15 := by
              unfold fixedObjects
              apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
              rw [hjcap_15]; simp
            rcases hF_15.1 _ hjr_mem_fix with h0 | hok
            · rw [hjcap_15] at h0; dsimp at h0; omega
            · exact hok
          -- Step E: Transfer `S` tables from `s` to `s15` and prove `S ++ T_new` disjointness:
          have hS_tr : ∀ u ∈ S, HtabWF s15 u ∧ htabFootprint s15 u = htabFootprint s u ∧
              (∀ k, k < 11 → hdr s15 u k = hdr s u k) := by
            intro u hu
            exact WkBal.htabWF_transfer_unhit hAR0 hAR_s15 (hT.2.1 u hu).1
              (fun i hi a ha8 hlo hhi => hu_tab_s u hu i hi a ha8 ⟨by omega, by omega⟩)
              (fun i hi => hag_0_15.allocated ((hT.2.1 u hu).2 i hi).1)
          have hT_disj_S : ∀ t ∈ T_new, t ∉ S := by
            intro t ht htS
            obtain ⟨lo, hi, _, hlo_t, hhi_10, hfp_t⟩ := hT_ivls t ht
            have hu88_15 : (t, 88) ∈ htabFootprint s15 t := by simp [htabFootprint]
            have hu88_s : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
            have hin_u := (hfp_t _ hu88_15).2.1
            have hal_s := ((hT.2.1 t htS).2 _ hu88_s).1
            have hbound_s : t + 88 ≤ globN s "heap_ptr" ∨ scratchStart ≤ t := by
              rcases hal_s with h1 | h2
              · exact Or.inl h1.2
              · exact Or.inr (le_trans hAR0.2.2.2.1 (le_trans hAR0.2.2.2.2.1 h2.1))
            have hlim10 := hAR_s10.2.2.1
            have hsep : heapLimit ≤ scratchStart := by decide
            dsimp [Inside] at hin_u
            omega
          have hST_nd : (S ++ T_new).Nodup :=
            List.nodup_append.2 ⟨hT.1, hT_nd, fun u hu v hv heq => hT_disj_S u (heq ▸ hv) hu⟩
          -- Step F: `RolesOK s15 (S ++ T_new) (worldRoleSlots s15) (journalRoleSlots s15)`:
          have hjrs_15 : journalRoleSlots s15 = [] := by
            unfold journalRoleSlots; rw [hjn_15]; rfl
          have hcnt_tws_15 : hdr s15 tw_ws.toNat 3 = 0 := (hhdr_tws_eq 3 (by omega)).trans hcnt_tws
          have hcnt_tb32_15 : hdr s15 tb32.toNat 3 = 0 := (hhdr_tb32_eq 3 (by omega)).trans hcnt_tb32
          have hpws_nz : pws.toNat ≠ 0 := by
            have hsb : 0 < sourceBase := by decide
            exact Nat.ne_of_gt (lt_of_lt_of_le hsb hpws_lo)
          have hpbs_nz : pbs.toNat ≠ 0 := by
            have hsb : 0 < sourceBase := by decide
            exact Nat.ne_of_gt (lt_of_lt_of_le hsb hpbs_lo)
          have hbrec_15 : balRecords s15 = balRecords s :=
            R10Shards.P26_P28.balRecords_eq_of_unhit hT (hcore_kept "bal_accounts" (by decide))
              (fun hnz => by
                rcases hT.2.2.2.2.2.2.1 "bal_accounts" (by simp [globalTableRoots]) with h0 | hm
                · exact absurd h0 hnz
                · exact hu_tab_s _ hm)
          have hroles_15 : RolesOK s15 (S ++ T_new) (worldRoleSlots s15) (journalRoleSlots s15) := by
            rw [hjrs_15]
            let add_p : List (Nat × String) :=
              [(tw_ws.toNat, "ws+32"), (tb8.toNat, "bs+8"), (tb16.toNat, "bs+16"),
               (tb24.toNat, "bs+24"), (tb32.toNat, "bs+32"), (tb40.toNat, "bs+40"),
               (tb48.toNat, "bs+48"), (tb72.toNat, "bs+72")]
            let suf_p : List (Nat × String) :=
              ([(globN s15 "bal_accounts", "bal_accounts"),
                (globN s15 "bal_idx_accts", "bal_idx_accts"),
                (globN s15 "bal_idx_stor", "bal_idx_stor")] ++
               ((balRecords s15).flatMap fun ad => [(memW s15 ad, "bal.stor"), (memW s15 (ad + 8), "bal.reads")])).filter
                (fun a => a.1 != 0)
            let pre_cd : List (Nat × String) :=
              if cdw.toNat = 0 then [] else [(cdw.toNat, "ws+16")]
            have hwrs_15_eq : worldRoleSlots s15 = pre_cd ++ add_p ++ suf_p := by
              unfold worldRoleSlots
              have hrec_ws_15 : (recRoles s15 "ws" [(16, "ws+16"), (32, "ws+32")]).filter (fun a => a.1 != 0) =
                  pre_cd ++ [(tw_ws.toNat, "ws+32")] := by
                unfold recRoles
                rw [hws_15, if_neg hpws_nz]
                simp only [List.map, hmw15_ws16, hmw15_ws32]
                have hnz_tws := WkBal.htab_nonzero_of_wf hwf_tws_p
                by_cases hcd0 : cdw.toNat = 0 <;> simp [pre_cd, hcd0, hnz_tws]
              have hrec_bs_15 : (recRoles s15 "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"),
                  (32, "bs+32"), (40, "bs+40"), (48, "bs+48"), (72, "bs+72")]).filter (fun a => a.1 != 0) =
                  [(tb8.toNat, "bs+8"), (tb16.toNat, "bs+16"), (tb24.toNat, "bs+24"),
                   (tb32.toNat, "bs+32"), (tb40.toNat, "bs+40"), (tb48.toNat, "bs+48"), (tb72.toNat, "bs+72")] := by
                unfold recRoles
                rw [hbs_15, if_neg hpbs_nz]
                simp only [List.map, hmw15_bs8, hmw15_bs16, hmw15_bs24, hmw15_bs32, hmw15_bs40, hmw15_bs48, hmw15_bs72]
                have z1 := WkBal.htab_nonzero_of_wf hwf_tb8_p
                have z2 := WkBal.htab_nonzero_of_wf hwf_tb16_p
                have z3 := WkBal.htab_nonzero_of_wf hwf_tb24_p
                have z4 := WkBal.htab_nonzero_of_wf hwf_tb32_p
                have z5 := WkBal.htab_nonzero_of_wf hwf_tb40_p
                have z6 := WkBal.htab_nonzero_of_wf hwf_tb48_p
                have z7 := WkBal.htab_nonzero_of_wf hwf_tb72_p
                simp [z1, z2, z3, z4, z5, z6, z7]
              have hrec_ts_15 : recRoles s15 "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"),
                  (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")] = [] := by
                unfold recRoles; rw [hts_15]; simp
              have hnest_bs_15 : nestRoles s15 "bs" "bs.inner" = [] := by
                unfold nestRoles
                rw [hbs_15, if_neg hpbs_nz, hmw15_bs32, if_neg (WkBal.htab_nonzero_of_wf hwf_tb32_p)]
                unfold htabValues; rw [hcnt_tb32_15]; rfl
              have hnest_ts_15 : nestRoles s15 "ts" "ts.inner" = [] := by
                unfold nestRoles; rw [hts_15]; simp
              rw [hrec_ts_15, hnest_bs_15, hnest_ts_15]
              simp only [List.filter_append, hrec_ws_15, hrec_bs_15, List.filter_nil, List.append_nil, List.nil_append]
              simp only [add_p, suf_p, List.filter_append, List.append_assoc, List.cons_append, List.nil_append]
            have hsuf_eq_s : suf_p =
                ([(globN s "bal_accounts", "bal_accounts"),
                  (globN s "bal_idx_accts", "bal_idx_accts"),
                  (globN s "bal_idx_stor", "bal_idx_stor")] ++
                 ((balRecords s).flatMap fun ad => [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")])).filter
                  (fun a => a.1 != 0) := by
              have eba := hcore_kept "bal_accounts" (by decide)
              have ebia := hcore_kept "bal_idx_accts" (by decide)
              have ebis := hcore_kept "bal_idx_stor" (by decide)
              have hflat_eq : ((balRecords s15).flatMap fun ad => [(memW s15 ad, "bal.stor"), (memW s15 (ad + 8), "bal.reads")]) =
                  ((balRecords s).flatMap fun ad => [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")]) := by
                have hcongr : ∀ ad ∈ balRecords s15,
                    [(memW s15 ad, "bal.stor"), (memW s15 (ad + 8), "bal.reads")] =
                    [(memW s ad, "bal.stor"), (memW s (ad + 8), "bal.reads")] := by
                  intro ad had
                  obtain ⟨h0, h8, _⟩ := hbal_eq_15.2 ad had
                  rw [h0, h8]
                rw [List.flatMap_congr hcongr, hbrec_15]
              dsimp only [suf_p]
              rw [eba, ebia, ebis, hflat_eq]
            have hsuf_sub_wrs : List.Sublist suf_p (worldRoleSlots s) := by
              rw [hsuf_eq_s]
              unfold worldRoleSlots
              simp only [List.filter_append]
              have h1 : List.Sublist
                  (List.filter (fun a => a.1 != 0) [(globN s "bal_accounts", "bal_accounts"),
                    (globN s "bal_idx_accts", "bal_idx_accts"), (globN s "bal_idx_stor", "bal_idx_stor")])
                  (List.filter (fun a => a.1 != 0) (recRoles s "ws" [(16, "ws+16"), (32, "ws+32")]) ++
                   List.filter (fun a => a.1 != 0) (recRoles s "bs" [(8, "bs+8"), (16, "bs+16"), (24, "bs+24"), (32, "bs+32"), (40, "bs+40"), (48, "bs+48"), (72, "bs+72")]) ++
                   List.filter (fun a => a.1 != 0) (recRoles s "ts" [(8, "ts+8"), (16, "ts+16"), (24, "ts+24"), (32, "ts+32"), (40, "ts+40"), (48, "ts+48"), (56, "ts+56"), (64, "ts+64")]) ++
                   List.filter (fun a => a.1 != 0) [(globN s "bal_accounts", "bal_accounts"),
                    (globN s "bal_idx_accts", "bal_idx_accts"), (globN s "bal_idx_stor", "bal_idx_stor")] ++
                   List.filter (fun a => a.1 != 0) (nestRoles s "bs" "bs.inner") ++
                   List.filter (fun a => a.1 != 0) (nestRoles s "ts" "ts.inner")) := by
                apply List.Sublist.trans _ (List.sublist_append_left _ _)
                apply List.Sublist.trans _ (List.sublist_append_left _ _)
                exact List.sublist_append_right _ _
              simpa only [List.append_assoc] using List.Sublist.append h1 (List.Sublist.refl _)
            have hadd_ok : ∀ a ∈ add_p, a.1 ∈ T_new ∧ hdr s15 a.1 0 = roleKeyLen a.2 := by
              intro a ha
              simp only [add_p, List.mem_cons, List.not_mem_nil, or_false] at ha
              rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
              · exact ⟨by simp [T_new], (hhdr_tws_eq 0 (by omega)).trans (hhdr_tws.trans (show (32#64 : BitVec 64).toNat = roleKeyLen "ws+32" by decide))⟩
              · exact ⟨by simp [T_new], (hhdr_tb8_eq 0 (by omega)).trans (hhdr_tb8.trans (show (20#64 : BitVec 64).toNat = roleKeyLen "bs+8" by decide))⟩
              · exact ⟨by simp [T_new], (hhdr_tb16_eq 0 (by omega)).trans (hhdr_tb16.trans (show (20#64 : BitVec 64).toNat = roleKeyLen "bs+16" by decide))⟩
              · exact ⟨by simp [T_new], (hhdr_tb24_eq 0 (by omega)).trans (hhdr_tb24.trans (show (52#64 : BitVec 64).toNat = roleKeyLen "bs+24" by decide))⟩
              · exact ⟨by simp [T_new], (hhdr_tb32_eq 0 (by omega)).trans (hhdr_tb32.trans (show (20#64 : BitVec 64).toNat = roleKeyLen "bs+32" by decide))⟩
              · exact ⟨by simp [T_new], (hhdr_tb40_eq 0 (by omega)).trans (hhdr_tb40.trans (show (52#64 : BitVec 64).toNat = roleKeyLen "bs+40" by decide))⟩
              · exact ⟨by simp [T_new], (hhdr_tb48_eq 0 (by omega)).trans (hhdr_tb48.trans (show (32#64 : BitVec 64).toNat = roleKeyLen "bs+48" by decide))⟩
              · exact ⟨by simp [T_new], (hhdr_tb72_eq 0 (by omega)).trans (hhdr_tb72.trans (show (20#64 : BitVec 64).toNat = roleKeyLen "bs+72" by decide))⟩
            have hadd_pw : add_p.Pairwise (fun a b => a.1 ≠ b.1) := by
              have hpw_t : T_new.Pairwise (· ≠ ·) := List.nodup_iff_pairwise_ne.1 hT_nd
              have hmap_eq : T_new = add_p.map Prod.fst := rfl
              rw [hmap_eq] at hpw_t
              exact List.Pairwise.of_map Prod.fst (fun {a b} hne heq => absurd heq hne) hpw_t
            have hne_ST : ∀ u ∈ S, ∀ v ∈ T_new, u ≠ v := fun u hu v hv heq => hT_disj_S u (heq ▸ hv) hu
            have hpre_ok : ∀ a ∈ pre_cd, a.1 ∈ S ∧ hdr s15 a.1 0 = roleKeyLen a.2 := by
              intro a ha
              by_cases hcd0 : cdw.toNat = 0
              · simp [pre_cd, hcd0] at ha
              · simp only [pre_cd, hcd0, ↓reduceIte, List.mem_singleton] at ha; subst ha
                have hcd_S : cdw.toNat ∈ S := by
                  apply hTS
                  dsimp only
                  rw [hcd_nat, if_neg hcd0]
                  exact List.mem_singleton.2 rfl
                rcases hcd_sir with h0 | ⟨_, hhdr_cd, _, _⟩
                · exact absurd (hcd_nat.symm.trans h0) hcd0
                · rw [hcd_nat] at hhdr_cd
                  exact ⟨hcd_S, ((hS_tr cdw.toNat hcd_S).2.2 0 (by omega)).trans (hhdr_cd.trans (show 32 = roleKeyLen "ws+16" by decide))⟩
            have hpre_disj_suf : ∀ a ∈ pre_cd, ∀ b ∈ suf_p, a.1 ≠ b.1 := by
              intro a ha b hb heq
              by_cases hcd0 : cdw.toNat = 0
              · simp [pre_cd, hcd0] at ha
              · simp only [pre_cd, hcd0, ↓reduceIte, List.mem_singleton] at ha; subst ha
                obtain ⟨hne1, hne2, hne3, hne_ad⟩ := hcd_not_bal hcd0
                rw [hsuf_eq_s] at hb
                have hb' := (List.mem_filter.1 hb).1
                rcases List.mem_append.1 hb' with hb_g | hb_rec
                · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb_g
                  rcases hb_g with rfl | rfl | rfl
                  · exact hne1 heq
                  · exact hne2 heq
                  · exact hne3 heq
                · obtain ⟨ad, had, hbad⟩ := List.mem_flatMap.1 hb_rec
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hbad
                  rcases hbad with rfl | rfl
                  · exact (hne_ad ad had).1 heq
                  · exact (hne_ad ad had).2 heq
            rw [hwrs_15_eq]
            unfold RolesOK
            rw [List.append_nil]
            refine ⟨?_, ?_, fun _ h => by cases h⟩
            · intro a ha
              rcases List.mem_append.1 ha with ha_pa | ha_suf
              · rcases List.mem_append.1 ha_pa with ha_pre | ha_add
                · obtain ⟨haS, hkl⟩ := hpre_ok a ha_pre
                  exact ⟨List.mem_append_left _ haS, hkl⟩
                · obtain ⟨haT, hkl⟩ := hadd_ok a ha_add
                  exact ⟨List.mem_append_right _ haT, hkl⟩
              · have ho := hsuf_sub_wrs.subset ha_suf
                obtain ⟨haS, hkl⟩ := hT.2.2.2.2.2.2.2.2.2.2.2.1 a (List.mem_append_left _ ho)
                exact ⟨List.mem_append_left _ haS, ((hS_tr a.1 haS).2.2 0 (by omega)).trans hkl⟩
            · have hpw_pre : pre_cd.Pairwise (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) := by
                by_cases hcd0 : cdw.toNat = 0 <;> simp [pre_cd, hcd0]
              have hpw_suf : suf_p.Pairwise (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) :=
                hT.2.2.2.2.2.2.2.2.2.2.2.2.1.sublist hsuf_sub_wrs
              apply List.pairwise_append.2
              refine ⟨List.pairwise_append.2 ⟨hpw_pre, hadd_pw.imp (fun hne heq => absurd heq hne), ?_⟩, hpw_suf, ?_⟩
              · intro a ha b hb heq
                exact absurd heq (hne_ST a.1 (hpre_ok a ha).1 b.1 (hadd_ok b hb).1)
              · intro a ha b hb heq
                rcases List.mem_append.1 ha with ha_pre | ha_add
                · exact absurd heq (hpre_disj_suf a ha_pre b hb)
                · have hbS := (hT.2.2.2.2.2.2.2.2.2.2.2.1 b (List.mem_append_left _ (hsuf_sub_wrs.subset hb))).1
                  exact absurd heq.symm (hne_ST b.1 hbS a.1 (hadd_ok a ha_add).1)
          -- Step G: `TablesTyped s15 (S ++ T_new)`:
          have hT_15 : TablesTyped s15 (S ++ T_new) := by
            refine ⟨hST_nd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbo_eq_15.2, hroles_15⟩
            · -- `∀ t ∈ S ++ T_new, HtabWF s15 t ∧ ∀ i ∈ htabFootprint s15 t, Allocated s15 i ∧ ∀ j ∈ fixedObjects s15, Disj i j`:
              intro t ht
              rcases List.mem_append.1 ht with htS | htT
              · obtain ⟨hwf_u, hfp_u, _⟩ := hS_tr t htS
                refine ⟨hwf_u, fun i hi => ?_⟩
                rw [hfp_u] at hi
                obtain ⟨hal_i_s, hdisj_fix_s⟩ := (hT.2.1 t htS).2 i hi
                refine ⟨hag_0_15.allocated hal_i_s, fun j hj => ?_⟩
                rcases hfix_15_cls j hj with hj_s | rfl | hj_fresh
                · exact hdisj_fix_s j hj_s
                · exact Or.inr (Or.inl rfl)
                · exact (InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAR0.2 hAR_s15.2 hal_i_s hj_fresh).flip
              · obtain ⟨lo, hi, hwf_idx, hlo_idx, hhi_idx, hfp_idx⟩ := hT_ivls t htT
                refine ⟨hwf_idx, fun i hi_fp => ?_⟩
                obtain ⟨hal_i, hin_i, hd_ws, hd_bs, hd_sk, hd_jr⟩ := hfp_idx i hi_fp
                refine ⟨hal_i, fun j hj => ?_⟩
                rcases hfix_15_exact j hj with hj_s | rfl | rfl | rfl | rfl | rfl
                · rcases hF.1 j hj_s with hj0 | ⟨hal_j, _⟩
                  · exact Or.inr (Or.inl hj0)
                  · exact InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAR0.2 hAR_s15.2 hal_j
                      ⟨by dsimp [Inside] at hin_i ⊢; omega, by dsimp [Inside] at hin_i ⊢; omega⟩
                · exact Or.inr (Or.inl rfl)
                · exact hd_ws
                · exact hd_bs
                · exact hd_sk
                · exact hd_jr
            · -- Pairwise disjointness across `S ++ T_new`:
              intro u hu v hv hne i hi j hj
              rcases List.mem_append.1 hu with huS | huT
              · rcases List.mem_append.1 hv with hvS | hvT
                · rw [(hS_tr u huS).2.1] at hi
                  rw [(hS_tr v hvS).2.1] at hj
                  exact hT.2.2.1 u huS v hvS hne i hi j hj
                · rw [(hS_tr u huS).2.1] at hi
                  obtain ⟨lo_v, hi_v, _, hlo_v, hhi_v, hfp_v⟩ := hT_ivls v hvT
                  have hin_j := (hfp_v j hj).2.1
                  exact (InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAR0.2 hAR_s15.2
                    (((hT.2.1 u huS).2 i hi).1)
                    ⟨by dsimp [Inside] at hin_j ⊢; omega, by dsimp [Inside] at hin_j ⊢; omega⟩).flip
              · rcases List.mem_append.1 hv with hvS | hvT
                · rw [(hS_tr v hvS).2.1] at hj
                  obtain ⟨lo_u, hi_u, _, hlo_u, hhi_u, hfp_u⟩ := hT_ivls u huT
                  have hin_i := (hfp_u i hi).2.1
                  exact InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAR0.2 hAR_s15.2
                    (((hT.2.1 v hvS).2 j hj).1)
                    ⟨by dsimp [Inside] at hin_i ⊢; omega, by dsimp [Inside] at hin_i ⊢; omega⟩
                · exact hT_pw u huT v hvT hne i hi j hj
            · -- `wsTableSlots`:
              intro k hk _
              rw [hws_15]
              simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
              rcases hk with rfl | rfl
              · rw [hmw15_ws16]
                by_cases hcd0 : cdw.toNat = 0
                · exact Or.inl hcd0
                · refine Or.inr (List.mem_append_left _ (hTS _ ?_))
                  dsimp only
                  rw [hcd_nat, if_neg hcd0]; exact List.mem_singleton.2 rfl
              · rw [hmw15_ws32]
                exact Or.inr (List.mem_append_right _ (by simp [T_new]))
            · -- `bsTableSlots`:
              intro k hk _
              rw [hbs_15]
              simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
              rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
              · rw [hmw15_bs8]; exact Or.inr (List.mem_append_right _ (by simp [T_new]))
              · rw [hmw15_bs16]; exact Or.inr (List.mem_append_right _ (by simp [T_new]))
              · rw [hmw15_bs24]; exact Or.inr (List.mem_append_right _ (by simp [T_new]))
              · rw [hmw15_bs32]; exact Or.inr (List.mem_append_right _ (by simp [T_new]))
              · rw [hmw15_bs40]; exact Or.inr (List.mem_append_right _ (by simp [T_new]))
              · rw [hmw15_bs48]; exact Or.inr (List.mem_append_right _ (by simp [T_new]))
              · rw [hmw15_bs72]; exact Or.inr (List.mem_append_right _ (by simp [T_new]))
            · -- `tsTableSlots`:
              intro k _ hnz; exact absurd hts_15 hnz
            · -- `globalTableRoots`:
              intro g hg
              rw [hcore_kept g (by simp only [globalTableRoots, List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl | rfl | rfl <;> decide)]
              rcases hT.2.2.2.2.2.2.1 g hg with h0 | hm
              · exact Or.inl h0
              · exact Or.inr (List.mem_append_left _ hm)
            · -- `HtabValuesIn s15 (bs + 32)`:
              intro _ _ idx hidx
              rw [hbs_15, hmw15_bs32, hcnt_tb32_15] at hidx; omega
            · -- `HtabValuesIn s15 (ts + 32)`:
              intro hnz; exact absurd hts_15 hnz
            · -- `balRecords s15`:
              intro ad had
              obtain ⟨e0, e8, _, hkl, hll⟩ := hbal_eq_15.2 ad had
              rw [hbrec_15] at had
              have had_s := hT.2.2.2.2.2.2.2.2.2.1 ad had
              exact ⟨e0 ▸ List.mem_append_left _ had_s.1, e8 ▸ List.mem_append_left _ had_s.2.1, hkl, hll⟩
          -- Step H: `TriesTypedWith s15 (S ++ T_new) Nd'`:
          have hTr_15 : TriesTypedWith s15 (S ++ T_new) Nd' := by
            refine ⟨hNH_15, ?_, ?_⟩
            · intro o ho
              rw [hne_15_eq] at ho
              rcases hnd'_s1_cls o ho with rfl | ho_old | ho_dw
              · exact ⟨fun _ _ _ _ => Or.inl rfl, fun _ _ => Or.inl rfl⟩
              · -- `o ∈ nodeExtents s Nd`:
                have hal_or_0 : o.2 = 0 ∨ Allocated s o := by
                  unfold nodeExtents at ho_old
                  obtain ⟨n, hn, hno⟩ := List.mem_flatMap.1 ho_old
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hno
                  rcases hno with rfl | rfl
                  · exact Or.inr (hTr.1.1 n hn).2.1
                  · unfold nodePath; split_ifs with hc
                    · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hc.1 with h0 | ⟨_, hal, _⟩
                      · exact absurd h0 hc.2
                      · exact Or.inr hal
                    · exact Or.inl rfl
                refine ⟨fun t ht i hi => ?_, fun j hj => ?_⟩
                · rcases List.mem_append.1 ht with htS | htT
                  · rw [(hS_tr t htS).2.1] at hi
                    exact (hTr.2.1 o ho_old).1 t htS i hi
                  · rcases hal_or_0 with h0 | hal_o
                    · exact Or.inl h0
                    · obtain ⟨lo_t, hi_t, _, hlo_t, hhi_t, hfp_t⟩ := hT_ivls t htT
                      have hin_i := (hfp_t i hi).2.1
                      exact (InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAR0.2 hAR_s15.2 hal_o
                        ⟨by dsimp [Inside] at hin_i ⊢; omega, by dsimp [Inside] at hin_i ⊢; omega⟩).flip
                · rcases hfix_15_cls j hj with hj_s | rfl | hj_fresh
                  · exact (hTr.2.1 o ho_old).2 j hj_s
                  · exact Or.inr (Or.inl rfl)
                  · rcases hal_or_0 with h0 | hal_o
                    · exact Or.inl h0
                    · exact (InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAR0.2 hAR_s15.2 hal_o hj_fresh).flip
              · -- `Inside o (globN s0c "heap_ptr") (globN s1 "heap_ptr")`:
                refine ⟨fun t ht i hi => ?_, fun j hj => ?_⟩
                · rcases List.mem_append.1 ht with htS | htT
                  · rw [(hS_tr t htS).2.1] at hi
                    exact InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAR0.2 hAR_s15.2
                      (((hT.2.1 t htS).2 i hi).1)
                      ⟨by dsimp [Inside] at ho_dw ⊢; omega, by dsimp [Inside] at ho_dw ⊢; omega⟩
                  · obtain ⟨lo_t, _, _, hlo_t, _, hfp_t⟩ := hT_ivls t htT
                    have hin_i := (hfp_t i hi).2.1
                    exact WkBal.disj_fresh_sub ho_dw hin_i hlo_t
                · rcases hfix_15_exact j hj with hj_s | rfl | rfl | rfl | rfl | rfl
                  · rcases hF.1 j hj_s with hj0 | ⟨hal_j, _⟩
                    · exact Or.inr (Or.inl hj0)
                    · exact InitECandidate.Solver.Wave8Contracts.M08.disj_allocated_fresh_heap hAR0.2 hAR_s15.2 hal_j
                        ⟨by dsimp [Inside] at ho_dw ⊢; omega, by dsimp [Inside] at ho_dw ⊢; omega⟩
                  · exact Or.inr (Or.inl rfl)
                  · exact Or.inr (Or.inr (Or.inr (by dsimp [Inside] at ho_dw; omega)))
                  · exact Or.inr (Or.inr (Or.inl (by dsimp [Inside] at ho_dw; omega)))
                  · exact Or.inr (Or.inr (Or.inl (by dsimp [Inside] at ho_dw; omega)))
                  · exact Or.inr (Or.inr (Or.inl (by dsimp [Inside] at ho_dw; omega)))
            · intro _
              rw [hws_15, hmw15_ws24, hmw15_ws32]
              refine ⟨hroot_Nd', fun _ i hi => ?_⟩
              rw [hcnt_tws_15] at hi; omega
          -- Step I: Package `∃ S' Nd', ...`:
          refine ⟨S ++ T_new, Nd', fun t ht => List.mem_append_left _ ht,
            ⟨hT_15, hJ_15, hF_15, hTr_15⟩, ?_, ?_, ?_⟩
          · -- `OwnedGrows s s15 (worldOwned s S Nd) (worldOwned s15 (S ++ T_new) Nd')`:
            intro o ho
            unfold worldOwned at ho
            rcases List.mem_append.1 ho with ho12 | ho_nd
            · rcases List.mem_append.1 ho12 with ho_tab | ho_fix
              · obtain ⟨t, ht, hi⟩ := List.mem_flatMap.1 ho_tab
                rcases List.mem_append.1 ht with htS | htT
                · rw [(hS_tr t htS).2.1] at hi
                  refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
                  unfold worldOwned
                  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨t, htS, hi⟩))
                · obtain ⟨lo_t, hi_t, _, hlo_t, hhi_t, hfp_t⟩ := hT_ivls t htT
                  have hin_o := (hfp_t o hi).2.1
                  exact Or.inr (Or.inr ⟨by dsimp [Inside] at hin_o ⊢; omega, by dsimp [Inside] at hin_o ⊢; omega⟩)
              · rcases hfix_15_cls o ho_fix with ho_s | rfl | ho_fresh
                · refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
                  unfold worldOwned
                  exact List.mem_append_left _ (List.mem_append_right _ ho_s)
                · exact Or.inl rfl
                · exact Or.inr (Or.inr ho_fresh)
            · rw [hne_15_eq] at ho_nd
              rcases hnd'_s1_cls o ho_nd with rfl | ho_old | ho_dw
              · exact Or.inl rfl
              · refine Or.inr (Or.inl ⟨o, ?_, le_rfl, le_rfl⟩)
                unfold worldOwned
                exact List.mem_append_right _ ho_old
              · exact Or.inr (Or.inr ⟨by dsimp [Inside] at ho_dw ⊢; omega, by dsimp [Inside] at ho_dw ⊢; omega⟩)
          · -- `FrameOutside s s15 (worldOwned s S Nd ++ [] ++ [freeGap s]) (heapFree s)`:
            intro x hno hnhf
            exact hfr_s_s15 x (fun j hj => hno j (List.mem_append_right _ hj)) hnhf
          · -- `RetStateInit`:
            intro v hv
            rw [hjcap_15]
            decide

end InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalStateInit
