import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.WkGetAccount
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_stor_lookup

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
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
