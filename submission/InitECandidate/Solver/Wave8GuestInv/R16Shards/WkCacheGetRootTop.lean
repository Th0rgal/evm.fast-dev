import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkCacheGetRoot

/-!
# R16 Shard `WkCacheGetRootTop`: Top-Level Proofs of `wk_ws_get_account_optional`, `wk_ws_storage_root_of`, `wk_cache_get_root`

Builds directly on the 0-`sorry` `WorldEff` combinator framework and `worldEff_decode_account_from_leaf`
in `R16Shards.WkCacheGetRoot` to prove:
1. `worldEff_trie_lookup`
2. `worldEff_ws_account_leaf`
3. `worldEff_ws_get_account_optional` & `wk_ws_get_account_optional`
4. `worldEff_ws_storage_root_of` & `wk_ws_storage_root_of`
5. `worldEff_cache_get_root` & `wk_cache_get_root`
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

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
open InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03

private theorem lookup_decode_account_from_leaf_top :
    originalRuntimeCode.lookup (ofString "decode_account_from_leaf") =
      some ([(ofString "p", .one), (ofString "n", .one), (ofString "acct_out", .one)],
        sourceFnBody Guest.Software.guestFn_decode_account_from_leaf, .one) :=
  lookup_of_guestAst_getElem 293 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_account_from_leaf) rfl

private theorem lookup_trie_lookup_top :
    originalRuntimeCode.lookup (ofString "trie_lookup") =
      some ([(ofString "root", .one), (ofString "key_hash32", .one)],
        sourceFnBody Guest.Software.guestFn_trie_lookup, .comb [.one, .one, .one]) :=
  lookup_of_guestAst_getElem 267 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_trie_lookup) rfl

private theorem lookup_ws_account_leaf_top :
    originalRuntimeCode.lookup (ofString "ws_account_leaf") =
      some ([(ofString "addr", .one)],
        sourceFnBody Guest.Software.guestFn_ws_account_leaf, .comb [.one, .one, .one]) :=
  lookup_of_guestAst_getElem 365 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ws_account_leaf) rfl

theorem lookup_ws_get_account_optional_top :
    originalRuntimeCode.lookup (ofString "ws_get_account_optional") =
      some ([(ofString "addr", .one)],
        sourceFnBody Guest.Software.guestFn_ws_get_account_optional, .one) :=
  lookup_of_guestAst_getElem 366 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ws_get_account_optional) rfl

theorem lookup_ws_storage_root_of_top :
    originalRuntimeCode.lookup (ofString "ws_storage_root_of") =
      some ([(ofString "addr", .one)],
        sourceFnBody Guest.Software.guestFn_ws_storage_root_of, .one) :=
  lookup_of_guestAst_getElem 367 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ws_storage_root_of) rfl

theorem lookup_cache_get_root_top :
    originalRuntimeCode.lookup (ofString "cache_get_root") =
      some ([(ofString "cache", .one), (ofString "addr", .one)],
        sourceFnBody Guest.Software.guestFn_cache_get_root, .one) :=
  lookup_of_guestAst_getElem 842 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_cache_get_root) rfl

private theorem ws_no_gb_top : ∀ gs ∈ globalBuffers, ofString gs.1 ∉ wsGw.map ofString := by
  decide

private theorem ws_B_sub_top : ∀ gs ∈ wsBufs, gs ∈ globalBuffers := by
  decide

private theorem ws_B_ok_top : ∀ gs ∈ wsBufs, gs ∈ globalBuffers ∧ gs.1 ∉ typedRecords.map Prod.fst := by
  decide

private theorem ws_core_out_top : ∀ g ∈ coreWorldGlobals, ofString g ∉ wsGw.map ofString := by
  decide

private theorem call0_or_resumes_top {F : Type}
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

private theorem worldEff_call0_funByteEff_top {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    {fname : MlS} {argR : List (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → List Ivl}
    (hf : FunByteEff fname argR)
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
    (call0_byteEff hf cur args Sub h.code h.arena.1 hsub_args hnt (call0_or_resumes_top cur fname args hcr))
    hsub_world

private theorem worldEff_tailCall_ro_top {F : Type} {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (h : WorldEff s cur Rl B gw)
    {fname : MlS} (hf : ReadOnlyFn fname) (args : List (ExpHOL 64))
    (hnt : (evaluateHOLFiniteState cur (.call none fname args)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call none fname args)).1) :
    WorldEff s (evaluateHOLFiniteState cur (.call none fname args)).2 Rl B gw := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  exact worldEff_tailCall_eff h fname args params body ret hlook
    (fun callee vals _ hl hnt_b hres_b => by
      have hentryEq : callEntryStateHOLFinite cur callee =
          { cur with locals := callee, clock := (callEntryStateHOLFinite cur callee).clock } := by
        cases cur; rfl
      have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
          some (body, (callEntryStateHOLFinite cur callee).locals, ret) :=
        ⟨vals, by simpa only [h.code, callEntryStateHOLFinite] using hl⟩
      have hro := hspec (callEntryStateHOLFinite cur callee) h.code
        (guestInv_callEntry cur callee h.arena.1) hex hnt_b hres_b
      exact h.of_readOnly (InitECandidate.Solver.Wave8GuestInv.R13.state_trans_locals_clock hentryEq hro))
    hnt hcr

/-! ## 1. `worldEff_trie_lookup` -/

private theorem call0_none_locals_top {F : Type}
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

private theorem call0_three_word_resumes_top {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname p1 p2 p3 : MlS) (body : ProgHOL 64) (a1 a2 a3 : ExpHOL 64) (w1 w2 w3 : BitVec 64)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (hc : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one), (p3, .one)], body, .one))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [a1, a2, a3] =
      some [.val (.word w1), .val (.word w2), .val (.word w3)])
    (hor : (evaluateHOLFiniteState s (.call (some (none, none)) fname [a1, a2, a3])).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none, none)) fname [a1, a2, a3])).1) :
    Resumes (evaluateHOLFiniteState
      (callEntryStateHOLFinite s
        (((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))).update
          (p3, .val (.word w3))))
      body).1 := by
  have hl := pan_three_word_lookup s.code.lookup fname p1 p2 p3 body w1 w2 w3 h12 h13 h23
    (by rw [hc]; exact hlook)
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

theorem worldEff_trie_lookup {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F)
    (heff_cur : WorldEff s0 cur [] wsBufs wsGw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_trie_lookup)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_trie_lookup)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_trie_lookup)).2 [] wsBufs wsGw := by
  have hlook_ktn : originalRuntimeCode.lookup (ofString "key_to_nibbles") =
      some ([(ofString "key", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_key_to_nibbles, .one) :=
    lookup_of_guestAst_getElem 248 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_key_to_nibbles) rfl
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_trie_lookup,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  have hmns_eq : globN cur "mpt_nib_scratch" = globN s0 "mpt_nib_scratch" :=
    globN_eq_of_lookup (heff_cur.gw_kept (ofString "mpt_nib_scratch") (by decide))
  refine worldEff_seq hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun hnt_k hcr_k =>
      worldEff_call0_funByteEff_top heff_cur funByteEff_key_to_nibbles _
        [bufferRegion s0 ("mpt_nib_scratch", 64)]
        (fun vals hargs i hi hpos => by
          have hor_k := call0_or_resumes_top cur (ofString "key_to_nibbles") _ hcr_k
          have hargs_orig := hargs
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact] at hargs
          rcases hk0 : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
              (.var .local (ofString "key_hash32")) with _ | vk0
          · simp [hk0] at hargs
          · rw [hk0] at hargs
            obtain ⟨wm, hwm_lk⟩ : ∃ wm : BitVec 64,
                cur.globals.lookup (ofString "mpt_nib_scratch") = some (.val (.word wm)) :=
              heff_cur.arena.2.2.2.2.2.2.2.2.2 "mpt_nib_scratch" (by decide)
            simp only [evalHOLExact, toExact, hwm_lk] at hargs
            injection hargs with hargs_eq; subst hargs_eq
            -- Note: if `vk0` is not a word, `lookupCodeHOLFinite` is `none`, making `evaluateHOLFiniteState` = `error`!
            have hvk_word : ∃ wk : BitVec 64, vk0 = .val (.word wk) := by
              rcases vk0 with ⟨⟨wk⟩⟩ | flds | ⟨nm, flds⟩
              · exact ⟨wk, rfl⟩
              · exfalso
                rw [evaluateHOLFiniteState_call, hargs_orig] at hor_k
                dsimp only at hor_k
                have hln : lookupCodeHOLFinite cur.code.lookup (ofString "key_to_nibbles")
                    [.rStruct flds, .val (.word 32#64), .val (.word wm)] = none := by
                  rw [heff_cur.code]
                  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
                  have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "key_to_nibbles")
                      [.rStruct flds, .val (.word 32#64), .val (.word wm)] = none := by
                    simp [lookupCodeHOLExact, hlook_ktn, shapeOfHOLExact, shapeEqHOL]
                  split
                  · rfl
                  · rename_i b' l' r' hsome; rw [hraw] at hsome; cases hsome
                rw [hln] at hor_k
                rcases hor_k with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
              · exfalso
                rw [evaluateHOLFiniteState_call, hargs_orig] at hor_k
                dsimp only at hor_k
                have hln : lookupCodeHOLFinite cur.code.lookup (ofString "key_to_nibbles")
                    [.nStruct nm flds, .val (.word 32#64), .val (.word wm)] = none := by
                  rw [heff_cur.code]
                  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
                  have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "key_to_nibbles")
                      [.nStruct nm flds, .val (.word 32#64), .val (.word wm)] = none := by
                    simp [lookupCodeHOLExact, hlook_ktn, shapeOfHOLExact, shapeEqHOL]
                  split
                  · rfl
                  · rename_i b' l' r' hsome; rw [hraw] at hsome; cases hsome
                rw [hln] at hor_k
                rcases hor_k with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
            obtain ⟨wk, rfl⟩ := hvk_word
            have hres_ktn := call0_three_word_resumes_top cur (ofString "key_to_nibbles")
              (ofString "key") (ofString "n") (ofString "out")
              (sourceFnBody Guest.Software.guestFn_key_to_nibbles) _ _ _ wk 32#64 wm
              (by decide) (by decide) (by decide) heff_cur.code hlook_ktn hargs_orig hor_k
            let cent := callEntryStateHOLFinite cur
              (((HolFiniteMapExact.empty.update (ofString "key", .val (.word wk))).update
                (ofString "n", .val (.word 32#64))).update (ofString "out", .val (.word wm)))
            have hktn_dom := (key_to_nibbles_body_eff cent wk 32#64 wm heff_cur.code
              (guestInv_callEntry cur _ heff_cur.arena.1)
              (by simp [cent, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "out" ≠ ofString "key" by decide, show ofString "n" ≠ ofString "key" by decide])
              (by simp [cent, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "out" ≠ ofString "n" by decide])
              (by simp [cent, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
              hres_ktn).2 (by decide)
            have hsb_pos : 0 < sourceBase := by rw [sourceBase_val]; decide
            have hwm_nat : wm.toNat = globN s0 "mpt_nib_scratch" := by
              rw [← hmns_eq]; simp [globN, hwm_lk]
            have hnz_mns : globN s0 "mpt_nib_scratch" ≠ 0 := by omega
            simp only [List.mem_singleton] at hi
            subst hi
            refine ⟨bufferRegion s0 ("mpt_nib_scratch", 64), List.mem_singleton.2 rfl, ?_, ?_⟩
            · simp [bufferRegion, valWordNat, hwm_nat]
            · simp [bufferRegion, valWordNat, hwm_nat, if_neg hnz_mns])
        (fun iv hiv _ => by
          simp only [List.mem_singleton] at hiv; subst hiv
          exact Or.inr (Or.inl ⟨("mpt_nib_scratch", 64), by decide, le_rfl, le_rfl⟩))
        hnt_k hcr_k)
    (fun mid _ heff_mid hnt_tw hcr_tw =>
      worldEff_tailCall_ro_top heff_mid ro_trie_walk _ hnt_tw hcr_tw)

/-! ## 2. `worldEff_ws_account_leaf` -/

theorem worldEff_ws_account_leaf {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F)
    (hAs0 : ArenaOK s0)
    (heff_cur : WorldEff s0 cur [] wsBufs wsGw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_ws_account_leaf)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_ws_account_leaf)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_ws_account_leaf)).2 [] wsBufs wsGw := by
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_ws_account_leaf,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_heap_mark heff_cur (ofString "mark") hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun hpm m1 _ _ hhpm_al hhpm_lo hhpm_hi hm1_eq heff_m1 hnt1 hcr1 => ?_)
  have hm1_mark : m1.locals.lookup (ofString "mark") = some (.val (.word hpm)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "h") (.const 32#64) hnt1 hcr1
    (fun wh nw m2 hsz_ev _ hm2_loc _ heff_m2 _ _ hwh_lo hwh_end hhp_m2 _ hnt2 hcr2 => ?_)
  have hnw_eq : nw = 32#64 := by
    simp [evalHOLExact] at hsz_ev; exact hsz_ev.symm
  subst hnw_eq
  have hwh_hi : wh.toNat + 32 ≤ heapLimit := by
    change wh.toNat + (32 + 7) / 8 * 8 = globN m2 "heap_ptr" at hwh_end
    omega
  have hm2_mark : m2.locals.lookup (ofString "mark") = some (.val (.word hpm)) := by
    rw [hm2_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_mark, show ofString "h" ≠ ofString "mark" by decide]
  have hm2_h : m2.locals.lookup (ofString "h") = some (.val (.word wh)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hkpad_m2 : globMapN m2.globals "keccak_pad" = globN s0 "keccak_pad" :=
    globN_eq_of_lookup (heff_m2.gw_kept (ofString "keccak_pad") (by decide))
  have hkst_m2 : globMapN m2.globals "keccak_st" = globN s0 "keccak_st" :=
    globN_eq_of_lookup (heff_m2.gw_kept (ofString "keccak_st") (by decide))
  refine worldEff_seq hnt2 hcr2
    (fun hnt_k hcr_k =>
      worldEff_call0_funByteEff_top heff_m2 funByteEff_keccak256 _
        [bufferRegion s0 ("keccak_st", 200), bufferRegion s0 ("keccak_pad", 136), (wh.toNat, 32)]
        (fun vals hargs i hi _ => by
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact] at hargs
          rcases ha0 : m2.locals.lookup (ofString "addr") with _ | va0
          · simp [evalHOLExact, toExact, ha0] at hargs
          · simp only [evalHOLExact, toExact, ha0, hm2_h] at hargs
            injection hargs with hargs_eq; subst hargs_eq
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl | rfl
            · refine ⟨bufferRegion s0 ("keccak_st", 200), List.mem_cons_self, ?_, ?_⟩ <;>
                simp [globBufIvl, bufferRegion, hkst_m2]
            · refine ⟨bufferRegion s0 ("keccak_pad", 136), List.mem_cons_of_mem _ List.mem_cons_self, ?_, ?_⟩ <;>
                simp [globBufIvl, bufferRegion, hkpad_m2]
            · refine ⟨(wh.toNat, 32), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_, ?_⟩ <;>
                simp [valWordNat])
        (fun iv hiv _ => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv
          rcases hiv with rfl | rfl | rfl
          · exact Or.inr (Or.inl ⟨("keccak_st", 200), by decide, le_rfl, le_rfl⟩)
          · exact Or.inr (Or.inl ⟨("keccak_pad", 136), by decide, le_rfl, le_rfl⟩)
          · exact Or.inr (Or.inr (Or.inr ⟨hwh_lo, hwh_hi⟩)))
        hnt_k hcr_k)
    (fun m3 hm3 heff_m3 hnt3 hcr3 => ?_)
  have hm3_loc : m3.locals = m2.locals := by
    have := call0_none_locals_top m2 (ofString "keccak256")
      [.var .local (ofString "addr"), .const 20#64, .var .local (ofString "h")]
      (by rw [hm3])
    rwa [hm3] at this
  have hm3_mark : m3.locals.lookup (ofString "mark") = some (.val (.word hpm)) := by
    rw [hm3_loc]; exact hm2_mark
  refine worldEff_decCall_eff heff_m3 (ofString "r")
    (.comb (InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural [.one, .one, .one]))
    (ofString "trie_lookup") _ _ _ _ lookup_trie_lookup_top
    (fun callee vals _ _ hnt_tl hres_tl =>
      worldEff_trie_lookup s0 (callEntryStateHOLFinite m3 callee)
        (heff_m3.locals_clock _ _) hnt_tl hres_tl)
    (fun callee vals rv cpost _ _ _ _ heff_cp hnt4' hcr4' => ?_)
    hnt3 hcr3
  let m4 := setVarHOLFinite (ofString "r") rv { cpost with locals := m3.locals }
  have hm4_mark : m4.locals.lookup (ofString "mark") = some (.val (.word hpm)) := by
    simp [m4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm3_mark,
      show ofString "r" ≠ ofString "mark" by decide]
  have heff_m4 : WorldEff s0 m4 [] wsBufs wsGw :=
    (heff_cp.locals_clock m3.locals cpost.clock).locals_clock _ _
  refine worldEff_seq hnt4' hcr4'
    (fun hnt_hr _ =>
      (worldEff_call0_heap_release hAs0 heff_m4 (by decide) ws_no_gb_top
        (.var .local (ofString "mark")) hpm
        (by simp [evalHOLExact, toExact, hm4_mark])
        hhpm_lo hhpm_hi hhpm_al hnt_hr).2.choose_spec.2)
    (fun m5 _ heff_m5 _ _ => worldEff_return heff_m5 _)

/-! ## 3. `worldEff_ws_get_account_optional` & `wk_ws_get_account_optional` -/

theorem worldEff_ws_get_account_optional {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F)
    (hAs0 : ArenaOK s0)
    (heff_cur : WorldEff s0 cur [] wsBufs wsGw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).2
      [] wsBufs wsGw := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_ws_get_account_optional,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_eff heff_cur (ofString "leaf")
    (.comb (InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural [.one, .one, .one]))
    (ofString "ws_account_leaf") _ _ _ _ lookup_ws_account_leaf_top
    (fun callee vals _ _ hnt_al hres_al =>
      worldEff_ws_account_leaf s0 (callEntryStateHOLFinite cur callee)
        hAs0 (heff_cur.locals_clock _ _) hnt_al hres_al)
    (fun callee vals rv cpost _ _ _ _ heff_cp hnt1 hcr1 => ?_)
    hnt (Or.inr (Or.inr (Or.inr hres)))
  let m1 := setVarHOLFinite (ofString "leaf") rv { cpost with locals := cur.locals }
  have heff_m1 : WorldEff s0 m1 [] wsBufs wsGw :=
    (heff_cp.locals_clock cur.locals cpost.clock).locals_clock _ _
  refine worldEff_seq hnt1 hcr1
    (fun hnt_i hcr_i =>
      worldEff_ite heff_m1 _ hnt_i hcr_i
        (fun _ _ _ _ _ => worldEff_return heff_m1 _)
        (fun _ _ _ => worldEff_skip heff_m1))
    (fun m2 _ heff_m2 hnt2 hcr2 =>
      worldEff_decCall_alloc heff_m2 (by decide) (ofString "a") (.const 56#64) hnt2 hcr2
        (fun wa nw m3 hsz_ev _ hm3_loc _ heff_m3 _ _ hwa_lo hwa_end hhp_m3 _ hnt3 hcr3 => by
          have hnw_eq : nw = 56#64 := by
            simp [evalHOLExact] at hsz_ev; exact hsz_ev.symm
          subst hnw_eq
          have hwa_hi : wa.toNat + 56 ≤ heapLimit := by
            change wa.toNat + (56 + 7) / 8 * 8 = globN m3 "heap_ptr" at hwa_end
            omega
          have hm3_a : m3.locals.lookup (ofString "a") = some (.val (.word wa)) := by
            rw [hm3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
          refine worldEff_seq hnt3 hcr3
            (fun hnt_d hcr_d =>
              worldEff_call0_eff heff_m3 (ofString "decode_account_from_leaf") _
                _ _ _ lookup_decode_account_from_leaf_top
                (fun dcallee dvals hdargs hdl hnt_db hres_db => by
                  have hdl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "decode_account_from_leaf") dvals =
                      some (sourceFnBody Guest.Software.guestFn_decode_account_from_leaf,
                        (callEntryStateHOLFinite m3 dcallee).locals, .one) := by
                    simpa [heff_m3.code, callEntryStateHOLFinite] using hdl
                  obtain ⟨wp, wn, wa', hdvals_eq, _, _, hwa'_lk⟩ :=
                    lookupCode_three_words (by decide) (by decide) (by decide)
                      lookup_decode_account_from_leaf_top hdl_orig
                  have hwa_eq : wa = wa' := by
                    rw [evalListHOLFinite_eq_toExact] at hdargs
                    simp only [evalListHOLExact] at hdargs
                    rcases hp0 : @evalHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a))
                        (.rfield 1 (.var .local (ofString "leaf"))) with _ | vp0
                    · simp [hp0] at hdargs
                    · rcases hn0 : @evalHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a))
                          (.rfield 2 (.var .local (ofString "leaf"))) with _ | vn0
                      · simp [hp0, hn0] at hdargs
                      · have ha0 : @evalHOLExact 64 F _ m3.toExact (fun a => Classical.propDecidable (m3.memaddrs a))
                            (.var .local (ofString "a")) = some (.val (.word wa)) := by
                          simp [evalHOLExact, toExact, hm3_a]
                        simp only [hp0, hn0, ha0] at hdargs
                        injection hdargs with hdargs'
                        rw [hdvals_eq] at hdargs'
                        injection hdargs' with _ hd1
                        injection hd1 with _ hd2
                        injection hd2 with hd3 _
                        cases hd3
                        rfl
                  subst hwa_eq
                  exact worldEff_decode_account_from_leaf s0 (callEntryStateHOLFinite m3 dcallee) dvals wa
                    (heff_m3.locals_clock _ _) hwa_lo hwa_hi hdl_orig hwa'_lk hnt_db hres_db)
                hnt_d hcr_d)
            (fun m4 _ heff_m4 _ _ => worldEff_return heff_m4 _)))

/-! ## 4. `worldEff_ws_storage_root_of` & `worldEff_cache_get_root` -/

theorem worldEff_ws_storage_root_of {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F)
    (hAs0 : ArenaOK s0)
    (heff_cur : WorldEff s0 cur [] wsBufs wsGw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_ws_storage_root_of)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_ws_storage_root_of)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_ws_storage_root_of)).2
      [] wsBufs wsGw := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_ws_storage_root_of,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_eff heff_cur (ofString "a") .one
    (ofString "ws_get_account_optional") _ _ _ _ lookup_ws_get_account_optional_top
    (fun callee vals _ _ hnt_ao hres_ao =>
      worldEff_ws_get_account_optional s0 (callEntryStateHOLFinite cur callee)
        hAs0 (heff_cur.locals_clock _ _) hnt_ao hres_ao)
    (fun callee vals rv cpost _ _ _ _ heff_cp hnt1 hcr1 => ?_)
    hnt (Or.inr (Or.inr (Or.inr hres)))
  let m1 := setVarHOLFinite (ofString "a") rv { cpost with locals := cur.locals }
  have heff_m1 : WorldEff s0 m1 [] wsBufs wsGw :=
    (heff_cp.locals_clock cur.locals cpost.clock).locals_clock _ _
  refine worldEff_seq hnt1 hcr1
    (fun hnt_i hcr_i =>
      worldEff_ite heff_m1 _ hnt_i hcr_i
        (fun _ _ _ _ _ => worldEff_return heff_m1 _)
        (fun _ _ _ => worldEff_skip heff_m1))
    (fun m2 _ heff_m2 _ _ => worldEff_return heff_m2 _)

theorem worldEff_cache_get_root {F : Type}
    (s0 cur : PanSemStateFiniteExact 64 F)
    (hAs0 : ArenaOK s0)
    (heff_cur : WorldEff s0 cur [] wsBufs wsGw)
    (hnt : (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_cache_get_root)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_cache_get_root)).1) :
    WorldEff s0 (evaluateHOLFiniteState cur (sourceFnBody Guest.Software.guestFn_cache_get_root)).2
      [] wsBufs wsGw := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_cache_get_root,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_ro heff_cur Wave8Contracts.M15.«ro_htab_has»
    (ofString "has") .one _ hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun rv cpost _ hcpost hnt1 hcr1 => ?_)
  let m1 := setVarHOLFinite (ofString "has") rv { cpost with locals := cur.locals }
  have heff_m1 : WorldEff s0 m1 [] wsBufs wsGw :=
    ((heff_cur.of_readOnly hcpost).locals_clock cur.locals cpost.clock).locals_clock _ _
  refine worldEff_seq hnt1 hcr1
    (fun hnt_i hcr_i =>
      worldEff_ite heff_m1 _ hnt_i hcr_i
        (fun _ _ _ _ _ => worldEff_return heff_m1 _)
        (fun _ _ _ => worldEff_skip heff_m1))
    (fun m2 _ heff_m2 hnt2 hcr2 =>
      worldEff_decCall_eff heff_m2 (ofString "r") .one
        (ofString "ws_storage_root_of") _ _ _ _ lookup_ws_storage_root_of_top
        (fun callee vals _ _ hnt_sr hres_sr =>
          worldEff_ws_storage_root_of s0 (callEntryStateHOLFinite m2 callee)
            hAs0 (heff_m2.locals_clock _ _) hnt_sr hres_sr)
        (fun callee vals rv2 cpost2 _ _ _ _ heff_cp2 _ _ =>
          worldEff_return ((heff_cp2.locals_clock m2.locals cpost2.clock).locals_clock _ _) _)
        hnt2 hcr2)

/-! ## 5. Contract Theorems (`wk_ws_get_account_optional`, `wk_ws_storage_root_of`, `wk_cache_get_root`) -/

private abbrev wsContractR : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl :=
  fun s =>
    [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
     (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
     (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)]

private theorem worldStep_of_wsWorldEff {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hWOK : WorldOK s)
    (heff : WorldEff s post [] wsBufs wsGw) :
    WorldStep wsContractR wsGw
      [("ws", [0, 8, 16, 24, 32]),
       ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra s r post := by
  have heff' : WorldEff s post (wsContractR s) wsBufs wsGw :=
    heff.mono (fun _ hiv => by cases hiv) (fun _ h => h) (fun _ h => h)
  exact heff'.to_worldStep_Q hWOK ws_B_ok_top ws_core_out_top (fun _ _ _ _ _ _ _ _ => trivial)

theorem «wk_ws_get_account_optional» :
    WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "ws_get_account_optional") :=
  ⟨_, _, _, lookup_ws_get_account_optional_top, fun s hc hWOK _ hnt hres =>
    worldStep_of_wsWorldEff hWOK
      (worldEff_ws_get_account_optional s s hWOK.1.2 (WorldEff.refl s [] wsBufs wsGw hWOK.1 hc) hnt hres)⟩

theorem «wk_ws_storage_root_of» :
    WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "ws_storage_root_of") :=
  ⟨_, _, _, lookup_ws_storage_root_of_top, fun s hc hWOK _ hnt hres =>
    worldStep_of_wsWorldEff hWOK
      (worldEff_ws_storage_root_of s s hWOK.1.2 (WorldEff.refl s [] wsBufs wsGw hWOK.1 hc) hnt hres)⟩

theorem «wk_cache_get_root» :
    WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "cache_get_root") :=
  ⟨_, _, _, lookup_cache_get_root_top, fun s hc hWOK _ hnt hres =>
    worldStep_of_wsWorldEff hWOK
      (worldEff_cache_get_root s s hWOK.1.2 (WorldEff.refl s [] wsBufs wsGw hWOK.1 hc) hnt hres)⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards
