import InitECandidate.Solver.Wave8GuestInv.R16Shards.ResolveDecodeStep
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkCacheGetRoot
import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptNibbleKeyWW
import InitECandidate.Solver.Wave8GuestInv.R14Shards.NodeFnHelpers
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.rt_scratch_alloc
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M28.Common

/-!
# Standalone Proofs of `ww__decode_step` & `sp__decode_step`

Proves the write-frame and frame-push contracts for `_decode_step` (`Guest/SoftwareAst.lean:10110`,
AST index 261) in the minimal Wave8 GuestInv cone.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 6400000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.ResolveDecodeStep
open InitECandidate.Solver.Wave8GuestInv.R14Shards
open InitECandidate.Solver.Wave8Contracts.M26 (NS Ret ev updW arenaOK_globals alloc_body_run rt_scratch_alloc)

/-! ## Section 1: Lookups and Conversion between `WorldEff [] wsBufs wsGw` and `StepFrame` -/

private theorem lookup_rlp_decode_fully_ds :
    originalRuntimeCode.lookup (ofString "rlp_decode_fully") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_decode_fully, .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 108 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_decode_fully) rfl

private theorem lookup_rlp_list_count_ds :
    originalRuntimeCode.lookup (ofString "rlp_list_count") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_list_count, .one) :=
  lookup_of_guestAst_getElem 113 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_list_count) rfl

private theorem lookup_rlp_list_to_slices_ds :
    originalRuntimeCode.lookup (ofString "rlp_list_to_slices") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_list_to_slices, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 115 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_list_to_slices) rfl

private theorem lookup_compact_to_nibbles_ds :
    originalRuntimeCode.lookup (ofString "compact_to_nibbles") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_compact_to_nibbles, .comb [.one, .one, .one]) :=
  lookup_of_guestAst_getElem 249 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_compact_to_nibbles) rfl

private theorem lookup__decode_step_ds :
    originalRuntimeCode.lookup (ofString "_decode_step") =
      some ([(ofString "db", .one), (ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn__decode_step, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 261 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__decode_step) rfl

private theorem lookup_three_words_ds {vals : List (ValueHOL 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {body : ProgHOL 64} {ret : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "_decode_step") vals =
      some (body, L, ret)) :
    ∃ wdb wp wn : BitVec 64,
      L.lookup (ofString "db") = some (.val (.word wdb)) ∧
      L.lookup (ofString "p") = some (.val (.word wp)) ∧
      L.lookup (ofString "n") = some (.val (.word wn)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup _ vals _ L _ hl
  simp only [lookupCodeHOLExact, lookup__decode_step_ds] at hx
  rcases vals with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩⟩ <;> try (simp at hx)
  rcases v0 with ⟨⟨w0⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;>
    rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
    simp [shapeOfHOLExact, shapeEqHOL] at hx
  obtain ⟨_, _, h1, _⟩ := hx
  refine ⟨w0, w1, w2, ?_, ?_, ?_⟩ <;>
    (rw [← h1]; simp [
      show ofString "db" ≠ ofString "p" by decide,
      show ofString "db" ≠ ofString "n" by decide,
      show ofString "p" ≠ ofString "db" by decide,
      show ofString "p" ≠ ofString "n" by decide,
      show ofString "n" ≠ ofString "db" by decide,
      show ofString "n" ≠ ofString "p" by decide])

private theorem lookupCode_two_words_any_ds {fname p1 p2 : MlS} {body : ProgHOL 64} {retShape : ShapeHOL}
    {vals : List (ValueHOL 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hne : p1 ≠ p2)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], body, retShape))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, retShape)) :
    ∃ w1 w2 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L retShape hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    refine ⟨w1, w2, rfl, ?_, ?_⟩ <;> (rw [← hL]; simp [hne, Ne.symm hne])
  · simp at hx

private theorem stepFrame_of_worldEff_emptyB {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (heff : WorldEff s post [] [] wsGw) :
    StepFrame s post := by
  refine ⟨heff.arena, heff.hp_lo, heff.fmp_eq, heff.sp_hi, ?_, ?_⟩
  · intro a hkeep hfresh
    by_contra hne
    rcases heff.cell_frame a hne with ⟨_, hm, _⟩ | ⟨_, hm, _⟩ | ⟨_, hch⟩ | ⟨_, hch⟩
    · cases hm
    · cases hm
    · exact hkeep (freeGap s) (List.mem_singleton.mpr rfl) hch
    · exact hfresh hch
  · intro k hk
    exact heff.gw_kept k hk

/-! ## Section 2: `WritesWithin` for Callees of `_decode_step` -/

private theorem hsub_sp_ds : ∀ x ∈ (["scratch_ptr"] : List String), x ∈ ["heap_ptr", "scratch_ptr"] := by
  intro x hx; simp at hx; subst hx; simp

private theorem hsub_hp_ds : ∀ x ∈ (["heap_ptr"] : List String), x ∈ ["heap_ptr", "scratch_ptr"] := by
  intro x hx; simp at hx; subst hx; simp

private theorem hsub_both_ds : ∀ x ∈ (["heap_ptr", "scratch_ptr"] : List String), x ∈ ["heap_ptr", "scratch_ptr"] :=
  fun _ h => h

private theorem ww_rlp_decode_fully :
    WritesWithin (fun _ => []) ["heap_ptr", "scratch_ptr"] (ofString "rlp_decode_fully") := by
  refine ⟨_, _, _, lookup_rlp_decode_fully_ds, ?_⟩
  intro F s hc hAR _ hnt hres
  have hf : StepFlowProg (sourceFnBody Guest.Software.guestFn_rlp_decode_fully) := by
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_decode_fully,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, Option.map]
    exact StepFlowProg.decCall_ww hsub_sp_ds R10Shards.P02.ww_rlp_item _ _ _
      (StepFlowProg.seq
        (StepFlowProg.ite _
          (StepFlowProg.call0_ro InitECandidate.Solver.Wave8GuestInv.R13.ro_rlp_fail _)
          StepFlowProg.skip)
        (StepFlowProg.ret _))
  exact stepFrame_to_ww (hf s hc hAR hnt (Or.inr (Or.inr (Or.inr hres))))

private theorem lookup_rlp_item_total_ds :
    originalRuntimeCode.lookup (ofString "rlp_item_total") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_item_total, .one) :=
  lookup_of_guestAst_getElem 112 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_item_total) rfl

private theorem lookup_rlp_validate_items_ds :
    originalRuntimeCode.lookup (ofString "rlp_validate_items") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_validate_items, .one) :=
  lookup_of_guestAst_getElem 111 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_validate_items) rfl

private theorem lookup__rlp_validate_items_body_ds :
    originalRuntimeCode.lookup (ofString "_rlp_validate_items_body") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn__rlp_validate_items_body, .one) :=
  lookup_of_guestAst_getElem 110 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__rlp_validate_items_body) rfl

private def vibPushProg_ds : ProgHOL 64 :=
  .decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 24]
    (.seq (.store (.var .local (ofString "rec")) (.var .local (ofString "after")))
      (.seq (.store (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end")))
        (.seq (.store (.op .add [.var .local (ofString "rec"), .const 16]) (.var .local (ofString "top")))
          (.seq (.assign .local (ofString "top") (.var .local (ofString "rec")))
            (.seq (.assign .local (ofString "pos") (.var .local (ofString "payload")))
              (.assign .local (ofString "end") (.var .local (ofString "after"))))))))

private theorem worldEff_vibPush_ds {F : Type}
    {s t3 : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s)
    (heff_t3 : WorldEff s t3 [] [] wsGw)
    (w_top w_end w_aft : BitVec 64)
    (ht3_aft : t3.locals.lookup (ofString "after") = some (.val (.word w_aft)))
    (ht3_end : t3.locals.lookup (ofString "end") = some (.val (.word w_end)))
    (ht3_top : t3.locals.lookup (ofString "top") = some (.val (.word w_top)))
    (hnt_push : (evaluateHOLFiniteState t3 vibPushProg_ds).1 ≠ some .timeOut)
    (hcr_push : ContOrRes (evaluateHOLFiniteState t3 vibPushProg_ds).1) :
    WorldEff s (evaluateHOLFiniteState t3 vibPushProg_ds).2 [] [] wsGw := by
  dsimp only [vibPushProg_ds] at hnt_push hcr_push ⊢
  refine worldEff_decCall_scratch_alloc heff_t3 (by decide) _ _ hnt_push hcr_push
    (fun qw nw mid hsz_ev _ hmid_loc _ heff_mid _ hqw_lo hqw_add hsp_le _ _ hnt_ps hcr_ps => ?_)
  have hnw_eq : nw = 24 := by simp [evalHOLExact] at hsz_ev; exact hsz_ev.symm
  subst hnw_eq
  have h24 : ((24 : BitVec 64).toNat + 7) / 8 * 8 = 24 := by decide
  rw [h24] at hqw_add
  have hse_lt : scratchEnd < 2 ^ 64 := by decide
  have hsp_s_hi : globN s "scratch_ptr" ≤ scratchEnd := hAR.2.2.2.2.2.1
  have hqw8 : (qw + 8#64).toNat = qw.toNat + 8 := BitVec.toNat_add_of_lt (by change qw.toNat + 8 < 2 ^ 64; omega)
  have hqw16 : (qw + 16#64).toNat = qw.toNat + 16 := BitVec.toNat_add_of_lt (by change qw.toNat + 16 < 2 ^ 64; omega)
  have hmid_rec : mid.locals.lookup (ofString "rec") = some (.val (.word qw)) := by
    rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hmid_aft : mid.locals.lookup (ofString "after") = some (.val (.word w_aft)) := by
    rw [hmid_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, ht3_aft, show ofString "rec" ≠ ofString "after" by decide]
  have hmid_end : mid.locals.lookup (ofString "end") = some (.val (.word w_end)) := by
    rw [hmid_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, ht3_end, show ofString "rec" ≠ ofString "end" by decide]
  have hmid_top : mid.locals.lookup (ofString "top") = some (.val (.word w_top)) := by
    rw [hmid_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, ht3_top, show ofString "rec" ≠ ofString "top" by decide]
  refine worldEff_seq hnt_ps hcr_ps
    (fun _ _ => worldEff_store_word heff_mid _ _
      (fun v hv => by simp [evalHOLExact, hmid_aft] at hv; exact ⟨_, hv.symm⟩)
      (fun x hx _ => by
        simp [evalHOLExact, hmid_rec] at hx; subst hx
        exact Or.inr (Or.inr (Or.inl ⟨hqw_lo, by omega⟩))))
    (fun u1 hu1 heff_u1 hnt_u1 hcr_u1 => ?_)
  have hu1_loc : u1.locals = mid.locals := by
    have hcf := (evaluate_store_control_frame mid (.var .local (ofString "rec")) (.var .local (ofString "after"))).2.1
    rwa [hu1] at hcf
  refine worldEff_seq hnt_u1 hcr_u1
    (fun _ _ => worldEff_store_word heff_u1 _ _
      (fun v hv => by simp [evalHOLExact, hu1_loc, hmid_end] at hv; exact ⟨_, hv.symm⟩)
      (fun x hx _ => by
        simp [evalHOLExact, evalListHOLExact, hu1_loc, hmid_rec, valueIsWord, valueWord, wordOpHOL, wordOp] at hx
        subst hx
        exact Or.inr (Or.inr (Or.inl ⟨by rw [hqw8]; omega, by rw [hqw8]; omega⟩))))
    (fun u2 hu2 heff_u2 hnt_u2 hcr_u2 => ?_)
  have hu2_loc : u2.locals = mid.locals := by
    have hcf := (evaluate_store_control_frame u1 (.op .add [.var .local (ofString "rec"), .const 8]) (.var .local (ofString "end"))).2.1
    rw [hu2] at hcf; exact hcf.trans hu1_loc
  refine worldEff_seq hnt_u2 hcr_u2
    (fun _ _ => worldEff_store_word heff_u2 _ _
      (fun v hv => by simp [evalHOLExact, hu2_loc, hmid_top] at hv; exact ⟨_, hv.symm⟩)
      (fun x hx _ => by
        simp [evalHOLExact, evalListHOLExact, hu2_loc, hmid_rec, valueIsWord, valueWord, wordOpHOL, wordOp] at hx
        subst hx
        exact Or.inr (Or.inr (Or.inl ⟨by rw [hqw16]; omega, by rw [hqw16]; omega⟩))))
    (fun u3 _ heff_u3 hnt_u3 hcr_u3 =>
      worldEff_seq hnt_u3 hcr_u3
        (fun _ _ => worldEff_assign_local heff_u3 _ _)
        (fun u4 _ heff_u4 hnt_u4 hcr_u4 =>
          worldEff_seq hnt_u4 hcr_u4
            (fun _ _ => worldEff_assign_local heff_u4 _ _)
            (fun u5 _ heff_u5 _ _ => worldEff_assign_local heff_u5 _ _)))

private def vibLoopBody_ds : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "pos")) (.var .local (ofString "end")))
    (.ite (.cmp .equal (.var .local (ofString "top")) (.const 0))
      (.assign .local (ofString "go") (.const 0))
      (.seq
        (.assign .local (ofString "pos") (.load .one (.op .add [.var .local (ofString "top"), .const 0])))
        (.seq
          (.assign .local (ofString "end") (.load .one (.op .add [.var .local (ofString "top"), .const 8])))
          (.assign .local (ofString "top") (.load .one (.op .add [.var .local (ofString "top"), .const 16]))))))
    (.decCall (ofString "h") (.comb [.one, .one, .one]) (ofString "rlp_item_header")
      [.var .local (ofString "pos"), .op .sub [.var .local (ofString "end"), .var .local (ofString "pos")]]
      (.dec (ofString "payload") .one (.op .add [.var .local (ofString "pos"), .rfield 0 (.var .local (ofString "h"))])
        (.dec (ofString "after") .one (.op .add [.var .local (ofString "payload"), .rfield 1 (.var .local (ofString "h"))])
          (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "h"))) (.const 0))
            vibPushProg_ds
            (.assign .local (ofString "pos") (.var .local (ofString "after")))))))

private theorem worldEff_vibLoopBody_ds {F : Type}
    {s t : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s)
    (heff_t : WorldEff s t [] [] wsGw)
    (hinv_t : WordLocals ["top", "pos", "end", "go"] t)
    (hnt_b : (evaluateHOLFiniteState t vibLoopBody_ds).1 ≠ some .timeOut)
    (hcr_b : ContOrRes (evaluateHOLFiniteState t vibLoopBody_ds).1) :
    WorldEff s (evaluateHOLFiniteState t vibLoopBody_ds).2 [] [] wsGw := by
  dsimp only [vibLoopBody_ds] at hnt_b hcr_b ⊢
  refine worldEff_ite heff_t _ hnt_b hcr_b
    (fun _ _ _ hnt_eq hcr_eq =>
      worldEff_ite heff_t _ hnt_eq hcr_eq
        (fun _ _ _ _ _ => worldEff_assign_local heff_t _ _)
        (fun _ hnt_pop hcr_pop =>
          worldEff_seq hnt_pop hcr_pop
            (fun _ _ => worldEff_assign_local heff_t _ _)
            (fun m1 _ heff_m1 hnt_p2 hcr_p2 =>
              worldEff_seq hnt_p2 hcr_p2
                (fun _ _ => worldEff_assign_local heff_m1 _ _)
                (fun m2 _ heff_m2 _ _ => worldEff_assign_local heff_m2 _ _))))
    (fun _ hnt_neq hcr_neq => ?_)
  refine worldEff_decCall_ro heff_t InitECandidate.Solver.Wave8GuestInv.R13.ro_rlp_item_header
    (ofString "h") (.comb [.one, .one, .one]) _ hnt_neq hcr_neq (fun rvh cpost _ hcpost hnt_c1 hcr_c1 => ?_)
  let t1 := setVarHOLFinite (ofString "h") rvh { cpost with locals := t.locals }
  have heff_t1 : WorldEff s t1 [] [] wsGw := (heff_t.of_readOnly hcpost).locals_clock _ _
  obtain ⟨w_top, htop_t⟩ := hinv_t "top" (by simp)
  obtain ⟨w_end, hend_t⟩ := hinv_t "end" (by simp)
  refine worldEff_dec heff_t1 _ _ _ hnt_c1 hcr_c1 (fun vpay _ hsh_pay hnt_c2 hcr_c2 => ?_)
  rcases vpay with ⟨⟨wpay⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_pay
  let t2 := setVarHOLFinite (ofString "payload") (.val (.word wpay)) t1
  have heff_t2 : WorldEff s t2 [] [] wsGw := heff_t1.locals_clock _ _
  refine worldEff_dec heff_t2 _ _ _ hnt_c2 hcr_c2 (fun vaft _ hsh_aft hnt_c3 hcr_c3 => ?_)
  rcases vaft with ⟨⟨waft⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh_aft
  let t3 := setVarHOLFinite (ofString "after") (.val (.word waft)) t2
  have heff_t3 : WorldEff s t3 [] [] wsGw := heff_t2.locals_clock _ _
  refine worldEff_ite heff_t3 _ hnt_c3 hcr_c3
    (fun _ _ _ hnt_push hcr_push =>
      worldEff_vibPush_ds hAR heff_t3 w_top w_end waft
        (by simp [t3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        (by simp [t3, t2, t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hend_t,
              show ofString "after" ≠ ofString "end" by decide,
              show ofString "payload" ≠ ofString "end" by decide,
              show ofString "h" ≠ ofString "end" by decide])
        (by simp [t3, t2, t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, htop_t,
              show ofString "after" ≠ ofString "top" by decide,
              show ofString "payload" ≠ ofString "top" by decide,
              show ofString "h" ≠ ofString "top" by decide])
        hnt_push hcr_push)
    (fun _ _ _ => worldEff_assign_local heff_t3 _ _)

private theorem worldEff__rlp_validate_items_body_ds {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "_rlp_validate_items_body") vals =
      some (sourceFnBody Guest.Software.guestFn__rlp_validate_items_body, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__rlp_validate_items_body)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__rlp_validate_items_body)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__rlp_validate_items_body)).2
      [] [] wsGw := by
  obtain ⟨wp, wlen, rfl, hp_lk, hlen_lk⟩ :=
    lookupCode_two_words_any_ds (by decide) lookup__rlp_validate_items_body_ds hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  have hbody : sourceFnBody Guest.Software.guestFn__rlp_validate_items_body =
      .dec (ofString "top") .one (.const 0)
        (.dec (ofString "pos") .one (.var .local (ofString "p"))
          (.dec (ofString "end") .one (.op .add [.var .local (ofString "p"), .var .local (ofString "len")])
            (.dec (ofString "go") .one (.const 1)
              (.seq
                (.while (.cmp .notEqual (.var .local (ofString "go")) (.const 0)) vibLoopBody_ds)
                (.return (.const 0)))))) := rfl
  rw [hbody] at hnt hres ⊢
  refine worldEff_dec heff0 _ _ _ hnt (Or.inr (Or.inr (Or.inr hres))) (fun vtop hvtop _ hnt1 hcr1 => ?_)
  have hvtop_eq : vtop = .val (.word 0) := by simp [evalHOLExact] at hvtop; exact hvtop.symm
  subst hvtop_eq
  let s1 := setVarHOLFinite (ofString "top") (.val (.word 0)) s
  have heff1 : WorldEff s s1 [] [] wsGw := heff0.locals_clock _ _
  refine worldEff_dec heff1 _ _ _ hnt1 hcr1 (fun vpos hvpos _ hnt2 hcr2 => ?_)
  have hvpos_eq : vpos = .val (.word wp) := by
    simp [s1, setVarHOLFinite, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, hp_lk,
      show ofString "top" ≠ ofString "p" by decide] at hvpos
    exact hvpos.symm
  subst hvpos_eq
  let s2 := setVarHOLFinite (ofString "pos") (.val (.word wp)) s1
  have heff2 : WorldEff s s2 [] [] wsGw := heff1.locals_clock _ _
  refine worldEff_dec heff2 _ _ _ hnt2 hcr2 (fun vend hvend _ hnt3 hcr3 => ?_)
  have hvend_eq : vend = .val (.word (wp + wlen)) := by
    simp [s2, s1, setVarHOLFinite, evalHOLExact, evalListHOLExact, HolFiniteMapExact.lookup_update, FUPDATE,
      hp_lk, hlen_lk, valueIsWord, valueWord, wordOpHOL, wordOp,
      show ofString "pos" ≠ ofString "p" by decide, show ofString "top" ≠ ofString "p" by decide,
      show ofString "pos" ≠ ofString "len" by decide, show ofString "top" ≠ ofString "len" by decide] at hvend
    exact hvend.symm
  subst hvend_eq
  let s3 := setVarHOLFinite (ofString "end") (.val (.word (wp + wlen))) s2
  have heff3 : WorldEff s s3 [] [] wsGw := heff2.locals_clock _ _
  refine worldEff_dec heff3 _ _ _ hnt3 hcr3 (fun vgo hvgo _ hnt4 hcr4 => ?_)
  have hvgo_eq : vgo = .val (.word 1) := by simp [evalHOLExact] at hvgo; exact hvgo.symm
  subst hvgo_eq
  let s4 := setVarHOLFinite (ofString "go") (.val (.word 1)) s3
  have heff4 : WorldEff s s4 [] [] wsGw := heff3.locals_clock _ _
  have hw4 : WordLocals ["top", "pos", "end", "go"] s4 := by
    intro nm hnm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
    rcases hnm with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp [s4, s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "go" ≠ ofString "top" by decide, show ofString "end" ≠ ofString "top" by decide,
        show ofString "pos" ≠ ofString "top" by decide]⟩
    · exact ⟨wp, by simp [s4, s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "go" ≠ ofString "pos" by decide, show ofString "end" ≠ ofString "pos" by decide]⟩
    · exact ⟨wp + wlen, by simp [s4, s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "go" ≠ ofString "end" by decide]⟩
    · exact ⟨1, by simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
  have hws_vib : wsafe vibLoopBody_ds = true := by decide
  refine worldEff_seq hnt4 hcr4
    (fun hnt_w hcr_w =>
      worldEff_while _ (WordLocals ["top", "pos", "end", "go"])
        (fun _ hinv => hinv)
        (fun t heff_t hinv_t hnt_b hcr_b =>
          ⟨worldEff_vibLoopBody_ds hAR heff_t hinv_t hnt_b hcr_b,
           fun hf => wordLocals_flowing hws_vib hinv_t
             (by rcases hf with h | h; exact Or.inl h; exact Or.inr (Or.inr h))⟩)
        s4.clock s4 rfl heff4 hw4 hnt_w hcr_w)
    (fun mid _ heff_mid _ _ => worldEff_return heff_mid _)

private theorem handledCall_raise_keeps_local_ds {F : Type}
    (cur mid : PanSemStateFiniteExact 64 F)
    (eid evar fname : MlS) (preProg : ProgHOL 64) (rexp : ExpHOL 64) (args : List (ExpHOL 64))
    (key : MlS) (hrun : evaluateHOLFiniteState cur
      (.call (some (none, some (eid, evar, .seq preProg (.raise eid rexp)))) fname args) = (none, mid)) :
    mid.locals.lookup key = cur.locals.lookup key := by
  rw [evaluateHOLFiniteState_call] at hrun
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args with _ | vs
  · rw [hargs] at hrun; cases hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hlk : lookupCodeHOLFinite cur.code.lookup fname vs with _ | ⟨b', c', r'⟩
    · rw [hlk] at hrun; cases hrun
    · rw [hlk] at hrun; dsimp only at hrun
      split at hrun
      · cases hrun
      · rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite cur c') b' with ⟨rc, st⟩
        rw [hcal] at hrun
        cases rc with
        | none => cases hrun
        | some r =>
          cases r with
          | returned rv =>
            dsimp only at hrun
            split at hrun
            · injection hrun with _ hm; rw [← hm]
            · cases hrun
          | exception exId exVal =>
            dsimp only at hrun
            split at hrun
            · split at hrun
              · split at hrun
                · rw [evaluateHOLFiniteState_seq_line780] at hrun
                  rcases hpre : evaluateHOLFiniteState _ preProg with ⟨rp, sp0⟩
                  rw [hpre] at hrun
                  cases rp with
                  | none =>
                    dsimp only at hrun
                    rw [evaluateHOLFiniteState_raise] at hrun
                    split at hrun
                    · dsimp only at hrun
                      split at hrun; cases hrun; cases hrun
                    · cases hrun
                  | some r_pre =>
                    dsimp only at hrun
                    cases hrun
                · cases hrun
              · cases hrun
            · cases hrun
          | _ => dsimp only at hrun; (repeat' split at hrun) <;> cases hrun

private theorem empty_B_sub_ds : ∀ gs ∈ ([] : List (String × Nat)), gs ∈ globalBuffers :=
  fun _ h => nomatch h

private theorem ws_no_gb_ds : ∀ gs ∈ globalBuffers, ofString gs.1 ∉ wsGw.map ofString := by
  decide

private theorem worldEff_rlp_validate_items_ds {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_validate_items") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_validate_items, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_validate_items)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_validate_items)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_validate_items)).2
      [] [] wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  have hbody : sourceFnBody Guest.Software.guestFn_rlp_validate_items =
      .decCall (ofString "mark") .one (ofString "scratch_mark") []
        (.dec (ofString "e") .one (.const 0)
          (.seq
            (.call (some (none, some (ofString "RlpErr", ofString "e",
                .seq
                  (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "mark")])
                  (.raise (ofString "RlpErr") (.var .local (ofString "e"))))))
              (ofString "_rlp_validate_items_body") [.var .local (ofString "p"), .var .local (ofString "len")])
            (.seq
              (.call (some (none, none)) (ofString "scratch_release") [.var .local (ofString "mark")])
              (.return (.const 0))))) := rfl
  rw [hbody] at hnt hres ⊢
  refine worldEff_decCall_scratch_mark heff0 _ hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun sp mid1 _ _ hsp_al hsp_lo hsp_hi hmid1_eq heff1 hnt1 hcr1 => ?_)
  refine worldEff_dec heff1 _ _ _ hnt1 hcr1 (fun ve hve _ hnt2 hcr2 => ?_)
  have hve_eq : ve = .val (.word (0 : BitVec 64)) := by simp [evalHOLExact] at hve; exact hve.symm
  subst hve_eq
  let mid2 := setVarHOLFinite (ofString "e") (.val (.word (0 : BitVec 64))) mid1
  have heff2 : WorldEff s mid2 [] [] wsGw := heff1.locals_clock _ _
  have hmark_m2 : mid2.locals.lookup (ofString "mark") = some (.val (.word sp)) := by
    simp [mid2, setVarHOLFinite, hmid1_eq, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "e" ≠ ofString "mark" by decide]
  refine worldEff_seq hnt2 hcr2
    (fun hnt_c hcr_c =>
      worldEff_handledCall heff2 none (ofString "RlpErr") (ofString "e") _
        (ofString "_rlp_validate_items_body") _
        (fun _ _ h => by cases h) (by decide) _ _ _ lookup__rlp_validate_items_body_ds
        (fun callee cvals _ hlc hnt_cb hres_cb =>
          heff2.trans_noBuf
            (WorldEff.from_locals_clock
              (worldEff__rlp_validate_items_body_ds (callEntryStateHOLFinite mid2 callee) cvals
                heff2.code (localsFree_arenaReady mid2 callee _ heff2.arena)
                (by simpa [heff2.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
            empty_B_sub_ds ws_no_gb_ds)
        (fun exVal cpost heff_cp hnt_h hcr_h => by
          let hst := setVarHOLFinite (ofString "e") exVal { cpost with locals := mid2.locals }
          have heff_hst : WorldEff s hst [] [] wsGw := heff_cp.locals_clock _ _
          have hmark_hst : @evalHOLExact 64 F _ hst.toExact (fun a => Classical.propDecidable (hst.memaddrs a))
              (.var .local (ofString "mark")) = some (.val (.word sp)) := by
            simp [hst, setVarHOLFinite, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, hmark_m2,
              show ofString "e" ≠ ofString "mark" by decide]
          exact worldEff_seq hnt_h hcr_h
            (fun hnt_sr _ => (worldEff_call0_scratch_release hAR.2 heff_hst (by decide) _ sp hmark_hst hsp_lo hsp_hi hsp_al hnt_sr).2.choose_spec.2)
            (fun m_sr _ heff_sr _ _ => worldEff_raise heff_sr _ _))
        hnt_c hcr_c)
    (fun mid3 hmid3 heff3 hnt3 hcr3 => ?_)
  have hmark_m3 : mid3.locals.lookup (ofString "mark") = some (.val (.word sp)) := by
    rw [handledCall_raise_keeps_local_ds mid2 mid3 _ _ _ _ _ _ _ hmid3]
    exact hmark_m2
  have hmark_ev3 : @evalHOLExact 64 F _ mid3.toExact (fun a => Classical.propDecidable (mid3.memaddrs a))
      (.var .local (ofString "mark")) = some (.val (.word sp)) := hmark_m3
  exact worldEff_seq hnt3 hcr3
    (fun hnt_sr _ => (worldEff_call0_scratch_release hAR.2 heff3 (by decide) _ sp hmark_ev3 hsp_lo hsp_hi hsp_al hnt_sr).2.choose_spec.2)
    (fun m_sr _ heff_sr _ _ => worldEff_return heff_sr _)

private theorem worldEff_rlp_item_total_ds {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_item_total") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_item_total, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item_total)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item_total)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_item_total)).2
      [] [] wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_decCall_ro heff0 InitECandidate.Solver.Wave8GuestInv.R13.ro_rlp_item_header
    _ _ _ hnt (Or.inr (Or.inr (Or.inr hres))) (fun rvh cpost _ hcpost hnt1 hcr1 => ?_)
  let s1 := setVarHOLFinite (ofString "h") rvh { cpost with locals := s.locals }
  have heff1 : WorldEff s s1 [] [] wsGw := (heff0.of_readOnly hcpost).locals_clock _ _
  refine worldEff_seq hnt1 hcr1
    (fun hnt_i hcr_i =>
      worldEff_ite heff1 _ hnt_i hcr_i
        (fun _ _ _ hnt_c hcr_c =>
          worldEff_call0_eff heff1 (ofString "rlp_validate_items") _ _ _ _ lookup_rlp_validate_items_ds
            (fun callee cvals _ hlc hnt_cb hres_cb =>
              heff1.trans_noBuf
                (WorldEff.from_locals_clock
                  (worldEff_rlp_validate_items_ds (callEntryStateHOLFinite s1 callee) cvals
                    heff1.code (localsFree_arenaReady s1 callee _ heff1.arena)
                    (by simpa [heff1.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                empty_B_sub_ds ws_no_gb_ds)
            hnt_c hcr_c)
        (fun _ _ _ => worldEff_skip heff1))
    (fun mid _ heff_mid _ _ => worldEff_return heff_mid _)

private theorem worldEff_rlp_list_count_ds {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_list_count") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_list_count, s.locals, .one))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).1) :
    WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).2
      [] [] wsGw := by
  have _ := hl
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_list_count,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine worldEff_dec heff0 _ _ _ hnt (Or.inr (Or.inr (Or.inr hres))) (fun vcnt _ _ hnt1 hcr1 => ?_)
  let s1 := setVarHOLFinite (ofString "count") vcnt s
  have heff1 : WorldEff s s1 [] [] wsGw := heff0.locals_clock _ _
  refine worldEff_dec heff1 _ _ _ hnt1 hcr1 (fun voff _ _ hnt2 hcr2 => ?_)
  let s2 := setVarHOLFinite (ofString "off") voff s1
  have heff2 : WorldEff s s2 [] [] wsGw := heff1.locals_clock _ _
  refine worldEff_seq hnt2 hcr2
    (fun hnt_w hcr_w =>
      worldEff_while _ (fun _ => True) (fun _ _ => trivial)
        (fun t heff_t _ hnt_b hcr_b =>
          ⟨worldEff_decCall_eff heff_t (ofString "total") .one (ofString "rlp_item_total") _ _ _ _ lookup_rlp_item_total_ds
            (fun callee cvals _ hlc hnt_cb hres_cb =>
              heff_t.trans_noBuf
                (WorldEff.from_locals_clock
                  (worldEff_rlp_item_total_ds (callEntryStateHOLFinite t callee) cvals
                    heff_t.code (localsFree_arenaReady t callee _ heff_t.arena)
                    (by simpa [heff_t.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
                empty_B_sub_ds ws_no_gb_ds)
            (fun _ _ rv cpost _ _ _ _ heff_cp hnt_k hcr_k =>
              worldEff_seq hnt_k hcr_k
                (fun _ _ => worldEff_assign_local (heff_cp.locals_clock _ _) _ _)
                (fun m2 _ heff_m2 _ _ => worldEff_assign_local heff_m2 _ _))
            hnt_b hcr_b,
           fun _ => trivial⟩)
        s2.clock s2 rfl heff2 trivial hnt_w hcr_w)
    (fun mid _ heff_mid _ _ => worldEff_return heff_mid _)

private def ltsLoopBody_ds : ProgHOL 64 :=
  .decCall (ofString "total") .one (ofString "rlp_item_total_unchecked")
    [.op .add [.var .local (ofString "p"), .var .local (ofString "off")]]
    (.seq
      (.store (.op .add [.var .local (ofString "arr"),
          .panop .mul [.var .local (ofString "i"), .const 16]])
        (.op .add [.var .local (ofString "p"), .var .local (ofString "off")]))
      (.seq
        (.store (.op .add [.var .local (ofString "arr"),
            .panop .mul [.var .local (ofString "i"), .const 16], .const 8])
          (.var .local (ofString "total")))
        (.seq
          (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))))

private def LtsInv_ds {F : Type} (pw wcnt : BitVec 64) (t : PanSemStateFiniteExact 64 F) : Prop :=
  t.locals.lookup (ofString "arr") = some (.val (.word pw)) ∧
  t.locals.lookup (ofString "count") = some (.val (.word wcnt)) ∧
  WordLocals ["p", "off", "i"] t

private theorem eval_assign_flowing_keeps_ds {F : Type}
    (u : PanSemStateFiniteExact 64 F) (nm : MlS) (e : ExpHOL 64) (key : MlS)
    (hk : key ≠ nm)
    (hf : (evaluateHOLFiniteState u (.assign .local nm e)).1 = none ∨
      (evaluateHOLFiniteState u (.assign .local nm e)).1 = some .continue) :
    (evaluateHOLFiniteState u (.assign .local nm e)).2.locals.lookup key = u.locals.lookup key := by
  revert hf
  rw [evaluateHOLFiniteState_assign]
  rcases hv : @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) e with _ | val
  · simp
  · dsimp only
    by_cases hval : isValidValueHOLFinite u .local nm val = true
    · rw [if_pos hval]
      intro _
      simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
    · rw [if_neg hval]; simp

private theorem eval_store_flowing_inv_ds {F : Type}
    (u : PanSemStateFiniteExact 64 F) (d e : ExpHOL 64) {rest : ProgHOL 64}
    (hf : (evaluateHOLFiniteState u (.seq (.store d e) rest)).1 = none ∨
      (evaluateHOLFiniteState u (.seq (.store d e) rest)).1 = some .continue) :
    ∃ u1, evaluateHOLFiniteState u (.store d e) = (none, u1) ∧ u1.locals = u.locals ∧
      ((evaluateHOLFiniteState u1 rest).1 = none ∨ (evaluateHOLFiniteState u1 rest).1 = some .continue) ∧
      (evaluateHOLFiniteState u (.seq (.store d e) rest)).2 = (evaluateHOLFiniteState u1 rest).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at hf ⊢
  rcases hs : evaluateHOLFiniteState u (.store d e) with ⟨r, u1⟩
  rw [hs] at hf
  cases r with
  | none =>
    have hloc : u1.locals = u.locals := by
      have hcf := (evaluate_store_control_frame u d e).2.1
      rwa [hs] at hcf
    exact ⟨u1, rfl, hloc, hf, rfl⟩
  | some r =>
    exfalso
    have hse : r = .error := by
      rw [evaluateHOLFiniteState_store] at hs
      revert hs; repeat' split
      all_goals (intro hs; injection hs with hs1 _; cases hs1 <;> rfl)
    subst hse
    rcases hf with hf | hf <;> simp at hf

private theorem ltsLoopBody_keeps_arr_count_ds {F : Type}
    (t : PanSemStateFiniteExact 64 F) (pw wcnt : BitVec 64)
    (harr : t.locals.lookup (ofString "arr") = some (.val (.word pw)))
    (hcnt : t.locals.lookup (ofString "count") = some (.val (.word wcnt)))
    (hf : (evaluateHOLFiniteState t ltsLoopBody_ds).1 = none ∨
      (evaluateHOLFiniteState t ltsLoopBody_ds).1 = some .continue) :
    (evaluateHOLFiniteState t ltsLoopBody_ds).2.locals.lookup (ofString "arr") = some (.val (.word pw)) ∧
    (evaluateHOLFiniteState t ltsLoopBody_ds).2.locals.lookup (ofString "count") = some (.val (.word wcnt)) := by
  have heq : ∀ key : MlS, key ≠ ofString "total" → key ≠ ofString "off" → key ≠ ofString "i" →
      (evaluateHOLFiniteState t ltsLoopBody_ds).2.locals.lookup key = t.locals.lookup key := by
    intro key hk1 hk2 hk3
    revert hf
    unfold ltsLoopBody_ds
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.op .add [.var .local (ofString "p"), .var .local (ofString "off")]] with _ | vs
    · simp
    · simp only [hargs]
      rcases hlk : lookupCodeHOLFinite t.code.lookup (ofString "rlp_item_total_unchecked") vs with _ | ⟨b', c', r'⟩
      · simp
      · simp only [hlk]
        by_cases hz : t.clock = 0
        · simp [hz]
        · simp only [hz, ↓reduceIte]
          rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite t c') b' with ⟨rc, st⟩
          simp only [hcal]
          rcases rc with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> try simp
          split
          · intro hf
            dsimp only
            rw [resVarEq_lookup_local, if_neg hk1]
            let u0 := setVarHOLFinite (ofString "total") w { st with locals := t.locals }
            have hu0_k : u0.locals.lookup key = t.locals.lookup key := by
              simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk1]
            change (evaluateHOLFiniteState u0 _).1 = _ ∨ (evaluateHOLFiniteState u0 _).1 = _ at hf
            change (evaluateHOLFiniteState u0 _).2.locals.lookup key = t.locals.lookup key
            obtain ⟨u1, _, hu1_loc, hf1, heq1⟩ := eval_store_flowing_inv_ds u0 _ _ hf
            rw [heq1]
            obtain ⟨u2, _, hu2_loc, hf2, heq2⟩ := eval_store_flowing_inv_ds u1 _ _ hf1
            rw [heq2]
            rw [evaluateHOLFiniteState_seq_line780] at hf2 ⊢
            rcases ha1 : evaluateHOLFiniteState u2 (.assign .local (ofString "off")
                (.op .add [.var .local (ofString "off"), .var .local (ofString "total")])) with ⟨ra1, u3⟩
            rw [ha1] at hf2
            cases ra1 with
            | some _ =>
              exfalso
              have hbad : (evaluateHOLFiniteState u2 (.assign .local (ofString "off")
                  (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))).1 ≠ some .continue := by
                rw [evaluateHOLFiniteState_assign]; split <;> [simp; (split <;> simp)]
              rw [ha1] at hbad
              rcases hf2 with hf2 | hf2 <;> [cases hf2; exact hbad hf2]
            | none =>
              have hu3_k : u3.locals.lookup key = u2.locals.lookup key := by
                have := eval_assign_flowing_keeps_ds u2 (ofString "off")
                  (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]) key hk2
                  (by rw [ha1]; exact Or.inl rfl)
                rwa [ha1] at this
              have hu4_k := eval_assign_flowing_keeps_ds u3 (ofString "i")
                (.op .add [.var .local (ofString "i"), .const 1#64]) key hk3 hf2
              dsimp only
              rw [hu4_k, hu3_k, hu2_loc, hu1_loc, hu0_k]
          · simp
  exact ⟨(heq (ofString "arr") (by decide) (by decide) (by decide)).trans harr,
         (heq (ofString "count") (by decide) (by decide) (by decide)).trans hcnt⟩

private theorem worldEff_while_cond_ds {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (cond : ExpHOL 64) {body : ProgHOL 64}
    (Inv : PanSemStateFiniteExact 64 F → Prop)
    (hdec : ∀ t, Inv t → Inv (decClockHOLFinite t))
    (hb : ∀ t (cw : BitVec 64),
      @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word cw)) →
      cw ≠ 0 →
      WorldEff s (decClockHOLFinite t) Rl B gw → Inv (decClockHOLFinite t) →
      (evaluateHOLFiniteState (decClockHOLFinite t) body).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState (decClockHOLFinite t) body).1 →
      WorldEff s (evaluateHOLFiniteState (decClockHOLFinite t) body).2 Rl B gw ∧
      (((evaluateHOLFiniteState (decClockHOLFinite t) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite t) body).1 = some .continue) →
        Inv (evaluateHOLFiniteState (decClockHOLFinite t) body).2)) :
    ∀ (k : Nat) (cur : PanSemStateFiniteExact 64 F), cur.clock = k →
      WorldEff s cur Rl B gw → Inv cur →
      (evaluateHOLFiniteState cur (.while cond body)).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState cur (.while cond body)).1 →
      WorldEff s (evaluateHOLFiniteState cur (.while cond body)).2 Rl B gw := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro cur hclk heff hinv hnt hcr
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt hcr ⊢
    rcases hc : @evalHOLFinite 64 F _ cur (fun a => Classical.propDecidable (cur.memaddrs a)) cond with _ | cv
    · exact heff
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try exact heff
      rw [hc] at hnt hcr; dsimp only at hnt hcr ⊢
      by_cases hw0 : cw = 0
      · subst hw0; simp; exact heff
      · rw [if_pos hw0] at hnt hcr ⊢
        by_cases hk0 : cur.clock = 0
        · rw [if_pos hk0] at hnt; exact absurd rfl hnt
        · rw [if_neg hk0] at hnt hcr ⊢
          have heff_d : WorldEff s (decClockHOLFinite cur) Rl B gw := heff.locals_clock cur.locals (cur.clock - 1)
          have hinv_d : Inv (decClockHOLFinite cur) := hdec cur hinv
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite cur) body
          rcases hbo : evaluateHOLFiniteState (decClockHOLFinite cur) body with ⟨rb, sb⟩
          simp only [hbo] at hnt hcr hrem ⊢
          have hlt : sb.clock < k := by
            change sb.clock ≤ cur.clock - 1 at hrem; omega
          cases rb with
          | none =>
            obtain ⟨heff_b, hinv_b⟩ := hb cur cw hc hw0 heff_d hinv_d
              (by rw [hbo]; simp) (by rw [hbo]; exact Or.inl rfl)
            rw [hbo] at heff_b hinv_b
            exact ih sb.clock hlt sb rfl heff_b (hinv_b (Or.inl rfl)) hnt hcr
          | some r1 =>
            cases r1 with
            | «continue» =>
              obtain ⟨heff_b, hinv_b⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inl rfl)))
              rw [hbo] at heff_b hinv_b
              exact ih sb.clock hlt sb rfl heff_b (hinv_b (Or.inr rfl)) hnt hcr
            | «break» =>
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inl rfl))
              rw [hbo] at heff_b; exact heff_b
            | timeOut => exact absurd rfl hnt
            | returned v =>
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))))
              rw [hbo] at heff_b; exact heff_b
            | exception eid ev =>
              have hres_e : Resumes (some (.exception eid ev)) := by
                rcases hcr with h | h | h | hr <;> [cases h; cases h; cases h; exact hr]
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inr hres_e)))
              rw [hbo] at heff_b; exact heff_b
            | error =>
              rcases hcr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> cases h
            | finalFfi _ =>
              rcases hcr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> cases h

/-! ### `rlp_list_count` Return Bound (`wcnt.toNat ≤ domainBytes`) -/

private def RetOK_ds (Q : ValueHOL 64 → Prop) {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) :
    Prop :=
  ∀ v, (evaluateHOLFiniteState s p).1 = some (.returned v) → Q v

private theorem R_seq_ds {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (ha : RetOK_ds Q s a) (hb : ∀ mid, evaluateHOLFiniteState s a = (none, mid) → RetOK_ds Q mid b) :
    RetOK_ds Q s (.seq a b) := by
  intro v hv
  rw [evaluateHOLFiniteState_seq_line780] at hv
  rcases hr : evaluateHOLFiniteState s a with ⟨r, mid⟩
  rw [hr] at hv
  cases r with
  | none => exact hb mid hr v hv
  | some _ => apply ha v; rw [hr]; simpa using hv

private theorem R_ite_ds {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {yes no : ProgHOL 64}
    (h : ∀ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w)) → (w ≠ 0 → RetOK_ds Q s yes) ∧ (w = 0 → RetOK_ds Q s no)) :
    RetOK_ds Q s (.ite c yes no) := by
  intro v hv
  rw [evaluateHOLFiniteState_ite] at hv
  split at hv
  · rename_i w hw
    split at hv
    · exact (h w hw).2 (by assumption) v hv
    · exact (h w hw).1 (by assumption) v hv
  · simp at hv

private theorem R_dec_ds {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {n : MlS}
    {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (h : ∀ v, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) init =
      some v → shapeEqHOL sh (shapeOfHOLExact v) = true → RetOK_ds Q (setVarHOLFinite n v s) body) :
    RetOK_ds Q s (.dec n sh init body) := by
  intro v hv
  rw [evaluateHOLFiniteState_dec_total] at hv
  dsimp only at hv
  split at hv
  · simp at hv
  · rename_i val hval
    split at hv
    · rename_i hsh; exact h val hval hsh v hv
    · simp at hv

private theorem R_ret_ds {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64}
    (h : ∀ v, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e =
      some v → Q v) :
    RetOK_ds Q s (.return e) := by
  intro v hv
  rw [evaluateHOLFiniteState_return] at hv
  split at hv
  · simp at hv
  · rename_i val hval
    split at hv
    · simp at hv; subst hv; exact h val hval
    · simp at hv

private theorem R_skip_ds {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} :
    RetOK_ds Q s .skip := by
  intro v hv; rw [evaluateHOLFiniteState_skip] at hv; simp at hv

private theorem rlp_fail_noret_ds {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_fail)).1 ≠ some (.returned v) := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_fail =
      .seq (.raise (ofString "RlpErr") (.var .local (ofString "code"))) (.return (.const 0)) := rfl
  have hraise : ∀ w, (evaluateHOLFiniteState s (.raise (ofString "RlpErr") (.var .local (ofString "code")) :
        ProgHOL 64)).1 ≠ some (.returned w) ∧
      (evaluateHOLFiniteState s (.raise (ofString "RlpErr") (.var .local (ofString "code")) :
        ProgHOL 64)).1 ≠ none := by
    intro w
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  rw [hb, evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s (.raise (ofString "RlpErr") (.var .local (ofString "code")) :
    ProgHOL 64) with ⟨r, mid⟩
  rw [hr] at hraise
  cases r with
  | none => exact absurd rfl (hraise v).2
  | some _ => dsimp only; exact (hraise v).1

private theorem lookup_rlp_fail_ds : originalRuntimeCode.lookup (ofString "rlp_fail") =
    some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_rlp_fail, .one) :=
  lookup_of_guestAst_getElem 105 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_fail) rfl

private theorem lookup_rlp_item_header_ds : originalRuntimeCode.lookup (ofString "rlp_item_header") =
    some ([(ofString "p", .one), (ofString "len", .one)],
      sourceFnBody Guest.Software.guestFn_rlp_item_header, .comb [.one, .one, .one]) :=
  lookup_of_guestAst_getElem 109 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_item_header) rfl

private theorem call_noret_ds {F : Type} (s : PanSemStateFiniteExact 64 F) (f : MlS) (args : List (ExpHOL 64))
    (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) f args)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨r, st⟩
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> (repeat' split) <;> simp

private theorem call_fail_nonone_ds {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "rlp_fail") args)).1 ≠ none := by
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · rename_i values _
    split
    · simp
    · rename_i body callee rs hl
      have hb := lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ body _ rs values callee
        (by rw [hcode]; exact lookup_rlp_fail_ds) hl
      subst hb
      split
      · simp
      · have hnr := fun w => rlp_fail_noret_ds (callEntryStateHOLFinite s callee) w
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_rlp_fail) with ⟨r, st⟩
        rw [hrun] at hnr
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> (repeat' split) <;> try simp
        exact absurd rfl (hnr w)

private theorem R_guard_ds {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hcode : s.code = originalRuntimeCode) {c : ExpHOL 64} {args : List (ExpHOL 64)} {rest : ProgHOL 64}
    (h : ∀ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w)) → w = 0 → RetOK_ds Q s rest) :
    RetOK_ds Q s (.seq (.ite c (.call (some (none, none)) (ofString "rlp_fail") args) .skip) rest) := by
  apply R_seq_ds
  · apply R_ite_ds
    intro w _
    exact ⟨fun _ v hv => absurd hv (call_noret_ds s _ args v), fun _ => R_skip_ds⟩
  · intro mid hmid
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · rename_i w hw
      split at hmid
      · rename_i hw0
        rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        obtain ⟨-, rfl⟩ := hmid
        exact h w hw hw0
      · exact absurd (by rw [hmid]) (call_fail_nonone_ds s hcode args)
    · simp at hmid

private theorem R_decCall_ds {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {n : MlS}
    {sh : ShapeHOL} {f : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (h : ∀ (u : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), shapeEqHOL (shapeOfHOLExact v) sh = true →
      u.code = s.code → (∀ k, k ≠ n → u.locals.lookup k = s.locals.lookup k) →
      u.locals.lookup n = some v → RetOK_ds Q u cont) :
    RetOK_ds Q s (.decCall n sh f args cont) := by
  intro v hv
  rw [evaluateHOLFiniteState_decCall_total] at hv
  split at hv
  · simp at hv
  · split at hv
    · simp at hv
    · rename_i body callee rs _
      split at hv
      · simp at hv
      · have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, st⟩
        rw [hrun] at hmeta
        change st.code = s.code at hmeta
        simp only [hrun] at hv
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only at hv <;> try simp at hv
        split at hv
        · rename_i hsh
          try simp only [Bool.and_eq_true] at hsh
          refine h _ w hsh.1 (by simp [setVarHOLFinite, fixClockHOLFinite, hmeta]) ?_ ?_ v hv
          · intro k hk
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        · simp at hv

private theorem R_decCall'_ds {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {n : MlS}
    {sh : ShapeHOL} {f : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (h : ∀ (values : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (rs : ShapeHOL) (v : ValueHOL 64),
      evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address)) args =
        some values →
      lookupCodeHOLFinite s.code.lookup f values = some (body, callee, rs) →
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 = some (.returned v) →
      shapeEqHOL (shapeOfHOLExact v) sh = true →
      ∀ (u : PanSemStateFiniteExact 64 F), u.code = s.code →
        (∀ k, k ≠ n → u.locals.lookup k = s.locals.lookup k) → u.locals.lookup n = some v →
        RetOK_ds Q u cont) :
    RetOK_ds Q s (.decCall n sh f args cont) := by
  intro v hv
  rw [evaluateHOLFiniteState_decCall_total] at hv
  split at hv
  · simp at hv
  · rename_i values hargs
    split at hv
    · simp at hv
    · rename_i body callee rs hl
      split at hv
      · simp at hv
      · have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, st⟩
        rw [hrun] at hmeta
        change st.code = s.code at hmeta
        simp only [hrun] at hv
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only at hv <;> try simp at hv
        split at hv
        · rename_i hsh
          try simp only [Bool.and_eq_true] at hsh
          refine h values body callee rs w hargs hl (by rw [hrun]) hsh.1 _
            (by simp [setVarHOLFinite, fixClockHOLFinite, hmeta]) ?_ ?_ v hv
          · intro k hk
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        · simp at hv

private def abrupt_ds : ProgHOL 64 → Bool
  | .return _ => true
  | .raise _ _ => true
  | .seq _ b => abrupt_ds b
  | .dec _ _ _ b => abrupt_ds b
  | .decCall _ _ _ _ c => abrupt_ds c
  | .ite _ y n => abrupt_ds y && abrupt_ds n
  | _ => false

private theorem abrupt_nonone_ds {F : Type} (p : ProgHOL 64) (h : abrupt_ds p = true) (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ none := by
  match p, h with
  | .return e, _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | .raise n e, _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  | .seq a b, h =>
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr : evaluateHOLFiniteState s a with ⟨r, mid⟩
    cases r with
    | none => exact abrupt_nonone_ds b (by simpa [abrupt_ds] using h) mid
    | some _ => simp
  | .dec n sh e b, h =>
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact abrupt_nonone_ds b (by simpa [abrupt_ds] using h) _
      · simp
  | .decCall n sh f args c, h =>
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · simp
    · split
      · simp
      · rename_i body callee rs _
        split
        · simp
        · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, st⟩
          simp only [hrun]
          rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> try simp
          split
          · exact abrupt_nonone_ds c (by simpa [abrupt_ds] using h) _
          · simp
  | .ite c y n, h =>
    have hh : abrupt_ds y = true ∧ abrupt_ds n = true := by simpa [abrupt_ds] using h
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact abrupt_nonone_ds n hh.2 s
      · exact abrupt_nonone_ds y hh.1 s
    · simp

private theorem R_branch_ds {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {yes rest : ProgHOL 64} (hab : abrupt_ds yes = true)
    (hy : ∀ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w)) → w ≠ 0 → RetOK_ds Q s yes)
    (hr : ∀ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) c =
      some (.val (.word w)) → w = 0 → RetOK_ds Q s rest) :
    RetOK_ds Q s (.seq (.ite c yes .skip) rest) := by
  apply R_seq_ds
  · apply R_ite_ds
    intro w hw
    exact ⟨hy w hw, fun _ => R_skip_ds⟩
  · intro mid hmid
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · rename_i w hw
      split at hmid
      · rename_i hw0
        rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        obtain ⟨-, rfl⟩ := hmid
        exact hr w hw hw0
      · exact absurd (by rw [hmid]) (abrupt_nonone_ds yes hab s)
    · simp at hmid

private theorem R_check2_ds {Q : ValueHOL 64 → Prop} {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hcode : s.code = originalRuntimeCode) {c c' : ExpHOL 64} {args : List (ExpHOL 64)} {rest : ProgHOL 64}
    (hr : RetOK_ds Q s rest) :
    RetOK_ds Q s (.seq (.ite c (.ite c' (.call (some (none, none)) (ofString "rlp_fail") args) .skip) .skip)
      rest) := by
  apply R_seq_ds
  · apply R_ite_ds
    intro w _
    refine ⟨fun _ => ?_, fun _ => R_skip_ds⟩
    apply R_ite_ds
    intro w' _
    exact ⟨fun _ v hv => absurd hv (call_noret_ds s _ args v), fun _ => R_skip_ds⟩
  · intro mid hmid
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · split at hmid
      · rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        obtain ⟨-, rfl⟩ := hmid
        exact hr
      · rw [evaluateHOLFiniteState_ite] at hmid
        split at hmid
        · split at hmid
          · rw [evaluateHOLFiniteState_skip] at hmid
            simp only [Prod.mk.injEq] at hmid
            obtain ⟨-, rfl⟩ := hmid
            exact hr
          · exact absurd (by rw [hmid]) (call_fail_nonone_ds s hcode args)
        · simp at hmid
    · simp at hmid

private def hval_ds (a b c : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word a), .val (.word b), .val (.word c)]

private def HdrQ_ds (L : BitVec 64) (v : ValueHOL 64) : Prop :=
  ∃ a b c : BitVec 64, v = hval_ds a b c ∧ 1 ≤ a.toNat + b.toNat ∧ a.toNat + b.toNat ≤ L.toNat

private theorem loadByte_word_dom_ds {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (.loadByte e) =
      some v) :
    ∃ a B : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e =
        some (.val (.word a)) ∧
      s.memaddrs (panByteAlignHOL (width := 64) a) ∧
      v = .val (.word B) := by
  simp only [evalHOLExact] at hv
  split at hv
  · rename_i a ha
    dsimp only [panMemLoadByteHOL] at hv
    split at hv
    · rename_i hdom
      simp only [Option.map_some, Option.some.injEq] at hv
      exact ⟨a, _, ha, hdom, hv.symm⟩
    · simp at hv
  · simp at hv

private theorem lk_set_ds {F : Type} (st : PanSemStateFiniteExact 64 F) (k : MlS) (x : ValueHOL 64) (k' : MlS)
    (hk : k ≠ k') : (setVarHOLFinite k x st).locals.lookup k' = st.locals.lookup k' := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk]

private theorem lk_set'_ds {F : Type} (st : PanSemStateFiniteExact 64 F) (k : MlS) (x : ValueHOL 64) :
    (setVarHOLFinite k x st).locals.lookup k = some x := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

private theorem toNat_sub_one_ds (L : BitVec 64) (hL : L ≠ 0) : (L - 1#64).toNat = L.toNat - 1 := by
  have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
  rw [BitVec.toNat_sub]; simp; omega

private theorem short_branch_ds {F : Type} (st : PanSemStateFiniteExact 64 F) (hcode : st.code = originalRuntimeCode)
    (L B off flag : BitVec 64) (hL : L ≠ 0)
    (hl : st.locals.lookup (ofString "len") = some (.val (.word L)))
    (hb : st.locals.lookup (ofString "b") = some (.val (.word B))) :
    RetOK_ds (HdrQ_ds L) st
      (.dec (ofString "n") .one (.op .sub [.var .local (ofString "b"), .const off])
        (.seq (.ite (.cmp .lower (.op .sub [.var .local (ofString "len"), .const 1#64])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "rlp_fail") [.const 3#64]) .skip)
          (.return (.rstruct [.const 1#64, .var .local (ofString "n"), .const flag])))) := by
  refine R_dec_ds (fun v hv _ => ?_)
  simp [evalHOLExact, evalListHOLExact, hb, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  refine R_guard_ds (by exact hcode) (fun w hw hw0 => R_ret_ds (fun v hv => ?_))
  have hL1 := toNat_sub_one_ds L hL
  have hne_nlen : ofString "n" ≠ ofString "len" := by decide
  have hN : (B - off).toNat ≤ L.toNat - 1 := by
    simp [evalHOLExact, evalListHOLExact, lk_set_ds, lk_set'_ds, hne_nlen, hl, wordOpHOL, wordOp, valueIsWord,
      valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
    subst hw0
    by_contra hc
    have : L - 1#64 < B - off := by rw [BitVec.lt_def, hL1]; omega
    simp [this] at hw
  simp [evalHOLExact, evalListHOLExact, lk_set_ds, lk_set'_ds] at hv
  subst hv
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  refine ⟨1, B - off, flag, rfl, by simp, ?_⟩
  rw [h1]
  have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
  omega

private theorem long_branch_ds {F : Type} (st : PanSemStateFiniteExact 64 F) (hcode : st.code = originalRuntimeCode)
    (L B off flag : BitVec 64) (hL : L ≠ 0)
    (hl : st.locals.lookup (ofString "len") = some (.val (.word L)))
    (hb : st.locals.lookup (ofString "b") = some (.val (.word B))) :
    RetOK_ds (HdrQ_ds L) st
      (.dec (ofString "ll") .one (.op .sub [.var .local (ofString "b"), .const off])
        (.seq (.ite (.cmp .lower (.op .sub [.var .local (ofString "len"), .const 1#64])
              (.var .local (ofString "ll")))
            (.call (some (none, none)) (ofString "rlp_fail") [.const 3#64]) .skip)
          (.decCall (ofString "n") .one (ofString "rlp_read_length")
            [.op .add [.var .local (ofString "p"), .const 1#64], .var .local (ofString "ll")]
            (.seq (.ite (.cmp .notLower (.const 55#64) (.var .local (ofString "n")))
                (.call (some (none, none)) (ofString "rlp_fail") [.const 5#64]) .skip)
              (.seq (.ite (.cmp .lower (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64],
                    .var .local (ofString "ll")]) (.var .local (ofString "n")))
                  (.call (some (none, none)) (ofString "rlp_fail") [.const 3#64]) .skip)
                (.return (.rstruct [.op .add [.const 1#64, .var .local (ofString "ll")],
                  .var .local (ofString "n"), .const flag]))))))) := by
  refine R_dec_ds (fun v hv _ => ?_)
  simp [evalHOLExact, evalListHOLExact, hb, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  have hL1 := toNat_sub_one_ds L hL
  have hne_ll_len : ofString "ll" ≠ ofString "len" := by decide
  refine R_guard_ds (by exact hcode) (fun w hw hw0 => ?_)
  have hLL : (B - off).toNat ≤ L.toNat - 1 := by
    simp [evalHOLExact, evalListHOLExact, lk_set_ds, lk_set'_ds, hne_ll_len, hl, wordOpHOL, wordOp, valueIsWord,
      valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
    subst hw0
    by_contra hc
    have : L - 1#64 < B - off := by rw [BitVec.lt_def, hL1]; omega
    simp [this] at hw
  refine R_decCall_ds (fun u v hsh hcu hloc hn => ?_)
  have hvw : ∃ N : BitVec 64, v = .val (.word N) := by
    rcases v with ⟨⟨N⟩⟩ | fs | ⟨nm, fs⟩ <;> simp_all [shapeEqHOL, shapeOfHOLExact]
  obtain ⟨N, rfl⟩ := hvw
  have hul : u.locals.lookup (ofString "len") = some (.val (.word L)) := by
    rw [hloc _ (by decide), lk_set_ds _ _ _ _ (by decide)]; exact hl
  have hull : u.locals.lookup (ofString "ll") = some (.val (.word (B - off))) := by
    rw [hloc _ (by decide), lk_set'_ds]
  have hcu' : u.code = originalRuntimeCode := hcu.trans hcode
  refine R_guard_ds hcu' (fun w _ _ => ?_)
  refine R_guard_ds hcu' (fun w hw hw0 => R_ret_ds (fun v hv => ?_))
  have hsub : (L - 1#64 - (B - off)).toNat = L.toNat - 1 - (B - off).toNat := by
    rw [BitVec.toNat_sub, hL1]; have := (B - off).isLt; omega
  have hNle : N.toNat ≤ L.toNat - 1 - (B - off).toNat := by
    simp [evalHOLExact, evalListHOLExact, hul, hull, hn, wordOpHOL, wordOp, valueIsWord,
      valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
    subst hw0
    by_contra hc
    have : L - 1#64 - (B - off) < N := by rw [BitVec.lt_def, hsub]; omega
    simp [this] at hw
  simp [evalHOLExact, evalListHOLExact, hull, hn, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  have hadd : (1#64 + (B - off)).toNat = 1 + (B - off).toNat := by
    rw [BitVec.toNat_add_of_lt (by rw [h1]; have := L.isLt; omega), h1]
  refine ⟨1#64 + (B - off), N, flag, rfl, ?_, ?_⟩
  · rw [hadd]; omega
  · rw [hadd]
    have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
    omega

private theorem hdr_post_dom_ds {F : Type} (e : PanSemStateFiniteExact 64 F)
    (hcode : e.code = originalRuntimeCode) (hP : GuestInv e)
    (P L : BitVec 64)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl : e.locals.lookup (ofString "len") = some (.val (.word L)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState e (sourceFnBody Guest.Software.guestFn_rlp_item_header)).1 =
      some (.returned v)) :
    HdrQ_ds L v ∧ sourceBase ≤ P.toNat ∧ P.toNat < heapEnd := by
  revert v hret
  change RetOK_ds (fun v => HdrQ_ds L v ∧ sourceBase ≤ P.toNat ∧ P.toNat < heapEnd) e
    (sourceFnBody Guest.Software.guestFn_rlp_item_header)
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_header,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine R_guard_ds hcode (fun w hw hw0 => ?_)
  have hL : L ≠ 0 := by
    intro h; subst h; simp [evalHOLExact, hl, Compiler.Encoders.Asm.wordCmpHOL] at hw; subst hw0
    simp at hw
  refine R_dec_ds (fun v hv _ => ?_)
  obtain ⟨P', B, ha, hdom, rfl⟩ := loadByte_word_dom_ds e _ v hv
  simp only [evalHOLExact, PanSemStateFiniteExact.toExact, hp, Option.some.injEq, ValueHOL.val.injEq,
    HolWordLab.word.injEq] at ha
  subst ha
  rw [hP.memaddrs, InitECandidate.Solver.Wave8Contracts.M28.ordinaryDomain_iff] at hdom
  have hhe8 : heapEnd % 8 = 0 := by decide
  have hsb8 : sourceBase % 8 = 0 := by decide
  have hal := panByteAlign_toNat64 P
  have hp_in : sourceBase ≤ P.toNat ∧ P.toNat < heapEnd := ⟨by omega, by omega⟩
  have liftQ : ∀ {st : PanSemStateFiniteExact 64 F} {pr : ProgHOL 64},
      RetOK_ds (HdrQ_ds L) st pr →
      RetOK_ds (fun v => HdrQ_ds L v ∧ sourceBase ≤ P.toNat ∧ P.toNat < heapEnd) st pr :=
    fun h v hv => ⟨h v hv, hp_in⟩
  apply liftQ
  set e1 := setVarHOLFinite (ofString "b") (.val (.word B)) e with he1
  have hb1 : e1.locals.lookup (ofString "b") = some (.val (.word B)) := by
    simp [he1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hl1 : e1.locals.lookup (ofString "len") = some (.val (.word L)) := by
    simp [he1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "b" ≠ ofString "len" by decide, hl]
  have hc1 : e1.code = originalRuntimeCode := hcode
  refine R_branch_ds (by rfl) (fun w _ _ => R_ret_ds (fun v hv => ?_)) (fun w _ _ => ?_)
  · simp [evalHOLExact, evalListHOLExact] at hv
    subst hv
    refine ⟨0, 1, 0, rfl, by simp, ?_⟩
    have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
    simp; omega
  have hL1 := toNat_sub_one_ds L hL
  refine R_branch_ds (by rfl) (fun w _ _ => R_dec_ds (fun v hv _ => ?_)) (fun w _ _ => ?_)
  · simp [evalHOLExact, evalListHOLExact, hb1, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
    subst hv
    set e2 := setVarHOLFinite (ofString "n") (.val (.word (B - 128#64))) e1 with he2
    have hc2 : e2.code = originalRuntimeCode := hcode
    refine R_guard_ds hc2 (fun w hw hw0 => ?_)
    have hN : (B - 128#64).toNat ≤ L.toNat - 1 := by
      simp [evalHOLExact, evalListHOLExact, he2, lk_set_ds, lk_set'_ds,
        show ofString "n" ≠ ofString "len" by decide, hl1, wordOpHOL, wordOp, valueIsWord,
        valueWord, Compiler.Encoders.Asm.wordCmpHOL] at hw
      subst hw0
      by_contra hc
      have : L - 1#64 < B - 128#64 := by rw [BitVec.lt_def, hL1]; omega
      simp [this] at hw
    refine R_check2_ds hc2 (R_ret_ds (fun v hv => ?_))
    simp [evalHOLExact, evalListHOLExact, he2, lk_set_ds, lk_set'_ds] at hv
    subst hv
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    refine ⟨1, B - 128#64, 0, rfl, by simp, ?_⟩
    rw [h1]
    have : L.toNat ≠ 0 := fun h => hL (BitVec.eq_of_toNat_eq (by simpa using h))
    omega
  refine R_branch_ds (by rfl) (fun w _ _ => long_branch_ds e1 hc1 L B 183#64 0#64 hL hl1 hb1) (fun w _ _ => ?_)
  refine R_branch_ds (by rfl) (fun w _ _ => short_branch_ds e1 hc1 L B 192#64 1#64 hL hl1 hb1) (fun w _ _ => ?_)
  exact long_branch_ds e1 hc1 L B 247#64 1#64 hL hl1 hb1

private theorem call_flow_locals_ds {F : Type} (s : PanSemStateFiniteExact 64 F) (f : MlS) (args : List (ExpHOL 64))
    (mid : PanSemStateFiniteExact 64 F)
    (h : evaluateHOLFiniteState s (.call (some (none, none)) f args) = (none, mid)) :
    mid.locals = s.locals ∧ mid.code = s.code := by
  have hmeta := (evaluateHOLFiniteState_metadata s (.call (some (none, none)) f args)).1
  rw [h] at hmeta
  refine ⟨?_, hmeta⟩
  revert h
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨r, st⟩
        rcases r with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
        intro h; rw [← h]

private theorem callee_p_len_ds {fname : MlS} {body0 : ProgHOL 64} {rs0 : ShapeHOL}
    (hlook : originalRuntimeCode.lookup fname =
      some ([(ofString "p", .one), (ofString "len", .one)], body0, rs0))
    (v1 v2 : ValueHOL 64) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (rs : ShapeHOL)
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup fname [v1, v2] =
      some (body, callee, rs)) :
    body = body0 ∧ callee.lookup (ofString "p") = some v1 ∧ callee.lookup (ofString "len") = some v2 := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
  split at hl
  · simp at hl
  · rename_i b cl r heq
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    simp only [lookupCodeHOLExact, hlook] at heq
    split at heq
    · simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      refine ⟨rfl, ?_, by simp⟩
      simp [List.zip, List.foldl, show ofString "p" ≠ ofString "len" by decide]
    · simp at heq

private def TotQDom_ds (P L : BitVec 64) (v : ValueHOL 64) : Prop :=
  ∃ t : BitVec 64, v = .val (.word t) ∧ 1 ≤ t.toNat ∧ t.toNat ≤ L.toNat ∧
    sourceBase ≤ P.toNat ∧ P.toNat < heapEnd

private theorem total_post_dom_ds {F : Type} (e : PanSemStateFiniteExact 64 F)
    (hcode : e.code = originalRuntimeCode) (hP : GuestInv e)
    (P L : BitVec 64)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word P)))
    (hl : e.locals.lookup (ofString "len") = some (.val (.word L))) :
    RetOK_ds (TotQDom_ds P L) e (sourceFnBody Guest.Software.guestFn_rlp_item_total) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_rlp_item_total,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine R_decCall'_ds (fun values body callee rs v hargs hlk hret _ u _ _ hu => ?_)
  simp only [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hp, hl, Option.some.injEq] at hargs
  subst hargs
  rw [hcode] at hlk
  obtain ⟨rfl, hcp, hcl⟩ := callee_p_len_ds lookup_rlp_item_header_ds _ _ body callee rs hlk
  obtain ⟨⟨a, b, c, rfl, h1, h2⟩, hp_lo, hp_hi⟩ :=
    hdr_post_dom_ds (callEntryStateHOLFinite e callee) hcode (guestInv_callEntry e callee hP) P L hcp hcl v hret
  refine R_seq_ds (R_ite_ds (fun w _ => ⟨fun _ v hv => absurd hv (call_noret_ds u _ _ v), fun _ => R_skip_ds⟩))
    (fun mid hmid => ?_)
  have hmid_h : mid.locals.lookup (ofString "h") = some (hval_ds a b c) := by
    rw [evaluateHOLFiniteState_ite] at hmid
    split at hmid
    · split at hmid
      · rw [evaluateHOLFiniteState_skip] at hmid
        simp only [Prod.mk.injEq] at hmid
        rw [← hmid.2]; exact hu
      · rw [(call_flow_locals_ds u _ _ mid hmid).1]; exact hu
    · simp at hmid
  refine R_ret_ds (fun v hv => ?_)
  simp [evalHOLExact, evalListHOLExact, hmid_h, hval_ds, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
  subst hv
  refine ⟨a + b, rfl, ?_, ?_, hp_lo, hp_hi⟩
  · rw [BitVec.toNat_add_of_lt (by have := L.isLt; omega)]; omega
  · rw [BitVec.toNat_add_of_lt (by have := L.isLt; omega)]; omega

private theorem decCall_flow_ds {F : Type} {s : PanSemStateFiniteExact 64 F} {n : MlS} {sh : ShapeHOL} {f : MlS}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hflow : (evaluateHOLFiniteState s (.decCall n sh f args cont)).1 = none) :
    ∃ (values : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (rs : ShapeHOL) (v : ValueHOL 64),
      evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address)) args =
        some values ∧
      lookupCodeHOLFinite s.code.lookup f values = some (body, callee, rs) ∧
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 = some (.returned v) ∧
      ∃ u : PanSemStateFiniteExact 64 F, u.code = s.code ∧
        (∀ k, k ≠ n → u.locals.lookup k = s.locals.lookup k) ∧ u.locals.lookup n = some v ∧
        (evaluateHOLFiniteState u cont).1 = none ∧
        ∀ k, k ≠ n → (evaluateHOLFiniteState s (.decCall n sh f args cont)).2.locals.lookup k =
          (evaluateHOLFiniteState u cont).2.locals.lookup k := by
  revert hflow
  rw [evaluateHOLFiniteState_decCall_total]
  split
  · simp
  rename_i values hargs
  split
  · simp
  rename_i body callee rs hl
  split
  · simp
  have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
  rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, st⟩
  rw [hrun] at hmeta
  change st.code = s.code at hmeta
  simp only [hrun]
  cases r with
  | none => simp
  | some r =>
    cases r with
    | returned w =>
      dsimp only
      split
      · intro hflow
        refine ⟨values, body, callee, rs, w, hargs, hl, by rw [hrun], _,
          by simp [setVarHOLFinite, fixClockHOLFinite, hmeta], ?_, ?_, hflow, ?_⟩
        · intro k hk
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
        · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        · intro k hk
          simp only
          rw [resVarEq_lookup_local, if_neg hk]
      · simp
    | _ => simp

private def countCond_ds : ExpHOL 64 :=
  .cmp .lower (.var .local (ofString "off")) (.var .local (ofString "len"))

private def countBody_ds : ProgHOL 64 :=
  .decCall (ofString "total") .one (ofString "rlp_item_total")
    [.op .add [.var .local (ofString "p"), .var .local (ofString "off")],
      .op .sub [.var .local (ofString "len"), .var .local (ofString "off")]]
    (.seq (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))
      (.assign .local (ofString "count") (.op .add [.var .local (ofString "count"), .const 1])))

private theorem countBody_step_ds {F : Type} (s : PanSemStateFiniteExact 64 F) (P y m c : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hP : GuestInv s)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (hy : s.locals.lookup (ofString "off") = some (.val (.word y)))
    (hm : s.locals.lookup (ofString "len") = some (.val (.word m)))
    (hc : s.locals.lookup (ofString "count") = some (.val (.word c)))
    (hlt : y.toNat < m.toNat)
    (hflow : (evaluateHOLFiniteState s countBody_ds).1 = none) :
    ∃ T : BitVec 64,
      1 ≤ T.toNat ∧ y.toNat + T.toNat ≤ m.toNat ∧
      sourceBase ≤ (P + y).toNat ∧ (P + y).toNat < heapEnd ∧
      (evaluateHOLFiniteState s countBody_ds).2.locals.lookup (ofString "off") = some (.val (.word (y + T))) ∧
      (evaluateHOLFiniteState s countBody_ds).2.locals.lookup (ofString "count") = some (.val (.word (c + 1#64))) ∧
      (evaluateHOLFiniteState s countBody_ds).2.locals.lookup (ofString "p") = some (.val (.word P)) ∧
      (evaluateHOLFiniteState s countBody_ds).2.locals.lookup (ofString "len") = some (.val (.word m)) := by
  unfold countBody_ds at hflow ⊢
  obtain ⟨values, body, callee, rs, v, hargs, hl, hret, u, hcu, hloc, hu, hcont, hfin⟩ := decCall_flow_ds hflow
  simp only [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact, hp, hy, hm,
    wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self,
    ↓reduceIte, List.foldr, add_zero, Option.some.injEq] at hargs
  subst hargs
  rw [hcode] at hl
  obtain ⟨rfl, hcp, hcl⟩ := callee_p_len_ds lookup_rlp_item_total_ds _ _ body callee rs hl
  have hsub : (m - y).toNat = m.toNat - y.toNat := by rw [BitVec.toNat_sub]; omega
  obtain ⟨T, rfl, hT1, hT2, hpy_lo, hpy_hi⟩ :=
    total_post_dom_ds (callEntryStateHOLFinite s callee) hcode (guestInv_callEntry s callee hP)
      (P + y) (m - y) hcp hcl v hret
  rw [hsub] at hT2
  have huoff : u.locals.lookup (ofString "off") = some (.val (.word y)) := by
    rw [hloc _ (by decide)]; exact hy
  have hucnt : u.locals.lookup (ofString "count") = some (.val (.word c)) := by
    rw [hloc _ (by decide)]; exact hc
  have hup : u.locals.lookup (ofString "p") = some (.val (.word P)) := by
    rw [hloc _ (by decide)]; exact hp
  have hulen : u.locals.lookup (ofString "len") = some (.val (.word m)) := by
    rw [hloc _ (by decide)]; exact hm
  have hfirst : evaluateHOLFiniteState u
      (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "total")])) =
      (none, setKvarHOLFinite .local (ofString "off") (.val (.word (y + T))) u) := by
    rw [evaluateHOLFiniteState_assign]
    simp [evalHOLExact, evalListHOLExact, huoff, hu, wordOpHOL, wordOp, valueIsWord, valueWord,
      isValidValueHOLFinite, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL]
  let u1 := setKvarHOLFinite .local (ofString "off") (.val (.word (y + T))) u
  have hu1_cnt : u1.locals.lookup (ofString "count") = some (.val (.word c)) := by
    simp [u1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hucnt,
      show ofString "off" ≠ ofString "count" by decide]
  have hsecond : evaluateHOLFiniteState u1
      (.assign .local (ofString "count") (.op .add [.var .local (ofString "count"), .const 1])) =
      (none, setKvarHOLFinite .local (ofString "count") (.val (.word (c + 1#64))) u1) := by
    rw [evaluateHOLFiniteState_assign]
    simp [evalHOLExact, evalListHOLExact, hu1_cnt, wordOpHOL, wordOp, valueIsWord, valueWord,
      isValidValueHOLFinite, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL]
  refine ⟨T, hT1, by omega, hpy_lo, hpy_hi, ?_, ?_, ?_, ?_⟩
  · rw [hfin (ofString "off") (by decide), evaluateHOLFiniteState_seq_line780, hfirst]; dsimp only
    rw [hsecond]; dsimp only
    simp [u1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "count" ≠ ofString "off" by decide]
  · rw [hfin (ofString "count") (by decide), evaluateHOLFiniteState_seq_line780, hfirst]; dsimp only
    rw [hsecond]; dsimp only
    simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · rw [hfin (ofString "p") (by decide), evaluateHOLFiniteState_seq_line780, hfirst]; dsimp only
    rw [hsecond]; dsimp only
    simp [u1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hup,
      show ofString "count" ≠ ofString "p" by decide, show ofString "off" ≠ ofString "p" by decide]
  · rw [hfin (ofString "len") (by decide), evaluateHOLFiniteState_seq_line780, hfirst]; dsimp only
    rw [hsecond]; dsimp only
    simp [u1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hulen,
      show ofString "count" ≠ ofString "len" by decide, show ofString "off" ≠ ofString "len" by decide]

private def CountRetInv_ds {F : Type} (P m : BitVec 64) (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧ GuestInv s ∧
  ∃ (vis : Finset (Fin domainBytes)) (y c : BitVec 64),
    s.locals.lookup (ofString "p") = some (.val (.word P)) ∧
    s.locals.lookup (ofString "off") = some (.val (.word y)) ∧
    s.locals.lookup (ofString "len") = some (.val (.word m)) ∧
    s.locals.lookup (ofString "count") = some (.val (.word c)) ∧
    c.toNat = vis.card ∧
    ∀ k ∈ vis, ∃ d : BitVec 64, d.toNat < y.toNat ∧
      sourceBase ≤ (P + d).toNat ∧ (P + d).toNat < heapEnd ∧
      k.val = (P + d).toNat - sourceBase

private theorem countBody_no_bc_ds {F : Type} (t : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState t countBody_ds).1 ≠ some .break ∧
    (evaluateHOLFiniteState t countBody_ds).1 ≠ some .continue := by
  unfold countBody_ds
  rw [evaluateHOLFiniteState_decCall_total]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rename_i body callee _ _ _
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨r, st⟩
        simp only [hrun]
        cases r with
        | none => simp
        | some r =>
          cases r with
          | returned w =>
            dsimp only
            split
            · dsimp only
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
              split
              · simp
              · split
                · dsimp only
                  rw [evaluateHOLFiniteState_assign]
                  split <;> [simp; (split <;> simp)]
                · simp
            · simp
          | _ => simp

private theorem while_countRetInv_ds {F : Type} (P m : BitVec 64)
    (k : Nat) (s post : PanSemStateFiniteExact 64 F)
    (hclk : s.clock ≤ k) (hinv : CountRetInv_ds P m s)
    (hrun : evaluateHOLFiniteState s (.while countCond_ds countBody_ds) = (none, post)) :
    CountRetInv_ds P m post := by
  induction k generalizing s with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun <;> [simp at hrun; omega]
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun; exact hinv
    · simp at hrun
  | succ k ih =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · rename_i hnz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) countBody_ds
          have hbc := countBody_no_bc_ds (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) countBody_ds with ⟨r1, mid⟩
          rw [hbr] at hrun rem hbc
          cases r1 with
          | none =>
            obtain ⟨hc_s, hG_s, vis, y, c, hp, hy, hm, hc_cnt, hcard, hvis⟩ := hinv
            have hlt : y.toNat < m.toNat := by
              simp [countCond_ds, evalHOLExact, hy, hm, Compiler.Encoders.Asm.wordCmpHOL] at hcond
              by_contra hge
              have hge' : ¬ (y < m) := by rw [BitVec.lt_def]; omega
              simp [hge'] at hcond
              exact hnz hcond.symm
            let sd := decClockHOLFinite s
            have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG_s
            have hmeta := (evaluateHOLFiniteState_metadata sd countBody_ds).1
            have hG_mid : GuestInv mid := by
              have hg := guestInv_evaluate sd countBody_ds hGd
              rwa [hbr] at hg
            obtain ⟨T, hT1, hyT_le, hpy_lo, hpy_hi, hm_off, hm_cnt, hm_p, hm_len⟩ :=
              countBody_step_ds sd P y m c hc_s hGd hp hy hm hc_cnt hlt (by rw [hbr])
            rw [hbr] at hm_off hm_cnt hm_p hm_len hmeta
            dsimp only at hm_off hm_cnt hm_p hm_len
            change mid.code = s.code at hmeta
            have hk_lt : (P + y).toNat - sourceBase < domainBytes := by
              have eD : domainBytes = heapEnd - sourceBase := rfl; omega
            let k_now : Fin domainBytes := ⟨(P + y).toNat - sourceBase, hk_lt⟩
            have hfresh : k_now ∉ vis := by
              intro hmem
              obtain ⟨d, hd_lt, _, _, hk_eq⟩ := hvis k_now hmem
              have hbv : P + d = P + y := BitVec.eq_of_toNat_eq (by change (P + y).toNat - sourceBase = _ at hk_eq; omega)
              have hdy : d = y := by
                have hsub := congrArg (fun x => -P + x) hbv
                simpa [← BitVec.add_assoc] using hsub
              subst hdy; omega
            have hle_ins : (insert k_now vis).card ≤ domainBytes := by
              simpa using Finset.card_le_univ (insert k_now vis)
            have hcard_ins := Finset.card_insert_of_notMem hfresh
            have hdb_lt : domainBytes < 2 ^ 64 := by decide
            have hc1_nat : (c + 1#64).toNat = c.toNat + 1 :=
              BitVec.toNat_add_of_lt (by change c.toNat + 1 < 2 ^ 64; omega)
            have hyT_nat : (y + T).toNat = y.toNat + T.toNat :=
              BitVec.toNat_add_of_lt (by have := m.isLt; omega)
            have hinv_mid : CountRetInv_ds P m mid := by
              refine ⟨hmeta.trans hc_s, hG_mid, insert k_now vis, y + T, c + 1#64,
                hm_p, hm_off, hm_len, hm_cnt, by omega, ?_⟩
              intro k' hk'
              rcases Finset.mem_insert.mp hk' with rfl | hk'
              · exact ⟨y, by omega, hpy_lo, hpy_hi, rfl⟩
              · obtain ⟨d, hd, h1, h2, h3⟩ := hvis k' hk'
                exact ⟨d, by omega, h1, h2, h3⟩
            exact ih mid (by change mid.clock ≤ s.clock - 1 at rem; omega) hinv_mid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl hbc.2
            | «break» => exact absurd rfl hbc.1
            | _ => simp at hrun
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun; exact hinv
    · simp at hrun

private theorem countBody_no_return_ds {F : Type} (st : PanSemStateFiniteExact 64 F) (rv : ValueHOL 64) :
    (evaluateHOLFiniteState st countBody_ds).1 ≠ some (.returned rv) := by
  unfold countBody_ds
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
      [.op .add [.var .local (ofString "p"), .var .local (ofString "off")],
       .op .sub [.var .local (ofString "len"), .var .local (ofString "off")]] with _ | vs
  · simp
  · simp only [hargs]
    rcases hlk : lookupCodeHOLFinite st.code.lookup (ofString "rlp_item_total") vs with _ | ⟨b', c', r'⟩
    · simp
    · simp only [hlk]
      by_cases hz : st.clock = 0
      · simp [hz]
      · simp only [hz, ↓reduceIte]
        rcases hcal : evaluateHOLFiniteState (callEntryStateHOLFinite st c') b' with ⟨rc, cst⟩
        simp only [hcal]
        rcases rc with _ | (_ | _ | _ | _ | w | _ | _) <;> dsimp only <;> try simp
        split
        · dsimp only
          let u0 := setVarHOLFinite (ofString "total") w { cst with locals := st.locals }
          change (evaluateHOLFiniteState u0 _).1 ≠ some (.returned rv)
          rw [evaluateHOLFiniteState_seq_line780]
          have ha1 : ∀ x : Option (PanSemResultExact 64),
              (evaluateHOLFiniteState u0 (.assign .local (ofString "off")
                (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]))).1 = x →
              x = none ∨ x = some .error := by
            intro x hx; rw [← hx, evaluateHOLFiniteState_assign]
            rcases @evalHOLExact 64 F _ u0.toExact (fun a => Classical.propDecidable (u0.memaddrs a))
                (.op .add [.var .local (ofString "off"), .var .local (ofString "total")]) with _ | v1
            · exact Or.inr rfl
            · dsimp only
              by_cases hv : isValidValueHOLFinite u0 .local (ofString "off") v1 = true
              · rw [if_pos hv]; exact Or.inl rfl
              · rw [if_neg hv]; exact Or.inr rfl
          rcases h1 : evaluateHOLFiniteState u0 (.assign .local (ofString "off")
              (.op .add [.var .local (ofString "off"), .var .local (ofString "total")])) with ⟨r1, u1⟩
          rcases ha1 r1 (by rw [h1]) with rfl | rfl
          · dsimp only
            rw [evaluateHOLFiniteState_assign]
            rcases @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
                (.op .add [.var .local (ofString "count"), .const 1]) with _ | v2
            · simp
            · dsimp only
              by_cases hv2 : isValidValueHOLFinite u1 .local (ofString "count") v2 = true
              · rw [if_pos hv2]; simp
              · rw [if_neg hv2]; simp
          · simp
        · simp

private theorem while_count_no_return_ds {F : Type} (rv : ValueHOL 64) :
    ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock ≤ k →
      (evaluateHOLFiniteState st (.while countCond_ds countBody_ds)).1 ≠ some (.returned rv) := by
  intro k
  induction k with
  | zero =>
    intro st hck; rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) countCond_ds with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases hw0 : cw = 0#64
      · subst hw0; simp
      · rw [if_neg hw0]
        have hk0 : st.clock = 0 := by omega
        rw [if_pos hk0]; simp
  | succ k ih =>
    intro st hck; rw [evaluateHOLFiniteState_while_fixClockRewrite]
    rcases hc : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a)) countCond_ds with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases hw0 : cw = 0#64
      · subst hw0; simp
      · rw [if_neg hw0]
        by_cases hk0 : st.clock = 0
        · rw [if_pos hk0]; simp
        · rw [if_neg hk0]
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) countBody_ds
          have hb_nr := countBody_no_return_ds (decClockHOLFinite st) rv
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) countBody_ds with ⟨r1, m1⟩
          simp only [hbr] at rem hb_nr ⊢
          cases r1 with
          | none => exact ih m1 (by change m1.clock ≤ st.clock - 1 at rem; omega)
          | some r1 =>
            cases r1 with
            | «continue» => exact ih m1 (by change m1.clock ≤ st.clock - 1 at rem; omega)
            | «break» => simp
            | returned v' =>
              intro heq; injection heq with heq'; injection heq' with heq''; subst heq''
              exact hb_nr rfl
            | _ => simp

private theorem rlp_list_count_ret_bound_ds {F : Type}
    (s cpost : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64)) (rv : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_list_count") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_list_count, s.locals, .one))
    (hret : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count) =
      (some (.returned rv), cpost)) :
    ∃ wcnt : BitVec 64, rv = .val (.word wcnt) ∧ wcnt.toNat ≤ domainBytes := by
  obtain ⟨P, m, rfl, hp, hm⟩ := lookupCode_two_words_any_ds (by decide) lookup_rlp_list_count_ds hl
  have hbody : sourceFnBody Guest.Software.guestFn_rlp_list_count =
      .dec (ofString "count") .one (.const 0)
        (.dec (ofString "off") .one (.const 0)
          (.seq (.while countCond_ds countBody_ds)
            (.return (.var .local (ofString "count"))))) := rfl
  have hret1 : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_count)).1 =
      some (.returned rv) := by rw [hret]
  clear hret
  rw [hbody] at hret1
  revert rv hret1
  change RetOK_ds (fun rv => ∃ wcnt : BitVec 64, rv = .val (.word wcnt) ∧ wcnt.toNat ≤ domainBytes) s _
  refine R_dec_ds (fun vcnt hvcnt _ => ?_)
  have hvcnt_eq : vcnt = .val (.word 0) := by simp [evalHOLExact] at hvcnt; exact hvcnt.symm
  subst hvcnt_eq
  refine R_dec_ds (fun voff hvoff _ => ?_)
  have hvoff_eq : voff = .val (.word 0) := by simp [evalHOLExact] at hvoff; exact hvoff.symm
  subst hvoff_eq
  let s2 := setVarHOLFinite (ofString "off") (.val (.word 0))
    (setVarHOLFinite (ofString "count") (.val (.word 0)) s)
  have hinv2 : CountRetInv_ds P m s2 := by
    refine ⟨hc, guestInv_setVar _ _ _ (guestInv_setVar _ _ _ hG), ∅, 0, 0, ?_, ?_, ?_, ?_, by simp, by simp⟩
    · simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp,
        show ofString "off" ≠ ofString "p" by decide, show ofString "count" ≠ ofString "p" by decide]
    · simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm,
        show ofString "off" ≠ ofString "len" by decide, show ofString "count" ≠ ofString "len" by decide]
    · simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "off" ≠ ofString "count" by decide]
  refine R_seq_ds ?_ (fun mid hmid => ?_)
  · intro rv hwhile_ret
    exact absurd hwhile_ret (while_count_no_return_ds rv s2.clock s2 le_rfl)
  · obtain ⟨_, _, vis, _, c, _, _, _, hm_cnt, hcard, _⟩ := while_countRetInv_ds P m s2.clock s2 mid le_rfl hinv2 hmid
    refine R_ret_ds (fun v hv => ?_)
    simp [evalHOLExact, hm_cnt] at hv; subst hv
    have hle : vis.card ≤ domainBytes := by simpa using Finset.card_le_univ vis
    exact ⟨c, rfl, by omega⟩

private theorem shape_one_word_ds {v : ValueHOL 64}
    (h : shapeEqHOL (shapeOfHOLExact v) .one = true) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  rcases v with ⟨⟨w⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at h
  exact ⟨w, rfl⟩

private theorem ww_rlp_list_to_slices :
    WritesWithin (fun _ => []) ["heap_ptr", "scratch_ptr"] (ofString "rlp_list_to_slices") := by
  refine ⟨_, _, _, lookup_rlp_list_to_slices_ds, ?_⟩
  intro F s hc hAR ⟨vals, hvals⟩ hnt hres
  obtain ⟨wp, wlen, rfl, hp_lk, _⟩ := lookupCode_two_words_any_ds (by decide) lookup_rlp_list_to_slices_ds hvals
  suffices heff_fin : WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_to_slices)).2
      [] [] wsGw from
    stepFrame_to_ww (stepFrame_of_worldEff_emptyB heff_fin)
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  have hbody : sourceFnBody Guest.Software.guestFn_rlp_list_to_slices =
      .decCall (ofString "count") .one (ofString "rlp_list_count")
        [.var .local (ofString "p"), .var .local (ofString "len")]
        (.decCall (ofString "arr") .one (ofString "alloc")
          [.panop .mul [.var .local (ofString "count"), .const 16]]
          (.dec (ofString "i") .one (.const 0)
            (.dec (ofString "off") .one (.const 0)
              (.seq
                (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "count")))
                  ltsLoopBody_ds)
                (.return (.rstruct [.var .local (ofString "arr"), .var .local (ofString "count")])))))) := rfl
  rw [hbody] at hnt hres ⊢
  refine worldEff_decCall_eff heff0 (ofString "count") .one (ofString "rlp_list_count") _ _ _ _ lookup_rlp_list_count_ds
    (fun callee cvals _ hlc hnt_cb hres_cb =>
      heff0.trans_noBuf
        (WorldEff.from_locals_clock
          (worldEff_rlp_list_count_ds (callEntryStateHOLFinite s callee) cvals
            heff0.code (localsFree_arenaReady s callee _ heff0.arena)
            (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hnt_cb hres_cb))
        empty_B_sub_ds ws_no_gb_ds)
    (fun callee cvals rv cpost _ hlc hrun_c _ heff_cp hnt_k1 hcr_k1 => ?_)
    hnt (Or.inr (Or.inr (Or.inr hres)))
  obtain ⟨wcnt, rfl, hwcnt_le⟩ :=
    rlp_list_count_ret_bound_ds (callEntryStateHOLFinite s callee) cpost cvals rv
      heff0.code (guestInv_callEntry s callee heff0.arena.1)
      (by simpa [heff0.code, callEntryStateHOLFinite] using hlc) hrun_c
  let m1 := setVarHOLFinite (ofString "count") (.val (.word wcnt)) { cpost with locals := s.locals }
  have heff_m1 : WorldEff s m1 [] [] wsGw := heff_cp.locals_clock _ _
  have hm1_cnt : m1.locals.lookup (ofString "count") = some (.val (.word wcnt)) := by
    simp [m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hm1_p : m1.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    simp [m1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_lk,
      show ofString "count" ≠ ofString "p" by decide]
  refine worldEff_decCall_alloc heff_m1 (by decide) (ofString "arr") _ hnt_k1 hcr_k1
    (fun pw nw m2 hsz_ev _ hm2_loc _ heff_m2 _ _ hpw_lo_s hpw_add hhp_m2_hi _ hnt_k2 hcr_k2 => ?_)
  have hnw_eq : nw = wcnt * 16#64 := by
    simp [evalHOLExact, evalListHOLExact, hm1_cnt, panOpHOL, valueIsWord, valueWord] at hsz_ev
    exact hsz_ev.symm
  subst hnw_eq
  have halloc_hi : pw.toNat + ((wcnt * 16#64).toNat + 7) / 8 * 8 ≤ heapLimit := by omega
  refine worldEff_dec heff_m2 _ _ _ hnt_k2 hcr_k2 (fun vi hvi _ hnt_k3 hcr_k3 => ?_)
  have hvi_eq : vi = .val (.word 0) := by simp [evalHOLExact] at hvi; exact hvi.symm
  subst hvi_eq
  let m3 := setVarHOLFinite (ofString "i") (.val (.word 0)) m2
  have heff_m3 : WorldEff s m3 [] [] wsGw := heff_m2.locals_clock _ _
  refine worldEff_dec heff_m3 _ _ _ hnt_k3 hcr_k3 (fun voff hvoff _ hnt_k4 hcr_k4 => ?_)
  have hvoff_eq : voff = .val (.word 0) := by simp [evalHOLExact] at hvoff; exact hvoff.symm
  subst hvoff_eq
  let m4 := setVarHOLFinite (ofString "off") (.val (.word 0)) m3
  have heff_m4 : WorldEff s m4 [] [] wsGw := heff_m3.locals_clock _ _
  have hinv_m4 : LtsInv_ds pw wcnt m4 := by
    refine ⟨?_, ?_, ?_⟩
    · simp [m4, m3, setVarHOLFinite, hm2_loc, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "off" ≠ ofString "arr" by decide, show ofString "i" ≠ ofString "arr" by decide]
    · simp [m4, m3, setVarHOLFinite, hm2_loc, hm1_cnt, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "off" ≠ ofString "count" by decide, show ofString "i" ≠ ofString "count" by decide,
        show ofString "arr" ≠ ofString "count" by decide]
    · intro nm hnm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hnm
      rcases hnm with rfl | rfl | rfl
      · exact ⟨wp, by simp [m4, m3, setVarHOLFinite, hm2_loc, hm1_p, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "off" ≠ ofString "p" by decide, show ofString "i" ≠ ofString "p" by decide,
          show ofString "arr" ≠ ofString "p" by decide]⟩
      · exact ⟨0, by simp [m4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
      · exact ⟨0, by simp [m4, m3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "off" ≠ ofString "i" by decide]⟩
  have hws_lts : wsafe ltsLoopBody_ds = true := by decide
  refine worldEff_seq hnt_k4 hcr_k4
    (fun hnt_w hcr_w => ?_)
    (fun mid _ heff_mid _ _ => worldEff_return heff_mid _)
  -- Distinguish whether `wcnt * 16 < 2^64` or `2^64 ≤ wcnt * 16`!
  by_cases hcnt_ov : wcnt.toNat * 16 < 2 ^ 64
  · refine worldEff_while_cond_ds _ (LtsInv_ds pw wcnt)
      (fun _ hinv => hinv)
      (fun t0 cw hcond hnz heff_t hinv_t hnt_b hcr_b => ?_)
      m4.clock m4 rfl heff_m4 hinv_m4 hnt_w hcr_w
    set t := decClockHOLFinite t0
    obtain ⟨ht_arr, ht_cnt, ht_wloc⟩ := hinv_t
    obtain ⟨wp_t, htp⟩ := ht_wloc "p" (by simp)
    obtain ⟨woff_t, htoff⟩ := ht_wloc "off" (by simp)
    obtain ⟨wi_t, hti⟩ := ht_wloc "i" (by simp)
    have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word wi_t)) := hti
    have ht0_cnt : t0.locals.lookup (ofString "count") = some (.val (.word wcnt)) := ht_cnt
    have hlt_i : wi_t < wcnt := by
      rw [evalHOLFinite_eq_toExact] at hcond
      simp [evalHOLExact, ht0_i, ht0_cnt, Compiler.Encoders.Asm.wordCmpHOL] at hcond
      by_contra hge
      simp [hge] at hcond
      exact hnz hcond.symm
    have hhl_lt : heapLimit < 2 ^ 64 := by decide
    have hlt_nat : wi_t.toNat < wcnt.toNat := BitVec.lt_def.mp hlt_i
    have hcnt16 : (wcnt * 16#64).toNat = wcnt.toNat * 16 :=
      BitVec.toNat_mul_of_lt (by change wcnt.toNat * 16 < 2 ^ 64; exact hcnt_ov)
    have hwi16 : (wi_t * 16#64).toNat = wi_t.toNat * 16 :=
      BitVec.toNat_mul_of_lt (by change wi_t.toNat * 16 < 2 ^ 64; omega)
    have halign : ((wcnt * 16#64).toNat + 7) / 8 * 8 = wcnt.toNat * 16 := by
      rw [hcnt16]; omega
    have halloc_hi' : pw.toNat + wcnt.toNat * 16 ≤ heapLimit := by rw [← halign]; exact halloc_hi
    have hp_wi16 : (pw + wi_t * 16#64).toNat = pw.toNat + wi_t.toNat * 16 := by
      rw [BitVec.toNat_add_of_lt (by rw [hwi16]; omega), hwi16]
    have hp_wi16_8 : (pw + (wi_t * 16#64) + 8#64).toNat = pw.toNat + wi_t.toNat * 16 + 8 := by
      rw [BitVec.toNat_add_of_lt (by rw [hp_wi16]; change pw.toNat + wi_t.toNat * 16 + 8 < 2 ^ 64; omega), hp_wi16]
      rfl
    have ha0_lo : globN s "heap_ptr" ≤ (pw + wi_t * 16#64).toNat := by omega
    have ha0_hi : (pw + wi_t * 16#64).toNat + 8 ≤ heapLimit := by omega
    have ha8_lo : globN s "heap_ptr" ≤ (pw + (wi_t * 16#64) + 8#64).toNat := by omega
    have ha8_hi : (pw + (wi_t * 16#64) + 8#64).toNat + 8 ≤ heapLimit := by omega
    refine ⟨?_, fun hf => ?_⟩
    · dsimp only [ltsLoopBody_ds] at hnt_b hcr_b ⊢
      refine worldEff_decCall_ro heff_t InitECandidate.Solver.Wave8GuestInv.R13.ro_rlp_item_total_unchecked
        (ofString "total") .one _ hnt_b hcr_b (fun rvt cpost2 hsh_rvt hcpost2 hnt_s1 hcr_s1 => ?_)
      obtain ⟨wt, rfl⟩ := shape_one_word_ds hsh_rvt
      let u0 := setVarHOLFinite (ofString "total") (.val (.word wt)) { cpost2 with locals := t.locals }
      have heff_u0 : WorldEff s u0 [] [] wsGw := (heff_t.of_readOnly hcpost2).locals_clock _ _
      have hu0_arr : u0.locals.lookup (ofString "arr") = some (.val (.word pw)) := by
        simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_arr,
          show ofString "total" ≠ ofString "arr" by decide]
      have hu0_i : u0.locals.lookup (ofString "i") = some (.val (.word wi_t)) := by
        simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hti,
          show ofString "total" ≠ ofString "i" by decide]
      have hu0_p : u0.locals.lookup (ofString "p") = some (.val (.word wp_t)) := by
        simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, htp,
          show ofString "total" ≠ ofString "p" by decide]
      have hu0_off : u0.locals.lookup (ofString "off") = some (.val (.word woff_t)) := by
        simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, htoff,
          show ofString "total" ≠ ofString "off" by decide]
      have hu0_tot : u0.locals.lookup (ofString "total") = some (.val (.word wt)) := by
        simp [u0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      refine worldEff_seq hnt_s1 hcr_s1
        (fun _ _ => worldEff_store_word heff_u0 _ _
          (fun v hv => by
            simp [evalHOLExact, evalListHOLExact, hu0_p, hu0_off, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
            exact ⟨_, hv.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, hu0_arr, hu0_i, panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx
            exact Or.inr (Or.inr (Or.inr ⟨ha0_lo, ha0_hi⟩))))
        (fun u1 hu1 heff_u1 hnt_s2 hcr_s2 => ?_)
      have hu1_loc : u1.locals = u0.locals := by
        have hcf := (evaluate_store_control_frame u0
          (.op .add [.var .local (ofString "arr"), .panop .mul [.var .local (ofString "i"), .const 16]])
          (.op .add [.var .local (ofString "p"), .var .local (ofString "off")])).2.1
        rwa [hu1] at hcf
      refine worldEff_seq hnt_s2 hcr_s2
        (fun _ _ => worldEff_store_word heff_u1 _ _
          (fun v hv => by
            simp [evalHOLExact, hu1_loc, hu0_tot] at hv
            exact ⟨_, hv.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, hu1_loc, hu0_arr, hu0_i, panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx
            have hadd_assoc : pw + (wi_t * 16#64 + 8#64) = pw + wi_t * 16#64 + 8#64 :=
              (BitVec.add_assoc pw (wi_t * 16#64) 8#64).symm
            rw [hadd_assoc]
            exact Or.inr (Or.inr (Or.inr ⟨ha8_lo, ha8_hi⟩))))
        (fun u2 _ heff_u2 hnt_s3 hcr_s3 =>
          worldEff_seq hnt_s3 hcr_s3
            (fun _ _ => worldEff_assign_local heff_u2 _ _)
            (fun u3 _ heff_u3 _ _ => worldEff_assign_local heff_u3 _ _))
    · obtain ⟨hkeep_arr, hkeep_cnt⟩ := ltsLoopBody_keeps_arr_count_ds t pw wcnt ht_arr ht_cnt hf
      exact ⟨hkeep_arr, hkeep_cnt,
        wordLocals_flowing hws_lts ht_wloc (by rcases hf with h | h; exact Or.inl h; exact Or.inr (Or.inr h))⟩
  · exfalso
    have hdb : domainBytes = 31104957928 := by decide
    omega

private theorem call0_or_resumes_ds {F : Type}
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

private theorem ww_compact_to_nibbles :
    WritesWithin (fun _ => []) ["heap_ptr", "scratch_ptr"] (ofString "compact_to_nibbles") := by
  refine ⟨_, _, _, lookup_compact_to_nibbles_ds, ?_⟩
  intro F s hc hAR ⟨vals, hvals⟩ hnt hres
  obtain ⟨wp, wn, rfl, hp_lk, hn_lk⟩ :=
    lookupCode_two_words_any_ds (by decide) lookup_compact_to_nibbles_ds hvals
  have heff0 : WorldEff s s [] [] wsGw := WorldEff.refl s [] [] wsGw hAR hc
  have hbody : sourceFnBody Guest.Software.guestFn_compact_to_nibbles =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "n")) (.const 0#64))
          (.call (some (none, none)) (ofString "mpt_fail") [.const 5#64])
          .skip)
        (.dec (ofString "c0") .one (.loadByte (.var .local (ofString "p")))
          (.dec (ofString "first") .one (.shift .lsr (.var .local (ofString "c0")) (.const 4#64))
            (.dec (ofString "is_leaf") .one
              (.op .and [.shift .lsr (.var .local (ofString "first")) (.const 1#64), .const 1#64])
              (.dec (ofString "odd") .one (.op .and [.var .local (ofString "first"), .const 1#64])
                (.decCall (ofString "out") .one (ofString "alloc")
                  [.panop .mul [.const 2#64, .var .local (ofString "n")]]
                  (.dec (ofString "k") .one (.const 0#64)
                    (.seq
                      (.ite (.cmp .notEqual (.var .local (ofString "odd")) (.const 0#64))
                        (.seq
                          (.storeByte (.var .local (ofString "out"))
                            (.op .and [.var .local (ofString "c0"), .const 15#64]))
                          (.assign .local (ofString "k") (.const 1#64)))
                        .skip)
                      (.seq
                        (.call (some (none, none)) (ofString "key_to_nibbles")
                          [.op .add [.var .local (ofString "p"), .const 1#64],
                           .op .sub [.var .local (ofString "n"), .const 1#64],
                           .op .add [.var .local (ofString "out"), .var .local (ofString "k")]])
                        (.return (.rstruct
                          [.var .local (ofString "out"),
                           .op .add [.var .local (ofString "k"),
                             .panop .mul [.const 2#64,
                               .op .sub [.var .local (ofString "n"), .const 1#64]]],
                           .var .local (ofString "is_leaf")])))))))))) := rfl
  suffices heff_fin : WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_compact_to_nibbles)).2
      [] [] wsGw from stepFrame_to_ww (stepFrame_of_worldEff_emptyB heff_fin)
  rw [hbody] at hnt hres ⊢
  by_cases hn0 : wn = 0#64
  · subst hn0
    have hev_n0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .equal (.var .local (ofString "n")) (.const 0#64)) = some (.val (.word 1#64)) := by
      simp [evalHOLExact, evalListHOLExact, hn_lk, Compiler.Encoders.Asm.wordCmpHOL]
    have hite_n0 : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.var .local (ofString "n")) (.const 0#64))
          (.call (some (none, none)) (ofString "mpt_fail") [.const 5#64]) .skip) =
        evaluateHOLFiniteState s (.call (some (none, none)) (ofString "mpt_fail") [.const 5#64]) := by
      rw [evaluateHOLFiniteState_ite, hev_n0]; simp
    refine worldEff_seq hnt (Or.inr (Or.inr (Or.inr hres)))
      (fun hnt_i hcr_i =>
        worldEff_ite heff0 _ hnt_i hcr_i
          (fun _ _ _ hnt_t hcr_t => worldEff_call0_ro heff0 R11Adapters.ReadOnlyLeaves.«ro_mpt_fail» _ hnt_t hcr_t)
          (fun _ _ _ => worldEff_skip heff0))
      (fun m0 hm0 _ _ _ => ?_)
    rw [hite_n0] at hm0
    exfalso
    rw [evaluateHOLFiniteState_call] at hm0
    revert hm0
    split <;> [simp; (split <;> [simp; skip])]
    rename_i b_mf c_mf r_mf hl_mf
    have hb_mf := lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ b_mf _ r_mf _ c_mf
      (by rw [hc]; exact lookup_mpt_fail) hl_mf
    subst hb_mf
    split <;> [simp; skip]
    have hbody_mf : sourceFnBody Guest.Software.guestFn_mpt_fail =
        .seq (.raise (ofString "MptErr") (.var .local (ofString "code"))) (.return (.const 0#64)) := rfl
    have hmfn : (evaluateHOLFiniteState (callEntryStateHOLFinite s c_mf)
        (sourceFnBody Guest.Software.guestFn_mpt_fail)).1 ≠ none := by
      rw [hbody_mf, evaluateHOLFiniteState_seq_line780]
      rcases evaluateHOLFiniteState _ (.raise _ _) with ⟨rm, tm⟩
      cases rm with
      | some _ => simp
      | none => dsimp only; exact return_ne_none tm _
    have hmfr : ∀ u, (evaluateHOLFiniteState (callEntryStateHOLFinite s c_mf)
        (sourceFnBody Guest.Software.guestFn_mpt_fail)).1 ≠ some (.returned u) := by
      intro u
      rw [hbody_mf, evaluateHOLFiniteState_seq_line780]
      rcases hr1 : evaluateHOLFiniteState _ (.raise _ _) with ⟨rm, tm⟩
      cases rm with
      | some rm' =>
        dsimp only
        intro hret_u
        rw [evaluateHOLFiniteState_raise] at hr1
        split at hr1
        · dsimp only at hr1
          split at hr1
          · injection hr1 with hr1' _; injection hr1' with hr1''; subst hr1''; simp at hret_u
          · injection hr1 with hr1' _; injection hr1' with hr1''; subst hr1''; simp at hret_u
        · injection hr1 with hr1' _; injection hr1' with hr1''; subst hr1''; simp at hret_u
      | none =>
        exfalso
        rw [evaluateHOLFiniteState_raise] at hr1
        split at hr1
        · dsimp only at hr1; split at hr1 <;> simp at hr1
        · simp at hr1
    rcases hr_mf : evaluateHOLFiniteState (callEntryStateHOLFinite s c_mf)
        (sourceFnBody Guest.Software.guestFn_mpt_fail) with ⟨rmf, _⟩
    rw [hr_mf] at hmfn hmfr
    cases rmf with
    | none => exact absurd rfl hmfn
    | some rmf' =>
      cases rmf' with
      | returned rv => exact absurd rfl (hmfr rv)
      | _ => dsimp only; (repeat' split) <;> simp
  · have hn_pos : 0 < wn.toNat := Nat.pos_of_ne_zero (fun h => hn0 (BitVec.eq_of_toNat_eq h))
    have hev_n0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .equal (.var .local (ofString "n")) (.const 0#64)) = some (.val (.word 0#64)) := by
      simp [evalHOLExact, evalListHOLExact, hn_lk, Compiler.Encoders.Asm.wordCmpHOL, hn0]
    have hite_n0 : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.var .local (ofString "n")) (.const 0#64))
          (.call (some (none, none)) (ofString "mpt_fail") [.const 5#64]) .skip) = (none, s) := by
      rw [evaluateHOLFiniteState_ite, hev_n0]; simp [evaluateHOLFiniteState_skip]
    rw [evaluateHOLFiniteState_seq_line780, hite_n0] at hnt hres ⊢
    dsimp only at hnt hres ⊢
    refine worldEff_dec heff0 _ _ _ hnt (Or.inr (Or.inr (Or.inr hres))) (fun vc0 _ _ hnt1 hcr1 => ?_)
    let s1 := setVarHOLFinite (ofString "c0") vc0 s
    have heff1 : WorldEff s s1 [] [] wsGw := heff0.locals_clock _ _
    refine worldEff_dec heff1 _ _ _ hnt1 hcr1 (fun vfirst _ _ hnt2 hcr2 => ?_)
    let s2 := setVarHOLFinite (ofString "first") vfirst s1
    have heff2 : WorldEff s s2 [] [] wsGw := heff1.locals_clock _ _
    refine worldEff_dec heff2 _ _ _ hnt2 hcr2 (fun visl _ _ hnt3 hcr3 => ?_)
    let s3 := setVarHOLFinite (ofString "is_leaf") visl s2
    have heff3 : WorldEff s s3 [] [] wsGw := heff2.locals_clock _ _
    refine worldEff_dec heff3 _ _ _ hnt3 hcr3 (fun vodd _ _ hnt4 hcr4 => ?_)
    let s4 := setVarHOLFinite (ofString "odd") vodd s3
    have heff4 : WorldEff s s4 [] [] wsGw := heff3.locals_clock _ _
    have hs4_n : s4.locals.lookup (ofString "n") = some (.val (.word wn)) := by
      simp [s4, s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_lk,
        show ofString "odd" ≠ ofString "n" by decide,
        show ofString "is_leaf" ≠ ofString "n" by decide,
        show ofString "first" ≠ ofString "n" by decide,
        show ofString "c0" ≠ ofString "n" by decide]
    have hs4_p : s4.locals.lookup (ofString "p") = some (.val (.word wp)) := by
      simp [s4, s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_lk,
        show ofString "odd" ≠ ofString "p" by decide,
        show ofString "is_leaf" ≠ ofString "p" by decide,
        show ofString "first" ≠ ofString "p" by decide,
        show ofString "c0" ≠ ofString "p" by decide]
    refine worldEff_decCall_alloc heff4 (by decide) (ofString "out") _ hnt4 hcr4
      (fun pw nw s5 hsz_ev _ hs5_loc _ heff5 _ _ hpw_lo_s hpw_add hhp_s5_hi _ hnt5 hcr5 => ?_)
    have hnw_eq : nw = 2#64 * wn := by
      simp [evalHOLExact, evalListHOLExact, hs4_n, panOpHOL, valueIsWord, valueWord] at hsz_ev
      exact hsz_ev.symm
    subst hnw_eq
    have hhl_lt : heapLimit < 2 ^ 64 := by decide
    refine worldEff_dec heff5 _ _ _ hnt5 hcr5 (fun vk hvk _ hnt6 hcr6 => ?_)
    have hvk_eq : vk = .val (.word 0#64) := by simp [evalHOLExact] at hvk; exact hvk.symm
    subst hvk_eq
    let s6 := setVarHOLFinite (ofString "k") (.val (.word 0#64)) s5
    have heff6 : WorldEff s s6 [] [] wsGw := heff5.locals_clock _ _
    have hs6_out : s6.locals.lookup (ofString "out") = some (.val (.word pw)) := by
      simp [s6, setVarHOLFinite, hs5_loc, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "k" ≠ ofString "out" by decide]
    have hs6_p : s6.locals.lookup (ofString "p") = some (.val (.word wp)) := by
      simp [s6, setVarHOLFinite, hs5_loc, hs4_p, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "k" ≠ ofString "p" by decide, show ofString "out" ≠ ofString "p" by decide]
    have hs6_n : s6.locals.lookup (ofString "n") = some (.val (.word wn)) := by
      simp [s6, setVarHOLFinite, hs5_loc, hs4_n, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "k" ≠ ofString "n" by decide, show ofString "out" ≠ ofString "n" by decide]
    have hs6_k : s6.locals.lookup (ofString "k") = some (.val (.word 0#64)) := by
      simp [s6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have h2n_lt : 2 * wn.toNat < 2 ^ 64 := by
      by_contra hge
      have hwn_big : 2 ^ 63 ≤ wn.toNat := by omega
      rcases hite_ev : evaluateHOLFiniteState s6
          (.ite (.cmp .notEqual (.var .local (ofString "odd")) (.const 0#64))
            (.seq
              (.storeByte (.var .local (ofString "out"))
                (.op .and [.var .local (ofString "c0"), .const 15#64]))
              (.assign .local (ofString "k") (.const 1#64)))
            .skip) with ⟨ri, s7_ov⟩
      rw [evaluateHOLFiniteState_seq_line780, hite_ev] at hnt6 hcr6
      have hite_nonres : ri = none ∨ ri = some .error := by
        rw [evaluateHOLFiniteState_ite] at hite_ev
        rcases hce : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a))
            (.cmp .notEqual (.var .local (ofString "odd")) (.const 0#64)) with _ | vc
        · rw [hce] at hite_ev; injection hite_ev with hr _; exact Or.inr hr.symm
        · rw [hce] at hite_ev
          rcases vc with ⟨⟨wc⟩⟩ | _ | _ <;> try (injection hite_ev with hr _; exact Or.inr hr.symm)
          dsimp only at hite_ev
          by_cases hwc0 : wc = 0
          · subst hwc0; simp [evaluateHOLFiniteState_skip] at hite_ev
            exact Or.inl hite_ev.1.symm
          · rw [if_neg hwc0, evaluateHOLFiniteState_seq_line780] at hite_ev
            rcases hsb_ov : evaluateHOLFiniteState s6
                (.storeByte (.var .local (ofString "out"))
                  (.op .and [.var .local (ofString "c0"), .const 15#64])) with ⟨rsb, msb⟩
            rw [hsb_ov] at hite_ev
            have hsb_cf := (PanRunBounded.evaluate_storeByte_control_frame s6
              (.var .local (ofString "out"))
              (.op .and [.var .local (ofString "c0"), .const 15#64])).1
            rw [hsb_ov] at hsb_cf
            rcases hsb_cf with hrsb0 | hrsb_err
            · subst hrsb0; dsimp only at hite_ev
              rw [evaluateHOLFiniteState_assign] at hite_ev
              have hev1 : @evalHOLExact 64 F _ msb.toExact (fun a => Classical.propDecidable (msb.memaddrs a))
                  (.const 1#64) = some (.val (.word 1#64)) := rfl
              rw [hev1] at hite_ev; dsimp only at hite_ev
              split at hite_ev
              · exact Or.inl (congrArg Prod.fst hite_ev).symm
              · exact Or.inr (congrArg Prod.fst hite_ev).symm
            · subst hrsb_err; dsimp only at hite_ev
              exact Or.inr (congrArg Prod.fst hite_ev).symm
      rcases hite_nonres with hri0 | hri_err
      · subst hri0; dsimp only at hnt6 hcr6
        have hs7_ctrl : s7_ov.code = originalRuntimeCode ∧ GuestInv s7_ov ∧
            s7_ov.locals.lookup (ofString "n") = some (.val (.word wn)) := by
          rw [evaluateHOLFiniteState_ite] at hite_ev
          rcases hce : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a))
              (.cmp .notEqual (.var .local (ofString "odd")) (.const 0#64)) with _ | vc
          · rw [hce] at hite_ev; simp at hite_ev
          · rw [hce] at hite_ev
            rcases vc with ⟨⟨wc⟩⟩ | _ | _ <;> try (simp at hite_ev)
            by_cases hwc0 : wc = 0#64
            · subst hwc0; simp [evaluateHOLFiniteState_skip] at hite_ev; subst hite_ev
              exact ⟨heff6.code, heff6.arena.1, hs6_n⟩
            · simp only [hwc0, ↓reduceIte, evaluateHOLFiniteState_seq_line780] at hite_ev
              rcases hsb_ov : evaluateHOLFiniteState s6
                  (.storeByte (.var .local (ofString "out"))
                    (.op .and [.var .local (ofString "c0"), .const 15#64])) with ⟨rsb, msb⟩
              rw [hsb_ov] at hite_ev
              cases rsb with
              | some _ => dsimp only at hite_ev; cases hite_ev
              | none =>
                dsimp only at hite_ev
                have hcf := PanRunBounded.evaluate_storeByte_control_frame s6
                  (.var .local (ofString "out"))
                  (.op .and [.var .local (ofString "c0"), .const 15#64])
                have hcf_loc : msb.locals = s6.locals := by have h := hcf.2.2.1; rwa [hsb_ov] at h
                have hcf_code : msb.code = s6.code := by have h := hcf.2.2.2.2.1; rwa [hsb_ov] at h
                have hs7_G : GuestInv (setKvarHOLFinite .local (ofString "k") (.val (.word 1#64)) msb) := by
                  have hG_msb : GuestInv msb := by
                    have h := guestInv_evaluate s6
                      (.storeByte (.var .local (ofString "out"))
                        (.op .and [.var .local (ofString "c0"), .const 15#64])) heff6.arena.1
                    rwa [hsb_ov] at h
                  exact guestInv_congr (s := msb) rfl rfl rfl rfl hG_msb
                rw [evaluateHOLFiniteState_assign] at hite_ev
                have hev1 : @evalHOLExact 64 F _ msb.toExact (fun a => Classical.propDecidable (msb.memaddrs a))
                    (.const 1#64) = some (.val (.word 1#64)) := rfl
                rw [hev1] at hite_ev; dsimp only at hite_ev
                by_cases hval1 : isValidValueHOLFinite msb .local (ofString "k") (.val (.word 1#64)) = true
                · rw [if_pos hval1] at hite_ev
                  injection hite_ev with _ hs7_eq; subst hs7_eq
                  have hc_s7 : (setKvarHOLFinite .local (ofString "k") (.val (.word 1#64)) msb).code =
                      originalRuntimeCode := by
                    dsimp only [setKvarHOLFinite, setVarHOLFinite]
                    exact hcf_code.trans heff6.code
                  refine ⟨hc_s7, hs7_G, ?_⟩
                  simp [setKvarHOLFinite, setVarHOLFinite, hcf_loc, hs6_n, HolFiniteMapExact.lookup_update,
                    FUPDATE, show ofString "k" ≠ ofString "n" by decide]
                · rw [if_neg hval1] at hite_ev; cases hite_ev
        rcases hktn_ov : evaluateHOLFiniteState s7_ov
            (.call (some (none, none)) (ofString "key_to_nibbles")
              [.op .add [.var .local (ofString "p"), .const 1#64],
               .op .sub [.var .local (ofString "n"), .const 1#64],
               .op .add [.var .local (ofString "out"), .var .local (ofString "k")]]) with ⟨rk_ov, pk_ov⟩
        rw [evaluateHOLFiniteState_seq_line780, hktn_ov] at hnt6 hcr6
        have hktn_nt : rk_ov ≠ some .timeOut := by
          intro ht; subst ht; exact hnt6 rfl
        have hktn_or : rk_ov = none ∨ Resumes rk_ov := by
          cases rk_ov with
          | none => exact Or.inl rfl
          | some r' =>
            dsimp only at hcr6
            have hor_ov := call0_or_resumes_ds s7_ov (ofString "key_to_nibbles")
              [.op .add [.var .local (ofString "p"), .const 1#64],
               .op .sub [.var .local (ofString "n"), .const 1#64],
               .op .add [.var .local (ofString "out"), .var .local (ofString "k")]]
              (by rwa [hktn_ov])
            rwa [hktn_ov] at hor_ov
        obtain ⟨_, nw_ov, ow_ov, _, hnw_ov, _, _, _, hdom_ov⟩ :=
          call0_key_to_nibbles_eff s7_ov
            (.op .add [.var .local (ofString "p"), .const 1#64])
            (.op .sub [.var .local (ofString "n"), .const 1#64])
            (.op .add [.var .local (ofString "out"), .var .local (ofString "k")])
            hs7_ctrl.1 hs7_ctrl.2.1
            (by rwa [hktn_ov]) (by rwa [hktn_ov])
        have hnw_eq_sub : nw_ov = wn - 1#64 := by
          simp [evalHOLExact, evalListHOLExact, hs7_ctrl.2.2, wordOpHOL, wordOp, valueIsWord, valueWord] at hnw_ov
          exact hnw_ov.symm
        subst hnw_eq_sub
        have hsub_nat : (wn - 1#64).toNat = wn.toNat - 1 := by
          rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 1 ≤ wn.toNat; omega)]
          rfl
        have hdom_hi : ow_ov.toNat + 2 * (wn.toNat - 1) ≤ heapEnd := by
          have := (hdom_ov (by rw [hsub_nat]; omega)).2
          rwa [hsub_nat] at this
        have hhe_val : heapEnd < 2 ^ 63 := by decide
        omega
      · subst hri_err; dsimp only at hcr6
        rcases hcr6 with h | h | h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    have h2n_nat : (2#64 * wn).toNat = 2 * wn.toNat :=
      BitVec.toNat_mul_of_lt (by change 2 * wn.toNat < 2 ^ 64; exact h2n_lt)
    have halloc_hi : pw.toNat + 2 * wn.toNat ≤ heapLimit := by
      rw [h2n_nat] at hpw_add
      omega
    refine worldEff_seq hnt6 hcr6
      (fun hnt_i hcr_i =>
        worldEff_ite heff6 _ hnt_i hcr_i
          (fun _ _ _ hnt_t hcr_t =>
            worldEff_seq hnt_t hcr_t
              (fun _ _ => worldEff_storeByte heff6 _ _ (fun x hx _ => by
                simp [evalHOLExact, hs6_out] at hx; subst hx
                exact Or.inr (Or.inr (Or.inr ⟨hpw_lo_s, by omega⟩))))
              (fun m1 _ heff_m1 _ _ => worldEff_assign_local heff_m1 _ _))
          (fun _ _ _ => worldEff_skip heff6))
      (fun s7 hs7 heff7 hnt7 hcr7 => ?_)
    -- Show that in `s7`, `out = pw`, `p = wp`, `n = wn`, and `k ∈ {0, 1}`!
    have hs7_inv : s7.locals.lookup (ofString "out") = some (.val (.word pw)) ∧
        s7.locals.lookup (ofString "p") = some (.val (.word wp)) ∧
        s7.locals.lookup (ofString "n") = some (.val (.word wn)) ∧
        ∃ wk : BitVec 64, s7.locals.lookup (ofString "k") = some (.val (.word wk)) ∧ wk.toNat ≤ 1 := by
      rw [evaluateHOLFiniteState_ite] at hs7
      rcases hce : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a))
          (.cmp .notEqual (.var .local (ofString "odd")) (.const 0#64)) with _ | vc
      · rw [hce] at hs7; simp at hs7
      · rw [hce] at hs7
        rcases vc with ⟨⟨wc⟩⟩ | _ | _ <;> try (simp at hs7)
        by_cases hwc0 : wc = 0#64
        · subst hwc0; simp [evaluateHOLFiniteState_skip] at hs7; subst hs7
          exact ⟨hs6_out, hs6_p, hs6_n, 0#64, hs6_k, by decide⟩
        · simp only [hwc0, ↓reduceIte] at hs7
          rw [evaluateHOLFiniteState_seq_line780] at hs7
          rcases hsb : evaluateHOLFiniteState s6
              (.storeByte (.var .local (ofString "out"))
                (.op .and [.var .local (ofString "c0"), .const 15#64])) with ⟨rsb, msb⟩
          rw [hsb] at hs7
          cases rsb with
          | some _ => simp at hs7
          | none =>
            dsimp only at hs7
            have hmsb_loc : msb.locals = s6.locals := by
              have hcf := (PanRunBounded.evaluate_storeByte_control_frame s6
                (.var .local (ofString "out"))
                (.op .and [.var .local (ofString "c0"), .const 15#64])).2.2.1
              rwa [hsb] at hcf
            rw [evaluateHOLFiniteState_assign] at hs7
            have hev1 : @evalHOLExact 64 F _ msb.toExact (fun a => Classical.propDecidable (msb.memaddrs a))
                (.const 1#64) = some (.val (.word 1#64)) := rfl
            rw [hev1] at hs7; dsimp only at hs7
            split at hs7
            · injection hs7 with _ hs7_eq; subst hs7_eq
              refine ⟨?_, ?_, ?_, 1#64, ?_, by decide⟩
              · simp [setKvarHOLFinite, setVarHOLFinite, hmsb_loc, hs6_out, HolFiniteMapExact.lookup_update,
                  FUPDATE, show ofString "k" ≠ ofString "out" by decide]
              · simp [setKvarHOLFinite, setVarHOLFinite, hmsb_loc, hs6_p, HolFiniteMapExact.lookup_update,
                  FUPDATE, show ofString "k" ≠ ofString "p" by decide]
              · simp [setKvarHOLFinite, setVarHOLFinite, hmsb_loc, hs6_n, HolFiniteMapExact.lookup_update,
                  FUPDATE, show ofString "k" ≠ ofString "n" by decide]
              · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            · simp at hs7
    obtain ⟨hs7_out, hs7_p, hs7_n, wk, hs7_k, hwk_le⟩ := hs7_inv
    refine worldEff_seq hnt7 hcr7
      (fun hnt_ktn hcr_ktn => ?_)
      (fun s8 _ heff8 _ _ => worldEff_return heff8 _)
    -- `call (some (none, none)) "key_to_nibbles" [p + 1, n - 1, out + k]`
    obtain ⟨_, nw_ktn, ow_ktn, _, hnw_ktn, how_ktn, hbe_s7, _, _⟩ :=
      call0_key_to_nibbles_eff s7
        (.op .add [.var .local (ofString "p"), .const 1#64])
        (.op .sub [.var .local (ofString "n"), .const 1#64])
        (.op .add [.var .local (ofString "out"), .var .local (ofString "k")])
        heff7.code heff7.arena.1 hnt_ktn
        (call0_or_resumes_ds s7 (ofString "key_to_nibbles") _ hcr_ktn)
    have hnw_eq_ktn : nw_ktn = wn - 1#64 := by
      simp [evalHOLExact, evalListHOLExact, hs7_n, wordOpHOL, wordOp, valueIsWord, valueWord] at hnw_ktn
      exact hnw_ktn.symm
    have how_eq_ktn : ow_ktn = pw + wk := by
      simp [evalHOLExact, evalListHOLExact, hs7_out, hs7_k, wordOpHOL, wordOp, valueIsWord, valueWord] at how_ktn
      exact how_ktn.symm
    subst hnw_eq_ktn; subst how_eq_ktn
    have hsub_heap : (pw + wk).toNat + 2 * (wn - 1#64).toNat ≤ heapLimit ∧
        globN s "heap_ptr" ≤ (pw + wk).toNat := by
      have hsub1 : (wn - 1#64).toNat = wn.toNat - 1 := by
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 1 ≤ wn.toNat; omega)]
        rfl
      have hpwk : (pw + wk).toNat = pw.toNat + wk.toNat :=
        BitVec.toNat_add_of_lt (by omega)
      rw [hsub1, hpwk]
      exact ⟨by omega, by omega⟩
    have hbe_fast : Fast_C08WkShard03.ByteEff s7 _ [((pw + wk).toNat, 2 * (wn - 1#64).toNat)] :=
      ⟨hbe_s7.code, hbe_s7.memaddrs, hbe_s7.shMemaddrs, hbe_s7.baseAddr,
       hbe_s7.be, hbe_s7.globals, hbe_s7.eshapes, hbe_s7.out_dom,
       hbe_s7.cell_frame, hbe_s7.byte_frame⟩
    exact heff7.of_byteEff hbe_fast (fun iv hiv _ => by
      simp only [List.mem_singleton] at hiv; subst hiv
      exact Or.inr (Or.inr (Or.inr ⟨hsub_heap.2, hsub_heap.1⟩)))

private theorem ww_node_new_branch_ds :
    WritesWithin (fun _ => []) ["heap_ptr", "scratch_ptr"] (ofString "node_new_branch") := by
  refine ⟨_, _, _, R14Shards.lookup_node_new_branch, ?_⟩
  intro F s hc hAR _ _ hres
  have hnh0 : Wave8GuestInv.NodeHeap s [] :=
    And.intro (fun _ h => nomatch h) (fun _ h => nomatch h)
  have hspec := R14Shards.node_new_branch_spec s hc hAR hres
  rcases hspec with ⟨hARp, hhp, hsp, _, _, _, _, _, _, _, _, _, hns_fn⟩
  have hns := hns_fn [] hnh0
  exact ⟨hARp, hhp, hsp, hns.frame, hns.globals⟩

private theorem lookup_four_words_leaf {vals : List (ValueHOL 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {body : ProgHOL 64} {ret : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "node_new_leaf") vals =
      some (body, L, ret)) :
    ∃ w0 w1 w2 w3 : BitVec 64,
      L.lookup (ofString "nib") = some (.val (.word w0)) ∧
      L.lookup (ofString "nlen") = some (.val (.word w1)) ∧
      L.lookup (ofString "vptr") = some (.val (.word w2)) ∧
      L.lookup (ofString "vlen") = some (.val (.word w3)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup _ vals _ L _ hl
  simp only [lookupCodeHOLExact, lookup_node_new_leaf] at hx
  rcases vals with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩⟩ <;> try (simp at hx)
  rcases v0 with ⟨⟨w0⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;>
    rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;> rcases v3 with ⟨⟨w3⟩⟩ | _ | _ <;>
    simp [shapeOfHOLExact, shapeEqHOL] at hx
  obtain ⟨_, _, h1, _⟩ := hx
  refine ⟨w0, w1, w2, w3, ?_, ?_, ?_, ?_⟩ <;>
    (rw [← h1]; simp [
      show ofString "nib" ≠ ofString "nlen" by decide,
      show ofString "nib" ≠ ofString "vptr" by decide,
      show ofString "nib" ≠ ofString "vlen" by decide,
      show ofString "nlen" ≠ ofString "nib" by decide,
      show ofString "nlen" ≠ ofString "vptr" by decide,
      show ofString "nlen" ≠ ofString "vlen" by decide,
      show ofString "vptr" ≠ ofString "nib" by decide,
      show ofString "vptr" ≠ ofString "nlen" by decide,
      show ofString "vptr" ≠ ofString "vlen" by decide,
      show ofString "vlen" ≠ ofString "nib" by decide,
      show ofString "vlen" ≠ ofString "nlen" by decide,
      show ofString "vlen" ≠ ofString "vptr" by decide])

private theorem ww_node_new_leaf_ds :
    WritesWithin (fun _ => []) ["heap_ptr"] (ofString "node_new_leaf") := by
  refine ⟨_, _, _, lookup_node_new_leaf, ?_⟩
  intro F s hc hAR ⟨vals, hvals⟩ hnt hres
  obtain ⟨w0, w1, w2, w3, hw0, hw1, hw2, hw3⟩ := lookup_four_words_leaf hvals
  have heff0 : WorldEff s s [] [] ["heap_ptr"] := WorldEff.refl s [] [] ["heap_ptr"] hAR hc
  have hbody : sourceFnBody Guest.Software.guestFn_node_new_leaf =
      .decCall (ofString "nd") .one (ofString "alloc") [.const 64#64]
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const 0#64]) (.const 1#64))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const 8#64]) (.const 0#64))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16#64]) (.const 0#64))
              (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24#64]) (.const 0#64))
                (.seq (.store (.op .add [.var .local (ofString "nd"), .const 32#64]) (.var .local (ofString "nib")))
                  (.seq (.store (.op .add [.var .local (ofString "nd"), .const 40#64]) (.var .local (ofString "nlen")))
                    (.seq (.store (.op .add [.var .local (ofString "nd"), .const 48#64]) (.var .local (ofString "vptr")))
                      (.seq (.store (.op .add [.var .local (ofString "nd"), .const 56#64]) (.var .local (ofString "vlen")))
                        (.return (.var .local (ofString "nd"))))))))))) := rfl
  suffices heff_fin : WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_new_leaf)).2
      [] [] ["heap_ptr"] by
    refine ⟨heff_fin.arena, heff_fin.hp_lo, heff_fin.sp_hi, ?_, ?_⟩
    · intro a hkeep hfresh
      by_contra hne
      rcases heff_fin.cell_frame a hne with ⟨_, hm, _⟩ | ⟨_, hm, _⟩ | ⟨_, hch⟩ | ⟨_, hch⟩
      · cases hm
      · cases hm
      · exact hkeep (freeGap s) (List.mem_singleton.mpr rfl) hch
      · exact hfresh hch
    · intro k hk
      exact heff_fin.gw_kept k hk
  rw [hbody] at hnt hres ⊢
  refine worldEff_decCall_alloc heff0 (by decide) (ofString "nd") _ hnt (Or.inr (Or.inr (Or.inr hres)))
    (fun pw nw m0 hsz_ev _ hm0_loc _ heff_m0 _ _ hpw_lo_s hpw_add hhp_m0_hi _ hnt_k hcr_k => ?_)
  have hnw_eq : nw = 64#64 := by simp [evalHOLExact] at hsz_ev; exact hsz_ev.symm
  subst hnw_eq
  have h64 : ((64#64).toNat + 7) / 8 * 8 = 64 := by decide
  rw [h64] at hpw_add
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hin_off : ∀ (cur : PanSemStateFiniteExact 64 F) (off : BitVec 64),
      cur.locals = m0.locals → off.toNat ≤ 56 →
      ∀ x : BitVec 64,
        @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
          (.op .add [.var .local (ofString "nd"), .const off]) = some (.val (.word x)) →
        cur.memaddrs x →
        (∃ j ∈ ([] : List Ivl), j.1 ≤ x.toNat ∧ x.toNat + 8 ≤ j.1 + j.2) ∨
        (∃ gs ∈ ([] : List (String × Nat)), (bufferRegion s gs).1 ≤ x.toNat ∧ x.toNat + 8 ≤ (bufferRegion s gs).1 + (bufferRegion s gs).2) ∨
        (globN s "frame_mem_ptr" ≤ x.toNat ∧ x.toNat + 8 ≤ globN s "scratch_ptr") ∨
        (globN s "heap_ptr" ≤ x.toNat ∧ x.toNat + 8 ≤ heapLimit) := by
    intro cur off hloc hoff x hx _
    have hnd_lk : cur.locals.lookup (ofString "nd") = some (.val (.word pw)) := by
      simp [hloc, hm0_loc, HolFiniteMapExact.lookup_update, FUPDATE]
    simp [evalHOLExact, evalListHOLExact, hnd_lk, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
    subst hx
    have hadd_nat : (pw + off).toNat = pw.toNat + off.toNat := BitVec.toNat_add_of_lt (by omega)
    exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
  have hval_const : ∀ (cur : PanSemStateFiniteExact 64 F) (c : BitVec 64) v,
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) (.const c) = some v →
      ∃ w : BitVec 64, v = .val (.word w) := fun _ c v hv => by
    simp [evalHOLExact] at hv; exact ⟨c, hv.symm⟩
  have hval_var : ∀ (cur : PanSemStateFiniteExact 64 F) (nm : String) (w : BitVec 64),
      cur.locals = m0.locals → s.locals.lookup (ofString nm) = some (.val (.word w)) →
      ofString "nd" ≠ ofString nm →
      ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
        (.var .local (ofString nm)) = some v →
      ∃ w' : BitVec 64, v = .val (.word w') := by
    intro cur nm w hloc hs_lk hne v hv
    have hlk : cur.locals.lookup (ofString nm) = some (.val (.word w)) := by
      simp [hloc, hm0_loc, HolFiniteMapExact.lookup_update, FUPDATE, hs_lk, hne]
    simp [evalHOLExact, hlk] at hv; exact ⟨w, hv.symm⟩
  have store_loc : ∀ {cur nxt : PanSemStateFiniteExact 64 F} {dst src : ExpHOL 64},
      evaluateHOLFiniteState cur (.store dst src) = (none, nxt) → nxt.locals = cur.locals := by
    intro cur nxt dst src hev
    have hcf := (evaluate_store_control_frame cur dst src).2.1
    rwa [hev] at hcf
  refine worldEff_seq hnt_k hcr_k
    (fun _ _ => worldEff_store_word heff_m0 _ _ (hval_const m0 1#64) (hin_off m0 0#64 rfl (by decide)))
    (fun m1 hm1 heff_m1 hnt1 hcr1 => ?_)
  have hm1_loc : m1.locals = m0.locals := store_loc hm1
  refine worldEff_seq hnt1 hcr1
    (fun _ _ => worldEff_store_word heff_m1 _ _ (hval_const m1 0#64) (hin_off m1 8#64 hm1_loc (by decide)))
    (fun m2 hm2 heff_m2 hnt2 hcr2 => ?_)
  have hm2_loc : m2.locals = m0.locals := (store_loc hm2).trans hm1_loc
  refine worldEff_seq hnt2 hcr2
    (fun _ _ => worldEff_store_word heff_m2 _ _ (hval_const m2 0#64) (hin_off m2 16#64 hm2_loc (by decide)))
    (fun m3 hm3 heff_m3 hnt3 hcr3 => ?_)
  have hm3_loc : m3.locals = m0.locals := (store_loc hm3).trans hm2_loc
  refine worldEff_seq hnt3 hcr3
    (fun _ _ => worldEff_store_word heff_m3 _ _ (hval_const m3 0#64) (hin_off m3 24#64 hm3_loc (by decide)))
    (fun m4 hm4 heff_m4 hnt4 hcr4 => ?_)
  have hm4_loc : m4.locals = m0.locals := (store_loc hm4).trans hm3_loc
  refine worldEff_seq hnt4 hcr4
    (fun _ _ => worldEff_store_word heff_m4 _ _ (hval_var m4 "nib" w0 hm4_loc hw0 (by decide)) (hin_off m4 32#64 hm4_loc (by decide)))
    (fun m5 hm5 heff_m5 hnt5 hcr5 => ?_)
  have hm5_loc : m5.locals = m0.locals := (store_loc hm5).trans hm4_loc
  refine worldEff_seq hnt5 hcr5
    (fun _ _ => worldEff_store_word heff_m5 _ _ (hval_var m5 "nlen" w1 hm5_loc hw1 (by decide)) (hin_off m5 40#64 hm5_loc (by decide)))
    (fun m6 hm6 heff_m6 hnt6 hcr6 => ?_)
  have hm6_loc : m6.locals = m0.locals := (store_loc hm6).trans hm5_loc
  refine worldEff_seq hnt6 hcr6
    (fun _ _ => worldEff_store_word heff_m6 _ _ (hval_var m6 "vptr" w2 hm6_loc hw2 (by decide)) (hin_off m6 48#64 hm6_loc (by decide)))
    (fun m7 hm7 heff_m7 hnt7 hcr7 => ?_)
  have hm7_loc : m7.locals = m0.locals := (store_loc hm7).trans hm6_loc
  refine worldEff_seq hnt7 hcr7
    (fun _ _ => worldEff_store_word heff_m7 _ _ (hval_var m7 "vlen" w3 hm7_loc hw3 (by decide)) (hin_off m7 56#64 hm7_loc (by decide)))
    (fun m8 _ heff_m8 _ _ => worldEff_return heff_m8 _)

/-! ## Section 3: Return-Block Spec for `node_new_leaf` -/

private theorem rt_node_new_leaf_64 :
    Returns ArenaReady (fun s post nd => FreshBlock s post nd 64) (ofString "node_new_leaf") := by
  refine ⟨_, _, _, lookup_node_new_leaf, ?_⟩
  intro F s hc hAR ⟨vals, hvals⟩ _hnt v hret
  obtain ⟨w0, w1, w2, w3, hw0, hw1, hw2, hw3⟩ := lookup_four_words_leaf hvals
  obtain ⟨hG, hA⟩ := hAR
  obtain ⟨hp, _, _, hhp, hhp_eq, _, _, _, _⟩ := arenaOK_globals s hA
  have hbody : sourceFnBody Guest.Software.guestFn_node_new_leaf =
      .decCall (ofString "nd") .one (ofString "alloc") [.const 64#64]
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const 0#64]) (.const 1#64))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const 8#64]) (.const 0#64))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16#64]) (.const 0#64))
              (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24#64]) (.const 0#64))
                (.seq (.store (.op .add [.var .local (ofString "nd"), .const 32#64]) (.var .local (ofString "nib")))
                  (.seq (.store (.op .add [.var .local (ofString "nd"), .const 40#64]) (.var .local (ofString "nlen")))
                    (.seq (.store (.op .add [.var .local (ofString "nd"), .const 48#64]) (.var .local (ofString "vptr")))
                      (.seq (.store (.op .add [.var .local (ofString "nd"), .const 56#64]) (.var .local (ofString "vlen")))
                        (.return (.var .local (ofString "nd"))))))))))) := rfl
  have hrun : Ret s (sourceFnBody Guest.Software.guestFn_node_new_leaf)
      (fun val post => ∃ w : BitVec 64, val = .val (.word w) ∧
        ArenaReady post ∧ AllocatorGrows s post ∧ FreshBlock s post w.toNat 64) := by
    rw [hbody]
    apply Ret.of_NS
    refine Ret.ns_alloc hc 64#64 rfl hp hhp ?_
    intro hcmp1 hcmp2
    set q : BitVec 64 := (hp + (64#64 + 7)) &&& ((0 : BitVec 64) - 8)
    set L1 := s.locals.update (ofString "nd", .val (.word hp))
    set G1 := s.globals.update (ofString "heap_ptr", .val (.word q))
    have hnd_ev : ∀ M off, ev (NS s L1 G1 M (s.clock - 1))
        (.op .add [.var .local (ofString "nd"), .const off]) = some (.val (.word (hp + off))) := fun _ _ => by
      simp [ev, evalHOLExact, evalListHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE,
        valueIsWord, valueWord, wordOpHOL, wordOp]
    have hvar_ev : ∀ M (nm : String) (w : BitVec 64),
        s.locals.lookup (ofString nm) = some (.val (.word w)) → ofString "nd" ≠ ofString nm →
        ev (NS s L1 G1 M (s.clock - 1)) (.var .local (ofString nm)) = some (.val (.word w)) :=
      fun _ nm w hlk hne => by
        simp [ev, evalHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE, hlk, hne]
    refine Ret.ns_storeW (hp + 0#64) 1#64 (hnd_ev _ _) rfl fun _ => ?_
    refine Ret.ns_storeW (hp + 8#64) 0#64 (hnd_ev _ _) rfl fun _ => ?_
    refine Ret.ns_storeW (hp + 16#64) 0#64 (hnd_ev _ _) rfl fun _ => ?_
    refine Ret.ns_storeW (hp + 24#64) 0#64 (hnd_ev _ _) rfl fun _ => ?_
    refine Ret.ns_storeW (hp + 32#64) w0 (hnd_ev _ _) (hvar_ev _ "nib" w0 hw0 (by decide)) fun _ => ?_
    refine Ret.ns_storeW (hp + 40#64) w1 (hnd_ev _ _) (hvar_ev _ "nlen" w1 hw1 (by decide)) fun _ => ?_
    refine Ret.ns_storeW (hp + 48#64) w2 (hnd_ev _ _) (hvar_ev _ "vptr" w2 hw2 (by decide)) fun _ => ?_
    refine Ret.ns_storeW (hp + 56#64) w3 (hnd_ev _ _) (hvar_ev _ "vlen" w3 hw3 (by decide)) fun _ => ?_
    refine Ret.ns_ret fun val hval => ?_
    have hv : val = .val (.word hp) := by
      simp [ev, evalHOLExact, L1, HolFiniteMapExact.lookup_update, FUPDATE] at hval; exact hval.symm
    subst hv
    refine ⟨hp, rfl, ?_⟩
    set M8 := updW (updW (updW (updW (updW (updW (updW (updW s.memory
      (hp + 0#64) 1#64) (hp + 8#64) 0#64) (hp + 16#64) 0#64) (hp + 24#64) 0#64)
      (hp + 32#64) w0) (hp + 40#64) w1) (hp + 48#64) w2) (hp + 56#64) w3
    let post : PanSemStateFiniteExact 64 F :=
      { (NS s (emptyLocalsHOLFinite (NS s L1 G1 M8 (s.clock - 1))).locals G1 M8 (s.clock - 1)) with
        locals := HolFiniteMapExact.resVarEq
          (NS s (emptyLocalsHOLFinite (NS s L1 G1 M8 (s.clock - 1))).locals G1 M8 (s.clock - 1)).locals
          (ofString "nd", s.locals.lookup (ofString "nd")) }
    change ArenaReady post ∧ AllocatorGrows s post ∧ FreshBlock s post hp.toNat 64
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hA.2.1
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
    obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q⟩ :=
      R10Shards.P02.alloc_arith hp 64#64 hhp_hi hhp_al hcmp1 hcmp2
    change q.toNat = _ at hq_eq
    change q.toNat ≤ heapLimit at hq_hi
    change q.toNat % 8 = 0 at hq_al
    change hp.toNat ≤ q.toNat at hp_le_q
    have h64 : ((64#64).toNat + 7) / 8 * 8 = 64 := by decide
    have h64' : (64 + 7) / 8 * 8 = 64 := by decide
    rw [h64] at hq_eq
    have hpost_hp : globN post "heap_ptr" = q.toNat := by
      simp [post, NS, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE]
    have hpost_fp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
      simp [post, NS, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
    have hpost_sp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
      simp [post, NS, G1, globN, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
    have hG_post : GuestInv post := ⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩
    have hsb_le : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hA.1
    have hlim_le_he : heapLimit ≤ heapEnd := by decide
    have hA_post : ArenaOK post := by
      unfold ArenaOK
      rw [hpost_hp, hpost_fp, hpost_sp]
      refine ⟨by omega, hq_hi, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hq_al, hA.2.2.2.2.2.2.1,
        hA.2.2.2.2.2.2.2.1,
        globalsWord_update (s := s) (t := post) (ofString "heap_ptr") q rfl hA.2.2.2.2.2.2.2.2⟩
    refine ⟨⟨hG_post, hA_post⟩, ⟨by rw [hpost_hp, ← hhp_eq]; exact hp_le_q, by rw [hpost_sp]⟩,
      hhp_al, ⟨by rw [← hhp_eq], by dsimp only; rw [hpost_hp, h64', hq_eq]⟩, ?_⟩
    rw [h64']
    exact Wave8Contracts.M26.wordsOK_of_guestInv post hG_post hp.toNat 64 hhp_al (by decide)
      hsb_le (by omega)
  exact hrun v hret

/-! ## Section 4: Exact Store-Sequence Helpers for `_decode_step` -/

private theorem updW_eq_ds {m : BitVec 64 → HolWordLab 64} {a w : BitVec 64} :
    updW m a w a = .word w := by
  simp [updW]

private theorem updW_ne_ds {m : BitVec 64 → HolWordLab 64} {a b w : BitVec 64} (h : b ≠ a) :
    updW m a w b = m b := by
  simp [updW, h]

private theorem eval_store_local_off {F : Type}
    (st : PanSemStateFiniteExact 64 F) (baseVar : String) (base : BitVec 64)
    (off : Nat) (valExp : ExpHOL 64) (w : BitVec 64)
    (hbase : st.locals.lookup (ofString baseVar) = some (.val (.word base)))
    (hval : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) valExp =
      some (.val (.word w)))
    (hdom : st.memaddrs (base + BitVec.ofNat 64 off)) :
    evaluateHOLFiniteState st
      (.store (.op .add [.var .local (ofString baseVar), .const (BitVec.ofNat 64 off)]) valExp) =
      (none, { st with memory := updW st.memory (base + BitVec.ofNat 64 off) w }) := by
  rw [evaluateHOLFiniteState_store]
  have hd : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.op .add [.var .local (ofString baseVar), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (base + BitVec.ofNat 64 off))) := by
    simp [evalHOLExact, evalListHOLExact, hbase, valueIsWord, valueWord, wordOpHOL, wordOp]
  rw [hd, hval]
  simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom]
  rfl

private theorem scratch_88_dom_and_add {F : Type}
    (st : PanSemStateFiniteExact 64 F) (recw : BitVec 64)
    (hG : GuestInv st) (hA : ArenaOK st)
    (hfs_al : recw.toNat % 8 = 0)
    (hfs_lo : globN st "frame_mem_ptr" ≤ recw.toNat)
    (hfs_hi : recw.toNat + 88 ≤ scratchEnd) :
    (∀ k : Nat, k ≤ 80 →
      recw + BitVec.ofNat 64 k = BitVec.ofNat 64 (recw.toNat + k) ∧
      (recw + BitVec.ofNat 64 k).toNat = recw.toNat + k) ∧
    (∀ k : Nat, k ≤ 80 → k % 8 = 0 → st.memaddrs (recw + BitVec.ofNat 64 k)) := by
  have hse_lt : scratchEnd < 2 ^ 64 := by decide
  have hsb_le_ss : sourceBase ≤ scratchStart := by decide
  have hse_le_he : scratchEnd ≤ heapEnd := by decide
  have hadd : ∀ k : Nat, k ≤ 80 →
      recw + BitVec.ofNat 64 k = BitVec.ofNat 64 (recw.toNat + k) ∧
      (recw + BitVec.ofNat 64 k).toNat = recw.toNat + k := by
    intro k hk
    have hlt : recw.toNat + k < 2 ^ 64 := by omega
    have heq : recw + BitVec.ofNat 64 k = BitVec.ofNat 64 (recw.toNat + k) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    exact ⟨heq, by rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]⟩
  refine ⟨hadd, fun k hk hk8 => ?_⟩
  rw [hG.memaddrs, (hadd k hk).1]
  have hfmp_lo := hA.2.2.1
  exact Wave8Contracts.M26.ordinaryDomain_of_nat (recw.toNat + k)
    (by omega) (by omega) (by omega)

/-! ## Section 5: `StepFrame` Store & `decCall` Helpers + `ww__decode_step` -/

private theorem stepFrame_store_word {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F}
    (hsf : StepFrame s0 cur) (dstExp valExp : ExpHOL 64)
    (hval : ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      valExp = some v → ∃ w : BitVec 64, v = .val (.word w))
    (hin : ∀ x : BitVec 64,
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp =
        some (.val (.word x)) →
      cur.memaddrs x →
      CellHits x.toNat (globN s0 "frame_mem_ptr", globN s0 "scratch_ptr" - globN s0 "frame_mem_ptr") ∨
      CellHits x.toNat (globN s0 "heap_ptr", heapLimit - globN s0 "heap_ptr")) :
    StepFrame s0 (evaluateHOLFiniteState cur (.store dstExp valExp)).2 := by
  rw [evaluateHOLFiniteState_store]
  rcases hx : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp with _ | dv
  · exact hsf
  · rcases dv with ⟨⟨x⟩⟩ | _ | _ <;> try exact hsf
    rcases hv : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp with _ | val
    · exact hsf
    · obtain ⟨w, rfl⟩ := hval val hv
      by_cases hdom : cur.memaddrs x
      · simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom, ↓reduceIte]
        refine ⟨⟨⟨hsf.1.1.code, hsf.1.1.memaddrs, hsf.1.1.shMemaddrs, hsf.1.1.baseAddr⟩, hsf.1.2⟩,
          hsf.2.1, hsf.2.2.1, hsf.2.2.2.1, ?_, hsf.2.2.2.2.2⟩
        intro a hkeep hfresh
        by_cases hax : a = x
        · subst hax
          rcases hin a hx hdom with hfg | hhf
          · exact absurd hfg (hkeep _ (List.mem_singleton.mpr rfl))
          · exact absurd hhf hfresh
        · simp [Function.update, hax]
          exact hsf.2.2.2.2.1 a hkeep hfresh
      · simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom]
        exact hsf

private theorem stepFrame_seq_step {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (hnt : (evaluateHOLFiniteState cur (.seq a b)).1 ≠ some .timeOut)
    (hfr : FlowsOrResumes (evaluateHOLFiniteState cur (.seq a b)).1)
    (ha : (evaluateHOLFiniteState cur a).1 ≠ some .timeOut →
      FlowsOrResumes (evaluateHOLFiniteState cur a).1 →
      StepFrame s0 (evaluateHOLFiniteState cur a).2)
    (hb : ∀ mid, evaluateHOLFiniteState cur a = (none, mid) →
      StepFrame s0 mid →
      (evaluateHOLFiniteState mid b).1 ≠ some .timeOut →
      FlowsOrResumes (evaluateHOLFiniteState mid b).1 →
      StepFrame s0 (evaluateHOLFiniteState mid b).2) :
    StepFrame s0 (evaluateHOLFiniteState cur (.seq a b)).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hr1 : evaluateHOLFiniteState cur a with ⟨r1, mid⟩
  simp only [hr1] at hnt hfr ⊢
  cases r1 with
  | none =>
    have hsf_mid := ha (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at hsf_mid
    exact hb mid hr1 hsf_mid hnt hfr
  | some _ =>
    have hsf_mid := ha (by rw [hr1]; exact hnt) (by rw [hr1]; exact hfr)
    rw [hr1] at hsf_mid
    exact hsf_mid

private theorem stepFrame_ite_step {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} (cond : ExpHOL 64) {yes no : ProgHOL 64}
    (hsf : StepFrame s0 cur)
    (hnt : (evaluateHOLFiniteState cur (.ite cond yes no)).1 ≠ some .timeOut)
    (hfr : FlowsOrResumes (evaluateHOLFiniteState cur (.ite cond yes no)).1)
    (hy : (evaluateHOLFiniteState cur yes).1 ≠ some .timeOut →
      FlowsOrResumes (evaluateHOLFiniteState cur yes).1 →
      StepFrame s0 (evaluateHOLFiniteState cur yes).2)
    (hn : (evaluateHOLFiniteState cur no).1 ≠ some .timeOut →
      FlowsOrResumes (evaluateHOLFiniteState cur no).1 →
      StepFrame s0 (evaluateHOLFiniteState cur no).2) :
    StepFrame s0 (evaluateHOLFiniteState cur (.ite cond yes no)).2 := by
  rw [evaluateHOLFiniteState_ite] at hnt hfr ⊢
  revert hnt hfr
  split <;> intro hnt hfr
  · split at hnt
    · rename_i hz; simp only [hz, ↓reduceIte] at hfr ⊢; exact hn hnt hfr
    · rename_i hz; simp only [hz, ↓reduceIte] at hfr ⊢; exact hy hnt hfr
  · exact hsf

private theorem stepFrame_dec_step {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F}
    (hsf : StepFrame s0 cur) (name : MlS) (sh : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    (hnt : (evaluateHOLFiniteState cur (.dec name sh init body)).1 ≠ some .timeOut)
    (hfr : FlowsOrResumes (evaluateHOLFiniteState cur (.dec name sh init body)).1)
    (hb : ∀ v,
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) init = some v →
      shapeEqHOL sh (shapeOfHOLExact v) = true →
      (evaluateHOLFiniteState (setVarHOLFinite name v cur) body).1 ≠ some .timeOut →
      FlowsOrResumes (evaluateHOLFiniteState (setVarHOLFinite name v cur) body).1 →
      StepFrame s0 (evaluateHOLFiniteState (setVarHOLFinite name v cur) body).2) :
    StepFrame s0 (evaluateHOLFiniteState cur (.dec name sh init body)).2 := by
  rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
  dsimp only at hnt hfr ⊢
  rcases hv : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) init with _ | v
  · exact hsf
  · simp only [hv] at hnt hfr ⊢
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact v) = true
    · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
      exact stepFrame_locals_clock (hb v hv hsh hnt hfr) _ _
    · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hnt hfr ⊢
      exact hsf

private theorem stepFrame_decCall_ww_step {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {fname : MlS} {gw : List String}
    (hsf : StepFrame s0 cur)
    (hsub : ∀ x ∈ gw, x ∈ ["heap_ptr", "scratch_ptr"])
    (hf : WritesWithin (fun _ => []) gw fname)
    (name : MlS) (sh : ShapeHOL) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hnt : (evaluateHOLFiniteState cur (.decCall name sh fname args cont)).1 ≠ some .timeOut)
    (hfr : FlowsOrResumes (evaluateHOLFiniteState cur (.decCall name sh fname args cont)).1)
    (hcont : ∀ (fbody : ProgHOL 64) (retShape : ShapeHOL)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (vals : List (ValueHOL 64))
      (rv : ValueHOL 64) (cpost : PanSemStateFiniteExact 64 F),
      evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args = some vals →
      lookupCodeHOLFinite cur.code.lookup fname vals = some (fbody, callee, retShape) →
      evaluateHOLFiniteState (callEntryStateHOLFinite cur callee) fbody =
        (some (.returned rv), cpost) →
      shapeEqHOL (shapeOfHOLExact rv) sh = true →
      StepFrame cur cpost →
      let cstate := setVarHOLFinite name rv { cpost with locals := cur.locals }
      StepFrame s0 cstate →
      (evaluateHOLFiniteState cstate cont).1 ≠ some .timeOut →
      FlowsOrResumes (evaluateHOLFiniteState cstate cont).1 →
      StepFrame s0 (evaluateHOLFiniteState cstate cont).2) :
    StepFrame s0 (evaluateHOLFiniteState cur (.decCall name sh fname args cont)).2 := by
  obtain ⟨fparams, fbody, retShape, hlook, hspec⟩ := hf
  have hc : cur.code = originalRuntimeCode := hsf.1.1.code
  rw [evaluateHOLFiniteState_decCall_total] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args with _ | vals
  · exact hsf
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite cur.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact hsf
    · simp only [hl] at hnt hfr ⊢
      have hsame := lookupCodeHOLFinite_installed_body cur.code.lookup fname fparams fbody body'
        retShape ret' vals callee (by rw [hc]; exact hlook) hl
      cases hsame
      have hret_eq := lookupCodeHOLFinite_installed_return cur fname fparams fbody fbody
        retShape ret' vals callee (by rw [hc]; exact hlook) hl
      cases hret_eq
      by_cases hz : cur.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        try dsimp only at hnt hfr ⊢
        rw [fixClockHOLFinite_evaluateState] at hnt hfr ⊢
        let entry := callEntryStateHOLFinite cur callee
        have hARe : ArenaReady entry := localsFree_arenaReady cur callee (cur.clock - 1) hsf.1
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
            some (fbody, entry.locals, retShape) :=
          ⟨vals, by simpa [hc, entry, callEntryStateHOLFinite] using hl⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite cur callee) fbody with ⟨res, post⟩
        simp only [hrun] at hnt hfr ⊢
        cases res with
        | none => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
        | some r =>
          cases r with
          | returned rv =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact rv) sh &&
                shapeEqHOL (shapeOfHOLExact rv) retShape) = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hsh1 : shapeEqHOL (shapeOfHOLExact rv) sh = true := (Bool.and_eq_true _ _ ▸ hsh).1
              obtain ⟨hARp, hhp, hsp, hfo, hgl⟩ := hspec entry hc hARe hex
                (by dsimp only [entry]; rw [hrun]; simp)
                (by dsimp only [entry]; rw [hrun]; exact Or.inl ⟨rv, rfl⟩)
              dsimp only [entry] at hARp hhp hsp hfo hgl
              rw [hrun] at hARp hhp hsp hfo hgl
              have hsf_cur : StepFrame cur post :=
                stepFrame_trans (stepFrame_locals_clock (stepFrame_refl hsf.1) _ _)
                  (stepFrame_of_ww_sub hsub hARp hhp hsp hfo hgl)
              let cstate := setVarHOLFinite name rv { post with locals := cur.locals }
              have hsf_cs : StepFrame s0 cstate :=
                stepFrame_locals_clock (stepFrame_trans hsf hsf_cur) cstate.locals post.clock
              exact stepFrame_locals_clock
                (hcont fbody retShape callee vals rv post hargs hl hrun hsh1 hsf_cur hsf_cs hnt hfr) _ _
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | exception e v =>
            have hres_e : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | hr <;> [simp at h; simp at h; simp at h; exact hr]
            obtain ⟨hARp, hhp, hsp, hfo, hgl⟩ := hspec entry hc hARe hex
              (by dsimp only [entry]; rw [hrun]; simp)
              (by dsimp only [entry]; rw [hrun]; exact hres_e)
            dsimp only [entry] at hARp hhp hsp hfo hgl
            rw [hrun] at hARp hhp hsp hfo hgl
            have hsf_cur : StepFrame cur post :=
              stepFrame_trans (stepFrame_locals_clock (stepFrame_refl hsf.1) _ _)
                (stepFrame_of_ww_sub hsub hARp hhp hsp hfo hgl)
            exact stepFrame_locals_clock (stepFrame_trans hsf hsf_cur) _ post.clock
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

private theorem shape_comb2_words_ds {v : ValueHOL 64}
    (h : shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one]) = true) :
    ∃ a b : BitVec 64, v = .rStruct [.val (.word a), .val (.word b)] := by
  rcases v with _ | fs | _ <;> simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
  rcases fs with _ | ⟨f0, _ | ⟨f1, _ | _⟩⟩ <;>
    simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
  rcases f0 with ⟨⟨i0⟩⟩ | _ | _ <;> rcases f1 with ⟨⟨i1⟩⟩ | _ | _ <;>
    simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
  exact ⟨i0, i1, rfl⟩

private theorem shape_comb3_words_ds {v : ValueHOL 64}
    (h : shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one, .one]) = true) :
    ∃ a b c : BitVec 64, v = .rStruct [.val (.word a), .val (.word b), .val (.word c)] := by
  rcases v with _ | fs | _ <;> simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
  rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | _⟩⟩⟩ <;>
    simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
  rcases f0 with ⟨⟨i0⟩⟩ | _ | _ <;> rcases f1 with ⟨⟨i1⟩⟩ | _ | _ <;>
    rcases f2 with ⟨⟨i2⟩⟩ | _ | _ <;>
    simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
  exact ⟨i0, i1, i2, rfl⟩

/-- `_decode_step` (`Guest/SoftwareAst.lean:10110`): writes only fresh heap and free scratch,
updating at most `heap_ptr` and `scratch_ptr`. -/
theorem «ww__decode_step» :
    WritesWithin (fun _ => []) ["heap_ptr", "scratch_ptr"] (ofString "_decode_step") := by
  refine ⟨_, _, _, lookup__decode_step_ds, ?_⟩
  intro F s hc hAR ⟨vals, hvals⟩ hnt hres
  obtain ⟨_, wp, wn, _, hwp_s, hwn_s⟩ := lookup_three_words_ds hvals
  have store_loc : ∀ {cur nxt : PanSemStateFiniteExact 64 F} {dst src : ExpHOL 64},
      evaluateHOLFiniteState cur (.store dst src) = (none, nxt) → nxt.locals = cur.locals := by
    intro cur nxt dst src hev
    have hcf := (evaluate_store_control_frame cur dst src).2.1
    rwa [hev] at hcf
  have hsf0 : StepFrame s s := stepFrame_refl hAR
  suffices hsf_fin : StepFrame s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__decode_step)).2 from
    stepFrame_to_ww hsf_fin
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn__decode_step,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    List.map, Option.map] at hnt hres ⊢
  refine stepFrame_dec_step hsf0 _ _ _ hnt (Or.inr (Or.inr (Or.inr hres))) (fun vit _ _ hnt1 hfr1 => ?_)
  let s1 := setVarHOLFinite (ofString "it") vit s
  have hsf1 : StepFrame s s1 := stepFrame_locals_clock hsf0 _ _
  refine stepFrame_dec_step hsf1 _ _ _ hnt1 hfr1 (fun ve _ _ hnt2 hfr2 => ?_)
  let s2 := setVarHOLFinite (ofString "e") ve s1
  have hsf2 : StepFrame s s2 := stepFrame_locals_clock hsf1 _ _
  have hs2_p : s2.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hwp_s,
      show ofString "e" ≠ ofString "p" by decide, show ofString "it" ≠ ofString "p" by decide]
  have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word wn)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hwn_s,
      show ofString "e" ≠ ofString "n" by decide, show ofString "it" ≠ ofString "n" by decide]
  -- 1. Handled call to `rlp_decode_fully`
  refine stepFrame_seq_step hnt2 hfr2
    (fun hnt_hc hfr_hc =>
      stepFrame_trans hsf2
        ((StepFlowProg.handledCall_ww hsub_both_ds ww_rlp_decode_fully _ _ _ (by decide)
          (StepFlowProg.call0_ro R11Adapters.ReadOnlyLeaves.«ro_mpt_fail» _) _)
          s2 hsf2.1.1.code hsf2.1 hnt_hc hfr_hc))
    (fun s3 hs3 hsf3 hnt3 hfr3 => ?_)
  have hs3_pn : s3.locals.lookup (ofString "p") = some (.val (.word wp)) ∧
      s3.locals.lookup (ofString "n") = some (.val (.word wn)) := by
    have hk_keeps : ∀ (key : MlS), key ≠ ofString "it" → key ≠ ofString "e" →
        s3.locals.lookup key = s2.locals.lookup key := by
      intro key hne_it hne_e
      rw [evaluateHOLFiniteState_call] at hs3
      revert hs3
      split <;> [simp; (split <;> [simp; (split <;> [simp; skip])])]
      rcases evaluateHOLFiniteState (callEntryStateHOLFinite s2 _) _ with ⟨rc_c, pc_c⟩
      cases rc_c with
      | none => simp
      | some rc_v =>
        cases rc_v with
        | returned rv_c =>
          dsimp only
          split <;> [skip; simp]
          split <;> [skip; simp]
          intro hh; injection hh with _ hs3_eq; subst hs3_eq
          simp [s2, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            Ne.symm hne_it, Ne.symm hne_e]
        | exception exId exVal =>
          dsimp only
          split <;> [skip; simp]
          split <;> [skip; simp]
          split <;> [skip; simp]
          intro hh
          have hfl_h : Flowing (evaluateHOLFiniteState
              (setVarHOLFinite (ofString "e") exVal { pc_c with locals := s2.locals })
              (.call (some (none, none)) (ofString "mpt_fail") [.const 3#64])).1 := by
            rw [hh]; exact Or.inl rfl
          have hav_h := evaluate_avoidsLocal_flowing key _ (by rfl)
            (setVarHOLFinite (ofString "e") exVal { pc_c with locals := s2.locals }) hfl_h
          rw [hh] at hav_h
          exact hav_h.trans (by simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne_e])
        | _ => dsimp only; (repeat' split) <;> simp
    exact ⟨(hk_keeps (ofString "p") (by decide) (by decide)).trans hs2_p,
      (hk_keeps (ofString "n") (by decide) (by decide)).trans hs2_n⟩
  -- 2. `ite (it.0 == 0)`
  refine stepFrame_seq_step hnt3 hfr3
    (fun hnt_i0 hfr_i0 =>
      stepFrame_trans hsf3
        ((StepFlowProg.ite _
          (StepFlowProg.seq
            (StepFlowProg.ite _ (StepFlowProg.ret _) StepFlowProg.skip)
            (StepFlowProg.call0_ro R11Adapters.ReadOnlyLeaves.«ro_mpt_fail» _))
          StepFlowProg.skip) s3 hsf3.1.1.code hsf3.1 hnt_i0 hfr_i0))
    (fun s4 hs4 hsf4 hnt4 hfr4 => ?_)
  have hs4_pn : s4.locals.lookup (ofString "p") = some (.val (.word wp)) ∧
      s4.locals.lookup (ofString "n") = some (.val (.word wn)) := by
    let p_empty : ProgHOL 64 :=
      .ite (.cmp .equal (.rfield 0 (.var .local (ofString "it"))) (.const 0#64))
        (.seq
          (.ite (.cmp .equal (.rfield 2 (.var .local (ofString "it"))) (.const 0#64))
            (.return (.rstruct [.const 0#64, .const 0#64])) .skip)
          (.call (some (none, none)) (ofString "mpt_fail") [.const 4#64]))
        .skip
    have hav_p : avoidsLocal (ofString "p") p_empty = true := rfl
    have hav_n : avoidsLocal (ofString "n") p_empty = true := rfl
    have hfl4 : Flowing (evaluateHOLFiniteState s3 p_empty).1 := by rw [hs4]; exact Or.inl rfl
    have hp4 := evaluate_avoidsLocal_flowing (ofString "p") p_empty hav_p s3 hfl4
    have hn4 := evaluate_avoidsLocal_flowing (ofString "n") p_empty hav_n s3 hfl4
    rw [hs4] at hp4 hn4
    exact ⟨hp4.trans hs3_pn.1, hn4.trans hs3_pn.2⟩
  -- 3. `decCall "sl" (.comb [.one, .one]) "rlp_list_to_slices"`
  refine stepFrame_decCall_ww_step hsf4 hsub_both_ds ww_rlp_list_to_slices (ofString "sl") _ _
    hnt4 hfr4 (fun _ _ _ _ rv_sl cpost_sl _ _ _ hsh_sl _ hsf5 hnt5 hfr5 => ?_)
  obtain ⟨wsl0, wsl1, rfl⟩ := shape_comb2_words_ds hsh_sl
  set s5 := setVarHOLFinite (ofString "sl") (.rStruct [.val (.word wsl0), .val (.word wsl1)])
    { cpost_sl with locals := s4.locals }
  have hs5_p : s5.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    simp [s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_pn.1,
      show ofString "sl" ≠ ofString "p" by decide]
  have hs5_n : s5.locals.lookup (ofString "n") = some (.val (.word wn)) := by
    simp [s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_pn.2,
      show ofString "sl" ≠ ofString "n" by decide]
  -- 4. `dec "arr" .one sl.0`
  refine stepFrame_dec_step hsf5 _ _ _ hnt5 hfr5 (fun varr hvarr _ hnt6 hfr6 => ?_)
  have hvarr_eq : varr = .val (.word wsl0) := by
    have hsl_lk : s5.locals.lookup (ofString "sl") =
        some (.rStruct [.val (.word wsl0), .val (.word wsl1)]) := by
      simp [s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    simp [evalHOLExact, hsl_lk] at hvarr; exact hvarr.symm
  subst hvarr_eq
  let s6 := setVarHOLFinite (ofString "arr") (.val (.word wsl0)) s5
  have hsf6 : StepFrame s s6 := stepFrame_locals_clock hsf5 _ _
  have hs6_arr : s6.locals.lookup (ofString "arr") = some (.val (.word wsl0)) := by
    simp [s6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs6_p : s6.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    simp [s6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs5_p,
      show ofString "arr" ≠ ofString "p" by decide]
  have hs6_n : s6.locals.lookup (ofString "n") = some (.val (.word wn)) := by
    simp [s6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs5_n,
      show ofString "arr" ≠ ofString "n" by decide]
  -- Helper for scratch_alloc(88) + word stores + return
  have hscratch88_hits : ∀ (u0 : PanSemStateFiniteExact 64 F)
      (fbody_sa : ProgHOL 64) (retShape_sa : ShapeHOL)
      (recw : BitVec 64)
      (cpost : PanSemStateFiniteExact 64 F) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (vals_sa : List (ValueHOL 64)),
      StepFrame s u0 →
      evalListHOLFinite u0 (h := fun a => Classical.propDecidable (u0.memaddrs a)) [.const 88#64] = some vals_sa →
      lookupCodeHOLFinite u0.code.lookup (ofString "scratch_alloc") vals_sa =
        some (fbody_sa, callee, retShape_sa) →
      evaluateHOLFiniteState (callEntryStateHOLFinite u0 callee) fbody_sa =
        (some (.returned (.val (.word recw))), cpost) →
      ∀ off : Nat, off ≤ 80 →
        CellHits (recw + BitVec.ofNat 64 off).toNat
          (globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr") := by
    intro u0 fbody_sa retShape_sa recw cpost callee vals_sa hsf_u0 hargs_sa hl_sa hrun_sa off hoff
    have hvals_sa : vals_sa = [.val (.word 88#64)] := by
      rw [evalListHOLFinite_eq_toExact] at hargs_sa
      simpa [evalListHOLExact, evalHOLExact] using hargs_sa.symm
    subst hvals_sa
    obtain ⟨fp_sa, fb_sa, rs_sa, hlook_sa0, hspec_sa0⟩ := rt_scratch_alloc
    have hsame_b := lookupCodeHOLFinite_installed_body u0.code.lookup _ fp_sa fb_sa fbody_sa
      rs_sa retShape_sa _ callee (by rw [hsf_u0.1.1.code]; exact hlook_sa0) hl_sa
    have hsame_r := lookupCodeHOLFinite_installed_return u0 _ fp_sa fb_sa fbody_sa
      rs_sa retShape_sa _ callee (by rw [hsf_u0.1.1.code]; exact hlook_sa0) hl_sa
    cases hsame_b
    cases hsame_r
    let ent_sa := callEntryStateHOLFinite u0 callee
    have hAR_ent : ArenaReady ent_sa := localsFree_arenaReady u0 callee (u0.clock - 1) hsf_u0.1
    have hrt := hspec_sa0 ent_sa hsf_u0.1.1.code hAR_ent
      ⟨[.val (.word 88#64)], by simpa [hsf_u0.1.1.code, ent_sa, callEntryStateHOLFinite] using hl_sa⟩
      (by dsimp only [ent_sa]; rw [hrun_sa]; simp)
      (.val (.word recw))
      (by dsimp only [ent_sa]; rw [hrun_sa])
    dsimp only [ent_sa] at hrt
    rw [hrun_sa] at hrt
    obtain ⟨w_sa, hw_eq, hAR_cp, _, ⟨hfs_al, hfs_lo, hfs_in, _⟩, hsp_cp⟩ := hrt
    injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
    have hn_loc : locN (callEntryStateHOLFinite u0 callee) "n" = 88 := by
      have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup _ [.val (.word 88#64)] _ callee _
        (by rwa [← hsf_u0.1.1.code])
      have h13 : originalRuntimeCode.lookup (ofString "scratch_alloc") =
          some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_scratch_alloc, .one) :=
        lookup_of_guestAst_getElem 13 (by rw [guestAst_len]; decide)
          (extractFn Guest.Software.guestFn_scratch_alloc) rfl
      have heq13 := Option.some.inj (hlook_sa0.symm.trans h13)
      rw [(Prod.mk.inj heq13).1] at hlook_sa0
      simp only [lookupCodeHOLExact, hlook_sa0, shapeOfHOLExact, shapeEqHOL] at hx
      simp at hx
      unfold locN
      dsimp only [callEntryStateHOLFinite]
      rw [← hx.2]
      simp
    rw [hn_loc] at hfs_in
    have h88 : (88 + 7) / 8 * 8 = 88 := by decide
    rw [h88] at hfs_in
    dsimp only [Inside] at hfs_in
    have hfmp_ent : globN (callEntryStateHOLFinite u0 callee) "frame_mem_ptr" = globN s "frame_mem_ptr" :=
      hsf_u0.2.2.1
    have hsp_ent : globN (callEntryStateHOLFinite u0 callee) "scratch_ptr" ≤ globN s "scratch_ptr" :=
      hsf_u0.2.2.2.1
    have hse_lt : scratchEnd < 2 ^ 64 := by decide
    have hsp_s_hi : globN s "scratch_ptr" ≤ scratchEnd := hAR.2.2.2.2.2.1
    have hadd_nat : (recw + BitVec.ofNat 64 off).toNat = recw.toNat + off := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    unfold CellHits
    rw [hadd_nat]
    omega
  -- 5. Sequence of `ite (sl.1 == 2) (...) skip` and branch path
  refine stepFrame_seq_step hnt6 hfr6
    (fun hnt_2 hfr_2 => ?_)
    (fun s_br hs_br hsf_br hnt_br hfr_br => ?_)
  · -- `sl.1 == 2` branch!
    refine stepFrame_ite_step _ hsf6 hnt_2 hfr_2
      (fun hnt_y hfr_y => ?_)
      (fun _ _ => by rw [evaluateHOLFiniteState_skip]; exact hsf6)
    -- `decCall "pi" "rlp_item"`
    refine stepFrame_decCall_ww_step hsf6 hsub_sp_ds R10Shards.P02.ww_rlp_item (ofString "pi") _ _
      hnt_y hfr_y (fun _ _ _ _ rv_pi cpost_pi _ _ _ _ _ hsf_pi hnt_pi hfr_pi => ?_)
    set spi := setVarHOLFinite (ofString "pi") rv_pi { cpost_pi with locals := s6.locals }
    have hspi_arr : spi.locals.lookup (ofString "arr") = some (.val (.word wsl0)) := by
      simp [spi, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs6_arr,
        show ofString "pi" ≠ ofString "arr" by decide]
    have hspi_p : spi.locals.lookup (ofString "p") = some (.val (.word wp)) := by
      simp [spi, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs6_p,
        show ofString "pi" ≠ ofString "p" by decide]
    have hspi_n : spi.locals.lookup (ofString "n") = some (.val (.word wn)) := by
      simp [spi, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs6_n,
        show ofString "pi" ≠ ofString "n" by decide]
    -- `ite (pi.0 != 0) (mpt_fail 5) skip`
    refine stepFrame_seq_step hnt_pi hfr_pi
      (fun hnt_p0 hfr_p0 =>
        stepFrame_trans hsf_pi
          ((StepFlowProg.ite _
            (StepFlowProg.call0_ro R11Adapters.ReadOnlyLeaves.«ro_mpt_fail» _)
            StepFlowProg.skip) spi hsf_pi.1.1.code hsf_pi.1 hnt_p0 hfr_p0))
      (fun spi2 hspi2 hsf_pi2 hnt_pi2 hfr_pi2 => ?_)
    have hspi2_keep : ∀ nm : String, spi2.locals.lookup (ofString nm) = spi.locals.lookup (ofString nm) := by
      intro nm
      let p0Prog : ProgHOL 64 :=
        .ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "pi"))) (.const 0#64))
          (.call (some (none, none)) (ofString "mpt_fail") [.const 5#64]) .skip
      have hav : avoidsLocal (ofString nm) p0Prog = true := by simp [p0Prog, avoidsLocal]
      have hfl : Flowing (evaluateHOLFiniteState spi p0Prog).1 := by rw [hspi2]; exact Or.inl rfl
      have hk := evaluate_avoidsLocal_flowing (ofString nm) p0Prog hav spi hfl
      rwa [hspi2] at hk
    -- `decCall "cn" "compact_to_nibbles"`
    refine stepFrame_decCall_ww_step hsf_pi2 hsub_both_ds ww_compact_to_nibbles (ofString "cn") _ _
      hnt_pi2 hfr_pi2 (fun _ _ _ _ rv_cn cpost_cn _ _ _ hsh_cn _ hsf_cn hnt_cn hfr_cn => ?_)
    obtain ⟨wcn0, wcn1, wcn2, rfl⟩ := shape_comb3_words_ds hsh_cn
    set scn := setVarHOLFinite (ofString "cn")
      (.rStruct [.val (.word wcn0), .val (.word wcn1), .val (.word wcn2)])
      { cpost_cn with locals := spi2.locals }
    have hscn_arr : scn.locals.lookup (ofString "arr") = some (.val (.word wsl0)) := by
      simp [scn, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hspi2_keep "arr", hspi_arr,
        show ofString "cn" ≠ ofString "arr" by decide]
    have hscn_p : scn.locals.lookup (ofString "p") = some (.val (.word wp)) := by
      simp [scn, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hspi2_keep "p", hspi_p,
        show ofString "cn" ≠ ofString "p" by decide]
    have hscn_n : scn.locals.lookup (ofString "n") = some (.val (.word wn)) := by
      simp [scn, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hspi2_keep "n", hspi_n,
        show ofString "cn" ≠ ofString "n" by decide]
    have hscn_cn : scn.locals.lookup (ofString "cn") =
        some (.rStruct [.val (.word wcn0), .val (.word wcn1), .val (.word wcn2)]) := by
      simp [scn, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    -- `seq (ite (cn.2 != 0) (... leaf ...) skip) (... ext ...)`
    refine stepFrame_seq_step hnt_cn hfr_cn
      (fun hnt_lf hfr_lf => ?_)
      (fun sext hsext hsf_ext hnt_ext hfr_ext => ?_)
    · -- Leaf branch (`cn.2 != 0`)
      refine stepFrame_ite_step _ hsf_cn hnt_lf hfr_lf
        (fun hnt_lfy hfr_lfy => ?_)
        (fun _ _ => by rw [evaluateHOLFiniteState_skip]; exact hsf_cn)
      -- `decCall "vi" "rlp_item"`
      refine stepFrame_decCall_ww_step hsf_cn hsub_sp_ds R10Shards.P02.ww_rlp_item (ofString "vi") _ _
        hnt_lfy hfr_lfy (fun _ _ _ _ rv_vi cpost_vi _ _ _ _ _ hsf_vi hnt_vi hfr_vi => ?_)
      set svi := setVarHOLFinite (ofString "vi") rv_vi { cpost_vi with locals := scn.locals }
      have hsvi_p : svi.locals.lookup (ofString "p") = some (.val (.word wp)) := by
        simp [svi, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hscn_p,
          show ofString "vi" ≠ ofString "p" by decide]
      have hsvi_n : svi.locals.lookup (ofString "n") = some (.val (.word wn)) := by
        simp [svi, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hscn_n,
          show ofString "vi" ≠ ofString "n" by decide]
      -- `ite (vi.0 != 0) (mpt_fail 6) skip`
      refine stepFrame_seq_step hnt_vi hfr_vi
        (fun hnt_v0 hfr_v0 =>
          stepFrame_trans hsf_vi
            ((StepFlowProg.ite _
              (StepFlowProg.call0_ro R11Adapters.ReadOnlyLeaves.«ro_mpt_fail» _)
              StepFlowProg.skip) svi hsf_vi.1.1.code hsf_vi.1 hnt_v0 hfr_v0))
        (fun svi2 hsvi2 hsf_vi2 hnt_vi2 hfr_vi2 => ?_)
      have hsvi2_keep : ∀ nm : String, svi2.locals.lookup (ofString nm) = svi.locals.lookup (ofString nm) := by
        intro nm
        let v0Prog : ProgHOL 64 :=
          .ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "vi"))) (.const 0#64))
            (.call (some (none, none)) (ofString "mpt_fail") [.const 6#64]) .skip
        have hav : avoidsLocal (ofString nm) v0Prog = true := by simp [v0Prog, avoidsLocal]
        have hfl : Flowing (evaluateHOLFiniteState svi v0Prog).1 := by rw [hsvi2]; exact Or.inl rfl
        have hk := evaluate_avoidsLocal_flowing (ofString nm) v0Prog hav svi hfl
        rwa [hsvi2] at hk
      -- `decCall "lf" "node_new_leaf"`
      refine stepFrame_decCall_ww_step hsf_vi2 hsub_hp_ds ww_node_new_leaf_ds (ofString "lf") _ _
        hnt_vi2 hfr_vi2 (fun fb_lf rs_lf cal_lf vals_lf rv_lf cpost_lf hargs_lf hl_lf hrun_lf hsh_lf _ hsf_lf hnt_lfk hfr_lfk => ?_)
      obtain ⟨wlf, rfl⟩ := shape_one_word_ds hsh_lf
      set slf := setVarHOLFinite (ofString "lf") (.val (.word wlf)) { cpost_lf with locals := svi2.locals }
      -- Use `rt_node_new_leaf_64` to get `wlf` in fresh heap `[hp_s, heapLimit)`!
      have hlf_hits : ∀ off : Nat, off ≤ 56 →
          CellHits (wlf + BitVec.ofNat 64 off).toNat
            (globN s "heap_ptr", heapLimit - globN s "heap_ptr") := by
        intro off hoff
        obtain ⟨fp_lf, fb_lf0, rs_lf0, hlook_lf0, hspec_lf0⟩ := rt_node_new_leaf_64
        have hsame_b := lookupCodeHOLFinite_installed_body svi2.code.lookup _ fp_lf fb_lf0 fb_lf
          rs_lf0 rs_lf _ cal_lf (by rw [hsf_vi2.1.1.code]; exact hlook_lf0) hl_lf
        have hsame_r := lookupCodeHOLFinite_installed_return svi2 _ fp_lf fb_lf0 fb_lf
          rs_lf0 rs_lf _ cal_lf (by rw [hsf_vi2.1.1.code]; exact hlook_lf0) hl_lf
        cases hsame_b
        cases hsame_r
        let ent_lf := callEntryStateHOLFinite svi2 cal_lf
        have hAR_ent : ArenaReady ent_lf := localsFree_arenaReady svi2 cal_lf (svi2.clock - 1) hsf_vi2.1
        have hrt := hspec_lf0 ent_lf hsf_vi2.1.1.code hAR_ent
          ⟨vals_lf, by simpa [hsf_vi2.1.1.code, ent_lf, callEntryStateHOLFinite] using hl_lf⟩
          (by dsimp only [ent_lf]; rw [hrun_lf]; simp)
          (.val (.word wlf))
          (by dsimp only [ent_lf]; rw [hrun_lf])
        dsimp only [ent_lf] at hrt
        rw [hrun_lf] at hrt
        obtain ⟨w_l, hw_eq, hAR_cp, _, ⟨hlf_al, hlf_in, _⟩⟩ := hrt
        injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
        have h64 : (64 + 7) / 8 * 8 = 64 := by decide
        rw [h64] at hlf_in
        dsimp only [Inside] at hlf_in
        have hhp_ent : globN s "heap_ptr" ≤ globN (callEntryStateHOLFinite svi2 cal_lf) "heap_ptr" :=
          hsf_vi2.2.1
        have hhp_cp_hi : globN cpost_lf "heap_ptr" ≤ heapLimit := hAR_cp.2.2.1
        have hhl_lt : heapLimit < 2 ^ 64 := by decide
        have hadd_nat : (wlf + BitVec.ofNat 64 off).toNat = wlf.toNat + off := by
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        unfold CellHits
        rw [hadd_nat]
        omega
      have hslf_lf : slf.locals.lookup (ofString "lf") = some (.val (.word wlf)) := by
        simp [slf, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hslf_p : slf.locals.lookup (ofString "p") = some (.val (.word wp)) := by
        simp [slf, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsvi2_keep "p", hsvi_p,
          show ofString "lf" ≠ ofString "p" by decide]
      have hslf_n : slf.locals.lookup (ofString "n") = some (.val (.word wn)) := by
        simp [slf, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsvi2_keep "n", hsvi_n,
          show ofString "lf" ≠ ofString "n" by decide]
      refine stepFrame_seq_step hnt_lfk hfr_lfk
        (fun _ _ => stepFrame_store_word hsf_lf _ _
          (fun v hv => by simp [evalHOLExact, hslf_p] at hv; exact ⟨wp, hv.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, hslf_lf, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx; exact Or.inr (hlf_hits 8 (by decide))))
        (fun slf1 hslf1 hsf_lf1 hnt_lfk2 hfr_lfk2 => ?_)
      have hslf1_loc : slf1.locals = slf.locals := store_loc hslf1
      refine stepFrame_seq_step hnt_lfk2 hfr_lfk2
        (fun _ _ => stepFrame_store_word hsf_lf1 _ _
          (fun v hv => by simp [evalHOLExact, hslf1_loc, hslf_n] at hv; exact ⟨wn, hv.symm⟩)
          (fun x hx _ => by
            simp [evalHOLExact, evalListHOLExact, hslf1_loc, hslf_lf, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
            subst hx; exact Or.inr (hlf_hits 16 (by decide))))
        (fun slf2 _ hsf_lf2 hnt_ret hfr_ret =>
          stepFrame_trans hsf_lf2 ((StepFlowProg.ret _) slf2 hsf_lf2.1.1.code hsf_lf2.1 hnt_ret hfr_ret))
    · -- Extension path after `ite (cn.2 != 0) (...) skip`!
      -- Notice if `ite (cn.2 != 0)` flowed to `sext`, it MUST have taken `.skip` (because the then-branch ends in `return` or `mpt_fail`, neither of which flows with `none`!).
      -- Or even simpler: `avoidsLocal` holds for `"arr"`, `"p"`, `"n"`, `"cn"` on the `ite`!
      have hsext_keep : ∀ nm : MlS, nm ≠ ofString "vi" → nm ≠ ofString "lf" →
          sext.locals.lookup nm = scn.locals.lookup nm := by
        intro nm hne1 hne2
        let lfIte : ProgHOL 64 :=
          .ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "cn"))) (.const 0#64))
            (.decCall (ofString "vi") (.comb [.one, .one, .one, .one]) (ofString "rlp_item")
              [.load .one (.op .add [.var .local (ofString "arr"), .panop .mul [.const 1#64, .const 16#64]]),
               .load .one (.op .add [.var .local (ofString "arr"), .panop .mul [.const 1#64, .const 16#64], .const 8#64])]
              (.seq
                (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "vi"))) (.const 0#64))
                  (.call (some (none, none)) (ofString "mpt_fail") [.const 6#64]) .skip)
                (.decCall (ofString "lf") .one (ofString "node_new_leaf")
                  [.rfield 0 (.var .local (ofString "cn")), .rfield 1 (.var .local (ofString "cn")),
                   .rfield 1 (.var .local (ofString "vi")), .rfield 2 (.var .local (ofString "vi"))]
                  (.seq
                    (.store (.op .add [.var .local (ofString "lf"), .const 8#64]) (.var .local (ofString "p")))
                    (.seq
                      (.store (.op .add [.var .local (ofString "lf"), .const 16#64]) (.var .local (ofString "n")))
                      (.return (.rstruct [.const 0#64, .var .local (ofString "lf")])))))))
            .skip
        have hav : avoidsLocal nm lfIte = true := by
          simp [lfIte, avoidsLocal, beq_iff_eq, Ne.symm hne1, Ne.symm hne2]
        have hfl : Flowing (evaluateHOLFiniteState scn lfIte).1 := by rw [hsext]; exact Or.inl rfl
        have hk := evaluate_avoidsLocal_flowing nm lfIte hav scn hfl
        rwa [hsext] at hk
      -- `ite (cn.1 == 0) (mpt_fail 7) skip`
      refine stepFrame_seq_step hnt_ext hfr_ext
        (fun hnt_c1 hfr_c1 =>
          stepFrame_trans hsf_ext
            ((StepFlowProg.ite _
              (StepFlowProg.call0_ro R11Adapters.ReadOnlyLeaves.«ro_mpt_fail» _)
              StepFlowProg.skip) sext hsf_ext.1.1.code hsf_ext.1 hnt_c1 hfr_c1))
        (fun sext2 hsext2 hsf_ext2 hnt_ext2 hfr_ext2 => ?_)
      have hsext2_keep : ∀ nm : String, sext2.locals.lookup (ofString nm) = sext.locals.lookup (ofString nm) := by
        intro nm
        let c1Prog : ProgHOL 64 :=
          .ite (.cmp .equal (.rfield 1 (.var .local (ofString "cn"))) (.const 0#64))
            (.call (some (none, none)) (ofString "mpt_fail") [.const 7#64]) .skip
        have hav : avoidsLocal (ofString nm) c1Prog = true := by simp [c1Prog, avoidsLocal]
        have hfl : Flowing (evaluateHOLFiniteState sext c1Prog).1 := by rw [hsext2]; exact Or.inl rfl
        have hk := evaluate_avoidsLocal_flowing (ofString nm) c1Prog hav sext hfl
        rwa [hsext2] at hk
      -- `decCall "rec" "scratch_alloc" [88]`
      refine stepFrame_decCall_ww_step hsf_ext2 hsub_sp_ds R10Shards.P02.ww_scratch_alloc (ofString "rec") _ _
        hnt_ext2 hfr_ext2 (fun fb_sa rs_sa cal_sa vals_sa rv_rec cpost_sa hargs_sa hl_sa hrun_sa hsh_rec _ hsf_rec hnt_rk hfr_rk => ?_)
      obtain ⟨wrec, rfl⟩ := shape_one_word_ds hsh_rec
      have hrec_hits := hscratch88_hits sext2 fb_sa rs_sa wrec cpost_sa cal_sa vals_sa hsf_ext2 hargs_sa hl_sa hrun_sa
      set srec0 := setVarHOLFinite (ofString "rec") (.val (.word wrec)) { cpost_sa with locals := sext2.locals }
      have hsrec0_rec : srec0.locals.lookup (ofString "rec") = some (.val (.word wrec)) := by
        simp [srec0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hsrec0_arr : srec0.locals.lookup (ofString "arr") = some (.val (.word wsl0)) := by
        simp [srec0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          hsext2_keep "arr", hsext_keep (ofString "arr") (by decide) (by decide), hscn_arr,
          show ofString "rec" ≠ ofString "arr" by decide]
      have hsrec0_p : srec0.locals.lookup (ofString "p") = some (.val (.word wp)) := by
        simp [srec0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          hsext2_keep "p", hsext_keep (ofString "p") (by decide) (by decide), hscn_p,
          show ofString "rec" ≠ ofString "p" by decide]
      have hsrec0_n : srec0.locals.lookup (ofString "n") = some (.val (.word wn)) := by
        simp [srec0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          hsext2_keep "n", hsext_keep (ofString "n") (by decide) (by decide), hscn_n,
          show ofString "rec" ≠ ofString "n" by decide]
      have hsrec0_cn : srec0.locals.lookup (ofString "cn") =
          some (.rStruct [.val (.word wcn0), .val (.word wcn1), .val (.word wcn2)]) := by
        simp [srec0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          hsext2_keep "cn", hsext_keep (ofString "cn") (by decide) (by decide), hscn_cn,
          show ofString "rec" ≠ ofString "cn" by decide]
      have hrec_dst : ∀ (cur : PanSemStateFiniteExact 64 F) (off : Nat),
          cur.locals = srec0.locals → off ≤ 80 →
          ∀ x : BitVec 64,
            @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
              (.op .add [.var .local (ofString "rec"), .const (BitVec.ofNat 64 off)]) =
              some (.val (.word x)) →
            cur.memaddrs x →
            CellHits x.toNat (globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr") ∨
            CellHits x.toNat (globN s "heap_ptr", heapLimit - globN s "heap_ptr") := by
        intro cur off hloc hoff x hx _
        have hlk : cur.locals.lookup (ofString "rec") = some (.val (.word wrec)) := by
          rw [hloc]; exact hsrec0_rec
        simp [evalHOLExact, evalListHOLExact, hlk, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
        subst hx; exact Or.inl (hrec_hits off hoff)
      refine stepFrame_seq_step hnt_rk hfr_rk
        (fun _ _ => stepFrame_store_word hsf_rec _ _
          (fun v hv => by simp [evalHOLExact] at hv; exact ⟨1#64, hv.symm⟩)
          (hrec_dst srec0 8 rfl (by decide)))
        (fun r1 hr1 hsf_r1 hnt_r1 hfr_r1 => ?_)
      have hr1_loc : r1.locals = srec0.locals := store_loc hr1
      refine stepFrame_seq_step hnt_r1 hfr_r1
        (fun _ _ => stepFrame_store_word hsf_r1 _ _
          (fun v hv => by simp [evalHOLExact, hr1_loc, hsrec0_arr] at hv; exact ⟨wsl0, hv.symm⟩)
          (hrec_dst r1 24 hr1_loc (by decide)))
        (fun r2 hr2 hsf_r2 hnt_r2 hfr_r2 => ?_)
      have hr2_loc : r2.locals = srec0.locals := (store_loc hr2).trans hr1_loc
      refine stepFrame_seq_step hnt_r2 hfr_r2
        (fun _ _ => stepFrame_store_word hsf_r2 _ _
          (fun v hv => by simp [evalHOLExact, hr2_loc, hsrec0_p] at hv; exact ⟨wp, hv.symm⟩)
          (hrec_dst r2 48 hr2_loc (by decide)))
        (fun r3 hr3 hsf_r3 hnt_r3 hfr_r3 => ?_)
      have hr3_loc : r3.locals = srec0.locals := (store_loc hr3).trans hr2_loc
      refine stepFrame_seq_step hnt_r3 hfr_r3
        (fun _ _ => stepFrame_store_word hsf_r3 _ _
          (fun v hv => by simp [evalHOLExact, hr3_loc, hsrec0_n] at hv; exact ⟨wn, hv.symm⟩)
          (hrec_dst r3 56 hr3_loc (by decide)))
        (fun r4 hr4 hsf_r4 hnt_r4 hfr_r4 => ?_)
      have hr4_loc : r4.locals = srec0.locals := (store_loc hr4).trans hr3_loc
      refine stepFrame_seq_step hnt_r4 hfr_r4
        (fun _ _ => stepFrame_store_word hsf_r4 _ _
          (fun v hv => by simp [evalHOLExact, hr4_loc, hsrec0_cn] at hv; exact ⟨wcn0, hv.symm⟩)
          (hrec_dst r4 64 hr4_loc (by decide)))
        (fun r5 hr5 hsf_r5 hnt_r5 hfr_r5 => ?_)
      have hr5_loc : r5.locals = srec0.locals := (store_loc hr5).trans hr4_loc
      refine stepFrame_seq_step hnt_r5 hfr_r5
        (fun _ _ => stepFrame_store_word hsf_r5 _ _
          (fun v hv => by simp [evalHOLExact, hr5_loc, hsrec0_cn] at hv; exact ⟨wcn1, hv.symm⟩)
          (hrec_dst r5 72 hr5_loc (by decide)))
        (fun r6 _ hsf_r6 hnt_r6 hfr_r6 =>
          stepFrame_trans hsf_r6 ((StepFlowProg.ret _) r6 hsf_r6.1.1.code hsf_r6.1 hnt_r6 hfr_r6))
  · -- Branch path (`sl.1 == 17`) after `ite (sl.1 == 2) (...) skip`!
    have hsbr_keep : ∀ nm : MlS, nm ≠ ofString "pi" → nm ≠ ofString "cn" → nm ≠ ofString "vi" →
        nm ≠ ofString "lf" → nm ≠ ofString "rec" →
        s_br.locals.lookup nm = s6.locals.lookup nm := by
      intro nm hne1 hne2 hne3 hne4 hne5
      have hk_aux : ∀ {prog : ProgHOL 64},
          evaluateHOLFiniteState s6 prog = (none, s_br) →
          avoidsLocal nm prog = true →
          s_br.locals.lookup nm = s6.locals.lookup nm := by
        intro prog hp hav
        have hfl : Flowing (evaluateHOLFiniteState s6 prog).1 := by rw [hp]; exact Or.inl rfl
        have hk := evaluate_avoidsLocal_flowing nm prog hav s6 hfl
        rwa [hp] at hk
      exact hk_aux hs_br (by simp [avoidsLocal, beq_iff_eq,
        Ne.symm hne1, Ne.symm hne2, Ne.symm hne3, Ne.symm hne4, Ne.symm hne5])
    -- `ite (sl.1 != 17) (mpt_fail 4) skip`
    refine stepFrame_seq_step hnt_br hfr_br
      (fun hnt_17 hfr_17 =>
        stepFrame_trans hsf_br
          ((StepFlowProg.ite _
            (StepFlowProg.call0_ro R11Adapters.ReadOnlyLeaves.«ro_mpt_fail» _)
            StepFlowProg.skip) s_br hsf_br.1.1.code hsf_br.1 hnt_17 hfr_17))
      (fun s_br2 hs_br2 hsf_br2 hnt_br2 hfr_br2 => ?_)
    have hsbr2_keep : ∀ nm : String, s_br2.locals.lookup (ofString nm) = s_br.locals.lookup (ofString nm) := by
      intro nm
      have hk_aux : ∀ {prog : ProgHOL 64},
          evaluateHOLFiniteState s_br prog = (none, s_br2) →
          avoidsLocal (ofString nm) prog = true →
          s_br2.locals.lookup (ofString nm) = s_br.locals.lookup (ofString nm) := by
        intro prog hp hav
        have hfl : Flowing (evaluateHOLFiniteState s_br prog).1 := by rw [hp]; exact Or.inl rfl
        have hk := evaluate_avoidsLocal_flowing (ofString nm) prog hav s_br hfl
        rwa [hp] at hk
      exact hk_aux hs_br2 (by simp [avoidsLocal])
    -- `decCall "br" "node_new_branch" []`
    refine stepFrame_decCall_ww_step hsf_br2 hsub_both_ds ww_node_new_branch_ds (ofString "br") _ _
      hnt_br2 hfr_br2 (fun _ _ _ _ rv_br cpost_br _ _ _ hsh_br _ hsf_nb hnt_nb hfr_nb => ?_)
    obtain ⟨wbr, rfl⟩ := shape_one_word_ds hsh_br
    set snb := setVarHOLFinite (ofString "br") (.val (.word wbr)) { cpost_br with locals := s_br2.locals }
    -- `decCall "rec2" "scratch_alloc" [88]`
    refine stepFrame_decCall_ww_step hsf_nb hsub_sp_ds R10Shards.P02.ww_scratch_alloc (ofString "rec2") _ _
      hnt_nb hfr_nb (fun fb_sa2 rs_sa2 cal_sa2 vals_sa2 rv_rec2 cpost_sa2 hargs_sa2 hl_sa2 hrun_sa2 hsh_rec2 _ hsf_rec2 hnt_r2k hfr_r2k => ?_)
    obtain ⟨wrec2, rfl⟩ := shape_one_word_ds hsh_rec2
    have hrec2_hits := hscratch88_hits snb fb_sa2 rs_sa2 wrec2 cpost_sa2 cal_sa2 vals_sa2 hsf_nb hargs_sa2 hl_sa2 hrun_sa2
    set srec2 := setVarHOLFinite (ofString "rec2") (.val (.word wrec2)) { cpost_sa2 with locals := snb.locals }
    have hsrec2_rec2 : srec2.locals.lookup (ofString "rec2") = some (.val (.word wrec2)) := by
      simp [srec2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hsrec2_br : srec2.locals.lookup (ofString "br") = some (.val (.word wbr)) := by
      simp [srec2, snb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "rec2" ≠ ofString "br" by decide]
    have hsrec2_arr : srec2.locals.lookup (ofString "arr") = some (.val (.word wsl0)) := by
      simp [srec2, snb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hsbr2_keep "arr", hsbr_keep (ofString "arr") (by decide) (by decide) (by decide) (by decide) (by decide), hs6_arr,
        show ofString "rec2" ≠ ofString "arr" by decide, show ofString "br" ≠ ofString "arr" by decide]
    have hsrec2_p : srec2.locals.lookup (ofString "p") = some (.val (.word wp)) := by
      simp [srec2, snb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hsbr2_keep "p", hsbr_keep (ofString "p") (by decide) (by decide) (by decide) (by decide) (by decide), hs6_p,
        show ofString "rec2" ≠ ofString "p" by decide, show ofString "br" ≠ ofString "p" by decide]
    have hsrec2_n : srec2.locals.lookup (ofString "n") = some (.val (.word wn)) := by
      simp [srec2, snb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hsbr2_keep "n", hsbr_keep (ofString "n") (by decide) (by decide) (by decide) (by decide) (by decide), hs6_n,
        show ofString "rec2" ≠ ofString "n" by decide, show ofString "br" ≠ ofString "n" by decide]
    have hrec2_dst : ∀ (cur : PanSemStateFiniteExact 64 F) (off : Nat),
        cur.locals = srec2.locals → off ≤ 80 →
        ∀ x : BitVec 64,
          @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
            (.op .add [.var .local (ofString "rec2"), .const (BitVec.ofNat 64 off)]) =
            some (.val (.word x)) →
          cur.memaddrs x →
          CellHits x.toNat (globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr") ∨
          CellHits x.toNat (globN s "heap_ptr", heapLimit - globN s "heap_ptr") := by
      intro cur off hloc hoff x hx _
      have hlk : cur.locals.lookup (ofString "rec2") = some (.val (.word wrec2)) := by
        rw [hloc]; exact hsrec2_rec2
      simp [evalHOLExact, evalListHOLExact, hlk, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
      subst hx; exact Or.inl (hrec2_hits off hoff)
    refine stepFrame_seq_step hnt_r2k hfr_r2k
      (fun _ _ => stepFrame_store_word hsf_rec2 _ _
        (fun v hv => by simp [evalHOLExact] at hv; exact ⟨2#64, hv.symm⟩)
        (hrec2_dst srec2 8 rfl (by decide)))
      (fun b1 hb1 hsf_b1 hnt_b1 hfr_b1 => ?_)
    have hb1_loc : b1.locals = srec2.locals := store_loc hb1
    refine stepFrame_seq_step hnt_b1 hfr_b1
      (fun _ _ => stepFrame_store_word hsf_b1 _ _
        (fun v hv => by simp [evalHOLExact, hb1_loc, hsrec2_br] at hv; exact ⟨wbr, hv.symm⟩)
        (hrec2_dst b1 16 hb1_loc (by decide)))
      (fun b2 hb2 hsf_b2 hnt_b2 hfr_b2 => ?_)
    have hb2_loc : b2.locals = srec2.locals := (store_loc hb2).trans hb1_loc
    refine stepFrame_seq_step hnt_b2 hfr_b2
      (fun _ _ => stepFrame_store_word hsf_b2 _ _
        (fun v hv => by simp [evalHOLExact, hb2_loc, hsrec2_arr] at hv; exact ⟨wsl0, hv.symm⟩)
        (hrec2_dst b2 24 hb2_loc (by decide)))
      (fun b3 hb3 hsf_b3 hnt_b3 hfr_b3 => ?_)
    have hb3_loc : b3.locals = srec2.locals := (store_loc hb3).trans hb2_loc
    refine stepFrame_seq_step hnt_b3 hfr_b3
      (fun _ _ => stepFrame_store_word hsf_b3 _ _
        (fun v hv => by simp [evalHOLExact] at hv; exact ⟨0#64, hv.symm⟩)
        (hrec2_dst b3 32 hb3_loc (by decide)))
      (fun b4 hb4 hsf_b4 hnt_b4 hfr_b4 => ?_)
    have hb4_loc : b4.locals = srec2.locals := (store_loc hb4).trans hb3_loc
    refine stepFrame_seq_step hnt_b4 hfr_b4
      (fun _ _ => stepFrame_store_word hsf_b4 _ _
        (fun v hv => by simp [evalHOLExact] at hv; exact ⟨0#64, hv.symm⟩)
        (hrec2_dst b4 40 hb4_loc (by decide)))
      (fun b5 hb5 hsf_b5 hnt_b5 hfr_b5 => ?_)
    have hb5_loc : b5.locals = srec2.locals := (store_loc hb5).trans hb4_loc
    refine stepFrame_seq_step hnt_b5 hfr_b5
      (fun _ _ => stepFrame_store_word hsf_b5 _ _
        (fun v hv => by simp [evalHOLExact, hb5_loc, hsrec2_p] at hv; exact ⟨wp, hv.symm⟩)
        (hrec2_dst b5 48 hb5_loc (by decide)))
      (fun b6 hb6 hsf_b6 hnt_b6 hfr_b6 => ?_)
    have hb6_loc : b6.locals = srec2.locals := (store_loc hb6).trans hb5_loc
    refine stepFrame_seq_step hnt_b6 hfr_b6
      (fun _ _ => stepFrame_store_word hsf_b6 _ _
        (fun v hv => by simp [evalHOLExact, hb6_loc, hsrec2_n] at hv; exact ⟨wn, hv.symm⟩)
        (hrec2_dst b6 56 hb6_loc (by decide)))
      (fun b7 _ hsf_b7 hnt_b7 hfr_b7 =>
        stepFrame_trans hsf_b7 ((StepFlowProg.ret _) b7 hsf_b7.1.1.code hsf_b7.1 hnt_b7 hfr_b7))

/-! ## Section 5: `sp__decode_step` (`PushesFrame (ofString "_decode_step")`) -/

private def DecodeExit {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (vpost : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ a b : BitVec 64,
    v = .rStruct [.val (.word a), .val (.word b)] ∧
    (a.toNat = 0 → b.toNat = 0 ∨ FreshBlock s vpost b.toNat 32) ∧
    (a.toNat ≠ 0 →
      FreshScratch s vpost b.toNat 88 ∧
      (memW vpost (b.toNat + 8) = 1 ∨
        (memW vpost (b.toNat + 8) = 2 ∧
          memW vpost (b.toNat + 32) = 0 ∧
          memW vpost (b.toNat + 40) = 0 ∧
          FreshBlock s vpost (memW vpost (b.toNat + 16)) 176)))

private theorem decodeExit_with_locals_clock {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {v : ValueHOL 64}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {C : Nat}
    (h : DecodeExit s v post) :
    DecodeExit s v { post with locals := L, clock := C } := by
  have hFB_lc : ∀ {p n : Nat}, FreshBlock s post p n →
      FreshBlock s { post with locals := L, clock := C } p n := by
    rintro p n ⟨hal, hin, hw0, hw1, hwk⟩
    exact ⟨hal, hin, hw0, hw1, fun k hk => hwk k hk⟩
  have hFS_lc : ∀ {p n : Nat}, FreshScratch s post p n →
      FreshScratch s { post with locals := L, clock := C } p n := by
    rintro p n ⟨hal, hlo, hin, hw0, hw1, hwk⟩
    exact ⟨hal, hlo, hin, hw0, hw1, fun k hk => hwk k hk⟩
  obtain ⟨a, b, rfl, h0, h1⟩ := h
  refine ⟨a, b, rfl, fun ha => ?_, fun ha => ?_⟩
  · rcases h0 ha with hb0 | hfb
    · exact Or.inl hb0
    · exact Or.inr (hFB_lc hfb)
  · obtain ⟨hfs, hor⟩ := h1 ha
    refine ⟨hFS_lc hfs, ?_⟩
    rcases hor with hk1 | ⟨hk2, h32, h40, hfb⟩
    · exact Or.inl hk1
    · exact Or.inr ⟨hk2, h32, h40, hFB_lc hfb⟩

private theorem call0_never_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (f : MlS) (args : List (ExpHOL 64)) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) f args)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨r, _⟩
        rcases r with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp

private theorem ret_call0_no_ret {F : Type}
    {s : PanSemStateFiniteExact 64 F} (f : MlS) (args : List (ExpHOL 64))
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} :
    Ret s (.call (some (none, none)) f args) Φ :=
  fun v hv => False.elim (call0_never_returned s f args v hv)

private theorem ret_handledCall_no_ret {F : Type}
    {s : PanSemStateFiniteExact 64 F} (dv eid evar callee f : MlS)
    (args fargs : List (ExpHOL 64))
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} :
    Ret s (.call (some (some (.local, dv),
      some (eid, evar, .call (some (none, none)) f fargs))) callee args) Φ := by
  intro v hv
  exfalso
  rw [evaluateHOLFiniteState_call] at hv
  revert hv
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ with ⟨r, _⟩
        cases r with
        | none => simp
        | some r' =>
          cases r' with
          | exception exId exVal =>
            dsimp only
            split
            · split
              · try dsimp only
                split
                · intro hv; exact call0_never_returned _ f fargs v hv
                · simp
              · simp
            · simp
          | _ => dsimp only; (repeat' split) <;> simp

private theorem ret_ite_step {F : Type}
    {s : PanSemStateFiniteExact 64 F} (c : ExpHOL 64) {thn els : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (ht : Ret s thn Φ) (he : Ret s els Φ) :
    Ret s (.ite c thn els) Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_ite] at hv ⊢
  revert hv
  split
  · split
    · intro hv; exact he v hv
    · intro hv; exact ht v hv
  · simp

private theorem ret_skip_no_ret {F : Type}
    {s : PanSemStateFiniteExact 64 F}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} :
    Ret s .skip Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_skip] at hv
  cases hv

private theorem ret_dec_step_ds {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F}
    (hsf : StepFrame s0 cur) (name : MlS) (sh : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    (hb : ∀ v,
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) init = some v →
      shapeEqHOL sh (shapeOfHOLExact v) = true →
      StepFrame s0 (setVarHOLFinite name v cur) →
      Ret (setVarHOLFinite name v cur) body (DecodeExit s0)) :
    Ret cur (.dec name sh init body) (DecodeExit s0) := by
  intro rv hret
  rw [evaluateHOLFiniteState_dec_total] at hret ⊢
  dsimp only at hret ⊢
  rcases hv : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) init with _ | v
  · rw [hv] at hret; simp at hret
  · simp only [hv] at hret ⊢
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact v) = true
    · simp only [hsh, ↓reduceIte] at hret ⊢
      have hsf' : StepFrame s0 (setVarHOLFinite name v cur) := stepFrame_locals_clock hsf _ _
      exact decodeExit_with_locals_clock (hb v hv hsh hsf' rv hret)
    · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hret; simp at hret

private theorem ret_seq_step_ds {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (ha_ret : Ret cur a (DecodeExit s0))
    (ha_sf : (evaluateHOLFiniteState cur a).1 = none → StepFrame s0 (evaluateHOLFiniteState cur a).2)
    (hb : ∀ mid, evaluateHOLFiniteState cur a = (none, mid) → StepFrame s0 mid →
      Ret mid b (DecodeExit s0)) :
    Ret cur (.seq a b) (DecodeExit s0) := by
  refine Ret.seq ha_ret ?_
  intro mid hmid
  have hsf_mid : StepFrame s0 mid := by
    have h := ha_sf (by rw [hmid])
    rwa [hmid] at h
  exact hb mid hmid hsf_mid

private theorem ret_decCall_ww_step_ds {F : Type}
    {s0 cur : PanSemStateFiniteExact 64 F} {gw : List String}
    (hsf : StepFrame s0 cur)
    (hsub : ∀ x ∈ gw, x ∈ ["heap_ptr", "scratch_ptr"])
    {fname : MlS} (hf : WritesWithin (fun _ => []) gw fname)
    (name : MlS) (sh : ShapeHOL) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hcont : ∀ fbody retShape callee vals rv cpost,
      evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args = some vals →
      lookupCodeHOLFinite cur.code.lookup fname vals = some (fbody, callee, retShape) →
      evaluateHOLFiniteState (callEntryStateHOLFinite cur callee) fbody = (some (.returned rv), cpost) →
      shapeEqHOL (shapeOfHOLExact rv) sh = true →
      StepFrame cur cpost →
      let cstate := setVarHOLFinite name rv { cpost with locals := cur.locals }
      StepFrame s0 cstate →
      Ret cstate cont (DecodeExit s0)) :
    Ret cur (.decCall name sh fname args cont) (DecodeExit s0) := by
  intro outv hret
  obtain ⟨fparams, fbody, retShape, hlook, hspec⟩ := hf
  have hc : cur.code = originalRuntimeCode := hsf.1.1.code
  rw [evaluateHOLFiniteState_decCall_total] at hret ⊢
  rcases hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) args with _ | vals
  · rw [hargs] at hret; simp at hret
  · simp only [hargs] at hret ⊢
    rcases hl : lookupCodeHOLFinite cur.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hret; simp at hret
    · simp only [hl] at hret ⊢
      have hsame := lookupCodeHOLFinite_installed_body cur.code.lookup fname fparams fbody body'
        retShape ret' vals callee (by rw [hc]; exact hlook) hl
      cases hsame
      have hret_eq := lookupCodeHOLFinite_installed_return cur fname fparams fbody fbody
        retShape ret' vals callee (by rw [hc]; exact hlook) hl
      cases hret_eq
      by_cases hz : cur.clock = 0
      · simp [hz] at hret
      · simp only [hz, ↓reduceIte] at hret ⊢
        try dsimp only at hret ⊢
        rw [fixClockHOLFinite_evaluateState] at hret ⊢
        let entry := callEntryStateHOLFinite cur callee
        have hARe : ArenaReady entry := localsFree_arenaReady cur callee (cur.clock - 1) hsf.1
        have hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup fname vs =
            some (fbody, entry.locals, retShape) :=
          ⟨vals, by simpa [hc, entry, callEntryStateHOLFinite] using hl⟩
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite cur callee) fbody with ⟨res, post⟩
        simp only [hrun] at hret ⊢
        cases res with
        | none => simp at hret
        | some r =>
          cases r with
          | returned rv =>
            dsimp only at hret ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact rv) sh &&
                shapeEqHOL (shapeOfHOLExact rv) retShape) = true
            · simp only [hsh, ↓reduceIte] at hret ⊢
              have hsh1 : shapeEqHOL (shapeOfHOLExact rv) sh = true := (Bool.and_eq_true _ _ ▸ hsh).1
              obtain ⟨hARp, hhp, hsp, hfo, hgl⟩ := hspec entry hc hARe hex
                (by dsimp only [entry]; rw [hrun]; simp)
                (by dsimp only [entry]; rw [hrun]; exact Or.inl ⟨rv, rfl⟩)
              dsimp only [entry] at hARp hhp hsp hfo hgl
              rw [hrun] at hARp hhp hsp hfo hgl
              have hsf_cur : StepFrame cur post :=
                stepFrame_trans (stepFrame_locals_clock (stepFrame_refl hsf.1) _ _)
                  (stepFrame_of_ww_sub hsub hARp hhp hsp hfo hgl)
              let cstate := setVarHOLFinite name rv { post with locals := cur.locals }
              have hsf_cs : StepFrame s0 cstate :=
                stepFrame_locals_clock (stepFrame_trans hsf hsf_cur) cstate.locals post.clock
              exact decodeExit_with_locals_clock
                (hcont fbody retShape callee vals rv post hargs hl hrun hsh1 hsf_cur hsf_cs outv hret)
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hret; simp at hret
          | _ => simp at hret

private theorem memW_updW_self {F : Type}
    {m : BitVec 64 → HolWordLab 64} {s : PanSemStateFiniteExact 64 F}
    {base : BitVec 64} {off : Nat} (w : BitVec 64)
    (hm : s.memory = updW m (base + BitVec.ofNat 64 off) w)
    (hsum : base.toNat + off < 2 ^ 64) :
    memW s (base.toNat + off) = w.toNat := by
  have hbv : BitVec.ofNat 64 (base.toNat + off) = base + BitVec.ofNat 64 off := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_add]
    omega
  unfold memW
  rw [hm, hbv]
  simp [updW]

private theorem memW_updW_other {m : BitVec 64 → HolWordLab 64}
    {base : BitVec 64} {off1 off2 : Nat} (w : BitVec 64)
    (hsum1 : base.toNat + off1 < 2 ^ 64) (hsum2 : base.toNat + off2 < 2 ^ 64)
    (hne : off1 ≠ off2) :
    updW m (base + BitVec.ofNat 64 off2) w (BitVec.ofNat 64 (base.toNat + off1)) =
      m (BitVec.ofNat 64 (base.toNat + off1)) := by
  have hne_bv : BitVec.ofNat 64 (base.toNat + off1) ≠ base + BitVec.ofNat 64 off2 := by
    intro heq
    have := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_add] at this
    omega
  simp [updW, if_neg hne_bv]

private theorem memW_eq_of_memory {F1 F2 : Type}
    {s1 : PanSemStateFiniteExact 64 F1} {s2 : PanSemStateFiniteExact 64 F2} {a : Nat}
    (h : s1.memory (BitVec.ofNat 64 a) = s2.memory (BitVec.ofNat 64 a)) :
    memW s1 a = memW s2 a := by
  unfold memW; rw [h]

private theorem globN_eq_of_globals {F1 F2 : Type}
    {s1 : PanSemStateFiniteExact 64 F1} {s2 : PanSemStateFiniteExact 64 F2}
    (name : String) (h : s1.globals = s2.globals) :
    globN s1 name = globN s2 name := by
  unfold globN; rw [h]

private theorem wordsOK_of_same_guest {F : Type}
    (s : PanSemStateFiniteExact 64 F) (t : PanSemStateFiniteExact 64 F)
    (hc : t.code = s.code) (hm : t.memaddrs = s.memaddrs)
    (hsh : t.shMemaddrs = s.shMemaddrs) (hb : t.baseAddr = s.baseAddr)
    (hG : GuestInv s) (p n : Nat) (hal : p % 8 = 0) (hn8 : n % 8 = 0)
    (hlo : sourceBase ≤ p) (hhi : p + n ≤ heapEnd) :
    WordsOK t (p, n) :=
  Wave8Contracts.M26.wordsOK_of_guestInv t (guestInv_congr hc hm hsh hb hG) p n hal hn8 hlo hhi

/-- `_decode_step` (`Guest/SoftwareAst.lean:10110`): a pushed record is a fresh 88-byte scratch
block tagged 1 or 2, and a completed result is null or a fresh heap node. -/
theorem «sp__decode_step» :
    PushesFrame (ofString "_decode_step") := by
  refine ⟨_, _, _, lookup__decode_step_ds, ?_⟩
  intro F s hc hAR ⟨vals, hvals⟩ _ v hret
  obtain ⟨_, wp, wn, _, hwp_s, hwn_s⟩ := lookup_three_words_ds hvals
  have hsf0 : StepFrame s s := stepFrame_refl hAR
  suffices hR : Ret s (sourceFnBody Guest.Software.guestFn__decode_step) (DecodeExit s) from
    hR v hret
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn__decode_step,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    List.map, Option.map]
  refine ret_dec_step_ds hsf0 _ _ _ (fun vit _ _ hsf1 => ?_)
  set s1 := setVarHOLFinite (ofString "it") vit s
  refine ret_dec_step_ds hsf1 _ _ _ (fun ve _ _ hsf2 => ?_)
  set s2 := setVarHOLFinite (ofString "e") ve s1
  have hs2_p : s2.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hwp_s,
      show ofString "e" ≠ ofString "p" by decide, show ofString "it" ≠ ofString "p" by decide]
  have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word wn)) := by
    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hwn_s,
      show ofString "e" ≠ ofString "n" by decide, show ofString "it" ≠ ofString "n" by decide]
  -- 1. Handled call to `rlp_decode_fully`
  refine ret_seq_step_ds
    (ret_handledCall_no_ret _ _ _ _ _ _ _)
    (fun hnone =>
      stepFrame_trans hsf2
        ((StepFlowProg.handledCall_ww hsub_both_ds ww_rlp_decode_fully _ _ _ (by decide)
          (StepFlowProg.call0_ro R11Adapters.ReadOnlyLeaves.«ro_mpt_fail» _) _)
          s2 hsf2.1.1.code hsf2.1 (by rw [hnone]; simp) (by rw [hnone]; exact Or.inl rfl)))
    (fun s3 hs3 hsf3 => ?_)
  have hs3_pn : s3.locals.lookup (ofString "p") = some (.val (.word wp)) ∧
      s3.locals.lookup (ofString "n") = some (.val (.word wn)) := by
    have hk_keeps : ∀ (key : MlS), key ≠ ofString "it" → key ≠ ofString "e" →
        s3.locals.lookup key = s2.locals.lookup key := by
      intro key hne_it hne_e
      rw [evaluateHOLFiniteState_call] at hs3
      revert hs3
      split <;> [simp; (split <;> [simp; (split <;> [simp; skip])])]
      rcases evaluateHOLFiniteState (callEntryStateHOLFinite s2 _) _ with ⟨rc_c, pc_c⟩
      cases rc_c with
      | none => simp
      | some rc_v =>
        cases rc_v with
        | returned rv_c =>
          dsimp only
          split <;> [skip; simp]
          split <;> [skip; simp]
          intro hh; injection hh with _ hs3_eq; subst hs3_eq
          simp [s2, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            Ne.symm hne_it, Ne.symm hne_e]
        | exception exId exVal =>
          dsimp only
          split <;> [skip; simp]
          split <;> [skip; simp]
          split <;> [skip; simp]
          intro hh
          have hfl_h : Flowing (evaluateHOLFiniteState
              (setVarHOLFinite (ofString "e") exVal { pc_c with locals := s2.locals })
              (.call (some (none, none)) (ofString "mpt_fail") [.const 3#64])).1 := by
            rw [hh]; exact Or.inl rfl
          have hav_h := evaluate_avoidsLocal_flowing key _ (by rfl)
            (setVarHOLFinite (ofString "e") exVal { pc_c with locals := s2.locals }) hfl_h
          rw [hh] at hav_h
          exact hav_h.trans (by simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne_e])
        | _ => dsimp only; (repeat' split) <;> simp
    exact ⟨(hk_keeps (ofString "p") (by decide) (by decide)).trans hs2_p,
      (hk_keeps (ofString "n") (by decide) (by decide)).trans hs2_n⟩
  -- 2. `ite (it.0 == 0)`
  refine ret_seq_step_ds
    (ret_ite_step _
      (Ret.seq
        (ret_ite_step _
          (Ret.ret fun val hval => by
            simp [ev, evalHOLExact, evalListHOLExact] at hval
            subst hval
            exact ⟨0#64, 0#64, rfl, fun _ => Or.inl rfl, fun h => absurd rfl h⟩)
          ret_skip_no_ret)
        (fun _ _ => ret_call0_no_ret _ _))
      ret_skip_no_ret)
    (fun hnone =>
      stepFrame_trans hsf3
        ((StepFlowProg.ite _
          (StepFlowProg.seq
            (StepFlowProg.ite _ (StepFlowProg.ret _) StepFlowProg.skip)
            (StepFlowProg.call0_ro R11Adapters.ReadOnlyLeaves.«ro_mpt_fail» _))
          StepFlowProg.skip) s3 hsf3.1.1.code hsf3.1 (by rw [hnone]; simp) (by rw [hnone]; exact Or.inl rfl)))
    (fun s4 hs4 hsf4 => ?_)
  have hs4_pn : s4.locals.lookup (ofString "p") = some (.val (.word wp)) ∧
      s4.locals.lookup (ofString "n") = some (.val (.word wn)) := by
    let p_empty : ProgHOL 64 :=
      .ite (.cmp .equal (.rfield 0 (.var .local (ofString "it"))) (.const 0#64))
        (.seq
          (.ite (.cmp .equal (.rfield 2 (.var .local (ofString "it"))) (.const 0#64))
            (.return (.rstruct [.const 0#64, .const 0#64])) .skip)
          (.call (some (none, none)) (ofString "mpt_fail") [.const 4#64]))
        .skip
    have hav_p : avoidsLocal (ofString "p") p_empty = true := rfl
    have hav_n : avoidsLocal (ofString "n") p_empty = true := rfl
    have hfl4 : Flowing (evaluateHOLFiniteState s3 p_empty).1 := by rw [hs4]; exact Or.inl rfl
    have hp4 := evaluate_avoidsLocal_flowing (ofString "p") p_empty hav_p s3 hfl4
    have hn4 := evaluate_avoidsLocal_flowing (ofString "n") p_empty hav_n s3 hfl4
    rw [hs4] at hp4 hn4
    exact ⟨hp4.trans hs3_pn.1, hn4.trans hs3_pn.2⟩
  -- 3. `decCall "sl" (.comb [.one, .one]) "rlp_list_to_slices"`
  refine ret_decCall_ww_step_ds hsf4 hsub_both_ds ww_rlp_list_to_slices (ofString "sl") _ _
    (fun _ _ _ _ rv_sl cpost_sl _ _ _ hsh_sl _ hsf5 => ?_)
  obtain ⟨wsl0, wsl1, rfl⟩ := shape_comb2_words_ds hsh_sl
  set s5 := setVarHOLFinite (ofString "sl") (.rStruct [.val (.word wsl0), .val (.word wsl1)])
    { cpost_sl with locals := s4.locals }
  have hs5_p : s5.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    simp [s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_pn.1,
      show ofString "sl" ≠ ofString "p" by decide]
  have hs5_n : s5.locals.lookup (ofString "n") = some (.val (.word wn)) := by
    simp [s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_pn.2,
      show ofString "sl" ≠ ofString "n" by decide]
  -- 4. `dec "arr" .one sl.0`
  refine ret_dec_step_ds hsf5 _ _ _ (fun varr hvarr _ hsf6 => ?_)
  have hvarr_eq : varr = .val (.word wsl0) := by
    have hsl_lk : s5.locals.lookup (ofString "sl") =
        some (.rStruct [.val (.word wsl0), .val (.word wsl1)]) := by
      simp [s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    simp [evalHOLExact, hsl_lk] at hvarr; exact hvarr.symm
  subst hvarr_eq
  set s6 := setVarHOLFinite (ofString "arr") (.val (.word wsl0)) s5
  have hs6_arr : s6.locals.lookup (ofString "arr") = some (.val (.word wsl0)) := by
    simp [s6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs6_p : s6.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    simp [s6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs5_p,
      show ofString "arr" ≠ ofString "p" by decide]
  have hs6_n : s6.locals.lookup (ofString "n") = some (.val (.word wn)) := by
    simp [s6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs5_n,
      show ofString "arr" ≠ ofString "n" by decide]
  -- Shared `scratch_alloc(88)` return-typing helper
  have hscratch88_rt : ∀ (u0 : PanSemStateFiniteExact 64 F)
      (fbody_sa : ProgHOL 64) (retShape_sa : ShapeHOL)
      (recw : BitVec 64)
      (cpost : PanSemStateFiniteExact 64 F) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (vals_sa : List (ValueHOL 64)),
      StepFrame s u0 →
      evalListHOLFinite u0 (h := fun a => Classical.propDecidable (u0.memaddrs a)) [.const 88#64] = some vals_sa →
      lookupCodeHOLFinite u0.code.lookup (ofString "scratch_alloc") vals_sa =
        some (fbody_sa, callee, retShape_sa) →
      evaluateHOLFiniteState (callEntryStateHOLFinite u0 callee) fbody_sa =
        (some (.returned (.val (.word recw))), cpost) →
      recw.toNat % 8 = 0 ∧
      globN s "frame_mem_ptr" ≤ recw.toNat ∧
      Inside (recw.toNat, 88) (globN cpost "scratch_ptr") (globN s "scratch_ptr") ∧
      cpost.memory = u0.memory ∧
      cpost.globals.lookup (ofString "heap_ptr") = u0.globals.lookup (ofString "heap_ptr") := by
    intro u0 fbody_sa retShape_sa recw cpost callee vals_sa hsf_u0 hargs_sa hl_sa hrun_sa
    have hvals_sa : vals_sa = [.val (.word 88#64)] := by
      rw [evalListHOLFinite_eq_toExact] at hargs_sa
      simpa [evalListHOLExact, evalHOLExact] using hargs_sa.symm
    subst hvals_sa
    obtain ⟨fp_sa, fb_sa, rs_sa, hlook_sa0, hspec_sa0⟩ := rt_scratch_alloc
    have hsame_b := lookupCodeHOLFinite_installed_body u0.code.lookup _ fp_sa fb_sa fbody_sa
      rs_sa retShape_sa _ callee (by rw [hsf_u0.1.1.code]; exact hlook_sa0) hl_sa
    have hsame_r := lookupCodeHOLFinite_installed_return u0 _ fp_sa fb_sa fbody_sa
      rs_sa retShape_sa _ callee (by rw [hsf_u0.1.1.code]; exact hlook_sa0) hl_sa
    cases hsame_b
    cases hsame_r
    let ent_sa := callEntryStateHOLFinite u0 callee
    have hAR_ent : ArenaReady ent_sa := localsFree_arenaReady u0 callee (u0.clock - 1) hsf_u0.1
    have hrt := hspec_sa0 ent_sa hsf_u0.1.1.code hAR_ent
      ⟨[.val (.word 88#64)], by simpa [hsf_u0.1.1.code, ent_sa, callEntryStateHOLFinite] using hl_sa⟩
      (by dsimp only [ent_sa]; rw [hrun_sa]; simp)
      (.val (.word recw))
      (by dsimp only [ent_sa]; rw [hrun_sa])
    dsimp only [ent_sa] at hrt
    rw [hrun_sa] at hrt
    obtain ⟨w_sa, hw_eq, _, _, ⟨hfs_al, hfs_lo, hfs_in, _⟩, _⟩ := hrt
    injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
    have h13 : originalRuntimeCode.lookup (ofString "scratch_alloc") =
        some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_scratch_alloc, .one) :=
      lookup_of_guestAst_getElem 13 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_scratch_alloc) rfl
    have heq13 := Option.some.inj (hlook_sa0.symm.trans h13)
    rcases Prod.mk.inj heq13 with ⟨hp13, heq13b⟩
    rcases Prod.mk.inj heq13b with ⟨hb13, _⟩
    subst hp13 hb13
    have hn_lk : ent_sa.locals.lookup (ofString "n") = some (.val (.word 88#64)) := by
      have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup _ [.val (.word 88#64)] _ callee _
        (by rwa [← hsf_u0.1.1.code])
      simp only [lookupCodeHOLExact, hlook_sa0, shapeOfHOLExact, shapeEqHOL] at hx
      simp at hx
      dsimp only [ent_sa, callEntryStateHOLFinite]
      rw [← hx.2]; simp
    have hn_loc : locN (callEntryStateHOLFinite u0 callee) "n" = 88 := by
      unfold locN; exact by rw [hn_lk]; rfl
    rw [hn_loc] at hfs_in
    have h88 : (88 + 7) / 8 * 8 = 88 := by decide
    rw [h88] at hfs_in
    obtain ⟨_, fp_w, sp_w, _, _, hfp_w, _, hsp_w, _⟩ := arenaOK_globals u0 hsf_u0.1.2
    have hrun_ex := Wave8Contracts.M26.scratch_alloc_body_run ent_sa sp_w fp_w 88#64
      hsf_u0.1.1.code hsp_w hfp_w hn_lk (.val (.word recw)) (by dsimp only [ent_sa]; rw [hrun_sa])
    dsimp only [ent_sa] at hrun_ex
    rw [hrun_sa] at hrun_ex
    obtain ⟨_, _, _, hcpost_eq⟩ := hrun_ex
    dsimp only at hcpost_eq hfs_in
    have hcpost_mem : cpost.memory = u0.memory := by rw [hcpost_eq]; rfl
    have hcpost_hp : cpost.globals.lookup (ofString "heap_ptr") = u0.globals.lookup (ofString "heap_ptr") := by
      rw [hcpost_eq]
      simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "scratch_ptr" ≠ ofString "heap_ptr" by decide]
    have hfmp_ent : globN (callEntryStateHOLFinite u0 callee) "frame_mem_ptr" = globN s "frame_mem_ptr" :=
      hsf_u0.2.2.1
    have hsp_ent : globN (callEntryStateHOLFinite u0 callee) "scratch_ptr" ≤ globN s "scratch_ptr" :=
      hsf_u0.2.2.2.1
    dsimp only [Inside] at hfs_in ⊢
    exact ⟨hfs_al, by omega, ⟨hfs_in.1, Nat.le_trans hfs_in.2 hsp_ent⟩, hcpost_mem, hcpost_hp⟩
  -- 5. `seq (ite (sl.1 == 2) (...) skip) (...)`
  refine ret_seq_step_ds
    (ret_ite_step _ ?_ ret_skip_no_ret)
    (fun hnone => ?_)
    (fun s_br hs_br hsf_br => ?_)
  · -- Then-branch of `ite (sl.1 == 2)`
    refine ret_decCall_ww_step_ds hsf6 hsub_sp_ds R10Shards.P02.ww_rlp_item (ofString "pi") _ _
      (fun _ _ _ _ rv_pi cpost_pi _ _ _ _ _ hsf_pi => ?_)
    set spi := setVarHOLFinite (ofString "pi") rv_pi { cpost_pi with locals := s6.locals }
    have hspi_arr : spi.locals.lookup (ofString "arr") = some (.val (.word wsl0)) := by
      simp [spi, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs6_arr,
        show ofString "pi" ≠ ofString "arr" by decide]
    have hspi_p : spi.locals.lookup (ofString "p") = some (.val (.word wp)) := by
      simp [spi, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs6_p,
        show ofString "pi" ≠ ofString "p" by decide]
    have hspi_n : spi.locals.lookup (ofString "n") = some (.val (.word wn)) := by
      simp [spi, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs6_n,
        show ofString "pi" ≠ ofString "n" by decide]
    refine ret_seq_step_ds
      (ret_ite_step _ (ret_call0_no_ret _ _) ret_skip_no_ret)
      (fun hnone =>
        stepFrame_trans hsf_pi
          ((StepFlowProg.ite _
            (StepFlowProg.call0_ro R11Adapters.ReadOnlyLeaves.«ro_mpt_fail» _)
            StepFlowProg.skip) spi hsf_pi.1.1.code hsf_pi.1 (by rw [hnone]; simp) (by rw [hnone]; exact Or.inl rfl)))
      (fun spi2 hspi2 hsf_pi2 => ?_)
    have hspi2_keep : ∀ nm : String, spi2.locals.lookup (ofString nm) = spi.locals.lookup (ofString nm) := by
      intro nm
      let p0Prog : ProgHOL 64 :=
        .ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "pi"))) (.const 0#64))
          (.call (some (none, none)) (ofString "mpt_fail") [.const 5#64]) .skip
      have hav : avoidsLocal (ofString nm) p0Prog = true := by simp [p0Prog, avoidsLocal]
      have hfl : Flowing (evaluateHOLFiniteState spi p0Prog).1 := by rw [hspi2]; exact Or.inl rfl
      have hk := evaluate_avoidsLocal_flowing (ofString nm) p0Prog hav spi hfl
      rwa [hspi2] at hk
    refine ret_decCall_ww_step_ds hsf_pi2 hsub_both_ds ww_compact_to_nibbles (ofString "cn") _ _
      (fun _ _ _ _ rv_cn cpost_cn _ _ _ hsh_cn _ hsf_cn => ?_)
    obtain ⟨wcn0, wcn1, wcn2, rfl⟩ := shape_comb3_words_ds hsh_cn
    set scn := setVarHOLFinite (ofString "cn")
      (.rStruct [.val (.word wcn0), .val (.word wcn1), .val (.word wcn2)])
      { cpost_cn with locals := spi2.locals }
    have hscn_arr : scn.locals.lookup (ofString "arr") = some (.val (.word wsl0)) := by
      simp [scn, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hspi2_keep "arr", hspi_arr,
        show ofString "cn" ≠ ofString "arr" by decide]
    have hscn_p : scn.locals.lookup (ofString "p") = some (.val (.word wp)) := by
      simp [scn, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hspi2_keep "p", hspi_p,
        show ofString "cn" ≠ ofString "p" by decide]
    have hscn_n : scn.locals.lookup (ofString "n") = some (.val (.word wn)) := by
      simp [scn, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hspi2_keep "n", hspi_n,
        show ofString "cn" ≠ ofString "n" by decide]
    have hscn_cn : scn.locals.lookup (ofString "cn") =
        some (.rStruct [.val (.word wcn0), .val (.word wcn1), .val (.word wcn2)]) := by
      simp [scn, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    refine ret_seq_step_ds
      (ret_ite_step _ ?_ ret_skip_no_ret)
      (fun hnone => ?_)
      (fun sext hsext hsf_ext => ?_)
    · -- Leaf branch (`cn.2 != 0`)
      refine ret_decCall_ww_step_ds hsf_cn hsub_sp_ds R10Shards.P02.ww_rlp_item (ofString "vi") _ _
        (fun _ _ _ _ rv_vi cpost_vi _ _ _ _ _ hsf_vi => ?_)
      set svi := setVarHOLFinite (ofString "vi") rv_vi { cpost_vi with locals := scn.locals }
      have hsvi_p : svi.locals.lookup (ofString "p") = some (.val (.word wp)) := by
        simp [svi, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hscn_p,
          show ofString "vi" ≠ ofString "p" by decide]
      have hsvi_n : svi.locals.lookup (ofString "n") = some (.val (.word wn)) := by
        simp [svi, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hscn_n,
          show ofString "vi" ≠ ofString "n" by decide]
      refine ret_seq_step_ds
        (ret_ite_step _ (ret_call0_no_ret _ _) ret_skip_no_ret)
        (fun hnone =>
          stepFrame_trans hsf_vi
            ((StepFlowProg.ite _
              (StepFlowProg.call0_ro R11Adapters.ReadOnlyLeaves.«ro_mpt_fail» _)
              StepFlowProg.skip) svi hsf_vi.1.1.code hsf_vi.1 (by rw [hnone]; simp) (by rw [hnone]; exact Or.inl rfl)))
        (fun svi2 hsvi2 hsf_vi2 => ?_)
      have hsvi2_keep : ∀ nm : String, svi2.locals.lookup (ofString nm) = svi.locals.lookup (ofString nm) := by
        intro nm
        let v0Prog : ProgHOL 64 :=
          .ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "vi"))) (.const 0#64))
            (.call (some (none, none)) (ofString "mpt_fail") [.const 6#64]) .skip
        have hav : avoidsLocal (ofString nm) v0Prog = true := by simp [v0Prog, avoidsLocal]
        have hfl : Flowing (evaluateHOLFiniteState svi v0Prog).1 := by rw [hsvi2]; exact Or.inl rfl
        have hk := evaluate_avoidsLocal_flowing (ofString nm) v0Prog hav svi hfl
        rwa [hsvi2] at hk
      refine ret_decCall_ww_step_ds hsf_vi2 hsub_hp_ds ww_node_new_leaf_ds (ofString "lf") _ _
        (fun fb_lf rs_lf cal_lf vals_lf rv_lf cpost_lf _ hl_lf hrun_lf hsh_lf _ hsf_lf => ?_)
      obtain ⟨wlf, rfl⟩ := shape_one_word_ds hsh_lf
      set slf := setVarHOLFinite (ofString "lf") (.val (.word wlf)) { cpost_lf with locals := svi2.locals }
      have hlf_fb : wlf.toNat % 8 = 0 ∧
          Inside (wlf.toNat, 64) (globN s "heap_ptr") (globN cpost_lf "heap_ptr") := by
        obtain ⟨fp_lf, fb_lf0, rs_lf0, hlook_lf0, hspec_lf0⟩ := rt_node_new_leaf_64
        have hsame_b := lookupCodeHOLFinite_installed_body svi2.code.lookup _ fp_lf fb_lf0 fb_lf
          rs_lf0 rs_lf _ cal_lf (by rw [hsf_vi2.1.1.code]; exact hlook_lf0) hl_lf
        have hsame_r := lookupCodeHOLFinite_installed_return svi2 _ fp_lf fb_lf0 fb_lf
          rs_lf0 rs_lf _ cal_lf (by rw [hsf_vi2.1.1.code]; exact hlook_lf0) hl_lf
        cases hsame_b
        cases hsame_r
        let ent_lf := callEntryStateHOLFinite svi2 cal_lf
        have hAR_ent : ArenaReady ent_lf := localsFree_arenaReady svi2 cal_lf (svi2.clock - 1) hsf_vi2.1
        have hrt := hspec_lf0 ent_lf hsf_vi2.1.1.code hAR_ent
          ⟨vals_lf, by simpa [hsf_vi2.1.1.code, ent_lf, callEntryStateHOLFinite] using hl_lf⟩
          (by dsimp only [ent_lf]; rw [hrun_lf]; simp)
          (.val (.word wlf))
          (by dsimp only [ent_lf]; rw [hrun_lf])
        dsimp only [ent_lf] at hrt
        rw [hrun_lf] at hrt
        obtain ⟨w_l, hw_eq, _, _, ⟨hlf_al, hlf_in, _⟩⟩ := hrt
        injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
        have h64 : (64 + 7) / 8 * 8 = 64 := by decide
        rw [h64] at hlf_in
        dsimp only [Inside] at hlf_in ⊢
        have hhp_ent : globN s "heap_ptr" ≤ globN (callEntryStateHOLFinite svi2 cal_lf) "heap_ptr" :=
          hsf_vi2.2.1
        exact ⟨hlf_al, ⟨Nat.le_trans hhp_ent hlf_in.1, hlf_in.2⟩⟩
      have hslf_lf : slf.locals.lookup (ofString "lf") = some (.val (.word wlf)) := by
        simp [slf, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hslf_p : slf.locals.lookup (ofString "p") = some (.val (.word wp)) := by
        simp [slf, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsvi2_keep "p", hsvi_p,
          show ofString "lf" ≠ ofString "p" by decide]
      have hslf_n : slf.locals.lookup (ofString "n") = some (.val (.word wn)) := by
        simp [slf, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsvi2_keep "n", hsvi_n,
          show ofString "lf" ≠ ofString "n" by decide]
      apply Ret.of_NS
      refine Ret.ns_storeW (wlf + 8#64) wp
        (by simp [ev, evalHOLExact, evalListHOLExact, hslf_lf, wordOpHOL, wordOp, valueIsWord, valueWord])
        (by simp [ev, evalHOLExact, hslf_p]) (fun _ => ?_)
      refine Ret.ns_storeW (wlf + 16#64) wn
        (by simp [ev, evalHOLExact, evalListHOLExact, hslf_lf, wordOpHOL, wordOp, valueIsWord, valueWord])
        (by simp [ev, evalHOLExact, hslf_n]) (fun _ => ?_)
      refine Ret.ns_ret (fun val hval => ?_)
      simp [ev, evalHOLExact, evalListHOLExact, hslf_lf] at hval
      subst hval
      refine ⟨0#64, wlf, rfl, fun _ => Or.inr ?_, fun h => absurd rfl h⟩
      have h32 : (32 + 7) / 8 * 8 = 32 := by decide
      have hsb_le : sourceBase ≤ wlf.toNat := by
        have := hAR.2.1; dsimp only [Inside] at hlf_fb; omega
      have hhi_le : wlf.toNat + 32 ≤ heapEnd := by
        have := hsf_lf.1.2.2.1
        have hhl_he : heapLimit ≤ heapEnd := by decide
        dsimp only [Inside] at hlf_fb
        have hhp_slf : globN slf "heap_ptr" = globN cpost_lf "heap_ptr" := rfl
        omega
      refine ⟨hlf_fb.1, ?_, ?_⟩
      · rw [h32]
        rw [Inside, show globN (NS slf (emptyLocalsHOLFinite _).locals slf.globals _ slf.clock) "heap_ptr" = globN cpost_lf "heap_ptr" from rfl]
        dsimp only [Inside] at hlf_fb
        omega
      · rw [h32]
        exact wordsOK_of_same_guest slf
          (NS slf (NS slf slf.locals slf.globals (updW (updW slf.memory (wlf + 8#64) wp) (wlf + 16#64) wn) slf.clock).emptyLocalsHOLFinite.locals slf.globals (updW (updW slf.memory (wlf + 8#64) wp) (wlf + 16#64) wn) slf.clock)
          rfl rfl rfl rfl hsf_lf.1.1 wlf.toNat 32 hlf_fb.1 (by decide) hsb_le hhi_le
    · -- `ite (cn.2 != 0)` flowed with `none`
      rw [evaluateHOLFiniteState_ite] at hnone ⊢
      revert hnone
      split
      · split
        · intro _; rw [evaluateHOLFiniteState_skip]; exact hsf_cn
        · intro hnone_thn
          exfalso
          rw [evaluateHOLFiniteState_decCall_total] at hnone_thn
          revert hnone_thn
          split <;> [simp; skip]
          try dsimp only
          split <;> [simp; skip]
          try dsimp only
          split <;> [simp; skip]
          rw [fixClockHOLFinite_evaluateState]
          rcases evaluateHOLFiniteState _ _ with ⟨r_v, _⟩
          cases r_v with
          | none => simp
          | some rv' =>
            cases rv' with
            | returned _ =>
              dsimp only
              split <;> [skip; simp]
              rw [evaluateHOLFiniteState_seq_line780]
              rcases evaluateHOLFiniteState _ _ with ⟨r_i, _⟩
              cases r_i with
              | some _ => simp
              | none =>
                dsimp only
                rw [evaluateHOLFiniteState_decCall_total]
                split <;> [simp; skip]
                try dsimp only
                split <;> [simp; skip]
                try dsimp only
                split <;> [simp; skip]
                rw [fixClockHOLFinite_evaluateState]
                rcases evaluateHOLFiniteState _ _ with ⟨r_l, _⟩
                cases r_l with
                | none => simp
                | some rl' =>
                  cases rl' with
                  | returned _ =>
                    dsimp only
                    split <;> [skip; simp]
                    rw [evaluateHOLFiniteState_seq_line780]
                    rcases evaluateHOLFiniteState _ _ with ⟨rs1, _⟩
                    cases rs1 with
                    | some _ => simp
                    | none =>
                      dsimp only
                      rw [evaluateHOLFiniteState_seq_line780]
                      rcases evaluateHOLFiniteState _ _ with ⟨rs2, ts2⟩
                      cases rs2 with
                      | some _ => simp
                      | none =>
                        dsimp only
                        rw [evaluateHOLFiniteState_return]
                        split <;> [simp; (split <;> simp)]
                  | _ => simp
            | _ => simp
      · simp
    · -- Extension path (`sext`)
      have hsext_keep : ∀ nm : MlS, nm ≠ ofString "vi" → nm ≠ ofString "lf" →
          sext.locals.lookup nm = scn.locals.lookup nm := by
        intro nm hne1 hne2
        let lfIte : ProgHOL 64 :=
          .ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "cn"))) (.const 0#64))
            (.decCall (ofString "vi") (.comb [.one, .one, .one, .one]) (ofString "rlp_item")
              [.load .one (.op .add [.var .local (ofString "arr"), .panop .mul [.const 1#64, .const 16#64]]),
               .load .one (.op .add [.var .local (ofString "arr"), .panop .mul [.const 1#64, .const 16#64], .const 8#64])]
              (.seq
                (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "vi"))) (.const 0#64))
                  (.call (some (none, none)) (ofString "mpt_fail") [.const 6#64]) .skip)
                (.decCall (ofString "lf") .one (ofString "node_new_leaf")
                  [.rfield 0 (.var .local (ofString "cn")), .rfield 1 (.var .local (ofString "cn")),
                   .rfield 1 (.var .local (ofString "vi")), .rfield 2 (.var .local (ofString "vi"))]
                  (.seq
                    (.store (.op .add [.var .local (ofString "lf"), .const 8#64]) (.var .local (ofString "p")))
                    (.seq
                      (.store (.op .add [.var .local (ofString "lf"), .const 16#64]) (.var .local (ofString "n")))
                      (.return (.rstruct [.const 0#64, .var .local (ofString "lf")])))))))
            .skip
        have hav : avoidsLocal nm lfIte = true := by
          simp [lfIte, avoidsLocal, beq_iff_eq, Ne.symm hne1, Ne.symm hne2]
        have hfl : Flowing (evaluateHOLFiniteState scn lfIte).1 := by rw [hsext]; exact Or.inl rfl
        have hk := evaluate_avoidsLocal_flowing nm lfIte hav scn hfl
        rwa [hsext] at hk
      refine ret_seq_step_ds
        (ret_ite_step _ (ret_call0_no_ret _ _) ret_skip_no_ret)
        (fun hnone =>
          stepFrame_trans hsf_ext
            ((StepFlowProg.ite _
              (StepFlowProg.call0_ro R11Adapters.ReadOnlyLeaves.«ro_mpt_fail» _)
              StepFlowProg.skip) sext hsf_ext.1.1.code hsf_ext.1 (by rw [hnone]; simp) (by rw [hnone]; exact Or.inl rfl)))
        (fun sext2 hsext2 hsf_ext2 => ?_)
      have hsext2_keep : ∀ nm : String, sext2.locals.lookup (ofString nm) = sext.locals.lookup (ofString nm) := by
        intro nm
        let c1Prog : ProgHOL 64 :=
          .ite (.cmp .equal (.rfield 1 (.var .local (ofString "cn"))) (.const 0#64))
            (.call (some (none, none)) (ofString "mpt_fail") [.const 7#64]) .skip
        have hav : avoidsLocal (ofString nm) c1Prog = true := by simp [c1Prog, avoidsLocal]
        have hfl : Flowing (evaluateHOLFiniteState sext c1Prog).1 := by rw [hsext2]; exact Or.inl rfl
        have hk := evaluate_avoidsLocal_flowing (ofString nm) c1Prog hav sext hfl
        rwa [hsext2] at hk
      refine ret_decCall_ww_step_ds hsf_ext2 hsub_sp_ds R10Shards.P02.ww_scratch_alloc (ofString "rec") _ _
        (fun fb_sa rs_sa cal_sa vals_sa rv_rec cpost_sa hargs_sa hl_sa hrun_sa hsh_rec _ hsf_rec => ?_)
      obtain ⟨wrec, rfl⟩ := shape_one_word_ds hsh_rec
      obtain ⟨hrec_al, hrec_lo, hrec_in, _, _⟩ :=
        hscratch88_rt sext2 fb_sa rs_sa wrec cpost_sa cal_sa vals_sa hsf_ext2 hargs_sa hl_sa hrun_sa
      set srec0 := setVarHOLFinite (ofString "rec") (.val (.word wrec)) { cpost_sa with locals := sext2.locals }
      have hsrec0_rec : srec0.locals.lookup (ofString "rec") = some (.val (.word wrec)) := by
        simp [srec0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hsrec0_arr : srec0.locals.lookup (ofString "arr") = some (.val (.word wsl0)) := by
        simp [srec0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          hsext2_keep "arr", hsext_keep (ofString "arr") (by decide) (by decide), hscn_arr,
          show ofString "rec" ≠ ofString "arr" by decide]
      have hsrec0_p : srec0.locals.lookup (ofString "p") = some (.val (.word wp)) := by
        simp [srec0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          hsext2_keep "p", hsext_keep (ofString "p") (by decide) (by decide), hscn_p,
          show ofString "rec" ≠ ofString "p" by decide]
      have hsrec0_n : srec0.locals.lookup (ofString "n") = some (.val (.word wn)) := by
        simp [srec0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          hsext2_keep "n", hsext_keep (ofString "n") (by decide) (by decide), hscn_n,
          show ofString "rec" ≠ ofString "n" by decide]
      have hsrec0_cn : srec0.locals.lookup (ofString "cn") =
          some (.rStruct [.val (.word wcn0), .val (.word wcn1), .val (.word wcn2)]) := by
        simp [srec0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          hsext2_keep "cn", hsext_keep (ofString "cn") (by decide) (by decide), hscn_cn,
          show ofString "rec" ≠ ofString "cn" by decide]
      apply Ret.of_NS
      refine Ret.ns_storeW (wrec + 8#64) 1#64
        (by simp [ev, evalHOLExact, evalListHOLExact, hsrec0_rec, wordOpHOL, wordOp, valueIsWord, valueWord])
        (by rfl) (fun _ => ?_)
      refine Ret.ns_storeW (wrec + 24#64) wsl0
        (by simp [ev, evalHOLExact, evalListHOLExact, hsrec0_rec, wordOpHOL, wordOp, valueIsWord, valueWord])
        (by simp [ev, evalHOLExact, hsrec0_arr]) (fun _ => ?_)
      refine Ret.ns_storeW (wrec + 48#64) wp
        (by simp [ev, evalHOLExact, evalListHOLExact, hsrec0_rec, wordOpHOL, wordOp, valueIsWord, valueWord])
        (by simp [ev, evalHOLExact, hsrec0_p]) (fun _ => ?_)
      refine Ret.ns_storeW (wrec + 56#64) wn
        (by simp [ev, evalHOLExact, evalListHOLExact, hsrec0_rec, wordOpHOL, wordOp, valueIsWord, valueWord])
        (by simp [ev, evalHOLExact, hsrec0_n]) (fun _ => ?_)
      refine Ret.ns_storeW (wrec + 64#64) wcn0
        (by simp [ev, evalHOLExact, evalListHOLExact, hsrec0_rec, wordOpHOL, wordOp, valueIsWord, valueWord])
        (by simp [ev, evalHOLExact, hsrec0_cn]) (fun _ => ?_)
      refine Ret.ns_storeW (wrec + 72#64) wcn1
        (by simp [ev, evalHOLExact, evalListHOLExact, hsrec0_rec, wordOpHOL, wordOp, valueIsWord, valueWord])
        (by simp [ev, evalHOLExact, hsrec0_cn]) (fun _ => ?_)
      refine Ret.ns_ret (fun val hval => ?_)
      simp [ev, evalHOLExact, evalListHOLExact, hsrec0_rec] at hval
      subst hval
      refine ⟨1#64, wrec, rfl, fun h => by simp at h, fun _ => ?_⟩
      have h88 : (88 + 7) / 8 * 8 = 88 := by decide
      have hse_lt : scratchEnd < 2 ^ 64 := by decide
      have hsp_s_hi : globN s "scratch_ptr" ≤ scratchEnd := hAR.2.2.2.2.2.1
      have hrec_lt : wrec.toNat + 88 ≤ scratchEnd := by
        dsimp only [Inside] at hrec_in; omega
      have hsb_le : sourceBase ≤ wrec.toNat := by
        have hss : sourceBase ≤ scratchStart := by decide
        have := hAR.2.2.2.1
        omega
      have hhi_le : wrec.toNat + 88 ≤ heapEnd := by
        have hhe : scratchEnd ≤ heapEnd := by decide
        omega
      refine ⟨⟨hrec_al, hrec_lo, ?_, ?_⟩, Or.inl ?_⟩
      · rw [h88]
        rw [Inside, show globN (NS srec0 (emptyLocalsHOLFinite _).locals srec0.globals _ srec0.clock) "scratch_ptr" = globN cpost_sa "scratch_ptr" from rfl]
        exact hrec_in
      · rw [h88]
        let m1 := updW (updW (updW (updW (updW (updW srec0.memory (wrec + 8#64) 1#64) (wrec + 24#64) wsl0) (wrec + 48#64) wp) (wrec + 56#64) wn) (wrec + 64#64) wcn0) (wrec + 72#64) wcn1
        exact wordsOK_of_same_guest srec0
          (NS srec0 (NS srec0 srec0.locals srec0.globals m1 srec0.clock).emptyLocalsHOLFinite.locals srec0.globals m1 srec0.clock)
          rfl rfl rfl rfl hsf_rec.1.1 wrec.toNat 88 hrec_al (by decide) hsb_le hhi_le
      · unfold memW; dsimp only [NS]
        rw [memW_updW_other wcn1 (by omega) (by omega) (by decide),
            memW_updW_other wcn0 (by omega) (by omega) (by decide),
            memW_updW_other wn (by omega) (by omega) (by decide),
            memW_updW_other wp (by omega) (by omega) (by decide),
            memW_updW_other wsl0 (by omega) (by omega) (by decide)]
        have hbv8 : BitVec.ofNat 64 (wrec.toNat + 8) = wrec + BitVec.ofNat 64 8 := by
          apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, BitVec.toNat_add]; try omega
        rw [hbv8]; simp [updW]
  · -- `ite (sl.1 == 2)` flowed with `none`
    rw [evaluateHOLFiniteState_ite] at hnone ⊢
    revert hnone
    split
    · split
      · intro _; rw [evaluateHOLFiniteState_skip]; exact hsf6
      · intro hnone_thn
        exfalso
        rw [evaluateHOLFiniteState_decCall_total] at hnone_thn
        revert hnone_thn
        split <;> [simp; skip]
        try dsimp only
        split <;> [simp; skip]
        try dsimp only
        split <;> [simp; skip]
        rw [fixClockHOLFinite_evaluateState]
        rcases evaluateHOLFiniteState _ _ with ⟨r_pi, _⟩
        cases r_pi with
        | none => simp
        | some rpi' =>
          cases rpi' with
          | returned _ =>
            dsimp only
            split <;> [skip; simp]
            rw [evaluateHOLFiniteState_seq_line780]
            rcases evaluateHOLFiniteState _ _ with ⟨r_i5, _⟩
            cases r_i5 with
            | some _ => simp
            | none =>
              dsimp only
              rw [evaluateHOLFiniteState_decCall_total]
              split <;> [simp; skip]
              try dsimp only
              split <;> [simp; skip]
              try dsimp only
              split <;> [simp; skip]
              rw [fixClockHOLFinite_evaluateState]
              rcases evaluateHOLFiniteState _ _ with ⟨r_cn, _⟩
              cases r_cn with
              | none => simp
              | some rcn' =>
                cases rcn' with
                | returned _ =>
                  dsimp only
                  split <;> [skip; simp]
                  rw [evaluateHOLFiniteState_seq_line780]
                  rcases evaluateHOLFiniteState _ _ with ⟨r_lf, _⟩
                  cases r_lf with
                  | some _ => simp
                  | none =>
                    dsimp only
                    rw [evaluateHOLFiniteState_seq_line780]
                    rcases evaluateHOLFiniteState _ _ with ⟨r_i7, _⟩
                    cases r_i7 with
                    | some _ => simp
                    | none =>
                      dsimp only
                      rw [evaluateHOLFiniteState_decCall_total]
                      split <;> [simp; skip]
                      try dsimp only
                      split <;> [simp; skip]
                      try dsimp only
                      split <;> [simp; skip]
                      rw [fixClockHOLFinite_evaluateState]
                      rcases evaluateHOLFiniteState _ _ with ⟨r_sa, _⟩
                      cases r_sa with
                      | none => simp
                      | some rsa' =>
                        cases rsa' with
                        | returned _ =>
                          dsimp only
                          split <;> [skip; simp]
                          rw [evaluateHOLFiniteState_seq_line780]
                          rcases evaluateHOLFiniteState _ _ with ⟨ru1, _⟩
                          cases ru1 with
                          | some _ => simp
                          | none =>
                            dsimp only; rw [evaluateHOLFiniteState_seq_line780]
                            rcases evaluateHOLFiniteState _ _ with ⟨ru2, _⟩
                            cases ru2 with
                            | some _ => simp
                            | none =>
                              dsimp only; rw [evaluateHOLFiniteState_seq_line780]
                              rcases evaluateHOLFiniteState _ _ with ⟨ru3, _⟩
                              cases ru3 with
                              | some _ => simp
                              | none =>
                                dsimp only; rw [evaluateHOLFiniteState_seq_line780]
                                rcases evaluateHOLFiniteState _ _ with ⟨ru4, _⟩
                                cases ru4 with
                                | some _ => simp
                                | none =>
                                  dsimp only; rw [evaluateHOLFiniteState_seq_line780]
                                  rcases evaluateHOLFiniteState _ _ with ⟨ru5, _⟩
                                  cases ru5 with
                                  | some _ => simp
                                  | none =>
                                    dsimp only; rw [evaluateHOLFiniteState_seq_line780]
                                    rcases evaluateHOLFiniteState _ _ with ⟨ru6, _⟩
                                    cases ru6 with
                                    | some _ => simp
                                    | none =>
                                      dsimp only; rw [evaluateHOLFiniteState_return]
                                      split <;> [simp; (split <;> simp)]
                        | _ => simp
                | _ => simp
          | _ => simp
    · simp
  · -- Branch path (`sl.1 == 17`)
    have hsbr_keep : ∀ nm : MlS, nm ≠ ofString "pi" → nm ≠ ofString "cn" → nm ≠ ofString "vi" →
        nm ≠ ofString "lf" → nm ≠ ofString "rec" →
        s_br.locals.lookup nm = s6.locals.lookup nm := by
      intro nm hne1 hne2 hne3 hne4 hne5
      have hk_aux : ∀ {prog : ProgHOL 64},
          evaluateHOLFiniteState s6 prog = (none, s_br) →
          avoidsLocal nm prog = true →
          s_br.locals.lookup nm = s6.locals.lookup nm := by
        intro prog hp hav
        have hfl : Flowing (evaluateHOLFiniteState s6 prog).1 := by rw [hp]; exact Or.inl rfl
        have hk := evaluate_avoidsLocal_flowing nm prog hav s6 hfl
        rwa [hp] at hk
      exact hk_aux hs_br (by simp [avoidsLocal, beq_iff_eq,
        Ne.symm hne1, Ne.symm hne2, Ne.symm hne3, Ne.symm hne4, Ne.symm hne5])
    refine ret_seq_step_ds
      (ret_ite_step _ (ret_call0_no_ret _ _) ret_skip_no_ret)
      (fun hnone =>
        stepFrame_trans hsf_br
          ((StepFlowProg.ite _
            (StepFlowProg.call0_ro R11Adapters.ReadOnlyLeaves.«ro_mpt_fail» _)
            StepFlowProg.skip) s_br hsf_br.1.1.code hsf_br.1 (by rw [hnone]; simp) (by rw [hnone]; exact Or.inl rfl)))
      (fun s_br2 hs_br2 hsf_br2 => ?_)
    have hsbr2_keep : ∀ nm : String, s_br2.locals.lookup (ofString nm) = s_br.locals.lookup (ofString nm) := by
      intro nm
      have hk_aux : ∀ {prog : ProgHOL 64},
          evaluateHOLFiniteState s_br prog = (none, s_br2) →
          avoidsLocal (ofString nm) prog = true →
          s_br2.locals.lookup (ofString nm) = s_br.locals.lookup (ofString nm) := by
        intro prog hp hav
        have hfl : Flowing (evaluateHOLFiniteState s_br prog).1 := by rw [hp]; exact Or.inl rfl
        have hk := evaluate_avoidsLocal_flowing (ofString nm) prog hav s_br hfl
        rwa [hp] at hk
      exact hk_aux hs_br2 (by simp [avoidsLocal])
    refine ret_decCall_ww_step_ds hsf_br2 hsub_both_ds ww_node_new_branch_ds (ofString "br") _ _
      (fun fb_nb rs_nb cal_nb _ rv_br cpost_br _ hl_nb hrun_nb hsh_br _ hsf_nb => ?_)
    obtain ⟨wbr, rfl⟩ := shape_one_word_ds hsh_br
    have hbr_fb : wbr.toNat % 8 = 0 ∧
        Inside (wbr.toNat, 176) (globN s "heap_ptr") (globN cpost_br "heap_ptr") := by
      have hsame_b := lookupCodeHOLFinite_installed_body s_br2.code.lookup _ _ _ fb_nb
        _ rs_nb _ cal_nb (by rw [hsf_br2.1.1.code]; exact R14Shards.lookup_node_new_branch) hl_nb
      cases hsame_b
      let ent_nb := callEntryStateHOLFinite s_br2 cal_nb
      have hAR_ent : ArenaReady ent_nb := localsFree_arenaReady s_br2 cal_nb (s_br2.clock - 1) hsf_br2.1
      have hspec_nb := R14Shards.node_new_branch_spec ent_nb hsf_br2.1.1.code hAR_ent
        (by dsimp only [ent_nb]; rw [hrun_nb]; exact Or.inl ⟨_, rfl⟩)
      dsimp only [ent_nb] at hspec_nb
      rw [hrun_nb] at hspec_nb
      rcases hspec_nb with ⟨_, _, _, br_w, hret_br, hbr_eq, hbr_al, hhp_post, _⟩
      dsimp only at hret_br hhp_post
      injection hret_br with h1; injection h1 with h2; injection h2 with h3; injection h3 with h4; subst h4
      have hhp_ent : globN s "heap_ptr" ≤ globN (callEntryStateHOLFinite s_br2 cal_nb) "heap_ptr" :=
        hsf_br2.2.1
      dsimp only [Inside]
      omega
    set snb := setVarHOLFinite (ofString "br") (.val (.word wbr)) { cpost_br with locals := s_br2.locals }
    refine ret_decCall_ww_step_ds hsf_nb hsub_sp_ds R10Shards.P02.ww_scratch_alloc (ofString "rec2") _ _
      (fun fb_sa2 rs_sa2 cal_sa2 vals_sa2 rv_rec2 cpost_sa2 hargs_sa2 hl_sa2 hrun_sa2 hsh_rec2 _ hsf_rec2 => ?_)
    obtain ⟨wrec2, rfl⟩ := shape_one_word_ds hsh_rec2
    obtain ⟨hrec2_al, hrec2_lo, hrec2_in, _, hcpost_sa2_hp⟩ :=
      hscratch88_rt snb fb_sa2 rs_sa2 wrec2 cpost_sa2 cal_sa2 vals_sa2 hsf_nb hargs_sa2 hl_sa2 hrun_sa2
    have hhp_sa2_eq : globN cpost_sa2 "heap_ptr" = globN cpost_br "heap_ptr" := by
      unfold globN; rw [hcpost_sa2_hp]; rfl
    set srec2 := setVarHOLFinite (ofString "rec2") (.val (.word wrec2)) { cpost_sa2 with locals := snb.locals }
    have hsrec2_rec2 : srec2.locals.lookup (ofString "rec2") = some (.val (.word wrec2)) := by
      simp [srec2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hsrec2_br : srec2.locals.lookup (ofString "br") = some (.val (.word wbr)) := by
      simp [srec2, snb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "rec2" ≠ ofString "br" by decide]
    have hsrec2_arr : srec2.locals.lookup (ofString "arr") = some (.val (.word wsl0)) := by
      simp [srec2, snb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hsbr2_keep "arr", hsbr_keep (ofString "arr") (by decide) (by decide) (by decide) (by decide) (by decide), hs6_arr,
        show ofString "rec2" ≠ ofString "arr" by decide, show ofString "br" ≠ ofString "arr" by decide]
    have hsrec2_p : srec2.locals.lookup (ofString "p") = some (.val (.word wp)) := by
      simp [srec2, snb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hsbr2_keep "p", hsbr_keep (ofString "p") (by decide) (by decide) (by decide) (by decide) (by decide), hs6_p,
        show ofString "rec2" ≠ ofString "p" by decide, show ofString "br" ≠ ofString "p" by decide]
    have hsrec2_n : srec2.locals.lookup (ofString "n") = some (.val (.word wn)) := by
      simp [srec2, snb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hsbr2_keep "n", hsbr_keep (ofString "n") (by decide) (by decide) (by decide) (by decide) (by decide), hs6_n,
        show ofString "rec2" ≠ ofString "n" by decide, show ofString "br" ≠ ofString "n" by decide]
    apply Ret.of_NS
    refine Ret.ns_storeW (wrec2 + 8#64) 2#64
      (by simp [ev, evalHOLExact, evalListHOLExact, hsrec2_rec2, wordOpHOL, wordOp, valueIsWord, valueWord])
      (by rfl) (fun _ => ?_)
    refine Ret.ns_storeW (wrec2 + 16#64) wbr
      (by simp [ev, evalHOLExact, evalListHOLExact, hsrec2_rec2, wordOpHOL, wordOp, valueIsWord, valueWord])
      (by simp [ev, evalHOLExact, hsrec2_br]) (fun _ => ?_)
    refine Ret.ns_storeW (wrec2 + 24#64) wsl0
      (by simp [ev, evalHOLExact, evalListHOLExact, hsrec2_rec2, wordOpHOL, wordOp, valueIsWord, valueWord])
      (by simp [ev, evalHOLExact, hsrec2_arr]) (fun _ => ?_)
    refine Ret.ns_storeW (wrec2 + 32#64) 0#64
      (by simp [ev, evalHOLExact, evalListHOLExact, hsrec2_rec2, wordOpHOL, wordOp, valueIsWord, valueWord])
      (by rfl) (fun _ => ?_)
    refine Ret.ns_storeW (wrec2 + 40#64) 0#64
      (by simp [ev, evalHOLExact, evalListHOLExact, hsrec2_rec2, wordOpHOL, wordOp, valueIsWord, valueWord])
      (by rfl) (fun _ => ?_)
    refine Ret.ns_storeW (wrec2 + 48#64) wp
      (by simp [ev, evalHOLExact, evalListHOLExact, hsrec2_rec2, wordOpHOL, wordOp, valueIsWord, valueWord])
      (by simp [ev, evalHOLExact, hsrec2_p]) (fun _ => ?_)
    refine Ret.ns_storeW (wrec2 + 56#64) wn
      (by simp [ev, evalHOLExact, evalListHOLExact, hsrec2_rec2, wordOpHOL, wordOp, valueIsWord, valueWord])
      (by simp [ev, evalHOLExact, hsrec2_n]) (fun _ => ?_)
    refine Ret.ns_ret (fun val hval => ?_)
    simp [ev, evalHOLExact, evalListHOLExact, hsrec2_rec2] at hval
    subst hval
    refine ⟨1#64, wrec2, rfl, fun h => by simp at h, fun _ => ?_⟩
    have h88 : (88 + 7) / 8 * 8 = 88 := by decide
    have h176 : (176 + 7) / 8 * 8 = 176 := by decide
    have hse_lt : scratchEnd < 2 ^ 64 := by decide
    have hsp_s_hi : globN s "scratch_ptr" ≤ scratchEnd := hAR.2.2.2.2.2.1
    have hrec2_lt : wrec2.toNat + 88 ≤ scratchEnd := by
      dsimp only [Inside] at hrec2_in; omega
    have hsb_rec2 : sourceBase ≤ wrec2.toNat := by
      have hss : sourceBase ≤ scratchStart := by decide
      have := hAR.2.2.2.1
      omega
    have hhi_rec2 : wrec2.toNat + 88 ≤ heapEnd := by
      have hhe : scratchEnd ≤ heapEnd := by decide
      omega
    have hsb_br : sourceBase ≤ wbr.toNat := by
      have := hAR.2.1; dsimp only [Inside] at hbr_fb; omega
    have hhi_br : wbr.toNat + 176 ≤ heapEnd := by
      have := hsf_nb.1.2.2.1
      have hhl_he : heapLimit ≤ heapEnd := by decide
      have hhp_snb : globN snb "heap_ptr" = globN cpost_br "heap_ptr" := rfl
      dsimp only [Inside] at hbr_fb
      omega
    let m2 := updW (updW (updW (updW (updW (updW (updW srec2.memory
      (wrec2 + 8#64) 2#64) (wrec2 + 16#64) wbr) (wrec2 + 24#64) wsl0)
      (wrec2 + 32#64) 0#64) (wrec2 + 40#64) 0#64) (wrec2 + 48#64) wp) (wrec2 + 56#64) wn
    let st_end := NS srec2 (emptyLocalsHOLFinite (NS srec2 srec2.locals srec2.globals m2 srec2.clock)).locals srec2.globals m2 srec2.clock
    have hmw16 : memW st_end (wrec2.toNat + 16) = wbr.toNat := by
      unfold memW; dsimp only [st_end, NS, m2]
      rw [memW_updW_other wn (by omega) (by omega) (by decide),
          memW_updW_other wp (by omega) (by omega) (by decide),
          memW_updW_other 0#64 (by omega) (by omega) (by decide),
          memW_updW_other 0#64 (by omega) (by omega) (by decide),
          memW_updW_other wsl0 (by omega) (by omega) (by decide)]
      have hbv16 : BitVec.ofNat 64 (wrec2.toNat + 16) = wrec2 + BitVec.ofNat 64 16 := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, BitVec.toNat_add]; try omega
      rw [hbv16]; simp [updW]
    refine ⟨⟨hrec2_al, hrec2_lo, ?_, ?_⟩, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [h88]
      rw [Inside, show globN st_end "scratch_ptr" = globN cpost_sa2 "scratch_ptr" from rfl]
      exact hrec2_in
    · rw [h88]
      exact wordsOK_of_same_guest srec2 st_end rfl rfl rfl rfl hsf_rec2.1.1 wrec2.toNat 88 hrec2_al (by decide) hsb_rec2 hhi_rec2
    · unfold memW; dsimp only [st_end, NS, m2]
      rw [memW_updW_other wn (by omega) (by omega) (by decide),
          memW_updW_other wp (by omega) (by omega) (by decide),
          memW_updW_other 0#64 (by omega) (by omega) (by decide),
          memW_updW_other 0#64 (by omega) (by omega) (by decide),
          memW_updW_other wsl0 (by omega) (by omega) (by decide),
          memW_updW_other wbr (by omega) (by omega) (by decide)]
      have hbv8 : BitVec.ofNat 64 (wrec2.toNat + 8) = wrec2 + BitVec.ofNat 64 8 := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, BitVec.toNat_add]; try omega
      rw [hbv8]; simp [updW]
    · unfold memW; dsimp only [st_end, NS, m2]
      rw [memW_updW_other wn (by omega) (by omega) (by decide),
          memW_updW_other wp (by omega) (by omega) (by decide),
          memW_updW_other 0#64 (by omega) (by omega) (by decide)]
      have hbv32 : BitVec.ofNat 64 (wrec2.toNat + 32) = wrec2 + BitVec.ofNat 64 32 := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, BitVec.toNat_add]; try omega
      rw [hbv32]; simp [updW]
    · unfold memW; dsimp only [st_end, NS, m2]
      rw [memW_updW_other wn (by omega) (by omega) (by decide),
          memW_updW_other wp (by omega) (by omega) (by decide)]
      have hbv40 : BitVec.ofNat 64 (wrec2.toNat + 40) = wrec2 + BitVec.ofNat 64 40 := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, BitVec.toNat_add]; try omega
      rw [hbv40]; simp [updW]
    · refine ⟨by rw [hmw16]; exact hbr_fb.1, ?_, ?_⟩
      · rw [h176, Inside, show globN st_end "heap_ptr" = globN cpost_sa2 "heap_ptr" from rfl, hhp_sa2_eq, hmw16]
        exact hbr_fb.2
      · rw [h176, hmw16]
        exact wordsOK_of_same_guest srec2 st_end rfl rfl rfl rfl hsf_rec2.1.1 wbr.toNat 176 hbr_fb.1 (by decide) hsb_br hhi_br

end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12
