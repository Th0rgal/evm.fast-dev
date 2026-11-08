import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group05bEnv3b

/-! # OpHandlerSpec Group 05bEnv2 (`OpHandlers-A`): `track_ancestor_access` preservation -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8Contracts.M23

private theorem lookup_track_ancestor_access_local :
    originalRuntimeCode.lookup (ofString "track_ancestor_access") =
      some ([(ofString "offset", .one)],
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
          (extractFn Guest.Software.guestFn_track_ancestor_access).body, .one) :=
  lookup_of_guestAst_getElem 402 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_track_ancestor_access) rfl

private theorem store_res_none_or_error {F : Type} (t : PanSemStateFiniteExact 64 F)
    (d e : ExpHOL 64) :
    (evaluateHOLFiniteState t (.store d e)).1 = none ∨
      (evaluateHOLFiniteState t (.store d e)).1 = some .error := by
  rw [evaluateHOLFiniteState_store]
  split <;> [(split <;> [(split <;> [exact Or.inl rfl; exact Or.inr rfl]); exact Or.inr rfl]); exact Or.inr rfl]

private theorem track_ancestor_access_effect {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {offw : BitVec 64}
    (hoff : s.locals.lookup (ofString "offset") = some (.val (.word offw)))
    (hW : WorldOK s)
    (hres : evaluateHOLFiniteState s
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
          (extractFn Guest.Software.guestFn_track_ancestor_access).body) =
        (some (.returned (.val (.word 0))), post)) :
    ByteRegionEffect s post [(globN s "bs" + 56, 16)] ∧ globN s "bs" ≠ 0 := by
  have hb :
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_track_ancestor_access).body =
      .seq (.ite (.cmp .equal (.load .one (.op .add [.var .global (ofString "bs"), .const 56])) (.const 0))
        (.seq
          (.store (.op .add [.var .global (ofString "bs"), .const 56]) (.const 1))
          (.store (.op .add [.var .global (ofString "bs"), .const 64]) (.var .local (ofString "offset"))))
        (.ite (.cmp .lower (.load .one (.op .add [.var .global (ofString "bs"), .const 64]))
            (.var .local (ofString "offset")))
          (.store (.op .add [.var .global (ofString "bs"), .const 64]) (.var .local (ofString "offset")))
          .skip))
        (.return (.const 0)) := rfl
  rw [hb] at hres
  have hbs_info : ∃ bsw : BitVec 64,
      s.globals.lookup (ofString "bs") = some (.val (.word bsw)) ∧
      globN s "bs" = bsw.toNat ∧ globN s "bs" ≠ 0 ∧ bsw.toNat + 64 < heapEnd := by
    have hres0 := hres
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres0
    rcases hg : s.globals.lookup (ofString "bs") with _ | gv
    · simp only [evalHOLExact, evalListHOLExact, hg] at hres0; cases (Prod.mk.inj hres0).1
    · rcases gv with ⟨⟨bsw⟩⟩ | _ | _
      · by_cases hdom56 : s.memaddrs (bsw + 56#64)
        · obtain ⟨_, _, _, hF0, _⟩ := hW.2
          have hglob_bs : globN s "bs" = bsw.toNat := by simp [globN, hg]
          have hbs_nz : bsw.toNat ≠ 0 := by
            intro hz
            have h0 : bsw = 0#64 := BitVec.eq_of_toNat_eq hz
            subst h0
            have hdom' := hW.1.1.memaddrs ▸ hdom56
            rw [ordinaryDomain_iff] at hdom'
            have : (0#64 + 56#64).toNat = 56 := by decide
            omega
          have hfix0 := typedRec_in_fixedObjects s (g := "bs") (sz := 80) (by decide)
          rw [hglob_bs, if_neg hbs_nz] at hfix0
          rcases hF0.1 _ hfix0 with h0 | ⟨hal0, _⟩
          · dsimp at h0; omega
          · have hb_le : bsw.toNat + 80 ≤ scratchEnd := by
              rcases hal0 with ⟨_, hhi⟩ | ⟨_, hhi⟩
              · have := hW.1.2.2.1; rw [Wave8Contracts.M23.heapLimit_val] at this; rw [Wave8Contracts.M23.scratchEnd_val]; dsimp at hhi; omega
              · exact hhi
            rw [Wave8Contracts.M23.scratchEnd_val] at hb_le; rw [Wave8Contracts.M23.heapEnd_val]
            exact ⟨bsw, rfl, hglob_bs, by omega, by omega⟩
        · have hc1_none : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
              (.cmp .equal (.load .one (.op .add [.var .global (ofString "bs"), .const 56])) (.const 0)) = none := by
            simp [evalHOLExact, evalListHOLExact, hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact, hdom56]
          rw [hc1_none] at hres0; cases (Prod.mk.inj hres0).1
      · simp only [evalHOLExact, evalListHOLExact, hg, valueIsWord] at hres0; cases (Prod.mk.inj hres0).1
      · simp only [evalHOLExact, evalListHOLExact, hg, valueIsWord] at hres0; cases (Prod.mk.inj hres0).1
  obtain ⟨bsw, hbsw, hbs_nat, hbs_nz, hbs_lt_he⟩ := hbs_info
  have hhe := Wave8Contracts.M23.heapEnd_val
  have hbs56_nat : (bsw + 56).toNat = globN s "bs" + 56 := by
    rw [BitVec.toNat_add, show (56 : BitVec 64).toNat = 56 from rfl, ← hbs_nat]
    exact Nat.mod_eq_of_lt (by omega)
  have hbs64_nat : (bsw + 64).toNat = globN s "bs" + 64 := by
    rw [BitVec.toNat_add, show (64 : BitVec 64).toNat = 64 from rfl, ← hbs_nat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres
  rcases hc1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.load .one (.op .add [.var .global (ofString "bs"), .const 56])) (.const 0)) with _ | cv1
  · simp only [hc1] at hres; cases (Prod.mk.inj hres).1
  · simp only [hc1] at hres
    rcases cv1 with ⟨⟨cw1⟩⟩ | _ | _
    · dsimp only at hres
      by_cases hcw1 : cw1 = 0
      · rw [if_pos hcw1, evaluateHOLFiniteState_ite] at hres
        rcases hc2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
            (.cmp .lower (.load .one (.op .add [.var .global (ofString "bs"), .const 64]))
              (.var .local (ofString "offset"))) with _ | cv2
        · simp only [hc2] at hres; cases (Prod.mk.inj hres).1
        · simp only [hc2] at hres
          rcases cv2 with ⟨⟨cw2⟩⟩ | _ | _
          · dsimp only at hres
            by_cases hcw2 : cw2 = 0
            · rw [if_pos hcw2, evaluateHOLFiniteState_skip, evaluateHOLFiniteState_return] at hres
              simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, Nat.reduceLeDiff, ↓reduceIte] at hres
              rcases (Prod.mk.inj hres).2 with rfl
              exact ⟨(ByteRegionEffect.refl s _).with_locals_clock _ _, hbs_nz⟩
            · rw [if_neg hcw2] at hres
              rcases hst : evaluateHOLFiniteState s
                  (.store (.op .add [.var .global (ofString "bs"), .const 64])
                    (.var .local (ofString "offset"))) with ⟨rs, s1⟩
              simp only [hst] at hres
              rcases store_res_none_or_error s
                  (.op .add [.var .global (ofString "bs"), .const 64])
                  (.var .local (ofString "offset")) with hsn | hse
              · rw [hst] at hsn; dsimp at hsn; subst hsn; dsimp only at hres
                obtain ⟨heff1, _⟩ := ByteRegionEffect.of_store_word hW.1.1.memaddrs hst
                  (Rl := [(globN s "bs" + 56, 16)])
                  (fun v hv => by simp [evalHOLExact, hoff] at hv; exact ⟨offw, hv.symm⟩)
                  (fun addr hdst _ => by
                    have haddr : addr = bsw + 64 := by
                      simp [evalHOLExact, evalListHOLExact, hbsw, wordOpHOL, wordOp,
                        valueIsWord, valueWord, BitVec.add_zero] at hdst
                      exact hdst.symm
                    subst haddr
                    exact ⟨_, List.mem_singleton.2 rfl, by dsimp only; rw [hbs64_nat]; omega,
                      by dsimp only; rw [hbs64_nat]⟩)
                rw [evaluateHOLFiniteState_return] at hres
                simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, Nat.reduceLeDiff, ↓reduceIte] at hres
                rcases (Prod.mk.inj hres).2 with rfl
                exact ⟨heff1.with_locals_clock _ _, hbs_nz⟩
              · rw [hst] at hse; dsimp at hse; subst hse; cases (Prod.mk.inj hres).1
          · cases (Prod.mk.inj hres).1
          · cases (Prod.mk.inj hres).1
      · rw [if_neg hcw1, evaluateHOLFiniteState_seq_line780] at hres
        rcases hst1 : evaluateHOLFiniteState s
            (.store (.op .add [.var .global (ofString "bs"), .const 56]) (.const 1)) with ⟨rs1, s1⟩
        simp only [hst1] at hres
        rcases store_res_none_or_error s
            (.op .add [.var .global (ofString "bs"), .const 56]) (.const 1) with hsn1 | hse1
        · rw [hst1] at hsn1; dsimp at hsn1; subst hsn1; dsimp only at hres
          obtain ⟨heff1, hs1_loc⟩ := ByteRegionEffect.of_store_word hW.1.1.memaddrs hst1
            (Rl := [(globN s "bs" + 56, 16)])
            (fun v hv => by simp [evalHOLExact] at hv; exact ⟨1, hv.symm⟩)
            (fun addr hdst _ => by
              have haddr : addr = bsw + 56 := by
                simp [evalHOLExact, evalListHOLExact, hbsw, wordOpHOL, wordOp,
                  valueIsWord, valueWord, BitVec.add_zero] at hdst
                exact hdst.symm
              subst haddr
              exact ⟨_, List.mem_singleton.2 rfl, by dsimp only; rw [hbs56_nat],
                by dsimp only; rw [hbs56_nat]; omega⟩)
          have hs1_ma : s1.memaddrs = ordinaryDomain := heff1.memaddrs.trans hW.1.1.memaddrs
          have hs1_bs : s1.globals.lookup (ofString "bs") = some (.val (.word bsw)) := heff1.globals ▸ hbsw
          rcases hst2 : evaluateHOLFiniteState s1
              (.store (.op .add [.var .global (ofString "bs"), .const 64])
                (.var .local (ofString "offset"))) with ⟨rs2, s2⟩
          simp only [hst2] at hres
          rcases store_res_none_or_error s1
              (.op .add [.var .global (ofString "bs"), .const 64])
              (.var .local (ofString "offset")) with hsn2 | hse2
          · rw [hst2] at hsn2; dsimp at hsn2; subst hsn2; dsimp only at hres
            have hs1_off : s1.locals.lookup (ofString "offset") = some (.val (.word offw)) := hs1_loc ▸ hoff
            obtain ⟨heff2, _⟩ := ByteRegionEffect.of_store_word hs1_ma hst2
              (Rl := [(globN s "bs" + 56, 16)])
              (fun v hv => by simp [evalHOLExact, hs1_off] at hv; exact ⟨offw, hv.symm⟩)
              (fun addr hdst _ => by
                have haddr : addr = bsw + 64 := by
                  simp [evalHOLExact, evalListHOLExact, hs1_bs, wordOpHOL, wordOp,
                    valueIsWord, valueWord, BitVec.add_zero] at hdst
                  exact hdst.symm
                subst haddr
                exact ⟨_, List.mem_singleton.2 rfl, by dsimp only; rw [hbs64_nat]; omega,
                  by dsimp only; rw [hbs64_nat]⟩)
            rw [evaluateHOLFiniteState_return] at hres
            simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, Nat.reduceLeDiff, ↓reduceIte] at hres
            rcases (Prod.mk.inj hres).2 with rfl
            exact ⟨(heff1.trans heff2).with_locals_clock _ _, hbs_nz⟩
          · rw [hst2] at hse2; dsimp at hse2; subst hse2; cases (Prod.mk.inj hres).1
        · rw [hst1] at hse1; dsimp at hse1; subst hse1; cases (Prod.mk.inj hres).1
    · cases (Prod.mk.inj hres).1
    · cases (Prod.mk.inj hres).1

theorem eps_track_ancestor_access :
    EvmPreservingSpec (fun _ => True) (fun s _ post => post.globals = s.globals)
      (ofString "track_ancestor_access") := by
  refine ⟨_, _, _, lookup_track_ancestor_access_local, ?_⟩
  intro F s _hcode hInv _ hex _hnt
  obtain ⟨vals, hlk⟩ := hex
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup (ofString "track_ancestor_access") vals _ s.locals .one hlk
  have hoff : ∃ offw : BitVec 64, s.locals.lookup (ofString "offset") = some (.val (.word offw)) := by
    rcases vals with _ | ⟨v0, _ | _⟩
    · simp [Flapjack.lookupCodeHOLExact, lookup_track_ancestor_access_local] at hx
    · obtain ⟨_, _, offw, _, hoff⟩ := one_word_arg_lookup lookup_track_ancestor_access_local hlk
      exact ⟨offw, hoff⟩
    · simp [Flapjack.lookupCodeHOLExact, lookup_track_ancestor_access_local] at hx
  obtain ⟨offw, hoff⟩ := hoff
  have hout : (evaluateHOLFiniteState s
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
          (extractFn Guest.Software.guestFn_track_ancestor_access).body)).1 = some .error ∨
      (evaluateHOLFiniteState s
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
          (extractFn Guest.Software.guestFn_track_ancestor_access).body)).1 =
        some (.returned (.val (.word 0))) := by
    have hb :
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
          (extractFn Guest.Software.guestFn_track_ancestor_access).body =
        .seq (.ite (.cmp .equal (.load .one (.op .add [.var .global (ofString "bs"), .const 56])) (.const 0))
          (.seq
            (.store (.op .add [.var .global (ofString "bs"), .const 56]) (.const 1))
            (.store (.op .add [.var .global (ofString "bs"), .const 64]) (.var .local (ofString "offset"))))
          (.ite (.cmp .lower (.load .one (.op .add [.var .global (ofString "bs"), .const 64]))
              (.var .local (ofString "offset")))
            (.store (.op .add [.var .global (ofString "bs"), .const 64]) (.var .local (ofString "offset")))
            .skip))
          (.return (.const 0)) := rfl
    have hnone_or_err : ∀ (t : PanSemStateFiniteExact 64 F),
        (evaluateHOLFiniteState t
          (.ite (.cmp .equal (.load .one (.op .add [.var .global (ofString "bs"), .const 56])) (.const 0))
            (.seq
              (.store (.op .add [.var .global (ofString "bs"), .const 56]) (.const 1))
              (.store (.op .add [.var .global (ofString "bs"), .const 64]) (.var .local (ofString "offset"))))
            (.ite (.cmp .lower (.load .one (.op .add [.var .global (ofString "bs"), .const 64]))
                (.var .local (ofString "offset")))
              (.store (.op .add [.var .global (ofString "bs"), .const 64]) (.var .local (ofString "offset")))
              .skip))).1 = none ∨
        (evaluateHOLFiniteState t
          (.ite (.cmp .equal (.load .one (.op .add [.var .global (ofString "bs"), .const 56])) (.const 0))
            (.seq
              (.store (.op .add [.var .global (ofString "bs"), .const 56]) (.const 1))
              (.store (.op .add [.var .global (ofString "bs"), .const 64]) (.var .local (ofString "offset"))))
            (.ite (.cmp .lower (.load .one (.op .add [.var .global (ofString "bs"), .const 64]))
                (.var .local (ofString "offset")))
              (.store (.op .add [.var .global (ofString "bs"), .const 64]) (.var .local (ofString "offset")))
              .skip))).1 = some .error := by
      intro t; rw [evaluateHOLFiniteState_ite]
      split
      · split_ifs
        · rw [evaluateHOLFiniteState_ite]
          split
          · split_ifs
            · exact Or.inl (by simp [evaluateHOLFiniteState_skip])
            · exact store_res_none_or_error _ _ _
          · exact Or.inr rfl
        · rw [evaluateHOLFiniteState_seq_line780]
          rcases h1 : evaluateHOLFiniteState t
              (.store (.op .add [.var .global (ofString "bs"), .const 56]) (.const 1)) with ⟨r1, s1⟩
          rcases store_res_none_or_error t
              (.op .add [.var .global (ofString "bs"), .const 56]) (.const 1) with hn1 | he1
          · rw [h1] at hn1; dsimp at hn1; subst hn1; exact store_res_none_or_error _ _ _
          · rw [h1] at he1; dsimp at he1; subst he1; exact Or.inr rfl
      · exact Or.inr rfl
    rw [hb, evaluateHOLFiniteState_seq_line780]
    rcases h1 : evaluateHOLFiniteState s _ with ⟨r1, s1⟩
    rcases hnone_or_err s with hn | he
    · rw [h1] at hn; dsimp at hn; subst hn; dsimp only
      rw [evaluateHOLFiniteState_return]
      exact Or.inr (by simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL])
    · rw [h1] at he; dsimp at he; subst he; exact Or.inl rfl
  dsimp only
  rcases hev : evaluateHOLFiniteState s
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_track_ancestor_access).body) with ⟨r, post⟩
  rw [hev] at hout; dsimp only at hout ⊢
  rcases hout with rfl | rfl
  · refine ⟨fun _ h => ?_, ?_⟩
    · injection h with h'; cases h'
    · rintro ⟨_, h⟩; injection h with h'; cases h'
  · refine ⟨fun v hv => ?_, ?_⟩
    · have hW : WorldOK s := ⟨hInv.1, let ⟨S, hW, _⟩ := hInv.2; ⟨S, hW⟩⟩
      obtain ⟨heff, hbs0⟩ := track_ancestor_access_effect hoff hW hev
      obtain ⟨hInv_post, hg_eq, hch_eq, hR_eq⟩ := evmInv_of_bs56_effect hInv hbs0 heff
      exact ⟨hInv_post, hch_eq, le_of_eq hR_eq, hg_eq⟩
    · rintro ⟨_, h⟩; injection h with h'; cases h'

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
