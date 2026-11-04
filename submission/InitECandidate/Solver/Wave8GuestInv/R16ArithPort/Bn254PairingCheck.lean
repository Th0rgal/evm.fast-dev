import InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
import InitECandidate.Solver.Wave8GuestInv.R16Shards.BlsPrecompiles.BlsDecodeTouch
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BitFqSmallLeaves
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.CappedLoopLeaves

/-! Standalone bounded termination proof on `GuestInv` for `bn254_pairing_check`
(parameterized only by `fb_fq12_inv`) and `pre_alt_bn128_pairing_check`.
Zero `LeafStatements.lean` dependency, zero `sorry`. -/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R16ArithPort

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common
open InitECandidate.Solver.Wave8GuestInv.P13.Callees
open InitECandidate.Solver.Wave8GuestInv.P13.DivMod
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
open InitECandidate.Solver.Wave8GuestInv.R16Shards.BlsPrecompiles
open InitECandidate.Solver.Wave8GuestInv.R16ArithPort.Capped
open InitECandidate.Solver.Wave8GuestInv.Arith (ReadFailure arithEval arith_load_none
  arith_loadByte_none arith_shift_none arith_two_arg_lookup_inv_shape arithSourceBody
  arithU256Shape)

/-! ### 1. `ReadFailure` propagation across `u256_from_be(..., 32)` -> `bn254_parse_g1` -/

private theorem outside_word_memaddrs {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b : BitVec 64) (hg : GuestInv s)
    (hb : ¬ (sourceBase ≤ b.toNat ∧ b.toNat < heapEnd)) :
    ¬ s.memaddrs b := by
  intro h
  rw [hg.memaddrs] at h
  have hi := ordinaryDomain_interval b h
  exact hb ⟨hi.1, by omega⟩

private theorem outside_byte_memaddrs {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b : BitVec 64) (hg : GuestInv s)
    (hb : ¬ (sourceBase ≤ b.toNat ∧ b.toNat < heapEnd)) :
    ¬ s.memaddrs (panByteAlignHOL b) := by
  intro h
  rw [hg.memaddrs] at h
  exact hb (ordinaryDomain_byte_interval b h)

private theorem shape_one_word {v : ValueHOL 64}
    (h : shapeEqHOL .one (shapeOfHOLExact v) = true) : ∃ w : BitVec 64, v = .val (.word w) := by
  cases v with
  | val wl => cases wl with | word w => exact ⟨w, rfl⟩
  | rStruct _ => simp [shapeOfHOLExact, shapeEqHOL] at h
  | nStruct _ _ => simp [shapeOfHOLExact, shapeEqHOL] at h

private def decCallRest (p : ProgHOL 64) : ProgHOL 64 :=
  match p with | .decCall _ _ _ _ rest => rest | _ => .skip

private theorem ReadFailure.decCall_two_arg_any {F : Type} (s : PanSemStateFiniteExact 64 F)
    (tmp fname p1 p2 : MlS) (sh rs : ShapeHOL) (fbody : ProgHOL 64)
    (arg1 arg2 : ExpHOL 64) (cont : ProgHOL 64) (b : BitVec 64)
    (hdiff : p1 ≠ p2)
    (hlookup : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], fbody, rs))
    (hg : GuestInv s)
    (harg1 : arithEval s arg1 = some (.val (.word b)))
    (hfail : ∀ (v2 : ValueHOL 64),
      arithEval s arg2 = some v2 →
      ∀ (st : PanSemStateFiniteExact 64 F),
        GuestInv st →
        st.locals.lookup p1 = some (.val (.word b)) →
        st.locals.lookup p2 = some v2 →
        ReadFailure st fbody) :
    ReadFailure s (.decCall tmp sh fname [arg1, arg2] cont) := by
  unfold ReadFailure
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [arg1, arg2] with _ | vals
  · simp
  · dsimp only
    rcases hlk : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · simp
    · dsimp only
      by_cases hz : s.clock = 0
      · simp [hz]
      · rw [if_neg hz]
        have hargs' : @evalListHOLExact 64 F _ s.toExact
            (fun a => Classical.propDecidable (s.memaddrs a)) [arg1, arg2] = some vals := by
          simpa [evalListHOLFinite] using hargs
        dsimp only [arithEval] at harg1
        rcases harg2 : @evalHOLExact 64 F _ s.toExact
            (fun a => Classical.propDecidable (s.memaddrs a)) arg2 with _ | v2
        · simp [evalListHOLExact, harg1, harg2] at hargs'
        · have hvals : vals = [.val (.word b), v2] := by
            simpa [evalListHOLExact, harg1, harg2] using hargs'.symm
          subst hvals
          rw [hg.code] at hlk
          obtain ⟨_, _, hfb, hcal, _⟩ := arith_two_arg_lookup_inv_shape
            originalRuntimeCode.lookup fname p1 p2 .one .one rs fbody (.val (.word b)) v2
            hdiff hlookup hlk
          rw [hfb, hcal]
          have hf := hfail v2 harg2 (callEntryStateHOLFinite s
            ((HolFiniteMapExact.empty.update (p1, .val (.word b))).update (p2, v2)))
            (guestInv_callEntry _ _ hg)
            (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              Ne.symm hdiff])
            (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
          unfold ReadFailure at hf
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s
            ((HolFiniteMapExact.empty.update (p1, .val (.word b))).update (p2, v2))) fbody with
            ⟨res, bpost⟩
          rw [hrun] at hf ⊢
          rcases hf with hf | hf <;> dsimp only at hf <;> subst res <;> simp

private def u256FromBeFastCond : ExpHOL 64 :=
  match arithSourceBody Guest.Software.guestFn_u256_from_be with
  | .seq (.ite cond _ _) _ => cond
  | _ => .const 0#64

private def u256FromBeFastCont : ProgHOL 64 :=
  match arithSourceBody Guest.Software.guestFn_u256_from_be with
  | .seq (.ite _ (.dec _ _ _ cont) _) _ => cont
  | _ => .skip

private def u256FromBeLoopBodyRest : ProgHOL 64 :=
  match arithSourceBody Guest.Software.guestFn_u256_from_be with
  | .seq _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _
      (.seq (.while _ (.dec _ _ _ (.dec _ _ _ rest))) _)))))) => rest
  | _ => .skip

private def u256FromBeAfterLoop : ProgHOL 64 :=
  match arithSourceBody Guest.Software.guestFn_u256_from_be with
  | .seq _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _
      (.seq _ after)))))) => after
  | _ => .skip

private theorem u256_from_be_32_outside {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b : BitVec 64) (hg : GuestInv s)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word b)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word 32#64)))
    (hb : ¬ (sourceBase ≤ b.toNat ∧ b.toNat < heapEnd)) :
    ReadFailure s (arithSourceBody Guest.Software.guestFn_u256_from_be) := by
  have hbody : arithSourceBody Guest.Software.guestFn_u256_from_be =
      .seq
        (.ite u256FromBeFastCond
          (.dec (ofString "w") .one (.load .one (.var .local (ofString "p"))) u256FromBeFastCont)
          .skip)
        (.dec (ofString "l0") .one (.const 0#64)
          (.dec (ofString "l1") .one (.const 0#64)
            (.dec (ofString "l2") .one (.const 0#64)
              (.dec (ofString "l3") .one (.const 0#64)
                (.dec (ofString "i") .one (.const 0#64)
                  (.seq
                    (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
                      (.dec (ofString "pos") .one
                        (.op .sub [.op .sub [.var .local (ofString "n"), .const 1#64],
                          .var .local (ofString "i")])
                        (.dec (ofString "byte") .one
                          (.shift .lsl
                            (.loadByte (.op .add [.var .local (ofString "p"), .var .local (ofString "i")]))
                            (.panop .mul
                              [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]))
                          u256FromBeLoopBodyRest)))
                    u256FromBeAfterLoop)))))) := rfl
  rw [hbody]
  unfold ReadFailure
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  rcases hc : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) u256FromBeFastCond with _ | cv
  · simp
  · cases cv with
    | rStruct _ => simp
    | nStruct _ _ => simp
    | val wl =>
      cases wl with
      | word cw =>
        dsimp only
        by_cases hcw : cw = 0
        · rw [if_pos hcw]
          rw [evaluateHOLFiniteState_skip]
          dsimp only
          change ReadFailure s _
          apply ReadFailure.dec s _ _ _ _ (.val (.word 0#64)) rfl
          let s1 := setVarHOLFinite (ofString "l0") (.val (.word 0#64)) s
          apply ReadFailure.dec s1 _ _ _ _ (.val (.word 0#64)) rfl
          let s2 := setVarHOLFinite (ofString "l1") (.val (.word 0#64)) s1
          apply ReadFailure.dec s2 _ _ _ _ (.val (.word 0#64)) rfl
          let s3 := setVarHOLFinite (ofString "l2") (.val (.word 0#64)) s2
          apply ReadFailure.dec s3 _ _ _ _ (.val (.word 0#64)) rfl
          let s4 := setVarHOLFinite (ofString "l3") (.val (.word 0#64)) s3
          apply ReadFailure.dec s4 _ _ _ _ (.val (.word 0#64)) rfl
          let s5 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s4
          have hg5 : GuestInv s5 :=
            guestInv_setVar _ _ _ (guestInv_setVar _ _ _ (guestInv_setVar _ _ _
              (guestInv_setVar _ _ _ (guestInv_setVar _ _ _ hg))))
          have hp5 : s5.locals.lookup (ofString "p") = some (.val (.word b)) := by
            simp [s5, s4, s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp,
              show ofString "i" ≠ ofString "p" by decide,
              show ofString "l3" ≠ ofString "p" by decide,
              show ofString "l2" ≠ ofString "p" by decide,
              show ofString "l1" ≠ ofString "p" by decide,
              show ofString "l0" ≠ ofString "p" by decide]
          have hn5 : s5.locals.lookup (ofString "n") = some (.val (.word 32#64)) := by
            simp [s5, s4, s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
              show ofString "i" ≠ ofString "n" by decide,
              show ofString "l3" ≠ ofString "n" by decide,
              show ofString "l2" ≠ ofString "n" by decide,
              show ofString "l1" ≠ ofString "n" by decide,
              show ofString "l0" ≠ ofString "n" by decide]
          have hi5 : s5.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
            simp [s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          apply ReadFailure.seq
          have hcond : evalHOLFinite s5 (h := fun a => Classical.propDecidable (s5.memaddrs a))
              (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
              some (.val (.word 1#64)) := by
            simp [evalHOLFinite, evalHOLExact, hi5, hn5, wordCmpHOL]
          apply ReadFailure.while s5 _ _ 1#64 hcond (by decide)
          let sd := decClockHOLFinite s5
          have hpos : arithEval sd
              (.op .sub [.op .sub [.var .local (ofString "n"), .const 1#64],
                .var .local (ofString "i")]) = some (.val (.word 31#64)) := by
            simp [sd, arithEval, evalHOLExact, evalListHOLExact, decClockHOLFinite, hn5, hi5,
              wordOpHOL, wordOp, valueIsWord, valueWord]
          apply ReadFailure.dec sd _ _ _ _ (.val (.word 31#64)) hpos
          let sp := setVarHOLFinite (ofString "pos") (.val (.word 31#64)) sd
          have hgp : GuestInv sp := guestInv_setVar _ _ _ (guestInv_decClock s5 hg5)
          have hpp : sp.locals.lookup (ofString "p") = some (.val (.word b)) := by
            simp [sp, sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update,
              FUPDATE, hp5, show ofString "pos" ≠ ofString "p" by decide]
          have hip : sp.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
            simp [sp, sd, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update,
              FUPDATE, hi5, show ofString "pos" ≠ ofString "i" by decide]
          apply ReadFailure.dec_none
          apply arith_shift_none
          apply arith_loadByte_none sp _ b
          · simp [arithEval, evalHOLExact, evalListHOLExact, hpp, hip,
              wordOpHOL, wordOp, valueIsWord, valueWord]
          · exact outside_byte_memaddrs sp b hgp hb
        · rw [if_neg hcw]
          have hld : ReadFailure s
              (.dec (ofString "w") .one (.load .one (.var .local (ofString "p"))) u256FromBeFastCont) := by
            apply ReadFailure.dec_none
            exact arith_load_none s _ b
              (by simp [arithEval, evalHOLExact, hp])
              (outside_word_memaddrs s b hg hb)
          unfold ReadFailure at hld
          rcases hrun : evaluateHOLFiniteState s
              (.dec (ofString "w") .one (.load .one (.var .local (ofString "p"))) u256FromBeFastCont)
            with ⟨res, post⟩
          rw [hrun] at hld
          rcases hld with hld | hld <;> dsimp only at hld <;> subst res <;> simp

private theorem bn254_parse_g1_outside {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b : BitVec 64) (hg : GuestInv s)
    (hd : s.locals.lookup (ofString "data") = some (.val (.word b)))
    (hb : ¬ (sourceBase ≤ b.toNat ∧ b.toNat < heapEnd)) :
    ReadFailure s (arithSourceBody Guest.Software.guestFn_bn254_parse_g1) := by
  have hbody : arithSourceBody Guest.Software.guestFn_bn254_parse_g1 =
      .decCall (ofString "x") arithU256Shape (ofString "u256_from_be")
        [.var .local (ofString "data"), .const 32#64]
        (decCallRest (arithSourceBody Guest.Software.guestFn_bn254_parse_g1)) := rfl
  rw [hbody]
  have hlk : originalRuntimeCode.lookup (ofString "u256_from_be") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        arithSourceBody Guest.Software.guestFn_u256_from_be, arithU256Shape) :=
    lookup_of_guestAst_getElem 86 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_u256_from_be) rfl
  refine ReadFailure.decCall_two_arg_any s (ofString "x") (ofString "u256_from_be")
    (ofString "p") (ofString "n") arithU256Shape arithU256Shape _ _ _ _ b (by decide) hlk hg
    (by simp [arithEval, evalHOLExact, hd]) ?_
  intro v2 hv2 st hgst hpst hnst
  have hv2_eq : v2 = .val (.word 32#64) := by
    simpa [arithEval, evalHOLExact] using hv2.symm
  subst hv2_eq
  exact u256_from_be_32_outside st b hgst hpst hnst hb

theorem touch_dec_bn254_parse_g1 (addrExp outArg : ExpHOL 64) (rest : ProgHOL 64) :
    DomainTouch addrExp
      (.dec (ofString "chunk") .one addrExp
        (.decCall (ofString "e1") .one (ofString "bn254_parse_g1")
          [.var .local (ofString "chunk"), outArg] rest)) := by
  intro F s hg hflow
  rw [evaluateHOLFiniteState_dec_total] at hflow
  dsimp only at hflow
  rcases hval : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) addrExp with _ | val
  · rw [hval] at hflow; simp at hflow
  · rw [hval] at hflow; dsimp only at hflow
    split at hflow
    · rename_i hsh
      obtain ⟨b, rfl⟩ := shape_one_word hsh
      refine ⟨b, rfl, ?_⟩
      by_contra hout
      let s1 := setVarHOLFinite (ofString "chunk") (.val (.word b)) s
      have hlk : originalRuntimeCode.lookup (ofString "bn254_parse_g1") =
          some ([(ofString "data", .one), (ofString "out", .one)],
            arithSourceBody Guest.Software.guestFn_bn254_parse_g1, .one) :=
        lookup_of_guestAst_getElem 686 (by rw [guestAst_len]; decide)
          (extractFn Guest.Software.guestFn_bn254_parse_g1) rfl
      have hf : ReadFailure s1
          (.decCall (ofString "e1") .one (ofString "bn254_parse_g1")
            [.var .local (ofString "chunk"), outArg] rest) := by
        refine ReadFailure.decCall_two_arg_any s1 (ofString "e1") (ofString "bn254_parse_g1")
          (ofString "data") (ofString "out") .one .one _ _ _ _ b (by decide) hlk
          (guestInv_setVar _ _ s hg)
          (by simp [s1, arithEval, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
          ?_
        intro _ _ st hgst hdst _
        exact bn254_parse_g1_outside st b hgst hdst hout
      unfold ReadFailure at hf
      rcases hrun : evaluateHOLFiniteState s1
          (.decCall (ofString "e1") .one (ofString "bn254_parse_g1")
            [.var .local (ofString "chunk"), outArg] rest) with ⟨res, post⟩
      rw [hrun] at hf hflow
      rcases hf with hf | hf <;> dsimp only at hf <;> subst res <;> simp at hflow
    · simp at hflow

/-! ### 2. `bn254_pairing_check` and `pre_alt_bn128_pairing_check` -/

theorem fb_bn254_pairing_check_of
    (h_fq12_inv : TerminatingFunBoundedOn GuestInv (ofString "fq12_inv") K.«fq12_inv») :
    TerminatingFunBoundedOn GuestInv (ofString "bn254_pairing_check") K.«bn254_pairing_check» := by
  have _ := fb_bn254_init
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fe_set_one
  have _ := fb_bn254_parse_g1
  have _ := fb_bn254_parse_g2
  have _ := fb_ecp_mul
  have _ := fb_ecp_is_inf
  have _ := fb_fq12_twist
  have _ := fb_fq12_cast
  have _ := fb_bn254_miller_raw
  have _ := fb_fq12_mul
  have _ := h_fq12_inv
  have _ := fb_fq12_pow_words
  have _ := fb_memzero
  have _ := fb_memeq
  have _ := fb_heap_release
  bls_unfold 691 Guest.Software.guestFn_bn254_pairing_check
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    apply while_scaled_walk_guestInv (ofString "pairs") (ofString "i") 192
    · bls_auto
    · exact touch_dec_bn254_parse_g1 _ _ _
    · bls_counter_step
    · rfl
    · decide
    · decide
  · clear * -
    unfold K.«bn254_pairing_check»
    rw [domainBytes_eq]
    fast_generalize_K
    simp only [Nat.add_zero, nat_max_eq]
    omega

theorem fb_pre_alt_bn128_pairing_check_of
    (h_bn254_pairing_check : TerminatingFunBoundedOn GuestInv
      (ofString "bn254_pairing_check") K.«bn254_pairing_check») :
    TerminatingFunBoundedOn GuestInv
      (ofString "pre_alt_bn128_pairing_check") K.«pre_alt_bn128_pairing_check» := by
  have _ := fb_udivmod
  have _ := fb_charge_gas
  have _ := h_bn254_pairing_check
  have _ := fb_alloc
  have _ := fb_memzero
  bls_prove 694 Guest.Software.guestFn_pre_alt_bn128_pairing_check K.«pre_alt_bn128_pairing_check»

end InitECandidate.Solver.Wave8GuestInv.R16ArithPort
