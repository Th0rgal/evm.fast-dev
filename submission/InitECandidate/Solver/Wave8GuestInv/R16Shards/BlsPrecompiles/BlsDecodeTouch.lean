import InitECandidate.Solver.Wave8GuestInv.R16Shards.BlsPrecompiles.BlsFpBase
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.ReadFailure

/-! Scaled memory-walk combinator (`stride ≤ 512`) and `DomainTouch` proofs for `g1_decode` and
`g2_decode` entry checks via `bls_fp_decode64` -> `is_zero_bytes(..., 16)`.
Used by `bls_g1_msm_exec` (stride 160), `bls_g2_msm_exec` (stride 288), and `bls_pairing_exec`
(stride 384). Zero `LeafStatements.lean` dependency, zero `sorry`. -/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.BlsPrecompiles

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common
open InitECandidate.Solver.Wave8GuestInv.Arith (ReadFailure arithEval arith_loadByte_none
  arith_two_arg_lookup_inv_shape arithSourceBody)

/-! ### 1. Scaled ordinary-domain memory walk (`stride ≤ 512`) -/

theorem domainRank_add_lt512 (a : BitVec 64) (step : Nat)
    (ha : sourceBase ≤ a.toNat ∧ a.toNat < heapEnd)
    (hstep : 0 < step) (hsmall : step ≤ 512) :
    domainRank (a + BitVec.ofNat 64 step) < domainRank a := by
  have hend : heapEnd + 512 < 2 ^ 64 := by decide
  have hadd : (a + BitVec.ofNat 64 step).toNat = a.toNat + step := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  unfold domainRank
  rw [if_pos ha, hadd]
  split_ifs <;> omega

private theorem scaled_locals_inv_stride {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base counter : MlS) (stride : Nat) (address : BitVec 64)
    (h : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local base, .panop .mul [.var .local counter, .const (BitVec.ofNat 64 stride)]]) =
      some (.val (.word address))) :
    ∃ b i : BitVec 64, s.locals.lookup base = some (.val (.word b)) ∧
      s.locals.lookup counter = some (.val (.word i)) ∧
      address = b + i * BitVec.ofNat 64 stride := by
  cases hb : s.locals.lookup base with
  | none => simp [evalHOLExact, evalListHOLExact, hb] at h
  | some bv =>
    cases bv with
    | rStruct _ =>
      cases hi : s.locals.lookup counter with
      | none => simp [evalHOLExact, evalListHOLExact, hb, hi] at h
      | some v =>
        cases v with
        | val w => cases w; simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, valueWord, panOpHOL] at h
        | rStruct _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
        | nStruct _ _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
    | nStruct _ _ =>
      cases hi : s.locals.lookup counter with
      | none => simp [evalHOLExact, evalListHOLExact, hb, hi] at h
      | some v =>
        cases v with
        | val w => cases w; simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, valueWord, panOpHOL] at h
        | rStruct _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
        | nStruct _ _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
    | val bw =>
      cases bw with
      | word b =>
        cases hi : s.locals.lookup counter with
        | none => simp [evalHOLExact, evalListHOLExact, hb, hi] at h
        | some iv =>
          cases iv with
          | rStruct _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
          | nStruct _ _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
          | val iw =>
            cases iw with
            | word i =>
              refine ⟨b, i, rfl, rfl, ?_⟩
              simpa [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, valueWord,
                wordOpHOL, wordOp, panOpHOL] using h.symm

def scaledWalkMu (stride : Nat) (base counter : MlS) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup base, s.locals.lookup counter with
  | some (.val (.word b)), some (.val (.word i)) => domainRank (b + i * BitVec.ofNat 64 stride)
  | _, _ => 0

theorem scaledWalkMu_bound (stride : Nat) (base counter : MlS) {F : Type}
    (s : PanSemStateFiniteExact 64 F) :
    scaledWalkMu stride base counter s ≤ domainBytes + 1 := by
  unfold scaledWalkMu
  split
  · exact domainRank_bound _
  · omega

theorem while_scaled_walk_guestInv (base counter : MlS) (stride : Nat) (condition : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (htouch : DomainTouch
      (.op .add [.var .local base, .panop .mul [.var .local counter, .const (BitVec.ofNat 64 stride)]])
      body)
    (hadd : CounterStep counter 1#64 body)
    (hbase : avoidsLocal base body = true)
    (hstep : 0 < stride) (hsmall : stride ≤ 512) :
    TerminatingProgBoundedOn GuestInv (.while condition body) ((domainBytes + 1 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv condition body B (domainBytes + 1)
    (scaledWalkMu stride base counter)
    (fun s hs => guestInv_decClock s hs) hbody
    (fun s _ _ _ => scaledWalkMu_bound stride base counter s) ?_
  intro F s _ hguest _ hflow
  have hguest' := guestInv_decClock s hguest
  obtain ⟨addr, haddr, hlow, hhigh⟩ := htouch (decClockHOLFinite s) hguest' hflow
  obtain ⟨b, i, hb, hi, rfl⟩ := scaled_locals_inv_stride (decClockHOLFinite s) base counter stride addr haddr
  have hipost := hadd (decClockHOLFinite s) i hi hflow
  have hbpost := evaluate_avoidsLocal_flowing base body hbase (decClockHOLFinite s)
    (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
  change s.locals.lookup base = some (.val (.word b)) at hb
  change s.locals.lookup counter = some (.val (.word i)) at hi
  have hbpost' := hbpost.trans hb
  refine ⟨guestInv_evaluate (decClockHOLFinite s) body hguest', ?_⟩
  have heq : b + (i + 1#64) * BitVec.ofNat 64 stride =
      (b + i * BitVec.ofNat 64 stride) + BitVec.ofNat 64 stride := by
    rw [BitVec.add_mul, BitVec.one_mul, BitVec.add_assoc]
  simpa only [scaledWalkMu, hipost, hbpost', hb, hi, heq]
    using domainRank_add_lt512 (b + i * BitVec.ofNat 64 stride) stride ⟨hlow, hhigh⟩ hstep hsmall

macro "bls_counter_step" : tactic => `(tactic| repeat (first
  | exact CounterStep.assign _ _
  | exact CounterStep.sub_one _
  | apply CounterStep.dec _ _ _ _ _ (by decide)
  | apply CounterStep.decCall _ _ _ _ _ _ (by decide)
  | apply CounterStep.seq _ _ _ (by decide) (by decide)))

/-! ### 2. `ReadFailure` propagation across `is_zero_bytes` -> `bls_fp_decode64` -> `g1/g2_decode` -/

private theorem outside_byte_memaddrs {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b : BitVec 64) (hg : GuestInv s)
    (hb : ¬ (sourceBase ≤ b.toNat ∧ b.toNat < heapEnd)) :
    ¬ s.memaddrs (panByteAlignHOL b) := by
  intro h; rw [hg.memaddrs] at h; exact hb (ordinaryDomain_byte_interval b h)

private theorem ReadFailure.ite_cond_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (cond : ExpHOL 64) (yes no : ProgHOL 64)
    (hc : arithEval s cond = none) :
    ReadFailure s (.ite cond yes no) := by
  unfold ReadFailure
  rw [evaluateHOLFiniteState_ite]
  dsimp only [arithEval] at hc
  rw [hc]
  simp

private theorem ReadFailure.decCall_two_arg {F : Type} (s : PanSemStateFiniteExact 64 F)
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

private theorem is_zero_bytes_16_outside {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b : BitVec 64) (hg : GuestInv s)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word b)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word 16#64)))
    (hb : ¬ (sourceBase ≤ b.toNat ∧ b.toNat < heapEnd)) :
    ReadFailure s (arithSourceBody Guest.Software.guestFn_is_zero_bytes) := by
  have hbody : arithSourceBody Guest.Software.guestFn_is_zero_bytes =
      .dec (ofString "i") .one (.const 0#64)
        (.seq
          (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
            (.seq
              (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])) (.const 0#64))
                (.return (.const 0#64))
                .skip)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))))
          (.return (.const 1#64))) := rfl
  rw [hbody]
  apply ReadFailure.dec s _ _ _ _ (.val (.word 0#64)) rfl
  let s0 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s
  have hg0 : GuestInv s0 := guestInv_setVar _ _ s hg
  have hp0 : s0.locals.lookup (ofString "p") = some (.val (.word b)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp,
      show ofString "i" ≠ ofString "p" by decide]
  have hn0 : s0.locals.lookup (ofString "n") = some (.val (.word 16#64)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "i" ≠ ofString "n" by decide]
  have hi0 : s0.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  apply ReadFailure.seq
  have hcond : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
      some (.val (.word 1#64)) := by
    simp [evalHOLFinite, evalHOLExact, hi0, hn0, wordCmpHOL]
  apply ReadFailure.while s0 _ _ 1#64 hcond (by decide)
  apply ReadFailure.seq
  apply ReadFailure.ite_cond_none
  have ha : arithEval (decClockHOLFinite s0)
      (.op .add [.var .local (ofString "p"), .var .local (ofString "i")]) =
      some (.val (.word b)) := by
    simp [arithEval, evalHOLExact, evalListHOLExact, decClockHOLFinite, hp0, hi0,
      wordOpHOL, wordOp, valueIsWord, valueWord]
  have hlb := arith_loadByte_none (decClockHOLFinite s0) _ b ha (outside_byte_memaddrs s0 b hg0 hb)
  simp [arithEval, evalHOLExact] at hlb ⊢
  rw [hlb]

private def decCallRest (p : ProgHOL 64) : ProgHOL 64 :=
  match p with | .decCall _ _ _ _ rest => rest | _ => .skip

private theorem bls_fp_decode64_outside {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b : BitVec 64) (hg : GuestInv s)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word b)))
    (hb : ¬ (sourceBase ≤ b.toNat ∧ b.toNat < heapEnd)) :
    ReadFailure s (arithSourceBody Guest.Software.guestFn_bls_fp_decode64) := by
  have hbody : arithSourceBody Guest.Software.guestFn_bls_fp_decode64 =
      .decCall (ofString "z") .one (ofString "is_zero_bytes")
        [.var .local (ofString "p"), .const 16#64]
        (decCallRest (arithSourceBody Guest.Software.guestFn_bls_fp_decode64)) := rfl
  rw [hbody]
  have hlk : originalRuntimeCode.lookup (ofString "is_zero_bytes") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        arithSourceBody Guest.Software.guestFn_is_zero_bytes, .one) :=
    lookup_of_guestAst_getElem 19 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_is_zero_bytes) rfl
  refine ReadFailure.decCall_two_arg s (ofString "z") (ofString "is_zero_bytes")
    (ofString "p") (ofString "n") .one .one _ _ _ _ b (by decide) hlk hg
    (by simp [arithEval, evalHOLExact, hp]) ?_
  intro v2 hv2 st hgst hpst hnst
  have hv2_eq : v2 = .val (.word 16#64) := by
    simpa [arithEval, evalHOLExact] using hv2.symm
  subst hv2_eq
  exact is_zero_bytes_16_outside st b hgst hpst hnst hb

private theorem g1_decode_outside {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b : BitVec 64) (hg : GuestInv s)
    (hd : s.locals.lookup (ofString "data") = some (.val (.word b)))
    (hb : ¬ (sourceBase ≤ b.toNat ∧ b.toNat < heapEnd)) :
    ReadFailure s (arithSourceBody Guest.Software.guestFn_g1_decode) := by
  have hbody : arithSourceBody Guest.Software.guestFn_g1_decode =
      .decCall (ofString "okx") .one (ofString "bls_fp_decode64")
        [.var .local (ofString "data"), .var .local (ofString "r")]
        (decCallRest (arithSourceBody Guest.Software.guestFn_g1_decode)) := rfl
  rw [hbody]
  have hlk : originalRuntimeCode.lookup (ofString "bls_fp_decode64") =
      some ([(ofString "p", .one), (ofString "out", .one)],
        arithSourceBody Guest.Software.guestFn_bls_fp_decode64, .one) :=
    lookup_of_guestAst_getElem 719 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_bls_fp_decode64) rfl
  refine ReadFailure.decCall_two_arg s (ofString "okx") (ofString "bls_fp_decode64")
    (ofString "p") (ofString "out") .one .one _ _ _ _ b (by decide) hlk hg
    (by simp [arithEval, evalHOLExact, hd]) ?_
  intro _ _ st hgst hpst _
  exact bls_fp_decode64_outside st b hgst hpst hb

private theorem g2_decode_outside {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b : BitVec 64) (hg : GuestInv s)
    (hd : s.locals.lookup (ofString "data") = some (.val (.word b)))
    (hb : ¬ (sourceBase ≤ b.toNat ∧ b.toNat < heapEnd)) :
    ReadFailure s (arithSourceBody Guest.Software.guestFn_g2_decode) := by
  have hbody : arithSourceBody Guest.Software.guestFn_g2_decode =
      .decCall (ofString "ok") .one (ofString "bls_fp_decode64")
        [.var .local (ofString "data"), .var .local (ofString "r")]
        (decCallRest (arithSourceBody Guest.Software.guestFn_g2_decode)) := rfl
  rw [hbody]
  have hlk : originalRuntimeCode.lookup (ofString "bls_fp_decode64") =
      some ([(ofString "p", .one), (ofString "out", .one)],
        arithSourceBody Guest.Software.guestFn_bls_fp_decode64, .one) :=
    lookup_of_guestAst_getElem 719 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_bls_fp_decode64) rfl
  refine ReadFailure.decCall_two_arg s (ofString "ok") (ofString "bls_fp_decode64")
    (ofString "p") (ofString "out") .one .one _ _ _ _ b (by decide) hlk hg
    (by simp [arithEval, evalHOLExact, hd]) ?_
  intro _ _ st hgst hpst _
  exact bls_fp_decode64_outside st b hgst hpst hb

private theorem shape_one_word {v : ValueHOL 64}
    (h : shapeEqHOL .one (shapeOfHOLExact v) = true) : ∃ w : BitVec 64, v = .val (.word w) := by
  cases v with
  | val wl => cases wl with | word w => exact ⟨w, rfl⟩
  | rStruct _ => simp [shapeOfHOLExact, shapeEqHOL] at h
  | nStruct _ _ => simp [shapeOfHOLExact, shapeEqHOL] at h

theorem touch_dec_g1_decode (addrExp pArg : ExpHOL 64) (rest : ProgHOL 64) :
    DomainTouch addrExp
      (.dec (ofString "d") .one addrExp
        (.decCall (ofString "ok") .one (ofString "g1_decode")
          [.var .local (ofString "d"), pArg] rest)) := by
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
      let s1 := setVarHOLFinite (ofString "d") (.val (.word b)) s
      have hlk : originalRuntimeCode.lookup (ofString "g1_decode") =
          some ([(ofString "data", .one), (ofString "r", .one)],
            arithSourceBody Guest.Software.guestFn_g1_decode, .one) :=
        lookup_of_guestAst_getElem 767 (by rw [guestAst_len]; decide)
          (extractFn Guest.Software.guestFn_g1_decode) rfl
      have hf : ReadFailure s1
          (.decCall (ofString "ok") .one (ofString "g1_decode")
            [.var .local (ofString "d"), pArg] rest) := by
        refine ReadFailure.decCall_two_arg s1 (ofString "ok") (ofString "g1_decode")
          (ofString "data") (ofString "r") .one .one _ _ _ _ b (by decide) hlk
          (guestInv_setVar _ _ s hg)
          (by simp [s1, arithEval, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
          ?_
        intro _ _ st hgst hdst _
        exact g1_decode_outside st b hgst hdst hout
      unfold ReadFailure at hf
      rcases hrun : evaluateHOLFiniteState s1
          (.decCall (ofString "ok") .one (ofString "g1_decode")
            [.var .local (ofString "d"), pArg] rest) with ⟨res, post⟩
      rw [hrun] at hf hflow
      rcases hf with hf | hf <;> dsimp only at hf <;> subst res <;> simp at hflow
    · simp at hflow

theorem touch_dec_g2_decode (addrExp pArg : ExpHOL 64) (rest : ProgHOL 64) :
    DomainTouch addrExp
      (.dec (ofString "d") .one addrExp
        (.decCall (ofString "ok") .one (ofString "g2_decode")
          [.var .local (ofString "d"), pArg] rest)) := by
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
      let s1 := setVarHOLFinite (ofString "d") (.val (.word b)) s
      have hlk : originalRuntimeCode.lookup (ofString "g2_decode") =
          some ([(ofString "data", .one), (ofString "r", .one)],
            arithSourceBody Guest.Software.guestFn_g2_decode, .one) :=
        lookup_of_guestAst_getElem 779 (by rw [guestAst_len]; decide)
          (extractFn Guest.Software.guestFn_g2_decode) rfl
      have hf : ReadFailure s1
          (.decCall (ofString "ok") .one (ofString "g2_decode")
            [.var .local (ofString "d"), pArg] rest) := by
        refine ReadFailure.decCall_two_arg s1 (ofString "ok") (ofString "g2_decode")
          (ofString "data") (ofString "r") .one .one _ _ _ _ b (by decide) hlk
          (guestInv_setVar _ _ s hg)
          (by simp [s1, arithEval, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
          ?_
        intro _ _ st hgst hdst _
        exact g2_decode_outside st b hgst hdst hout
      unfold ReadFailure at hf
      rcases hrun : evaluateHOLFiniteState s1
          (.decCall (ofString "ok") .one (ofString "g2_decode")
            [.var .local (ofString "d"), pArg] rest) with ⟨res, post⟩
      rw [hrun] at hf hflow
      rcases hf with hf | hf <;> dsimp only at hf <;> subst res <;> simp at hflow
    · simp at hflow

end InitECandidate.Solver.Wave8GuestInv.R16Shards.BlsPrecompiles
