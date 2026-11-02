import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.Exec

/-! Proof of `wk_u256_to_be_min` on frozen spec rev9 (`8a79d9f28`) for contract micro-shard m13. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8GuestInv.M13

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. `LocFrame` and return-value upper bound (`≤ 32`) for `u256_byte_length` and `u256_limb` -/

theorem lookup_u256_limb :
    originalRuntimeCode.lookup (ofString "u256_limb") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]), (ofString "i", .one)],
        sourceFnBody Guest.Software.guestFn_u256_limb, .one) :=
  lookup_of_guestAst_getElem 43 (by rw [guestAst_len]; omega)
    (extractFn Guest.Software.guestFn_u256_limb) rfl

theorem funLocFrame_u256_limb : FunLocFrame (ofString "u256_limb") :=
  funLocFrame_of_locOnlyW 43 (by rw [guestAst_len]; omega)
    Guest.Software.guestFn_u256_limb rfl rfl

theorem lookup_bit_length64 :
    originalRuntimeCode.lookup (ofString "bit_length64") =
      some ([(ofString "x", .one)], sourceFnBody Guest.Software.guestFn_bit_length64, .one) :=
  lookup_of_guestAst_getElem 77 (by rw [guestAst_len]; omega)
    (extractFn Guest.Software.guestFn_bit_length64) rfl

theorem funLocFrame_bit_length64 : FunLocFrame (ofString "bit_length64") :=
  funLocFrame_of_locOnlyW 77 (by rw [guestAst_len]; omega)
    Guest.Software.guestFn_bit_length64 rfl rfl

theorem lookup_u256_bit_length :
    originalRuntimeCode.lookup (ofString "u256_bit_length") =
      some ([(ofString "a", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_u256_bit_length, .one) :=
  lookup_of_guestAst_getElem 78 (by rw [guestAst_len]; omega)
    (extractFn Guest.Software.guestFn_u256_bit_length) rfl

theorem funLocFrame_u256_bit_length : FunLocFrame (ofString "u256_bit_length") := by
  refine ⟨_, _, _, lookup_u256_bit_length, fun s hcode => ?_⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_bit_length,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  apply locFrame_seq
  · apply locFrame_ite
    · exact locFrame_decCall hcode funLocFrame_bit_length64 _ _ _ (fun t _ => locFrameW_eval _ rfl t)
    · exact locFrameW_eval _ rfl s
  · intro m1 hm1
    have hc1 := hm1.code.trans hcode
    apply locFrame_seq
    · apply locFrame_ite
      · exact locFrame_decCall hc1 funLocFrame_bit_length64 _ _ _ (fun t _ => locFrameW_eval _ rfl t)
      · exact locFrameW_eval _ rfl m1
    · intro m2 hm2
      have hc2 := hm2.code.trans hc1
      apply locFrame_seq
      · apply locFrame_ite
        · exact locFrame_decCall hc2 funLocFrame_bit_length64 _ _ _ (fun t _ => locFrameW_eval _ rfl t)
        · exact locFrameW_eval _ rfl m2
      · intro m3 hm3
        exact locFrame_tailCall (hm3.code.trans hc2) funLocFrame_bit_length64 _

theorem lookup_u256_byte_length :
    originalRuntimeCode.lookup (ofString "u256_byte_length") =
      some ([(ofString "a", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_u256_byte_length, .one) :=
  lookup_of_guestAst_getElem 79 (by rw [guestAst_len]; omega)
    (extractFn Guest.Software.guestFn_u256_byte_length) rfl

theorem locFrame_u256_byte_length_body {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) :
    LocFrame s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_byte_length)).2 := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_byte_length,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact locFrame_decCall hcode funLocFrame_u256_bit_length _ _ _ (fun t _ => locFrameW_eval _ rfl t)

theorem funLocFrame_u256_byte_length : FunLocFrame (ofString "u256_byte_length") :=
  ⟨_, _, _, lookup_u256_byte_length, fun s hcode => locFrame_u256_byte_length_body s hcode⟩

theorem lookup_u256_to_be_min :
    originalRuntimeCode.lookup (ofString "u256_to_be_min") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_u256_to_be_min, .one) :=
  lookup_of_guestAst_getElem 88 (by rw [guestAst_len]; omega)
    (extractFn Guest.Software.guestFn_u256_to_be_min) rfl

/-! ### Upper bound on `bit_length64`, `u256_bit_length`, `u256_byte_length` -/

private def bitStepProg (sh : Nat) : ProgHOL 64 :=
  .ite (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const (BitVec.ofNat 64 sh))) (.const (BitVec.ofNat 64 0)))
    (.seq
      (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const (BitVec.ofNat 64 sh)]))
      (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const (BitVec.ofNat 64 sh)))))
    .skip

private theorem bitStepProg_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nv xv : BitVec 64) (sh : Nat) (nMax : Nat)
    (hsh_pos : 0 < sh) (hsh_lt : sh < 64)
    (hx_lt : xv.toNat < 2 ^ (2 * sh))
    (hn_le : nv.toNat ≤ nMax)
    (hsum_lt : nMax + sh < 2 ^ 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nv)))
    (hx : s.locals.lookup (ofString "x") = some (.val (.word xv))) :
    ∀ mid, evaluateHOLFiniteState s (bitStepProg sh) = (none, mid) →
      ∃ nv' xv' : BitVec 64,
        mid.locals.lookup (ofString "n") = some (.val (.word nv')) ∧
        mid.locals.lookup (ofString "x") = some (.val (.word xv')) ∧
        nv'.toNat ≤ nMax + sh ∧ xv'.toNat < 2 ^ sh := by
  intro mid hrun
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  have hsh_bv : (BitVec.ofNat 64 sh).toNat = sh := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsh_cond : ¬ (sh ≠ 0 ∧ 64 ≤ sh) := by omega
  dsimp only [bitStepProg] at hrun
  rw [evaluateHOLFiniteState_ite] at hrun
  have hevc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const (BitVec.ofNat 64 sh))) (.const (BitVec.ofNat 64 0))) =
      some (.val (.word (if (xv >>> sh) = 0#64 then 0#64 else 1#64))) := by
    simp [evalHOLExact, hx, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, wordShiftHOL, hsh_bv, hsh_cond]
  rw [hevc] at hrun; dsimp only at hrun
  by_cases hnz : (xv >>> sh) ≠ 0#64
  · have hne0 : ¬ ((xv >>> sh) = 0#64) := hnz
    rw [if_neg hne0] at hrun
    have h1 : ¬ ((1#64 : BitVec 64) = 0) := by intro h; cases h
    rw [if_neg h1] at hrun
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hrun
    have hev_add : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.op .add [.var .local (ofString "n"), .const (BitVec.ofNat 64 sh)]) =
        some (.val (.word (nv + BitVec.ofNat 64 sh))) := by
      simp [evalHOLExact, evalListHOLExact, hn, wordOpHOL, wordOp, valueIsWord, valueWord]
    rw [hev_add] at hrun; dsimp only at hrun
    have hval1 : isValidValueHOLFinite s .local (ofString "n") (.val (.word (nv + BitVec.ofNat 64 sh))) = true := by
      simp [isValidValueHOLFinite, lookupKvarHOLFinite, hn, shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hval1] at hrun; dsimp only at hrun
    set s1 := setKvarHOLFinite .local (ofString "n") (.val (.word (nv + BitVec.ofNat 64 sh))) s
    have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word (nv + BitVec.ofNat 64 sh))) := by
      simp [s1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs1_x : s1.locals.lookup (ofString "x") = some (.val (.word xv)) := by
      simp [s1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hx,
        show ofString "n" ≠ ofString "x" from mls_ne rfl]
    rw [evaluateHOLFiniteState_assign] at hrun
    have hev_sh : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.shift .lsr (.var .local (ofString "x")) (.const (BitVec.ofNat 64 sh))) =
        some (.val (.word (xv >>> sh))) := by
      simp [evalHOLExact, hs1_x, wordShiftHOL, hsh_bv, hsh_cond]
    rw [hev_sh] at hrun; dsimp only at hrun
    have hval2 : isValidValueHOLFinite s1 .local (ofString "x") (.val (.word (xv >>> sh))) = true := by
      simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs1_x, shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hval2] at hrun
    injection hrun with _ hmid; subst hmid
    refine ⟨nv + BitVec.ofNat 64 sh, xv >>> sh, ?_, ?_, ?_, ?_⟩
    · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_n,
        show ofString "x" ≠ ofString "n" from mls_ne rfl]
    · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · rw [BitVec.toNat_add, hsh_bv, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have hmul : 2 ^ (2 * sh) = 2 ^ sh * 2 ^ sh := by rw [Nat.two_mul, Nat.pow_add]
      rw [hmul] at hx_lt
      exact Nat.div_lt_of_lt_mul hx_lt
  · have heq0 : (xv >>> sh) = 0#64 := Classical.not_not.mp hnz
    have h0_eq : (0#64 : BitVec 64) = 0 := rfl
    rw [if_pos heq0, if_pos h0_eq, evaluateHOLFiniteState_skip] at hrun
    injection hrun with _ hmid; subst hmid
    have hdiv0 : xv.toNat / 2 ^ sh = 0 := by
      have := congrArg BitVec.toNat heq0
      rwa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
    refine ⟨nv, xv, hn, hx, by omega, ?_⟩
    exact Nat.lt_of_div_eq_zero (Nat.two_pow_pos sh) hdiv0

theorem bit_length64_body_le_64 {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bit_length64)).1 =
      some (.returned v)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ 64 := by
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  have hbody : sourceFnBody Guest.Software.guestFn_bit_length64 =
      .dec (ofString "n") .one (.const 0#64)
        (.seq (bitStepProg 32)
          (.seq (bitStepProg 16)
            (.seq (bitStepProg 8)
              (.seq (bitStepProg 4)
                (.seq (bitStepProg 2)
                  (.seq (bitStepProg 1)
                    (.return (.op .add [.var .local (ofString "n"), .var .local (ofString "x")])))))))) := rfl
  rw [hbody, evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
  have h0_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const 0#64) =
      some (.val (.word 0#64)) := rfl
  rw [h0_ev] at hret; dsimp only at hret
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh0] at hret; dsimp only at hret
  set s0 := setVarHOLFinite (ofString "n") (.val (.word 0#64)) s
  have hn0 : s0.locals.lookup (ofString "n") = some (.val (.word 0#64)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  -- If `x` is not a word in `s0.locals`, the very first `bitStepProg 32` errors (`(some .error, _)`):
  have hx_word : ∃ xv : BitVec 64, s0.locals.lookup (ofString "x") = some (.val (.word xv)) := by
    rcases hx_opt : s0.locals.lookup (ofString "x") with _ | xval
    · rw [evaluateHOLFiniteState_seq_line780] at hret
      dsimp only [bitStepProg] at hret
      rw [evaluateHOLFiniteState_ite] at hret
      have hev_none : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
          (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const (BitVec.ofNat 64 32))) (.const (BitVec.ofNat 64 0))) = none := by
        simp [evalHOLExact, hx_opt]
      rw [hev_none] at hret; simp at hret
    · cases xval with
      | val wl => cases wl with | word xv => exact ⟨xv, rfl⟩
      | rStruct _ =>
        rw [evaluateHOLFiniteState_seq_line780] at hret; dsimp only [bitStepProg] at hret
        rw [evaluateHOLFiniteState_ite] at hret
        have hev_none : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
            (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const (BitVec.ofNat 64 32))) (.const (BitVec.ofNat 64 0))) = none := by
          simp [evalHOLExact, hx_opt]
        rw [hev_none] at hret; simp at hret
      | nStruct _ _ =>
        rw [evaluateHOLFiniteState_seq_line780] at hret; dsimp only [bitStepProg] at hret
        rw [evaluateHOLFiniteState_ite] at hret
        have hev_none : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
            (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const (BitVec.ofNat 64 32))) (.const (BitVec.ofNat 64 0))) = none := by
          simp [evalHOLExact, hx_opt]
        rw [hev_none] at hret; simp at hret
  obtain ⟨x0, hx0⟩ := hx_word
  have noRetStep : ∀ {st : PanSemStateFiniteExact 64 F} {sh : Nat} {w : ValueHOL 64},
      (evaluateHOLFiniteState st (bitStepProg sh)).1 ≠ some (.returned w) := by
    intro st sh w
    dsimp only [bitStepProg]
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · rw [evaluateHOLFiniteState_skip]; simp
      · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        split
        · simp
        · split
          · dsimp only; rw [evaluateHOLFiniteState_assign]
            split
            · simp
            · split <;> simp
          · simp
    · simp
  -- Step 1..6:
  rw [evaluateHOLFiniteState_seq_line780] at hret
  rcases hr1 : evaluateHOLFiniteState s0 (bitStepProg 32) with ⟨r1, s1⟩
  rw [hr1] at hret
  cases r1 with
  | some r1' => exact absurd hret (by have := @noRetStep s0 32 v; rw [hr1] at this; exact this)
  | none =>
    dsimp only at hret
    obtain ⟨n1, x1, hn1, hx1, hnb1, hxb1⟩ := bitStepProg_bound s0 0 x0 32 0
      (by omega) (by omega) x0.isLt (by rfl) (by omega) hn0 hx0 s1 hr1
    rw [evaluateHOLFiniteState_seq_line780] at hret
    rcases hr2 : evaluateHOLFiniteState s1 (bitStepProg 16) with ⟨r2, s2⟩
    rw [hr2] at hret
    cases r2 with
    | some _ => exact absurd hret (by have := @noRetStep s1 16 v; rw [hr2] at this; exact this)
    | none =>
      dsimp only at hret
      obtain ⟨n2, x2, hn2, hx2, hnb2, hxb2⟩ := bitStepProg_bound s1 n1 x1 16 32
        (by omega) (by omega) hxb1 hnb1 (by omega) hn1 hx1 s2 hr2
      rw [evaluateHOLFiniteState_seq_line780] at hret
      rcases hr3 : evaluateHOLFiniteState s2 (bitStepProg 8) with ⟨r3, s3⟩
      rw [hr3] at hret
      cases r3 with
      | some _ => exact absurd hret (by have := @noRetStep s2 8 v; rw [hr3] at this; exact this)
      | none =>
        dsimp only at hret
        obtain ⟨n3, x3, hn3, hx3, hnb3, hxb3⟩ := bitStepProg_bound s2 n2 x2 8 48
          (by omega) (by omega) hxb2 hnb2 (by omega) hn2 hx2 s3 hr3
        rw [evaluateHOLFiniteState_seq_line780] at hret
        rcases hr4 : evaluateHOLFiniteState s3 (bitStepProg 4) with ⟨r4, s4⟩
        rw [hr4] at hret
        cases r4 with
        | some _ => exact absurd hret (by have := @noRetStep s3 4 v; rw [hr4] at this; exact this)
        | none =>
          dsimp only at hret
          obtain ⟨n4, x4, hn4, hx4, hnb4, hxb4⟩ := bitStepProg_bound s3 n3 x3 4 56
            (by omega) (by omega) hxb3 hnb3 (by omega) hn3 hx3 s4 hr4
          rw [evaluateHOLFiniteState_seq_line780] at hret
          rcases hr5 : evaluateHOLFiniteState s4 (bitStepProg 2) with ⟨r5, s5⟩
          rw [hr5] at hret
          cases r5 with
          | some _ => exact absurd hret (by have := @noRetStep s4 2 v; rw [hr5] at this; exact this)
          | none =>
            dsimp only at hret
            obtain ⟨n5, x5, hn5, hx5, hnb5, hxb5⟩ := bitStepProg_bound s4 n4 x4 2 60
              (by omega) (by omega) hxb4 hnb4 (by omega) hn4 hx4 s5 hr5
            rw [evaluateHOLFiniteState_seq_line780] at hret
            rcases hr6 : evaluateHOLFiniteState s5 (bitStepProg 1) with ⟨r6, s6⟩
            rw [hr6] at hret
            cases r6 with
            | some _ => exact absurd hret (by have := @noRetStep s5 1 v; rw [hr6] at this; exact this)
            | none =>
              dsimp only at hret
              obtain ⟨n6, x6, hn6, hx6, hnb6, hxb6⟩ := bitStepProg_bound s5 n5 x5 1 62
                (by omega) (by omega) hxb5 hnb5 (by omega) hn5 hx5 s6 hr6
              rw [evaluateHOLFiniteState_return] at hret
              have hev_ret : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a))
                  (.op .add [.var .local (ofString "n"), .var .local (ofString "x")]) =
                  some (.val (.word (n6 + x6))) := by
                simp [evalHOLExact, evalListHOLExact, hn6, hx6, wordOpHOL, wordOp, valueIsWord, valueWord]
              rw [hev_ret] at hret; dsimp only at hret
              split at hret
              · injection hret with h1; injection h1 with hv
                refine ⟨n6 + x6, hv.symm, ?_⟩
                have h21 : (2 ^ 1 : Nat) = 2 := rfl
                rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                omega
              · simp at hret

private theorem decCall_bit_length64_add_le {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode)
    (var : MlS) (arg : ExpHOL 64) (base : BitVec 64) (v : ValueHOL 64)
    (hbase : base.toNat ≤ 192)
    (hret : (evaluateHOLFiniteState s
        (.decCall var .one (ofString "bit_length64") [arg]
          (.return (.op .add [.const base, .var .local var])))).1 = some (.returned v)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ 256 := by
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
  split at hret
  · simp at hret
  · rename_i values _
    split at hret
    · simp at hret
    · rename_i body' callee ret' hl
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "bit_length64")
        [(ofString "x", .one)] (sourceFnBody Guest.Software.guestFn_bit_length64) body' .one ret'
        values callee (by rw [hcode]; exact lookup_bit_length64) hl
      subst hsame
      split at hret
      · simp at hret
      · dsimp only at hret
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_bit_length64) with ⟨rb, post⟩
        rw [hrun] at hret
        rcases rb with _ | rb
        · simp at hret
        · cases rb with
          | returned vb =>
            obtain ⟨wb, rfl, hwb_le⟩ := bit_length64_body_le_64 (callEntryStateHOLFinite s callee) vb (by rw [hrun])
            dsimp only at hret
            split at hret
            · dsimp only at hret
              rw [evaluateHOLFiniteState_return] at hret
              set cs := setVarHOLFinite var (.val (.word wb)) { post with locals := s.locals }
              have hcs_var : cs.locals.lookup var = some (.val (.word wb)) := by
                simp [cs, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              have hev : @evalHOLExact 64 F _ cs.toExact (fun a => Classical.propDecidable (cs.memaddrs a))
                  (.op .add [.const base, .var .local var]) = some (.val (.word (base + wb))) := by
                simp [evalHOLExact, evalListHOLExact, hcs_var, wordOpHOL, wordOp, valueIsWord, valueWord]
              rw [hev] at hret; dsimp only at hret
              split at hret
              · injection hret with h1; injection h1 with hv
                refine ⟨base + wb, hv.symm, ?_⟩
                rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega
              · simp at hret
            · simp at hret
          | _ => simp at hret

theorem u256_bit_length_body_le_256 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_bit_length)).1 =
      some (.returned v)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ 256 := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_bit_length,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map] at hret
  have hbranch : ∀ (st : PanSemStateFiniteExact 64 F) (hc : st.code = originalRuntimeCode)
      (cond : ExpHOL 64) (var : MlS) (arg : ExpHOL 64) (base : BitVec 64) (rest : ProgHOL 64),
      base.toNat ≤ 192 →
      (∀ (st' : PanSemStateFiniteExact 64 F), st'.code = originalRuntimeCode →
        (evaluateHOLFiniteState st' rest).1 = some (.returned v) →
        ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ 256) →
      (evaluateHOLFiniteState st
        (.seq (.ite cond (.decCall var .one (ofString "bit_length64") [arg]
            (.return (.op .add [.const base, .var .local var]))) .skip) rest)).1 =
        some (.returned v) →
      ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ 256 := by
    intro st hc cond var arg base rest hb hrest hseq
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hseq
    split at hseq
    · split at hseq
      · rw [evaluateHOLFiniteState_skip] at hseq; dsimp only at hseq
        exact hrest st hc hseq
      · rcases hdc : evaluateHOLFiniteState st
            (.decCall var .one (ofString "bit_length64") [arg]
              (.return (.op .add [.const base, .var .local var]))) with ⟨r1, m1⟩
        rw [hdc] at hseq
        cases r1 with
        | some r1' =>
          dsimp only at hseq
          exact decCall_bit_length64_add_le st hc var arg base v hb (by rw [hdc]; exact hseq)
        | none =>
          -- `.decCall ... (.return ...)` can NEVER return `none`!
          exfalso
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hdc
          split at hdc
          · simp at hdc
          · split at hdc
            · simp at hdc
            · rename_i b_dc c_dc _ _
              split at hdc
              · simp at hdc
              · dsimp only at hdc
                rcases hbdc : evaluateHOLFiniteState (callEntryStateHOLFinite st c_dc) b_dc with ⟨rb, pb⟩
                rw [hbdc] at hdc; dsimp only at hdc
                rcases rb with _ | rb
                · simp at hdc
                · cases rb with
                  | returned vb =>
                    dsimp only at hdc
                    split at hdc
                    · rw [evaluateHOLFiniteState_return] at hdc
                      split at hdc
                      · simp at hdc
                      · split at hdc <;> simp at hdc
                    · simp at hdc
                  | _ => simp at hdc
    · simp at hseq
  have h192 : (BitVec.ofNat 64 192).toNat ≤ 192 := by
    have : (BitVec.ofNat 64 192).toNat = 192 := rfl; omega
  have h128 : (BitVec.ofNat 64 128).toNat ≤ 192 := by
    have : (BitVec.ofNat 64 128).toNat = 128 := rfl; omega
  have h64 : (BitVec.ofNat 64 64).toNat ≤ 192 := by
    have : (BitVec.ofNat 64 64).toNat = 64 := rfl; omega
  refine hbranch s hcode _ _ _ _ _ h192 (fun s1 hc1 hs1 => ?_) hret
  refine hbranch s1 hc1 _ _ _ _ _ h128 (fun s2 hc2 hs2 => ?_) hs1
  refine hbranch s2 hc2 _ _ _ _ _ h64 (fun s3 hc3 hs3 => ?_) hs2
  -- Final tail call `Prog.call none "bit_length64" [a.0]`:
  rw [evaluateHOLFiniteState_call] at hs3
  split at hs3
  · simp at hs3
  · rename_i values _
    split at hs3
    · simp at hs3
    · rename_i body' callee ret' hl
      have hsame := lookupCodeHOLFinite_installed_body s3.code.lookup (ofString "bit_length64")
        [(ofString "x", .one)] (sourceFnBody Guest.Software.guestFn_bit_length64) body' .one ret'
        values callee (by rw [hc3]; exact lookup_bit_length64) hl
      subst hsame
      split at hs3
      · simp at hs3
      · dsimp only at hs3
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s3 callee)
            (sourceFnBody Guest.Software.guestFn_bit_length64) with ⟨rb, pb⟩
        rw [hrun] at hs3
        rcases rb with _ | rb
        · simp at hs3
        · cases rb with
          | returned vb =>
            obtain ⟨wb, rfl, hwb_le⟩ := bit_length64_body_le_64 (callEntryStateHOLFinite s3 callee) vb (by rw [hrun])
            dsimp only at hs3
            split at hs3
            · injection hs3 with h1; injection h1 with hv
              exact ⟨wb, hv.symm, by omega⟩
            · simp at hs3
          | _ => simp at hs3

theorem u256_byte_length_body_le_32 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_byte_length)).1 =
      some (.returned v)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ 32 := by
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_byte_length,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hret
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
  split at hret
  · simp at hret
  · rename_i values _
    split at hret
    · simp at hret
    · rename_i body' callee ret' hl
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "u256_bit_length")
        [(ofString "a", .comb [.one, .one, .one, .one])]
        (sourceFnBody Guest.Software.guestFn_u256_bit_length) body' .one ret'
        values callee (by rw [hcode]; exact lookup_u256_bit_length) hl
      subst hsame
      split at hret
      · simp at hret
      · dsimp only at hret
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_u256_bit_length) with ⟨rb, post⟩
        rw [hrun] at hret
        rcases rb with _ | rb
        · simp at hret
        · cases rb with
          | returned vb =>
            obtain ⟨nb, rfl, hnb_le⟩ := u256_bit_length_body_le_256 (callEntryStateHOLFinite s callee) hcode vb (by rw [hrun])
            dsimp only at hret
            split at hret
            · dsimp only at hret
              rw [evaluateHOLFiniteState_return] at hret
              set cs := setVarHOLFinite (ofString "n") (.val (.word nb)) { post with locals := s.locals }
              have hcs_n : cs.locals.lookup (ofString "n") = some (.val (.word nb)) := by
                simp [cs, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              have h3 : (3#64 : BitVec 64).toNat = 3 := rfl
              have h7 : (7#64 : BitVec 64).toNat = 7 := rfl
              have hev : @evalHOLExact 64 F _ cs.toExact (fun a => Classical.propDecidable (cs.memaddrs a))
                  (.shift .lsr (.op .add [.var .local (ofString "n"), .const 7#64]) (.const 3#64)) =
                  some (.val (.word ((nb + 7#64) >>> (3 : Nat)))) := by
                simp [evalHOLExact, evalListHOLExact, hcs_n, wordOpHOL, wordOp, valueIsWord, valueWord, wordShiftHOL, h3]
              rw [hev] at hret; dsimp only at hret
              split at hret
              · injection hret with h1; injection h1 with hv
                refine ⟨(nb + 7#64) >>> (3 : Nat), hv.symm, ?_⟩
                rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, h7,
                  Nat.mod_eq_of_lt (by omega)]
                have : (2 ^ 3 : Nat) = 8 := rfl
                omega
              · simp at hret
            · simp at hret
          | _ => simp at hret

/-! ## 2. Loop & body `ByteFrame` for `u256_to_be_min` -/

private theorem lookup_resVarEq_ne (m : HolFiniteMapExact MlS (ValueHOL 64))
    (k q : MlS) (old : Option (ValueHOL 64)) (hne : k ≠ q) :
    (m.resVarEq (k, old)).lookup q = m.lookup q := by
  unfold HolFiniteMapExact.resVarEq
  cases old with
  | none => simp [HolFiniteMapExact.eraseEq, FDOMSUB_HOL, hne.symm]
  | some v => simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, hne.symm]

private def toBeMinLoopBody : ProgHOL 64 :=
  .dec (ofString "pos") .one
    (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64], .var .local (ofString "i")])
    (.decCall (ofString "l") .one (ofString "u256_limb")
      [.var .local (ofString "a"), .shift .lsr (.var .local (ofString "pos")) (.const 3#64)]
      (.seq
        (.storeByte (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
          (.op .and
            [.shift .lsr (.var .local (ofString "l"))
              (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
             .const 255#64]))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))))

private def toBeMinWhile : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) toBeMinLoopBody

private theorem toBeMinLoopBody_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (R : List Ivl) (len iv : BitVec 64)
    (outOpt : Option (ValueHOL 64))
    (hcode : s.code = originalRuntimeCode)
    (hdom_eq : s.memaddrs = ordinaryDomain)
    (hiv_lt : iv.toNat < len.toNat)
    (hlen_le : len.toNat ≤ 32)
    (hlen : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iv)))
    (hout : s.locals.lookup (ofString "out") = outOpt)
    (hR : ∀ outW : BitVec 64, outOpt = some (.val (.word outW)) → (outW.toNat, 32) ∈ R) :
    let res := evaluateHOLFiniteState s toBeMinLoopBody
    ByteFrame R s res.2 ∧
    res.1 ≠ some .continue ∧
    (res.1 = none →
      res.2.code = originalRuntimeCode ∧
      res.2.memaddrs = ordinaryDomain ∧
      res.2.locals.lookup (ofString "len") = some (.val (.word len)) ∧
      res.2.locals.lookup (ofString "out") = outOpt ∧
      ∃ iv' : BitVec 64, res.2.locals.lookup (ofString "i") = some (.val (.word iv'))) := by
  dsimp only [toBeMinLoopBody]
  rw [evaluateHOLFiniteState_dec_total]; dsimp only
  let posv := (len - 1#64) - iv
  have hev_pos : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64], .var .local (ofString "i")]) =
      some (.val (.word posv)) := by
    simp [evalHOLExact, evalListHOLExact, hlen, hi, wordOpHOL, wordOp, valueIsWord, valueWord, posv]
  rw [hev_pos]; dsimp only
  have hsh1 : shapeEqHOL .one (shapeOfHOLExact (.val (.word posv))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh1]; dsimp only
  set s1 := setVarHOLFinite (ofString "pos") (.val (.word posv)) s
  have hs1_len : s1.locals.lookup (ofString "len") = some (.val (.word len)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlen,
      show ofString "pos" ≠ ofString "len" from mls_ne rfl]
  have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word iv)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi,
      show ofString "pos" ≠ ofString "i" from mls_ne rfl]
  have hs1_out : s1.locals.lookup (ofString "out") = outOpt := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hout,
      show ofString "pos" ≠ ofString "out" from mls_ne rfl]
  -- `decCall "l" .one "u256_limb" [...] cont`:
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  split
  · exact ⟨(ByteFrame.refl R s).setVar _ _ |>.locals _, by simp, fun h => by simp at h⟩
  · rename_i values _
    split
    · exact ⟨(ByteFrame.refl R s).setVar _ _ |>.locals _, by simp, fun h => by simp at h⟩
    · rename_i body' callee ret' hl
      have hsame := lookupCodeHOLFinite_installed_body s1.code.lookup (ofString "u256_limb")
        [(ofString "a", .comb [.one, .one, .one, .one]), (ofString "i", .one)]
        (sourceFnBody Guest.Software.guestFn_u256_limb) body' .one ret' values callee
        (by rw [show s1.code = originalRuntimeCode from hcode]; exact lookup_u256_limb) hl
      subst hsame
      split
      · exact ⟨(ByteFrame.refl R s).setVar _ _ |>.emptyLocals.locals _, by simp, fun h => by simp at h⟩
      · dsimp only
        have hlf_b : LocFrame (callEntryStateHOLFinite s1 callee)
            (evaluateHOLFiniteState (callEntryStateHOLFinite s1 callee)
              (sourceFnBody Guest.Software.guestFn_u256_limb)).2 :=
          locFrameW_eval _ rfl _
        rcases hrun_l : evaluateHOLFiniteState (callEntryStateHOLFinite s1 callee)
            (sourceFnBody Guest.Software.guestFn_u256_limb) with ⟨rl, post_l⟩
        rw [hrun_l] at hlf_b
        have hbf_l : ByteFrame R s post_l :=
          ByteFrame.of_locFrame R (by unfold LocFrame at hlf_b ⊢; dsimp only at hlf_b; rw [hlf_b]; rfl)
        rcases rl with _ | rl
        · exact ⟨hbf_l.locals _, by simp, fun h => by simp at h⟩
        · cases rl with
          | returned vl =>
            dsimp only
            split
            · dsimp only
              set s2 := setVarHOLFinite (ofString "l") vl { post_l with locals := s1.locals }
              have hs2_bf : ByteFrame R s s2 := (hbf_l.locals _).setVar _ _
              have hs2_code : s2.code = originalRuntimeCode := by rw [hs2_bf.1]; exact hcode
              have hs2_dom : s2.memaddrs = ordinaryDomain := by rw [hs2_bf.1]; exact hdom_eq
              have hs2_len : s2.locals.lookup (ofString "len") = some (.val (.word len)) := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_len,
                  show ofString "l" ≠ ofString "len" from mls_ne rfl]
              have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word iv)) := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_i,
                  show ofString "l" ≠ ofString "i" from mls_ne rfl]
              have hs2_out : s2.locals.lookup (ofString "out") = outOpt := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_out,
                  show ofString "l" ≠ ofString "out" from mls_ne rfl]
              -- `seq (storeByte ...) (assign "i" (i + 1))`:
              let sbProg : ProgHOL 64 := .storeByte (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
                (.op .and
                  [.shift .lsr (.var .local (ofString "l"))
                    (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
                   .const 255#64])
              have hbf_sb : ByteFrame R s2 (evaluateHOLFiniteState s2 sbProg).2 := by
                refine byteFrame_storeByte s2 _ _ (fun addr hdst hdom => ?_)
                rcases hout_case : outOpt with _ | outVal
                · simp [evalHOLExact, evalListHOLExact, hs2_out, hout_case] at hdst
                · cases outVal with
                  | rStruct _ =>
                    simp [evalHOLExact, evalListHOLExact, hs2_out, hs2_i, hout_case, List.all, wordOpHOL, wordOp, valueIsWord] at hdst
                  | nStruct _ _ =>
                    simp [evalHOLExact, evalListHOLExact, hs2_out, hs2_i, hout_case, List.all, wordOpHOL, wordOp, valueIsWord] at hdst
                  | val wl =>
                    cases wl with
                    | word outW =>
                      have haddr_eq : addr = outW + iv := by
                        simp [evalHOLExact, evalListHOLExact, hs2_out, hs2_i, hout_case,
                          wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                        exact hdst.symm
                      subst haddr_eq
                      rw [hs2_dom] at hdom
                      have hsb_val : sourceBase = 2701131776 := rfl
                      have hnw := add_no_wrap_of_memaddrs outW iv (by omega) hdom
                      exact ⟨(outW.toNat, 32), hR outW hout_case, by rw [hnw.2.1]; omega, by rw [hnw.2.1]; omega⟩
              rw [evaluateHOLFiniteState_seq_line780]
              rcases hsb_run : evaluateHOLFiniteState s2 sbProg with ⟨rsb, s3⟩
              rw [hsb_run] at hbf_sb
              have hsb_ctrl := evaluate_storeByte_control_frame s2
                (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
                (.op .and
                  [.shift .lsr (.var .local (ofString "l"))
                    (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
                   .const 255#64])
              have hsb_r : rsb = none ∨ rsb = some .error := by
                have h1 := hsb_ctrl.1; change (evaluateHOLFiniteState s2 sbProg).1 = _ ∨ (evaluateHOLFiniteState s2 sbProg).1 = _ at h1
                rw [hsb_run] at h1; exact h1
              have hs3_loc : s3.locals = s2.locals := by
                have h2 := hsb_ctrl.2.2.1; change (evaluateHOLFiniteState s2 sbProg).2.locals = s2.locals at h2
                rw [hsb_run] at h2; exact h2
              rcases hsb_r with rfl | rfl
              · dsimp only
                rw [evaluateHOLFiniteState_assign]
                have hs3_i : s3.locals.lookup (ofString "i") = some (.val (.word iv)) := by
                  rw [hs3_loc]; exact hs2_i
                have hs3_len : s3.locals.lookup (ofString "len") = some (.val (.word len)) := by
                  rw [hs3_loc]; exact hs2_len
                have hs3_out : s3.locals.lookup (ofString "out") = outOpt := by
                  rw [hs3_loc]; exact hs2_out
                have hev_inc : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                    (.op .add [.var .local (ofString "i"), .const 1#64]) = some (.val (.word (iv + 1#64))) := by
                  simp [evalHOLExact, evalListHOLExact, hs3_i, wordOpHOL, wordOp, valueIsWord, valueWord]
                rw [hev_inc]; dsimp only
                have hval_i : isValidValueHOLFinite s3 .local (ofString "i") (.val (.word (iv + 1#64))) = true := by
                  simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs3_i, shapeOfHOLExact, shapeEqHOL]
                rw [if_pos hval_i]; dsimp only
                have hbf_all : ByteFrame R s (setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1#64))) s3) :=
                  (hs2_bf.trans hbf_sb).setVar _ _
                let finalSt :=
                  let __src2 := setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1#64))) s3
                  let __src1 : PanSemStateFiniteExact 64 F := { __src2 with locals := __src2.locals.resVarEq (ofString "l", s1.locals.lookup (ofString "l")) }
                  ({ __src1 with locals := __src1.locals.resVarEq (ofString "pos", s.locals.lookup (ofString "pos")) } : PanSemStateFiniteExact 64 F)
                have hbf_final : ByteFrame R s finalSt := hbf_all.locals _ |>.locals _
                have hf_code : finalSt.code = originalRuntimeCode := by
                  have h1 := hbf_all.1; dsimp only [finalSt]; rw [h1]; exact hcode
                have hf_dom : finalSt.memaddrs = ordinaryDomain := by
                  have h1 := hbf_all.1; dsimp only [finalSt]; rw [h1]; exact hdom_eq
                refine ⟨hbf_final, by simp, fun _ => ⟨hf_code, hf_dom, ?_, ?_, iv + 1#64, ?_⟩⟩
                · change ((setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1#64))) s3).locals.resVarEq
                      (ofString "l", s1.locals.lookup (ofString "l")) |>.resVarEq
                      (ofString "pos", s.locals.lookup (ofString "pos"))).lookup (ofString "len") = _
                  rw [lookup_resVarEq_ne _ _ _ _ (mls_ne rfl), lookup_resVarEq_ne _ _ _ _ (mls_ne rfl)]
                  simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_len,
                    show ofString "i" ≠ ofString "len" from mls_ne rfl]
                · change ((setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1#64))) s3).locals.resVarEq
                      (ofString "l", s1.locals.lookup (ofString "l")) |>.resVarEq
                      (ofString "pos", s.locals.lookup (ofString "pos"))).lookup (ofString "out") = _
                  rw [lookup_resVarEq_ne _ _ _ _ (mls_ne rfl), lookup_resVarEq_ne _ _ _ _ (mls_ne rfl)]
                  simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_out,
                    show ofString "i" ≠ ofString "out" from mls_ne rfl]
                · change ((setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1#64))) s3).locals.resVarEq
                      (ofString "l", s1.locals.lookup (ofString "l")) |>.resVarEq
                      (ofString "pos", s.locals.lookup (ofString "pos"))).lookup (ofString "i") = _
                  rw [lookup_resVarEq_ne _ _ _ _ (mls_ne rfl), lookup_resVarEq_ne _ _ _ _ (mls_ne rfl)]
                  simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              · exact ⟨(hs2_bf.trans hbf_sb).locals _ |>.locals _, by simp, fun h => by simp at h⟩
            · exact ⟨hbf_l.locals _, by simp, fun h => by simp at h⟩
          | «break» => exact ⟨hbf_l.locals _, by simp, fun h => by simp at h⟩
          | «continue» => exact ⟨hbf_l.locals _, by simp, fun h => by simp at h⟩
          | _ => exact ⟨hbf_l.emptyLocals.locals _, by simp, fun h => by simp at h⟩

private theorem toBeMinWhile_byteFrame {F : Type}
    (s : PanSemStateFiniteExact 64 F) (R : List Ivl) (len iv : BitVec 64)
    (outOpt : Option (ValueHOL 64))
    (hcode : s.code = originalRuntimeCode)
    (hdom_eq : s.memaddrs = ordinaryDomain)
    (hlen_le : len.toNat ≤ 32)
    (hlen : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iv)))
    (hout : s.locals.lookup (ofString "out") = outOpt)
    (hR : ∀ outW : BitVec 64, outOpt = some (.val (.word outW)) → (outW.toNat, 32) ∈ R) :
    ByteFrame R s (evaluateHOLFiniteState s toBeMinWhile).2 := by
  suffices hrec : ∀ (clk : Nat) (st : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      st.clock = clk →
      st.code = originalRuntimeCode →
      st.memaddrs = ordinaryDomain →
      st.locals.lookup (ofString "len") = some (.val (.word len)) →
      st.locals.lookup (ofString "i") = some (.val (.word w)) →
      st.locals.lookup (ofString "out") = outOpt →
      ByteFrame R st (evaluateHOLFiniteState st toBeMinWhile).2 by
    exact hrec s.clock s iv rfl hcode hdom_eq hlen hi hout
  intro clk
  induction clk using Nat.strongRecOn with
  | ind clk ih =>
    intro st w hclk hst_code hst_dom hst_len hst_i hst_out
    dsimp only [toBeMinWhile]
    rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact]
    have hevc : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) =
        some (.val (.word (if w.toNat < len.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hst_i, hst_len, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def, decide_eq_true_eq]
    rw [hevc]; dsimp only
    by_cases hlt_w : w.toNat < len.toNat
    · rw [if_pos hlt_w]
      have h1 : (1 : BitVec 64) ≠ 0 := by intro h; cases h
      rw [if_pos h1]
      by_cases hcz : st.clock = 0
      · rw [if_pos hcz]; exact (ByteFrame.refl R st).emptyLocals
      · rw [if_neg hcz]
        rw [fixClockHOLFinite_evaluateState]
        have hstep := toBeMinLoopBody_step (decClockHOLFinite st) R len w outOpt
          hst_code hst_dom hlt_w hlen_le hst_len hst_i hst_out hR
        have hcle := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) toBeMinLoopBody
        rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) toBeMinLoopBody with ⟨rb, mid⟩
        rw [hbr] at hstep hcle; dsimp only at hstep hcle
        have hclk_lt : mid.clock < clk := by change mid.clock ≤ st.clock - 1 at hcle; omega
        have hbf1 : ByteFrame R st mid :=
          (ByteFrame.of_locFrame R (s := st) (t := decClockHOLFinite st) rfl).trans hstep.1
        cases rb with
        | none =>
          obtain ⟨hm_code, hm_dom, hm_len, hm_out, w', hm_i⟩ := hstep.2.2 rfl
          exact hbf1.trans (ih mid.clock hclk_lt mid w' rfl hm_code hm_dom hm_len hm_i hm_out)
        | some r' =>
          cases r' with
          | «continue» => exact absurd rfl hstep.2.1
          | _ => exact hbf1
    · rw [if_neg hlt_w]
      have h0 : ¬ ((0 : BitVec 64) ≠ 0) := not_not.mpr rfl
      rw [if_neg h0]; exact ByteFrame.refl R st

/-! ## 3. Top-level contract `wk_u256_to_be_min` -/

theorem «wk_u256_to_be_min» :
    WorldKeeps WorldOK (fun s => [(locN s "out", 32)])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
     ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "u256_to_be_min") := by
  refine ⟨_, _, _, lookup_u256_to_be_min, fun {F} s hcode hWOK _ _ _ => ?_⟩
  apply worldStep_of_byteFrame hWOK
  let R := [(locN s "out", 32)]
  have hdom_eq : s.memaddrs = ordinaryDomain := hWOK.1.1.memaddrs
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_to_be_min,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  split
  · exact ByteFrame.refl R s
  · rename_i values _
    split
    · exact ByteFrame.refl R s
    · rename_i body' callee ret' hl
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "u256_byte_length")
        [(ofString "a", .comb [.one, .one, .one, .one])]
        (sourceFnBody Guest.Software.guestFn_u256_byte_length) body' .one ret' values callee
        (by rw [hcode]; exact lookup_u256_byte_length) hl
      subst hsame
      split
      · exact (ByteFrame.refl R s).emptyLocals
      · dsimp only
        have hlf_bl := locFrame_u256_byte_length_body (callEntryStateHOLFinite s callee) hcode
        rcases hrun_bl : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_u256_byte_length) with ⟨rbl, post_bl⟩
        rw [hrun_bl] at hlf_bl
        have hbf_bl : ByteFrame R s post_bl :=
          ByteFrame.of_locFrame R (by unfold LocFrame at hlf_bl ⊢; dsimp only at hlf_bl; rw [hlf_bl]; rfl)
        rcases rbl with _ | rbl
        · exact hbf_bl
        · cases rbl with
          | returned vbl =>
            obtain ⟨len, rfl, hlen_le⟩ := u256_byte_length_body_le_32 (callEntryStateHOLFinite s callee) hcode vbl (by rw [hrun_bl])
            dsimp only
            split
            · dsimp only
              set s1 := setVarHOLFinite (ofString "len") (.val (.word len)) { post_bl with locals := s.locals }
              have hs1_bf : ByteFrame R s s1 := (hbf_bl.locals _).setVar _ _
              rw [evaluateHOLFiniteState_dec_total]; dsimp only
              have h0_ev : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
                  (.const 0#64) = some (.val (.word 0#64)) := rfl
              rw [h0_ev]; dsimp only
              have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64))) = true := by
                simp [shapeEqHOL, shapeOfHOLExact]
              rw [if_pos hsh0]; dsimp only
              set s2 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s1
              have hs2_bf : ByteFrame R s s2 := hs1_bf.setVar _ _
              have hs2_code : s2.code = originalRuntimeCode := by rw [hs2_bf.1]; exact hcode
              have hs2_dom : s2.memaddrs = ordinaryDomain := by rw [hs2_bf.1]; exact hdom_eq
              have hs2_len : s2.locals.lookup (ofString "len") = some (.val (.word len)) := by
                simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "i" ≠ ofString "len" from mls_ne rfl]
              have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              have hs2_out : s2.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") := by
                simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "i" ≠ ofString "out" from mls_ne rfl,
                  show ofString "len" ≠ ofString "out" from mls_ne rfl]
              have hR_mem : ∀ outW : BitVec 64,
                  s.locals.lookup (ofString "out") = some (.val (.word outW)) →
                  (outW.toNat, 32) ∈ R := by
                intro outW houtW
                have hlocN : locN s "out" = outW.toNat := by simp [locN, houtW]
                simp [R, hlocN]
              have hseq_bf : ByteFrame R s2
                  (evaluateHOLFiniteState s2
                    (.seq toBeMinWhile (.return (.var .local (ofString "len"))))).2 := by
                rw [evaluateHOLFiniteState_seq_line780]
                have hw_bf := toBeMinWhile_byteFrame s2 R len 0#64 (s.locals.lookup (ofString "out"))
                  hs2_code hs2_dom hlen_le hs2_len hs2_i hs2_out hR_mem
                rcases hw_run : evaluateHOLFiniteState s2 toBeMinWhile with ⟨rw_res, s3⟩
                rw [hw_run] at hw_bf
                cases rw_res with
                | some _ => exact hw_bf
                | none =>
                  dsimp only
                  exact hw_bf.trans (ByteFrame.of_locFrame R (locFrameW_eval _ rfl s3))
              exact (hs2_bf.trans hseq_bf).locals _ |>.locals _
            · exact hbf_bl
          | «break» => exact hbf_bl
          | «continue» => exact hbf_bl
          | _ => exact hbf_bl.emptyLocals

end InitECandidate.Solver.Wave8GuestInv.M13
