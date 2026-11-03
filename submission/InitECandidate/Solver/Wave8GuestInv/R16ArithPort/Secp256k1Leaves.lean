import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.CappedLoopLeaves

/-! Standalone 0-sorry bounded termination proofs on `GuestInv` for:
- `fb_u256_addmod`, `fb_u256_mulmod` (using `P13.DivMod.fb_digits_divmod_guarded` for `m ≤ 16`)
- `fb_secp256k1_init`, `fb_fp_inv`, `fb_fp_sqrt`, `fb_fn_mul`, `fb_fn_inv`
- `fb_ec_set_infinity`, `fb_ec_set_affine`, `fb_ec_is_infinity`,
  `fb_ec_double`, `fb_ec_add_affine`, `fb_ec_to_affine`, `fb_ec_mul2`
- `fb_secp256k1_decompress_r`, `fb_secp256k1_recover`,
  `fb_secp256k1_address_of_point`, `fb_secp256k1_ecrecover`
- `fb_p256_on_curve`, `fb_p256_ec_double`, `fb_p256_ec_add_affine`,
  `fb_p256_ec_mul2`, `fb_p256_verify`.
Zero `LeafStatements.lean` dependency, zero `sorry`, zero `axiom`. -/

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
open InitECandidate.Solver.Wave8GuestInv.FastU256Core
open InitECandidate.Solver.Wave8GuestInv.R16Shards.BlsPrecompiles
open InitECandidate.Solver.Wave8GuestInv.R16ArithPort.Capped

/-! ### 1. Guarded tail-calls to `digits_divmod` (`m ≤ 16`) -> `fb_u256_addmod` & `fb_u256_mulmod` -/

private theorem lookup_digits_divmod_spec :
    originalRuntimeCode.lookup (ofString "digits_divmod") =
      some ([(ofString "u", .one), (ofString "m", .one), (ofString "d", .comb [.one, .one, .one, .one])],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_digits_divmod).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 68 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_digits_divmod) rfl

private theorem three_arg_lookup_digits_divmod
    {vu vm vd : ValueHOL 64} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "digits_divmod") [vu, vm, vd] = some (body', callee, ret')) :
    callee.lookup (ofString "m") = some vm := by
  have hraw := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, lookup_digits_divmod_spec] at hraw
  split at hraw
  · have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hraw)).2).1.symm
    have hm := congrFun hfn (ofString "m")
    simpa [FUPDATE_LIST, FUPDATE,
      show ofString "m" ≠ ofString "d" by decide] using hm
  · cases hraw

private theorem three_args_eval_eq {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e1 e2 e3 : ExpHOL 64) (vals : List (ValueHOL 64))
    (h : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [e1, e2, e3] = some vals) :
    ∃ v1 v2 v3, evalAt s e2 = some v2 ∧ vals = [v1, v2, v3] := by
  rcases h1 : evalAt s e1 with _ | v1; · simp [evalListHOLFinite, evalListHOLExact, h1] at h
  rcases h2 : evalAt s e2 with _ | v2; · simp [evalListHOLFinite, evalListHOLExact, h1, h2] at h
  rcases h3 : evalAt s e3 with _ | v3; · simp [evalListHOLFinite, evalListHOLExact, h1, h2, h3] at h
  refine ⟨v1, v2, v3, rfl, ?_⟩
  simpa [evalListHOLFinite, evalListHOLExact, h1, h2, h3] using h.symm

private theorem tail_digits_divmod_const (u m : ExpHOL 64) (c : Nat) (hc : c ≤ 16) :
    TerminatingProgBoundedOn GuestInv
      (.call none (ofString "digits_divmod") [u, .const (BitVec.ofNat 64 c), m])
      (K.«digits_divmod» + 1) := by
  apply TerminatingProgBoundedOn.tailCall_on
    (Pc := DigitsDivModGuard) fb_digits_divmod_guarded
  intro F s values _ callee _ hcode hg hargs hl
  obtain ⟨_, v2, _, hv2, rfl⟩ := three_args_eval_eq s _ _ _ values hargs
  have hv2_eq : v2 = .val (.word (BitVec.ofNat 64 c)) := by
    simpa [evalAt, evalHOLExact] using hv2.symm
  subst v2
  rw [hcode] at hl
  have hcm := three_arg_lookup_digits_divmod hl
  refine ⟨guestInv_callEntry s callee hg, ?_⟩
  simp only [locN, callEntryStateHOLFinite, hcm, BitVec.toNat_ofNat]
  omega

theorem fb_u256_addmod :
    TerminatingFunBoundedOn GuestInv (ofString "u256_addmod") K.«u256_addmod» := by
  have h0 := fb_u256_add_carry
  have h1 := fb_u256_mod
  have h2 := fb_u256_to_digits
  bls_unfold 75 Guest.Software.guestFn_u256_addmod
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.seq_guestInv
    · exact TerminatingProgBoundedOn.ite_on (straightOn _ rfl) (straightOn _ rfl)
    · apply decCall_guestInv' h0
      apply dec_guestInv
      apply TerminatingProgBoundedOn.seq_guestInv
      · exact TerminatingProgBoundedOn.ite_on
          (TerminatingProgBoundedOn.tailCall_guestInv h1 _) (straightOn _ rfl)
      · apply dec_guestInv
        apply TerminatingProgBoundedOn.seq_guestInv
        · exact call_guestInv' h2
        · apply TerminatingProgBoundedOn.seq_guestInv
          · exact straightOn _ rfl
          · apply TerminatingProgBoundedOn.seq_guestInv
            · exact straightOn _ rfl
            · exact tail_digits_divmod_const _ _ 10 (by decide)
  · bls_arith K.«u256_addmod»

theorem fb_u256_mulmod :
    TerminatingFunBoundedOn GuestInv (ofString "u256_mulmod") K.«u256_mulmod» := by
  have h0 := fb_mul64x64
  have h1 := fb_u256_mod
  have h2 := fb_u256_to_digits
  have h3 := Arith.fb_u256_mul_full
  bls_unfold 76 Guest.Software.guestFn_u256_mulmod
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.seq_guestInv
    · exact TerminatingProgBoundedOn.ite_on (straightOn _ rfl) (straightOn _ rfl)
    · apply dec_guestInv
      apply TerminatingProgBoundedOn.seq_guestInv
      · apply TerminatingProgBoundedOn.ite_on
        · apply decCall_guestInv' h0
          apply TerminatingProgBoundedOn.seq_guestInv
          · exact TerminatingProgBoundedOn.ite_on
              (TerminatingProgBoundedOn.tailCall_guestInv h1 _) (straightOn _ rfl)
          · apply TerminatingProgBoundedOn.seq_guestInv
            · exact call_guestInv' h2
            · exact tail_digits_divmod_const _ _ 4 (by decide)
        · exact straightOn _ rfl
      · apply decCall_guestInv' h3
        apply TerminatingProgBoundedOn.seq_guestInv
        · exact call_guestInv' h2
        · apply TerminatingProgBoundedOn.seq_guestInv
          · exact call_guestInv' h2
          · exact tail_digits_divmod_const _ _ 16 (by decide)
  · bls_arith K.«u256_mulmod»

/-! ### 2. `secp256k1` field/scalar/curve helpers and recovery leaves -/

theorem fb_secp256k1_init :
    TerminatingFunBoundedOn GuestInv (ofString "secp256k1_init") K.«secp256k1_init» := by
  bls_prove 148 Guest.Software.guestFn_secp256k1_init K.«secp256k1_init»

theorem fb_fp_inv :
    TerminatingFunBoundedOn GuestInv (ofString "fp_inv") K.«fp_inv» := by
  have _ := Arith.fb_modinv_bin
  bls_prove 160 Guest.Software.guestFn_fp_inv K.«fp_inv»

theorem fb_fp_sqrt :
    TerminatingFunBoundedOn GuestInv (ofString "fp_sqrt") K.«fp_sqrt» := by
  have _ := fb_fp_pow
  bls_prove 161 Guest.Software.guestFn_fp_sqrt K.«fp_sqrt»

theorem fb_fn_mul :
    TerminatingFunBoundedOn GuestInv (ofString "fn_mul") K.«fn_mul» := by
  have _ := fb_u256_mulmod
  bls_prove 162 Guest.Software.guestFn_fn_mul K.«fn_mul»

theorem fb_fn_inv :
    TerminatingFunBoundedOn GuestInv (ofString "fn_inv") K.«fn_inv» := by
  have _ := Arith.fb_modinv_bin
  bls_prove 166 Guest.Software.guestFn_fn_inv K.«fn_inv»

theorem fb_ec_set_infinity :
    TerminatingFunBoundedOn GuestInv (ofString "ec_set_infinity") K.«ec_set_infinity» := by
  bls_prove 167 Guest.Software.guestFn_ec_set_infinity K.«ec_set_infinity»

theorem fb_ec_set_affine :
    TerminatingFunBoundedOn GuestInv (ofString "ec_set_affine") K.«ec_set_affine» := by
  bls_prove 168 Guest.Software.guestFn_ec_set_affine K.«ec_set_affine»

theorem fb_ec_is_infinity :
    TerminatingFunBoundedOn GuestInv (ofString "ec_is_infinity") K.«ec_is_infinity» := by
  have _ := fb_u256_is_zero
  bls_prove 169 Guest.Software.guestFn_ec_is_infinity K.«ec_is_infinity»

theorem fb_ec_double :
    TerminatingFunBoundedOn GuestInv (ofString "ec_double") K.«ec_double» := by
  have _ := fb_u256_is_zero
  have _ := fb_ec_set_infinity
  have _ := fb_fp_sqr
  have _ := fb_fp_mul
  have _ := Arith.fb_fp_add
  have _ := Arith.fb_fp_sub
  bls_prove 170 Guest.Software.guestFn_ec_double K.«ec_double»

theorem fb_ec_add_affine :
    TerminatingFunBoundedOn GuestInv (ofString "ec_add_affine") K.«ec_add_affine» := by
  have _ := fb_u256_is_zero
  have _ := fb_ec_set_affine
  have _ := fb_fp_sqr
  have _ := fb_fp_mul
  have _ := fb_u256_eq
  have _ := Arith.fb_fp_add
  have _ := fb_ec_set_infinity
  have _ := fb_ec_double
  have _ := Arith.fb_fp_sub
  bls_prove 171 Guest.Software.guestFn_ec_add_affine K.«ec_add_affine»

theorem fb_ec_to_affine :
    TerminatingFunBoundedOn GuestInv (ofString "ec_to_affine") K.«ec_to_affine» := by
  have _ := fb_u256_is_zero
  have _ := fb_fp_inv
  have _ := fb_fp_sqr
  have _ := fb_fp_mul
  have _ := fb_ec_set_affine
  bls_prove 175 Guest.Software.guestFn_ec_to_affine K.«ec_to_affine»

theorem fb_ec_mul2 :
    TerminatingFunBoundedOn GuestInv (ofString "ec_mul2") K.«ec_mul2» := by
  have _ := fb_ec_set_infinity
  have _ := Arith.fb_u256_bit_length
  have _ := fb_max
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_ec_set_affine
  have _ := fb_ec_add_affine
  have _ := fb_ec_is_infinity
  have _ := fb_ec_to_affine
  have _ := fb_ec_double
  have _ := fb_u256_bit
  have _ := fb_heap_release
  bls_unfold 174 Guest.Software.guestFn_ec_mul2
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    apply while_down_unsigned_guestInv (ofString "i")
    · bls_auto
    · exact CounterStep.suffix _ _ _ (CounterStep.sub_one _) (by decide)
  · bls_arith K.«ec_mul2»

theorem fb_secp256k1_decompress_r :
    TerminatingFunBoundedOn GuestInv (ofString "secp256k1_decompress_r") K.«secp256k1_decompress_r» := by
  have _ := fb_u256_add_carry
  have _ := fb_u256_lt
  have _ := fb_fp_sqr
  have _ := fb_fp_mul
  have _ := Arith.fb_fp_add
  have _ := fb_fp_sqrt
  have _ := fb_u256_eq
  have _ := Arith.fb_fp_neg
  have _ := fb_ec_set_affine
  bls_prove 177 Guest.Software.guestFn_secp256k1_decompress_r K.«secp256k1_decompress_r»

theorem fb_secp256k1_recover :
    TerminatingFunBoundedOn GuestInv (ofString "secp256k1_recover") K.«secp256k1_recover» := by
  have _ := fb_u256_is_zero
  have _ := fb_u256_lt
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_secp256k1_decompress_r
  have _ := fb_heap_release
  have _ := fb_u256_from_be
  have _ := InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2.fb_u256_sub
  have _ := fb_fn_inv
  have _ := fb_fn_mul
  have _ := fb_ec_mul2
  have _ := fb_ec_to_affine
  have _ := fb_u256_to_be32
  bls_prove 178 Guest.Software.guestFn_secp256k1_recover K.«secp256k1_recover»

theorem fb_secp256k1_address_of_point :
    TerminatingFunBoundedOn GuestInv (ofString "secp256k1_address_of_point") K.«secp256k1_address_of_point» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_keccak256
  have _ := fb_memcpy
  have _ := fb_heap_release
  bls_prove 179 Guest.Software.guestFn_secp256k1_address_of_point K.«secp256k1_address_of_point»

theorem fb_secp256k1_ecrecover :
    TerminatingFunBoundedOn GuestInv (ofString "secp256k1_ecrecover") K.«secp256k1_ecrecover» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_secp256k1_recover
  have _ := fb_secp256k1_address_of_point
  have _ := fb_heap_release
  bls_prove 180 Guest.Software.guestFn_secp256k1_ecrecover K.«secp256k1_ecrecover»

/-! ### 3. P-256 curve & `p256_verify` leaves -/

theorem fb_p256_on_curve :
    TerminatingFunBoundedOn GuestInv (ofString "p256_on_curve") K.«p256_on_curve» := by
  have _ := Arith.fb_p256_fp_sqr
  have _ := Arith.fb_p256_fp_mul
  have _ := Arith.fb_p256_fp_add
  have _ := Arith.fb_p256_fp_sub
  have _ := fb_u256_eq
  bls_prove 643 Guest.Software.guestFn_p256_on_curve K.«p256_on_curve»

theorem fb_p256_ec_double :
    TerminatingFunBoundedOn GuestInv (ofString "p256_ec_double") K.«p256_ec_double» := by
  have _ := fb_u256_is_zero
  have _ := Arith.fb_p256_set_infinity
  have _ := Arith.fb_p256_fp_sqr
  have _ := Arith.fb_p256_fp_mul
  have _ := Arith.fb_p256_fp_sub
  have _ := Arith.fb_p256_fp_add
  bls_prove 639 Guest.Software.guestFn_p256_ec_double K.«p256_ec_double»

theorem fb_p256_ec_add_affine :
    TerminatingFunBoundedOn GuestInv (ofString "p256_ec_add_affine") K.«p256_ec_add_affine» := by
  have _ := fb_u256_is_zero
  have _ := Arith.fb_p256_set_affine
  have _ := Arith.fb_p256_fp_sqr
  have _ := Arith.fb_p256_fp_mul
  have _ := fb_u256_eq
  have _ := Arith.fb_p256_fp_add
  have _ := Arith.fb_p256_set_infinity
  have _ := fb_p256_ec_double
  have _ := Arith.fb_p256_fp_sub
  bls_prove 640 Guest.Software.guestFn_p256_ec_add_affine K.«p256_ec_add_affine»

theorem fb_p256_ec_mul2 :
    TerminatingFunBoundedOn GuestInv (ofString "p256_ec_mul2") K.«p256_ec_mul2» := by
  have _ := Arith.fb_p256_set_infinity
  have _ := Arith.fb_u256_bit_length
  have _ := fb_max
  have _ := fb_p256_ec_double
  have _ := fb_u256_bit
  have _ := fb_p256_ec_add_affine
  bls_unfold 641 Guest.Software.guestFn_p256_ec_mul2
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    apply while_down_unsigned_guestInv (ofString "i")
    · bls_auto
    · exact CounterStep.suffix _ _ _ (CounterStep.sub_one _) (by decide)
  · bls_arith K.«p256_ec_mul2»

theorem fb_p256_verify :
    TerminatingFunBoundedOn GuestInv (ofString "p256_verify") K.«p256_verify» := by
  have _ := fb_u256_is_zero
  have _ := fb_u256_lt
  have _ := fb_p256_on_curve
  have _ := fb_u256_from_be
  have _ := InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2.fb_u256_sub
  have _ := Arith.fb_modinv_bin
  have _ := fb_u256_mulmod
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_p256_ec_mul2
  have _ := fb_heap_release
  have _ := Arith.fb_p256_fp_sqr
  have _ := Arith.fb_p256_fp_mul
  have _ := fb_u256_eq
  have _ := fb_u256_add_carry
  bls_prove 644 Guest.Software.guestFn_p256_verify K.«p256_verify»

end InitECandidate.Solver.Wave8GuestInv.R16ArithPort
