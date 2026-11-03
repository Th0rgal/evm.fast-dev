import InitECandidate.Solver.Wave8GuestInv.R16Shards.BlsPrecompiles.BlsDecodeTouch

/-! Standalone 0-sorry bounded termination proofs on `GuestInv` for all BLS12-381 G1 curve,
SWU/isogeny map-to-curve, and precompile functions:
`fb_g1_*`, `fb_swu_*_fp`, `fb_iso_*_g1`, `fb_map_fp_to_g1`,
`fb_bls_g1_add_exec`, `fb_pre_bls_g1_add`,
`fb_bls_map_fp_to_g1_exec`, `fb_pre_bls_map_fp_to_g1`,
`fb_bls_g1_msm_exec`, `fb_pre_bls_g1_msm`.
Zero `LeafStatements.lean` dependency, zero `sorry`. -/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.BlsPrecompiles

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common
open InitECandidate.Solver.Wave8GuestInv.P13.Callees
open InitECandidate.Solver.Wave8GuestInv.P13.DivMod

/-! ### 1. G1 curve arithmetic, decoding, encoding, and subgroup check -/

theorem fb_g1_set_inf :
    TerminatingFunBoundedOn GuestInv (ofString "g1_set_inf") K.«g1_set_inf» := by
  bls_prove 758 Guest.Software.guestFn_g1_set_inf K.«g1_set_inf»

theorem fb_g1_is_inf :
    TerminatingFunBoundedOn GuestInv (ofString "g1_is_inf") K.«g1_is_inf» := by
  have _ := fb_bls_fp_is_zero
  bls_prove 759 Guest.Software.guestFn_g1_is_inf K.«g1_is_inf»

theorem fb_g1_copy :
    TerminatingFunBoundedOn GuestInv (ofString "g1_copy") K.«g1_copy» := by
  have _ := fb_memcpy
  bls_prove 760 Guest.Software.guestFn_g1_copy K.«g1_copy»

theorem fb_g1_double :
    TerminatingFunBoundedOn GuestInv (ofString "g1_double") K.«g1_double» := by
  have _ := fb_bls_fp_sqr
  have _ := fb_bls_fp_add
  have _ := fb_bls_fp_sub
  have _ := fb_bls_fp_mul
  bls_prove 762 Guest.Software.guestFn_g1_double K.«g1_double»

theorem fb_g1_add :
    TerminatingFunBoundedOn GuestInv (ofString "g1_add") K.«g1_add» := by
  have _ := fb_bls_fp_is_zero
  have _ := fb_bls_fp_eq
  have _ := fb_bls_fp_add
  have _ := fb_bls_fp_sub
  have _ := fb_bls_fp_mul
  have _ := fb_bls_fp_sqr
  have _ := fb_g1_copy
  have _ := fb_g1_double
  have _ := fb_g1_set_inf
  bls_prove 763 Guest.Software.guestFn_g1_add K.«g1_add»

theorem fb_g1_mul :
    TerminatingFunBoundedOn GuestInv (ofString "g1_mul") K.«g1_mul» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_g1_copy
  have _ := fb_g1_set_inf
  have _ := fb_g1_double
  have _ := fb_g1_add
  have _ := fb_heap_release
  bls_unfold 764 Guest.Software.guestFn_g1_mul
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    apply while_down_unsigned_guestInv (ofString "i")
    · bls_auto
    · exact CounterStep.suffix _ _ _ (CounterStep.sub_one _) rfl
  · bls_arith K.«g1_mul»

theorem fb_g1_normalize :
    TerminatingFunBoundedOn GuestInv (ofString "g1_normalize") K.«g1_normalize» := by
  have _ := fb_bls_fp_inv
  have _ := fb_bls_fp_mul
  have _ := fb_bls_fp_is_zero
  bls_prove 765 Guest.Software.guestFn_g1_normalize K.«g1_normalize»

theorem fb_g1_on_curve :
    TerminatingFunBoundedOn GuestInv (ofString "g1_on_curve") K.«g1_on_curve» := by
  have _ := fb_bls_fp_sqr
  have _ := fb_bls_fp_mul
  have _ := fb_bls_fp_add
  have _ := fb_bls_fp_eq
  bls_prove 766 Guest.Software.guestFn_g1_on_curve K.«g1_on_curve»

theorem fb_g1_decode :
    TerminatingFunBoundedOn GuestInv (ofString "g1_decode") K.«g1_decode» := by
  have _ := fb_bls_fp_decode64
  have _ := fb_bls_fp_is_zero
  have _ := fb_g1_on_curve
  bls_prove 767 Guest.Software.guestFn_g1_decode K.«g1_decode»

theorem fb_g1_encode :
    TerminatingFunBoundedOn GuestInv (ofString "g1_encode") K.«g1_encode» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_g1_normalize
  have _ := fb_bls_fp_encode64
  have _ := fb_heap_release
  bls_prove 768 Guest.Software.guestFn_g1_encode K.«g1_encode»

theorem fb_g1_subgroup_check :
    TerminatingFunBoundedOn GuestInv (ofString "g1_subgroup_check") K.«g1_subgroup_check» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_g1_mul
  have _ := fb_g1_is_inf
  have _ := fb_heap_release
  bls_prove 769 Guest.Software.guestFn_g1_subgroup_check K.«g1_subgroup_check»

/-! ### 2. SWU & 11-isogeny map `Fp -> G1` -/

theorem fb_swu_sqrt_division_fp :
    TerminatingFunBoundedOn GuestInv (ofString "swu_sqrt_division_fp") K.«swu_sqrt_division_fp» := by
  have _ := fb_bls_fp_mul
  have _ := fb_bls_fp_sqr
  have _ := fb_bls_fp_pow
  have _ := fb_bls_fp_sub
  have _ := fb_bls_fp_is_zero
  bls_prove 787 Guest.Software.guestFn_swu_sqrt_division_fp K.«swu_sqrt_division_fp»

theorem fb_swu_g1 :
    TerminatingFunBoundedOn GuestInv (ofString "swu_g1") K.«swu_g1» := by
  have _ := fb_bls_fp_sqr
  have _ := fb_bls_fp_mul
  have _ := fb_bls_fp_add
  have _ := fb_bls_fp_neg
  have _ := fb_bls_fp_is_zero
  have _ := fb_swu_sqrt_division_fp
  have _ := fb_bls_fp_sgn0
  bls_prove 788 Guest.Software.guestFn_swu_g1 K.«swu_g1»

theorem fb_iso_horner_fp :
    TerminatingFunBoundedOn GuestInv (ofString "iso_horner_fp") K.«iso_horner_fp» := by
  have _ := fb_bls_fp_mul
  have _ := fb_bls_fp_add
  bls_unfold 789 Guest.Software.guestFn_iso_horner_fp
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    apply while_up_exp_guestInv .lower (Or.inr rfl) (ofString "j") _
    · bls_auto
    · bls_counter_step
    · rfl
  · bls_arith K.«iso_horner_fp»

theorem fb_iso_map_g1 :
    TerminatingFunBoundedOn GuestInv (ofString "iso_map_g1") K.«iso_map_g1» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_bls_fp_mul
  have _ := fb_iso_horner_fp
  have _ := fb_heap_release
  bls_unfold 790 Guest.Software.guestFn_iso_map_g1
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    apply while_up_unsigned_const_guestInv (ofString "j") (BitVec.ofNat 64 15)
    · bls_auto
    · bls_counter_step
  · rw [show (BitVec.ofNat 64 15).toNat = 15 by decide]
    bls_arith K.«iso_map_g1»

theorem fb_map_fp_to_g1 :
    TerminatingFunBoundedOn GuestInv (ofString "map_fp_to_g1") K.«map_fp_to_g1» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_swu_g1
  have _ := fb_iso_map_g1
  have _ := fb_g1_mul
  have _ := fb_heap_release
  bls_prove 791 Guest.Software.guestFn_map_fp_to_g1 K.«map_fp_to_g1»

/-! ### 3. BLS12-381 G1 precompile entry points (`add`, `map_fp_to_g1`, `msm`) -/

theorem fb_bls_g1_add_exec :
    TerminatingFunBoundedOn GuestInv (ofString "bls_g1_add_exec") K.«bls_g1_add_exec» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_g1_decode
  have _ := fb_g1_add
  have _ := fb_g1_encode
  have _ := fb_heap_release
  bls_prove 802 Guest.Software.guestFn_bls_g1_add_exec K.«bls_g1_add_exec»

theorem fb_pre_bls_g1_add :
    TerminatingFunBoundedOn GuestInv (ofString "pre_bls_g1_add") K.«pre_bls_g1_add» := by
  have _ := fb_charge_gas
  have _ := fb_alloc
  have _ := fb_bls_g1_add_exec
  bls_prove 814 Guest.Software.guestFn_pre_bls_g1_add K.«pre_bls_g1_add»

theorem fb_bls_map_fp_to_g1_exec :
    TerminatingFunBoundedOn GuestInv (ofString "bls_map_fp_to_g1_exec") K.«bls_map_fp_to_g1_exec» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_bls_fp_decode64
  have _ := fb_map_fp_to_g1
  have _ := fb_g1_encode
  have _ := fb_heap_release
  bls_prove 807 Guest.Software.guestFn_bls_map_fp_to_g1_exec K.«bls_map_fp_to_g1_exec»

theorem fb_pre_bls_map_fp_to_g1 :
    TerminatingFunBoundedOn GuestInv (ofString "pre_bls_map_fp_to_g1") K.«pre_bls_map_fp_to_g1» := by
  have _ := fb_charge_gas
  have _ := fb_alloc
  have _ := fb_bls_map_fp_to_g1_exec
  bls_prove 819 Guest.Software.guestFn_pre_bls_map_fp_to_g1 K.«pre_bls_map_fp_to_g1»

theorem fb_bls_g1_msm_exec :
    TerminatingFunBoundedOn GuestInv (ofString "bls_g1_msm_exec") K.«bls_g1_msm_exec» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_g1_decode
  have _ := fb_g1_subgroup_check
  have _ := fb_u256_from_be
  have _ := fb_g1_mul
  have _ := fb_g1_copy
  have _ := fb_g1_add
  have _ := fb_g1_encode
  have _ := fb_heap_release
  bls_unfold 803 Guest.Software.guestFn_bls_g1_msm_exec
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    apply while_scaled_walk_guestInv (ofString "data") (ofString "i") 160
    · bls_auto
    · exact touch_dec_g1_decode _ _ _
    · bls_counter_step
    · rfl
    · decide
    · decide
  · clear * -
    unfold K.«bls_g1_msm_exec»
    rw [domainBytes_eq]
    fast_generalize_K
    simp only [Nat.add_zero, nat_max_eq]
    omega

theorem fb_pre_bls_g1_msm :
    TerminatingFunBoundedOn GuestInv (ofString "pre_bls_g1_msm") K.«pre_bls_g1_msm» := by
  have _ := fb_udivmod
  have _ := fb_bls_g1_msm_discount
  have _ := fb_charge_gas
  have _ := fb_alloc
  have _ := fb_bls_g1_msm_exec
  bls_prove 815 Guest.Software.guestFn_pre_bls_g1_msm K.«pre_bls_g1_msm»

end InitECandidate.Solver.Wave8GuestInv.R16Shards.BlsPrecompiles
