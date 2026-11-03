import InitECandidate.Solver.Wave8GuestInv.R16Shards.BlsPrecompiles.BlsDecodeTouch

/-! Standalone 0-sorry bounded termination proofs on `GuestInv` for all BLS12-381 `Fp2`, G2 curve,
SWU/isogeny map-to-G2, and G2 precompile functions:
`fb_fp2_*`, `fb_g2_*`, `fb_swu_*_fp2`, `fb_swu_g2`, `fb_iso_*_fp2`, `fb_iso_map_g2`,
`fb_map_fp2_to_g2`, `fb_bls_g2_add_exec`, `fb_pre_bls_g2_add`,
`fb_bls_map_fp2_to_g2_exec`, `fb_pre_bls_map_fp2_to_g2`,
`fb_bls_g2_msm_exec`, `fb_pre_bls_g2_msm`.
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

/-! ### 1. `Fp2` extension field arithmetic -/

theorem fb_fp2_copy :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_copy") K.«fp2_copy» := by
  have _ := fb_memcpy
  bls_prove 721 Guest.Software.guestFn_fp2_copy K.«fp2_copy»

theorem fb_fp2_set_zero :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_set_zero") K.«fp2_set_zero» := by
  have _ := fb_memzero
  bls_prove 722 Guest.Software.guestFn_fp2_set_zero K.«fp2_set_zero»

theorem fb_fp2_set_one :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_set_one") K.«fp2_set_one» := by
  bls_prove 723 Guest.Software.guestFn_fp2_set_one K.«fp2_set_one»

theorem fb_fp2_is_zero :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_is_zero") K.«fp2_is_zero» := by
  bls_prove 724 Guest.Software.guestFn_fp2_is_zero K.«fp2_is_zero»

theorem fb_fp2_eq :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_eq") K.«fp2_eq» := by
  have _ := fb_bls_fp_eq
  bls_prove 725 Guest.Software.guestFn_fp2_eq K.«fp2_eq»

theorem fb_fp2_add :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_add") K.«fp2_add» := by
  have _ := fb_bls_fp_add
  bls_prove 726 Guest.Software.guestFn_fp2_add K.«fp2_add»

theorem fb_fp2_sub :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_sub") K.«fp2_sub» := by
  have _ := fb_bls_fp_sub
  bls_prove 727 Guest.Software.guestFn_fp2_sub K.«fp2_sub»

theorem fb_fp2_neg :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_neg") K.«fp2_neg» := by
  have _ := fb_bls_fp_neg
  bls_prove 728 Guest.Software.guestFn_fp2_neg K.«fp2_neg»

theorem fb_fp2_conj :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_conj") K.«fp2_conj» := by
  have _ := fb_bls_fp_neg
  bls_prove 730 Guest.Software.guestFn_fp2_conj K.«fp2_conj»

theorem fb_fp2_mul :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_mul") K.«fp2_mul» := by
  have _ := fb_bls_fp_mul
  have _ := fb_bls_fp_add
  have _ := fb_bls_fp_sub
  bls_prove 731 Guest.Software.guestFn_fp2_mul K.«fp2_mul»

theorem fb_fp2_sqr :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_sqr") K.«fp2_sqr» := by
  have _ := fb_bls_fp_add
  have _ := fb_bls_fp_sub
  have _ := fb_bls_fp_mul
  bls_prove 732 Guest.Software.guestFn_fp2_sqr K.«fp2_sqr»

theorem fb_fp2_mul_xi :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_mul_xi") K.«fp2_mul_xi» := by
  have _ := fb_bls_fp_sub
  have _ := fb_bls_fp_add
  bls_prove 733 Guest.Software.guestFn_fp2_mul_xi K.«fp2_mul_xi»

theorem fb_fp2_scale :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_scale") K.«fp2_scale» := by
  have _ := fb_bls_fp_mul
  bls_prove 734 Guest.Software.guestFn_fp2_scale K.«fp2_scale»

theorem fb_fp2_inv :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_inv") K.«fp2_inv» := by
  have _ := fb_bls_fp_sqr
  have _ := fb_bls_fp_add
  have _ := fb_bls_fp_inv
  have _ := fb_bls_fp_mul
  have _ := fb_bls_fp_neg
  bls_prove 735 Guest.Software.guestFn_fp2_inv K.«fp2_inv»

theorem fb_fp2_pow :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_pow") K.«fp2_pow» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fp2_copy
  have _ := fb_fp2_set_one
  have _ := fb_fp2_sqr
  have _ := fb_fp2_mul
  have _ := fb_heap_release
  bls_unfold 736 Guest.Software.guestFn_fp2_pow
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    apply while_down_unsigned_guestInv (ofString "i")
    · bls_auto
    · exact CounterStep.suffix _ _ _ (CounterStep.sub_one _) rfl
  · bls_arith K.«fp2_pow»

theorem fb_fp2_sgn0 :
    TerminatingFunBoundedOn GuestInv (ofString "fp2_sgn0") K.«fp2_sgn0» := by
  have _ := fb_bls_fp_sgn0
  have _ := fb_bls_fp_is_zero
  bls_prove 737 Guest.Software.guestFn_fp2_sgn0 K.«fp2_sgn0»

/-! ### 2. G2 curve arithmetic, decoding, encoding, and subgroup check -/

theorem fb_g2_set_inf :
    TerminatingFunBoundedOn GuestInv (ofString "g2_set_inf") K.«g2_set_inf» := by
  have _ := fb_fp2_set_zero
  have _ := fb_fp2_set_one
  bls_prove 770 Guest.Software.guestFn_g2_set_inf K.«g2_set_inf»

theorem fb_g2_is_inf :
    TerminatingFunBoundedOn GuestInv (ofString "g2_is_inf") K.«g2_is_inf» := by
  have _ := fb_fp2_is_zero
  bls_prove 771 Guest.Software.guestFn_g2_is_inf K.«g2_is_inf»

theorem fb_g2_copy :
    TerminatingFunBoundedOn GuestInv (ofString "g2_copy") K.«g2_copy» := by
  have _ := fb_memcpy
  bls_prove 772 Guest.Software.guestFn_g2_copy K.«g2_copy»

theorem fb_g2_neg :
    TerminatingFunBoundedOn GuestInv (ofString "g2_neg") K.«g2_neg» := by
  have _ := fb_fp2_copy
  have _ := fb_fp2_neg
  bls_prove 773 Guest.Software.guestFn_g2_neg K.«g2_neg»

theorem fb_g2_double :
    TerminatingFunBoundedOn GuestInv (ofString "g2_double") K.«g2_double» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fp2_sqr
  have _ := fb_fp2_add
  have _ := fb_fp2_mul
  have _ := fb_fp2_sub
  have _ := fb_fp2_copy
  have _ := fb_heap_release
  bls_prove 774 Guest.Software.guestFn_g2_double K.«g2_double»

theorem fb_g2_add :
    TerminatingFunBoundedOn GuestInv (ofString "g2_add") K.«g2_add» := by
  have _ := fb_g2_is_inf
  have _ := fb_g2_copy
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fp2_sqr
  have _ := fb_fp2_mul
  have _ := fb_fp2_eq
  have _ := fb_g2_double
  have _ := fb_g2_set_inf
  have _ := fb_fp2_sub
  have _ := fb_fp2_add
  have _ := fb_fp2_copy
  have _ := fb_heap_release
  bls_prove 775 Guest.Software.guestFn_g2_add K.«g2_add»

theorem fb_g2_mul :
    TerminatingFunBoundedOn GuestInv (ofString "g2_mul") K.«g2_mul» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_g2_set_inf
  have _ := fb_g2_double
  have _ := fb_g2_add
  have _ := fb_g2_copy
  have _ := fb_heap_release
  bls_unfold 776 Guest.Software.guestFn_g2_mul
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    apply while_down_unsigned_guestInv (ofString "i")
    · bls_auto
    · exact CounterStep.suffix _ _ _ (CounterStep.sub_one _) rfl
  · bls_arith K.«g2_mul»

theorem fb_g2_normalize :
    TerminatingFunBoundedOn GuestInv (ofString "g2_normalize") K.«g2_normalize» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_g2_is_inf
  have _ := fb_memzero
  have _ := fb_fp2_inv
  have _ := fb_fp2_mul
  have _ := fb_heap_release
  bls_prove 777 Guest.Software.guestFn_g2_normalize K.«g2_normalize»

theorem fb_g2_on_curve :
    TerminatingFunBoundedOn GuestInv (ofString "g2_on_curve") K.«g2_on_curve» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fp2_sqr
  have _ := fb_fp2_mul
  have _ := fb_fp2_add
  have _ := fb_fp2_eq
  have _ := fb_heap_release
  bls_prove 778 Guest.Software.guestFn_g2_on_curve K.«g2_on_curve»

theorem fb_g2_decode :
    TerminatingFunBoundedOn GuestInv (ofString "g2_decode") K.«g2_decode» := by
  have _ := fb_bls_fp_decode64
  have _ := fb_fp2_is_zero
  have _ := fb_fp2_set_zero
  have _ := fb_fp2_set_one
  have _ := fb_g2_on_curve
  bls_prove 779 Guest.Software.guestFn_g2_decode K.«g2_decode»

theorem fb_g2_encode :
    TerminatingFunBoundedOn GuestInv (ofString "g2_encode") K.«g2_encode» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_g2_normalize
  have _ := fb_bls_fp_encode64
  have _ := fb_heap_release
  bls_prove 780 Guest.Software.guestFn_g2_encode K.«g2_encode»

theorem fb_g2_subgroup_check :
    TerminatingFunBoundedOn GuestInv (ofString "g2_subgroup_check") K.«g2_subgroup_check» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_g2_mul
  have _ := fb_g2_is_inf
  have _ := fb_heap_release
  bls_prove 781 Guest.Software.guestFn_g2_subgroup_check K.«g2_subgroup_check»

/-! ### 3. SWU & 3-isogeny map `Fp2 -> G2` -/

theorem fb_swu_sqrt_division_fp2 :
    TerminatingFunBoundedOn GuestInv (ofString "swu_sqrt_division_fp2") K.«swu_sqrt_division_fp2» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fp2_copy
  have _ := fb_fp2_mul
  have _ := fb_fp2_pow
  have _ := fb_fp2_sqr
  have _ := fb_fp2_sub
  have _ := fb_fp2_is_zero
  have _ := fb_heap_release
  bls_unfold 792 Guest.Software.guestFn_swu_sqrt_division_fp2
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    · apply while_up_unsigned_const_guestInv (ofString "i") (BitVec.ofNat 64 6)
      · bls_auto
      · bls_counter_step
    · apply while_up_unsigned_const_guestInv (ofString "i") (BitVec.ofNat 64 4)
      · bls_auto
      · bls_counter_step
  · rw [show (BitVec.ofNat 64 6).toNat = 6 by decide, show (BitVec.ofNat 64 4).toNat = 4 by decide]
    bls_arith K.«swu_sqrt_division_fp2»

theorem fb_swu_g2 :
    TerminatingFunBoundedOn GuestInv (ofString "swu_g2") K.«swu_g2» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fp2_sqr
  have _ := fb_fp2_mul
  have _ := fb_fp2_add
  have _ := fb_fp2_neg
  have _ := fb_fp2_set_one
  have _ := fb_fp2_is_zero
  have _ := fb_swu_sqrt_division_fp2
  have _ := fb_fp2_sub
  have _ := fb_fp2_copy
  have _ := fb_fp2_sgn0
  have _ := fb_heap_release
  bls_unfold 793 Guest.Software.guestFn_swu_g2
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    apply while_up_unsigned_const_guestInv (ofString "i") (BitVec.ofNat 64 4)
    · bls_auto
    · bls_counter_step
  · rw [show (BitVec.ofNat 64 4).toNat = 4 by decide]
    bls_arith K.«swu_g2»

theorem fb_iso_horner_fp2 :
    TerminatingFunBoundedOn GuestInv (ofString "iso_horner_fp2") K.«iso_horner_fp2» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fp2_copy
  have _ := fb_fp2_mul
  have _ := fb_fp2_add
  have _ := fb_heap_release
  bls_unfold 794 Guest.Software.guestFn_iso_horner_fp2
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    apply while_up_exp_guestInv .lower (Or.inr rfl) (ofString "j") _
    · bls_auto
    · bls_counter_step
    · rfl
  · bls_arith K.«iso_horner_fp2»

theorem fb_iso_map_g2 :
    TerminatingFunBoundedOn GuestInv (ofString "iso_map_g2") K.«iso_map_g2» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fp2_copy
  have _ := fb_fp2_sqr
  have _ := fb_fp2_mul
  have _ := fb_iso_horner_fp2
  have _ := fb_g2_copy
  have _ := fb_heap_release
  bls_prove 795 Guest.Software.guestFn_iso_map_g2 K.«iso_map_g2»

theorem fb_map_fp2_to_g2 :
    TerminatingFunBoundedOn GuestInv (ofString "map_fp2_to_g2") K.«map_fp2_to_g2» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_swu_g2
  have _ := fb_iso_map_g2
  have _ := fb_g2_mul
  have _ := fb_heap_release
  bls_prove 796 Guest.Software.guestFn_map_fp2_to_g2 K.«map_fp2_to_g2»

/-! ### 4. BLS12-381 G2 precompile entry points (`add`, `map_fp2_to_g2`, `msm`) -/

theorem fb_bls_g2_add_exec :
    TerminatingFunBoundedOn GuestInv (ofString "bls_g2_add_exec") K.«bls_g2_add_exec» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_g2_decode
  have _ := fb_g2_add
  have _ := fb_g2_encode
  have _ := fb_heap_release
  bls_prove 804 Guest.Software.guestFn_bls_g2_add_exec K.«bls_g2_add_exec»

theorem fb_pre_bls_g2_add :
    TerminatingFunBoundedOn GuestInv (ofString "pre_bls_g2_add") K.«pre_bls_g2_add» := by
  have _ := fb_charge_gas
  have _ := fb_alloc
  have _ := fb_bls_g2_add_exec
  bls_prove 816 Guest.Software.guestFn_pre_bls_g2_add K.«pre_bls_g2_add»

theorem fb_bls_map_fp2_to_g2_exec :
    TerminatingFunBoundedOn GuestInv (ofString "bls_map_fp2_to_g2_exec") K.«bls_map_fp2_to_g2_exec» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_bls_fp_decode64
  have _ := fb_map_fp2_to_g2
  have _ := fb_g2_encode
  have _ := fb_heap_release
  bls_prove 808 Guest.Software.guestFn_bls_map_fp2_to_g2_exec K.«bls_map_fp2_to_g2_exec»

theorem fb_pre_bls_map_fp2_to_g2 :
    TerminatingFunBoundedOn GuestInv (ofString "pre_bls_map_fp2_to_g2") K.«pre_bls_map_fp2_to_g2» := by
  have _ := fb_charge_gas
  have _ := fb_alloc
  have _ := fb_bls_map_fp2_to_g2_exec
  bls_prove 820 Guest.Software.guestFn_pre_bls_map_fp2_to_g2 K.«pre_bls_map_fp2_to_g2»

theorem fb_bls_g2_msm_exec :
    TerminatingFunBoundedOn GuestInv (ofString "bls_g2_msm_exec") K.«bls_g2_msm_exec» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_g2_decode
  have _ := fb_g2_subgroup_check
  have _ := fb_u256_from_be
  have _ := fb_g2_mul
  have _ := fb_g2_copy
  have _ := fb_g2_add
  have _ := fb_g2_encode
  have _ := fb_heap_release
  bls_unfold 805 Guest.Software.guestFn_bls_g2_msm_exec
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    apply while_scaled_walk_guestInv (ofString "data") (ofString "i") 288
    · bls_auto
    · exact touch_dec_g2_decode _ _ _
    · bls_counter_step
    · rfl
    · decide
    · decide
  · clear * -
    unfold K.«bls_g2_msm_exec»
    rw [domainBytes_eq]
    fast_generalize_K
    simp only [Nat.add_zero, nat_max_eq]
    omega

theorem fb_pre_bls_g2_msm :
    TerminatingFunBoundedOn GuestInv (ofString "pre_bls_g2_msm") K.«pre_bls_g2_msm» := by
  have _ := fb_udivmod
  have _ := fb_bls_g2_msm_discount
  have _ := fb_charge_gas
  have _ := fb_alloc
  have _ := fb_bls_g2_msm_exec
  bls_prove 817 Guest.Software.guestFn_pre_bls_g2_msm K.«pre_bls_g2_msm»

end InitECandidate.Solver.Wave8GuestInv.R16Shards.BlsPrecompiles
