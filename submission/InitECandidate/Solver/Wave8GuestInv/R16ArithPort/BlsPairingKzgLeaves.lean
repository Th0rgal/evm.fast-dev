import InitECandidate.Solver.Wave8GuestInv.R16Shards.BlsPrecompiles.BlsG1
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.CappedLoopLeaves
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_Sha256

/-! Standalone bounded termination proofs on `GuestInv` for the BLS12-381 extension
inversion, final exponentiation, Miller accumulation, pairing precompile, and KZG point
evaluation precompile chain:
- `fb_fp6_inv`, `fb_fp12_frob`, `fb_fp12_inv`, `fb_fp12_exp_x`, `fb_fp12_final_exp`, `fb_fp12_is_one`
- `fb_pair_accumulate`, `fb_bls_pairing_exec`, `fb_pre_bls_pairing`
- `fb_kzg_decompress_g1`, `fb_kzg_load_g1`, `fb_kzg_neg_scalar`, `fb_kzg_verify`,
  `fb_kzg_point_evaluation_exec`, `fb_pre_kzg_point_evaluation`.
Zero `LeafStatements.lean` dependency. -/

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
open InitECandidate.Solver.Wave8GuestInv.R16Shards.BlsPrecompiles
open InitECandidate.Solver.Wave8GuestInv.R16ArithPort.Capped

/-! ### 1. `Fp6` / `Fp12` inversion, Frobenius, and final exponentiation -/

theorem fb_fp6_inv :
    TerminatingFunBoundedOn GuestInv (ofString "fp6_inv") K.«fp6_inv» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fp2_sqr
  have _ := fb_fp2_mul
  have _ := fb_fp2_mul_xi
  have _ := fb_fp2_sub
  have _ := fb_fp2_add
  have _ := fb_fp2_inv
  have _ := fb_heap_release
  bls_prove 746 Guest.Software.guestFn_fp6_inv K.«fp6_inv»

theorem fb_fp12_frob :
    TerminatingFunBoundedOn GuestInv (ofString "fp12_frob") K.«fp12_frob» := by
  have _ := fb_fp2_conj
  have _ := fb_fp2_mul
  bls_prove 754 Guest.Software.guestFn_fp12_frob K.«fp12_frob»

theorem fb_fp12_inv :
    TerminatingFunBoundedOn GuestInv (ofString "fp12_inv") K.«fp12_inv» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fp6_mul
  have _ := fb_fp6_mul_v
  have _ := fb_fp6_sub
  have _ := fb_fp6_inv
  have _ := fb_fp6_neg
  have _ := fb_heap_release
  bls_prove 753 Guest.Software.guestFn_fp12_inv K.«fp12_inv»

theorem fb_fp12_exp_x :
    TerminatingFunBoundedOn GuestInv (ofString "fp12_exp_x") K.«fp12_exp_x» := by
  have _ := fb_fp12_pow_absx
  have _ := fb_fp12_conj
  bls_prove 756 Guest.Software.guestFn_fp12_exp_x K.«fp12_exp_x»

theorem fb_fp12_final_exp :
    TerminatingFunBoundedOn GuestInv (ofString "fp12_final_exp") K.«fp12_final_exp» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fp12_inv
  have _ := fb_fp12_conj
  have _ := fb_fp12_mul
  have _ := fb_fp12_frob
  have _ := fb_fp12_exp_x
  have _ := fb_heap_release
  bls_prove 757 Guest.Software.guestFn_fp12_final_exp K.«fp12_final_exp»

theorem fb_fp12_is_one :
    TerminatingFunBoundedOn GuestInv (ofString "fp12_is_one") K.«fp12_is_one» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fp12_set_one
  have _ := fb_memeq
  have _ := fb_heap_release
  bls_prove 749 Guest.Software.guestFn_fp12_is_one K.«fp12_is_one»

/-! ### 2. BLS12-381 Miller loop accumulation and pairing precompile -/

theorem fb_pair_accumulate :
    TerminatingFunBoundedOn GuestInv (ofString "pair_accumulate") K.«pair_accumulate» := by
  have _ := fb_g1_is_inf
  have _ := fb_g2_is_inf
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_g1_normalize
  have _ := fb_g2_normalize
  have _ := fb_pair_miller_loop
  have _ := fb_fp12_mul
  have _ := fb_heap_release
  bls_prove 786 Guest.Software.guestFn_pair_accumulate K.«pair_accumulate»

theorem fb_bls_pairing_exec :
    TerminatingFunBoundedOn GuestInv (ofString "bls_pairing_exec") K.«bls_pairing_exec» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fp12_set_one
  have _ := fb_g1_decode
  have _ := fb_g1_subgroup_check
  have _ := fb_g2_decode
  have _ := fb_g2_subgroup_check
  have _ := fb_pair_accumulate
  have _ := fb_fp12_final_exp
  have _ := fb_fp12_is_one
  have _ := fb_memzero
  have _ := fb_heap_release
  bls_unfold 806 Guest.Software.guestFn_bls_pairing_exec
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    apply while_scaled_walk_guestInv (ofString "data") (ofString "i") 384
    · bls_auto
    · exact touch_dec_g1_decode _ _ _
    · bls_counter_step
    · rfl
    · decide
    · decide
  · clear * -
    unfold K.«bls_pairing_exec»
    rw [domainBytes_eq]
    fast_generalize_K
    simp only [Nat.add_zero, nat_max_eq]
    omega

theorem fb_pre_bls_pairing :
    TerminatingFunBoundedOn GuestInv (ofString "pre_bls_pairing") K.«pre_bls_pairing» := by
  have _ := fb_udivmod
  have _ := fb_charge_gas
  have _ := fb_alloc
  have _ := fb_bls_pairing_exec
  bls_prove 818 Guest.Software.guestFn_pre_bls_pairing K.«pre_bls_pairing»

/-! ### 3. KZG point evaluation helpers, verification, and precompile -/

theorem fb_kzg_decompress_g1 :
    TerminatingFunBoundedOn GuestInv (ofString "kzg_decompress_g1") K.«kzg_decompress_g1» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_memcpy
  have _ := fb_bls_fp_from_be48
  have _ := fb_heap_release
  have _ := fb_bls_fp_is_zero
  have _ := fb_g1_set_inf
  have _ := fb_bls_fp_lt_raw
  have _ := fb_bls_fp_to_mont
  have _ := fb_bls_fp_sqr
  have _ := fb_bls_fp_mul
  have _ := fb_bls_fp_add
  have _ := fb_bls_fp_pow
  have _ := fb_bls_fp_eq
  have _ := fb_bls_fp_is_high
  have _ := fb_bls_fp_neg
  bls_prove 797 Guest.Software.guestFn_kzg_decompress_g1 K.«kzg_decompress_g1»

theorem fb_kzg_load_g1 :
    TerminatingFunBoundedOn GuestInv (ofString "kzg_load_g1") K.«kzg_load_g1» := by
  have _ := InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB1.fb_is_zero_bytes
  have _ := fb_g1_set_inf
  have _ := fb_kzg_decompress_g1
  have _ := fb_g1_is_inf
  have _ := fb_g1_subgroup_check
  bls_prove 798 Guest.Software.guestFn_kzg_load_g1 K.«kzg_load_g1»

theorem fb_kzg_neg_scalar :
    TerminatingFunBoundedOn GuestInv (ofString "kzg_neg_scalar") K.«kzg_neg_scalar» := by
  have _ := fb_u256_from_be
  have _ := fb_u256_is_zero
  have _ := InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2.fb_u256_sub
  bls_prove 799 Guest.Software.guestFn_kzg_neg_scalar K.«kzg_neg_scalar»

theorem fb_kzg_verify :
    TerminatingFunBoundedOn GuestInv (ofString "kzg_verify") K.«kzg_verify» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fp2_copy
  have _ := fb_fp2_set_one
  have _ := fb_kzg_neg_scalar
  have _ := fb_g2_mul
  have _ := fb_g2_add
  have _ := fb_memcpy
  have _ := fb_g1_mul
  have _ := fb_g1_add
  have _ := fb_g2_neg
  have _ := fb_fp12_set_one
  have _ := fb_pair_accumulate
  have _ := fb_fp12_final_exp
  have _ := fb_fp12_is_one
  have _ := fb_heap_release
  bls_prove 800 Guest.Software.guestFn_kzg_verify K.«kzg_verify»

theorem fb_kzg_point_evaluation_exec :
    TerminatingFunBoundedOn GuestInv (ofString "kzg_point_evaluation_exec") K.«kzg_point_evaluation_exec» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := InitECandidate.Solver.Wave8GuestInv.FastSha256.fb_sha256
  have _ := fb_memeq
  have _ := fb_kzg_load_g1
  have _ := fb_u256_from_be
  have _ := fb_u256_lt
  have _ := fb_kzg_verify
  have _ := fb_heap_release
  have _ := fb_memzero
  have _ := Arith.fb_u256_to_be32
  bls_prove 809 Guest.Software.guestFn_kzg_point_evaluation_exec K.«kzg_point_evaluation_exec»

theorem fb_pre_kzg_point_evaluation :
    TerminatingFunBoundedOn GuestInv (ofString "pre_kzg_point_evaluation") K.«pre_kzg_point_evaluation» := by
  have _ := fb_charge_gas
  have _ := fb_alloc
  have _ := fb_kzg_point_evaluation_exec
  bls_prove 821 Guest.Software.guestFn_pre_kzg_point_evaluation K.«pre_kzg_point_evaluation»

end InitECandidate.Solver.Wave8GuestInv.R16ArithPort
