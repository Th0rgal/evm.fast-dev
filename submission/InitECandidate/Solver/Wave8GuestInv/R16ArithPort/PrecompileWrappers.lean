import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsPairingKzgLeaves
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.Secp256k1Leaves
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BitFqSmallLeaves
import InitECandidate.Solver.Wave8GuestInv.R14Shards.MissingFb5.FbRipemd160

/-! Standalone bounded termination proofs on `GuestInv` for precompile entry points,
Blake2f compression, and low-level word helpers:
- `fb_st_le32`, `fb_st_le64`, `fb_sat_word`, `fb_credit_state_gas_refund`
- `fb_blake2_g`, `fb_blake2b_f`
- `fb_precompile_index`, `fb_pre_identity`, `fb_pre_sha256`, `fb_pre_ripemd160`,
  `fb_pre_ecrecover`, `fb_pre_blake2f`, `fb_pre_alt_bn128_add`, `fb_pre_alt_bn128_mul`,
  `fb_pre_p256verify`.
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
open InitECandidate.Solver.Wave8GuestInv.FastU256Core
open InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB1
open InitECandidate.Solver.Wave8GuestInv.FastSha256
open InitECandidate.Solver.Wave8GuestInv.R14Shards.MissingFb5
open InitECandidate.Solver.Wave8GuestInv.R16Shards.BlsPrecompiles

/-! ### 1. Word-level helpers (`st_le32`, `st_le64`, `sat_word`, `credit_state_gas_refund`) -/

theorem fb_st_le32 :
    TerminatingFunBoundedOn GuestInv (ofString "st_le32") K.«st_le32» := by
  bls_prove 25 Guest.Software.guestFn_st_le32 K.«st_le32»

theorem fb_st_le64 :
    TerminatingFunBoundedOn GuestInv (ofString "st_le64") K.«st_le64» := by
  have _ := fb_st_le32
  bls_prove 26 Guest.Software.guestFn_st_le64 K.«st_le64»

theorem fb_sat_word :
    TerminatingFunBoundedOn GuestInv (ofString "sat_word") K.«sat_word» := by
  bls_prove 440 Guest.Software.guestFn_sat_word K.«sat_word»

theorem fb_credit_state_gas_refund :
    TerminatingFunBoundedOn GuestInv (ofString "credit_state_gas_refund")
      K.«credit_state_gas_refund» := by
  have _ := fb_min
  bls_prove 450 Guest.Software.guestFn_credit_state_gas_refund K.«credit_state_gas_refund»

/-! ### 2. Blake2f compression (`blake2_g`, `blake2b_f`, `pre_blake2f`) -/

theorem fb_blake2_g :
    TerminatingFunBoundedOn GuestInv (ofString "blake2_g") K.«blake2_g» := by
  bls_prove 622 Guest.Software.guestFn_blake2_g K.«blake2_g»

theorem fb_blake2b_f :
    TerminatingFunBoundedOn GuestInv (ofString "blake2b_f") K.«blake2b_f» := by
  have _ := fb_memcpy
  have _ := fb_blake2_g
  bls_unfold 623 Guest.Software.guestFn_blake2b_f
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    · apply while_up_exp_guestInv .lower (Or.inr rfl) (ofString "r") _
      · bls_auto
      · refine CounterStep.seq _ _ _ rfl rfl ?_
        refine CounterStep.seq _ _ _ rfl rfl ?_
        refine CounterStep.seq _ _ _ rfl rfl ?_
        refine CounterStep.seq _ _ _ rfl rfl ?_
        refine CounterStep.seq _ _ _ rfl rfl ?_
        refine CounterStep.seq _ _ _ rfl rfl ?_
        refine CounterStep.seq _ _ _ rfl rfl ?_
        refine CounterStep.seq _ _ _ rfl rfl ?_
        exact CounterStep.suffix _ _ _ (CounterStep.assign _ 1#64) (by decide)
      · rfl
    · apply while_up_signed_const_guestInv (ofString "i") 1#64 (BitVec.ofNat 64 8)
      · bls_auto
      · bls_counter_step
      · decide
      · decide
  · bls_arith K.«blake2b_f»

theorem fb_pre_blake2f :
    TerminatingFunBoundedOn GuestInv (ofString "pre_blake2f") K.«pre_blake2f» := by
  have _ := fb_charge_gas
  have _ := fb_alloc
  have _ := fb_heap_mark
  have _ := fb_blake2b_f
  have _ := fb_st_le64
  have _ := fb_heap_release
  bls_unfold 827 Guest.Software.guestFn_pre_blake2f
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    · apply while_up_signed_const_guestInv (ofString "i") 1#64 (BitVec.ofNat 64 8)
      · bls_auto
      · bls_counter_step
      · decide
      · decide
    · apply while_up_signed_const_guestInv (ofString "i") 1#64 (BitVec.ofNat 64 16)
      · bls_auto
      · bls_counter_step
      · decide
      · decide
    · apply while_up_signed_const_guestInv (ofString "i") 1#64 (BitVec.ofNat 64 8)
      · bls_auto
      · bls_counter_step
      · decide
      · decide
  · bls_arith K.«pre_blake2f»

/-! ### 3. Precompile dispatch index & wrapper entry points -/

theorem fb_precompile_index :
    TerminatingFunBoundedOn GuestInv (ofString "precompile_index") K.«precompile_index» := by
  have _ := fb_is_zero_bytes
  bls_prove 822 Guest.Software.guestFn_precompile_index K.«precompile_index»

theorem fb_pre_identity :
    TerminatingFunBoundedOn GuestInv (ofString "pre_identity") K.«pre_identity» := by
  have _ := fb_words_of
  have _ := fb_charge_gas
  bls_prove 823 Guest.Software.guestFn_pre_identity K.«pre_identity»

theorem fb_pre_sha256 :
    TerminatingFunBoundedOn GuestInv (ofString "pre_sha256") K.«pre_sha256» := by
  have _ := fb_words_of
  have _ := fb_charge_gas
  have _ := fb_alloc
  have _ := fb_sha256
  bls_prove 824 Guest.Software.guestFn_pre_sha256 K.«pre_sha256»

theorem fb_pre_ripemd160 :
    TerminatingFunBoundedOn GuestInv (ofString "pre_ripemd160") K.«pre_ripemd160» := by
  have _ := fb_words_of
  have _ := fb_charge_gas
  have _ := fb_alloc
  have _ := fb_memzero
  have _ := fb_ripemd160
  bls_prove 826 Guest.Software.guestFn_pre_ripemd160 K.«pre_ripemd160»

theorem fb_pre_ecrecover :
    TerminatingFunBoundedOn GuestInv (ofString "pre_ecrecover") K.«pre_ecrecover» := by
  have _ := fb_charge_gas
  have _ := fb_alloc
  have _ := fb_heap_mark
  have _ := fb_buffer_read
  have _ := fb_u256_from_be
  have _ := fb_u256_fits_word
  have _ := fb_heap_release
  have _ := fb_secp256k1_ecrecover
  have _ := fb_memzero
  bls_prove 825 Guest.Software.guestFn_pre_ecrecover K.«pre_ecrecover»

theorem fb_pre_alt_bn128_add :
    TerminatingFunBoundedOn GuestInv (ofString "pre_alt_bn128_add") K.«pre_alt_bn128_add» := by
  have _ := fb_alloc
  have _ := fb_bn254_g1_add
  have _ := fb_buffer_read
  have _ := fb_charge_gas
  have _ := fb_heap_mark
  have _ := fb_heap_release
  bls_prove 692 Guest.Software.guestFn_pre_alt_bn128_add K.«pre_alt_bn128_add»

theorem fb_pre_alt_bn128_mul :
    TerminatingFunBoundedOn GuestInv (ofString "pre_alt_bn128_mul") K.«pre_alt_bn128_mul» := by
  have _ := fb_alloc
  have _ := fb_bn254_g1_mul
  have _ := fb_buffer_read
  have _ := fb_charge_gas
  have _ := fb_heap_mark
  have _ := fb_heap_release
  bls_prove 693 Guest.Software.guestFn_pre_alt_bn128_mul K.«pre_alt_bn128_mul»

theorem fb_pre_p256verify :
    TerminatingFunBoundedOn GuestInv (ofString "pre_p256verify") K.«pre_p256verify» := by
  have _ := fb_charge_gas
  have _ := fb_alloc
  have _ := fb_u256_from_be
  have _ := fb_p256_verify
  have _ := fb_memzero
  bls_prove 645 Guest.Software.guestFn_pre_p256verify K.«pre_p256verify»

end InitECandidate.Solver.Wave8GuestInv.R16ArithPort
