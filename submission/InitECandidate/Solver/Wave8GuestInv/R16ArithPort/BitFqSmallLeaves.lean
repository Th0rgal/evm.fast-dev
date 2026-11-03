import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.CappedLoopLeaves

/-! Standalone 0-sorry bounded termination proofs on `GuestInv` for:
- `fb_bit_length64`, `fb_u256_bit_length`
- `fb_fq_mul_small`, `fb_fe_mul_small`, `fb_fe_add`, `fb_fe_sub`, `fb_fe_neg`, `fb_fe_eq`
- `fb_fe_mul`, `fb_fe_sqr`, `fb_ecp_is_inf`, `fb_ecp_double`, `fb_ecp_add`, `fb_ecp_linefunc`
- `fb_fq_to_mont`, `fb_fq_from_mont`, `fb_fq_inv`
- `fb_fq12_cast`, `fb_fq12_twist`, `fb_fq12_frob`, `fb_fq12_pow_words`
- `fb_bn254_parse_g1`, `fb_bn254_parse_g2`, `fb_bn254_g1_to_bytes`,
  `fb_bn254_g1_add`, `fb_bn254_g1_mul`, `fb_bn254_miller_raw`.
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
open InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2 (while_scaled32_walk_guestInv DomainTouch.dec_load_comb4)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.BlsPrecompiles
open InitECandidate.Solver.Wave8GuestInv.R16ArithPort.Capped

/-! ### 1. `bit_length64`, `u256_bit_length`, and `fq_mul_small` -/

theorem fb_bit_length64 :
    TerminatingFunBoundedOn GuestInv (ofString "bit_length64") K.«bit_length64» :=
  InitECandidate.Solver.Wave8GuestInv.Arith.fb_bit_length64

theorem fb_u256_bit_length :
    TerminatingFunBoundedOn GuestInv (ofString "u256_bit_length") K.«u256_bit_length» :=
  InitECandidate.Solver.Wave8GuestInv.Arith.fb_u256_bit_length

theorem fb_fq_mul_small :
    TerminatingFunBoundedOn GuestInv (ofString "fq_mul_small") K.«fq_mul_small» :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2.fb_fq_mul_small

/-! ### 2. `fq` Montgomery helpers & `fq_inv` -/

theorem fb_fq_to_mont :
    TerminatingFunBoundedOn GuestInv (ofString "fq_to_mont") K.«fq_to_mont» := by
  have _ := fb_fq_mul
  bls_prove 653 Guest.Software.guestFn_fq_to_mont K.«fq_to_mont»

theorem fb_fq_from_mont :
    TerminatingFunBoundedOn GuestInv (ofString "fq_from_mont") K.«fq_from_mont» := by
  have _ := fb_fq_mul
  bls_prove 654 Guest.Software.guestFn_fq_from_mont K.«fq_from_mont»

theorem fb_fq_inv :
    TerminatingFunBoundedOn GuestInv (ofString "fq_inv") K.«fq_inv» := by
  have _ := InitECandidate.Solver.Wave8GuestInv.Arith.fb_modinv_bin
  have _ := fb_fq_mul
  bls_prove 655 Guest.Software.guestFn_fq_inv K.«fq_inv»

/-! ### 3. Unconditional `fe_*` and `ecp_*` extension/curve leaves -/

theorem fb_fe_add :
    TerminatingFunBoundedOn GuestInv (ofString "fe_add") K.«fe_add» :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2.fb_fe_add

theorem fb_fe_sub :
    TerminatingFunBoundedOn GuestInv (ofString "fe_sub") K.«fe_sub» :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2.fb_fe_sub

theorem fb_fe_mul_small :
    TerminatingFunBoundedOn GuestInv (ofString "fe_mul_small") K.«fe_mul_small» :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2.fb_fe_mul_small

theorem fb_fe_neg :
    TerminatingFunBoundedOn GuestInv (ofString "fe_neg") K.«fe_neg» := by
  fb_unfold 665 Guest.Software.guestFn_fe_neg
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · exact while_scaled32_walk_guestInv (ofString "a") (ofString "i") _
        (dec_guestInv _ _ _ (decCall_guestInv' fb_fq_neg (straightOn _ rfl)))
        (DomainTouch.dec_load_comb4 _ _ _) (by counter_step) rfl
    · exact straightOn _ rfl
  · rw [domainBytes_eq]
    unfold K.«fe_neg»
    fast_generalize_K
    omega

theorem fb_fe_eq :
    TerminatingFunBoundedOn GuestInv (ofString "fe_eq") K.«fe_eq» :=
  fb_fe_eq_of fb_memeq

theorem fb_fe_mul :
    TerminatingFunBoundedOn GuestInv (ofString "fe_mul") K.«fe_mul» :=
  fb_fe_mul_of fb_fq12_mul

theorem fb_fe_sqr :
    TerminatingFunBoundedOn GuestInv (ofString "fe_sqr") K.«fe_sqr» :=
  fb_fe_sqr_of fb_fe_mul fb_fq12_sqr

theorem fb_ecp_is_inf :
    TerminatingFunBoundedOn GuestInv (ofString "ecp_is_inf") K.«ecp_is_inf» := by
  have _ := fb_fe_is_zero
  bls_prove 672 Guest.Software.guestFn_ecp_is_inf K.«ecp_is_inf»

theorem fb_ecp_double :
    TerminatingFunBoundedOn GuestInv (ofString "ecp_double") K.«ecp_double» :=
  fb_ecp_double_of fb_fe_mul fb_fe_mul_small fb_fe_sqr fb_fe_sub

theorem fb_ecp_add :
    TerminatingFunBoundedOn GuestInv (ofString "ecp_add") K.«ecp_add» :=
  fb_ecp_add_of fb_ecp_double fb_fe_eq fb_fe_mul fb_fe_mul_small fb_fe_sqr fb_fe_sub

theorem fb_ecp_linefunc :
    TerminatingFunBoundedOn GuestInv (ofString "ecp_linefunc") K.«ecp_linefunc» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_heap_release
  have _ := fb_fe_set_zero
  have _ := fb_fe_is_zero
  have _ := fb_fe_mul
  have _ := fb_fe_sub
  have _ := fb_fe_sqr
  have _ := fb_fe_mul_small
  bls_prove 676 Guest.Software.guestFn_ecp_linefunc K.«ecp_linefunc»

/-! ### 4. `fq12_cast`, `fq12_twist`, `fq12_frob`, `fq12_pow_words` -/

theorem fb_fq12_cast :
    TerminatingFunBoundedOn GuestInv (ofString "fq12_cast") K.«fq12_cast» := by
  have _ := fb_memzero
  bls_prove 678 Guest.Software.guestFn_fq12_cast K.«fq12_cast»

theorem fb_fq12_twist :
    TerminatingFunBoundedOn GuestInv (ofString "fq12_twist") K.«fq12_twist» := by
  have _ := fb_memzero
  have _ := fb_fq_mul_small
  have _ := fb_fq_sub
  bls_unfold 677 Guest.Software.guestFn_fq12_twist
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    apply while_up_unsigned_const_guestInv (ofString "j") (BitVec.ofNat 64 3)
    · bls_auto
    · counter_step
  · rw [show (BitVec.ofNat 64 3).toNat = 3 by decide]
    bls_arith K.«fq12_twist»

theorem fb_fq12_frob :
    TerminatingFunBoundedOn GuestInv (ofString "fq12_frob") K.«fq12_frob» := by
  have _ := fb_fq_mul_small
  have _ := fb_fq_add
  have _ := fb_fq_neg
  have _ := fb_fq_mul
  have _ := fb_fq_sub
  bls_unfold 679 Guest.Software.guestFn_fq12_frob
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    apply while_up_unsigned_const_guestInv (ofString "k") (BitVec.ofNat 64 6)
    · bls_auto
    · counter_step
  · rw [show (BitVec.ofNat 64 6).toNat = 6 by decide]
    bls_arith K.«fq12_frob»

theorem fb_fq12_pow_words :
    TerminatingFunBoundedOn GuestInv (ofString "fq12_pow_words") K.«fq12_pow_words» := by
  have _ := fb_fe_set_one
  have _ := fb_fq12_sqr
  have _ := fb_fq12_mul
  bls_unfold 683 Guest.Software.guestFn_fq12_pow_words
  apply TerminatingProgBoundedOn.weaken'
  · bls_auto_loops
    apply while_down_unsigned_guestInv (ofString "i")
    · bls_auto
    · exact CounterStep.suffix _ _ _ (CounterStep.sub_one _) (by decide)
  · bls_arith K.«fq12_pow_words»

/-! ### 5. BN254 G1/G2/Miller leaves (`bn254_parse_g1`, `bn254_parse_g2`, `bn254_g1_to_bytes`,
`bn254_g1_add`, `bn254_g1_mul`, `bn254_miller_raw`) -/

theorem fb_bn254_parse_g1 :
    TerminatingFunBoundedOn GuestInv (ofString "bn254_parse_g1") K.«bn254_parse_g1» := by
  have _ := fb_u256_from_be
  have _ := fb_u256_lt
  have _ := fb_u256_is_zero
  have _ := fb_ecp_set_inf
  have _ := fb_fq_to_mont
  have _ := fb_fq_mul
  have _ := fb_fq_add
  have _ := fb_u256_eq
  bls_prove 686 Guest.Software.guestFn_bn254_parse_g1 K.«bn254_parse_g1»

theorem fb_bn254_parse_g2 :
    TerminatingFunBoundedOn GuestInv (ofString "bn254_parse_g2") K.«bn254_parse_g2» := by
  have _ := fb_u256_from_be
  have _ := fb_u256_lt
  have _ := InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB1.fb_is_zero_bytes
  have _ := fb_ecp_set_inf
  have _ := fb_fq_to_mont
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fq2_mul
  have _ := fb_fe_add
  have _ := fb_memeq
  have _ := fb_heap_release
  bls_prove 687 Guest.Software.guestFn_bn254_parse_g2 K.«bn254_parse_g2»

theorem fb_bn254_g1_to_bytes :
    TerminatingFunBoundedOn GuestInv (ofString "bn254_g1_to_bytes") K.«bn254_g1_to_bytes» := by
  have _ := fb_u256_is_zero
  have _ := fb_memzero
  have _ := fb_fq_inv
  have _ := fb_fq_mul
  have _ := fb_fq_from_mont
  have _ := fb_u256_to_be32
  bls_prove 688 Guest.Software.guestFn_bn254_g1_to_bytes K.«bn254_g1_to_bytes»

theorem fb_bn254_g1_add :
    TerminatingFunBoundedOn GuestInv (ofString "bn254_g1_add") K.«bn254_g1_add» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_bn254_parse_g1
  have _ := fb_heap_release
  have _ := fb_ecp_add
  have _ := fb_bn254_g1_to_bytes
  bls_prove 689 Guest.Software.guestFn_bn254_g1_add K.«bn254_g1_add»

theorem fb_bn254_g1_mul :
    TerminatingFunBoundedOn GuestInv (ofString "bn254_g1_mul") K.«bn254_g1_mul» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_bn254_parse_g1
  have _ := fb_heap_release
  have _ := fb_u256_from_be
  have _ := fb_ecp_mul
  have _ := fb_bn254_g1_to_bytes
  bls_prove 690 Guest.Software.guestFn_bn254_g1_mul K.«bn254_g1_mul»

theorem fb_bn254_miller_raw :
    TerminatingFunBoundedOn GuestInv (ofString "bn254_miller_raw") K.«bn254_miller_raw» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_memcpy
  have _ := fb_fe_neg
  have _ := fb_fe_set_one
  have _ := fb_ecp_linefunc
  have _ := fb_fq12_sqr
  have _ := fb_fq12_mul
  have _ := fb_ecp_double
  have _ := fb_ecp_add
  have _ := fb_fq12_frob
  have _ := fb_heap_release
  bls_unfold 684 Guest.Software.guestFn_bn254_miller_raw
  apply TerminatingProgBoundedOn.weaken'
  · apply decCall_guestInv' fb_heap_mark
    apply decCall_guestInv' fb_alloc
    apply decCall_guestInv' fb_alloc
    apply decCall_guestInv' fb_alloc
    apply decCall_guestInv' fb_alloc
    apply decCall_guestInv' fb_alloc
    apply decCall_guestInv' fb_alloc
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_memcpy)
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_memcpy)
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fe_neg)
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fe_set_one)
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fe_set_one)
    apply dec_const_cap_guestInv "i" (BitVec.ofNat 64 64)
    apply seq_to_guestInv (fun _ h => h.1)
    · apply while_down_first_capped_on .lower (Or.inr rfl) "i"
      · bls_auto
      · rfl
    · bls_auto
  · rw [show (BitVec.ofNat 64 64).toNat = 64 by decide]
    bls_arith K.«bn254_miller_raw»

end InitECandidate.Solver.Wave8GuestInv.R16ArithPort
