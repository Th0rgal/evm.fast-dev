import InitECandidate.Solver.Wave8GuestInv.Expressions

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded

theorem ub_bit_length64 : TerminatingFunBounded (ofString "bit_length64") K.«bit_length64» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 77
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_bit_length64) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_bit_length64 : TerminatingFunBoundedOn GuestInv (ofString "bit_length64") K.«bit_length64» :=
  TerminatingFunBoundedOn.of_unconditional ub_bit_length64


theorem ub_bswap64 : TerminatingFunBounded (ofString "bswap64") K.«bswap64» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 23
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_bswap64) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_bswap64 : TerminatingFunBoundedOn GuestInv (ofString "bswap64") K.«bswap64» :=
  TerminatingFunBoundedOn.of_unconditional ub_bswap64


theorem ub_max : TerminatingFunBounded (ofString "max") K.«max» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 32
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_max) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_max : TerminatingFunBoundedOn GuestInv (ofString "max") K.«max» :=
  TerminatingFunBoundedOn.of_unconditional ub_max


theorem ub_min : TerminatingFunBounded (ofString "min") K.«min» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 31
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_min) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_min : TerminatingFunBoundedOn GuestInv (ofString "min") K.«min» :=
  TerminatingFunBoundedOn.of_unconditional ub_min


theorem ub_mul64x64 : TerminatingFunBounded (ofString "mul64x64") K.«mul64x64» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 59
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_mul64x64) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_mul64x64 : TerminatingFunBoundedOn GuestInv (ofString "mul64x64") K.«mul64x64» :=
  TerminatingFunBoundedOn.of_unconditional ub_mul64x64


theorem ub_p256_set_affine : TerminatingFunBounded (ofString "p256_set_affine") K.«p256_set_affine» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 638
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_p256_set_affine) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_p256_set_affine : TerminatingFunBoundedOn GuestInv (ofString "p256_set_affine") K.«p256_set_affine» :=
  TerminatingFunBoundedOn.of_unconditional ub_p256_set_affine


theorem ub_p256_set_infinity : TerminatingFunBounded (ofString "p256_set_infinity") K.«p256_set_infinity» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 637
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_p256_set_infinity) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_p256_set_infinity : TerminatingFunBoundedOn GuestInv (ofString "p256_set_infinity") K.«p256_set_infinity» :=
  TerminatingFunBoundedOn.of_unconditional ub_p256_set_infinity


theorem ub_sha256_block : TerminatingFunBounded (ofString "sha256_block") K.«sha256_block» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 93
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_sha256_block) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_sha256_block : TerminatingFunBoundedOn GuestInv (ofString "sha256_block") K.«sha256_block» :=
  TerminatingFunBoundedOn.of_unconditional ub_sha256_block


theorem ub_sha256_pair : TerminatingFunBounded (ofString "sha256_pair") K.«sha256_pair» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 96
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_sha256_pair) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_sha256_pair : TerminatingFunBoundedOn GuestInv (ofString "sha256_pair") K.«sha256_pair» :=
  TerminatingFunBoundedOn.of_unconditional ub_sha256_pair


theorem ub_sha256_state_init : TerminatingFunBounded (ofString "sha256_state_init") K.«sha256_state_init» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 92
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_sha256_state_init) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_sha256_state_init : TerminatingFunBoundedOn GuestInv (ofString "sha256_state_init") K.«sha256_state_init» :=
  TerminatingFunBoundedOn.of_unconditional ub_sha256_state_init


theorem ub_st_be32 : TerminatingFunBounded (ofString "st_be32") K.«st_be32» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 27
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_st_be32) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_st_be32 : TerminatingFunBoundedOn GuestInv (ofString "st_be32") K.«st_be32» :=
  TerminatingFunBoundedOn.of_unconditional ub_st_be32


theorem ub_trap_with : TerminatingFunBounded (ofString "trap_with") K.«trap_with» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 3
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_trap_with) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_trap_with : TerminatingFunBoundedOn GuestInv (ofString "trap_with") K.«trap_with» :=
  TerminatingFunBoundedOn.of_unconditional ub_trap_with


theorem ub_u256_add : TerminatingFunBounded (ofString "u256_add") K.«u256_add» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 56
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_add) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_u256_add : TerminatingFunBoundedOn GuestInv (ofString "u256_add") K.«u256_add» :=
  TerminatingFunBoundedOn.of_unconditional ub_u256_add


theorem ub_u256_add_carry : TerminatingFunBounded (ofString "u256_add_carry") K.«u256_add_carry» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 55
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_add_carry) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_u256_add_carry : TerminatingFunBoundedOn GuestInv (ofString "u256_add_carry") K.«u256_add_carry» :=
  TerminatingFunBoundedOn.of_unconditional ub_u256_add_carry


theorem ub_u256_and : TerminatingFunBounded (ofString "u256_and") K.«u256_and» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 52
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_and) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_u256_and : TerminatingFunBoundedOn GuestInv (ofString "u256_and") K.«u256_and» :=
  TerminatingFunBoundedOn.of_unconditional ub_u256_and


theorem ub_u256_eq : TerminatingFunBounded (ofString "u256_eq") K.«u256_eq» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 45
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_eq) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_u256_eq : TerminatingFunBoundedOn GuestInv (ofString "u256_eq") K.«u256_eq» :=
  TerminatingFunBoundedOn.of_unconditional ub_u256_eq


theorem ub_u256_fits_word : TerminatingFunBounded (ofString "u256_fits_word") K.«u256_fits_word» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 41
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_fits_word) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_u256_fits_word : TerminatingFunBoundedOn GuestInv (ofString "u256_fits_word") K.«u256_fits_word» :=
  TerminatingFunBoundedOn.of_unconditional ub_u256_fits_word


theorem ub_u256_from_word : TerminatingFunBounded (ofString "u256_from_word") K.«u256_from_word» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 39
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_from_word) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_u256_from_word : TerminatingFunBoundedOn GuestInv (ofString "u256_from_word") K.«u256_from_word» :=
  TerminatingFunBoundedOn.of_unconditional ub_u256_from_word


theorem ub_u256_is_zero : TerminatingFunBounded (ofString "u256_is_zero") K.«u256_is_zero» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 42
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_is_zero) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_u256_is_zero : TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero» :=
  TerminatingFunBoundedOn.of_unconditional ub_u256_is_zero


theorem ub_u256_limb : TerminatingFunBounded (ofString "u256_limb") K.«u256_limb» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 43
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_limb) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_u256_limb : TerminatingFunBoundedOn GuestInv (ofString "u256_limb") K.«u256_limb» :=
  TerminatingFunBoundedOn.of_unconditional ub_u256_limb


theorem ub_u256_lt : TerminatingFunBounded (ofString "u256_lt") K.«u256_lt» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 46
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_lt) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_u256_lt : TerminatingFunBoundedOn GuestInv (ofString "u256_lt") K.«u256_lt» :=
  TerminatingFunBoundedOn.of_unconditional ub_u256_lt


theorem ub_u256_neg : TerminatingFunBounded (ofString "u256_neg") K.«u256_neg» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 58
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_neg) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_u256_neg : TerminatingFunBoundedOn GuestInv (ofString "u256_neg") K.«u256_neg» :=
  TerminatingFunBoundedOn.of_unconditional ub_u256_neg


theorem ub_u256_not : TerminatingFunBounded (ofString "u256_not") K.«u256_not» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 51
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_not) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_u256_not : TerminatingFunBoundedOn GuestInv (ofString "u256_not") K.«u256_not» :=
  TerminatingFunBoundedOn.of_unconditional ub_u256_not


theorem ub_u256_or : TerminatingFunBounded (ofString "u256_or") K.«u256_or» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 53
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_or) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_u256_or : TerminatingFunBoundedOn GuestInv (ofString "u256_or") K.«u256_or» :=
  TerminatingFunBoundedOn.of_unconditional ub_u256_or


theorem ub_u256_shl : TerminatingFunBounded (ofString "u256_shl") K.«u256_shl» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 81
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_shl) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_u256_shl : TerminatingFunBoundedOn GuestInv (ofString "u256_shl") K.«u256_shl» :=
  TerminatingFunBoundedOn.of_unconditional ub_u256_shl


theorem ub_u256_shr : TerminatingFunBounded (ofString "u256_shr") K.«u256_shr» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 82
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_shr) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_u256_shr : TerminatingFunBoundedOn GuestInv (ofString "u256_shr") K.«u256_shr» :=
  TerminatingFunBoundedOn.of_unconditional ub_u256_shr


theorem ub_u256_slt : TerminatingFunBounded (ofString "u256_slt") K.«u256_slt» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 48
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_slt) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_u256_slt : TerminatingFunBoundedOn GuestInv (ofString "u256_slt") K.«u256_slt» :=
  TerminatingFunBoundedOn.of_unconditional ub_u256_slt


theorem ub_u256_sub : TerminatingFunBounded (ofString "u256_sub") K.«u256_sub» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 57
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_sub) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_u256_sub : TerminatingFunBoundedOn GuestInv (ofString "u256_sub") K.«u256_sub» :=
  TerminatingFunBoundedOn.of_unconditional ub_u256_sub


theorem ub_u256_to_digits : TerminatingFunBounded (ofString "u256_to_digits") K.«u256_to_digits» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 64
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_to_digits) rfl, ?_⟩
  exact (TerminatingProgBounded.straight _ rfl)

theorem fb_u256_to_digits : TerminatingFunBoundedOn GuestInv (ofString "u256_to_digits") K.«u256_to_digits» :=
  TerminatingFunBoundedOn.of_unconditional ub_u256_to_digits


end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
