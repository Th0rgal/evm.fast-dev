import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.Wave8GuestInv.Shards.S05.Structural
import InitECandidate.Solver.Wave8GuestInv.Shards.S14.Core

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Campaign.Leaves.S05

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanRunBoundedExt
open InitECandidate.Solver.PanTerminatingBounded

/-- Function-level boundedness guarded by an arbitrary entry-state predicate. -/
def TerminatingFunBoundedOn
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) (K : Nat) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    TerminatingProgBoundedOn P body K

theorem terminatingFunBoundedOn_of_funBounded
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    {fname : MlS} {K : Nat} (h : FunBounded fname K) :
    TerminatingFunBoundedOn P fname K := by
  obtain ⟨params, body, retShape, hlookup, hbody⟩ := h
  refine ⟨params, body, retShape, hlookup, ?_⟩
  intro F state hcode _
  exact terminatingProgBounded_of_progBounded hbody state hcode

/-- `sat_word` has no calls and is structurally straight-line. -/
theorem fb_sat_word (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) :
    TerminatingFunBoundedOn P (ofString "sat_word") 0 := by
  apply terminatingFunBoundedOn_of_funBounded
  exact funBounded_of_guestAst 440 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_sat_word 0 rfl (ProgBounded.straight _ rfl)

/-- `credit_state_gas_refund` only calls the straight-line `min` helper. -/
theorem fb_credit_state_gas_refund
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) :
    TerminatingFunBoundedOn P (ofString "credit_state_gas_refund") 1 := by
  apply terminatingFunBoundedOn_of_funBounded
  refine funBounded_of_guestAst 450 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_credit_state_gas_refund 1 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_credit_state_gas_refund,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    List.map, Option.map]
  apply ProgBounded.dec
  exact ProgBounded.decCall
    (funBounded_of_guestAst 31 (by rw [guestAst_len]; decide)
      Guest.Software.guestFn_min 0 rfl (ProgBounded.straight _ rfl)) _ _ _
    (ProgBounded.seq (ProgBounded.straight _ rfl)
      (ProgBounded.seq (ProgBounded.straight _ rfl)
        (ProgBounded.seq (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))))

private theorem funBounded_add_sat : FunBounded (ofString "add_sat") 0 :=
  funBounded_of_guestAst 441 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_add_sat 0 rfl (ProgBounded.straight _ rfl)

private theorem funBounded_ceil32 : FunBounded (ofString "ceil32") 1 :=
  by
    refine funBounded_of_guestAst 442 (by rw [guestAst_len]; decide)
      Guest.Software.guestFn_ceil32 1 rfl ?_
    dsimp only [extractFn, Guest.Software.guestFn_ceil32,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      List.map, Option.map]
    apply ProgBounded.dec
    exact ProgBounded.seq
      (ProgBounded.ite _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
      (ProgBounded.decCall funBounded_add_sat _ _ _ (ProgBounded.straight _ rfl))

private theorem funBounded_words_of : FunBounded (ofString "words_of") 2 :=
  by
    refine funBounded_of_guestAst 443 (by rw [guestAst_len]; decide)
      Guest.Software.guestFn_words_of 2 rfl ?_
    dsimp only [extractFn, Guest.Software.guestFn_words_of,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      List.map, Option.map]
    exact ProgBounded.decCall funBounded_ceil32 _ _ _ (ProgBounded.straight _ rfl)

private theorem funBounded_charge_gas : FunBounded (ofString "charge_gas") 0 :=
  funBounded_of_guestAst 448 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_charge_gas 0 rfl (ProgBounded.straight _ rfl)

/-- `pre_identity` is the static composition of `words_of` and `charge_gas`. -/
theorem fb_pre_identity
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) :
    TerminatingFunBoundedOn P (ofString "pre_identity") 4 := by
  apply terminatingFunBoundedOn_of_funBounded
  refine funBounded_of_guestAst 823 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_pre_identity 4 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_pre_identity,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    List.map, Option.map]
  apply ProgBounded.dec
  apply ProgBounded.dec
  exact ProgBounded.decCall funBounded_words_of _ _ _
    (ProgBounded.seq (ProgBounded.call funBounded_charge_gas none _)
      (ProgBounded.seq (ProgBounded.straight _ rfl)
        (ProgBounded.seq (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))))

theorem fb_pre_alt_bn128_mul
    (h_alloc : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "alloc")
      InitECandidate.Solver.Wave8GuestInv.K.«alloc»)
    (h_bn254_g1_mul : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "bn254_g1_mul")
      InitECandidate.Solver.Wave8GuestInv.K.«bn254_g1_mul»)
    (h_buffer_read : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "buffer_read")
      InitECandidate.Solver.Wave8GuestInv.K.«buffer_read»)
    (h_charge_gas : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "charge_gas")
      InitECandidate.Solver.Wave8GuestInv.K.«charge_gas»)
    (h_heap_mark : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "heap_mark")
      InitECandidate.Solver.Wave8GuestInv.K.«heap_mark»)
    (h_heap_release : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "heap_release")
      InitECandidate.Solver.Wave8GuestInv.K.«heap_release»)
    : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "pre_alt_bn128_mul")
      InitECandidate.Solver.Wave8GuestInv.K.«pre_alt_bn128_mul» := by
  have hl := originalRuntimeCode_lookup_of_guestAst_getElem 693 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_pre_alt_bn128_mul) rfl
  dsimp only [extractFn, Guest.Software.guestFn_pre_alt_bn128_mul] at hl
  refine ⟨_, _, _, hl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_pre_alt_bn128_mul,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply Campaign.Leaves.S05.Structural.weaken'
  · s05_auto
  · unfold InitECandidate.Solver.Wave8GuestInv.K.«pre_alt_bn128_mul»
    omega

theorem fb_pre_alt_bn128_pairing_check
    (h_udivmod : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "udivmod")
      InitECandidate.Solver.Wave8GuestInv.K.«udivmod»)
    (h_charge_gas : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "charge_gas")
      InitECandidate.Solver.Wave8GuestInv.K.«charge_gas»)
    (h_bn254_pairing_check : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "bn254_pairing_check")
      InitECandidate.Solver.Wave8GuestInv.K.«bn254_pairing_check»)
    (h_alloc : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "alloc")
      InitECandidate.Solver.Wave8GuestInv.K.«alloc»)
    (h_memzero : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "memzero")
      InitECandidate.Solver.Wave8GuestInv.K.«memzero»)
    :
    InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "pre_alt_bn128_pairing_check")
      InitECandidate.Solver.Wave8GuestInv.K.«pre_alt_bn128_pairing_check» := by
  have hl := originalRuntimeCode_lookup_of_guestAst_getElem 694 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_pre_alt_bn128_pairing_check) rfl
  dsimp only [extractFn, Guest.Software.guestFn_pre_alt_bn128_pairing_check] at hl
  refine ⟨_, _, _, hl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_pre_alt_bn128_pairing_check,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply Campaign.Leaves.S05.Structural.weaken'
  · s05_auto
  · unfold InitECandidate.Solver.Wave8GuestInv.K.«pre_alt_bn128_pairing_check»
    omega

theorem fb_pre_sha256
    (h_words_of : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "words_of")
      InitECandidate.Solver.Wave8GuestInv.K.«words_of»)
    (h_charge_gas : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "charge_gas")
      InitECandidate.Solver.Wave8GuestInv.K.«charge_gas»)
    (h_alloc : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "alloc")
      InitECandidate.Solver.Wave8GuestInv.K.«alloc»)
    (h_sha256 : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "sha256")
      InitECandidate.Solver.Wave8GuestInv.K.«sha256»)
    : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "pre_sha256")
      InitECandidate.Solver.Wave8GuestInv.K.«pre_sha256» := by
  have hl := originalRuntimeCode_lookup_of_guestAst_getElem 824 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_pre_sha256) rfl
  dsimp only [extractFn, Guest.Software.guestFn_pre_sha256] at hl
  refine ⟨_, _, _, hl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_pre_sha256,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply Campaign.Leaves.S05.Structural.weaken'
  · s05_auto
  · unfold InitECandidate.Solver.Wave8GuestInv.K.«pre_sha256»
    omega

theorem fb_pre_ripemd160
    (h_words_of : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "words_of") InitECandidate.Solver.Wave8GuestInv.K.«words_of»)
    (h_charge_gas : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "charge_gas") InitECandidate.Solver.Wave8GuestInv.K.«charge_gas»)
    (h_alloc : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "alloc") InitECandidate.Solver.Wave8GuestInv.K.«alloc»)
    (h_memzero : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "memzero") InitECandidate.Solver.Wave8GuestInv.K.«memzero»)
    (h_ripemd160 : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "ripemd160") InitECandidate.Solver.Wave8GuestInv.K.«ripemd160»)
    : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn
      InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "pre_ripemd160")
      InitECandidate.Solver.Wave8GuestInv.K.«pre_ripemd160» := by
  have hl := originalRuntimeCode_lookup_of_guestAst_getElem 826 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_pre_ripemd160) rfl
  dsimp only [extractFn, Guest.Software.guestFn_pre_ripemd160] at hl
  refine ⟨_, _, _, hl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_pre_ripemd160,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply Campaign.Leaves.S05.Structural.weaken'
  · s05_auto
  · unfold InitECandidate.Solver.Wave8GuestInv.K.«pre_ripemd160»
    omega

theorem fb_pre_ecrecover
    (h_charge_gas : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "charge_gas") InitECandidate.Solver.Wave8GuestInv.K.«charge_gas»)
    (h_alloc : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "alloc") InitECandidate.Solver.Wave8GuestInv.K.«alloc»)
    (h_heap_mark : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "heap_mark") InitECandidate.Solver.Wave8GuestInv.K.«heap_mark»)
    (h_buffer_read : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "buffer_read") InitECandidate.Solver.Wave8GuestInv.K.«buffer_read»)
    (h_u256_from_be : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "u256_from_be") InitECandidate.Solver.Wave8GuestInv.K.«u256_from_be»)
    (h_u256_fits_word : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "u256_fits_word") InitECandidate.Solver.Wave8GuestInv.K.«u256_fits_word»)
    (h_heap_release : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "heap_release") InitECandidate.Solver.Wave8GuestInv.K.«heap_release»)
    (h_secp256k1_ecrecover : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "secp256k1_ecrecover") InitECandidate.Solver.Wave8GuestInv.K.«secp256k1_ecrecover»)
    (h_memzero : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "memzero") InitECandidate.Solver.Wave8GuestInv.K.«memzero»)
    : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv
      (ofString "pre_ecrecover") InitECandidate.Solver.Wave8GuestInv.K.«pre_ecrecover» := by
  have hl := originalRuntimeCode_lookup_of_guestAst_getElem 825 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_pre_ecrecover) rfl
  dsimp only [extractFn, Guest.Software.guestFn_pre_ecrecover] at hl
  refine ⟨_, _, _, hl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_pre_ecrecover,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply Campaign.Leaves.S05.Structural.weaken'
  · s05_auto
  · unfold InitECandidate.Solver.Wave8GuestInv.K.«pre_ecrecover»
    simp only [Nat.max_eq_left (Nat.zero_le _)]
    omega

theorem fb_pre_kzg_point_evaluation
    (h_charge_gas : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "charge_gas") InitECandidate.Solver.Wave8GuestInv.K.«charge_gas»)
    (h_alloc : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "alloc") InitECandidate.Solver.Wave8GuestInv.K.«alloc»)
    (h_kzg_point_evaluation_exec : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "kzg_point_evaluation_exec") InitECandidate.Solver.Wave8GuestInv.K.«kzg_point_evaluation_exec»)
    : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv
      (ofString "pre_kzg_point_evaluation") InitECandidate.Solver.Wave8GuestInv.K.«pre_kzg_point_evaluation» := by
  have hl := originalRuntimeCode_lookup_of_guestAst_getElem 821 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_pre_kzg_point_evaluation) rfl
  dsimp only [extractFn, Guest.Software.guestFn_pre_kzg_point_evaluation] at hl
  refine ⟨_, _, _, hl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_pre_kzg_point_evaluation,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply Campaign.Leaves.S05.Structural.weaken'
  · s05_auto
  · unfold InitECandidate.Solver.Wave8GuestInv.K.«pre_kzg_point_evaluation»
    omega

theorem fb_pre_p256verify
    (h_charge_gas : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "charge_gas") InitECandidate.Solver.Wave8GuestInv.K.«charge_gas»)
    (h_alloc : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "alloc") InitECandidate.Solver.Wave8GuestInv.K.«alloc»)
    (h_u256_from_be : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "u256_from_be") InitECandidate.Solver.Wave8GuestInv.K.«u256_from_be»)
    (h_p256_verify : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "p256_verify") InitECandidate.Solver.Wave8GuestInv.K.«p256_verify»)
    (h_memzero : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "memzero") InitECandidate.Solver.Wave8GuestInv.K.«memzero»)
    : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv
      (ofString "pre_p256verify") InitECandidate.Solver.Wave8GuestInv.K.«pre_p256verify» := by
  have hl := originalRuntimeCode_lookup_of_guestAst_getElem 645 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_pre_p256verify) rfl
  dsimp only [extractFn, Guest.Software.guestFn_pre_p256verify] at hl
  refine ⟨_, _, _, hl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_pre_p256verify,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply Campaign.Leaves.S05.Structural.weaken'
  · s05_auto
  · unfold InitECandidate.Solver.Wave8GuestInv.K.«pre_p256verify»
    simp only [Nat.max_eq_left (Nat.zero_le _)]
    omega

theorem fb_frame_start
    (h_frame_prologue : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "frame_prologue") InitECandidate.Solver.Wave8GuestInv.K.«frame_prologue»)
    (h_frame_exception : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "frame_exception") InitECandidate.Solver.Wave8GuestInv.K.«frame_exception»)
    : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv
      (ofString "frame_start") InitECandidate.Solver.Wave8GuestInv.K.«frame_start» := by
  have hl := originalRuntimeCode_lookup_of_guestAst_getElem 581 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_frame_start) rfl
  dsimp only [extractFn, Guest.Software.guestFn_frame_start] at hl
  refine ⟨_, _, _, hl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_frame_start,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply Campaign.Leaves.S05.Structural.weaken'
  · s05_auto
  · unfold InitECandidate.Solver.Wave8GuestInv.K.«frame_start»
    omega

theorem fb_frame_prologue
    (h_u256_is_zero : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "u256_is_zero") InitECandidate.Solver.Wave8GuestInv.K.«u256_is_zero»)
    (h_move_ether : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "move_ether") InitECandidate.Solver.Wave8GuestInv.K.«move_ether»)
    (h_memeq : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "memeq") InitECandidate.Solver.Wave8GuestInv.K.«memeq»)
    (h_emit_transfer_log : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "emit_transfer_log") InitECandidate.Solver.Wave8GuestInv.K.«emit_transfer_log»)
    (h_precompile_index : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "precompile_index") InitECandidate.Solver.Wave8GuestInv.K.«precompile_index»)
    (h_run_precompile : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "run_precompile") InitECandidate.Solver.Wave8GuestInv.K.«run_precompile»)
    : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv
      (ofString "frame_prologue") InitECandidate.Solver.Wave8GuestInv.K.«frame_prologue» := by
  have hl := originalRuntimeCode_lookup_of_guestAst_getElem 580 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_frame_prologue) rfl
  dsimp only [extractFn, Guest.Software.guestFn_frame_prologue] at hl
  refine ⟨_, _, _, hl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_frame_prologue,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply Campaign.Leaves.S05.Structural.weaken'
  · s05_auto
  · unfold InitECandidate.Solver.Wave8GuestInv.K.«frame_prologue»
    simp only [Nat.max_eq_left (Nat.zero_le _)]
    omega

theorem fb_run_precompile
    (h_pre_ecrecover : type_of% InitECandidate.Solver.Wave8GuestInv.fb_pre_ecrecover)
    (h_pre_sha256 : type_of% InitECandidate.Solver.Wave8GuestInv.fb_pre_sha256)
    (h_pre_ripemd160 : type_of% InitECandidate.Solver.Wave8GuestInv.fb_pre_ripemd160)
    (h_pre_identity : type_of% InitECandidate.Solver.Wave8GuestInv.fb_pre_identity)
    (h_pre_alt_bn128_add : type_of% InitECandidate.Solver.Wave8GuestInv.fb_pre_alt_bn128_add)
    (h_pre_alt_bn128_mul : type_of% InitECandidate.Solver.Wave8GuestInv.fb_pre_alt_bn128_mul)
    (h_pre_alt_bn128_pairing_check : type_of% InitECandidate.Solver.Wave8GuestInv.fb_pre_alt_bn128_pairing_check)
    (h_pre_modexp : type_of% InitECandidate.Solver.Wave8GuestInv.fb_pre_modexp)
    (h_pre_blake2f : type_of% InitECandidate.Solver.Wave8GuestInv.fb_pre_blake2f)
    (h_pre_kzg_point_evaluation : type_of% InitECandidate.Solver.Wave8GuestInv.fb_pre_kzg_point_evaluation)
    (h_pre_bls_g1_add : type_of% InitECandidate.Solver.Wave8GuestInv.fb_pre_bls_g1_add)
    (h_pre_bls_g1_msm : type_of% InitECandidate.Solver.Wave8GuestInv.fb_pre_bls_g1_msm)
    (h_pre_bls_g2_add : type_of% InitECandidate.Solver.Wave8GuestInv.fb_pre_bls_g2_add)
    (h_pre_bls_g2_msm : type_of% InitECandidate.Solver.Wave8GuestInv.fb_pre_bls_g2_msm)
    (h_pre_bls_pairing : type_of% InitECandidate.Solver.Wave8GuestInv.fb_pre_bls_pairing)
    (h_pre_bls_map_fp_to_g1 : type_of% InitECandidate.Solver.Wave8GuestInv.fb_pre_bls_map_fp_to_g1)
    (h_pre_bls_map_fp2_to_g2 : type_of% InitECandidate.Solver.Wave8GuestInv.fb_pre_bls_map_fp2_to_g2)
    (h_pre_p256verify : type_of% InitECandidate.Solver.Wave8GuestInv.fb_pre_p256verify)
    : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv
      (ofString "run_precompile") InitECandidate.Solver.Wave8GuestInv.K.«run_precompile» := by
  have hl := originalRuntimeCode_lookup_of_guestAst_getElem 830 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_run_precompile) rfl
  dsimp only [extractFn, Guest.Software.guestFn_run_precompile] at hl
  refine ⟨_, _, _, hl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_run_precompile,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply Campaign.Leaves.S05.Structural.weaken'
  · s05_auto
  · unfold InitECandidate.Solver.Wave8GuestInv.K.«run_precompile»
    simp only [Nat.max_eq_left (Nat.zero_le _)]
    omega

theorem fb_pre_modexp
    (h_buffer_read : type_of% InitECandidate.Solver.Wave8GuestInv.fb_buffer_read)
    (h_u256_from_be : type_of% InitECandidate.Solver.Wave8GuestInv.fb_u256_from_be)
    (h_sat_word : type_of% InitECandidate.Solver.Wave8GuestInv.fb_sat_word)
    (h_min : type_of% InitECandidate.Solver.Wave8GuestInv.fb_min)
    (h_modexp_gas : type_of% InitECandidate.Solver.Wave8GuestInv.fb_modexp_gas)
    (h_charge_gas : type_of% InitECandidate.Solver.Wave8GuestInv.fb_charge_gas)
    (h_alloc : type_of% InitECandidate.Solver.Wave8GuestInv.fb_alloc)
    (h_heap_mark : type_of% InitECandidate.Solver.Wave8GuestInv.fb_heap_mark)
    (h_modexp : type_of% InitECandidate.Solver.Wave8GuestInv.fb_modexp)
    (h_heap_release : type_of% InitECandidate.Solver.Wave8GuestInv.fb_heap_release)
    : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv
      (ofString "pre_modexp") InitECandidate.Solver.Wave8GuestInv.K.«pre_modexp» := by
  have hl := originalRuntimeCode_lookup_of_guestAst_getElem 829 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_pre_modexp) rfl
  dsimp only [extractFn, Guest.Software.guestFn_pre_modexp] at hl
  refine ⟨_, _, _, hl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_pre_modexp,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply Campaign.Leaves.S05.Structural.weaken'
  · s05_auto
  · unfold InitECandidate.Solver.Wave8GuestInv.K.«pre_modexp»
    simp only [Nat.max_eq_left (Nat.zero_le _)]
    omega

theorem fb_pre_bls_g1_add
    (h_charge_gas : type_of% InitECandidate.Solver.Wave8GuestInv.fb_charge_gas)
    (h_alloc : type_of% InitECandidate.Solver.Wave8GuestInv.fb_alloc)
    (h_bls_g1_add_exec : type_of% InitECandidate.Solver.Wave8GuestInv.fb_bls_g1_add_exec)
    : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv
      (ofString "pre_bls_g1_add") InitECandidate.Solver.Wave8GuestInv.K.«pre_bls_g1_add» := by
  have hl := originalRuntimeCode_lookup_of_guestAst_getElem 814 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_pre_bls_g1_add) rfl
  dsimp only [extractFn, Guest.Software.guestFn_pre_bls_g1_add] at hl
  refine ⟨_, _, _, hl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_pre_bls_g1_add,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply Campaign.Leaves.S05.Structural.weaken'
  · s05_auto
  · unfold InitECandidate.Solver.Wave8GuestInv.K.«pre_bls_g1_add»
    omega

theorem fb_pre_bls_g2_add
    (h_charge_gas : type_of% InitECandidate.Solver.Wave8GuestInv.fb_charge_gas)
    (h_alloc : type_of% InitECandidate.Solver.Wave8GuestInv.fb_alloc)
    (h_bls_g2_add_exec : type_of% InitECandidate.Solver.Wave8GuestInv.fb_bls_g2_add_exec)
    : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv
      (ofString "pre_bls_g2_add") InitECandidate.Solver.Wave8GuestInv.K.«pre_bls_g2_add» := by
  have hl := originalRuntimeCode_lookup_of_guestAst_getElem 816 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_pre_bls_g2_add) rfl
  dsimp only [extractFn, Guest.Software.guestFn_pre_bls_g2_add] at hl
  refine ⟨_, _, _, hl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_pre_bls_g2_add,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply Campaign.Leaves.S05.Structural.weaken'
  · s05_auto
  · unfold InitECandidate.Solver.Wave8GuestInv.K.«pre_bls_g2_add»
    omega

theorem fb_pre_bls_map_fp_to_g1
    (h_charge_gas : type_of% InitECandidate.Solver.Wave8GuestInv.fb_charge_gas)
    (h_alloc : type_of% InitECandidate.Solver.Wave8GuestInv.fb_alloc)
    (h_bls_map_fp_to_g1_exec : type_of% InitECandidate.Solver.Wave8GuestInv.fb_bls_map_fp_to_g1_exec)
    : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv
      (ofString "pre_bls_map_fp_to_g1") InitECandidate.Solver.Wave8GuestInv.K.«pre_bls_map_fp_to_g1» := by
  have hl := originalRuntimeCode_lookup_of_guestAst_getElem 819 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_pre_bls_map_fp_to_g1) rfl
  dsimp only [extractFn, Guest.Software.guestFn_pre_bls_map_fp_to_g1] at hl
  refine ⟨_, _, _, hl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_pre_bls_map_fp_to_g1,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply Campaign.Leaves.S05.Structural.weaken'
  · s05_auto
  · unfold InitECandidate.Solver.Wave8GuestInv.K.«pre_bls_map_fp_to_g1»
    omega

theorem fb_pre_bls_map_fp2_to_g2
    (h_charge_gas : type_of% InitECandidate.Solver.Wave8GuestInv.fb_charge_gas)
    (h_alloc : type_of% InitECandidate.Solver.Wave8GuestInv.fb_alloc)
    (h_bls_map_fp2_to_g2_exec : type_of% InitECandidate.Solver.Wave8GuestInv.fb_bls_map_fp2_to_g2_exec)
    : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv
      (ofString "pre_bls_map_fp2_to_g2") InitECandidate.Solver.Wave8GuestInv.K.«pre_bls_map_fp2_to_g2» := by
  have hl := originalRuntimeCode_lookup_of_guestAst_getElem 820 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_pre_bls_map_fp2_to_g2) rfl
  dsimp only [extractFn, Guest.Software.guestFn_pre_bls_map_fp2_to_g2] at hl
  refine ⟨_, _, _, hl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_pre_bls_map_fp2_to_g2,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply Campaign.Leaves.S05.Structural.weaken'
  · s05_auto
  · unfold InitECandidate.Solver.Wave8GuestInv.K.«pre_bls_map_fp2_to_g2»
    omega

theorem fb_pre_bls_g1_msm
    (h_udivmod : type_of% InitECandidate.Solver.Wave8GuestInv.fb_udivmod)
    (h_bls_g1_msm_discount : type_of% InitECandidate.Solver.Wave8GuestInv.fb_bls_g1_msm_discount)
    (h_charge_gas : type_of% InitECandidate.Solver.Wave8GuestInv.fb_charge_gas)
    (h_alloc : type_of% InitECandidate.Solver.Wave8GuestInv.fb_alloc)
    (h_bls_g1_msm_exec : type_of% InitECandidate.Solver.Wave8GuestInv.fb_bls_g1_msm_exec)
    : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv
      (ofString "pre_bls_g1_msm") InitECandidate.Solver.Wave8GuestInv.K.«pre_bls_g1_msm» := by
  have hl := originalRuntimeCode_lookup_of_guestAst_getElem 815 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_pre_bls_g1_msm) rfl
  dsimp only [extractFn, Guest.Software.guestFn_pre_bls_g1_msm] at hl
  refine ⟨_, _, _, hl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_pre_bls_g1_msm,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply Campaign.Leaves.S05.Structural.weaken'
  · s05_auto
  · unfold InitECandidate.Solver.Wave8GuestInv.K.«pre_bls_g1_msm»
    omega

theorem fb_pre_bls_g2_msm
    (h_udivmod : type_of% InitECandidate.Solver.Wave8GuestInv.fb_udivmod)
    (h_bls_g2_msm_discount : type_of% InitECandidate.Solver.Wave8GuestInv.fb_bls_g2_msm_discount)
    (h_charge_gas : type_of% InitECandidate.Solver.Wave8GuestInv.fb_charge_gas)
    (h_alloc : type_of% InitECandidate.Solver.Wave8GuestInv.fb_alloc)
    (h_bls_g2_msm_exec : type_of% InitECandidate.Solver.Wave8GuestInv.fb_bls_g2_msm_exec)
    : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv
      (ofString "pre_bls_g2_msm") InitECandidate.Solver.Wave8GuestInv.K.«pre_bls_g2_msm» := by
  have hl := originalRuntimeCode_lookup_of_guestAst_getElem 817 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_pre_bls_g2_msm) rfl
  dsimp only [extractFn, Guest.Software.guestFn_pre_bls_g2_msm] at hl
  refine ⟨_, _, _, hl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_pre_bls_g2_msm,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply Campaign.Leaves.S05.Structural.weaken'
  · s05_auto
  · unfold InitECandidate.Solver.Wave8GuestInv.K.«pre_bls_g2_msm»
    omega

theorem fb_pre_bls_pairing
    (h_udivmod : type_of% InitECandidate.Solver.Wave8GuestInv.fb_udivmod)
    (h_charge_gas : type_of% InitECandidate.Solver.Wave8GuestInv.fb_charge_gas)
    (h_alloc : type_of% InitECandidate.Solver.Wave8GuestInv.fb_alloc)
    (h_bls_pairing_exec : type_of% InitECandidate.Solver.Wave8GuestInv.fb_bls_pairing_exec)
    : InitECandidate.Solver.Wave8GuestInv.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv
      (ofString "pre_bls_pairing") InitECandidate.Solver.Wave8GuestInv.K.«pre_bls_pairing» := by
  have hl := originalRuntimeCode_lookup_of_guestAst_getElem 818 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_pre_bls_pairing) rfl
  dsimp only [extractFn, Guest.Software.guestFn_pre_bls_pairing] at hl
  refine ⟨_, _, _, hl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_pre_bls_pairing,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply Campaign.Leaves.S05.Structural.weaken'
  · s05_auto
  · unfold InitECandidate.Solver.Wave8GuestInv.K.«pre_bls_pairing»
    omega

theorem fb_pre_blake2f
    (h_charge_gas : InitECandidate.Solver.Wave8Leaves.S14.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "charge_gas") InitECandidate.Solver.Wave8GuestInv.K.«charge_gas»)
    (h_alloc : InitECandidate.Solver.Wave8Leaves.S14.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "alloc") InitECandidate.Solver.Wave8GuestInv.K.«alloc»)
    (h_heap_mark : InitECandidate.Solver.Wave8Leaves.S14.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "heap_mark") InitECandidate.Solver.Wave8GuestInv.K.«heap_mark»)
    (h_blake2b_f : InitECandidate.Solver.Wave8Leaves.S14.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "blake2b_f") InitECandidate.Solver.Wave8GuestInv.K.«blake2b_f»)
    (h_st_le64 : InitECandidate.Solver.Wave8Leaves.S14.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "st_le64") InitECandidate.Solver.Wave8GuestInv.K.«st_le64»)
    (h_heap_release : InitECandidate.Solver.Wave8Leaves.S14.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv (ofString "heap_release") InitECandidate.Solver.Wave8GuestInv.K.«heap_release»)
    : InitECandidate.Solver.Wave8Leaves.S14.TerminatingFunBoundedOn InitECandidate.Solver.Wave8GuestInv.GuestInv
      (ofString "pre_blake2f") InitECandidate.Solver.Wave8GuestInv.K.«pre_blake2f» := by
  have hP : InitECandidate.Solver.Wave8Leaves.S14.MetadataInv
      InitECandidate.Solver.Wave8GuestInv.GuestInv := by
    intro F s t hc hm hs hb h
    exact InitECandidate.Solver.Wave8GuestInv.guestInv_congr hc hm hs hb h
  fb_unfold 827 Guest.Software.guestFn_pre_blake2f
  apply InitECandidate.Solver.Wave8Leaves.S14.TerminatingProgBoundedOn.weaken'
  · fb_auto hP
  · unfold InitECandidate.Solver.Wave8GuestInv.K.«pre_blake2f»
    omega

end Campaign.Leaves.S05
