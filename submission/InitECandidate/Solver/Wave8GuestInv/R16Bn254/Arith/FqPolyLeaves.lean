import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ScaledMemoryWalk
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.CounterMore
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.Composed
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqMulSource

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators

private theorem straight_prefix {p tail : ProgHOL 64} {B : Nat}
    (hp : extStraightLine p = true) (ht : TerminatingProgBounded tail B) :
    TerminatingProgBounded (.seq p tail) B := by
  intro F s hc
  simpa only [Nat.zero_add] using TerminatingProgBounded.seq (TerminatingProgBounded.straight p hp) ht s hc

private theorem montAccProducts_bound (products : List (ExpHOL 64 × ExpHOL 64))
    {tail : ProgHOL 64} {B : Nat} (ht : TerminatingProgBounded tail B) :
    TerminatingProgBounded (montAccProducts products tail) B := by
  induction products with
  | nil => exact ht
  | cons ab rest ih =>
    unfold montAccProducts List.foldr montAccProduct
    exact straight_prefix rfl (straight_prefix rfl (straight_prefix rfl ih))

private theorem montLowerColumn_bound (dest : String) (products : List (ExpHOL 64 × ExpHOL 64))
    {tail : ProgHOL 64} {B : Nat} (ht : TerminatingProgBounded tail B) :
    TerminatingProgBounded (montLowerColumn dest products tail) B :=
  montAccProducts_bound products
    (straight_prefix rfl (straight_prefix rfl (straight_prefix rfl (straight_prefix rfl
      (straight_prefix rfl (straight_prefix rfl (straight_prefix rfl (straight_prefix rfl ht))))))))

private theorem montUpperColumn_bound (dest : String) (products : List (ExpHOL 64 × ExpHOL 64))
    {tail : ProgHOL 64} {B : Nat} (ht : TerminatingProgBounded tail B) :
    TerminatingProgBounded (montUpperColumn dest products tail) B :=
  montAccProducts_bound products
    (straight_prefix rfl (straight_prefix rfl (straight_prefix rfl
      (straight_prefix rfl (straight_prefix rfl ht)))))

private theorem fqMulInits_bound (inits : List (String × ExpHOL 64))
    {tail : ProgHOL 64} {B : Nat} (ht : TerminatingProgBounded tail B) :
    TerminatingProgBounded (inits.foldr (fun ne rest => .dec (ofString ne.1) .one ne.2 rest) tail) B := by
  induction inits with
  | nil => exact ht
  | cons ne rest ih => exact TerminatingProgBounded.dec _ _ _ ih

theorem ub_fq_mul : TerminatingFunBounded (ofString "fq_mul") K.«fq_mul» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 652
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_fq_mul) rfl, ?_⟩
  change TerminatingProgBounded (arithSourceBody Guest.Software.guestFn_fq_mul) K.«fq_mul»
  rw [fqMul_source_eq]
  have hfin : TerminatingProgBounded fqMulFinish K.«fq_mul» :=
    TerminatingProgBounded.dec _ _ _
      (TerminatingProgBounded.decCall ub_u256_lt _ _ _
        (TerminatingProgBounded.seq
          (TerminatingProgBounded.ite
            (TerminatingProgBounded.tailCall ub_u256_sub _)
            (TerminatingProgBounded.straight _ rfl))
          (TerminatingProgBounded.straight _ rfl)))
  unfold fqMulProgram fqMulColumn0 fqMulColumn1 fqMulColumn2 fqMulColumn3 fqMulColumn4
    fqMulColumn5 fqMulColumn6 fqMulColumn7 fqMulColumn8 fqMulColumn9 fqMulColumn10
    fqMulColumn11 fqMulColumn12 fqMulColumn13 fqMulColumn14
  intro F state hc
  exact fqMulInits_bound fqMulInitializers
    (montLowerColumn_bound _ _ (montLowerColumn_bound _ _ (montLowerColumn_bound _ _
      (montLowerColumn_bound _ _ (montLowerColumn_bound _ _ (montLowerColumn_bound _ _
        (montLowerColumn_bound _ _ (montLowerColumn_bound _ _ (montUpperColumn_bound _ _
          (montUpperColumn_bound _ _ (montUpperColumn_bound _ _ (montUpperColumn_bound _ _
            (montUpperColumn_bound _ _ (montUpperColumn_bound _ _
              (montUpperColumn_bound _ _ hfin))))))))))))))) state hc

theorem fb_fq_mul : TerminatingFunBoundedOn GuestInv (ofString "fq_mul") K.«fq_mul» :=
  TerminatingFunBoundedOn.of_unconditional ub_fq_mul

theorem ub_fq_add : TerminatingFunBounded (ofString "fq_add") K.«fq_add» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 649
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_fq_add) rfl, ?_⟩
  exact (TerminatingProgBounded.decCall ub_u256_add _ _ _
    (TerminatingProgBounded.decCall ub_u256_lt _ _ _
      (TerminatingProgBounded.seq
        (TerminatingProgBounded.ite (TerminatingProgBounded.tailCall ub_u256_sub _)
          (TerminatingProgBounded.straight _ rfl))
        (TerminatingProgBounded.straight _ rfl))))

theorem fb_fq_add : TerminatingFunBoundedOn GuestInv (ofString "fq_add") K.«fq_add» :=
  TerminatingFunBoundedOn.of_unconditional ub_fq_add

theorem ub_fq_sub : TerminatingFunBounded (ofString "fq_sub") K.«fq_sub» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 650
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_fq_sub) rfl, ?_⟩
  exact (TerminatingProgBounded.decCall ub_u256_lt _ _ _
    (TerminatingProgBounded.decCall ub_u256_sub _ _ _
      (TerminatingProgBounded.seq
        (TerminatingProgBounded.ite (TerminatingProgBounded.call ub_u256_add _ _)
          (TerminatingProgBounded.straight _ rfl))
        (TerminatingProgBounded.straight _ rfl))))

theorem fb_fq_sub : TerminatingFunBoundedOn GuestInv (ofString "fq_sub") K.«fq_sub» :=
  TerminatingFunBoundedOn.of_unconditional ub_fq_sub

theorem ub_fq_neg : TerminatingFunBounded (ofString "fq_neg") K.«fq_neg» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 651
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_fq_neg) rfl, ?_⟩
  exact (TerminatingProgBounded.decCall ub_u256_is_zero _ _ _
    (TerminatingProgBounded.seq (TerminatingProgBounded.straight _ rfl)
      (TerminatingProgBounded.tailCall ub_u256_sub _)))

theorem fb_fq_neg : TerminatingFunBoundedOn GuestInv (ofString "fq_neg") K.«fq_neg» :=
  TerminatingFunBoundedOn.of_unconditional ub_fq_neg

theorem ub_is_zero_bytes : TerminatingFunBounded (ofString "is_zero_bytes") K.«is_zero_bytes» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 19
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_is_zero_bytes) rfl, ?_⟩
  exact (TerminatingProgBounded.dec _ _ _
    (TerminatingProgBounded.seq
      (while_up_unsigned_one _ _ (TerminatingProgBounded.straight _ rfl)
        (CounterAdd.seq _ _ _ (by decide) (by decide) (CounterAdd.assign _ _)))
      (TerminatingProgBounded.straight _ rfl)))

theorem fb_is_zero_bytes : TerminatingFunBoundedOn GuestInv (ofString "is_zero_bytes") K.«is_zero_bytes» :=
  TerminatingFunBoundedOn.of_unconditional ub_is_zero_bytes

theorem ub_fq_poly_deg : TerminatingFunBounded (ofString "fq_poly_deg") K.«fq_poly_deg» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 680
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_fq_poly_deg) rfl, ?_⟩
  exact (TerminatingProgBounded.dec _ _ _
    (TerminatingProgBounded.seq
      (while_down_first_unsigned _
        (TerminatingProgBounded.decCall ub_is_zero_bytes _ _ _ (TerminatingProgBounded.straight _ rfl))
        (by decide))
      (TerminatingProgBounded.straight _ rfl)))

theorem fb_fq_poly_deg : TerminatingFunBoundedOn GuestInv (ofString "fq_poly_deg") K.«fq_poly_deg» :=
  TerminatingFunBoundedOn.of_unconditional ub_fq_poly_deg

theorem fb_fq_poly_submul : TerminatingFunBoundedOn GuestInv (ofString "fq_poly_submul") K.«fq_poly_submul» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 681
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_fq_poly_submul) rfl, ?_⟩
  exact (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
    (TerminatingProgBoundedOn.seq_guestInv
      (while_scaled_memory_walk (ofString "b") (ofString "i") _
        (TerminatingProgBounded.dec _ _ _
          (TerminatingProgBounded.decCall ub_fq_mul _ _ _
            (TerminatingProgBounded.dec _ _ _
              (TerminatingProgBounded.seq
                (TerminatingProgBounded.call ub_fq_sub _ _)
                (TerminatingProgBounded.straight _ rfl)))))
        (DomainTouch.dec_read _ _ _ _ _ (DomainRead.load4 _))
        (CounterAdd.dec _ _ _ _ _ (by decide)
          (CounterAdd.decCall _ _ _ _ _ _ (by decide)
            (CounterAdd.dec _ _ _ _ _ (by decide)
              (CounterAdd.seq _ _ _ (by decide) (by decide)
                (CounterAdd.seq _ _ _ (by decide) (by decide) (CounterAdd.assign _ _))))))
        (by decide))
      (fun s hc _ => TerminatingProgBounded.straight _ rfl s hc)))

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
