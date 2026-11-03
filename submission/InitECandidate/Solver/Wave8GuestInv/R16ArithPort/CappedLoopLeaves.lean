import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2
import InitECandidate.Solver.Wave8GuestInv.R16Shards.BlsPrecompiles.BlsG2
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.ModinvLeaf
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.P256Leaves

/-! R11-tightened capped-counter leaf proofs for:
`fb_fp_pow`, `fb_fp12_pow_absx`, `fb_pair_miller_loop`, `fb_fq12_reduce`, `fb_fq12_mul`,
`fb_fq12_sqr`, and `fb_ecp_mul`. -/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R16ArithPort.Capped

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

/-! ### 0. Self-contained `fq_mul` / `fq_neg` / `fq2_mul` / `fp6` / `fp12` / `ecp` callees -/

private def fqModulus : Arith.Limbs256 :=
  ⟨4332616871279656263, 10917124144477883021, 13281191951274694749, 3486998266802970665⟩

private def limbs256ConstExpr (a : Arith.Limbs256) : ExpHOL 64 :=
  .rstruct [.const a.l0, .const a.l1, .const a.l2, .const a.l3]

private def montVar (name : String) : ExpHOL 64 := .var .local (ofString name)
private def montLoExpr (e : ExpHOL 64) : ExpHOL 64 := .op .and [e, .const 4294967295]
private def montHiExpr (e : ExpHOL 64) : ExpHOL 64 := .shift .lsr e (.const 32)

private def montAccProduct (a b : ExpHOL 64) (tail : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local (ofString "pr") (.panop .mul [a, b]))
    (.seq (.assign .local (ofString "L") (.op .add [montVar "L", montLoExpr (montVar "pr")]))
      (.seq (.assign .local (ofString "H") (.op .add [montVar "H", montHiExpr (montVar "pr")])) tail))

private def montAccProducts (products : List (ExpHOL 64 × ExpHOL 64)) (tail : ProgHOL 64) : ProgHOL 64 :=
  products.foldr (fun ab rest => montAccProduct ab.1 ab.2 rest) tail

private def montLowerColumn (dest : String) (products : List (ExpHOL 64 × ExpHOL 64)) (tail : ProgHOL 64) : ProgHOL 64 :=
  montAccProducts products
    (.seq (.assign .local (ofString "col") (.op .add [montVar "L", montVar "c"]))
      (.seq (.assign .local (ofString "dg") (montLoExpr (montVar "col")))
        (.seq (.assign .local (ofString dest) (montLoExpr (.panop .mul [montVar "dg", .const 3834012553])))
          (.seq (.assign .local (ofString "pr") (.panop .mul [montVar dest, .const 3632069959]))
            (.seq (.assign .local (ofString "col2") (.op .add [montVar "dg", montLoExpr (montVar "pr")]))
              (.seq (.assign .local (ofString "c") (.op .add [montHiExpr (montVar "col"), montVar "H",
                montHiExpr (montVar "col2"), montHiExpr (montVar "pr")]))
                (.seq (.assign .local (ofString "L") (.const 0))
                  (.seq (.assign .local (ofString "H") (.const 0)) tail))))))))

private def montUpperColumn (dest : String) (products : List (ExpHOL 64 × ExpHOL 64)) (tail : ProgHOL 64) : ProgHOL 64 :=
  montAccProducts products
    (.seq (.assign .local (ofString "col") (.op .add [montVar "L", montVar "c"]))
      (.seq (.assign .local (ofString dest) (montLoExpr (montVar "col")))
        (.seq (.assign .local (ofString "c") (.op .add [montHiExpr (montVar "col"), montVar "H"]))
          (.seq (.assign .local (ofString "L") (.const 0))
            (.seq (.assign .local (ofString "H") (.const 0)) tail)))))

private def fqMulFinish : ProgHOL 64 :=
  .dec (ofString "r") Arith.arithU256Shape
    (.rstruct [
      .op .or [montVar "u0", .shift .lsl (montVar "u1") (.const 32)],
      .op .or [montVar "u2", .shift .lsl (montVar "u3") (.const 32)],
      .op .or [montVar "u4", .shift .lsl (montVar "u5") (.const 32)],
      .op .or [montVar "u6", .shift .lsl (montVar "c") (.const 32)]])
    (.decCall (ofString "lt") .one (ofString "u256_lt") [montVar "r", limbs256ConstExpr fqModulus]
      (.seq (.ite (.cmp .equal (montVar "lt") (.const 0))
        (.call none (ofString "u256_sub") [montVar "r", limbs256ConstExpr fqModulus]) .skip)
        (.return (montVar "r"))))

private def fqMulColumn14 : ProgHOL 64 :=
  montUpperColumn "u6"
    [(montVar "a7", montVar "b7"),
     (montVar "m7", .const 811880050)] fqMulFinish

private def fqMulColumn13 : ProgHOL 64 :=
  montUpperColumn "u5"
    [(montVar "a6", montVar "b7"),
     (montVar "a7", montVar "b6"),
     (montVar "m6", .const 811880050),
     (montVar "m7", .const 3778125865)] fqMulColumn14

private def fqMulColumn12 : ProgHOL 64 :=
  montUpperColumn "u4"
    [(montVar "a5", montVar "b7"),
     (montVar "a6", montVar "b6"),
     (montVar "a7", montVar "b5"),
     (montVar "m5", .const 811880050),
     (montVar "m6", .const 3778125865),
     (montVar "m7", .const 3092268470)] fqMulColumn13

private def fqMulColumn11 : ProgHOL 64 :=
  montUpperColumn "u3"
    [(montVar "a4", montVar "b7"),
     (montVar "a5", montVar "b6"),
     (montVar "a6", montVar "b5"),
     (montVar "a7", montVar "b4"),
     (montVar "m4", .const 811880050),
     (montVar "m5", .const 3778125865),
     (montVar "m6", .const 3092268470),
     (montVar "m7", .const 2172737629)] fqMulColumn12

private def fqMulColumn10 : ProgHOL 64 :=
  montUpperColumn "u2"
    [(montVar "a3", montVar "b7"),
     (montVar "a4", montVar "b6"),
     (montVar "a5", montVar "b5"),
     (montVar "a6", montVar "b4"),
     (montVar "a7", montVar "b3"),
     (montVar "m3", .const 811880050),
     (montVar "m4", .const 3778125865),
     (montVar "m5", .const 3092268470),
     (montVar "m6", .const 2172737629),
     (montVar "m7", .const 2541841041)] fqMulColumn11

private def fqMulColumn9 : ProgHOL 64 :=
  montUpperColumn "u1"
    [(montVar "a2", montVar "b7"),
     (montVar "a3", montVar "b6"),
     (montVar "a4", montVar "b5"),
     (montVar "a5", montVar "b4"),
     (montVar "a6", montVar "b3"),
     (montVar "a7", montVar "b2"),
     (montVar "m2", .const 811880050),
     (montVar "m3", .const 3778125865),
     (montVar "m4", .const 3092268470),
     (montVar "m5", .const 2172737629),
     (montVar "m6", .const 2541841041),
     (montVar "m7", .const 1752287885)] fqMulColumn10

private def fqMulColumn8 : ProgHOL 64 :=
  montUpperColumn "u0"
    [(montVar "a1", montVar "b7"),
     (montVar "a2", montVar "b6"),
     (montVar "a3", montVar "b5"),
     (montVar "a4", montVar "b4"),
     (montVar "a5", montVar "b3"),
     (montVar "a6", montVar "b2"),
     (montVar "a7", montVar "b1"),
     (montVar "m1", .const 811880050),
     (montVar "m2", .const 3778125865),
     (montVar "m3", .const 3092268470),
     (montVar "m4", .const 2172737629),
     (montVar "m5", .const 2541841041),
     (montVar "m6", .const 1752287885),
     (montVar "m7", .const 1008765974)] fqMulColumn9

private def fqMulColumn7 : ProgHOL 64 :=
  montLowerColumn "m7"
    [(montVar "a0", montVar "b7"),
     (montVar "a1", montVar "b6"),
     (montVar "a2", montVar "b5"),
     (montVar "a3", montVar "b4"),
     (montVar "a4", montVar "b3"),
     (montVar "a5", montVar "b2"),
     (montVar "a6", montVar "b1"),
     (montVar "a7", montVar "b0"),
     (montVar "m0", .const 811880050),
     (montVar "m1", .const 3778125865),
     (montVar "m2", .const 3092268470),
     (montVar "m3", .const 2172737629),
     (montVar "m4", .const 2541841041),
     (montVar "m5", .const 1752287885),
     (montVar "m6", .const 1008765974)] fqMulColumn8

private def fqMulColumn6 : ProgHOL 64 :=
  montLowerColumn "m6"
    [(montVar "a0", montVar "b6"),
     (montVar "a1", montVar "b5"),
     (montVar "a2", montVar "b4"),
     (montVar "a3", montVar "b3"),
     (montVar "a4", montVar "b2"),
     (montVar "a5", montVar "b1"),
     (montVar "a6", montVar "b0"),
     (montVar "m0", .const 3778125865),
     (montVar "m1", .const 3092268470),
     (montVar "m2", .const 2172737629),
     (montVar "m3", .const 2541841041),
     (montVar "m4", .const 1752287885),
     (montVar "m5", .const 1008765974)] fqMulColumn7

private def fqMulColumn5 : ProgHOL 64 :=
  montLowerColumn "m5"
    [(montVar "a0", montVar "b5"),
     (montVar "a1", montVar "b4"),
     (montVar "a2", montVar "b3"),
     (montVar "a3", montVar "b2"),
     (montVar "a4", montVar "b1"),
     (montVar "a5", montVar "b0"),
     (montVar "m0", .const 3092268470),
     (montVar "m1", .const 2172737629),
     (montVar "m2", .const 2541841041),
     (montVar "m3", .const 1752287885),
     (montVar "m4", .const 1008765974)] fqMulColumn6

private def fqMulColumn4 : ProgHOL 64 :=
  montLowerColumn "m4"
    [(montVar "a0", montVar "b4"),
     (montVar "a1", montVar "b3"),
     (montVar "a2", montVar "b2"),
     (montVar "a3", montVar "b1"),
     (montVar "a4", montVar "b0"),
     (montVar "m0", .const 2172737629),
     (montVar "m1", .const 2541841041),
     (montVar "m2", .const 1752287885),
     (montVar "m3", .const 1008765974)] fqMulColumn5

private def fqMulColumn3 : ProgHOL 64 :=
  montLowerColumn "m3"
    [(montVar "a0", montVar "b3"),
     (montVar "a1", montVar "b2"),
     (montVar "a2", montVar "b1"),
     (montVar "a3", montVar "b0"),
     (montVar "m0", .const 2541841041),
     (montVar "m1", .const 1752287885),
     (montVar "m2", .const 1008765974)] fqMulColumn4

private def fqMulColumn2 : ProgHOL 64 :=
  montLowerColumn "m2"
    [(montVar "a0", montVar "b2"),
     (montVar "a1", montVar "b1"),
     (montVar "a2", montVar "b0"),
     (montVar "m0", .const 1752287885),
     (montVar "m1", .const 1008765974)] fqMulColumn3

private def fqMulColumn1 : ProgHOL 64 :=
  montLowerColumn "m1"
    [(montVar "a0", montVar "b1"),
     (montVar "a1", montVar "b0"),
     (montVar "m0", .const 1008765974)] fqMulColumn2

private def fqMulColumn0 : ProgHOL 64 :=
  montLowerColumn "m0"
    [(montVar "a0", montVar "b0")] fqMulColumn1

private def fqMulInitializers : List (String × ExpHOL 64) :=
  [("a0", montLoExpr (.rfield 0 (montVar "a"))),
   ("a1", montHiExpr (.rfield 0 (montVar "a"))),
   ("a2", montLoExpr (.rfield 1 (montVar "a"))),
   ("a3", montHiExpr (.rfield 1 (montVar "a"))),
   ("a4", montLoExpr (.rfield 2 (montVar "a"))),
   ("a5", montHiExpr (.rfield 2 (montVar "a"))),
   ("a6", montLoExpr (.rfield 3 (montVar "a"))),
   ("a7", montHiExpr (.rfield 3 (montVar "a"))),
   ("b0", montLoExpr (.rfield 0 (montVar "b"))),
   ("b1", montHiExpr (.rfield 0 (montVar "b"))),
   ("b2", montLoExpr (.rfield 1 (montVar "b"))),
   ("b3", montHiExpr (.rfield 1 (montVar "b"))),
   ("b4", montLoExpr (.rfield 2 (montVar "b"))),
   ("b5", montHiExpr (.rfield 2 (montVar "b"))),
   ("b6", montLoExpr (.rfield 3 (montVar "b"))),
   ("b7", montHiExpr (.rfield 3 (montVar "b"))),
   ("pr", .const 0),
   ("L", .const 0),
   ("H", .const 0),
   ("c", .const 0),
   ("col", .const 0),
   ("col2", .const 0),
   ("dg", .const 0),
   ("m0", .const 0),
   ("m1", .const 0),
   ("m2", .const 0),
   ("m3", .const 0),
   ("m4", .const 0),
   ("m5", .const 0),
   ("m6", .const 0),
   ("m7", .const 0),
   ("u0", .const 0),
   ("u1", .const 0),
   ("u2", .const 0),
   ("u3", .const 0),
   ("u4", .const 0),
   ("u5", .const 0),
   ("u6", .const 0)]

private def fqMulProgram : ProgHOL 64 :=
  fqMulInitializers.foldr (fun ne tail => .dec (ofString ne.1) .one ne.2 tail) fqMulColumn0

private theorem fqMul_source_eq : Arith.arithSourceBody Guest.Software.guestFn_fq_mul = fqMulProgram := rfl

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
  change TerminatingProgBounded (Arith.arithSourceBody Guest.Software.guestFn_fq_mul) K.«fq_mul»
  rw [fqMul_source_eq]
  have hfin : TerminatingProgBounded fqMulFinish K.«fq_mul» :=
    TerminatingProgBounded.dec _ _ _
      (InitECandidate.Solver.PanTerminatingCombinators.TerminatingProgBounded.decCall Arith.ub_u256_lt _ _ _
        (TerminatingProgBounded.seq
          (TerminatingProgBounded.ite
            (InitECandidate.Solver.PanTerminatingCombinators.TerminatingProgBounded.tailCall Arith.ub_u256_sub _)
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

theorem fb_fq_add : TerminatingFunBoundedOn GuestInv (ofString "fq_add") K.«fq_add» :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2.fb_fq_add

theorem fb_fq_sub : TerminatingFunBoundedOn GuestInv (ofString "fq_sub") K.«fq_sub» :=
  InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2.fb_fq_sub

theorem fb_fq_neg : TerminatingFunBoundedOn GuestInv (ofString "fq_neg") K.«fq_neg» := by
  have _ := fb_u256_is_zero
  have _ := InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2.fb_u256_sub
  bls_prove 651 Guest.Software.guestFn_fq_neg K.«fq_neg»

theorem fb_fq2_mul : TerminatingFunBoundedOn GuestInv (ofString "fq2_mul") K.«fq2_mul» := by
  have _ := fb_fq_mul
  have _ := fb_fq_sub
  have _ := fb_fq_add
  bls_prove 657 Guest.Software.guestFn_fq2_mul K.«fq2_mul»

theorem fb_fe_is_zero :
    TerminatingFunBoundedOn GuestInv (ofString "fe_is_zero") K.«fe_is_zero» := by
  have _ := InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB1.fb_is_zero_bytes
  bls_prove 667 Guest.Software.guestFn_fe_is_zero K.«fe_is_zero»

theorem fb_fp6_set_one :
    TerminatingFunBoundedOn GuestInv (ofString "fp6_set_one") K.«fp6_set_one» := by
  have _ := fb_fp2_set_one
  have _ := fb_fp2_set_zero
  bls_prove 740 Guest.Software.guestFn_fp6_set_one K.«fp6_set_one»

theorem fb_fp_mul : TerminatingFunBoundedOn GuestInv (ofString "fp_mul") K.«fp_mul» :=
  Arith.fb_fp_mul

theorem fb_fp_sqr : TerminatingFunBoundedOn GuestInv (ofString "fp_sqr") K.«fp_sqr» :=
  Arith.fb_fp_sqr

theorem fb_u256_bit : TerminatingFunBoundedOn GuestInv (ofString "u256_bit") K.«u256_bit» :=
  Arith.fb_u256_bit

/-! ### 0. Lightweight FP6/FP12/Pair/ECP loop-free callees (decoupled from `FG_30`) -/

theorem fb_fp6_copy :
    TerminatingFunBoundedOn GuestInv (ofString "fp6_copy") K.«fp6_copy» := by
  have _ := fb_memcpy
  bls_prove 738 Guest.Software.guestFn_fp6_copy K.«fp6_copy»

theorem fb_fp6_set_zero :
    TerminatingFunBoundedOn GuestInv (ofString "fp6_set_zero") K.«fp6_set_zero» := by
  have _ := fb_memzero
  bls_prove 739 Guest.Software.guestFn_fp6_set_zero K.«fp6_set_zero»

theorem fb_fp6_add :
    TerminatingFunBoundedOn GuestInv (ofString "fp6_add") K.«fp6_add» := by
  have _ := fb_fp2_add
  bls_prove 741 Guest.Software.guestFn_fp6_add K.«fp6_add»

theorem fb_fp6_sub :
    TerminatingFunBoundedOn GuestInv (ofString "fp6_sub") K.«fp6_sub» := by
  have _ := fb_fp2_sub
  bls_prove 742 Guest.Software.guestFn_fp6_sub K.«fp6_sub»

theorem fb_fp6_neg :
    TerminatingFunBoundedOn GuestInv (ofString "fp6_neg") K.«fp6_neg» := by
  have _ := fb_fp2_neg
  bls_prove 743 Guest.Software.guestFn_fp6_neg K.«fp6_neg»

theorem fb_fp6_mul :
    TerminatingFunBoundedOn GuestInv (ofString "fp6_mul") K.«fp6_mul» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fp2_mul
  have _ := fb_fp2_add
  have _ := fb_fp2_mul_xi
  have _ := fb_heap_release
  bls_prove 744 Guest.Software.guestFn_fp6_mul K.«fp6_mul»

theorem fb_fp6_mul_v :
    TerminatingFunBoundedOn GuestInv (ofString "fp6_mul_v") K.«fp6_mul_v» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fp2_mul_xi
  have _ := fb_fp2_copy
  have _ := fb_heap_release
  bls_prove 745 Guest.Software.guestFn_fp6_mul_v K.«fp6_mul_v»

theorem fb_fp12_copy :
    TerminatingFunBoundedOn GuestInv (ofString "fp12_copy") K.«fp12_copy» := by
  have _ := fb_memcpy
  bls_prove 747 Guest.Software.guestFn_fp12_copy K.«fp12_copy»

theorem fb_fp12_set_one :
    TerminatingFunBoundedOn GuestInv (ofString "fp12_set_one") K.«fp12_set_one» := by
  have _ := fb_fp6_set_one
  have _ := fb_fp6_set_zero
  bls_prove 748 Guest.Software.guestFn_fp12_set_one K.«fp12_set_one»

theorem fb_fp12_mul :
    TerminatingFunBoundedOn GuestInv (ofString "fp12_mul") K.«fp12_mul» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fp6_mul
  have _ := fb_fp6_add
  have _ := fb_fp6_sub
  have _ := fb_fp6_mul_v
  have _ := fb_heap_release
  bls_prove 750 Guest.Software.guestFn_fp12_mul K.«fp12_mul»

theorem fb_fp12_conj :
    TerminatingFunBoundedOn GuestInv (ofString "fp12_conj") K.«fp12_conj» := by
  have _ := fb_fp6_copy
  have _ := fb_fp6_neg
  bls_prove 752 Guest.Software.guestFn_fp12_conj K.«fp12_conj»

theorem fb_pair_doubling_step :
    TerminatingFunBoundedOn GuestInv (ofString "pair_doubling_step") K.«pair_doubling_step» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fp2_sqr
  have _ := fb_fp2_add
  have _ := fb_fp2_sub
  have _ := fb_fp2_mul
  have _ := fb_fp2_copy
  have _ := fb_fp2_neg
  have _ := fb_heap_release
  bls_prove 782 Guest.Software.guestFn_pair_doubling_step K.«pair_doubling_step»

theorem fb_pair_addition_step :
    TerminatingFunBoundedOn GuestInv (ofString "pair_addition_step") K.«pair_addition_step» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_fp2_sqr
  have _ := fb_fp2_mul
  have _ := fb_fp2_add
  have _ := fb_fp2_sub
  have _ := fb_fp2_copy
  have _ := fb_fp2_neg
  have _ := fb_heap_release
  bls_prove 783 Guest.Software.guestFn_pair_addition_step K.«pair_addition_step»

theorem fb_pair_ell :
    TerminatingFunBoundedOn GuestInv (ofString "pair_ell") K.«pair_ell» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_memzero
  have _ := fb_fp2_copy
  have _ := fb_fp2_scale
  have _ := fb_fp12_mul
  have _ := fb_heap_release
  bls_prove 784 Guest.Software.guestFn_pair_ell K.«pair_ell»

theorem fb_fe_set_zero :
    TerminatingFunBoundedOn GuestInv (ofString "fe_set_zero") K.«fe_set_zero» := by
  have _ := fb_memzero
  bls_prove 669 Guest.Software.guestFn_fe_set_zero K.«fe_set_zero»

theorem fb_fe_set_one :
    TerminatingFunBoundedOn GuestInv (ofString "fe_set_one") K.«fe_set_one» := by
  have _ := fb_memzero
  bls_prove 670 Guest.Software.guestFn_fe_set_one K.«fe_set_one»

theorem fb_ecp_set_inf :
    TerminatingFunBoundedOn GuestInv (ofString "ecp_set_inf") K.«ecp_set_inf» := by
  have _ := fb_fe_set_one
  have _ := fb_fe_set_zero
  bls_prove 671 Guest.Software.guestFn_ecp_set_inf K.«ecp_set_inf»

theorem fb_fe_eq_of
    (h_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») :
    TerminatingFunBoundedOn GuestInv (ofString "fe_eq") K.«fe_eq» := by
  have _ := h_memeq
  bls_prove 668 Guest.Software.guestFn_fe_eq K.«fe_eq»

theorem fb_fe_mul_of
    (h_fq12_mul : TerminatingFunBoundedOn GuestInv (ofString "fq12_mul") K.«fq12_mul») :
    TerminatingFunBoundedOn GuestInv (ofString "fe_mul") K.«fe_mul» := by
  have _ := fb_fq_mul
  have _ := fb_fq2_mul
  have _ := h_fq12_mul
  bls_prove 661 Guest.Software.guestFn_fe_mul K.«fe_mul»

theorem fb_fe_sqr_of
    (h_fe_mul : TerminatingFunBoundedOn GuestInv (ofString "fe_mul") K.«fe_mul»)
    (h_fq12_sqr : TerminatingFunBoundedOn GuestInv (ofString "fq12_sqr") K.«fq12_sqr») :
    TerminatingFunBoundedOn GuestInv (ofString "fe_sqr") K.«fe_sqr» := by
  have _ := h_fq12_sqr
  have _ := h_fe_mul
  bls_prove 662 Guest.Software.guestFn_fe_sqr K.«fe_sqr»

theorem fb_ecp_double_of
    (h_fe_mul : TerminatingFunBoundedOn GuestInv (ofString "fe_mul") K.«fe_mul»)
    (h_fe_mul_small : TerminatingFunBoundedOn GuestInv (ofString "fe_mul_small") K.«fe_mul_small»)
    (h_fe_sqr : TerminatingFunBoundedOn GuestInv (ofString "fe_sqr") K.«fe_sqr»)
    (h_fe_sub : TerminatingFunBoundedOn GuestInv (ofString "fe_sub") K.«fe_sub») :
    TerminatingFunBoundedOn GuestInv (ofString "ecp_double") K.«ecp_double» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_memcpy
  have _ := fb_heap_release
  have _ := h_fe_sqr
  have _ := h_fe_mul_small
  have _ := h_fe_mul
  have _ := h_fe_sub
  bls_prove 673 Guest.Software.guestFn_ecp_double K.«ecp_double»

theorem fb_ecp_add_of
    (h_ecp_double : TerminatingFunBoundedOn GuestInv (ofString "ecp_double") K.«ecp_double»)
    (h_fe_eq : TerminatingFunBoundedOn GuestInv (ofString "fe_eq") K.«fe_eq»)
    (h_fe_mul : TerminatingFunBoundedOn GuestInv (ofString "fe_mul") K.«fe_mul»)
    (h_fe_mul_small : TerminatingFunBoundedOn GuestInv (ofString "fe_mul_small") K.«fe_mul_small»)
    (h_fe_sqr : TerminatingFunBoundedOn GuestInv (ofString "fe_sqr") K.«fe_sqr»)
    (h_fe_sub : TerminatingFunBoundedOn GuestInv (ofString "fe_sub") K.«fe_sub») :
    TerminatingFunBoundedOn GuestInv (ofString "ecp_add") K.«ecp_add» := by
  have _ := fb_heap_mark
  have _ := fb_alloc
  have _ := fb_memcpy
  have _ := fb_heap_release
  have _ := fb_fe_is_zero
  have _ := fb_ecp_set_inf
  have _ := h_fe_mul
  have _ := h_fe_eq
  have _ := h_ecp_double
  have _ := h_fe_sub
  have _ := h_fe_sqr
  have _ := h_fe_mul_small
  bls_prove 674 Guest.Software.guestFn_ecp_add K.«ecp_add»

/-- 1. `fb_fp_pow` (`i` initialized to `256 = 2^8`, decremented first) -/
theorem fb_fp_pow : TerminatingFunBoundedOn GuestInv (ofString "fp_pow") K.«fp_pow» := by
  have _ := fb_fp_sqr
  have _ := fb_u256_bit
  have _ := fb_fp_mul
  bls_unfold 155 Guest.Software.guestFn_fp_pow
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply dec_guestInv
    apply dec_const_cap_guestInv "i" (BitVec.ofNat 64 256)
    exact seq_to_guestInv (fun _ h => h.1)
      (while_down_first_capped_on .lower (Or.inr rfl) "i"
        (TerminatingProgBoundedOn.seq_guestInv
          (TerminatingProgBoundedOn.ite_on (call_guestInv' fb_fp_sqr) (straightOn _ rfl))
          (decCall_guestInv' fb_u256_bit
            (TerminatingProgBoundedOn.ite_on
              (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp_mul) (straightOn _ rfl))
              (straightOn _ rfl))))
        rfl)
      (straightOn _ rfl)
  · rw [show (BitVec.ofNat 64 256).toNat = 2 ^ 8 by decide]
    bls_arith K.«fp_pow»

/-- 2. `fb_fp12_pow_absx` (`i` initialized to `64`, decremented first) -/
theorem fb_fp12_pow_absx :
    TerminatingFunBoundedOn GuestInv (ofString "fp12_pow_absx") K.«fp12_pow_absx» := by
  bls_unfold 755 Guest.Software.guestFn_fp12_pow_absx
  apply TerminatingProgBoundedOn.weaken'
  · apply decCall_guestInv' fb_heap_mark
    apply decCall_guestInv' fb_alloc
    apply decCall_guestInv' fb_alloc
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp12_copy)
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp12_set_one)
    apply dec_guestInv
    apply dec_guestInv
    apply dec_const_cap_guestInv "i" (BitVec.ofNat 64 64)
    apply seq_to_guestInv (fun _ h => h.1)
    · exact while_down_first_capped_on .lower (Or.inr rfl) "i"
        (TerminatingProgBoundedOn.seq_guestInv
          (TerminatingProgBoundedOn.ite_on (call_guestInv' fb_fp12_mul) (straightOn _ rfl))
          (TerminatingProgBoundedOn.ite_on
            (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp12_mul) (straightOn _ rfl))
            (straightOn _ rfl)))
        rfl
    · apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp12_copy)
      apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_heap_release)
      exact straightOn _ rfl
  · rw [show (BitVec.ofNat 64 64).toNat = 64 by decide]
    bls_arith K.«fp12_pow_absx»

/-- 3. `fb_pair_miller_loop` (`i` initialized to `63`, decremented first) -/
theorem fb_pair_miller_loop :
    TerminatingFunBoundedOn GuestInv (ofString "pair_miller_loop") K.«pair_miller_loop» := by
  bls_unfold 785 Guest.Software.guestFn_pair_miller_loop
  apply TerminatingProgBoundedOn.weaken'
  · apply decCall_guestInv' fb_heap_mark
    apply decCall_guestInv' fb_alloc
    apply decCall_guestInv' fb_alloc
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp2_copy)
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp2_copy)
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp2_set_one)
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp12_set_one)
    apply dec_guestInv
    apply dec_const_cap_guestInv "i" (BitVec.ofNat 64 63)
    apply seq_to_guestInv (fun _ h => h.1)
    · exact while_down_first_capped_on .lower (Or.inr rfl) "i"
        (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp12_mul)
          (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_pair_doubling_step)
            (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_pair_ell)
              (TerminatingProgBoundedOn.ite_on
                (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_pair_addition_step)
                  (call_guestInv' fb_pair_ell))
                (straightOn _ rfl)))))
        rfl
    · apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fp12_conj)
      apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_heap_release)
      exact straightOn _ rfl
  · rw [show (BitVec.ofNat 64 63).toNat = 63 by decide]
    bls_arith K.«pair_miller_loop»

/-- 4. `fb_fq12_reduce` (`e` initialized to `11`, decremented first) -/
theorem fb_fq12_reduce :
    TerminatingFunBoundedOn GuestInv (ofString "fq12_reduce") K.«fq12_reduce» := by
  have h_fq_mul_small := InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2.fb_fq_mul_small
  bls_unfold 658 Guest.Software.guestFn_fq12_reduce
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_const_cap_guestInv "e" (BitVec.ofNat 64 11)
    apply seq_to_guestInv (fun _ h => h.1)
    · exact while_down_first_capped_on .lower (Or.inr rfl) "e"
        (dec_guestInv _ _ _
          (decCall_guestInv' h_fq_mul_small
            (decCall_guestInv' h_fq_mul_small
              (dec_guestInv _ _ _
                (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fq_sub)
                  (TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl)
                    (dec_guestInv _ _ _
                      (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fq_add)
                        (straightOn _ rfl)))))))))
        rfl
    · exact straightOn _ rfl
  · rw [show (BitVec.ofNat 64 11).toNat = 11 by decide]
    bls_arith K.«fq12_reduce»

/-- Inner-loop helper for `fq12_mul`: `while (iend >=u i)` where `iend ≤ 11`. -/
private def fq12MulInnerMu {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup (ofString "i"), s.locals.lookup (ofString "iend") with
  | some (.val (.word wi)), some (.val (.word we)) =>
    if we.toNat ≤ 11 then we.toNat + 1 - wi.toNat else 0
  | _, _ => 0

private theorem fq12MulInnerMu_le {F : Type} (s : PanSemStateFiniteExact 64 F) :
    fq12MulInnerMu s ≤ 12 := by
  unfold fq12MulInnerMu
  split
  · split_ifs <;> omega
  · omega

private def fq12MulGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ ∃ we : BitVec 64,
    s.locals.lookup (ofString "iend") = some (.val (.word we)) ∧ we.toNat ≤ 11

private theorem while_fq12_mul_inner {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hstep : CounterStep (ofString "i") 1#64 body)
    (havoid : avoidsLocal (ofString "iend") body = true) :
    TerminatingProgBoundedOn fq12MulGuard
      (.while (.cmp .notLower (.var .local (ofString "iend")) (.var .local (ofString "i"))) body)
      ((12 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank fq12MulGuard
    (.cmp .notLower (.var .local (ofString "iend")) (.var .local (ofString "i"))) body B 12
    fq12MulInnerMu
    (fun s hP => ⟨guestInv_decClock s hP.1, hP.2⟩)
    (fun s hc hP => hbody s hc hP.1)
    (fun s _ _ _ => fq12MulInnerMu_le s) ?_
  intro F s _ ⟨hg, we, hwe, hwe11⟩ hact hflow
  obtain ⟨word, hw, hnz⟩ := hact
  change evalAt s _ = _ at hw
  obtain ⟨ve, vi, hve, hvi, hword⟩ := evalAt_cmp s .notLower _ _ word hw
  have hve_eq : ve = we := by simpa [evalAt, evalHOLExact, hwe] using hve.symm
  subst ve
  have hli : s.locals.lookup (ofString "i") = some (.val (.word vi)) := by
    simpa [evalAt, evalHOLExact] using hvi
  have hcmp : wordCmpHOL .notLower we vi = true := by
    by_cases hc : wordCmpHOL .notLower we vi = true
    · exact hc
    · simp [hc] at hword; exact absurd hword hnz
  have hle : vi.toNat ≤ we.toNat := by
    simp only [wordCmpHOL, BitVec.lt_def] at hcmp
    by_contra hgt
    have hlt' : we.toNat < vi.toNat := by omega
    simp [hlt'] at hcmp
  have hip := hstep (decClockHOLFinite s) vi hli hflow
  have hkeep := evaluate_avoidsLocal_flowing (ofString "iend") body havoid (decClockHOLFinite s)
    (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
  have hwe_post : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "iend") =
      some (.val (.word we)) := hkeep.trans hwe
  have hadd1 : (vi + 1#64).toNat = vi.toNat + 1 := BitVec.toNat_add_of_lt (by simp; omega)
  refine ⟨⟨guestInv_evaluate _ _ (guestInv_decClock s hg), we, hwe_post, hwe11⟩, ?_⟩
  unfold fq12MulInnerMu
  rw [hip, hwe_post, hli, hwe]
  dsimp only
  rw [if_pos hwe11, if_pos hwe11, hadd1]
  omega

/-- 5. `fb_fq12_mul` (`k < 23` outer, `iend <= 11` inner) -/
theorem fb_fq12_mul :
    TerminatingFunBoundedOn GuestInv (ofString "fq12_mul") K.«fq12_mul» := by
  have _ := fb_fq12_reduce
  bls_unfold 659 Guest.Software.guestFn_fq12_mul
  apply TerminatingProgBoundedOn.weaken'
  · apply decCall_guestInv' fb_heap_mark
    apply decCall_guestInv' fb_alloc
    apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply while_up_unsigned_const_guestInv (ofString "k") (BitVec.ofNat 64 23)
      · apply dec_guestInv
        apply dec_guestInv
        apply TerminatingProgBoundedOn.seq_guestInv
        · exact TerminatingProgBoundedOn.ite_on (straightOn _ rfl) (straightOn _ rfl)
        · apply dec_guestInv
          apply seq_step_on (P := GuestInv) (Q := fq12MulGuard)
          · exact TerminatingProgBoundedOn.ite_on (straightOn _ rfl) (straightOn _ rfl)
          · intro F s _ hg hnone
            rw [evaluateHOLFiniteState_ite] at hnone ⊢
            rcases hlk : s.locals.lookup (ofString "iend") with _ | vend
            · simp [evalHOLExact, hlk] at hnone
            rcases vend with ⟨⟨we⟩⟩ | _ | _ <;> try (simp [evalHOLExact, hlk] at hnone; done)
            have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
                (.cmp .lower (.const 11#64) (.var .local (ofString "iend"))) =
                some (.val (.word (if 11 < we.toNat then 1#64 else 0#64))) := by
              have h11_nat : (11#64 : BitVec 64).toNat = 11 := by decide
              simp only [evalHOLExact, hlk, wordCmpHOL, BitVec.lt_def, h11_nat, decide_eq_true_eq]
              split_ifs <;> rfl
            rw [hcond] at hnone ⊢
            by_cases h11 : 11 < we.toNat
            · simp only [if_pos h11, show ¬ ((1#64 : BitVec 64) = 0) by decide, ↓reduceIte] at hnone ⊢
              have hass : evaluateHOLFiniteState s
                  (.assign .local (ofString "iend") (.const 11#64)) =
                  (none, setVarHOLFinite (ofString "iend") (.val (.word 11#64)) s) := by
                simp [evaluateHOLFiniteState_assign, evalHOLExact, lookupKvarHOLExact, hlk,
                  isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
              rw [hass]
              exact ⟨guestInv_setVar _ _ s hg, 11#64,
                by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], by decide⟩
            · simp only [if_neg h11, ↓reduceIte] at hnone ⊢
              rw [evaluateHOLFiniteState_skip]
              exact ⟨hg, we, hlk, by omega⟩
          · apply seq_to_guestInv (fun _ h => h.1)
            · exact while_fq12_mul_inner
                (dec_guestInv _ _ _
                  (dec_guestInv _ _ _
                    (decCall_guestInv' fb_fq_mul
                      (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fq_add)
                        (straightOn _ rfl)))))
                (by counter_step)
                rfl
            · exact TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl) (straightOn _ rfl)
      · counter_step
    · apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fq12_reduce)
      apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_memcpy)
      apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_heap_release)
      exact straightOn _ rfl
  · rw [show (BitVec.ofNat 64 23).toNat = 23 by decide]
    bls_arith K.«fq12_mul»

/-- Inner-loop helpers for `fq12_sqr`: `while (i <u k - i)` when `k < 23` and `i ≤ k`. -/
private def fq12SqrInnerGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ ∃ wi wk : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word wi)) ∧
    s.locals.lookup (ofString "k") = some (.val (.word wk)) ∧
    wi.toNat ≤ wk.toNat ∧ wk.toNat < 23

private def fq12SqrInnerMu {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup (ofString "i"), s.locals.lookup (ofString "k") with
  | some (.val (.word wi)), some (.val (.word wk)) =>
    if wk.toNat < 23 then wk.toNat - wi.toNat else 0
  | _, _ => 0

private theorem fq12SqrInnerMu_le {F : Type} (s : PanSemStateFiniteExact 64 F) :
    fq12SqrInnerMu s ≤ 22 := by
  unfold fq12SqrInnerMu
  split
  · split_ifs <;> omega
  · omega

private theorem while_fq12_sqr_inner {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hstep : CounterStep (ofString "i") 1#64 body)
    (havoid : avoidsLocal (ofString "k") body = true) :
    TerminatingProgBoundedOn fq12SqrInnerGuard
      (.while (.cmp .lower (.var .local (ofString "i"))
        (.op .sub [.var .local (ofString "k"), .var .local (ofString "i")])) body)
      ((22 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank fq12SqrInnerGuard
    (.cmp .lower (.var .local (ofString "i"))
      (.op .sub [.var .local (ofString "k"), .var .local (ofString "i")])) body B 22
    fq12SqrInnerMu
    (fun s hP => ⟨guestInv_decClock s hP.1, hP.2⟩)
    (fun s hc hP => hbody s hc hP.1)
    (fun s _ _ _ => fq12SqrInnerMu_le s) ?_
  intro F s _ ⟨hg, wi, wk, hwi, hwk, hilek, hwk23⟩ hact hflow
  obtain ⟨word, hw, hnz⟩ := hact
  change evalAt s _ = _ at hw
  obtain ⟨vi, vsub, hvi, hvsub, hword⟩ := evalAt_cmp s .lower _ _ word hw
  have hvi_eq : vi = wi := by simpa [evalAt, evalHOLExact, hwi] using hvi.symm
  subst vi
  have hsub_eq : vsub = wk - wi := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hwk, hwi, wordOpHOL, wordOp, valueIsWord, valueWord] using hvsub.symm
  subst vsub
  have hcmp : wordCmpHOL .lower wi (wk - wi) = true := by
    by_cases hc : wordCmpHOL .lower wi (wk - wi) = true
    · exact hc
    · simp [hc] at hword; exact absurd hword hnz
  have hlt_sub : wi.toNat < (wk - wi).toNat := by
    simpa [wordCmpHOL, BitVec.lt_def] using hcmp
  have hsub_nat : (wk - wi).toNat = wk.toNat - wi.toNat := by
    rw [BitVec.toNat_sub]
    have := wk.isLt; have := wi.isLt
    omega
  have hip := hstep (decClockHOLFinite s) wi hwi hflow
  have hkeep := evaluate_avoidsLocal_flowing (ofString "k") body havoid (decClockHOLFinite s)
    (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
  have hwk_post : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "k") =
      some (.val (.word wk)) := hkeep.trans hwk
  have hadd1 : (wi + 1#64).toNat = wi.toNat + 1 := BitVec.toNat_add_of_lt (by simp; omega)
  refine ⟨⟨guestInv_evaluate _ _ (guestInv_decClock s hg),
    wi + 1#64, wk, hip, hwk_post, by omega, hwk23⟩, ?_⟩
  unfold fq12SqrInnerMu
  rw [hip, hwk_post, hwi, hwk]
  dsimp only
  rw [if_pos hwk23, if_pos hwk23, hadd1]
  omega

private def fq12SqrKGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ ∃ wk : BitVec 64,
    s.locals.lookup (ofString "k") = some (.val (.word wk)) ∧ wk.toNat < 23

private theorem while_up_const_active_k23 {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn fq12SqrKGuard body B)
    (hadd : CounterStep (ofString "k") 1#64 body) :
    TerminatingProgBoundedOn GuestInv
      (.while (.cmp .lower (.var .local (ofString "k")) (.const 23#64)) body)
      ((23 + 1) * (B + 1)) := by
  intro F state hcode hg
  have haux := while_rank_stationary_aux (P := GuestInv)
    (condition := .cmp .lower (.var .local (ofString "k")) (.const 23#64))
    (body := body) (B := B)
    (constUpRank (ofString "k") 23#64)
    (fun s hs_code hs_g hact => by
      obtain ⟨word, hw, hnz⟩ := hact
      change evalAt s _ = _ at hw
      obtain ⟨w, v, hl, hv, hword⟩ := evalAt_cmp s .lower _ _ word hw
      have hv_eq : v = 23#64 := by simpa [evalAt, evalHOLExact] using hv.symm
      subst hv_eq
      have hlw : s.locals.lookup (ofString "k") = some (.val (.word w)) := by
        simpa [evalAt, evalHOLExact] using hl
      have hcmp : wordCmpHOL .lower w 23#64 = true := by
        by_cases hc : wordCmpHOL .lower w 23#64 = true
        · exact hc
        · simp [hc] at hword; exact absurd hword hnz
      have hlt : w.toNat < 23 := by simpa [wordCmpHOL, BitVec.lt_def] using hcmp
      exact hbody (decClockHOLFinite s) hs_code ⟨guestInv_decClock s hs_g, w, hlw, hlt⟩)
    (fun s _ hs_g hact hflow => by
      obtain ⟨word, hw, hnz⟩ := hact
      change evalAt s _ = _ at hw
      obtain ⟨w, v, hl, hv, hword⟩ := evalAt_cmp s .lower _ _ word hw
      have hv_eq : v = 23#64 := by simpa [evalAt, evalHOLExact] using hv.symm
      subst hv_eq
      have hlw : s.locals.lookup (ofString "k") = some (.val (.word w)) := by
        simpa [evalAt, evalHOLExact] using hl
      have hcmp : wordCmpHOL .lower w 23#64 = true := by
        by_cases hc : wordCmpHOL .lower w 23#64 = true
        · exact hc
        · simp [hc] at hword; exact absurd hword hnz
      have hlt : w.toNat < 23 := by simpa [wordCmpHOL, BitVec.lt_def] using hcmp
      have heff := hadd (decClockHOLFinite s) w hlw hflow
      have hnext : (w + 1#64).toNat = w.toNat + 1 := BitVec.toNat_add_of_lt (by simp; omega)
      refine ⟨guestInv_evaluate _ _ (guestInv_decClock s hs_g), Or.inl ?_⟩
      simp only [constUpRank, heff, hlw, hnext, show (23#64 : BitVec 64).toNat = 23 by decide]
      omega)
    (23 + 1) state hcode hg
    (fun _ => by
      unfold constUpRank
      split
      · have : (23#64 : BitVec 64).toNat = 23 := by decide
        omega
      · omega)
  exact haux

/-- 6. `fb_fq12_sqr` (`k < 23` outer, `i < k - i` inner) -/
theorem fb_fq12_sqr :
    TerminatingFunBoundedOn GuestInv (ofString "fq12_sqr") K.«fq12_sqr» := by
  have _ := fb_fq12_reduce
  bls_unfold 660 Guest.Software.guestFn_fq12_sqr
  apply TerminatingProgBoundedOn.weaken'
  · apply decCall_guestInv' fb_heap_mark
    apply decCall_guestInv' fb_alloc
    apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply while_up_const_active_k23
      · have hglo : GuestLocalsOnly ["k"] fq12SqrKGuard := {
          toGuest := fun _ h => h.1
          congr := fun _ _ hg hkeep ⟨_, wk, hk, hk23⟩ =>
            ⟨hg, wk, (hkeep "k" (by simp)).trans hk, hk23⟩
        }
        apply dec_avoids_on hglo _ (by decide)
        let sqrTailProg : ProgHOL 64 :=
          (ProgHOL.ite (ExpHOL.cmp Cmp.lower (ExpHOL.const 11#64) (ExpHOL.var VarKind.local (ofString "k")))
            (ProgHOL.assign VarKind.local (ofString "i")
              (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "k"), ExpHOL.const 11#64]))
            ProgHOL.skip).seq
            ((ProgHOL.while
              (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "i"))
                (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "k"), ExpHOL.var VarKind.local (ofString "i")]))
              (ProgHOL.dec (ofString "ai") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one])
                (ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one])
                  (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "a"),
                    ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 32#64]]))
                (ProgHOL.dec (ofString "aj") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one])
                  (ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one])
                    (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "a"),
                      ExpHOL.panop PanOp.mul [ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "k"),
                        ExpHOL.var VarKind.local (ofString "i")], ExpHOL.const 32#64]]))
                  (ProgHOL.decCall (ofString "p") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one])
                    (ofString "fq_mul") [ExpHOL.var VarKind.local (ofString "ai"), ExpHOL.var VarKind.local (ofString "aj")]
                    ((ProgHOL.call (some (some (VarKind.local, ofString "acc"), none)) (ofString "fq_add")
                      [ExpHOL.var VarKind.local (ofString "acc"), ExpHOL.var VarKind.local (ofString "p")]).seq
                      (ProgHOL.assign VarKind.local (ofString "i")
                        (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 1#64]))))))).seq
              ((ProgHOL.call (some (some (VarKind.local, ofString "acc"), none)) (ofString "fq_add")
                [ExpHOL.var VarKind.local (ofString "acc"), ExpHOL.var VarKind.local (ofString "acc")]).seq
                ((ProgHOL.ite
                  (ExpHOL.cmp Cmp.equal (ExpHOL.op BinOp.and [ExpHOL.var VarKind.local (ofString "k"), ExpHOL.const 1#64])
                    (ExpHOL.const 0#64))
                  (ProgHOL.dec (ofString "am") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one])
                    (ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one])
                      (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "a"),
                        ExpHOL.panop PanOp.mul [ExpHOL.shift Shift.lsr (ExpHOL.var VarKind.local (ofString "k"))
                          (ExpHOL.const 1#64), ExpHOL.const 32#64]]))
                    (ProgHOL.decCall (ofString "sq") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one])
                      (ofString "fq_mul") [ExpHOL.var VarKind.local (ofString "am"), ExpHOL.var VarKind.local (ofString "am")]
                      (ProgHOL.call (some (some (VarKind.local, ofString "acc"), none)) (ofString "fq_add")
                        [ExpHOL.var VarKind.local (ofString "acc"), ExpHOL.var VarKind.local (ofString "sq")])))
                  ProgHOL.skip).seq
                  ((ProgHOL.store
                    (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "t"),
                      ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "k"), ExpHOL.const 32#64]])
                    (ExpHOL.var VarKind.local (ofString "acc"))).seq
                    (ProgHOL.assign VarKind.local (ofString "k")
                      (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "k"), ExpHOL.const 1#64]))))))
        have hstep_i : TerminatingProgBoundedOn fq12SqrInnerGuard sqrTailProg
            (Nat.max 0 0 +
              (((22 + 1) * ((K.«fq_mul» + (K.«fq_add» + 1 + 0) + 1) + 1)) +
                ((K.«fq_add» + 1) +
                  (Nat.max (K.«fq_mul» + (K.«fq_add» + 1) + 1) 0 + (0 + 0))))) := by
          dsimp only [sqrTailProg]
          apply seq_step_on (P := fq12SqrInnerGuard) (Q := fq12SqrInnerGuard)
          · exact fun s hc hP => TerminatingProgBoundedOn.ite_on (straightOn _ rfl) (straightOn _ rfl) s hc hP.1
          · intro F' s _ ⟨hgs, wi, wk', hwi', hwk', hilek, hwk23'⟩ hnone
            rw [evaluateHOLFiniteState_ite] at hnone ⊢
            have hcond : @evalHOLExact 64 F' _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
                (.cmp .lower (.const 11#64) (.var .local (ofString "k"))) =
                some (.val (.word (if 11 < wk'.toNat then 1#64 else 0#64))) := by
              have h11_nat : (11#64 : BitVec 64).toNat = 11 := by decide
              simp only [evalHOLExact, hwk', wordCmpHOL, BitVec.lt_def, h11_nat, decide_eq_true_eq]
              split_ifs <;> rfl
            rw [hcond] at hnone ⊢
            by_cases h11 : 11 < wk'.toNat
            · simp only [if_pos h11, show ¬ ((1#64 : BitVec 64) = 0) by decide, ↓reduceIte] at hnone ⊢
              have hass : evaluateHOLFiniteState s
                  (.assign .local (ofString "i") (.op .sub [.var .local (ofString "k"), .const 11#64])) =
                  (none, setVarHOLFinite (ofString "i") (.val (.word (wk' - 11#64))) s) := by
                simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hwk', hwi',
                  wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
                  isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
              rw [hass]
              refine ⟨guestInv_setVar _ _ s hgs, wk' - 11#64, wk',
                by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
                by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "i" ≠ ofString "k" by decide, hwk'],
                ?_, hwk23'⟩
              rw [BitVec.toNat_sub]
              have := wk'.isLt
              change (18446744073709551616 - 11 + wk'.toNat) % 18446744073709551616 ≤ wk'.toNat
              omega
            · simp only [if_neg h11, ↓reduceIte] at hnone ⊢
              rw [evaluateHOLFiniteState_skip]
              exact ⟨hgs, wi, wk', hwi', hwk', hilek, hwk23'⟩
          · apply seq_to_guestInv (fun _ h => h.1)
            · exact while_fq12_sqr_inner
                (dec_guestInv _ _ _
                  (dec_guestInv _ _ _
                    (decCall_guestInv' fb_fq_mul
                      (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fq_add)
                        (straightOn _ rfl)))))
                (by counter_step)
                rfl
            · apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fq_add)
              apply TerminatingProgBoundedOn.seq_guestInv
              · exact TerminatingProgBoundedOn.ite_on
                  (dec_guestInv _ _ _ (decCall_guestInv' fb_fq_mul (call_guestInv' fb_fq_add)))
                  (straightOn _ rfl)
              · exact TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl) (straightOn _ rfl)
        refine fun {F} state hcode ⟨hg, wk, hwk, hwk23⟩ hnt => ?_
        rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
        dsimp only [evalHOLExact] at hnt ⊢
        rw [if_pos (show shapeEqHOL ShapeHOL.one (shapeOfHOLExact (.val (.word 0#64))) = true by simp [shapeOfHOLExact, shapeEqHOL])] at hnt ⊢
        dsimp only at hnt ⊢
        let s0 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) state
        have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
          simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs0_k : s0.locals.lookup (ofString "k") = some (.val (.word wk)) := by
          simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "k" by decide, hwk]
        have hs0 : fq12SqrInnerGuard s0 := ⟨guestInv_setVar _ _ state hg, 0#64, wk, hs0_i, hs0_k, by simp, hwk23⟩
        simpa [s0, setVarHOLFinite] using hstep_i s0 hcode hs0 hnt
      · counter_step
    · apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_fq12_reduce)
      apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_memcpy)
      apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_heap_release)
      exact straightOn _ rfl
  · bls_arith K.«fq12_sqr»

/-- Helper for `ecp_mul`: `while (i <u len)` when `len ≤ 256` (`2^8`). -/
private def ecpMulGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ ∃ wlen : BitVec 64,
    s.locals.lookup (ofString "len") = some (.val (.word wlen)) ∧ wlen.toNat ≤ 256

private def ecpMulMu {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup (ofString "i"), s.locals.lookup (ofString "len") with
  | some (.val (.word wi)), some (.val (.word wl)) =>
    if wl.toNat ≤ 256 then wl.toNat - wi.toNat else 0
  | _, _ => 0

private theorem ecpMulMu_le {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ecpMulMu s ≤ 2 ^ 8 := by
  unfold ecpMulMu
  split
  · split_ifs <;> omega
  · omega

private theorem while_ecp_mul_loop {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hstep : CounterStep (ofString "i") 1#64 body)
    (havoid : avoidsLocal (ofString "len") body = true) :
    TerminatingProgBoundedOn ecpMulGuard
      (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) body)
      ((2 ^ 8 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank ecpMulGuard
    (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) body B (2 ^ 8)
    ecpMulMu
    (fun s hP => ⟨guestInv_decClock s hP.1, hP.2⟩)
    (fun s hc hP => hbody s hc hP.1)
    (fun s _ _ _ => ecpMulMu_le s) ?_
  intro F s _ ⟨hg, wlen, hwlen, hwlen256⟩ hact hflow
  obtain ⟨word, hw, hnz⟩ := hact
  change evalAt s _ = _ at hw
  obtain ⟨vi, vl, hvi, hvl, hword⟩ := evalAt_cmp s .lower _ _ word hw
  have hvl_eq : vl = wlen := by simpa [evalAt, evalHOLExact, hwlen] using hvl.symm
  subst vl
  have hli : s.locals.lookup (ofString "i") = some (.val (.word vi)) := by
    simpa [evalAt, evalHOLExact] using hvi
  have hcmp : wordCmpHOL .lower vi wlen = true := by
    by_cases hc : wordCmpHOL .lower vi wlen = true
    · exact hc
    · simp [hc] at hword; exact absurd hword hnz
  have hlt : vi.toNat < wlen.toNat := by simpa [wordCmpHOL, BitVec.lt_def] using hcmp
  have hip := hstep (decClockHOLFinite s) vi hli hflow
  have hkeep := evaluate_avoidsLocal_flowing (ofString "len") body havoid (decClockHOLFinite s)
    (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
  have hwlen_post : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "len") =
      some (.val (.word wlen)) := hkeep.trans hwlen
  have hadd1 : (vi + 1#64).toNat = vi.toNat + 1 := BitVec.toNat_add_of_lt (by simp; omega)
  refine ⟨⟨guestInv_evaluate _ _ (guestInv_decClock s hg), wlen, hwlen_post, hwlen256⟩, ?_⟩
  unfold ecpMulMu
  rw [hip, hwlen_post, hli, hwlen]
  dsimp only
  rw [if_pos hwlen256, if_pos hwlen256, hadd1]
  omega

/-- Self-contained return bound `≤ 64` for `bit_length64` and `≤ 256` for `u256_bit_length`. -/
private def fnBody64 (d : Decl (BitVec 64)) : ProgHOL 64 :=
  InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body

private theorem lookup_bit_length64_spec :
    originalRuntimeCode.lookup (ofString "bit_length64") =
      some ([(ofString "x", .one)], fnBody64 Guest.Software.guestFn_bit_length64, .one) :=
  lookup_of_guestAst_getElem 77 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bit_length64) rfl

private theorem lookupCode_one_word_spec {code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    {fn p1 : MlS} {body foundBody : ProgHOL 64} {rs foundRs : ShapeHOL}
    {v1 : ValueHOL 64} {locals : HolFiniteMapExact MlS (ValueHOL 64)}
    (hlookup : code fn = some ([(p1, .one)], body, rs))
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code fn [v1] =
      some (foundBody, locals, foundRs)) :
    foundBody = body ∧ ∃ w1 : BitVec 64, locals.lookup p1 = some (.val (.word w1)) := by
  have hb := lookupCodeHOLFinite_installed_body code fn _ body foundBody rs foundRs
    [v1] locals hlookup hfound
  refine ⟨hb, ?_⟩
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
  split at hfound
  · cases hfound
  · rename_i _ _ _ raw
    cases v1 with
    | val wl =>
      cases wl with
      | word w1 =>
        have hraw : lookupCodeHOLExact code fn [ValueHOL.val (HolWordLab.word w1)] =
            some (body,
              (fun current => if current = p1 then some (ValueHOL.val (HolWordLab.word w1)) else none),
              rs) := by
          simp [lookupCodeHOLExact, hlookup, shapeOfHOLExact, shapeEqHOL]
        rw [hraw] at raw
        cases raw
        cases hfound
        exact ⟨w1, by simp⟩
    | rStruct _ =>
      simp [lookupCodeHOLExact, hlookup, shapeOfHOLExact, shapeEqHOL] at raw
    | nStruct _ _ =>
      simp [lookupCodeHOLExact, hlookup, shapeOfHOLExact, shapeEqHOL] at raw

private theorem bit_length64_step_le {F : Type}
    (s : PanSemStateFiniteExact 64 F) (k : BitVec 64)
    (n x : BitVec 64) (hx : x.toNat < 2 ^ (2 * k.toNat))
    (hk_pos : 0 < k.toNat) (hk_le : k.toNat ≤ 32)
    (hn_le : n.toNat + 2 * k.toNat ≤ 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hx_loc : s.locals.lookup (ofString "x") = some (.val (.word x))) :
    let stepProg : ProgHOL 64 :=
      .ite (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const k)) (.const 0#64))
        (.seq
          (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const k]))
          (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const k))))
        .skip
    ∀ s', evaluateHOLFiniteState s stepProg = (none, s') →
      ∃ n' x',
        s'.locals.lookup (ofString "n") = some (.val (.word n')) ∧
        s'.locals.lookup (ofString "x") = some (.val (.word x')) ∧
        x'.toNat < 2 ^ k.toNat ∧
        n'.toNat + k.toNat ≤ 64 := by
  dsimp only
  intro s' hrun
  rw [evaluateHOLFiniteState_ite] at hrun
  have hk_not64 : ¬ (¬ k.toNat = 0 ∧ 64 ≤ k.toNat) := by omega
  have hcond : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const k)) (.const 0#64)) =
      some (.val (.word (if x >>> k.toNat = 0#64 then 0#64 else 1#64))) := by
    simp [evalHOLExact, hx_loc, Compiler.Encoders.Asm.wordCmpHOL, wordShiftHOL, hk_not64]
  rw [hcond] at hrun
  dsimp only at hrun
  by_cases hz : x >>> k.toNat = 0#64
  · rw [if_pos hz] at hrun
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    rw [if_pos h0, evaluateHOLFiniteState_skip] at hrun
    cases hrun
    refine ⟨n, x, hn, hx_loc, ?_, by omega⟩
    have hzt := congrArg BitVec.toNat hz
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hzt
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hzt
    exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos k.toNat)).mp hzt
  · rw [if_neg hz, if_neg (show ¬ ((1#64 : BitVec 64) = 0) by decide),
      evaluateHOLFiniteState_seq_line780] at hrun
    have hasgn_n : evaluateHOLFiniteState s
        (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const k])) =
        (none, setVarHOLFinite (ofString "n") (.val (.word (n + k))) s) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hn,
        wordOpHOL, wordOp, valueIsWord, valueWord,
        lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite, setVarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [hasgn_n] at hrun
    dsimp only at hrun
    let s1 := setVarHOLFinite (ofString "n") (.val (.word (n + k))) s
    have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word (n + k))) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs1_x : s1.locals.lookup (ofString "x") = some (.val (.word x)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "x" by decide, hx_loc]
    have hasgn_x : evaluateHOLFiniteState s1
        (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const k))) =
        (none, setVarHOLFinite (ofString "x") (.val (.word (x >>> k.toNat))) s1) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, hs1_x, wordShiftHOL, hk_not64,
        lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite, setVarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [hasgn_x] at hrun
    cases hrun
    refine ⟨n + k, x >>> k.toNat, ?_, ?_, ?_, ?_⟩
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "x" ≠ ofString "n" by decide, hs1_n]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have hpow : 2 ^ (2 * k.toNat) = 2 ^ k.toNat * 2 ^ k.toNat := by
        rw [Nat.two_mul, Nat.pow_add]
      rw [hpow] at hx
      exact Nat.div_lt_of_lt_mul hx
    · have hadd : (n + k).toNat = n.toNat + k.toNat := BitVec.toNat_add_of_lt (by omega)
      omega

private theorem evaluate_bit_length64_le64 {F : Type}
    (state : PanSemStateFiniteExact 64 F) (x : BitVec 64)
    (hx : state.locals.lookup (ofString "x") = some (.val (.word x))) :
    ∀ w, (evaluateHOLFiniteState state (fnBody64 Guest.Software.guestFn_bit_length64)).1 =
      some (.returned w) →
      ∃ b : BitVec 64, w = .val (.word b) ∧ b.toNat ≤ 64 := by
  intro w hrun
  unfold fnBody64 at hrun
  dsimp only [extractFn, Guest.Software.guestFn_bit_length64,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hrun
  rw [evaluateHOLFiniteState_dec_total] at hrun
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hrun
  let s0 := setVarHOLFinite (ofString "n") (.val (.word 0#64)) state
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word 0#64)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_x : s0.locals.lookup (ofString "x") = some (.val (.word x)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "x" by decide, hx]
  have hno_ret_step : ∀ (k : BitVec 64) (st : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState st
        (.ite (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const k)) (.const 0#64))
          (.seq
            (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const k]))
            (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const k))))
          .skip)).1 ≠ some (.returned w) := by
    intro k st hc
    rw [evaluateHOLFiniteState_ite] at hc
    split at hc
    · split at hc
      · rw [evaluateHOLFiniteState_skip] at hc; simp at hc
      · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hc
        split at hc
        · simp at hc
        · split at hc
          · dsimp only at hc
            rw [evaluateHOLFiniteState_assign] at hc
            split at hc
            · simp at hc
            · split at hc <;> simp at hc
          · simp at hc
    · simp at hc
  have hstep_seq : ∀ {p1 p2 : ProgHOL 64} {st : PanSemStateFiniteExact 64 F},
      (evaluateHOLFiniteState st (.seq p1 p2)).1 = some (.returned w) →
      (evaluateHOLFiniteState st p1).1 ≠ some (.returned w) →
      ∃ sm, evaluateHOLFiniteState st p1 = (none, sm) ∧
        (evaluateHOLFiniteState sm p2).1 = some (.returned w) := by
    intro p1 p2 st hs hnr
    rw [evaluateHOLFiniteState_seq_line780] at hs
    rcases hr1 : evaluateHOLFiniteState st p1 with ⟨r1, sm⟩
    rw [hr1] at hs hnr
    cases r1 with
    | none => exact ⟨sm, rfl, hs⟩
    | some _ => exact False.elim (hnr hs)
  obtain ⟨s1, hr1, hrun⟩ := hstep_seq hrun (hno_ret_step 32#64 s0)
  obtain ⟨n1, x1, hn1, hx1, hxb1, hnb1⟩ := bit_length64_step_le s0 32#64 0#64 x
    (by change x.toNat < 2 ^ 64; exact x.isLt) (by decide) (by decide) (by decide) hs0_n hs0_x s1 hr1
  obtain ⟨s2, hr2, hrun⟩ := hstep_seq hrun (hno_ret_step 16#64 s1)
  obtain ⟨n2, x2, hn2, hx2, hxb2, hnb2⟩ := bit_length64_step_le s1 16#64 n1 x1
    hxb1 (by decide) (by decide) (by change n1.toNat + 32 ≤ 64; exact hnb1) hn1 hx1 s2 hr2
  obtain ⟨s3, hr3, hrun⟩ := hstep_seq hrun (hno_ret_step 8#64 s2)
  obtain ⟨n3, x3, hn3, hx3, hxb3, hnb3⟩ := bit_length64_step_le s2 8#64 n2 x2
    hxb2 (by decide) (by decide) (by change n2.toNat + 16 ≤ 64; exact hnb2) hn2 hx2 s3 hr3
  obtain ⟨s4, hr4, hrun⟩ := hstep_seq hrun (hno_ret_step 4#64 s3)
  obtain ⟨n4, x4, hn4, hx4, hxb4, hnb4⟩ := bit_length64_step_le s3 4#64 n3 x3
    hxb3 (by decide) (by decide) (by change n3.toNat + 8 ≤ 64; exact hnb3) hn3 hx3 s4 hr4
  obtain ⟨s5, hr5, hrun⟩ := hstep_seq hrun (hno_ret_step 2#64 s4)
  obtain ⟨n5, x5, hn5, hx5, hxb5, hnb5⟩ := bit_length64_step_le s4 2#64 n4 x4
    hxb4 (by decide) (by decide) (by change n4.toNat + 4 ≤ 64; exact hnb4) hn4 hx4 s5 hr5
  obtain ⟨s6, hr6, hrun⟩ := hstep_seq hrun (hno_ret_step 1#64 s5)
  obtain ⟨n6, x6, hn6, hx6, hxb6, hnb6⟩ := bit_length64_step_le s5 1#64 n5 x5
    hxb5 (by decide) (by decide) (by change n5.toNat + 2 ≤ 64; exact hnb5) hn5 hx5 s6 hr6
  rw [evaluateHOLFiniteState_return] at hrun
  have hev_ret : @evalHOLExact 64 F _ s6.toExact
      (fun a => Classical.propDecidable (s6.memaddrs a))
      (.op .add [.var .local (ofString "n"), .var .local (ofString "x")]) =
      some (.val (.word (n6 + x6))) := by
    simp [evalHOLExact, evalListHOLExact, hn6, hx6, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [hev_ret] at hrun
  dsimp only at hrun
  split at hrun
  · simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at hrun
    subst hrun
    refine ⟨n6 + x6, rfl, ?_⟩
    change x6.toNat < 2 ^ 1 at hxb6
    change n6.toNat + 1 ≤ 64 at hnb6
    have hadd : (n6 + x6).toNat = n6.toNat + x6.toNat := BitVec.toNat_add_of_lt (by omega)
    omega
  · simp at hrun

private theorem u256_bit_length_ret_le_256 {F : Type}
    (entry post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hcode : entry.code = originalRuntimeCode)
    (hrun : evaluateHOLFiniteState entry (fnBody64 Guest.Software.guestFn_u256_bit_length) =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ 256 := by
  unfold fnBody64 at hrun
  dsimp only [extractFn, Guest.Software.guestFn_u256_bit_length,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hrun
  have hbranch : ∀ (s : PanSemStateFiniteExact 64 F) (cond : ExpHOL 64) (nm : MlS)
      (arg : ExpHOL 64) (off : BitVec 64) (rest : ProgHOL 64),
      off.toNat ≤ 192 →
      s.code = originalRuntimeCode →
      evaluateHOLFiniteState s
        (.seq (.ite cond (.decCall nm .one (ofString "bit_length64") [arg]
          (.return (.op .add [.const off, .var .local nm]))) .skip) rest) =
        (some (.returned v), post) →
      (∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ 256) ∨
      evaluateHOLFiniteState s rest = (some (.returned v), post) := by
    intro s cond nm arg off rest hoff hs_code hseq
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hseq
    split at hseq
    · split at hseq
      · rw [evaluateHOLFiniteState_skip] at hseq; exact Or.inr hseq
      · rcases hdc : evaluateHOLFiniteState s
            (.decCall nm .one (ofString "bit_length64") [arg]
              (.return (.op .add [.const off, .var .local nm]))) with ⟨rdc, sdc⟩
        rw [hdc] at hseq
        dsimp only at hseq
        have hdc1 := congrArg Prod.fst hdc
        dsimp only at hdc1
        rw [evaluateHOLFiniteState_decCall_total] at hdc1
        rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [arg] with _ | vs
        · rw [hargs] at hdc1; subst rdc; cases hseq
        · rw [hargs] at hdc1; dsimp only at hdc1
          have hvs1 : ∃ v1, vs = [v1] := by
            rw [evalListHOLFinite_eq_toExact] at hargs
            simp only [evalListHOLExact] at hargs
            rcases ha : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) arg with _ | v1
            · rw [ha] at hargs; cases hargs
            · rw [ha] at hargs; cases hargs; exact ⟨v1, rfl⟩
          obtain ⟨v1, rfl⟩ := hvs1
          rcases hlk : lookupCodeHOLFinite s.code.lookup (ofString "bit_length64") [v1] with _ | ⟨b, cal, rs⟩
          · rw [hlk] at hdc1; subst rdc; cases hseq
          · rw [hlk] at hdc1; dsimp only at hdc1
            split at hdc1
            · subst rdc; cases hseq
            · rcases hrb : evaluateHOLFiniteState (callEntryStateHOLFinite s cal) b with ⟨rb, sb⟩
              rw [hrb] at hdc1
              cases rb with
              | none => dsimp only at hdc1; subst rdc; cases hseq
              | some rr =>
                cases rr with
                | «break» => dsimp only at hdc1; subst rdc; cases hseq
                | «continue» => dsimp only at hdc1; subst rdc; cases hseq
                | error => dsimp only at hdc1; subst rdc; cases hseq
                | timeOut => dsimp only at hdc1; subst rdc; cases hseq
                | exception _ _ => dsimp only at hdc1; subst rdc; cases hseq
                | finalFfi _ => dsimp only at hdc1; subst rdc; cases hseq
                | returned vv =>
                  dsimp only at hdc1
                  split at hdc1
                  · dsimp only at hdc1
                    have hlk' := hlk; rw [hs_code] at hlk'
                    obtain ⟨rfl, w1, hw1⟩ := lookupCode_one_word_spec lookup_bit_length64_spec hlk'
                    obtain ⟨wb, rfl, hwb64⟩ := evaluate_bit_length64_le64
                      (callEntryStateHOLFinite s cal) w1 hw1 vv (by rw [hrb])
                    rw [evaluateHOLFiniteState_return] at hdc1
                    have hev_add : @evalHOLExact 64 F _
                        (setVarHOLFinite nm (.val (.word wb))
                          { (fixClockHOLFinite (callEntryStateHOLFinite s cal)
                              (some (PanSemResultExact.returned (.val (.word wb))), sb)).2 with locals := s.locals }).toExact
                        (fun a => Classical.propDecidable
                          ((setVarHOLFinite nm (.val (.word wb))
                            { (fixClockHOLFinite (callEntryStateHOLFinite s cal)
                                (some (PanSemResultExact.returned (.val (.word wb))), sb)).2 with locals := s.locals }).memaddrs a))
                        (.op .add [.const off, .var .local nm]) =
                        some (.val (.word (off + wb))) := by
                      simp [evalHOLExact, evalListHOLExact, setVarHOLFinite,
                        HolFiniteMapExact.lookup_update, FUPDATE,
                        wordOpHOL, wordOp, valueIsWord, valueWord]
                    rw [hev_add] at hdc1
                    dsimp only at hdc1
                    have hsize_ok : sizeOfShapeWithContextHOL
                        (setVarHOLFinite nm (.val (.word wb))
                          { (fixClockHOLFinite (callEntryStateHOLFinite s cal)
                              (some (PanSemResultExact.returned (.val (.word wb))), sb)).2 with locals := s.locals }).structs
                        (shapeOfHOLExact (.val (.word (off + wb)))) ≤ 32 := by
                      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                    rw [if_pos hsize_ok] at hdc1
                    dsimp only at hdc1
                    subst rdc
                    have hinj := PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj hseq).1)
                    subst hinj
                    refine Or.inl ⟨off + wb, rfl, ?_⟩
                    have hadd : (off + wb).toNat = off.toNat + wb.toNat := BitVec.toNat_add_of_lt (by omega)
                    omega
                  · subst rdc; cases hseq
    · cases hseq
  rcases hbranch entry _ (ofString "n3") _ 192#64 _ (by decide) hcode hrun with h | h1
  · exact h
  · rcases hbranch entry _ (ofString "n2") _ 128#64 _ (by decide) hcode h1 with h | h2
    · exact h
    · rcases hbranch entry _ (ofString "n1") _ 64#64 _ (by decide) hcode h2 with h | h3
      · exact h
      · rw [evaluateHOLFiniteState_call] at h3
        rcases hargs : evalListHOLFinite entry (h := fun a => Classical.propDecidable (entry.memaddrs a))
            [.rfield 0 (.var .local (ofString "a"))] with _ | vs
        · rw [hargs] at h3; cases h3
        · rw [hargs] at h3; dsimp only at h3
          have hvs1 : ∃ v1, vs = [v1] := by
            rw [evalListHOLFinite_eq_toExact] at hargs
            simp only [evalListHOLExact] at hargs
            rcases ha : @evalHOLExact 64 F _ entry.toExact (fun a => Classical.propDecidable (entry.memaddrs a))
                (.rfield 0 (.var .local (ofString "a"))) with _ | v1
            · rw [ha] at hargs; cases hargs
            · rw [ha] at hargs; cases hargs; exact ⟨v1, rfl⟩
          obtain ⟨v1, rfl⟩ := hvs1
          rcases hlk : lookupCodeHOLFinite entry.code.lookup (ofString "bit_length64") [v1] with _ | ⟨b, cal, rs⟩
          · rw [hlk] at h3; cases h3
          · rw [hlk] at h3; dsimp only at h3
            split at h3
            · cases h3
            · rcases hrb : evaluateHOLFiniteState (callEntryStateHOLFinite entry cal) b with ⟨rb, sb⟩
              rw [hrb] at h3
              cases rb with
              | none => cases h3
              | some rr =>
                cases rr with
                | returned vv =>
                  dsimp only at h3
                  split at h3
                  · have hinj := PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj h3).1)
                    subst hinj
                    have hlk' := hlk; rw [hcode] at hlk'
                    obtain ⟨rfl, w1, hw1⟩ := lookupCode_one_word_spec lookup_bit_length64_spec hlk'
                    obtain ⟨wb, rfl, hwb64⟩ := evaluate_bit_length64_le64
                      (callEntryStateHOLFinite entry cal) w1 hw1 vv (by rw [hrb])
                    exact ⟨wb, rfl, by omega⟩
                  · cases h3
                | _ => cases h3

/-- 7. `fb_ecp_mul` (`len = u256_bit_length(n) ≤ 256 = 2^8`) -/
theorem fb_ecp_mul :
    TerminatingFunBoundedOn GuestInv (ofString "ecp_mul") K.«ecp_mul» := by
  have h_fe_mul := fb_fe_mul_of fb_fq12_mul
  have h_fe_sqr := fb_fe_sqr_of h_fe_mul fb_fq12_sqr
  have h_fe_mul_small := InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2.fb_fe_mul_small
  have h_fe_sub := InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_RemoteLeavesB2.fb_fe_sub
  have h_fe_eq := fb_fe_eq_of fb_memeq
  have h_ecp_double := fb_ecp_double_of h_fe_mul h_fe_mul_small h_fe_sqr h_fe_sub
  have h_ecp_add := fb_ecp_add_of h_ecp_double h_fe_eq h_fe_mul h_fe_mul_small h_fe_sqr h_fe_sub
  bls_unfold 675 Guest.Software.guestFn_ecp_mul
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply decCall_guestInv' fb_heap_mark
    apply decCall_guestInv' fb_alloc
    apply decCall_guestInv' fb_alloc
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_ecp_set_inf)
    apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_memcpy)
    apply TerminatingProgBoundedOn.decCall_on (Q := ecpMulGuard) fb_u256_bit_length
    · intro F s _ _ callee _ _ hg _ _
      exact guestInv_callEntry s callee hg
    · intro F s values body' callee ret' value post hcode hg _ hfound hrun
      have hlook_ubl : originalRuntimeCode.lookup (ofString "u256_bit_length") =
          some ([(ofString "a", .comb [.one, .one, .one, .one])],
                fnBody64 Guest.Software.guestFn_u256_bit_length, .one) :=
        lookup_of_guestAst_getElem 78 (by rw [guestAst_len]; decide)
          (extractFn Guest.Software.guestFn_u256_bit_length) rfl
      have hfound' := hfound; rw [hcode] at hfound'
      have hb_eq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
        (ofString "u256_bit_length") _ (fnBody64 Guest.Software.guestFn_u256_bit_length)
        body' .one ret' values callee hlook_ubl hfound'
      subst body'
      obtain ⟨wlen, rfl, hwlen256⟩ := u256_bit_length_ret_le_256
        (callEntryStateHOLFinite s callee) post value hcode hrun
      have hpostG : GuestInv post := by
        have := guestInv_evaluate (callEntryStateHOLFinite s callee)
          (fnBody64 Guest.Software.guestFn_u256_bit_length)
          (guestInv_callEntry s callee hg)
        rw [hrun] at this; exact this
      refine ⟨guestInv_setVar _ _ _ (guestInv_with_locals_clock post s.locals post.clock hpostG),
        wlen, ?_, hwlen256⟩
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · have hglo : GuestLocalsOnly ["len"] ecpMulGuard := {
        toGuest := fun _ h => h.1
        congr := fun _ _ hg hkeep ⟨_, wl, hl, hl256⟩ =>
          ⟨hg, wl, (hkeep "len" (by simp)).trans hl, hl256⟩
      }
      apply dec_avoids_on hglo _ (by decide)
      apply seq_to_guestInv (fun _ h => h.1)
      · exact while_ecp_mul_loop
          (decCall_guestInv' fb_u256_bit
            (TerminatingProgBoundedOn.seq_guestInv
              (TerminatingProgBoundedOn.ite_on (call_guestInv' h_ecp_add) (straightOn _ rfl))
              (TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl)
                (TerminatingProgBoundedOn.ite_on (call_guestInv' h_ecp_double) (straightOn _ rfl)))))
          (CounterStep.decCall _ _ _ _ _ _ (by decide)
            (CounterStep.seq _ _ _ rfl rfl
              (CounterStep.suffix _ _ _ (CounterStep.assign _ _) rfl)))
          rfl
      · apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_memcpy)
        apply TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_heap_release)
        exact straightOn _ rfl
  · bls_arith K.«ecp_mul»

end InitECandidate.Solver.Wave8GuestInv.R16ArithPort.Capped
