import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsTypedDeclarations
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsInverseOuterBound

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators

def blsInverseZeroExpr : ExpHOL 64 := .rstruct [.const 0, .const 0, .const 0, .const 0, .const 0, .const 0]
def blsInverseOneExpr : ExpHOL 64 := .rstruct [.const 1, .const 0, .const 0, .const 0, .const 0, .const 0]
def blsInverseInitBody : ProgHOL 64 :=
  .dec (ofString "u") blsU384Shape (.var .local (ofString "a"))
    (.dec (ofString "v") blsU384Shape blsModulusExpr
      (.dec (ofString "x1") blsU384Shape blsInverseOneExpr
        (.dec (ofString "x2") blsU384Shape blsInverseZeroExpr
          (.seq blsInverseOuterLoop (.return blsInverseZeroExpr)))))

theorem blsInverseSource_eq : arithSourceBody Guest.Software.guestFn_bls_fp_inv_raw =
    .decCall (ofString "az") .one (ofString "bls_fp_is_zero") [.var .local (ofString "a")]
      (.seq (.ite (.cmp .equal (.var .local (ofString "az")) (.const 1))
        (.return blsInverseZeroExpr) .skip) blsInverseInitBody) := rfl

def blsInverseLoopCost : Nat := (769 + 1) * (blsInverseBodyCost + 1)

theorem blsInverseInitBody_bound : TerminatingProgBounded blsInverseInitBody
    blsInverseLoopCost := by
  have hfinish : TerminatingProgBoundedOn blsInverseTyped
      (.seq blsInverseOuterLoop (.return blsInverseZeroExpr))
      (blsInverseLoopCost + 0) :=
    TerminatingProgBoundedOn.seq_on_none blsInverseOuterLoop_bound
      (Q := fun _ => True) (fun _ _ _ _ _ => trivial)
      (fun state hc _ => TerminatingProgBounded.straight _ rfl state hc)
  have htyped : TerminatingProgBoundedOn
      (hasU384Locals [ofString "x2", ofString "x1", ofString "v", ofString "u"])
      (.seq blsInverseOuterLoop (.return blsInverseZeroExpr))
      blsInverseLoopCost := by
    intro F state hc hp
    obtain ⟨u, hu⟩ := hp (ofString "u") (by simp)
    obtain ⟨v, hv⟩ := hp (ofString "v") (by simp)
    obtain ⟨x1, hx1⟩ := hp (ofString "x1") (by simp)
    obtain ⟨x2, hx2⟩ := hp (ofString "x2") (by simp)
    simpa only [Nat.add_zero] using hfinish state hc ⟨⟨u, v, x1, x2⟩, hu, hv, hx1, hx2⟩
  have hb : TerminatingProgBoundedOn (hasU384Locals []) blsInverseInitBody
      blsInverseLoopCost := by
    unfold blsInverseInitBody
    exact dec_u384_bound [] (ofString "u") _
      (dec_u384_bound [ofString "u"] (ofString "v") blsModulusExpr
        (dec_u384_bound [ofString "v", ofString "u"] (ofString "x1") _
          (dec_u384_bound [ofString "x1", ofString "v", ofString "u"] (ofString "x2") _ htyped)))
  intro F state hc
  exact hb state hc (by intro key hk; cases hk)

private theorem bls_inverse_cost_layout (a b c d e n : Nat) :
    (a + (0 + n * ((b + b + (c + d + e)) + 1))) + 1 =
      (a + 1) + n * (b + b + c + d + e + 1) := by
  simp only [Nat.zero_add, Nat.add_assoc]
  omega

theorem blsInverseCost_eq : (K.bls_fp_is_zero + (0 + blsInverseLoopCost)) + 1 = K.bls_fp_inv_raw :=
  bls_inverse_cost_layout K.bls_fp_is_zero blsInverseHalfCost (K.bls_fp_lt_raw + 1)
    (K.bls_fp_sub_raw + 1) (K.bls_fp_sub + 1) (769 + 1)

attribute [local irreducible] blsInverseLoopCost blsInverseOuterLoop blsInverseBodyCost blsInverseHalfCost blsInverseTailCost K.bls_fp_inv_raw

theorem ub_bls_fp_inv_raw : TerminatingFunBounded (ofString "bls_fp_inv_raw") K.bls_fp_inv_raw := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 712
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_bls_fp_inv_raw) rfl, ?_⟩
  change TerminatingProgBounded (arithSourceBody Guest.Software.guestFn_bls_fp_inv_raw) K.bls_fp_inv_raw
  rw [blsInverseSource_eq]
  have hb : TerminatingProgBounded
      (.decCall (ofString "az") .one (ofString "bls_fp_is_zero") [.var .local (ofString "a")]
        (.seq (.ite (.cmp .equal (.var .local (ofString "az")) (.const 1))
          (.return blsInverseZeroExpr) .skip) blsInverseInitBody))
      ((K.bls_fp_is_zero + (0 + blsInverseLoopCost)) + 1) :=
    TerminatingProgBounded.decCall ub_bls_fp_is_zero _ _ _
      (TerminatingProgBounded.seq (TerminatingProgBounded.straight _ rfl) blsInverseInitBody_bound)
  rw [blsInverseCost_eq] at hb
  intro F state hc
  exact hb state hc

theorem fb_bls_fp_inv_raw : TerminatingFunBoundedOn GuestInv (ofString "bls_fp_inv_raw") K.bls_fp_inv_raw :=
  TerminatingFunBoundedOn.of_unconditional ub_bls_fp_inv_raw
end InitECandidate.Solver.Wave8GuestInv.Arith
