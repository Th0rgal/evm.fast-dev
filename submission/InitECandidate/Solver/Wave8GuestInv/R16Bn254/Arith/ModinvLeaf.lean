import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.TypedDeclarations

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators

def inverseZeroExpr : ExpHOL 64 := .rstruct [.const 0, .const 0, .const 0, .const 0]
def inverseOneExpr : ExpHOL 64 := .rstruct [.const 1, .const 0, .const 0, .const 0]
def inverseInitBody : ProgHOL 64 :=
  .dec (ofString "u") arithU256Shape (.var .local (ofString "a"))
    (.dec (ofString "v") arithU256Shape (.var .local (ofString "m"))
      (.dec (ofString "x1") arithU256Shape inverseOneExpr
        (.dec (ofString "x2") arithU256Shape inverseZeroExpr
          (.seq inverseOuterLoop (.return inverseZeroExpr)))))

theorem inverseSource_eq : arithSourceBody Guest.Software.guestFn_modinv_bin =
    .decCall (ofString "az") .one (ofString "u256_is_zero") [.var .local (ofString "a")]
      (.seq (.ite (.cmp .equal (.var .local (ofString "az")) (.const 1))
        (.return inverseZeroExpr) .skip) inverseInitBody) := rfl

def inverseLoopCost : Nat := (513 + 1) * (inverseBodyCost + 1)

theorem inverseInitBody_bound : TerminatingProgBounded inverseInitBody
    inverseLoopCost := by
  have hfinish : TerminatingProgBoundedOn inverseTyped
      (.seq inverseOuterLoop (.return inverseZeroExpr))
      (inverseLoopCost + 0) :=
    TerminatingProgBoundedOn.seq_on_none inverseOuterLoop_bound
      (Q := fun _ => True) (fun _ _ _ _ _ => trivial)
      (fun state hc _ => TerminatingProgBounded.straight _ rfl state hc)
  have htyped : TerminatingProgBoundedOn
      (hasU256Locals [ofString "x2", ofString "x1", ofString "v", ofString "m", ofString "u"])
      (.seq inverseOuterLoop (.return inverseZeroExpr))
      inverseLoopCost := by
    intro F state hc hp
    obtain ⟨u, hu⟩ := hp (ofString "u") (by simp)
    obtain ⟨v, hv⟩ := hp (ofString "v") (by simp)
    obtain ⟨x1, hx1⟩ := hp (ofString "x1") (by simp)
    obtain ⟨x2, hx2⟩ := hp (ofString "x2") (by simp)
    obtain ⟨m, hm⟩ := hp (ofString "m") (by simp)
    simpa only [Nat.add_zero] using hfinish state hc ⟨⟨u, v, x1, x2, m⟩, hu, hv, hx1, hx2, hm⟩
  have hb : TerminatingProgBoundedOn (hasU256Locals []) inverseInitBody
      inverseLoopCost := by
    unfold inverseInitBody
    exact dec_u256_bound [] (ofString "u") _
      (dec_u256_local_bound [ofString "u"] (ofString "v") (ofString "m")
        (dec_u256_bound [ofString "v", ofString "m", ofString "u"] (ofString "x1") _
          (dec_u256_bound [ofString "x1", ofString "v", ofString "m", ofString "u"] (ofString "x2") _ htyped)))
  intro F state hc
  exact hb state hc (by intro key hk; cases hk)

private theorem inverse_cost_layout (a b c d e n : Nat) :
    (a + (0 + n * ((b + b + (c + d + e)) + 1))) + 1 =
      (a + 1) + n * (b + b + c + d + e + 1) := by
  simp only [Nat.zero_add, Nat.add_assoc]
  omega

theorem inverseCost_eq : (K.u256_is_zero + (0 + inverseLoopCost)) + 1 = K.modinv_bin :=
  inverse_cost_layout K.u256_is_zero inverseHalfCost (K.u256_lt + 1)
    (K.u256_sub + 1) (K.mod_sub + 1) (513 + 1)

attribute [local irreducible] inverseLoopCost inverseOuterLoop inverseBodyCost inverseHalfCost inverseTailCost K.modinv_bin

theorem ub_modinv_bin : TerminatingFunBounded (ofString "modinv_bin") K.modinv_bin := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 157
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_modinv_bin) rfl, ?_⟩
  change TerminatingProgBounded (arithSourceBody Guest.Software.guestFn_modinv_bin) K.modinv_bin
  rw [inverseSource_eq]
  have hb : TerminatingProgBounded
      (.decCall (ofString "az") .one (ofString "u256_is_zero") [.var .local (ofString "a")]
        (.seq (.ite (.cmp .equal (.var .local (ofString "az")) (.const 1))
          (.return inverseZeroExpr) .skip) inverseInitBody))
      ((K.u256_is_zero + (0 + inverseLoopCost)) + 1) :=
    TerminatingProgBounded.decCall ub_u256_is_zero _ _ _
      (TerminatingProgBounded.seq (TerminatingProgBounded.straight _ rfl) inverseInitBody_bound)
  rw [inverseCost_eq] at hb
  intro F state hc
  exact hb state hc

theorem fb_modinv_bin : TerminatingFunBoundedOn GuestInv (ofString "modinv_bin") K.modinv_bin :=
  TerminatingFunBoundedOn.of_unconditional ub_modinv_bin

end InitECandidate.Solver.Wave8GuestInv.Arith
