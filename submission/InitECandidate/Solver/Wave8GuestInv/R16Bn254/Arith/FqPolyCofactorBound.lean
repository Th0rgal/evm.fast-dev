import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyLeaves
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyCofactorBody
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.CounterUpOn

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators

def polyCofactorBodyCost : Nat := K.u256_is_zero + (max (K.fq_poly_submul+1) 0 + 0) + 1

theorem polyCofactorBody_bounded : TerminatingProgBoundedOn GuestInv polyCofactorBody polyCofactorBodyCost := by
  exact TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
    (TerminatingProgBoundedOn.decCall_guestInv (TerminatingFunBoundedOn.of_unconditional ub_u256_is_zero) _ _ _
      (TerminatingProgBoundedOn.seq_guestInv
        (TerminatingProgBoundedOn.ite_on
          (TerminatingProgBoundedOn.call_guestInv fb_fq_poly_submul _ _)
          (fun s hc _ => TerminatingProgBounded.straight _ rfl s hc))
        (fun s hc _ => TerminatingProgBounded.straight _ rfl s hc)))

theorem polyCofactorLoop_bounded : TerminatingProgBoundedOn GuestInv polyCofactorLoop
    (14 * (polyCofactorBodyCost+1)) :=
  while_up_unsigned_const_on (ofString "j") 13 polyCofactorBody_bounded polyCofactorBody_counter

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
