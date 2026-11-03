import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.PositiveHalfLoop
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.Composed

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators

private def decCallBody : ProgHOL 64 → ProgHOL 64
  | .decCall _ _ _ _ body => body | _ => .skip
private def decBody : ProgHOL 64 → ProgHOL 64
  | .dec _ _ _ body => body | _ => .skip
private def seqLeft : ProgHOL 64 → ProgHOL 64
  | .seq body _ => body | _ => .skip
private def seqRight : ProgHOL 64 → ProgHOL 64
  | .seq _ body => body | _ => .skip
private def whileBody : ProgHOL 64 → ProgHOL 64
  | .while _ body => body | _ => .skip

def inverseOuterLoop : ProgHOL 64 :=
  seqLeft (decBody (decBody (decBody (decBody (seqRight
    (decCallBody (arithSourceBody Guest.Software.guestFn_modinv_bin)))))))

def inverseOuterBody : ProgHOL 64 := whileBody inverseOuterLoop

def inverseUHalfLoop : ProgHOL 64 := seqLeft (seqRight (seqRight inverseOuterBody))
def inverseVHalfLoop : ProgHOL 64 := seqLeft (seqRight (seqRight (seqRight inverseOuterBody)))

theorem inverseOuterLoop_eq : inverseOuterLoop = .while (.const 1) inverseOuterBody := rfl

theorem inverseUHalfLoop_eq : inverseUHalfLoop =
    .while (inverseEvenExpr (ofString "u"))
      (.seq (.assign .local (ofString "u") (inverseHalfExpr (ofString "u")))
        (.call (some (some (.local, ofString "x1"), none)) (ofString "mod_half")
          [.var .local (ofString "x1"), .var .local (ofString "m")])) := rfl

theorem inverseVHalfLoop_eq : inverseVHalfLoop =
    .while (inverseEvenExpr (ofString "v"))
      (.seq (.assign .local (ofString "v") (inverseHalfExpr (ofString "v")))
        (.call (some (some (.local, ofString "x2"), none)) (ofString "mod_half")
          [.var .local (ofString "x2"), .var .local (ofString "m")])) := rfl

theorem inverseUHalf_positive :
    TerminatingProgBoundedOn (inversePositive (ofString "u")) inverseUHalfLoop
      ((256 + 1) * ((K.«mod_half» + 1) + 1)) := by
  rw [inverseUHalfLoop_eq]
  exact while_inverse_half_positive _ (TerminatingProgBounded.call ub_mod_half _ _) (by decide)

theorem inverseVHalf_positive :
    TerminatingProgBoundedOn (inversePositive (ofString "v")) inverseVHalfLoop
      ((256 + 1) * ((K.«mod_half» + 1) + 1)) := by
  rw [inverseVHalfLoop_eq]
  exact while_inverse_half_positive _ (TerminatingProgBounded.call ub_mod_half _ _) (by decide)
end InitECandidate.Solver.Wave8GuestInv.Arith
