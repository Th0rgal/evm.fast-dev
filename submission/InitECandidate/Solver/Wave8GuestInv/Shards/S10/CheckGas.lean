import InitECandidate.Solver.Wave8GuestInv.Shards.S10.Helpers

set_option maxRecDepth 1000000

namespace InitECandidate.Solver.Wave8Leaves.S10

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.PanTerminatingBounded

theorem fb_check_gas :
    TerminatingFunBoundedOn GuestInv (ofString "check_gas") K.«check_gas» := by
  fb_prove 447 Guest.Software.guestFn_check_gas K.«check_gas»

example : type_of% fb_check_gas =
    TerminatingFunBoundedOn GuestInv (ofString "check_gas") K.«check_gas» := rfl

end InitECandidate.Solver.Wave8Leaves.S10
