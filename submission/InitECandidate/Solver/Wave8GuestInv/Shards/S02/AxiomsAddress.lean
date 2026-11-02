import InitECandidate.Solver.Wave8GuestInv.Shards.S02.Base
import InitECandidate.Solver.Wave8GuestInv.Shards.S02.Simple

namespace InitECandidate.Solver.Wave8GuestInv.S02

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE InitECandidate.Solver.Wave8GuestInv

example (h : TerminatingFunBoundedOn GuestInv (ofString "u256_from_be") K.«u256_from_be») :
    type_of% (fb_address_to_u256 h) =
      type_of% InitECandidate.Solver.Wave8GuestInv.«fb_address_to_u256» := rfl


end InitECandidate.Solver.Wave8GuestInv.S02
