import InitECandidate.Solver.Wave8GuestInv.Shards.S02.Base
import InitECandidate.Solver.Wave8GuestInv.Shards.S02.RlpPut

namespace InitECandidate.Solver.Wave8GuestInv.S02

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE InitECandidate.Solver.Wave8GuestInv

set_option maxRecDepth 5000 in
example
    (h1 : TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark»)
    (h2 : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h3 : TerminatingFunBoundedOn GuestInv (ofString "u256_to_be_min") K.«u256_to_be_min»)
    (h4 : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.«rlp_encode_bytes»)
    (h5 : TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release») :
    type_of% (fb_rlp_put_u256 h1 h2 h3 h4 h5) =
      type_of% InitECandidate.Solver.Wave8GuestInv.«fb_rlp_put_u256» := rfl


end InitECandidate.Solver.Wave8GuestInv.S02
