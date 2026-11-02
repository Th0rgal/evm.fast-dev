import InitECandidate.Solver.Wave8GuestInv.Shards.S08.Core

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S08

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem fb_compute_create2_contract_address
    (h_heap_mark : TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark»)
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (h_keccak256 : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»)
    (h_heap_release : TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release») :
    TerminatingFunBoundedOn GuestInv (ofString "compute_create2_contract_address") K.«compute_create2_contract_address» := by
  fb_prove 597 Guest.Software.guestFn_compute_create2_contract_address K.«compute_create2_contract_address»

theorem fb_compute_create2_contract_address_of
    (h_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (h_keccak256 : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256») :
    TerminatingFunBoundedOn GuestInv (ofString "compute_create2_contract_address") K.«compute_create2_contract_address» :=
  fb_compute_create2_contract_address on_heap_mark on_alloc h_memcpy h_keccak256 on_heap_release

example :
    type_of% Wave8GuestInv.«fb_heap_mark» →
    type_of% Wave8GuestInv.«fb_alloc» →
    type_of% Wave8GuestInv.«fb_memcpy» →
    type_of% Wave8GuestInv.«fb_keccak256» →
    type_of% Wave8GuestInv.«fb_heap_release» →
    type_of% Wave8GuestInv.«fb_compute_create2_contract_address» :=
  fb_compute_create2_contract_address

example :
    type_of% Wave8GuestInv.«fb_memcpy» →
    type_of% Wave8GuestInv.«fb_keccak256» →
    type_of% Wave8GuestInv.«fb_compute_create2_contract_address» :=
  fb_compute_create2_contract_address_of

end InitECandidate.Solver.Wave8Leaves.S08
