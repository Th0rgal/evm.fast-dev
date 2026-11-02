import InitECandidate.Solver.Wave8GuestInv.Shards.S12.S12Recovery

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S12

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8Leaves.S15

theorem «fb_sender_address_from_public_key»
    (hmark : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark»)
    (halloc : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hkeccak : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»)
    (hmemcpy : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (hrelease : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release») :
    Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "sender_address_from_public_key") K.«sender_address_from_public_key» := by
  fb_unfold 341 Guest.Software.guestFn_sender_address_from_public_key
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.decCall_guestInv hmark
    apply TerminatingProgBoundedOn.decCall_guestInv halloc
    apply seq_meta s12_metadataInv_guestInv
    · apply TerminatingProgBoundedOn.call_guestInv hkeccak
    · apply seq_meta s12_metadataInv_guestInv
      · apply TerminatingProgBoundedOn.call_guestInv hmemcpy
      · apply seq_meta s12_metadataInv_guestInv
        · apply TerminatingProgBoundedOn.call_guestInv hrelease
        · exact s12_straightOn _ rfl
  · unfold K.«sender_address_from_public_key»
    omega

end InitECandidate.Solver.Wave8Leaves.S12
