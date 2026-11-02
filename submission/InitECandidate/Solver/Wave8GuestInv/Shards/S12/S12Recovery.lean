import InitECandidate.Solver.Wave8GuestInv.Shards.S12.S12Transactions

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

theorem «fb_recover_sender_with_chain_id»
    (hmark : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark»)
    (halloc : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hpub : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "recover_transaction_public_key") K.«recover_transaction_public_key»)
    (hsender : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "sender_address_from_public_key") K.«sender_address_from_public_key»)
    (hrelease : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release») :
    Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "recover_sender_with_chain_id") K.«recover_sender_with_chain_id» := by
  fb_unfold 343 Guest.Software.guestFn_recover_sender_with_chain_id
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.decCall_guestInv hmark
    apply TerminatingProgBoundedOn.decCall_guestInv halloc
    apply seq_meta s12_metadataInv_guestInv
    · exact s12_straightOn _ rfl
    · apply seq_meta s12_metadataInv_guestInv
      · apply TerminatingProgBoundedOn.call_guestInv hpub
      · apply seq_meta s12_metadataInv_guestInv
        · apply TerminatingProgBoundedOn.call_guestInv hsender
        · apply seq_meta s12_metadataInv_guestInv
          · apply TerminatingProgBoundedOn.call_guestInv hrelease
          · exact s12_straightOn _ rfl
  · unfold K.«recover_sender_with_chain_id»
    omega

end InitECandidate.Solver.Wave8Leaves.S12
