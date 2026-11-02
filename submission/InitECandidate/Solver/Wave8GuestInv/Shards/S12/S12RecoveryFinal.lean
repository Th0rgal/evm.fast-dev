import InitECandidate.Solver.Wave8GuestInv.Shards.S12.S12RecoveryMore

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

theorem «fb_recover_transaction_public_key»
    (hmark : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark»)
    (halloc : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hsig : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "signature_recovery_parameters") K.«signature_recovery_parameters»)
    (hsecp : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "secp256k1_recover") K.«secp256k1_recover»)
    (hrelease : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release») :
    Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "recover_transaction_public_key") K.«recover_transaction_public_key» := by
  fb_unfold 340 Guest.Software.guestFn_recover_transaction_public_key
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.decCall_guestInv hmark
    apply TerminatingProgBoundedOn.decCall_guestInv halloc
    apply TerminatingProgBoundedOn.decCall_guestInv hsig
    apply TerminatingProgBoundedOn.decCall_guestInv hsecp
    apply seq_meta s12_metadataInv_guestInv
    · apply TerminatingProgBoundedOn.call_guestInv hrelease
    · apply seq_meta s12_metadataInv_guestInv
      · apply ite_meta
        · exact s12_straightOn _ rfl
        · exact s12_straightOn _ rfl
      · exact s12_straightOn _ rfl
  · unfold K.«recover_transaction_public_key»
    omega

end InitECandidate.Solver.Wave8Leaves.S12
