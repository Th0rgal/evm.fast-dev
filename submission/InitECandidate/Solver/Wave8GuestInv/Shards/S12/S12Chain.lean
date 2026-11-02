import InitECandidate.Solver.Wave8GuestInv.Shards.S12.S12RecoveryFinal

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

theorem «fb_tx_chain_id»
    (hfits : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "u256_fits_word") K.«u256_fits_word»)
    (hsub : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "u256_sub") K.«u256_sub»)
    (hshr : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "u256_shr") K.«u256_shr») :
    Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "tx_chain_id") K.«tx_chain_id» := by
  fb_unfold 338 Guest.Software.guestFn_tx_chain_id
  apply TerminatingProgBoundedOn.weaken'
  · apply seq_meta s12_metadataInv_guestInv
    · apply ite_meta
      · exact s12_straightOn _ rfl
      · exact s12_straightOn _ rfl
    · apply dec_meta s12_metadataInv_guestInv
      apply TerminatingProgBoundedOn.decCall_guestInv hfits
      apply seq_meta s12_metadataInv_guestInv
      · apply ite_meta
        · apply seq_meta s12_metadataInv_guestInv
          · apply ite_meta <;> exact s12_straightOn _ rfl
          · apply ite_meta <;> exact s12_straightOn _ rfl
        · exact s12_straightOn _ rfl
      · apply TerminatingProgBoundedOn.decCall_guestInv hsub
        apply TerminatingProgBoundedOn.decCall_guestInv hshr
        apply seq_meta s12_metadataInv_guestInv
        · apply TerminatingProgBoundedOn.call_guestInv hfits
        · apply seq_meta s12_metadataInv_guestInv
          · apply ite_meta <;> exact s12_straightOn _ rfl
          · exact s12_straightOn _ rfl
  · unfold K.«tx_chain_id»
    omega

end InitECandidate.Solver.Wave8Leaves.S12
