import InitECandidate.Solver.Wave8GuestInv.Shards.S12.S12More

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

theorem «fb_encode_transaction»
    (hgeneric : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "tx_encode_generic") K.«tx_encode_generic») :
    Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "encode_transaction") K.«encode_transaction» := by
  fb_unfold 329 Guest.Software.guestFn_encode_transaction
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.tailCall_guestInv hgeneric
  · unfold K.«encode_transaction»
    omega

theorem «fb_tx_put_to»
    (hrlp : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.«rlp_encode_bytes») :
    Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "tx_put_to") K.«tx_put_to» := by
  fb_unfold 320 Guest.Software.guestFn_tx_put_to
  apply TerminatingProgBoundedOn.weaken'
  · apply seq_meta s12_metadataInv_guestInv
    · apply ite_meta
      · exact s12_straightOn _ rfl
      · exact s12_straightOn _ rfl
    · apply TerminatingProgBoundedOn.tailCall_guestInv hrlp
  · unfold K.«tx_put_to»
    omega

theorem «fb_tx_signing_hash_mode»
    (hmark : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark»)
    (hencode : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "tx_encode_generic") K.«tx_encode_generic»)
    (hkeccak : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»)
    (hrelease : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release») :
    Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "tx_signing_hash_mode") K.«tx_signing_hash_mode» := by
  fb_unfold 331 Guest.Software.guestFn_tx_signing_hash_mode
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.decCall_guestInv hmark
    apply TerminatingProgBoundedOn.decCall_guestInv hencode
    apply seq_meta s12_metadataInv_guestInv
    · apply TerminatingProgBoundedOn.call_guestInv hkeccak
    · apply seq_meta s12_metadataInv_guestInv
      · apply TerminatingProgBoundedOn.call_guestInv hrelease
      · exact s12_straightOn _ rfl
  · unfold K.«tx_signing_hash_mode»
    omega

theorem «fb_tx_put_u256»
    (hmark : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark»)
    (halloc : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hbe : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "u256_to_be_min") K.«u256_to_be_min»)
    (hrlp : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.«rlp_encode_bytes»)
    (hrelease : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release») :
    Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "tx_put_u256") K.«tx_put_u256» := by
  fb_unfold 318 Guest.Software.guestFn_tx_put_u256
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.decCall_guestInv hmark
    apply TerminatingProgBoundedOn.decCall_guestInv halloc
    apply TerminatingProgBoundedOn.decCall_guestInv hbe
    apply TerminatingProgBoundedOn.decCall_guestInv hrlp
    apply seq_meta s12_metadataInv_guestInv
    · apply TerminatingProgBoundedOn.call_guestInv hrelease
    · exact s12_straightOn _ rfl
  · unfold K.«tx_put_u256»
    omega

theorem «fb_set_account_balance»
    (hget : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account»)
    (hcopy : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "acct_copy") K.«acct_copy»)
    (hcommit : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "modify_state_commit") K.«modify_state_commit») :
    Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "set_account_balance") K.«set_account_balance» := by
  fb_unfold 397 Guest.Software.guestFn_set_account_balance
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.decCall_guestInv hget
    apply seq_meta s12_metadataInv_guestInv
    · apply TerminatingProgBoundedOn.call_guestInv hcopy
    · apply seq_meta s12_metadataInv_guestInv
      · exact s12_straightOn _ rfl
      · apply seq_meta s12_metadataInv_guestInv
        · apply TerminatingProgBoundedOn.call_guestInv hcommit
        · exact s12_straightOn _ rfl
  · unfold K.«set_account_balance»
    omega

end InitECandidate.Solver.Wave8Leaves.S12
