import InitECandidate.Solver.Wave8GuestInv.Shards.S12.S12RecoveryFinal
import InitECandidate.Solver.Wave8GuestInv.Shards.S14.Core

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

theorem s12_s14_metadata : InitECandidate.Solver.Wave8Leaves.S14.MetadataInv (@GuestInv) :=
  fun hcode hmem hsh hbase h => guestInv_congr hcode hmem hsh hbase h

open InitECandidate.Solver.Wave8Leaves.S14

theorem «fb_tx_put_blob_hashes»
    (hheader : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_list_header") K.«rlp_encode_list_header»)
    (hbytes : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.«rlp_encode_bytes») :
    Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "tx_put_blob_hashes") K.«tx_put_blob_hashes» := by
  fb_unfold 323 Guest.Software.guestFn_tx_put_blob_hashes
  apply TerminatingProgBoundedOn.weaken'
  · apply decCall_meta s12_s14_metadata hheader
    apply dec_meta s12_s14_metadata
    apply dec_meta s12_s14_metadata
    apply seq_meta s12_s14_metadata
    · apply while_counter_meta s12_s14_metadata .lower (Or.inr rfl)
      · apply seq_meta s12_s14_metadata
        · apply TerminatingProgBoundedOn.call_guestInv hbytes
        · exact straightOn _ rfl
      · incr_body
      · rfl
    · exact straightOn _ rfl
  · unfold K.«tx_put_blob_hashes»
    omega

end InitECandidate.Solver.Wave8Leaves.S12
