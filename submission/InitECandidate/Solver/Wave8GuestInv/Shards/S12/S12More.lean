import InitECandidate.Solver.Wave8GuestInv.Shards.S12.S12Simple
import InitECandidate.Solver.Wave8GuestInv.Shards.S15.Core

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

theorem s12_metadataInv_guestInv :
    InitECandidate.Solver.Wave8Leaves.S15.MetadataInv (@GuestInv) :=
  fun hcode hmem hsh hbase h => guestInv_congr hcode hmem hsh hbase h

open InitECandidate.Solver.Wave8Leaves.S15

theorem «fb_udiv_small5»
    (hudiv : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "udiv") K.«udiv») :
    Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "udiv_small5") K.«udiv_small5» := by
  fb_unfold 874 Guest.Software.guestFn_udiv_small5
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.decCall_guestInv hudiv
    exact s12_straightOn _ rfl
  · unfold K.«udiv_small5»
    omega

theorem «fb_signing_hash_pre155»
    (hmode : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "tx_signing_hash_mode")
      K.«tx_signing_hash_mode») :
    Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "signing_hash_pre155")
      K.«signing_hash_pre155» := by
  fb_unfold 332 Guest.Software.guestFn_signing_hash_pre155
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.tailCall_guestInv hmode
  · unfold K.«signing_hash_pre155»
    omega

theorem «fb_signing_hash_155»
    (hmode : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "tx_signing_hash_mode") K.«tx_signing_hash_mode») :
    Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "signing_hash_155") K.«signing_hash_155» := by
  fb_unfold 333 Guest.Software.guestFn_signing_hash_155
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.tailCall_guestInv hmode
  · unfold K.«signing_hash_155»
    omega

theorem «fb_signing_hash_2930»
    (hmode : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "tx_signing_hash_mode") K.«tx_signing_hash_mode») :
    Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "signing_hash_2930") K.«signing_hash_2930» := by
  fb_unfold 334 Guest.Software.guestFn_signing_hash_2930
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.tailCall_guestInv hmode
  · unfold K.«signing_hash_2930»
    omega

theorem «fb_signing_hash_1559»
    (hmode : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "tx_signing_hash_mode") K.«tx_signing_hash_mode») :
    Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "signing_hash_1559") K.«signing_hash_1559» := by
  fb_unfold 335 Guest.Software.guestFn_signing_hash_1559
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.tailCall_guestInv hmode
  · unfold K.«signing_hash_1559»
    omega

theorem «fb_signing_hash_4844»
    (hmode : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "tx_signing_hash_mode") K.«tx_signing_hash_mode») :
    Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "signing_hash_4844") K.«signing_hash_4844» := by
  fb_unfold 336 Guest.Software.guestFn_signing_hash_4844
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.tailCall_guestInv hmode
  · unfold K.«signing_hash_4844»
    omega

theorem «fb_signing_hash_7702»
    (hmode : Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "tx_signing_hash_mode") K.«tx_signing_hash_mode») :
    Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "signing_hash_7702") K.«signing_hash_7702» := by
  fb_unfold 337 Guest.Software.guestFn_signing_hash_7702
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.tailCall_guestInv hmode
  · unfold K.«signing_hash_7702»
    omega

end InitECandidate.Solver.Wave8Leaves.S12
