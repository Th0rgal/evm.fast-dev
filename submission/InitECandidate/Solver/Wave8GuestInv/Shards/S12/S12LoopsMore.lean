import InitECandidate.Solver.Wave8GuestInv.Shards.S12.S12Loops

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
open InitECandidate.Solver.Wave8Leaves.S14

theorem «fb_count_tokens_in_data» :
    Wave8GuestInv.TerminatingFunBoundedOn GuestInv (ofString "count_tokens_in_data") K.«count_tokens_in_data» := by
  fb_unfold 344 Guest.Software.guestFn_count_tokens_in_data
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_meta s12_s14_metadata
    apply dec_meta s12_s14_metadata
    apply seq_meta s12_s14_metadata
    · apply while_counter_meta s12_s14_metadata .lower (Or.inr rfl)
      · apply seq_meta s12_s14_metadata
        · apply ite_meta <;> exact straightOn _ rfl
        · exact straightOn _ rfl
      · incr_body
      · rfl
    · exact straightOn _ rfl
  · unfold K.«count_tokens_in_data»
    omega

end InitECandidate.Solver.Wave8Leaves.S12
