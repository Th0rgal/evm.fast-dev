import InitECandidate.Solver.Wave8GuestInv.Shards.S09.Core

/-! Proof for `fb_is_valid_jumpdest` (shard s09). -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S09

open Flapjack.Basis.Pure.MlString
variable {GuestInv : ∀ {F : Type}, Flapjack.PanSemStateFiniteExact 64 F → Prop} [IsGuestInv GuestInv]

theorem fb_is_valid_jumpdest :
    TerminatingFunBoundedOn GuestInv (ofString "is_valid_jumpdest") K.«is_valid_jumpdest» := by
  fb_prove 464 Guest.Software.guestFn_is_valid_jumpdest K.«is_valid_jumpdest»


end InitECandidate.Solver.Wave8Leaves.S09
