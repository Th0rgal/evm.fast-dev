import InitECandidate.Solver.Wave8GuestInv.Shards.S09.Core

/-! Proof for `fb_op_jump` (shard s09). -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S09

open Flapjack.Basis.Pure.MlString
variable {GuestInv : ∀ {F : Type}, Flapjack.PanSemStateFiniteExact 64 F → Prop} [IsGuestInv GuestInv]

theorem fb_op_jump
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_is_valid_jumpdest : TerminatingFunBoundedOn GuestInv (ofString "is_valid_jumpdest") K.«is_valid_jumpdest»)
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop») :
    TerminatingFunBoundedOn GuestInv (ofString "op_jump") K.«op_jump» := by
  fb_prove 503 Guest.Software.guestFn_op_jump K.«op_jump»


end InitECandidate.Solver.Wave8Leaves.S09
