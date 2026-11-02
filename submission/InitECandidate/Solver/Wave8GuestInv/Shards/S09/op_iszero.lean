import InitECandidate.Solver.Wave8GuestInv.Shards.S09.Core

/-! Proof for `fb_op_iszero` (shard s09). -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S09

open Flapjack.Basis.Pure.MlString
variable {GuestInv : ∀ {F : Type}, Flapjack.PanSemStateFiniteExact 64 F → Prop} [IsGuestInv GuestInv]

theorem fb_op_iszero
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_pc_add : TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add»)
    (h_stack_pop : TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop»)
    (h_stack_push_bool : TerminatingFunBoundedOn GuestInv (ofString "stack_push_bool") K.«stack_push_bool»)
    (h_u256_is_zero : TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero») :
    TerminatingFunBoundedOn GuestInv (ofString "op_iszero") K.«op_iszero» := by
  fb_prove 491 Guest.Software.guestFn_op_iszero K.«op_iszero»


end InitECandidate.Solver.Wave8Leaves.S09
