import InitECandidate.Solver.Wave8GuestInv.LeafStatements
import InitECandidate.Solver.Wave8GuestInv.Shards.S06.LoopFree
import InitECandidate.Solver.Wave8GuestInv.Shards.S06.IncorporateSuccess
import InitECandidate.Solver.Wave8GuestInv.Shards.S06.StateRestore
import InitECandidate.Solver.Wave8GuestInv.Shards.S06.TaylorExp

/-! Axiom and exact statement checks for all 24 leaves in shard s06 (`wave8/leaves-s06`).

Each `example : type_of% ... = ... := rfl` verifies that our theorem proves the exact spec
statement of the corresponding leaf in `campaign/specs-proposed/GuestInv.lean` (modulo explicit
hypotheses for any cross-shard callee leaves it calls).

Each `#print axioms` checks that the proof uses only standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`), with no `sorryAx` or `Lean.ofReduceBool`.
-/

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8GuestInv.S06

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.Wave8GuestInv

instance : GuestInvLike (@Wave8GuestInv.GuestInv) where
  congr hc hm hsh hb h := Wave8GuestInv.guestInv_congr hc hm hsh hb h

-- 1. fb_incorporate_child_on_error (idx 591)
example : type_of% (fb_incorporate_child_on_error (GuestInv := @Wave8GuestInv.GuestInv)) =
    type_of% @Wave8GuestInv.fb_incorporate_child_on_error := rfl

-- 2. fb_incorporate_child_on_success (idx 592)
example : type_of% (fb_incorporate_child_on_success_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (TerminatingFunBoundedOn GuestInv
       (ofString "incorporate_child_on_error") K.«incorporate_child_on_error» →
     TerminatingFunBoundedOn GuestInv (ofString "log_append") K.«log_append» →
     TerminatingFunBoundedOn GuestInv (ofString "htab_union_into") K.«htab_union_into» →
     type_of% @Wave8GuestInv.fb_incorporate_child_on_success) := rfl

-- 3. fb_pc_add (idx 468)
example : type_of% (fb_pc_add (GuestInv := @Wave8GuestInv.GuestInv)) =
    type_of% @Wave8GuestInv.fb_pc_add := rfl

-- 4. fb_set_retdata (idx 595)
example : type_of% (fb_set_retdata_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy» →
     type_of% @Wave8GuestInv.fb_set_retdata) := rfl

-- 5. fb_stack_push (idx 454)
example : type_of% (fb_stack_push_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy» →
     type_of% @Wave8GuestInv.fb_stack_push) := rfl

-- 6. fb_state_restore (idx 359)
example : type_of% (fb_state_restore_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set» →
     TerminatingFunBoundedOn GuestInv (ofString "htab_del") K.«htab_del» →
     type_of% @Wave8GuestInv.fb_state_restore) := rfl

-- 7. fb_frame_epilogue (idx 582)
example : type_of% (fb_frame_epilogue_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (TerminatingFunBoundedOn GuestInv (ofString "state_restore") K.«state_restore» →
     type_of% @Wave8GuestInv.fb_frame_epilogue) := rfl

-- 8. fb_stack_pop (idx 453)
example : type_of% (fb_stack_pop (GuestInv := @Wave8GuestInv.GuestInv)) =
    type_of% @Wave8GuestInv.fb_stack_pop := rfl

-- 9. fb_op_add (idx 475)
example : type_of% (fb_op_add_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas» →
     TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop» →
     TerminatingFunBoundedOn GuestInv (ofString "u256_add") K.«u256_add» →
     TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push» →
     TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add» →
     type_of% @Wave8GuestInv.fb_op_add) := rfl

-- 10. fb_op_addmod (idx 482)
example : type_of% (fb_op_addmod_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas» →
     TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop» →
     TerminatingFunBoundedOn GuestInv (ofString "u256_addmod") K.«u256_addmod» →
     TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push» →
     TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add» →
     type_of% @Wave8GuestInv.fb_op_addmod) := rfl

-- 11. fb_op_address (idx 531)
example : type_of% (fb_op_address_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas» →
     TerminatingFunBoundedOn GuestInv (ofString "address_to_u256") K.«address_to_u256» →
     TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push» →
     TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add» →
     type_of% @Wave8GuestInv.fb_op_address) := rfl

-- 12. fb_op_and (idx 492)
example : type_of% (fb_op_and_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas» →
     TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop» →
     TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push» →
     TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add» →
     type_of% @Wave8GuestInv.fb_op_and) := rfl

-- 13. fb_to_address_masked (idx 444)
example : type_of% (fb_to_address_masked (GuestInv := @Wave8GuestInv.GuestInv)) =
    type_of% @Wave8GuestInv.fb_to_address_masked := rfl

-- 14. fb_warm_after_charge (idx 474)
example : type_of% (fb_warm_after_charge_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (TerminatingFunBoundedOn GuestInv (ofString "warm_address") K.«warm_address» →
     type_of% @Wave8GuestInv.fb_warm_after_charge) := rfl

-- 15. fb_op_balance (idx 532)
example : type_of% (fb_op_balance_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop» →
     TerminatingFunBoundedOn GuestInv (ofString "to_address_masked") K.«to_address_masked» →
     TerminatingFunBoundedOn GuestInv (ofString "access_gas_cost") K.«access_gas_cost» →
     TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas» →
     TerminatingFunBoundedOn GuestInv (ofString "warm_after_charge") K.«warm_after_charge» →
     TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account» →
     TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push» →
     TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add» →
     type_of% @Wave8GuestInv.fb_op_balance) := rfl

-- 16. fb_block_env (idx 550)
example : type_of% (fb_block_env (GuestInv := @Wave8GuestInv.GuestInv)) =
    type_of% @Wave8GuestInv.fb_block_env := rfl

-- 17. fb_op_basefee (idx 551)
example : type_of% (fb_op_basefee_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas» →
     TerminatingFunBoundedOn GuestInv (ofString "block_env") K.«block_env» →
     TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push» →
     TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add» →
     type_of% @Wave8GuestInv.fb_op_basefee) := rfl

-- 18. fb_taylor_exponential (idx 232)
example : type_of% (fb_taylor_exponential_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (TerminatingFunBoundedOn GuestInv (ofString "u256_from_word") K.«u256_from_word» →
     TerminatingFunBoundedOn GuestInv (ofString "u256_mul") K.«u256_mul» →
     TerminatingFunBoundedOn GuestInv (ofString "u256_is_zero") K.«u256_is_zero» →
     TerminatingFunBoundedOn GuestInv (ofString "u256_add") K.«u256_add» →
     TerminatingFunBoundedOn GuestInv (ofString "u256_mul_full") K.«u256_mul_full» →
     TerminatingFunBoundedOn GuestInv (ofString "trap_with") K.«trap_with» →
     TerminatingFunBoundedOn GuestInv (ofString "u256_div") K.«u256_div» →
     type_of% @Wave8GuestInv.fb_taylor_exponential) := rfl

-- 19. fb_calculate_blob_gas_price (idx 233)
example : type_of% (fb_calculate_blob_gas_price_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (TerminatingFunBoundedOn GuestInv (ofString "taylor_exponential") K.«taylor_exponential» →
     type_of% @Wave8GuestInv.fb_calculate_blob_gas_price) := rfl

-- 20. fb_op_blobbasefee (idx 553)
example : type_of% (fb_op_blobbasefee_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas» →
     TerminatingFunBoundedOn GuestInv (ofString "block_env") K.«block_env» →
     TerminatingFunBoundedOn GuestInv (ofString "calculate_blob_gas_price") K.«calculate_blob_gas_price» →
     TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push» →
     TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add» →
     type_of% @Wave8GuestInv.fb_op_blobbasefee) := rfl

-- 21. fb_op_blobhash (idx 552)
example : type_of% (fb_op_blobhash_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas» →
     TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop» →
     TerminatingFunBoundedOn GuestInv (ofString "sat_word") K.«sat_word» →
     TerminatingFunBoundedOn GuestInv (ofString "u256_from_be") K.«u256_from_be» →
     TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push» →
     TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add» →
     type_of% @Wave8GuestInv.fb_op_blobhash) := rfl

-- 22. fb_track_ancestor_access (idx 402)
example : type_of% (fb_track_ancestor_access (GuestInv := @Wave8GuestInv.GuestInv)) =
    type_of% @Wave8GuestInv.fb_track_ancestor_access := rfl

-- 23. fb_op_blockhash (idx 554)
example : type_of% (fb_op_blockhash_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop» →
     TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas» →
     TerminatingFunBoundedOn GuestInv (ofString "block_env") K.«block_env» →
     TerminatingFunBoundedOn GuestInv (ofString "sat_word") K.«sat_word» →
     TerminatingFunBoundedOn GuestInv (ofString "u256_from_be") K.«u256_from_be» →
     TerminatingFunBoundedOn GuestInv (ofString "track_ancestor_access") K.«track_ancestor_access» →
     TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push» →
     TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add» →
     type_of% @Wave8GuestInv.fb_op_blockhash) := rfl

-- 24. fb_stack_push_word (idx 455)
example : type_of% (fb_stack_push_word_of (GuestInv := @Wave8GuestInv.GuestInv)) =
    (TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push» →
     type_of% @Wave8GuestInv.fb_stack_push_word) := rfl

end InitECandidate.Solver.Wave8GuestInv.S06
