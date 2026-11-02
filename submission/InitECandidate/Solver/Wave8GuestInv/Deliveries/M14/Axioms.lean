import InitECandidate.Solver.Wave8GuestInv.Contracts
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_calculate_total_blob_gas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_check_gas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_check_gas_limit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_common_prefix_length
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_fee_mul
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_heap_mark

/-! Final gate (`Axioms.lean`) for contract micro-shard `m14` (`wave8/contracts-m14`),
checked against frozen spec revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

Every `example` verifies definitional equality (`rfl`) of `type_of%` against the corresponding
spec contract statement in `InitECandidate.Solver.Wave8GuestInv`.
Every `#print axioms` output must show only `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Contracts.M14

-- 1. ro_calculate_total_blob_gas
example : (type_of% @ro_calculate_total_blob_gas) =
    (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_calculate_total_blob_gas) := rfl

-- 2. ro_check_gas
example : (type_of% @ro_check_gas) =
    (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_check_gas) := rfl

-- 3. ro_check_gas_limit
example : (type_of% @ro_check_gas_limit) =
    (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_check_gas_limit) := rfl

-- 4. ro_common_prefix_length
example : (type_of% @ro_common_prefix_length) =
    (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_common_prefix_length) := rfl

-- 5. ro_fee_mul
example : (type_of% @ro_fee_mul) =
    (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_fee_mul) := rfl

-- 6. ro_heap_mark
example : (type_of% @ro_heap_mark) =
    (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_heap_mark) := rfl


end InitECandidate.Solver.Wave8Contracts.M14
