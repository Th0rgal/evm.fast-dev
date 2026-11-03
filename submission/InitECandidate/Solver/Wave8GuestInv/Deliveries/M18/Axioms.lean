import InitECandidate.Solver.Wave8GuestInv.Contracts
import InitECandidate.Solver.Wave8GuestInv.ContractParts.C08
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_is_zero
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_mul
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_u256_sub
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_udiv_small5
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_validate_block_access_list_gas_limit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.ro_validate_transaction

/-! Final gate (`Axioms.lean`) for contract micro-shard `m18` (`wave8/contracts-m18`),
checked against frozen spec revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

Every `example` verifies definitional equality (`rfl`) of `type_of%` against the corresponding
spec contract statement in `InitECandidate.Solver.Wave8GuestInv`.
Every `#print axioms` output must show only `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Contracts.M18

-- 1. ro_u256_is_zero
example : (type_of% @ro_u256_is_zero) = (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_u256_is_zero) := rfl

-- 2. ro_u256_mul
example : (type_of% @ro_u256_mul) = (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_u256_mul) := rfl

-- 3. ro_u256_sub
example : (type_of% @ro_u256_sub) = (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_u256_sub) := rfl

-- 4. ro_udiv_small5
example : (type_of% @ro_udiv_small5) = (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_udiv_small5) := rfl

-- 5. ro_validate_block_access_list_gas_limit
example : (type_of% @ro_validate_block_access_list_gas_limit) = (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_validate_block_access_list_gas_limit) := rfl

-- 6. ro_validate_transaction
example : (type_of% @ro_validate_transaction) = (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_validate_transaction) := rfl


end InitECandidate.Solver.Wave8Contracts.M18
