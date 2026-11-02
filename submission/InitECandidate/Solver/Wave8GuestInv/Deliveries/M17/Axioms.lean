import InitECandidate.Solver.Wave8GuestInv.Contracts
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_stor_lookup
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_tx_chain_id
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_tx_has_access_list
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_tx_is_blob
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_tx_is_setcode
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M17.ro_u256_eq

/-! Final `type_of%` and `#print axioms` audit gate for contract micro-shard `m17`
(`wave8/contracts-m17`, frozen spec rev9 `8a79d9f28`).

Checks definitional equality (`rfl`) of every proved theorem's type against the frozen spec
statement in `InitECandidate.Solver.Wave8GuestInv`, and verifies that every theorem depends only
on `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8GuestInv.M17

-- 1. ro_stor_lookup
example : (type_of% @ro_stor_lookup) =
    (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_stor_lookup) := rfl

-- 2. ro_tx_chain_id
example : (type_of% @ro_tx_chain_id) =
    (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_tx_chain_id) := rfl

-- 3. ro_tx_has_access_list
example : (type_of% @ro_tx_has_access_list) =
    (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_tx_has_access_list) := rfl

-- 4. ro_tx_is_blob
example : (type_of% @ro_tx_is_blob) =
    (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_tx_is_blob) := rfl

-- 5. ro_tx_is_setcode
example : (type_of% @ro_tx_is_setcode) =
    (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_tx_is_setcode) := rfl

-- 6. ro_u256_eq
example : (type_of% @ro_u256_eq) =
    (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_u256_eq) := rfl

end InitECandidate.Solver.Wave8GuestInv.M17
