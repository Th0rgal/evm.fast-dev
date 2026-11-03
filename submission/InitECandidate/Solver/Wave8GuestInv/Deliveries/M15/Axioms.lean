import InitECandidate.Solver.Wave8GuestInv.Contracts
import InitECandidate.Solver.Wave8GuestInv.ContractParts.C08
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_get
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_has
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_htab_item
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_max
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_memeq
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_min

/-! Final gate (`Axioms.lean`) for contract micro-shard `m15` (`wave8/contracts-m15`),
checked against frozen spec revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

Every `example` verifies definitional equality (`rfl`) of `type_of%` against the corresponding
spec contract statement in `InitECandidate.Solver.Wave8GuestInv`.
Every `#print axioms` output must show only `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Contracts.M15

-- 1. ro_htab_get
example : (type_of% @ro_htab_get) = (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_htab_get) := rfl

-- 2. ro_htab_has
example : (type_of% @ro_htab_has) = (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_htab_has) := rfl

-- 3. ro_htab_item
example : (type_of% @ro_htab_item) = (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_htab_item) := rfl

-- 4. ro_max
example : (type_of% @ro_max) = (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_max) := rfl

-- 5. ro_memeq
example : (type_of% @ro_memeq) = (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_memeq) := rfl

-- 6. ro_min
example : (type_of% @ro_min) = (type_of% @InitECandidate.Solver.Wave8GuestInv.ro_min) := rfl


end InitECandidate.Solver.Wave8Contracts.M15
