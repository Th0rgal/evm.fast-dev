import InitECandidate.Solver.Wave8GuestInv.Contracts
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_calculate_total_blob_gas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_check_gas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_check_gas_limit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_common_prefix_length
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_fee_mul
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_heap_mark

namespace InitECandidate.Solver.Wave8GuestInv.R10Ports
set_option autoImplicit false

theorem ro_calculate_total_blob_gas : type_of% InitECandidate.Solver.Wave8GuestInv.ro_calculate_total_blob_gas := by
  rcases InitECandidate.Solver.Wave8Contracts.M14.ro_calculate_total_blob_gas with ⟨ps, body, ret, hl, hrun⟩
  refine ⟨ps, body, ret, hl, ?_⟩
  intro F s hc hp _ hnt
  exact hrun s hc hp hnt
#print axioms ro_calculate_total_blob_gas

theorem ro_check_gas : type_of% InitECandidate.Solver.Wave8GuestInv.ro_check_gas := by
  rcases InitECandidate.Solver.Wave8Contracts.M14.ro_check_gas with ⟨ps, body, ret, hl, hrun⟩
  refine ⟨ps, body, ret, hl, ?_⟩
  intro F s hc hp _ hnt
  exact hrun s hc hp hnt
#print axioms ro_check_gas

theorem ro_check_gas_limit : type_of% InitECandidate.Solver.Wave8GuestInv.ro_check_gas_limit := by
  rcases InitECandidate.Solver.Wave8Contracts.M14.ro_check_gas_limit with ⟨ps, body, ret, hl, hrun⟩
  refine ⟨ps, body, ret, hl, ?_⟩
  intro F s hc hp _ hnt
  exact hrun s hc hp hnt
#print axioms ro_check_gas_limit

theorem ro_common_prefix_length : type_of% InitECandidate.Solver.Wave8GuestInv.ro_common_prefix_length := by
  rcases InitECandidate.Solver.Wave8Contracts.M14.ro_common_prefix_length with ⟨ps, body, ret, hl, hrun⟩
  refine ⟨ps, body, ret, hl, ?_⟩
  intro F s hc hp _ hnt
  exact hrun s hc hp hnt
#print axioms ro_common_prefix_length

theorem ro_fee_mul : type_of% InitECandidate.Solver.Wave8GuestInv.ro_fee_mul := by
  rcases InitECandidate.Solver.Wave8Contracts.M14.ro_fee_mul with ⟨ps, body, ret, hl, hrun⟩
  refine ⟨ps, body, ret, hl, ?_⟩
  intro F s hc hp _ hnt
  exact hrun s hc hp hnt
#print axioms ro_fee_mul

theorem ro_heap_mark : type_of% InitECandidate.Solver.Wave8GuestInv.ro_heap_mark := by
  rcases InitECandidate.Solver.Wave8Contracts.M14.ro_heap_mark with ⟨ps, body, ret, hl, hrun⟩
  refine ⟨ps, body, ret, hl, ?_⟩
  intro F s hc hp _ hnt
  exact hrun s hc hp hnt
#print axioms ro_heap_mark

end InitECandidate.Solver.Wave8GuestInv.R10Ports
