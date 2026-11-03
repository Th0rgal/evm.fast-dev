import InitECandidate.Solver.Wave8GuestInv.ContractParts.C00
import InitECandidate.Solver.Wave8GuestInv.ContractParts.C08
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_calculate_total_blob_gas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_check_gas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_check_gas_limit
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_common_prefix_length
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_fee_mul
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.ro_heap_mark

namespace InitECandidate.Solver.Wave8GuestInv.R10Ports
set_option autoImplicit false

theorem ro_calculate_total_blob_gas : InitECandidate.Solver.Wave8GuestInv.ReadOnlyFn (Flapjack.Basis.Pure.MlString.ofString "calculate_total_blob_gas") := by
  rcases InitECandidate.Solver.Wave8Contracts.M14.ro_calculate_total_blob_gas with ⟨ps, body, ret, hl, hrun⟩
  refine ⟨ps, body, ret, hl, ?_⟩
  intro F s hc hp _ hnt
  exact hrun s hc hp hnt

theorem ro_check_gas : InitECandidate.Solver.Wave8GuestInv.ReadOnlyFn (Flapjack.Basis.Pure.MlString.ofString "check_gas") := by
  rcases InitECandidate.Solver.Wave8Contracts.M14.ro_check_gas with ⟨ps, body, ret, hl, hrun⟩
  refine ⟨ps, body, ret, hl, ?_⟩
  intro F s hc hp _ hnt
  exact hrun s hc hp hnt

theorem ro_check_gas_limit : InitECandidate.Solver.Wave8GuestInv.ReadOnlyFn (Flapjack.Basis.Pure.MlString.ofString "check_gas_limit") := by
  rcases InitECandidate.Solver.Wave8Contracts.M14.ro_check_gas_limit with ⟨ps, body, ret, hl, hrun⟩
  refine ⟨ps, body, ret, hl, ?_⟩
  intro F s hc hp _ hnt
  exact hrun s hc hp hnt

theorem ro_common_prefix_length : InitECandidate.Solver.Wave8GuestInv.ReadOnlyFn (Flapjack.Basis.Pure.MlString.ofString "common_prefix_length") := by
  rcases InitECandidate.Solver.Wave8Contracts.M14.ro_common_prefix_length with ⟨ps, body, ret, hl, hrun⟩
  refine ⟨ps, body, ret, hl, ?_⟩
  intro F s hc hp _ hnt
  exact hrun s hc hp hnt

theorem ro_fee_mul : InitECandidate.Solver.Wave8GuestInv.ReadOnlyFn (Flapjack.Basis.Pure.MlString.ofString "fee_mul") := by
  rcases InitECandidate.Solver.Wave8Contracts.M14.ro_fee_mul with ⟨ps, body, ret, hl, hrun⟩
  refine ⟨ps, body, ret, hl, ?_⟩
  intro F s hc hp _ hnt
  exact hrun s hc hp hnt

theorem ro_heap_mark : InitECandidate.Solver.Wave8GuestInv.ReadOnlyFn (Flapjack.Basis.Pure.MlString.ofString "heap_mark") := by
  rcases InitECandidate.Solver.Wave8Contracts.M14.ro_heap_mark with ⟨ps, body, ret, hl, hrun⟩
  refine ⟨ps, body, ret, hl, ?_⟩
  intro F s hc hp _ hnt
  exact hrun s hc hp hnt

end InitECandidate.Solver.Wave8GuestInv.R10Ports
