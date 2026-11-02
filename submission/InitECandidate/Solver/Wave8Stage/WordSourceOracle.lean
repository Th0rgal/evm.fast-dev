import InitECandidate.Solver.Wave8Stage.WordCostEntryCertificate
import InitECandidate.Solver.Wave8Stage.ConcreteWordCostData
import InitE.SourceSemantics

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordSourceOracle
open Flapjack Flapjack.Basis.Pure.MlString WordCostEntryCertificate

/-- The challenge's actual oracle discharges every terminal-call assumption
used by the cost certificates, at arbitrary host state, configuration and bytes. -/
theorem terminalOracle : TerminalOracle terminal InitE.sourceOracle := by
  intro ffi name oracle term config bytes
  have names : name = ofString "halt" ∨ name = ofString "trap" := by
    simpa only [terminal,Bool.or_eq_true,beq_iff_eq] using term
  rcases names with rfl | rfl
  · have final : ffi.oracle (.extCall (ofString "halt")) ffi.ffiState config bytes = .final .failed := by
      rw [oracle]
      exact InitE.halt_is_terminal ffi.ffiState config bytes
    exact ⟨_,callFFIHOL_final ffi (.extCall (ofString "halt")) config bytes .failed (by decide) final⟩
  · have final : ffi.oracle (.extCall (ofString "trap")) ffi.ffiState config bytes = .final .failed := by
      rw [oracle]
      exact InitE.trap_is_terminal ffi.ffiState config bytes
    exact ⟨_,callFFIHOL_final ffi (.extCall (ofString "trap")) config bytes .failed (by decide) final⟩

end InitECandidate.Solver.Wave8Stage.WordSourceOracle
