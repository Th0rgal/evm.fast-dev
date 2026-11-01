import InitE.Challenge
import Flapjack.Compiler.Backend.LabToTarget.EvaluateIgnoreClocks

/-! Final finite-certificate packaging using an already certified submission.
The actual uniform target bound remains a proof obligation. No compiler model,
installation theorem, primitive instance, or replacement program is assumed. -/

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8GuestInv.FiniteRebudget
open InitE Flapjack

def withFiniteBound (submission : Submission) (bound : Nat) : Submission :=
  { submission with K := .finite bound }

theorem machineConfig_eq (submission : Submission) (bound : Nat) :
    (withFiniteBound submission bound).machineConfig = submission.machineConfig := rfl

theorem initialState_eq (submission : Submission) (bound : Nat) (input : Guest.InputBlob) :
    (withFiniteBound submission bound).initialState input = submission.initialState input := rfl

theorem admitted (submission : Submission) (bound : Nat) (h : submission.Admitted) :
    (withFiniteBound submission bound).Admitted :=
  ⟨h.code_nonempty, h.code_limit, h.anchor_lower, h.anchor_upper,
    h.anchor_aligned, h.name_boundary, h.metadata_length, h.ordinary_slots_loaded,
    h.mmio_valid, h.entry_distinct, h.entry_loaded, h.entry_aligned,
    h.entry_dispatch_separate, h.mmio_program, h.exit_loaded, h.layout_bound⟩

/-- A genuine matching halt at any clock fixes every non-timeout evaluation's
outcome and observable trace, including at the proposed finite bound. -/
theorem matching_at_bound (submission : Submission) (bound oldSteps : Nat)
    (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (old : matchingExecutionAt submission input outcome events oldSteps)
    (notTimeout : (evaluateTargetHOL submission.machineConfig (sourceFfi input) bound
      (submission.initialState input)).1 ≠ .timeOut) :
    matchingExecutionAt (withFiniteBound submission bound) input outcome events bound := by
  obtain ⟨targetOutcome, oldPost, oldFfi, oldRun, matching⟩ := old
  rcases run : evaluateTargetHOL submission.machineConfig (sourceFfi input) bound
      (submission.initialState input) with ⟨result, post, finalFfi⟩
  rw [run] at notTimeout
  have agreement := evaluateTargetIgnoreClocks submission.machineConfig (sourceFfi input)
    bound oldSteps (submission.initialState input) result (.halt targetOutcome)
    post oldPost finalFfi oldFfi ⟨run, notTimeout, oldRun, by simp⟩
  have halt : result = .halt targetOutcome := congrArg Prod.fst agreement
  have trace : finalFfi.ioEvents = oldFfi.ioEvents :=
    congrArg (fun r => r.2.2.ioEvents) agreement
  refine ⟨targetOutcome, post, finalFfi, ?_, ?_⟩
  · rw [machineConfig_eq, initialState_eq, run, halt]
  · rw [trace]
    exact matching

def UniformNotTimeOut (submission : Submission) (bound : Nat) : Prop :=
  ∀ input : Guest.InputBlob,
    Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
    ∀ outcome events,
      sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL submission.machineConfig (sourceFfi input) bound
        (submission.initialState input)).1 ≠ .timeOut

/-- Preserve the submitted program, admission, matching outcome and trace,
changing only its certified budget. The old certificate must be proved. -/
theorem certificate (submission : Submission) (oldScore : NatE) (bound : Nat)
    (original : Certificate submission oldScore)
    (uniform : UniformNotTimeOut submission bound) :
    Certificate (withFiniteBound submission bound) (.finite bound) := by
  refine ⟨rfl, admitted submission bound original.admitted, ?_⟩
  intro input gas outcome events source covered
  obtain ⟨oldSteps, _, old⟩ := original.correct input gas outcome events source covered
  exact ⟨bound, Nat.le_refl _, matching_at_bound submission bound oldSteps input outcome events
    old (uniform input gas outcome events source covered)⟩

end InitECandidate.Solver.Wave8GuestInv.FiniteRebudget
