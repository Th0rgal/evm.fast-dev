import InitECandidate.Solver.Wave8Stage.ConcreteStageTransferBridge

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Guest Stage 5 transfer

Assembles `Wave8GuestInv.StageTransfer` (source `K_pan` budget ⇒ target `K_target`
budget) for a concrete oracle compilation witness `w` from the Proofs-free
bridge `ConcreteStageTransferBridge.stageTransfer`.

Of the three static obligations of `Stage5Bridge.stageTransfer_from_obligations`:

* `h_front` (`listBudget ConcreteCompilerCrep.source ≤ 448`) is discharged inside
  `Stage5TransferInstanceArgon` by `CrepListBudget448.crep_listBudget_le_448`;
* `h_word_all` (every Word entry passes the static cost checker) is taken as the
  `checked` hypothesis here; `PrefixChecks.AllChecked.checked` is its instance;
* `h_m7313` (`BackendBound w`: the post-StackRemove step budget of the compiled
  table is `≤ 7313`) is taken as the `backend` hypothesis. Its value depends on
  the register-allocation oracles `w.oracles`, so it cannot be discharged
  uniformly in `w`; it is a per-witness concrete computation.
-/

namespace InitECandidate.Solver.GuestStageTransfer
open InitECandidate.Solver InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Stage

/-- Backend step-budget obligation for a witness, restated from
`ConcreteStageTransferBridge.BackendBound`. -/
abbrev BackendBound (w : LeanBridge.ConcreteOracleCompilationWitness) : Prop :=
  ConcreteStageTransferBridge.BackendBound w

/-- Word-level static cost obligation (`h_word_all`). -/
abbrev WordChecked : Prop :=
  ConcreteCompilerWord.source.all ConcreteWordCheckInput.check = true

/-- Axioms: `propext`, `Classical.choice`, `Quot.sound`. -/
theorem guestStageTransfer_of_checked_and_backend
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (checked : WordChecked) (backend : BackendBound w) : StageTransfer :=
  ConcreteStageTransferBridge.stageTransfer w checked backend

end InitECandidate.Solver.GuestStageTransfer
