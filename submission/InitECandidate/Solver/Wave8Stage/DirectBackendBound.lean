import InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Oracles
import InitECandidate.Solver.GuestStageTransfer

/-!
# Direct Stage 5 backend bound

`oracleCompilerConfig` changes only `wordToWordConf.colOracle`. The stack and data
configurations that `FullMakeInitSemantics.code2` reads are therefore the empty-oracle
ones, and `BackendBound` depends on the oracle table only through the word-to-word
compiler. That compiler is the executable per-function compiler on the concrete colouring
table `ConcreteM7313.oracles` (`oracles.length = 814`).

`concreteBackendBound` is the remaining closed computation: the native word-to-stack table
of that colouring, plus `stepCost ≤ 7313` on every lowered body. It does not import
`InitECandidate.Proofs` or `ConcreteOracleWitness`. `concreteStageTransfer` still needs
`PrefixChecks.checked` (`AllChecked`), whose cone is not built here.
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.DirectBackendBound
open InitE Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Stage
open InitECandidate.Solver.Wave8Stage.ConcreteM7313
open InitECandidate.Solver.Wave8Stage.ConcreteM7313.BackendDecomposition
open InitECandidate.Solver.Wave8Stage.ConcreteM7313.StackPasses
open InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget

theorem stackConf_independent (oracles : List (Option (Spt Nat))) :
    (oracleCompilerConfig oracles).stackConf = (oracleCompilerConfig []).stackConf := rfl

theorem dataConf_independent (oracles : List (Option (Spt Nat))) :
    (oracleCompilerConfig oracles).dataConf = (oracleCompilerConfig []).dataConf := rfl

theorem source_length : ConcreteCompilerWord.source.length = 814 := rfl

theorem oracles_length_eq_source :
    oracles.length = ConcreteCompilerWord.source.length :=
  oracles_length.trans source_length.symm

/-- Word-to-word compilation of the guest on the concrete colouring table is the
pointwise executable compiler. -/
theorem compile_eq_concrete :
    WordToWord.compile (oracleCompilerConfig oracles).wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) =
      ([], (ConcreteCompilerWord.source.zip oracles).map (fun p => wordFunction p.2 p.1)) :=
  compile_eq_map oracles oracles_length_eq_source

/-- `BackendBound` for any witness whose oracle table is the concrete colouring,
from the native word-to-stack table and a uniform lowered-body budget. -/
theorem backendBound_concrete
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = oracles)
    (bodies : List (Nat × HolProg 64)) (frames : List Nat)
    (bitmaps : AppList (BitVec 64) × Nat) (info : Spt Nat)
    (compiled : WordToStack.Native.compileWordToStackNative riscvConfig false registers
      ((ConcreteCompilerWord.source.zip oracles).map (fun p => wordFunction p.2 p.1))
      (.list [4], 1) = (bodies, frames, bitmaps))
    (collected : StackRawCall.collectInfo (nativeStubs ++ bodies) .ln = info)
    (bounded : Bounded info (nativeStubs ++ bodies)) :
    ConcreteStageTransferBridge.BackendBound w := by
  apply backendBound w (by rw [same]; exact oracles_length_eq_source) bodies frames bitmaps info
  · simpa only [same] using compiled
  · exact collected
  · exact bounded

/-- The closed computation still required for `BackendBound` on `oracles`. -/
def concreteBackendBound : Prop :=
  ∃ (bodies : List (Nat × HolProg 64)) (frames : List Nat)
    (bitmaps : AppList (BitVec 64) × Nat) (info : Spt Nat),
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      ((ConcreteCompilerWord.source.zip oracles).map (fun p => wordFunction p.2 p.1))
      (.list [4], 1) = (bodies, frames, bitmaps) ∧
    StackRawCall.collectInfo (nativeStubs ++ bodies) .ln = info ∧
    Bounded info (nativeStubs ++ bodies)

theorem backendBound_of_concrete
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = oracles)
    (h : concreteBackendBound) :
    ConcreteStageTransferBridge.BackendBound w := by
  rcases h with ⟨bodies, frames, bitmaps, info, compiled, collected, bounded⟩
  exact backendBound_concrete w same bodies frames bitmaps info compiled collected bounded

/-- `StageTransfer` once the word checker and the concrete backend computation are done.
`PrefixChecks.checked` supplies `WordChecked`; it is not built on this machine. -/
theorem concreteStageTransfer
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = oracles)
    (checked : GuestStageTransfer.WordChecked)
    (h : concreteBackendBound) : StageTransfer :=
  ConcreteStageTransferBridge.stageTransfer w checked
    (backendBound_of_concrete w same h)

end InitECandidate.Solver.Wave8Stage.DirectBackendBound
