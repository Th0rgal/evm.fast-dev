import InitECandidate.Solver.Wave8Stage.ConcreteStageTransferBridge
import InitECandidate.Solver.Wave8Stage.ConcreteCompilerWord
import InitECandidate.Solver.Wave8Stage.WordCostCompilerControl
import Flapjack.Compiler.Backend.WordToWord.FastCompile
import Flapjack.Compiler.Backend.RegAlloc.Executable

/-! Proofs-free decomposition of `ConcreteStageTransferBridge.BackendBound`.

The whole-pipeline obligation (word-to-word allocation, word-to-stack
compilation with threaded bitmap state, the three stack passes and the
`codeStepBudget` maximum) is reduced to one closed statement per source
function, so each function can be certified by kernel reduction in its own
shard. Nothing here depends on `InitECandidate.Proofs`. -/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.BackendDecomposition
open InitE Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Stage
open InitECandidate.Solver.Wave8Stage.StackToLabClock (stepCost)

/-! ## Word-to-word: the noncomputable compiler is the executable one -/

/-- Register count used by both `WordToWord.compile` and `compileNative`. -/
abbrev registers : Nat := riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length)

/-- One function through the executable word-to-word compiler, written with
the `preAllocation` prefix that the `PrefixChecks` shards already certify. -/
def wordFunction (oracle : Option (Spt Nat)) (entry : Nat × Nat × WordLangProgHOL (BitVec 64)) :
    Nat × Nat × WordLangProgHOL (BitVec 64) :=
  (entry.1, entry.2.1,
    WordRemove.removeMustTerminate
      (WordToWord.wordAllocWith RegAlloc.regAllocExecutable entry.1 riscvConfig
        (oracleCompilerConfig []).wordToWordConf.regAlg registers
        (WordCostCompilerControl.preAllocation riscvConfig riscvConfig.twoRegArith entry.2.1
          entry.2.2)
        oracle))

theorem fullCompileSingleWith_eq_wordFunction (oracle : Option (Spt Nat))
    (entry : Nat × Nat × WordLangProgHOL (BitVec 64)) :
    WordToWord.fullCompileSingleWith RegAlloc.regAllocExecutable riscvConfig.twoRegArith
      registers (oracleCompilerConfig []).wordToWordConf.regAlg riscvConfig (entry, oracle) =
      wordFunction oracle entry := by
  rcases entry with ⟨name, arity, body⟩
  rfl

theorem regAlg_oracles (oracles : List (Option (Spt Nat))) :
    (oracleCompilerConfig oracles).wordToWordConf.regAlg =
      (oracleCompilerConfig []).wordToWordConf.regAlg := rfl

/-- `WordToWord.compile` on the concrete source with an oracle table of exactly
one entry per function is the pointwise executable compiler. -/
theorem compile_eq_map (oracles : List (Option (Spt Nat)))
    (hlen : oracles.length = ConcreteCompilerWord.source.length) :
    WordToWord.compile (oracleCompilerConfig oracles).wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) =
      ([], (ConcreteCompilerWord.source.zip oracles).map
        (fun p => wordFunction p.2 p.1)) := by
  have hsrc : panToWordCompileProgHOL riscvConfig.isa sourceDeclarations =
      ConcreteCompilerWord.source := ConcreteCompilerWord.compile_eq
  rw [hsrc, ← WordToWord.compileWith_eq_compile RegAlloc.regAllocExecutable
    (funext fun a => funext fun b => funext fun c => funext fun d => funext fun e =>
      funext fun f => funext fun g => RegAlloc.regAllocExecutable_eq a b c d e f g)]
  unfold WordToWord.compileWith
  dsimp only
  have hcol : (oracleCompilerConfig oracles).wordToWordConf.colOracle = oracles := rfl
  rw [hcol, WordToWord.nextNOracle, if_pos (by omega), List.take_of_length_le (by omega),
    List.drop_of_length_le (by omega), regAlg_oracles]
  dsimp only
  congr 1

/-! ## Word-to-stack: per-function bodies with threaded bitmap state -/

theorem compileWordToStack_cons (identifier arguments : Nat)
    (body : WordLangProgHOL (BitVec 64))
    (rest : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (before middle after : AppList (BitVec 64) × Nat)
    (stackBody : HolProg 64) (frame : Nat)
    (stackRest : List (Nat × HolProg 64)) (frames : List Nat)
    (head_eq : WordToStack.Native.compileProgNative riscvConfig false body arguments registers
      before = (stackBody, frame, middle))
    (tail_eq : WordToStack.Native.compileWordToStackNative riscvConfig false registers rest
      middle = (stackRest, frames, after)) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      ((identifier, arguments, body) :: rest) before =
      ((identifier, stackBody) :: stackRest, frame :: frames, after) := by
  simp only [WordToStack.Native.compileWordToStackNative, head_eq, tail_eq]

theorem compileWordToStack_nil (before : AppList (BitVec 64) × Nat) :
    WordToStack.Native.compileWordToStackNative riscvConfig false registers
      ([] : List (Nat × Nat × WordLangProgHOL (BitVec 64))) before = ([], [], before) := rfl

theorem compileNative_of_bodies
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (bodies : List (Nat × HolProg 64)) (frames : List Nat)
    (bitmaps : AppList (BitVec 64) × Nat)
    (compiled : WordToStack.Native.compileWordToStackNative riscvConfig false registers programs
      (.list [4], 1) = (bodies, frames, bitmaps)) :
    WordToStack.Native.compileNative riscvConfig false programs =
      (appListAppend bitmaps.1,
       { bitmapsLength := bitmaps.2,
         stackFrameSize := sptFromAList ((bodies.zip frames).map
           (fun ((identifier, _), frame) => (identifier, frame))) },
       0 :: frames,
       (raiseStubLocation, WordToStack.Native.raiseStubNative false registers) ::
       (storeConstsStubLocation, WordToStack.Native.storeConstsStubNative registers) ::
       bodies) := by
  unfold WordToStack.Native.compileNative
  simp only [Bool.false_eq_true, if_false]
  change (match WordToStack.Native.compileWordToStackNative riscvConfig false registers
      programs (.list [4], 1) with
    | (bodies, frames, bitmaps) => _) = _
  rw [compiled]

/-! ## Stack passes and the budget -/

/-- Every post-RawCall body cost is bounded if every entry of the final table is. -/
theorem codeStepBudget_le_of_forall {code : List (Nat × HolProg 64)} {M : Nat}
    (h : ∀ e ∈ code, stepCost e.2 ≤ M) : Stage4.codeStepBudget code ≤ M := by
  induction code with
  | nil => exact Nat.zero_le _
  | cons e es ih =>
    simp only [Stage4.codeStepBudget, List.map_cons, List.foldr_cons]
    exact Nat.max_le.mpr ⟨h e (List.mem_cons_self), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

/-- The three stack passes in the shape used by `FullMakeInitSemantics.code2`. -/
def stackPasses (oracles : List (Option (Spt Nat))) (p : List (Nat × HolProg 64)) :
    List (Nat × HolProg 64) :=
  FullMakeInitSemantics.code2
    (oracleCompilerConfig oracles).stackConf (oracleCompilerConfig oracles).dataConf
    (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig oracles).dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset p

/-- `BackendBound` restated for an explicit oracle table. -/
theorem backendBound_of_table (w : LeanBridge.ConcreteOracleCompilationWitness)
    (hlen : w.oracles.length = ConcreteCompilerWord.source.length)
    (bodies : List (Nat × HolProg 64)) (frames : List Nat) (bitmaps : AppList (BitVec 64) × Nat)
    (compiled : WordToStack.Native.compileWordToStackNative riscvConfig false registers
      ((ConcreteCompilerWord.source.zip w.oracles).map (fun p => wordFunction p.2 p.1))
      (.list [4], 1) = (bodies, frames, bitmaps))
    (budget : Stage4.codeStepBudget (stackPasses w.oracles
      ((raiseStubLocation, WordToStack.Native.raiseStubNative false registers) ::
       (storeConstsStubLocation, WordToStack.Native.storeConstsStubNative registers) ::
       bodies)) ≤ 7313) :
    ConcreteStageTransferBridge.BackendBound w := by
  intro col wprog wconf fs p hword hstack
  rw [compile_eq_map w.oracles hlen] at hword
  cases hword
  rw [compileNative_of_bodies _ bodies frames bitmaps compiled] at hstack
  have hp : p = (raiseStubLocation, WordToStack.Native.raiseStubNative false registers) ::
      (storeConstsStubLocation, WordToStack.Native.storeConstsStubNative registers) :: bodies :=
    (congrArg (fun x => x.2.2.2) hstack).symm
  subst hp
  exact budget

/-- The backend budget depends only on the oracle table, not on the other
fields of a concrete compilation witness. -/
theorem backendBound_of_oracles_eq
    (w v : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = v.oracles)
    (bounded : ConcreteStageTransferBridge.BackendBound v) :
    ConcreteStageTransferBridge.BackendBound w := by
  unfold ConcreteStageTransferBridge.BackendBound at bounded ⊢
  simpa only [same] using bounded

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.BackendDecomposition
