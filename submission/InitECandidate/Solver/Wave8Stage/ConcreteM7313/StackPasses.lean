import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BackendDecomposition

/-! Proofs-free per-body decomposition of the three stack passes used by
`FullMakeInitSemantics.code2` (`StackRawCall`, `StackAlloc`, `StackRemove`) and
of the resulting `codeStepBudget`. Each body of the native word-to-stack table
is pushed through the three passes separately; only the raw-call frame
information `collectInfo` is a whole-table computation, and it is threaded as
an explicit closed value. -/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.StackPasses
open InitE Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open InitECandidate.Solver.Wave8Stage.StackToLabClock (stepCost)
open InitECandidate.Solver.Wave8Stage.ConcreteM7313.BackendDecomposition

/-- The pointer (stack-pointer register) argument of `code2`. -/
abbrev pointer : Nat := riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)

/-- Combined per-body stack lowering: raw calls (with global frame info),
stack allocation, then stack removal, exactly as composed by `code2`. -/
def lowerBody (oracles : List (Option (Spt Nat))) (info : Spt Nat) (body : HolProg 64) :
    HolProg 64 :=
  StackRemove.comp (oracleCompilerConfig oracles).stackConf.jump riscvConfig.addrOffset pointer
    (StackAlloc.comp 0 (StackAlloc.nextLabHOL (StackRawCall.compTop info body) 2)
      (StackRawCall.compTop info body)).1

theorem stackAlloc_progComp (n : Nat) (p : HolProg 64) :
    StackAlloc.progComp (n, p) = (n, (StackAlloc.comp n (StackAlloc.nextLabHOL p 2) p).1) := rfl

/-- `StackAlloc.comp` ignores its name argument up to the resulting program. -/
theorem lowerBody_table_entry (oracles : List (Option (Spt Nat))) (info : Spt Nat)
    (n : Nat) (body : HolProg 64)
    (hname : ∀ m, (StackAlloc.comp m (StackAlloc.nextLabHOL (StackRawCall.compTop info body) 2)
      (StackRawCall.compTop info body)).1 =
      (StackAlloc.comp 0 (StackAlloc.nextLabHOL (StackRawCall.compTop info body) 2)
      (StackRawCall.compTop info body)).1) :
    StackRemove.progComp (oracleCompilerConfig oracles).stackConf.jump riscvConfig.addrOffset
      pointer (StackAlloc.progComp (n, StackRawCall.compTop info body)) =
      (n, lowerBody oracles info body) := by
  simp only [stackAlloc_progComp, StackRemove.progComp, lowerBody, hname]

/-- `code2` as stubs plus a pointwise map of the native bodies. -/
theorem code2_eq (oracles : List (Option (Spt Nat))) (table : List (Nat × HolProg 64)) :
    stackPasses oracles table =
      StackRemove.initStubs (StackToLab.isGenGc (oracleCompilerConfig oracles).dataConf.gcKind)
        (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig oracles).dataConf - 1) pointer
        BvlToBvi.initGlobalsLocation ++
      (StackAlloc.stubs (oracleCompilerConfig oracles).dataConf ++
        List.map StackAlloc.progComp
          (table.map (fun (e : Nat × HolProg 64) => (e.1, StackRawCall.compTop (StackRawCall.collectInfo table .ln) e.2)))).map
        (StackRemove.progComp (oracleCompilerConfig oracles).stackConf.jump riscvConfig.addrOffset
          pointer) := by
  rfl

/-- Budget of `code2` from a bound on the stubs and a bound on every lowered body. -/
theorem budget_of_bodies (oracles : List (Option (Spt Nat))) (table : List (Nat × HolProg 64))
    (M : Nat)
    (stubs : ∀ e ∈ (StackRemove.initStubs (width := 64)
        (StackToLab.isGenGc (oracleCompilerConfig oracles).dataConf.gcKind)
        (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig oracles).dataConf - 1) pointer
        BvlToBvi.initGlobalsLocation ++
      (StackAlloc.stubs (oracleCompilerConfig oracles).dataConf).map
        (StackRemove.progComp (oracleCompilerConfig oracles).stackConf.jump riscvConfig.addrOffset
          pointer)), stepCost e.2 ≤ M)
    (bodies : ∀ e ∈ table,
      stepCost (StackRemove.progComp (oracleCompilerConfig oracles).stackConf.jump
        riscvConfig.addrOffset pointer
        (StackAlloc.progComp (e.1, StackRawCall.compTop (StackRawCall.collectInfo table .ln) e.2))).2
        ≤ M) :
    Stage4.codeStepBudget (stackPasses oracles table) ≤ M := by
  rw [code2_eq]
  apply codeStepBudget_le_of_forall
  intro e he
  rw [List.map_append, List.map_map, List.map_map] at he
  rcases List.mem_append.mp he with h | h
  · exact stubs e (List.mem_append_left _ h)
  rcases List.mem_append.mp h with h | h
  · exact stubs e (List.mem_append_right _ h)
  · rcases List.mem_map.mp h with ⟨x, hx, rfl⟩
    exact bodies x hx

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.StackPasses
