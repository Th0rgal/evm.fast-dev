import InitECandidate.Solver.Wave8Stage.ConcreteBaseline.Trace
import InitECandidate.Solver.Wave8Stage.ConcreteBaseline.ExactInstructions
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option autoImplicit false
namespace InitECandidate.Solver.Wave8Stage.ConcreteBaseline.ExactBootstrap
open InitE
open InitECandidate.Proofs.BootstrapStraightLine
open Flapjack.Misc
open Flapjack Flapjack.RiscV.L3 Flapjack.RiscV.L3.Step
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps
open InitECandidate.Proofs.BootstrapSteps InitECandidate.Proofs.BootstrapCopy
open InitECandidate.Proofs.BootstrapAsmComposition
open InitECandidate.Solver.Wave8Stage.ConcreteBaseline.BootstrapStraightLine InitECandidate.Solver.Wave8Stage.ConcreteBaseline.BootstrapTrace
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Backend.BackendProof Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Pancake.Proofs.PanToTarget

open InitECandidate.Solver.Wave8Stage.ConcreteBaseline
open InitECandidate.Solver.Wave8Stage.ConcreteBaseline.ExactInstructions
theorem prefix_inst_ok : ∀ i ∈ prefixCode, BootstrapInstOk i := by
  intro i hi
  simp [prefixCode, bootstrapBlocks, bootLoc] at hi
  rcases hi with rfl | rfl | rfl <;> trivial

theorem loopBody_inst_ok : ∀ i ∈ loopBody, BootstrapInstOk i := by
  intro i hi
  simp [loopBody] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · trivial
  · trivial
  · trivial
  · trivial
  · simp [BootstrapInstOk]

theorem loopProgram_inst_ok (words : Nat) : ∀ i ∈ loopProgram words, BootstrapInstOk i := by
  intro i hi
  simp only [loopProgram, List.mem_flatten, List.mem_replicate] at hi
  rcases hi with ⟨l, ⟨_, rfl⟩, hi⟩
  exact loopBody_inst_ok i hi

theorem tail_inst_ok : ∀ i ∈ tailCode, BootstrapInstOk i := by
  intro i hi
  simp [tailCode, bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore, bootAdd] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

theorem full_inst_ok : ∀ i ∈ fullBootstrapCode, BootstrapInstOk i := by
  intro i hi
  simp only [fullBootstrapCode, List.mem_append] at hi
  rcases hi with h | h | h
  · exact prefix_inst_ok i h
  · exact loopProgram_inst_ok 4606 i h
  · exact tail_inst_ok i h

theorem prefix_steps : bootstrapTraceSteps prefixCode = 6 := by decide
theorem loopBody_steps : bootstrapTraceSteps loopBody = 5 := by decide
theorem tail_steps : bootstrapTraceSteps tailCode = 41 := by decide

theorem loopProgram_steps (words : Nat) : bootstrapTraceSteps (loopProgram words) = 5 * words := by
  induction words with
  | zero => rfl
  | succ words ih =>
    simp only [loopProgram, List.replicate_succ, List.flatten_cons, bootstrapTraceSteps_append]
    rw [show bootstrapTraceSteps ((List.replicate words loopBody).flatten) =
      bootstrapTraceSteps (loopProgram words) from rfl, ih, loopBody_steps]
    omega

theorem full_steps : bootstrapTraceSteps fullBootstrapCode = bootstrapSteps := by
  simp only [fullBootstrapCode, bootstrapTraceSteps_append, prefix_steps, loopProgram_steps, tail_steps,
    bootstrapSteps, initDataWords]
  rfl

/-- Exact step-count version of `full_evaluator`: the submitted bootstrap executes
in `bootstrapSteps = 23077` target evaluator steps (`0x80000000` -> `0x80001070`). -/
theorem full_evaluator_exact {σ : Type} (io : HolFfiState σ) (ms : riscv_state)
    (initial : targetStateRel riscvTarget initialAsm ms) :
    ∃ post,
      (∀ clock, evaluateTargetHOL baselineMachineConfig io (bootstrapSteps + clock) ms =
        evaluateTargetHOL baselineMachineConfig io clock post) ∧
      (∀ clock, findNextInterference baselineMachineConfig io (bootstrapSteps + clock) ms =
        findNextInterference baselineMachineConfig io clock post) ∧
      targetStateRel riscvTarget installedAsm post := by
  obtain ⟨post, shift, search, relation⟩ :=
    checked_trace_evaluator_bootstrap baselineMachineConfig rfl rfl fullBootstrapCode initialAsm
      full_inst_ok full_checked full_guards ms io initial
  rw [full_steps] at shift search
  exact ⟨post, shift, search, by rwa [full_endpoint] at relation⟩

#print axioms full_evaluator_exact
end InitECandidate.Solver.Wave8Stage.ConcreteBaseline.ExactBootstrap
