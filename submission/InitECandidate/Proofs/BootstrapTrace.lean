import InitECandidate.Proofs.BootstrapStraightLine
import InitECandidate.Proofs.BootstrapCopyGuards
import InitECandidate.Proofs.BootstrapTailChecks

set_option autoImplicit false

namespace InitECandidate.Proofs.BootstrapTrace
open InitE
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps
open InitECandidate.Proofs.BootstrapSteps InitECandidate.Proofs.BootstrapCopy InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Proofs.BootstrapAsmComposition InitECandidate.Proofs.BootstrapCopyGuards

def fullBootstrapCode : List (HolAsm 64) :=
  prefixCode ++ (loopProgram 4617 ++ tailCode)

theorem full_length : fullBootstrapCode.length = 23120 := by
  simp only [fullBootstrapCode, List.length_append, loopProgram_length]
  change 3 + (5 * 4617 + 32) = 23120
  rfl

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
  · exact loopProgram_inst_ok 4617 i h
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

theorem checked_append (left right : List (HolAsm 64)) (s : AsmState 64) :
    Checked (left ++ right) s ↔ Checked left s ∧ Checked right (run left s) := by
  induction left generalizing s with
  | nil => simp [Checked, run]
  | cons i rest ih => simp only [List.cons_append, Checked, run, ih, and_assoc]

theorem guards_append (left right : List (HolAsm 64)) (s : AsmState 64) :
    EvaluatorGuards baselineMachineConfig (left ++ right) s ↔
      EvaluatorGuards baselineMachineConfig left s ∧
        EvaluatorGuards baselineMachineConfig right (run left s) := by
  induction left generalizing s with
  | nil => simp [EvaluatorGuards, run]
  | cons i rest ih => simp only [List.cons_append, EvaluatorGuards, run, ih, and_assoc]

/-- The three address loads execute below every native FFI entry. -/
theorem prefix_guards : EvaluatorGuards baselineMachineConfig prefixCode initialAsm := by
  simp only [prefixCode, bootstrapBlocks, List.take, List.map, EvaluatorGuards]
  refine ⟨rfl, ?_, rfl, ?_, rfl, ?_, trivial⟩
  all_goals apply bootstrap_ffi_disjoint
  all_goals simp [after, bootLoc, asmUpd, updPc, updReg, initialAsm, initialPc,
    riscvEnc, riscvAst, riscvEncode, initDataRom, initDataRam, initDataEnd]

/-- The computed endpoint of prefix, loop and tail is the tail endpoint. -/
theorem full_run : run fullBootstrapCode initialAsm = tailEndpoint := by
  simp only [fullBootstrapCode, run_append, prefix_endpoint, loopProgram_run]
  rfl

/-- Local checked traces compose without a machine-run premise. -/
theorem full_checked_of_tail (tail : Checked tailCode (copyState 4617)) :
    Checked fullBootstrapCode initialAsm := by
  rw [fullBootstrapCode, checked_append]
  refine ⟨prefix_checked, ?_⟩
  rw [prefix_endpoint, checked_append]
  refine ⟨copyLoop_checked, ?_⟩
  simpa only [loopProgram_run, copyState] using tail

theorem full_guards_of_tail
    (tail : EvaluatorGuards baselineMachineConfig tailCode (copyState 4617)) :
    EvaluatorGuards baselineMachineConfig fullBootstrapCode initialAsm := by
  rw [fullBootstrapCode, guards_append]
  refine ⟨prefix_guards, ?_⟩
  rw [prefix_endpoint, guards_append]
  refine ⟨copyLoop_guards, ?_⟩
  simpa only [loopProgram_run, copyState] using tail

theorem full_endpoint_of_tail (tail : Checked tailCode (copyState 4617)) :
    run fullBootstrapCode initialAsm = installedAsm :=
  full_run.trans (tail_endpoint_eq tail)

/-- Checked ASM execution yields the exact target-evaluator prefix ending at
an installed native-entry state. The machine endpoint is obtained from the
encoder correctness proof, never assumed. -/
theorem full_evaluator_of_tail {σ : Type} (io : HolFfiState σ) (ms : riscv_state)
    (initial : targetStateRel riscvTarget initialAsm ms)
    (tailChecks : Checked tailCode (copyState 4617))
    (tailGuards : EvaluatorGuards baselineMachineConfig tailCode (copyState 4617)) :
    ∃ count post,
      (∀ clock, evaluateTargetHOL baselineMachineConfig io (count + clock) ms =
        evaluateTargetHOL baselineMachineConfig io clock post) ∧
      targetStateRel riscvTarget installedAsm post := by
  obtain ⟨count, post, shift, relation, _⟩ :=
    checked_trace_evaluator baselineMachineConfig rfl rfl fullBootstrapCode initialAsm
      (full_checked_of_tail tailChecks) (full_guards_of_tail tailGuards) ms io initial
  exact ⟨count, post, shift, by rwa [full_endpoint_of_tail tailChecks] at relation⟩

/-- Every instruction of the actual submitted bootstrap has a checked ASM step. -/
theorem full_checked : Checked fullBootstrapCode initialAsm :=
  full_checked_of_tail tail_checked

theorem full_guards : EvaluatorGuards baselineMachineConfig fullBootstrapCode initialAsm :=
  full_guards_of_tail tail_guards

/-- The submitted startup reaches the exact native compiler installation. -/
theorem full_endpoint : run fullBootstrapCode initialAsm = installedAsm :=
  full_endpoint_of_tail tail_checked

/-- The actual submitted bootstrap supplies a finite evaluator prefix, with
no assumed bootstrap execution or installation poststate. -/
theorem full_evaluator {σ : Type} (io : HolFfiState σ) (ms : riscv_state)
    (initial : targetStateRel riscvTarget initialAsm ms) :
    ∃ count post,
      (∀ clock, evaluateTargetHOL baselineMachineConfig io (count + clock) ms =
        evaluateTargetHOL baselineMachineConfig io clock post) ∧
      targetStateRel riscvTarget installedAsm post :=
  full_evaluator_of_tail io ms initial tail_checked tail_guards

/-- Exact step-count version of `full_evaluator`: the submitted bootstrap executes
in `bootstrapSteps = 23132` target evaluator steps (`0x80000000` -> `0x80001190`). -/
theorem full_evaluator_exact {σ : Type} (io : HolFfiState σ) (ms : riscv_state)
    (initial : targetStateRel riscvTarget initialAsm ms) :
    ∃ post,
      (∀ clock, evaluateTargetHOL baselineMachineConfig io (bootstrapSteps + clock) ms =
        evaluateTargetHOL baselineMachineConfig io clock post) ∧
      targetStateRel riscvTarget installedAsm post := by
  obtain ⟨post, shift, relation⟩ :=
    checked_trace_evaluator_bootstrap baselineMachineConfig rfl rfl fullBootstrapCode initialAsm
      full_inst_ok full_checked full_guards ms io initial
  rw [full_steps] at shift
  exact ⟨post, shift, by rwa [full_endpoint] at relation⟩

end InitECandidate.Proofs.BootstrapTrace
