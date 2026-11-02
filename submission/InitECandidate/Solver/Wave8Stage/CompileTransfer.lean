import InitECandidate.Solver.Wave8Stage.CompilerOutput
import InitECandidate.Solver.Wave8Stage.UnfilteredTransfer

/-! Stage 5 from an actual successful LabToTarget.compile invocation. The
canonical section witness is extracted from compilation, retaining the actual
returned configuration. No labels-only output update is asserted. -/
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8Stage.CompileTransfer
open Flapjack Compiler.Backend Compiler.Backend.LabToTarget Compiler.Backend.LabSem
  Compiler.Encoders.Asm Compiler.Encoders.RiscV.Target RiscV.L3

/-- The exact FFI list selected by compileLab before label removal. -/
def compilerFfis {width : Nat} [NeZero width] (cfg : Config) (source : LabProgHOL width) :
    List HolFfiName :=
  cfg.ffiNames.getD (findFfiNames (LabFilter.filterSkip source))

/-- Compilation fixes the FFI list as well as the emitted sections and labels. -/
theorem canonical_witness {width : Nat} [NeZero width]
    (asm : AsmConfigExact width) (cfg output : Config)
    (source : LabProgHOL width) (bytes : List (BitVec 8))
    (run : compile asm cfg source = some (bytes, output)) :
    ∃ code, removeLabels cfg.initClock asm cfg.pos cfg.labels (compilerFfis cfg source)
      (LabFilter.filterSkip source) = some (code, output.labels) ∧ bytes = progToBytes code := by
  unfold compile compileLab at run
  cases names : cfg.ffiNames with
  | none =>
    simp only [names, ↓reduceIte] at run
    split at run
    · rename_i code labs removed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj run).symm
      exact ⟨code, by simpa only [compilerFfis, names, Option.getD_none] using removed, rfl⟩
    · cases run
  | some ffis =>
    simp only [names] at run
    split at run
    · split at run
      · rename_i code labs removed
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj run).symm
        exact ⟨code, by simpa only [compilerFfis, names, Option.getD_some] using removed, rfl⟩
      · cases run
    · cases run

/-- Sections certified by the actual successful compilation. They are unique
because the compiler's FFI list, input configuration and source are fixed. -/
noncomputable def compiledCode {width : Nat} [NeZero width]
    (asm : AsmConfigExact width) (cfg output : Config)
    (source : LabProgHOL width) (bytes : List (BitVec 8))
    (run : compile asm cfg source = some (bytes, output)) : LabProgHOL width :=
  Classical.choose (canonical_witness asm cfg output source bytes run)

theorem compiledCode_spec {width : Nat} [NeZero width]
    (asm : AsmConfigExact width) (cfg output : Config)
    (source : LabProgHOL width) (bytes : List (BitVec 8))
    (run : compile asm cfg source = some (bytes, output)) :
    ∃ ffis, removeLabels cfg.initClock asm cfg.pos cfg.labels ffis
      (LabFilter.filterSkip source) =
        some (compiledCode asm cfg output source bytes run, output.labels) ∧
      bytes = progToBytes (compiledCode asm cfg output source bytes run) :=
  ⟨compilerFfis cfg source, Classical.choose_spec (canonical_witness asm cfg output source bytes run)⟩

/-- An installation's explicitly extracted canonical sections are exactly the
sections in this interface; callers can rewrite their existing stateRel proof. -/
theorem compiledCode_eq {width : Nat} [NeZero width]
    (asm : AsmConfigExact width) (cfg output : Config)
    (source code : LabProgHOL width) (bytes : List (BitVec 8))
    (run : compile asm cfg source = some (bytes, output))
    (removed : removeLabels cfg.initClock asm cfg.pos cfg.labels (compilerFfis cfg source)
      (LabFilter.filterSkip source) = some (code, output.labels)) :
    compiledCode asm cfg output source bytes run = code := by
  have own := Classical.choose_spec (canonical_witness asm cfg output source bytes run)
  exact (Prod.mk.inj (Option.some.inj (own.1.symm.trans removed))).1

/-- Concrete affine transfer with the compiler, true-base full relation, oracle
tie and bootstrap identity explicit. All numeric instruction bounds are derived.
`initial` and `installed` can be the baseline states without importing them. -/
theorem stage5_lab_to_target_affine_not_timeOut {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (target : mc.target = riscvTarget)
    (initial installed : riscv_state) (lab : LabSem.State 64 Config F) (t : AsmState 64)
    (cfg output : Config) (bytes : List (BitVec 8))
    (compiled : compile riscvConfig cfg lab.code = some (bytes, output))
    (position : cfg.pos = 0)
    (safe : LabProps.noInstall lab.code)
    (compiler : lab.compile = compile mc.target.config) (failed : lab.failed = false)
    (related : LabToTarget.stateRel
      (mc, compiledCode riscvConfig cfg output lab.code bytes compiled, output.labels,
        mc.target.getPc installed) (UnfilteredTransfer.filtered mc lab) t installed)
    (tied : oracleTie mc installed lab)
    (bootstrap k_lab : Nat)
    (bootstrapRun : ∀ fuel, evaluateTargetHOL mc lab.ffi (bootstrap + fuel) initial =
      evaluateTargetHOL mc lab.ffi fuel installed)
    (notError : (LabSem.evaluate {lab with clock := k_lab}).1 ≠ .error)
    (notTimeout : (LabSem.evaluate {lab with clock := k_lab}).1 ≠ .timeOut) :
    (evaluateTargetHOL mc lab.ffi (bootstrap + 9 * (k_lab + 1)) initial).1 ≠ .timeOut := by
  obtain ⟨ffis, removed, _⟩ := compiledCode_spec riscvConfig cfg output lab.code bytes compiled
  rw [position] at removed
  rw [bootstrapRun]
  exact UnfilteredTransfer.stage5_lab_to_target_affine_not_timeOut mc target lab t installed
    (compiledCode riscvConfig cfg output lab.code bytes compiled) output.labels cfg.labels ffis
    cfg.initClock removed safe compiler failed related tied k_lab notError notTimeout

end InitECandidate.Solver.Wave8Stage.CompileTransfer
