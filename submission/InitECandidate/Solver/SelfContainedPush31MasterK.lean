import InitECandidate.Solver.GuestEvmStepOpcodeBounds
import InitECandidate.Solver.SelfContainedIsoReducedK
import InitECandidate.Solver.SelfContainedBasicBlockBridge

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.SelfContainedPush31MasterK` (`W5_24`)

Self-contained integration in `Solver/` (with **0 `Proofs/Bounded*` imports**) of the worst-case
collision-free `PUSH31` source clock from `GuestEvmStepOpcodeBounds` (`54` ticks for `3` gas =
`18` ticks/gas -> `3,659,564,234` `PanSem` ticks) with the isometric reduced frontend/backend
pipeline of `SelfContainedIsoReducedK` (`isoFrontFactor = 6`, `bMax = 8`).

Main results:
1. `push31SourceClock = 59,564,234 + 18 * 200,000,000 = 3,659,564,234` matches
   `GuestEvmStepOpcodeBounds.tightLinearClock`.
2. `push31CandidateK = 23,132 + 8 * 6 * (3,659,564,234 + 5,000) = 175,659,346,364` satisfies
   `5 * push31CandidateK < 900,719,925,474` (over `5x` below the Yukon IEEE-754 float64 ceiling,
   with `6 * push31CandidateK > 900,719,925,474`).
3. Outside GC (`C_sr = 1`, `noGcFrontFactor = 3`), the candidate budget drops to
   `push31NoGcCandidateK = 87,829,684,748 < 100,000,000,000` (over `10x` below the Yukon ceiling).
4. Full `InitE.Certificate` theorems for both `push31CandidateK` and `push31NoGcCandidateK`.
-/

namespace InitECandidate.Solver.SelfContainedPush31MasterK

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedStageBounds
open InitECandidate.Solver.SelfContainedPipelineBridge
open InitECandidate.Solver.SelfContainedMasterK
open InitECandidate.Solver.SelfContainedIsoReducedK
open InitECandidate.Solver.SelfContainedBasicBlockBridge
open InitECandidate.Solver.GuestEvmStepOpcodeBounds
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.StackLang

/-- Worst-case collision-free `PanSem` source clock driven by `PUSH31` (`18` ticks/gas):
`59,564,234 + 18 * 200,000,000 = 3,659,564,234`. -/
def push31SourceClock : Nat := 59_564_234 + 18 * 200_000_000

/-- Post-bootstrap RISC-V target ticks at `B_max = 8` and `isoFrontFactor = 6` (`C_sr = 2`). -/
def push31PostK : Nat := bMax * isoFrontFactor * (push31SourceClock + pipeOffset)

/-- Total RISC-V target budget for the collision-free `PUSH31` worst case at `frontFactor = 6`, `B_max = 8`:
`23,132 + 8 * 6 * (3,659,564,234 + 5,000) = 175,659,346,364`. -/
def push31CandidateK : Nat := 23_132 + 8 * 6 * (3_659_564_234 + 5_000)

/-- Front-end multiplier when `StackRemove` runs outside GC (`C_sr = 1`): `1 * 3 * 1 * 1 * 1 = 3`. -/
def noGcFrontFactor : Nat := 1 * 3 * 1 * 1 * 1

/-- Post-bootstrap RISC-V target ticks outside GC (`noGcFrontFactor = 3`, `B_max = 8`). -/
def push31NoGcPostK : Nat := bMax * noGcFrontFactor * (push31SourceClock + pipeOffset)

/-- Total RISC-V target budget for `PUSH31` with `C_sr = 1` outside GC (`frontFactor = 3`, `B_max = 8`):
`23,132 + 8 * 3 * (3,659,564,234 + 5,000) = 87,829,684,748`. -/
def push31NoGcCandidateK : Nat := 23_132 + 8 * 3 * (3_659_564_234 + 5_000)

/-- 1. `push31SourceClock` equals `GuestEvmStepOpcodeBounds.tightLinearClock = 3,659,564,234`
and is attained by `PUSH31` (`54` ticks / `3` gas = `18` ticks/gas). -/
theorem push31SourceClock_eq :
    push31SourceClock = 3_659_564_234 ∧
      push31SourceClock = GuestEvmStepOpcodeBounds.tightLinearClock ∧
      push31SourceClock = prologueTicks + 18 * SelfContainedMasterK.gasCap ∧
      GuestEvmStepOpcodeBounds.pushTicks 31 = 18 * 3 := by
  decide

/-- 2. Exact values and bootstrap + post-bootstrap decomposition for `push31CandidateK`. -/
theorem push31CandidateK_eq :
    push31CandidateK = 175_659_346_364 ∧
      push31PostK = 175_659_323_232 ∧
      push31CandidateK = bootstrapSteps + push31PostK := by
  refine ⟨by decide, by decide, ?_⟩
  rw [InitE.bootstrapSteps_eq]
  decide

/-- 3. `push31CandidateK` is more than `5x` below the Yukon IEEE-754 float64 ceiling
(`900,719,925,474`), and `5` is the exact integer multiple threshold (`6x` exceeds the ceiling). -/
theorem push31CandidateK_five_times_lt_ceiling :
    5 * push31CandidateK < 900_719_925_474 ∧
      5 * push31CandidateK = 878_296_731_820 ∧
      900_719_925_474 - 5 * push31CandidateK = 22_423_193_654 ∧
      ¬ 6 * push31CandidateK ≤ 900_719_925_474 := by
  decide

/-- 4. Outside GC (`C_sr = 1`, `noGcFrontFactor = 3`), `push31NoGcCandidateK = 87,829,684,748 < 100,000,000,000`
and is more than `10x` below the Yukon float64 ceiling. -/
theorem push31NoGcCandidateK_eq_and_lt_100B :
    noGcFrontFactor = 3 ∧
      push31NoGcCandidateK = 87_829_684_748 ∧
      push31NoGcPostK = 87_829_661_616 ∧
      push31NoGcCandidateK = bootstrapSteps + push31NoGcPostK ∧
      push31NoGcCandidateK < 100_000_000_000 ∧
      10 * push31NoGcCandidateK < 900_719_925_474 ∧
      ¬ 11 * push31NoGcCandidateK ≤ 900_719_925_474 := by
  refine ⟨by decide, by decide, by decide, ?_, by decide, by decide, by decide⟩
  rw [InitE.bootstrapSteps_eq]
  decide

/-- 5. Exact savings of `C_sr = 1` (`noGcFrontFactor = 3`) vs `C_sr = 2` (`isoFrontFactor = 6`),
and instantiation of the affine clock composition for `noGcFrontFactor = 3`. -/
theorem push31_nogc_saving_and_affine (d_pc d_cl d_sl d_ws k : Nat) :
    push31CandidateK - push31NoGcCandidateK = 87_829_661_616 ∧
      LoopWordStackExactClockIso.affine 1 d_sl
        (LoopWordStackExactClockIso.affine 1 d_ws
          (LoopWordStackExactClockIso.affine 1 0
            (LoopWordStackExactClockIso.affine 3 d_cl
              (LoopWordStackExactClockIso.affine 1 d_pc k)))) =
      LoopWordStackExactClockIso.affine noGcFrontFactor
        (1 * (3 * d_pc + d_cl + d_ws) + d_sl) k := by
  refine ⟨by decide, ?_⟩
  exact LoopWordStackExactClockIso.front_factor_after_iso 1 d_pc 3 d_cl 1 d_sl d_ws k

/-- 6. Exact front-factor threshold for staying below the Yukon float64 ceiling at `push31SourceClock`
and `B_max = 8`: the total budget stays below `900,719,925,474` iff `factor ≤ 30`. -/
theorem push31_front_factor_ceiling_threshold (factor : Nat) :
    bootstrapSteps + bMax * (factor * (push31SourceClock + pipeOffset)) < 900_719_925_474 ↔
      factor ≤ 30 := by
  rw [InitE.bootstrapSteps_eq]
  unfold bMax push31SourceClock pipeOffset
  omega

/-- 7. Tightness at the `175,659,346,364` and `87,829,684,748` boundaries (one tick below fails). -/
theorem push31_budget_one_tick_tight :
    (¬ bootstrapSteps + bMax * (isoFrontFactor * (push31SourceClock + pipeOffset)) ≤
        push31CandidateK - 1) ∧
      (¬ bootstrapSteps + bMax * (noGcFrontFactor * (push31SourceClock + pipeOffset)) ≤
        push31NoGcCandidateK - 1) := by
  rw [InitE.bootstrapSteps_eq]
  decide

/-- 8. Both `push31CandidateK` and `push31NoGcCandidateK` have strictly representable Yukon scores
below `2 ^ 53 - 1` for every verification time `minutes`. -/
theorem push31_yukonScore_representable (minutes : Nat) :
    yukonScore push31CandidateK minutes < 2 ^ 53 - 1 ∧
      yukonScore push31NoGcCandidateK minutes < 2 ^ 53 - 1 :=
  ⟨yukonScore_lt_two_pow_53_sub_one (by decide),
   yukonScore_lt_two_pow_53_sub_one (by decide)⟩

/-- 9. Uniform post-bootstrap `InitE.Certificate` for `push31CandidateK = 175,659,346,364`. -/
theorem self_contained_push31_master_certificate
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          push31CandidateK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK push31CandidateK) (.finite push31CandidateK) ∧
      5 * push31CandidateK < 900_719_925_474 ∧
      ∀ minutes, yukonScore push31CandidateK minutes < 2 ^ 53 - 1 := by
  have hdecomp : push31CandidateK = bootstrapSteps + push31PostK := push31CandidateK_eq.2.2
  have hcert : InitE.Certificate (baselineWithFiniteK push31CandidateK) (.finite push31CandidateK) := by
    rw [hdecomp] at not_timeOut ⊢
    exact finite_certificate_of_uniform_post_bootstrap_not_timeOut
      oracles c depth push31PostK hlab compiled depthBound not_timeOut
  exact ⟨hcert, push31CandidateK_five_times_lt_ceiling.1, fun m => (push31_yukonScore_representable m).1⟩

/-- 10. Uniform post-bootstrap `InitE.Certificate` for `push31NoGcCandidateK = 87,829,684,748` (`C_sr = 1`). -/
theorem self_contained_push31_nogc_master_certificate
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          push31NoGcCandidateK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK push31NoGcCandidateK) (.finite push31NoGcCandidateK) ∧
      push31NoGcCandidateK < 100_000_000_000 ∧
      ∀ minutes, yukonScore push31NoGcCandidateK minutes < 2 ^ 53 - 1 := by
  have hdecomp : push31NoGcCandidateK = bootstrapSteps + push31NoGcPostK :=
    push31NoGcCandidateK_eq_and_lt_100B.2.2.2.1
  have hcert : InitE.Certificate (baselineWithFiniteK push31NoGcCandidateK) (.finite push31NoGcCandidateK) := by
    rw [hdecomp] at not_timeOut ⊢
    exact finite_certificate_of_uniform_post_bootstrap_not_timeOut
      oracles c depth push31NoGcPostK hlab compiled depthBound not_timeOut
  exact ⟨hcert, push31NoGcCandidateK_eq_and_lt_100B.2.2.2.2.1,
    fun m => (push31_yukonScore_representable m).2⟩

/-- 11. End-to-end 5-stage pipeline `InitE.Certificate` at `push31CandidateK = 175,659,346,364`. -/
theorem end_to_end_push31_iso_finite_certificate
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (k_pan k_word k_stack k_lab : Guest.InputBlob → Nat)
    (pan_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory),
          decsStcnamesHOLExact [] sourceDeclarations = some stCtxt →
          @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
            { sourceInitialState input with structs := stCtxt }
            (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
            sourceDeclarations = some s_decls →
          (PanSemStateFiniteExact.evaluateHOLFiniteState
            { s_decls with clock := k_pan input }
            (.call none (ofString "main") [] : ProgHOL 64)).1 ≠ some .timeOut)
    (word_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (WordSemStateFiniteExact.evaluate
            (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
            { pipelinePanToWordInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 620 ltconf sourceDeclarations wprog
                InitECandidate.bitmaps p 0 with clock := k_word input }).1 ≠ some .timeOut)
    (stack_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (StackSemEvaluate.evaluate
            ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64),
              { pipelineStackInitState (oracleCompilerConfig oracles) baselineMachineConfig
                  (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                  InitECandidate.nativeCode 620 ltconf InitECandidate.bitmaps p 0 with
                  clock := k_stack input })).1 ≠ some .timeOut)
    (lab_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (LabSem.evaluate
            { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 620 ltconf p with
                clock := k_lab input }).1 ≠ .timeOut)
    (target_not_timeOut_of_lab_halt : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (LabSem.evaluate
            { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 620 ltconf p with
                clock := k_lab input }).1 = .halt outcome →
          (LabSem.evaluate
            { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 620 ltconf p with
                clock := k_lab input }).2.ffi.ioEvents = events →
          (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
            push31CandidateK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK push31CandidateK)
      (.finite push31CandidateK) := by
  rw [push31CandidateK_eq.2.2] at target_not_timeOut_of_lab_halt ⊢
  exact finite_certificate_of_source_to_target_clock_chain
    oracles c depth push31PostK hlab compiled depthBound
    k_pan k_word k_stack k_lab pan_not_timeOut word_not_timeOut
    stack_not_timeOut lab_not_timeOut target_not_timeOut_of_lab_halt

#print axioms push31SourceClock_eq
#print axioms push31CandidateK_eq
#print axioms push31CandidateK_five_times_lt_ceiling
#print axioms push31NoGcCandidateK_eq_and_lt_100B
#print axioms push31_nogc_saving_and_affine
#print axioms push31_front_factor_ceiling_threshold
#print axioms push31_budget_one_tick_tight
#print axioms push31_yukonScore_representable
#print axioms self_contained_push31_master_certificate
#print axioms self_contained_push31_nogc_master_certificate
#print axioms end_to_end_push31_iso_finite_certificate

end InitECandidate.Solver.SelfContainedPush31MasterK
