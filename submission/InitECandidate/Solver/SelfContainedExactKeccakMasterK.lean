import InitECandidate.Solver.SelfContainedIsoReducedK

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
Exact arithmetic for the extracted worst-alignment tick envelope. As in
GuestKeccakAndMptExactTicks this is NOT a PanSem execution equality: that
module's hand-extracted bounds are not connected to the guest AST here.
Certificates retain the explicit stage non-timeout and compilation obligations.
The only import has no Proofs/Bounded* dependencies.
-/
namespace InitECandidate.Solver.SelfContainedExactKeccakMasterK

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedStageBounds
open InitECandidate.Solver.YukonCleanVerifierCheck (baselineHeapLen baseline_pan_installed oracle_baseline_installation)
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanToTarget (semanticsDecls_mainFirstHOL)
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.LoopToWordStateRelImpSemanticsSupport


open InitECandidate.Solver
open InitECandidate.Solver.SelfContainedMasterK
open InitECandidate.Solver.SelfContainedPipelineBridge
open InitECandidate.Solver.SelfContainedIsoReducedK (isoFrontFactor)


def keccakBaseTicks : Nat := 74
def keccakBlockTicks : Nat := 19
def mptNodeTicks : Nat := 633
def mptKeyTicks : Nat := 40_512
def epiBaseTicks : Nat := 7
/-- Extracted uniform bound, exact as an arithmetic formula. -/
def keccak256Ticks (n : Nat) : Nat := keccakBaseTicks + keccakBlockTicks * (n / 136 + 1)
def keccakGas (n : Nat) : Nat := 30 + 6 * ((n + 31) / 32)
def exactKeccakLoopTicks : Nat := gasCap / keccakGas 0 * keccak256Ticks 0
def exactKeccak128LoopTicks : Nat := gasCap / keccakGas 128 * keccak256Ticks 128
def exactKeccakSourceClock : Nat := prologueTicks + exactKeccakLoopTicks + epiBaseTicks
def exactKeccak128SourceClock : Nat := prologueTicks + exactKeccak128LoopTicks + epiBaseTicks
def exactKeccakPostK : Nat := bMax * isoFrontFactor * (exactKeccakSourceClock + pipeOffset)
def exactKeccak128PostK : Nat := bMax * isoFrontFactor * (exactKeccak128SourceClock + pipeOffset)
def exactKeccakCandidateK : Nat := 23_132 + exactKeccakPostK
def exactKeccak128CandidateK : Nat := 23_132 + exactKeccak128PostK

theorem keccak_ticks_formula (n : Nat) :
    keccak256Ticks n = 74 + 19 * (n / 136 + 1) := rfl

theorem keccak_one_block (n : Nat) (hn : n < 136) : keccak256Ticks n = 93 := by
  unfold keccak256Ticks keccakBaseTicks keccakBlockTicks
  rw [Nat.div_eq_of_lt hn]

theorem keccak_zero_ticks : keccak256Ticks 0 = 93 := by decide
theorem keccak_128_ticks : keccak256Ticks 128 = 93 := by decide
theorem keccak_128_words : (128 + 31) / 32 = (4 : Nat) := by decide
theorem keccak_128_gas : keccakGas 128 = 54 := by decide
theorem keccak_zero_gas : keccakGas 0 = 30 := by decide
theorem keccak_128_below_two_ticks_per_gas : keccak256Ticks 128 < 2 * keccakGas 128 := by decide
theorem keccak_zero_loop_eq : exactKeccakLoopTicks = 619_999_938 := by decide
theorem keccak_128_loop_eq : exactKeccak128LoopTicks = 344_444_379 := by decide
theorem mpt_per_key_eq : mptKeyTicks = 64 * mptNodeTicks := by decide
theorem epi_base_eq : epiBaseTicks = 7 := rfl
theorem exact_source_clock_eq : exactKeccakSourceClock = 679_564_179 := by decide
theorem exact_128_source_clock_eq : exactKeccak128SourceClock = 404_008_620 := by decide
theorem exact_candidate_eq : exactKeccakCandidateK = 32_619_343_724 := by decide
theorem exact_128_candidate_eq : exactKeccak128CandidateK = 19_392_676_892 := by decide
/-- The requested 128-byte advertised ceiling is valid with 40 ticks of slack.
The exact division is 344444379, not 344444391. -/
theorem exact_128_advertised_budget_slack :
    exactKeccak128CandidateK + 40 = 19_392_676_932 := by decide

theorem exact_128_advertised_budget_valid :
    exactKeccak128CandidateK ≤ 19_392_676_932 := by decide

theorem exact_budget_27x_below_ceiling : 27 * exactKeccakCandidateK < 900_719_925_474 := by decide
theorem exact_budget_ratio_floor : 900_719_925_474 / exactKeccakCandidateK = 27 := by decide
theorem exact_budget_below_ceiling : exactKeccakCandidateK < 900_719_925_474 := by decide
theorem exact_128_below_20_billion : exactKeccak128CandidateK < 20_000_000_000 := by decide
theorem exact_128_below_zero : exactKeccak128CandidateK < exactKeccakCandidateK := by decide

theorem exact_budget_decomposition : exactKeccakCandidateK = bootstrapSteps + exactKeccakPostK := by
  rw [InitE.bootstrapSteps_eq]; rfl

theorem exact_128_budget_decomposition : exactKeccak128CandidateK = bootstrapSteps + exactKeccak128PostK := by
  rw [InitE.bootstrapSteps_eq]; rfl

theorem exact_budget_one_tick_tight :
    ¬ bootstrapSteps + bMax * isoFrontFactor * (exactKeccakSourceClock + pipeOffset) ≤
      exactKeccakCandidateK - 1 := by
  rw [InitE.bootstrapSteps_eq]; decide

theorem exact_128_budget_one_tick_tight :
    ¬ bootstrapSteps + bMax * isoFrontFactor * (exactKeccak128SourceClock + pipeOffset) ≤
      exactKeccak128CandidateK - 1 := by
  rw [InitE.bootstrapSteps_eq]; decide

theorem exact_score_representable (minutes : Nat) :
    yukonScore exactKeccakCandidateK minutes < 2 ^ 53 - 1 :=
  yukonScore_lt_two_pow_53_sub_one (by decide)

theorem exact_128_score_representable (minutes : Nat) :
    yukonScore exactKeccak128CandidateK minutes < 2 ^ 53 - 1 :=
  yukonScore_lt_two_pow_53_sub_one (by decide)

theorem end_to_end_exact_keccak_finite_certificate
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
            exactKeccakCandidateK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK exactKeccakCandidateK)
      (.finite exactKeccakCandidateK) := by
  rw [exact_budget_decomposition] at target_not_timeOut_of_lab_halt ⊢
  exact finite_certificate_of_source_to_target_clock_chain
    oracles c depth exactKeccakPostK hlab compiled depthBound
    k_pan k_word k_stack k_lab pan_not_timeOut word_not_timeOut
    stack_not_timeOut lab_not_timeOut target_not_timeOut_of_lab_halt

theorem end_to_end_exact_keccak_128_finite_certificate
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
            exactKeccak128CandidateK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK exactKeccak128CandidateK)
      (.finite exactKeccak128CandidateK) := by
  rw [exact_128_budget_decomposition] at target_not_timeOut_of_lab_halt ⊢
  exact finite_certificate_of_source_to_target_clock_chain
    oracles c depth exactKeccak128PostK hlab compiled depthBound
    k_pan k_word k_stack k_lab pan_not_timeOut word_not_timeOut
    stack_not_timeOut lab_not_timeOut target_not_timeOut_of_lab_halt


#print axioms keccak_ticks_formula
#print axioms keccak_one_block
#print axioms keccak_zero_ticks
#print axioms keccak_128_ticks
#print axioms keccak_128_words
#print axioms keccak_128_gas
#print axioms keccak_zero_gas
#print axioms keccak_128_below_two_ticks_per_gas
#print axioms keccak_zero_loop_eq
#print axioms keccak_128_loop_eq
#print axioms mpt_per_key_eq
#print axioms epi_base_eq
#print axioms exact_source_clock_eq
#print axioms exact_128_source_clock_eq
#print axioms exact_candidate_eq
#print axioms exact_128_candidate_eq
#print axioms exact_128_advertised_budget_slack
#print axioms exact_128_advertised_budget_valid
#print axioms exact_budget_27x_below_ceiling
#print axioms exact_budget_ratio_floor
#print axioms exact_budget_below_ceiling
#print axioms exact_128_below_20_billion
#print axioms exact_128_below_zero
#print axioms exact_budget_decomposition
#print axioms exact_128_budget_decomposition
#print axioms exact_budget_one_tick_tight
#print axioms exact_128_budget_one_tick_tight
#print axioms exact_score_representable
#print axioms exact_128_score_representable
#print axioms end_to_end_exact_keccak_finite_certificate
#print axioms end_to_end_exact_keccak_128_finite_certificate

end InitECandidate.Solver.SelfContainedExactKeccakMasterK
