import InitE
import InitECandidate.Proofs.CompilerComputation
import InitECandidate.Proofs.BaselineInstallationFacts
import InitECandidate.Proofs.OracleBaselineCorrectness
import InitECandidate.Proofs.PanInstallation
import InitE.TargetTotality
import InitECandidate.Proofs.InstallationTransport
import InitECandidate.Proofs.StartupEnvironment
import InitECandidate.Proofs.BootstrapTrace
import InitECandidate.Proofs.BootstrapComposition
import InitECandidate.Proofs.BaselineSubmission

open scoped InitECandidate.Proofs.CompilerComputation

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false

namespace InitE
open InitECandidate.Proofs
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Pancake.Proofs.PanToTarget

set_option maxRecDepth 100000

/-- Heap-shaped domain size, including the globals reserved at its upper end. -/
def baselineHeapLen : Nat := (stackStart - sourceBase) / 8

def baselineAdj2 : BitVec 64 := BitVec.ofNat 64 sourceBase +
  (8 : BitVec 64) * BitVec.ofNat 64 StackRemove.maxStackAlloc

def baselineAdj4 : BitVec 64 := BitVec.ofNat 64 ramEnd -
  (8 : BitVec 64) * BitVec.ofNat 64 StackRemove.maxStackAlloc

/-- Remaining numeric and register premises for `OracleBaselineInstallation`,
decoupled from the 46,000-file artifact stage tree. -/
theorem oracle_baseline_installation (input : Guest.InputBlob)
    (c : Backend.Config)
    (memory : panInstalled InitECandidate.nativeCode 620 InitECandidate.bitmaps 0
      c.labConf.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig c.labConf.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs) :
    OracleBaselineInstallation input baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode InitECandidate.bitmaps c baselineHeapLen
      baselineAdj2 baselineAdj4 620 0 := by
  refine ⟨baseline_machine_isRiscv,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, memory, ?_⟩
  · change (0 : BitVec 64) < BitVec.ofNat 64 sourceBase
    decide_cbv
  · change BitVec.ofNat 64 sourceBase < BitVec.ofNat 64 stackStart
    decide_cbv
  · rfl
  · change baselineHeapLen = (BitVec.ofNat 64 stackStart +
      -1 * BitVec.ofNat 64 sourceBase).toNat / (64 / 8)
    decide_cbv
  · change BitVec.ofNat 64 heapEnd = BitVec.ofNat 64 sourceBase +
      (wordSemBytesInWord : BitVec 64) * BitVec.ofNat 64 baselineHeapLen -
        BitVec.ofNat 64 (globalsWords * 64 / 8)
    decide_cbv
  · decide_cbv
  · rfl
  · change holAligned (wordShiftAmount 64 + 1)
      (BitVec.ofNat 64 stackStart + -1 * BitVec.ofNat 64 sourceBase) = true
    decide_cbv
  · rfl
  · rfl
  · change baselineAdj2 ≤ BitVec.ofNat 64 stackStart
    decide_cbv
  · change BitVec.ofNat 64 stackStart ≤ baselineAdj4
    decide_cbv
  · change (BitVec.ofNat 64 stackStart + -1 * BitVec.ofNat 64 sourceBase).toNat ≤
      (wordSemBytesInWord : BitVec 64).toNat *
        (2 * DataToWord.maxHeapLimit 64 pancakeRiscVBackendConfig.dataConf - 1)
    decide_cbv
  · rfl
  · have names :
        (StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 2,
         StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 3,
         StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 4) =
          (11,12,13) := by decide_cbv
    have n2 := congrArg Prod.fst names
    have n3 := congrArg (fun p => p.2.1) names
    have n4 := congrArg (fun p => p.2.2) names
    dsimp only at n2 n3 n4
    simp only [readLimits, n2, n3, n4]
    rfl

/-- Concrete pre-transport oracle installation witness for `baselineConfigLiteral`. -/
theorem oracle_baseline_installed (input : Guest.InputBlob) :
    OracleBaselineInstallation input baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode InitECandidate.bitmaps baselineConfigLiteral
      baselineHeapLen baselineAdj2 baselineAdj4 620 0 :=
  oracle_baseline_installation input baselineConfigLiteral (baseline_pan_installed input)

/-- Oracle installations are stable under the machine projection agreement
established by the bootstrap. -/
theorem oracle_baseline_installation_transport (input : Guest.InputBlob)
    (c : Backend.Config)
    (ms : RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm ms)
    (installed : OracleBaselineInstallation input baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 620 0) :
    OracleBaselineInstallation input baselineMachineConfig ms
      InitECandidate.nativeCode InitECandidate.bitmaps c baselineHeapLen
      baselineAdj2 baselineAdj4 620 0 := by
  have agreement := baseline_endpoint_agreement ms related
  have r11 := agreement.regs 11 (by decide)
  have r12 := agreement.regs 12 (by decide)
  have r13 := agreement.regs 13 (by decide)
  have names :
      (StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 2,
       StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 3,
       StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 4) =
         (11,12,13) := by decide_cbv
  have n2 := congrArg Prod.fst names
  have n3 := congrArg (fun p => p.2.1) names
  have n4 := congrArg (fun p => p.2.2) names
  dsimp only at n2 n3 n4
  have limits : readLimits baselineMachineConfig.target.config pancakeRiscVBackendConfig
      baselineMachineConfig ms = readLimits baselineMachineConfig.target.config
        pancakeRiscVBackendConfig baselineMachineConfig baselineInstalledState := by
    simp only [readLimits, n2, n3, n4, r11, r12, r13]
  have rlen : baselineMachineConfig.target.getReg ms baselineMachineConfig.lenReg =
      baselineMachineConfig.target.getReg baselineInstalledState baselineMachineConfig.lenReg := r11
  have rptr : baselineMachineConfig.target.getReg ms baselineMachineConfig.ptr2Reg =
      baselineMachineConfig.target.getReg baselineInstalledState baselineMachineConfig.ptr2Reg := r12
  have rlen2 : baselineMachineConfig.target.getReg ms baselineMachineConfig.len2Reg =
      baselineMachineConfig.target.getReg baselineInstalledState baselineMachineConfig.len2Reg := r13
  rcases installed with ⟨hmc, hpositive, hsplit, hbase, hlen, htop, hglobals,
    hdomain, haligned, hadj2, hadj4, hleft, hright, hmax, hendian, hmemory, hlimits⟩
  have memory := panInstalled_transport agreement hmemory
  unfold OracleBaselineInstallation
  simp only [rlen, rptr, rlen2, limits]
  exact ⟨hmc, hpositive, hsplit, hbase, hlen, htop, hglobals, hdomain,
    haligned, hadj2, hadj4, hleft, hright, hmax, hendian, memory, hlimits⟩

/-- Compiler correctness at whichever concrete machine startup reaches, parameterized
only by the oracle compilation equation and stack depth bound. -/
theorem oracle_baseline_endpoint_behaviour_eq (oracles : List (Option (Spt Nat)))
    (input : Guest.InputBlob)
    (c : Backend.Config) (depth : Nat)
    (ms : RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm ms)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (installed : OracleBaselineInstallation input baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 620 0)
    (nonfail : sourceBehaviour input ≠ HolBehaviour.fail) :
    ∀ behaviour, machineSemHOL baselineMachineConfig (sourceFfi input) ms behaviour →
      behaviour = sourceBehaviour input :=
  oracle_baseline_behaviour_eq oracles input baselineMachineConfig ms
    InitECandidate.nativeCode InitECandidate.bitmaps c depth baselineHeapLen
    baselineAdj2 baselineAdj4 620 0 compiled depthBound
    (oracle_baseline_installation_transport input c ms related installed) nonfail

/-- Source termination yields a finite target Halt witness with the same full
observable behavior, parameterized only by the oracle compilation equation and stack bound. -/
theorem oracle_baseline_endpoint_terminates (oracles : List (Option (Spt Nat)))
    (input : Guest.InputBlob)
    (c : Backend.Config) (depth : Nat)
    (ms : RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm ms)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (installed : OracleBaselineInstallation input baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 620 0)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (source : sourceBehaviour input = .terminate outcome events) :
    machineSemHOL baselineMachineConfig (sourceFfi input) ms (.terminate outcome events) ∧
      targetTerminatesWithin .infinity baselineMachineConfig (sourceFfi input) ms := by
  have nonfail : sourceBehaviour input ≠ HolBehaviour.fail := by
    rw [source]
    intro impossible
    cases impossible
  have correct := oracle_baseline_endpoint_behaviour_eq oracles input c depth ms
    related compiled depthBound installed nonfail
  have termination := target_termination_of_behaviour_eq baselineMachineConfig
    (sourceFfi input) ms outcome events (fun b hb => (correct b hb).trans source)
  exact ⟨termination, (target_termination_iff_infinity _ _ _).mp
    ⟨outcome, events, termination⟩⟩

/-- Exact 23,132-step bootstrap clock shift from `baselineInitialState` to `installedAsm`. -/
theorem full_baseline_evaluator_exact (input : Guest.InputBlob) :
    ∃ post,
      (∀ clock, evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        (bootstrapSteps + clock) (baselineInitialState input) =
        evaluateTargetHOL baselineMachineConfig (sourceFfi input) clock post) ∧
      targetStateRel riscvTarget installedAsm post :=
  BootstrapTrace.full_evaluator_exact
    (sourceFfi input) (baselineInitialState input) (baselineInitialState_related input)

/-- Full end-to-end correctness from `baselineInitialState` (including the 23,132-step
zero-RAM bootstrap), parameterized only by the oracle compilation equation and stack bound. -/
theorem oracle_full_baseline_correct (oracles : List (Option (Spt Nat)))
    (input : Guest.InputBlob)
    (c : Backend.Config) (depth : Nat)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (installed : OracleBaselineInstallation input baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 620 0)
    (nonfail : sourceBehaviour input ≠ HolBehaviour.fail) :
    ∀ behaviour,
      machineSemHOL baselineMachineConfig (sourceFfi input)
        (baselineInitialState input) behaviour →
      behaviour = sourceBehaviour input := by
  obtain ⟨post, shift, related⟩ := full_baseline_evaluator_exact input
  exact Bootstrap.behavior_property_from_clock_shift (sourceFfi input) shift
    (fun behaviour => behaviour = sourceBehaviour input)
    (oracle_baseline_endpoint_behaviour_eq oracles input c depth post related
      compiled depthBound installed nonfail)

/-- End-to-end `InitE.Certificate baselineSubmission .infinity` parameterized only by
the oracle compilation equation and stack depth bound (zero stage files required). -/
theorem oracle_full_baseline_certificate (oracles : List (Option (Spt Nat)))
    (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480) :
    InitE.Certificate baselineSubmission .infinity := by
  apply InitE.certificate_of_exact_behaviour baselineSubmission rfl baselineSubmission_admitted
  intro input outcome events source behaviour execution
  have nonfail : sourceBehaviour input ≠ HolBehaviour.fail := by
    rw [source]
    intro impossible
    cases impossible
  change machineSemHOL baselineSubmission.machineConfig (sourceFfi input)
    (baselineSubmission.initialState input) behaviour at execution
  rw [baselineSubmission_machineConfig, baselineSubmission_initialState] at execution
  have hmem : panInstalled InitECandidate.nativeCode 620 InitECandidate.bitmaps 0
      c.labConf.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig c.labConf.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs := by
    rw [hlab]
    exact baseline_pan_installed input
  have hinst := oracle_baseline_installation input c hmem
  exact (oracle_full_baseline_correct oracles input c depth compiled depthBound hinst nonfail
    behaviour execution).trans source

end InitE
