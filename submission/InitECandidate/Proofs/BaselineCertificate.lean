import InitECandidate.Proofs.CompilerComputation
import InitECandidate.Proofs.BaselineInstallationFacts
import InitECandidate.Proofs.BaselineCorrectness
import InitECandidate.Proofs.OracleBaselineCertificate
import InitE.TargetTotality
import InitECandidate.Proofs.InstallationTransport

open scoped InitECandidate.Proofs.CompilerComputation

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false

namespace InitE
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Pancake.Proofs.PanToTarget

set_option maxRecDepth 100000

/-- Remaining numeric and register premises are fixed baseline facts, rather
than requirements on inputs or assumptions supplied by a participant. -/
theorem baseline_installation (input : Guest.InputBlob)
    (memory : panInstalled InitECandidate.nativeCode 620 InitECandidate.bitmaps 0
      baselineConfig.labConf.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig baselineConfig.labConf.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs) :
    BaselineInstallation input baselineOutput baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode InitECandidate.bitmaps baselineConfig baselineHeapLen
      baselineAdj2 baselineAdj4 620 0 := by
  obtain ⟨hmc, hpositive, hsplit, hbase, hlen, htop, hglobals, hdomain,
    haligned, hadj2, hadj4, hleft, hright, hmax, hendian, hmemory, hlimits⟩ :=
    oracle_baseline_installation input baselineConfig memory
  exact ⟨hmc, baseline_artifact_complete, hpositive, hsplit, hbase, hlen, htop,
    hglobals, hdomain, haligned, hadj2, hadj4, hleft, hright, hmax, hendian,
    hmemory, hlimits⟩

/-- Compiler-derived behavior equality at the actual native entry. -/
theorem baseline_native_behaviour_eq (input : Guest.InputBlob)
    (installation : BaselineInstallation input baselineOutput baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      baselineConfig baselineHeapLen baselineAdj2 baselineAdj4 620 0)
    (nonfail : sourceBehaviour input ≠ HolBehaviour.fail) :
    ∀ behaviour, machineSemHOL baselineMachineConfig (sourceFfi input)
      baselineInstalledState behaviour → behaviour = sourceBehaviour input :=
  baseline_behaviour_eq input baselineOutput baseline_ast_compilation
    baselineMachineConfig baselineInstalledState InitECandidate.nativeCode
    InitECandidate.bitmaps baselineConfig baselineHeapLen baselineAdj2 baselineAdj4
    620 0 installation nonfail

/-- Installations are stable under the machine projection agreement established
by the bootstrap, including the precise compiler resource limits. -/
theorem baseline_installation_transport (input : Guest.InputBlob)
    (ms : RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm ms)
    (installed : BaselineInstallation input baselineOutput baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      baselineConfig baselineHeapLen baselineAdj2 baselineAdj4 620 0) :
    BaselineInstallation input baselineOutput baselineMachineConfig ms
      InitECandidate.nativeCode InitECandidate.bitmaps baselineConfig baselineHeapLen
      baselineAdj2 baselineAdj4 620 0 := by
  rcases installed with ⟨hmc, hart, hpositive, hsplit, hbase, hlen, htop, hglobals,
    hdomain, haligned, hadj2, hadj4, hleft, hright, hmax, hendian, hmemory, hlimits⟩
  obtain ⟨hmc', hpositive', hsplit', hbase', hlen', htop', hglobals', hdomain',
    haligned', hadj2', hadj4', hleft', hright', hmax', hendian', hmemory', hlimits'⟩ :=
    oracle_baseline_installation_transport input baselineConfig ms related
      ⟨hmc, hpositive, hsplit, hbase, hlen, htop, hglobals, hdomain, haligned,
       hadj2, hadj4, hleft, hright, hmax, hendian, hmemory, hlimits⟩
  exact ⟨hmc', hart, hpositive', hsplit', hbase', hlen', htop', hglobals',
    hdomain', haligned', hadj2', hadj4', hleft', hright', hmax', hendian',
    hmemory', hlimits'⟩

/-- Compiler correctness at whichever concrete machine startup reaches. -/
theorem baseline_endpoint_behaviour_eq (input : Guest.InputBlob)
    (ms : RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm ms)
    (installed : BaselineInstallation input baselineOutput baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      baselineConfig baselineHeapLen baselineAdj2 baselineAdj4 620 0)
    (nonfail : sourceBehaviour input ≠ HolBehaviour.fail) :
    ∀ behaviour, machineSemHOL baselineMachineConfig (sourceFfi input) ms behaviour →
      behaviour = sourceBehaviour input :=
  baseline_behaviour_eq input baselineOutput baseline_ast_compilation
    baselineMachineConfig ms InitECandidate.nativeCode InitECandidate.bitmaps
    baselineConfig baselineHeapLen baselineAdj2 baselineAdj4 620 0
    (baseline_installation_transport input ms related installed) nonfail

/-- Source termination yields a finite target Halt witness with the same full
observable behavior, despite the literal infinite score. -/
theorem baseline_endpoint_terminates (input : Guest.InputBlob)
    (ms : RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm ms)
    (installed : BaselineInstallation input baselineOutput baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      baselineConfig baselineHeapLen baselineAdj2 baselineAdj4 620 0)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (source : sourceBehaviour input = .terminate outcome events) :
    machineSemHOL baselineMachineConfig (sourceFfi input) ms (.terminate outcome events) ∧
      targetTerminatesWithin .infinity baselineMachineConfig (sourceFfi input) ms := by
  have nonfail : sourceBehaviour input ≠ HolBehaviour.fail := by
    rw [source]
    intro impossible
    cases impossible
  have correct := baseline_endpoint_behaviour_eq input ms related installed nonfail
  have termination := target_termination_of_behaviour_eq baselineMachineConfig
    (sourceFfi input) ms outcome events (fun b hb => (correct b hb).trans source)
  exact ⟨termination, (target_termination_iff_infinity _ _ _).mp
    ⟨outcome, events, termination⟩⟩

end InitE
