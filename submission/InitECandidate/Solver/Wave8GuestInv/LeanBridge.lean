import InitE.Challenge
import InitECandidate.Proofs.OracleBaselineCorrectness
import InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.InstallationTransport
import InitECandidate.Solver.Wave8GuestInv.FiniteRebudget
import InitECandidate.Solver.Wave8Stage.ConcreteBaseline.ExactBootstrap
import InitECandidate.Solver.Wave8Stage.ConcreteStage5
import InitECandidate.Solver.Wave8Stage.PipelineIntegration

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8GuestInv.LeanBridge

open Classical InitE InitECandidate.Proofs
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Stage
open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Pancake.Proofs.PanToTarget

def baselineHeapLen : Nat := (stackStart - sourceBase) / 8

def baselineAdj2 : BitVec 64 := BitVec.ofNat 64 sourceBase +
  (8 : BitVec 64) * BitVec.ofNat 64 StackRemove.maxStackAlloc

def baselineAdj4 : BitVec 64 := BitVec.ofNat 64 ramEnd -
  (8 : BitVec 64) * BitVec.ofNat 64 StackRemove.maxStackAlloc

structure ConcreteOracleCompilationWitness : Type where
  oracles : List (Option (Spt Nat))
  c : Backend.Config
  depth : Nat
  hlab : c.labConf = baselineLabConfig
  compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
    sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth)
  depthBound : depth ≤ 7480

open scoped InitECandidate.Proofs.CompilerComputation in
set_option maxRecDepth 100000 in
theorem oracle_baseline_installation (input : Guest.InputBlob)
    (c : Backend.Config)
    (memory : panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      c.labConf.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      ArtifactEnv.baselineMachineConfig c.labConf.shmemExtra ArtifactEnv.baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs) :
    OracleBaselineInstallation input ArtifactEnv.baselineMachineConfig ArtifactEnv.baselineInstalledState
      InitECandidate.nativeCode InitECandidate.bitmaps c baselineHeapLen
      baselineAdj2 baselineAdj4 3788 0 := by
  refine ⟨ArtifactEnv.baseline_machine_isRiscv,
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
          (11, 12, 13) := by decide_cbv
    have n2 := congrArg Prod.fst names
    have n3 := congrArg (fun p => p.2.1) names
    have n4 := congrArg (fun p => p.2.2) names
    dsimp only at n2 n3 n4
    simp only [readLimits, n2, n3, n4]
    rfl

open scoped InitECandidate.Proofs.CompilerComputation in
set_option maxRecDepth 100000 in
theorem oracle_baseline_installation_transport (input : Guest.InputBlob)
    (c : Backend.Config)
    (ms : RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm ms)
    (installed : OracleBaselineInstallation input ArtifactEnv.baselineMachineConfig
      ArtifactEnv.baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 3788 0) :
    OracleBaselineInstallation input ArtifactEnv.baselineMachineConfig ms
      InitECandidate.nativeCode InitECandidate.bitmaps c baselineHeapLen
      baselineAdj2 baselineAdj4 3788 0 := by
  have agreement := ArtifactEnv.baseline_endpoint_agreement ms related
  have r11 := agreement.regs 11 (by decide)
  have r12 := agreement.regs 12 (by decide)
  have r13 := agreement.regs 13 (by decide)
  have names :
      (StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 2,
       StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 3,
       StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 4) =
         (11, 12, 13) := by decide_cbv
  have n2 := congrArg Prod.fst names
  have n3 := congrArg (fun p => p.2.1) names
  have n4 := congrArg (fun p => p.2.2) names
  dsimp only at n2 n3 n4
  have limits : readLimits ArtifactEnv.baselineMachineConfig.target.config pancakeRiscVBackendConfig
      ArtifactEnv.baselineMachineConfig ms =
        readLimits ArtifactEnv.baselineMachineConfig.target.config
          pancakeRiscVBackendConfig ArtifactEnv.baselineMachineConfig
          ArtifactEnv.baselineInstalledState := by
    simp only [readLimits, n2, n3, n4, r11, r12, r13]
  have rlen : ArtifactEnv.baselineMachineConfig.target.getReg ms
      ArtifactEnv.baselineMachineConfig.lenReg =
        ArtifactEnv.baselineMachineConfig.target.getReg
          ArtifactEnv.baselineInstalledState ArtifactEnv.baselineMachineConfig.lenReg := r11
  have rptr : ArtifactEnv.baselineMachineConfig.target.getReg ms
      ArtifactEnv.baselineMachineConfig.ptr2Reg =
        ArtifactEnv.baselineMachineConfig.target.getReg
          ArtifactEnv.baselineInstalledState ArtifactEnv.baselineMachineConfig.ptr2Reg := r12
  have rlen2 : ArtifactEnv.baselineMachineConfig.target.getReg ms
      ArtifactEnv.baselineMachineConfig.len2Reg =
        ArtifactEnv.baselineMachineConfig.target.getReg
          ArtifactEnv.baselineInstalledState ArtifactEnv.baselineMachineConfig.len2Reg := r13
  rcases installed with ⟨hmc, hpositive, hsplit, hbase, hlen, htop, hglobals,
    hdomain, haligned, hadj2, hadj4, hleft, hright, hmax, hendian, hmemory, hlimits⟩
  have memory := ArtifactEnv.panInstalled_transport agreement hmemory
  unfold OracleBaselineInstallation
  simp only [rlen, rptr, rlen2, limits]
  exact ⟨hmc, hpositive, hsplit, hbase, hlen, htop, hglobals, hdomain,
    haligned, hadj2, hadj4, hleft, hright, hmax, hendian, memory, hlimits⟩

theorem config_eq : ConcreteBaseline.baselineMachineConfig = ArtifactEnv.baselineMachineConfig := by
  have hn : ConcreteBaseline.baselineNames = ArtifactEnv.baselineNames := by
    unfold ConcreteBaseline.baselineNames ArtifactEnv.baselineNames
    rfl
  have hm : ConcreteBaseline.baselineMmio = ArtifactEnv.baselineMmio := by
    unfold ConcreteBaseline.baselineMmio ArtifactEnv.baselineMmio
    rfl
  unfold ConcreteBaseline.baselineMachineConfig ArtifactEnv.baselineMachineConfig
    ConcreteBaseline.programDomain ArtifactEnv.programDomain
  rw [hn, hm]

theorem initial_eq (input : Guest.InputBlob) :
    ConcreteBaseline.baselineInitialState input = ArtifactEnv.baselineInitialState input := rfl

theorem oracle_full_baseline_terminates
    (w : ConcreteOracleCompilationWitness)
    (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (source : sourceBehaviour input = .terminate outcome events) :
    machineSemHOL ArtifactEnv.baselineMachineConfig (sourceFfi input)
      (ArtifactEnv.baselineInitialState input) (.terminate outcome events) := by
  have hmem : panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      w.c.labConf.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      ArtifactEnv.baselineMachineConfig w.c.labConf.shmemExtra ArtifactEnv.baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs := by
    rw [w.hlab]
    exact ArtifactEnv.baseline_pan_installed input
  have hinst := oracle_baseline_installation input w.c hmem
  obtain ⟨post, shift, _, related⟩ := ConcreteBaseline.ExactBootstrap.full_evaluator_exact
    (sourceFfi input) (ConcreteBaseline.baselineInitialState input)
    (ConcreteBaseline.baselineInitialState_related input)
  rw [config_eq, initial_eq] at shift
  have nonfail : sourceBehaviour input ≠ HolBehaviour.fail := by
    rw [source]
    intro impossible
    cases impossible
  have correct := oracle_baseline_behaviour_eq w.oracles input
    ArtifactEnv.baselineMachineConfig post InitECandidate.nativeCode
    InitECandidate.bitmaps w.c w.depth baselineHeapLen baselineAdj2 baselineAdj4
    3788 0 w.compiled w.depthBound
    (oracle_baseline_installation_transport input w.c post related hinst) nonfail
  have postTerm := target_termination_of_behaviour_eq ArtifactEnv.baselineMachineConfig
    (sourceFfi input) post outcome events (fun b hb => (correct b hb).trans source)
  obtain ⟨k0, ms0, ffi0, run0, io0⟩ := postTerm
  exact ⟨bootstrapSteps + k0, ms0, ffi0, (shift k0).trans run0, io0⟩

theorem baseline_infinity_certificate (w : ConcreteOracleCompilationWitness) :
    InitE.Certificate ArtifactEnv.baselineSubmission .infinity := by
  apply InitE.certificate_of_exact_behaviour ArtifactEnv.baselineSubmission rfl
    ArtifactEnv.baselineSubmission_admitted
  intro input outcome events source behaviour execution
  change machineSemHOL ArtifactEnv.baselineSubmission.machineConfig (sourceFfi input)
    (ArtifactEnv.baselineSubmission.initialState input) behaviour at execution
  rw [ArtifactEnv.baselineSubmission_machineConfig,
      ArtifactEnv.baselineSubmission_initialState] at execution
  have hterm := oracle_full_baseline_terminates w input outcome events source
  obtain ⟨k1, ms1, ffi1, run1, io1⟩ := hterm
  cases behaviour with
  | terminate out2 ev2 =>
    obtain ⟨k2, ms2, ffi2, run2, io2⟩ := execution
    have heq := evaluateTargetIgnoreClocks ArtifactEnv.baselineMachineConfig
      (sourceFfi input) k2 k1 (ArtifactEnv.baselineInitialState input)
      (.halt out2) (.halt outcome) ms2 ms1 ffi2 ffi1 ⟨run2, by simp, run1, by simp⟩
    have hout : out2 = outcome := by injection (congrArg Prod.fst heq)
    have hffi : ffi2.ioEvents = ffi1.ioEvents := congrArg (fun r => r.2.2.ioEvents) heq
    rw [hout, ← io2, hffi, io1]
  | diverge ev2 =>
    rcases execution with ⟨hdiv, _⟩
    obtain ⟨ms2, ffi2, run2⟩ := hdiv k1
    rw [run1] at run2
    cases (congrArg Prod.fst run2)
  | fail =>
    obtain ⟨k2, run2⟩ := execution
    rcases h2 : evaluateTargetHOL ArtifactEnv.baselineMachineConfig
      (sourceFfi input) k2 (ArtifactEnv.baselineInitialState input) with ⟨res2, ms2, ffi2⟩
    rw [h2] at run2
    dsimp only at run2
    subst run2
    have heq := evaluateTargetIgnoreClocks ArtifactEnv.baselineMachineConfig
      (sourceFfi input) k2 k1 (ArtifactEnv.baselineInitialState input)
      .error (.halt outcome) ms2 ms1 ffi2 ffi1 ⟨h2, by simp, run1, by simp⟩
    have hres : (MachineResult.error : MachineResult) = .halt outcome := congrArg Prod.fst heq
    nomatch hres

def finiteSubmission (bound : Nat) : Submission :=
  FiniteRebudget.withFiniteBound ArtifactEnv.baselineSubmission bound

theorem finite_certificate_of_witness
    (w : ConcreteOracleCompilationWitness) (bound : Nat)
    (uniform : FiniteRebudget.UniformNotTimeOut ArtifactEnv.baselineSubmission bound) :
    InitE.Certificate (finiteSubmission bound) (.finite bound) :=
  FiniteRebudget.certificate ArtifactEnv.baselineSubmission .infinity bound
    (baseline_infinity_certificate w) uniform

end InitECandidate.Solver.Wave8GuestInv.LeanBridge
