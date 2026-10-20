import InitE.Challenge
import InitECandidate.Proofs.OracleBaselineCertificate
import Flapjack.Compiler.Backend.LabToTarget.MachineSemantics
import Flapjack.Compiler.Backend.LabToTarget.SemanticsCompileFinal
import Flapjack.Compiler.Backend.LabFilter.Proofs.Semantics

namespace InitE
open InitECandidate.Proofs
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.Proofs.PanToTarget

/-- Direct finite-`K` certificate constructor from a bounded `matchingExecutionAt` witness. -/
theorem certificate_of_bounded_behaviour (submission : Submission) (K : Nat)
    (score : submission.K = .finite K) (admitted : submission.Admitted)
    (correct : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∃ steps ≤ K, matchingExecutionAt submission input outcome events steps) :
    Certificate submission (.finite K) :=
  ⟨score, admitted, correct⟩

/-- Any finite `targetTerminatesAt` witness at `steps` for a machine whose `machineSemHOL`
equals `.terminate outcome events` automatically produces `matchingExecutionAt` at the same
`steps` by target clock determinism (`evaluateTargetIgnoreClocks`). -/
theorem matchingExecutionAt_of_behaviour_and_terminatesAt (submission : Submission)
    (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (steps : Nat)
    (hsem : machineSemHOL submission.machineConfig (sourceFfi input)
      (submission.initialState input) (.terminate outcome events))
    (covered : coveredOutcome outcome)
    (hterm : targetTerminatesAt submission.machineConfig (sourceFfi input)
      (submission.initialState input) steps) :
    matchingExecutionAt submission input outcome events steps := by
  obtain ⟨k0, ms0, ffi0, hrun0, hevents0⟩ := hsem
  obtain ⟨out1, ms1, ffi1, hrun1⟩ := hterm
  have heq := evaluateTargetIgnoreClocks submission.machineConfig (sourceFfi input)
    steps k0 (submission.initialState input) (.halt out1) (.halt outcome) ms1 ms0 ffi1 ffi0
    ⟨hrun1, by simp, hrun0, by simp⟩
  have hout : out1 = outcome := by
    have h := congrArg Prod.fst heq
    injection h
  have hffi : ffi1 = ffi0 := congrArg (fun r => r.2.2) heq
  subst hout
  subst hffi
  refine ⟨out1, ms1, ffi1, hrun1, ?_⟩
  rw [← hevents0]
  exact matchingResult_refl input out1 ffi1.ioEvents covered

/-- Combining exact behaviour preservation with a finite `K` termination bound yields
`Certificate submission (.finite K)` without re-proving I/O trace or outcome agreement. -/
theorem certificate_of_exact_behaviour_and_bound (submission : Submission) (K : Nat)
    (score : submission.K = .finite K) (admitted : submission.Admitted)
    (correct : ∀ input outcome events,
      sourceBehaviour input = .terminate outcome events →
      ∀ behaviour, machineSemHOL submission.machineConfig (sourceFfi input)
        (submission.initialState input) behaviour → behaviour = .terminate outcome events)
    (bounded : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        targetTerminatesWithin (.finite K) submission.machineConfig (sourceFfi input)
          (submission.initialState input)) :
    Certificate submission (.finite K) := by
  refine ⟨score, admitted, ?_⟩
  intro input hgas outcome events source covered
  have hsem := target_termination_of_behaviour_eq submission.machineConfig
    (sourceFfi input) (submission.initialState input) outcome events
    (correct input outcome events source)
  obtain ⟨steps, hle, hterm⟩ := bounded input hgas outcome events source covered
  exact ⟨steps, hle,
    matchingExecutionAt_of_behaviour_and_terminatesAt submission input outcome events
      steps hsem covered hterm⟩

/-- Shifting a post-bootstrap `targetTerminatesAt` witness across the 23,132-step
zero-RAM bootstrap. -/
theorem targetTerminatesAt_of_bootstrap_shift (input : Guest.InputBlob)
    (post : RiscV.L3.riscv_state) (steps : Nat)
    (shift : ∀ clock, evaluateTargetHOL baselineMachineConfig (sourceFfi input)
      (bootstrapSteps + clock) (baselineInitialState input) =
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) clock post)
    (hterm : targetTerminatesAt baselineMachineConfig (sourceFfi input) post steps) :
    targetTerminatesAt baselineMachineConfig (sourceFfi input)
      (baselineInitialState input) (bootstrapSteps + steps) := by
  obtain ⟨outcome, ms', ffi', hrun⟩ := hterm
  exact ⟨outcome, ms', ffi', (shift steps).trans hrun⟩

/-- Clock-preserving domain alignment (`alignDm` + `alignSdm`) and `filterSkip` bridge:
if the aligned unfiltered `LabSem` state halts at clock `k`, then the `filterSkip`-related
state `s` halts at the exact same clock `k` with the same outcome and FFI state. -/
theorem lab_filter_align_clocked_halt {width : Nat} [NeZero width] {C F : Type}
    (hw : goodDimindex width)
    (s t : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hr : LabFilter.Proofs.stateRel s t)
    (k : Nat) (outcome : HolOutcome)
    (next : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hhalt : LabSem.evaluate { alignDm (alignSdm t) with clock := k } = (.halt outcome, next)) :
    (LabSem.evaluate { s with clock := k }).1 = .halt outcome ∧
      (LabSem.evaluate { s with clock := k }).2.ffi = next.ffi := by
  have hdm : LabSem.evaluate { alignDm (alignSdm t) with clock := k } =
      ((LabSem.evaluate { alignSdm t with clock := k }).1,
        alignDm (LabSem.evaluate { alignSdm t with clock := k }).2) := by
    change LabSem.evaluate (alignDm { alignSdm t with clock := k }) = _
    have h := evaluateAlignDM hw { alignSdm t with clock := k }
    cases he : LabSem.evaluate { alignSdm t with clock := k }
    simpa only [he] using h
  have hsdm : LabSem.evaluate { alignSdm t with clock := k } =
      ((LabSem.evaluate { t with clock := k }).1,
        alignSdm (LabSem.evaluate { t with clock := k }).2) := by
    change LabSem.evaluate (alignSdm { t with clock := k }) = _
    have h := evaluateAlignSDM hw { t with clock := k }
    cases he : LabSem.evaluate { t with clock := k }
    simpa only [he] using h
  rw [hsdm] at hdm
  rw [hhalt] at hdm
  have hres_t : (LabSem.evaluate { t with clock := k }).1 = .halt outcome :=
    (congrArg Prod.fst hdm).symm
  have hffi_t : (LabSem.evaluate { t with clock := k }).2.ffi = next.ffi := by
    have h2 := congrArg Prod.snd hdm
    have hffi := congrArg Flapjack.Compiler.Backend.LabSem.State.ffi h2
    exact hffi.symm
  have hrc : LabFilter.Proofs.stateRel { s with clock := k } { t with clock := k } := by
    rcases hr with ⟨⟨compile, hs, hcomp⟩, hf⟩
    subst s
    exact ⟨⟨compile, rfl, hcomp⟩, hf⟩
  obtain ⟨extra, t2, he, hf⟩ := LabFilter.Proofs.filterCorrect
    { s with clock := k } { t with clock := k }
    (LabSem.evaluate { s with clock := k }).1
    (LabSem.evaluate { s with clock := k }).2
    ⟨rfl, hrc, hrc.2⟩
  have hnt : (LabSem.evaluate { t with clock := k }).1 ≠ .timeOut := by
    rw [hres_t]
    intro h
    cases h
  have hadd := evaluateAddClock { t with clock := k }
    (LabSem.evaluate { t with clock := k }).1
    (LabSem.evaluate { t with clock := k }).2 extra
    ⟨rfl, hnt⟩
  rw [hadd] at he
  constructor
  · exact (congrArg Prod.fst he).symm.trans hres_t
  · have ht2 : (LabSem.evaluate { t with clock := k }).2.ffi = t2.ffi :=
      congrArg (fun p => p.2.ffi) he
    rw [hf, ← ht2]
    exact hffi_t

/-- Clocked `LabToTarget.compileCorrect` bridge: a halting `LabSem` evaluation at clock `k`
yields a halting target execution at clock `k + extra` with the same outcome and FFI state. -/
theorem lab_to_target_clocked_halt {S Q F : Type}
    (mc : MachineConfig 64 S Q) (p : BitVec 64) (ms : S)
    (s : Flapjack.Compiler.Backend.LabSem.State 64 LabToTarget.Config F)
    (hencoder : encoderCorrect mc.target)
    (hinit : initOk (mc, p) s ms)
    (k : Nat) (outcome : HolOutcome)
    (hhalt : (LabSem.evaluate { s with clock := k }).1 = .halt outcome) :
    ∃ extra ms2,
      evaluateTargetHOL mc s.ffi (k + extra) ms =
        (.halt outcome, ms2, (LabSem.evaluate { s with clock := k }).2.ffi) ∧
      targetTerminatesAt mc s.ffi ms (k + extra) := by
  obtain ⟨code2, labs, t1, hrel, htie⟩ := hinit
  generalize hev : LabSem.evaluate { s with clock := k } = run
  rcases run with ⟨result, next⟩
  have hres : result = .halt outcome := by
    rw [hev] at hhalt
    exact hhalt
  subst hres
  have hnoterr : (MachineResult.halt outcome : MachineResult) ≠ .error := by
    intro h
    cases h
  obtain ⟨extra, _, ms2, htarget⟩ := LabToTarget.compileCorrect (T := Unit) p
    { s with clock := k } (.halt outcome) mc next code2 labs t1 ms
    ⟨oracleTie_clock mc ms s k htie, hev, hnoterr, hencoder,
      stateRelClock (mc, code2, labs, p) s t1 ms k hrel⟩
  refine ⟨extra, ms2, htarget, outcome, ms2, next.ffi, htarget⟩

/-- End-to-end finite-`K` `InitE.Certificate submission (.finite K)` parameterized by
the oracle compilation equation, stack depth bound, and a post-bootstrap step bound `K_post`
with `bootstrapSteps + K_post ≤ K` (zero stage files required). -/
theorem oracle_full_baseline_bounded_certificate (submission : Submission)
    (K K_post : Nat)
    (score : submission.K = .finite K)
    (admitted : submission.Admitted)
    (hmc : submission.machineConfig = baselineMachineConfig)
    (hinit : submission.initialState = baselineInitialState)
    (oracles : List (Option (Spt Nat)))
    (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (hK : bootstrapSteps + K_post ≤ K)
    (bounded_post : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ post : RiscV.L3.riscv_state,
          targetStateRel riscvTarget installedAsm post →
          targetTerminatesWithin (.finite K_post) baselineMachineConfig (sourceFfi input) post) :
    InitE.Certificate submission (.finite K) := by
  apply certificate_of_exact_behaviour_and_bound submission K score admitted
  · intro input outcome events source behaviour execution
    have nonfail : sourceBehaviour input ≠ HolBehaviour.fail := by
      rw [source]
      intro impossible
      cases impossible
    change machineSemHOL submission.machineConfig (sourceFfi input)
      (submission.initialState input) behaviour at execution
    rw [hmc, hinit] at execution
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
  · intro input hgas outcome events source covered
    rw [hmc, hinit]
    obtain ⟨post, shift, related⟩ := full_baseline_evaluator_exact input
    obtain ⟨steps, hle, hterm⟩ := bounded_post input hgas outcome events source covered post related
    have hle' : steps ≤ K_post := hle
    refine ⟨bootstrapSteps + steps, Nat.le_trans (Nat.add_le_add_left hle' bootstrapSteps) hK, ?_⟩
    exact targetTerminatesAt_of_bootstrap_shift input post steps shift hterm

#print axioms certificate_of_exact_behaviour_and_bound
#print axioms lab_filter_align_clocked_halt
#print axioms lab_to_target_clocked_halt
#print axioms oracle_full_baseline_bounded_certificate

end InitE
