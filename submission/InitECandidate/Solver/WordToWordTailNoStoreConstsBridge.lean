import InitECandidate.Solver.WordPassesPreserveNoStoreConsts
import InitECandidate.Solver.BlockVsTxSixPassTargetCert
import InitECandidate.Solver.SelfContainedExactKeccakMasterK

set_option autoImplicit false

namespace InitECandidate.Solver.WordToWordTailNoStoreConstsBridge
open Flapjack InitE
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.Proofs.PanToTarget
open InitECandidate.Proofs InitECandidate.Solver
open WordPassesPreserveNoStoreConsts StackRemoveStoreConstsZeroBridge
open SelfContainedBoundedCertificate

/-- The requested composition, with the rightmost pass applied first. -/
def tail {width : Nat} [NeZero width] (b : Bool) (p : WordLangProgHOL (BitVec width)) :=
  WordInst.threeToTwoRegProg b (WordUnreach.removeUnreach (WordRemove.removeMustTerminate p))

/-- NoSt permits alloc, but still eliminates every store-constant payload. -/
theorem noSt_allowance_zero {α : Type} (p : WordLangProgHOL α)
    (h : NoSt p = true) : storeConstsAllowance p = 0 := by
  induction p using NoSt.induct <;> (try simp_all [NoSt, storeConstsAllowance])
  rename_i ret target args handler ihr ihh
  cases ret with
  | none =>
    cases handler with
    | none => rfl
    | some v => rcases v with ⟨a, p, b, c⟩; simp_all [NoSt, storeConstsAllowance]
  | some v =>
    rcases v with ⟨a, cuts, p, b, c⟩
    cases handler with
    | none => simp_all [NoSt, storeConstsAllowance]
    | some v => rcases v with ⟨d, q, e, f⟩; simp_all [NoSt, storeConstsAllowance]

theorem tail_NoSt {width : Nat} [NeZero width] (b : Bool)
    (p : WordLangProgHOL (BitVec width)) (h : NoSt p = true) :
    NoSt (tail b p) = true :=
  t_threeToTwo b _ (t_removeUnreach _ (t_removeMustTerminate p h))

theorem compiled_tail_NoSt {width : Nat} [NeZero width] (ctx : Spt Nat)
    (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool) :
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true :=
  tail_NoSt b _ (loopToWord_NoSt ctx p labels)

theorem compiled_tail_allowance_zero {width : Nat} [NeZero width] (ctx : Spt Nat)
    (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool) :
    storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 0 :=
  noSt_allowance_zero _ (compiled_tail_NoSt ctx p labels b)

theorem compiled_tail_safe {width : Nat} [NeZero width] (ctx : Spt Nat)
    (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool) :
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 0 :=
  ⟨compiled_tail_NoSt ctx p labels b, compiled_tail_allowance_zero ctx p labels b⟩

/-- The imported chain is in the opposite order; it has the same invariant. -/
theorem imported_tail_safe {width : Nat} [NeZero width] (ctx : Spt Nat)
    (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool) :
    NoSt (WordRemove.removeMustTerminate (WordUnreach.removeUnreach
      (WordInst.threeToTwoRegProg b (LoopToWord.compHOL ctx p labels).1))) = true ∧
    storeConstsAllowance (WordRemove.removeMustTerminate (WordUnreach.removeUnreach
      (WordInst.threeToTwoRegProg b (LoopToWord.compHOL ctx p labels).1))) = 0 := by
  have h := t_tail_chain b _ (loopToWord_NoSt ctx p labels)
  exact ⟨h, noSt_allowance_zero _ h⟩

theorem tail_clock_identity {width : Nat} [NeZero width] (ctx : Spt Nat)
    (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool) (clock : Nat) :
    clock + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = clock := by
  rw [compiled_tail_allowance_zero, Nat.add_zero]

/-- Structural counterexample: the allowance is not identically zero. -/
theorem store_payload_nonzero {α : Type} (x : Bool × α) :
    storeConstsAllowance (.storeConsts 0 2 4 6 [x]) = 1 := rfl

/-- Even an empty payload fails NoSt, so the converse of noSt_allowance_zero is false. -/
theorem empty_payload_distinction {α : Type} :
    NoSt (.storeConsts (α := α) 0 2 4 6 []) = false ∧
    storeConstsAllowance (.storeConsts (α := α) 0 2 4 6 []) = 0 := ⟨rfl, rfl⟩

theorem block3_tail_budget {width : Nat} [NeZero width] (ctx : Spt Nat)
    (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool) :
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    BlockVsTxSixPassTargetCert.blockVsTxSlope3K + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 214346021162 := by
  refine ⟨compiled_tail_NoSt ctx p labels b, ?_⟩
  rw [compiled_tail_allowance_zero, Nat.add_zero, BlockVsTxSixPassTargetCert.slope3_exact]

theorem block6_tail_budget {width : Nat} [NeZero width] (ctx : Spt Nat)
    (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool) :
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    BlockVsTxSixPassTargetCert.blockVsTxSlope6K + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 428692019192 := by
  refine ⟨compiled_tail_NoSt ctx p labels b, ?_⟩
  rw [compiled_tail_allowance_zero, Nat.add_zero, BlockVsTxSixPassTargetCert.slope6_exact]

theorem block12_tail_budget {width : Nat} [NeZero width] (ctx : Spt Nat)
    (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool) :
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    BlockVsTxSixPassTargetCert.blockVsTxSlope12K + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 857384015252 := by
  refine ⟨compiled_tail_NoSt ctx p labels b, ?_⟩
  rw [compiled_tail_allowance_zero, Nat.add_zero, BlockVsTxSixPassTargetCert.slope12_exact]

theorem keccak_tail_budget {width : Nat} [NeZero width] (ctx : Spt Nat)
    (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool) :
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    SelfContainedExactKeccakMasterK.exactKeccakCandidateK + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 32619343724 := by
  refine ⟨compiled_tail_NoSt ctx p labels b, ?_⟩
  rw [compiled_tail_allowance_zero, Nat.add_zero, SelfContainedExactKeccakMasterK.exact_candidate_eq]

theorem keccak128_tail_budget {width : Nat} [NeZero width] (ctx : Spt Nat)
    (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool) :
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    SelfContainedExactKeccakMasterK.exactKeccak128CandidateK + storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 19392676892 := by
  refine ⟨compiled_tail_NoSt ctx p labels b, ?_⟩
  rw [compiled_tail_allowance_zero, Nat.add_zero, SelfContainedExactKeccakMasterK.exact_128_candidate_eq]

/-- Requested advertised ceilings exceed the exact imported arithmetic K. -/
theorem keccak_advertised_slack :
    SelfContainedExactKeccakMasterK.exactKeccakCandidateK + 172620000 = 32791963724 := by decide

theorem keccak128_advertised_slack :
    SelfContainedExactKeccakMasterK.exactKeccak128CandidateK + 15438 = 19392692330 := by decide

/-- No numerical model is used to discharge semantic non-timeout. -/
theorem block3_tail_certificate {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool)
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        BlockVsTxSixPassTargetCert.blockVsTxSlope3K (baselineInitialState input)).1 ≠ .timeOut) :
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 0 ∧
    InitE.Certificate (baselineWithFiniteK 214346021162) (.finite 214346021162) := by
  refine ⟨compiled_tail_NoSt ctx p labels b, compiled_tail_allowance_zero ctx p labels b, ?_⟩
  have h := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (214346021162 - 23132) hlab compiled depthBound
    (by simpa only [bootstrapSteps_eq, BlockVsTxSixPassTargetCert.slope3_exact] using not_timeOut)
  simpa only [bootstrapSteps_eq] using h

theorem block6_tail_certificate {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool)
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        BlockVsTxSixPassTargetCert.blockVsTxSlope6K (baselineInitialState input)).1 ≠ .timeOut) :
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 0 ∧
    InitE.Certificate (baselineWithFiniteK 428692019192) (.finite 428692019192) := by
  refine ⟨compiled_tail_NoSt ctx p labels b, compiled_tail_allowance_zero ctx p labels b, ?_⟩
  have h := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (428692019192 - 23132) hlab compiled depthBound
    (by simpa only [bootstrapSteps_eq, BlockVsTxSixPassTargetCert.slope6_exact] using not_timeOut)
  simpa only [bootstrapSteps_eq] using h

theorem block12_tail_certificate {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool)
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        BlockVsTxSixPassTargetCert.blockVsTxSlope12K (baselineInitialState input)).1 ≠ .timeOut) :
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 0 ∧
    InitE.Certificate (baselineWithFiniteK 857384015252) (.finite 857384015252) := by
  refine ⟨compiled_tail_NoSt ctx p labels b, compiled_tail_allowance_zero ctx p labels b, ?_⟩
  have h := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (857384015252 - 23132) hlab compiled depthBound
    (by simpa only [bootstrapSteps_eq, BlockVsTxSixPassTargetCert.slope12_exact] using not_timeOut)
  simpa only [bootstrapSteps_eq] using h

theorem keccak_tail_certificate {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool)
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        SelfContainedExactKeccakMasterK.exactKeccakCandidateK (baselineInitialState input)).1 ≠ .timeOut) :
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 0 ∧
    InitE.Certificate (baselineWithFiniteK 32619343724) (.finite 32619343724) := by
  refine ⟨compiled_tail_NoSt ctx p labels b, compiled_tail_allowance_zero ctx p labels b, ?_⟩
  have h := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (32619343724 - 23132) hlab compiled depthBound
    (by simpa only [bootstrapSteps_eq, SelfContainedExactKeccakMasterK.exact_candidate_eq] using not_timeOut)
  simpa only [bootstrapSteps_eq] using h

theorem keccak128_tail_certificate {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool)
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        SelfContainedExactKeccakMasterK.exactKeccak128CandidateK (baselineInitialState input)).1 ≠ .timeOut) :
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 0 ∧
    InitE.Certificate (baselineWithFiniteK 19392676892) (.finite 19392676892) := by
  refine ⟨compiled_tail_NoSt ctx p labels b, compiled_tail_allowance_zero ctx p labels b, ?_⟩
  have h := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (19392676892 - 23132) hlab compiled depthBound
    (by simpa only [bootstrapSteps_eq, SelfContainedExactKeccakMasterK.exact_128_candidate_eq] using not_timeOut)
  simpa only [bootstrapSteps_eq] using h

theorem keccak_advertised_tail_certificate {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool)
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        32791963724 (baselineInitialState input)).1 ≠ .timeOut) :
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 0 ∧
    InitE.Certificate (baselineWithFiniteK 32791963724) (.finite 32791963724) := by
  refine ⟨compiled_tail_NoSt ctx p labels b, compiled_tail_allowance_zero ctx p labels b, ?_⟩
  have h := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (32791963724 - 23132) hlab compiled depthBound
    (by simpa only [bootstrapSteps_eq] using not_timeOut)
  simpa only [bootstrapSteps_eq] using h

theorem keccak128_advertised_tail_certificate {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (labels : Nat × Nat) (b : Bool)
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        19392692330 (baselineInitialState input)).1 ≠ .timeOut) :
    NoSt (tail b (LoopToWord.compHOL ctx p labels).1) = true ∧
    storeConstsAllowance (tail b (LoopToWord.compHOL ctx p labels).1) = 0 ∧
    InitE.Certificate (baselineWithFiniteK 19392692330) (.finite 19392692330) := by
  refine ⟨compiled_tail_NoSt ctx p labels b, compiled_tail_allowance_zero ctx p labels b, ?_⟩
  have h := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (19392692330 - 23132) hlab compiled depthBound
    (by simpa only [bootstrapSteps_eq] using not_timeOut)
  simpa only [bootstrapSteps_eq] using h

#print axioms noSt_allowance_zero
#print axioms tail_NoSt
#print axioms compiled_tail_NoSt
#print axioms compiled_tail_allowance_zero
#print axioms compiled_tail_safe
#print axioms imported_tail_safe
#print axioms tail_clock_identity
#print axioms store_payload_nonzero
#print axioms empty_payload_distinction
#print axioms block3_tail_budget
#print axioms block6_tail_budget
#print axioms block12_tail_budget
#print axioms keccak_tail_budget
#print axioms keccak128_tail_budget
#print axioms keccak_advertised_slack
#print axioms keccak128_advertised_slack
#print axioms block3_tail_certificate
#print axioms block6_tail_certificate
#print axioms block12_tail_certificate
#print axioms keccak_tail_certificate
#print axioms keccak128_tail_certificate
#print axioms keccak_advertised_tail_certificate
#print axioms keccak128_advertised_tail_certificate
end InitECandidate.Solver.WordToWordTailNoStoreConstsBridge
