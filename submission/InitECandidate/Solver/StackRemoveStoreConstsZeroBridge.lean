import InitECandidate.Solver.PanToWordNoStoreConsts
import InitECandidate.Solver.SelfContainedSixPassMaster

set_option autoImplicit false

namespace InitECandidate.Solver.StackRemoveStoreConstsZeroBridge
open Flapjack InitE
open Flapjack.Pancake.Proofs.PanToTarget Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Proofs
open InitECandidate.Solver
open PanToWordNoStoreConsts StackRemoveClockOriginAudit SelfContainedSixPassMaster

/-- Structural sum of store-constant copy payloads, including nested call bodies.
This is a syntactic allowance; preservation through intervening Word passes and
trace provenance are separate semantic obligations. -/
def storeConstsAllowance {α : Type} : WordLangProgHOL α → Nat
  | .storeConsts _ _ _ _ ws => ws.length
  | .mustTerminate b => storeConstsAllowance b
  | .seq a b => storeConstsAllowance a + storeConstsAllowance b
  | .ite _ _ _ a b => storeConstsAllowance a + storeConstsAllowance b
  | .loop _ b _ => storeConstsAllowance b
  | .call ret _ _ h =>
      (match ret with | none => 0 | some (_, _, r, _, _) => storeConstsAllowance r) +
      (match h with | none => 0 | some (_, p, _, _) => storeConstsAllowance p)
  | _ => 0

/-- NoSC eliminates every summand of the structural copy allowance. -/
theorem noSC_allowance_zero {α : Type} (p : WordLangProgHOL α)
    (h : NoSC p = true) : storeConstsAllowance p = 0 := by
  induction p using NoSC.induct <;> (try simp_all [NoSC, storeConstsAllowance])
  rename_i ret target args handler ihr ihh
  cases ret with
  | none =>
    cases handler with
    | none => rfl
    | some v => rcases v with ⟨a, p, b, c⟩; simp_all [NoSC, storeConstsAllowance]
  | some v =>
    rcases v with ⟨a, cuts, p, b, c⟩
    cases handler with
    | none => simp_all [NoSC, storeConstsAllowance]
    | some v => rcases v with ⟨d, q, e, f⟩; simp_all [NoSC, storeConstsAllowance]

theorem compiled_allowance_zero {width : Nat} [NeZero width] (ctx : Spt Nat)
    (p : HolLoopProg width) (labels : Nat × Nat) :
    storeConstsAllowance (LoopToWord.compHOL ctx p labels).1 = 0 :=
  noSC_allowance_zero _ (compHOL_NoSC ctx p labels)

theorem compiled_list_allowance_zero {width : Nat} [NeZero width] (ctx : Spt Nat)
    (ps : List (HolLoopProg width)) (labels : Nat × Nat) :
    ∀ q ∈ ps.map (fun p => (LoopToWord.compHOL ctx p labels).1),
      storeConstsAllowance q = 0 := by
  intro q hq
  exact noSC_allowance_zero q (compHOL_list_NoSC ctx labels ps q hq)

/-- Trace provenance: a store-constant event must originate in a program
that fails NoSC. This premise must be supplied by a semantic simulation. -/
def TraceFrom {α : Type} (p : WordLangProgHOL α) (xs : List (Bool × Nat)) : Prop :=
  ∀ event ∈ xs, event.1 = true → NoSC p = false

theorem noSC_trace_flags {α : Type} (p : WordLangProgHOL α)
    (xs : List (Bool × Nat)) (hp : NoSC p = true) (origin : TraceFrom p xs) :
    ∀ event ∈ xs, event.1 = false := by
  intro event he
  cases hb : event.1 with
  | false => rfl
  | true => have := origin event he hb; simp_all

theorem compiled_run_allowance_zero {width : Nat} [NeZero width] (ctx : Spt Nat)
    (p : HolLoopProg width) (labels : Nat × Nat) (xs : List (Bool × Nat))
    (origin : TraceFrom (LoopToWord.compHOL ctx p labels).1 xs) :
    runAllowance xs = 0 :=
  allowance_zero_of_NoSC xs (noSC_trace_flags _ xs (compHOL_NoSC ctx p labels) origin)

/-- The frontend restriction and the guest jump configuration hold together. -/
theorem compiled_guest_zero {width : Nat} [NeZero width] (ctx : Spt Nat)
    (p : HolLoopProg width) (labels : Nat × Nat)
    (oracles : List (Option (Spt Nat))) :
    storeConstsAllowance (LoopToWord.compHOL ctx p labels).1 = 0 ∧
      (oracleCompilerConfig oracles).stackConf.jump = false :=
  ⟨compiled_allowance_zero ctx p labels, guest_stackRemove_jump_false oracles⟩

/-- In the explicit allowance model zero extra ticks gives C_sr=1, D_sr=0. -/
theorem compiled_clock_identity {width : Nat} [NeZero width] (ctx : Spt Nat)
    (p : HolLoopProg width) (labels : Nat × Nat) (clock : Nat) :
    clock + storeConstsAllowance (LoopToWord.compHOL ctx p labels).1 = 1 * clock + 0 := by
  rw [compiled_allowance_zero]; simp

theorem compiled_trace_clock_identity {width : Nat} [NeZero width] (ctx : Spt Nat)
    (p : HolLoopProg width) (labels : Nat × Nat) (clock : Nat) (xs : List (Bool × Nat))
    (origin : TraceFrom (LoopToWord.compHOL ctx p labels).1 xs) :
    clock + runAllowance xs = clock := by
  rw [compiled_run_allowance_zero ctx p labels xs origin, Nat.add_zero]

theorem neutral_six_pass_slope : sixPassSlope 1 3 = 3 :=
  six_pass_slope_three 1 3 rfl rfl

theorem neutral_six_pass_affine (d_cl d_ws clock : Nat) :
    sixPassAffine d_cl d_ws 0 clock = 3 * clock + (d_cl + d_ws) := by
  simpa using six_pass_affine_exact d_cl d_ws 0 clock

theorem neutral_six_pass_budget : sixPassReducedK = 11_029_683_788 := reduced_budget_exact

/-- A real storeConsts payload distinguishes the allowance from a constant-zero function. -/
theorem allowance_storeConsts_tight {α : Type} (a b c d : Nat) (ws : List (Bool × α)) :
    storeConstsAllowance (.storeConsts a b c d ws) = ws.length := rfl

theorem allowance_seq_additive {α : Type} (a b : WordLangProgHOL α) :
    storeConstsAllowance (.seq a b) = storeConstsAllowance a + storeConstsAllowance b := rfl

/-- Transport the existing reduced certificate without removing its obligations. -/
theorem reduced_certificate_at_literal
    (certificate : InitE.Certificate
      (SelfContainedBoundedCertificate.baselineWithFiniteK sixPassReducedK)
      (.finite sixPassReducedK)) :
    InitE.Certificate
      (SelfContainedBoundedCertificate.baselineWithFiniteK 11_029_683_788)
      (.finite 11_029_683_788) := by
  simpa only [reduced_budget_exact] using certificate

theorem reduced_certificate_baseline
    (certificate : InitE.Certificate
      (SelfContainedBoundedCertificate.baselineWithFiniteK sixPassReducedK)
      (.finite sixPassReducedK)) :
    InitE.Certificate SelfContainedEndToEndCert.submission .infinity :=
  reduced_baseline_compatible certificate

/-- Finite certificate at the literal reduced K, retaining the compiler,
depth and uniform target non-timeout obligations of the six-pass master. -/
theorem reduced_finite_certificate_bridge
    (oracles : List (Option (Spt Nat)))
    (c : Flapjack.Compiler.Backend.Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable
      (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations =
      (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
      sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL
        baselineMachineConfig
        (sourceFfi input)
        sixPassReducedK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate
      (SelfContainedBoundedCertificate.baselineWithFiniteK 11_029_683_788)
      (.finite 11_029_683_788) :=
  reduced_certificate_at_literal
    (reduced_finite_certificate oracles c depth hlab compiled depthBound not_timeOut)

#print axioms noSC_allowance_zero
#print axioms compiled_allowance_zero
#print axioms compiled_list_allowance_zero
#print axioms noSC_trace_flags
#print axioms compiled_run_allowance_zero
#print axioms compiled_guest_zero
#print axioms compiled_clock_identity
#print axioms compiled_trace_clock_identity
#print axioms neutral_six_pass_slope
#print axioms neutral_six_pass_affine
#print axioms neutral_six_pass_budget
#print axioms allowance_storeConsts_tight
#print axioms allowance_seq_additive
#print axioms reduced_certificate_at_literal
#print axioms reduced_certificate_baseline
#print axioms reduced_finite_certificate_bridge
end InitECandidate.Solver.StackRemoveStoreConstsZeroBridge
