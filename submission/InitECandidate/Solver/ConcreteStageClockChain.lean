import InitECandidate.Solver.ConcreteStage1To5ClockCertificate

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.ConcreteStageClockChain

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedPipelineBridge
open InitECandidate.Solver.SelfContainedConcretePipelineMaster
open InitECandidate.Solver.ConcreteStage1To5ClockCertificate
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabSem

/-- Maximum valid Yukon `K` parameter such that `yukonScore K verifyMinutes < 10^299`
for every `verifyMinutes : Nat`. -/
def maxYukonK : Nat := (10 ^ 299 - 1) / 10 ^ 4

/-- Yukon score formula: `K * 10000 + min verifyMinutes 9999`. -/
def yukonScore (K verifyMinutes : Nat) : Nat :=
  K * 10000 + min verifyMinutes 9999

theorem yukonScore_lt_ceiling_of_le_maxYukonK
    (K verifyMinutes : Nat) (hK : K ≤ maxYukonK) :
    yukonScore K verifyMinutes < 10 ^ 299 := by
  unfold yukonScore maxYukonK at *
  have hmin : min verifyMinutes 9999 ≤ 9999 := Nat.min_le_right _ _
  have hpow : 10000 ≤ 10 ^ 299 := by decide
  omega

/-- Uniform source clock predicate matching Track B's `CoveredSourceTicksConsumedBounded`. -/
def CoveredSourceTicksConsumedBounded (K_pan_max : Nat) : Prop :=
  ∀ (input : Guest.InputBlob),
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
          { s_decls with clock := K_pan_max }
          (.call none (Flapjack.Basis.Pure.MlString.ofString "main") [] : ProgHOL 64)).1
            ≠ some .timeOut

end InitECandidate.Solver.ConcreteStageClockChain

