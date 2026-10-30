import InitECandidate.Solver.PanTerminatingBounded
import InitECandidate.Solver.LeafSszMerkleize
import InitECandidate.Solver.LeafBlockTxLoop
import InitECandidate.Solver.GuestBoundMain
import InitECandidate.Solver.GuestBoundSszHtr

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.LeafMainUniformClock` — Track B Leaf 18 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Top-level Track B aggregator connecting `LeafSszMerkleize`, `LeafBlockTxLoop`, `GuestBoundMain`,
and `GuestBoundSszHtr.funBounded_main_reduced` to `PanTerminatingBounded`:

1. Proves `terminatingFunBounded_main : TerminatingFunBounded (ofString "main") K_main_body`
   with `K_main_body + 1 ≤ maxYukonK` (note: even with conservative `2^64 - 1` factors across nested
   calls, verify `K_pan_max` satisfies `bootstrapSteps + linearPipelineTargetBudget K_pan_max ... ≤ maxYukonK`,
   where `maxYukonK ≈ 10^295`, while `K_main_body < 10^80`!).
2. Applies `PanTerminatingBounded.coveredSourceTicksConsumedBounded_of_terminatingMain` and
   `UniformSourceClock` to export the exact `pan_not_timeOut` theorem consumed by
   `ConcreteStage1To5ClockCertificate.concrete_affine_stage1_to_5_certificate`!

Forbidden: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.LeafMainUniformClock

open Classical
open InitE
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.LeafSszMerkleize
open InitECandidate.Solver.LeafBlockTxLoop
open InitECandidate.Solver.GuestBoundMain
open InitECandidate.Solver.GuestBoundSszHtr

def K_main_body : Nat :=
  16 * K_htr_new_payload_request + 8 * K_run_attempt + 16 * (2 ^ 64 - 1) + 16777216

def K_pan_uniform : Nat := K_main_body + 1

theorem terminatingFunBounded_main :
    TerminatingFunBounded (ofString "main") K_main_body := by
  sorry

theorem coveredSourceTicksConsumedBounded_concrete :
    CoveredSourceTicksConsumedBounded K_pan_uniform := by
  sorry

/-- Exact Stage 1 `pan_not_timeOut` input to
`ConcreteStage1To5ClockCertificate.concrete_affine_stage1_to_5_certificate`. -/
theorem concrete_uniform_pan_not_timeOut
    (input : Guest.InputBlob)
    (hgas : Guest.GasLimit.declaredGasLimit input ≤ 200000000)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (hsource : sourceBehaviour input = .terminate outcome events)
    (hcov : coveredOutcome outcome)
    (stCtxt : StructContextExact)
    (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hst : decsStcnamesHOLExact [] sourceDeclarations = some stCtxt)
    (hdecls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState
      { s_decls with clock := K_pan_uniform }
      (.call none (ofString "main") [] : ProgHOL 64)).1 ≠ some .timeOut := by
  sorry

end InitECandidate.Solver.LeafMainUniformClock
