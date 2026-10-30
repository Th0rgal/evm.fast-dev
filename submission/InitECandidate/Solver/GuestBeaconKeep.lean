import InitE.SourceSemantics
import InitE.SourceDeclarationsCore
import InitE.SourceNameFacts
import InitE.SourceMainFacts
import InitECandidate.Solver.CompactComputation
import InitECandidate.Solver.FrontendCodecComputation
import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.PanToTarget.MainFirstSemantics
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant
import InitECandidate.Solver.GuestCodeLookup
import InitECandidate.Solver.GuestGlobalKeep
import InitECandidate.Solver.GuestFrameMemKeep

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.GuestBeaconKeep

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestFrameMemKeep

def badBeacon : List MlS :=
  [ofString "fork_init", ofString "main"]

def goodBeacon (f : MlS) : Bool := !(badBeacon.contains f)

theorem program_check_beacon_roots_address :
    (functionsHOL sourceDeclarations).all
      (fun entry => !(goodBeacon entry.1) ||
        GuestGlobalKeep.keepsG (ofString "beacon_roots_address") goodBeacon entry.2.2.1) = true := by
  unfold sourceDeclarations
  rw [InitECandidate.Solver.FrontendCodecComputation.declToHOL_function_eq]
  kernel_rfl

theorem goodBeacon_bodies :
    ∀ function, goodBeacon function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      GuestGlobalKeep.keepsG (ofString "beacon_roots_address") goodBeacon body = true := by
  intro f hf values body callee rs h
  obtain ⟨params, rs', hc⟩ := lookupCode_installed h
  have hmem := originalRuntimeCode_mem hc
  have hall := List.all_eq_true.mp program_check_beacon_roots_address _ hmem
  simpa [hf] using hall

theorem evaluate_keeps_beacon_roots_address {F : Type} (program : ProgHOL 64)
    (supported : GuestGlobalKeep.keepsG (ofString "beacon_roots_address") goodBeacon program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state program).2.globals.lookup (ofString "beacon_roots_address") =
      state.globals.lookup (ofString "beacon_roots_address") :=
  evaluate_keepsG (ofString "beacon_roots_address") goodBeacon goodBeacon_bodies program supported state code

end InitECandidate.Solver.GuestBeaconKeep
