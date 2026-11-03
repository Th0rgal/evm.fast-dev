import InitECandidate.Solver.Wave8GuestInv.ContractParts.C07

/-! Standalone zero-sorry proof of `gbody_incorporate_tx_into_block`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

theorem «lookup_incorporate_tx_into_block» :
    originalRuntimeCode.lookup (ofString "incorporate_tx_into_block") =
      some ((sourceFunctionEntry Guest.Software.guestFn_incorporate_tx_into_block).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 428 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_incorporate_tx_into_block) rfl

theorem «gbody_incorporate_tx_into_block» :
    (TerminatingFunBoundedOn GuestInv (ofString "merge_tx_into_block") K.«merge_tx_into_block») →
    (TerminatingFunBoundedOn WorldOK (ofString "update_builder_from_tx") K.«update_builder_from_tx») →
    TerminatingFunBoundedOn WorldOK (ofString "incorporate_tx_into_block") K.«incorporate_tx_into_block» := by
  intro hm hu
  refine ⟨_, _, _, «lookup_incorporate_tx_into_block», ?_⟩
  simp only [InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.seq_guestInv_after
      (TerminatingProgBoundedOn.call_on hu _ _ (callEntryOn_of_localsFree localsFree_worldOK _ _))
      worldOK_guestInv
      (TerminatingProgBoundedOn.seq_guestInv
        (TerminatingProgBoundedOn.call_guestInv hm _ _)
        (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«incorporate_tx_into_block»; omega

end InitECandidate.Solver.Wave8GuestInv.R16Shards
