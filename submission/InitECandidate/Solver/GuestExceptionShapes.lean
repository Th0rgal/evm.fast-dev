import InitE.SourceSemantics
import InitE.SourceDeclarationsCore
import InitECandidate.Solver.CompactComputation
import InitECandidate.Solver.FrontendCodecComputation
import Flapjack.Pancake.Proofs.PanToCrep

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.GuestExceptionShapes

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE

def originalEshapes : HolFiniteMapExact MlS ShapeHOL :=
  HolFiniteMapExact.empty.updateList (exceptionsHOL sourceDeclarations)

theorem originalEshapes_lookup_eq_reverse_lookup (eid : MlS) :
    originalEshapes.lookup eid = List.lookup eid (exceptionsHOL sourceDeclarations).reverse := by
  change (HolFiniteMapExact.empty.updateList (exceptionsHOL sourceDeclarations)).lookup eid = _
  rw [HolFiniteMapExact.lookup_updateList]
  change FUPDATE_LIST FEMPTY (exceptionsHOL sourceDeclarations) eid = _
  simpa only [List.reverse_reverse, FLOOKUP] using
    FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (exceptionsHOL sourceDeclarations).reverse eid

def expectedExns : List (MlS × ShapeHOL) :=
  [(ofString "TrapErr", .one),
   (ofString "RlpErr", .one),
   (ofString "SszErr", .one),
   (ofString "HdrErr", .one),
   (ofString "BlockErr", .one),
   (ofString "MptErr", .one),
   (ofString "TxErr", .one),
   (ofString "StateErr", .one),
   (ofString "EvmErr", .one),
   (ofString "Fail", .one)]

theorem exceptionsHOL_sourceDeclarations_eq :
    exceptionsHOL sourceDeclarations = expectedExns := by
  unfold sourceDeclarations
  rw [InitECandidate.Solver.FrontendCodecComputation.declToHOL_function_eq]
  kernel_rfl

theorem lookup_RlpErr : originalEshapes.lookup (ofString "RlpErr") = some .one := by
  rw [originalEshapes_lookup_eq_reverse_lookup, exceptionsHOL_sourceDeclarations_eq]
  rfl

theorem lookup_MptErr : originalEshapes.lookup (ofString "MptErr") = some .one := by
  rw [originalEshapes_lookup_eq_reverse_lookup, exceptionsHOL_sourceDeclarations_eq]
  rfl

theorem lookup_TrapErr : originalEshapes.lookup (ofString "TrapErr") = some .one := by
  rw [originalEshapes_lookup_eq_reverse_lookup, exceptionsHOL_sourceDeclarations_eq]
  rfl

theorem lookup_SszErr : originalEshapes.lookup (ofString "SszErr") = some .one := by
  rw [originalEshapes_lookup_eq_reverse_lookup, exceptionsHOL_sourceDeclarations_eq]
  rfl

theorem lookup_Fail : originalEshapes.lookup (ofString "Fail") = some .one := by
  rw [originalEshapes_lookup_eq_reverse_lookup, exceptionsHOL_sourceDeclarations_eq]
  rfl

end InitECandidate.Solver.GuestExceptionShapes
