import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.Base

/-! `ro_calculate_total_blob_gas`: `calculate_total_blob_gas` (AST line 11914) is read-only. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Contracts.M14

open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

theorem «ro_calculate_total_blob_gas» :
    ReadOnlyFn (ofString "calculate_total_blob_gas") := by
  refine readOnlyFn_of_guestAst 317 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_calculate_total_blob_gas rfl ?_
  dsimp only [Guest.Software.guestFn_calculate_total_blob_gas, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact ReadOnlyProg.ret _

end InitECandidate.Solver.Wave8Contracts.M14
