import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.Base

/-! `ro_check_gas`: `check_gas` (AST line 14935) is read-only. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Contracts.M14

open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

theorem «ro_check_gas» : ReadOnlyFn (ofString "check_gas") := by
  refine readOnlyFn_of_guestAst 447 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_check_gas rfl ?_
  dsimp only [Guest.Software.guestFn_check_gas, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact ReadOnlyProg.seq
    (ReadOnlyProg.ite _ (ReadOnlyProg.raise _ _) ReadOnlyProg.skip)
    (ReadOnlyProg.ret _)

end InitECandidate.Solver.Wave8Contracts.M14
