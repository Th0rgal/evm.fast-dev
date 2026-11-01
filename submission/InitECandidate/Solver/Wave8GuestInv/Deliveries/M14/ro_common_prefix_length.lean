import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.Base

/-! `ro_common_prefix_length`: `common_prefix_length` (AST line 9903) is read-only.
Walks `min` (AST 667) -> `common_prefix_length` (AST 9903). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Contracts.M14

open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

private theorem ro_min_aux : ReadOnlyFn (ofString "min") := by
  refine readOnlyFn_of_guestAst 31 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_min rfl ?_
  dsimp only [Guest.Software.guestFn_min, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact ReadOnlyProg.seq
    (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
    (ReadOnlyProg.ret _)

theorem «ro_common_prefix_length» :
    ReadOnlyFn (ofString "common_prefix_length") := by
  refine readOnlyFn_of_guestAst 251 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_common_prefix_length rfl ?_
  dsimp only [Guest.Software.guestFn_common_prefix_length, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact ReadOnlyProg.decCall ro_min_aux _ _ _
    (ReadOnlyProg.dec _ _ _
      (ReadOnlyProg.seq
        (ReadOnlyProg.while_loop _
          (ReadOnlyProg.seq
            (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
            (ReadOnlyProg.assign_local _ _)))
        (ReadOnlyProg.ret _)))

end InitECandidate.Solver.Wave8Contracts.M14
