import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.Base

/-! `ro_check_gas_limit`: `check_gas_limit` (AST line 9590) is read-only.
Walks `udivmod` (AST 695) -> `udiv` (AST 727) -> `check_gas_limit` (AST 9590). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Contracts.M14

open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

private theorem ro_udivmod_aux : ReadOnlyFn (ofString "udivmod") := by
  refine readOnlyFn_of_guestAst 33 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_udivmod rfl ?_
  dsimp only [Guest.Software.guestFn_udivmod, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, Option.map]
  exact ReadOnlyProg.seq
    (ReadOnlyProg.ite _ (ReadOnlyProg.call_trap_with _) ReadOnlyProg.skip)
    (ReadOnlyProg.seq
      (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
      (ReadOnlyProg.dec _ _ _
        (ReadOnlyProg.dec _ _ _
          (ReadOnlyProg.dec _ _ _
            (ReadOnlyProg.seq
              (ReadOnlyProg.while_loop _
                (ReadOnlyProg.seq
                  (ReadOnlyProg.assign_local _ _)
                  (ReadOnlyProg.seq
                    (ReadOnlyProg.assign_local _ _)
                    (ReadOnlyProg.ite _
                      (ReadOnlyProg.seq
                        (ReadOnlyProg.assign_local _ _)
                        (ReadOnlyProg.assign_local _ _))
                      ReadOnlyProg.skip))))
              (ReadOnlyProg.ret _))))))

private theorem ro_udiv_aux : ReadOnlyFn (ofString "udiv") := by
  refine readOnlyFn_of_guestAst 34 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_udiv rfl ?_
  dsimp only [Guest.Software.guestFn_udiv, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact ReadOnlyProg.decCall ro_udivmod_aux _ _ _ (ReadOnlyProg.ret _)

theorem «ro_check_gas_limit» : ReadOnlyFn (ofString "check_gas_limit") := by
  refine readOnlyFn_of_guestAst 235 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_check_gas_limit rfl ?_
  dsimp only [Guest.Software.guestFn_check_gas_limit, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact ReadOnlyProg.decCall ro_udiv_aux _ _ _
    (ReadOnlyProg.seq
      (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
      (ReadOnlyProg.seq
        (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
        (ReadOnlyProg.seq
          (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
          (ReadOnlyProg.ret _))))

end InitECandidate.Solver.Wave8Contracts.M14
