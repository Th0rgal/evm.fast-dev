import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.Base

/-! `ro_heap_mark`: `heap_mark` (AST line 88) is read-only. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Contracts.M14

open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

theorem «ro_heap_mark» : ReadOnlyFn (ofString "heap_mark") := by
  refine readOnlyFn_of_guestAst 8 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_heap_mark rfl ?_
  dsimp only [Guest.Software.guestFn_heap_mark, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact ReadOnlyProg.ret _

end InitECandidate.Solver.Wave8Contracts.M14
