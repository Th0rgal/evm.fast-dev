import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_LEAVES.Base

/-! Hash-table / list leaves that follow from a total `FunBounded` bound (the body terminates on
every state with enough clock, whatever memory holds): `htab_new`, `htab_new_scratch`,
`htab_count`, `htab_item`, `htab_first_diff`, `lst_new`, `lst_new_scratch`, and the callee
bounds `alloc` / `scratch_alloc` they share. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8GuestInv.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

theorem on_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc» :=
  funOn funBounded_alloc (by decide)

theorem on_scratch_alloc :
    TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc» :=
  funOn funBounded_scratch_alloc (by decide)

theorem fb_htab_new : TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new» :=
  funOn Old.funBounded_htab_new (by decide)

theorem fb_htab_new_scratch :
    TerminatingFunBoundedOn GuestInv (ofString "htab_new_scratch") K.«htab_new_scratch» :=
  funOn Old.funBounded_htab_new_scratch (by decide)

theorem fb_htab_count : TerminatingFunBoundedOn GuestInv (ofString "htab_count") K.«htab_count» :=
  funOn Old.funBounded_htab_count (by decide)

theorem fb_htab_item : TerminatingFunBoundedOn GuestInv (ofString "htab_item") K.«htab_item» :=
  funOn Old.funBounded_htab_item (by decide)

theorem funBounded_lst_new : FunBounded (ofString "lst_new") 4 := by
  refine funBounded_of_guestAst 408 (by rw [guestAst_len]; decide) Guest.Software.guestFn_lst_new 4
    rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_lst_new,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_alloc _ _ _
      (ProgBounded.decCall funBounded_alloc _ _ _ (ProgBounded.straight _ rfl)))
    (by decide)

theorem funBounded_lst_new_scratch : FunBounded (ofString "lst_new_scratch") 4 := by
  refine funBounded_of_guestAst 409 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_lst_new_scratch 4 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_lst_new_scratch,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.decCall funBounded_scratch_alloc _ _ _
      (ProgBounded.decCall funBounded_scratch_alloc _ _ _ (ProgBounded.straight _ rfl)))
    (by decide)

theorem fb_lst_new : TerminatingFunBoundedOn GuestInv (ofString "lst_new") K.«lst_new» :=
  funOn funBounded_lst_new (by decide)

theorem fb_lst_new_scratch :
    TerminatingFunBoundedOn GuestInv (ofString "lst_new_scratch") K.«lst_new_scratch» :=
  funOn funBounded_lst_new_scratch (by decide)

end InitECandidate.Solver.Wave8GuestInv.Htab
