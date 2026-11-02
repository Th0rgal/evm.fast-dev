import InitECandidate.Solver.Wave8GuestInv.Shards.S06.LoopFree

/-! Leaf 2 (`fb_incorporate_child_on_success`, idx 592) in shard s06 (`wave8/leaves-s06`).

`incorporate_child_on_success` has a single counted `while i < log_count` loop with step 1 (`i = i + 1`).
Using `counted_while` (`while_counter_guestInv .less`), we prove `fb_incorporate_child_on_success_of`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8GuestInv.S06

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

attribute [local irreducible] TerminatingProgBoundedOn

variable {GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} [GuestInvLike GuestInv]

/-- 2. `incorporate_child_on_success` (idx 592): counted `while i < log_count` loop, calls
`incorporate_child_on_error`, `log_append`, and `htab_union_into`. -/
theorem fb_incorporate_child_on_success_of
    (herr : TerminatingFunBoundedOn GuestInv
      (ofString "incorporate_child_on_error") K.«incorporate_child_on_error»)
    (hlog : TerminatingFunBoundedOn GuestInv (ofString "log_append") K.«log_append»)
    (huni : TerminatingFunBoundedOn GuestInv (ofString "htab_union_into") K.«htab_union_into») :
    TerminatingFunBoundedOn GuestInv
      (ofString "incorporate_child_on_success") K.«incorporate_child_on_success» := by
  apply onFun_le 592 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_incorporate_child_on_success _ rfl
  · htab_unfold Guest.Software.guestFn_incorporate_child_on_success
    htab_walk
    counted_while
    all_goals htab_walk
  · htab_bound K.«incorporate_child_on_success»

end InitECandidate.Solver.Wave8GuestInv.S06
