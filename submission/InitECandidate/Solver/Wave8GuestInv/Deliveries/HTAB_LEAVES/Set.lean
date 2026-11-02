import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_LEAVES.Loop2
import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_LEAVES.Loops
import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_LEAVES.Get

/-! `fb_htab_set` (lookup, `memeq`, `htab_first_diff`, the two-word descent, two node
allocations) and `fb_htab_union_into` (`while i < cap`, `htab_item` + `htab_set`). `memcpy` and
`memeq` belong to the bytes family; their leaves are hypotheses. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

attribute [local irreducible] TerminatingProgBoundedOn

abbrev MemeqLeaf : Prop :=
  TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»

theorem fb_htab_union_into_of (_hc : MemcpyLeaf)
    (hs : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set») :
    TerminatingFunBoundedOn GuestInv (ofString "htab_union_into") K.«htab_union_into» := by
  have hi := fb_htab_item
  apply onFun_le 400 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_union_into _ rfl
  · htab_unfold Guest.Software.guestFn_htab_union_into
    htab_walk
    counted_while
    all_goals htab_walk
  · unfold K.«htab_union_into»
    simp only [Nat.max_zero, Nat.add_zero]
    apply Nat.mul_le_mul_left
    omega

end InitECandidate.Solver.Wave8GuestInv.Htab
