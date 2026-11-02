import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_LEAVES.FindLeaf

/-! `htab_get`, `htab_has`, `htab_del` (unguarded bounds): `htab_find_leaf`, then `memeq`, then
straight-line code. `memeq` belongs to the bytes family; its leaf `fb_memeq` is a hypothesis. -/

set_option autoImplicit false
set_option maxRecDepth 100000

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

theorem fb_htab_get_of
    (hm : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») :
    TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get» := by
  have hf := fb_htab_find_leaf
  apply onFun_le 132 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_get _ rfl
  · htab_unfold Guest.Software.guestFn_htab_get
    htab_walk
  · htab_bound K.«htab_get»

theorem fb_htab_has_of
    (hm : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») :
    TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.«htab_has» := by
  have hf := fb_htab_find_leaf
  apply onFun_le 133 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_has _ rfl
  · htab_unfold Guest.Software.guestFn_htab_has
    htab_walk
  · htab_bound K.«htab_has»

theorem fb_htab_del_of
    (hm : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») :
    TerminatingFunBoundedOn GuestInv (ofString "htab_del") K.«htab_del» := by
  have hf := fb_htab_find_leaf
  apply onFun_le 139 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_del _ rfl
  · htab_unfold Guest.Software.guestFn_htab_del
    htab_walk
  · htab_bound K.«htab_del»

end InitECandidate.Solver.Wave8GuestInv.Htab
