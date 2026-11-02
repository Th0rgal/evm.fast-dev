import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_LEAVES.Simple
import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_LEAVES.FindLeaf

/-! Loop-free table/list helpers with calls: `htab_grow`, `htab_new_node`, `htab_new_leaf`,
`htab_new_internal`, `htab_copy`, `lst_push`. `memcpy` belongs to the bytes family; its leaf
`fb_memcpy` is a hypothesis. -/

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

abbrev MemcpyLeaf : Prop :=
  TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»

theorem fb_htab_grow_of (hc : MemcpyLeaf) :
    TerminatingFunBoundedOn GuestInv (ofString "htab_grow") K.«htab_grow» := by
  have ha := on_alloc
  apply onFun_le 137 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_grow _ rfl
  · htab_unfold Guest.Software.guestFn_htab_grow
    htab_walk
  · htab_bound K.«htab_grow»

theorem fb_htab_new_node_of (hc : MemcpyLeaf) :
    TerminatingFunBoundedOn GuestInv (ofString "htab_new_node") K.«htab_new_node» := by
  have hg := fb_htab_grow_of hc
  apply onFun_le 134 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_new_node _ rfl
  · htab_unfold Guest.Software.guestFn_htab_new_node
    htab_walk
  · htab_bound K.«htab_new_node»

theorem fb_htab_new_leaf_of (hc : MemcpyLeaf) :
    TerminatingFunBoundedOn GuestInv (ofString "htab_new_leaf") K.«htab_new_leaf» := by
  have hn := fb_htab_new_node_of hc
  apply onFun_le 135 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_new_leaf _ rfl
  · htab_unfold Guest.Software.guestFn_htab_new_leaf
    htab_walk
  · htab_bound K.«htab_new_leaf»

theorem fb_htab_new_internal_of (hc : MemcpyLeaf) :
    TerminatingFunBoundedOn GuestInv (ofString "htab_new_internal") K.«htab_new_internal» := by
  have hn := fb_htab_new_node_of hc
  apply onFun_le 136 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_new_internal _ rfl
  · htab_unfold Guest.Software.guestFn_htab_new_internal
    htab_walk
  · htab_bound K.«htab_new_internal»

theorem fb_htab_copy_of (hc : MemcpyLeaf) :
    TerminatingFunBoundedOn GuestInv (ofString "htab_copy") K.«htab_copy» := by
  have ha := on_alloc
  apply onFun_le 145 (by rw [guestAst_len]; decide) Guest.Software.guestFn_htab_copy _ rfl
  · htab_unfold Guest.Software.guestFn_htab_copy
    htab_walk
  · htab_bound K.«htab_copy»

theorem fb_lst_push_of (hc : MemcpyLeaf) :
    TerminatingFunBoundedOn GuestInv (ofString "lst_push") K.«lst_push» := by
  have ha := on_alloc
  apply onFun_le 410 (by rw [guestAst_len]; decide) Guest.Software.guestFn_lst_push _ rfl
  · htab_unfold Guest.Software.guestFn_lst_push
    htab_walk
  · htab_bound K.«lst_push»

end InitECandidate.Solver.Wave8GuestInv.Htab
