import InitECandidate.Solver.Wave8GuestInv.Shards.S13.CounterAuto

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S13

attribute [local irreducible] InitECandidate.Solver.PanTerminatingBounded.TerminatingProgBoundedOn
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S13.Spec

variable {GuestInv : ∀ {F : Type}, Flapjack.PanSemStateFiniteExact 64 F → Prop}
  [IsGuestInv GuestInv]

open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

theorem fb_nodedb_build
    (h_htab_new : TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new»)
    (h_htab_set : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set»)
    (h_keccak256 : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256») :
    TerminatingFunBoundedOn GuestInv (ofString "nodedb_build") K.«nodedb_build» := by
  apply onFun_le 253 (by rw [guestAst_len]; decide) Guest.Software.guestFn_nodedb_build _ rfl
  · htab_unfold Guest.Software.guestFn_nodedb_build
    apply TerminatingProgBoundedOn.dec_on localsFree_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply while_oneWord_guestInv (ofString "cap") (straightOn _ rfl) rfl
      · intro y hy
        simp [avoidsLocal, beq_false_of_ne hy]
      · intro F s h
        exact active_cmp_var _ _ _ s h
    · s13_walk
  · htab_bound K.«nodedb_build»

example : type_of% (fb_nodedb_build (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new») →
    (TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set») →
    (TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256») →
    TerminatingFunBoundedOn GuestInv (ofString "nodedb_build") K.«nodedb_build») := rfl


end InitECandidate.Solver.Wave8Leaves.S13
