import InitECandidate.Solver.Wave8GuestInv.Shards.S13.InputAccess

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S13

attribute [local irreducible] InitECandidate.Solver.PanTerminatingBounded.TerminatingProgBoundedOn
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Leaves.S13.Spec

variable {GuestInv : ∀ {F : Type}, Flapjack.PanSemStateFiniteExact 64 F → Prop}
  [IsGuestInv GuestInv]
variable [HasOrdinaryDomain GuestInv]

open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded

syntax "input_walk" : tactic
macro_rules
  | `(tactic| input_walk) => `(tactic| first
    | exact input_loop _
    | exact straightOn _ rfl
    | (apply TerminatingProgBoundedOn.dec_on localsFree_guestInv; input_walk)
    | (apply TerminatingProgBoundedOn.seq_guestInv <;> input_walk)
    | (apply TerminatingProgBoundedOn.ite_on <;> input_walk)
    | (apply TerminatingProgBoundedOn.decCall_guestInv
       · callee_hyp
       · input_walk)
    | (apply TerminatingProgBoundedOn.call_guestInv; callee_hyp))

theorem fb_input_blob
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_trap_with : TerminatingFunBoundedOn GuestInv (ofString "trap_with") K.«trap_with») :
    TerminatingFunBoundedOn GuestInv (ofString "input_blob") K.«input_blob» := by
  apply onFun_le 29 (by rw [guestAst_len]; decide) Guest.Software.guestFn_input_blob _ rfl
  · htab_unfold Guest.Software.guestFn_input_blob
    input_walk
  · htab_bound K.«input_blob»

example : type_of% (fb_input_blob (GuestInv := GuestInv)) =
    ((TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
     (TerminatingFunBoundedOn GuestInv (ofString "trap_with") K.«trap_with») →
      TerminatingFunBoundedOn GuestInv (ofString "input_blob") K.«input_blob») := rfl


end InitECandidate.Solver.Wave8Leaves.S13
