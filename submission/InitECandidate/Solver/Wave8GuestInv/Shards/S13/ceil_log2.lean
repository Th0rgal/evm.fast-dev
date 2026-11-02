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

theorem fb_ceil_log2 :
    TerminatingFunBoundedOn GuestInv (ofString "ceil_log2") K.«ceil_log2» := by
  apply onFun_le 36 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ceil_log2 _ rfl
  · htab_unfold Guest.Software.guestFn_ceil_log2
    apply TerminatingProgBoundedOn.dec_on localsFree_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply while_oneWord_guestInv (ofString "d") (straightOn _ rfl) rfl
      · intro y hy
        simp [avoidsLocal, beq_false_of_ne hy]
      · intro F s h
        obtain ⟨word, hw, _⟩ := h
        change evalAt s _ = _ at hw
        obtain ⟨a, b, ha, _, _⟩ := evalAt_cmp s _ _ _ word hw
        rcases hd : s.locals.lookup (ofString "d") with _ | v
        · simp [evalAt, evalHOLExact, hd] at ha
        · rcases v with ⟨⟨w⟩⟩ | _ | _
          · exact ⟨w, rfl⟩
          all_goals simp [evalAt, evalHOLExact, hd] at ha
    · s13_walk
  · htab_bound K.«ceil_log2»

example : type_of% (fb_ceil_log2 (GuestInv := GuestInv)) =
    (TerminatingFunBoundedOn GuestInv (ofString "ceil_log2") K.«ceil_log2») := rfl


end InitECandidate.Solver.Wave8Leaves.S13
