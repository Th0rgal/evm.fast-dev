import InitECandidate.Solver.Wave8GuestInv.Shards.S13.Counter

/- Adapted from htab Counter.while_counter_guestInv. The expression-independent
rank follows arith/CounterSignedUpOn.lean at 9b84c81a6b5a72de4849820871268eb39889817a. -/
set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Leaves.S13

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Leaves.S13.Spec

variable {GuestInv : ∀ {F : Type}, Flapjack.PanSemStateFiniteExact 64 F → Prop}
  [IsGuestInv GuestInv]


def counterRoom (op : Cmp) (i : MlS) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup i with
  | some (.val (.word a)) => 2 ^ 64 - cmpRank op a
  | _ => 0

theorem while_counter_expr_guestInv (op : Cmp) (hop : op = .less ∨ op = .lower) (i : MlS) (bound : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B) (hinc : IncrBody i body) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp op (.var .local i) bound) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine TerminatingProgBoundedOn.while_rank (counterRoom op i)
    (fun s hs => guestInv_decClock s hs) hbody ?_ ?_
  · intro F s _ _ _
    simp only [counterRoom]
    split <;> omega
  · intro F s _ hs hact hflow
    refine ⟨guestInv_evaluate _ _ (guestInv_decClock s hs), ?_⟩
    obtain ⟨word, hw, hnz⟩ := hact
    change evalAt s _ = _ at hw
    obtain ⟨a, b, ha, _, hword⟩ := evalAt_cmp s op _ _ word hw
    simp only [evalAt, evalHOLExact] at ha
    have hia : s.locals.lookup i = some (.val (.word a)) := by simpa using ha
    have hcmp : Flapjack.Compiler.Encoders.Asm.wordCmpHOL op a b = true := by
      by_contra hc
      simp [hc] at hword
      exact hnz hword
    have hlt := cmpRank_lt op hop a b hcmp
    obtain ⟨hnc, hinc'⟩ := hinc.run (decClockHOLFinite s) a hia
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none := by
      rcases hflow with h | h
      · exact h
      · exact absurd h hnc
    have hi' := hinc' hnone
    have hsucc := cmpRank_succ op a b hlt
    have hmax := cmpRank_le op b
    simp only [counterRoom, hi', hia]
    omega

end InitECandidate.Solver.Wave8Leaves.S13
