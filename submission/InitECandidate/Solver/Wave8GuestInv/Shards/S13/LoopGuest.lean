/- Provenance: helpers from htab/FindLeaf.lean at 3ea193df0cf872ba6789df0100aa8734e0f75704. -/
import InitECandidate.Solver.Wave8GuestInv.Shards.S13.Loop

/-! `fb_htab_find_leaf`: the crit-bit descent `while n != 0 { … n = child }` is read-only and
carries the single word `n`, so `while_oneWord` bounds it by `(2^64 + 1)·1` for arbitrary
memory (a cyclic node graph makes the run time out, which the bound does not constrain). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Leaves.S13

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Leaves.S13.Spec

variable {GuestInv : ∀ {F : Type}, Flapjack.PanSemStateFiniteExact 64 F → Prop}
  [IsGuestInv GuestInv]


theorem guestInv_locFrame {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : LocFrame s t)
    (hs : GuestInv s) : GuestInv t := by
  unfold LocFrame at h
  rw [h]
  exact guestInv_with_locals_clock s _ _ hs

theorem guestInv_decClock {F : Type} (s : PanSemStateFiniteExact 64 F) (hs : GuestInv s) :
    GuestInv (decClockHOLFinite s) :=
  guestInv_with_locals_clock s s.locals _ hs

/-- `while_oneWord` under `GuestInv`. -/
theorem while_oneWord_guestInv (x : MlS) {condition : ExpHOL 64} {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hloc : locOnly body = true)
    (havoid : ∀ y, y ≠ x → avoidsLocal y body = true)
    (hact : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LoopActive condition s →
      ∃ w, s.locals.lookup x = some (.val (.word w))) :
    TerminatingProgBoundedOn GuestInv (.while condition body) ((2 ^ 64 + 1) * (B + 1)) :=
  while_oneWord x (fun s hs => guestInv_decClock s hs)
    (fun _ _ hs hfr _ => guestInv_locFrame hfr hs) hbody hloc havoid hact

theorem beq_false_of_ne {a b : MlS} (h : b ≠ a) : (a == b) = false := by
  simp only [beq_eq_false_iff_ne]; exact fun e => h e.symm

end InitECandidate.Solver.Wave8Leaves.S13
