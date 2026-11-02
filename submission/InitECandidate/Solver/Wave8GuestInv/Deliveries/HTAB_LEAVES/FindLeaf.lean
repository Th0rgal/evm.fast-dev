import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_LEAVES.Loop

/-! `fb_htab_find_leaf`: the crit-bit descent `while n != 0 { … n = child }` is read-only and
carries the single word `n`, so `while_oneWord` bounds it by `(2^64 + 1)·1` for arbitrary
memory (a cyclic node graph makes the run time out, which the bound does not constrain). -/

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

theorem fb_htab_find_leaf :
    TerminatingFunBoundedOn GuestInv (ofString "htab_find_leaf") K.«htab_find_leaf» := by
  refine onFun_of_guestAst 131 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_find_leaf _ rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_htab_find_leaf,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  refine TerminatingProgBoundedOn.weakenK (K := (2 ^ 64 + 1) * (0 + 1) + 0) ?_
    (by simp [K.«htab_find_leaf»])
  refine TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _ ?_
  refine TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _ ?_
  refine TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _ ?_
  refine TerminatingProgBoundedOn.seq_guestInv ?_ (straightOn _ rfl)
  refine while_oneWord_guestInv (ofString "n") (straightOn _ rfl) rfl ?_
    (fun s h => active_cmp_var _ _ _ s h)
  intro y hy
  simp [avoidsLocal, beq_false_of_ne hy]

end InitECandidate.Solver.Wave8GuestInv.Htab
