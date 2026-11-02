import InitECandidate.Solver.Wave8GuestInv.ContractParts.C03
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptCache

/-! Rev9 `InvalidatesCache` implies stationarity after warm-up and local restoration.
This lemma assumes the callee contract; it does not use its unproved spec leaf. -/

set_option autoImplicit false
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Restore the caller's local map after invalidating an already cleared cache. -/
theorem invalidatesCache_warm_stationary (fname : MlS)
    (h : InvalidatesCache fname) :
    FunSpec
      (fun s => NodeArgs ["nd"] (fun _ _ => True) s ∧
        clearCache s (locN s "nd") = s)
      (fun s r post => Resumes r → SameHead s { post with locals := s.locals })
      fname := by
  obtain ⟨params, body, ret, hlookup, hpost⟩ := h
  refine ⟨params, body, ret, hlookup, ?_⟩
  intro F s hc hs hnot hr
  have heffect := hpost s hc hs.1 hnot hr
  change (evaluateHOLFiniteState s body).2 =
    { clearCache s (locN s "nd") with
      locals := (evaluateHOLFiniteState s body).2.locals,
      clock := (evaluateHOLFiniteState s body).2.clock } at heffect
  rw [hs.2] at heffect
  unfold SameHead
  rw [heffect]

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
