import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.U256CallFacts

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A non-returning read-only prefix leaves its input state unchanged. -/
def NoChangeOnNone (p : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s post : PanSemStateFiniteExact 64 F),
    evaluateHOLFiniteState s p = (none, post) → post = s

theorem NoChangeOnNone.skip : NoChangeOnNone .skip := by
  intro F s post h
  rw [evaluateHOLFiniteState_skip] at h
  exact (Prod.mk.inj h).2.symm

theorem NoChangeOnNone.ret (e : ExpHOL 64) : NoChangeOnNone (.return e) := by
  intro F s post h
  rw [evaluateHOLFiniteState_return] at h
  split at h
  · simp at h
  · split at h <;> simp at h

theorem NoChangeOnNone.ite (c : ExpHOL 64) {yes no : ProgHOL 64}
    (hy : NoChangeOnNone yes) (hn : NoChangeOnNone no) : NoChangeOnNone (.ite c yes no) := by
  intro F s post h
  rw [evaluateHOLFiniteState_ite] at h
  split at h
  · split at h
    · exact hn s post h
    · exact hy s post h
  · simp at h

theorem NoChangeOnNone.seq {first second : ProgHOL 64}
    (hfirst : NoChangeOnNone first) (hsecond : NoChangeOnNone second) :
    NoChangeOnNone (.seq first second) := by
  intro F s post h
  obtain ⟨mid, h1, h2⟩ := arith_seq_none h
  exact (hsecond mid post h2).trans (hfirst s mid h1)
end InitECandidate.Solver.Wave8GuestInv.Arith
