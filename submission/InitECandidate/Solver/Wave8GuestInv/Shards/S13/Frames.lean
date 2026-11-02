import InitECandidate.Solver.Wave8GuestInv.Shards.S13.Base
/- Reused htab/Base.lean local frames at 3ea193df0cf872ba6789df0100aa8734e0f75704. -/

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


/-! ## Local frames of loop-free local-only programs -/

/-- `t` agrees with `s` on every field but the locals and the clock. -/
def LocFrame {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  t = { s with locals := t.locals, clock := t.clock }

theorem LocFrame.refl {F : Type} (s : PanSemStateFiniteExact 64 F) : LocFrame s s := by
  cases s; rfl

theorem LocFrame.trans {F : Type} {s t u : PanSemStateFiniteExact 64 F}
    (h1 : LocFrame s t) (h2 : LocFrame t u) : LocFrame s u := by
  unfold LocFrame at *
  rw [h2]; rw [h1]

/-- Loop-free programs whose only effects are on locals. -/
def locOnly : ProgHOL 64 → Bool
  | .dec _ _ _ body => locOnly body
  | .seq first second => locOnly first && locOnly second
  | .ite _ yes no => locOnly yes && locOnly no
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | _ => false

theorem locFrame_eval {F : Type} : ∀ (p : ProgHOL 64), locOnly p = true →
    ∀ (s : PanSemStateFiniteExact 64 F), LocFrame s (evaluateHOLFiniteState s p).2
  | .skip, _, s => by rw [evaluateHOLFiniteState_skip]; exact LocFrame.refl s
  | .break, _, s => by rw [evaluateHOLFiniteState_break]; exact LocFrame.refl s
  | .continue, _, s => by rw [evaluateHOLFiniteState_continue]; exact LocFrame.refl s
  | .annot _ _, _, s => by rw [evaluateHOLFiniteState_annot]; exact LocFrame.refl s
  | .raise _ _, _, s => by
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split
      · rfl
      · exact LocFrame.refl s
    · exact LocFrame.refl s
  | .return _, _, s => by
    rw [evaluateHOLFiniteState_return]
    split
    · exact LocFrame.refl s
    · split
      · rfl
      · exact LocFrame.refl s
  | .assign kind name e, h, s => by
    cases kind with
    | global => simp [locOnly] at h
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact LocFrame.refl s
      · split
        · rfl
        · exact LocFrame.refl s
  | .dec name sh init body, h, s => by
    have hb : locOnly body = true := by simpa [locOnly] using h
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact LocFrame.refl s
    · rename_i val _
      split
      · have ih := locFrame_eval body hb (setVarHOLFinite name val s)
        unfold LocFrame at ih ⊢
        dsimp only
        rw [ih]; rfl
      · exact LocFrame.refl s
  | .seq first second, h, s => by
    have h12 : locOnly first = true ∧ locOnly second = true := by
      simpa [locOnly, Bool.and_eq_true] using h
    rw [evaluateHOLFiniteState_seq_line780]
    have ih1 := locFrame_eval first h12.1 s
    rcases hr1 : evaluateHOLFiniteState s first with ⟨r1, mid⟩
    rw [hr1] at ih1
    dsimp only at ih1 ⊢
    cases r1 with
    | none => exact ih1.trans (locFrame_eval second h12.2 mid)
    | some _ => exact ih1
  | .ite cond yes no, h, s => by
    have h12 : locOnly yes = true ∧ locOnly no = true := by
      simpa [locOnly, Bool.and_eq_true] using h
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact locFrame_eval no h12.2 s
      · exact locFrame_eval yes h12.1 s
    · exact LocFrame.refl s
  | .while _ _, h, _ => by simp [locOnly] at h
  | .call _ _ _, h, _ => by simp [locOnly] at h
  | .decCall _ _ _ _ _, h, _ => by simp [locOnly] at h
  | .store _ _, h, _ => by simp [locOnly] at h
  | .storeByte _ _, h, _ => by simp [locOnly] at h
  | .store32 _ _, h, _ => by simp [locOnly] at h
  | .tick, h, _ => by simp [locOnly] at h
  | .primitive _ _ _, h, _ => by simp [locOnly] at h
  | .extCall _ _ _ _ _, h, _ => by simp [locOnly] at h
  | .shMemLoad _ _ _ _, h, _ => by simp [locOnly] at h
  | .shMemStore _ _ _, h, _ => by simp [locOnly] at h


end InitECandidate.Solver.Wave8Leaves.S13
