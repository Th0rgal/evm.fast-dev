import InitECandidate.Solver.Wave8Stage.WordCostAnalysis

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordCostLabelSupport
open Flapjack WordCostEffects WordCostCertificates

def labelBound {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → Nat
  | .break label | .continue label => label
  | .seq a b | .ite _ _ _ a b => max (labelBound a) (labelBound b)
  | .loop _ body _ => labelBound body
  | .call ret _ _ handler => max
      (match ret with | none => 0 | some (_,_,p,_,_) => labelBound p)
      (match handler with | none => 0 | some (_,p,_,_) => labelBound p)
  | _ => 0
termination_by p => sizeOf p

def HighNone (bound : Nat) (effects : Effects) : Prop :=
  ∀ label, bound < label → effects (.breakTo label) = none ∧ effects (.continueTo label) = none

@[simp] theorem add_none (a : Budget) : add a none = none := by cases a <;> rfl

/-- Certificates have finite label support. Thus a Boolean checker may test a
finite range and still exclude every escaping break/continue label. -/
theorem derives_high {width : Nat} [NeZero width]
    (defs : Option Nat → Effects) (terminal : Basis.Pure.MlString.MlString → Bool)
    (noLabels : ∀ dest label, defs dest (.breakTo label) = none ∧ defs dest (.continueTo label) = none)
    (p : WordLangProgHOL (BitVec width)) (effects : Effects)
    (certificate : Derives defs terminal p effects) : HighNone (labelBound p) effects := by
  induction certificate with
  | normal p erased => intro label lt; simp [atom]
  | tick => intro label lt; simp [atom]
  | share op reg exp => intro label lt; simp [merge,atom,join]
  | raise reg => intro label lt; simp [atom]
  | result reg regs => intro label lt; simp [atom]
  | breakTo actual =>
    intro label lt
    have ne : label ≠ actual := by simpa only [labelBound] using Nat.ne_of_gt lt
    simp [atom,ne]
  | continueTo actual =>
    intro label lt
    have ne : label ≠ actual := by simpa only [labelBound] using Nat.ne_of_gt lt
    simp [atom,ne]
  | ffi name p1 l1 p2 l2 names =>
    intro label lt
    cases terminal name <;> simp [ffiEffects,atom,merge,join]
  | @seq first second a b left right ihLeft ihRight =>
    intro label lt
    have hl := ihLeft label (by simp only [labelBound] at lt; omega)
    have hr := ihRight label (by simp only [labelBound] at lt; omega)
    simp [WordCostEffects.seq,hl.1,hl.2,hr.1,hr.2,join]
  | @branch cmp reg operand first second a b left right ihLeft ihRight =>
    intro label lt
    have hl := ihLeft label (by simp only [labelBound] at lt; omega)
    have hr := ihRight label (by simp only [labelBound] at lt; omega)
    simp [merge,hl.1,hl.2,hr.1,hr.2,join]
  | @loop names exits body a bodyRule cycle ih =>
    intro label lt
    have h := ih (label+1) (by simp only [labelBound] at lt; omega)
    exact h
  | tail dest args =>
    intro label lt
    have h := noLabels dest label
    simp [shift,h.1,h.2]
  | returning names live next l1 l2 dest args handler contEffects handlerEffects cont handlers ihCont ihHandlers =>
    intro label lt
    cases handler with
    | none =>
      have hc := ihCont label (by simpa only [labelBound,Nat.max_zero] using lt)
      simp [returningEffects,hc.1,hc.2,join]
    | some h =>
      rcases h with ⟨name,hbody,h1,h2⟩
      have hc := ihCont label (by simp only [labelBound] at lt; omega)
      have hh := ihHandlers name hbody h1 h2 rfl label (by simp only [labelBound] at lt; omega)
      simp [returningEffects,hc.1,hc.2,hh.1,hh.2,join]

end InitECandidate.Solver.Wave8Stage.WordCostLabelSupport
