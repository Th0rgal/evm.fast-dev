import InitECandidate.Solver.Wave8GuestInv.Shards.S04.VariableWalk
import InitECandidate.Solver.Wave8GuestInv.Shards.S04.CounterEffects

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S04.AdvanceEffects
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingCombinators
open InitECandidate.Solver.Wave8Leaves.S04.Light.Arith
open Flapjack.Compiler.Encoders.Asm

def RangeAt {F : Type} (key : MlS) (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w : BitVec 64, s.locals.lookup key = some (.val (.word w)) ∧
    0 < w.toNat ∧ w.toNat ≤ 64

def KeepsRange (key : MlS) (p : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), RangeAt key s →
    (evaluateHOLFiniteState s p).1 = none → RangeAt key (evaluateHOLFiniteState s p).2

theorem KeepsRange.avoids {key : MlS} {p : ProgHOL 64}
    (ha : avoidsLocal key p = true) : KeepsRange key p := by
  intro F s hr hn
  obtain ⟨w, hw, hlo, hhi⟩ := hr
  exact ⟨w, (evaluate_avoidsLocal_flowing key p ha s (Or.inl hn)).trans hw, hlo, hhi⟩

theorem seq_none {F : Type} (s : PanSemStateFiniteExact 64 F) (p q : ProgHOL 64)
    (hn : (evaluateHOLFiniteState s (.seq p q)).1 = none) :
    ∃ mid, evaluateHOLFiniteState s p = (none, mid) ∧
      (evaluateHOLFiniteState mid q).1 = none ∧
      evaluateHOLFiniteState s (.seq p q) = evaluateHOLFiniteState mid q := by
  rw [evaluateHOLFiniteState_seq_line780] at hn ⊢
  cases hp : evaluateHOLFiniteState s p with
  | mk r mid =>
    rw [hp] at hn
    cases r with
    | none => exact ⟨mid, rfl, hn, rfl⟩
    | some r => simp_all

theorem KeepsRange.seq {key : MlS} {p q : ProgHOL 64}
    (hp : KeepsRange key p) (hq : KeepsRange key q) : KeepsRange key (.seq p q) := by
  intro F s hr hn
  obtain ⟨mid, hmid, hqnone, heq⟩ := seq_none s p q hn
  rw [heq]
  have hm := hp s hr (by rw [hmid])
  rw [hmid] at hm
  exact hq mid hm hqnone

theorem KeepsRange.ite {key : MlS} {c : ExpHOL 64} {p q : ProgHOL 64}
    (hp : KeepsRange key p) (hq : KeepsRange key q) : KeepsRange key (.ite c p q) := by
  intro F s hr hn
  rw [evaluateHOLFiniteState_ite] at hn ⊢
  split
  · rename_i flag hflag
    rw [hflag] at hn
    dsimp only at hn ⊢
    split
    · rw [if_pos (by assumption)] at hn
      exact hq s hr hn
    · rw [if_neg (by assumption)] at hn
      exact hp s hr hn
  · simp_all

theorem KeepsRange.dec {key name : MlS} {shape : ShapeHOL} {e : ExpHOL 64} {body : ProgHOL 64}
    (hne : key ≠ name) (hb : KeepsRange key body) : KeepsRange key (.dec name shape e body) := by
  intro F s hr hn
  cases hrun : evaluateHOLFiniteState s (.dec name shape e body) with
  | mk result post =>
    rw [hrun] at hn
    dsimp only at hn ⊢
    subst result
    obtain ⟨value, inner, hi, hrestore⟩ := dec_flowing (Or.inl rfl) hrun
    obtain ⟨w, hw, hlo, hhi⟩ := hr
    have he : RangeAt key (setVarHOLFinite name value s) := by
      refine ⟨w, ?_, hlo, hhi⟩
      simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne] using hw
    have ho := hb (setVarHOLFinite name value s) he (by rw [hi])
    rw [hi] at ho
    obtain ⟨v, hv, hvlo, hvhi⟩ := ho
    refine ⟨v, ?_, hvlo, hvhi⟩
    rw [hrestore, InitECandidate.Solver.PanRunBounded.resVarEq_lookup, if_neg hne]
    exact hv

theorem KeepsRange.assign_const (key : MlS) (v : BitVec 64)
    (hlo : 0 < v.toNat) (hhi : v.toNat ≤ 64) :
    KeepsRange key (.assign .local key (.const v)) := by
  intro F s hr hn
  obtain ⟨w, hw, _, _⟩ := hr
  have run : evaluateHOLFiniteState s (.assign .local key (.const v)) =
      (none, setVarHOLFinite key (.val (.word v)) s) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, hw,
      lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
      shapeOfHOLExact, shapeEqHOL]
  rw [run]
  exact ⟨v, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], hlo, hhi⟩


def AdvanceOnRange (counter adv : MlS) (body : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (y : BitVec 64),
    s.locals.lookup counter = some (.val (.word y)) → RangeAt adv s →
    (evaluateHOLFiniteState s body).1 = none →
    ∃ stride : BitVec 64, 0 < stride.toNat ∧ stride.toNat ≤ 64 ∧
      (evaluateHOLFiniteState s body).2.locals.lookup counter = some (.val (.word (y + stride)))

theorem advance_seq {counter adv : MlS} {prelude : ProgHOL 64}
    (hp : KeepsRange adv prelude) (ha : avoidsLocal counter prelude = true) :
    AdvanceOnRange counter adv (.seq prelude
      (.assign .local counter (.op .add [.var .local counter, .var .local adv]))) := by
  intro F s y hy hr hn
  obtain ⟨mid, hmid, htail, heq⟩ := seq_none s prelude _ hn
  have hpn : (evaluateHOLFiniteState s prelude).1 = none := by rw [hmid]
  have hkeep := evaluate_avoidsLocal_flowing counter prelude ha s (Or.inl hpn)
  have hrange := hp s hr hpn
  rw [hmid] at hkeep hrange
  have hcounter : mid.locals.lookup counter = some (.val (.word y)) := hkeep.trans hy
  obtain ⟨stride, hs, hlo, hhi⟩ := hrange
  change mid.locals.lookup adv = some (.val (.word stride)) at hs
  have run : evaluateHOLFiniteState mid
      (.assign .local counter (.op .add [.var .local counter, .var .local adv])) =
      (none, setVarHOLFinite counter (.val (.word (y + stride))) mid) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact,
      hcounter, hs, wordOpHOL, wordOp, valueIsWord, valueWord,
      lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
      shapeOfHOLExact, shapeEqHOL]
  rw [heq, run]
  exact ⟨stride, hlo, hhi, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩

theorem advance_dec {counter name : MlS} {shape : ShapeHOL} {e : ExpHOL 64} {body : ProgHOL 64}
    (hne : counter ≠ name) (hb : VariableAdvance counter body) :
    VariableAdvance counter (.dec name shape e body) := by
  intro F s y hy hn
  cases hrun : evaluateHOLFiniteState s (.dec name shape e body) with
  | mk result post =>
    rw [hrun] at hn
    dsimp only at hn ⊢
    subst result
    obtain ⟨value, inner, hi, hrestore⟩ := dec_flowing (Or.inl rfl) hrun
    have he : (setVarHOLFinite name value s).locals.lookup counter = some (.val (.word y)) := by
      simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne] using hy
    have ho := hb (setVarHOLFinite name value s) y he (by rw [hi])
    rw [hi] at ho
    obtain ⟨stride, hlo, hhi, hc⟩ := ho
    refine ⟨stride, hlo, hhi, ?_⟩
    rw [hrestore, InitECandidate.Solver.PanRunBounded.resVarEq_lookup, if_neg hne]
    exact hc

theorem advance_init {counter adv : MlS} {body : ProgHOL 64}
    (hne : counter ≠ adv) (hb : AdvanceOnRange counter adv body) :
    VariableAdvance counter (.dec adv .one (.const 1) body) := by
  intro F s y hy hn
  have he : (setVarHOLFinite adv (.val (.word (1 : BitVec 64))) s).locals.lookup counter =
      some (.val (.word y)) := by
    simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne] using hy
  have hr : RangeAt adv (setVarHOLFinite adv (.val (.word (1 : BitVec 64))) s) := by
    refine ⟨1, ?_, by decide, by decide⟩
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_dec_total] at hn ⊢
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL] at hn ⊢
  cases hi : evaluateHOLFiniteState (setVarHOLFinite adv (.val (.word (1 : BitVec 64))) s) body with
  | mk result post =>
    rw [hi] at hn
    cases result with
    | none =>
      have ho := hb (setVarHOLFinite adv (.val (.word (1 : BitVec 64))) s) y he hr (by rw [hi])
      rw [hi] at ho
      obtain ⟨stride, hlo, hhi, hc⟩ := ho
      refine ⟨stride, hlo, hhi, ?_⟩
      simpa [InitECandidate.Solver.PanRunBounded.resVarEq_lookup, hne] using hc
    | some r => simp_all

end InitECandidate.Solver.Wave8Leaves.S04.AdvanceEffects
