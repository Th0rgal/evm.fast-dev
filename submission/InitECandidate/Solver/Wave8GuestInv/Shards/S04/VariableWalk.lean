import InitECandidate.Solver.Wave8GuestInv.Shards.S04.RlpWalk

/-! Fresh-address walk with a variable positive stride, adapted from the local
RlpWalk.lean (provenance recorded there). The cap is domainBytes, so the total
loop bound matches compute_jumpdests exactly. The concrete body proof is in JumpAdvance.lean. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S04

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8Leaves.S04.Light InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingCombinators
open InitECandidate.Solver.Wave8Leaves.S04.Rlp

def tightWalkRank (a : BitVec 64) : Nat := min (heapEnd - a.toNat) domainBytes

def tightWalkMu (d i : MlS) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat := fun s =>
  match s.locals.lookup d, s.locals.lookup i with
  | some (.val (.word x)), some (.val (.word y)) => tightWalkRank (x + y)
  | _, _ => 0

theorem tightWalkMu_le (d i : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    tightWalkMu d i s ≤ domainBytes := by
  unfold tightWalkMu
  split
  · exact Nat.min_le_right _ _
  · exact Nat.zero_le _

theorem tightWalkRank_step (a stride : BitVec 64)
    (hs : 0 < stride.toNat) (hs2 : stride.toNat ≤ 64)
    (hlo : sourceBase ≤ a.toNat) (hhi : a.toNat < heapEnd) :
    tightWalkRank (a + stride) < tightWalkRank a := by
  have eH : heapEnd = 2701131776 + 8 * 3888119741 := by decide
  have eS : sourceBase = 2701131776 := by decide
  have eD : domainBytes = heapEnd - sourceBase := rfl
  have hadd : (a + stride).toNat = a.toNat + stride.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  unfold tightWalkRank
  rw [hadd]
  omega

/-- The stride may depend on the run, but remains in the interval [1,64]. -/
def VariableAdvance (i : MlS) (body : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (y : BitVec 64),
    s.locals.lookup i = some (.val (.word y)) →
    (evaluateHOLFiniteState s body).1 = none →
    ∃ stride : BitVec 64, 0 < stride.toNat ∧ stride.toNat ≤ 64 ∧
      (evaluateHOLFiniteState s body).2.locals.lookup i = some (.val (.word (y + stride)))

theorem while_variable_walk {cond : ExpHOL 64} {body : ProgHOL 64} {d i : MlS}
    (hadvance : VariableAdvance i body)
    (hd : avoidsLocal d body = true) (hfirst : FirstAccess d i body)
    (hstraight : extStraightLine body = true) (hnc : noTopContinue body = true) :
    TerminatingProgBoundedOn GuestInv (.while cond body) ((domainBytes + 1) * (0 + 1)) := by
  have hentry : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      GuestInv s → GuestInv (decClockHOLFinite s) :=
    fun s h => guestInv_congr (s := s) rfl rfl rfl rfl h
  have hstep : LoopStep (tightWalkMu d i) cond body 0 GuestInv := by
    apply while_step_of_progBoundedOn GuestInv (tightWalkMu d i) cond
      (straightOn _ hstraight) hentry
    intro F s word hcode hP hcond hnz hclk
    dsimp only
    intro hflow
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none := by
      rcases hflow with h | h
      · exact h
      · exact absurd h (evaluate_noTopContinue body hnc _)
    obtain ⟨x, y, hx, hy, hlo, hhi⟩ := hfirst (decClockHOLFinite s) (hentry s hP) hnone
    obtain ⟨stride, hs, hs2, hnext⟩ := hadvance (decClockHOLFinite s) y hy hnone
    have hbase := evaluate_avoidsLocal_flowing d body hd (decClockHOLFinite s) (Or.inl hnone)
    have hxp := hbase.trans hx
    change s.locals.lookup d = some (.val (.word x)) at hx
    change s.locals.lookup i = some (.val (.word y)) at hy
    refine ⟨?_, guestInv_evaluate _ body (hentry s hP)⟩
    unfold tightWalkMu
    rw [hxp, hnext, hx, hy]
    dsimp only
    rw [← BitVec.add_assoc]
    exact tightWalkRank_step _ _ hs hs2 hlo hhi
  intro F s hcode hP
  exact TerminatingProgBoundedOn.while_measure (tightWalkMu d i) cond body hstep s hcode
    ⟨hP, tightWalkMu_le d i s⟩

end InitECandidate.Solver.Wave8Leaves.S04
