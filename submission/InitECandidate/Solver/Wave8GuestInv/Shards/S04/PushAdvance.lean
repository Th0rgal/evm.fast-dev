import InitECandidate.Solver.Wave8GuestInv.Shards.S04.AdvanceEffects

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S04.AdvanceEffects
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded
open Flapjack.Compiler.Encoders.Asm

def pushGuard (op : MlS) : ExpHOL 64 :=
  .op .and [
    .cmp .notEqual (.const 0) (.cmp .notLower (.var .local op) (.const 96)),
    .cmp .notEqual (.const 0) (.cmp .notLower (.const 127) (.var .local op))]

def pushStride (op : MlS) : ExpHOL 64 :=
  .op .add [.op .sub [.var .local op, .const 96], .const 2]

theorem pushGuard_active {F : Type} (s : PanSemStateFiniteExact 64 F) (op : MlS)
    (flag : BitVec 64)
    (hc : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (pushGuard op) = some (.val (.word flag))) (hnz : flag ≠ 0) :
    ∃ w : BitVec 64, s.locals.lookup op = some (.val (.word w)) ∧
      96 ≤ w.toNat ∧ w.toNat ≤ 127 := by
  cases hl : s.locals.lookup op with
  | none => simp [pushGuard, evalHOLExact, evalListHOLExact, lookupKvarHOLExact, hl] at hc
  | some value =>
    cases value with
    | rStruct vs => simp [pushGuard, evalHOLExact, evalListHOLExact, lookupKvarHOLExact, hl] at hc
    | nStruct n vs => simp [pushGuard, evalHOLExact, evalListHOLExact, lookupKvarHOLExact, hl] at hc
    | val word =>
      cases word with
      | word w =>
        refine ⟨w, rfl, ?_⟩
        by_cases hlo : (96 : BitVec 64) ≤ w
        · by_cases hhi : w ≤ (127 : BitVec 64)
          · change 96 ≤ w.toNat at hlo
            change w.toNat ≤ 127 at hhi
            exact ⟨hlo, hhi⟩
          · simp [pushGuard, evalHOLExact, evalListHOLExact, hl,
              wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord] at hc
            change ((if (96 : BitVec 64) ≤ w then (1 : BitVec 64) else 0) &&&
              ((if w ≤ (127 : BitVec 64) then 1 else 0) &&& 18446744073709551615)) = flag at hc
            simp only [hlo, hhi, ↓reduceIte, BitVec.and_zero] at hc
            exact False.elim (hnz hc.symm)
        · simp [pushGuard, evalHOLExact, evalListHOLExact, hl,
            wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord] at hc
          change ((if (96 : BitVec 64) ≤ w then (1 : BitVec 64) else 0) &&&
            ((if w ≤ (127 : BitVec 64) then 1 else 0) &&& 18446744073709551615)) = flag at hc
          simp only [hlo, ↓reduceIte] at hc
          exact False.elim (hnz (hc.symm.trans (BitVec.zero_and (x := _))))

theorem pushStride_bounds (w : BitVec 64) (hlo : 96 ≤ w.toNat) (hhi : w.toNat ≤ 127) :
    0 < (w - 96 + 2).toNat ∧ (w - 96 + 2).toNat ≤ 64 := by
  have hv : (96 : BitVec 64) ≤ w := hlo
  have hs : (w - 96).toNat = w.toNat - 96 := BitVec.toNat_sub_of_le hv
  have ha : (w - 96 + 2).toNat = w.toNat - 96 + 2 := by
    rw [BitVec.toNat_add_of_lt, hs] <;> simp_all <;> omega
  rw [ha]
  omega


theorem KeepsRange.push_ite (adv op : MlS) {rest : ProgHOL 64}
    (hr : KeepsRange adv rest) :
    KeepsRange adv (.ite (pushGuard op) (.assign .local adv (pushStride op)) rest) := by
  intro F s hR hn
  rw [evaluateHOLFiniteState_ite] at hn ⊢
  split
  · rename_i flag hflag
    rw [hflag] at hn
    dsimp only at hn ⊢
    split
    · rw [if_pos (by assumption)] at hn
      exact hr s hR hn
    · rename_i hnz
      obtain ⟨w, hw, hlo, hhi⟩ := pushGuard_active s op flag hflag hnz
      obtain ⟨old, hold, _, _⟩ := hR
      have run : evaluateHOLFiniteState s (.assign .local adv (pushStride op)) =
          (none, setVarHOLFinite adv (.val (.word (w - 96 + 2))) s) := by
        simp [evaluateHOLFiniteState_assign, pushStride, evalHOLExact, evalListHOLExact,
          hw, hold, wordOpHOL, wordOp, valueIsWord, valueWord,
          lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
          shapeOfHOLExact, shapeEqHOL]
      rw [run]
      obtain ⟨hl, hh⟩ := pushStride_bounds w hlo hhi
      exact ⟨w - 96 + 2, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], hl, hh⟩
  · simp_all

syntax "s04_range" : tactic
macro_rules
  | `(tactic| s04_range) => `(tactic| first
      | (apply KeepsRange.avoids; rfl)
      | (apply KeepsRange.assign_const <;> decide)
      | (apply KeepsRange.push_ite; s04_range)
      | (apply KeepsRange.seq <;> s04_range)
      | (apply KeepsRange.ite <;> s04_range)
      | (apply KeepsRange.dec
         · decide
         · s04_range))

end InitECandidate.Solver.Wave8Leaves.S04.AdvanceEffects
