import InitECandidate.Solver.Wave8GuestInv.ContractParts.C08
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01AllocMpt
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkCacheGetRootTop
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_max
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.RlpHelpers

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03

theorem udivmod_step_inv (a b : Nat) {k q r : Nat}
    (hinv : q * b + r * 2 ^ (k + 1) = (a / 2 ^ (k + 1)) * 2 ^ (k + 1) ∧
            r < b ∧ q % 2 ^ (k + 1) = 0) :
    let bit := (a / 2 ^ k) % 2
    let r1 := 2 * r + bit
    let q' := if b ≤ r1 then q + 2 ^ k else q
    let r' := if b ≤ r1 then r1 - b else r1
    q' * b + r' * 2 ^ k = (a / 2 ^ k) * 2 ^ k ∧ r' < b ∧ q' % 2 ^ k = 0 := by
  intro bit r1 q' r'
  obtain ⟨heq, hrlt, hqmod⟩ := hinv
  have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := by rw [Nat.pow_succ]
  have hbit_eq : a / 2 ^ k = 2 * (a / 2 ^ (k + 1)) + bit := by
    dsimp [bit]; rw [hpow, ← Nat.div_div_eq_div_mul]; omega
  have hbit_lt : bit < 2 := by dsimp [bit]; omega
  have hq_div : 2 ^ k ∣ q :=
    dvd_of_mul_right_dvd (hpow ▸ Nat.dvd_of_mod_eq_zero hqmod)
  by_cases hge : b ≤ r1
  · dsimp [q', r']; rw [if_pos hge, if_pos hge]
    refine ⟨?_, by dsimp [r1] at *; omega,
      Nat.mod_eq_zero_of_dvd (dvd_add hq_div (dvd_refl _))⟩
    calc (q + 2 ^ k) * b + (r1 - b) * 2 ^ k
      _ = q * b + (b + (r1 - b)) * 2 ^ k := by ring
      _ = q * b + r1 * 2 ^ k := by rw [Nat.add_sub_of_le hge]
      _ = (q * b + r * (2 ^ k * 2)) + bit * 2 ^ k := by dsimp [r1]; ring
      _ = (a / 2 ^ (k + 1)) * (2 ^ k * 2) + bit * 2 ^ k := by rw [← hpow, heq]
      _ = (2 * (a / 2 ^ (k + 1)) + bit) * 2 ^ k := by ring
      _ = (a / 2 ^ k) * 2 ^ k := by rw [hbit_eq]
  · dsimp [q', r']; rw [if_neg hge, if_neg hge]
    refine ⟨?_, by omega, Nat.mod_eq_zero_of_dvd hq_div⟩
    calc q * b + r1 * 2 ^ k
      _ = (q * b + r * (2 ^ k * 2)) + bit * 2 ^ k := by dsimp [r1]; ring
      _ = (a / 2 ^ (k + 1)) * (2 ^ k * 2) + bit * 2 ^ k := by rw [← hpow, heq]
      _ = (2 * (a / 2 ^ (k + 1)) + bit) * 2 ^ k := by ring
      _ = (a / 2 ^ k) * 2 ^ k := by rw [hbit_eq]

theorem bv_or_pow2_eq_add {q : BitVec 64} {k : Nat} (hk : k < 64)
    (hq_lt : q.toNat + 2 ^ k < 2 ^ 64)
    (hqmod : q.toNat % 2 ^ (k + 1) = 0) :
    (q ||| ((1 : BitVec 64) <<< BitVec.ofNat 64 k)).toNat = q.toNat + 2 ^ k := by
  have hk_lt : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hk
  have hk_bv : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1k : ((1 : BitVec 64) <<< BitVec.ofNat 64 k) = BitVec.ofNat 64 (2 ^ k) := by
    apply BitVec.eq_of_toNat_eq
    have : ((1 : BitVec 64) <<< BitVec.ofNat 64 k) = (1 : BitVec 64) <<< (BitVec.ofNat 64 k).toNat := rfl
    rw [this, BitVec.toNat_shiftLeft, hk_bv, BitVec.toNat_ofNat]
    change 1 <<< k % 2 ^ 64 = 2 ^ k % 2 ^ 64
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [h1k]
  have hand : q &&& BitVec.ofNat 64 (2 ^ k) = 0#64 := by
    ext j hj
    rw [BitVec.getElem_and, BitVec.getElem_eq_testBit_toNat, BitVec.getElem_eq_testBit_toNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk_lt, Nat.testBit_two_pow, BitVec.getElem_zero]
    by_cases hkj : k = j
    · subst hkj
      simp only [decide_true, Bool.and_true, Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not]
      obtain ⟨m, hm⟩ : 2 ^ (k + 1) ∣ q.toNat := Nat.dvd_of_mod_eq_zero hqmod
      rw [hm, Nat.pow_succ, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
      omega
    · simp [hkj]
  have hor := (BitVec.add_eq_or_of_and_eq_zero q (BitVec.ofNat 64 (2 ^ k)) hand).symm
  rw [hor, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk_lt, Nat.mod_eq_of_lt hq_lt]

theorem bv_r1_eq {r a : BitVec 64} {k : Nat} (hk : k < 64)
    (hr_lt : 2 * r.toNat + 1 < 2 ^ 64) :
    ((r <<< (1 : BitVec 64)) ||| ((a >>> BitVec.ofNat 64 k) &&& (1 : BitVec 64))).toNat =
      2 * r.toNat + (a.toNat / 2 ^ k) % 2 := by
  have hr_sh : (r <<< (1 : BitVec 64)).toNat = 2 * r.toNat := by
    have : (r <<< (1 : BitVec 64)) = r <<< (1 : Nat) := rfl
    rw [this, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, pow_one,
      Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  have hk_bv : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hshk : (a >>> BitVec.ofNat 64 k).toNat = a.toNat / 2 ^ k := by
    have : (a >>> BitVec.ofNat 64 k) = a >>> (BitVec.ofNat 64 k).toNat := rfl
    rw [this, BitVec.toNat_ushiftRight, hk_bv, Nat.shiftRight_eq_div_pow]
  have hbit_val : ((a >>> BitVec.ofNat 64 k) &&& (1 : BitVec 64)).toNat = (a.toNat / 2 ^ k) % 2 := by
    rw [BitVec.toNat_and, hshk]
    exact Nat.and_one_is_mod _
  have hand0 : (r <<< (1 : BitVec 64)) &&& ((a >>> BitVec.ofNat 64 k) &&& (1 : BitVec 64)) = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, hr_sh, hbit_val]
    have hbit2 : (a.toNat / 2 ^ k) % 2 = 0 ∨ (a.toNat / 2 ^ k) % 2 = 1 := by omega
    rcases hbit2 with hb | hb
    · rw [hb, Nat.and_zero]; rfl
    · rw [hb, Nat.and_one_is_mod]; change (2 * r.toNat) % 2 = 0; omega
  have hor := (BitVec.add_eq_or_of_and_eq_zero _ _ hand0).symm
  rw [hor, BitVec.toNat_add, hr_sh, hbit_val, Nat.mod_eq_of_lt (by omega)]


abbrev udivmodLoopBody : ProgHOL 64 :=
  .seq
    (.assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const 1#64]))
    (.seq
      (.assign .local (ofString "r")
        (.op .or [.shift .lsl (.var .local (ofString "r")) (.const 1#64),
                  .op .and [.shift .lsr (.var .local (ofString "a")) (.var .local (ofString "i")), .const 1#64]]))
      (.ite (.cmp .notLower (.var .local (ofString "r")) (.var .local (ofString "b")))
        (.seq
          (.assign .local (ofString "r") (.op .sub [.var .local (ofString "r"), .var .local (ofString "b")]))
          (.assign .local (ofString "q")
            (.op .or [.var .local (ofString "q"),
                      .shift .lsl (.const 1#64) (.var .local (ofString "i"))])))
        .skip))

abbrev udivmodLoop : ProgHOL 64 :=
  .while (.cmp .less (.const 0#64) (.var .local (ofString "i"))) udivmodLoopBody

theorem udivmod_loop_inv {F : Type} (aw bw : BitVec 64) (hb0 : 0 < bw.toNat) :
    ∀ (k : Nat) (cur : PanSemStateFiniteExact 64 F) (qw rw_ : BitVec 64),
      k ≤ 64 →
      cur.locals.lookup (ofString "a") = some (.val (.word aw)) →
      cur.locals.lookup (ofString "b") = some (.val (.word bw)) →
      cur.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 k))) →
      cur.locals.lookup (ofString "q") = some (.val (.word qw)) →
      cur.locals.lookup (ofString "r") = some (.val (.word rw_)) →
      (qw.toNat * bw.toNat + rw_.toNat * 2 ^ k = (aw.toNat / 2 ^ k) * 2 ^ k ∧
       rw_.toNat < bw.toNat ∧ qw.toNat % 2 ^ k = 0) →
      (evaluateHOLFiniteState cur udivmodLoop).1 = none →
      ∃ qf rf : BitVec 64,
        (evaluateHOLFiniteState cur udivmodLoop).2.locals.lookup (ofString "q") = some (.val (.word qf)) ∧
        (evaluateHOLFiniteState cur udivmodLoop).2.locals.lookup (ofString "r") = some (.val (.word rf)) ∧
        qf.toNat * bw.toNat + rf.toNat = aw.toNat ∧ rf.toNat < bw.toNat := by
  intro k
  induction k with
  | zero =>
    intro cur qw rw_ _ ha hb hi hq hr hinv hnone
    have hw := evaluateHOLFiniteState_while_fixClockRewrite cur
      (.cmp .less (.const 0#64) (.var .local (ofString "i"))) udivmodLoopBody
    have hc : @evalHOLFinite 64 F _ cur (fun a => Classical.propDecidable (cur.memaddrs a))
        (.cmp .less (.const 0#64) (.var .local (ofString "i"))) = some (.val (.word 0)) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, hi, Compiler.Encoders.Asm.wordCmpHOL]
      decide
    rw [hc] at hw; dsimp only at hw; rw [if_neg (by simp)] at hw
    rw [hw]
    refine ⟨qw, rw_, hq, hr, ?_, hinv.2.1⟩
    simpa using hinv.1
  | succ k ih =>
    intro cur qw rw_ hkle ha hb hi hq hr hinv hnone
    have hk64 : k < 64 := by omega
    have hw := evaluateHOLFiniteState_while_fixClockRewrite cur
      (.cmp .less (.const 0#64) (.var .local (ofString "i"))) udivmodLoopBody
    have hc : @evalHOLFinite 64 F _ cur (fun a => Classical.propDecidable (cur.memaddrs a))
        (.cmp .less (.const 0#64) (.var .local (ofString "i"))) = some (.val (.word 1)) := by
      have hk1_lt63 : (BitVec.ofNat 64 (k + 1)).toNat < 2 ^ 63 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      have hk1_pos : (0#64).toNat < (BitVec.ofNat 64 (k + 1)).toNat := by
        change 0 < (BitVec.ofNat 64 (k + 1)).toNat
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      rw [evalHOLFinite_eq_toExact]
      have hsl : Compiler.Encoders.Asm.holAsmSignedLess (0#64) (BitVec.ofNat 64 (k + 1)) = true := by
        rw [holAsmSignedLess_small (0#64) (BitVec.ofNat 64 (k + 1)) (by decide) hk1_lt63, decide_eq_true_eq]
        exact hk1_pos
      simp [evalHOLExact, hi, Compiler.Encoders.Asm.wordCmpHOL, hsl]
    rw [hc] at hw; dsimp only at hw; rw [if_pos (by decide)] at hw
    by_cases hclk0 : cur.clock = 0
    · rw [if_pos hclk0] at hw; rw [hw] at hnone; simp at hnone
    · rw [if_neg hclk0] at hw
      set t0 := decClockHOLFinite cur
      have ha0 : t0.locals.lookup (ofString "a") = some (.val (.word aw)) := ha
      have hb0' : t0.locals.lookup (ofString "b") = some (.val (.word bw)) := hb
      have hi0 : t0.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (k + 1)))) := hi
      have hq0 : t0.locals.lookup (ofString "q") = some (.val (.word qw)) := hq
      have hr0 : t0.locals.lookup (ofString "r") = some (.val (.word rw_)) := hr
      have hsub_k : BitVec.ofNat 64 (k + 1) - 1#64 = BitVec.ofNat 64 k := by
        have hk1_nat : (BitVec.ofNat 64 (k + 1)).toNat = k + 1 := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hk_nat : (BitVec.ofNat 64 k).toNat = k := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have h1_nat : (1#64).toNat = 1 := rfl
        apply BitVec.eq_of_toNat_eq
        have hle1 : 1#64 ≤ BitVec.ofNat 64 (k + 1) := by
          rw [BitVec.le_def, h1_nat, hk1_nat]; omega
        rw [BitVec.toNat_sub_of_le hle1, hk1_nat, h1_nat, hk_nat]; omega
      have hs1 : evaluateHOLFiniteState t0
          (.assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const 1#64])) =
          (none, setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 k))) t0) := by
        simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi0,
          lookupKvarHOLExact, isValidValueHOLExact, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setVarHOLFinite,
          valueIsWord, valueWord, wordOpHOL, wordOp, hsub_k]
      set t1 := setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 k))) t0
      have ha1 : t1.locals.lookup (ofString "a") = some (.val (.word aw)) := by
        simp [t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ha0,
          show ofString "i" ≠ ofString "a" by decide]
      have hb1 : t1.locals.lookup (ofString "b") = some (.val (.word bw)) := by
        simp [t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hb0',
          show ofString "i" ≠ ofString "b" by decide]
      have hi1 : t1.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 k))) := by
        simp [t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hq1 : t1.locals.lookup (ofString "q") = some (.val (.word qw)) := by
        simp [t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hq0,
          show ofString "i" ≠ ofString "q" by decide]
      have hr1_lk : t1.locals.lookup (ofString "r") = some (.val (.word rw_)) := by
        simp [t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hr0,
          show ofString "i" ≠ ofString "r" by decide]
      -- Bound on rw_: since rw_.toNat * 2^(k+1) ≤ aw.toNat < 2^64 and k+1 ≥ 1, 2 * rw_.toNat + 1 < 2^64!
      have hrw_2_lt : 2 * rw_.toNat + 1 < 2 ^ 64 := by
        have h1 : rw_.toNat * 2 ^ (k + 1) ≤ aw.toNat := by
          have := hinv.1
          have : (aw.toNat / 2 ^ (k + 1)) * 2 ^ (k + 1) ≤ aw.toNat := Nat.div_mul_le_self _ _
          omega
        have h2 : 2 ≤ 2 ^ (k + 1) := by
          rw [Nat.pow_succ]; have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega); omega
        have : rw_.toNat * 2 ≤ rw_.toNat * 2 ^ (k + 1) := Nat.mul_le_mul_left _ h2
        have := aw.isLt
        omega
      let r1_bv : BitVec 64 :=
        (rw_ <<< 1#64) ||| ((aw >>> k) &&& 1#64)
      have hr1_eq_bv : r1_bv = (rw_ <<< (1 : BitVec 64)) ||| ((aw >>> BitVec.ofNat 64 k) &&& (1 : BitVec 64)) := by
        dsimp [r1_bv]
        have hsh : aw >>> k = aw >>> BitVec.ofNat 64 k := by
          apply BitVec.eq_of_toNat_eq
          have hk_m : k % 18446744073709551616 = k := Nat.mod_eq_of_lt (by omega)
          simp [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, hk_m]
        rw [hsh]; rfl
      have hr1_nat : r1_bv.toNat = 2 * rw_.toNat + (aw.toNat / 2 ^ k) % 2 := by
        rw [hr1_eq_bv]; exact bv_r1_eq hk64 hrw_2_lt
      have hs2 : evaluateHOLFiniteState t1
          (.assign .local (ofString "r")
            (.op .or [.shift .lsl (.var .local (ofString "r")) (.const 1#64),
                      .op .and [.shift .lsr (.var .local (ofString "a")) (.var .local (ofString "i")), .const 1#64]])) =
          (none, setVarHOLFinite (ofString "r") (.val (.word r1_bv)) t1) := by
        have hk_mod : k % 18446744073709551616 = k := Nat.mod_eq_of_lt (by omega)
        have hk_n64 : ¬ 64 ≤ k := by omega
        have hand1 : ∀ x : BitVec 64, x &&& 18446744073709551615#64 = x := by
          intro x; apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_and]
          change x.toNat &&& (2 ^ 64 - 1) = x.toNat
          rw [Nat.and_two_pow_sub_one_eq_mod _ 64, Nat.mod_eq_of_lt x.isLt]
        have hor0 : ∀ x : BitVec 64, OrOp.or x 0#64 = x := by
          intro x; change x ||| 0#64 = x; exact BitVec.or_zero
        simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hr1_lk, ha1, hi1,
          lookupKvarHOLExact, isValidValueHOLExact, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setVarHOLFinite,
          valueIsWord, valueWord, wordOpHOL, wordOp, wordShiftHOL, r1_bv,
          BitVec.toNat_ofNat, hk_mod, hk_n64, hand1, hor0]
        rfl
      set t2 := setVarHOLFinite (ofString "r") (.val (.word r1_bv)) t1
      have ha2 : t2.locals.lookup (ofString "a") = some (.val (.word aw)) := by
        simp [t2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ha1,
          show ofString "r" ≠ ofString "a" by decide]
      have hb2 : t2.locals.lookup (ofString "b") = some (.val (.word bw)) := by
        simp [t2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hb1,
          show ofString "r" ≠ ofString "b" by decide]
      have hi2 : t2.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 k))) := by
        simp [t2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi1,
          show ofString "r" ≠ ofString "i" by decide]
      have hq2 : t2.locals.lookup (ofString "q") = some (.val (.word qw)) := by
        simp [t2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hq1,
          show ofString "r" ≠ ofString "q" by decide]
      have hr2 : t2.locals.lookup (ofString "r") = some (.val (.word r1_bv)) := by
        simp [t2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hstep_math := udivmod_step_inv aw.toNat bw.toNat hinv
      dsimp only at hstep_math
      by_cases hge : bw.toNat ≤ r1_bv.toNat
      · have hnotlt : ¬ r1_bv < bw := by rw [BitVec.lt_def]; omega
        have hite : evaluateHOLFiniteState t2
            (.ite (.cmp .notLower (.var .local (ofString "r")) (.var .local (ofString "b")))
              (.seq
                (.assign .local (ofString "r") (.op .sub [.var .local (ofString "r"), .var .local (ofString "b")]))
                (.assign .local (ofString "q")
                  (.op .or [.var .local (ofString "q"),
                            .shift .lsl (.const 1#64) (.var .local (ofString "i"))])))
              .skip) =
            (none,
             setVarHOLFinite (ofString "q") (.val (.word (qw ||| (1#64 <<< k))))
               (setVarHOLFinite (ofString "r") (.val (.word (r1_bv - bw))) t2)) := by
          have hk_mod : k % 18446744073709551616 = k := Nat.mod_eq_of_lt (by omega)
          have hk_n64 : ¬ 64 ≤ k := by omega
          have hor0 : ∀ x : BitVec 64, OrOp.or x 0#64 = x := by
            intro x; change x ||| 0#64 = x; exact BitVec.or_zero
          simp [evaluateHOLFiniteState_ite, evalHOLExact, hr2, hb2,
            Compiler.Encoders.Asm.wordCmpHOL, hnotlt, evaluateHOLFiniteState_seq_line780,
            evaluateHOLFiniteState_assign, evalListHOLExact, lookupKvarHOLExact,
            isValidValueHOLExact, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setVarHOLFinite,
            valueIsWord, valueWord, wordOpHOL, wordOp, wordShiftHOL,
            HolFiniteMapExact.lookup_update, FUPDATE, hi2, hq2,
            BitVec.toNat_ofNat, hk_mod, hk_n64, hor0,
            show ofString "r" ≠ ofString "i" by decide,
            show ofString "r" ≠ ofString "q" by decide]
          rfl
        have hbody_eval : evaluateHOLFiniteState t0 udivmodLoopBody =
            (none,
             setVarHOLFinite (ofString "q") (.val (.word (qw ||| (1#64 <<< k))))
               (setVarHOLFinite (ofString "r") (.val (.word (r1_bv - bw))) t2)) := by
          unfold udivmodLoopBody
          rw [evaluateHOLFiniteState_seq_line780, hs1]; dsimp only
          rw [evaluateHOLFiniteState_seq_line780, hs2]; dsimp only
          exact hite
        rw [hbody_eval] at hw; dsimp only at hw
        have hge' : bw.toNat ≤ 2 * rw_.toNat + aw.toNat / 2 ^ k % 2 := by omega
        rw [if_pos hge', if_pos hge'] at hstep_math
        have hq_plus_lt : qw.toNat + 2 ^ k < 2 ^ 64 := by
          have : (qw.toNat + 2 ^ k) * 1 ≤ (qw.toNat + 2 ^ k) * bw.toNat := Nat.mul_le_mul_left _ hb0
          have : (aw.toNat / 2 ^ k) * 2 ^ k ≤ aw.toNat := Nat.div_mul_le_self _ _
          have := aw.isLt
          omega
        have hq_next_nat : (qw ||| (1#64 <<< k)).toNat = qw.toNat + 2 ^ k := by
          have hsh1 : (1#64 <<< k) = (1 : BitVec 64) <<< BitVec.ofNat 64 k := by
            apply BitVec.eq_of_toNat_eq
            have hk_m : k % 18446744073709551616 = k := Nat.mod_eq_of_lt (by omega)
            simp [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, hk_m]
          rw [hsh1]; exact bv_or_pow2_eq_add hk64 hq_plus_lt hinv.2.2
        have hr_next_nat : (r1_bv - bw).toNat = 2 * rw_.toNat + aw.toNat / 2 ^ k % 2 - bw.toNat := by
          rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hge), hr1_nat]
        set t3 := setVarHOLFinite (ofString "q") (.val (.word (qw ||| (1#64 <<< k))))
          (setVarHOLFinite (ofString "r") (.val (.word (r1_bv - bw))) t2)
        rw [hw] at hnone ⊢
        apply ih t3 (qw ||| (1#64 <<< k)) (r1_bv - bw) (by omega)
        · simp [t3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ha2,
            show ofString "q" ≠ ofString "a" by decide, show ofString "r" ≠ ofString "a" by decide]
        · simp [t3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hb2,
            show ofString "q" ≠ ofString "b" by decide, show ofString "r" ≠ ofString "b" by decide]
        · simp [t3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi2,
            show ofString "q" ≠ ofString "i" by decide, show ofString "r" ≠ ofString "i" by decide]
        · simp [t3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        · simp [t3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "q" ≠ ofString "r" by decide]
        · rw [hq_next_nat, hr_next_nat]; exact hstep_math
        · exact hnone
      · have hlt : r1_bv < bw := by rw [BitVec.lt_def]; omega
        have hite : evaluateHOLFiniteState t2
            (.ite (.cmp .notLower (.var .local (ofString "r")) (.var .local (ofString "b")))
              (.seq
                (.assign .local (ofString "r") (.op .sub [.var .local (ofString "r"), .var .local (ofString "b")]))
                (.assign .local (ofString "q")
                  (.op .or [.var .local (ofString "q"),
                            .shift .lsl (.const 1#64) (.var .local (ofString "i"))])))
              .skip) = (none, t2) := by
          simp [evaluateHOLFiniteState_ite, evalHOLExact, hr2, hb2,
            Compiler.Encoders.Asm.wordCmpHOL, hlt, evaluateHOLFiniteState_skip]
        have hbody_eval : evaluateHOLFiniteState t0 udivmodLoopBody = (none, t2) := by
          unfold udivmodLoopBody
          rw [evaluateHOLFiniteState_seq_line780, hs1]; dsimp only
          rw [evaluateHOLFiniteState_seq_line780, hs2]; dsimp only
          exact hite
        rw [hbody_eval] at hw; dsimp only at hw
        have hge' : ¬ bw.toNat ≤ 2 * rw_.toNat + aw.toNat / 2 ^ k % 2 := by omega
        rw [if_neg hge', if_neg hge'] at hstep_math
        rw [hw] at hnone ⊢
        exact ih t2 qw r1_bv (by omega) ha2 hb2 hi2 hq2 hr2 (by rw [hr1_nat]; exact hstep_math) hnone



theorem udivmodLoop_not_returned {F : Type} :
    ∀ (n : Nat) (t : PanSemStateFiniteExact 64 F) (rv : ValueHOL 64),
      t.clock ≤ n →
      (evaluateHOLFiniteState t udivmodLoop).1 ≠ some (.returned rv) := by
  have hbody_nret : ∀ (u : PanSemStateFiniteExact 64 F) (rv : ValueHOL 64),
      (evaluateHOLFiniteState u udivmodLoopBody).1 ≠ some (.returned rv) := by
    intro u rv hb
    unfold udivmodLoopBody at hb
    rw [evaluateHOLFiniteState_seq_line780] at hb
    rcases h1 : evaluateHOLFiniteState u _ with ⟨r1, m1⟩
    rw [h1] at hb
    cases r1 with
    | some _ =>
      dsimp only at hb; injection hb with hb; subst hb
      rw [evaluateHOLFiniteState_assign] at h1
      split at h1 <;> (try split at h1) <;> simp at h1
    | none =>
      dsimp only at hb
      rw [evaluateHOLFiniteState_seq_line780] at hb
      rcases h2 : evaluateHOLFiniteState m1 _ with ⟨r2, m2⟩
      rw [h2] at hb
      cases r2 with
      | some _ =>
        dsimp only at hb; injection hb with hb; subst hb
        rw [evaluateHOLFiniteState_assign] at h2
        split at h2 <;> (try split at h2) <;> simp at h2
      | none =>
        dsimp only at hb
        rw [evaluateHOLFiniteState_ite] at hb
        split at hb
        · split at hb
          · rw [evaluateHOLFiniteState_skip] at hb; simp at hb
          · rw [evaluateHOLFiniteState_seq_line780] at hb
            rcases h3 : evaluateHOLFiniteState m2 _ with ⟨r3, m3⟩
            rw [h3] at hb
            cases r3 with
            | some _ =>
              dsimp only at hb; injection hb with hb; subst hb
              rw [evaluateHOLFiniteState_assign] at h3
              split at h3 <;> (try split at h3) <;> simp at h3
            | none =>
              dsimp only at hb
              rw [evaluateHOLFiniteState_assign] at hb
              split at hb <;> (try split at hb) <;> simp at hb
        · simp at hb
  intro n
  induction n with
  | zero =>
    intro t rv hclk hr
    have hc0 : t.clock = 0 := Nat.eq_zero_of_le_zero hclk
    rw [show udivmodLoop = .while _ _ from rfl, evaluateHOLFiniteState_while_fixClockRewrite] at hr
    split at hr
    · dsimp only at hr; split at hr <;> [simp [hc0] at hr; simp at hr]
    · simp at hr
  | succ n ih =>
    intro t rv hclk hr
    rw [show udivmodLoop = .while _ _ from rfl, evaluateHOLFiniteState_while_fixClockRewrite] at hr
    split at hr
    · dsimp only at hr
      split at hr
      · split at hr
        · simp at hr
        · rcases hrun : evaluateHOLFiniteState (decClockHOLFinite t) udivmodLoopBody with ⟨rb, mb⟩
          rw [hrun] at hr
          have hle0 := evaluateHOLFiniteState_clock_le (decClockHOLFinite t) udivmodLoopBody
          rw [hrun] at hle0
          have hmb_le : mb.clock ≤ n := by change mb.clock ≤ t.clock - 1 at hle0; omega
          cases rb with
          | none => exact ih mb rv hmb_le hr
          | some r =>
            cases r with
            | «continue» => exact ih mb rv hmb_le hr
            | returned v =>
              exact hbody_nret (decClockHOLFinite t) v (by rw [hrun])
            | «break» | exception _ _ | timeOut | error | finalFfi _ => simp at hr
      · simp at hr
    · simp at hr

theorem udivmod_body_returns {F : Type}
    (ent : PanSemStateFiniteExact 64 F) (aw bw : BitVec 64)
    (hcode : ent.code = originalRuntimeCode)
    (ha : ent.locals.lookup (ofString "a") = some (.val (.word aw)))
    (hb : ent.locals.lookup (ofString "b") = some (.val (.word bw)))
    (rv : ValueHOL 64)
    (hret : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_udivmod)).1 =
      some (.returned rv)) :
    0 < bw.toNat ∧
    ∃ qw rw_ : BitVec 64,
      rv = .rStruct [.val (.word qw), .val (.word rw_)] ∧
      qw.toNat * bw.toNat + rw_.toNat = aw.toNat ∧
      rw_.toNat < bw.toNat ∧
      qw.toNat ≤ aw.toNat := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_udivmod,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hret
  -- First seq: if b == 0 then trap_with(2) else skip
  rw [evaluateHOLFiniteState_seq_line780] at hret
  by_cases hb0 : bw = 0
  · subst hb0
    have hite1 : evaluateHOLFiniteState ent
        (.ite (.cmp .equal (.var .local (ofString "b")) (.const 0#64))
          (.call (some (none, none)) (ofString "trap_with") [.const 2#64]) .skip) =
        evaluateHOLFiniteState ent (.call (some (none, none)) (ofString "trap_with") [.const 2#64]) := by
      simp [evaluateHOLFiniteState_ite, evalHOLExact, hb, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hite1] at hret
    rcases hc : evaluateHOLFiniteState ent (.call (some (none, none)) (ofString "trap_with") [.const 2#64]) with ⟨rc, sc⟩
    rw [hc] at hret
    cases rc with
    | some rc1 =>
      dsimp only at hret
      exact False.elim (WkBlockTxEnc.evaluate_call_trap_with_no_resumes ent 2#64 hcode
        (by rw [hc]; exact Or.inl ⟨rv, hret⟩))
    | none =>
      exact False.elim (evaluate_call_trap_with_no_none ent 2#64 hcode (by rw [hc]))
  · have hb_pos : 0 < bw.toNat := by
      have : bw ≠ 0#64 := hb0
      exact Nat.pos_of_ne_zero (fun h => this (BitVec.eq_of_toNat_eq h))
    have hite1 : evaluateHOLFiniteState ent
        (.ite (.cmp .equal (.var .local (ofString "b")) (.const 0#64))
          (.call (some (none, none)) (ofString "trap_with") [.const 2#64]) .skip) =
        (none, ent) := by
      have hbw0 : bw ≠ 0#64 := hb0
      simp [evaluateHOLFiniteState_ite, evalHOLExact, hb, Compiler.Encoders.Asm.wordCmpHOL,
        hbw0, evaluateHOLFiniteState_skip]
    rw [hite1] at hret; dsimp only at hret
    -- Second seq: if a <+ b then return {0, a} else skip
    rw [evaluateHOLFiniteState_seq_line780] at hret
    by_cases halb : aw.toNat < bw.toNat
    · have hlt_bv : aw < bw := by rw [BitVec.lt_def]; exact halb
      have hite2 : evaluateHOLFiniteState ent
          (.ite (.cmp .lower (.var .local (ofString "a")) (.var .local (ofString "b")))
            (.return (.rstruct [.const 0#64, .var .local (ofString "a")])) .skip) =
          evaluateHOLFiniteState ent (.return (.rstruct [.const 0#64, .var .local (ofString "a")])) := by
        simp [evaluateHOLFiniteState_ite, evalHOLExact, ha, hb,
          Compiler.Encoders.Asm.wordCmpHOL, hlt_bv]
      rw [hite2, evaluateHOLFiniteState_return] at hret
      simp [evalHOLExact, evalListHOLExact, ha, shapeOfHOLExact] at hret
      exact ⟨hb_pos, 0#64, aw, hret.symm, by simp, halb, Nat.zero_le _⟩
    · have hnotlt_bv : ¬ aw < bw := by rw [BitVec.lt_def]; omega
      have hite2 : evaluateHOLFiniteState ent
          (.ite (.cmp .lower (.var .local (ofString "a")) (.var .local (ofString "b")))
            (.return (.rstruct [.const 0#64, .var .local (ofString "a")])) .skip) =
          (none, ent) := by
        simp [evaluateHOLFiniteState_ite, evalHOLExact, ha, hb,
          Compiler.Encoders.Asm.wordCmpHOL, hnotlt_bv, evaluateHOLFiniteState_skip]
      rw [hite2] at hret; dsimp only at hret
      -- Declarations q := 0, r := 0, i := 64
      rw [evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
      simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hret
      set s1 := setVarHOLFinite (ofString "q") (.val (.word 0#64)) ent
      change (evaluateHOLFiniteState s1 _).1 = some (.returned rv) at hret
      rw [evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
      simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hret
      set s2 := setVarHOLFinite (ofString "r") (.val (.word 0#64)) s1
      change (evaluateHOLFiniteState s2 _).1 = some (.returned rv) at hret
      rw [evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
      simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hret
      set s3 := setVarHOLFinite (ofString "i") (.val (.word 64#64)) s2
      change (evaluateHOLFiniteState s3 _).1 = some (.returned rv) at hret
      rw [evaluateHOLFiniteState_seq_line780] at hret
      rcases hw : evaluateHOLFiniteState s3 udivmodLoop with ⟨wres, wpost⟩
      have hw' : evaluateHOLFiniteState s3
          (.while (.cmp .less (.const 0#64) (.var .local (ofString "i"))) udivmodLoopBody) = (wres, wpost) := hw
      rw [hw'] at hret; dsimp only at hret
      cases wres with
      | some wr =>
        dsimp only at hret; injection hret with hret; subst hret
        exact False.elim (udivmodLoop_not_returned s3.clock s3 rv le_rfl (by rw [hw]))
      | none =>
        have ha3 : s3.locals.lookup (ofString "a") = some (.val (.word aw)) := by
          simp [s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ha,
            show ofString "i" ≠ ofString "a" by decide,
            show ofString "r" ≠ ofString "a" by decide,
            show ofString "q" ≠ ofString "a" by decide]
        have hb3 : s3.locals.lookup (ofString "b") = some (.val (.word bw)) := by
          simp [s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hb,
            show ofString "i" ≠ ofString "b" by decide,
            show ofString "r" ≠ ofString "b" by decide,
            show ofString "q" ≠ ofString "b" by decide]
        have hi3 : s3.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 64))) := by
          simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hq3 : s3.locals.lookup (ofString "q") = some (.val (.word 0#64)) := by
          simp [s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "q" by decide,
            show ofString "r" ≠ ofString "q" by decide]
        have hr3 : s3.locals.lookup (ofString "r") = some (.val (.word 0#64)) := by
          simp [s3, s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "r" by decide]
        have hinv3 : (0#64).toNat * bw.toNat + (0#64).toNat * 2 ^ 64 =
            aw.toNat / 2 ^ 64 * 2 ^ 64 ∧ (0#64).toNat < bw.toNat ∧ (0#64).toNat % 2 ^ 64 = 0 := by
          have hz0 : (0#64).toNat = 0 := rfl
          have hd0 : aw.toNat / 2 ^ 64 = 0 := Nat.div_eq_of_lt aw.isLt
          rw [hz0, hd0]
          exact ⟨by simp, hb_pos, by simp⟩
        obtain ⟨qf, rf, hqf, hrf, hmul, hrflt⟩ :=
          udivmod_loop_inv aw bw hb_pos 64 s3 0#64 0#64 le_rfl ha3 hb3 hi3 hq3 hr3 hinv3 (by rw [hw])
        rw [hw] at hqf hrf; dsimp only at hqf hrf
        dsimp only at hret
        rw [evaluateHOLFiniteState_return] at hret
        simp [evalHOLExact, evalListHOLExact, hqf, hrf, shapeOfHOLExact] at hret
        have hqle : qf.toNat ≤ aw.toNat := by
          have : qf.toNat * 1 ≤ qf.toNat * bw.toNat := Nat.mul_le_mul_left _ hb_pos
          omega
        exact ⟨hb_pos, qf, rf, hret.symm, hmul, hrflt, hqle⟩

theorem lookup_host_input_byte :
    originalRuntimeCode.lookup (ofString "host_input_byte") =
      some ([(ofString "i", .one)], sourceFnBody Guest.Software.guestFn_host_input_byte, .one) :=
  lookup_of_guestAst_getElem 197 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_host_input_byte) rfl

theorem lookup_host_input_le32 :
    originalRuntimeCode.lookup (ofString "host_input_le32") =
      some ([(ofString "i", .one)], sourceFnBody Guest.Software.guestFn_host_input_le32, .one) :=
  lookup_of_guestAst_getElem 198 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_host_input_le32) rfl

theorem worldEff_host_input_byte_body {F : Type}
    {s entry : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (heff : WorldEff s entry Rl B gw)
    (hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_host_input_byte)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_host_input_byte)).1) :
    WorldEff s (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_host_input_byte)).2 Rl B gw := by
  dsimp only [Guest.Software.guestFn_host_input_byte, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hcr ⊢
  refine worldEff_dec heff _ _ _ hnt hcr (fun val _ _ hnt1 hcr1 => ?_)
  refine worldEff_seq hnt1 hcr1
    (fun _ _ => worldEff_shMemLoad_local (heff.locals_clock _ _) _ _ _)
    (fun mid _ heff_mid _ _ => worldEff_return heff_mid _)

theorem worldEff_host_input_le32_body {F : Type}
    {s entry : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (heff : WorldEff s entry Rl B gw)
    (hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_host_input_le32)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_host_input_le32)).1) :
    WorldEff s (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_host_input_le32)).2 Rl B gw := by
  dsimp only [Guest.Software.guestFn_host_input_le32, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hcr ⊢
  refine worldEff_decCall_eff heff _ _ _ _ _ _ _ lookup_host_input_byte
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_byte_body (heff.locals_clock callee (entry.clock - 1)) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ _ _ _ _ _ _ heff1 hnt1 hcr1 => ?_) hnt hcr
  refine worldEff_decCall_eff (heff1.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_byte
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_byte_body (heff1.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ _ _ _ _ _ _ heff2 hnt2 hcr2 => ?_) hnt1 hcr1
  refine worldEff_decCall_eff (heff2.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_byte
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_byte_body (heff2.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ _ _ _ _ _ _ heff3 hnt3 hcr3 => ?_) hnt2 hcr2
  refine worldEff_decCall_eff (heff3.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_byte
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_byte_body (heff3.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ _ _ _ _ _ _ heff4 _ _ => worldEff_return (heff4.locals_clock _ _) _) hnt3 hcr3

theorem readOnlyProg_call_trap_with (args : List (ExpHOL 64)) :
    R13.ReadOnlyProg (.call (some (none, none)) (ofString "trap_with") args) := by
  intro F s hcode _ hnt hfr
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rfl
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "trap_with") values with _ | ⟨body', callee, ret'⟩
    · rfl
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "trap_with")
          [(ofString "code", .one)] (sourceFnBody Guest.Software.guestFn_trap_with) body'
          .one ret' values callee (by rw [hcode]; exact lookup_trap_with) hl
        subst hsame
        have hout := evaluate_trap_with_body_outcomes (callEntryStateHOLFinite s callee)
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, post⟩
        simp only [hrun] at hout hnt hfr ⊢
        obtain ⟨hnone, hret, hexn⟩ := hout
        cases res with
        | none => exact absurd rfl hnone
        | some r =>
          cases r with
          | returned v => exact absurd rfl (hret v)
          | exception eid v =>
            dsimp only at hfr
            rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨e', v', h, hne⟩⟩
            · simp at h
            · simp at h
            · simp at h
            · simp at h
            · injection h with h'
              injection h' with he _
              subst he
              exact absurd rfl (hexn eid v hne)
          | timeOut => simp at hnt
          | _ => rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

theorem ro_udivmod : InitECandidate.Solver.Wave8GuestInv.ReadOnlyFn (ofString "udivmod") := by
  refine R13.readOnlyFn_of_guestAst 33 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_udivmod rfl ?_
  dsimp only [Guest.Software.guestFn_udivmod, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, Option.map]
  exact R13.ReadOnlyProg.seq
    (R13.ReadOnlyProg.ite _ (readOnlyProg_call_trap_with _) R13.ReadOnlyProg.skip)
    (R13.ReadOnlyProg.seq
      (R13.ReadOnlyProg.ite _ (R13.ReadOnlyProg.ret _) R13.ReadOnlyProg.skip)
      (R13.ReadOnlyProg.dec _ _ _
        (R13.ReadOnlyProg.dec _ _ _
          (R13.ReadOnlyProg.dec _ _ _
            (R13.ReadOnlyProg.seq
              (R13.ReadOnlyProg.while_loop _
                (R13.ReadOnlyProg.seq
                  (R13.ReadOnlyProg.assign_local _ _)
                  (R13.ReadOnlyProg.seq
                    (R13.ReadOnlyProg.assign_local _ _)
                    (R13.ReadOnlyProg.ite _
                      (R13.ReadOnlyProg.seq
                        (R13.ReadOnlyProg.assign_local _ _)
                        (R13.ReadOnlyProg.assign_local _ _))
                      R13.ReadOnlyProg.skip))))
              (R13.ReadOnlyProg.ret _))))))

theorem ro_host_ssz_fail_local : InitECandidate.Solver.Wave8GuestInv.ReadOnlyFn (ofString "ssz_fail") := by
  refine R13.readOnlyFn_of_guestAst 196 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_ssz_fail rfl ?_
  dsimp only [Guest.Software.guestFn_ssz_fail, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact R13.ReadOnlyProg.seq (R13.ReadOnlyProg.raise _ _) (R13.ReadOnlyProg.ret _)

theorem ro_ssz_fixed_list_count : InitECandidate.Solver.Wave8GuestInv.ReadOnlyFn (ofString "ssz_fixed_list_count") := by
  refine R13.readOnlyFn_of_guestAst 203 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_ssz_fixed_list_count rfl ?_
  dsimp only [Guest.Software.guestFn_ssz_fixed_list_count, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact R13.ReadOnlyProg.decCall ro_udivmod _ _ _
    (R13.ReadOnlyProg.seq
      (R13.ReadOnlyProg.ite _ (R13.ReadOnlyProg.call0 ro_host_ssz_fail_local _) R13.ReadOnlyProg.skip)
      (R13.ReadOnlyProg.seq
        (R13.ReadOnlyProg.ite _ (R13.ReadOnlyProg.call0 ro_host_ssz_fail_local _) R13.ReadOnlyProg.skip)
        (R13.ReadOnlyProg.ret _)))

theorem evalHOLExact_op_is_word {F : Type} (st : PanSemStateFiniteExact 64 F)
    (bop : BinOp) (es : List (ExpHOL 64)) (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) (.op bop es) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  simp only [evalHOLExact] at hv
  rcases hvs : @evalListHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) es with _ | vs
  · rw [hvs] at hv; simp at hv
  · rw [hvs] at hv; dsimp only at hv
    split at hv <;> simp at hv
    obtain ⟨w, _, hw⟩ := hv
    exact ⟨w, hw.symm⟩

theorem evalHOLExact_rfield_comb2_is_word {F : Type} (st : PanSemStateFiniteExact 64 F)
    (idx : Nat) (re : ExpHOL 64) (w0 w1 : BitVec 64) (v : ValueHOL 64)
    (hre : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) re =
      some (.rStruct [.val (.word w0), .val (.word w1)]))
    (hv : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) (.rfield idx re) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  simp only [evalHOLExact, hre] at hv
  cases idx with
  | zero => simp at hv; exact ⟨w0, hv.symm⟩
  | succ j =>
    cases j with
    | zero => simp at hv; exact ⟨w1, hv.symm⟩
    | succ k => simp at hv

abbrev dhiOffsRegions {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  [(globN s "ssz_offs", if globN s "ssz_offs" = 0 then 0 else 64)]

abbrev dhiGw : List String := ["heap_ptr"]

theorem dhi_no_gb : ∀ gs ∈ globalBuffers, ofString gs.1 ∉ dhiGw.map ofString := by decide
theorem dhi_core_out : ∀ g ∈ coreWorldGlobals, ofString g ∉ dhiGw.map ofString := by decide

theorem ssz_fail_noret {F : Type} (st : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState st (sourceFnBody Guest.Software.guestFn_ssz_fail)).1 ≠ some (.returned v) := by
  have hb : sourceFnBody Guest.Software.guestFn_ssz_fail =
      .seq (.raise (ofString "SszErr") (.var .local (ofString "code"))) (.return (.const 0)) := rfl
  have hraise : (evaluateHOLFiniteState st (.raise (ofString "SszErr") (.var .local (ofString "code")) :
        ProgHOL 64)).1 ≠ some (.returned v) ∧
      (evaluateHOLFiniteState st (.raise (ofString "SszErr") (.var .local (ofString "code")) :
        ProgHOL 64)).1 ≠ none := by
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  rw [hb, evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState st (.raise (ofString "SszErr") (.var .local (ofString "code")) : ProgHOL 64) with ⟨r1, _⟩
  rw [hr] at hraise
  cases r1 with
  | none => exact absurd rfl hraise.2
  | some _ => exact hraise.1

theorem ite_ssz_fail_keeps {F : Type}
    (cur mid : PanSemStateFiniteExact 64 F)
    (hc : cur.code = originalRuntimeCode)
    (cond : ExpHOL 64) (codeExp : ExpHOL 64)
    (hrun : evaluateHOLFiniteState cur
      (.ite cond (.call (some (none, none)) (ofString "ssz_fail") [codeExp]) .skip) = (none, mid)) :
    mid = cur ∧
    @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) cond =
      some (.val (.word 0)) := by
  have hlook_sf : originalRuntimeCode.lookup (ofString "ssz_fail") =
      some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_ssz_fail, .one) :=
    lookup_of_guestAst_getElem 196 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_ssz_fail) rfl
  rw [evaluateHOLFiniteState_ite] at hrun
  rcases hcv : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) cond with _ | cv
  · rw [hcv] at hrun; simp at hrun
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> (rw [hcv] at hrun; try simp at hrun)
    by_cases hw0 : cw = 0#64
    · subst hw0; rw [if_pos rfl] at hrun
      injection hrun with _ hm; exact ⟨hm.symm, rfl⟩
    · rw [if_neg hw0] at hrun
      exfalso
      rw [evaluateHOLFiniteState_call] at hrun
      rcases ha : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [codeExp] with _ | fvs
      · rw [ha] at hrun; simp at hrun
      · rw [ha] at hrun; dsimp only at hrun
        rcases hl : lookupCodeHOLFinite cur.code.lookup (ofString "ssz_fail") fvs with _ | ⟨fb, fc, fr⟩
        · rw [hl] at hrun; simp at hrun
        · rw [hl] at hrun; dsimp only at hrun
          have hfb := lookupCodeHOLFinite_installed_body cur.code.lookup _ _ _ fb _ fr fvs fc
            (by rw [hc]; exact hlook_sf) hl
          subst hfb
          by_cases hz : cur.clock = 0
          · rw [if_pos hz] at hrun; simp at hrun
          · rw [if_neg hz] at hrun
            have hnr := ssz_fail_noret (callEntryStateHOLFinite cur fc)
            rcases hfrun : evaluateHOLFiniteState (callEntryStateHOLFinite cur fc)
                (sourceFnBody Guest.Software.guestFn_ssz_fail) with ⟨fr_r, _⟩
            rw [hfrun] at hrun hnr
            cases fr_r with
            | none => simp at hrun
            | some fr1 =>
              cases fr1 with
              | returned fv => exact hnr fv rfl
              | _ => simp at hrun

theorem ite_trap_with_keeps {F : Type}
    (cur mid : PanSemStateFiniteExact 64 F)
    (hc : cur.code = originalRuntimeCode)
    (cond : ExpHOL 64) (codeExp : ExpHOL 64)
    (hrun : evaluateHOLFiniteState cur
      (.ite cond (.call (some (none, none)) (ofString "trap_with") [codeExp]) .skip) = (none, mid)) :
    mid = cur ∧
    @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) cond =
      some (.val (.word 0)) := by
  rw [evaluateHOLFiniteState_ite] at hrun
  rcases hcv : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) cond with _ | cv
  · rw [hcv] at hrun; simp at hrun
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> (rw [hcv] at hrun; try simp at hrun)
    by_cases hw0 : cw = 0#64
    · subst hw0; rw [if_pos rfl] at hrun
      injection hrun with _ hm; exact ⟨hm.symm, rfl⟩
    · rw [if_neg hw0] at hrun
      exfalso
      rw [evaluateHOLFiniteState_call] at hrun
      rcases ha : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [codeExp] with _ | fvs
      · rw [ha] at hrun; simp at hrun
      · rw [ha] at hrun; dsimp only at hrun
        rcases hl : lookupCodeHOLFinite cur.code.lookup (ofString "trap_with") fvs with _ | ⟨fb, fc, fr⟩
        · rw [hl] at hrun; simp at hrun
        · rw [hl] at hrun; dsimp only at hrun
          have hfb := lookupCodeHOLFinite_installed_body cur.code.lookup _ _ _ fb _ fr fvs fc
            (by rw [hc]; exact lookup_trap_with) hl
          subst hfb
          by_cases hz : cur.clock = 0
          · rw [if_pos hz] at hrun; simp at hrun
          · rw [if_neg hz] at hrun
            have hout := evaluate_trap_with_body_outcomes (callEntryStateHOLFinite cur fc)
            rcases hfrun : evaluateHOLFiniteState (callEntryStateHOLFinite cur fc)
                (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨fr_r, _⟩
            rw [hfrun] at hrun hout
            cases fr_r with
            | none => exact hout.1 rfl
            | some fr1 =>
              cases fr1 with
              | returned fv => exact hout.2.1 fv rfl
              | _ => simp at hrun

theorem worldEff_call_trap_with {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (heff : WorldEff s cur Rl B gw) (args : List (ExpHOL 64))
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "trap_with") args)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "trap_with") args)).1) :
    WorldEff s (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "trap_with") args)).2 Rl B gw :=
  heff.of_readOnly (readOnlyProg_call_trap_with args cur heff.code heff.arena.1 hnt hcr)

theorem ssz_offs_allocated {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hWOK : WorldOK s) :
    globN s "ssz_offs" = 0 ∨
    (sourceBase ≤ globN s "ssz_offs" ∧ globN s "ssz_offs" + 64 ≤ heapEnd ∧
      globN s "ssz_offs" % 8 = 0 ∧ WordsOK s (globN s "ssz_offs", 64)) := by
  obtain ⟨hAs, S, hWS⟩ := hWOK
  obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with s S).1 hWS
  have hmem : bufferRegion s ("ssz_offs", 64) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.2 ⟨("ssz_offs", 64), by decide, rfl⟩
  rcases hWT.2.2.1.1 _ hmem with hz | ⟨hal, hwok⟩
  · by_cases hg0 : globN s "ssz_offs" = 0
    · exact Or.inl hg0
    · simp [bufferRegion, hg0] at hz
  · by_cases hg0 : globN s "ssz_offs" = 0
    · exact Or.inl hg0
    · simp only [bufferRegion, hg0, ↓reduceIte] at hal hwok
      have hal_bounds : sourceBase ≤ globN s "ssz_offs" ∧ globN s "ssz_offs" + 64 ≤ heapEnd := by
        rcases hal with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have := hAs.2.1; have := hAs.2.2.1; have : heapLimit ≤ heapEnd := by decide
          omega
        · have := hAs.2.2.2.1; have := hAs.2.2.2.2.1; have := hAs.2.2.2.2.2.1
          have : sourceBase ≤ scratchStart := by decide
          have : scratchEnd ≤ heapEnd := by decide
          omega
      exact Or.inr ⟨hal_bounds.1, hal_bounds.2, hwok.1, hwok⟩

theorem worldEff_store_ssz_offs_const {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hWOK : WorldOK s)
    (heff : WorldEff s cur (dhiOffsRegions s) B dhiGw)
    (off : Nat) (hoff : off + 8 ≤ 64)
    (dstExp valExp : ExpHOL 64)
    (hdst : dstExp = .var .global (ofString "ssz_offs") ∧ off = 0 ∨
      dstExp = .op .add [.var .global (ofString "ssz_offs"), .const (BitVec.ofNat 64 off)])
    (hval_one : ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp =
      some v → ∃ w : BitVec 64, v = .val (.word w)) :
    WorldEff s (evaluateHOLFiniteState cur (.store dstExp valExp)).2 (dhiOffsRegions s) B dhiGw := by
  refine worldEff_store_word heff dstExp valExp hval_one (fun x hx hdom => ?_)
  have hg_kept := heff.gw_kept (ofString "ssz_offs") (by decide)
  obtain ⟨sw, hsw_s⟩ := hWOK.1.2.2.2.2.2.2.2.2.2 "ssz_offs" (by decide)
  unfold GlobalWord at hsw_s
  have hsw_cur : cur.globals.lookup (ofString "ssz_offs") = some (.val (.word sw)) :=
    hg_kept.symm.trans hsw_s
  have hglob : globN s "ssz_offs" = sw.toNat := by simp [globN, hsw_s]
  have hx_eq : x = sw + BitVec.ofNat 64 off := by
    rcases hdst with ⟨rfl, rfl⟩ | rfl
    · simp [evalHOLExact, toExact, hsw_cur] at hx
      simpa using hx.symm
    · simp [evalHOLExact, evalListHOLExact, toExact, hsw_cur, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
      exact hx.symm
  rw [heff.memaddrs, hWOK.1.1.memaddrs, ordinaryDomain_iff] at hdom
  rcases ssz_offs_allocated hWOK with hg0 | ⟨hlo, hhi, _, _⟩
  · have hsw0 : sw = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hsw0 hx_eq
    have hsb : 64 < sourceBase := by decide
    have h1 : (0#64 + BitVec.ofNat 64 off).toNat = off := by
      simp [BitVec.toNat_ofNat]; omega
    omega
  · have hhe : heapEnd < 2 ^ 64 := by decide
    have hsb : 0 < sourceBase := by decide
    have hg_ne0 : globN s "ssz_offs" ≠ 0 := by omega
    have hx_nat : x.toNat = globN s "ssz_offs" + off := by
      rw [hx_eq, BitVec.toNat_add_of_lt]
      · simp [hglob, BitVec.toNat_ofNat]; omega
      · simp [BitVec.toNat_ofNat]; omega
    exact Or.inl ⟨(globN s "ssz_offs", if globN s "ssz_offs" = 0 then 0 else 64),
      List.mem_singleton.2 rfl, by simp [hg_ne0]; omega, by simp [hg_ne0]; omega⟩

theorem worldEff_store_ssz_offs_dyn {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hWOK : WorldOK s)
    (heff : WorldEff s cur (dhiOffsRegions s) B dhiGw)
    (offExp valExp : ExpHOL 64)
    (offw : BitVec 64)
    (hoff_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) offExp =
      some (.val (.word offw)))
    (hoff_le : offw.toNat + 8 ≤ 64)
    (hval_one : ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp =
      some v → ∃ w : BitVec 64, v = .val (.word w)) :
    WorldEff s (evaluateHOLFiniteState cur (.store (.op .add [.var .global (ofString "ssz_offs"), offExp]) valExp)).2
      (dhiOffsRegions s) B dhiGw := by
  refine worldEff_store_word heff _ valExp hval_one (fun x hx hdom => ?_)
  have hg_kept := heff.gw_kept (ofString "ssz_offs") (by decide)
  obtain ⟨sw, hsw_s⟩ := hWOK.1.2.2.2.2.2.2.2.2.2 "ssz_offs" (by decide)
  unfold GlobalWord at hsw_s
  have hsw_cur : cur.globals.lookup (ofString "ssz_offs") = some (.val (.word sw)) :=
    hg_kept.symm.trans hsw_s
  have hglob : globN s "ssz_offs" = sw.toNat := by simp [globN, hsw_s]
  have hx_eq : x = sw + offw := by
    simp [evalHOLExact, evalListHOLExact, toExact, hsw_cur, hoff_ev, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
    exact hx.symm
  rw [heff.memaddrs, hWOK.1.1.memaddrs, ordinaryDomain_iff] at hdom
  rcases ssz_offs_allocated hWOK with hg0 | ⟨hlo, hhi, _, _⟩
  · have hsw0 : sw = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hsw0 hx_eq
    have hsb : 64 < sourceBase := by decide
    have h1 : (0#64 + offw).toNat = offw.toNat := by simp
    omega
  · have hhe : heapEnd < 2 ^ 64 := by decide
    have hsb : 0 < sourceBase := by decide
    have hg_ne0 : globN s "ssz_offs" ≠ 0 := by omega
    have hx_nat : x.toNat = globN s "ssz_offs" + offw.toNat := by
      rw [hx_eq, BitVec.toNat_add_of_lt]
      · omega
      · omega
    exact Or.inl ⟨(globN s "ssz_offs", if globN s "ssz_offs" = 0 then 0 else 64),
      List.mem_singleton.2 rfl, by simp [hg_ne0]; omega, by simp [hg_ne0]; omega⟩

def noLocalAssign (x : MlS) : ProgHOL 64 → Bool
  | .dec _ _ _ body => noLocalAssign x body
  | .seq first second => noLocalAssign x first && noLocalAssign x second
  | .ite _ yes no => noLocalAssign x yes && noLocalAssign x no
  | .while _ body => noLocalAssign x body
  | .assign .global _ _ => true
  | .assign .local nm _ => decide (x ≠ nm)
  | .store _ _ | .storeByte _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .decCall _ _ _ _ continuation => noLocalAssign x continuation
  | .call none _ _ => true
  | .call (some (none, none)) _ _ => true
  | .call (some (some (.global, _), none)) _ _ => true
  | .call (some (some (.local, nm), none)) _ _ => decide (x ≠ nm)
  | .call (some (none, some (_, hv, handler))) _ _ => decide (x ≠ hv) && noLocalAssign x handler
  | .call (some (some (.global, _), some (_, hv, handler))) _ _ => decide (x ≠ hv) && noLocalAssign x handler
  | .call (some (some (.local, nm), some (_, hv, handler))) _ _ =>
    decide (x ≠ nm) && decide (x ≠ hv) && noLocalAssign x handler
  | .shMemLoad _ .local nm _ => decide (x ≠ nm)
  | _ => false

theorem evaluate_keepLocal {F : Type} (x : MlS)
    (program : ProgHOL 64) (supported : noLocalAssign x program = true)
    (state : PanSemStateFiniteExact 64 F)
    (hflow : Flowing (evaluateHOLFiniteState state program).1) :
    (evaluateHOLFiniteState state program).2.locals.lookup x = state.locals.lookup x := by
  cases shape : program with
  | skip => subst shape; rw [evaluateHOLFiniteState_skip]
  | «break» => subst shape; rw [evaluateHOLFiniteState_break]
  | «continue» => subst shape; rw [evaluateHOLFiniteState_continue]
  | annot _ _ => subst shape; rw [evaluateHOLFiniteState_annot]
  | raise _ _ =>
    subst shape; revert hflow; rw [evaluateHOLFiniteState_raise]
    split <;> [ (dsimp only; split <;> simp [Flowing]); simp [Flowing] ]
  | «return» _ =>
    subst shape; revert hflow; rw [evaluateHOLFiniteState_return]
    split <;> [ simp [Flowing]; (split <;> simp [Flowing]) ]
  | store _ _ =>
    subst shape; revert hflow; rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> [ (intro _; rfl); simp [Flowing] ]
      · simp [Flowing]
    · simp [Flowing]
  | storeByte _ _ =>
    subst shape; revert hflow; rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> [ (intro _; rfl); simp [Flowing] ]
      · simp [Flowing]
    · simp [Flowing]
  | assign kind name _ =>
    have hsup := supported; rw [shape] at hsup
    subst shape; revert hflow; rw [evaluateHOLFiniteState_assign]
    split
    · simp [Flowing]
    · split
      · intro _
        cases kind with
        | global => simp [setKvarHOLFinite, setGlobalHOLFinite]
        | «local» =>
          have hxn : x ≠ name := of_decide_eq_true hsup
          simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxn]
      · simp [Flowing]
  | dec name _ _ body =>
    have child : noLocalAssign x body = true := by simpa only [shape, noLocalAssign] using supported
    subst shape; revert hflow; rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · simp [Flowing]
    · split
      · rename_i v _ _
        intro hflow
        by_cases hxn : x = name
        · subst hxn; dsimp only; rw [resVarEq_lookup_local, if_pos rfl]
        · have hm := evaluate_keepLocal x body child (setVarHOLFinite name v state) hflow
          dsimp only; rw [resVarEq_lookup_local, if_neg hxn, hm]
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxn]
      · simp [Flowing]
  | seq first second =>
    have children : noLocalAssign x first = true ∧ noLocalAssign x second = true := by
      simpa only [shape, noLocalAssign, Bool.and_eq_true] using supported
    subst shape
    have remaining := evaluateHOLFiniteState_clock_le state first
    revert hflow; rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at remaining; dsimp only at remaining
      cases result with
      | none =>
        intro hflow
        have mclock : middle.clock ≤ state.clock := remaining
        have hm := evaluate_keepLocal x first children.1 state (by rw [firstRun]; exact Or.inl rfl)
        rw [firstRun] at hm
        exact (evaluate_keepLocal x second children.2 middle hflow).trans hm
      | some _ =>
        intro hflow
        have hm := evaluate_keepLocal x first children.1 state (by rw [firstRun]; exact hflow)
        rw [firstRun] at hm; exact hm
  | ite _ yes no =>
    have children : noLocalAssign x yes = true ∧ noLocalAssign x no = true := by
      simpa only [shape, noLocalAssign, Bool.and_eq_true] using supported
    subst shape; revert hflow; rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_keepLocal x no children.2 state
      · exact evaluate_keepLocal x yes children.1 state
    · simp [Flowing]
  | «while» condition body =>
    have child : noLocalAssign x body = true := by simpa only [shape, noLocalAssign] using supported
    subst shape; revert hflow; rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp [Flowing]
        · dsimp only; rw [fixClockHOLFinite_evaluateState]
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at remaining; dsimp only at remaining
            have small : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining; omega
            have hmid (hf : Flowing result) : middle.locals.lookup x = state.locals.lookup x := by
              have := evaluate_keepLocal x body child (decClockHOLFinite state) (by rw [bodyRun]; exact hf)
              rw [bodyRun] at this; exact this
            cases result with
            | none =>
              intro hflow
              exact (evaluate_keepLocal x (.while condition body) (by simpa [noLocalAssign] using child) middle hflow).trans (hmid (Or.inl rfl))
            | some result =>
              cases result with
              | «continue» =>
                intro hflow
                exact (evaluate_keepLocal x (.while condition body) (by simpa [noLocalAssign] using child) middle hflow).trans (hmid (Or.inr (Or.inr rfl)))
              | «break» => intro _; exact hmid (Or.inr (Or.inl rfl))
              | _ => simp [Flowing]
      · intro _; rfl
    · simp [Flowing]
  | decCall name _ _ _ continuation =>
    have child : noLocalAssign x continuation = true := by simpa only [shape, noLocalAssign] using supported
    subst shape; revert hflow; rw [evaluateHOLFiniteState_decCall_total]
    split
    · simp [Flowing]
    · split
      · simp [Flowing]
      · rename_i body callee _ _
        split
        · simp [Flowing]
        · dsimp only
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at cl ⊢
          obtain ⟨r, st⟩ := out
          dsimp only at cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          rcases r with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only [fixClockHOLFinite])
          all_goals (try simp [Flowing])
          split
          · intro hflow
            have small : (if state.clock - 1 < st.clock then state.clock - 1 else st.clock) < state.clock := by
              split <;> omega
            by_cases hxn : x = name
            · subst hxn; dsimp only; rw [resVarEq_lookup_local, if_pos rfl]
            · have hm := evaluate_keepLocal x continuation child _ hflow
              dsimp only; rw [resVarEq_lookup_local, if_neg hxn, hm]
              simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxn]
          · intro h; rcases h with h | h | h <;> simp at h
  | call info _ _ =>
    have hsup := supported; rw [shape] at hsup
    subst shape; revert hflow; rw [evaluateHOLFiniteState_call]
    split
    · simp [Flowing]
    · split
      · simp [Flowing]
      · rename_i body callee _ _
        split
        · simp [Flowing]
        · have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at cl ⊢
          obtain ⟨r, st⟩ := out
          dsimp only at cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have small : st.clock < state.clock := by omega
          have hnf : ∀ (o : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F),
              o ≠ none → o ≠ some .break → o ≠ some .continue → Flowing (o, t).1 →
              (o, t).2.locals.lookup x = state.locals.lookup x := by
            intro o _ h1 h2 h3 hf; rcases hf with hf | hf | hf <;> [exact absurd hf h1; exact absurd hf h2; exact absurd hf h3]
          cases r with
          | none => exact hnf _ _ (by simp) (by simp) (by simp)
          | some r =>
            cases r with
            | returned v =>
              dsimp only; split
              · rcases info with _ | ⟨_ | ⟨kind, nm⟩, hnd⟩
                · exact hnf _ _ (by simp) (by simp) (by simp)
                · intro _; rfl
                · dsimp only; split
                  · intro _
                    cases kind with
                    | global => simp [setKvarHOLFinite, setGlobalHOLFinite]
                    | «local» =>
                      have hxn : x ≠ nm := by
                        rcases hnd with _ | ⟨_, _, _⟩
                        · simpa [noLocalAssign] using hsup
                        · simp [noLocalAssign] at hsup; exact hsup.1.1
                      simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxn]
                  · exact hnf _ _ (by simp) (by simp) (by simp)
              · exact hnf _ _ (by simp) (by simp) (by simp)
            | exception _ v =>
              dsimp only
              rcases info with _ | ⟨dest, _ | ⟨_, hv, hp⟩⟩
              · exact hnf _ _ (by simp) (by simp) (by simp)
              · exact hnf _ _ (by simp) (by simp) (by simp)
              · have hxhv_hp : x ≠ hv ∧ noLocalAssign x hp = true := by
                  rcases dest with _ | ⟨kd, _⟩
                  · simpa [noLocalAssign] using hsup
                  · cases kd
                    · simp [noLocalAssign] at hsup; exact ⟨hsup.1.2, hsup.2⟩
                    · simpa [noLocalAssign] using hsup
                dsimp only; split
                · split
                  · split
                    · intro hflow
                      have hm := evaluate_keepLocal x hp hxhv_hp.2 _ hflow
                      rw [hm]
                      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxhv_hp.1]
                    · exact hnf _ _ (by simp) (by simp) (by simp)
                  · exact hnf _ _ (by simp) (by simp) (by simp)
                · exact hnf _ _ (by simp) (by simp) (by simp)
            | _ => exact hnf _ _ (by simp) (by simp) (by simp)
  | shMemLoad op kind name addr =>
    cases kind with
    | global => simp [shape, noLocalAssign] at supported
    | «local» =>
      have hxn : x ≠ name := by simpa [shape, noLocalAssign] using supported
      subst shape
      rcases h : evaluateHOLFiniteState state (.shMemLoad op .local name addr) with ⟨r, post⟩
      simp only [h] at hflow ⊢
      cases r with
      | none =>
        obtain ⟨val, hpost⟩ := shMemLoad_local_none_inv state op name addr h
        rw [hpost]
        simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxn]
      | some r1 =>
        exfalso
        have hr1 : r1 = .break ∨ r1 = .continue := by
          rcases hflow with h0 | h0 | h0
          · cases h0
          · injection h0 with h0'; exact Or.inl h0'
          · injection h0 with h0'; exact Or.inr h0'
        classical
        rw [evaluateHOLFiniteState_shMemLoad_source] at h
        revert h; split
        · split
          · unfold shMemLoadHOLFiniteExact; dsimp only
            split <;> split <;> (try split) <;>
              (intro h; rcases hr1 with rfl | rfl <;> simp at h)
          · intro h; rcases hr1 with rfl | rfl <;> simp at h
        · intro h; rcases hr1 with rfl | rfl <;> simp at h
  | _ => simp [shape, noLocalAssign] at supported
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply InitECandidate.Solver.GuestGlobalKeep.lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite, ProgHOL.seq.sizeOf_spec,
      ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec, ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, true_and]
    first | exact Or.inl small | omega

theorem lookup_precheck_host_ssz_header :
    originalRuntimeCode.lookup (ofString "precheck_host_ssz_header") =
      some ([], sourceFnBody Guest.Software.guestFn_precheck_host_ssz_header, .one) :=
  lookup_of_guestAst_getElem 199 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_precheck_host_ssz_header) rfl

theorem lookup_ssz_fail_dhi :
    originalRuntimeCode.lookup (ofString "ssz_fail") =
      some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_ssz_fail, .one) :=
  lookup_of_guestAst_getElem 196 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ssz_fail) rfl

theorem lookup_ssz_check_offsets_dhi :
    originalRuntimeCode.lookup (ofString "ssz_check_offsets") =
      some ([(ofString "offs", .one), (ofString "n", .one), (ofString "fixed", .one),
        (ofString "len", .one)], sourceFnBody Guest.Software.guestFn_ssz_check_offsets, .one) :=
  lookup_of_guestAst_getElem 201 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ssz_check_offsets) rfl

theorem ro_ssz_check_offsets_local :
    InitECandidate.Solver.Wave8GuestInv.ReadOnlyFn (ofString "ssz_check_offsets") := by
  refine R13.readOnlyFn_of_guestAst 201 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_ssz_check_offsets rfl ?_
  dsimp only [Guest.Software.guestFn_ssz_check_offsets, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  repeat first
    | apply R13.ReadOnlyProg.seq
    | apply R13.ReadOnlyProg.ite
    | apply R13.ReadOnlyProg.dec
    | apply R13.ReadOnlyProg.while_loop
    | exact R13.ReadOnlyProg.call0 ro_host_ssz_fail_local _
    | exact R13.ReadOnlyProg.assign_local _ _
    | exact R13.ReadOnlyProg.ret _
    | exact R13.ReadOnlyProg.skip

theorem val_word_of_shapeEq_one {v : ValueHOL 64}
    (hsh : shapeEqHOL (shapeOfHOLExact v) .one = true) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  rcases v with ⟨⟨w⟩⟩ | _ | _
  · exact ⟨w, rfl⟩
  · simp [shapeOfHOLExact, shapeEqHOL] at hsh
  · simp [shapeOfHOLExact, shapeEqHOL] at hsh

theorem store_keeps_locals {F : Type}
    (st mid : PanSemStateFiniteExact 64 F) (dst val : ExpHOL 64)
    (h : evaluateHOLFiniteState st (.store dst val) = (none, mid)) :
    mid.locals = st.locals := by
  rw [evaluateHOLFiniteState_store] at h
  rcases hdv : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) dst with _ | dv
  · rw [hdv] at h; simp at h
  · rw [hdv] at h
    rcases dv with ⟨⟨dw⟩⟩ | _ | _ <;> try simp at h
    rcases hvv : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) val with _ | vv
    · rw [hvv] at h; simp at h
    · rw [hvv] at h; dsimp only at h
      split at h
      · injection h with _ hm; rw [← hm]
      · simp at h

theorem lookup_setVar_eq {F : Type} (st : PanSemStateFiniteExact 64 F)
    (nm : MlS) (v : ValueHOL 64) :
    (setVarHOLFinite nm v st).locals.lookup nm = some v := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

theorem lookup_setVar_ne {F : Type} (st : PanSemStateFiniteExact 64 F)
    (nm k : MlS) (v : ValueHOL 64) (hne : k ≠ nm) :
    (setVarHOLFinite nm v st).locals.lookup k = st.locals.lookup k := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]

theorem eval_local_word {F : Type} (cur : PanSemStateFiniteExact 64 F)
    (nm : MlS) (w : BitVec 64)
    (hw : cur.locals.lookup nm = some (.val (.word w))) :
    ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      (.var .local nm) = some v → ∃ w' : BitVec 64, v = .val (.word w') := by
  intro v hv
  simp [evalHOLExact, toExact, hw] at hv
  exact ⟨w, hv.symm⟩

theorem worldEff_ite_ssz_fail {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (heff : WorldEff s cur Rl B gw) (cond : ExpHOL 64) (codeArgs : List (ExpHOL 64))
    (hnt : (evaluateHOLFiniteState cur (.ite cond (.call (some (none, none)) (ofString "ssz_fail") codeArgs) .skip)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.ite cond (.call (some (none, none)) (ofString "ssz_fail") codeArgs) .skip)).1) :
    WorldEff s (evaluateHOLFiniteState cur (.ite cond (.call (some (none, none)) (ofString "ssz_fail") codeArgs) .skip)).2 Rl B gw :=
  worldEff_ite heff cond hnt hcr
    (fun _ _ _ hnt_y hcr_y => worldEff_call0_ro heff ro_host_ssz_fail_local codeArgs hnt_y hcr_y)
    (fun _ _ _ => worldEff_skip heff)


end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
