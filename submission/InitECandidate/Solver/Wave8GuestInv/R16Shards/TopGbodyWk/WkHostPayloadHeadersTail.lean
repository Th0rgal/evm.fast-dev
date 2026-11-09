import InitECandidate.Solver.Wave8GuestInv.ContractParts.C08
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01AllocMpt
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkCacheGetRootTop
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M15.ro_max
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.RlpHelpers
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.GbodyRunAttempt

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
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

section DecodeHostInput

private theorem udivmod_step_inv (a b : Nat) {k q r : Nat}
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

private theorem bv_or_pow2_eq_add {q : BitVec 64} {k : Nat} (hk : k < 64)
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

private theorem bv_r1_eq {r a : BitVec 64} {k : Nat} (hk : k < 64)
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


private abbrev udivmodLoopBody : ProgHOL 64 :=
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

private abbrev udivmodLoop : ProgHOL 64 :=
  .while (.cmp .less (.const 0#64) (.var .local (ofString "i"))) udivmodLoopBody

private theorem udivmod_loop_inv {F : Type} (aw bw : BitVec 64) (hb0 : 0 < bw.toNat) :
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



private theorem udivmodLoop_not_returned {F : Type} :
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

private theorem udivmod_body_returns {F : Type}
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

private theorem lookup_host_input_byte :
    originalRuntimeCode.lookup (ofString "host_input_byte") =
      some ([(ofString "i", .one)], sourceFnBody Guest.Software.guestFn_host_input_byte, .one) :=
  lookup_of_guestAst_getElem 197 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_host_input_byte) rfl

private theorem lookup_host_input_le32 :
    originalRuntimeCode.lookup (ofString "host_input_le32") =
      some ([(ofString "i", .one)], sourceFnBody Guest.Software.guestFn_host_input_le32, .one) :=
  lookup_of_guestAst_getElem 198 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_host_input_le32) rfl

private theorem worldEff_host_input_byte_body {F : Type}
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

private theorem worldEff_host_input_le32_body {F : Type}
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

private theorem readOnlyProg_call_trap_with (args : List (ExpHOL 64)) :
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

private theorem ro_udivmod : InitECandidate.Solver.Wave8GuestInv.ReadOnlyFn (ofString "udivmod") := by
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

private theorem ro_host_ssz_fail_local : InitECandidate.Solver.Wave8GuestInv.ReadOnlyFn (ofString "ssz_fail") := by
  refine R13.readOnlyFn_of_guestAst 196 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_ssz_fail rfl ?_
  dsimp only [Guest.Software.guestFn_ssz_fail, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  exact R13.ReadOnlyProg.seq (R13.ReadOnlyProg.raise _ _) (R13.ReadOnlyProg.ret _)

private theorem ro_ssz_fixed_list_count : InitECandidate.Solver.Wave8GuestInv.ReadOnlyFn (ofString "ssz_fixed_list_count") := by
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

private theorem evalHOLExact_op_is_word {F : Type} (st : PanSemStateFiniteExact 64 F)
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

private theorem evalHOLExact_rfield_comb2_is_word {F : Type} (st : PanSemStateFiniteExact 64 F)
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

private abbrev dhiOffsRegions {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  [(globN s "ssz_offs", if globN s "ssz_offs" = 0 then 0 else 64)]

private abbrev dhiGw : List String := ["heap_ptr"]

private theorem dhi_no_gb : ∀ gs ∈ globalBuffers, ofString gs.1 ∉ dhiGw.map ofString := by decide
private theorem dhi_core_out : ∀ g ∈ coreWorldGlobals, ofString g ∉ dhiGw.map ofString := by decide

private theorem ssz_fail_noret {F : Type} (st : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
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

private theorem ite_ssz_fail_keeps {F : Type}
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

private theorem ite_trap_with_keeps {F : Type}
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

private theorem worldEff_call_trap_with {F : Type}
    {s cur : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (heff : WorldEff s cur Rl B gw) (args : List (ExpHOL 64))
    (hnt : (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "trap_with") args)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "trap_with") args)).1) :
    WorldEff s (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "trap_with") args)).2 Rl B gw :=
  heff.of_readOnly (readOnlyProg_call_trap_with args cur heff.code heff.arena.1 hnt hcr)

private theorem ssz_offs_allocated {F : Type} {s : PanSemStateFiniteExact 64 F}
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

private theorem worldEff_store_ssz_offs_const {F : Type}
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

private theorem worldEff_store_ssz_offs_dyn {F : Type}
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

private def noLocalAssign (x : MlS) : ProgHOL 64 → Bool
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

private theorem evaluate_keepLocal {F : Type} (x : MlS)
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

private theorem lookup_precheck_host_ssz_header :
    originalRuntimeCode.lookup (ofString "precheck_host_ssz_header") =
      some ([], sourceFnBody Guest.Software.guestFn_precheck_host_ssz_header, .one) :=
  lookup_of_guestAst_getElem 199 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_precheck_host_ssz_header) rfl

private theorem lookup_ssz_fail_dhi :
    originalRuntimeCode.lookup (ofString "ssz_fail") =
      some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_ssz_fail, .one) :=
  lookup_of_guestAst_getElem 196 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ssz_fail) rfl

private theorem lookup_ssz_check_offsets_dhi :
    originalRuntimeCode.lookup (ofString "ssz_check_offsets") =
      some ([(ofString "offs", .one), (ofString "n", .one), (ofString "fixed", .one),
        (ofString "len", .one)], sourceFnBody Guest.Software.guestFn_ssz_check_offsets, .one) :=
  lookup_of_guestAst_getElem 201 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ssz_check_offsets) rfl

private theorem ro_ssz_check_offsets_local :
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

private theorem val_word_of_shapeEq_one {v : ValueHOL 64}
    (hsh : shapeEqHOL (shapeOfHOLExact v) .one = true) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  rcases v with ⟨⟨w⟩⟩ | _ | _
  · exact ⟨w, rfl⟩
  · simp [shapeOfHOLExact, shapeEqHOL] at hsh
  · simp [shapeOfHOLExact, shapeEqHOL] at hsh

private theorem store_keeps_locals {F : Type}
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

private theorem lookup_setVar_eq {F : Type} (st : PanSemStateFiniteExact 64 F)
    (nm : MlS) (v : ValueHOL 64) :
    (setVarHOLFinite nm v st).locals.lookup nm = some v := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

private theorem lookup_setVar_ne {F : Type} (st : PanSemStateFiniteExact 64 F)
    (nm k : MlS) (v : ValueHOL 64) (hne : k ≠ nm) :
    (setVarHOLFinite nm v st).locals.lookup k = st.locals.lookup k := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]

private theorem eval_local_word {F : Type} (cur : PanSemStateFiniteExact 64 F)
    (nm : MlS) (w : BitVec 64)
    (hw : cur.locals.lookup nm = some (.val (.word w))) :
    ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a))
      (.var .local nm) = some v → ∃ w' : BitVec 64, v = .val (.word w') := by
  intro v hv
  simp [evalHOLExact, toExact, hw] at hv
  exact ⟨w, hv.symm⟩

private theorem worldEff_ite_ssz_fail {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (heff : WorldEff s cur Rl B gw) (cond : ExpHOL 64) (codeArgs : List (ExpHOL 64))
    (hnt : (evaluateHOLFiniteState cur (.ite cond (.call (some (none, none)) (ofString "ssz_fail") codeArgs) .skip)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.ite cond (.call (some (none, none)) (ofString "ssz_fail") codeArgs) .skip)).1) :
    WorldEff s (evaluateHOLFiniteState cur (.ite cond (.call (some (none, none)) (ofString "ssz_fail") codeArgs) .skip)).2 Rl B gw :=
  worldEff_ite heff cond hnt hcr
    (fun _ _ _ hnt_y hcr_y => worldEff_call0_ro heff ro_host_ssz_fail_local codeArgs hnt_y hcr_y)
    (fun _ _ _ => worldEff_skip heff)

private theorem worldEff_precheck_host_ssz_header_body {F : Type}
    {s entry : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hWOK : WorldOK s)
    (heff : WorldEff s entry (dhiOffsRegions s) B dhiGw)
    (hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_precheck_host_ssz_header)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_precheck_host_ssz_header)).1) :
    WorldEff s (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_precheck_host_ssz_header)).2 (dhiOffsRegions s) B dhiGw := by
  dsimp only [Guest.Software.guestFn_precheck_host_ssz_header, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hcr ⊢
  refine worldEff_dec heff _ _ _ hnt hcr (fun _ _ _ hnt1 hcr1 => ?_)
  refine worldEff_seq hnt1 hcr1
    (fun _ _ => worldEff_shMemLoad_local (heff.locals_clock _ _) _ _ _)
    (fun m1 _ heff1 hnt2 hcr2 => ?_)
  refine worldEff_seq hnt2 hcr2
    (fun hnt_a hcr_a => worldEff_ite heff1 _ hnt_a hcr_a
      (fun _ _ _ _ _ => worldEff_return heff1 _)
      (fun _ _ _ => worldEff_skip heff1))
    (fun m2 _ heff2 hnt3 hcr3 => ?_)
  refine worldEff_seq hnt3 hcr3
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail heff2 _ _ hnt_a hcr_a)
    (fun m3 _ heff3 hnt4 hcr4 => ?_)
  refine worldEff_decCall_eff heff3 _ _ _ _ _ _ _ lookup_host_input_byte
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_byte_body (heff3.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ _ _ _ _ _ _ heff4 hnt5 hcr5 => ?_) hnt4 hcr4
  refine worldEff_decCall_eff (heff4.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_byte
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_byte_body (heff4.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ _ _ _ _ _ _ heff5 hnt6 hcr6 => ?_) hnt5 hcr5
  refine worldEff_seq hnt6 hcr6
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail (heff5.locals_clock _ _) _ _ hnt_a hcr_a)
    (fun m6 _ heff6 hnt7 hcr7 => ?_)
  refine worldEff_dec heff6 _ _ _ hnt7 hcr7 (fun _ _ _ hnt8 hcr8 => ?_)
  refine worldEff_seq hnt8 hcr8
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail (heff6.locals_clock _ _) _ _ hnt_a hcr_a)
    (fun m7 _ heff7 hnt9 hcr9 => ?_)
  refine worldEff_decCall_eff heff7 _ _ _ _ _ _ _ lookup_host_input_le32
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_le32_body (heff7.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ rv1 cpost1 _ _ _ hsh1 heff8 hnt10 hcr10 => ?_) hnt9 hcr9
  obtain ⟨w_onpr, rfl⟩ := val_word_of_shapeEq_one hsh1
  refine worldEff_decCall_eff (heff8.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_le32
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_le32_body (heff8.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ rv2 cpost2 _ _ _ hsh2 heff9 hnt11 hcr11 => ?_) hnt10 hcr10
  obtain ⟨w_owit, rfl⟩ := val_word_of_shapeEq_one hsh2
  have honpr_m8 : (setVarHOLFinite (ofString "o_wit") (.val (.word w_owit))
      { cpost2 with locals := (setVarHOLFinite (ofString "o_npr") (.val (.word w_onpr)) { cpost1 with locals := m7.locals }).locals }).locals.lookup
      (ofString "o_npr") = some (.val (.word w_onpr)) := by
    rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact lookup_setVar_eq _ _ _
  have howit_m8 : (setVarHOLFinite (ofString "o_wit") (.val (.word w_owit))
      { cpost2 with locals := (setVarHOLFinite (ofString "o_npr") (.val (.word w_onpr)) { cpost1 with locals := m7.locals }).locals }).locals.lookup
      (ofString "o_wit") = some (.val (.word w_owit)) :=
    lookup_setVar_eq _ _ _
  refine worldEff_seq hnt11 hcr11
    (fun _ _ => worldEff_store_ssz_offs_const hWOK (heff9.locals_clock _ _) 0 (by decide) _ _ (Or.inl ⟨rfl, rfl⟩)
      (eval_local_word _ _ _ honpr_m8))
    (fun m9 hm9 heff10 hnt12 hcr12 => ?_)
  have hm9_loc := store_keeps_locals _ _ _ _ hm9
  have howit_m9 : m9.locals.lookup (ofString "o_wit") = some (.val (.word w_owit)) := by
    rw [hm9_loc]; exact howit_m8
  refine worldEff_seq hnt12 hcr12
    (fun _ _ => worldEff_store_ssz_offs_const hWOK heff10 8 (by decide) _ _ (Or.inr rfl)
      (eval_local_word _ _ _ howit_m9))
    (fun m10 _ heff11 hnt13 hcr13 => ?_)
  refine worldEff_seq hnt13 hcr13
    (fun hnt_a hcr_a => worldEff_call0_ro heff11 ro_ssz_check_offsets_local _ hnt_a hcr_a)
    (fun m11 _ heff12 hnt14 hcr14 => ?_)
  refine worldEff_dec heff12 _ _ _ hnt14 hcr14 (fun _ _ _ hnt15 hcr15 => ?_)
  refine worldEff_seq hnt15 hcr15
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail (heff12.locals_clock _ _) _ _ hnt_a hcr_a)
    (fun m12 _ heff13 hnt16 hcr16 => ?_)
  refine worldEff_dec heff13 _ _ _ hnt16 hcr16 (fun v_np _ _ hnt17 hcr17 => ?_)
  let m12_np := setVarHOLFinite (ofString "np") v_np m12
  refine worldEff_decCall_eff (heff13.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_le32
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_le32_body (heff13.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ rv_pl cpost_pl _ _ _ hsh_pl heff14 hnt18 hcr18 => ?_) hnt17 hcr17
  obtain ⟨w_opl, rfl⟩ := val_word_of_shapeEq_one hsh_pl
  refine worldEff_decCall_eff (heff14.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_le32
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_le32_body (heff14.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ rv_vh cpost_vh _ _ _ hsh_vh heff15 hnt19 hcr19 => ?_) hnt18 hcr18
  obtain ⟨w_ovh, rfl⟩ := val_word_of_shapeEq_one hsh_vh
  refine worldEff_decCall_eff (heff15.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_le32
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_le32_body (heff15.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ rv_rq cpost_rq _ _ _ hsh_rq heff16 hnt20 hcr20 => ?_) hnt19 hcr19
  obtain ⟨w_orq, rfl⟩ := val_word_of_shapeEq_one hsh_rq
  have hopl_0 : (setVarHOLFinite (ofString "o_rq") (.val (.word w_orq))
      { cpost_rq with locals := (setVarHOLFinite (ofString "o_vh") (.val (.word w_ovh))
        { cpost_vh with locals := (setVarHOLFinite (ofString "o_pl") (.val (.word w_opl))
          { cpost_pl with locals := m12_np.locals }).locals }).locals }).locals.lookup (ofString "o_pl") =
      some (.val (.word w_opl)) := by
    rw [lookup_setVar_ne _ _ _ _ (by decide)]
    change (setVarHOLFinite (ofString "o_vh") _ _).locals.lookup _ = _
    rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hovh_0 : (setVarHOLFinite (ofString "o_rq") (.val (.word w_orq))
      { cpost_rq with locals := (setVarHOLFinite (ofString "o_vh") (.val (.word w_ovh))
        { cpost_vh with locals := (setVarHOLFinite (ofString "o_pl") (.val (.word w_opl))
          { cpost_pl with locals := m12_np.locals }).locals }).locals }).locals.lookup (ofString "o_vh") =
      some (.val (.word w_ovh)) := by
    rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have horq_0 : (setVarHOLFinite (ofString "o_rq") (.val (.word w_orq))
      { cpost_rq with locals := (setVarHOLFinite (ofString "o_vh") (.val (.word w_ovh))
        { cpost_vh with locals := (setVarHOLFinite (ofString "o_pl") (.val (.word w_opl))
          { cpost_pl with locals := m12_np.locals }).locals }).locals }).locals.lookup (ofString "o_rq") =
      some (.val (.word w_orq)) :=
    lookup_setVar_eq _ _ _
  refine worldEff_seq hnt20 hcr20
    (fun _ _ => worldEff_store_ssz_offs_const hWOK (heff16.locals_clock _ _) 0 (by decide) _ _ (Or.inl ⟨rfl, rfl⟩)
      (eval_local_word _ _ _ hopl_0))
    (fun m20 hm20 heff17 hnt21 hcr21 => ?_)
  have hm20_loc := store_keeps_locals _ _ _ _ hm20
  have hovh_1 : m20.locals.lookup (ofString "o_vh") = some (.val (.word w_ovh)) := by
    rw [hm20_loc]; exact hovh_0
  have horq_1 : m20.locals.lookup (ofString "o_rq") = some (.val (.word w_orq)) := by
    rw [hm20_loc]; exact horq_0
  refine worldEff_seq hnt21 hcr21
    (fun _ _ => worldEff_store_ssz_offs_const hWOK heff17 8 (by decide) _ _ (Or.inr rfl)
      (eval_local_word _ _ _ hovh_1))
    (fun m21 hm21 heff18 hnt22 hcr22 => ?_)
  have hm21_loc := store_keeps_locals _ _ _ _ hm21
  have horq_2 : m21.locals.lookup (ofString "o_rq") = some (.val (.word w_orq)) := by
    rw [hm21_loc]; exact horq_1
  refine worldEff_seq hnt22 hcr22
    (fun _ _ => worldEff_store_ssz_offs_const hWOK heff18 16 (by decide) _ _ (Or.inr rfl)
      (eval_local_word _ _ _ horq_2))
    (fun m22 _ heff19 hnt23 hcr23 => ?_)
  refine worldEff_seq hnt23 hcr23
    (fun hnt_a hcr_a => worldEff_call0_ro heff19 ro_ssz_check_offsets_local _ hnt_a hcr_a)
    (fun m23 _ heff20 hnt24 hcr24 => ?_)
  refine worldEff_dec heff20 _ _ _ hnt24 hcr24 (fun _ _ _ hnt25 hcr25 => ?_)
  refine worldEff_seq hnt25 hcr25
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail (heff20.locals_clock _ _) _ _ hnt_a hcr_a)
    (fun m24 _ heff21 hnt26 hcr26 => ?_)
  refine worldEff_dec heff21 _ _ _ hnt26 hcr26 (fun v_pld _ _ hnt27 hcr27 => ?_)
  let m24_pld := setVarHOLFinite (ofString "payload") v_pld m24
  refine worldEff_decCall_eff (heff21.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_le32
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_le32_body (heff21.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ rv_ex cpost_ex _ _ _ hsh_ex heff22 hnt28 hcr28 => ?_) hnt27 hcr27
  obtain ⟨w_oex, rfl⟩ := val_word_of_shapeEq_one hsh_ex
  refine worldEff_decCall_eff (heff22.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_le32
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_le32_body (heff22.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ rv_tx cpost_tx _ _ _ hsh_tx heff23 hnt29 hcr29 => ?_) hnt28 hcr28
  obtain ⟨w_otx, rfl⟩ := val_word_of_shapeEq_one hsh_tx
  refine worldEff_decCall_eff (heff23.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_le32
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_le32_body (heff23.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ rv_wd cpost_wd _ _ _ hsh_wd heff24 hnt30 hcr30 => ?_) hnt29 hcr29
  obtain ⟨w_owd, rfl⟩ := val_word_of_shapeEq_one hsh_wd
  refine worldEff_decCall_eff (heff24.locals_clock _ _) _ _ _ _ _ _ _ lookup_host_input_le32
    (fun callee _ _ _ hnt_c hres_c => worldEff_host_input_le32_body (heff24.locals_clock callee _) hnt_c (Or.inr (Or.inr (Or.inr hres_c))))
    (fun _ _ rv_bl cpost_bl _ _ _ hsh_bl heff25 hnt31 hcr31 => ?_) hnt30 hcr30
  obtain ⟨w_obl, rfl⟩ := val_word_of_shapeEq_one hsh_bl
  have hoex_0 : (setVarHOLFinite (ofString "o_bal") (.val (.word w_obl))
      { cpost_bl with locals := (setVarHOLFinite (ofString "o_wd") (.val (.word w_owd))
        { cpost_wd with locals := (setVarHOLFinite (ofString "o_txs") (.val (.word w_otx))
          { cpost_tx with locals := (setVarHOLFinite (ofString "o_extra") (.val (.word w_oex))
            { cpost_ex with locals := m24_pld.locals }).locals }).locals }).locals }).locals.lookup (ofString "o_extra") =
      some (.val (.word w_oex)) := by
    rw [lookup_setVar_ne _ _ _ _ (by decide)]
    change (setVarHOLFinite (ofString "o_wd") _ _).locals.lookup _ = _
    rw [lookup_setVar_ne _ _ _ _ (by decide)]
    change (setVarHOLFinite (ofString "o_txs") _ _).locals.lookup _ = _
    rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hotx_0 : (setVarHOLFinite (ofString "o_bal") (.val (.word w_obl))
      { cpost_bl with locals := (setVarHOLFinite (ofString "o_wd") (.val (.word w_owd))
        { cpost_wd with locals := (setVarHOLFinite (ofString "o_txs") (.val (.word w_otx))
          { cpost_tx with locals := (setVarHOLFinite (ofString "o_extra") (.val (.word w_oex))
            { cpost_ex with locals := m24_pld.locals }).locals }).locals }).locals }).locals.lookup (ofString "o_txs") =
      some (.val (.word w_otx)) := by
    rw [lookup_setVar_ne _ _ _ _ (by decide)]
    change (setVarHOLFinite (ofString "o_wd") _ _).locals.lookup _ = _
    rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have howd_0 : (setVarHOLFinite (ofString "o_bal") (.val (.word w_obl))
      { cpost_bl with locals := (setVarHOLFinite (ofString "o_wd") (.val (.word w_owd))
        { cpost_wd with locals := (setVarHOLFinite (ofString "o_txs") (.val (.word w_otx))
          { cpost_tx with locals := (setVarHOLFinite (ofString "o_extra") (.val (.word w_oex))
            { cpost_ex with locals := m24_pld.locals }).locals }).locals }).locals }).locals.lookup (ofString "o_wd") =
      some (.val (.word w_owd)) := by
    rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hobl_0 : (setVarHOLFinite (ofString "o_bal") (.val (.word w_obl))
      { cpost_bl with locals := (setVarHOLFinite (ofString "o_wd") (.val (.word w_owd))
        { cpost_wd with locals := (setVarHOLFinite (ofString "o_txs") (.val (.word w_otx))
          { cpost_tx with locals := (setVarHOLFinite (ofString "o_extra") (.val (.word w_oex))
            { cpost_ex with locals := m24_pld.locals }).locals }).locals }).locals }).locals.lookup (ofString "o_bal") =
      some (.val (.word w_obl)) :=
    lookup_setVar_eq _ _ _
  refine worldEff_seq hnt31 hcr31
    (fun _ _ => worldEff_store_ssz_offs_const hWOK (heff25.locals_clock _ _) 0 (by decide) _ _ (Or.inl ⟨rfl, rfl⟩)
      (eval_local_word _ _ _ hoex_0))
    (fun m31 hm31 heff26 hnt32 hcr32 => ?_)
  have hm31_loc := store_keeps_locals _ _ _ _ hm31
  have hotx_1 : m31.locals.lookup (ofString "o_txs") = some (.val (.word w_otx)) := by
    rw [hm31_loc]; exact hotx_0
  have howd_1 : m31.locals.lookup (ofString "o_wd") = some (.val (.word w_owd)) := by
    rw [hm31_loc]; exact howd_0
  have hobl_1 : m31.locals.lookup (ofString "o_bal") = some (.val (.word w_obl)) := by
    rw [hm31_loc]; exact hobl_0
  refine worldEff_seq hnt32 hcr32
    (fun _ _ => worldEff_store_ssz_offs_const hWOK heff26 8 (by decide) _ _ (Or.inr rfl)
      (eval_local_word _ _ _ hotx_1))
    (fun m32 hm32 heff27 hnt33 hcr33 => ?_)
  have hm32_loc := store_keeps_locals _ _ _ _ hm32
  have howd_2 : m32.locals.lookup (ofString "o_wd") = some (.val (.word w_owd)) := by
    rw [hm32_loc]; exact howd_1
  have hobl_2 : m32.locals.lookup (ofString "o_bal") = some (.val (.word w_obl)) := by
    rw [hm32_loc]; exact hobl_1
  refine worldEff_seq hnt33 hcr33
    (fun _ _ => worldEff_store_ssz_offs_const hWOK heff27 16 (by decide) _ _ (Or.inr rfl)
      (eval_local_word _ _ _ howd_2))
    (fun m33 hm33 heff28 hnt34 hcr34 => ?_)
  have hm33_loc := store_keeps_locals _ _ _ _ hm33
  have hobl_3 : m33.locals.lookup (ofString "o_bal") = some (.val (.word w_obl)) := by
    rw [hm33_loc]; exact hobl_2
  refine worldEff_seq hnt34 hcr34
    (fun _ _ => worldEff_store_ssz_offs_const hWOK heff28 24 (by decide) _ _ (Or.inr rfl)
      (eval_local_word _ _ _ hobl_3))
    (fun m34 _ heff29 hnt35 hcr35 => ?_)
  refine worldEff_seq hnt35 hcr35
    (fun hnt_a hcr_a => worldEff_call0_ro heff29 ro_ssz_check_offsets_local _ hnt_a hcr_a)
    (fun m35 _ heff30 _ _ => worldEff_return heff30 _)

private theorem lookup_input_blob :
    originalRuntimeCode.lookup (ofString "input_blob") =
      some ([], sourceFnBody Guest.Software.guestFn_input_blob, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 29 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_input_blob) rfl

private theorem lookup_ssz_split_var_list :
    originalRuntimeCode.lookup (ofString "ssz_split_var_list") =
      some ([(ofString "p", .one), (ofString "len", .one), (ofString "lim", .one)],
        sourceFnBody Guest.Software.guestFn_ssz_split_var_list, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 202 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ssz_split_var_list) rfl

private theorem lookup_decode_payload :
    originalRuntimeCode.lookup (ofString "decode_payload") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_decode_payload, .one) :=
  lookup_of_guestAst_getElem 204 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_payload) rfl

private theorem lookup_decode_requests :
    originalRuntimeCode.lookup (ofString "decode_requests") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_decode_requests, .one) :=
  lookup_of_guestAst_getElem 205 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_requests) rfl

private theorem lookup_decode_bytes_list :
    originalRuntimeCode.lookup (ofString "decode_bytes_list") =
      some ([(ofString "p", .one), (ofString "len", .one), (ofString "lim", .one), (ofString "maxb", .one)],
        sourceFnBody Guest.Software.guestFn_decode_bytes_list, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 206 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_bytes_list) rfl

private theorem lookup_decode_stateless_input :
    originalRuntimeCode.lookup (ofString "decode_stateless_input") =
      some ([(ofString "p", .one), (ofString "len", .one)],
        sourceFnBody Guest.Software.guestFn_decode_stateless_input, .one) :=
  lookup_of_guestAst_getElem 207 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_stateless_input) rfl

private theorem lookup_decode_host_input :
    originalRuntimeCode.lookup (ofString "decode_host_input") =
      some ([], sourceFnBody Guest.Software.guestFn_decode_host_input, .one) :=
  lookup_of_guestAst_getElem 200 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_host_input) rfl

private theorem worldEff_while_cond_dhi {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (cond : ExpHOL 64) {body : ProgHOL 64}
    (Inv : PanSemStateFiniteExact 64 F → Prop)
    (hdec : ∀ t, Inv t → Inv (decClockHOLFinite t))
    (hb : ∀ t (cw : BitVec 64),
      @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word cw)) →
      cw ≠ 0 →
      WorldEff s (decClockHOLFinite t) Rl B gw → Inv (decClockHOLFinite t) →
      (evaluateHOLFiniteState (decClockHOLFinite t) body).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState (decClockHOLFinite t) body).1 →
      WorldEff s (evaluateHOLFiniteState (decClockHOLFinite t) body).2 Rl B gw ∧
      (((evaluateHOLFiniteState (decClockHOLFinite t) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite t) body).1 = some .continue) →
        Inv (evaluateHOLFiniteState (decClockHOLFinite t) body).2)) :
    ∀ (k : Nat) (cur : PanSemStateFiniteExact 64 F), cur.clock = k →
      WorldEff s cur Rl B gw → Inv cur →
      (evaluateHOLFiniteState cur (.while cond body)).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState cur (.while cond body)).1 →
      WorldEff s (evaluateHOLFiniteState cur (.while cond body)).2 Rl B gw := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro cur hclk heff hinv hnt hcr
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt hcr ⊢
    rcases hc : @evalHOLFinite 64 F _ cur (fun a => Classical.propDecidable (cur.memaddrs a)) cond with _ | cv
    · exact heff
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try exact heff
      rw [hc] at hnt hcr; dsimp only at hnt hcr ⊢
      by_cases hw0 : cw = 0
      · subst hw0; simp; exact heff
      · rw [if_pos hw0] at hnt hcr ⊢
        by_cases hk0 : cur.clock = 0
        · rw [if_pos hk0] at hnt; exact absurd rfl hnt
        · rw [if_neg hk0] at hnt hcr ⊢
          have heff_d : WorldEff s (decClockHOLFinite cur) Rl B gw := heff.locals_clock cur.locals (cur.clock - 1)
          have hinv_d : Inv (decClockHOLFinite cur) := hdec cur hinv
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite cur) body
          rcases hbo : evaluateHOLFiniteState (decClockHOLFinite cur) body with ⟨rb, sb⟩
          simp only [hbo] at hnt hcr hrem ⊢
          have hlt : sb.clock < k := by
            change sb.clock ≤ cur.clock - 1 at hrem; omega
          cases rb with
          | none =>
            obtain ⟨heff_b, hinv_b⟩ := hb cur cw hc hw0 heff_d hinv_d
              (by rw [hbo]; simp) (by rw [hbo]; exact Or.inl rfl)
            rw [hbo] at heff_b hinv_b
            exact ih sb.clock hlt sb rfl heff_b (hinv_b (Or.inl rfl)) hnt hcr
          | some r1 =>
            cases r1 with
            | «continue» =>
              obtain ⟨heff_b, hinv_b⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inl rfl)))
              rw [hbo] at heff_b hinv_b
              exact ih sb.clock hlt sb rfl heff_b (hinv_b (Or.inr rfl)) hnt hcr
            | «break» =>
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inl rfl))
              rw [hbo] at heff_b; exact heff_b
            | timeOut => exact absurd rfl hnt
            | returned v =>
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))))
              rw [hbo] at heff_b; exact heff_b
            | exception eid ev =>
              have hres_e : InitECandidate.Solver.Wave8GuestInv.Resumes (some (.exception eid ev)) := by
                rcases hcr with h | h | h | hr <;> [cases h; cases h; cases h; exact hr]
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inr hres_e)))
              rw [hbo] at heff_b; exact heff_b
            | error =>
              rcases hcr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> cases h
            | finalFfi _ =>
              rcases hcr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> cases h

private theorem flowing_of_none_or_continue {r : Option (PanSemResultExact 64)}
    (h : r = none ∨ r = some .continue) : Flowing r := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

private theorem worldEff_input_blob_body {F : Type}
    {s entry : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    (heff : WorldEff s entry Rl B dhiGw)
    (hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_input_blob)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_input_blob)).1) :
    WorldEff s (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_input_blob)).2 Rl B dhiGw := by
  dsimp only [Guest.Software.guestFn_input_blob, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hcr ⊢
  refine worldEff_dec heff _ _ _ hnt hcr (fun _ _ _ hnt1 hcr1 => ?_)
  refine worldEff_seq hnt1 hcr1
    (fun _ _ => worldEff_shMemLoad_local (heff.locals_clock _ _) _ _ _)
    (fun m1 _ heff1 hnt2 hcr2 => ?_)
  refine worldEff_seq hnt2 hcr2
    (fun hnt_a hcr_a => worldEff_ite heff1 _ hnt_a hcr_a
      (fun _ _ _ hnt_y hcr_y => worldEff_call_trap_with heff1 _ hnt_y hcr_y)
      (fun _ _ _ => worldEff_skip heff1))
    (fun m2 hm2 heff2 hnt3 hcr3 => ?_)
  obtain ⟨hm2_eq, hcond_le⟩ := ite_trap_with_keeps m1 m2 heff1.code _ _ hm2
  have hlen_m1 : ∃ wlen : BitVec 64,
      m1.locals.lookup (ofString "len") = some (.val (.word wlen)) ∧ wlen.toNat ≤ 1073741808 := by
    simp only [evalHOLExact, evalListHOLExact, toExact] at hcond_le
    rcases hl : m1.locals.lookup (ofString "len") with _ | lv
    · simp [hl] at hcond_le
    · rcases lv with ⟨⟨wlen⟩⟩ | _ | _ <;>
        simp [hl, Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord] at hcond_le
      refine ⟨wlen, rfl, ?_⟩
      exact BitVec.le_def.1 hcond_le
  obtain ⟨wlen, hwlen_m1, hwlen_le⟩ := hlen_m1
  have hwlen_m2 : m2.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hm2_eq]; exact hwlen_m1
  refine worldEff_decCall_alloc heff2 (by decide) (ofString "p") _ hnt3 hcr3
    (fun pw nw m3 hsz_ev _ hm3_loc _ heff3 _ _ hpw_lo hpw_add hhp3_hi _ hnt4 hcr4 => ?_)
  have hnw_eq : nw = wlen + 8#64 := by
    simp [evalHOLExact, evalListHOLExact, toExact, hwlen_m2, wordOpHOL, wordOp, valueIsWord, valueWord] at hsz_ev
    exact hsz_ev.symm
  subst hnw_eq
  have hnw_nat : (wlen + 8#64).toNat = wlen.toNat + 8 := by
    rw [BitVec.toNat_add_of_lt]; · rfl
    · change wlen.toNat + 8 < 2 ^ 64; omega
  have hpw_hi : pw.toNat + wlen.toNat + 8 ≤ heapLimit := by omega
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  refine worldEff_dec heff3 _ _ _ hnt4 hcr4 (fun vi hvi _ hnt5 hcr5 => ?_)
  have hvi0 : vi = .val (.word 0#64) := by simp [evalHOLExact] at hvi; exact hvi.symm
  subst hvi0
  refine worldEff_dec (heff3.locals_clock _ _) _ _ _ hnt5 hcr5 (fun vw hvw _ hnt6 hcr6 => ?_)
  have hvw0 : vw = .val (.word 0#64) := by simp [evalHOLExact] at hvw; exact hvw.symm
  subst hvw0
  let m5 := setVarHOLFinite (ofString "w") (.val (.word 0#64)) (setVarHOLFinite (ofString "i") (.val (.word 0#64)) m3)
  let InvIb : PanSemStateFiniteExact 64 F → Prop := fun t =>
    t.locals.lookup (ofString "p") = some (.val (.word pw)) ∧
    t.locals.lookup (ofString "len") = some (.val (.word wlen)) ∧
    (∃ wi : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word wi))) ∧
    (∃ ww : BitVec 64, t.locals.lookup (ofString "w") = some (.val (.word ww)))
  have hinv_m5 : InvIb m5 := by
    refine ⟨?_, ?_, ⟨0#64, ?_⟩, ⟨0#64, lookup_setVar_eq _ _ _⟩⟩
    · dsimp only [m5]
      rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide), hm3_loc]
      simp [HolFiniteMapExact.lookup_update, FUPDATE]
    · dsimp only [m5]
      rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide), hm3_loc]
      simp [HolFiniteMapExact.lookup_update, FUPDATE, hwlen_m2,
        show ofString "p" ≠ ofString "len" by decide]
    · dsimp only [m5]
      rw [lookup_setVar_ne _ _ _ _ (by decide)]
      exact lookup_setVar_eq _ _ _
  refine worldEff_seq hnt6 hcr6
    (fun hnt_w hcr_w =>
      worldEff_while_cond_dhi _ InvIb (fun _ h => h)
        (fun t0 cw hcond hnz heff_t ⟨ht_p, ht_len, ⟨wi, ht_i⟩, ⟨ww, ht_w⟩⟩ hnt_b hcr_b => ?_)
        m5.clock m5 rfl (heff3.locals_clock _ _) hinv_m5 hnt_w hcr_w)
    (fun m6 _ heff6 _ _ => worldEff_return heff6 _)
  have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word wi)) := ht_i
  have ht0_len : t0.locals.lookup (ofString "len") = some (.val (.word wlen)) := ht_len
  have hwi_lt : wi.toNat < wlen.toNat := by
    rw [evalHOLFinite_eq_toExact] at hcond
    simp [evalHOLExact, evalListHOLExact, toExact, ht0_i, ht0_len,
      Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord] at hcond
    by_contra hge
    have hnlt : ¬(wi < wlen) := by simp [BitVec.lt_def]; omega
    simp [hnlt] at hcond
    exact hnz hcond.symm
  refine ⟨?_, fun hf => ?_⟩
  · refine worldEff_seq hnt_b hcr_b
      (fun _ _ => worldEff_shMemLoad_local heff_t _ _ _)
      (fun u1 hu1 heff_u1 hnt_s hcr_s => ?_)
    obtain ⟨ww', hu1_eq⟩ := shMemLoad_local_none_inv (decClockHOLFinite t0) .opW (ofString "w") _ hu1
    have hu1_p : u1.locals.lookup (ofString "p") = some (.val (.word pw)) := by
      rw [hu1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, ht_p,
        show ofString "w" ≠ ofString "p" by decide]
    have hu1_i : u1.locals.lookup (ofString "i") = some (.val (.word wi)) := by
      rw [hu1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, ht_i,
        show ofString "w" ≠ ofString "i" by decide]
    have hu1_w : u1.locals.lookup (ofString "w") = some (.val (.word ww')) := by
      rw [hu1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    refine worldEff_seq hnt_s hcr_s
      (fun _ _ => worldEff_store_word heff_u1 _ _
        (eval_local_word _ _ _ hu1_w)
        (fun x hx _ => ?_))
      (fun u2 _ heff_u2 _ _ => worldEff_assign_local heff_u2 _ _)
    simp [evalHOLExact, evalListHOLExact, toExact, hu1_p, hu1_i, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
    subst hx
    have hx_nat : (pw + wi).toNat = pw.toNat + wi.toNat := by
      rw [BitVec.toNat_add_of_lt]; omega
    exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
  · have hfl := flowing_of_none_or_continue hf
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [evaluate_keepLocal (ofString "p") _ (by decide) _ hfl]; exact ht_p
    · rw [evaluate_keepLocal (ofString "len") _ (by decide) _ hfl]; exact ht_len
    · exact evaluate_wordLocal (ofString "i") _ (by decide) _ ⟨wi, ht_i⟩ hfl
    · exact evaluate_wordLocal (ofString "w") _ (by decide) _ ⟨ww, ht_w⟩ hfl

private theorem eval_op_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (h_op : ∃ bop args, e = .op bop args) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v →
      ∃ w : BitVec 64, v = .val (.word w) := by
  obtain ⟨bop, args, rfl⟩ := h_op
  intro v hv
  simp only [evalHOLExact] at hv
  split at hv
  · split at hv
    · simp only [Option.map_eq_some_iff] at hv
      obtain ⟨_, _, rfl⟩ := hv; exact ⟨_, rfl⟩
    · cases hv
  · cases hv

private theorem eval_load_one_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.load .one e) = some v →
      ∃ w : BitVec 64, v = .val (.word w) := by
  intro v hv
  rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | ve
  · simp [evalHOLExact, isWfShapeExactHOL, he] at hv
  · cases ve with
    | val wl =>
      cases wl with
      | word a =>
        cases hm : s.memory a with
        | word w =>
          by_cases hd : s.memaddrs a
          · simp [evalHOLExact, isWfShapeExactHOL, he, memLoadHOLExact, hd, hm] at hv
            exact ⟨w, hv.symm⟩
          · simp [evalHOLExact, isWfShapeExactHOL, he, memLoadHOLExact, hd] at hv
    | _ =>
      simp [evalHOLExact, isWfShapeExactHOL, he] at hv

private theorem eval_rfield_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (idx : Nat) (name : MlS) (w0 w1 : BitVec 64)
    (hl : s.locals.lookup name = some (.rStruct [.val (.word w0), .val (.word w1)]))
    (hidx : idx = 0 ∨ idx = 1) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.rfield idx (.var .local name)) = some v →
      ∃ w : BitVec 64, v = .val (.word w) := by
  intro v hv
  rcases hidx with rfl | rfl <;>
  · simp [evalHOLExact, toExact, hl] at hv
    exact ⟨_, hv.symm⟩

private theorem eval_loadByte_lt_256 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.loadByte e) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat < 256 := by
  simp only [evalHOLExact] at hv
  split at hv
  · rename_i a ha
    dsimp only [panMemLoadByteHOL] at hv
    split at hv
    · simp only [Option.map_some, Option.some.injEq] at hv
      subst hv
      refine ⟨_, rfl, ?_⟩
      rw [BitVec.toNat_ofNat]
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (UInt8.toNat_lt _)
    · simp at hv
  · simp at hv

private theorem eval_or4_bytes_lt {F : Type} (s : PanSemStateFiniteExact 64 F)
    (l0 l1 l2 l3 : ExpHOL 64) (v : ValueHOL 64)
    (h0 : ∀ v0, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) l0 = some v0 →
      ∃ w0 : BitVec 64, v0 = .val (.word w0) ∧ w0.toNat < 256)
    (h1 : ∀ v1, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) l1 = some v1 →
      ∃ w1 : BitVec 64, v1 = .val (.word w1) ∧ w1.toNat < 256)
    (h2 : ∀ v2, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) l2 = some v2 →
      ∃ w2 : BitVec 64, v2 = .val (.word w2) ∧ w2.toNat < 256)
    (h3 : ∀ v3, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) l3 = some v3 →
      ∃ w3 : BitVec 64, v3 = .val (.word w3) ∧ w3.toNat < 256)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .or [l0, .shift .lsl l1 (.const 8#64), .shift .lsl l2 (.const 16#64), .shift .lsl l3 (.const 24#64)]) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat < 2 ^ 32 := by
  rcases hb0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) l0 with _ | v0
  · simp [evalHOLExact, evalListHOLExact, hb0] at hv
  rcases hb1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) l1 with _ | v1
  · simp [evalHOLExact, evalListHOLExact, hb0, hb1] at hv
  rcases hb2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) l2 with _ | v2
  · simp [evalHOLExact, evalListHOLExact, hb0, hb1, hb2] at hv
  rcases hb3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) l3 with _ | v3
  · simp [evalHOLExact, evalListHOLExact, hb0, hb1, hb2, hb3] at hv
  obtain ⟨w0, rfl, hw0⟩ := h0 v0 hb0
  obtain ⟨w1, rfl, hw1⟩ := h1 v1 hb1
  obtain ⟨w2, rfl, hw2⟩ := h2 v2 hb2
  obtain ⟨w3, rfl, hw3⟩ := h3 v3 hb3
  simp [evalHOLExact, evalListHOLExact, hb0, hb1, hb2, hb3, wordShiftHOL, wordOpHOL, wordOp,
    valueIsWord, valueWord] at hv
  subst hv
  refine ⟨_, rfl, ?_⟩
  have hsh_lt : ∀ (x : BitVec 64) (s m : Nat),
      x.toNat < 256 → s ≤ 24 → 256 * 2 ^ s ≤ 2 ^ m → m ≤ 32 →
      (x <<< s).toNat < 2 ^ m := by
    intro x s m hx hs hsm hm32
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have h1 : x.toNat * 2 ^ s < 256 * 2 ^ s := Nat.mul_lt_mul_of_pos_right hx (by positivity)
    have h2 : 2 ^ m ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) hm32
    have h3 : 2 ^ 32 < 2 ^ 64 := by decide
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hor_lt : ∀ (u v : BitVec 64) (m : Nat),
      u.toNat < 2 ^ m → v.toNat < 2 ^ m → (u ||| v).toNat < 2 ^ m := by
    intro u v m hu hv
    rw [BitVec.toNat_or]
    exact Nat.or_lt_two_pow hu hv
  change (w0 ||| ((w1 <<< 8) ||| ((w2 <<< 16) ||| ((w3 <<< 24) ||| 0#64)))).toNat < 2 ^ 32
  rw [BitVec.or_zero]
  exact hor_lt w0 _ 32 (by omega)
    (hor_lt (w1 <<< 8) _ 32 (hsh_lt w1 8 32 hw1 (by omega) (by decide) (by omega))
      (hor_lt (w2 <<< 16) (w3 <<< 24) 32
        (hsh_lt w2 16 32 hw2 (by omega) (by decide) (by omega))
        (hsh_lt w3 24 32 hw3 (by omega) (by decide) (by omega))))

private theorem eval_le32_word_lt {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e0 e1 e2 e3 : ExpHOL 64) (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .or [.loadByte e0,
                .shift .lsl (.loadByte e1) (.const 8#64),
                .shift .lsl (.loadByte e2) (.const 16#64),
                .shift .lsl (.loadByte e3) (.const 24#64)]) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat < 2 ^ 32 :=
  eval_or4_bytes_lt s _ _ _ _ v
    (eval_loadByte_lt_256 s e0)
    (eval_loadByte_lt_256 s e1)
    (eval_loadByte_lt_256 s e2)
    (eval_loadByte_lt_256 s e3)
    hv

private theorem worldEff_store_fresh_const {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    (heff : WorldEff s cur Rl B dhiGw)
    (bname : MlS) (bw : BitVec 64) (sz off : Nat)
    (hb : cur.locals.lookup bname = some (.val (.word bw)))
    (hlo : globN s "heap_ptr" ≤ bw.toNat)
    (hhi : bw.toNat + sz ≤ heapLimit)
    (hoff : off + 8 ≤ sz)
    (valExp : ExpHOL 64)
    (hword : ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w)) :
    WorldEff s
      (evaluateHOLFiniteState cur (.store (.op .add [.var .local bname, .const (BitVec.ofNat 64 off)]) valExp)).2
      Rl B dhiGw := by
  have hhl : heapLimit < 2 ^ 64 := by decide
  refine worldEff_store_word heff _ valExp hword (fun x hx _ => ?_)
  simp [evalHOLExact, evalListHOLExact, toExact, hb, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
  subst hx
  have hoff_nat : (BitVec.ofNat 64 off).toNat = off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx_nat : (bw + BitVec.ofNat 64 off).toNat = bw.toNat + off := by
    rw [BitVec.toNat_add_of_lt] <;> omega
  exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))

private def hasIncTail (x : MlS) : ProgHOL 64 → Bool
  | .assign .local nm (.op .add [.var .local nm', .const c]) =>
    decide (nm = x ∧ nm' = x ∧ c = 1#64)
  | .seq a b => noLocalAssign x a && hasIncTail x b
  | .dec nm _ _ b => decide (x ≠ nm) && hasIncTail x b
  | _ => false

private theorem evaluate_incTail_le {F : Type} (x : MlS) (bound : Nat) (hbound : bound < 2 ^ 64)
    (p : ProgHOL 64) (hinc : hasIncTail x p = true) :
    ∀ (st : PanSemStateFiniteExact 64 F) (wi : BitVec 64),
      st.locals.lookup x = some (.val (.word wi)) →
      wi.toNat < bound →
      ((evaluateHOLFiniteState st p).1 = none ∨ (evaluateHOLFiniteState st p).1 = some .continue) →
      ∃ wi' : BitVec 64,
        (evaluateHOLFiniteState st p).2.locals.lookup x = some (.val (.word wi')) ∧
        wi'.toNat ≤ bound := by
  match hp_eq : p with
  | .assign vk nm rhs =>
    cases vk with
    | global => simp [hasIncTail] at hinc
    | «local» =>
      cases rhs with
      | op bop args =>
        cases bop <;> try simp [hasIncTail] at hinc
        rcases args with _ | ⟨a1, _ | ⟨a2, _ | _⟩⟩ <;> try simp [hasIncTail] at hinc
        cases a1 with
        | var vk1 nm' =>
          cases vk1 <;> try simp [hasIncTail] at hinc
          cases a2 with
          | const c =>
            simp only [hasIncTail, decide_eq_true_eq] at hinc
            obtain ⟨rfl, rfl, rfl⟩ := hinc
            intro st wi hst hlt hf
            rw [evaluateHOLFiniteState_assign]
            simp only [evalHOLExact, evalListHOLExact, toExact, hst, wordOpHOL, wordOp, valueIsWord, valueWord,
              Option.map_some, List.all_cons, List.all_nil, Bool.and_self, ↓reduceIte,
              List.map, List.foldr, BitVec.add_zero] at hf ⊢
            split_ifs at hf ⊢ with hv
            · refine ⟨wi + 1#64, ?_, ?_⟩
              · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              · rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega)]
                omega
            · exact ⟨wi, hst, by omega⟩
          | _ => simp [hasIncTail] at hinc
        | _ => simp [hasIncTail] at hinc
      | _ => simp [hasIncTail] at hinc
  | .seq a b =>
    simp only [hasIncTail, Bool.and_eq_true] at hinc
    intro st wi hst hlt hf
    rw [evaluateHOLFiniteState_seq_line780] at hf ⊢
    rcases ha : evaluateHOLFiniteState st a with ⟨ra, mid⟩
    rw [ha] at hf
    cases ra with
    | none =>
      dsimp only at hf ⊢
      have hmid : mid.locals.lookup x = some (.val (.word wi)) := by
        have hk := evaluate_keepLocal x a hinc.1 st (Or.inl (by rw [ha]))
        rw [ha] at hk; rw [hk]; exact hst
      exact evaluate_incTail_le x bound hbound b hinc.2 mid wi hmid hlt hf
    | some r1 =>
      rcases hf with h | h
      · simp at h
      · injection h with h'; subst h'
        dsimp only
        have hmid : mid.locals.lookup x = some (.val (.word wi)) := by
          have hk := evaluate_keepLocal x a hinc.1 st (Or.inr (Or.inr (by rw [ha])))
          rw [ha] at hk; rw [hk]; exact hst
        exact ⟨wi, hmid, by omega⟩
  | .dec nm sh rhs b =>
    simp only [hasIncTail, Bool.and_eq_true, decide_eq_true_eq] at hinc
    intro st wi hst hlt hf
    revert hf; rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · intro hf; rcases hf with h | h <;> simp at h
    · split
      · rename_i v _ _
        intro hf
        have hset : (setVarHOLFinite nm v st).locals.lookup x = some (.val (.word wi)) := by
          rw [lookup_setVar_ne _ _ _ _ hinc.1]; exact hst
        obtain ⟨wi', hwi', hle'⟩ := evaluate_incTail_le x bound hbound b hinc.2 (setVarHOLFinite nm v st) wi hset hlt hf
        refine ⟨wi', ?_, hle'⟩
        dsimp only
        rw [resVarEq_lookup_local, if_neg hinc.1, hwi']
      · intro hf; rcases hf with h | h <;> simp at h
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _
  | .store _ _ | .storeByte _ _ | .ite _ _ _ | .while _ _ | .decCall _ _ _ _ _
  | .call _ _ _ | .shMemLoad _ _ _ _ | .shMemStore _ _ _ | .extCall _ _ _ _ _ =>
    simp [hasIncTail] at hinc
termination_by sizeOf p
decreasing_by
  all_goals
    subst hp_eq
    decreasing_tactic

private theorem shape_two_words_dhi (v : ValueHOL 64)
    (h : shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one]) = true) :
    ∃ a b : BitVec 64,
      v = .rStruct [.val (.word a), .val (.word b)] := by
  rcases v with _ | fs | _
  · simp [shapeOfHOLExact, shapeEqHOL] at h
  · rcases fs with _ | ⟨v0, _ | ⟨v1, _ | _⟩⟩ <;>
      try (simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h)
    rcases v0 with ⟨⟨a⟩⟩ | _ | _ <;> rcases v1 with ⟨⟨b⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL] at h
    exact ⟨a, b, rfl⟩
  · simp [shapeOfHOLExact, shapeEqHOL] at h

private theorem contOrRes_of_resumes_dhi {r : Option (PanSemResultExact 64)}
    (h : InitECandidate.Solver.Wave8GuestInv.Resumes r) : ContOrRes r :=
  Or.inr (Or.inr (Or.inr h))

private theorem worldEff_decCall_alloc_const {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    (heff : WorldEff s cur Rl B dhiGw)
    (name : MlS) (sz : Nat) (hsz8 : (sz + 7) / 8 * 8 = sz) (hsz_lt : sz < 2 ^ 64)
    {cont : ProgHOL 64}
    (hnt : (evaluateHOLFiniteState cur (.decCall name .one (ofString "alloc") [.const (BitVec.ofNat 64 sz)] cont)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.decCall name .one (ofString "alloc") [.const (BitVec.ofNat 64 sz)] cont)).1)
    (hcont : ∀ (pw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      mid.locals = cur.locals.update (name, .val (.word pw)) →
      WorldEff s mid Rl B dhiGw →
      pw.toNat % 8 = 0 →
      globN s "heap_ptr" ≤ pw.toNat →
      pw.toNat + sz ≤ heapLimit →
      WordsOK mid (pw.toNat, sz) →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState mid cont).1 →
      WorldEff s (evaluateHOLFiniteState mid cont).2 Rl B dhiGw) :
    WorldEff s (evaluateHOLFiniteState cur (.decCall name .one (ofString "alloc") [.const (BitVec.ofNat 64 sz)] cont)).2 Rl B dhiGw := by
  refine worldEff_decCall_alloc heff (by decide) name (.const (BitVec.ofNat 64 sz)) hnt hcr
    (fun pw nw mid hsz_ev _ hloc _ heff_m hal _ hlo hhp_eq hhp_hi hwok hnt_k hcr_k => ?_)
  have hnw : nw = BitVec.ofNat 64 sz := by
    simp [evalHOLExact] at hsz_ev; exact hsz_ev.symm
  subst hnw
  have hnw_nat : (BitVec.ofNat 64 sz).toNat = sz := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz_lt]
  rw [hnw_nat, hsz8] at hhp_eq hwok
  exact hcont pw mid hloc heff_m hal hlo (by omega) hwok hnt_k hcr_k

private theorem worldEff_seq_store_fresh {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    (heff : WorldEff s cur Rl B dhiGw)
    (bname : MlS) (bw : BitVec 64) (sz off : Nat)
    (hb : cur.locals.lookup bname = some (.val (.word bw)))
    (hlo : globN s "heap_ptr" ≤ bw.toNat)
    (hhi : bw.toNat + sz ≤ heapLimit)
    (hoff : off + 8 ≤ sz)
    (valExp : ExpHOL 64) {cont : ProgHOL 64}
    (hword : ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hnt : (evaluateHOLFiniteState cur (.seq (.store (.op .add [.var .local bname, .const (BitVec.ofNat 64 off)]) valExp) cont)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.seq (.store (.op .add [.var .local bname, .const (BitVec.ofNat 64 off)]) valExp) cont)).1)
    (hcont : ∀ mid, mid.locals = cur.locals → WorldEff s mid Rl B dhiGw →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState mid cont).1 →
      WorldEff s (evaluateHOLFiniteState mid cont).2 Rl B dhiGw) :
    WorldEff s (evaluateHOLFiniteState cur (.seq (.store (.op .add [.var .local bname, .const (BitVec.ofNat 64 off)]) valExp) cont)).2 Rl B dhiGw :=
  worldEff_seq hnt hcr
    (fun _ _ => worldEff_store_fresh_const heff bname bw sz off hb hlo hhi hoff valExp hword)
    (fun mid hmid heff_m hnt_c hcr_c => hcont mid (store_keeps_locals cur mid _ valExp hmid) heff_m hnt_c hcr_c)

private theorem worldEff_seq_store_ssz_offs_const {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hWOK : WorldOK s)
    (heff : WorldEff s cur (dhiOffsRegions s) B dhiGw)
    (off : Nat) (hoff : off + 8 ≤ 64)
    (dst valExp : ExpHOL 64) {cont : ProgHOL 64}
    (hdst : (dst = .var .global (ofString "ssz_offs") ∧ off = 0) ∨
            dst = .op .add [.var .global (ofString "ssz_offs"), .const (BitVec.ofNat 64 off)])
    (hword : ∀ v, @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hnt : (evaluateHOLFiniteState cur (.seq (.store dst valExp) cont)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState cur (.seq (.store dst valExp) cont)).1)
    (hcont : ∀ mid, mid.locals = cur.locals → WorldEff s mid (dhiOffsRegions s) B dhiGw →
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState mid cont).1 →
      WorldEff s (evaluateHOLFiniteState mid cont).2 (dhiOffsRegions s) B dhiGw) :
    WorldEff s (evaluateHOLFiniteState cur (.seq (.store dst valExp) cont)).2 (dhiOffsRegions s) B dhiGw :=
  worldEff_seq hnt hcr
    (fun _ _ => worldEff_store_ssz_offs_const hWOK heff off hoff dst valExp hdst hword)
    (fun mid hmid heff_m hnt_c hcr_c => hcont mid (store_keeps_locals cur mid dst valExp hmid) heff_m hnt_c hcr_c)

private theorem worldEff_ssz_split_var_list_body {F : Type}
    {s entry : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    (heff : WorldEff s entry Rl B dhiGw)
    (hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_ssz_split_var_list)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_ssz_split_var_list)).1) :
    WorldEff s (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_ssz_split_var_list)).2 Rl B dhiGw := by
  dsimp only [Guest.Software.guestFn_ssz_split_var_list, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hcr ⊢
  refine worldEff_seq hnt hcr
    (fun hnt_a hcr_a => worldEff_ite heff _ hnt_a hcr_a
      (fun _ _ _ _ _ => worldEff_return heff _)
      (fun _ _ _ => worldEff_skip heff))
    (fun m1 _ heff1 hnt1 hcr1 => ?_)
  refine worldEff_seq hnt1 hcr1
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail heff1 _ _ hnt_a hcr_a)
    (fun m2 _ heff2 hnt2 hcr2 => ?_)
  refine worldEff_dec heff2 _ _ _ hnt2 hcr2 (fun v_first hv_first _ hnt3 hcr3 => ?_)
  obtain ⟨w_first, rfl, hfirst_lt⟩ := eval_le32_word_lt m2 _ _ _ _ v_first hv_first
  let m3 := setVarHOLFinite (ofString "first") (.val (.word w_first)) m2
  refine worldEff_seq hnt3 hcr3
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail (heff2.locals_clock _ _) _ _ hnt_a hcr_a)
    (fun m4 hm4 heff4 hnt4 hcr4 => ?_)
  obtain ⟨hm4_eq, hcond21⟩ := ite_ssz_fail_keeps m3 m4 heff2.code _ _ hm4
  have hm3_first : m3.locals.lookup (ofString "first") = some (.val (.word w_first)) :=
    lookup_setVar_eq _ _ _
  have hfirst_pos : 4 ≤ w_first.toNat := by
    dsimp only [evalHOLExact, evalListHOLExact, toExact] at hcond21
    rw [hm3_first] at hcond21
    rcases hl_len : m3.locals.lookup (ofString "len") with _ | lv_len
    · simp [hl_len] at hcond21
    · rcases lv_len with ⟨⟨w_len⟩⟩ | _ | _ <;>
        (try simp [hl_len, Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord] at hcond21; done)
      simp only [hl_len, Compiler.Encoders.Asm.wordCmpHOL,
        wordOpHOL, wordOp, valueIsWord, valueWord,
        List.all_cons, List.all_nil, Bool.and_self, Option.map_some, ↓reduceIte,
        List.map, List.foldr,
        Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hcond21
      have hcond21' :
          (if (!0#64 == (if (w_first == 0#64) = true then 1#64 else 0#64) |||
              ((if (!w_first &&& (3#64 &&& ~~~0#64) == 0#64) = true then 1#64 else 0#64) |||
                ((if decide (w_len < w_first) = true then 1#64 else 0#64) ||| 0#64))) = true
            then 1#64 else 0#64) = 0#64 := hcond21
      have hne0 : w_first ≠ 0#64 := by
        intro hz; subst hz
        simp at hcond21'
      have hmod4 : w_first.toNat % 4 = 0 := by
        have hand3 : (3#64 &&& ~~~0#64 : BitVec 64) = 3#64 := rfl
        rw [hand3] at hcond21'
        by_cases hm : (w_first &&& 3#64) == 0#64
        · have hm' : w_first &&& 3#64 = 0#64 := eq_of_beq hm
          have hn := congrArg BitVec.toNat hm'
          rw [BitVec.toNat_and] at hn
          change w_first.toNat &&& (2 ^ 2 - 1) = 0 at hn
          rwa [Nat.and_two_pow_sub_one_eq_mod _ 2] at hn
        · exfalso
          simp [hm] at hcond21'
          revert hcond21'
          split <;> split <;> simp
      have hf_pos : 0 < w_first.toNat := by
        by_cases hp : w_first.toNat = 0
        · exact absurd (BitVec.eq_of_toNat_eq hp) hne0
        · omega
      omega
  have hm4_first : m4.locals.lookup (ofString "first") = some (.val (.word w_first)) := by
    rw [hm4_eq]; exact hm3_first
  refine worldEff_dec heff4 _ _ _ hnt4 hcr4 (fun v_cnt hv_cnt _ hnt5 hcr5 => ?_)
  have hv_cnt_eq : v_cnt = .val (.word (w_first >>> 2)) := by
    simp [evalHOLExact, toExact, hm4_first, wordShiftHOL] at hv_cnt
    exact hv_cnt.symm
  subst hv_cnt_eq
  let w_cnt := w_first >>> 2
  have hw_cnt_nat : w_cnt.toNat = w_first.toNat / 4 := by
    dsimp only [w_cnt]
    change (w_first >>> (2 : Nat)).toNat = w_first.toNat / 4
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hcnt_pos : 1 ≤ w_cnt.toNat := by omega
  have hcnt_lt : w_cnt.toNat < 2 ^ 30 := by omega
  let m5 := setVarHOLFinite (ofString "count") (.val (.word w_cnt)) m4
  refine worldEff_seq hnt5 hcr5
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail (heff4.locals_clock _ _) _ _ hnt_a hcr_a)
    (fun m6 hm6 heff6 hnt6 hcr6 => ?_)
  obtain ⟨hm6_eq, _⟩ := ite_ssz_fail_keeps m5 m6 heff4.code _ _ hm6
  have hm6_cnt : m6.locals.lookup (ofString "count") = some (.val (.word w_cnt)) := by
    rw [hm6_eq]; exact lookup_setVar_eq _ _ _
  have hm6_first : m6.locals.lookup (ofString "first") = some (.val (.word w_first)) := by
    rw [hm6_eq]; dsimp only [m5]
    rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm4_first
  refine worldEff_decCall_alloc heff6 (by decide) (ofString "arr") _ hnt6 hcr6
    (fun w_arr nw m7 hsz_ev _ hm7_loc _ heff7 _ _ harr_lo harr_add hhp7_hi _ hnt7 hcr7 => ?_)
  have hnw_eq : nw = w_cnt * 16#64 := by
    simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, hm6_cnt, valueIsWord, valueWord] at hsz_ev
    exact hsz_ev.symm
  subst hnw_eq
  have hnw_nat : (w_cnt * 16#64).toNat = w_cnt.toNat * 16 := by
    rw [BitVec.toNat_mul, show (16#64 : BitVec 64).toNat = 16 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have harr_hi : w_arr.toNat + w_cnt.toNat * 16 ≤ heapLimit := by omega
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hm7_cnt : m7.locals.lookup (ofString "count") = some (.val (.word w_cnt)) := by
    rw [hm7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm6_cnt,
      show ofString "arr" ≠ ofString "count" by decide]
  have hm7_first : m7.locals.lookup (ofString "first") = some (.val (.word w_first)) := by
    rw [hm7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm6_first,
      show ofString "arr" ≠ ofString "first" by decide]
  have hm7_arr : m7.locals.lookup (ofString "arr") = some (.val (.word w_arr)) := by
    rw [hm7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_dec heff7 _ _ _ hnt7 hcr7 (fun vi hvi _ hnt8 hcr8 => ?_)
  have hvi0 : vi = .val (.word 0#64) := by simp [evalHOLExact] at hvi; exact hvi.symm
  subst hvi0
  let m8 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) m7
  have hm8_first : m8.locals.lookup (ofString "first") = some (.val (.word w_first)) := by
    dsimp only [m8]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm7_first
  refine worldEff_dec (heff7.locals_clock _ _) _ _ _ hnt8 hcr8 (fun vprev hvprev _ hnt9 hcr9 => ?_)
  have hvprev_eq : vprev = .val (.word w_first) := by
    change @evalHOLExact 64 F _ m8.toExact (fun a => Classical.propDecidable (m8.memaddrs a)) _ = _ at hvprev
    simp [evalHOLExact, toExact, hm8_first] at hvprev; exact hvprev.symm
  subst hvprev_eq
  let m9 := setVarHOLFinite (ofString "prev") (.val (.word w_first)) m8
  let InvSp : PanSemStateFiniteExact 64 F → Prop := fun t =>
    t.locals.lookup (ofString "arr") = some (.val (.word w_arr)) ∧
    t.locals.lookup (ofString "count") = some (.val (.word w_cnt)) ∧
    ∃ wi : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word wi)) ∧ wi.toNat ≤ w_cnt.toNat
  have hinv_m9 : InvSp m9 := by
    refine ⟨?_, ?_, ⟨0#64, ?_, Nat.zero_le _⟩⟩
    · dsimp only [m9, m8]
      rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]
      exact hm7_arr
    · dsimp only [m9, m8]
      rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]
      exact hm7_cnt
    · dsimp only [m9, m8]
      rw [lookup_setVar_ne _ _ _ _ (by decide)]
      exact lookup_setVar_eq _ _ _
  refine worldEff_seq hnt9 hcr9
    (fun hnt_w hcr_w =>
      worldEff_while_cond_dhi _ InvSp (fun _ h => h)
        (fun t0 cw hcond hnz heff_t ⟨ht_arr, ht_cnt, wi, ht_i, hwi_le⟩ hnt_b hcr_b => ?_)
        m9.clock m9 rfl (heff7.locals_clock _ _) hinv_m9 hnt_w hcr_w)
    (fun m10 hm10 heff10 hnt10 hcr10 => ?_)
  · have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word wi)) := ht_i
    have ht0_cnt : t0.locals.lookup (ofString "count") = some (.val (.word w_cnt)) := ht_cnt
    have h2_30_63 : (2 : Nat) ^ 30 < 2 ^ 63 := by decide
    have hwi_lt : wi.toNat < w_cnt.toNat := by
      rw [evalHOLFinite_eq_toExact] at hcond
      simp only [evalHOLExact, evalListHOLExact, toExact, ht0_i, ht0_cnt,
        Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small wi w_cnt (by omega) (by omega)] at hcond
      by_cases hlt : wi.toNat < w_cnt.toNat
      · exact hlt
      · simp [hlt] at hcond; exact absurd hcond.symm hnz
    refine ⟨?_, fun hf => ?_⟩
    · refine worldEff_dec heff_t _ _ _ hnt_b hcr_b (fun v_o hv_o _ hnt_s1 hcr_s1 => ?_)
      obtain ⟨w_o, rfl, _⟩ := eval_le32_word_lt (decClockHOLFinite t0) _ _ _ _ v_o hv_o
      let u0 := setVarHOLFinite (ofString "o") (.val (.word w_o)) (decClockHOLFinite t0)
      refine worldEff_seq hnt_s1 hcr_s1
        (fun hnt_a hcr_a => worldEff_ite_ssz_fail (heff_t.locals_clock _ _) _ _ hnt_a hcr_a)
        (fun u1 hu1 heff_u1 hnt_s2 hcr_s2 => ?_)
      obtain ⟨hu1_eq, _⟩ := ite_ssz_fail_keeps u0 u1 heff_t.code _ _ hu1
      have hu1_arr : u1.locals.lookup (ofString "arr") = some (.val (.word w_arr)) := by
        rw [hu1_eq]; dsimp only [u0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact ht_arr
      have hu1_i : u1.locals.lookup (ofString "i") = some (.val (.word wi)) := by
        rw [hu1_eq]; dsimp only [u0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact ht_i
      refine worldEff_seq hnt_s2 hcr_s2
        (fun hnt_a hcr_a => worldEff_ite heff_u1 _ hnt_a hcr_a
          (fun cw_gt hcond_gt hnz_gt _ _ => ?_)
          (fun _ _ _ => worldEff_skip heff_u1))
        (fun u2 hu2 heff_u2 hnt_s3 hcr_s3 => ?_)
      · have hwi_pos : 0 < wi.toNat := by
          simp only [evalHOLExact, evalListHOLExact, toExact, hu1_i,
            Compiler.Encoders.Asm.wordCmpHOL,
            holAsmSignedLess_small 0#64 wi (by decide) (by omega),
            show (0#64 : BitVec 64).toNat = 0 from rfl] at hcond_gt
          by_cases hp : 0 < wi.toNat
          · exact hp
          · simp [hp] at hcond_gt; exact absurd hcond_gt.symm hnz_gt
        refine worldEff_store_word heff_u1 _ _ (eval_op_word u1 _ ⟨_, _, rfl⟩) (fun x hx _ => ?_)
        simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, hu1_arr, hu1_i,
          wordOpHOL, wordOp, valueIsWord, valueWord] at hx
        subst hx
        have hsub1 : (wi - 1#64).toNat = wi.toNat - 1 := by
          rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]
          rfl
        have hmul16 : ((wi - 1#64) * 16#64).toNat = (wi.toNat - 1) * 16 := by
          rw [BitVec.toNat_mul, hsub1, show (16#64 : BitVec 64).toNat = 16 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        have hadd_r : (((wi - 1#64) * 16#64) + 8#64).toNat = (wi.toNat - 1) * 16 + 8 := by
          rw [BitVec.toNat_add_of_lt]
          · rw [hmul16]; rfl
          · rw [hmul16]; change (wi.toNat - 1) * 16 + 8 < 2 ^ 64; omega
        have hx_nat : (w_arr + (((wi - 1#64) * 16#64) + 8#64)).toNat = w_arr.toNat + (wi.toNat - 1) * 16 + 8 := by
          rw [BitVec.toNat_add_of_lt] <;> omega
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
      · have hu2_arr : u2.locals.lookup (ofString "arr") = some (.val (.word w_arr)) := by
          have hk := evaluate_keepLocal (ofString "arr") _ (by decide) u1 (Or.inl (congrArg Prod.fst hu2))
          rw [hu2] at hk; rw [hk]; exact hu1_arr
        have hu2_i : u2.locals.lookup (ofString "i") = some (.val (.word wi)) := by
          have hk := evaluate_keepLocal (ofString "i") _ (by decide) u1 (Or.inl (congrArg Prod.fst hu2))
          rw [hu2] at hk; rw [hk]; exact hu1_i
        refine worldEff_seq hnt_s3 hcr_s3
          (fun _ _ => worldEff_store_word heff_u2 _ _ (eval_op_word u2 _ ⟨_, _, rfl⟩) (fun x hx _ => ?_))
          (fun u3 _ heff_u3 hnt_s4 hcr_s4 =>
            worldEff_seq hnt_s4 hcr_s4
              (fun _ _ => worldEff_assign_local heff_u3 _ _)
              (fun u4 _ heff_u4 _ _ => worldEff_assign_local heff_u4 _ _))
        simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, hu2_arr, hu2_i,
          wordOpHOL, wordOp, valueIsWord, valueWord] at hx
        subst hx
        have hmul16 : (wi * 16#64).toNat = wi.toNat * 16 := by
          rw [BitVec.toNat_mul, show (16#64 : BitVec 64).toNat = 16 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        have hx_nat : (w_arr + (wi * 16#64)).toNat = w_arr.toNat + wi.toNat * 16 := by
          rw [BitVec.toNat_add_of_lt] <;> omega
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
    · have hfl := flowing_of_none_or_continue hf
      refine ⟨?_, ?_, ?_⟩
      · rw [evaluate_keepLocal (ofString "arr") _ (by decide) _ hfl]; exact ht_arr
      · rw [evaluate_keepLocal (ofString "count") _ (by decide) _ hfl]; exact ht_cnt
      · exact evaluate_incTail_le (ofString "i") w_cnt.toNat (by omega) _ (by decide)
          (decClockHOLFinite t0) wi ht_i hwi_lt hf
  · have hm10_arr : m10.locals.lookup (ofString "arr") = some (.val (.word w_arr)) := by
      have hk := evaluate_keepLocal (ofString "arr") _ (by decide) _ (Or.inl (congrArg Prod.fst hm10))
      rw [hm10] at hk; rw [hk]; exact hinv_m9.1
    have hm10_cnt : m10.locals.lookup (ofString "count") = some (.val (.word w_cnt)) := by
      have hk := evaluate_keepLocal (ofString "count") _ (by decide) _ (Or.inl (congrArg Prod.fst hm10))
      rw [hm10] at hk; rw [hk]; exact hinv_m9.2.1
    refine worldEff_seq hnt10 hcr10
      (fun _ _ => worldEff_store_word heff10 _ _ (eval_op_word m10 _ ⟨_, _, rfl⟩) (fun x hx _ => ?_))
      (fun m11 _ heff11 _ _ => worldEff_return heff11 _)
    simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, hm10_arr, hm10_cnt,
      wordOpHOL, wordOp, valueIsWord, valueWord] at hx
    subst hx
    have hsub1 : (w_cnt - 1#64).toNat = w_cnt.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]
      rfl
    have hmul16 : ((w_cnt - 1#64) * 16#64).toNat = (w_cnt.toNat - 1) * 16 := by
      rw [BitVec.toNat_mul, hsub1, show (16#64 : BitVec 64).toNat = 16 from rfl,
        Nat.mod_eq_of_lt (by omega)]
    have hadd_r : (((w_cnt - 1#64) * 16#64) + 8#64).toNat = (w_cnt.toNat - 1) * 16 + 8 := by
      rw [BitVec.toNat_add_of_lt]
      · rw [hmul16]; rfl
      · rw [hmul16]; change (w_cnt.toNat - 1) * 16 + 8 < 2 ^ 64; omega
    have hx_nat : (w_arr + (((w_cnt - 1#64) * 16#64) + 8#64)).toNat = w_arr.toNat + (w_cnt.toNat - 1) * 16 + 8 := by
      rw [BitVec.toNat_add_of_lt] <;> omega
    exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))

private theorem eval_var_local_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : MlS) (w : BitVec 64) (hl : s.locals.lookup nm = some (.val (.word w))) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.var .local nm) = some v →
      ∃ w' : BitVec 64, v = .val (.word w') := by
  intro v hv; simp [evalHOLExact, toExact, hl] at hv; exact ⟨w, hv.symm⟩

private theorem worldEff_decode_bytes_list_body {F : Type}
    {s entry : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    (heff : WorldEff s entry Rl B dhiGw)
    (hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_bytes_list)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_bytes_list)).1) :
    WorldEff s (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_bytes_list)).2 Rl B dhiGw := by
  dsimp only [Guest.Software.guestFn_decode_bytes_list, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hcr ⊢
  refine worldEff_decCall_eff heff _ _ _ _ _ _ _ lookup_ssz_split_var_list
    (fun callee _ _ _ hnt_c hres_c => worldEff_ssz_split_var_list_body (heff.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
    (fun _ _ _ cp_dbl _ _ _ _ heff_cp hnt_k hcr_k => ?_) hnt hcr
  refine worldEff_dec (heff_cp.locals_clock _ _) _ _ _ hnt_k hcr_k (fun _ _ _ hnt1 hcr1 => ?_)
  refine worldEff_seq hnt1 hcr1
    (fun hnt_w hcr_w => ?_)
    (fun m_end _ heff_end _ _ => worldEff_return heff_end _)
  exact worldEff_while _ (fun _ => True) (fun _ _ => trivial)
    (fun t0 heff_t _ hnt_b hcr_b =>
      ⟨worldEff_seq hnt_b hcr_b
        (fun hnt_i hcr_i => worldEff_ite_ssz_fail heff_t _ _ hnt_i hcr_i)
        (fun tb _ heff_tb _ _ => worldEff_assign_local heff_tb _ _),
       fun _ => trivial⟩)
    _ _ rfl (heff_cp.locals_clock _ _) trivial hnt_w hcr_w

private theorem worldEff_decode_payload_body {F : Type}
    {s entry : PanSemStateFiniteExact 64 F} {B : List (String × Nat)} {wp wlen : BitVec 64}
    (hWOK : WorldOK s)
    (heff : WorldEff s entry (dhiOffsRegions s) B dhiGw)
    (hp : entry.locals.lookup (ofString "p") = some (.val (.word wp)))
    (hlen : entry.locals.lookup (ofString "len") = some (.val (.word wlen)))
    (hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_payload)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_payload)).1) :
    WorldEff s (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_payload)).2 (dhiOffsRegions s) B dhiGw := by
  dsimp only [Guest.Software.guestFn_decode_payload, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hcr ⊢
  refine worldEff_seq hnt hcr
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail heff _ _ hnt_a hcr_a)
    (fun m1 hm1 heff1 hnt1 hcr1 => ?_)
  obtain ⟨hm1_eq, _⟩ := ite_ssz_fail_keeps entry m1 heff.code _ _ hm1
  have hm1_p : m1.locals.lookup (ofString "p") = some (.val (.word wp)) := by rw [hm1_eq]; exact hp
  have hm1_len : m1.locals.lookup (ofString "len") = some (.val (.word wlen)) := by rw [hm1_eq]; exact hlen
  refine worldEff_decCall_alloc_const heff1 (ofString "pl") 136 (by rfl) (by decide) hnt1 hcr1
    (fun w_pl m2 hm2_loc heff_cp _ hpl_lo hpl_hi _ hnt2 hcr2 => ?_)
  have hm2_pl : m2.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm2_p : m2.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_p,
      show ofString "pl" ≠ ofString "p" by decide]
  have hm2_len : m2.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hm2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm1_len,
      show ofString "pl" ≠ ofString "len" by decide]
  refine worldEff_seq_store_fresh heff_cp (ofString "pl") w_pl 136 0 hm2_pl hpl_lo hpl_hi (by omega) _
    (eval_var_local_word m2 _ wp hm2_p) hnt2 hcr2 (fun m3 hm3_loc heff3 hnt3 hcr3 => ?_)
  refine worldEff_seq_store_fresh heff3 (ofString "pl") w_pl 136 8 (by rw [hm3_loc]; exact hm2_pl) hpl_lo hpl_hi (by omega) _
    (eval_var_local_word m3 _ wlen (by rw [hm3_loc]; exact hm2_len)) hnt3 hcr3 (fun m4 hm4_loc heff4 hnt4 hcr4 => ?_)
  have hm4_pl : m4.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by rw [hm4_loc, hm3_loc]; exact hm2_pl
  refine worldEff_dec heff4 _ _ _ hnt4 hcr4 (fun v_oex hv_oex _ hnt5 hcr5 => ?_)
  obtain ⟨w_oex, rfl, _⟩ := eval_le32_word_lt m4 _ _ _ _ v_oex hv_oex
  let m5 := setVarHOLFinite (ofString "o_extra") (.val (.word w_oex)) m4
  refine worldEff_dec (heff4.locals_clock _ _) _ _ _ hnt5 hcr5 (fun v_otx hv_otx _ hnt6 hcr6 => ?_)
  obtain ⟨w_otx, rfl, _⟩ := eval_le32_word_lt m5 _ _ _ _ v_otx hv_otx
  let m6 := setVarHOLFinite (ofString "o_txs") (.val (.word w_otx)) m5
  refine worldEff_dec (heff4.locals_clock _ _) _ _ _ hnt6 hcr6 (fun v_owd hv_owd _ hnt7 hcr7 => ?_)
  obtain ⟨w_owd, rfl, _⟩ := eval_le32_word_lt m6 _ _ _ _ v_owd hv_owd
  let m7 := setVarHOLFinite (ofString "o_wd") (.val (.word w_owd)) m6
  refine worldEff_dec (heff4.locals_clock _ _) _ _ _ hnt7 hcr7 (fun v_obl hv_obl _ hnt8 hcr8 => ?_)
  obtain ⟨w_obl, rfl, _⟩ := eval_le32_word_lt m7 _ _ _ _ v_obl hv_obl
  let m8 := setVarHOLFinite (ofString "o_bal") (.val (.word w_obl)) m7
  have hm8_pl : m8.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    dsimp only [m8, m7, m6, m5]
    iterate 4 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm4_pl
  have hm8_oex : m8.locals.lookup (ofString "o_extra") = some (.val (.word w_oex)) := by
    dsimp only [m8, m7, m6, m5]
    iterate 3 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hm8_otx : m8.locals.lookup (ofString "o_txs") = some (.val (.word w_otx)) := by
    dsimp only [m8, m7, m6]
    iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hm8_owd : m8.locals.lookup (ofString "o_wd") = some (.val (.word w_owd)) := by
    dsimp only [m8, m7]
    rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hm8_obl : m8.locals.lookup (ofString "o_bal") = some (.val (.word w_obl)) := lookup_setVar_eq _ _ _
  refine worldEff_seq_store_ssz_offs_const hWOK (heff4.locals_clock _ _) 0 (by omega) _ _ (Or.inl ⟨rfl, rfl⟩)
    (eval_var_local_word m8 _ w_oex hm8_oex) hnt8 hcr8 (fun m9 hm9_loc heff9 hnt9 hcr9 => ?_)
  refine worldEff_seq_store_ssz_offs_const hWOK heff9 8 (by omega) _ _ (Or.inr rfl)
    (eval_var_local_word m9 _ w_otx (by rw [hm9_loc]; exact hm8_otx)) hnt9 hcr9 (fun m10 hm10_loc heff10 hnt10 hcr10 => ?_)
  refine worldEff_seq_store_ssz_offs_const hWOK heff10 16 (by omega) _ _ (Or.inr rfl)
    (eval_var_local_word m10 _ w_owd (by rw [hm10_loc, hm9_loc]; exact hm8_owd)) hnt10 hcr10 (fun m11 hm11_loc heff11 hnt11 hcr11 => ?_)
  refine worldEff_seq_store_ssz_offs_const hWOK heff11 24 (by omega) _ _ (Or.inr rfl)
    (eval_var_local_word m11 _ w_obl (by rw [hm11_loc, hm10_loc, hm9_loc]; exact hm8_obl)) hnt11 hcr11 (fun m12 hm12_loc heff12 hnt12 hcr12 => ?_)
  have hm12_pl : m12.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    rw [hm12_loc, hm11_loc, hm10_loc, hm9_loc]; exact hm8_pl
  refine worldEff_seq hnt12 hcr12
    (fun hnt_a hcr_a => worldEff_call0_ro heff12 ro_ssz_check_offsets_local _ hnt_a hcr_a)
    (fun m13 hm13 heff13 hnt13 hcr13 => ?_)
  have hm13_pl : m13.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    have hk := evaluate_keepLocal (ofString "pl") _ (by decide) m12 (Or.inl (congrArg Prod.fst hm13))
    rw [hm13] at hk; rw [hk]; exact hm12_pl
  refine worldEff_seq hnt13 hcr13
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail heff13 _ _ hnt_a hcr_a)
    (fun m14 hm14 heff14 hnt14 hcr14 => ?_)
  obtain ⟨hm14_eq, _⟩ := ite_ssz_fail_keeps m13 m14 heff13.code _ _ hm14
  have hm14_pl : m14.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by rw [hm14_eq]; exact hm13_pl
  refine worldEff_seq_store_fresh heff14 (ofString "pl") w_pl 136 16 hm14_pl hpl_lo hpl_hi (by omega) _
    (eval_op_word m14 _ ⟨_, _, rfl⟩) hnt14 hcr14 (fun m15 hm15_loc heff15 hnt15 hcr15 => ?_)
  refine worldEff_seq_store_fresh heff15 (ofString "pl") w_pl 136 24 (by rw [hm15_loc]; exact hm14_pl) hpl_lo hpl_hi (by omega) _
    (eval_op_word m15 _ ⟨_, _, rfl⟩) hnt15 hcr15 (fun m16 hm16_loc heff16 hnt16 hcr16 => ?_)
  have hm16_pl : m16.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by rw [hm16_loc, hm15_loc]; exact hm14_pl
  refine worldEff_decCall_eff heff16 _ _ _ _ _ _ _ lookup_ssz_split_var_list
    (fun callee _ _ _ hnt_c hres_c => worldEff_ssz_split_var_list_body (heff16.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
    (fun _ _ rv_txs cpost_txs _ _ _ hsh_txs heff_txs hnt17 hcr17 => ?_) hnt16 hcr16
  obtain ⟨w_txp, w_ntx, rfl⟩ := shape_two_words_dhi rv_txs hsh_txs
  let m17 := setVarHOLFinite (ofString "txs") (.rStruct [.val (.word w_txp), .val (.word w_ntx)]) { cpost_txs with locals := m16.locals }
  have hm17_txs : m17.locals.lookup (ofString "txs") = some (.rStruct [.val (.word w_txp), .val (.word w_ntx)]) :=
    lookup_setVar_eq _ _ _
  have hm17_pl : m17.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    dsimp only [m17]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm16_pl
  refine worldEff_seq_store_fresh (heff_txs.locals_clock _ _) (ofString "pl") w_pl 136 32 hm17_pl hpl_lo hpl_hi (by omega) _
    (eval_rfield_word m17 0 _ w_txp w_ntx hm17_txs (Or.inl rfl)) hnt17 hcr17 (fun m18 hm18_loc heff18 hnt18 hcr18 => ?_)
  refine worldEff_seq_store_fresh heff18 (ofString "pl") w_pl 136 40 (by rw [hm18_loc]; exact hm17_pl) hpl_lo hpl_hi (by omega) _
    (eval_rfield_word m18 1 _ w_txp w_ntx (by rw [hm18_loc]; exact hm17_txs) (Or.inr rfl)) hnt18 hcr18 (fun m19 hm19_loc heff19 hnt19 hcr19 => ?_)
  have hm19_pl : m19.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by rw [hm19_loc, hm18_loc]; exact hm17_pl
  refine worldEff_decCall_ro heff19 ro_ssz_fixed_list_count _ _ _ hnt19 hcr19
    (fun rv_nwd cpost_nwd hsh_nwd hcp_eq hnt20 hcr20 => ?_)
  obtain ⟨w_nwd, rfl⟩ := val_word_of_shapeEq_one hsh_nwd
  have heff_nwd : WorldEff s (setVarHOLFinite (ofString "nwd") (.val (.word w_nwd)) { cpost_nwd with locals := m19.locals }) (dhiOffsRegions s) B dhiGw := by
    rw [hcp_eq]; exact heff19.locals_clock _ _
  let m20 := setVarHOLFinite (ofString "nwd") (.val (.word w_nwd)) { cpost_nwd with locals := m19.locals }
  have hm20_nwd : m20.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) := lookup_setVar_eq _ _ _
  have hm20_pl : m20.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    dsimp only [m20]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm19_pl
  refine worldEff_seq_store_fresh heff_nwd (ofString "pl") w_pl 136 48 hm20_pl hpl_lo hpl_hi (by omega) _
    (eval_op_word m20 _ ⟨_, _, rfl⟩) hnt20 hcr20 (fun m21 hm21_loc heff21 hnt21 hcr21 => ?_)
  refine worldEff_seq_store_fresh heff21 (ofString "pl") w_pl 136 56 (by rw [hm21_loc]; exact hm20_pl) hpl_lo hpl_hi (by omega) _
    (eval_var_local_word m21 _ w_nwd (by rw [hm21_loc]; exact hm20_nwd)) hnt21 hcr21 (fun m22 hm22_loc heff22 hnt22 hcr22 => ?_)
  have hm22_pl : m22.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by rw [hm22_loc, hm21_loc]; exact hm20_pl
  refine worldEff_seq_store_fresh heff22 (ofString "pl") w_pl 136 64 hm22_pl hpl_lo hpl_hi (by omega) _
    (eval_op_word m22 _ ⟨_, _, rfl⟩) hnt22 hcr22 (fun m23 hm23_loc heff23 hnt23 hcr23 => ?_)
  refine worldEff_seq_store_fresh heff23 (ofString "pl") w_pl 136 72 (by rw [hm23_loc]; exact hm22_pl) hpl_lo hpl_hi (by omega) _
    (eval_op_word m23 _ ⟨_, _, rfl⟩) hnt23 hcr23 (fun m24 hm24_loc heff24 hnt24 hcr24 => ?_)
  have hm24_pl : m24.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by rw [hm24_loc, hm23_loc]; exact hm22_pl
  refine worldEff_seq_store_fresh heff24 (ofString "pl") w_pl 136 80 hm24_pl hpl_lo hpl_hi (by omega) _
    (eval_op_word m24 _ ⟨_, _, rfl⟩) hnt24 hcr24 (fun m25 hm25_loc heff25 hnt25 hcr25 => ?_)
  refine worldEff_seq_store_fresh heff25 (ofString "pl") w_pl 136 88 (by rw [hm25_loc]; exact hm24_pl) hpl_lo hpl_hi (by omega) _
    (eval_op_word m25 _ ⟨_, _, rfl⟩) hnt25 hcr25 (fun m26 hm26_loc heff26 hnt26 hcr26 => ?_)
  refine worldEff_seq_store_fresh heff26 (ofString "pl") w_pl 136 96 (by rw [hm26_loc, hm25_loc]; exact hm24_pl) hpl_lo hpl_hi (by omega) _
    (eval_op_word m26 _ ⟨_, _, rfl⟩) hnt26 hcr26 (fun m27 hm27_loc heff27 hnt27 hcr27 => ?_)
  refine worldEff_seq_store_fresh heff27 (ofString "pl") w_pl 136 104 (by rw [hm27_loc, hm26_loc, hm25_loc]; exact hm24_pl) hpl_lo hpl_hi (by omega) _
    (eval_op_word m27 _ ⟨_, _, rfl⟩) hnt27 hcr27 (fun m28 hm28_loc heff28 hnt28 hcr28 => ?_)
  refine worldEff_seq_store_fresh heff28 (ofString "pl") w_pl 136 112 (by rw [hm28_loc, hm27_loc, hm26_loc, hm25_loc]; exact hm24_pl) hpl_lo hpl_hi (by omega) _
    (eval_op_word m28 _ ⟨_, _, rfl⟩) hnt28 hcr28 (fun m29 hm29_loc heff29 hnt29 hcr29 => ?_)
  refine worldEff_seq_store_fresh heff29 (ofString "pl") w_pl 136 120 (by rw [hm29_loc, hm28_loc, hm27_loc, hm26_loc, hm25_loc]; exact hm24_pl) hpl_lo hpl_hi (by omega) _
    (eval_op_word m29 _ ⟨_, _, rfl⟩) hnt29 hcr29 (fun m30 hm30_loc heff30 hnt30 hcr30 => ?_)
  refine worldEff_seq_store_fresh heff30 (ofString "pl") w_pl 136 128 (by rw [hm30_loc, hm29_loc, hm28_loc, hm27_loc, hm26_loc, hm25_loc]; exact hm24_pl) hpl_lo hpl_hi (by omega) _
    (eval_op_word m30 _ ⟨_, _, rfl⟩) hnt30 hcr30 (fun m31 _ heff31 _ _ => worldEff_return heff31 _)

private theorem worldEff_decode_requests_body {F : Type}
    {s entry : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hWOK : WorldOK s)
    (heff : WorldEff s entry (dhiOffsRegions s) B dhiGw)
    (hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_requests)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_requests)).1) :
    WorldEff s (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_requests)).2 (dhiOffsRegions s) B dhiGw := by
  dsimp only [Guest.Software.guestFn_decode_requests, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hcr ⊢
  refine worldEff_seq hnt hcr
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail heff _ _ hnt_a hcr_a)
    (fun m1 _ heff1 hnt1 hcr1 => ?_)
  refine worldEff_dec heff1 _ _ _ hnt1 hcr1 (fun v_i hv_i _ hnt2 hcr2 => ?_)
  have hv_i_eq : v_i = .val (.word 0#64) := by
    simp [evalHOLExact] at hv_i; exact hv_i.symm
  subst hv_i_eq
  let m2 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) m1
  let Inv : PanSemStateFiniteExact 64 F → Prop :=
    fun t => ∃ wi : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word wi)) ∧ wi.toNat ≤ 5
  refine worldEff_seq hnt2 hcr2
    (fun hnt_w hcr_w =>
      worldEff_while_cond_dhi _ Inv (fun _ h => h)
        (fun t0 cw hcond hnz heff_t ⟨wi, ht_i, hwi_le⟩ hnt_b hcr_b => ?_)
        m2.clock m2 rfl (heff1.locals_clock _ _) ⟨0#64, lookup_setVar_eq _ _ _, by decide⟩ hnt_w hcr_w)
    (fun m3 _ heff3 hnt3 hcr3 => ?_)
  · have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word wi)) := ht_i
    have h5_63 : 5 < (2 : Nat) ^ 63 := by decide
    have hwi_lt : wi.toNat < 5 := by
      rw [evalHOLFinite_eq_toExact] at hcond
      simp only [evalHOLExact, evalListHOLExact, toExact, ht0_i,
        Compiler.Encoders.Asm.wordCmpHOL,
        holAsmSignedLess_small wi 5#64 (by omega) (by decide)] at hcond
      by_cases hlt : wi.toNat < 5
      · exact hlt
      · have h5 : (5#64 : BitVec 64).toNat = 5 := rfl
        simp [h5, hlt] at hcond; exact absurd hcond.symm hnz
    have hoff_eq : (wi * 8#64).toNat = wi.toNat * 8 := by
      rw [BitVec.toNat_mul, show (8#64 : BitVec 64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
    refine ⟨?_, fun hf => ?_⟩
    · refine worldEff_seq hnt_b hcr_b
        (fun _ _ => worldEff_store_ssz_offs_dyn hWOK heff_t _ _ (wi * 8#64)
          (by simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, decClockHOLFinite, ht0_i, valueIsWord, valueWord])
          (by omega) (eval_op_word (decClockHOLFinite t0) _ ⟨_, _, rfl⟩))
        (fun tb _ heff_tb _ _ => worldEff_assign_local heff_tb _ _)
    · exact evaluate_incTail_le (ofString "i") 5 (by decide) _ (by decide) (decClockHOLFinite t0) wi ht_i hwi_lt hf
  · refine worldEff_seq hnt3 hcr3
      (fun hnt_a hcr_a => worldEff_call0_ro heff3 ro_ssz_check_offsets_local _ hnt_a hcr_a)
      (fun m4 _ heff4 hnt4 hcr4 => ?_)
    refine worldEff_decCall_alloc_const heff4 (ofString "rq") 80 (by rfl) (by decide) hnt4 hcr4
      (fun w_rq m5 hm5_loc heff_cp _ hrq_lo hrq_hi _ hnt5 hcr5 => ?_)
    have hm5_rq : m5.locals.lookup (ofString "rq") = some (.val (.word w_rq)) := by
      rw [hm5_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    refine worldEff_dec heff_cp _ _ _ hnt5 hcr5 (fun v_o0 hv_o0 _ hnt6 hcr6 => ?_)
    obtain ⟨w_o0, rfl⟩ := eval_load_one_word m5 _ v_o0 hv_o0
    let m6 := setVarHOLFinite (ofString "o0") (.val (.word w_o0)) m5
    refine worldEff_dec (heff_cp.locals_clock _ _) _ _ _ hnt6 hcr6 (fun v_o1 hv_o1 _ hnt7 hcr7 => ?_)
    obtain ⟨w_o1, rfl⟩ := eval_load_one_word m6 _ v_o1 hv_o1
    let m7 := setVarHOLFinite (ofString "o1") (.val (.word w_o1)) m6
    refine worldEff_dec (heff_cp.locals_clock _ _) _ _ _ hnt7 hcr7 (fun v_o2 hv_o2 _ hnt8 hcr8 => ?_)
    obtain ⟨w_o2, rfl⟩ := eval_load_one_word m7 _ v_o2 hv_o2
    let m8 := setVarHOLFinite (ofString "o2") (.val (.word w_o2)) m7
    refine worldEff_dec (heff_cp.locals_clock _ _) _ _ _ hnt8 hcr8 (fun v_o3 hv_o3 _ hnt9 hcr9 => ?_)
    obtain ⟨w_o3, rfl⟩ := eval_load_one_word m8 _ v_o3 hv_o3
    let m9 := setVarHOLFinite (ofString "o3") (.val (.word w_o3)) m8
    refine worldEff_dec (heff_cp.locals_clock _ _) _ _ _ hnt9 hcr9 (fun v_o4 hv_o4 _ hnt10 hcr10 => ?_)
    obtain ⟨w_o4, rfl⟩ := eval_load_one_word m9 _ v_o4 hv_o4
    let m10 := setVarHOLFinite (ofString "o4") (.val (.word w_o4)) m9
    have hm10_rq : m10.locals.lookup (ofString "rq") = some (.val (.word w_rq)) := by
      dsimp only [m10, m9, m8, m7, m6]
      iterate 5 rw [lookup_setVar_ne _ _ _ _ (by decide)]
      exact hm5_rq
    refine worldEff_decCall_ro (heff_cp.locals_clock _ _) ro_ssz_fixed_list_count _ _ _ hnt10 hcr10
      (fun rv_n0 cp0 hsh0 hcp0 hnt11 hcr11 => ?_)
    obtain ⟨w_n0, rfl⟩ := val_word_of_shapeEq_one hsh0
    have heff_n0 : WorldEff s (setVarHOLFinite (ofString "n0") (.val (.word w_n0)) { cp0 with locals := m10.locals }) (dhiOffsRegions s) B dhiGw := by
      rw [hcp0]; exact heff_cp.locals_clock _ _
    let m11 := setVarHOLFinite (ofString "n0") (.val (.word w_n0)) { cp0 with locals := m10.locals }
    refine worldEff_decCall_ro heff_n0 ro_ssz_fixed_list_count _ _ _ hnt11 hcr11
      (fun rv_n1 cp1 hsh1 hcp1 hnt12 hcr12 => ?_)
    obtain ⟨w_n1, rfl⟩ := val_word_of_shapeEq_one hsh1
    have heff_n1 : WorldEff s (setVarHOLFinite (ofString "n1") (.val (.word w_n1)) { cp1 with locals := m11.locals }) (dhiOffsRegions s) B dhiGw := by
      rw [hcp1]; exact heff_n0.locals_clock _ _
    let m12 := setVarHOLFinite (ofString "n1") (.val (.word w_n1)) { cp1 with locals := m11.locals }
    refine worldEff_decCall_ro heff_n1 ro_ssz_fixed_list_count _ _ _ hnt12 hcr12
      (fun rv_n2 cp2 hsh2 hcp2 hnt13 hcr13 => ?_)
    obtain ⟨w_n2, rfl⟩ := val_word_of_shapeEq_one hsh2
    have heff_n2 : WorldEff s (setVarHOLFinite (ofString "n2") (.val (.word w_n2)) { cp2 with locals := m12.locals }) (dhiOffsRegions s) B dhiGw := by
      rw [hcp2]; exact heff_n1.locals_clock _ _
    let m13 := setVarHOLFinite (ofString "n2") (.val (.word w_n2)) { cp2 with locals := m12.locals }
    refine worldEff_decCall_ro heff_n2 ro_ssz_fixed_list_count _ _ _ hnt13 hcr13
      (fun rv_n3 cp3 hsh3 hcp3 hnt14 hcr14 => ?_)
    obtain ⟨w_n3, rfl⟩ := val_word_of_shapeEq_one hsh3
    have heff_n3 : WorldEff s (setVarHOLFinite (ofString "n3") (.val (.word w_n3)) { cp3 with locals := m13.locals }) (dhiOffsRegions s) B dhiGw := by
      rw [hcp3]; exact heff_n2.locals_clock _ _
    let m14 := setVarHOLFinite (ofString "n3") (.val (.word w_n3)) { cp3 with locals := m13.locals }
    refine worldEff_decCall_ro heff_n3 ro_ssz_fixed_list_count _ _ _ hnt14 hcr14
      (fun rv_n4 cp4 hsh4 hcp4 hnt15 hcr15 => ?_)
    obtain ⟨w_n4, rfl⟩ := val_word_of_shapeEq_one hsh4
    have heff_n4 : WorldEff s (setVarHOLFinite (ofString "n4") (.val (.word w_n4)) { cp4 with locals := m14.locals }) (dhiOffsRegions s) B dhiGw := by
      rw [hcp4]; exact heff_n3.locals_clock _ _
    let m15 := setVarHOLFinite (ofString "n4") (.val (.word w_n4)) { cp4 with locals := m14.locals }
    have hm15_rq : m15.locals.lookup (ofString "rq") = some (.val (.word w_rq)) := by
      dsimp only [m15, m14, m13, m12, m11]
      iterate 5 rw [lookup_setVar_ne _ _ _ _ (by decide)]
      exact hm10_rq
    have hm15_n0 : m15.locals.lookup (ofString "n0") = some (.val (.word w_n0)) := by
      dsimp only [m15, m14, m13, m12, m11]
      iterate 4 rw [lookup_setVar_ne _ _ _ _ (by decide)]
      exact lookup_setVar_eq _ _ _
    have hm15_n1 : m15.locals.lookup (ofString "n1") = some (.val (.word w_n1)) := by
      dsimp only [m15, m14, m13, m12]
      iterate 3 rw [lookup_setVar_ne _ _ _ _ (by decide)]
      exact lookup_setVar_eq _ _ _
    have hm15_n2 : m15.locals.lookup (ofString "n2") = some (.val (.word w_n2)) := by
      dsimp only [m15, m14, m13]
      iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
      exact lookup_setVar_eq _ _ _
    have hm15_n3 : m15.locals.lookup (ofString "n3") = some (.val (.word w_n3)) := by
      dsimp only [m15, m14]
      rw [lookup_setVar_ne _ _ _ _ (by decide)]
      exact lookup_setVar_eq _ _ _
    have hm15_n4 : m15.locals.lookup (ofString "n4") = some (.val (.word w_n4)) := lookup_setVar_eq _ _ _
    refine worldEff_seq_store_fresh heff_n4 (ofString "rq") w_rq 80 0 hm15_rq hrq_lo hrq_hi (by omega) _
      (eval_op_word m15 _ ⟨_, _, rfl⟩) hnt15 hcr15 (fun s1 hl1 he1 hnt_1 hcr_1 => ?_)
    refine worldEff_seq_store_fresh he1 (ofString "rq") w_rq 80 8 (by rw [hl1]; exact hm15_rq) hrq_lo hrq_hi (by omega) _
      (eval_var_local_word s1 _ w_n0 (by rw [hl1]; exact hm15_n0)) hnt_1 hcr_1 (fun s2 hl2 he2 hnt_2 hcr_2 => ?_)
    refine worldEff_seq_store_fresh he2 (ofString "rq") w_rq 80 16 (by rw [hl2, hl1]; exact hm15_rq) hrq_lo hrq_hi (by omega) _
      (eval_op_word s2 _ ⟨_, _, rfl⟩) hnt_2 hcr_2 (fun s3 hl3 he3 hnt_3 hcr_3 => ?_)
    refine worldEff_seq_store_fresh he3 (ofString "rq") w_rq 80 24 (by rw [hl3, hl2, hl1]; exact hm15_rq) hrq_lo hrq_hi (by omega) _
      (eval_var_local_word s3 _ w_n1 (by rw [hl3, hl2, hl1]; exact hm15_n1)) hnt_3 hcr_3 (fun s4 hl4 he4 hnt_4 hcr_4 => ?_)
    refine worldEff_seq_store_fresh he4 (ofString "rq") w_rq 80 32 (by rw [hl4, hl3, hl2, hl1]; exact hm15_rq) hrq_lo hrq_hi (by omega) _
      (eval_op_word s4 _ ⟨_, _, rfl⟩) hnt_4 hcr_4 (fun s5 hl5 he5 hnt_5 hcr_5 => ?_)
    refine worldEff_seq_store_fresh he5 (ofString "rq") w_rq 80 40 (by rw [hl5, hl4, hl3, hl2, hl1]; exact hm15_rq) hrq_lo hrq_hi (by omega) _
      (eval_var_local_word s5 _ w_n2 (by rw [hl5, hl4, hl3, hl2, hl1]; exact hm15_n2)) hnt_5 hcr_5 (fun s6 hl6 he6 hnt_6 hcr_6 => ?_)
    refine worldEff_seq_store_fresh he6 (ofString "rq") w_rq 80 48 (by rw [hl6, hl5, hl4, hl3, hl2, hl1]; exact hm15_rq) hrq_lo hrq_hi (by omega) _
      (eval_op_word s6 _ ⟨_, _, rfl⟩) hnt_6 hcr_6 (fun s7 hl7 he7 hnt_7 hcr_7 => ?_)
    refine worldEff_seq_store_fresh he7 (ofString "rq") w_rq 80 56 (by rw [hl7, hl6, hl5, hl4, hl3, hl2, hl1]; exact hm15_rq) hrq_lo hrq_hi (by omega) _
      (eval_var_local_word s7 _ w_n3 (by rw [hl7, hl6, hl5, hl4, hl3, hl2, hl1]; exact hm15_n3)) hnt_7 hcr_7 (fun s8 hl8 he8 hnt_8 hcr_8 => ?_)
    refine worldEff_seq_store_fresh he8 (ofString "rq") w_rq 80 64 (by rw [hl8, hl7, hl6, hl5, hl4, hl3, hl2, hl1]; exact hm15_rq) hrq_lo hrq_hi (by omega) _
      (eval_op_word s8 _ ⟨_, _, rfl⟩) hnt_8 hcr_8 (fun s9 hl9 he9 hnt_9 hcr_9 => ?_)
    refine worldEff_seq_store_fresh he9 (ofString "rq") w_rq 80 72 (by rw [hl9, hl8, hl7, hl6, hl5, hl4, hl3, hl2, hl1]; exact hm15_rq) hrq_lo hrq_hi (by omega) _
      (eval_var_local_word s9 _ w_n4 (by rw [hl9, hl8, hl7, hl6, hl5, hl4, hl3, hl2, hl1]; exact hm15_n4)) hnt_9 hcr_9 (fun s10 _ he10 _ _ => worldEff_return he10 _)

private theorem worldEff_decode_stateless_input_body {F : Type}
    {s entry : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hWOK : WorldOK s)
    (heff : WorldEff s entry (dhiOffsRegions s) B dhiGw)
    (hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_stateless_input)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_stateless_input)).1) :
    WorldEff s (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_stateless_input)).2 (dhiOffsRegions s) B dhiGw := by
  dsimp only [Guest.Software.guestFn_decode_stateless_input, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hcr ⊢
  refine worldEff_seq hnt hcr
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail heff _ _ hnt_a hcr_a)
    (fun m1 _ heff1 hnt1 hcr1 => ?_)
  refine worldEff_seq hnt1 hcr1
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail heff1 _ _ hnt_a hcr_a)
    (fun m2 _ heff2 hnt2 hcr2 => ?_)
  refine worldEff_seq hnt2 hcr2
    (fun _ _ => worldEff_assign_local heff2 _ _)
    (fun m3 _ heff3 hnt3 hcr3 => ?_)
  refine worldEff_seq hnt3 hcr3
    (fun _ _ => worldEff_assign_local heff3 _ _)
    (fun m4 _ heff4 hnt4 hcr4 => ?_)
  refine worldEff_seq hnt4 hcr4
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail heff4 _ _ hnt_a hcr_a)
    (fun m5 _ heff5 hnt5 hcr5 => ?_)
  refine worldEff_seq_store_ssz_offs_const hWOK heff5 0 (by omega) _ _ (Or.inl ⟨rfl, rfl⟩)
    (eval_op_word m5 _ ⟨_, _, rfl⟩) hnt5 hcr5 (fun m6 _ heff6 hnt6 hcr6 => ?_)
  refine worldEff_seq_store_ssz_offs_const hWOK heff6 8 (by omega) _ _ (Or.inr rfl)
    (eval_op_word m6 _ ⟨_, _, rfl⟩) hnt6 hcr6 (fun m7 _ heff7 hnt7 hcr7 => ?_)
  refine worldEff_seq hnt7 hcr7
    (fun hnt_a hcr_a => worldEff_call0_ro heff7 ro_ssz_check_offsets_local _ hnt_a hcr_a)
    (fun m8 _ heff8 hnt8 hcr8 => ?_)
  refine worldEff_dec heff8 _ _ _ hnt8 hcr8 (fun _ _ _ hnt9 hcr9 => ?_)
  refine worldEff_dec (heff8.locals_clock _ _) _ _ _ hnt9 hcr9 (fun _ _ _ hnt10 hcr10 => ?_)
  refine worldEff_decCall_alloc_const (heff8.locals_clock _ _) (ofString "si") 96 (by rfl) (by decide) hnt10 hcr10
    (fun w_si m11 hm11_loc heff_si _ hsi_lo hsi_hi _ hnt11 hcr11 => ?_)
  have hm11_si : m11.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    rw [hm11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine worldEff_seq_store_fresh heff_si (ofString "si") w_si 96 88 hm11_si hsi_lo hsi_hi (by omega) _
    (eval_op_word m11 _ ⟨_, _, rfl⟩) hnt11 hcr11 (fun m12 hm12_loc heff12 hnt12 hcr12 => ?_)
  have hm12_si : m12.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm12_loc]; exact hm11_si
  refine worldEff_dec heff12 _ _ _ hnt12 hcr12 (fun v_np _ _ hnt13 hcr13 => ?_)
  let m13 := setVarHOLFinite (ofString "np") v_np m12
  refine worldEff_dec (heff12.locals_clock _ _) _ _ _ hnt13 hcr13 (fun v_nlen _ _ hnt14 hcr14 => ?_)
  let m14 := setVarHOLFinite (ofString "nlen") v_nlen m13
  have hm14_si : m14.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    dsimp only [m14, m13]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm12_si
  refine worldEff_seq hnt14 hcr14
    (fun hnt_a hcr_a => worldEff_ite_ssz_fail (heff12.locals_clock _ _) _ _ hnt_a hcr_a)
    (fun m15 hm15 heff15 hnt15 hcr15 => ?_)
  obtain ⟨hm15_eq, _⟩ := ite_ssz_fail_keeps m14 m15 heff12.code _ _ hm15
  have hm15_si : m15.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm15_eq]; exact hm14_si
  refine worldEff_dec heff15 _ _ _ hnt15 hcr15 (fun v_opl hv_opl _ hnt16 hcr16 => ?_)
  obtain ⟨w_opl, rfl, _⟩ := eval_le32_word_lt m15 _ _ _ _ v_opl hv_opl
  let m16 := setVarHOLFinite (ofString "o_pl") (.val (.word w_opl)) m15
  refine worldEff_dec (heff15.locals_clock _ _) _ _ _ hnt16 hcr16 (fun v_ovh hv_ovh _ hnt17 hcr17 => ?_)
  obtain ⟨w_ovh, rfl, _⟩ := eval_le32_word_lt m16 _ _ _ _ v_ovh hv_ovh
  let m17 := setVarHOLFinite (ofString "o_vh") (.val (.word w_ovh)) m16
  refine worldEff_dec (heff15.locals_clock _ _) _ _ _ hnt17 hcr17 (fun v_orq hv_orq _ hnt18 hcr18 => ?_)
  obtain ⟨w_orq, rfl, _⟩ := eval_le32_word_lt m17 _ _ _ _ v_orq hv_orq
  let m18 := setVarHOLFinite (ofString "o_rq") (.val (.word w_orq)) m17
  have hm18_si : m18.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    dsimp only [m18, m17, m16]; iterate 3 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm15_si
  have hm18_opl : m18.locals.lookup (ofString "o_pl") = some (.val (.word w_opl)) := by
    dsimp only [m18, m17, m16]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hm18_ovh : m18.locals.lookup (ofString "o_vh") = some (.val (.word w_ovh)) := by
    dsimp only [m18, m17]; rw [lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hm18_orq : m18.locals.lookup (ofString "o_rq") = some (.val (.word w_orq)) := lookup_setVar_eq _ _ _
  refine worldEff_seq_store_ssz_offs_const hWOK (heff15.locals_clock _ _) 0 (by omega) _ _ (Or.inl ⟨rfl, rfl⟩)
    (eval_var_local_word m18 _ w_opl hm18_opl) hnt18 hcr18 (fun m19 hm19_loc heff19 hnt19 hcr19 => ?_)
  refine worldEff_seq_store_ssz_offs_const hWOK heff19 8 (by omega) _ _ (Or.inr rfl)
    (eval_var_local_word m19 _ w_ovh (by rw [hm19_loc]; exact hm18_ovh)) hnt19 hcr19 (fun m20 hm20_loc heff20 hnt20 hcr20 => ?_)
  refine worldEff_seq_store_ssz_offs_const hWOK heff20 16 (by omega) _ _ (Or.inr rfl)
    (eval_var_local_word m20 _ w_orq (by rw [hm20_loc, hm19_loc]; exact hm18_orq)) hnt20 hcr20 (fun m21 hm21_loc heff21 hnt21 hcr21 => ?_)
  have hm21_si : m21.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    rw [hm21_loc, hm20_loc, hm19_loc]; exact hm18_si
  refine worldEff_seq hnt21 hcr21
    (fun hnt_a hcr_a => worldEff_call0_ro heff21 ro_ssz_check_offsets_local _ hnt_a hcr_a)
    (fun m22 hm22 heff22 hnt22 hcr22 => ?_)
  have hm22_si : m22.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    have hk := evaluate_keepLocal (ofString "si") _ (by decide) m21 (Or.inl (congrArg Prod.fst hm22))
    rw [hm22] at hk; rw [hk]; exact hm21_si
  refine worldEff_decCall_eff heff22 _ _ _ _ _ _ _ lookup_decode_payload
    (fun callee vals _ hlook hnt_c hres_c => ?_)
    (fun _ _ rv_pl cp_pl _ _ _ hsh_pl heff_pl hnt23 hcr23 => ?_) hnt22 hcr22
  · obtain ⟨wp_c, wlen_c, _, hc_p, hc_len⟩ :=
      lookupCode_two_words (by decide) lookup_decode_payload (by rwa [heff22.code] at hlook)
    exact worldEff_decode_payload_body hWOK (heff22.locals_clock callee _) hc_p hc_len hnt_c (contOrRes_of_resumes_dhi hres_c)
  · obtain ⟨w_pl, rfl⟩ := val_word_of_shapeEq_one hsh_pl
    let m23 := setVarHOLFinite (ofString "pl") (.val (.word w_pl)) { cp_pl with locals := m22.locals }
    have hm23_pl : m23.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := lookup_setVar_eq _ _ _
    have hm23_si : m23.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
      dsimp only [m23]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm22_si
    refine worldEff_seq_store_fresh (heff_pl.locals_clock _ _) (ofString "si") w_si 96 0 hm23_si hsi_lo hsi_hi (by omega) _
      (eval_var_local_word m23 _ w_pl hm23_pl) hnt23 hcr23 (fun m24 hm24_loc heff24 hnt24 hcr24 => ?_)
    have hm24_si : m24.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm24_loc]; exact hm23_si
    refine worldEff_decCall_ro heff24 ro_ssz_fixed_list_count _ _ _ hnt24 hcr24
      (fun rv_nvh cp_nvh hsh_nvh hcp_nvh hnt25 hcr25 => ?_)
    obtain ⟨w_nvh, rfl⟩ := val_word_of_shapeEq_one hsh_nvh
    have heff_nvh : WorldEff s (setVarHOLFinite (ofString "nvh") (.val (.word w_nvh)) { cp_nvh with locals := m24.locals }) (dhiOffsRegions s) B dhiGw := by
      rw [hcp_nvh]; exact heff24.locals_clock _ _
    let m25 := setVarHOLFinite (ofString "nvh") (.val (.word w_nvh)) { cp_nvh with locals := m24.locals }
    have hm25_nvh : m25.locals.lookup (ofString "nvh") = some (.val (.word w_nvh)) := lookup_setVar_eq _ _ _
    have hm25_si : m25.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
      dsimp only [m25]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm24_si
    refine worldEff_seq_store_fresh heff_nvh (ofString "si") w_si 96 8 hm25_si hsi_lo hsi_hi (by omega) _
      (eval_op_word m25 _ ⟨_, _, rfl⟩) hnt25 hcr25 (fun m26 hm26_loc heff26 hnt26 hcr26 => ?_)
    refine worldEff_seq_store_fresh heff26 (ofString "si") w_si 96 16 (by rw [hm26_loc]; exact hm25_si) hsi_lo hsi_hi (by omega) _
      (eval_var_local_word m26 _ w_nvh (by rw [hm26_loc]; exact hm25_nvh)) hnt26 hcr26 (fun m27 hm27_loc heff27 hnt27 hcr27 => ?_)
    refine worldEff_seq_store_fresh heff27 (ofString "si") w_si 96 24 (by rw [hm27_loc, hm26_loc]; exact hm25_si) hsi_lo hsi_hi (by omega) _
      (eval_op_word m27 _ ⟨_, _, rfl⟩) hnt27 hcr27 (fun m28 hm28_loc heff28 hnt28 hcr28 => ?_)
    have hm28_si : m28.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
      rw [hm28_loc, hm27_loc, hm26_loc]; exact hm25_si
    refine worldEff_decCall_eff heff28 _ _ _ _ _ _ _ lookup_decode_requests
      (fun callee _ _ _ hnt_c hres_c => worldEff_decode_requests_body hWOK (heff28.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
      (fun _ _ rv_rq cp_rq _ _ _ hsh_rq heff_rq hnt29 hcr29 => ?_) hnt28 hcr28
    obtain ⟨w_rq, rfl⟩ := val_word_of_shapeEq_one hsh_rq
    let m29 := setVarHOLFinite (ofString "rq") (.val (.word w_rq)) { cp_rq with locals := m28.locals }
    have hm29_rq : m29.locals.lookup (ofString "rq") = some (.val (.word w_rq)) := lookup_setVar_eq _ _ _
    have hm29_si : m29.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
      dsimp only [m29]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm28_si
    refine worldEff_seq_store_fresh (heff_rq.locals_clock _ _) (ofString "si") w_si 96 32 hm29_si hsi_lo hsi_hi (by omega) _
      (eval_var_local_word m29 _ w_rq hm29_rq) hnt29 hcr29 (fun m30 hm30_loc heff30 hnt30 hcr30 => ?_)
    have hm30_si : m30.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm30_loc]; exact hm29_si
    refine worldEff_dec heff30 _ _ _ hnt30 hcr30 (fun v_wp _ _ hnt31 hcr31 => ?_)
    let m31 := setVarHOLFinite (ofString "wp") v_wp m30
    refine worldEff_dec (heff30.locals_clock _ _) _ _ _ hnt31 hcr31 (fun v_wlen _ _ hnt32 hcr32 => ?_)
    let m32 := setVarHOLFinite (ofString "wlen") v_wlen m31
    have hm32_si : m32.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
      dsimp only [m32, m31]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
      exact hm30_si
    refine worldEff_seq hnt32 hcr32
      (fun hnt_a hcr_a => worldEff_ite_ssz_fail (heff30.locals_clock _ _) _ _ hnt_a hcr_a)
      (fun m33 hm33 heff33 hnt33 hcr33 => ?_)
    obtain ⟨hm33_eq, _⟩ := ite_ssz_fail_keeps m32 m33 heff30.code _ _ hm33
    have hm33_si : m33.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm33_eq]; exact hm32_si
    refine worldEff_dec heff33 _ _ _ hnt33 hcr33 (fun v_i hv_i _ hnt34 hcr34 => ?_)
    have hv_i_eq : v_i = .val (.word 0#64) := by
      simp [evalHOLExact] at hv_i; exact hv_i.symm
    subst hv_i_eq
    let m34 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) m33
    have hm34_si : m34.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
      dsimp only [m34]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm33_si
    let Inv3 : PanSemStateFiniteExact 64 F → Prop :=
      fun t => ∃ wi : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word wi)) ∧ wi.toNat ≤ 3
    refine worldEff_seq hnt34 hcr34
      (fun hnt_w hcr_w =>
        worldEff_while_cond_dhi _ Inv3 (fun _ h => h)
          (fun t0 cw hcond hnz heff_t ⟨wi, ht_i, hwi_le⟩ hnt_b hcr_b => ?_)
          m34.clock m34 rfl (heff33.locals_clock _ _) ⟨0#64, lookup_setVar_eq _ _ _, by decide⟩ hnt_w hcr_w)
      (fun m35 hm35 heff35 hnt35 hcr35 => ?_)
    · have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word wi)) := ht_i
      have h3_63 : 3 < (2 : Nat) ^ 63 := by decide
      have hwi_lt : wi.toNat < 3 := by
        rw [evalHOLFinite_eq_toExact] at hcond
        simp only [evalHOLExact, evalListHOLExact, toExact, ht0_i,
          Compiler.Encoders.Asm.wordCmpHOL,
          holAsmSignedLess_small wi 3#64 (by omega) (by decide)] at hcond
        by_cases hlt : wi.toNat < 3
        · exact hlt
        · have h3 : (3#64 : BitVec 64).toNat = 3 := rfl
          simp [h3, hlt] at hcond; exact absurd hcond.symm hnz
      have hoff_eq : (wi * 8#64).toNat = wi.toNat * 8 := by
        rw [BitVec.toNat_mul, show (8#64 : BitVec 64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
      refine ⟨?_, fun hf => ?_⟩
      · refine worldEff_seq hnt_b hcr_b
          (fun _ _ => worldEff_store_ssz_offs_dyn hWOK heff_t _ _ (wi * 8#64)
            (by simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, decClockHOLFinite, ht0_i, valueIsWord, valueWord])
            (by omega) (eval_op_word (decClockHOLFinite t0) _ ⟨_, _, rfl⟩))
          (fun tb _ heff_tb _ _ => worldEff_assign_local heff_tb _ _)
      · exact evaluate_incTail_le (ofString "i") 3 (by decide) _ (by decide) (decClockHOLFinite t0) wi ht_i hwi_lt hf
    · have hm35_si : m35.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
        have hk := evaluate_keepLocal (ofString "si") _ (by decide) m34 (Or.inl (congrArg Prod.fst hm35))
        rw [hm35] at hk; rw [hk]; exact hm34_si
      refine worldEff_seq hnt35 hcr35
        (fun hnt_a hcr_a => worldEff_call0_ro heff35 ro_ssz_check_offsets_local _ hnt_a hcr_a)
        (fun m36 hm36 heff36 hnt36 hcr36 => ?_)
      have hm36_si : m36.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
        have hk := evaluate_keepLocal (ofString "si") _ (by decide) m35 (Or.inl (congrArg Prod.fst hm36))
        rw [hm36] at hk; rw [hk]; exact hm35_si
      refine worldEff_dec heff36 _ _ _ hnt36 hcr36 (fun v_w0 _ _ hnt37 hcr37 => ?_)
      let m37 := setVarHOLFinite (ofString "w0") v_w0 m36
      refine worldEff_dec (heff36.locals_clock _ _) _ _ _ hnt37 hcr37 (fun v_w1 _ _ hnt38 hcr38 => ?_)
      let m38 := setVarHOLFinite (ofString "w1") v_w1 m37
      refine worldEff_dec (heff36.locals_clock _ _) _ _ _ hnt38 hcr38 (fun v_w2 _ _ hnt39 hcr39 => ?_)
      let m39 := setVarHOLFinite (ofString "w2") v_w2 m38
      have hm39_si : m39.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
        dsimp only [m39, m38, m37]; iterate 3 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        exact hm36_si
      refine worldEff_decCall_eff (heff36.locals_clock _ _) _ _ _ _ _ _ _ lookup_decode_bytes_list
        (fun callee _ _ _ hnt_c hres_c => worldEff_decode_bytes_list_body (heff36.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
        (fun _ _ rv_st0 cp_st0 _ _ _ hsh_st0 heff_st0 hnt40 hcr40 => ?_) hnt39 hcr39
      obtain ⟨w_st0a, w_st0b, rfl⟩ := shape_two_words_dhi rv_st0 hsh_st0
      let m40 := setVarHOLFinite (ofString "st0") (.rStruct [.val (.word w_st0a), .val (.word w_st0b)]) { cp_st0 with locals := m39.locals }
      have hm40_st0 : m40.locals.lookup (ofString "st0") = some (.rStruct [.val (.word w_st0a), .val (.word w_st0b)]) := lookup_setVar_eq _ _ _
      have hm40_si : m40.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
        dsimp only [m40]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm39_si
      refine worldEff_seq_store_fresh (heff_st0.locals_clock _ _) (ofString "si") w_si 96 40 hm40_si hsi_lo hsi_hi (by omega) _
        (eval_rfield_word m40 0 _ w_st0a w_st0b hm40_st0 (Or.inl rfl)) hnt40 hcr40 (fun m41 hm41_loc heff41 hnt41 hcr41 => ?_)
      refine worldEff_seq_store_fresh heff41 (ofString "si") w_si 96 48 (by rw [hm41_loc]; exact hm40_si) hsi_lo hsi_hi (by omega) _
        (eval_rfield_word m41 1 _ w_st0a w_st0b (by rw [hm41_loc]; exact hm40_st0) (Or.inr rfl)) hnt41 hcr41 (fun m42 hm42_loc heff42 hnt42 hcr42 => ?_)
      have hm42_si : m42.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm42_loc, hm41_loc]; exact hm40_si
      refine worldEff_decCall_eff heff42 _ _ _ _ _ _ _ lookup_decode_bytes_list
        (fun callee _ _ _ hnt_c hres_c => worldEff_decode_bytes_list_body (heff42.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
        (fun _ _ rv_cd cp_cd _ _ _ hsh_cd heff_cd hnt43 hcr43 => ?_) hnt42 hcr42
      obtain ⟨w_cda, w_cdb, rfl⟩ := shape_two_words_dhi rv_cd hsh_cd
      let m43 := setVarHOLFinite (ofString "cd") (.rStruct [.val (.word w_cda), .val (.word w_cdb)]) { cp_cd with locals := m42.locals }
      have hm43_cd : m43.locals.lookup (ofString "cd") = some (.rStruct [.val (.word w_cda), .val (.word w_cdb)]) := lookup_setVar_eq _ _ _
      have hm43_si : m43.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
        dsimp only [m43]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm42_si
      refine worldEff_seq_store_fresh (heff_cd.locals_clock _ _) (ofString "si") w_si 96 56 hm43_si hsi_lo hsi_hi (by omega) _
        (eval_rfield_word m43 0 _ w_cda w_cdb hm43_cd (Or.inl rfl)) hnt43 hcr43 (fun m44 hm44_loc heff44 hnt44 hcr44 => ?_)
      refine worldEff_seq_store_fresh heff44 (ofString "si") w_si 96 64 (by rw [hm44_loc]; exact hm43_si) hsi_lo hsi_hi (by omega) _
        (eval_rfield_word m44 1 _ w_cda w_cdb (by rw [hm44_loc]; exact hm43_cd) (Or.inr rfl)) hnt44 hcr44 (fun m45 hm45_loc heff45 hnt45 hcr45 => ?_)
      have hm45_si : m45.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm45_loc, hm44_loc]; exact hm43_si
      refine worldEff_decCall_eff heff45 _ _ _ _ _ _ _ lookup_decode_bytes_list
        (fun callee _ _ _ hnt_c hres_c => worldEff_decode_bytes_list_body (heff45.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
        (fun _ _ rv_hd cp_hd _ _ _ hsh_hd heff_hd hnt46 hcr46 => ?_) hnt45 hcr45
      obtain ⟨w_hda, w_hdb, rfl⟩ := shape_two_words_dhi rv_hd hsh_hd
      let m46 := setVarHOLFinite (ofString "hd") (.rStruct [.val (.word w_hda), .val (.word w_hdb)]) { cp_hd with locals := m45.locals }
      have hm46_hd : m46.locals.lookup (ofString "hd") = some (.rStruct [.val (.word w_hda), .val (.word w_hdb)]) := lookup_setVar_eq _ _ _
      have hm46_si : m46.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
        dsimp only [m46]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm45_si
      refine worldEff_seq_store_fresh (heff_hd.locals_clock _ _) (ofString "si") w_si 96 72 hm46_si hsi_lo hsi_hi (by omega) _
        (eval_rfield_word m46 0 _ w_hda w_hdb hm46_hd (Or.inl rfl)) hnt46 hcr46 (fun m47 hm47_loc heff47 hnt47 hcr47 => ?_)
      refine worldEff_seq_store_fresh heff47 (ofString "si") w_si 96 80 (by rw [hm47_loc]; exact hm46_si) hsi_lo hsi_hi (by omega) _
        (eval_rfield_word m47 1 _ w_hda w_hdb (by rw [hm47_loc]; exact hm46_hd) (Or.inr rfl)) hnt47 hcr47 (fun m48 _ heff48 _ _ => worldEff_return heff48 _)

private theorem worldEff_decode_host_input_body {F : Type}
    {s entry : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hWOK : WorldOK s)
    (heff : WorldEff s entry (dhiOffsRegions s) B dhiGw)
    (hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_host_input)).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_host_input)).1) :
    WorldEff s (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_host_input)).2 (dhiOffsRegions s) B dhiGw := by
  dsimp only [Guest.Software.guestFn_decode_host_input, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hcr ⊢
  refine worldEff_seq hnt hcr
    (fun hnt_a hcr_a => worldEff_call0_eff heff _ _ _ _ _ lookup_precheck_host_ssz_header
      (fun callee _ _ _ hnt_c hres_c => worldEff_precheck_host_ssz_header_body hWOK (heff.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
      hnt_a hcr_a)
    (fun m1 _ heff1 hnt1 hcr1 => ?_)
  refine worldEff_decCall_eff heff1 _ _ _ _ _ _ _ lookup_input_blob
    (fun callee _ _ _ hnt_c hres_c => worldEff_input_blob_body (heff1.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
    (fun _ _ _ cp_inp _ _ _ _ heff_inp hnt2 hcr2 => ?_) hnt1 hcr1
  exact worldEff_tailCall_eff (heff_inp.locals_clock _ _) _ _ _ _ _ lookup_decode_stateless_input
    (fun callee _ _ _ hnt_c hres_c => worldEff_decode_stateless_input_body hWOK (heff_inp.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
    hnt2 hcr2

theorem wk_decode_host_input_noExtra :
    WorldKeeps WorldOK
      (fun s => [(globN s "ssz_offs", if globN s "ssz_offs" = 0 then 0 else 64)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]),
       ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "decode_host_input") := by
  refine ⟨_, _, _, lookup_decode_host_input, ?_⟩
  intro F s hc hWOK hl hnt hres
  have heff : WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input)).2
      (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw :=
    worldEff_decode_host_input_body hWOK
      (WorldEff.refl s (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw hWOK.1 hc)
      hnt (contOrRes_of_resumes_dhi hres)
  exact R16Shards.WorldEff.to_worldStep_Q (R := dhiOffsRegions)
    hWOK (by intro _ h; cases h)
    (by decide)
    heff (fun _ _ _ _ _ _ _ _ => trivial)


theorem lookup_ssz_fixed_list_count_dhi :
    originalRuntimeCode.lookup (ofString "ssz_fixed_list_count") =
      some ([(ofString "len", .one), (ofString "sz", .one), (ofString "lim", .one)],
        sourceFnBody Guest.Software.guestFn_ssz_fixed_list_count, .one) :=
  lookup_of_guestAst_getElem 203 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ssz_fixed_list_count) rfl

theorem ssz_offs_allocated_strong {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hWOK : WorldOK s) :
    globN s "ssz_offs" = 0 ∨
    Allocated s (globN s "ssz_offs", 64) := by
  obtain ⟨hAs, S, hWS⟩ := hWOK
  obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with s S).1 hWS
  have hmem : bufferRegion s ("ssz_offs", 64) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.2 ⟨("ssz_offs", 64), by decide, rfl⟩
  rcases hWT.2.2.1.1 _ hmem with hz | ⟨hal, _⟩
  · by_cases hg0 : globN s "ssz_offs" = 0
    · exact Or.inl hg0
    · simp [bufferRegion, hg0] at hz
  · by_cases hg0 : globN s "ssz_offs" = 0
    · exact Or.inl hg0
    · simp only [bufferRegion, hg0, ↓reduceIte] at hal
      exact Or.inr hal

theorem lookupCode_two_words_any_dhi
    {lk : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    {fname p1 p2 : MlS} {body : ProgHOL 64} {retShape : ShapeHOL}
    {vals : List (ValueHOL 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hne : p1 ≠ p2)
    (hlook : lk fname = some ([(p1, .one), (p2, .one)], body, retShape))
    (hl : lookupCodeHOLFinite lk fname vals = some (body, L, retShape)) :
    ∃ w1 w2 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) := by
  have hx := lookupCodeHOLFinite_eq_some lk fname vals body L retShape hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    refine ⟨w1, w2, rfl, ?_, ?_⟩ <;>
      (rw [← hL]; simp only [HolFiniteMapExact.lookup_updateList, HolFiniteMapExact.lookup_empty,
        FUPDATE_LIST, FUPDATE, List.foldl, hne, Ne.symm hne, ↓reduceIte])
  · simp at hx

theorem lookupCode_three_words_any_dhi
    {lk : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    {fname p1 p2 p3 : MlS} {body : ProgHOL 64} {retShape : ShapeHOL}
    {vals : List (ValueHOL 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hne12 : p1 ≠ p2) (hne13 : p1 ≠ p3) (hne23 : p2 ≠ p3)
    (hlook : lk fname = some ([(p1, .one), (p2, .one), (p3, .one)], body, retShape))
    (hl : lookupCodeHOLFinite lk fname vals = some (body, L, retShape)) :
    ∃ w1 w2 w3 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2), .val (.word w3)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) ∧
      L.lookup p3 = some (.val (.word w3)) := by
  have hx := lookupCodeHOLFinite_eq_some lk fname vals body L retShape hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;> rcases v3 with ⟨⟨w3⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    refine ⟨w1, w2, w3, rfl, ?_, ?_, ?_⟩ <;>
      (rw [← hL]; simp only [HolFiniteMapExact.lookup_updateList, HolFiniteMapExact.lookup_empty,
        FUPDATE_LIST, FUPDATE, List.foldl, hne12, hne13, hne23, Ne.symm hne12, Ne.symm hne13, Ne.symm hne23, ↓reduceIte])
  · simp at hx

theorem lookupCode_four_words_any_dhi
    {lk : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    {fname p1 p2 p3 p4 : MlS} {body : ProgHOL 64} {retShape : ShapeHOL}
    {vals : List (ValueHOL 64)} {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hne12 : p1 ≠ p2) (hne13 : p1 ≠ p3) (hne14 : p1 ≠ p4)
    (hne23 : p2 ≠ p3) (hne24 : p2 ≠ p4) (hne34 : p3 ≠ p4)
    (hlook : lk fname = some ([(p1, .one), (p2, .one), (p3, .one), (p4, .one)], body, retShape))
    (hl : lookupCodeHOLFinite lk fname vals = some (body, L, retShape)) :
    ∃ w1 w2 w3 w4 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) ∧
      L.lookup p3 = some (.val (.word w3)) ∧
      L.lookup p4 = some (.val (.word w4)) := by
  have hx := lookupCodeHOLFinite_eq_some lk fname vals body L retShape hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | _⟩⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      rcases v3 with ⟨⟨w3⟩⟩ | _ | _ <;> rcases v4 with ⟨⟨w4⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    refine ⟨w1, w2, w3, w4, rfl, ?_, ?_, ?_, ?_⟩ <;>
      (rw [← hL]; simp only [HolFiniteMapExact.lookup_updateList, HolFiniteMapExact.lookup_empty,
        FUPDATE_LIST, FUPDATE, List.foldl, hne12, hne13, hne14, hne23, hne24, hne34,
        Ne.symm hne12, Ne.symm hne13, Ne.symm hne14, Ne.symm hne23, Ne.symm hne24, Ne.symm hne34, ↓reduceIte])
  · simp at hx

theorem call0_noret_dhi {F : Type} (u : PanSemStateFiniteExact 64 F)
    (fn : MlS) (args : List (ExpHOL 64)) :
    ∀ rv, (evaluateHOLFiniteState u (.call (some (none, none)) fn args)).1 ≠ some (.returned rv) := by
  intro rv
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args with _ | vals
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite u.code.lookup fn vals with _ | ⟨body, callee, rs⟩
    · simp
    · dsimp only
      split
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite u callee) body with ⟨r, st⟩
        cases r with
        | none => simp
        | some r1 =>
          cases r1 with
          | returned _ => dsimp only; split <;> simp
          | _ => simp

theorem ite_call0_noret_dhi {F : Type} (u : PanSemStateFiniteExact 64 F)
    (cond : ExpHOL 64) (fn : MlS) (args : List (ExpHOL 64)) :
    ∀ rv, (evaluateHOLFiniteState u (.ite cond (.call (some (none, none)) fn args) .skip)).1 ≠ some (.returned rv) := by
  intro rv
  rw [evaluateHOLFiniteState_ite]
  rcases @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) cond with _ | cv
  · simp
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
    by_cases h0 : cw = 0#64
    · subst h0; simp [evaluateHOLFiniteState_skip]
    · rw [if_neg h0]; exact call0_noret_dhi u fn args rv

theorem call0_nobreak_nock_dhi {F : Type} (u : PanSemStateFiniteExact 64 F)
    (fn : MlS) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState u (.call (some (none, none)) fn args)).1 ≠ some .break ∧
    (evaluateHOLFiniteState u (.call (some (none, none)) fn args)).1 ≠ some .continue := by
  constructor <;> {
    rw [evaluateHOLFiniteState_call]
    rcases evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args with _ | vals
    · simp
    · dsimp only
      rcases lookupCodeHOLFinite u.code.lookup fn vals with _ | ⟨body, callee, rs⟩
      · simp
      · dsimp only
        split
        · simp
        · rcases evaluateHOLFiniteState (callEntryStateHOLFinite u callee) body with ⟨r, st⟩
          cases r with
          | none => simp
          | some r1 =>
            cases r1 with
            | returned _ => dsimp only; split <;> simp
            | _ => simp
  }

theorem ite_call0_nobreak_dhi {F : Type} (u : PanSemStateFiniteExact 64 F)
    (cond : ExpHOL 64) (fn : MlS) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState u (.ite cond (.call (some (none, none)) fn args) .skip)).1 ≠ some .break ∧
    (evaluateHOLFiniteState u (.ite cond (.call (some (none, none)) fn args) .skip)).1 ≠ some .continue := by
  constructor <;> {
    rw [evaluateHOLFiniteState_ite]
    rcases @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) cond with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases h0 : cw = 0#64
      · subst h0; simp [evaluateHOLFiniteState_skip]
      · rw [if_neg h0]
        first
        | exact (call0_nobreak_nock_dhi u fn args).1
        | exact (call0_nobreak_nock_dhi u fn args).2
  }

theorem ite2_call0_noctrl_dhi {F : Type} (u : PanSemStateFiniteExact 64 F)
    (c1 c2 : ExpHOL 64) (fn : MlS) (args : List (ExpHOL 64)) :
    (∀ rv, (evaluateHOLFiniteState u (.ite c1 (.ite c2 (.call (some (none, none)) fn args) .skip) .skip)).1 ≠ some (.returned rv)) ∧
    (evaluateHOLFiniteState u (.ite c1 (.ite c2 (.call (some (none, none)) fn args) .skip) .skip)).1 ≠ some .break ∧
    (evaluateHOLFiniteState u (.ite c1 (.ite c2 (.call (some (none, none)) fn args) .skip) .skip)).1 ≠ some .continue := by
  have h1 := ite_call0_noret_dhi u c2 fn args
  have h2 := ite_call0_nobreak_dhi u c2 fn args
  rw [evaluateHOLFiniteState_ite, evaluateHOLFiniteState_skip] at h1 h2
  refine ⟨fun rv => ?_, ?_, ?_⟩
  · rw [evaluateHOLFiniteState_ite]
    rcases @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) c1 with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases h0 : cw = 0#64
      · subst h0; simp [evaluateHOLFiniteState_skip]
      · rw [if_neg h0]; exact h1 rv
  · rw [evaluateHOLFiniteState_ite]
    rcases @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) c1 with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases h0 : cw = 0#64
      · subst h0; simp [evaluateHOLFiniteState_skip]
      · rw [if_neg h0]; exact h2.1
  · rw [evaluateHOLFiniteState_ite]
    rcases @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) c1 with _ | cv
    · simp
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
      by_cases h0 : cw = 0#64
      · subst h0; simp [evaluateHOLFiniteState_skip]
      · rw [if_neg h0]; exact h2.2

theorem ite2_ssz_fail_none_keeps {F : Type} (u sb : PanSemStateFiniteExact 64 F)
    (hcode : u.code = originalRuntimeCode)
    (c1 c2 : ExpHOL 64) (code_arg : ExpHOL 64)
    (h : evaluateHOLFiniteState u (.ite c1 (.ite c2 (.call (some (none, none)) (ofString "ssz_fail") [code_arg]) .skip) .skip) = (none, sb)) :
    sb = u := by
  have hk := ite_ssz_fail_keeps u sb hcode c2 code_arg
  rw [evaluateHOLFiniteState_ite, evaluateHOLFiniteState_skip] at hk
  have h1 : evaluateHOLFiniteState u (.ite c1 (.ite c2 (.call (some (none, none)) (ofString "ssz_fail") [code_arg]) .skip) .skip) = (none, sb) := h
  revert h1
  rw [evaluateHOLFiniteState_ite]
  rcases @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) c1 with _ | cv
  · simp
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try simp
    by_cases h0 : cw = 0#64
    · subst h0; simp [evaluateHOLFiniteState_skip]
      intro h; exact h.symm
    · rw [if_neg h0]
      intro h; exact (hk h).1

def DhiOffsOK {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ArenaReady s ∧
  (globN s "ssz_offs" = 0 ∨
   (sourceBase ≤ globN s "ssz_offs" ∧ globN s "ssz_offs" + 64 ≤ heapEnd ∧
    globN s "ssz_offs" % 8 = 0 ∧
    ((sourceBase ≤ globN s "ssz_offs" ∧ globN s "ssz_offs" + 64 ≤ globN s "heap_ptr") ∨
     (scratchStart ≤ globN s "ssz_offs" ∧ globN s "ssz_offs" + 64 ≤ scratchEnd))))

theorem dhiOffsOK_of_worldOK {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hWOK : WorldOK s) : DhiOffsOK s := by
  refine ⟨hWOK.1, ?_⟩
  rcases ssz_offs_allocated_strong hWOK with h0 | hal
  · exact Or.inl h0
  · rcases ssz_offs_allocated hWOK with h0' | ⟨hlo, hhi, hmod, _⟩
    · exact Or.inl h0'
    · refine Or.inr ⟨hlo, hhi, hmod, ?_⟩
      rcases hal with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · have hfmp_lo : scratchStart ≤ globN s "frame_mem_ptr" := hWOK.1.2.2.2.1
        have hfmp_sp : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hWOK.1.2.2.2.2.1
        exact Or.inr ⟨by omega, h2⟩

theorem dhiOffsOK_of_worldEff {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    (hOK : DhiOffsOK s)
    (heff : WorldEff s cur Rl B dhiGw) : DhiOffsOK cur := by
  refine ⟨heff.arena, ?_⟩
  have hg : globN cur "ssz_offs" = globN s "ssz_offs" :=
    globN_eq_of_lookup (heff.gw_kept (ofString "ssz_offs") (by decide))
  have hhp : globN s "heap_ptr" ≤ globN cur "heap_ptr" := heff.hp_lo
  rw [hg]
  rcases hOK.2 with h0 | ⟨hlo, hhi, hmod, hal⟩
  · exact Or.inl h0
  · refine Or.inr ⟨hlo, hhi, hmod, ?_⟩
    rcases hal with ⟨h1, h2⟩ | hsc
    · exact Or.inl ⟨h1, Nat.le_trans h2 hhp⟩
    · exact Or.inr hsc

theorem dhiOffsOK_locals_clock {F : Type}
    {s : PanSemStateFiniteExact 64 F}
    (hOK : DhiOffsOK s) (hc : s.code = originalRuntimeCode)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (c : Nat) :
    DhiOffsOK { s with locals := L, clock := c } := by
  have heff : WorldEff s { s with locals := L, clock := c } [] [] dhiGw :=
    (WorldEff.refl s [] [] dhiGw hOK.1 hc).locals_clock L c
  exact dhiOffsOK_of_worldEff hOK heff

theorem worldEff_store_ssz_offs_const_ok {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hOK : DhiOffsOK s)
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
  obtain ⟨sw, hsw_s⟩ := hOK.1.2.2.2.2.2.2.2.2.2 "ssz_offs" (by decide)
  have hsw_cur : cur.globals.lookup (ofString "ssz_offs") = some (.val (.word sw)) :=
    hg_kept.symm.trans hsw_s
  have hglob : globN s "ssz_offs" = sw.toNat := by unfold GlobalWord at hsw_s; simp [globN, hsw_s]
  have hx_eq : x = sw + BitVec.ofNat 64 off := by
    rcases hdst with ⟨rfl, rfl⟩ | rfl
    · simp [evalHOLExact, toExact, hsw_cur] at hx
      simpa using hx.symm
    · simp [evalHOLExact, evalListHOLExact, toExact, hsw_cur, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
      exact hx.symm
  rw [heff.memaddrs, hOK.1.1.memaddrs, ordinaryDomain_iff] at hdom
  rcases hOK.2 with hg0 | ⟨hlo, hhi, _, _⟩
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

theorem worldEff_store_ssz_offs_dyn_ok {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {B : List (String × Nat)}
    (hOK : DhiOffsOK s)
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
  obtain ⟨sw, hsw_s⟩ := hOK.1.2.2.2.2.2.2.2.2.2 "ssz_offs" (by decide)
  have hsw_cur : cur.globals.lookup (ofString "ssz_offs") = some (.val (.word sw)) :=
    hg_kept.symm.trans hsw_s
  have hglob : globN s "ssz_offs" = sw.toNat := by unfold GlobalWord at hsw_s; simp [globN, hsw_s]
  have hx_eq : x = sw + offw := by
    simp [evalHOLExact, evalListHOLExact, toExact, hsw_cur, hoff_ev, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
    exact hx.symm
  rw [heff.memaddrs, hOK.1.1.memaddrs, ordinaryDomain_iff] at hdom
  rcases hOK.2 with hg0 | ⟨hlo, hhi, _, _⟩
  · have hsw0 : sw = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hsw0 hx_eq
    have hsb : 64 < sourceBase := by decide
    have h1 : (0#64 + offw).toNat = offw.toNat := by simp
    omega
  · have hhe : heapEnd < 2 ^ 64 := by decide
    have hsb : 0 < sourceBase := by decide
    have hg_ne0 : globN s "ssz_offs" ≠ 0 := by omega
    have hx_nat : x.toNat = globN s "ssz_offs" + offw.toNat := by
      rw [hx_eq, BitVec.toNat_add_of_lt] <;> omega
    exact Or.inl ⟨(globN s "ssz_offs", if globN s "ssz_offs" = 0 then 0 else 64),
      List.mem_singleton.2 rfl, by simp [hg_ne0]; omega, by simp [hg_ne0]; omega⟩

theorem dhiOffs_disj_above_heap {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hWOK : WorldOK s) {addr : Nat}
    (hlo : globN s "heap_ptr" ≤ addr)
    (hhi_lim : addr + 8 ≤ heapLimit) :
    ∀ iv ∈ dhiOffsRegions s, 0 < iv.2 → ¬ (iv.1 ≤ addr ∧ addr + 8 ≤ iv.1 + iv.2 ∨ addr < iv.1 + iv.2 ∧ iv.1 < addr + 8) := by
  intro iv hiv hpos hhit
  simp only [dhiOffsRegions, List.mem_singleton] at hiv
  subst hiv
  by_cases hg0 : globN s "ssz_offs" = 0
  · simp [hg0] at hpos
  · simp only [hg0, ↓reduceIte] at hpos hhit
    rcases ssz_offs_allocated_strong hWOK with h0 | hal
    · exact hg0 h0
    · rcases hal with ⟨_, hhi⟩ | ⟨hsc, _⟩
      · omega
      · have hfmp_lo : scratchStart ≤ globN s "frame_mem_ptr" := hWOK.1.2.2.2.1
        have hfmp_sp : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hWOK.1.2.2.2.2.1
        have hlim_sc : heapLimit ≤ scratchStart := by decide
        omega

theorem worldEff_dhi_keeps_heap_memW {F : Type}
    {s cur next : PanSemStateFiniteExact 64 F}
    (hWOK_s : WorldOK s)
    (heff_s_cur : WorldEff s cur (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw)
    (heff_step : WorldEff cur next (dhiOffsRegions cur) ([] : List (String × Nat)) dhiGw)
    {addr : Nat}
    (hal8 : addr % 8 = 0)
    (hlo : globN s "heap_ptr" ≤ addr)
    (hhi : addr + 8 ≤ globN cur "heap_ptr") :
    memW next addr = memW cur addr := by
  have hcur_hp_lim : globN cur "heap_ptr" ≤ heapLimit := heff_s_cur.arena.2.2.1
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have ha_lt : addr < 2 ^ 64 := by omega
  have hbv_nat : (BitVec.ofNat 64 addr).toNat = addr := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
  have hoff_eq : dhiOffsRegions cur = dhiOffsRegions s := by
    have hg := globN_eq_of_lookup (heff_s_cur.gw_kept (ofString "ssz_offs") (by decide))
    simp [dhiOffsRegions, hg]
  unfold memW
  by_cases hmem : next.memory (BitVec.ofNat 64 addr) = cur.memory (BitVec.ofNat 64 addr)
  · rw [hmem]
  · exfalso
    rcases heff_step.cell_frame (BitVec.ofNat 64 addr) hmem with ⟨iv, hiv, hpos, hc1, hc2⟩ | ⟨_, hgs, _⟩ | ⟨_, hfg1, _⟩ | ⟨_, hhf1, _⟩
    · rw [hoff_eq] at hiv
      exact dhiOffs_disj_above_heap hWOK_s hlo (by omega) iv hiv hpos (Or.inr ⟨by omega, by omega⟩)
    · cases hgs
    · dsimp only [freeGap] at hfg1
      have hfmp_lo : scratchStart ≤ globN cur "frame_mem_ptr" := heff_s_cur.arena.2.2.2.1
      have hlim_sc : heapLimit ≤ scratchStart := by decide
      omega
    · dsimp only [heapFree] at hhf1
      omega

theorem store_memW_eq_and_ne {F : Type}
    (cur mid : PanSemStateFiniteExact 64 F) (dstExp valExp : ExpHOL 64)
    (xw vw : BitVec 64)
    (hrun : evaluateHOLFiniteState cur (.store dstExp valExp) = (none, mid))
    (hdst : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) dstExp = some (.val (.word xw)))
    (hval : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp = some (.val (.word vw))) :
    memW mid xw.toNat = vw.toNat ∧
    (∀ y : Nat, y < 2 ^ 64 → y ≠ xw.toNat → memW mid y = memW cur y) := by
  rw [evaluateHOLFiniteState_store] at hrun
  simp only [hdst, hval, flattenHOL, panMemStoresHOL, panMemStoreHOL] at hrun
  by_cases hdom : cur.memaddrs xw
  · simp only [hdom, ↓reduceIte] at hrun
    injection hrun with _ hmid
    subst hmid
    refine ⟨?_, fun y hy hne => ?_⟩
    · unfold memW; dsimp only
      have hbx : BitVec.ofNat 64 xw.toNat = xw := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt xw.isLt]
      simp [hbx]
    · unfold memW; dsimp only
      have hby : BitVec.ofNat 64 y ≠ xw := by
        intro heq; apply hne
        have h1 := congrArg BitVec.toNat heq
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy] at h1
      simp [hby]
  · simp only [hdom, ↓reduceIte] at hrun
    simp at hrun

theorem wordsOK_preserved_of_worldEff {F : Type}
    {cur next : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (heff : WorldEff cur next Rl B gw)
    {iv : Ivl}
    (hal8 : iv.1 % 8 = 0) (hsz8 : iv.2 % 8 = 0)
    (hlo : sourceBase ≤ iv.1) (hhi : iv.1 + iv.2 ≤ heapLimit) :
    WordsOK next iv := by
  have hle : heapLimit ≤ heapEnd := by decide
  exact wordsOK_of_inside_heap heff.arena.1 hal8 hsz8 hlo (Nat.le_trans hhi hle)

theorem ssz_fixed_list_count_body_returns {F : Type}
    (ent : PanSemStateFiniteExact 64 F) (wlen wsz wlim : BitVec 64)
    (hcode : ent.code = originalRuntimeCode)
    (hG : GuestInv ent)
    (hlen : ent.locals.lookup (ofString "len") = some (.val (.word wlen)))
    (hsz : ent.locals.lookup (ofString "sz") = some (.val (.word wsz)))
    (hlim : ent.locals.lookup (ofString "lim") = some (.val (.word wlim)))
    (rv : ValueHOL 64) (cpost : PanSemStateFiniteExact 64 F)
    (hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_ssz_fixed_list_count) =
      (some (.returned rv), cpost)) :
    0 < wsz.toNat ∧
    ∃ qw : BitVec 64,
      rv = .val (.word qw) ∧
      qw.toNat * wsz.toNat = wlen.toNat ∧
      qw.toNat ≤ wlim.toNat := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_ssz_fixed_list_count,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map] at hrun
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  have hargs : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
      [.var .local (ofString "len"), .var .local (ofString "sz")] =
      some [.val (.word wlen), .val (.word wsz)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact, toExact, hlen, hsz]
  rw [hargs] at hrun; dsimp only at hrun
  have hlook_ud : originalRuntimeCode.lookup (ofString "udivmod") =
      some ([(ofString "a", .one), (ofString "b", .one)],
        sourceFnBody Guest.Software.guestFn_udivmod, .comb [.one, .one]) :=
    lookup_of_guestAst_getElem 33 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_udivmod) rfl
  rcases hl : lookupCodeHOLFinite ent.code.lookup (ofString "udivmod") [.val (.word wlen), .val (.word wsz)] with _ | ⟨fb, fc, fr⟩
  · rw [hl] at hrun; simp at hrun
  · rw [hl] at hrun; dsimp only at hrun
    have hfb := lookupCodeHOLFinite_installed_body ent.code.lookup _ _ _ fb _ fr _ fc (by rw [hcode]; exact hlook_ud) hl
    subst hfb
    have hfr := lookupCodeHOLFinite_installed_return ent _ _ _ _ _ fr _ fc (by rw [hcode]; exact hlook_ud) hl
    subst hfr
    by_cases hz : ent.clock = 0
    · rw [if_pos hz] at hrun; simp at hrun
    · rw [if_neg hz] at hrun
      obtain ⟨wa', wb', heq_vs, hfc_a, hfc_b⟩ :=
        lookupCode_two_words_any_dhi (by decide) hlook_ud (by rwa [hcode] at hl)
      injection heq_vs with h1 h2; injection h1 with h1'; injection h1' with h1''; subst h1''
      injection h2 with h2a _; injection h2a with h2'; injection h2' with h2''; subst h2''
      rcases hud : evaluateHOLFiniteState (callEntryStateHOLFinite ent fc) (sourceFnBody Guest.Software.guestFn_udivmod) with ⟨rud, sud⟩
      rw [hud] at hrun
      cases rud with
      | none => simp at hrun
      | some rud1 =>
        cases rud1 with
        | returned rv_ud =>
          dsimp only at hrun
          obtain ⟨hsz_pos, qw, rw_, rfl, hdiv_eq, _, _⟩ :=
            udivmod_body_returns (callEntryStateHOLFinite ent fc) wlen wsz hcode hfc_a hfc_b rv_ud (by rw [hud])
          have hsh : shapeEqHOL (shapeOfHOLExact (.rStruct [.val (.word qw), .val (.word rw_)] : ValueHOL 64))
              (.comb [.one, .one]) = true := by
            simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
          simp only [hsh, Bool.and_self, ↓reduceIte] at hrun
          obtain ⟨_, rSh_ro, _, hlook_ro, hspec_ro⟩ := ro_udivmod
          have hsame_b := Option.some.inj (hlook_ud.symm.trans hlook_ro)
          injection hsame_b with _ hsame_b'; injection hsame_b' with hsame_b'' hsame_r
          subst hsame_b''; subst hsame_r
          have hro := hspec_ro (callEntryStateHOLFinite ent fc) hcode
            (guestInv_callEntry ent fc hG)
            ⟨_, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩
            (by rw [hud]; simp) (by rw [hud]; exact Or.inl ⟨_, rfl⟩)
          rw [hud] at hro; dsimp only at hro
          have hsud_code : sud.code = originalRuntimeCode := by rw [hro]; exact hcode
          let u0 := setVarHOLFinite (ofString "qr") (.rStruct [.val (.word qw), .val (.word rw_)]) { sud with locals := ent.locals }
          have hu0_code : u0.code = originalRuntimeCode := hsud_code
          have hu0_qr : u0.locals.lookup (ofString "qr") = some (.rStruct [.val (.word qw), .val (.word rw_)]) :=
            lookup_setVar_eq _ _ _
          have hu0_lim : u0.locals.lookup (ofString "lim") = some (.val (.word wlim)) := by
            dsimp only [u0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hlim
          have hret1 : (evaluateHOLFiniteState u0
              (.seq
                (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "qr"))) (.const 0#64))
                  (.call (some (none, none)) (ofString "ssz_fail") [.const 30#64]) .skip)
                (.seq
                  (.ite (.cmp .lower (.var .local (ofString "lim")) (.rfield 0 (.var .local (ofString "qr"))))
                    (.call (some (none, none)) (ofString "ssz_fail") [.const 31#64]) .skip)
                  (.return (.rfield 0 (.var .local (ofString "qr"))))))).1 =
              some (.returned rv) := by
            have h1 := congrArg Prod.fst hrun
            simpa using h1
          rw [evaluateHOLFiniteState_seq_line780] at hret1
          rcases hi1 : evaluateHOLFiniteState u0 _ with ⟨ri1, u1⟩
          rw [hi1] at hret1
          cases ri1 with
          | some r1 =>
            exfalso
            have hnr := ite_call0_noret_dhi u0
              (.cmp .notEqual (.rfield 1 (.var .local (ofString "qr"))) (.const 0#64))
              (ofString "ssz_fail") [.const 30#64] rv
            rw [hi1] at hnr; exact hnr hret1
          | none =>
            obtain ⟨hu1_eq, hcond30⟩ := ite_ssz_fail_keeps u0 u1 hu0_code _ _ hi1
            subst hu1_eq
            have hrw0 : rw_.toNat = 0 := by
              simp only [evalHOLExact, evalListHOLExact, toExact, hu0_qr,
                Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord] at hcond30
              by_cases hr0 : rw_ = 0#64
              · subst hr0; rfl
              · simp [hr0] at hcond30
            dsimp only at hret1
            rw [evaluateHOLFiniteState_seq_line780] at hret1
            rcases hi2 : evaluateHOLFiniteState u0 _ with ⟨ri2, u2⟩
            rw [hi2] at hret1
            cases ri2 with
            | some r2 =>
              exfalso
              have hnr := ite_call0_noret_dhi u0
                (.cmp .lower (.var .local (ofString "lim")) (.rfield 0 (.var .local (ofString "qr"))))
                (ofString "ssz_fail") [.const 31#64] rv
              rw [hi2] at hnr; exact hnr hret1
            | none =>
              obtain ⟨hu2_eq, hcond31⟩ := ite_ssz_fail_keeps u0 u2 hu0_code _ _ hi2
              subst hu2_eq
              have hqw_le : qw.toNat ≤ wlim.toNat := by
                simp only [evalHOLExact, evalListHOLExact, toExact, hu0_lim, hu0_qr,
                  Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord] at hcond31
                by_cases hlt : wlim < qw
                · simp [hlt] at hcond31
                · exact Nat.le_of_not_lt (fun h => hlt ((BitVec.lt_def).2 h))
              dsimp only at hret1
              rw [evaluateHOLFiniteState_return] at hret1
              simp [evalHOLExact, toExact, hu0_qr, shapeOfHOLExact] at hret1
              exact ⟨hsz_pos, qw, hret1.symm, by omega, hqw_le⟩
        | _ => simp at hrun

theorem while_none_inv_dhi {F : Type}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (Inv : PanSemStateFiniteExact 64 F → Prop)
    (hdec : ∀ t, Inv t → Inv (decClockHOLFinite t))
    (hno_brk : ∀ t, Inv t → (evaluateHOLFiniteState t body).1 ≠ some .break)
    (hstep : ∀ t (cw : BitVec 64),
      @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word cw)) →
      cw ≠ 0 →
      Inv (decClockHOLFinite t) →
      ((evaluateHOLFiniteState (decClockHOLFinite t) body).1 = none ∨
       (evaluateHOLFiniteState (decClockHOLFinite t) body).1 = some .continue) →
      Inv (evaluateHOLFiniteState (decClockHOLFinite t) body).2) :
    ∀ (k : Nat) (cur : PanSemStateFiniteExact 64 F), cur.clock = k →
      Inv cur →
      (evaluateHOLFiniteState cur (.while cond body)).1 = none →
      Inv (evaluateHOLFiniteState cur (.while cond body)).2 ∧
      (∀ cw : BitVec 64,
        @evalHOLFinite 64 F _ (evaluateHOLFiniteState cur (.while cond body)).2
          (fun a => Classical.propDecidable ((evaluateHOLFiniteState cur (.while cond body)).2.memaddrs a)) cond =
          some (.val (.word cw)) → cw = 0) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro cur hclk hinv hnone
    have hw_eq := evaluateHOLFiniteState_while_fixClockRewrite cur cond body
    rcases hc : @evalHOLFinite 64 F _ cur (fun a => Classical.propDecidable (cur.memaddrs a)) cond with _ | cv
    · rw [hc] at hw_eq; rw [hw_eq] at hnone; simp at hnone
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _
      · rw [hc] at hw_eq; dsimp only at hw_eq
        by_cases hw0 : cw = 0
        · subst hw0; rw [if_neg (by simp)] at hw_eq; rw [hw_eq]
          refine ⟨hinv, fun cw' hcw' => ?_⟩
          change @evalHOLFinite 64 F _ cur (fun a => Classical.propDecidable (cur.memaddrs a)) cond = _ at hcw'
          rw [hc] at hcw'; injection hcw' with h1; injection h1 with h2; injection h2 with h3; exact h3.symm
        · rw [if_pos hw0] at hw_eq
          by_cases hk0 : cur.clock = 0
          · rw [if_pos hk0] at hw_eq; rw [hw_eq] at hnone; simp at hnone
          · rw [if_neg hk0] at hw_eq
            have hinv_d : Inv (decClockHOLFinite cur) := hdec cur hinv
            have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite cur) body
            rcases hbo : evaluateHOLFiniteState (decClockHOLFinite cur) body with ⟨rb, sb⟩
            rw [hbo] at hw_eq hrem
            have hlt : sb.clock < k := by change sb.clock ≤ cur.clock - 1 at hrem; omega
            cases rb with
            | none =>
              dsimp only at hw_eq
              have hinv_sb : Inv sb := by
                have h := hstep cur cw hc hw0 hinv_d (by rw [hbo]; exact Or.inl rfl)
                rwa [hbo] at h
              rw [hw_eq] at hnone ⊢
              exact ih sb.clock hlt sb rfl hinv_sb hnone
            | some r1 =>
              cases r1 with
              | «continue» =>
                dsimp only at hw_eq
                have hinv_sb : Inv sb := by
                  have h := hstep cur cw hc hw0 hinv_d (by rw [hbo]; exact Or.inr rfl)
                  rwa [hbo] at h
                rw [hw_eq] at hnone ⊢
                exact ih sb.clock hlt sb rfl hinv_sb hnone
              | «break» =>
                exfalso
                exact hno_brk (decClockHOLFinite cur) hinv_d (by rw [hbo])
              | _ =>
                dsimp only at hw_eq; rw [hw_eq] at hnone; simp at hnone
      · rw [hc] at hw_eq; rw [hw_eq] at hnone; simp at hnone
      · rw [hc] at hw_eq; rw [hw_eq] at hnone; simp at hnone

theorem ssz_check_offsets_body_returns {F : Type}
    (ent : PanSemStateFiniteExact 64 F) (woffs wn wfixed wlen : BitVec 64)
    (hcode : ent.code = originalRuntimeCode)
    (hoffs : ent.locals.lookup (ofString "offs") = some (.val (.word woffs)))
    (hn : ent.locals.lookup (ofString "n") = some (.val (.word wn)))
    (hfixed : ent.locals.lookup (ofString "fixed") = some (.val (.word wfixed)))
    (hlen : ent.locals.lookup (ofString "len") = some (.val (.word wlen)))
    (hn_pos : 0 < wn.toNat) (hn_lt : wn.toNat < 2 ^ 60)
    (hoffs_hi : woffs.toNat + wn.toNat * 8 ≤ 2 ^ 64)
    (rv : ValueHOL 64) (cpost : PanSemStateFiniteExact 64 F)
    (hrun : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_ssz_check_offsets) =
      (some (.returned rv), cpost)) :
    cpost.memory = ent.memory ∧
    memW ent woffs.toNat = wfixed.toNat ∧
    (∀ j : Nat, j < wn.toNat →
      wfixed.toNat ≤ memW ent (woffs.toNat + j * 8) ∧
      memW ent (woffs.toNat + j * 8) ≤ wlen.toNat) ∧
    (∀ j : Nat, j + 1 < wn.toNat →
      memW ent (woffs.toNat + j * 8) ≤ memW ent (woffs.toNat + (j + 1) * 8)) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_ssz_check_offsets,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hrun
  rw [evaluateHOLFiniteState_seq_line780] at hrun
  have hwn_ne0 : wn ≠ 0#64 := fun h => by subst h; simp at hn_pos
  have hi0 : evaluateHOLFiniteState ent
      (.ite (.cmp .equal (.var .local (ofString "n")) (.const 0#64)) (.return (.const 0#64)) .skip) =
      (none, ent) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact, evalListHOLExact, toExact, hn, Compiler.Encoders.Asm.wordCmpHOL,
      valueIsWord, valueWord, hwn_ne0, evaluateHOLFiniteState_skip]
  rw [hi0] at hrun; dsimp only at hrun
  rw [evaluateHOLFiniteState_dec_total] at hrun
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hrun
  let m0 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) ent
  let wcond : ExpHOL 64 := .cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))
  let wbody : ProgHOL 64 :=
    .dec (ofString "o") .one
      (.load .one (.op .add [.var .local (ofString "offs"), .panop .mul [.var .local (ofString "i"), .const 8#64]]))
      (.seq
        (.ite (.cmp .notEqual (.const 0#64)
            (.op .or [.cmp .lower (.var .local (ofString "o")) (.var .local (ofString "fixed")),
              .cmp .lower (.var .local (ofString "len")) (.var .local (ofString "o"))]))
          (.call (some (none, none)) (ofString "ssz_fail") [.const 10#64]) .skip)
        (.seq
          (.ite (.cmp .less (.const 0#64) (.var .local (ofString "i")))
            (.ite (.cmp .lower (.var .local (ofString "o"))
                (.load .one (.op .sub [.op .add [.var .local (ofString "offs"),
                  .panop .mul [.var .local (ofString "i"), .const 8#64]], .const 8#64])))
              (.call (some (none, none)) (ofString "ssz_fail") [.const 11#64]) .skip)
            .skip)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))))
  let tailP : ProgHOL 64 :=
    .seq
      (.ite (.cmp .notEqual (.load .one (.var .local (ofString "offs"))) (.var .local (ofString "fixed")))
        (.call (some (none, none)) (ofString "ssz_fail") [.const 12#64]) .skip)
      (.return (.const 0#64))
  rcases hseq_w : evaluateHOLFiniteState m0 (.seq (.while wcond wbody) tailP) with ⟨rsw, ssw⟩
  dsimp only [m0, wcond, wbody, tailP] at hseq_w
  rw [hseq_w] at hrun
  injection hrun with hrsw hcpost
  subst hrsw
  have hcpost_mem : cpost.memory = ssw.memory := by rw [← hcpost]
  rw [evaluateHOLFiniteState_seq_line780] at hseq_w
  rcases hw : evaluateHOLFiniteState m0 (.while wcond wbody) with ⟨rw0, sw⟩
  rw [hw] at hseq_w
  have hw_noret : ∀ (t : PanSemStateFiniteExact 64 F), t.code = originalRuntimeCode → ∀ rv', (evaluateHOLFiniteState t (.while wcond wbody)).1 ≠ some (.returned rv') := by
    intro t0 ht0_code rv'
    suffices ∀ k (t : PanSemStateFiniteExact 64 F), t.clock = k → t.code = originalRuntimeCode →
        (evaluateHOLFiniteState t (.while wcond wbody)).1 ≠ some (.returned rv') from
      this t0.clock t0 rfl ht0_code
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro t hk ht_code hret_w
      have hweq := evaluateHOLFiniteState_while_fixClockRewrite t wcond wbody
      rcases hc : @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) wcond with _ | cv
      · rw [hc] at hweq; rw [hweq] at hret_w; simp at hret_w
      · rcases cv with ⟨⟨cw⟩⟩ | _ | _
        · rw [hc] at hweq; dsimp only at hweq
          by_cases hw0 : cw = 0
          · subst hw0; rw [if_neg (by simp)] at hweq; rw [hweq] at hret_w; simp at hret_w
          · rw [if_pos hw0] at hweq
            by_cases hk0 : t.clock = 0
            · rw [if_pos hk0] at hweq; rw [hweq] at hret_w; simp at hret_w
            · rw [if_neg hk0] at hweq
              have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite t) wbody
              rcases hb : evaluateHOLFiniteState (decClockHOLFinite t) wbody with ⟨rb, sb⟩
              rw [hb] at hweq hrem
              have hlt : sb.clock < k := by change sb.clock ≤ t.clock - 1 at hrem; omega
              dsimp only [wbody] at hb
              rw [evaluateHOLFiniteState_dec_total] at hb
              dsimp only at hb
              rcases hev_o : @evalHOLExact 64 F _ (decClockHOLFinite t).toExact (fun a => Classical.propDecidable ((decClockHOLFinite t).memaddrs a))
                  (.load .one (.op .add [.var .local (ofString "offs"), .panop .mul [.var .local (ofString "i"), .const 8#64]])) with _ | vo
              · rw [hev_o] at hb; dsimp only at hb; injection hb with hrb _; subst hrb; dsimp only at hweq; rw [hweq] at hret_w; simp at hret_w
              · rw [hev_o] at hb; dsimp only at hb
                by_cases hsho : shapeEqHOL .one (shapeOfHOLExact vo) = true
                · rw [if_pos hsho] at hb
                  let u1 := setVarHOLFinite (ofString "o") vo (decClockHOLFinite t)
                  rw [evaluateHOLFiniteState_seq_line780] at hb
                  rcases hb1 : evaluateHOLFiniteState u1 _ with ⟨rb1, sb1⟩
                  rw [hb1] at hb
                  cases rb1 with
                  | some r1 =>
                    dsimp only at hb
                    injection hb with hrb hsb
                    subst hrb
                    cases r1 with
                    | returned rv'' => exact ite_call0_noret_dhi u1 _ (ofString "ssz_fail") [.const 10#64] rv'' (by rw [hb1])
                    | «continue» => exact absurd (by rw [hb1] : (evaluateHOLFiniteState u1 _).1 = some .continue) (ite_call0_nobreak_dhi u1 _ (ofString "ssz_fail") [.const 10#64]).2
                    | _ => dsimp only at hweq; rw [hweq] at hret_w; simp at hret_w
                  | none =>
                    obtain ⟨hsb1_eq, _⟩ := ite_ssz_fail_keeps u1 sb1 ht_code _ _ hb1
                    subst hsb1_eq
                    dsimp only at hb
                    rw [evaluateHOLFiniteState_seq_line780] at hb
                    rcases hb2 : evaluateHOLFiniteState u1 _ with ⟨rb2, sb2⟩
                    rw [hb2] at hb
                    cases rb2 with
                    | some r2 =>
                      dsimp only at hb
                      injection hb with hrb _
                      subst hrb
                      cases r2 with
                      | returned rv'' => exact (ite2_call0_noctrl_dhi u1 _ _ (ofString "ssz_fail") [.const 11#64]).1 rv'' (by rw [hb2])
                      | «continue» => exact absurd (by rw [hb2] : (evaluateHOLFiniteState u1 _).1 = some .continue) (ite2_call0_noctrl_dhi u1 _ _ (ofString "ssz_fail") [.const 11#64]).2.2
                      | _ => dsimp only at hweq; rw [hweq] at hret_w; simp at hret_w
                    | none =>
                      have hsb2_code_mem : sb2 = u1 := ite2_ssz_fail_none_keeps u1 sb2 ht_code _ _ _ hb2
                      subst hsb2_code_mem
                      dsimp only at hb
                      rw [evaluateHOLFiniteState_assign] at hb
                      rcases hva : @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
                          (.op .add [.var .local (ofString "i"), .const 1#64]) with _ | va
                      · rw [hva] at hb; dsimp only at hb; injection hb with hrb _; subst hrb; dsimp only at hweq; rw [hweq] at hret_w; simp at hret_w
                      · rw [hva] at hb; dsimp only at hb
                        split at hb
                        · injection hb with hrb hsb
                          subst hrb
                          have hsb_code : sb.code = originalRuntimeCode := by rw [← hsb]; exact ht_code
                          dsimp only at hweq; rw [hweq] at hret_w
                          exact ih sb.clock hlt sb rfl hsb_code hret_w
                        · injection hb with hrb _; subst hrb; dsimp only at hweq; rw [hweq] at hret_w; simp at hret_w
                · rw [if_neg hsho] at hb; injection hb with hrb _; subst hrb; dsimp only at hweq; rw [hweq] at hret_w; simp at hret_w
        · rw [hc] at hweq; rw [hweq] at hret_w; simp at hret_w
        · rw [hc] at hweq; rw [hweq] at hret_w; simp at hret_w
  cases rw0 with
  | some rw1 =>
    exfalso
    dsimp only at hseq_w
    injection hseq_w with hrw1 _
    have hrw1' : rw1 = .returned rv := Option.some.inj hrw1
    subst hrw1'
    exact hw_noret m0 hcode rv (by rw [hw])
  | none =>
    dsimp only at hseq_w
    let Inv : PanSemStateFiniteExact 64 F → Prop := fun t =>
      t.code = originalRuntimeCode ∧
      t.memory = ent.memory ∧
      t.memaddrs = ent.memaddrs ∧
      t.locals.lookup (ofString "offs") = some (.val (.word woffs)) ∧
      t.locals.lookup (ofString "n") = some (.val (.word wn)) ∧
      t.locals.lookup (ofString "fixed") = some (.val (.word wfixed)) ∧
      t.locals.lookup (ofString "len") = some (.val (.word wlen)) ∧
      ∃ wi : BitVec 64,
        t.locals.lookup (ofString "i") = some (.val (.word wi)) ∧
        wi.toNat ≤ wn.toNat ∧
        (∀ j < wi.toNat,
          wfixed.toNat ≤ memW ent (woffs.toNat + j * 8) ∧
          memW ent (woffs.toNat + j * 8) ≤ wlen.toNat) ∧
        (∀ j, j + 1 < wi.toNat →
          memW ent (woffs.toNat + j * 8) ≤ memW ent (woffs.toNat + (j + 1) * 8))
    have hInv0 : Inv m0 := by
      refine ⟨hcode, rfl, rfl, ?_, ?_, ?_, ?_, 0#64, lookup_setVar_eq _ _ _, by simp,
        fun j hj => by simp at hj, fun j hj => by simp at hj⟩ <;>
        (dsimp only [m0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; assumption)
    have hno_brk : ∀ t, Inv t → (evaluateHOLFiniteState t wbody).1 ≠ some .break := by
      intro t ht hbrk
      dsimp only [wbody] at hbrk
      rw [evaluateHOLFiniteState_dec_total] at hbrk
      dsimp only at hbrk
      rcases hev_o : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.load .one (.op .add [.var .local (ofString "offs"), .panop .mul [.var .local (ofString "i"), .const 8#64]])) with _ | vo
      · rw [hev_o] at hbrk; simp at hbrk
      · rw [hev_o] at hbrk; dsimp only at hbrk
        by_cases hsho : shapeEqHOL .one (shapeOfHOLExact vo) = true
        · rw [if_pos hsho] at hbrk
          let u1 := setVarHOLFinite (ofString "o") vo t
          rw [evaluateHOLFiniteState_seq_line780] at hbrk
          rcases hb1 : evaluateHOLFiniteState u1 _ with ⟨rb1, sb1⟩
          rw [hb1] at hbrk
          cases rb1 with
          | some r1 =>
            dsimp only at hbrk
            have h1 : r1 = .break := Option.some.inj hbrk
            subst h1
            exact (ite_call0_nobreak_dhi u1 _ (ofString "ssz_fail") [.const 10#64]).1 (by rw [hb1])
          | none =>
            obtain ⟨hsb1, _⟩ := ite_ssz_fail_keeps u1 sb1 ht.1 _ _ hb1
            subst hsb1; dsimp only at hbrk
            rw [evaluateHOLFiniteState_seq_line780] at hbrk
            rcases hb2 : evaluateHOLFiniteState u1 _ with ⟨rb2, sb2⟩
            rw [hb2] at hbrk
            cases rb2 with
            | some r2 =>
              dsimp only at hbrk
              have h2 : r2 = .break := Option.some.inj hbrk
              subst h2
              exact (ite2_call0_noctrl_dhi u1 _ _ (ofString "ssz_fail") [.const 11#64]).2.1 (by rw [hb2])
            | none =>
              dsimp only at hbrk
              rw [evaluateHOLFiniteState_assign] at hbrk
              rcases hva : @evalHOLExact 64 F _ sb2.toExact (fun a => Classical.propDecidable (sb2.memaddrs a))
                  (.op .add [.var .local (ofString "i"), .const 1#64]) with _ | va
              · rw [hva] at hbrk; simp at hbrk
              · rw [hva] at hbrk; dsimp only at hbrk; split at hbrk <;> simp at hbrk
        · rw [if_neg hsho] at hbrk; simp at hbrk
    have hstep_w : ∀ t (cw : BitVec 64),
        @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) wcond = some (.val (.word cw)) →
        cw ≠ 0 →
        Inv (decClockHOLFinite t) →
        ((evaluateHOLFiniteState (decClockHOLFinite t) wbody).1 = none ∨
         (evaluateHOLFiniteState (decClockHOLFinite t) wbody).1 = some .continue) →
        Inv (evaluateHOLFiniteState (decClockHOLFinite t) wbody).2 := by
      intro t cw hcond hnz ⟨ht_code, ht_mem, ht_dom, ht_offs, ht_n, ht_fixed, ht_len, wi, ht_i, hwi_le, hbounds, hmono⟩ hnc
      have hloc_offs : t.locals.lookup (ofString "offs") = some (.val (.word woffs)) := ht_offs
      have hloc_n : t.locals.lookup (ofString "n") = some (.val (.word wn)) := ht_n
      have hloc_fixed : t.locals.lookup (ofString "fixed") = some (.val (.word wfixed)) := ht_fixed
      have hloc_len : t.locals.lookup (ofString "len") = some (.val (.word wlen)) := ht_len
      have hloc_i : t.locals.lookup (ofString "i") = some (.val (.word wi)) := ht_i
      have hmem_t : t.memory = ent.memory := ht_mem
      have hdom_t : t.memaddrs = ent.memaddrs := ht_dom
      have hcode_t : t.code = originalRuntimeCode := ht_code
      have hwi_lt : wi.toNat < wn.toNat := by
        rw [evalHOLFinite_eq_toExact] at hcond
        simp only [wcond, evalHOLExact, evalListHOLExact, toExact, hloc_i, hloc_n,
          Compiler.Encoders.Asm.wordCmpHOL,
          holAsmSignedLess_small wi wn (by omega) (by omega)] at hcond
        by_cases hlt : wi.toNat < wn.toNat
        · exact hlt
        · simp [hlt] at hcond; exact absurd hcond.symm hnz
      rcases hbo_ev : evaluateHOLFiniteState (decClockHOLFinite t) wbody with ⟨rb_step, sb_step⟩
      have hnc' : rb_step = none ∨ rb_step = some .continue := by
        rcases hnc with h | h
        · exact Or.inl (by rw [← h, hbo_ev])
        · exact Or.inr (by rw [← h, hbo_ev])
      show Inv sb_step
      dsimp only [wbody] at hbo_ev
      rw [evaluateHOLFiniteState_dec_total] at hbo_ev
      dsimp only at hbo_ev
      rcases hev_o : @evalHOLExact 64 F _ (decClockHOLFinite t).toExact (fun a => Classical.propDecidable ((decClockHOLFinite t).memaddrs a))
          (.load .one (.op .add [.var .local (ofString "offs"), .panop .mul [.var .local (ofString "i"), .const 8#64]])) with _ | vo
      · rw [hev_o] at hbo_ev; dsimp only at hbo_ev
        injection hbo_ev with hrb_eq _
        rw [← hrb_eq] at hnc'
        rcases hnc' with h | h <;> cases h
      · rw [hev_o] at hbo_ev; dsimp only at hbo_ev
        by_cases hsho : shapeEqHOL .one (shapeOfHOLExact vo) = true
        · rw [if_pos hsho] at hbo_ev
          obtain ⟨wo, rfl⟩ := eval_load_one_word (decClockHOLFinite t) _ vo hev_o
          have hmul_eq : (wi * 8#64).toNat = wi.toNat * 8 := by
            rw [BitVec.toNat_mul, show (8#64 : BitVec 64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
          have haddr_eq : (woffs + wi * 8#64).toNat = woffs.toNat + wi.toNat * 8 := by
            rw [BitVec.toNat_add_of_lt] <;> omega
          have hwo_eq : wo.toNat = memW ent (woffs.toNat + wi.toNat * 8) := by
            change @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
              (.load .one (.op .add [.var .local (ofString "offs"), .panop .mul [.var .local (ofString "i"), .const 8#64]])) =
              some (.val (.word wo)) at hev_o
            have hadd_ev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
                (.op .add [.var .local (ofString "offs"), .panop .mul [.var .local (ofString "i"), .const 8#64]]) =
                some (.val (.word (woffs + wi * 8#64))) := by
              simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, hloc_offs, hloc_i,
                wordOpHOL, wordOp, valueIsWord, valueWord]
            unfold evalHOLExact at hev_o
            rw [hadd_ev] at hev_o
            by_cases hdom_a : t.memaddrs (woffs + wi * 8#64)
            · rcases hwlab : ent.memory (woffs + wi * 8#64) with ⟨w_loaded⟩
              simp [isWfShapeExactHOL, memLoadHOLExact, panMemLoadHOL, toExact, hmem_t, hdom_a, hwlab] at hev_o
              subst hev_o
              have hbv : BitVec.ofNat 64 (woffs.toNat + wi.toNat * 8) = woffs + wi * 8#64 := by
                apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), haddr_eq]
              simp [memW, hbv, hwlab]
            · simp [isWfShapeExactHOL, memLoadHOLExact, panMemLoadHOL, toExact, hdom_a] at hev_o
          let u1 := setVarHOLFinite (ofString "o") (.val (.word wo)) (decClockHOLFinite t)
          have hu1_o : u1.locals.lookup (ofString "o") = some (.val (.word wo)) := lookup_setVar_eq _ _ _
          have hu1_offs : u1.locals.lookup (ofString "offs") = some (.val (.word woffs)) := by
            dsimp only [u1]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hloc_offs
          have hu1_n : u1.locals.lookup (ofString "n") = some (.val (.word wn)) := by
            dsimp only [u1]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hloc_n
          have hu1_fixed : u1.locals.lookup (ofString "fixed") = some (.val (.word wfixed)) := by
            dsimp only [u1]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hloc_fixed
          have hu1_len : u1.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
            dsimp only [u1]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hloc_len
          have hu1_i : u1.locals.lookup (ofString "i") = some (.val (.word wi)) := by
            dsimp only [u1]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hloc_i
          have hu1_mem : u1.memory = ent.memory := hmem_t
          have hu1_dom : u1.memaddrs = ent.memaddrs := hdom_t
          have hu1_code : u1.code = originalRuntimeCode := hcode_t
          rw [evaluateHOLFiniteState_seq_line780] at hbo_ev
          rcases hb1 : evaluateHOLFiniteState u1 _ with ⟨rb1, sb1⟩
          rw [hb1] at hbo_ev
          cases rb1 with
          | some r1 =>
            exfalso
            dsimp only at hbo_ev
            injection hbo_ev with hrb_eq _
            rw [← hrb_eq] at hnc'
            rcases hnc' with h1 | h1
            · cases h1
            · injection h1 with h1'; subst h1'
              exact (ite_call0_nobreak_dhi u1 _ (ofString "ssz_fail") [.const 10#64]).2 (by rw [hb1])
          | none =>
            obtain ⟨hsb1_eq, hcond10⟩ := ite_ssz_fail_keeps u1 sb1 hu1_code _ _ hb1
            subst hsb1_eq
            have hwo_bounds : wfixed.toNat ≤ wo.toNat ∧ wo.toNat ≤ wlen.toNat := by
              simp only [evalHOLExact, evalListHOLExact, toExact, hu1_o, hu1_fixed, hu1_len,
                wordOpHOL, wordOp, Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord] at hcond10
              constructor
              · by_cases h1 : wo < wfixed
                · exfalso
                  by_cases h2 : wlen < wo <;>
                    (simp [h1, h2, valueIsWord, valueWord] at hcond10; revert hcond10; decide)
                · exact Nat.le_of_not_lt (fun h => h1 ((BitVec.lt_def).2 h))
              · by_cases h2 : wlen < wo
                · exfalso
                  by_cases h1 : wo < wfixed <;>
                    (simp [h1, h2, valueIsWord, valueWord] at hcond10; revert hcond10; decide)
                · exact Nat.le_of_not_lt (fun h => h2 ((BitVec.lt_def).2 h))
            dsimp only at hbo_ev
            rw [evaluateHOLFiniteState_seq_line780] at hbo_ev
            rcases hb2 : evaluateHOLFiniteState u1 _ with ⟨rb2, sb2⟩
            rw [hb2] at hbo_ev
            cases rb2 with
            | some r2 =>
              exfalso
              dsimp only at hbo_ev
              injection hbo_ev with hrb_eq _
              rw [← hrb_eq] at hnc'
              rcases hnc' with h2 | h2
              · cases h2
              · injection h2 with h2'; subst h2'
                exact (ite2_call0_noctrl_dhi u1 _ _ (ofString "ssz_fail") [.const 11#64]).2.2 (by rw [hb2])
            | none =>
              obtain ⟨hsb2_eq, hprev_le⟩ : sb2 = u1 ∧ (0 < wi.toNat → memW ent (woffs.toNat + (wi.toNat - 1) * 8) ≤ wo.toNat) := by
                rw [evaluateHOLFiniteState_ite] at hb2
                have hcond_i : @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
                    (.cmp .less (.const 0#64) (.var .local (ofString "i"))) =
                    some (.val (.word (if 0 < wi.toNat then 1#64 else 0#64))) := by
                  simp only [evalHOLExact, evalListHOLExact, toExact, hu1_i,
                    Compiler.Encoders.Asm.wordCmpHOL,
                    holAsmSignedLess_small 0#64 wi (by decide) (by omega), valueIsWord, valueWord]
                  by_cases hpos : 0 < wi.toNat <;> simp [hpos]
                rw [hcond_i] at hb2; dsimp only at hb2
                by_cases hpos : 0 < wi.toNat
                · simp only [hpos, ↓reduceIte] at hb2
                  rw [if_neg (by decide : (1#64 : BitVec 64) ≠ 0)] at hb2
                  obtain ⟨hsb2_eq, hcond11⟩ := ite_ssz_fail_keeps u1 sb2 hu1_code
                    (.cmp .lower (.var .local (ofString "o"))
                      (.load .one (.op .sub [.op .add [.var .local (ofString "offs"),
                        .panop .mul [.var .local (ofString "i"), .const 8#64]], .const 8#64])))
                    (.const 11#64) hb2
                  refine ⟨hsb2_eq, fun _ => ?_⟩
                  have hsub_ev : @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
                      (.op .sub [.op .add [.var .local (ofString "offs"),
                        .panop .mul [.var .local (ofString "i"), .const 8#64]], .const 8#64]) =
                      some (.val (.word (woffs + wi * 8#64 - 8#64))) := by
                    simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, hu1_offs, hu1_i,
                      wordOpHOL, wordOp, valueIsWord, valueWord]
                  have hsub_eq : (woffs + wi * 8#64 - 8#64).toNat = woffs.toNat + (wi.toNat - 1) * 8 := by
                    have h1 : 8 ≤ (woffs + wi * 8#64).toNat := by omega
                    rw [BitVec.toNat_sub_of_le (by exact (BitVec.le_def).2 h1)]
                    have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
                    omega
                  have ho_ev : @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
                      (.var .local (ofString "o")) = some (.val (.word wo)) := by
                    simp [evalHOLExact, toExact, hu1_o]
                  unfold evalHOLExact at hcond11
                  rw [ho_ev] at hcond11
                  unfold evalHOLExact at hcond11
                  rw [hsub_ev] at hcond11
                  by_cases hdom_p : u1.memaddrs (woffs + wi * 8#64 - 8#64)
                  · rcases hwlab_p : ent.memory (woffs + wi * 8#64 - 8#64) with ⟨wp_loaded⟩
                    simp [isWfShapeExactHOL, memLoadHOLExact, panMemLoadHOL, toExact, hu1_mem, hdom_p, hwlab_p] at hcond11
                    have hbv_p : BitVec.ofNat 64 (woffs.toNat + (wi.toNat - 1) * 8) = woffs + wi * 8#64 - 8#64 := by
                      apply BitVec.eq_of_toNat_eq
                      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hsub_eq]
                    have hwp_eq : memW ent (woffs.toNat + (wi.toNat - 1) * 8) = wp_loaded.toNat := by
                      simp [memW, hbv_p, hwlab_p]
                    rw [hwp_eq]
                    by_cases hlt_p : wo < wp_loaded
                    · simp [Compiler.Encoders.Asm.wordCmpHOL, hlt_p] at hcond11
                    · exact Nat.le_of_not_lt (fun h => hlt_p ((BitVec.lt_def).2 h))
                  · simp [isWfShapeExactHOL, memLoadHOLExact, panMemLoadHOL, toExact, hdom_p] at hcond11
                · simp only [hpos, ↓reduceIte] at hb2
                  rw [if_pos (by decide : (0#64 : BitVec 64) = 0), evaluateHOLFiniteState_skip] at hb2
                  injection hb2 with _ h; exact ⟨h.symm, fun hp => absurd hp hpos⟩
              subst hsb2_eq
              dsimp only at hbo_ev
              rw [evaluateHOLFiniteState_assign] at hbo_ev
              have hev_inc : @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
                  (.op .add [.var .local (ofString "i"), .const 1#64]) = some (.val (.word (wi + 1#64))) := by
                simp [evalHOLExact, evalListHOLExact, toExact, hu1_i, wordOpHOL, wordOp, valueIsWord, valueWord]
              have hvv_i : u1.isValidValueHOLFinite .local (ofString "i") (.val (.word (wi + 1#64))) = true := by
                simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, toExact, hu1_i,
                  shapeOfHOLExact, shapeEqHOL]
              simp only [hev_inc, hvv_i, ↓reduceIte, setKvarHOLFinite] at hbo_ev
              injection hbo_ev with _ hsb_step_eq
              rw [← hsb_step_eq]
              have hwi1_nat : (wi + 1#64).toNat = wi.toNat + 1 := by
                rw [BitVec.toNat_add_of_lt]
                · rfl
                · change wi.toNat + 1 < 2 ^ 64; omega
              refine ⟨hu1_code, hu1_mem, hu1_dom, ?_, ?_, ?_, ?_, wi + 1#64, ?_, by omega, ?_, ?_⟩
              · simp only [InitECandidate.Solver.PanRunBounded.resVarEq_lookup, show ofString "offs" ≠ ofString "o" by decide, ↓reduceIte]
                rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hu1_offs
              · simp only [InitECandidate.Solver.PanRunBounded.resVarEq_lookup, show ofString "n" ≠ ofString "o" by decide, ↓reduceIte]
                rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hu1_n
              · simp only [InitECandidate.Solver.PanRunBounded.resVarEq_lookup, show ofString "fixed" ≠ ofString "o" by decide, ↓reduceIte]
                rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hu1_fixed
              · simp only [InitECandidate.Solver.PanRunBounded.resVarEq_lookup, show ofString "len" ≠ ofString "o" by decide, ↓reduceIte]
                rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hu1_len
              · simp only [InitECandidate.Solver.PanRunBounded.resVarEq_lookup, show ofString "i" ≠ ofString "o" by decide, ↓reduceIte]
                exact lookup_setVar_eq _ _ _
              · intro j hj
                rw [hwi1_nat] at hj
                by_cases hjeq : j = wi.toNat
                · subst hjeq; rw [← hwo_eq]; exact hwo_bounds
                · exact hbounds j (by omega)
              · intro j hj
                rw [hwi1_nat] at hj
                by_cases hjeq : j + 1 = wi.toNat
                · have hj_sub : j = wi.toNat - 1 := by omega
                  have hpos : 0 < wi.toNat := by omega
                  have hp := hprev_le hpos
                  rw [← hj_sub, hwo_eq] at hp
                  rwa [hjeq]
                · exact hmono j (by omega)
        · rw [if_neg hsho] at hbo_ev
          injection hbo_ev with hrb_eq _
          rw [← hrb_eq] at hnc'
          rcases hnc' with h | h <;> cases h
    obtain ⟨hInv_sw, hcond_exit⟩ := while_none_inv_dhi wcond wbody Inv
      (fun t ht => ht) hno_brk hstep_w
      m0.clock m0 rfl hInv0 (by rw [hw])
    rw [hw] at hInv_sw hcond_exit
    obtain ⟨hsw_code, hsw_mem, hsw_dom, hsw_offs, hsw_n, hsw_fixed, hsw_len, wi_end, hsw_i, hwi_end_le, hbounds_end, hmono_end⟩ := hInv_sw
    have hwi_end_eq : wi_end.toNat = wn.toNat := by
      have hev_end : @evalHOLFinite 64 F _ sw (fun a => Classical.propDecidable (sw.memaddrs a)) wcond =
          some (.val (.word (if wi_end.toNat < wn.toNat then 1#64 else 0#64))) := by
        rw [evalHOLFinite_eq_toExact]
        have hi_sw : sw.locals.lookup (ofString "i") = some (.val (.word wi_end)) := hsw_i
        have hn_sw : sw.locals.lookup (ofString "n") = some (.val (.word wn)) := hsw_n
        simp [wcond, evalHOLExact, evalListHOLExact, toExact, hi_sw, hn_sw,
          Compiler.Encoders.Asm.wordCmpHOL,
          holAsmSignedLess_small wi_end wn (by omega) (by omega)]
      have h0 := hcond_exit _ hev_end
      by_cases hlt : wi_end.toNat < wn.toNat
      · simp [hlt] at h0
      · omega
    rw [evaluateHOLFiniteState_seq_line780] at hseq_w
    rcases hit12 : evaluateHOLFiniteState sw _ with ⟨rit12, sit12⟩
    rw [hit12] at hseq_w
    cases rit12 with
    | some r12 =>
      exfalso
      dsimp only at hseq_w
      injection hseq_w with hr12 _
      have hr12' : r12 = .returned rv := Option.some.inj hr12
      subst hr12'
      exact ite_call0_noret_dhi sw _ (ofString "ssz_fail") [.const 12#64] rv (by rw [hit12])
    | none =>
      dsimp only at hseq_w
      obtain ⟨hsit12_eq, hcond12⟩ := ite_ssz_fail_keeps sw sit12 hsw_code _ _ hit12
      rw [hsit12_eq] at hseq_w
      rw [evaluateHOLFiniteState_return] at hseq_w
      simp [evalHOLExact, shapeOfHOLExact] at hseq_w
      obtain ⟨_, hssw_eq⟩ := hseq_w
      have hcpost_mem' : cpost.memory = sw.memory := by
        rw [hcpost_mem, ← hssw_eq]
        rfl
      have hoffs_sw : sw.locals.lookup (ofString "offs") = some (.val (.word woffs)) := hsw_offs
      have hfixed_sw : sw.locals.lookup (ofString "fixed") = some (.val (.word wfixed)) := hsw_fixed
      have hmem_sw : sw.memory = ent.memory := hsw_mem
      have hdom_sw : sw.memaddrs = ent.memaddrs := hsw_dom
      have hmem0_eq : memW ent woffs.toNat = wfixed.toNat := by
        change @evalHOLExact 64 F _ sw.toExact (fun a => Classical.propDecidable (sw.memaddrs a))
          (ExpHOL.cmp Cmp.notEqual (ExpHOL.load ShapeHOL.one (ExpHOL.var VarKind.local (ofString "offs")))
            (ExpHOL.var VarKind.local (ofString "fixed"))) =
          some (.val (.word 0#64)) at hcond12
        by_cases hdom0 : sw.memaddrs woffs
        · rcases hwlab0 : ent.memory woffs with ⟨w0_loaded⟩
          simp [evalHOLExact, evalListHOLExact, toExact, hoffs_sw, hfixed_sw, hmem_sw,
            isWfShapeExactHOL, memLoadHOLExact, panMemLoadHOL, hdom0, hwlab0,
            valueIsWord, valueWord] at hcond12
          have hbv0 : BitVec.ofNat 64 woffs.toNat = woffs := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt woffs.isLt]
          simp only [memW, hbv0, hwlab0]
          by_cases heq0 : w0_loaded = wfixed
          · subst heq0; rfl
          · simp [Compiler.Encoders.Asm.wordCmpHOL, heq0] at hcond12
        · simp [evalHOLExact, evalListHOLExact, toExact, hoffs_sw, hfixed_sw,
            isWfShapeExactHOL, memLoadHOLExact, panMemLoadHOL, hdom0] at hcond12
      rw [hwi_end_eq] at hbounds_end hmono_end
      exact ⟨hcpost_mem'.trans hmem_sw, hmem0_eq, hbounds_end, hmono_end⟩

theorem fk_decode_host_input :
    KeepsOn WorldOK WorldOK (ofString "decode_host_input") :=
  WorldKeeps.keepsOn_buffers wk_decode_host_input_noExtra fun s i hi => by
    simp only [List.mem_singleton] at hi
    exact ⟨("ssz_offs", 64), by decide, by decide, hi⟩

end DecodeHostInput

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
