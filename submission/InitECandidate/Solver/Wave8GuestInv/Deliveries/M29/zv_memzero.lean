import InitECandidate.Solver.Wave8GuestInv.Deliveries.M29.Common

/-! Value contract `zv_memzero` for micro-shard `m29` (`wave8/contracts-m29`),
checked against frozen spec revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

`memzero(dst, n)` (AST line 251, index 17): on any normal return from an `ArenaReady` entry state,
every 8-byte aligned address `a` with `locN s "dst" ≤ a` and `a + 8 ≤ locN s "dst" + locN s "n"`
satisfies `memW post a = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8Contracts.M29

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Byte-level helpers for `panMemStoreHOL` and `panMemStoreByteWord8HOL` -/

private def memWordAt (mem : BitVec 64 → HolWordLab 64) (addr : BitVec 64) : BitVec 64 :=
  match mem addr with
  | .word w => w

private def memByteAt (mem : BitVec 64 → HolWordLab 64) (be : Bool) (addr : BitVec 64) : UInt8 :=
  panGetByteHOL addr (memWordAt mem (panByteAlignHOL addr)) be

private theorem panMemStoreByte_getByte_same {mem : BitVec 64 → HolWordLab 64}
    {dom : BitVec 64 → Prop} [DecidablePred dom] {be : Bool}
    {addr : BitVec 64} {b : UInt8} {mem' : BitVec 64 → HolWordLab 64}
    (hst : panMemStoreByteWord8HOL mem dom be addr (BitVec.ofNat 8 b.toNat) = some mem') :
    memByteAt mem' be addr = b ∧
    ∀ addr' : BitVec 64, addr' ≠ addr → memByteAt mem' be addr' = memByteAt mem be addr' := by
  unfold panMemStoreByteWord8HOL at hst
  dsimp only at hst
  cases hcell : mem (panByteAlignHOL addr) with
  | word cell =>
    rw [hcell] at hst
    split at hst
    · injection hst with hmem
      subst hmem
      have hb8 : b.toNat < 256 := b.toNat_lt_size
      have hb_mod : (BitVec.ofNat 8 b.toNat).toNat = b.toNat := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hb8
      have hset_nat := panSetByteHOL_toNat (width := 64) (by decide) addr cell b be
      have hpow_div : ∀ (x y z K : Nat), y < 256 → z < 2 ^ K →
          (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ K % 256 = y := by
        intro x y z K hy hz
        have hpK : 0 < 2 ^ K := Nat.two_pow_pos K
        have h1 : x * 2 ^ (K + 8) + y * 2 ^ K + z = z + (y + x * 256) * 2 ^ K := by
          rw [Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide, Nat.add_mul,
            Nat.mul_assoc x 256 (2 ^ K), Nat.mul_comm 256 (2 ^ K), ← Nat.mul_assoc]
          omega
        rw [h1, Nat.add_mul_div_right _ _ hpK, Nat.div_eq_of_lt hz, Nat.zero_add]
        omega
      have hpow_div_low : ∀ (x y z K J : Nat), y < 256 → z < 2 ^ K → J + 8 ≤ K →
          (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ J % 256 = z / 2 ^ J % 256 := by
        intro x y z K J _ _ hJK
        have hpJ : 0 < 2 ^ J := Nat.two_pow_pos J
        have hdK : 2 ^ K = 2 ^ (K - J - 8) * (256 * 2 ^ J) := by
          have hk_eq : K = (K - J - 8) + 8 + J := by omega
          conv_lhs => rw [hk_eq]
          rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide, Nat.mul_assoc]
        have hdK8 : 2 ^ (K + 8) = 2 ^ (K - J) * (256 * 2 ^ J) := by
          have hk_eq : K + 8 = (K - J) + 8 + J := by omega
          conv_lhs => rw [hk_eq]
          rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide, Nat.mul_assoc]
        have h1 : x * 2 ^ (K + 8) + y * 2 ^ K + z =
            z + ((x * 2 ^ (K - J) + y * 2 ^ (K - J - 8)) * 256) * 2 ^ J := by
          rw [hdK, hdK8, ← Nat.mul_assoc x, ← Nat.mul_assoc y, ← Nat.add_mul, ← Nat.mul_assoc]
          omega
        rw [h1, Nat.add_mul_div_right _ _ hpJ]
        omega
      have hpow_div_high : ∀ (x y z K J : Nat), y < 256 → z < 2 ^ K → K + 8 ≤ J →
          (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ J % 256 =
            (x * 2 ^ (K + 8)) / 2 ^ J % 256 := by
        intro x y z K J hy hz hKJ
        have hyz : y * 2 ^ K + z < 2 ^ (K + 8) := by
          have : y * 2 ^ K ≤ 255 * 2 ^ K := Nat.mul_le_mul_right _ (by omega)
          have h2 : 255 * 2 ^ K + 2 ^ K = 2 ^ (K + 8) := by
            rw [Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide]; omega
          omega
        have hdJ : 2 ^ J = 2 ^ (K + 8) * 2 ^ (J - (K + 8)) := by
          have hj_eq : J = (K + 8) + (J - (K + 8)) := by omega
          conv_lhs => rw [hj_eq]
          rw [Nat.pow_add]
        have hpK8 : 0 < 2 ^ (K + 8) := Nat.two_pow_pos _
        have hsum : x * 2 ^ (K + 8) + y * 2 ^ K + z = (y * 2 ^ K + z) + x * 2 ^ (K + 8) := by omega
        rw [hsum, hdJ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
          Nat.add_mul_div_right _ _ hpK8, Nat.div_eq_of_lt hyz, Nat.zero_add,
          Nat.mul_div_cancel _ hpK8]
      have hcell_high : ∀ J : Nat, byteBitIndex addr be + 8 ≤ J →
          ((cell.toNat / 2 ^ (byteBitIndex addr be + 8)) * 2 ^ (byteBitIndex addr be + 8)) / 2 ^ J =
            cell.toNat / 2 ^ J := by
        intro J hKJ
        have hdJ : 2 ^ J = 2 ^ (byteBitIndex addr be + 8) * 2 ^ (J - (byteBitIndex addr be + 8)) := by
          have hj_eq : J = (byteBitIndex addr be + 8) + (J - (byteBitIndex addr be + 8)) := by omega
          conv_lhs => rw [hj_eq]
          rw [Nat.pow_add]
        have hpK8 : 0 < 2 ^ (byteBitIndex addr be + 8) := Nat.two_pow_pos _
        rw [hdJ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ hpK8]
      have h256_pow : ∀ a : BitVec 64,
          (256 : Nat) ^ (if be then 8 - 1 - a.toNat % 8 else a.toNat % 8) = 2 ^ byteBitIndex a be := by
        intro a
        rw [pow256_eq_two_pow_mul]
        cases be <;> simp [byteBitIndex]
      constructor
      · simp only [memByteAt, memWordAt, ↓reduceIte, hb_mod, panGetByteHOL]
        have heq_nat : (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
            256 ^ (if be then 64 / 8 - 1 - addr.toNat % (64 / 8) else addr.toNat % (64 / 8)) % 256 =
            b.toNat := by
          change (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
              256 ^ (if be then 8 - 1 - addr.toNat % 8 else addr.toNat % 8) % 256 =
            b.toNat
          rw [hset_nat, h256_pow addr]
          exact hpow_div _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _))
        rw [heq_nat, UInt8.ofNat_toNat]
      · intro addr' hne
        by_cases hal : panByteAlignHOL addr' = panByteAlignHOL addr
        · simp only [memByteAt, memWordAt, hal, ↓reduceIte, hb_mod, hcell, panGetByteHOL]
          have hmod_ne : addr'.toNat % 8 ≠ addr.toNat % 8 := by
            intro hmeq
            apply hne
            apply BitVec.eq_of_toNat_eq
            have ha1 := panByteAlign_toNat64 addr'
            have ha2 := panByteAlign_toNat64 addr
            rw [hal] at ha1
            omega
          have hidx_sep : byteBitIndex addr' be + 8 ≤ byteBitIndex addr be ∨
              byteBitIndex addr be + 8 ≤ byteBitIndex addr' be := by
            have hm1 : addr'.toNat % 8 < 8 := by omega
            have hm2 : addr.toNat % 8 < 8 := by omega
            cases be <;> simp only [byteBitIndex, Bool.false_eq_true, if_true, if_false] <;> omega
          have heq_mod : (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
              256 ^ (if be then 64 / 8 - 1 - addr'.toNat % (64 / 8) else addr'.toNat % (64 / 8)) % 256 =
            cell.toNat / 256 ^ (if be then 64 / 8 - 1 - addr'.toNat % (64 / 8) else addr'.toNat % (64 / 8)) % 256 := by
            change (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
                256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256 =
              cell.toNat / 256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256
            rw [hset_nat, h256_pow addr']
            rcases hidx_sep with hlow | hhigh
            · rw [hpow_div_low _ _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _)) hlow]
              have hc_eq : 2 ^ byteBitIndex addr be =
                  (2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8)) * 256) *
                    2 ^ byteBitIndex addr' be := by
                have hk_eq : byteBitIndex addr be =
                    (byteBitIndex addr be - (byteBitIndex addr' be + 8)) + 8 + byteBitIndex addr' be := by omega
                conv_lhs => rw [hk_eq]
                rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide]
              have hcell_eq : cell.toNat =
                  cell.toNat % 2 ^ byteBitIndex addr be +
                  (((cell.toNat / 2 ^ byteBitIndex addr be) *
                    2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8))) * 256) *
                    2 ^ byteBitIndex addr' be := by
                have hdm := (Nat.div_add_mod cell.toNat (2 ^ byteBitIndex addr be)).symm
                rw [Nat.mul_comm (2 ^ byteBitIndex addr be)] at hdm
                have hmul : (cell.toNat / 2 ^ byteBitIndex addr be) * 2 ^ byteBitIndex addr be =
                    (((cell.toNat / 2 ^ byteBitIndex addr be) *
                      2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8))) * 256) *
                      2 ^ byteBitIndex addr' be := by
                  rw [hc_eq, ← Nat.mul_assoc, ← Nat.mul_assoc]
                rw [hmul] at hdm
                omega
              conv_rhs => rw [hcell_eq]
              rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)]
              omega
            · rw [hpow_div_high _ _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _)) hhigh,
                hcell_high _ hhigh]
          rw [heq_mod]
        · simp only [memByteAt, memWordAt, hal, ↓reduceIte]
    · cases hst

private theorem nat_eq_zero_of_digits_256_8 {u : Nat} (hu : u < 2 ^ 64)
    (hd : ∀ r : Nat, r < 8 → u / 256 ^ r % 256 = 0) : u = 0 := by
  have hstep : ∀ k : Nat, k ≤ 8 → u % 256 ^ k = 0 := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      have hklt : k < 8 := by omega
      have hprev := ih (by omega)
      have hdk := hd k hklt
      have hp1 : 256 ^ (k + 1) = 256 ^ k * 256 := Nat.pow_succ 256 k
      have hp_pos : 0 < 256 ^ k := Nat.pos_of_ne_zero (by positivity)
      have hlt_rem : (u / 256 ^ k % 256) * 256 ^ k + u % 256 ^ k < 256 ^ k * 256 := by
        have h1 : u / 256 ^ k % 256 ≤ 255 := by omega
        have h2 : (u / 256 ^ k % 256) * 256 ^ k ≤ 255 * 256 ^ k := Nat.mul_le_mul_right _ h1
        have h3 : u % 256 ^ k < 256 ^ k := Nat.mod_lt _ hp_pos
        omega
      have hx_eq : u = ((u / 256 ^ k % 256) * 256 ^ k + u % 256 ^ k) +
          (u / 256 ^ k / 256) * (256 ^ k * 256) := by
        calc u
          _ = 256 ^ k * (u / 256 ^ k) + u % 256 ^ k := (Nat.div_add_mod u (256 ^ k)).symm
          _ = 256 ^ k * (256 * (u / 256 ^ k / 256) + u / 256 ^ k % 256) + u % 256 ^ k := by
              rw [Nat.div_add_mod (u / 256 ^ k) 256]
          _ = ((u / 256 ^ k % 256) * 256 ^ k + u % 256 ^ k) +
              (u / 256 ^ k / 256) * (256 ^ k * 256) := by
              rw [Nat.left_distrib, Nat.mul_comm (256 ^ k) (u / 256 ^ k % 256),
                ← Nat.mul_assoc, Nat.mul_comm (256 ^ k * 256) (u / 256 ^ k / 256)]
              omega
      have hdecomp : u % 256 ^ (k + 1) = (u / 256 ^ k % 256) * 256 ^ k + u % 256 ^ k := by
        rw [hp1]
        conv_lhs => rw [hx_eq]
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt_rem]
      rw [hdecomp, hdk, hprev]
      omega
  have h8 := hstep 8 (le_refl 8)
  have hp8 : (256 ^ 8 : Nat) = 2 ^ 64 := by decide
  rw [hp8, Nat.mod_eq_of_lt hu] at h8
  exact h8

private theorem memW_eq_zero_of_bytes_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a : Nat) (ha8 : a % 8 = 0) (ha_lt : a + 8 ≤ heapEnd)
    (hb : ∀ r : Nat, r < 8 → memByteAt s.memory s.be (BitVec.ofNat 64 (a + r)) = 0) :
    memW s a = 0 := by
  have hhe : heapEnd < 2 ^ 64 := by decide
  have ha64 : a < 2 ^ 64 := by omega
  unfold memW
  cases hm : s.memory (BitVec.ofNat 64 a) with
  | word w =>
    dsimp only
    apply nat_eq_zero_of_digits_256_8 w.isLt
    intro k hk
    let r := if s.be then 7 - k else k
    have hr : r < 8 := by
      dsimp only [r]
      cases s.be
      · simp; omega
      · simp; omega
    have hidx : (if s.be then 8 - 1 - r else r) = k := by
      dsimp only [r]
      cases s.be
      · simp
      · simp; omega
    have har64 : a + r < 2 ^ 64 := by omega
    have hal : panByteAlignHOL (BitVec.ofNat 64 (a + r)) = BitVec.ofNat 64 a := by
      apply BitVec.eq_of_toNat_eq
      rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt har64,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64]
      omega
    have hmod_r : (BitVec.ofNat 64 (a + r)).toNat % 8 = r := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt har64]
      omega
    have hbr := congrArg UInt8.toNat (hb r hr)
    simp only [memByteAt, memWordAt, hal, hm, panGetByteHOL, UInt8.toNat_zero] at hbr
    change (UInt8.ofNat (w.toNat /
      256 ^ (if s.be then 8 - 1 - (BitVec.ofNat 64 (a + r)).toNat % 8 else (BitVec.ofNat 64 (a + r)).toNat % 8) %
      256)).toNat = 0 at hbr
    rw [hmod_r, hidx, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))] at hbr
    exact hbr

/-! ## 2. Prefix-zero invariant and step lemmas for `memzero` -/

private def ZeroPrefix {F : Type} (dst0 : BitVec 64) (len : Nat)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ b : Nat, dst0.toNat ≤ b → b < dst0.toNat + len →
    memByteAt s.memory s.be (BitVec.ofNat 64 b) = 0

private def MemzeroZeroInv {F : Type} (dst0 n0 : BitVec 64)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧ GuestInv s ∧
  s.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
  s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
  ∃ iw : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
    iw.toNat ≤ n0.toNat ∧
    ZeroPrefix dst0 iw.toNat s ∧
    (0 < iw.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + iw.toNat ≤ heapEnd)

private def noBreak : ProgHOL 64 → Bool
  | .break => false
  | .seq a b => noBreak a && noBreak b
  | .ite _ a b => noBreak a && noBreak b
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem evaluate_noBreak {F : Type} (p : ProgHOL 64) (hp : noBreak p = true)
    (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ some .break := by
  cases shape : p with
  | «break» => simp [shape, noBreak] at hp
  | skip => simp [evaluateHOLFiniteState_skip]
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noBreak] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · simp
      · split <;> simp
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | seq a b =>
    have hab : noBreak a = true ∧ noBreak b = true := by
      simpa [shape, noBreak, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noBreak a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha
    cases r with
    | none => exact evaluate_noBreak b hab.2 m
    | some _ => exact ha
  | ite _ a b =>
    have hab : noBreak a = true ∧ noBreak b = true := by
      simpa [shape, noBreak, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noBreak b hab.2 s
      · exact evaluate_noBreak a hab.1 s
    · simp
  | _ => simp [shape, noBreak] at hp

private def noReturn : ProgHOL 64 → Bool
  | .seq a b => noReturn a && noReturn b
  | .ite _ a b => noReturn a && noReturn b
  | .while _ a => noReturn a
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem evaluate_noReturn {F : Type} (p : ProgHOL 64) (hp : noReturn p = true)
    (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s p).1 ≠ some (.returned v) := by
  cases shape : p with
  | skip => simp [evaluateHOLFiniteState_skip]
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noReturn] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · simp
      · split <;> simp
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | seq a b =>
    have hab : noReturn a = true ∧ noReturn b = true := by
      simpa [shape, noReturn, Bool.and_eq_true] using hp
    have rem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noReturn a hab.1 s v
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha rem
    cases r with
    | none =>
      have mclk : m.clock ≤ s.clock := rem
      exact evaluate_noReturn b hab.2 m v
    | some _ => exact ha
  | ite _ a b =>
    have hab : noReturn a = true ∧ noReturn b = true := by
      simpa [shape, noReturn, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noReturn b hab.2 s v
      · exact evaluate_noReturn a hab.1 s v
    · simp
  | «while» cond body =>
    have hb : noReturn body = true := by simpa [shape, noReturn] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by
            simp only [decClockHOLFinite]; omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noReturn body hb (decClockHOLFinite s) v
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at rem
            omega
          cases r1 with
          | none =>
            exact evaluate_noReturn (.while cond body) (by simpa [noReturn] using hb) mid v
          | some r1 =>
            cases r1 with
            | «continue» =>
              exact evaluate_noReturn (.while cond body) (by simpa [noReturn] using hb) mid v
            | «break» | timeOut | error | finalFfi _ | exception _ _ => simp
            | returned _ => exact ih1
      · simp
    · simp
  | _ => simp [shape, noReturn] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

private theorem store_const_zero_zp {F : Type} {s : PanSemStateFiniteExact 64 F}
    {dst0 : BitVec 64} {len : Nat}
    (hG : GuestInv s) (hzp : ZeroPrefix dst0 len s)
    (addrExp : ExpHOL 64) (x : BitVec 64)
    (haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp =
      some (.val (.word x)))
    (hnone : (evaluateHOLFiniteState s (.store addrExp (.const 0))).1 = none) :
    sourceBase ≤ x.toNat ∧ x.toNat + 8 ≤ heapEnd ∧
    (x.toNat = dst0.toNat + len →
      ZeroPrefix dst0 (len + 8) (evaluateHOLFiniteState s (.store addrExp (.const 0))).2) := by
  rw [evaluateHOLFiniteState_store] at hnone ⊢
  rw [haddr] at hnone ⊢
  have hv0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const 0) =
      some (.val (.word 0)) := rfl
  dsimp only at hnone ⊢
  rw [hv0] at hnone ⊢
  dsimp only at hnone ⊢
  split at hnone
  · rename_i mem' hmem
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
    by_cases hdom : s.memaddrs x
    · simp only [hdom, ↓reduceIte, Option.some.injEq] at hmem
      subst hmem
      have hdom_ord : x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
        rw [hG.memaddrs, ordinaryDomain_iff] at hdom; exact hdom
      have hhe_mod : heapEnd % 8 = 0 := by decide
      have hhe_lt : heapEnd < 2 ^ 64 := by decide
      refine ⟨hdom_ord.2.1, by omega, fun hxeq b hblo hbhi => ?_⟩
      dsimp only
      have hb_lt : b < 2 ^ 64 := by omega
      by_cases hbin : b < dst0.toNat + len
      · have hal_ne : panByteAlignHOL (BitVec.ofNat 64 b) ≠ x := by
          intro heq
          have hc_nat := panByteAlign_toNat64 (BitVec.ofNat 64 b)
          rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_lt] at hc_nat
          omega
        simp only [memByteAt, memWordAt, hal_ne, ↓reduceIte]
        exact hzp b hblo hbin
      · have hal_eq : panByteAlignHOL (BitVec.ofNat 64 b) = x := by
          apply BitVec.eq_of_toNat_eq
          rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_lt]
          omega
        have hz_bv : (0 : BitVec 64).toNat = 0 := rfl
        simp only [memByteAt, memWordAt, hal_eq, ↓reduceIte, panGetByteHOL, hz_bv,
          Nat.zero_div, Nat.zero_mod]
        rfl
    · simp [hdom] at hmem
  · simp at hnone

private theorem storeByte_const_zero_zp {F : Type} {s : PanSemStateFiniteExact 64 F}
    {dst0 : BitVec 64} {len : Nat}
    (hG : GuestInv s) (hzp : ZeroPrefix dst0 len s)
    (addrExp : ExpHOL 64) (x : BitVec 64)
    (haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp =
      some (.val (.word x)))
    (hnone : (evaluateHOLFiniteState s (.storeByte addrExp (.const 0))).1 = none) :
    sourceBase ≤ x.toNat ∧ x.toNat + 1 ≤ heapEnd ∧
    (x.toNat = dst0.toNat + len →
      ZeroPrefix dst0 (len + 1) (evaluateHOLFiniteState s (.storeByte addrExp (.const 0))).2) := by
  rw [evaluateHOLFiniteState_storeByte] at hnone ⊢
  rw [haddr] at hnone ⊢
  have hv0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const 0) =
      some (.val (.word 0)) := rfl
  dsimp only at hnone ⊢
  rw [hv0] at hnone ⊢
  dsimp only at hnone ⊢
  split at hnone
  · rename_i mem' hmem
    have hdom : s.memaddrs (panByteAlignHOL x) := by
      by_contra hc
      unfold panMemStoreByteWord8HOL at hmem
      cases s.memory (panByteAlignHOL x) with
      | word _ => simp [hc] at hmem
    have hdom_ord : (panByteAlignHOL x).toNat % 8 = 0 ∧
        sourceBase ≤ (panByteAlignHOL x).toNat ∧ (panByteAlignHOL x).toNat < heapEnd := by
      rw [hG.memaddrs, ordinaryDomain_iff] at hdom; exact hdom
    have hhe_mod : heapEnd % 8 = 0 := by decide
    have hhe_lt : heapEnd < 2 ^ 64 := by decide
    have hal_nat := panByteAlign_toNat64 x
    refine ⟨by omega, by omega, fun hxeq b hblo hbhi => ?_⟩
    dsimp only
    have hb_lt : b < 2 ^ 64 := by omega
    have hst0 := @panMemStoreByte_getByte_same s.memory s.memaddrs
      (fun addr => Classical.propDecidable (s.memaddrs addr)) s.be x 0 mem' hmem
    by_cases hbx : b = x.toNat
    · have hbv : BitVec.ofNat 64 b = x := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_lt, hbx]
      rw [hbv]
      exact hst0.1
    · have hbv_ne : BitVec.ofNat 64 b ≠ x := by
        intro heq
        apply hbx
        have := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_lt] at this
        exact this
      rw [hst0.2 _ hbv_ne]
      exact hzp b hblo (by omega)
  · simp at hnone

private theorem eval_add2_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (d i : MlS) (x y : BitVec 64)
    (hx : s.locals.lookup d = some (.val (.word x)))
    (hy : s.locals.lookup i = some (.val (.word y))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local d, .var .local i]) = some (.val (.word (x + y))) := by
  simp [evalHOLExact, evalListHOLExact, hx, hy, valueIsWord, valueWord, wordOpHOL, wordOp]

private theorem eval_add3_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (d i : MlS) (x y c : BitVec 64)
    (hx : s.locals.lookup d = some (.val (.word x)))
    (hy : s.locals.lookup i = some (.val (.word y))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local d, .var .local i, .const c]) = some (.val (.word (x + y + c))) := by
  simp [evalHOLExact, evalListHOLExact, hx, hy, valueIsWord, valueWord, wordOpHOL, wordOp,
    BitVec.add_assoc]

private theorem seq_none_split {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64)
    (hG : GuestInv s) (dst0 n0 iw : BitVec 64)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (had : avoidsLocal (ofString "dst") a = true)
    (han : avoidsLocal (ofString "n") a = true)
    (hai : avoidsLocal (ofString "i") a = true)
    (h : (evaluateHOLFiniteState s (.seq a b)).1 = none) :
    (evaluateHOLFiniteState s a).1 = none ∧
    ∃ m : PanSemStateFiniteExact 64 F,
      m = (evaluateHOLFiniteState s a).2 ∧
      GuestInv m ∧
      m.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
      m.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
      m.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
      (evaluateHOLFiniteState m b).1 = none ∧
      (evaluateHOLFiniteState s (.seq a b)).2 = (evaluateHOLFiniteState m b).2 := by
  have h1 := h
  rw [evaluateHOLFiniteState_seq_line780] at h1
  rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
  cases r with
  | none =>
    have h1' : (evaluateHOLFiniteState m b).1 = none := by simpa [hr] using h1
    refine ⟨by simp [hr], m, by simp [hr], ?_, ?_, ?_, ?_, h1', ?_⟩
    · have hm := guestInv_evaluate s a hG; rw [hr] at hm; exact hm
    · have := evaluate_avoidsLocal_flowing (ofString "dst") a had s (by rw [hr]; exact Or.inl rfl)
      rw [hr] at this; exact this.trans hd
    · have := evaluate_avoidsLocal_flowing (ofString "n") a han s (by rw [hr]; exact Or.inl rfl)
      rw [hr] at this; exact this.trans hn
    · have := evaluate_avoidsLocal_flowing (ofString "i") a hai s (by rw [hr]; exact Or.inl rfl)
      rw [hr] at this; exact this.trans hi
    · rw [evaluateHOLFiniteState_seq_line780, hr]
  | some _ => simp [hr] at h1

private theorem step_domain_nowrap (dst0 iw n0 k : BitVec 64)
    (hle : iw.toNat ≤ n0.toNat)
    (hprev : 0 < iw.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + iw.toNat ≤ heapEnd)
    (hcur : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + k.toNat ≤ heapEnd)
    (hk : 0 < k.toNat) (hk32 : k.toNat ≤ 32)
    (hcond : ¬ (n0 < iw + k)) :
    (dst0 + iw).toNat = dst0.toNat + iw.toNat ∧
    (iw + k).toNat = iw.toNat + k.toNat ∧
      (iw + k).toNat ≤ n0.toNat ∧
      sourceBase ≤ dst0.toNat ∧ dst0.toNat + (iw + k).toNat ≤ heapEnd := by
  have hS : sourceBase = 2701131776 := by decide
  have hH : heapEnd = 33806089704 := by decide
  have hdlt := dst0.isLt
  have hilt := iw.isLt
  have hnlt := n0.isLt
  rw [BitVec.lt_def] at hcond
  by_cases hiz : iw.toNat = 0
  · have hi0 : iw = 0 := BitVec.eq_of_toNat_eq hiz
    subst hi0
    have hd0 : dst0 + 0 = dst0 := BitVec.add_zero _
    have hk0 : (0 : BitVec 64) + k = k := BitVec.zero_add _
    rw [hd0] at hcur ⊢
    rw [hk0] at hcond ⊢
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [hz0]
    exact ⟨by omega, by omega, by omega, hcur.1, hcur.2⟩
  · obtain ⟨hdlo, hdhi⟩ := hprev (by omega)
    have hadd_di : (dst0 + iw).toNat = dst0.toNat + iw.toNat :=
      BitVec.toNat_add_of_lt (by omega)
    rw [hadd_di] at hcur ⊢
    have hik_lt : iw.toNat + k.toNat < 2 ^ 64 := by omega
    have hadd_ik : (iw + k).toNat = iw.toNat + k.toNat :=
      BitVec.toNat_add_of_lt hik_lt
    rw [hadd_ik] at hcond ⊢
    exact ⟨rfl, rfl, by omega, hdlo, by omega⟩

private theorem eval_notLower_true {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n0 iw k w : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const k])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    ¬ (n0 < iw + k) := by
  simp [evalHOLExact, evalListHOLExact, hn, hi, valueIsWord, valueWord, wordOpHOL, wordOp,
    Compiler.Encoders.Asm.wordCmpHOL] at he
  intro hlt
  have hnotle : ¬ (iw + k ≤ n0) := by
    rw [BitVec.lt_def] at hlt
    rw [BitVec.le_def]
    omega
  simp [hnotle] at he
  exact hw he.symm

private theorem eval_lower_true {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n0 iw w : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word w)))
    (hw : w ≠ 0) :
    iw < n0 := by
  simp [evalHOLExact, hn, hi, Compiler.Encoders.Asm.wordCmpHOL] at he
  by_contra hge
  simp [hge] at he
  exact hw he.symm

private theorem eval_lower_false {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n0 iw : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word 0))) :
    ¬ (iw < n0) := by
  simp [evalHOLExact, hn, hi, Compiler.Encoders.Asm.wordCmpHOL] at he
  rw [BitVec.le_def] at he
  rw [BitVec.lt_def]
  omega

private theorem assign_i_zp {F : Type} {s : PanSemStateFiniteExact 64 F}
    {dst0 n0 iw k : BitVec 64}
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hzp : ZeroPrefix dst0 (iw + k).toNat s)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hle : (iw + k).toNat ≤ n0.toNat)
    (hdlo : sourceBase ≤ dst0.toNat) (hdhi : dst0.toNat + (iw + k).toNat ≤ heapEnd) :
    MemzeroZeroInv dst0 n0
      (evaluateHOLFiniteState s (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const k]))).2 := by
  have hrun : evaluateHOLFiniteState s
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const k])) =
      (none, setVarHOLFinite (ofString "i") (.val (.word (iw + k))) s) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi, wordOpHOL, wordOp,
      valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
      shapeOfHOLExact, shapeEqHOL]
  rw [hrun]
  dsimp only
  refine ⟨hc, guestInv_setVar _ _ s hG, ?_, ?_, iw + k, ?_, hle, hzp, fun _ => ⟨hdlo, hdhi⟩⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd, show ofString "i" ≠ ofString "dst" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "i" ≠ ofString "n" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

private theorem while_preserve_zp {F : Type} {dst0 n0 : BitVec 64}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hnb : noBreak body = true) (hnc : noTopContinue body = true)
    (hbody : ∀ (s : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      MemzeroZeroInv dst0 n0 s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word w)) → w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemzeroZeroInv dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2)
    (k : Nat) (s post : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k)
    (hinv : MemzeroZeroInv dst0 n0 s)
    (hrun : evaluateHOLFiniteState s (.while cond body) = (none, post)) :
    MemzeroZeroInv dst0 n0 post ∧
    @evalHOLExact 64 F _ post.toExact (fun a => Classical.propDecidable (post.memaddrs a)) cond =
      some (.val (.word 0)) := by
  induction k generalizing s with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun
        · simp at hrun
        · omega
      · rename_i hcw0
        have hw0 : cw = 0 := Classical.not_not.mp hcw0
        subst hw0
        injection hrun with _ hp
        subst hp
        exact ⟨hinv, hcond⟩
    · simp at hrun
  | succ k ih =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · rename_i hnz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have nb := evaluate_noBreak body hnb (decClockHOLFinite s)
          have nc := evaluate_noTopContinue body hnc (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at hrun rem nb nc
          cases r1 with
          | none =>
            have hmid : MemzeroZeroInv dst0 n0 mid := by
              have hb := hbody s cw hinv hcond hnz (by rw [hbr])
              rw [hbr] at hb; exact hb
            exact ih mid (by change mid.clock ≤ s.clock - 1 at rem; omega) hmid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl nc
            | «break» => exact absurd rfl nb
            | _ => simp at hrun
      · rename_i hcw0
        have hw0 : cw = 0 := Classical.not_not.mp hcw0
        subst hw0
        injection hrun with _ hp
        subst hp
        exact ⟨hinv, hcond⟩
    · simp at hrun

private theorem step_zp_loop1 {F : Type} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemzeroZeroInv dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 32])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0))
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8]) (.const 0))
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16]) (.const 0))
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24]) (.const 0))
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32]))))))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemzeroZeroInv dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hdst, hn, iw, hi, hle, hzp, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hzpd : ZeroPrefix dst0 iw.toNat sd := hzp
  have hnl := eval_notLower_true s n0 iw 32 w hn hi hcond hw
  have hH : heapEnd = 33806089704 := by decide
  obtain ⟨hs0, s1, hs1_eq, hG1, hd1, hn1, hi1, hr1, heq1⟩ :=
    seq_none_split sd _ _ hGd dst0 n0 iw hdst hn hi rfl rfl rfl hnone
  obtain ⟨hs8, s2, hs2_eq, hG2, hd2, hn2, hi2, hr2, heq2⟩ :=
    seq_none_split s1 _ _ hG1 dst0 n0 iw hd1 hn1 hi1 rfl rfl rfl hr1
  obtain ⟨hs16, s3, hs3_eq, hG3, hd3, hn3, hi3, hr3, heq3⟩ :=
    seq_none_split s2 _ _ hG2 dst0 n0 iw hd2 hn2 hi2 rfl rfl rfl hr2
  obtain ⟨hs24, s4, hs4_eq, hG4, hd4, hn4, hi4, _, heq4⟩ :=
    seq_none_split s3 _ _ hG3 dst0 n0 iw hd3 hn3 hi3 rfl rfl rfl hr3
  have st0 := store_const_zero_zp hGd hzpd _ (dst0 + iw) (eval_add2_locals sd _ _ dst0 iw hdst hi) hs0
  have hd8_raw := store_const_zero_zp hG1 (fun _ _ h => by omega : ZeroPrefix dst0 0 s1) _ (dst0 + iw + 8)
    (eval_add3_locals s1 _ _ dst0 iw 8 hd1 hi1) hs8
  have hd16_raw := store_const_zero_zp hG2 (fun _ _ h => by omega : ZeroPrefix dst0 0 s2) _ (dst0 + iw + 16)
    (eval_add3_locals s2 _ _ dst0 iw 16 hd2 hi2) hs16
  have hd24_raw := store_const_zero_zp hG3 (fun _ _ h => by omega : ZeroPrefix dst0 0 s3) _ (dst0 + iw + 24)
    (eval_add3_locals s3 _ _ dst0 iw 24 hd3 hi3) hs24
  have a8 : (dst0 + iw + 8).toNat = (dst0 + iw).toNat + 8 :=
    BitVec.toNat_add_of_lt (by have := st0.2.1; change (dst0 + iw).toNat + 8 < 2 ^ 64; omega)
  have a16 : (dst0 + iw + 16).toNat = (dst0 + iw).toNat + 16 := by
    have : (dst0 + iw).toNat + 8 + 8 ≤ heapEnd := by rw [← a8]; exact hd8_raw.2.1
    exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 16 < 2 ^ 64; omega)
  have a24 : (dst0 + iw + 24).toNat = (dst0 + iw).toNat + 24 := by
    have : (dst0 + iw).toNat + 16 + 8 ≤ heapEnd := by rw [← a16]; exact hd16_raw.2.1
    exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 24 < 2 ^ 64; omega)
  have hcur32 : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + (32 : BitVec 64).toNat ≤ heapEnd := by
    refine ⟨st0.1, ?_⟩
    have := hd24_raw.2.1; rw [a24] at this; change (dst0 + iw).toNat + 32 ≤ heapEnd; omega
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 32 hle hdom hcur32 (by decide) (by decide) hnl
  have hk32_val : (32 : BitVec 64).toNat = 32 := rfl
  have hzp1 : ZeroPrefix dst0 (iw.toNat + 8) s1 := by rw [hs1_eq]; exact st0.2.2 hdi_eq
  have hzp2 : ZeroPrefix dst0 (iw.toNat + 16) s2 := by
    rw [hs2_eq]
    exact (store_const_zero_zp hG1 hzp1 _ (dst0 + iw + 8)
      (eval_add3_locals s1 _ _ dst0 iw 8 hd1 hi1) hs8).2.2 (by omega)
  have hzp3 : ZeroPrefix dst0 (iw.toNat + 24) s3 := by
    rw [hs3_eq]
    exact (store_const_zero_zp hG2 hzp2 _ (dst0 + iw + 16)
      (eval_add3_locals s2 _ _ dst0 iw 16 hd2 hi2) hs16).2.2 (by omega)
  have hzp4 : ZeroPrefix dst0 (iw + 32).toNat s4 := by
    have h := (store_const_zero_zp hG3 hzp3 _ (dst0 + iw + 24)
      (eval_add3_locals s3 _ _ dst0 iw 24 hd3 hi3) hs24).2.2 (by omega)
    rw [← hs4_eq] at h
    have hik32 : (iw + 32).toNat = iw.toNat + 24 + 8 := by rw [hik_eq, hk32_val]
    rw [hik32]; exact h
  change MemzeroZeroInv dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1, heq2, heq3, heq4]
  exact assign_i_zp hG4.code hG4 hzp4 hd4 hn4 hi4 hle_ik hdlo hdhi

private theorem step_zp_loop2 {F : Type} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemzeroZeroInv dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemzeroZeroInv dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hdst, hn, iw, hi, hle, hzp, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hzpd : ZeroPrefix dst0 iw.toNat sd := hzp
  have hnl := eval_notLower_true s n0 iw 8 w hn hi hcond hw
  obtain ⟨hs0, s1, hs1_eq, hG1, hd1, hn1, hi1, _, heq1⟩ :=
    seq_none_split sd _ _ hGd dst0 n0 iw hdst hn hi rfl rfl rfl hnone
  have st0 := store_const_zero_zp hGd hzpd _ (dst0 + iw) (eval_add2_locals sd _ _ dst0 iw hdst hi) hs0
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom ⟨st0.1, st0.2.1⟩ (by decide) (by decide) hnl
  have hk8_val : (8 : BitVec 64).toNat = 8 := rfl
  have hzp1 : ZeroPrefix dst0 (iw + 8).toNat s1 := by
    have h := st0.2.2 hdi_eq
    rw [← hs1_eq] at h
    rw [hik_eq, hk8_val]; exact h
  change MemzeroZeroInv dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1]
  exact assign_i_zp hG1.code hG1 hzp1 hd1 hn1 hi1 hle_ik hdlo hdhi

private theorem step_zp_loop3 {F : Type} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemzeroZeroInv dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0))
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1]) (.const 0))
          (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2]) (.const 0))
            (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3]) (.const 0))
              (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4]) (.const 0))
                (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5]) (.const 0))
                  (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6]) (.const 0))
                    (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7]) (.const 0))
                      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))))))))))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemzeroZeroInv dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hdst, hn, iw, hi, hle, hzp, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hzpd : ZeroPrefix dst0 iw.toNat sd := hzp
  have hnl := eval_notLower_true s n0 iw 8 w hn hi hcond hw
  have hH : heapEnd = 33806089704 := by decide
  obtain ⟨hs0, s1, hs1_eq, hG1, hd1, hn1, hi1, hr1, heq1⟩ :=
    seq_none_split sd _ _ hGd dst0 n0 iw hdst hn hi rfl rfl rfl hnone
  obtain ⟨hs1, s2, hs2_eq, hG2, hd2, hn2, hi2, hr2, heq2⟩ :=
    seq_none_split s1 _ _ hG1 dst0 n0 iw hd1 hn1 hi1 rfl rfl rfl hr1
  obtain ⟨hs2, s3, hs3_eq, hG3, hd3, hn3, hi3, hr3, heq3⟩ :=
    seq_none_split s2 _ _ hG2 dst0 n0 iw hd2 hn2 hi2 rfl rfl rfl hr2
  obtain ⟨hs3, s4, hs4_eq, hG4, hd4, hn4, hi4, hr4, heq4⟩ :=
    seq_none_split s3 _ _ hG3 dst0 n0 iw hd3 hn3 hi3 rfl rfl rfl hr3
  obtain ⟨hs4, s5, hs5_eq, hG5, hd5, hn5, hi5, hr5, heq5⟩ :=
    seq_none_split s4 _ _ hG4 dst0 n0 iw hd4 hn4 hi4 rfl rfl rfl hr4
  obtain ⟨hs5, s6, hs6_eq, hG6, hd6, hn6, hi6, hr6, heq6⟩ :=
    seq_none_split s5 _ _ hG5 dst0 n0 iw hd5 hn5 hi5 rfl rfl rfl hr5
  obtain ⟨hs6, s7, hs7_eq, hG7, hd7, hn7, hi7, hr7, heq7⟩ :=
    seq_none_split s6 _ _ hG6 dst0 n0 iw hd6 hn6 hi6 rfl rfl rfl hr6
  obtain ⟨hs7, s8, hs8_eq, hG8, hd8, hn8, hi8, _, heq8⟩ :=
    seq_none_split s7 _ _ hG7 dst0 n0 iw hd7 hn7 hi7 rfl rfl rfl hr7
  have b0 := storeByte_const_zero_zp hGd hzpd _ (dst0 + iw) (eval_add2_locals sd _ _ dst0 iw hdst hi) hs0
  have b7_raw := storeByte_const_zero_zp hG7 (fun _ _ h => by omega : ZeroPrefix dst0 0 s7) _ (dst0 + iw + 7)
    (eval_add3_locals s7 _ _ dst0 iw 7 hd7 hi7) hs7
  have a1 : (dst0 + iw + 1).toNat = (dst0 + iw).toNat + 1 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 1 < 2 ^ 64; omega)
  have a2 : (dst0 + iw + 2).toNat = (dst0 + iw).toNat + 2 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 2 < 2 ^ 64; omega)
  have a3 : (dst0 + iw + 3).toNat = (dst0 + iw).toNat + 3 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 3 < 2 ^ 64; omega)
  have a4 : (dst0 + iw + 4).toNat = (dst0 + iw).toNat + 4 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 4 < 2 ^ 64; omega)
  have a5 : (dst0 + iw + 5).toNat = (dst0 + iw).toNat + 5 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 5 < 2 ^ 64; omega)
  have a6 : (dst0 + iw + 6).toNat = (dst0 + iw).toNat + 6 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 6 < 2 ^ 64; omega)
  have a7 : (dst0 + iw + 7).toNat = (dst0 + iw).toNat + 7 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 7 < 2 ^ 64; omega)
  have hcur8 : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + (8 : BitVec 64).toNat ≤ heapEnd := by
    refine ⟨b0.1, ?_⟩
    have := b7_raw.2.1; rw [a7] at this; change (dst0 + iw).toNat + 8 ≤ heapEnd; omega
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom hcur8 (by decide) (by decide) hnl
  have hk8_val : (8 : BitVec 64).toNat = 8 := rfl
  have hzp1 : ZeroPrefix dst0 (iw.toNat + 1) s1 := by rw [hs1_eq]; exact b0.2.2 hdi_eq
  have hzp2 : ZeroPrefix dst0 (iw.toNat + 2) s2 := by
    rw [hs2_eq]; exact (storeByte_const_zero_zp hG1 hzp1 _ (dst0 + iw + 1) (eval_add3_locals s1 _ _ dst0 iw 1 hd1 hi1) hs1).2.2 (by omega)
  have hzp3 : ZeroPrefix dst0 (iw.toNat + 3) s3 := by
    rw [hs3_eq]; exact (storeByte_const_zero_zp hG2 hzp2 _ (dst0 + iw + 2) (eval_add3_locals s2 _ _ dst0 iw 2 hd2 hi2) hs2).2.2 (by omega)
  have hzp4 : ZeroPrefix dst0 (iw.toNat + 4) s4 := by
    rw [hs4_eq]; exact (storeByte_const_zero_zp hG3 hzp3 _ (dst0 + iw + 3) (eval_add3_locals s3 _ _ dst0 iw 3 hd3 hi3) hs3).2.2 (by omega)
  have hzp5 : ZeroPrefix dst0 (iw.toNat + 5) s5 := by
    rw [hs5_eq]; exact (storeByte_const_zero_zp hG4 hzp4 _ (dst0 + iw + 4) (eval_add3_locals s4 _ _ dst0 iw 4 hd4 hi4) hs4).2.2 (by omega)
  have hzp6 : ZeroPrefix dst0 (iw.toNat + 6) s6 := by
    rw [hs6_eq]; exact (storeByte_const_zero_zp hG5 hzp5 _ (dst0 + iw + 5) (eval_add3_locals s5 _ _ dst0 iw 5 hd5 hi5) hs5).2.2 (by omega)
  have hzp7 : ZeroPrefix dst0 (iw.toNat + 7) s7 := by
    rw [hs7_eq]; exact (storeByte_const_zero_zp hG6 hzp6 _ (dst0 + iw + 6) (eval_add3_locals s6 _ _ dst0 iw 6 hd6 hi6) hs6).2.2 (by omega)
  have hzp8 : ZeroPrefix dst0 (iw + 8).toNat s8 := by
    have h := (storeByte_const_zero_zp hG7 hzp7 _ (dst0 + iw + 7) (eval_add3_locals s7 _ _ dst0 iw 7 hd7 hi7) hs7).2.2 (by omega)
    rw [← hs8_eq] at h
    have hik8 : (iw + 8).toNat = iw.toNat + 7 + 1 := by rw [hik_eq, hk8_val]
    rw [hik8]; exact h
  change MemzeroZeroInv dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8]
  exact assign_i_zp hG8.code hG8 hzp8 hd8 hn8 hi8 hle_ik hdlo hdhi

private theorem step_zp_loop4 {F : Type} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemzeroZeroInv dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemzeroZeroInv dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hdst, hn, iw, hi, hle, hzp, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hzpd : ZeroPrefix dst0 iw.toNat sd := hzp
  have hlt := eval_lower_true s n0 iw w hn hi hcond hw
  rw [BitVec.lt_def] at hlt
  obtain ⟨hs0, s1, hs1_eq, hG1, hd1, hn1, hi1, _, heq1⟩ :=
    seq_none_split sd _ _ hGd dst0 n0 iw hdst hn hi rfl rfl rfl hnone
  have b0 := storeByte_const_zero_zp hGd hzpd _ (dst0 + iw) (eval_add2_locals sd _ _ dst0 iw hdst hi) hs0
  have hnlt := n0.isLt
  have ha1 : (iw + 1).toNat = iw.toNat + 1 :=
    BitVec.toNat_add_of_lt (by change iw.toNat + 1 < 2 ^ 64; omega)
  have hnl : ¬ (n0 < iw + 1) := by rw [BitVec.lt_def, ha1]; omega
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 1 hle hdom ⟨b0.1, b0.2.1⟩ (by decide) (by decide) hnl
  have hk1_val : (1 : BitVec 64).toNat = 1 := rfl
  have hzp1 : ZeroPrefix dst0 (iw + 1).toNat s1 := by
    have h := b0.2.2 hdi_eq
    rw [← hs1_eq] at h
    rw [hik_eq, hk1_val]; exact h
  change MemzeroZeroInv dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1]
  exact assign_i_zp hG1.code hG1 hzp1 hd1 hn1 hi1 hle_ik hdlo hdhi

private theorem setVar_lookup_ne {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : MlS)
    (v : ValueHOL 64) (h : b ≠ a) :
    (setVarHOLFinite a v s).locals.lookup b = s.locals.lookup b := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h]

/-! ## 3. Main theorem `zv_memzero` -/

/-- `memzero` (AST line 251): zero-fills `[dst, dst + n)` (value contract). -/
theorem «zv_memzero» :
    ZeroFills (ofString "memzero") := by
  refine ⟨_, _, _, lookup_memzero, ?_⟩
  intro F s hcode hAR _ _hnt v hret a ha_lo ha_hi ha8
  have hG : GuestInv s := hAR.1
  revert hret
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memzero,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · simp
  · rename_i iv hiv
    have hiv_eq : iv = .val (.word 0) := by
      simp [evalHOLExact] at hiv; exact hiv.symm
    subst hiv_eq
    split
    · set s1 := setVarHOLFinite (ofString "i") (.val (.word 0)) s with hs1
      rw [evaluateHOLFiniteState_seq_line780]
      set iteProg : ProgHOL 64 := .ite _ _ .skip
      have hite_nr : noReturn iteProg = true := rfl
      rcases hite_run : evaluateHOLFiniteState s1 iteProg with ⟨r_ite, s2⟩
      cases r_ite with
      | some _ =>
        intro hret
        have hnr := evaluate_noReturn iteProg hite_nr s1 v
        rw [hite_run] at hnr
        exact absurd hret hnr
      | none =>
        dsimp only
        have hdst_word : ∃ dst0 : BitVec 64,
            s.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
              dst0.toNat = locN s "dst" := by
          have hc_ite : (evaluateHOLFiniteState s1 iteProg).1 = none := by rw [hite_run]
          dsimp only [iteProg] at hc_ite
          rw [evaluateHOLFiniteState_ite] at hc_ite
          split at hc_ite
          · rename_i cw hcond
            simp only [evalHOLExact, evalListHOLExact] at hcond
            have hdl : s1.locals.lookup (ofString "dst") = s.locals.lookup (ofString "dst") :=
              setVar_lookup_ne s (ofString "i") (ofString "dst") _ (by decide)
            rw [hdl] at hcond
            rcases hd : s.locals.lookup (ofString "dst") with _ | dv
            · simp [hd] at hcond
            · rcases dv with ⟨⟨w⟩⟩ | _ | _
              · exact ⟨w, rfl, by simp [locN, hd]⟩
              · simp [hd, List.all, valueIsWord] at hcond
              · simp [hd, List.all, valueIsWord] at hcond
          · simp at hc_ite
        obtain ⟨dst0, hdst0, hdst0_eq⟩ := hdst_word
        rw [evaluateHOLFiniteState_seq_line780]
        set loop3 : ProgHOL 64 := .while _ _
        have hl3_nr : noReturn loop3 = true := rfl
        rcases hw3 : evaluateHOLFiniteState s2 loop3 with ⟨rw3, s3⟩
        cases rw3 with
        | some _ =>
          intro hret
          have hnr := evaluate_noReturn loop3 hl3_nr s2 v
          rw [hw3] at hnr
          exact absurd hret hnr
        | none =>
          dsimp only
          have hn_word : ∃ n0 : BitVec 64,
              s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
                n0.toNat = locN s "n" := by
            have hn2 : s2.locals.lookup (ofString "n") = s.locals.lookup (ofString "n") := by
              have h1 := evaluate_avoidsLocal_flowing (ofString "n") iteProg rfl s1 (by rw [hite_run]; exact Or.inl rfl)
              rw [hite_run] at h1
              exact h1.trans (setVar_lookup_ne s (ofString "i") (ofString "n") _ (by decide))
            have hc3 : (evaluateHOLFiniteState s2 loop3).1 = none := by rw [hw3]
            dsimp only [loop3] at hc3
            rw [evaluateHOLFiniteState_while_total] at hc3
            split at hc3
            · rename_i cw hcond
              unfold PanSemStateFiniteExact.evalHOLFinite at hcond
              simp only [evalHOLExact, hn2] at hcond
              rcases hn_lk : s.locals.lookup (ofString "n") with _ | nv
              · simp [hn_lk] at hcond
              · rcases nv with ⟨⟨w⟩⟩ | _ | _
                · exact ⟨w, rfl, by simp [locN, hn_lk]⟩
                · simp [hn_lk] at hcond
                · simp [hn_lk] at hcond
            · simp at hc3
          obtain ⟨n0, hn0, hn0_eq⟩ := hn_word
          have hinv1 : MemzeroZeroInv dst0 n0 s1 := by
            have hz0 : (0 : BitVec 64).toNat = 0 := rfl
            refine ⟨hcode, guestInv_setVar _ _ s hG, ?_, ?_, 0, ?_,
              Nat.zero_le _, fun _ hlo hhi => by rw [hz0] at hhi; omega, fun h => by simp at h⟩
            · rw [hs1, setVar_lookup_ne s (ofString "i") (ofString "dst") _ (by decide), hdst0]
            · rw [hs1, setVar_lookup_ne s (ofString "i") (ofString "n") _ (by decide), hn0]
            · simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hinv2 : MemzeroZeroInv dst0 n0 s2 := by
            dsimp only [iteProg] at hite_run
            rw [evaluateHOLFiniteState_ite] at hite_run
            split at hite_run
            · split at hite_run
              · rw [evaluateHOLFiniteState_skip] at hite_run
                injection hite_run with _ hs2
                rw [← hs2]; exact hinv1
              · rw [evaluateHOLFiniteState_seq_line780] at hite_run
                rcases hw1 : evaluateHOLFiniteState s1 _ with ⟨rw1, m1⟩
                rw [hw1] at hite_run
                cases rw1 with
                | some _ => simp at hite_run
                | none =>
                  dsimp only at hite_run
                  have hm1 := (while_preserve_zp _ _ rfl rfl step_zp_loop1 s1.clock s1 m1 le_rfl hinv1 hw1).1
                  exact (while_preserve_zp _ _ rfl rfl step_zp_loop2 m1.clock m1 s2 le_rfl hm1 hite_run).1
            · simp at hite_run
          have hinv3 := (while_preserve_zp _ _ rfl rfl step_zp_loop3 s2.clock s2 s3 le_rfl hinv2 hw3).1
          rw [evaluateHOLFiniteState_seq_line780]
          set loop4 : ProgHOL 64 := .while _ _
          have hl4_nr : noReturn loop4 = true := rfl
          rcases hw4 : evaluateHOLFiniteState s3 loop4 with ⟨rw4, s4⟩
          cases rw4 with
          | some _ =>
            intro hret
            have hnr := evaluate_noReturn loop4 hl4_nr s3 v
            rw [hw4] at hnr
            exact absurd hret hnr
          | none =>
            dsimp only
            obtain ⟨hinv4, hcond4⟩ :=
              while_preserve_zp _ _ rfl rfl step_zp_loop4 s3.clock s3 s4 le_rfl hinv3 hw4
            have hret_eval : evaluateHOLFiniteState s4 (.return (.const 0#64)) =
                (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite s4) := by
              simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact,
                sizeOfShapeWithContextHOL]
            rw [hret_eval]
            dsimp only
            intro _
            obtain ⟨_, _, _, hn4, iw4, hi4, hle4, hzp4, hdom4⟩ := hinv4
            have hge4 : ¬ (iw4 < n0) := eval_lower_false s4 n0 iw4 hn4 hi4 hcond4
            have hiw_eq : iw4.toNat = n0.toNat := by
              rw [BitVec.lt_def] at hge4
              omega
            rw [← hdst0_eq] at ha_lo ha_hi
            rw [← hn0_eq] at ha_hi
            have hn_pos : 0 < iw4.toNat := by omega
            obtain ⟨_, hdhi4⟩ := hdom4 hn_pos
            rw [hiw_eq] at hzp4 hdhi4
            have ha_lt_he : a + 8 ≤ heapEnd := by omega
            have hbytes : ∀ r : Nat, r < 8 →
                memByteAt s4.memory s4.be (BitVec.ofNat 64 (a + r)) = 0 := by
              intro r hr
              exact hzp4 (a + r) (by omega) (by omega)
            have hm4 := memW_eq_zero_of_bytes_zero s4 a ha8 ha_lt_he hbytes
            exact hm4
    · simp

end InitECandidate.Solver.Wave8Contracts.M29
