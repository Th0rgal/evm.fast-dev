import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01Common

/-! Exact cell-frame, byte-copy, and metadata preservation for `memcpy(dst, src, n)` on normal return
under `GuestInv` (adapted from `HtabC00Ports/MemcpyFrame.lean` over prebuilt `WkShard01Common`). -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Backend
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

theorem memcpy_ordinaryDomain_iff (x : BitVec 64) :
    ordinaryDomain x ↔ x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
  unfold ordinaryDomain
  rw [StackRemove.mem_addresses]
  have hx := x.isLt
  have hconst : (stackStart - sourceBase) / 8 - globalsWords = 3888119741 ∧
      sourceBase = 2701131776 ∧ heapEnd = 33806089704 ∧
      StackRemove.bytesInWord 64 = BitVec.ofNat 64 8 := by
    refine ⟨by decide, by decide, by decide, ?_⟩
    decide
  rcases hconst with ⟨hn, hsb, hhe, hbw⟩
  rw [hn, hbw]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    simp only [hsb, hhe]
    omega
  · rintro ⟨hal, hlo, hhi⟩
    refine ⟨(x.toNat - sourceBase) / 8, by simp only [hsb, hhe] at hlo hhi; omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    simp only [hsb, hhe] at hlo hhi ⊢
    omega

private theorem panMemStoreByte_getByte_eq_and_other {mem : BitVec 64 → HolWordLab 64}
    {dom : BitVec 64 → Prop} [DecidablePred dom] {be : Bool}
    {addr : BitVec 64} {bw : BitVec 8} {mem' : BitVec 64 → HolWordLab 64}
    (hst : panMemStoreByteWord8HOL mem dom be addr bw = some mem') :
    (match mem' (panByteAlignHOL addr) with | .word v => (panGetByteHOL addr v be).toNat) = bw.toNat ∧
    ∀ addr' : BitVec 64, addr' ≠ addr →
      (match mem' (panByteAlignHOL addr') with | .word v => (panGetByteHOL addr' v be).toNat) =
      (match mem (panByteAlignHOL addr') with | .word v => (panGetByteHOL addr' v be).toNat) := by
  unfold panMemStoreByteWord8HOL at hst
  dsimp only at hst
  cases hcell : mem (panByteAlignHOL addr) with
  | word cell =>
    rw [hcell] at hst
    split at hst
    · injection hst with hmem
      subst hmem
      let b : UInt8 := UInt8.ofNat bw.toNat
      have hb8 : b.toNat < 256 := b.toNat_lt_size
      have hbw_eq : bw.toNat = b.toNat := by
        have := bw.isLt
        simp [b, UInt8.toNat_ofNat', Nat.mod_eq_of_lt this]
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
      · simp only [↓reduceIte, hbw_eq, panGetByteHOL]
        have heq_nat : (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
            256 ^ (if be then 8 - 1 - addr.toNat % 8 else addr.toNat % 8) % 256 = b.toNat := by
          rw [hset_nat, h256_pow addr]
          exact hpow_div _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _))
        change (UInt8.ofNat ((panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
            256 ^ (if be then 8 - 1 - addr.toNat % 8 else addr.toNat % 8) % 256)).toNat = b.toNat
        rw [heq_nat, UInt8.ofNat_toNat]
      · intro addr' hne
        by_cases hal : panByteAlignHOL addr' = panByteAlignHOL addr
        · simp only [hal, ↓reduceIte, hbw_eq, hcell, panGetByteHOL]
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
              256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256 =
            cell.toNat / 256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256 := by
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
          simpa [UInt8.toNat_ofNat'] using heq_mod
        · simp only [hal, ↓reduceIte]
    · cases hst

/-- Byte-level memory write frame: metadata and globals preserved, cell-level `FrameOutside` on `[ivl]`,
byte-level `memB` equality outside `ivl`, and every modified cell lies in `ordinaryDomain`. -/
def MemWriteFrame {F : Type} (s0 s : PanSemStateFiniteExact 64 F) (ivl : Ivl) : Prop :=
  s.code = s0.code ∧ s.memaddrs = s0.memaddrs ∧ s.shMemaddrs = s0.shMemaddrs ∧
  s.baseAddr = s0.baseAddr ∧ s.be = s0.be ∧ s.globals = s0.globals ∧
  FrameOutside s0 s [ivl] (0, 0) ∧
  (∀ a : Nat, a < 2 ^ 64 → ¬ InIvl a ivl → memB s a = memB s0 a) ∧
  (∀ a : BitVec 64, s.memory a ≠ s0.memory a → s0.memaddrs a)

theorem memWriteFrame_refl {F : Type} (s0 : PanSemStateFiniteExact 64 F) (ivl : Ivl) :
    MemWriteFrame s0 s0 ivl :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ h => absurd rfl h⟩

theorem memWriteFrame_locals_clock {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {ivl : Ivl} (h : MemWriteFrame s0 s ivl) (loc : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    MemWriteFrame s0 { s with locals := loc, clock := k } ivl :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

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

private def noRet : ProgHOL 64 → Bool
  | .seq a b => noRet a && noRet b
  | .ite _ a b => noRet a && noRet b
  | .while _ a => noRet a
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem evaluate_noRet {F : Type} (p : ProgHOL 64) (hp : noRet p = true)
    (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s p).1 ≠ some (.returned v) := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; simp
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noRet] at hp
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
    have hab : noRet a = true ∧ noRet b = true := by
      simpa [shape, noRet, Bool.and_eq_true] using hp
    have rem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noRet a hab.1 s v
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha rem
    cases r with
    | none =>
      have mclk : m.clock ≤ s.clock := rem
      exact evaluate_noRet b hab.2 m v
    | some _ => exact ha
  | ite _ a b =>
    have hab : noRet a = true ∧ noRet b = true := by
      simpa [shape, noRet, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noRet b hab.2 s v
      · exact evaluate_noRet a hab.1 s v
    · simp
  | «while» cond body =>
    have hb : noRet body = true := by simpa [shape, noRet] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · rename_i nonzero
          have dec_lt : (decClockHOLFinite s).clock < s.clock := by
            simp only [decClockHOLFinite]; omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noRet body hb (decClockHOLFinite s) v
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at rem
            omega
          cases r1 with
          | none =>
            exact evaluate_noRet (.while cond body) (by simpa [noRet] using hb) mid v
          | some r1 =>
            cases r1 with
            | «continue» =>
              exact evaluate_noRet (.while cond body) (by simpa [noRet] using hb) mid v
            | «break» => simp
            | returned _ => exact ih1
            | exception _ _ => simp
            | timeOut => simp
            | error => simp
            | finalFfi _ => simp
      · simp
    · simp
  | _ => simp [shape, noRet] at hp
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

/-- Copy relation on bytes `[0, i)` when `dst` and `src` are disjoint:
for every `j < i`, `memB s (dst + j) = memB s0 (src + j)`. -/
def BytesCopiedUpTo {F : Type} (s0 s : PanSemStateFiniteExact 64 F)
    (dst0 src0 : BitVec 64) (len i : Nat) : Prop :=
  Disj (dst0.toNat, len) (src0.toNat, len) →
    src0.toNat + len ≤ 2 ^ 64 →
    ∀ j, j < i → memB s (dst0.toNat + j) = memB s0 (src0.toNat + j)

private theorem nat_eq_of_digits_256_8 {u v : Nat} (hu : u < 2 ^ 64) (hv : v < 2 ^ 64)
    (hd : ∀ r : Nat, r < 8 → u / 256 ^ r % 256 = v / 256 ^ r % 256) : u = v := by
  have hstep : ∀ k : Nat, k ≤ 8 → u % 256 ^ k = v % 256 ^ k := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      have hklt : k < 8 := by omega
      have hprev := ih (by omega)
      have hdk := hd k hklt
      have hp1 : 256 ^ (k + 1) = 256 ^ k * 256 := Nat.pow_succ 256 k
      have hdecomp : ∀ x : Nat, x % 256 ^ (k + 1) = (x / 256 ^ k % 256) * 256 ^ k + x % 256 ^ k := by
        intro x
        rw [hp1]
        have hdm := (Nat.div_add_mod (x % (256 ^ k * 256)) (256 ^ k)).symm
        have hdiv : (x % (256 ^ k * 256)) / 256 ^ k = x / 256 ^ k % 256 := by
          rw [Nat.mod_mul_right_div_self]
        have hmod : (x % (256 ^ k * 256)) % 256 ^ k = x % 256 ^ k :=
          Nat.mod_mul_right_mod x (256 ^ k) 256
        rw [hdiv, hmod, Nat.mul_comm (256 ^ k) (x / 256 ^ k % 256)] at hdm
        exact hdm
      rw [hdecomp u, hdecomp v, hdk, hprev]
  have h8 : 256 ^ 8 = 2 ^ 64 := by decide
  have heq := hstep 8 (le_refl _)
  rw [h8, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] at heq
  exact heq

/-- Two aligned words in memory are equal (`memW`) when all 8 of their bytes (`memB`) agree
under the same endianness `be`. -/
theorem memW_eq_of_memB_eq {F : Type} (s1 s2 : PanSemStateFiniteExact 64 F)
    (a1 a2 : Nat) (hbe : s1.be = s2.be)
    (ha1 : a1 % 8 = 0) (ha2 : a2 % 8 = 0)
    (h1 : a1 + 8 ≤ 2 ^ 64) (h2 : a2 + 8 ≤ 2 ^ 64)
    (hbytes : ∀ r, r < 8 → memB s1 (a1 + r) = memB s2 (a2 + r)) :
    memW s1 a1 = memW s2 a2 := by
  have hal_off : ∀ (a r : Nat), a % 8 = 0 → a + 8 ≤ 2 ^ 64 → r < 8 →
      panByteAlignHOL (BitVec.ofNat 64 (a + r)) = BitVec.ofNat 64 a ∧
      (BitVec.ofNat 64 (a + r)).toNat % 8 = r := by
    intro a r ha8 ha_lt hr
    have har : (BitVec.ofNat 64 (a + r)).toNat = a + r := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine ⟨?_, by omega⟩
    apply BitVec.eq_of_toNat_eq
    rw [panByteAlign_toNat64, har, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  unfold memW
  rcases hw1 : s1.memory (BitVec.ofNat 64 a1) with ⟨w1⟩
  rcases hw2 : s2.memory (BitVec.ofNat 64 a2) with ⟨w2⟩
  dsimp only
  apply nat_eq_of_digits_256_8 w1.isLt w2.isLt
  intro k hk
  let r := if s2.be then 7 - k else k
  have hr : r < 8 := by cases hb_flag : s2.be <;> simp only [r, hb_flag, Bool.false_eq_true, if_true, if_false] <;> omega
  have hidx : (if s2.be then 8 - 1 - r else r) = k := by cases hb_flag : s2.be <;> simp only [r, hb_flag, Bool.false_eq_true, if_true, if_false] <;> omega
  have hb := hbytes r hr
  obtain ⟨hp1, hm1⟩ := hal_off a1 r ha1 h1 hr
  obtain ⟨hp2, hm2⟩ := hal_off a2 r ha2 h2 hr
  unfold memB at hb
  rw [hp1, hp2, hw1, hw2, hbe] at hb
  dsimp only [panGetByteHOL] at hb
  change (UInt8.ofNat (w1.toNat /
      256 ^ (if s2.be then 8 - 1 - (BitVec.ofNat 64 (a1 + r)).toNat % 8 else (BitVec.ofNat 64 (a1 + r)).toNat % 8) % 256)).toNat =
    (UInt8.ofNat (w2.toNat /
      256 ^ (if s2.be then 8 - 1 - (BitVec.ofNat 64 (a2 + r)).toNat % 8 else (BitVec.ofNat 64 (a2 + r)).toNat % 8) % 256)).toNat at hb
  rw [hm1, hm2, hidx, UInt8.toNat_ofNat', UInt8.toNat_ofNat',
    Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)),
    Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))] at hb
  exact hb

/-- Conversely, copying an aligned word `s.memory y` into `x` copies all 8 bytes `memB` from `y` to `x`! -/
theorem memB_eq_of_word_eq {F : Type} (s1 s2 : PanSemStateFiniteExact 64 F)
    (a1 a2 r : Nat) (hbe : s1.be = s2.be)
    (ha1 : a1 % 8 = 0) (ha2 : a2 % 8 = 0)
    (h1 : a1 + 8 ≤ 2 ^ 64) (h2 : a2 + 8 ≤ 2 ^ 64) (hr : r < 8)
    (hw : s1.memory (BitVec.ofNat 64 a1) = s2.memory (BitVec.ofNat 64 a2)) :
    memB s1 (a1 + r) = memB s2 (a2 + r) := by
  have har1 : (BitVec.ofNat 64 (a1 + r)).toNat = a1 + r := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have har2 : (BitVec.ofNat 64 (a2 + r)).toNat = a2 + r := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hp1 : panByteAlignHOL (BitVec.ofNat 64 (a1 + r)) = BitVec.ofNat 64 a1 := by
    apply BitVec.eq_of_toNat_eq
    rw [panByteAlign_toNat64, har1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hp2 : panByteAlignHOL (BitVec.ofNat 64 (a2 + r)) = BitVec.ofNat 64 a2 := by
    apply BitVec.eq_of_toNat_eq
    rw [panByteAlign_toNat64, har2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  unfold memB
  rw [hp1, hp2, hw, hbe]
  rcases s2.memory (BitVec.ofNat 64 a2) with ⟨w⟩
  dsimp only [panGetByteHOL]
  have hm1 : (BitVec.ofNat 64 (a1 + r)).toNat % 8 = r := by rw [har1]; omega
  have hm2 : (BitVec.ofNat 64 (a2 + r)).toNat % 8 = r := by rw [har2]; omega
  change (UInt8.ofNat (w.toNat /
      256 ^ (if s2.be then 8 - 1 - (BitVec.ofNat 64 (a1 + r)).toNat % 8 else (BitVec.ofNat 64 (a1 + r)).toNat % 8) % 256)).toNat =
    (UInt8.ofNat (w.toNat /
      256 ^ (if s2.be then 8 - 1 - (BitVec.ofNat 64 (a2 + r)).toNat % 8 else (BitVec.ofNat 64 (a2 + r)).toNat % 8) % 256)).toNat
  rw [hm1, hm2]

/-- One-word copy `.store addrExp (.load .one srcExp)` at `x` from `y` preserves `MemWriteFrame` and
extends `BytesCopiedUpTo` by 8 bytes when `x = dst0 + off` and `y = src0 + off`. -/
private theorem store_load_word_step {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst0 src0 n0 : BitVec 64} {off : Nat}
    (hG : GuestInv s) (hmwf : MemWriteFrame s0 s (dst0.toNat, n0.toNat))
    (hcp : BytesCopiedUpTo s0 s dst0 src0 n0.toNat off)
    (addrExp srcExp : ExpHOL 64) (x y : BitVec 64)
    (haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp =
      some (.val (.word x)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp =
      some (.val (.word y)))
    (hnone : (evaluateHOLFiniteState s (.store addrExp (.load .one srcExp))).1 = none) :
    sourceBase ≤ x.toNat ∧ x.toNat + 8 ≤ heapEnd ∧
    (x.toNat = dst0.toNat + off ∧ off + 8 ≤ n0.toNat ∧
      (src0.toNat + n0.toNat ≤ 2 ^ 64 → y.toNat = src0.toNat + off) →
      MemWriteFrame s0 (evaluateHOLFiniteState s (.store addrExp (.load .one srcExp))).2 (dst0.toNat, n0.toNat) ∧
      BytesCopiedUpTo s0 (evaluateHOLFiniteState s (.store addrExp (.load .one srcExp))).2 dst0 src0 n0.toNat (off + 8)) := by
  rw [evaluateHOLFiniteState_store] at hnone ⊢
  rw [haddr] at hnone ⊢
  dsimp only at hnone ⊢
  by_cases hdy : s.memaddrs y
  · rcases hyw : s.memory y with ⟨w⟩
    have hload_eq : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one srcExp) = some (ValueHOL.val (HolWordLab.word w)) := by
      simp [evalHOLExact, isWfShapeExactHOL, hsrc, memLoadHOLExact, panMemLoadHOL, hdy, hyw]
    rw [hload_eq] at hnone ⊢
    dsimp only at hnone ⊢
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hnone ⊢
    by_cases hdx : s.memaddrs x
    · simp only [hdx, ↓reduceIte] at hnone ⊢
      have hdom_x : x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
        rw [hG.memaddrs, memcpy_ordinaryDomain_iff] at hdx; exact hdx
      have hdom_y : y.toNat % 8 = 0 ∧ sourceBase ≤ y.toNat ∧ y.toNat < heapEnd := by
        rw [hG.memaddrs, memcpy_ordinaryDomain_iff] at hdy; exact hdy
      have hhe_mod : heapEnd % 8 = 0 := by decide
      have hhe_lt : heapEnd < 2 ^ 64 := by decide
      refine ⟨hdom_x.2.1, by omega, fun ⟨hx_off, hoff_le, hy_off⟩ => ?_⟩
      obtain ⟨hc, hm, hsh, hba, hbe, hg, hfr, hbyte, hdwr⟩ := hmwf
      let s' : PanSemStateFiniteExact 64 F :=
        { s with memory := fun current => if current = x then .word w else s.memory current }
      have hmwf' : MemWriteFrame s0 s' (dst0.toNat, n0.toNat) := by
        refine ⟨hc, hm, hsh, hba, hbe, hg, ?_, ?_, ?_⟩
        · intro a hk hf
          by_cases hax : a = x
          · exfalso; subst hax
            exact hk (dst0.toNat, n0.toNat) (List.mem_singleton.2 rfl) ⟨by omega, by omega⟩
          · simp only [s', hax, ↓reduceIte]; exact hfr a hk hf
        · intro a ha_lt hnot_in
          have hal_ne : panByteAlignHOL (BitVec.ofNat 64 a) ≠ x := by
            intro heq
            have hc_nat := panByteAlign_toNat64 (BitVec.ofNat 64 a)
            rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at hc_nat
            apply hnot_in; unfold InIvl; omega
          unfold memB
          simp only [s', hal_ne, ↓reduceIte]
          exact hbyte a ha_lt hnot_in
        · intro a hne
          by_cases hax : a = x
          · subst hax; rw [← hm]; exact hdx
          · simp only [s', hax, ↓reduceIte] at hne; exact hdwr a hne
      refine ⟨hmwf', ?_⟩
      intro hdisj hsrc_fit j hj
      have hy_eq := hy_off hsrc_fit
      by_cases hj_old : j < off
      · have hal_ne : panByteAlignHOL (BitVec.ofNat 64 (dst0.toNat + j)) ≠ x := by
          intro heq
          have hc_nat := panByteAlign_toNat64 (BitVec.ofNat 64 (dst0.toNat + j))
          rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc_nat
          omega
        have hkeep : memB s' (dst0.toNat + j) = memB s (dst0.toNat + j) := by
          unfold memB; simp only [s', hal_ne, ↓reduceIte]
        rw [hkeep]
        exact hcp hdisj hsrc_fit j hj_old
      · let r := j - off
        have hr8 : r < 8 := by dsimp [r]; omega
        have hj_split : dst0.toNat + j = x.toNat + r := by dsimp [r]; omega
        have hsy_split : src0.toNat + j = y.toNat + r := by dsimp [r]; omega
        rw [hj_split, hsy_split]
        have hx_bv : BitVec.ofNat 64 x.toNat = x := by simp [BitVec.ofNat_toNat]
        have hy_bv : BitVec.ofNat 64 y.toNat = y := by simp [BitVec.ofNat_toNat]
        have hw_eq : s'.memory (BitVec.ofNat 64 x.toNat) = s.memory (BitVec.ofNat 64 y.toNat) := by
          rw [hx_bv, hy_bv]; simp [s', hyw]
        have hb1 := memB_eq_of_word_eq s' s x.toNat y.toNat r rfl
          hdom_x.1 hdom_y.1 (by omega) (by omega) hr8 hw_eq
        have hnot_in : ¬ InIvl (y.toNat + r) (dst0.toNat, n0.toNat) := by
          unfold Disj at hdisj
          unfold InIvl
          rcases hdisj with hd0 | hs0 | hd | hd <;> omega
        have hb2 := hbyte (y.toNat + r) (by omega) hnot_in
        exact hb1.trans hb2
    · simp [hdx] at hnone
  · have hload_none : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one srcExp) = none := by
      simp [evalHOLExact, isWfShapeExactHOL, hsrc, memLoadHOLExact, panMemLoadHOL, hdy]
    rw [hload_none] at hnone; simp at hnone

/-- One-byte copy `.storeByte addrExp (.loadByte srcExp)` at `x` from `y` preserves `MemWriteFrame`
and extends `BytesCopiedUpTo` by 1 byte when `x = dst0 + off` and `y = src0 + off`. -/
private theorem storeByte_loadByte_step {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst0 src0 n0 : BitVec 64} {off : Nat}
    (hG : GuestInv s) (hmwf : MemWriteFrame s0 s (dst0.toNat, n0.toNat))
    (hcp : BytesCopiedUpTo s0 s dst0 src0 n0.toNat off)
    (addrExp srcExp : ExpHOL 64) (x y : BitVec 64)
    (haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp =
      some (.val (.word x)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp =
      some (.val (.word y)))
    (hnone : (evaluateHOLFiniteState s (.storeByte addrExp (.loadByte srcExp))).1 = none) :
    sourceBase ≤ x.toNat ∧ x.toNat + 1 ≤ heapEnd ∧
    (x.toNat = dst0.toNat + off ∧ off < n0.toNat ∧
      (src0.toNat + n0.toNat ≤ 2 ^ 64 → y.toNat = src0.toNat + off) →
      MemWriteFrame s0 (evaluateHOLFiniteState s (.storeByte addrExp (.loadByte srcExp))).2 (dst0.toNat, n0.toNat) ∧
      BytesCopiedUpTo s0 (evaluateHOLFiniteState s (.storeByte addrExp (.loadByte srcExp))).2 dst0 src0 n0.toNat (off + 1)) := by
  rw [evaluateHOLFiniteState_storeByte] at hnone ⊢
  rw [haddr] at hnone ⊢
  dsimp only at hnone ⊢
  have hlb_eq : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.loadByte srcExp) =
      match @panMemLoadByteHOL 64 _ s.memory s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) s.be y with
      | some b => some (.val (.word (BitVec.ofNat 64 b.toNat)))
      | none => none := by
    simp [evalHOLExact, hsrc]
    cases @panMemLoadByteHOL 64 _ s.memory s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) s.be y <;> rfl
  rw [hlb_eq] at hnone ⊢
  cases hlb : @panMemLoadByteHOL 64 _ s.memory s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) s.be y with
  | none => simp [hlb] at hnone
  | some yb =>
    dsimp only at hnone ⊢
    cases hst : @panMemStoreByteWord8HOL 64 _ s.memory s.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.be x
        (BitVec.ofNat 8 (BitVec.ofNat 64 yb.toNat).toNat) with
    | none =>
      simp only [hlb, hst] at hnone
      cases hnone
    | some mem' =>
      dsimp only at hnone ⊢
      have hdom : s.memaddrs (panByteAlignHOL x) := by
        by_contra hc
        unfold panMemStoreByteWord8HOL at hst
        cases s.memory (panByteAlignHOL x) with
        | word _ => simp [hc] at hst
      have hdom_ord : (panByteAlignHOL x).toNat % 8 = 0 ∧
          sourceBase ≤ (panByteAlignHOL x).toNat ∧ (panByteAlignHOL x).toNat < heapEnd := by
        rw [hG.memaddrs, memcpy_ordinaryDomain_iff] at hdom; exact hdom
      have hhe_mod : heapEnd % 8 = 0 := by decide
      have hhe_lt : heapEnd < 2 ^ 64 := by decide
      have hal_nat := panByteAlign_toNat64 x
      refine ⟨by omega, by omega, fun ⟨hx_off, hoff_lt, hy_off⟩ => ?_⟩
      obtain ⟨hc, hm, hsh, hba, hbe, hg, hfr, hbyte, hdwr⟩ := hmwf
      have hmem_cell : ∀ a : BitVec 64, a ≠ panByteAlignHOL x → mem' a = s.memory a := by
        intro a hne
        have hm' := hst
        unfold panMemStoreByteWord8HOL at hm'
        cases s.memory (panByteAlignHOL x) with
        | word cell =>
          dsimp only at hm'
          rw [if_pos hdom] at hm'
          injection hm' with hm_eq
          subst hm_eq
          simp [hne]
      obtain ⟨hsame_b, hother_b⟩ := @panMemStoreByte_getByte_eq_and_other s.memory s.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.be x
        (BitVec.ofNat 8 (BitVec.ofNat 64 yb.toNat).toNat) mem' hst
      let s' : PanSemStateFiniteExact 64 F := { s with memory := mem' }
      have hmwf' : MemWriteFrame s0 s' (dst0.toNat, n0.toNat) := by
        refine ⟨hc, hm, hsh, hba, hbe, hg, ?_, ?_, ?_⟩
        · intro a hk hf
          by_cases hax : a = panByteAlignHOL x
          · exfalso; subst hax
            apply hk (dst0.toNat, n0.toNat) (List.mem_singleton.2 rfl)
            unfold CellHits; rw [hal_nat]; omega
          · change mem' a = s0.memory a
            rw [hmem_cell a hax]; exact hfr a hk hf
        · intro a ha_lt hnot_in
          have hba_ne : BitVec.ofNat 64 a ≠ x := by
            intro heq
            have : a = x.toNat := by
              have := congrArg BitVec.toNat heq
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at this
              exact this
            subst this
            apply hnot_in; unfold InIvl; omega
          have hob := hother_b (BitVec.ofNat 64 a) hba_ne
          have heq_memB : memB s' a = memB s a := hob
          exact heq_memB.trans (hbyte a ha_lt hnot_in)
        · intro a hne
          by_cases hax : a = panByteAlignHOL x
          · subst hax; rw [← hm]; exact hdom
          · change mem' a ≠ s0.memory a at hne
            rw [hmem_cell a hax] at hne; exact hdwr a hne
      refine ⟨hmwf', ?_⟩
      intro hdisj hsrc_fit j hj
      have hy_eq := hy_off hsrc_fit
      by_cases hj_old : j < off
      · have hba_ne : BitVec.ofNat 64 (dst0.toNat + j) ≠ x := by
          intro heq
          have := congrArg BitVec.toNat heq
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          omega
        have hob : memB s' (dst0.toNat + j) = memB s (dst0.toNat + j) :=
          hother_b (BitVec.ofNat 64 (dst0.toNat + j)) hba_ne
        exact hob.trans (hcp hdisj hsrc_fit j hj_old)
      · have hj_eq : j = off := by omega
        rw [hj_eq]
        have hx_bv : BitVec.ofNat 64 (dst0.toNat + off) = x := by
          rw [← hx_off]; simp [BitVec.ofNat_toNat]
        have hy_bv : BitVec.ofNat 64 (src0.toNat + off) = y := by
          rw [← hy_eq]; simp [BitVec.ofNat_toNat]
        have hyb_val : yb.toNat = memB s (src0.toNat + off) := by
          unfold panMemLoadByteHOL at hlb
          dsimp only at hlb
          cases hcy : s.memory (panByteAlignHOL y) with
          | word wy =>
            have hcy1 : (s.memory (panByteAlignHOL y)).1 = wy := by rw [hcy]
            by_cases hdy : s.memaddrs (panByteAlignHOL y)
            · simp only [hdy, ↓reduceIte, hcy1, Option.some.injEq] at hlb
              unfold memB
              rw [hy_bv, hcy, ← hlb]
            · simp [hdy] at hlb
        have hbw_nat : (BitVec.ofNat 8 (BitVec.ofNat 64 yb.toNat).toNat).toNat = yb.toNat := by
          have hyb8 : yb.toNat < 256 := yb.toNat_lt_size
          simp only [BitVec.toNat_ofNat]
          omega
        have hd_memB : memB s' (dst0.toNat + off) = yb.toNat := by
          unfold memB
          rw [hx_bv]
          exact hsame_b.trans hbw_nat
        have hnot_in : ¬ InIvl (src0.toNat + off) (dst0.toNat, n0.toNat) := by
          unfold Disj at hdisj
          unfold InIvl
          rcases hdisj with hd0 | hs0 | hd | hd <;> omega
        rw [hd_memB, hyb_val]
        exact hbyte (src0.toNat + off) (by omega) hnot_in

private def MemcpyFullInv {F : Type} (s0 : PanSemStateFiniteExact 64 F) (dst0 src0 n0 : BitVec 64)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧ GuestInv s ∧
  MemWriteFrame s0 s (dst0.toNat, n0.toNat) ∧
  s.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
  s.locals.lookup (ofString "src") = some (.val (.word src0)) ∧
  s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
  ∃ iw : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
    iw.toNat ≤ n0.toNat ∧
    BytesCopiedUpTo s0 s dst0 src0 n0.toNat iw.toNat ∧
    (0 < iw.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + iw.toNat ≤ heapEnd)

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
    (hG : GuestInv s) (dst0 src0 n0 iw : BitVec 64)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hsrc : s.locals.lookup (ofString "src") = some (.val (.word src0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (had : avoidsLocal (ofString "dst") a = true)
    (hasrc : avoidsLocal (ofString "src") a = true)
    (han : avoidsLocal (ofString "n") a = true)
    (hai : avoidsLocal (ofString "i") a = true)
    (h : (evaluateHOLFiniteState s (.seq a b)).1 = none) :
    (evaluateHOLFiniteState s a).1 = none ∧
    ∃ m : PanSemStateFiniteExact 64 F,
      m = (evaluateHOLFiniteState s a).2 ∧
      GuestInv m ∧
      m.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
      m.locals.lookup (ofString "src") = some (.val (.word src0)) ∧
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
    refine ⟨by simp [hr], m, by simp [hr], ?_, ?_, ?_, ?_, ?_, h1', ?_⟩
    · have hm := guestInv_evaluate s a hG; rw [hr] at hm; exact hm
    · have := evaluate_avoidsLocal_flowing (ofString "dst") a had s (by rw [hr]; exact Or.inl rfl)
      rw [hr] at this; exact this.trans hd
    · have := evaluate_avoidsLocal_flowing (ofString "src") a hasrc s (by rw [hr]; exact Or.inl rfl)
      rw [hr] at this; exact this.trans hsrc
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

private theorem assign_i_step {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst0 src0 n0 iw k : BitVec 64}
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hmwf : MemWriteFrame s0 s (dst0.toNat, n0.toNat))
    (hcp : BytesCopiedUpTo s0 s dst0 src0 n0.toNat (iw + k).toNat)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hsrc : s.locals.lookup (ofString "src") = some (.val (.word src0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hle : (iw + k).toNat ≤ n0.toNat)
    (hdlo : sourceBase ≤ dst0.toNat) (hdhi : dst0.toNat + (iw + k).toNat ≤ heapEnd) :
    MemcpyFullInv s0 dst0 src0 n0
      (evaluateHOLFiniteState s (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const k]))).2 := by
  have hrun : evaluateHOLFiniteState s
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const k])) =
      (none, setVarHOLFinite (ofString "i") (.val (.word (iw + k))) s) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi, wordOpHOL, wordOp,
      valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
      shapeOfHOLExact, shapeEqHOL]
  rw [hrun]
  dsimp only
  refine ⟨hc, guestInv_setVar _ _ s hG, memWriteFrame_locals_clock hmwf _ s.clock, ?_, ?_, ?_,
    iw + k, ?_, hle, hcp, fun _ => ⟨hdlo, hdhi⟩⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd, show ofString "i" ≠ ofString "dst" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsrc, show ofString "i" ≠ ofString "src" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "i" ≠ ofString "n" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

private theorem while_preserve_full {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 src0 n0 : BitVec 64}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hnb : noBreak body = true) (hnc : noTopContinue body = true)
    (hbody : ∀ (s : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      MemcpyFullInv s0 dst0 src0 n0 s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word w)) → w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemcpyFullInv s0 dst0 src0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2)
    (k : Nat) (s post : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k)
    (hinv : MemcpyFullInv s0 dst0 src0 n0 s)
    (hrun : evaluateHOLFiniteState s (.while cond body) = (none, post)) :
    MemcpyFullInv s0 dst0 src0 n0 post ∧
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
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.mp hnotnz
        simp at hrun; subst hrun
        rw [evalHOLFinite_eq_toExact, hcw0] at hcond
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
            have hmid : MemcpyFullInv s0 dst0 src0 n0 mid := by
              rw [evalHOLFinite_eq_toExact] at hcond
              have hb := hbody s cw hinv hcond hnz (by rw [hbr])
              rw [hbr] at hb; exact hb
            exact ih mid (by change mid.clock ≤ s.clock - 1 at rem; omega) hmid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl nc
            | «break» => exact absurd rfl nb
            | _ => simp at hrun
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.mp hnotnz
        simp at hrun; subst hrun
        rw [evalHOLFinite_eq_toExact, hcw0] at hcond
        exact ⟨hinv, hcond⟩
    · simp at hrun

private theorem step_loop1 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 src0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemcpyFullInv s0 dst0 src0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 32])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8])
            (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 8])))
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16])
              (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 16])))
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24])
                (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 24])))
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32]))))))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemcpyFullInv s0 dst0 src0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hmwf, hdst, hsrc, hn, iw, hi, hle, hcp, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hmwfd : MemWriteFrame s0 sd (dst0.toNat, n0.toNat) := memWriteFrame_locals_clock hmwf s.locals (s.clock - 1)
  have hcpd : BytesCopiedUpTo s0 sd dst0 src0 n0.toNat iw.toNat := hcp
  have hnl := eval_notLower_true s n0 iw 32 w hn hi hcond hw
  have hH : heapEnd = 33806089704 := by decide
  obtain ⟨hs0, s1, hs1_eq, hG1, hd1, hsrc1, hn1, hi1, hr1, heq1⟩ :=
    seq_none_split sd _ _ hGd dst0 src0 n0 iw hdst hsrc hn hi rfl rfl rfl rfl hnone
  obtain ⟨hs8, s2, hs2_eq, hG2, hd2, hsrc2, hn2, hi2, hr2, heq2⟩ :=
    seq_none_split s1 _ _ hG1 dst0 src0 n0 iw hd1 hsrc1 hn1 hi1 rfl rfl rfl rfl hr1
  obtain ⟨hs16, s3, hs3_eq, hG3, hd3, hsrc3, hn3, hi3, hr3, heq3⟩ :=
    seq_none_split s2 _ _ hG2 dst0 src0 n0 iw hd2 hsrc2 hn2 hi2 rfl rfl rfl rfl hr2
  obtain ⟨hs24, s4, hs4_eq, hG4, hd4, hsrc4, hn4, hi4, _, heq4⟩ :=
    seq_none_split s3 _ _ hG3 dst0 src0 n0 iw hd3 hsrc3 hn3 hi3 rfl rfl rfl rfl hr3
  have st0 := store_load_word_step hGd hmwfd hcpd _ _ (dst0 + iw) (src0 + iw)
    (eval_add2_locals sd _ _ dst0 iw hdst hi) (eval_add2_locals sd _ _ src0 iw hsrc hi) hs0
  have hd8_raw := @store_load_word_step F s1 s1 0#64 0#64 0#64 0 hG1 (memWriteFrame_refl s1 (0, 0))
    (fun _ _ _ h => absurd h (Nat.not_lt_zero _))
    _ _ (dst0 + iw + 8) (src0 + iw + 8) (eval_add3_locals s1 _ _ dst0 iw 8 hd1 hi1)
    (eval_add3_locals s1 _ _ src0 iw 8 hsrc1 hi1) hs8
  have hd16_raw := @store_load_word_step F s2 s2 0#64 0#64 0#64 0 hG2 (memWriteFrame_refl s2 (0, 0))
    (fun _ _ _ h => absurd h (Nat.not_lt_zero _))
    _ _ (dst0 + iw + 16) (src0 + iw + 16) (eval_add3_locals s2 _ _ dst0 iw 16 hd2 hi2)
    (eval_add3_locals s2 _ _ src0 iw 16 hsrc2 hi2) hs16
  have hd24_raw := @store_load_word_step F s3 s3 0#64 0#64 0#64 0 hG3 (memWriteFrame_refl s3 (0, 0))
    (fun _ _ _ h => absurd h (Nat.not_lt_zero _))
    _ _ (dst0 + iw + 24) (src0 + iw + 24) (eval_add3_locals s3 _ _ dst0 iw 24 hd3 hi3)
    (eval_add3_locals s3 _ _ src0 iw 24 hsrc3 hi3) hs24
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
  have hsrc_off : ∀ (k : BitVec 64), k.toNat ≤ 24 → src0.toNat + n0.toNat ≤ 2 ^ 64 →
      (src0 + iw + k).toNat = src0.toNat + (iw.toNat + k.toNat) := by
    intro k hk hfit
    have hsi : (src0 + iw).toNat = src0.toNat + iw.toNat := BitVec.toNat_add_of_lt (by omega)
    rw [BitVec.toNat_add_of_lt (by rw [hsi]; omega), hsi, Nat.add_assoc]
  obtain ⟨hmwf1, hcp1⟩ : MemWriteFrame s0 s1 (dst0.toNat, n0.toNat) ∧ BytesCopiedUpTo s0 s1 dst0 src0 n0.toNat (iw.toNat + 8) := by
    rw [hs1_eq]
    exact st0.2.2 ⟨hdi_eq, by omega, fun hfit => BitVec.toNat_add_of_lt (by omega)⟩
  obtain ⟨hmwf2, hcp2⟩ : MemWriteFrame s0 s2 (dst0.toNat, n0.toNat) ∧ BytesCopiedUpTo s0 s2 dst0 src0 n0.toNat (iw.toNat + 16) := by
    rw [hs2_eq]
    have step := (store_load_word_step hG1 hmwf1 hcp1 _ _ (dst0 + iw + 8) (src0 + iw + 8)
      (eval_add3_locals s1 _ _ dst0 iw 8 hd1 hi1) (eval_add3_locals s1 _ _ src0 iw 8 hsrc1 hi1) hs8).2.2
      ⟨by omega, by omega, hsrc_off 8 (by decide)⟩
    simpa [Nat.add_assoc] using step
  obtain ⟨hmwf3, hcp3⟩ : MemWriteFrame s0 s3 (dst0.toNat, n0.toNat) ∧ BytesCopiedUpTo s0 s3 dst0 src0 n0.toNat (iw.toNat + 24) := by
    rw [hs3_eq]
    have step := (store_load_word_step hG2 hmwf2 hcp2 _ _ (dst0 + iw + 16) (src0 + iw + 16)
      (eval_add3_locals s2 _ _ dst0 iw 16 hd2 hi2) (eval_add3_locals s2 _ _ src0 iw 16 hsrc2 hi2) hs16).2.2
      ⟨by omega, by omega, hsrc_off 16 (by decide)⟩
    simpa [Nat.add_assoc] using step
  obtain ⟨hmwf4, hcp4⟩ : MemWriteFrame s0 s4 (dst0.toNat, n0.toNat) ∧ BytesCopiedUpTo s0 s4 dst0 src0 n0.toNat (iw + 32).toNat := by
    rw [hs4_eq]
    have step := (store_load_word_step hG3 hmwf3 hcp3 _ _ (dst0 + iw + 24) (src0 + iw + 24)
      (eval_add3_locals s3 _ _ dst0 iw 24 hd3 hi3) (eval_add3_locals s3 _ _ src0 iw 24 hsrc3 hi3) hs24).2.2
      ⟨by omega, by omega, hsrc_off 24 (by decide)⟩
    have heq_32 : iw.toNat + 24 + 8 = (iw + 32).toNat := by rw [hik_eq]; omega
    rw [← heq_32]; exact step
  change MemcpyFullInv s0 dst0 src0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1, heq2, heq3, heq4]
  exact assign_i_step hG4.code hG4 hmwf4 hcp4 hd4 hsrc4 hn4 hi4 hle_ik hdlo hdhi

private theorem step_loop2 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 src0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemcpyFullInv s0 dst0 src0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemcpyFullInv s0 dst0 src0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hmwf, hdst, hsrc, hn, iw, hi, hle, hcp, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hmwfd : MemWriteFrame s0 sd (dst0.toNat, n0.toNat) := memWriteFrame_locals_clock hmwf s.locals (s.clock - 1)
  have hnl := eval_notLower_true s n0 iw 8 w hn hi hcond hw
  obtain ⟨hs0, s1, hs1_eq, hG1, hd1, hsrc1, hn1, hi1, _, heq1⟩ :=
    seq_none_split sd _ _ hGd dst0 src0 n0 iw hdst hsrc hn hi rfl rfl rfl rfl hnone
  have st0 := store_load_word_step hGd hmwfd hcp _ _ (dst0 + iw) (src0 + iw)
    (eval_add2_locals sd _ _ dst0 iw hdst hi) (eval_add2_locals sd _ _ src0 iw hsrc hi) hs0
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom ⟨st0.1, st0.2.1⟩ (by decide) (by decide) hnl
  have hk8_val : (8 : BitVec 64).toNat = 8 := rfl
  obtain ⟨hmwf1, hcp1⟩ : MemWriteFrame s0 s1 (dst0.toNat, n0.toNat) ∧ BytesCopiedUpTo s0 s1 dst0 src0 n0.toNat (iw + 8).toNat := by
    rw [hs1_eq]
    have step := st0.2.2 ⟨hdi_eq, by omega, fun hfit => BitVec.toNat_add_of_lt (by omega)⟩
    have heq_8 : iw.toNat + 8 = (iw + 8).toNat := by rw [hik_eq, hk8_val]
    rw [← heq_8]; exact step
  change MemcpyFullInv s0 dst0 src0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1]
  exact assign_i_step hG1.code hG1 hmwf1 hcp1 hd1 hsrc1 hn1 hi1 hle_ik hdlo hdhi

private theorem step_loop3 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 src0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemcpyFullInv s0 dst0 src0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1])
            (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 1])))
          (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2])
              (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 2])))
            (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3])
                (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 3])))
              (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4])
                  (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 4])))
                (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5])
                    (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 5])))
                  (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6])
                      (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 6])))
                    (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7])
                        (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 7])))
                      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))))))))))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemcpyFullInv s0 dst0 src0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hmwf, hdst, hsrc, hn, iw, hi, hle, hcp, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hmwfd : MemWriteFrame s0 sd (dst0.toNat, n0.toNat) := memWriteFrame_locals_clock hmwf s.locals (s.clock - 1)
  have hnl := eval_notLower_true s n0 iw 8 w hn hi hcond hw
  have hH : heapEnd = 33806089704 := by decide
  obtain ⟨hs0, s1, hs1_eq, hG1, hd1, hsrc1, hn1, hi1, hr1, heq1⟩ :=
    seq_none_split sd _ _ hGd dst0 src0 n0 iw hdst hsrc hn hi rfl rfl rfl rfl hnone
  obtain ⟨hs1, s2, hs2_eq, hG2, hd2, hsrc2, hn2, hi2, hr2, heq2⟩ :=
    seq_none_split s1 _ _ hG1 dst0 src0 n0 iw hd1 hsrc1 hn1 hi1 rfl rfl rfl rfl hr1
  obtain ⟨hs2, s3, hs3_eq, hG3, hd3, hsrc3, hn3, hi3, hr3, heq3⟩ :=
    seq_none_split s2 _ _ hG2 dst0 src0 n0 iw hd2 hsrc2 hn2 hi2 rfl rfl rfl rfl hr2
  obtain ⟨hs3, s4, hs4_eq, hG4, hd4, hsrc4, hn4, hi4, hr4, heq4⟩ :=
    seq_none_split s3 _ _ hG3 dst0 src0 n0 iw hd3 hsrc3 hn3 hi3 rfl rfl rfl rfl hr3
  obtain ⟨hs4, s5, hs5_eq, hG5, hd5, hsrc5, hn5, hi5, hr5, heq5⟩ :=
    seq_none_split s4 _ _ hG4 dst0 src0 n0 iw hd4 hsrc4 hn4 hi4 rfl rfl rfl rfl hr4
  obtain ⟨hs5, s6, hs6_eq, hG6, hd6, hsrc6, hn6, hi6, hr6, heq6⟩ :=
    seq_none_split s5 _ _ hG5 dst0 src0 n0 iw hd5 hsrc5 hn5 hi5 rfl rfl rfl rfl hr5
  obtain ⟨hs6, s7, hs7_eq, hG7, hd7, hsrc7, hn7, hi7, hr7, heq7⟩ :=
    seq_none_split s6 _ _ hG6 dst0 src0 n0 iw hd6 hsrc6 hn6 hi6 rfl rfl rfl rfl hr6
  obtain ⟨hs7, s8, hs8_eq, hG8, hd8, hsrc8, hn8, hi8, _, heq8⟩ :=
    seq_none_split s7 _ _ hG7 dst0 src0 n0 iw hd7 hsrc7 hn7 hi7 rfl rfl rfl rfl hr7
  have b0 := storeByte_loadByte_step hGd hmwfd hcp _ _ (dst0 + iw) (src0 + iw)
    (eval_add2_locals sd _ _ dst0 iw hdst hi) (eval_add2_locals sd _ _ src0 iw hsrc hi) hs0
  have b7_raw := @storeByte_loadByte_step F s7 s7 0#64 0#64 0#64 0 hG7 (memWriteFrame_refl s7 (0, 0))
    (fun _ _ _ h => absurd h (Nat.not_lt_zero _))
    _ _ (dst0 + iw + 7) (src0 + iw + 7) (eval_add3_locals s7 _ _ dst0 iw 7 hd7 hi7)
    (eval_add3_locals s7 _ _ src0 iw 7 hsrc7 hi7) hs7
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
  have hsrc_off : ∀ (k : BitVec 64), k.toNat ≤ 7 → src0.toNat + n0.toNat ≤ 2 ^ 64 →
      (src0 + iw + k).toNat = src0.toNat + (iw.toNat + k.toNat) := by
    intro k hk hfit
    have hsi : (src0 + iw).toNat = src0.toNat + iw.toNat := BitVec.toNat_add_of_lt (by omega)
    rw [BitVec.toNat_add_of_lt (by rw [hsi]; omega), hsi, Nat.add_assoc]
  obtain ⟨hmwf1, hcp1⟩ : MemWriteFrame s0 s1 (dst0.toNat, n0.toNat) ∧ BytesCopiedUpTo s0 s1 dst0 src0 n0.toNat (iw.toNat + 1) := by
    rw [hs1_eq]; exact b0.2.2 ⟨hdi_eq, by omega, fun hfit => BitVec.toNat_add_of_lt (by omega)⟩
  obtain ⟨hmwf2, hcp2⟩ : MemWriteFrame s0 s2 (dst0.toNat, n0.toNat) ∧ BytesCopiedUpTo s0 s2 dst0 src0 n0.toNat (iw.toNat + 2) := by
    rw [hs2_eq]
    simpa [Nat.add_assoc] using (storeByte_loadByte_step hG1 hmwf1 hcp1 _ _ (dst0 + iw + 1) (src0 + iw + 1)
      (eval_add3_locals s1 _ _ dst0 iw 1 hd1 hi1) (eval_add3_locals s1 _ _ src0 iw 1 hsrc1 hi1) hs1).2.2
      ⟨by omega, by omega, hsrc_off 1 (by decide)⟩
  obtain ⟨hmwf3, hcp3⟩ : MemWriteFrame s0 s3 (dst0.toNat, n0.toNat) ∧ BytesCopiedUpTo s0 s3 dst0 src0 n0.toNat (iw.toNat + 3) := by
    rw [hs3_eq]
    simpa [Nat.add_assoc] using (storeByte_loadByte_step hG2 hmwf2 hcp2 _ _ (dst0 + iw + 2) (src0 + iw + 2)
      (eval_add3_locals s2 _ _ dst0 iw 2 hd2 hi2) (eval_add3_locals s2 _ _ src0 iw 2 hsrc2 hi2) hs2).2.2
      ⟨by omega, by omega, hsrc_off 2 (by decide)⟩
  obtain ⟨hmwf4, hcp4⟩ : MemWriteFrame s0 s4 (dst0.toNat, n0.toNat) ∧ BytesCopiedUpTo s0 s4 dst0 src0 n0.toNat (iw.toNat + 4) := by
    rw [hs4_eq]
    simpa [Nat.add_assoc] using (storeByte_loadByte_step hG3 hmwf3 hcp3 _ _ (dst0 + iw + 3) (src0 + iw + 3)
      (eval_add3_locals s3 _ _ dst0 iw 3 hd3 hi3) (eval_add3_locals s3 _ _ src0 iw 3 hsrc3 hi3) hs3).2.2
      ⟨by omega, by omega, hsrc_off 3 (by decide)⟩
  obtain ⟨hmwf5, hcp5⟩ : MemWriteFrame s0 s5 (dst0.toNat, n0.toNat) ∧ BytesCopiedUpTo s0 s5 dst0 src0 n0.toNat (iw.toNat + 5) := by
    rw [hs5_eq]
    simpa [Nat.add_assoc] using (storeByte_loadByte_step hG4 hmwf4 hcp4 _ _ (dst0 + iw + 4) (src0 + iw + 4)
      (eval_add3_locals s4 _ _ dst0 iw 4 hd4 hi4) (eval_add3_locals s4 _ _ src0 iw 4 hsrc4 hi4) hs4).2.2
      ⟨by omega, by omega, hsrc_off 4 (by decide)⟩
  obtain ⟨hmwf6, hcp6⟩ : MemWriteFrame s0 s6 (dst0.toNat, n0.toNat) ∧ BytesCopiedUpTo s0 s6 dst0 src0 n0.toNat (iw.toNat + 6) := by
    rw [hs6_eq]
    simpa [Nat.add_assoc] using (storeByte_loadByte_step hG5 hmwf5 hcp5 _ _ (dst0 + iw + 5) (src0 + iw + 5)
      (eval_add3_locals s5 _ _ dst0 iw 5 hd5 hi5) (eval_add3_locals s5 _ _ src0 iw 5 hsrc5 hi5) hs5).2.2
      ⟨by omega, by omega, hsrc_off 5 (by decide)⟩
  obtain ⟨hmwf7, hcp7⟩ : MemWriteFrame s0 s7 (dst0.toNat, n0.toNat) ∧ BytesCopiedUpTo s0 s7 dst0 src0 n0.toNat (iw.toNat + 7) := by
    rw [hs7_eq]
    simpa [Nat.add_assoc] using (storeByte_loadByte_step hG6 hmwf6 hcp6 _ _ (dst0 + iw + 6) (src0 + iw + 6)
      (eval_add3_locals s6 _ _ dst0 iw 6 hd6 hi6) (eval_add3_locals s6 _ _ src0 iw 6 hsrc6 hi6) hs6).2.2
      ⟨by omega, by omega, hsrc_off 6 (by decide)⟩
  obtain ⟨hmwf8, hcp8⟩ : MemWriteFrame s0 s8 (dst0.toNat, n0.toNat) ∧ BytesCopiedUpTo s0 s8 dst0 src0 n0.toNat (iw + 8).toNat := by
    rw [hs8_eq]
    have step := (storeByte_loadByte_step hG7 hmwf7 hcp7 _ _ (dst0 + iw + 7) (src0 + iw + 7)
      (eval_add3_locals s7 _ _ dst0 iw 7 hd7 hi7) (eval_add3_locals s7 _ _ src0 iw 7 hsrc7 hi7) hs7).2.2
      ⟨by omega, by omega, hsrc_off 7 (by decide)⟩
    have heq_8 : iw.toNat + 7 + 1 = (iw + 8).toNat := by rw [hik_eq]; omega
    rw [← heq_8]; exact step
  change MemcpyFullInv s0 dst0 src0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8]
  exact assign_i_step hG8.code hG8 hmwf8 hcp8 hd8 hsrc8 hn8 hi8 hle_ik hdlo hdhi

private theorem step_loop4 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 src0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemcpyFullInv s0 dst0 src0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemcpyFullInv s0 dst0 src0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hmwf, hdst, hsrc, hn, iw, hi, hle, hcp, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hmwfd : MemWriteFrame s0 sd (dst0.toNat, n0.toNat) := memWriteFrame_locals_clock hmwf s.locals (s.clock - 1)
  have hlt := eval_lower_true s n0 iw w hn hi hcond hw
  rw [BitVec.lt_def] at hlt
  obtain ⟨hs0, s1, hs1_eq, hG1, hd1, hsrc1, hn1, hi1, _, heq1⟩ :=
    seq_none_split sd _ _ hGd dst0 src0 n0 iw hdst hsrc hn hi rfl rfl rfl rfl hnone
  have b0 := storeByte_loadByte_step hGd hmwfd hcp _ _ (dst0 + iw) (src0 + iw)
    (eval_add2_locals sd _ _ dst0 iw hdst hi) (eval_add2_locals sd _ _ src0 iw hsrc hi) hs0
  have hnlt := n0.isLt
  have ha1 : (iw + 1).toNat = iw.toNat + 1 :=
    BitVec.toNat_add_of_lt (by change iw.toNat + 1 < 2 ^ 64; omega)
  have hnl : ¬ (n0 < iw + 1) := by rw [BitVec.lt_def, ha1]; omega
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 1 hle hdom ⟨b0.1, b0.2.1⟩ (by decide) (by decide) hnl
  have hk1_val : (1 : BitVec 64).toNat = 1 := rfl
  obtain ⟨hmwf1, hcp1⟩ : MemWriteFrame s0 s1 (dst0.toNat, n0.toNat) ∧ BytesCopiedUpTo s0 s1 dst0 src0 n0.toNat (iw + 1).toNat := by
    rw [hs1_eq]
    have step := b0.2.2 ⟨hdi_eq, by omega, fun hfit => BitVec.toNat_add_of_lt (by omega)⟩
    have heq_1 : iw.toNat + 1 = (iw + 1).toNat := by rw [hik_eq, hk1_val]
    rw [← heq_1]; exact step
  change MemcpyFullInv s0 dst0 src0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1]
  exact assign_i_step hG1.code hG1 hmwf1 hcp1 hd1 hsrc1 hn1 hi1 hle_ik hdlo hdhi

theorem lookup_memcpy :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
  lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

/-- Full normal-return postcondition of `memcpy(dst, src, n)` under `GuestInv`. -/
theorem memcpy_body_run {F : Type} (s : PanSemStateFiniteExact 64 F) (dst0 src0 n0 : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hsrc : s.locals.lookup (ofString "src") = some (.val (.word src0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memcpy)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memcpy)).2
    MemWriteFrame s post (dst0.toNat, n0.toNat) ∧
    BytesCopiedUpTo s post dst0 src0 n0.toNat n0.toNat ∧
    (0 < n0.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapEnd) := by
  intro post
  have hb : sourceFnBody Guest.Software.guestFn_memcpy =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_memcpy).body := rfl
  show MemWriteFrame s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memcpy)).2 _ ∧
    BytesCopiedUpTo s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memcpy)).2 _ _ _ _ ∧ _
  rw [hb] at hret ⊢
  dsimp only [extractFn, Guest.Software.guestFn_memcpy,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map] at hret ⊢
  rw [evaluateHOLFiniteState_dec_total] at hret ⊢
  dsimp only at hret ⊢
  have hev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const 0#64) = some (.val (.word 0#64)) := rfl
  rw [hev0] at hret ⊢
  dsimp only at hret ⊢
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh0] at hret ⊢
  dsimp only at hret ⊢
  set s1 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s with hs1
  have hinv1 : MemcpyFullInv s dst0 src0 n0 s1 := by
    refine ⟨hcode, guestInv_setVar _ _ s hG, memWriteFrame_locals_clock (memWriteFrame_refl s _) _ s.clock,
      ?_, ?_, ?_, 0#64, ?_, Nat.zero_le _, fun _ _ _ hj => absurd hj (Nat.not_lt_zero _),
      fun h => by simp at h⟩
    · simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hdst, show ofString "i" ≠ ofString "dst" by decide]
    · simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsrc, show ofString "i" ≠ ofString "src" by decide]
    · simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "i" ≠ ofString "n" by decide]
    · simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
  set iteProg : ProgHOL 64 := .ite _ _ _
  have hite_nrr : noRet iteProg = true := rfl
  rcases hite_run : evaluateHOLFiniteState s1 iteProg with ⟨rite, s2⟩
  simp only [hite_run] at hret ⊢
  cases rite with
  | some _ =>
    have hnr := evaluate_noRet iteProg hite_nrr s1 v
    rw [hite_run] at hnr
    exact absurd hret hnr
  | none =>
    dsimp only at hret ⊢
    have hinv2 : MemcpyFullInv s dst0 src0 n0 s2 := by
      dsimp only [iteProg] at hite_run
      rw [evaluateHOLFiniteState_ite] at hite_run
      split at hite_run
      · split at hite_run
        · rw [evaluateHOLFiniteState_skip] at hite_run
          injection hite_run with _ hs2; rw [← hs2]; exact hinv1
        · rw [evaluateHOLFiniteState_seq_line780] at hite_run
          rcases hw1 : evaluateHOLFiniteState s1 _ with ⟨rw1, m1⟩
          rw [hw1] at hite_run
          cases rw1 with
          | some _ => dsimp only at hite_run; cases hite_run
          | none =>
            dsimp only at hite_run
            have hm1 := (while_preserve_full _ _ rfl rfl step_loop1 s1.clock s1 m1 le_rfl hinv1 hw1).1
            exact (while_preserve_full _ _ rfl rfl step_loop2 m1.clock m1 s2 le_rfl hm1 hite_run).1
      · simp at hite_run
    rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
    set loop3 : ProgHOL 64 := .while _ _
    have hl3_nrr : noRet loop3 = true := rfl
    rcases hw3 : evaluateHOLFiniteState s2 loop3 with ⟨rw3, s3⟩
    simp only [hw3] at hret ⊢
    cases rw3 with
    | some _ =>
      have hnr := evaluate_noRet loop3 hl3_nrr s2 v
      rw [hw3] at hnr
      exact absurd hret hnr
    | none =>
      dsimp only at hret ⊢
      have hinv3 : MemcpyFullInv s dst0 src0 n0 s3 :=
        (while_preserve_full _ _ rfl rfl step_loop3 s2.clock s2 s3 le_rfl hinv2 hw3).1
      rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
      set loop4 : ProgHOL 64 := .while _ _
      have hl4_nrr : noRet loop4 = true := rfl
      rcases hw4 : evaluateHOLFiniteState s3 loop4 with ⟨rw4, s4⟩
      simp only [hw4] at hret ⊢
      cases rw4 with
      | some _ =>
        have hnr := evaluate_noRet loop4 hl4_nrr s3 v
        rw [hw4] at hnr
        exact absurd hret hnr
      | none =>
        dsimp only at hret ⊢
        obtain ⟨hinv4, hexit4⟩ := while_preserve_full _ _ rfl rfl step_loop4 s3.clock s3 s4 le_rfl hinv3 hw4
        obtain ⟨_, _, hmwf4, _, _, hn4, iw4, hi4, hle4, hcp4, hdom4⟩ := hinv4
        have hiw_eq : iw4.toNat = n0.toNat := by
          simp only [evalHOLExact, hi4, hn4, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def] at hexit4
          by_cases hlt : iw4.toNat < n0.toNat
          · simp [hlt] at hexit4
          · omega
        rw [hiw_eq] at hcp4 hdom4
        have hret_eval : evaluateHOLFiniteState s4 (.return (.const 0#64)) =
            (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite s4) := by
          simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact,
            sizeOfShapeWithContextHOL]
        rw [hret_eval]
        dsimp only
        refine ⟨memWriteFrame_locals_clock hmwf4 _ s4.clock, hcp4, hdom4⟩

/-- Call-site wrapper for `.call (some (none, none)) "memcpy" [dstExp, srcExp, nExp]` inside a flowing/returning sequence. -/
theorem call_memcpy_step {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dstExp srcExp nExp : ExpHOL 64) (dst0 src0 n0 : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp =
      some (.val (.word src0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (t : PanSemStateFiniteExact 64 F)
    (hcall : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) =
      (none, t)) :
    t.locals = s.locals ∧
    MemWriteFrame s t (dst0.toNat, n0.toNat) ∧
    BytesCopiedUpTo s t dst0 src0 n0.toNat n0.toNat ∧
    (0 < n0.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapEnd) := by
  rw [evaluateHOLFiniteState_call] at hcall
  have hevargs : @evalListHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, srcExp, nExp] = some [.val (.word dst0), .val (.word src0), .val (.word n0)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, hdst, hsrc, hn]
  have hlook := pan_three_word_lookup s.code.lookup (ofString "memcpy")
    (ofString "dst") (ofString "src") (ofString "n") (sourceFnBody Guest.Software.guestFn_memcpy)
    dst0 src0 n0 (by decide) (by decide) (by decide) (by rw [hcode]; exact lookup_memcpy)
  rw [hevargs] at hcall
  dsimp only at hcall
  rw [hlook] at hcall
  dsimp only at hcall
  split at hcall
  · simp at hcall
  · set callee : HolFiniteMapExact MlS (ValueHOL 64) :=
      ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word dst0))).update
        (ofString "src", .val (.word src0))).update (ofString "n", .val (.word n0))
    let entry := callEntryStateHOLFinite s callee
    have hloc_dst : entry.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [entry, callEntryStateHOLFinite, callee, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "dst" by decide, show ofString "src" ≠ ofString "dst" by decide]
    have hloc_src : entry.locals.lookup (ofString "src") = some (.val (.word src0)) := by
      simp [entry, callEntryStateHOLFinite, callee, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "src" by decide]
    have hloc_n : entry.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [entry, callEntryStateHOLFinite, callee, HolFiniteMapExact.lookup_update, FUPDATE]
    have hGe : GuestInv entry := guestInv_with_locals_clock s callee (s.clock - 1) hG
    rcases hran : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_memcpy) with ⟨res, post⟩
    rw [hran] at hcall
    cases res with
    | none => simp at hcall
    | some r =>
      cases r with
      | returned rv =>
        dsimp only at hcall
        split at hcall
        · injection hcall with _ ht
          subst ht
          have hbody := memcpy_body_run entry dst0 src0 n0 hcode hGe hloc_dst hloc_src hloc_n rv
            (by rw [hran])
          rw [hran] at hbody
          dsimp only at hbody
          obtain ⟨hmwf, hcp, hdom⟩ := hbody
          have hmwf' : MemWriteFrame s { post with locals := s.locals } (dst0.toNat, n0.toNat) :=
            ⟨hmwf.1, hmwf.2.1, hmwf.2.2.1, hmwf.2.2.2.1, hmwf.2.2.2.2.1, hmwf.2.2.2.2.2.1,
              hmwf.2.2.2.2.2.2.1, hmwf.2.2.2.2.2.2.2.1, hmwf.2.2.2.2.2.2.2.2⟩
          exact ⟨rfl, hmwf', hcp, hdom⟩
        · simp at hcall
      | _ => simp at hcall
end InitECandidate.Solver.Wave8GuestInv.R13Shards
