import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.Base

/-! `wk_memcpy`: relational world step for `memcpy(dst, src, n)` with output region
`[(locN s "dst", locN s "n")]`, against frozen spec revision 9 (`8a79d9f28`).

AST index 16 (`Guest/SoftwareAst.lean:198`):
- Declares `i := 0`.
- Runs up to four `while` loops advancing `i` by `32`, `8`, `8`, and `1`, storing only into
  bytes `[dst + i, dst + i + step)` inside `ordinaryDomain ⊆ [sourceBase, heapEnd)`, without
  wrapping (`dst + i` and `i + step` stay `< heapEnd < 2^64`).
- Modifies no globals (`gw = []`), preserves `be` and all metadata, writes only aligned cells
  meeting `(dst, n)` (`FrameOutside s post [(dst, n)] (0, 0)`) and only bytes inside `(dst, n)`
  (`∀ a < 2^64, ¬ InIvl a (dst, n) → memB post a = memB s a`), so `worldStep_of_region_writes`
  discharges `WorldStep`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8Contracts.M08

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

private theorem panMemStoreByte_other_byte {mem : BitVec 64 → HolWordLab 64}
    {dom : BitVec 64 → Prop} [DecidablePred dom] {be : Bool}
    {addr : BitVec 64} {bw : BitVec 8} {mem' : BitVec 64 → HolWordLab 64}
    (hst : panMemStoreByteWord8HOL mem dom be addr bw = some mem')
    {addr' : BitVec 64} (hne : addr' ≠ addr) :
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
      by_cases hal : panByteAlignHOL addr' = panByteAlignHOL addr
      · simp only [hal, ↓reduceIte, hcell, panGetByteHOL]
        let b : UInt8 := UInt8.ofNat bw.toNat
        have hb8 : b.toNat < 256 := b.toNat_lt_size
        have hbw_eq : bw.toNat = b.toNat := by
          have := bw.isLt
          simp [b, UInt8.toNat_ofNat', Nat.mod_eq_of_lt this]
        rw [hbw_eq]
        have hset_nat := panSetByteHOL_toNat (width := 64) (by decide) addr cell b be
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

private def MemWriteFrame {F : Type} (s0 s : PanSemStateFiniteExact 64 F) (ivl : Ivl) : Prop :=
  s.code = s0.code ∧ s.memaddrs = s0.memaddrs ∧ s.shMemaddrs = s0.shMemaddrs ∧
  s.baseAddr = s0.baseAddr ∧ s.be = s0.be ∧ s.globals = s0.globals ∧
  FrameOutside s0 s [ivl] (0, 0) ∧
  (∀ a : Nat, a < 2 ^ 64 → ¬ InIvl a ivl → memB s a = memB s0 a) ∧
  (∀ a : BitVec 64, s.memory a ≠ s0.memory a → s0.memaddrs a)

private theorem memWriteFrame_refl {F : Type} (s0 : PanSemStateFiniteExact 64 F) (ivl : Ivl) :
    MemWriteFrame s0 s0 ivl :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ h => absurd rfl h⟩

private theorem memWriteFrame_locals_clock {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {ivl : Ivl} (h : MemWriteFrame s0 s ivl) (loc : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    MemWriteFrame s0 { s with locals := loc, clock := k } ivl :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

private theorem not_resumes_error : ¬ Resumes (some .error) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

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

private def noReturnOrRaise : ProgHOL 64 → Bool
  | .seq a b => noReturnOrRaise a && noReturnOrRaise b
  | .ite _ a b => noReturnOrRaise a && noReturnOrRaise b
  | .while _ a => noReturnOrRaise a
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem evaluate_noReturnOrRaise {F : Type} (p : ProgHOL 64) (hp : noReturnOrRaise p = true)
    (s : PanSemStateFiniteExact 64 F) :
    ¬ Resumes (evaluateHOLFiniteState s p).1 := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noReturnOrRaise] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact not_resumes_error
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error
      · exact not_resumes_error
    · exact not_resumes_error
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error
      · exact not_resumes_error
    · exact not_resumes_error
  | seq a b =>
    have hab : noReturnOrRaise a = true ∧ noReturnOrRaise b = true := by
      simpa [shape, noReturnOrRaise, Bool.and_eq_true] using hp
    have rem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noReturnOrRaise a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha rem
    cases r with
    | none =>
      have mclk : m.clock ≤ s.clock := rem
      exact evaluate_noReturnOrRaise b hab.2 m
    | some _ => exact ha
  | ite _ a b =>
    have hab : noReturnOrRaise a = true ∧ noReturnOrRaise b = true := by
      simpa [shape, noReturnOrRaise, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noReturnOrRaise b hab.2 s
      · exact evaluate_noReturnOrRaise a hab.1 s
    · exact not_resumes_error
  | «while» cond body =>
    have hb : noReturnOrRaise body = true := by simpa [shape, noReturnOrRaise] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · rename_i nonzero
          have dec_lt : (decClockHOLFinite s).clock < s.clock := by
            simp only [decClockHOLFinite]; omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noReturnOrRaise body hb (decClockHOLFinite s)
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at rem
            omega
          cases r1 with
          | none =>
            exact evaluate_noReturnOrRaise (.while cond body) (by simpa [noReturnOrRaise] using hb) mid
          | some r1 =>
            cases r1 with
            | «continue» =>
              exact evaluate_noReturnOrRaise (.while cond body) (by simpa [noReturnOrRaise] using hb) mid
            | «break» => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
            | returned _ => exact ih1
            | exception _ _ => exact ih1
            | timeOut => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
            | error => exact not_resumes_error
            | finalFfi _ => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
      · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
    · exact not_resumes_error
  | _ => simp [shape, noReturnOrRaise] at hp
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

/-- One-word store at `addrExp` evaluating to `x` inside `ivl` (`ivl.1 ≤ x.toNat` and `x.toNat + 8 ≤ ivl.1 + ivl.2`)
preserves `MemWriteFrame s0 · ivl`. -/
private theorem store_one_word_frame {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {ivl : Ivl} (hG : GuestInv s) (hmwf : MemWriteFrame s0 s ivl)
    (addrExp valExp : ExpHOL 64) (x : BitVec 64)
    (haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp =
      some (.val (.word x)))
    (hval_one : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some v → ∃ w : BitVec 64, v = .val (.word w))
    (hnone : (evaluateHOLFiniteState s (.store addrExp valExp)).1 = none) :
    sourceBase ≤ x.toNat ∧ x.toNat + 8 ≤ heapEnd ∧
    (x.toNat ≥ ivl.1 ∧ x.toNat + 8 ≤ ivl.1 + ivl.2 →
      MemWriteFrame s0 (evaluateHOLFiniteState s (.store addrExp valExp)).2 ivl) := by
  rw [evaluateHOLFiniteState_store] at hnone ⊢
  rw [haddr] at hnone ⊢
  dsimp only at hnone ⊢
  split at hnone
  · rename_i val hval
    obtain ⟨w, rfl⟩ := hval_one val hval
    split at hnone
    · rename_i mem' hmem
      simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
      by_cases hdom : s.memaddrs x
      · simp only [hdom, ↓reduceIte, Option.some.injEq] at hmem
        subst hmem
        have hdom_ord : x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
          rw [hG.memaddrs, ordinaryDomain_iff] at hdom; exact hdom
        have hhe_mod : heapEnd % 8 = 0 := by decide
        refine ⟨hdom_ord.2.1, by omega, fun hxin => ?_⟩
        dsimp only
        obtain ⟨hc, hm, hsh, hba, hbe, hg, hfr, hbyte, hdwr⟩ := hmwf
        refine ⟨hc, hm, hsh, hba, hbe, hg, ?_, ?_, ?_⟩
        · intro a hk hf
          by_cases hax : a = x
          · exfalso
            subst hax
            exact hk ivl (List.mem_singleton.2 rfl) ⟨by omega, by omega⟩
          · simp only [hax, ↓reduceIte]
            exact hfr a hk hf
        · intro a ha_lt hnot_in
          have hal_ne : panByteAlignHOL (BitVec.ofNat 64 a) ≠ x := by
            intro heq
            have hc_nat := panByteAlign_toNat64 (BitVec.ofNat 64 a)
            rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at hc_nat
            apply hnot_in
            unfold InIvl
            omega
          unfold memB
          simp only [hal_ne, ↓reduceIte]
          exact hbyte a ha_lt hnot_in
        · intro a hne
          by_cases hax : a = x
          · subst hax; rw [← hm]; exact hdom
          · simp only [hax, ↓reduceIte] at hne
            exact hdwr a hne
      · simp [hdom] at hmem
    · simp at hnone
  · simp at hnone

/-- One-byte store at `addrExp` evaluating to `x` preserves `MemWriteFrame s0 · ivl` once `InIvl x.toNat ivl`. -/
private theorem storeByte_frame {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {ivl : Ivl} (hG : GuestInv s) (hmwf : MemWriteFrame s0 s ivl)
    (addrExp valExp : ExpHOL 64) (x : BitVec 64)
    (haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp =
      some (.val (.word x)))
    (hnone : (evaluateHOLFiniteState s (.storeByte addrExp valExp)).1 = none) :
    sourceBase ≤ x.toNat ∧ x.toNat + 1 ≤ heapEnd ∧
    (InIvl x.toNat ivl →
      MemWriteFrame s0 (evaluateHOLFiniteState s (.storeByte addrExp valExp)).2 ivl) := by
  rw [evaluateHOLFiniteState_storeByte] at hnone ⊢
  rw [haddr] at hnone ⊢
  dsimp only at hnone ⊢
  split at hnone
  · rename_i vw hvw
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
      have hal_nat := panByteAlign_toNat64 x
      refine ⟨by omega, by omega, fun hxin => ?_⟩
      dsimp only
      obtain ⟨hc, hm, hsh, hba, hbe, hg, hfr, hbyte, hdwr⟩ := hmwf
      have hmem_cell : ∀ a : BitVec 64, a ≠ panByteAlignHOL x → mem' a = s.memory a := by
        intro a hne
        have hm' := hmem
        unfold panMemStoreByteWord8HOL at hm'
        cases s.memory (panByteAlignHOL x) with
        | word cell =>
          dsimp only at hm'
          rw [if_pos hdom] at hm'
          injection hm' with hm_eq
          subst hm_eq
          simp [hne]
      refine ⟨hc, hm, hsh, hba, hbe, hg, ?_, ?_, ?_⟩
      · intro a hk hf
        by_cases hax : a = panByteAlignHOL x
        · exfalso
          subst hax
          apply hk ivl (List.mem_singleton.2 rfl)
          unfold CellHits
          unfold InIvl at hxin
          rw [hal_nat]
          omega
        · change mem' a = s0.memory a
          rw [hmem_cell a hax]
          exact hfr a hk hf
      · intro a ha_lt hnot_in
        have hba_ne : BitVec.ofNat 64 a ≠ x := by
          intro heq
          have : a = x.toNat := by
            have := congrArg BitVec.toNat heq
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at this
            exact this
          subst this
          exact hnot_in hxin
        have hob := @panMemStoreByte_other_byte s.memory s.memaddrs
          (fun addr => Classical.propDecidable (s.memaddrs addr)) s.be x (BitVec.ofNat 8 vw.toNat) mem' hmem
          (BitVec.ofNat 64 a) hba_ne
        have heq_memB : memB { s with memory := mem' } a = memB s a := hob
        exact heq_memB.trans (hbyte a ha_lt hnot_in)
      · intro a hne
        by_cases hax : a = panByteAlignHOL x
        · subst hax; rw [← hm]; exact hdom
        · change mem' a ≠ s0.memory a at hne
          rw [hmem_cell a hax] at hne
          exact hdwr a hne
    · simp at hnone
  · simp at hnone

private def MemcpyFullInv {F : Type} (s0 : PanSemStateFiniteExact 64 F) (dst0 n0 : BitVec 64)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧ GuestInv s ∧
  MemWriteFrame s0 s (dst0.toNat, n0.toNat) ∧
  s.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
  s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
  ∃ iw : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
    iw.toNat ≤ n0.toNat ∧
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

private theorem eval_load_one_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (val : ValueHOL 64)
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one e) = some val) :
    ∃ w : BitVec 64, val = .val (.word w) := by
  simp only [evalHOLExact] at he
  split at he
  · split at he
    · simp only [memLoadHOLExact] at he
      split at he
      · injection he with hv
        rename_i addr _ _
        cases hcell : s.memory addr with
        | word w => rw [hcell] at hv; exact ⟨w, hv.symm⟩
      · simp at he
    · simp at he
  · simp at he

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

private theorem assign_i_step {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst0 n0 iw k : BitVec 64}
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hmwf : MemWriteFrame s0 s (dst0.toNat, n0.toNat))
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hle : (iw + k).toNat ≤ n0.toNat)
    (hdlo : sourceBase ≤ dst0.toNat) (hdhi : dst0.toNat + (iw + k).toNat ≤ heapEnd) :
    MemcpyFullInv s0 dst0 n0
      (evaluateHOLFiniteState s (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const k]))).2 := by
  have hrun : evaluateHOLFiniteState s
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const k])) =
      (none, setVarHOLFinite (ofString "i") (.val (.word (iw + k))) s) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi, wordOpHOL, wordOp,
      valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
      shapeOfHOLExact, shapeEqHOL]
  rw [hrun]
  dsimp only
  refine ⟨hc, guestInv_setVar _ _ s hG, memWriteFrame_locals_clock hmwf _ s.clock, ?_, ?_, iw + k, ?_, hle, fun _ => ⟨hdlo, hdhi⟩⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd, show ofString "i" ≠ ofString "dst" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "i" ≠ ofString "n" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

private theorem while_preserve_full {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hnb : noBreak body = true) (hnc : noTopContinue body = true)
    (hbody : ∀ (s : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      MemcpyFullInv s0 dst0 n0 s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word w)) → w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemcpyFullInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2)
    (k : Nat) (s post : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k)
    (hinv : MemcpyFullInv s0 dst0 n0 s)
    (hrun : evaluateHOLFiniteState s (.while cond body) = (none, post)) :
    MemcpyFullInv s0 dst0 n0 post := by
  induction k generalizing s with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · split at hrun
      · split at hrun
        · simp at hrun
        · omega
      · simp at hrun; subst hrun; exact hinv
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
            have hmid : MemcpyFullInv s0 dst0 n0 mid := by
              have hb := hbody s cw hinv hcond hnz (by rw [hbr])
              rw [hbr] at hb; exact hb
            exact ih mid (by change mid.clock ≤ s.clock - 1 at rem; omega) hmid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl nc
            | «break» => exact absurd rfl nb
            | _ => simp at hrun
      · simp at hrun; subst hrun; exact hinv
    · simp at hrun

private theorem step_loop1 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemcpyFullInv s0 dst0 n0 s)
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
      MemcpyFullInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hmwf, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hmwfd : MemWriteFrame s0 sd (dst0.toNat, n0.toNat) := memWriteFrame_locals_clock hmwf s.locals (s.clock - 1)
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
  have st0 := store_one_word_frame hGd hmwfd _ _ (dst0 + iw)
    (eval_add2_locals sd _ _ dst0 iw hdst hi) (eval_load_one_word sd _) hs0
  have hd8_raw := (store_one_word_frame hG1 (memWriteFrame_refl s1 (0, 0)) _ _ (dst0 + iw + 8)
    (eval_add3_locals s1 _ _ dst0 iw 8 hd1 hi1) (eval_load_one_word s1 _) hs8)
  have hd16_raw := (store_one_word_frame hG2 (memWriteFrame_refl s2 (0, 0)) _ _ (dst0 + iw + 16)
    (eval_add3_locals s2 _ _ dst0 iw 16 hd2 hi2) (eval_load_one_word s2 _) hs16)
  have hd24_raw := (store_one_word_frame hG3 (memWriteFrame_refl s3 (0, 0)) _ _ (dst0 + iw + 24)
    (eval_add3_locals s3 _ _ dst0 iw 24 hd3 hi3) (eval_load_one_word s3 _) hs24)
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
  have hmwf1 : MemWriteFrame s0 s1 (dst0.toNat, n0.toNat) := by
    rw [hs1_eq]; exact st0.2.2 ⟨by omega, by omega⟩
  have hmwf2 : MemWriteFrame s0 s2 (dst0.toNat, n0.toNat) := by
    rw [hs2_eq]
    exact (store_one_word_frame hG1 hmwf1 _ _ (dst0 + iw + 8)
      (eval_add3_locals s1 _ _ dst0 iw 8 hd1 hi1) (eval_load_one_word s1 _) hs8).2.2
      ⟨by omega, by omega⟩
  have hmwf3 : MemWriteFrame s0 s3 (dst0.toNat, n0.toNat) := by
    rw [hs3_eq]
    exact (store_one_word_frame hG2 hmwf2 _ _ (dst0 + iw + 16)
      (eval_add3_locals s2 _ _ dst0 iw 16 hd2 hi2) (eval_load_one_word s2 _) hs16).2.2
      ⟨by omega, by omega⟩
  have hmwf4 : MemWriteFrame s0 s4 (dst0.toNat, n0.toNat) := by
    rw [hs4_eq]
    exact (store_one_word_frame hG3 hmwf3 _ _ (dst0 + iw + 24)
      (eval_add3_locals s3 _ _ dst0 iw 24 hd3 hi3) (eval_load_one_word s3 _) hs24).2.2
      ⟨by omega, by omega⟩
  change MemcpyFullInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1, heq2, heq3, heq4]
  exact assign_i_step hG4.code hG4 hmwf4 hd4 hn4 hi4 hle_ik hdlo hdhi

private theorem step_loop2 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemcpyFullInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemcpyFullInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hmwf, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hmwfd : MemWriteFrame s0 sd (dst0.toNat, n0.toNat) := memWriteFrame_locals_clock hmwf s.locals (s.clock - 1)
  have hnl := eval_notLower_true s n0 iw 8 w hn hi hcond hw
  obtain ⟨hs0, s1, hs1_eq, hG1, hd1, hn1, hi1, _, heq1⟩ :=
    seq_none_split sd _ _ hGd dst0 n0 iw hdst hn hi rfl rfl rfl hnone
  have st0 := store_one_word_frame hGd hmwfd _ _ (dst0 + iw)
    (eval_add2_locals sd _ _ dst0 iw hdst hi) (eval_load_one_word sd _) hs0
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom ⟨st0.1, st0.2.1⟩ (by decide) (by decide) hnl
  have hk8_val : (8 : BitVec 64).toNat = 8 := rfl
  have hmwf1 : MemWriteFrame s0 s1 (dst0.toNat, n0.toNat) := by
    rw [hs1_eq]; exact st0.2.2 ⟨by omega, by omega⟩
  change MemcpyFullInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1]
  exact assign_i_step hG1.code hG1 hmwf1 hd1 hn1 hi1 hle_ik hdlo hdhi

private theorem step_loop3 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemcpyFullInv s0 dst0 n0 s)
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
      MemcpyFullInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hmwf, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hmwfd : MemWriteFrame s0 sd (dst0.toNat, n0.toNat) := memWriteFrame_locals_clock hmwf s.locals (s.clock - 1)
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
  have b0 := storeByte_frame hGd hmwfd _ _ (dst0 + iw) (eval_add2_locals sd _ _ dst0 iw hdst hi) hs0
  have b7_raw := storeByte_frame hG7 (memWriteFrame_refl s7 (0, 0)) _ _ (dst0 + iw + 7)
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
  have hmwf1 : MemWriteFrame s0 s1 (dst0.toNat, n0.toNat) := by rw [hs1_eq]; exact b0.2.2 ⟨by omega, by omega⟩
  have hmwf2 : MemWriteFrame s0 s2 (dst0.toNat, n0.toNat) := by
    rw [hs2_eq]; exact (storeByte_frame hG1 hmwf1 _ _ (dst0 + iw + 1) (eval_add3_locals s1 _ _ dst0 iw 1 hd1 hi1) hs1).2.2 ⟨by omega, by omega⟩
  have hmwf3 : MemWriteFrame s0 s3 (dst0.toNat, n0.toNat) := by
    rw [hs3_eq]; exact (storeByte_frame hG2 hmwf2 _ _ (dst0 + iw + 2) (eval_add3_locals s2 _ _ dst0 iw 2 hd2 hi2) hs2).2.2 ⟨by omega, by omega⟩
  have hmwf4 : MemWriteFrame s0 s4 (dst0.toNat, n0.toNat) := by
    rw [hs4_eq]; exact (storeByte_frame hG3 hmwf3 _ _ (dst0 + iw + 3) (eval_add3_locals s3 _ _ dst0 iw 3 hd3 hi3) hs3).2.2 ⟨by omega, by omega⟩
  have hmwf5 : MemWriteFrame s0 s5 (dst0.toNat, n0.toNat) := by
    rw [hs5_eq]; exact (storeByte_frame hG4 hmwf4 _ _ (dst0 + iw + 4) (eval_add3_locals s4 _ _ dst0 iw 4 hd4 hi4) hs4).2.2 ⟨by omega, by omega⟩
  have hmwf6 : MemWriteFrame s0 s6 (dst0.toNat, n0.toNat) := by
    rw [hs6_eq]; exact (storeByte_frame hG5 hmwf5 _ _ (dst0 + iw + 5) (eval_add3_locals s5 _ _ dst0 iw 5 hd5 hi5) hs5).2.2 ⟨by omega, by omega⟩
  have hmwf7 : MemWriteFrame s0 s7 (dst0.toNat, n0.toNat) := by
    rw [hs7_eq]; exact (storeByte_frame hG6 hmwf6 _ _ (dst0 + iw + 6) (eval_add3_locals s6 _ _ dst0 iw 6 hd6 hi6) hs6).2.2 ⟨by omega, by omega⟩
  have hmwf8 : MemWriteFrame s0 s8 (dst0.toNat, n0.toNat) := by
    rw [hs8_eq]; exact (storeByte_frame hG7 hmwf7 _ _ (dst0 + iw + 7) (eval_add3_locals s7 _ _ dst0 iw 7 hd7 hi7) hs7).2.2 ⟨by omega, by omega⟩
  change MemcpyFullInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8]
  exact assign_i_step hG8.code hG8 hmwf8 hd8 hn8 hi8 hle_ik hdlo hdhi

private theorem step_loop4 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemcpyFullInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemcpyFullInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hmwf, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hmwfd : MemWriteFrame s0 sd (dst0.toNat, n0.toNat) := memWriteFrame_locals_clock hmwf s.locals (s.clock - 1)
  have hlt := eval_lower_true s n0 iw w hn hi hcond hw
  rw [BitVec.lt_def] at hlt
  obtain ⟨hs0, s1, hs1_eq, hG1, hd1, hn1, hi1, _, heq1⟩ :=
    seq_none_split sd _ _ hGd dst0 n0 iw hdst hn hi rfl rfl rfl hnone
  have b0 := storeByte_frame hGd hmwfd _ _ (dst0 + iw) (eval_add2_locals sd _ _ dst0 iw hdst hi) hs0
  have hnlt := n0.isLt
  have ha1 : (iw + 1).toNat = iw.toNat + 1 :=
    BitVec.toNat_add_of_lt (by change iw.toNat + 1 < 2 ^ 64; omega)
  have hnl : ¬ (n0 < iw + 1) := by rw [BitVec.lt_def, ha1]; omega
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 1 hle hdom ⟨b0.1, b0.2.1⟩ (by decide) (by decide) hnl
  have hk1_val : (1 : BitVec 64).toNat = 1 := rfl
  have hmwf1 : MemWriteFrame s0 s1 (dst0.toNat, n0.toNat) := by rw [hs1_eq]; exact b0.2.2 ⟨by omega, by omega⟩
  change MemcpyFullInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1]
  exact assign_i_step hG1.code hG1 hmwf1 hd1 hn1 hi1 hle_ik hdlo hdhi

private theorem setVar_lookup_ne {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : MlS)
    (v : ValueHOL 64) (h : b ≠ a) :
    (setVarHOLFinite a v s).locals.lookup b = s.locals.lookup b := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h]

private theorem lookup_memcpy :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
  lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

/-- `memcpy` (AST line 198): relational world step with output region `[(locN s "dst", locN s "n")]`. -/
theorem «wk_memcpy» :
    WorldKeeps WorldOK (fun s => [(locN s "dst", locN s "n")])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "memcpy") := by
  refine ⟨_, _, _, lookup_memcpy, ?_⟩
  intro F s hcode hWOK _ _ hres
  have hG := hWOK.1.1
  revert hres
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
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
  · intro h; exact absurd h not_resumes_error
  · rename_i iv hiv
    have hiv_eq : iv = .val (.word 0) := by
      simp [evalHOLExact] at hiv; exact hiv.symm
    subst hiv_eq
    split
    · set s1 := setVarHOLFinite (ofString "i") (.val (.word 0)) s with hs1
      rw [evaluateHOLFiniteState_seq_line780]
      set iteProg : ProgHOL 64 := .ite _ _ .skip
      have hite_nrr : noReturnOrRaise iteProg = true := rfl
      rcases hite_run : evaluateHOLFiniteState s1 iteProg with ⟨r_ite, s2⟩
      cases r_ite with
      | some _ =>
        intro hres
        have hnr := evaluate_noReturnOrRaise iteProg hite_nrr s1
        rw [hite_run] at hnr
        exact absurd hres hnr
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
              · rcases hsrc : s1.locals.lookup (ofString "src") with _ | sv <;>
                  simp [hd, hsrc, List.all, valueIsWord] at hcond
              · rcases hsrc : s1.locals.lookup (ofString "src") with _ | sv <;>
                  simp [hd, hsrc, List.all, valueIsWord] at hcond
          · simp at hc_ite
        obtain ⟨dst0, hdst0, hdst0_eq⟩ := hdst_word
        rw [evaluateHOLFiniteState_seq_line780]
        set loop3 : ProgHOL 64 := .while _ _
        have hl3_nrr : noReturnOrRaise loop3 = true := rfl
        rcases hw3 : evaluateHOLFiniteState s2 loop3 with ⟨rw3, s3⟩
        cases rw3 with
        | some _ =>
          intro hres
          have hnr := evaluate_noReturnOrRaise loop3 hl3_nrr s2
          rw [hw3] at hnr
          exact absurd hres hnr
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
          have hinv1 : MemcpyFullInv s dst0 n0 s1 := by
            refine ⟨hcode, guestInv_setVar _ _ s hG,
              memWriteFrame_locals_clock (memWriteFrame_refl s _) _ s.clock, ?_, ?_, 0, ?_,
              Nat.zero_le _, fun h => by simp at h⟩
            · rw [hs1, setVar_lookup_ne s (ofString "i") (ofString "dst") _ (by decide), hdst0]
            · rw [hs1, setVar_lookup_ne s (ofString "i") (ofString "n") _ (by decide), hn0]
            · simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hinv2 : MemcpyFullInv s dst0 n0 s2 := by
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
                  have hm1 := while_preserve_full _ _ rfl rfl step_loop1 s1.clock s1 m1 le_rfl hinv1 hw1
                  exact while_preserve_full _ _ rfl rfl step_loop2 m1.clock m1 s2 le_rfl hm1 hite_run
            · simp at hite_run
          have hinv3 : MemcpyFullInv s dst0 n0 s3 :=
            while_preserve_full _ _ rfl rfl step_loop3 s2.clock s2 s3 le_rfl hinv2 hw3
          rw [evaluateHOLFiniteState_seq_line780]
          set loop4 : ProgHOL 64 := .while _ _
          have hl4_nrr : noReturnOrRaise loop4 = true := rfl
          rcases hw4 : evaluateHOLFiniteState s3 loop4 with ⟨rw4, s4⟩
          cases rw4 with
          | some _ =>
            intro hres
            have hnr := evaluate_noReturnOrRaise loop4 hl4_nrr s3
            rw [hw4] at hnr
            exact absurd hres hnr
          | none =>
            dsimp only
            have hinv4 : MemcpyFullInv s dst0 n0 s4 :=
              while_preserve_full _ _ rfl rfl step_loop4 s3.clock s3 s4 le_rfl hinv3 hw4
            have hret_eval : evaluateHOLFiniteState s4 (.return (.const 0#64)) =
                (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite s4) := by
              simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact,
                sizeOfShapeWithContextHOL]
            rw [hret_eval]
            dsimp only
            intro hres
            have hmwf_final : MemWriteFrame s
                { (emptyLocalsHOLFinite s4) with
                  locals := (emptyLocalsHOLFinite s4).locals.resVarEq (ofString "i", s.locals.lookup (ofString "i")) }
                (locN s "dst", locN s "n") := by
              rw [← hdst0_eq, ← hn0_eq]
              exact memWriteFrame_locals_clock hinv4.2.2.1 _ s4.clock
            exact worldStep_of_region_writes (R := fun s => [(locN s "dst", locN s "n")])
              hWOK
              ⟨hmwf_final.1, hmwf_final.2.1, hmwf_final.2.2.1, hmwf_final.2.2.2.1,
                hmwf_final.2.2.2.2.1, hmwf_final.2.2.2.2.2.1⟩
              hmwf_final.2.2.2.2.2.2.1
              (fun a ha_lt hnot => hmwf_final.2.2.2.2.2.2.2.1 a ha_lt (fun hin => hnot _ (List.mem_singleton.2 rfl) hin))
              hmwf_final.2.2.2.2.2.2.2.2
    · intro h; exact absurd h not_resumes_error

end InitECandidate.Solver.Wave8Contracts.M08
