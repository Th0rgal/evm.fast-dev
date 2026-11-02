import InitECandidate.Solver.Wave8GuestInv.MemoryViews
import Guest.SoftwareAst

/-! `dm_memcpy`: `memcpy` resumes only if its destination `(dst, n)` (when `0 < n`) lies in the
memory domain (`[sourceBase, heapEnd)`).

AST index 16 (`Guest/SoftwareAst.lean:198`):
- Declares `i := 0`.
- Runs up to four `while` loops advancing `i` by `32`, `8`, `8`, and `1`, storing every byte/word
  in `[dst, dst + i)` inside `ordinaryDomain ⊆ [sourceBase, heapEnd)`.
- Since `heapEnd - sourceBase = domainBytes = 31104957928 < 2^64 - 64`, if `dst + i ≤ heapEnd` and
  an iteration stores at `dst + i ∈ [sourceBase, heapEnd)`, neither `dst + i` nor `i + step` can
  wrap modulo `2^64`, so `i` stays `≤ n` and `[dst, dst + i) ⊆ [sourceBase, heapEnd)`.
- Exiting the final `while (i < n)` yields `n ≤ i`, hence `i = n` and
  `Inside (dst, n) sourceBase heapEnd`.
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.M21

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

private def FunSpec (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      Q s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2

private def Resumes (r : Option (PanSemResultExact 64)) : Prop :=
  (∃ v, r = some (.returned v)) ∨ ∃ e v, r = some (.exception e v) ∧ e ≠ ofString "TrapErr"

private def ResumesInDomain (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Ivl) (fname : MlS) :
    Prop :=
  FunSpec GuestInv (fun s r _ => Resumes r → 0 < (R s).2 → Inside (R s) sourceBase heapEnd) fname

private theorem addresses_bounds (base : BitVec 64) (n : Nat) (x : BitVec 64)
    (hfit : base.toNat + 8 * n < 2 ^ 64)
    (h : Flapjack.Compiler.Backend.StackRemove.addresses base n x) :
    base.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ base.toNat + 8 * n := by
  induction n generalizing base with
  | zero => exact absurd h id
  | succ n ih =>
    rcases h with h | h
    · subst h; omega
    · have hb : (base + Flapjack.Compiler.Backend.StackRemove.bytesInWord 64).toNat = base.toNat + 8 := by
        rw [BitVec.toNat_add_of_lt]
        · simp [Flapjack.Compiler.Backend.StackRemove.bytesInWord]
        · simp [Flapjack.Compiler.Backend.StackRemove.bytesInWord]; omega
      have := ih (base + Flapjack.Compiler.Backend.StackRemove.bytesInWord 64) (by omega) h
      omega

private theorem ordinaryDomain_bounds (x : BitVec 64) (h : ordinaryDomain x) :
    sourceBase ≤ x.toNat ∧ x.toNat + 8 ≤ heapEnd := by
  unfold ordinaryDomain at h
  have hn : ((stackStart - sourceBase) / 8 - globalsWords) = 3888119741 := by decide
  rw [hn] at h
  have hs : (BitVec.ofNat 64 sourceBase).toNat = 2701131776 := by decide
  have := addresses_bounds _ _ x (by rw [hs]; decide) h
  rw [hs] at this
  have e1 : sourceBase = 2701131776 := by decide
  have e2 : heapEnd = 2701131776 + 8 * 3888119741 := by decide
  omega

private theorem byteAlign_bounds (a : BitVec 64) :
    (panByteAlignHOL (width := 64) a).toNat ≤ a.toNat ∧
      a.toNat < (panByteAlignHOL (width := 64) a).toNat + 8 := by
  have h8 : 2 ^ Nat.log2 (64 / 8) = 8 := by decide
  simp only [panByteAlignHOL, h8, BitVec.toNat_ofNat]
  have ha := a.isLt
  have : a.toNat / 8 * 8 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]
  omega

private theorem sourceBase_eq : sourceBase = 2701131776 := by decide
private theorem heapEnd_eq : heapEnd = 33806089704 := by decide

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

private theorem lex_of {a1 a2 b1 b2 : Nat} (h : a1 < a2 ∨ a1 = a2 ∧ b1 < b2) :
    Prod.Lex (· < ·) (· < ·) (a1, b1) (a2, b2) := by
  rcases h with h | ⟨rfl, h⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ h

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

private def MemcpyInv {F : Type} (dst0 n0 : BitVec 64) (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧ GuestInv s ∧
  s.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
  s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
  ∃ iw : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
    iw.toNat ≤ n0.toNat ∧
    (0 < iw.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + iw.toNat ≤ heapEnd)

private theorem eval_add2_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    [h : DecidablePred s.memaddrs] (d i : MlS) (x y a : BitVec 64)
    (hx : s.locals.lookup d = some (.val (.word x)))
    (hy : s.locals.lookup i = some (.val (.word y)))
    (he : @evalHOLExact 64 F _ s.toExact h (.op .add [.var .local d, .var .local i]) =
      some (.val (.word a))) :
    a = x + y := by
  simp [evalHOLExact, evalListHOLExact, hx, hy, valueIsWord, valueWord, wordOpHOL, wordOp] at he
  exact he.symm

private theorem eval_add3_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    [h : DecidablePred s.memaddrs] (d i : MlS) (x y c a : BitVec 64)
    (hx : s.locals.lookup d = some (.val (.word x)))
    (hy : s.locals.lookup i = some (.val (.word y)))
    (he : @evalHOLExact 64 F _ s.toExact h (.op .add [.var .local d, .var .local i, .const c]) =
      some (.val (.word a))) :
    a = x + y + c := by
  simp [evalHOLExact, evalListHOLExact, hx, hy, valueIsWord, valueWord, wordOpHOL, wordOp] at he
  rw [← he, BitVec.add_assoc]

private theorem eval_load_one_isVal {F : Type} (s : PanSemStateFiniteExact 64 F)
    [h : DecidablePred s.memaddrs] (e : ExpHOL 64) (val : ValueHOL 64)
    (he : @evalHOLExact 64 F _ s.toExact h (.load .one e) = some val) :
    ∃ w, val = .val w := by
  simp only [evalHOLExact] at he
  split at he
  · split at he
    · simp only [memLoadHOLExact] at he
      split at he
      · exact ⟨_, (Option.some.inj he).symm⟩
      · simp at he
    · simp at he
  · simp at he

private theorem seq_none_split {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64)
    (hG : GuestInv s) (_hdst : ∃ dst0, s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (dst0 iw : BitVec 64)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (had : avoidsLocal (ofString "dst") a = true)
    (hai : avoidsLocal (ofString "i") a = true)
    (h : (evaluateHOLFiniteState s (.seq a b)).1 = none) :
    (evaluateHOLFiniteState s a).1 = none ∧
    ∃ m : PanSemStateFiniteExact 64 F,
      GuestInv m ∧
      m.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
      m.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
      (evaluateHOLFiniteState m b).1 = none := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
  rw [hr] at h
  cases r with
  | none =>
    refine ⟨rfl, m, ?_, ?_, ?_, h⟩
    · have hm := guestInv_evaluate s a hG; rw [hr] at hm; exact hm
    · have := evaluate_avoidsLocal_flowing (ofString "dst") a had s (by rw [hr]; exact Or.inl rfl)
      rw [hr] at this; exact this.trans hd
    · have := evaluate_avoidsLocal_flowing (ofString "i") a hai s (by rw [hr]; exact Or.inl rfl)
      rw [hr] at this; exact this.trans hi
  | some _ => simp at h

private theorem store_word_dom {F : Type} (s : PanSemStateFiniteExact 64 F) (hG : GuestInv s)
    (dst0 iw : BitVec 64) (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (srcExp : ExpHOL 64)
    (hnone : (evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
        (.load .one srcExp))).1 = none) :
    sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + 8 ≤ heapEnd := by
  rw [evaluateHOLFiniteState_store] at hnone
  split at hnone
  · rename_i address haddr
    have ha := eval_add2_locals s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (ofString "dst") (ofString "i") dst0 iw address hdst hi haddr
    subst ha
    split at hnone
    · rename_i val hval
      obtain ⟨w, rfl⟩ := eval_load_one_isVal s (h := fun a => Classical.propDecidable (s.memaddrs a))
        srcExp val hval
      split at hnone
      · rename_i mem hmem
        have hdom : s.memaddrs (dst0 + iw) := by
          simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
          by_contra hc; simp [hc] at hmem
        rw [hG.memaddrs] at hdom
        exact ordinaryDomain_bounds _ hdom
      · simp at hnone
    · simp at hnone
  · simp at hnone

private theorem store_word_off_dom {F : Type} (s : PanSemStateFiniteExact 64 F) (hG : GuestInv s)
    (dst0 iw c : BitVec 64) (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (srcExp : ExpHOL 64)
    (hnone : (evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const c])
        (.load .one srcExp))).1 = none) :
    sourceBase ≤ (dst0 + iw + c).toNat ∧ (dst0 + iw + c).toNat + 8 ≤ heapEnd := by
  rw [evaluateHOLFiniteState_store] at hnone
  split at hnone
  · rename_i address haddr
    have ha := eval_add3_locals s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (ofString "dst") (ofString "i") dst0 iw c address hdst hi haddr
    subst ha
    split at hnone
    · rename_i val hval
      obtain ⟨w, rfl⟩ := eval_load_one_isVal s (h := fun a => Classical.propDecidable (s.memaddrs a))
        srcExp val hval
      split at hnone
      · rename_i mem hmem
        have hdom : s.memaddrs (dst0 + iw + c) := by
          simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
          by_contra hc; simp [hc] at hmem
        rw [hG.memaddrs] at hdom
        exact ordinaryDomain_bounds _ hdom
      · simp at hnone
    · simp at hnone
  · simp at hnone

private theorem storeByte_dom {F : Type} (s : PanSemStateFiniteExact 64 F) (hG : GuestInv s)
    (dst0 iw : BitVec 64) (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (vExp : ExpHOL 64)
    (hnone : (evaluateHOLFiniteState s
      (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
        vExp)).1 = none) :
    sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + 1 ≤ heapEnd := by
  rw [evaluateHOLFiniteState_storeByte] at hnone
  split at hnone
  · rename_i address haddr
    have ha := eval_add2_locals s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (ofString "dst") (ofString "i") dst0 iw address hdst hi haddr
    subst ha
    split at hnone
    · split at hnone
      · rename_i mem hmem
        have hdom : s.memaddrs (panByteAlignHOL (width := 64) (dst0 + iw)) := by
          by_contra hc
          revert hmem
          simp only [panMemStoreByteWord8HOL]
          split <;> first | contradiction | simp [hc] | (split <;> first | contradiction | simp [hc])
        rw [hG.memaddrs] at hdom
        have hb := ordinaryDomain_bounds _ hdom
        have hal := byteAlign_bounds (dst0 + iw)
        omega
      · simp at hnone
    · simp at hnone
  · simp at hnone

private theorem storeByte_off_dom {F : Type} (s : PanSemStateFiniteExact 64 F) (hG : GuestInv s)
    (dst0 iw c : BitVec 64) (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (vExp : ExpHOL 64)
    (hnone : (evaluateHOLFiniteState s
      (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const c])
        vExp)).1 = none) :
    sourceBase ≤ (dst0 + iw + c).toNat ∧ (dst0 + iw + c).toNat + 1 ≤ heapEnd := by
  rw [evaluateHOLFiniteState_storeByte] at hnone
  split at hnone
  · rename_i address haddr
    have ha := eval_add3_locals s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (ofString "dst") (ofString "i") dst0 iw c address hdst hi haddr
    subst ha
    split at hnone
    · split at hnone
      · rename_i mem hmem
        have hdom : s.memaddrs (panByteAlignHOL (width := 64) (dst0 + iw + c)) := by
          by_contra hc
          revert hmem
          simp only [panMemStoreByteWord8HOL]
          split <;> first | contradiction | simp [hc] | (split <;> first | contradiction | simp [hc])
        rw [hG.memaddrs] at hdom
        have hb := ordinaryDomain_bounds _ hdom
        have hal := byteAlign_bounds (dst0 + iw + c)
        omega
      · simp at hnone
    · simp at hnone
  · simp at hnone

private theorem step_domain_nowrap (dst0 iw n0 k : BitVec 64)
    (hle : iw.toNat ≤ n0.toNat)
    (hprev : 0 < iw.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + iw.toNat ≤ heapEnd)
    (hcur : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + k.toNat ≤ heapEnd)
    (hk : 0 < k.toNat) (hk32 : k.toNat ≤ 32)
    (hcond : ¬ (n0 < iw + k)) :
    (iw + k).toNat = iw.toNat + k.toNat ∧
      (iw + k).toNat ≤ n0.toNat ∧
      sourceBase ≤ dst0.toNat ∧ dst0.toNat + (iw + k).toNat ≤ heapEnd := by
  have hS := sourceBase_eq
  have hH := heapEnd_eq
  have hdlt := dst0.isLt
  have hilt := iw.isLt
  have hnlt := n0.isLt
  rw [BitVec.lt_def] at hcond
  by_cases hiz : iw.toNat = 0
  · have hi0 : iw = 0 := BitVec.eq_of_toNat_eq hiz
    subst hi0
    have hd0 : dst0 + 0 = dst0 := BitVec.add_zero _
    have hk0 : (0 : BitVec 64) + k = k := BitVec.zero_add _
    rw [hd0] at hcur
    rw [hk0] at hcond ⊢
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [hz0]
    exact ⟨by omega, by omega, hcur.1, hcur.2⟩
  · obtain ⟨hdlo, hdhi⟩ := hprev (by omega)
    have hadd_di : (dst0 + iw).toNat = dst0.toNat + iw.toNat :=
      BitVec.toNat_add_of_lt (by omega)
    rw [hadd_di] at hcur
    have hik_lt : iw.toNat + k.toNat < 2 ^ 64 := by omega
    have hadd_ik : (iw + k).toNat = iw.toNat + k.toNat :=
      BitVec.toNat_add_of_lt hik_lt
    rw [hadd_ik] at hcond ⊢
    exact ⟨rfl, by omega, hdlo, by omega⟩

private theorem eval_notLower_true {F : Type} (s : PanSemStateFiniteExact 64 F)
    [h : DecidablePred s.memaddrs] (n0 iw k w : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (he : @evalHOLExact 64 F _ s.toExact h
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
    [h : DecidablePred s.memaddrs] (n0 iw w : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (he : @evalHOLExact 64 F _ s.toExact h
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word w)))
    (hw : w ≠ 0) :
    iw < n0 := by
  simp [evalHOLExact, hn, hi, Compiler.Encoders.Asm.wordCmpHOL] at he
  by_contra hge
  simp [hge] at he
  exact hw he.symm

private theorem eval_lower_false {F : Type} (s : PanSemStateFiniteExact 64 F)
    [h : DecidablePred s.memaddrs] (n0 iw : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (he : @evalHOLExact 64 F _ s.toExact h
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word 0))) :
    n0.toNat ≤ iw.toNat := by
  simp only [evalHOLExact, hn, hi, Compiler.Encoders.Asm.wordCmpHOL] at he
  by_cases hlt : iw < n0
  · simp [hlt] at he
  · rw [BitVec.lt_def] at hlt; omega

/-- Generic while preservation for `MemcpyInv` when the loop body has no `break` or `continue`
and preserves `MemcpyInv` on `none` runs when the condition holds. -/
private theorem while_preserve_inv {F : Type} {dst0 n0 : BitVec 64}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hnb : noBreak body = true) (hnc : noTopContinue body = true)
    (hbody : ∀ (s : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      MemcpyInv dst0 n0 s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word w)) → w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemcpyInv dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2)
    (k : Nat) (s post : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k)
    (hinv : MemcpyInv dst0 n0 s)
    (hrun : evaluateHOLFiniteState s (.while cond body) = (none, post)) :
    MemcpyInv dst0 n0 post ∧
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
        · rename_i hz; omega
      · rename_i hz
        have hcw0 : cw = 0 := Classical.not_not.mp hz
        subst hcw0
        simp at hrun
        subst hrun
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
        · rename_i hclk
          dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have nb := evaluate_noBreak body hnb (decClockHOLFinite s)
          have nc := evaluate_noTopContinue body hnc (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at hrun rem nb nc
          cases r1 with
          | none =>
            have hmid : MemcpyInv dst0 n0 mid := by
              have hb := hbody s cw hinv hcond hnz (by rw [hbr])
              rw [hbr] at hb
              exact hb
            have hmk : mid.clock ≤ k := by
              change mid.clock ≤ s.clock - 1 at rem
              omega
            exact ih mid hmk hmid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl nc
            | «break» => exact absurd rfl nb
            | _ => simp at hrun
      · rename_i hz
        have hcw0 : cw = 0 := Classical.not_not.mp hz
        subst hcw0
        simp at hrun
        subst hrun
        exact ⟨hinv, hcond⟩
    · simp at hrun

private theorem countedBody_loop1 :
    CountedBody (ofString "i") (BitVec.ofNat 64 32)
      (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8])
            (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 8])))
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16])
              (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 16])))
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24])
                (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 24])))
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32]))))))
      0 := by
  refine CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl ?_
  refine CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl ?_
  refine CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl ?_
  exact CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr

private theorem countedBody_loop2 :
    CountedBody (ofString "i") (BitVec.ofNat 64 8)
      (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
      0 :=
  CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr

private theorem countedBody_loop3 :
    CountedBody (ofString "i") (BitVec.ofNat 64 8)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
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
      0 := by
  refine CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl ?_
  refine CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl ?_
  refine CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl ?_
  refine CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl ?_
  refine CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl ?_
  refine CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl ?_
  refine CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl ?_
  exact CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr

private theorem countedBody_loop4 :
    CountedBody (ofString "i") (BitVec.ofNat 64 1)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
      0 :=
  CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr

private theorem step_loop1 {F : Type} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemcpyInv dst0 n0 s)
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
      MemcpyInv dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  have hGd : GuestInv (decClockHOLFinite s) := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hnl := eval_notLower_true s (h := fun a => Classical.propDecidable (s.memaddrs a))
    n0 iw 32 w hn hi hcond hw
  obtain ⟨hs0, s1, hG1, hd1, hi1, hr1⟩ :=
    seq_none_split (decClockHOLFinite s) _ _ hGd ⟨dst0, hdst⟩ dst0 iw hdst hi rfl rfl hnone
  have hd0 := store_word_dom (decClockHOLFinite s) hGd dst0 iw hdst hi _ hs0
  obtain ⟨hs8, s2, hG2, hd2, hi2, hr2⟩ :=
    seq_none_split s1 _ _ hG1 ⟨dst0, hd1⟩ dst0 iw hd1 hi1 rfl rfl hr1
  have hd8 := store_word_off_dom s1 hG1 dst0 iw 8 hd1 hi1 _ hs8
  obtain ⟨hs16, s3, hG3, hd3, hi3, hr3⟩ :=
    seq_none_split s2 _ _ hG2 ⟨dst0, hd2⟩ dst0 iw hd2 hi2 rfl rfl hr2
  have hd16 := store_word_off_dom s2 hG2 dst0 iw 16 hd2 hi2 _ hs16
  obtain ⟨hs24, _⟩ :=
    seq_none_split s3 _ _ hG3 ⟨dst0, hd3⟩ dst0 iw hd3 hi3 rfl rfl hr3
  have hd24 := store_word_off_dom s3 hG3 dst0 iw 24 hd3 hi3 _ hs24
  have hH := heapEnd_eq
  have a8 : (dst0 + iw + 8).toNat = (dst0 + iw).toNat + 8 :=
    BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 8 < 2 ^ 64; omega)
  have a16 : (dst0 + iw + 16).toNat = (dst0 + iw).toNat + 16 := by
    have : (dst0 + iw).toNat + 8 + 8 ≤ heapEnd := by rw [← a8]; exact hd8.2
    exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 16 < 2 ^ 64; omega)
  have a24 : (dst0 + iw + 24).toNat = (dst0 + iw).toNat + 24 := by
    have : (dst0 + iw).toNat + 16 + 8 ≤ heapEnd := by rw [← a16]; exact hd16.2
    exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 24 < 2 ^ 64; omega)
  have hcur32 : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + (32 : BitVec 64).toNat ≤ heapEnd := by
    refine ⟨hd0.1, ?_⟩
    rw [a24] at hd24
    change (dst0 + iw).toNat + 32 ≤ heapEnd
    omega
  obtain ⟨_, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 32 hle hdom hcur32 (by decide) (by decide) hnl
  have hpostG : GuestInv (evaluateHOLFiniteState (decClockHOLFinite s) body).2 :=
    guestInv_evaluate _ _ hGd
  have hdst_p : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "dst") =
      some (.val (.word dst0)) := by
    rw [evaluate_avoidsLocal_flowing (ofString "dst") body rfl (decClockHOLFinite s) (Or.inl hnone)]
    exact hdst
  have hn_p : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "n") =
      some (.val (.word n0)) := by
    rw [evaluate_avoidsLocal_flowing (ofString "n") body rfl (decClockHOLFinite s) (Or.inl hnone)]
    exact hn
  obtain ⟨_, _, _, _, hc5⟩ := countedBody_loop1.run (decClockHOLFinite s) hc iw hi (Nat.zero_le _)
  obtain ⟨hi_p, hc_p⟩ := hc5 hnone
  exact ⟨hc_p.trans hc, hpostG, hdst_p, hn_p, iw + 32, hi_p, hle_ik, fun _ => ⟨hdlo, hdhi⟩⟩

private theorem step_loop2 {F : Type} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemcpyInv dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemcpyInv dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  have hGd : GuestInv (decClockHOLFinite s) := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hnl := eval_notLower_true s (h := fun a => Classical.propDecidable (s.memaddrs a))
    n0 iw 8 w hn hi hcond hw
  obtain ⟨hs0, _⟩ :=
    seq_none_split (decClockHOLFinite s) _ _ hGd ⟨dst0, hdst⟩ dst0 iw hdst hi rfl rfl hnone
  have hd0 := store_word_dom (decClockHOLFinite s) hGd dst0 iw hdst hi _ hs0
  obtain ⟨_, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom hd0 (by decide) (by decide) hnl
  have hpostG : GuestInv (evaluateHOLFiniteState (decClockHOLFinite s) body).2 :=
    guestInv_evaluate _ _ hGd
  have hdst_p : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "dst") =
      some (.val (.word dst0)) := by
    rw [evaluate_avoidsLocal_flowing (ofString "dst") body rfl (decClockHOLFinite s) (Or.inl hnone)]
    exact hdst
  have hn_p : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "n") =
      some (.val (.word n0)) := by
    rw [evaluate_avoidsLocal_flowing (ofString "n") body rfl (decClockHOLFinite s) (Or.inl hnone)]
    exact hn
  obtain ⟨_, _, _, _, hc5⟩ := countedBody_loop2.run (decClockHOLFinite s) hc iw hi (Nat.zero_le _)
  obtain ⟨hi_p, hc_p⟩ := hc5 hnone
  exact ⟨hc_p.trans hc, hpostG, hdst_p, hn_p, iw + 8, hi_p, hle_ik, fun _ => ⟨hdlo, hdhi⟩⟩

private theorem step_loop3 {F : Type} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemcpyInv dst0 n0 s)
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
      MemcpyInv dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  have hGd : GuestInv (decClockHOLFinite s) := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hnl := eval_notLower_true s (h := fun a => Classical.propDecidable (s.memaddrs a))
    n0 iw 8 w hn hi hcond hw
  have hH := heapEnd_eq
  obtain ⟨hs0, s1, hG1, hd1, hi1, hr1⟩ :=
    seq_none_split (decClockHOLFinite s) _ _ hGd ⟨dst0, hdst⟩ dst0 iw hdst hi rfl rfl hnone
  have hd0 := storeByte_dom (decClockHOLFinite s) hGd dst0 iw hdst hi _ hs0
  obtain ⟨hs1, s2, hG2, hd2, hi2, hr2⟩ :=
    seq_none_split s1 _ _ hG1 ⟨dst0, hd1⟩ dst0 iw hd1 hi1 rfl rfl hr1
  obtain ⟨hs2, s3, hG3, hd3, hi3, hr3⟩ :=
    seq_none_split s2 _ _ hG2 ⟨dst0, hd2⟩ dst0 iw hd2 hi2 rfl rfl hr2
  obtain ⟨hs3, s4, hG4, hd4, hi4, hr4⟩ :=
    seq_none_split s3 _ _ hG3 ⟨dst0, hd3⟩ dst0 iw hd3 hi3 rfl rfl hr3
  obtain ⟨hs4, s5, hG5, hd5, hi5, hr5⟩ :=
    seq_none_split s4 _ _ hG4 ⟨dst0, hd4⟩ dst0 iw hd4 hi4 rfl rfl hr4
  obtain ⟨hs5, s6, hG6, hd6, hi6, hr6⟩ :=
    seq_none_split s5 _ _ hG5 ⟨dst0, hd5⟩ dst0 iw hd5 hi5 rfl rfl hr5
  obtain ⟨hs6, s7, hG7, hd7, hi7, hr7⟩ :=
    seq_none_split s6 _ _ hG6 ⟨dst0, hd6⟩ dst0 iw hd6 hi6 rfl rfl hr6
  obtain ⟨hs7, _⟩ :=
    seq_none_split s7 _ _ hG7 ⟨dst0, hd7⟩ dst0 iw hd7 hi7 rfl rfl hr7
  have hb1 := storeByte_off_dom s1 hG1 dst0 iw 1 hd1 hi1 _ hs1
  have hb2 := storeByte_off_dom s2 hG2 dst0 iw 2 hd2 hi2 _ hs2
  have hb3 := storeByte_off_dom s3 hG3 dst0 iw 3 hd3 hi3 _ hs3
  have hb4 := storeByte_off_dom s4 hG4 dst0 iw 4 hd4 hi4 _ hs4
  have hb5 := storeByte_off_dom s5 hG5 dst0 iw 5 hd5 hi5 _ hs5
  have hb6 := storeByte_off_dom s6 hG6 dst0 iw 6 hd6 hi6 _ hs6
  have hb7 := storeByte_off_dom s7 hG7 dst0 iw 7 hd7 hi7 _ hs7
  have a7 : (dst0 + iw + 7).toNat = (dst0 + iw).toNat + 7 :=
    BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 7 < 2 ^ 64; omega)
  have hcur8 : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + (8 : BitVec 64).toNat ≤ heapEnd := by
    refine ⟨hd0.1, ?_⟩
    rw [a7] at hb7
    change (dst0 + iw).toNat + 8 ≤ heapEnd
    omega
  obtain ⟨_, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom hcur8 (by decide) (by decide) hnl
  have hpostG : GuestInv (evaluateHOLFiniteState (decClockHOLFinite s) body).2 :=
    guestInv_evaluate _ _ hGd
  have hdst_p : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "dst") =
      some (.val (.word dst0)) := by
    rw [evaluate_avoidsLocal_flowing (ofString "dst") body rfl (decClockHOLFinite s) (Or.inl hnone)]
    exact hdst
  have hn_p : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "n") =
      some (.val (.word n0)) := by
    rw [evaluate_avoidsLocal_flowing (ofString "n") body rfl (decClockHOLFinite s) (Or.inl hnone)]
    exact hn
  obtain ⟨_, _, _, _, hc5⟩ := countedBody_loop3.run (decClockHOLFinite s) hc iw hi (Nat.zero_le _)
  obtain ⟨hi_p, hc_p⟩ := hc5 hnone
  exact ⟨hc_p.trans hc, hpostG, hdst_p, hn_p, iw + 8, hi_p, hle_ik, fun _ => ⟨hdlo, hdhi⟩⟩

private theorem step_loop4 {F : Type} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemcpyInv dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemcpyInv dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  have hGd : GuestInv (decClockHOLFinite s) := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hlt := eval_lower_true s (h := fun a => Classical.propDecidable (s.memaddrs a))
    n0 iw w hn hi hcond hw
  rw [BitVec.lt_def] at hlt
  obtain ⟨hs0, _⟩ :=
    seq_none_split (decClockHOLFinite s) _ _ hGd ⟨dst0, hdst⟩ dst0 iw hdst hi rfl rfl hnone
  have hd0 := storeByte_dom (decClockHOLFinite s) hGd dst0 iw hdst hi _ hs0
  have hnlt := n0.isLt
  have ha1 : (iw + 1).toNat = iw.toNat + 1 :=
    BitVec.toNat_add_of_lt (by change iw.toNat + 1 < 2 ^ 64; omega)
  have hnl : ¬ (n0 < iw + 1) := by
    rw [BitVec.lt_def, ha1]; omega
  obtain ⟨_, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 1 hle hdom hd0 (by decide) (by decide) hnl
  have hpostG : GuestInv (evaluateHOLFiniteState (decClockHOLFinite s) body).2 :=
    guestInv_evaluate _ _ hGd
  have hdst_p : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "dst") =
      some (.val (.word dst0)) := by
    rw [evaluate_avoidsLocal_flowing (ofString "dst") body rfl (decClockHOLFinite s) (Or.inl hnone)]
    exact hdst
  have hn_p : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup (ofString "n") =
      some (.val (.word n0)) := by
    rw [evaluate_avoidsLocal_flowing (ofString "n") body rfl (decClockHOLFinite s) (Or.inl hnone)]
    exact hn
  obtain ⟨_, _, _, _, hc5⟩ := countedBody_loop4.run (decClockHOLFinite s) hc iw hi (Nat.zero_le _)
  obtain ⟨hi_p, hc_p⟩ := hc5 hnone
  exact ⟨hc_p.trans hc, hpostG, hdst_p, hn_p, iw + 1, hi_p, hle_ik, fun _ => ⟨hdlo, hdhi⟩⟩

private theorem setVar_lookup_ne {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : MlS)
    (v : ValueHOL 64) (h : b ≠ a) :
    (setVarHOLFinite a v s).locals.lookup b = s.locals.lookup b := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h]

theorem lookup_memcpy :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
  lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

/-- `memcpy` (AST index 16, line 198): resumes only if its destination is in the memory domain. -/
theorem «dm_memcpy» :
    ResumesInDomain (fun s => (locN s "dst", locN s "n")) (ofString "memcpy") := by
  refine ⟨_, _, _, lookup_memcpy, ?_⟩
  intro F s hcode hG _ _ hres hn_pos
  dsimp only at hn_pos ⊢
  have hn_word : ∃ n0 : BitVec 64,
      s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧ n0.toNat = locN s "n" := by
    unfold locN at hn_pos ⊢
    split at hn_pos
    · rename_i w hw; exact ⟨w, hw, rfl⟩
    · omega
  obtain ⟨n0, hn0, hn0_eq⟩ := hn_word
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
      | some x =>
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
        have hinv1 : MemcpyInv dst0 n0 s1 := by
          refine ⟨hcode, guestInv_with_locals_clock s s1.locals s.clock hG, ?_, ?_, 0, ?_,
            Nat.zero_le _, fun h => by simp at h⟩
          · rw [hs1, setVar_lookup_ne s (ofString "i") (ofString "dst") _ (by decide), hdst0]
          · rw [hs1, setVar_lookup_ne s (ofString "i") (ofString "n") _ (by decide), hn0]
          · simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hinv2 : MemcpyInv dst0 n0 s2 := by
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
                have hm1 := (while_preserve_inv _ _ rfl rfl step_loop1 s1.clock s1 m1 le_rfl hinv1 hw1).1
                exact (while_preserve_inv _ _ rfl rfl step_loop2 m1.clock m1 s2 le_rfl hm1 hite_run).1
          · simp at hite_run
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
          have hinv3 : MemcpyInv dst0 n0 s3 :=
            (while_preserve_inv _ _ rfl rfl step_loop3 s2.clock s2 s3 le_rfl hinv2 hw3).1
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
            intro _
            obtain ⟨⟨_, _, _, hn4, iw, hi4, hle4, hdom4⟩, hcond4⟩ :=
              while_preserve_inv _ _ rfl rfl step_loop4 s3.clock s3 s4 le_rfl hinv3 hw4
            have hge4 := eval_lower_false s4
              (h := fun a => Classical.propDecidable (s4.memaddrs a)) n0 iw hn4 hi4 hcond4
            have hi_eq : iw.toNat = n0.toNat := by omega
            have hi_pos : 0 < iw.toNat := by omega
            obtain ⟨hdlo, hdhi⟩ := hdom4 hi_pos
            rw [← hdst0_eq, ← hn0_eq, ← hi_eq]
            exact ⟨hdlo, hdhi⟩
    · intro h; exact absurd h not_resumes_error

end InitECandidate.Solver.Wave8GuestInv.M21
