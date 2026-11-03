import InitECandidate.Solver.Wave8GuestInv.Deliveries.M28.Common

/-! Write-frame contract `ww_memzero` for contract micro-shard `m28` (`wave8/contracts-m28`),
checked against frozen spec revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

`memzero` (`Guest/SoftwareAst.lean:251`, AST index 17):
- Declares `i := 0`.
- Runs up to four `while` loops advancing `i` by `32`, `8`, `8`, and `1`, storing `0` only into
  bytes `[dst + i, dst + i + step)` inside `ordinaryDomain ⊆ [sourceBase, heapEnd)` without wrapping.
- Leaves `globals`, `code`, `memaddrs`, `shMemaddrs`, `baseAddr`, `be`, `ffi`, `structs`,
  `eshapes`, and `topAddr` untouched (`gw = []`), so `ArenaReady` and all globals are preserved
  trivially and `FrameOutside` holds for `[(locN s "dst", locN s "n")]`.
- Also exports `memzero_body_frame` so `node_new_branch` in `sp__decode_step` can reuse it directly.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8Contracts.M28

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-- Body-level memory write frame for `memzero`: preserves all non-local/non-clock/non-memory
fields, modifies memory only on cells meeting `ivl`, and writes only in-domain cells. -/
def MemzeroWriteFrame {F : Type} (s0 s : PanSemStateFiniteExact 64 F) (ivl : Ivl) : Prop :=
  s.code = s0.code ∧ s.memaddrs = s0.memaddrs ∧ s.shMemaddrs = s0.shMemaddrs ∧
  s.baseAddr = s0.baseAddr ∧ s.be = s0.be ∧ s.globals = s0.globals ∧
  s.ffi = s0.ffi ∧ s.topAddr = s0.topAddr ∧
  FrameOutside s0 s [ivl] (0, 0) ∧
  (∀ a : BitVec 64, s.memory a ≠ s0.memory a → s0.memaddrs a)

private theorem memzeroWriteFrame_refl {F : Type} (s0 : PanSemStateFiniteExact 64 F) (ivl : Ivl) :
    MemzeroWriteFrame s0 s0 ivl :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ h => absurd rfl h⟩

private theorem memzeroWriteFrame_locals_clock {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {ivl : Ivl} (h : MemzeroWriteFrame s0 s ivl) (loc : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    MemzeroWriteFrame s0 { s with locals := loc, clock := k } ivl :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

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
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by
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

private theorem store_const_zero_frame {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {ivl : Ivl} (hG : GuestInv s) (hmwf : MemzeroWriteFrame s0 s ivl)
    (addrExp : ExpHOL 64) (x : BitVec 64)
    (haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp =
      some (.val (.word x)))
    (hnone : (evaluateHOLFiniteState s (.store addrExp (.const 0))).1 = none) :
    sourceBase ≤ x.toNat ∧ x.toNat + 8 ≤ heapEnd ∧
    (x.toNat ≥ ivl.1 ∧ x.toNat + 8 ≤ ivl.1 + ivl.2 →
      MemzeroWriteFrame s0 (evaluateHOLFiniteState s (.store addrExp (.const 0))).2 ivl) := by
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
      refine ⟨hdom_ord.2.1, by omega, fun hxin => ?_⟩
      dsimp only
      obtain ⟨hc, hm, hsh, hba, hbe, hg, hffi, hta, hfr, hdwr⟩ := hmwf
      refine ⟨hc, hm, hsh, hba, hbe, hg, hffi, hta, ?_, ?_⟩
      · intro a hk hf
        by_cases hax : a = x
        · exfalso
          subst hax
          exact hk ivl (List.mem_singleton.2 rfl) ⟨by omega, by omega⟩
        · simp only [hax, ↓reduceIte]
          exact hfr a hk hf
      · intro a hne
        by_cases hax : a = x
        · subst hax; rw [← hm]; exact hdom
        · simp only [hax, ↓reduceIte] at hne
          exact hdwr a hne
    · simp [hdom] at hmem
  · simp at hnone

private theorem storeByte_const_zero_frame {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {ivl : Ivl} (hG : GuestInv s) (hmwf : MemzeroWriteFrame s0 s ivl)
    (addrExp : ExpHOL 64) (x : BitVec 64)
    (haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp =
      some (.val (.word x)))
    (hnone : (evaluateHOLFiniteState s (.storeByte addrExp (.const 0))).1 = none) :
    sourceBase ≤ x.toNat ∧ x.toNat + 1 ≤ heapEnd ∧
    (InIvl x.toNat ivl →
      MemzeroWriteFrame s0 (evaluateHOLFiniteState s (.storeByte addrExp (.const 0))).2 ivl) := by
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
    have hal_nat := panByteAlign_toNat64 x
    refine ⟨by omega, by omega, fun hxin => ?_⟩
    dsimp only
    obtain ⟨hc, hm, hsh, hba, hbe, hg, hffi, hta, hfr, hdwr⟩ := hmwf
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
    refine ⟨hc, hm, hsh, hba, hbe, hg, hffi, hta, ?_, ?_⟩
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
    · intro a hne
      by_cases hax : a = panByteAlignHOL x
      · subst hax; rw [← hm]; exact hdom
      · change mem' a ≠ s0.memory a at hne
        rw [hmem_cell a hax] at hne
        exact hdwr a hne
  · simp at hnone

private def MemzeroFullInv {F : Type} (s0 : PanSemStateFiniteExact 64 F) (dst0 n0 : BitVec 64)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧ GuestInv s ∧
  MemzeroWriteFrame s0 s (dst0.toNat, n0.toNat) ∧
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
    (hmwf : MemzeroWriteFrame s0 s (dst0.toNat, n0.toNat))
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hle : (iw + k).toNat ≤ n0.toNat)
    (hdlo : sourceBase ≤ dst0.toNat) (hdhi : dst0.toNat + (iw + k).toNat ≤ heapEnd) :
    MemzeroFullInv s0 dst0 n0
      (evaluateHOLFiniteState s (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const k]))).2 := by
  have hrun : evaluateHOLFiniteState s
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const k])) =
      (none, setVarHOLFinite (ofString "i") (.val (.word (iw + k))) s) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi, wordOpHOL, wordOp,
      valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
      shapeOfHOLExact, shapeEqHOL]
  rw [hrun]
  dsimp only
  refine ⟨hc, guestInv_setVar _ _ s hG, memzeroWriteFrame_locals_clock hmwf _ s.clock,
    ?_, ?_, iw + k, ?_, hle, fun _ => ⟨hdlo, hdhi⟩⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd, show ofString "i" ≠ ofString "dst" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "i" ≠ ofString "n" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

private theorem while_preserve_full {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hnb : noBreak body = true) (hnc : noTopContinue body = true)
    (hbody : ∀ (s : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      MemzeroFullInv s0 dst0 n0 s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word w)) → w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemzeroFullInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2)
    (k : Nat) (s post : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k)
    (hinv : MemzeroFullInv s0 dst0 n0 s)
    (hrun : evaluateHOLFiniteState s (.while cond body) = (none, post)) :
    MemzeroFullInv s0 dst0 n0 post := by
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
            have hmid : MemzeroFullInv s0 dst0 n0 mid := by
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
    (hinv : MemzeroFullInv s0 dst0 n0 s)
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
      MemzeroFullInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hmwf, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hmwfd : MemzeroWriteFrame s0 sd (dst0.toNat, n0.toNat) := memzeroWriteFrame_locals_clock hmwf s.locals (s.clock - 1)
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
  have st0 := store_const_zero_frame hGd hmwfd _ (dst0 + iw) (eval_add2_locals sd _ _ dst0 iw hdst hi) hs0
  have hd8_raw := store_const_zero_frame hG1 (memzeroWriteFrame_refl s1 (0, 0)) _ (dst0 + iw + 8)
    (eval_add3_locals s1 _ _ dst0 iw 8 hd1 hi1) hs8
  have hd16_raw := store_const_zero_frame hG2 (memzeroWriteFrame_refl s2 (0, 0)) _ (dst0 + iw + 16)
    (eval_add3_locals s2 _ _ dst0 iw 16 hd2 hi2) hs16
  have hd24_raw := store_const_zero_frame hG3 (memzeroWriteFrame_refl s3 (0, 0)) _ (dst0 + iw + 24)
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
  have hmwf1 : MemzeroWriteFrame s0 s1 (dst0.toNat, n0.toNat) := by
    rw [hs1_eq]; exact st0.2.2 ⟨by omega, by omega⟩
  have hmwf2 : MemzeroWriteFrame s0 s2 (dst0.toNat, n0.toNat) := by
    rw [hs2_eq]
    exact (store_const_zero_frame hG1 hmwf1 _ (dst0 + iw + 8)
      (eval_add3_locals s1 _ _ dst0 iw 8 hd1 hi1) hs8).2.2 ⟨by omega, by omega⟩
  have hmwf3 : MemzeroWriteFrame s0 s3 (dst0.toNat, n0.toNat) := by
    rw [hs3_eq]
    exact (store_const_zero_frame hG2 hmwf2 _ (dst0 + iw + 16)
      (eval_add3_locals s2 _ _ dst0 iw 16 hd2 hi2) hs16).2.2 ⟨by omega, by omega⟩
  have hmwf4 : MemzeroWriteFrame s0 s4 (dst0.toNat, n0.toNat) := by
    rw [hs4_eq]
    exact (store_const_zero_frame hG3 hmwf3 _ (dst0 + iw + 24)
      (eval_add3_locals s3 _ _ dst0 iw 24 hd3 hi3) hs24).2.2 ⟨by omega, by omega⟩
  change MemzeroFullInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1, heq2, heq3, heq4]
  exact assign_i_step hG4.code hG4 hmwf4 hd4 hn4 hi4 hle_ik hdlo hdhi

private theorem step_loop2 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemzeroFullInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemzeroFullInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hmwf, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hmwfd : MemzeroWriteFrame s0 sd (dst0.toNat, n0.toNat) := memzeroWriteFrame_locals_clock hmwf s.locals (s.clock - 1)
  have hnl := eval_notLower_true s n0 iw 8 w hn hi hcond hw
  obtain ⟨hs0, s1, hs1_eq, hG1, hd1, hn1, hi1, _, heq1⟩ :=
    seq_none_split sd _ _ hGd dst0 n0 iw hdst hn hi rfl rfl rfl hnone
  have st0 := store_const_zero_frame hGd hmwfd _ (dst0 + iw) (eval_add2_locals sd _ _ dst0 iw hdst hi) hs0
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom ⟨st0.1, st0.2.1⟩ (by decide) (by decide) hnl
  have hk8_val : (8 : BitVec 64).toNat = 8 := rfl
  have hmwf1 : MemzeroWriteFrame s0 s1 (dst0.toNat, n0.toNat) := by
    rw [hs1_eq]; exact st0.2.2 ⟨by omega, by omega⟩
  change MemzeroFullInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1]
  exact assign_i_step hG1.code hG1 hmwf1 hd1 hn1 hi1 hle_ik hdlo hdhi

private theorem step_loop3 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemzeroFullInv s0 dst0 n0 s)
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
      MemzeroFullInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hmwf, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hmwfd : MemzeroWriteFrame s0 sd (dst0.toNat, n0.toNat) := memzeroWriteFrame_locals_clock hmwf s.locals (s.clock - 1)
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
  have b0 := storeByte_const_zero_frame hGd hmwfd _ (dst0 + iw) (eval_add2_locals sd _ _ dst0 iw hdst hi) hs0
  have b7_raw := storeByte_const_zero_frame hG7 (memzeroWriteFrame_refl s7 (0, 0)) _ (dst0 + iw + 7)
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
  have hmwf1 : MemzeroWriteFrame s0 s1 (dst0.toNat, n0.toNat) := by rw [hs1_eq]; exact b0.2.2 ⟨by omega, by omega⟩
  have hmwf2 : MemzeroWriteFrame s0 s2 (dst0.toNat, n0.toNat) := by
    rw [hs2_eq]; exact (storeByte_const_zero_frame hG1 hmwf1 _ (dst0 + iw + 1) (eval_add3_locals s1 _ _ dst0 iw 1 hd1 hi1) hs1).2.2 ⟨by omega, by omega⟩
  have hmwf3 : MemzeroWriteFrame s0 s3 (dst0.toNat, n0.toNat) := by
    rw [hs3_eq]; exact (storeByte_const_zero_frame hG2 hmwf2 _ (dst0 + iw + 2) (eval_add3_locals s2 _ _ dst0 iw 2 hd2 hi2) hs2).2.2 ⟨by omega, by omega⟩
  have hmwf4 : MemzeroWriteFrame s0 s4 (dst0.toNat, n0.toNat) := by
    rw [hs4_eq]; exact (storeByte_const_zero_frame hG3 hmwf3 _ (dst0 + iw + 3) (eval_add3_locals s3 _ _ dst0 iw 3 hd3 hi3) hs3).2.2 ⟨by omega, by omega⟩
  have hmwf5 : MemzeroWriteFrame s0 s5 (dst0.toNat, n0.toNat) := by
    rw [hs5_eq]; exact (storeByte_const_zero_frame hG4 hmwf4 _ (dst0 + iw + 4) (eval_add3_locals s4 _ _ dst0 iw 4 hd4 hi4) hs4).2.2 ⟨by omega, by omega⟩
  have hmwf6 : MemzeroWriteFrame s0 s6 (dst0.toNat, n0.toNat) := by
    rw [hs6_eq]; exact (storeByte_const_zero_frame hG5 hmwf5 _ (dst0 + iw + 5) (eval_add3_locals s5 _ _ dst0 iw 5 hd5 hi5) hs5).2.2 ⟨by omega, by omega⟩
  have hmwf7 : MemzeroWriteFrame s0 s7 (dst0.toNat, n0.toNat) := by
    rw [hs7_eq]; exact (storeByte_const_zero_frame hG6 hmwf6 _ (dst0 + iw + 6) (eval_add3_locals s6 _ _ dst0 iw 6 hd6 hi6) hs6).2.2 ⟨by omega, by omega⟩
  have hmwf8 : MemzeroWriteFrame s0 s8 (dst0.toNat, n0.toNat) := by
    rw [hs8_eq]; exact (storeByte_const_zero_frame hG7 hmwf7 _ (dst0 + iw + 7) (eval_add3_locals s7 _ _ dst0 iw 7 hd7 hi7) hs7).2.2 ⟨by omega, by omega⟩
  change MemzeroFullInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8]
  exact assign_i_step hG8.code hG8 hmwf8 hd8 hn8 hi8 hle_ik hdlo hdhi

private theorem step_loop4 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemzeroFullInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      MemzeroFullInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, hmwf, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hmwfd : MemzeroWriteFrame s0 sd (dst0.toNat, n0.toNat) := memzeroWriteFrame_locals_clock hmwf s.locals (s.clock - 1)
  have hlt := eval_lower_true s n0 iw w hn hi hcond hw
  rw [BitVec.lt_def] at hlt
  obtain ⟨hs0, s1, hs1_eq, hG1, hd1, hn1, hi1, _, heq1⟩ :=
    seq_none_split sd _ _ hGd dst0 n0 iw hdst hn hi rfl rfl rfl hnone
  have b0 := storeByte_const_zero_frame hGd hmwfd _ (dst0 + iw) (eval_add2_locals sd _ _ dst0 iw hdst hi) hs0
  have hnlt := n0.isLt
  have ha1 : (iw + 1).toNat = iw.toNat + 1 :=
    BitVec.toNat_add_of_lt (by change iw.toNat + 1 < 2 ^ 64; omega)
  have hnl : ¬ (n0 < iw + 1) := by rw [BitVec.lt_def, ha1]; omega
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 1 hle hdom ⟨b0.1, b0.2.1⟩ (by decide) (by decide) hnl
  have hk1_val : (1 : BitVec 64).toNat = 1 := rfl
  have hmwf1 : MemzeroWriteFrame s0 s1 (dst0.toNat, n0.toNat) := by rw [hs1_eq]; exact b0.2.2 ⟨by omega, by omega⟩
  change MemzeroFullInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1]
  exact assign_i_step hG1.code hG1 hmwf1 hd1 hn1 hi1 hle_ik hdlo hdhi

private theorem setVar_lookup_ne {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : MlS)
    (v : ValueHOL 64) (h : b ≠ a) :
    (setVarHOLFinite a v s).locals.lookup b = s.locals.lookup b := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h]

/-- Reusable body-level write-frame lemma for `memzero` from any `GuestInv` entry state. -/
theorem memzero_body_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memzero)).1) :
    MemzeroWriteFrame s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memzero)).2
      (locN s "dst", locN s "n") := by
  revert hres
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
              · simp [hd, List.all, valueIsWord] at hcond
              · simp [hd, List.all, valueIsWord] at hcond
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
          have hinv1 : MemzeroFullInv s dst0 n0 s1 := by
            refine ⟨hcode, guestInv_setVar _ _ s hG,
              memzeroWriteFrame_locals_clock (memzeroWriteFrame_refl s _) _ s.clock, ?_, ?_, 0, ?_,
              Nat.zero_le _, fun h => by simp at h⟩
            · rw [hs1, setVar_lookup_ne s (ofString "i") (ofString "dst") _ (by decide), hdst0]
            · rw [hs1, setVar_lookup_ne s (ofString "i") (ofString "n") _ (by decide), hn0]
            · simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hinv2 : MemzeroFullInv s dst0 n0 s2 := by
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
          have hinv3 : MemzeroFullInv s dst0 n0 s3 :=
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
            have hinv4 : MemzeroFullInv s dst0 n0 s4 :=
              while_preserve_full _ _ rfl rfl step_loop4 s3.clock s3 s4 le_rfl hinv3 hw4
            have hret_eval : evaluateHOLFiniteState s4 (.return (.const 0#64)) =
                (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite s4) := by
              simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact,
                sizeOfShapeWithContextHOL]
            rw [hret_eval]
            dsimp only
            intro _
            rw [← hdst0_eq, ← hn0_eq]
            exact memzeroWriteFrame_locals_clock hinv4.2.2.1 _ s4.clock
    · intro h; exact absurd h not_resumes_error

/-- `memzero` (AST line 251): writes its parameter extent (`ArenaReady` tier, at `execute_block`). -/
theorem «ww_memzero» :
    WritesWithin (fun s => [(locN s "dst", locN s "n")])
    [] (ofString "memzero") := by
  refine ⟨_, _, _, lookup_memzero, ?_⟩
  intro F s hcode hAR _ _ hres
  obtain ⟨hG, hA⟩ := hAR
  have hmwf := memzero_body_frame s hcode hG hres
  obtain ⟨hc, hm, hsh, hba, _, hg, _, _, hfr, _⟩ := hmwf
  set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memzero)).2
  have hG_post : GuestInv post := guestInv_congr hc hm hsh hba hG
  have hglob_eq : ∀ nm : String, globN post nm = globN s nm := fun nm => by
    unfold globN; rw [hg]
  have hA_post : ArenaOK post := arenaOK_congr hg hA
  refine ⟨⟨hG_post, hA_post⟩, ?_, ?_, ?_, ?_⟩
  · rw [hglob_eq]
  · rw [hglob_eq]
  · intro a hkeep _
    exact hfr a
      (fun i hi => hkeep i (List.mem_append.2 (Or.inl hi)))
      (fun hc0 => by unfold CellHits at hc0; omega)
  · intro name _
    rw [hg]

end InitECandidate.Solver.Wave8Contracts.M28
