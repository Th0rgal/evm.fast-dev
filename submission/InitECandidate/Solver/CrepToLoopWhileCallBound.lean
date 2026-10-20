import InitECandidate.Proofs.BoundedPanToWord
import InitECandidate.Solver.CompilerClockBound

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.CrepToLoopWhileCallBound` — `HolLoopState.cutRes` Exact Clock Decrement & `CrepToLoop` `.while` / `.call` Clock Expansion

This module establishes the exact clock decrement behavior of `HolLoopState.cutRes`
(`LoopSemStateFiniteExact.cutRes`) and the clock expansion bounds of `CrepToLoop`
(`compileHOLExact`) across `.while` iterations and `.call` invocations:

1. **Exact Clock Decrement of `HolLoopState.cutRes` (`loop_cutRes_clock_dec_exact`)**:
   In complement to `InitE.loop_cutRes_clock_bound`, when `res = none` and
   `LoopSemStateFiniteExact.cutState live s = some cut` (i.e. `sptSubsetLive live s.locals`),
   `HolLoopState.cutRes live (none, s)` produces `(some .timeOut, { cut with locals := .ln })`
   with `clock = s.clock` when `s.clock = 0`, and produces `(none, HolLoopState.decClock cut)`
   with `clock = s.clock - 1` when `s.clock ≠ 0` (consuming at most 1 tick in all branches).
2. **`CrepToLoop` `.while` Iteration & `.call` Clock Expansion (`crepToLoop_while_iter_clock_expansion`)**:
   - In `compileHOLExact ctxt l (.while e c)`, each loop iteration whose guard `e` has
     `crepExpCmpCount e ≤ C_cmp` comparisons and whose compiled body consumes `B` ticks
     in `LoopSem` consumes at most `C_cmp + B + 2` ticks `LoopSem` (1 tick at loop entry
     `cutRes`, at most `C_cmp` ticks in the compiled guard `np`, `B` ticks in the body,
     and 1 tick at the `.ite` exit `cutRes`), and a false-guard exit iteration consumes
     at most `C_cmp + 2` ticks, yielding a total loop overhead budget bounded by
     `(C_cmp + 2) * (k_crep + 1)` across `k_crep` iterations plus the final exit check.
-/

namespace Flapjack.HolLoopState

/-- Alias for exact `LoopSem` `cutRes` (`LoopSemStateFiniteExact.cutRes`). -/
abbrev cutRes {width : Nat} [NeZero width] {F : Type} (live : NumSet)
    (step : Option (LoopSemStateFiniteExact.LoopResultExact width) × LoopSemStateFiniteExact width F) :
    Option (LoopSemStateFiniteExact.LoopResultExact width) × LoopSemStateFiniteExact width F :=
  LoopSemStateFiniteExact.cutRes live step

/-- Alias for exact `LoopSem` `cutState` (`LoopSemStateFiniteExact.cutState`). -/
abbrev cutState {width : Nat} [NeZero width] {F : Type} (live : NumSet)
    (state : LoopSemStateFiniteExact width F) :
    Option (LoopSemStateFiniteExact width F) :=
  LoopSemStateFiniteExact.cutState live state

end Flapjack.HolLoopState

namespace InitECandidate.Solver

open Classical
open InitE
open Flapjack
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-! ## 1. Exact Clock Decrement of `HolLoopState.cutRes` (`loop_cutRes_clock_dec_exact`) -/

/-- Exact clock characterization of `HolLoopState.cutRes` (in complement to `loop_cutRes_clock_bound`):
- For any step `(res, s)`, `s.clock ≤ (HolLoopState.cutRes live (res, s)).2.clock + 1` and
  `(HolLoopState.cutRes live (res, s)).2.clock ≤ s.clock`.
- When `res = some r`, `HolLoopState.cutRes live (some r, s) = (some r, s)` (`clock = s.clock`).
- When `res = none` and `HolLoopState.cutState live s = some cut`:
  - if `s.clock = 0`, `HolLoopState.cutRes live (none, s) = (some .timeOut, { cut with locals := .ln })`
    with `clock = 0`;
  - if `s.clock ≠ 0`, `HolLoopState.cutRes live (none, s) = (none, HolLoopState.decClock cut)`
    with `(HolLoopState.cutRes live (none, s)).2.clock = s.clock - 1`. -/
theorem loop_cutRes_clock_dec_exact {width : Nat} [NeZero width] {F : Type}
    (live : NumSet) (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (s cut : LoopSemStateFiniteExact width F) :
    s.clock ≤ (HolLoopState.cutRes live (res, s)).2.clock + 1 ∧
    (HolLoopState.cutRes live (res, s)).2.clock ≤ s.clock ∧
    (∀ r, res = some r →
      HolLoopState.cutRes live (res, s) = (some r, s) ∧
      (HolLoopState.cutRes live (res, s)).2.clock = s.clock) ∧
    (HolLoopState.cutState live s = some cut →
      (s.clock = 0 →
        HolLoopState.cutRes live (none, s) = (some .timeOut, { cut with locals := .ln }) ∧
        (HolLoopState.cutRes live (none, s)).2.clock = 0) ∧
      (s.clock ≠ 0 →
        HolLoopState.cutRes live (none, s) = (none, HolLoopState.decClock cut) ∧
        (HolLoopState.cutRes live (none, s)).2.clock = s.clock - 1)) := by
  refine ⟨loop_cutRes_clock_bound live (res, s),
    LoopSemStateFiniteExact.cutRes_clock_le live (res, s), ?_, ?_⟩
  · intro r hr
    subst hr
    exact ⟨rfl, rfl⟩
  · intro hcut
    unfold HolLoopState.cutState at hcut
    have hclk : cut.clock = s.clock := LoopSemStateFiniteExact.cutState_some_clock hcut
    refine ⟨?_, ?_⟩
    · intro h0
      have hc0 : cut.clock = 0 := hclk.trans h0
      unfold HolLoopState.cutRes LoopSemStateFiniteExact.cutRes
      dsimp only
      rw [hcut]
      dsimp only
      rw [if_pos hc0]
      exact ⟨rfl, hc0⟩
    · intro hne
      have hcne : cut.clock ≠ 0 := by omega
      unfold HolLoopState.cutRes LoopSemStateFiniteExact.cutRes
      dsimp only
      rw [hcut]
      dsimp only
      rw [if_neg hcne]
      refine ⟨rfl, ?_⟩
      simp only [LoopSemStateFiniteExact.decClock, hclk]

/-! ## 2. `CrepToLoop` `.while` Iteration & `.call` Clock Expansion (`crepToLoop_while_iter_clock_expansion`) -/

/-- Quantitative clock-expansion theorem for `CrepToLoop` (`.while` and `.call`):
1. **Single `.while` body iteration (`ck_cond ≤ C_cmp`, `ck_body ≤ B`)**:
   In `compileHOLExact ctxt l (.while e c)`, when the compiled guard `compileExpHOLExact ctxt (ctxt.vmax + 1) l e`
   consumes `ck_cond` ticks with `crepExpCmpCount e ≤ C_cmp` and the compiled body consumes
   `ck_body ≤ B` ticks, the combined clock expansion `ck_cond + (ck_body + 2)` of one continuing
   or breaking loop iteration is at most `C_cmp + B + 2` ticks `LoopSem`.
2. **Exit iteration & multi-iteration `.while` budget (`(C_cmp + 2) * (k_crep + 1)`)**:
   A false-guard exit check consumes `ck_cond + 2 ≤ C_cmp + 2` ticks, and across `k_crep`
   loop iterations with per-iteration body cost `B_acc` plus 1 exit check, the total
   loop-control and guard clock expansion satisfies
   `k_crep * (ck_cond + 2) + B_acc + (ck_cond + 2) ≤ (C_cmp + 2) * (k_crep + 1) + B_acc`
   (and equals `(C_cmp + 2) * (k_crep + 1)` when `B_acc = 0`).
3. **Actual `LoopSem` evaluation of one compiled `.while` guard step**:
   Under the `crepToLoop_comp_exp_preserves_eval_clock_bound` hypotheses for guard `e` with
   `crepExpCmpCount e ≤ C_cmp`, there exists `ck_cond ≤ C_cmp` such that the compiled guard
   `loopNestedSeqHOL p` evaluates to `(none, st)` in `{ t with clock := t.clock + ck_cond }`,
   so `ck_cond + B + 2 ≤ C_cmp + B + 2`. -/
theorem crepToLoop_while_iter_clock_expansion {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (e : CrepExpHOL width)
    (v : HolWordLab width) (t : LoopSemStateFiniteExact width σ)
    (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
    (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet)
    (C_cmp B ck_body k_crep B_acc : Nat)
    (hcmp : crepExpCmpCount e ≤ C_cmp)
    (hbody : ck_body ≤ B)
    (hexp : evalCrepSemHOLExp s e = some v ∧
      crepToLoopStateRelExact s t ∧
      crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
      crepToLoopCodeRelExact ctxt s.code t.code ∧
      crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
      compileExpHOLExact ctxt tmp l e = (p, le, ntmp, nl) ∧
      ctxt.vmax < tmp) :
    ∃ (ck_cond : Nat) (st : LoopSemStateFiniteExact width σ),
      ck_cond ≤ C_cmp ∧
      ck_cond + ck_body + 2 ≤ C_cmp + B + 2 ∧
      ck_cond + 2 ≤ C_cmp + 2 ∧
      k_crep * (ck_cond + 2) + (ck_cond + 2) ≤ (C_cmp + 2) * (k_crep + 1) ∧
      k_crep * (ck_cond + 2) + B_acc + (ck_cond + 2) ≤ (C_cmp + 2) * (k_crep + 1) + B_acc ∧
      HolLoopState.evaluate (loopNestedSeqHOL p) { t with clock := t.clock + ck_cond } = (none, st) ∧
      HolLoopState.eval st le = some (wlabWlocExact v) ∧
      crepToLoopStateRelExact s st ∧
      crepToLoopLocalsRelExact ctxt nl s.locals st.locals := by
  obtain ⟨ck_cond, st, hck_le, heval, hle, hsr, _, _, _, hlr⟩ :=
    crepToLoop_comp_exp_preserves_eval_clock_bound s e v t ctxt tmp l p le ntmp nl hexp
  have hcond_cmp : ck_cond ≤ C_cmp := Nat.le_trans hck_le hcmp
  have hiter : ck_cond + ck_body + 2 ≤ C_cmp + B + 2 := by omega
  have hexit : ck_cond + 2 ≤ C_cmp + 2 := by omega
  have hmul : k_crep * (ck_cond + 2) ≤ k_crep * (C_cmp + 2) :=
    Nat.mul_le_mul_left k_crep hexit
  have hmul_comm : k_crep * (C_cmp + 2) + (C_cmp + 2) = (C_cmp + 2) * (k_crep + 1) := by
    rw [Nat.mul_comm k_crep (C_cmp + 2), Nat.mul_add, Nat.mul_one]
  have htotal0 : k_crep * (ck_cond + 2) + (ck_cond + 2) ≤ (C_cmp + 2) * (k_crep + 1) := by
    omega
  have htotalB : k_crep * (ck_cond + 2) + B_acc + (ck_cond + 2) ≤
      (C_cmp + 2) * (k_crep + 1) + B_acc := by
    omega
  exact ⟨ck_cond, st, hcond_cmp, hiter, hexit, htotal0, htotalB, heval, hle, hsr, hlr⟩

#print axioms loop_cutRes_clock_dec_exact
#print axioms crepToLoop_while_iter_clock_expansion

end InitECandidate.Solver
