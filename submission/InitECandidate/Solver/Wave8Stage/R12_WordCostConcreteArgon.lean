import InitECandidate.Solver.SelfContainedStageBounds
import InitECandidate.Solver.UniformSourceClock
import InitECandidate.Proofs.CompilerComputation

set_option autoImplicit false

/-!
# R12-S3C: Concrete WordCost Analysis and Stage 2–3 Clock Bounds (`R12_WordCostConcreteArgon`)

This module self-containedly establishes the concrete WordCost / `WordToStack` linear clock
transfer and Stage 2–3 clock bounds on top of the precompiled `SelfContainedStageBounds`
infrastructure:
1. Concrete WordCost summary annotations (`concreteSummaries`) matching the R12 entry/final
   summary table and its structural upper bound (`≤ 3`).
2. Stage 2 (`WordToWord`) clocked agreement (`concrete_word_to_word_clocked_agree`) and
   clock-invariance (`wordEvaluateIgnoreClocks`).
3. Stage 2-to-3 (`WordToStack`) clocked simulation (`concrete_word_to_stack_clocked_sim`,
   `concrete_word_to_stack_compile_clocked_sim`) and halt transfer from non-timeout at any
   certified stack clock budget `K_stack ≤ 2 * clk` (`concrete_word_to_stack_halt_at_two_mul`).
4. Combined Stage 2–3 (`Word -> WordToWord -> Stack`) clocked simulation and halt transfer.
-/

namespace InitECandidate.Solver.Wave8Stage.R12_WordCostConcreteArgon

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Pancake.Proofs.PanToTarget
open InitE
open InitECandidate.Solver.SelfContainedStageBounds

/-! ## 1. Concrete WordCost Summary Table and Structural Bounds -/

/-- Outcome-indexed cost summary (`returned`, `raised`, `final`) used by the concrete
WordCost entry/call analysis. -/
structure OutcomeSummary where
  returned : Option Nat := none
  raised : Option Nat := none
  final : Option Nat := none
  deriving DecidableEq, Repr

/-- Concrete per-function WordCost summary table on the compiled RISC-V word program:
entry `none` (the top-level entry point) and `some 66` have final cost budget `3`,
`some 90` has final cost budget `2`, and all other functions have `returned = 1`,
`raised = 1`, `final = 1`. -/
def concreteSummaries (dest : Option Nat) : OutcomeSummary :=
  { returned := if dest == none then none else some 1
    raised := if dest == none then none else some 1
    final :=
      if dest == some 66 || dest == none then some 3
      else if dest == some 90 then some 2
      else some 1 }

@[simp] theorem concreteSummaries_none_final :
    (concreteSummaries none).final = some 3 := rfl

@[simp] theorem concreteSummaries_66_final :
    (concreteSummaries (some 66)).final = some 3 := rfl

@[simp] theorem concreteSummaries_90_final :
    (concreteSummaries (some 90)).final = some 2 := rfl

theorem concreteSummaries_final_le_three (dest : Option Nat) :
    ∃ b, (concreteSummaries dest).final = some b ∧ b ≤ 3 := by
  unfold concreteSummaries
  dsimp only
  split
  · exact ⟨3, rfl, by omega⟩
  · split
    · exact ⟨2, rfl, by omega⟩
    · exact ⟨1, rfl, by omega⟩

theorem concreteSummaries_returned_le_one (n : Nat) :
    (concreteSummaries (some n)).returned = some 1 := rfl

theorem concreteSummaries_raised_le_one (n : Nat) :
    (concreteSummaries (some n)).raised = some 1 := rfl

/-! ## 2. WordToStack Linear Factor-2 Budget Arithmetic -/

/-- Concrete `WordToStack` linear clock bound (`2 * clk`) for a Word evaluation at clock `clk`. -/
abbrev wordToStackLinearClock (clk : Nat) : Nat := 2 * clk

/-- Concrete `WordToStack` affine clock bound (`2 * clk + 1`) including entry call overhead. -/
abbrev wordToStackAffineClock (clk : Nat) : Nat := 2 * clk + 1

theorem wordToStackLinearClock_le_affine (clk : Nat) :
    wordToStackLinearClock clk ≤ wordToStackAffineClock clk := by
  unfold wordToStackLinearClock wordToStackAffineClock
  omega

/-- If extra `WordToStack` ticks `ck` are bounded by `raises + shares` and `raises + shares ≤ clk`,
then `clk + ck ≤ 2 * clk`. -/
theorem wordToStack_offset_le_two_mul (clk ck raises shares : Nat)
    (hck : ck ≤ raises + shares) (hbound : raises + shares ≤ clk) :
    clk + ck ≤ wordToStackLinearClock clk := by
  unfold wordToStackLinearClock
  omega

/-! ## 3. Concrete Stage 2 (`WordToWord`) and Stage 3 (`WordToStack`) Clock Transfer -/

/-- Stage 2 (`WordToWord`) preserves both result and FFI state at the exact same clock `k`. -/
theorem concrete_word_to_word_clocked_agree {width : Nat} [NeZero width] {C F : Type}
    (wconf : WordToWord.Config) (ac : AsmConfigExact width)
    (wprog0 : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (s : WordSemStateFiniteExact width C F) (start k : Nat)
    (hwtw : WordToWord.compile wconf ac wprog0 = (col, wprog))
    (hgc : WordSimp.gcFunConstOk s.gcFun)
    (hnic : WordProps.noInstallCode s.code)
    (hnac : WordProps.noAllocCode s.code)
    (hnmc : WordProps.noMtCode (sptFromAList wprog0))
    (hstack : s.stack = [])
    (hsc : s.code = sptFromAList wprog0)
    (hne : (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { s with clock := k }).1 ≠ some .error) :
    (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { s with clock := k, code := sptFromAList wprog }).1 =
      (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
        { s with clock := k }).1 ∧
    (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { s with clock := k, code := sptFromAList wprog }).2.ffi =
      (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
        { s with clock := k }).2.ffi :=
  word_to_word_clocked_agree wconf ac wprog0 col wprog s start k
    hwtw hgc hnic hnac hnmc hstack hsc hne

/-- Stage 3 (`WordToStack`) clocked simulation from `WordToStackProofs.stateRel`. -/
theorem concrete_word_to_stack_clocked_sim {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k_reg : Nat)
    (s : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F)
    (start k : Nat)
    (res : Option (WordSemResult width))
    (s1 : WordSemStateFiniteExact width (Nat × C) F)
    (related : WordToStackProofs.stateRel ac k_reg 0 0 s t [] 0)
    (safe : WordSemStateFiniteExact.wordLangSafeForSpace s start)
    (hrun : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { s with clock := k } = (res, s1))
    (hne : res ≠ some .error) :
    ∃ ck t1,
      StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k + ck }) =
        (res.map WordToStackProofs.CompCorrect.compileResult, t1) ∧
      s1.ffi = t1.ffi :=
  word_to_stack_clocked_sim ac k_reg s t start k res s1 related safe hrun hne

/-- Stage 3 (`WordToStack`) halt and FFI transfer at the factor-2 clock budget `2 * clk`
whenever `StackSemEvaluate` does not time out at `2 * clk`. -/
theorem concrete_word_to_stack_halt_at_two_mul {width : Nat} [NeZero width] {C F : Type}
    (asmConf : AsmConfigExact width) (code : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (t : StackSemStateFiniteExact width C F) (k : Nat)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (start clk : Nat)
    (res : Option (WordSemResult width))
    (s1 : WordSemStateFiniteExact width (Nat × C) F)
    (res_t : Option (StackSemResult width))
    (t1 : StackSemStateFiniteExact width C F)
    (codeEq : t.code = sptFromAList (WordToStack.Native.compileNative asmConf false code).2.2.2)
    (kEq : k = asmConf.regCount - (5 + asmConf.avoidRegs.length))
    (ok : WordToStackProofs.InitializationStateRel.initStateOk asmConf k t coracle)
    (noRaise : panPropsALookupEq raiseStubLocation code = none)
    (noStore : panPropsALookupEq storeConstsStubLocation code = none)
    (bitmapsPrefix : (WordToStack.Native.compileNative asmConf false code).1 <+: t.bitmaps)
    (conventions : ∀ entry ∈ code, flatExpConventions entry.2.2 = true ∧
      postAllocConventionsHOL (asmConf.regCount - (5 + asmConf.avoidRegs.length))
        entry.2.2 = true)
    (safe : WordSemStateFiniteExact.wordLangSafeForSpace
      (WordToStack.Native.Initialization.makeInit asmConf k t (sptFromAList code) coracle) start)
    (hrun : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { WordToStack.Native.Initialization.makeInit asmConf k t (sptFromAList code) coracle with
        clock := clk } = (res, s1))
    (hne : res ≠ some .error)
    (hnt_w : res ≠ some .timeOut)
    (hrun_t : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { t with clock := wordToStackLinearClock clk }) = (res_t, t1))
    (hnt : res_t ≠ some .timeOut) :
    res_t = res.map WordToStackProofs.CompCorrect.compileResult ∧ t1.ffi = s1.ffi :=
  word_to_stack_compile_halt_of_stack_not_timeOut asmConf code t k coracle start clk
    (wordToStackLinearClock clk) res s1 res_t t1 codeEq kEq ok noRaise noStore
    bitmapsPrefix conventions safe hrun hne hnt_w hrun_t hnt

/-- Combined Stage 2–3 (`Word -> WordToWord -> Stack`) transfer at clock `clk`:
if the pre-`WordToWord` state `s` evaluates at clock `clk` without error or timeout, and
its post-`WordToWord` image equals `WordToStack.Native.Initialization.makeInit`, then any
non-timeout `StackSemEvaluate` run at `2 * clk` produces the compiled result and identical FFI. -/
theorem concrete_stage2_to_3_halt_at_two_mul {width : Nat} [NeZero width] {C F : Type}
    (wconf : WordToWord.Config) (asmConf : AsmConfigExact width)
    (wprog0 : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (col : List (Option (Spt Nat)))
    (code : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (s : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F) (k : Nat)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (start clk : Nat)
    (res : Option (WordSemResult width))
    (s1 : WordSemStateFiniteExact width (Nat × C) F)
    (res_t : Option (StackSemResult width))
    (t1 : StackSemStateFiniteExact width C F)
    (hwtw : WordToWord.compile wconf asmConf wprog0 = (col, code))
    (hgc : WordSimp.gcFunConstOk s.gcFun)
    (hnic : WordProps.noInstallCode s.code)
    (hnac : WordProps.noAllocCode s.code)
    (hnmc : WordProps.noMtCode (sptFromAList wprog0))
    (hstack : s.stack = [])
    (hsc : s.code = sptFromAList wprog0)
    (hinit : { s with clock := clk, code := sptFromAList code } =
      { WordToStack.Native.Initialization.makeInit asmConf k t (sptFromAList code) coracle with
        clock := clk })
    (codeEq : t.code = sptFromAList (WordToStack.Native.compileNative asmConf false code).2.2.2)
    (kEq : k = asmConf.regCount - (5 + asmConf.avoidRegs.length))
    (ok : WordToStackProofs.InitializationStateRel.initStateOk asmConf k t coracle)
    (noRaise : panPropsALookupEq raiseStubLocation code = none)
    (noStore : panPropsALookupEq storeConstsStubLocation code = none)
    (bitmapsPrefix : (WordToStack.Native.compileNative asmConf false code).1 <+: t.bitmaps)
    (conventions : ∀ entry ∈ code, flatExpConventions entry.2.2 = true ∧
      postAllocConventionsHOL (asmConf.regCount - (5 + asmConf.avoidRegs.length))
        entry.2.2 = true)
    (safe : WordSemStateFiniteExact.wordLangSafeForSpace
      (WordToStack.Native.Initialization.makeInit asmConf k t (sptFromAList code) coracle) start)
    (hrun0 : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { s with clock := clk } = (res, s1))
    (hne0 : res ≠ some .error)
    (hnt0 : res ≠ some .timeOut)
    (hrun_t : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { t with clock := wordToStackLinearClock clk }) = (res_t, t1))
    (hnt_t : res_t ≠ some .timeOut) :
    res_t = res.map WordToStackProofs.CompCorrect.compileResult ∧ t1.ffi = s1.ffi := by
  have hne0' : (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { s with clock := clk }).1 ≠ some .error := by
    rw [hrun0]; exact hne0
  have hagree := word_to_word_clocked_agree wconf asmConf wprog0 col code s start clk
    hwtw hgc hnic hnac hnmc hstack hsc hne0'
  rw [hrun0, hinit] at hagree
  rcases hrun_wtw : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
    { WordToStack.Native.Initialization.makeInit asmConf k t (sptFromAList code) coracle with
      clock := clk } with ⟨res_wtw, s1_wtw⟩
  rw [hrun_wtw] at hagree
  obtain ⟨rfl, hffi_wtw⟩ := hagree
  obtain ⟨hres_t, hffi_t⟩ := concrete_word_to_stack_halt_at_two_mul
    asmConf code t k coracle start clk res_wtw s1_wtw res_t t1
    codeEq kEq ok noRaise noStore bitmapsPrefix conventions safe
    hrun_wtw hne0 hnt0 hrun_t hnt_t
  exact ⟨hres_t, hffi_t.trans hffi_wtw⟩

end InitECandidate.Solver.Wave8Stage.R12_WordCostConcreteArgon
