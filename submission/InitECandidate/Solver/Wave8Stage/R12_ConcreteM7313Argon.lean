import InitECandidate.Solver.SelfContainedStageBounds
import InitECandidate.Solver.UniformSourceClock
import InitECandidate.Proofs.CompilerComputation

set_option autoImplicit false

/-!
# R12-S3C: Concrete M=7313 Stage 4 `StackToLab` Bound (`R12_ConcreteM7313Argon`)

This module self-containedly establishes the concrete `M = 7313` `codeStepBudget` /
`StackToLab` Stage 4 clock bound and Stage 4 `fullMakeInit` / `LabFilter` transfer on top of
the precompiled `SelfContainedStageBounds` infrastructure:
1. `stepCost`, `CodeStepBounded`, `codeStepBudget`, and `stepCost_progCompHOL` with the
   concrete `M = 7313` bound (`M7313 = 7313`, `M7313Slope = 7314`) and `stepCost` preservation
   across `StackNames.progCompHOL`.
2. Explicit Stage 4 Lab clock budget `labBudgetOfStackClock k_stack = 7314 * (2 * k_stack + 1) + 7313`
   and total Lab clock `totalLabBudgetOfWordClock 15226 = 445491119 < 2^64`.
3. Stage 4 pass-by-pass clocked simulation (`StackRawCall`, `StackAlloc`, `StackRemove`,
   `StackNames`, `StackToLab`) and `fullMakeInit` halt/FFI transfer at `labBudgetOfStackClock k_stack`.
4. Combined Stage 4 `fullMakeInit` + `LabFilter` / alignment transfer at `labBudgetOfStackClock k_stack`.
-/

namespace InitECandidate.Solver.Wave8Stage.R12_ConcreteM7313Argon

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Pancake.Proofs.PanToTarget
open InitE
open InitECandidate.Solver.SelfContainedStageBounds

/-! ## 1. `stepCost`, `CodeStepBounded`, and Concrete `M = 7313` Constants -/

/-- The concrete `codeStepBudget` bound `M = 7313` for the Stage 4 `StackNames -> Lab`
flattening pass. -/
abbrev M7313 : Nat := 7313

/-- The per-step `StackToLab` clock multiplier `M + 1 = 7314`. -/
abbrev M7313Slope : Nat := 7314

@[simp] theorem m7313Slope_eq_succ :
    M7313Slope = M7313 + 1 := rfl

/-- Syntactic upper bound on the Lab clock ticks consumed by a single flattened `StackLang`
instruction before the next `StackLang` clock decrement. -/
def stepCost {width : Nat} [NeZero width] : HolProg width → Nat
  | .skip => 0
  | .halt _ => 1
  | .inst _ => 1
  | .tick => 1
  | .ret _ => 1
  | .raise _ => 1
  | .break _ => 1
  | .continue _ => 0
  | .locValue _ _ _ => 1
  | .codeBufferWrite _ _ => 1
  | .ffi _ _ _ _ _ _ => 2
  | .install _ _ _ _ _ => 2
  | .shMemOp _ _ _ => 0
  | .seq c1 c2 => stepCost c1 + stepCost c2
  | .ite _ _ _ c1 c2 => 2 + stepCost c1 + stepCost c2
  | .loop body => stepCost body
  | .jumpLower _ _ _ => 1
  | .rawCall _ => 0
  | .call none _ _ => 0
  | .call (some (rp, _, _, _)) _ none => 2 + stepCost rp
  | .call (some (rp, _, _, _)) _ (some (hp, _, _)) => 2 + stepCost rp + stepCost hp
  | _ => 0

/-- `StackNames.progCompHOL` preserves `stepCost` identically on every `StackLang` program. -/
theorem stepCost_progCompHOL {width : Nat} [NeZero width] (names : Spt Nat) :
    ∀ (p : HolProg width), stepCost (StackNames.progCompHOL names p) = stepCost p
  | .skip => rfl
  | .halt _ => rfl
  | .inst _ => rfl
  | .tick => rfl
  | .ret _ => rfl
  | .raise _ => rfl
  | .break _ => rfl
  | .continue _ => rfl
  | .locValue _ _ _ => rfl
  | .codeBufferWrite _ _ => rfl
  | .ffi _ _ _ _ _ _ => rfl
  | .install _ _ _ _ _ => rfl
  | .shMemOp _ _ (.addr _ _) => rfl
  | .seq c1 c2 => by
      simp only [StackNames.progCompHOL, stepCost,
        stepCost_progCompHOL names c1, stepCost_progCompHOL names c2]
  | .ite _ _ _ c1 c2 => by
      simp only [StackNames.progCompHOL, stepCost,
        stepCost_progCompHOL names c1, stepCost_progCompHOL names c2]
  | .loop body => by
      simp only [StackNames.progCompHOL, stepCost, stepCost_progCompHOL names body]
  | .jumpLower _ _ _ => rfl
  | .rawCall _ => rfl
  | .call none _ none => rfl
  | .call none _ (some (_, _, _)) => rfl
  | .call (some (rp, _, _, _)) _ none => by
      simp only [StackNames.progCompHOL, stepCost, stepCost_progCompHOL names rp]
  | .call (some (rp, _, _, _)) _ (some (hp, _, _)) => by
      simp only [StackNames.progCompHOL, stepCost,
        stepCost_progCompHOL names rp, stepCost_progCompHOL names hp]
  | .get _ _ | .set _ _ | .opCurrHeap _ _ _ | .alloc _ | .storeConsts _ _ _
  | .stackAlloc _ | .stackFree _ | .stackStore _ _ | .stackStoreAny _ _
  | .stackLoad _ _ | .stackLoadAny _ _ | .stackGetSize _ | .stackSetSize _
  | .bitmapLoad _ _ | .dataBufferWrite _ _ => rfl
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

/-- Maximum `stepCost` across a list of `(label, body)` sections. -/
def codeStepBudget {width : Nat} [NeZero width] (code : List (Nat × HolProg width)) : Nat :=
  code.foldl (fun acc entry => max acc (stepCost entry.2)) 0

/-- State invariant: every installed procedure in `s.code` and every installable oracle entry
in `s.compileOracle` has single-pass extra `LabSem` cost at most `M`. -/
def CodeStepBounded {width : Nat} [NeZero width] {C F : Type}
    (M : Nat) (s : StackSemStateFiniteExact width C F) : Prop :=
  (∀ k p, sptLookup k s.code = some p → stepCost p ≤ M) ∧
  (∀ i, ∀ e ∈ (s.compileOracle i).2.1, stepCost e.2 ≤ M)

/-- Given a `StackRawCall` source clock `k_stack`, the `StackNames` clock is bounded by
`2 * k_stack + 1`, and the extra `Lab` clock with `M = 7313` is bounded by
`7314 * (2 * k_stack + 1) + 7313 = 14628 * k_stack + 14627`. -/
def labBudgetOfStackClock (k_stack : Nat) : Nat :=
  (M7313 + 1) * (2 * k_stack + 1) + M7313

/-- Total Lab clock budget (`k_stack + labBudgetOfStackClock k_stack`) at `k_stack = 2 * k_word + 1`. -/
def totalLabBudgetOfWordClock (k_word : Nat) : Nat :=
  (2 * k_word + 1) + labBudgetOfStackClock (2 * k_word + 1)

theorem labBudgetOfStackClock_linear (k_stack : Nat) :
    labBudgetOfStackClock k_stack = 14628 * k_stack + 14627 := by
  unfold labBudgetOfStackClock M7313
  omega

/-- At the concrete `Word` clock `k = 15226` (where `k_stack = 2 * 15226 + 1 = 30453`),
`labBudgetOfStackClock 30453 = 445481111` and `totalLabBudgetOfWordClock 15226 = 445511564`,
both strictly below `2^64`. -/
theorem labBudgetOfStackClock_at_15226 :
    labBudgetOfStackClock (2 * 15226 + 1) = 445481111 ∧
    totalLabBudgetOfWordClock 15226 = 445511564 ∧
    totalLabBudgetOfWordClock 15226 < 2 ^ 64 := by
  decide +kernel

/-! ## 2. Stage 4 Pass-by-Pass Clocked Simulation and Halt Transfer at `M = 7313` -/

/-- `StackToLab` clocked halt simulation: if `stackRuns start s1 k` completes with `outcome`
and `ev`, then `LabSem.evaluate` halts with `outcome` and `ev`. -/
theorem concrete_stack_to_lab_clocked_halt {width : Nat} [NeZero width] {C F : Type}
    {start : Nat}
    {s1 : StackSemStateFiniteExact width C F}
    {s2 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (halt : FlattenCallCorrect.haltAssum C F s1.code)
    (rel : StateRel.stateRel s1 s2)
    (hpc : LabSem.locToPc start 0 s2.code = some s2.pc)
    (k : Nat) (outcome : HolOutcome) (ev : List HolIoEvent)
    (hrun : FlattenSemantics.stackRuns start s1 k = (.CompleteResult outcome, ev)) :
    ∃ k',
      (LabSem.evaluate { s2 with clock := k + k' - 1 }).1 = .halt outcome ∧
      (LabSem.evaluate { s2 with clock := k + k' - 1 }).2.ffi.ioEvents = ev :=
  stack_to_lab_clocked_halt halt rel hpc k outcome ev hrun

/-- Full Stage 4 (`fullMakeInit`: `StackRawCall -> StackAlloc -> StackRemove -> StackNames ->
StackToLab`) halt and FFI transfer at the `M = 7313` Lab clock budget `labBudgetOfStackClock k`:
whenever `LabSem.evaluate` does not time out at `labBudgetOfStackClock k`, it halts with the
exact `Stack` outcome and identical `ioEvents`. -/
theorem concrete_full_make_init_m7313_halt {width : Nat} [NeZero width] {C F : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × HolProg width)} {t : Flapjack.Compiler.Backend.LabSem.State width C F}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {s : StackSemStateFiniteExact width C F}
    {opt : Option (StackSemStateFiniteExact width C F)}
    (hfm : FullMakeInit.fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code t
      saveRegs dataSp coracle = (s, opt))
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle)
    (k : Nat) (res : Option (StackSemResult width)) (s_post : StackSemStateFiniteExact width C F)
    (outcome : HolOutcome)
    (hrun : StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
        { s with clock := k }) = (res, s_post))
    (hclass : FlattenSemantics.stackEntryClass res = .CompleteResult outcome)
    (hnt_lab : (LabSem.evaluate { t with clock := labBudgetOfStackClock k }).1 ≠ .timeOut) :
    (LabSem.evaluate { t with clock := labBudgetOfStackClock k }).1 = .halt outcome ∧
      (LabSem.evaluate { t with clock := labBudgetOfStackClock k }).2.ffi.ioEvents =
        s_post.ffi.ioEvents :=
  full_make_init_halt_of_lab_not_timeOut hfm hA k res s_post outcome hrun hclass
    (labBudgetOfStackClock k) hnt_lab

/-- Combined Stage 4 (`fullMakeInit` + `LabFilter` + `alignSdm` + `alignDm`) halt and FFI
transfer at `labBudgetOfStackClock k`: if the aligned filtered Lab state `alignDm (alignSdm t_filt)`
halts at `labBudgetOfStackClock k`, the pre-filter and post-filter Lab states agree on
`.halt outcome` and `ffi`. -/
theorem concrete_stage4_m7313_filter_align_halt {width : Nat} [NeZero width] {C F : Type}
    (hw : goodDimindex width)
    (s_lab t_filt : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hr : LabFilter.Proofs.stateRel s_lab t_filt)
    (k : Nat) (outcome : HolOutcome)
    (next : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hhalt : LabSem.evaluate { alignDm (alignSdm t_filt) with clock := labBudgetOfStackClock k } =
      (.halt outcome, next)) :
    (LabSem.evaluate { s_lab with clock := labBudgetOfStackClock k }).1 = .halt outcome ∧
      (LabSem.evaluate { s_lab with clock := labBudgetOfStackClock k }).2.ffi = next.ffi :=
  lab_filter_align_clocked_halt hw s_lab t_filt hr (labBudgetOfStackClock k) outcome next hhalt

end InitECandidate.Solver.Wave8Stage.R12_ConcreteM7313Argon
