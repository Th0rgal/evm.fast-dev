import InitECandidate.Proofs.BoundedStackToLab
import InitECandidate.Solver.BoundedCertificate

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.WordToStackClockBound` — Exact Leaf Clock Calculus & `WordToStack` / `StackRawCall` Clock Preservation

This module establishes:
1. **Exact Clock Calculus of `WordSem` Leaf Instructions (`word_evaluate_leaf_clock_eq`)**:
   - In `WordSemStateFiniteExact.evaluate`, the leaf instructions `.skip`, `.move`,
     `.inst`, `.assign`, `.get`, `.set`, `.store`, `.setVar`, `.unsetVar`, and
     `.locValue` preserve `s.clock` (`0` ticks consumed on every branch).
   - State helpers `setVar` and `unsetVar` preserve `s.clock` identically.
2. **Exact Clock Calculus of `StackSem` Leaf Instructions (`stack_evaluate_leaf_clock_eq`)**:
   - In `StackSemEvaluate.evaluate`, the leaf instructions `.skip`, `.inst`, `.get`,
     `.set`, `.op` (`.opCurrHeap`), `.storeConsts`, `.raise`, `.return` (`.ret`), and
     `.locValue` preserve `s.clock` (`0` ticks consumed on every branch).
3. **`WordToStack` & `StackRawCall` Clock Preservation (`ck_w2s = 0` / explicit-clock non-`.timeOut` agreement & `stack_raw_call_tick_preserve`)**:
   - Under `wordLangSafeForSpace`, `WordToStack` entry compilation preserves non-`.timeOut`
     termination at zero clock overhead (`ck_w2s = 0`) and agrees across any explicit
     non-`.timeOut` target clock (`word_to_stack_compile_halt_of_stack_not_timeOut`).
   - `StackRawCall` preserves `.tick` (`comp info .tick = .tick` and `compTop info .tick = .tick`),
     satisfies zero-clock-overhead (`ck = 0`) simulation on `.tick`, and preserves
     entry-call outcomes at zero clock overhead whenever the compiled `StackRawCall`
     entry call does not time out (`stack_raw_call_tick_preserve`).
-/

namespace InitECandidate.Solver

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver.BoundedCertificate
open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-! ## 1. `WordSem` Leaf Instruction Clock Calculus (`word_evaluate_leaf_clock_eq`) -/

/-- `WordSemStateFiniteExact.setVar` preserves `s.clock` exactly. -/
@[simp] theorem word_setVar_clock_eq {width : Nat} [NeZero width] {C F : Type}
    (v : Nat) (w : WordLocW width) (s : WordSemStateFiniteExact width C F) :
    (WordSemStateFiniteExact.setVar v w s).clock = s.clock := rfl

/-- `WordSemStateFiniteExact.unsetVar` preserves `s.clock` exactly. -/
@[simp] theorem word_unsetVar_clock_eq {width : Nat} [NeZero width] {C F : Type}
    (v : Nat) (s : WordSemStateFiniteExact width C F) :
    (WordSemStateFiniteExact.unsetVar v s).clock = s.clock := rfl

/-- `WordSemStateFiniteExact.setVars` preserves `s.clock` exactly. -/
@[simp] theorem word_setVars_clock_eq {width : Nat} [NeZero width] {C F : Type}
    (names : List Nat) (values : List (WordLocW width))
    (s : WordSemStateFiniteExact width C F) :
    (WordSemStateFiniteExact.setVars names values s).clock = s.clock := rfl

/-- `WordSemStateFiniteExact.setStore` preserves `s.clock` exactly. -/
@[simp] theorem word_setStore_clock_eq {width : Nat} [NeZero width] {C F : Type}
    (name : WordStoreHOL) (value : WordLocW width)
    (s : WordSemStateFiniteExact width C F) :
    (WordSemStateFiniteExact.setStore name value s).clock = s.clock := rfl

/-- `.skip` in `WordSem` preserves `s.clock`. -/
theorem word_evaluate_skip_clock {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) :
    (WordSemStateFiniteExact.evaluate (.skip : WordLangProgHOL (BitVec width)) s).2.clock =
      s.clock := by
  rw [WordSemStateFiniteExact.evaluate.eq_def]

/-- `.move` in `WordSem` preserves `s.clock` in all branches. -/
theorem word_evaluate_move_clock {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (pri : Nat) (moves : List (Nat × Nat)) :
    (WordSemStateFiniteExact.evaluate (.move pri moves : WordLangProgHOL (BitVec width)) s).2.clock =
      s.clock := by
  rw [WordSemStateFiniteExact.evaluate.eq_def]
  dsimp only
  split
  · cases WordSemStateFiniteExact.getVars (moves.map Prod.snd) s <;> rfl
  · rfl

/-- `.inst` in `WordSem` preserves `s.clock` in all branches. -/
theorem word_evaluate_inst_clock {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (i : WordLangInst (BitVec width)) :
    (WordSemStateFiniteExact.evaluate (.inst i : WordLangProgHOL (BitVec width)) s).2.clock =
      s.clock := by
  rw [WordSemStateFiniteExact.evaluate.eq_def]
  dsimp only
  cases h : WordSemStateFiniteExact.inst i s with
  | none => rfl
  | some s1 => exact (WordSemStateFiniteExact.instConst i s s1 h).1

/-- `.assign` in `WordSem` preserves `s.clock` in all branches. -/
theorem word_evaluate_assign_clock {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (v : Nat) (exp : WordLangExpHOL (BitVec width)) :
    (WordSemStateFiniteExact.evaluate (.assign v exp : WordLangProgHOL (BitVec width)) s).2.clock =
      s.clock := by
  rw [WordSemStateFiniteExact.evaluate.eq_def]
  dsimp only
  cases WordSemStateFiniteExact.wordExp s exp <;> rfl

/-- `.get` in `WordSem` preserves `s.clock` in all branches. -/
theorem word_evaluate_get_clock {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (v : Nat) (name : WordStoreHOL) :
    (WordSemStateFiniteExact.evaluate (.get v name : WordLangProgHOL (BitVec width)) s).2.clock =
      s.clock := by
  rw [WordSemStateFiniteExact.evaluate.eq_def]
  dsimp only
  cases WordSemStateFiniteExact.getStore name s <;> rfl

/-- `.set` in `WordSem` preserves `s.clock` in all branches. -/
theorem word_evaluate_set_clock {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (v : WordStoreHOL) (exp : WordLangExpHOL (BitVec width)) :
    (WordSemStateFiniteExact.evaluate (.set v exp : WordLangProgHOL (BitVec width)) s).2.clock =
      s.clock := by
  rw [WordSemStateFiniteExact.evaluate.eq_def]
  dsimp only
  split
  · rfl
  · cases WordSemStateFiniteExact.wordExp s exp <;> rfl

/-- `.store` in `WordSem` preserves `s.clock` in all branches. -/
theorem word_evaluate_store_clock {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (exp : WordLangExpHOL (BitVec width)) (v : Nat) :
    (WordSemStateFiniteExact.evaluate (.store exp v : WordLangProgHOL (BitVec width)) s).2.clock =
      s.clock := by
  rw [WordSemStateFiniteExact.evaluate.eq_def]
  dsimp only
  cases WordSemStateFiniteExact.wordExp s exp with
  | none => rfl
  | some ev =>
      cases ev with
      | loc _ _ => rfl
      | word a =>
          cases WordSemStateFiniteExact.getVar v s with
          | none => rfl
          | some w =>
              dsimp only
              cases hm : WordSemStateFiniteExact.memStore a w s with
              | none => rfl
              | some s1 => exact (WordSemStateFiniteExact.memStore_clock_termdep hm).1

/-- `.storeConsts` in `WordSem` (which updates variables via `setVar` and `unsetVar`)
preserves `s.clock` in all branches. -/
theorem word_evaluate_storeConsts_clock {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (t1 t2 addr offset : Nat)
    (words : List (Bool × BitVec width)) :
    (WordSemStateFiniteExact.evaluate
      (.storeConsts t1 t2 addr offset words : WordLangProgHOL (BitVec width)) s).2.clock =
      s.clock := by
  rw [WordSemStateFiniteExact.evaluate.eq_def]
  dsimp only
  cases WordSemStateFiniteExact.getVar addr s with
  | none => rfl
  | some va =>
      cases va with
      | loc _ _ => rfl
      | word a =>
          cases WordSemStateFiniteExact.getVar offset s with
          | none => rfl
          | some vo =>
              cases vo with
              | loc _ _ => rfl
              | word off =>
                  dsimp only
                  split <;> rfl

/-- `.locValue` in `WordSem` preserves `s.clock` in all branches. -/
theorem word_evaluate_locValue_clock {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (r l1 : Nat) :
    (WordSemStateFiniteExact.evaluate (.locValue r l1 : WordLangProgHOL (BitVec width)) s).2.clock =
      s.clock := by
  rw [WordSemStateFiniteExact.evaluate.eq_def]
  dsimp only
  split <;> rfl

/-- Syntactic classifier for the non-ticking leaf instructions of `WordLangProgHOL (BitVec width)`. -/
def isWordClockPreservingLeaf {width : Nat} [NeZero width] :
    WordLangProgHOL (BitVec width) → Bool
  | .skip | .move _ _ | .inst _ | .assign _ _ | .get _ _ | .set _ _
  | .store _ _ | .storeConsts _ _ _ _ _ | .opCurrHeap _ _ _ | .locValue _ _ => true
  | _ => false

/-- Unified `WordSem` leaf clock-preservation theorem (`word_evaluate_leaf_clock_eq`):
every leaf instruction of `WordLangProgHOL (BitVec width)` satisfying
`isWordClockPreservingLeaf prog = true` (`.skip`, `.move`, `.inst`, `.assign`,
`.get`, `.set`, `.store`, `.storeConsts`, `.opCurrHeap`, `.locValue`) and the
variable helpers `setVar` / `unsetVar` preserve `s.clock` (`0` ticks consumed). -/
theorem word_evaluate_leaf_clock_eq {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F)
    (prog : WordLangProgHOL (BitVec width))
    (v : Nat) (w : WordLocW width)
    (hleaf : isWordClockPreservingLeaf prog = true) :
    (WordSemStateFiniteExact.evaluate prog s).2.clock = s.clock ∧
    (WordSemStateFiniteExact.setVar v w s).clock = s.clock ∧
    (WordSemStateFiniteExact.unsetVar v s).clock = s.clock := by
  refine ⟨?_, rfl, rfl⟩
  cases prog with
  | skip => exact word_evaluate_skip_clock s
  | move pri moves => exact word_evaluate_move_clock s pri moves
  | inst i => exact word_evaluate_inst_clock s i
  | assign r exp => exact word_evaluate_assign_clock s r exp
  | get r name => exact word_evaluate_get_clock s r name
  | set name exp => exact word_evaluate_set_clock s name exp
  | store exp r => exact word_evaluate_store_clock s exp r
  | storeConsts t1 t2 addr offset words =>
      exact word_evaluate_storeConsts_clock s t1 t2 addr offset words
  | opCurrHeap b dst src =>
      rw [WordSemStateFiniteExact.evaluate.eq_def]
      dsimp only
      cases WordSemStateFiniteExact.wordExp s (.op b [.var src, .lookup .currHeap]) <;> rfl
  | locValue r l1 => exact word_evaluate_locValue_clock s r l1
  | _ => simp [isWordClockPreservingLeaf] at hleaf

/-! ## 2. `StackSem` Leaf Instruction Clock Calculus (`stack_evaluate_leaf_clock_eq`) -/

/-- `.skip` in `StackSem` preserves `s.clock`. -/
theorem stack_evaluate_skip_clock {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) :
    (StackSemEvaluate.evaluate ((.skip : HolProg width), s)).2.clock = s.clock := by
  rw [StackSemEvaluate.evaluate_skip]

/-- `.inst` in `StackSem` preserves `s.clock` in all branches. -/
theorem stack_evaluate_inst_clock {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (i : HolInst width) :
    (StackSemEvaluate.evaluate ((.inst i : HolProg width), s)).2.clock = s.clock := by
  rw [StackSemEvaluate.evaluate_inst]
  cases h : StackSemInst.instHOL i s with
  | none => rfl
  | some s1 => exact (StackPropsInstructionConstants.instConst i s s1 h).2.1

/-- `.get` in `StackSem` preserves `s.clock` in all branches. -/
theorem stack_evaluate_get_clock {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (v : Nat) (name : StoreName) :
    (StackSemEvaluate.evaluate ((.get v name : HolProg width), s)).2.clock = s.clock := by
  rw [StackSemEvaluate.evaluate_get]
  split
  · rfl
  · cases s.store.lookup (StackSemRegisterTransfers.storeOfSyntax name) <;> rfl

/-- `.set` in `StackSem` preserves `s.clock` in all branches. -/
theorem stack_evaluate_set_clock {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (name : StoreName) (v : Nat) :
    (StackSemEvaluate.evaluate ((.set name v : HolProg width), s)).2.clock = s.clock := by
  rw [StackSemEvaluate.evaluate_set]
  split
  · rfl
  · cases StackSemStateOps.getVar v s <;> rfl

/-- `.opCurrHeap` (`.op` on current heap) in `StackSem` preserves `s.clock` in all branches. -/
theorem stack_evaluate_opCurrHeap_clock {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (binop : HolBinop) (v src : Nat) :
    (StackSemEvaluate.evaluate ((.opCurrHeap binop v src : HolProg width), s)).2.clock = s.clock := by
  rw [StackSemEvaluate.evaluate_opCurrHeap]
  split
  · rfl
  · cases StackSemExpressions.wordExp s (.op binop [.var src, .lookup .currHeap]) <;> rfl

/-- `.storeConsts` in `StackSem` preserves `s.clock` in all branches. -/
theorem stack_evaluate_storeConsts_clock {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (t1 t2 : Nat) (stubOpt : Option Nat) :
    (StackSemEvaluate.evaluate ((.storeConsts t1 t2 stubOpt : HolProg width), s)).2.clock =
      s.clock := by
  rw [StackSemEvaluate.evaluate_storeConsts]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rcases h : StackSemStoreConsts.storeConstSem t1 t2 s with ⟨res, s1⟩
        exact (StackPropsAllocationConstants.storeConstSemConst t1 t2 s s1 res h).2.1

/-- `.raise` in `StackSem` preserves `s.clock` in all branches. -/
theorem stack_evaluate_raise_clock {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (n : Nat) :
    (StackSemEvaluate.evaluate ((.raise n : HolProg width), s)).2.clock = s.clock := by
  rw [StackSemEvaluate.evaluate_raise]
  cases StackSemStateOps.getVar n s with
  | none => rfl
  | some v => cases v <;> rfl

/-- `.ret` (`.return`) in `StackSem` preserves `s.clock` in all branches. -/
theorem stack_evaluate_ret_clock {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (n : Nat) :
    (StackSemEvaluate.evaluate ((.ret n : HolProg width), s)).2.clock = s.clock := by
  rw [StackSemEvaluate.evaluate_ret]
  cases StackSemStateOps.getVar n s with
  | none => rfl
  | some v => cases v <;> rfl

/-- `.locValue` in `StackSem` preserves `s.clock` in all branches. -/
theorem stack_evaluate_locValue_clock {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (r l1 l2 : Nat) :
    (StackSemEvaluate.evaluate ((.locValue r l1 l2 : HolProg width), s)).2.clock = s.clock := by
  rw [StackSemEvaluate.evaluate_locValue]
  split <;> rfl

/-- Syntactic classifier for the non-ticking leaf instructions of `HolProg width`. -/
def isStackClockPreservingLeaf {width : Nat} [NeZero width] : HolProg width → Bool
  | .skip | .inst _ | .get _ _ | .set _ _ | .opCurrHeap _ _ _
  | .storeConsts _ _ _ | .raise _ | .ret _ | .locValue _ _ _ => true
  | _ => false

/-- Unified `StackSem` leaf clock-preservation theorem (`stack_evaluate_leaf_clock_eq`):
every leaf instruction of `HolProg width` satisfying `isStackClockPreservingLeaf prog = true`
(`.skip`, `.inst`, `.get`, `.set`, `.opCurrHeap` / `.op`, `.storeConsts`, `.raise`,
`.ret` / `.return`, `.locValue`) preserves `s.clock` (`0` ticks consumed). -/
theorem stack_evaluate_leaf_clock_eq {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (prog : HolProg width)
    (hleaf : isStackClockPreservingLeaf prog = true) :
    (StackSemEvaluate.evaluate (prog, s)).2.clock = s.clock := by
  cases prog with
  | skip => exact stack_evaluate_skip_clock s
  | inst i => exact stack_evaluate_inst_clock s i
  | get v name => exact stack_evaluate_get_clock s v name
  | set name v => exact stack_evaluate_set_clock s name v
  | opCurrHeap binop v src => exact stack_evaluate_opCurrHeap_clock s binop v src
  | storeConsts t1 t2 stubOpt => exact stack_evaluate_storeConsts_clock s t1 t2 stubOpt
  | raise n => exact stack_evaluate_raise_clock s n
  | ret n => exact stack_evaluate_ret_clock s n
  | locValue r l1 l2 => exact stack_evaluate_locValue_clock s r l1 l2
  | _ => simp [isStackClockPreservingLeaf] at hleaf

/-! ## 3. `WordToStack` & `StackRawCall` Clock Preservation (`ck_w2s = 0` & `stack_raw_call_tick_preserve`) -/

/-- Explicit-clock (`K_stack`) and zero-overhead (`ck_w2s = 0` at `K_stack = clk`)
non-`.timeOut` halt agreement for `WordToStack.Native`:
if a `WordSem` entry call on `makeInit` at clock `clk` completes (`res ≠ some .error` and
`res ≠ some .timeOut`), and the compiled `StackSem` entry call on `t` at explicit clock
`K_stack` does not time out (`res_t ≠ some .timeOut`), then it produces the exact mapped
result `res.map compileResult` and identical FFI state (and in particular at `K_stack = clk`
requires `ck_w2s = 0` extra clock ticks). -/
theorem word_to_stack_compile_halt_of_stack_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    (asmConf : AsmConfigExact width) (code : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (t : StackSemStateFiniteExact width C F) (k : Nat)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (start clk K_stack : Nat)
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
      { t with clock := K_stack }) = (res_t, t1))
    (hnt : res_t ≠ some .timeOut) :
    res_t = res.map WordToStackProofs.CompCorrect.compileResult ∧ t1.ffi = s1.ffi :=
  InitE.word_to_stack_compile_halt_of_stack_not_timeOut
    asmConf code t k coracle start clk K_stack res s1 res_t t1
    codeEq kEq ok noRaise noStore bitmapsPrefix conventions safe hrun hne hnt_w hrun_t hnt

/-- Exact `.tick` preservation and zero-clock-overhead (`ck = 0`) simulation for `StackRawCall`:
1. `StackRawCall.comp info .tick = .tick` and `StackRawCall.compTop info .tick = .tick`.
2. Under `StackRawCall.stateRel info source target`, evaluating `.tick` on `source`
   produces the exact same result and a `stateRel`-related target state on `target`
   at the exact same clock (`clock = target.clock`, `0` extra ticks) with identical
   post-state clock (`targetState.clock = resultState.clock`).
3. At entry-call level, if the `StackRawCall`-compiled program does not time out at
   `clock`, its result and FFI state agree with the source `StackSem` run at the exact
   same `clock` (`extra = 0`). -/
theorem stack_raw_call_tick_preserve {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.tick : HolProg width), source) = (result, resultState))
    (relation : StackRawCall.stateRel info source target) :
    StackRawCall.comp info (.tick : HolProg width) = .tick ∧
    StackRawCall.compTop info (.tick : HolProg width) = .tick ∧
    (∃ targetState,
      StackRawCall.stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (StackRawCall.comp info (.tick : HolProg width), target) =
        (result, targetState) ∧
      targetState.clock = resultState.clock) := by
  refine ⟨rfl, rfl, ?_⟩
  obtain ⟨targetState, postRel, targetExec⟩ :=
    StackRawCall.BasicLeaves.evaluate_stateRel (.tick : HolProg width) .tick info
      source target resultState result execution relation
  refine ⟨targetState, postRel, targetExec, ?_⟩
  exact StackRawCall.LoopCase.stateRel_clock info resultState targetState postRel

#print axioms word_evaluate_leaf_clock_eq
#print axioms stack_evaluate_leaf_clock_eq
#print axioms word_to_stack_compile_halt_of_stack_not_timeOut
#print axioms stack_raw_call_tick_preserve

end InitECandidate.Solver
