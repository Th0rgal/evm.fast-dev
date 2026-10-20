import InitECandidate.Solver.StackRemoveInitOffsetBound
import InitECandidate.Solver.StackNamesExactClockIso
import Flapjack.Compiler.Backend.StackRemove.Comp

/-!
Exact StackSem clock preservation for the straight-line StackRemove fragment.
`alloc` in guest.pp.pnk is a user-defined bump-pointer function, not GC allocation.
No theorem here identifies StackSem ticks with LabSem instruction fuel.
`compCorrect` and `flattenCallCorrect` provide existential extra clocks only.
`comp` preserves explicit ticks; storeConsts introduces copy loops, and jump-mode
stackAlloc can invoke a stub. Neither is silently included in the neutral fragment.
-/
namespace InitECandidate.Solver.StackRemoveBodyClockBound
open Flapjack Flapjack.Compiler.Backend StackLang StackProps StackRemove
open StackProps.EvaluateAddClock
set_option autoImplicit false

/-- Leaves with neutral lowering, closed under sequence and conditionals.
Stack allocation is included in the non-jump overflow-check mode. -/
def Body {width : Nat} [NeZero width] (jump : Bool) : HolProg width → Prop
  | .skip | .inst _ | .halt _ | .locValue _ _ _ | .get _ _ | .set _ _
  | .opCurrHeap _ _ _ | .stackFree _ | .stackLoad _ _ | .stackStore _ _
  | .stackLoadAny _ _ | .stackStoreAny _ _ | .stackGetSize _ | .stackSetSize _
  | .bitmapLoad _ _ | .dataBufferWrite _ _ => True
  | .stackAlloc _ => jump = false
  | .seq p q | .ite _ _ _ p q => Body jump p ∧ Body jump q
  | _ => False

private theorem free_neutral {w : Nat} [NeZero w] (ptr n : Nat) :
    clockNeutralHOL (stackFree (width := w) ptr n) := by
  rw [stackFree]
  split
  · trivial
  · split
    · trivial
    · exact ⟨True.intro, free_neutral ptr _⟩
termination_by n
decreasing_by simp_all [maxStackAlloc]; omega

private theorem up_neutral {w : Nat} [NeZero w] (r n : Nat) :
    clockNeutralHOL (upshift (width := w) r n) := by
  rw [upshift]
  split
  · trivial
  · exact ⟨True.intro, up_neutral r _⟩
termination_by n
decreasing_by simp_all [maxStackAlloc]; omega

private theorem down_neutral {w : Nat} [NeZero w] (r n : Nat) :
    clockNeutralHOL (downshift (width := w) r n) := by
  rw [downshift]
  split
  · trivial
  · exact ⟨True.intro, down_neutral r _⟩
termination_by n
decreasing_by simp_all [maxStackAlloc]; omega

private theorem alloc_neutral {w : Nat} [NeZero w] (ptr n : Nat) :
    clockNeutralHOL (stackAlloc (width := w) false ptr n) := by
  rw [StackRemove.stackAlloc]
  split
  · trivial
  · split
    · simp [singleStackAlloc, haltInst, clockNeutralHOL]
    · exact ⟨by simp [singleStackAlloc, haltInst, clockNeutralHOL],
        alloc_neutral ptr _⟩
termination_by n
decreasing_by simp_all [maxStackAlloc]; omega

/-- Lowering every admitted body is structurally neutral, including all address chunks. -/
theorem comp_neutral {w : Nat} [NeZero w] (jump : Bool)
    (bounds : BitVec w × BitVec w) (ptr : Nat) (p : HolProg w) (h : Body jump p) :
    clockNeutralHOL (StackRemove.comp jump bounds ptr p) := by
  cases p <;> simp only [Body] at h
  case seq p q =>
    simp only [StackRemove.comp, clockNeutralHOL]
    exact ⟨comp_neutral jump bounds ptr p h.1, comp_neutral jump bounds ptr q h.2⟩
  case ite cmp r rhs p q =>
    simp only [StackRemove.comp, clockNeutralHOL]
    exact ⟨comp_neutral jump bounds ptr p h.1, comp_neutral jump bounds ptr q h.2⟩
  case stackAlloc n => simpa [StackRemove.comp, h] using alloc_neutral (w := w) ptr n
  all_goals simp [StackRemove.comp, clockNeutralHOL, moveInst, moveHOL, addInst, subInst,
    rightShiftInst, leftShiftInst, listSeqHOL, stackLoad, stackStore,
    free_neutral] <;>
    split <;> simp [clockNeutralHOL, up_neutral, down_neutral]
termination_by sizeOf p

/-- Exact clock of an arbitrary admitted source body, even on errors. -/
theorem source_post_clock {w : Nat} [NeZero w] {C F : Type}
    (jump : Bool) (p : HolProg w) (s : StackSemStateFiniteExact w C F) (h : Body jump p) :
    (StackSemEvaluate.evaluate (p, s)).2.clock = s.clock := by
  cases p <;> simp only [Body] at h
  case inst i => exact (clockFree_inst i s s.clock).2
  case seq p q =>
    rw [StackSemEvaluate.evaluate_seq]
    cases he : StackSemEvaluate.evaluate (p, s) with
    | mk r t =>
      have ht := source_post_clock jump p s h.1
      rw [he] at ht
      have hf : StackSemControl.fixClock s (r, t) = (r, t) := by
        change (r, {t with clock := min s.clock t.clock}) = (r, t)
        dsimp only at ht
        rw [← ht, Nat.min_self]
      rw [hf]
      cases r with
      | none => exact (source_post_clock jump q t h.2).trans ht
      | some r => exact ht
  case ite cmp r rhs p q =>
    simp only [StackSemEvaluate.evaluate_ite]
    repeat' (first | split | dsimp only)
    all_goals first | exact source_post_clock jump p s h.1
                    | exact source_post_clock jump q s h.2
  all_goals exact (clockFree_of_ctor _ rfl s s.clock).2
termination_by sizeOf p

private theorem neutral_post {w : Nat} [NeZero w] {C F : Type}
    (p : HolProg w) (s : StackSemStateFiniteExact w C F) (h : clockNeutralHOL p) :
    (StackSemEvaluate.evaluate (p, s)).2.clock = s.clock := by
  rcases he : StackSemEvaluate.evaluate (p, s) with ⟨r, t⟩
  have hx := EvaluateNeutral.evaluateClockNeutral p s t r s.clock ⟨he, h⟩
  have hs : {s with clock := s.clock} = s := rfl
  rw [hs, he] at hx
  exact congrArg (fun x => x.2.clock) hx

/-- Compiled clock is unchanged for all stores, registers and error outcomes. -/
theorem comp_post_clock {w : Nat} [NeZero w] {C F : Type}
    (jump : Bool) (bounds : BitVec w × BitVec w) (ptr : Nat) (p : HolProg w)
    (s : StackSemStateFiniteExact w C F) (h : Body jump p) :
    (StackSemEvaluate.evaluate (StackRemove.comp jump bounds ptr p, s)).2.clock = s.clock :=
  neutral_post _ s (comp_neutral jump bounds ptr p h)

/-- Arbitrary source and target states with equal input clocks have equal output clocks.
This clock-only result makes no claim about equality of values or memory. -/
theorem body_clock_preservation {w : Nat} [NeZero w] {C F : Type}
    (jump : Bool) (bounds : BitVec w × BitVec w) (ptr : Nat) (p : HolProg w)
    (s t : StackSemStateFiniteExact w C F) (h : Body jump p) (hc : t.clock = s.clock) :
    (StackSemEvaluate.evaluate (StackRemove.comp jump bounds ptr p, t)).2.clock =
      (StackSemEvaluate.evaluate (p, s)).2.clock := by
  rw [comp_post_clock jump bounds ptr p t h, source_post_clock jump p s h, hc]

/-- Compiled execution commutes with replacing its clock, including replacement by zero. -/
theorem comp_replace_clock {w : Nat} [NeZero w] {C F : Type}
    (jump : Bool) (bounds : BitVec w × BitVec w) (ptr : Nat) (p : HolProg w)
    (s : StackSemStateFiniteExact w C F) (k : Nat) (h : Body jump p) :
    StackSemEvaluate.evaluate (StackRemove.comp jump bounds ptr p, {s with clock := k}) =
      ((StackSemEvaluate.evaluate (StackRemove.comp jump bounds ptr p, s)).1,
       {(StackSemEvaluate.evaluate (StackRemove.comp jump bounds ptr p, s)).2 with clock := k}) := by
  exact EvaluateNeutral.evaluateClockNeutral _ s _ _ k ⟨rfl, comp_neutral jump bounds ptr p h⟩

/-- Sequential lowering remains neutral without any successful-evaluation assumption. -/
theorem seq_post_clock {w : Nat} [NeZero w] {C F : Type}
    (jump : Bool) (bounds : BitVec w × BitVec w) (ptr : Nat) (p q : HolProg w)
    (s : StackSemStateFiniteExact w C F) (hp : Body jump p) (hq : Body jump q) :
    (StackSemEvaluate.evaluate (StackRemove.comp jump bounds ptr (.seq p q), s)).2.clock = s.clock :=
  comp_post_clock jump bounds ptr (.seq p q) s ⟨hp, hq⟩

/-- Initializer and compiled body together consume exactly zero StackSem ticks. -/
theorem init_body_post_clock {w : Nat} [NeZero w] {C F : Type}
    (jump gc : Bool) (bounds : BitVec w × BitVec w) (ptr heap : Nat) (p : HolProg w)
    (s : StackSemStateFiniteExact w C F) (h : Body jump p) :
    (StackSemEvaluate.evaluate (.seq (initCode gc heap ptr) (StackRemove.comp jump bounds ptr p), s)).2.clock =
      s.clock :=
  neutral_post _ s ⟨StackRemoveInitOffsetBound.init_code_neutral gc heap ptr,
    comp_neutral jump bounds ptr p h⟩

/-- Composition with StackNames: renaming and initialization add zero body ticks. -/
theorem names_init_body_post_clock {w : Nat} [NeZero w] {C F : Type}
    (c : C → List (Nat × HolProg w) → Option (List (BitVec 8) × C))
    (f : Spt Nat) (jump gc : Bool) (bounds : BitVec w × BitVec w) (ptr heap : Nat)
    (p : HolProg w) (s : StackSemStateFiniteExact w C F) (h : Body jump p) :
    (StackSemEvaluate.evaluate (.seq (initCode gc heap ptr) (StackRemove.comp jump bounds ptr p),
      StackNamesExactClockIso.stateRel c f s)).2.clock = s.clock := by
  rw [init_body_post_clock jump gc bounds ptr heap p _ h]
  exact (StackNamesExactClockIso.stack_names_stateRel_clock_iso c f s).1.symm

/-- The actual StackNames program compiler preserves the initialized body's exact clock.
Its original bijection, runtime-mode and compiler compatibility premises are explicit. -/
theorem names_compiled_init_body_post_clock {w : Nat} [NeZero w] {C F : Type}
    (c : C → List (Nat × HolProg w) → Option (List (BitVec 8) × C))
    (f : Spt Nat) (jump gc : Bool) (bounds : BitVec w × BitVec w) (ptr heap : Nat)
    (p : HolProg w) (s : StackSemStateFiniteExact w C F) (h : Body jump p)
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (ha : ¬s.useAlloc) (hs : ¬s.useStore) (hk : ¬s.useStack)
    (hc : s.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f)) :
    (StackSemEvaluate.evaluate
      (StackNames.progCompHOL f (.seq (initCode gc heap ptr) (StackRemove.comp jump bounds ptr p)),
       StackNamesExactClockIso.stateRel c f s)).2.clock = s.clock := by
  have hn := (StackNamesExactClockIso.stack_names_eval_post_clock_iso c f
    (.seq (initCode gc heap ptr) (StackRemove.comp jump bounds ptr p)) s hf ha hs hk hc).2.1
  exact hn.trans (init_body_post_clock jump gc bounds ptr heap p s h)

/-- Sharp zero consumed-tick bound. -/
theorem body_consumed_ticks {w : Nat} [NeZero w] {C F : Type}
    (jump : Bool) (bounds : BitVec w × BitVec w) (ptr : Nat) (p : HolProg w)
    (s : StackSemStateFiniteExact w C F) (h : Body jump p) :
    s.clock - (StackSemEvaluate.evaluate (StackRemove.comp jump bounds ptr p, s)).2.clock = 0 := by
  rw [comp_post_clock jump bounds ptr p s h]; omega

/-- Explicit source ticks are preserved literally; no lowering-generated tick is added. -/
theorem comp_tick {w : Nat} [NeZero w] (jump : Bool)
    (bounds : BitVec w × BitVec w) (ptr : Nat) :
    StackRemove.comp jump bounds ptr (.tick : HolProg w) = .tick := by simp [StackRemove.comp]

#print axioms body_clock_preservation
#print axioms names_init_body_post_clock
#print axioms names_compiled_init_body_post_clock
#print axioms comp_replace_clock
end InitECandidate.Solver.StackRemoveBodyClockBound
