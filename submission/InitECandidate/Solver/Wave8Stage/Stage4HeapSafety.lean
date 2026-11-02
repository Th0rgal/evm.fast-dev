import InitECandidate.Solver.Wave8Stage.Stage4InitSafety

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace InitECandidate.Solver.Wave8Stage.RuntimeLabels
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemRegisterTransfers
variable {width : Nat} [NeZero width]

def HeapSafe {A : Type} (bad : Nat) (heap : (A × WordLocW width) → Prop) : Prop :=
  ∀ a v, heap (a, v) → ValueSafe bad v

theorem heapSafe_split {A : Type} {bad : Nat}
    {heap left right : (A × WordLocW width) → Prop}
    (hs : HeapSafe bad heap) (hp : SetSep.split heap (left, right)) :
    HeapSafe bad left ∧ HeapSafe bad right := by
  constructor
  · intro a v hv
    apply hs a v
    rw [← hp.1]
    exact Or.inl hv
  · intro a v hv
    apply hs a v
    rw [← hp.1]
    exact Or.inr hv

theorem heapSafe_memory {bad : Nat} {domain : BitVec width → Bool}
    {memory : BitVec width → WordLocW width} (hs : MemorySafe bad domain memory) :
    HeapSafe bad (SetSep.fun2Set (memory, fun a => domain a = true)) := by
  intro a v hv
  obtain ⟨he, hd⟩ := (SetSep.fun2SetThm memory _ a v).mp hv
  rw [← he]
  exact hs a hd

theorem heapSafe_wordList {bad : Nat} (values : List (WordLocW width))
    (base : BitVec width) (heap : (BitVec width × WordLocW width) → Prop)
    (hs : HeapSafe bad heap) (hl : Misc.wordList base values heap) :
    ∀ v ∈ values, ValueSafe bad v := by
  induction values generalizing base heap with
  | nil => simp
  | cons v vs ih =>
    obtain ⟨head, tail, split, one, rest⟩ := hl
    have hh := heapSafe_split hs split
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · apply hh.1 base x
      rw [one]
    · exact ih _ _ hh.2 rest x hx

theorem heapSafe_wordListRev {bad : Nat} (values : List (WordLocW width))
    (base : BitVec width) (heap : (BitVec width × WordLocW width) → Prop)
    (hs : HeapSafe bad heap) (hl : StackRemove.wordListRev base values heap) :
    ∀ v ∈ values, ValueSafe bad v := by
  induction values generalizing base heap with
  | nil => simp
  | cons v vs ih =>
    obtain ⟨head, tail, split, one, rest⟩ := hl
    have hh := heapSafe_split hs split
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · apply hh.1 (base - StackRemove.bytesInWord width) x
      rw [one]
    · exact ih _ _ hh.2 rest x hx

/-- The real StackRemove separation relation transfers memory, stack, and
store safety back to the abstract state. Registers outside its bound are
supplied separately; initReduce retains the complete target register map. -/
theorem stateSafe_of_remove_relation {C F : Type} {bad : Nat}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (hr : StackRemove.stateRelHOL jump bounds pointer source target)
    (hs : CoreSafe bad target) (hregs : MapSafe bad source.regs) :
    StateSafe bad source := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hcurr, _, _, _, hheap⟩ := hr
  dsimp only at hheap
  obtain ⟨_, hheap⟩ := hheap
  split at hheap
  next base hbase =>
    obtain ⟨_, _, _, hheap⟩ := hheap
    obtain ⟨h4, hstack, split4, a4, astack⟩ := hheap
    have safe4 := heapSafe_split (heapSafe_memory hs.memory) split4
    obtain ⟨h3, hstore, split3, a3, astore⟩ := a4
    have safe3 := heapSafe_split safe4.1 split3
    obtain ⟨h2, hdata, split2, a2, _⟩ := a3
    have safe2 := heapSafe_split safe3.1 split2
    obtain ⟨hmem, hbits, split1, amem, _⟩ := a2
    have safe1 := heapSafe_split safe2.1 split1
    refine ⟨hregs, ?_, heapSafe_wordList _ _ _ safe4.2 astack, ?_⟩
    · intro name v hv
      by_cases hc : name = .currHeap
      · subst name
        exact hs.regs _ v (hcurr.trans hv)
      · have hn : storeToSyntax name ≠ .currHeap := by
          intro he
          apply hc
          have hh := congrArg storeOfSyntax he
          change storeOfSyntax (storeToSyntax name) = storeOfSyntax .currHeap at hh
          rw [storeOfSyntax_storeToSyntax] at hh
          exact hh
        have hm := StackRemove.StoreNames.nameCases (storeToSyntax name) hn
        have hh := heapSafe_wordListRev _ _ _ safe3.2 astore v
        apply hh
        apply List.mem_map.mpr
        refine ⟨storeToSyntax name, hm, ?_⟩
        simp only [storeOfSyntax_storeToSyntax, hv, Option.getD_some]
    · intro a ha
      apply safe1.1 a (source.memory a)
      rw [amem]
      exact ⟨a, ha, rfl⟩
  next hbad => contradiction

end InitECandidate.Solver.Wave8Stage.RuntimeLabels
