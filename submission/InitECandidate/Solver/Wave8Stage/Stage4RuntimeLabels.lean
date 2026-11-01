import InitECandidate.Solver.SelfContainedStageBounds

set_option autoImplicit false

/-! Runtime-value groundwork for excluding indirect calls to the store-constants
stub. These lemmas do not assume that syntactic direct-call cleanliness alone
excludes an indirect target. Whole-evaluator preservation remains separate. -/
namespace InitECandidate.Solver.Wave8Stage.RuntimeLabels

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl

variable {width : Nat} [NeZero width]

/-- Words cannot denote code. A location is safe when its section is not bad. -/
def ValueSafe (bad : Nat) : WordLocW width → Prop
  | .word _ => True
  | .loc label _ => label ≠ bad

def MapSafe {K : Type} (bad : Nat) (m : HolFiniteMapExact K (WordLocW width)) : Prop :=
  ∀ k v, m.lookup k = some v → ValueSafe bad v

/-- All storage that can feed an indirect call. Memory outside mdomain is not
readable by StackSem and need not satisfy the invariant. -/
structure StateSafe {C F : Type} (bad : Nat) (s : StackSemStateFiniteExact width C F) : Prop where
  regs : MapSafe bad s.regs
  store : MapSafe bad s.store
  stack : ∀ v ∈ s.stack, ValueSafe bad v
  memory : ∀ a, s.mdomain a = true → ValueSafe bad (s.memory a)

theorem mapSafe_empty {K : Type} (bad : Nat) :
    MapSafe (width := width) bad (HolFiniteMapExact.empty : HolFiniteMapExact K _) := by
  intro k v h
  simp at h

theorem mapSafe_update {K : Type} [DecidableEq K] {bad : Nat} {m : HolFiniteMapExact K (WordLocW width)}
    (hm : MapSafe bad m) (k : K) (v : WordLocW width) (hv : ValueSafe bad v) :
    MapSafe bad (m.updateEq (k, v)) := by
  intro q w h
  rw [HolFiniteMapExact.lookup_updateEq] at h
  unfold FUPDATE_HOL at h
  split at h
  · cases h
    exact hv
  · exact hm q w h

theorem mapSafe_restrict {K : Type} {bad : Nat} {m : HolFiniteMapExact K (WordLocW width)}
    (hm : MapSafe bad m) (keep : K → Bool) : MapSafe bad (restrictIn m keep) := by
  intro k v h
  simp only [restrictIn_lookup] at h
  split at h
  · exact hm k v h
  · cases h

theorem StateSafe.withClock {C F : Type} {bad : Nat} {s : StackSemStateFiniteExact width C F}
    (h : StateSafe bad s) (k : Nat) : StateSafe bad { s with clock := k } :=
  ⟨h.regs, h.store, h.stack, h.memory⟩

theorem StateSafe.setVar_safe {C F : Type} {bad : Nat} {s : StackSemStateFiniteExact width C F}
    (h : StateSafe bad s) (r : Nat) (v : WordLocW width) (hv : ValueSafe bad v) :
    StateSafe bad (setVar r v s) :=
  ⟨mapSafe_update h.regs r v hv, h.store, h.stack, h.memory⟩

theorem StateSafe.setStore_safe {C F : Type} {bad : Nat} {s : StackSemStateFiniteExact width C F}
    (h : StateSafe bad s) (r : WordStoreHOL) (v : WordLocW width) (hv : ValueSafe bad v) :
    StateSafe bad (setStore r v s) :=
  ⟨h.regs, mapSafe_update h.store r v hv, h.stack, h.memory⟩

theorem StateSafe.emptyEnv_safe {C F : Type} {bad : Nat} {s : StackSemStateFiniteExact width C F}
    (h : StateSafe bad s) : StateSafe bad (emptyEnv s) :=
  ⟨mapSafe_empty bad, h.store, by intro v hv; exact False.elim (List.not_mem_nil hv), h.memory⟩

theorem StateSafe.memLoad_safe {C F : Type} {bad : Nat} {s : StackSemStateFiniteExact width C F}
    (h : StateSafe bad s) (a : BitVec width) (v : WordLocW width)
    (hl : memLoad a s = some v) : ValueSafe bad v := by
  unfold memLoad at hl
  split at hl
  · cases hl
    exact h.memory a (by assumption)
  · cases hl

theorem StateSafe.memStore_safe {C F : Type} {bad : Nat} {s post : StackSemStateFiniteExact width C F}
    (h : StateSafe bad s) (a : BitVec width) (v : WordLocW width) (hv : ValueSafe bad v)
    (hs : memStore a v s = some post) : StateSafe bad post := by
  unfold memStore at hs
  split at hs
  · cases hs
    refine ⟨h.regs, h.store, h.stack, ?_⟩
    intro b hb
    dsimp only
    split
    · exact hv
    · exact h.memory b hb
  · cases hs

theorem StateSafe.assign_safe {C F : Type} {bad : Nat} {s post : StackSemStateFiniteExact width C F}
    (h : StateSafe bad s) (r : Nat) (e : WordLangExpHOL (BitVec width))
    (he : StackSemExpressions.assign r e s = some post) : StateSafe bad post := by
  unfold StackSemExpressions.assign at he
  split at he
  · cases he
  · cases he
    exact h.setVar_safe _ _ trivial

/-- A successful indirect lookup chooses a non-bad section when register
values satisfy the runtime invariant. Direct targets need their own guard. -/
theorem findCode_safe_target {K A : Type} {bad : Nat}
    (regs : HolFiniteMapExact K (WordLocW width)) (code : Spt A)
    (dest : Nat ⊕ K) (body : A) (hr : MapSafe bad regs)
    (hd : ∀ n, dest = .inl n → n ≠ bad)
    (hl : findCode dest regs code = some body) :
    ∃ n, n ≠ bad ∧ sptLookup n code = some body := by
  cases dest with
  | inl n => exact ⟨n, hd n rfl, hl⟩
  | inr r =>
    simp only [findCode] at hl
    split at hl
    · rename_i n he
      exact ⟨n, hr r (.loc n 0) he, hl⟩
    · cases hl

/-- Replacing or removing bad's code entry leaves every safe lookup unchanged. -/
theorem findCode_eq_of_safe {K A : Type} {bad : Nat}
    (regs : HolFiniteMapExact K (WordLocW width)) (left right : Spt A)
    (dest : Nat ⊕ K) (hr : MapSafe bad regs)
    (hd : ∀ n, dest = .inl n → n ≠ bad)
    (hc : ∀ n, n ≠ bad → sptLookup n left = sptLookup n right) :
    findCode dest regs left = findCode dest regs right := by
  cases dest with
  | inl n => exact hc n (hd n rfl)
  | inr r =>
    simp only [findCode]
    split
    · rename_i n he
      exact hc n (hr r (.loc n 0) he)
    · rfl

#print axioms findCode_safe_target
#print axioms findCode_eq_of_safe
#print axioms StateSafe.memStore_safe
#print axioms StateSafe.assign_safe

end InitECandidate.Solver.Wave8Stage.RuntimeLabels
