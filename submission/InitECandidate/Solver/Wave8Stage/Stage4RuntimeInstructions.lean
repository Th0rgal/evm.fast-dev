import InitECandidate.Solver.Wave8Stage.Stage4RuntimeLabels

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Stage.RuntimeLabels
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps
variable {width : Nat} [NeZero width]

def MemorySafe (bad : Nat) (domain : BitVec width → Bool)
    (memory : BitVec width → WordLocW width) : Prop :=
  ∀ a, domain a = true → ValueSafe bad (memory a)

theorem memStoreByte_safe {bad : Nat} {domain : BitVec width → Bool}
    {memory next : BitVec width → WordLocW width}
    (hm : MemorySafe bad domain memory) (be : Bool) (addr : BitVec width) (byte : BitVec 8)
    (hr : memStoreByteAuxExact memory domain be addr byte = some next) :
    MemorySafe bad domain next := by
  unfold memStoreByteAuxExact at hr
  split at hr
  · split at hr
    · cases hr
      intro a ha
      dsimp only
      split
      · trivial
      · exact hm a ha
    · cases hr
  · cases hr

theorem memStore32_safe {bad : Nat} {domain : BitVec width → Bool}
    {memory next : BitVec width → WordLocW width}
    (hm : MemorySafe bad domain memory) (be : Bool) (addr : BitVec width) (word : BitVec 32)
    (hr : memStore32Exact memory domain be addr word = some next) :
    MemorySafe bad domain next := by
  unfold memStore32Exact at hr
  split at hr
  · split at hr
    · split at hr
      · cases hr
        intro a ha
        dsimp only
        split
        · trivial
        · exact hm a ha
      · cases hr
    · cases hr
  · cases hr

theorem StateSafe.setVar_word {C F : Type} {bad : Nat}
    {s : StackSemStateFiniteExact width C F} (h : StateSafe bad s)
    (r : Nat) (w : BitVec width) : StateSafe bad (setVar r (.word w) s) :=
  h.setVar_safe r (.word w) trivial

/-- Every successful integer or memory instruction preserves the runtime
location invariant, including Or's register-copy case and byte/word writes. -/
theorem StateSafe.instInteger_safe {C F : Type} {bad : Nat}
    {s post : StackSemStateFiniteExact width C F} (h : StateSafe bad s)
    (i : HolInst width)
    (run : StackSemIntegerInstructions.instInteger i s = some (some post)) :
    StateSafe bad post := by
  cases i <;> simp only [StackSemIntegerInstructions.instInteger] at run
  all_goals repeat' (split at run)
  all_goals try contradiction
  all_goals simp only [Option.some.injEq] at run
  all_goals first
    | exact h.assign_safe _ _ run
    | skip
  all_goals cases run
  all_goals first
    | exact h
    | exact h.setVar_safe _ _ trivial
    | exact (h.setVar_word _ _).setVar_word _ _
    | exact h.setVar_safe _ _ (h.regs _ _ (by assumption))
    | exact h.setVar_safe _ _ (h.memLoad_safe _ _ (by assumption))
    | exact h.memStore_safe _ _ (h.regs _ _ (by assumption)) (by assumption)
    | exact ⟨h.regs, h.store, h.stack, memStoreByte_safe h.memory _ _ _ (by assumption)⟩
    | exact ⟨h.regs, h.store, h.stack, memStore32_safe h.memory _ _ _ (by assumption)⟩

theorem StateSafe.instHOL_safe {C F : Type} {bad : Nat}
    {s post : StackSemStateFiniteExact width C F} (h : StateSafe bad s)
    (i : HolInst width) (run : StackSemInst.instHOL i s = some post) :
    StateSafe bad post := by
  have hi := StackSemInst.instHOL_coverage i s
  rw [run] at hi
  exact h.instInteger_safe i hi

#print axioms StateSafe.instInteger_safe
#print axioms StateSafe.instHOL_safe
end InitECandidate.Solver.Wave8Stage.RuntimeLabels
