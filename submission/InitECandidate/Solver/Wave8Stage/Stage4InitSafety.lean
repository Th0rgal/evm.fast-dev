import InitECandidate.Solver.Wave8Stage.Stage4CompiledSafety
import Flapjack.Compiler.Backend.StackRemove.Proofs.StoreNames

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8Stage.RuntimeLabels
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.StackSemStateOps
open Flapjack.StackSemEvaluate Flapjack.StackSemControl
variable {width : Nat} [NeZero width]

/-- Safety of the live storage used by the low-level initializer. Its disabled
abstract stack and store may still contain the original opaque HOL values. -/
structure CoreSafe {C F : Type} (bad : Nat) (s : StackSemStateFiniteExact width C F) : Prop where
  regs : MapSafe bad s.regs
  memory : MemorySafe bad s.mdomain s.memory

theorem CoreSafe.withClock {C F : Type} {bad : Nat} {s : StackSemStateFiniteExact width C F}
    (h : CoreSafe bad s) (k : Nat) : CoreSafe bad { s with clock := k } :=
  ⟨h.regs, h.memory⟩

theorem CoreSafe.setVar_safe {C F : Type} {bad : Nat} {s : StackSemStateFiniteExact width C F}
    (h : CoreSafe bad s) (r : Nat) (v : WordLocW width) (hv : ValueSafe bad v) :
    CoreSafe bad (setVar r v s) :=
  ⟨mapSafe_update h.regs r v hv, h.memory⟩

theorem CoreSafe.memLoad_safe {C F : Type} {bad : Nat} {s : StackSemStateFiniteExact width C F}
    (h : CoreSafe bad s) (a : BitVec width) (v : WordLocW width)
    (hl : memLoad a s = some v) : ValueSafe bad v := by
  unfold memLoad at hl
  split at hl
  · cases hl
    exact h.memory a (by assumption)
  · cases hl

theorem CoreSafe.memStore_safe {C F : Type} {bad : Nat} {s post : StackSemStateFiniteExact width C F}
    (h : CoreSafe bad s) (a : BitVec width) (v : WordLocW width) (hv : ValueSafe bad v)
    (hs : memStore a v s = some post) : CoreSafe bad post := by
  unfold memStore at hs
  split at hs
  · cases hs
    refine ⟨h.regs, ?_⟩
    intro b hb
    dsimp only
    split
    · exact hv
    · exact h.memory b hb
  · cases hs

theorem CoreSafe.assign_safe {C F : Type} {bad : Nat} {s post : StackSemStateFiniteExact width C F}
    (h : CoreSafe bad s) (r : Nat) (e : WordLangExpHOL (BitVec width))
    (he : StackSemExpressions.assign r e s = some post) : CoreSafe bad post := by
  unfold StackSemExpressions.assign at he
  split at he
  · cases he
  · cases he
    exact h.setVar_safe _ _ trivial

theorem CoreSafe.setVar_word {C F : Type} {bad : Nat}
    {s : StackSemStateFiniteExact width C F} (h : CoreSafe bad s)
    (r : Nat) (w : BitVec width) : CoreSafe bad (setVar r (.word w) s) :=
  h.setVar_safe r (.word w) trivial

/-- Every successful integer or memory instruction preserves the runtime
location invariant, including Or's register-copy case and byte/word writes. -/
theorem CoreSafe.instInteger_safe {C F : Type} {bad : Nat}
    {s post : StackSemStateFiniteExact width C F} (h : CoreSafe bad s)
    (i : HolInst width)
    (run : StackSemIntegerInstructions.instInteger i s = some (some post)) :
    CoreSafe bad post := by
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
    | exact ⟨h.regs, memStoreByte_safe h.memory _ _ _ (by assumption)⟩
    | exact ⟨h.regs, memStore32_safe h.memory _ _ _ (by assumption)⟩

theorem CoreSafe.instHOL_safe {C F : Type} {bad : Nat}
    {s post : StackSemStateFiniteExact width C F} (h : CoreSafe bad s)
    (i : HolInst width) (run : StackSemInst.instHOL i s = some post) :
    CoreSafe bad post := by
  have hi := StackSemInst.instHOL_coverage i s
  rw [run] at hi
  exact h.instInteger_safe i hi


/-- All successful or failing initializer executions preserve live storage safety. -/
theorem coreSafe_evaluate_neutral {C F : Type} {bad : Nat}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (hn : StackProps.clockNeutralHOL p) (hp : ProgramSafe bad p) (hs : CoreSafe bad s) :
    CoreSafe bad (evaluate (p, s)).2 := by
  cases he : p
  all_goals rw [he] at hn hp
  all_goals try simp only [ProgramSafe] at hp
  case seq a b =>
    obtain ⟨ha, hb⟩ := hp
    have h1 := coreSafe_evaluate_neutral a s hn.1 ha hs
    rw [evaluate_seq]
    generalize evaluate (a, s) = out at h1 ⊢
    obtain ⟨r, middle⟩ := out
    cases r with
    | some r => exact h1.withClock _
    | none => exact coreSafe_evaluate_neutral b _ hn.2 hb (h1.withClock _)
  case ite c r ri a b =>
    have h1 := coreSafe_evaluate_neutral a s hn.1 hp.1 hs
    have h2 := coreSafe_evaluate_neutral b s hn.2 hp.2 hs
    rw [evaluate_ite]
    repeat' split
    all_goals first | exact h1 | exact h2 | exact hs
  case inst i =>
    rw [evaluate_inst]
    split
    · exact hs.instHOL_safe i (by assumption)
    · exact hs
  case locValue r n l =>
    simp only [ProgramSafe, LeafAllowed] at hp
    rw [evaluate_locValue]
    split
    · exact hs.setVar_safe r (.loc n l) hp
    · exact hs
  case skip => simpa only [evaluate_skip] using hs
  case halt r =>
    rw [evaluate_halt]
    split
    · exact ⟨mapSafe_empty bad, hs.memory⟩
    · exact hs
  all_goals simp [StackProps.clockNeutralHOL] at hn
termination_by sizeOf p

private theorem programSafe_storeListCode (bad address temporary : Nat)
    (values : List (BitVec width ⊕ Nat)) :
    ProgramSafe bad (StackRemove.storeListCode address temporary values) := by
  induction values with
  | nil => simp [StackRemove.storeListCode, ProgramSafe, LeafAllowed]
  | cons v vs ih =>
    cases v <;> simp [StackRemove.storeListCode, listSeqHOL,
      addBytesInWordInst, ProgramSafe, LeafAllowed, ih]

/-- The real initializer only manufactures section 1. -/
theorem programSafe_initCode {bad : Nat} (hb : 1 ≠ bad)
    (generateGc : Bool) (maxHeap pointer : Nat) :
    ProgramSafe bad (StackRemove.initCode (width := width) generateGc maxHeap pointer) := by
  simp [StackRemove.initCode, StackRemove.initMemory, listSeqHOL, ProgramSafe,
    LeafAllowed, moveHOL, subInst, addInst, StackRemove.rightShiftInst,
    StackRemove.leftShiftInst, StackRemove.constInst, StackRemove.loadInst,
    StackRemove.storeInst, addBytesInWordInst, programSafe_storeListCode, hb]

theorem coreSafe_initCode {C F : Type} {bad : Nat} (hb : 1 ≠ bad)
    (generateGc : Bool) (maxHeap pointer : Nat) (s : StackSemStateFiniteExact width C F)
    (hs : CoreSafe bad s) :
    CoreSafe bad (evaluate (StackRemove.initCode generateGc maxHeap pointer, s)).2 :=
  coreSafe_evaluate_neutral _ s
    (StackRemove.Proofs.InitClock.initCodeClockNeutral generateGc maxHeap pointer)
    (programSafe_initCode hb generateGc maxHeap pointer) hs

#print axioms coreSafe_initCode
end InitECandidate.Solver.Wave8Stage.RuntimeLabels
