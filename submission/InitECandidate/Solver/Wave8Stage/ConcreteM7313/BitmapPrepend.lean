import Flapjack.Compiler.Backend.WordToStack.NativePrograms

/-!
# Bitmap-prefix parametricity for `compileProgNative`

`insertBitmap ws (data, len)` only appends `.list ws` onto `data` and reads `len`
without inspecting `data`. Consequently, `compNative` and `compileProgNative`
commute with prepending an arbitrary `AppList` prefix onto the accumulated
bitmap accumulator, allowing every `Function{n}` and `Chunk{c}` in Stage 5 to be
certified from `(.nil, offset_n)` and composed at any upstream `AppList` state.
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack
open Flapjack.Compiler.Backend.WordToStack.Native

def prependAppList {α : Type} (prefixList : AppList α) : AppList α → AppList α
  | .nil => prefixList
  | .list xs => .append prefixList (.list xs)
  | .append a b => .append (prependAppList prefixList a) b

@[simp] theorem prependAppList_nil {α : Type} (prefixList : AppList α) :
    prependAppList prefixList .nil = prefixList := rfl

@[simp] theorem prependAppList_append {α : Type} (prefixList a b : AppList α) :
    prependAppList prefixList (.append a b) = .append (prependAppList prefixList a) b := rfl

theorem prependAppList_assoc {α : Type} (p q r : AppList α) :
    prependAppList p (prependAppList q r) = prependAppList (prependAppList p q) r := by
  induction r with
  | nil => rfl
  | list xs => rfl
  | append a b iha ihb =>
    simp only [prependAppList, iha]

theorem insertBitmap_prepend {α : Type} (ws : List α)
    (prefixList data : AppList α) (offset : Nat) :
    insertBitmap ws (prependAppList prefixList data, offset) =
      (((prependAppList prefixList (insertBitmap ws (data, offset)).1.1),
        (insertBitmap ws (data, offset)).1.2),
       (insertBitmap ws (data, offset)).2) := by
  rfl

theorem wLiveNative_prepend {width : Nat} [NeZero width]
    (live : Spt Unit × Spt Unit) (prefixList data : AppList (BitVec width))
    (offset : Nat) (kf : Nat × Nat × Nat) :
    wLiveNative live (prependAppList prefixList data, offset) kf =
      let r := wLiveNative live (data, offset) kf
      (r.1, (prependAppList prefixList r.2.1, r.2.2)) := by
  unfold wLiveNative
  by_cases h : kf.2.1 = 0
  · simp [h]
  · simp [h, insertBitmap]

theorem compNative_prepend {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (perf : Bool) (program : WordLangProgHOL (BitVec width))
    (prefixList data : AppList (BitVec width)) (offset : Nat)
    (kf : Nat × Nat × Nat) :
    compNative conf perf program (prependAppList prefixList data, offset) kf =
      let r := compNative conf perf program (data, offset) kf
      (r.1, (prependAppList prefixList r.2.1, r.2.2)) := by
  cases program with
  | skip => simp [compNative]
  | move _ _ => simp [compNative]
  | inst _ => simp [compNative]
  | assign _ _ => simp [compNative]
  | get _ _ => simp [compNative]
  | set name exp =>
    cases name <;> cases exp <;> simp [compNative]
  | store _ _ => simp [compNative]
  | mustTerminate p =>
    simpa [compNative] using compNative_prepend conf perf p prefixList data offset kf
  | call ret _ _ handler =>
    cases ret with
    | none => simp [compNative]
    | some retPayload =>
      rcases retPayload with ⟨_, live, retCode, _, _⟩
      cases handler with
      | none =>
        simp only [compNative, wLiveNative_prepend]
        rw [compNative_prepend conf perf retCode prefixList
          (wLiveNative live (data, offset) kf).2.1
          (wLiveNative live (data, offset) kf).2.2 kf]
      | some hPayload =>
        rcases hPayload with ⟨_, handleCode, _, _⟩
        simp only [compNative, wLiveNative_prepend]
        rw [compNative_prepend conf perf retCode prefixList
          (wLiveNative live (data, offset) kf).2.1
          (wLiveNative live (data, offset) kf).2.2 kf]
        rw [compNative_prepend conf perf handleCode prefixList
          (compNative conf perf retCode (wLiveNative live (data, offset) kf).2 kf).2.1
          (compNative conf perf retCode (wLiveNative live (data, offset) kf).2 kf).2.2 kf]
  | seq first second =>
    simp only [compNative]
    rw [compNative_prepend conf perf first prefixList data offset kf]
    rw [compNative_prepend conf perf second prefixList
      (compNative conf perf first (data, offset) kf).2.1
      (compNative conf perf first (data, offset) kf).2.2 kf]
  | ite cmp _ ri first second =>
    cases ri with
    | reg _ =>
      simp only [compNative]
      rw [compNative_prepend conf perf first prefixList data offset kf]
      rw [compNative_prepend conf perf second prefixList
        (compNative conf perf first (data, offset) kf).2.1
        (compNative conf perf first (data, offset) kf).2.2 kf]
    | imm i =>
      by_cases hv : conf.validImm (.inr cmp) i
      · simp only [compNative, hv, ↓reduceIte]
        rw [compNative_prepend conf perf first prefixList data offset kf]
        rw [compNative_prepend conf perf second prefixList
          (compNative conf perf first (data, offset) kf).2.1
          (compNative conf perf first (data, offset) kf).2.2 kf]
      · simp only [compNative, hv, Bool.false_eq_true, ↓reduceIte]
        rw [compNative_prepend conf perf first prefixList data offset kf]
        rw [compNative_prepend conf perf second prefixList
          (compNative conf perf first (data, offset) kf).2.1
          (compNative conf perf first (data, offset) kf).2.2 kf]
  | loop _ body _ =>
    simp only [compNative]
    rw [compNative_prepend conf perf body prefixList data offset kf]
  | alloc _ live =>
    simp only [compNative, wLiveNative_prepend]
  | storeConsts _ _ _ _ _ =>
    simp [compNative, insertBitmap]
  | raise _ => simp [compNative]
  | «return» _ _ => simp [compNative]
  | tick => simp [compNative]
  | opCurrHeap _ _ _ => simp [compNative]
  | locValue _ _ => simp [compNative]
  | install _ _ _ _ _ => simp [compNative]
  | codeBufferWrite _ _ => simp [compNative]
  | dataBufferWrite _ _ => simp [compNative]
  | ffi _ _ _ _ _ _ => simp [compNative]
  | shareInst _ _ exp =>
    simp only [compNative]
    cases expToAddrHOL exp <;> rfl
  | «break» _ => simp [compNative]
  | «continue» _ => simp [compNative]
termination_by sizeOf program

theorem compileProgNative_prepend {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (perf : Bool) (program : WordLangProgHOL (BitVec width))
    (argumentCount registerCount : Nat)
    (prefixList data : AppList (BitVec width)) (offset : Nat) :
    compileProgNative conf perf program argumentCount registerCount
        (prependAppList prefixList data, offset) =
      let r := compileProgNative conf perf program argumentCount registerCount (data, offset)
      (r.1, r.2.1, (prependAppList prefixList r.2.2.1, r.2.2.2)) := by
  unfold compileProgNative
  dsimp only
  rw [compNative_prepend]

theorem compileProgNative_from_nil {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (perf : Bool) (program : WordLangProgHOL (BitVec width))
    (argumentCount registerCount : Nat)
    (prefixList : AppList (BitVec width)) (offset : Nat)
    (body : HolProg width) (frame : Nat)
    (delta : AppList (BitVec width)) (nextOffset : Nat)
    (h : compileProgNative conf perf program argumentCount registerCount (.nil, offset) =
      (body, frame, (delta, nextOffset))) :
    compileProgNative conf perf program argumentCount registerCount (prefixList, offset) =
      (body, frame, (prependAppList prefixList delta, nextOffset)) := by
  have hp := compileProgNative_prepend conf perf program argumentCount registerCount
    prefixList .nil offset
  simpa only [prependAppList_nil, h] using hp

theorem compileWordToStackNative_prepend {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (registerCount : Nat)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (prefixList data : AppList (BitVec width)) (offset : Nat) :
    compileWordToStackNative conf perf registerCount programs
        (prependAppList prefixList data, offset) =
      let r := compileWordToStackNative conf perf registerCount programs (data, offset)
      (r.1, r.2.1, (prependAppList prefixList r.2.2.1, r.2.2.2)) := by
  induction programs generalizing data offset with
  | nil =>
    simp [compileWordToStackNative]
  | cons entry rest ih =>
    rcases entry with ⟨identifier, arguments, body⟩
    simp only [compileWordToStackNative, compileProgNative_prepend]
    rw [ih (compileProgNative conf perf body arguments registerCount (data, offset)).2.2.1
      (compileProgNative conf perf body arguments registerCount (data, offset)).2.2.2]

theorem compileWordToStackNative_from_nil {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (registerCount : Nat)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (prefixList : AppList (BitVec width)) (offset : Nat)
    (bodies : List (Nat × HolProg width)) (frames : List Nat)
    (delta : AppList (BitVec width)) (nextOffset : Nat)
    (h : compileWordToStackNative conf perf registerCount programs (.nil, offset) =
      (bodies, frames, (delta, nextOffset))) :
    compileWordToStackNative conf perf registerCount programs (prefixList, offset) =
      (bodies, frames, (prependAppList prefixList delta, nextOffset)) := by
  have hp := compileWordToStackNative_prepend conf perf registerCount programs
    prefixList .nil offset
  simpa only [prependAppList_nil, h] using hp

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
