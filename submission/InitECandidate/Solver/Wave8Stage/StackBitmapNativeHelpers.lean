import InitECandidate.Solver.Wave8Stage.StackBitmapRefinement
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace InitECandidate.Solver.Wave8Stage.StackBitmapNativeHelpers
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm WordToStack.Native StackBitmapRefinement


theorem moves_safe {width : Nat} [NeZero width]
    (xs : List (Sum Nat Nat × Sum Nat Nat)) (kf : Nat × Nat × Nat) :
    Safe (wMoveAuxNative xs kf : HolProg width) := by
  have single (xy : Sum Nat Nat × Sum Nat Nat) :
      Safe (wMoveSingleNative (width := width) xy kf) := by
    rcases xy with ⟨x, y⟩
    cases x <;> cases y <;> simp [wMoveSingleNative, Safe]
  induction xs with
  | nil => simp [wMoveAuxNative, Safe]
  | cons xy xs ih =>
    cases xs with
    | nil => exact single xy
    | cons y ys => simp [wMoveAuxNative, Safe, single, ih]


theorem loads_safe {width : Nat} [NeZero width]
    (ls : List (Nat × Nat)) (prog : HolProg width) :
    Safe (wStackLoadNative ls prog) = Safe prog := by
  induction ls with
  | nil => rfl
  | cons pair ls ih =>
    rcases pair with ⟨r, i⟩
    simp [wStackLoadNative, Safe, ih]


theorem write1_safe {width : Nat} [NeZero width]
    (prog : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (h : ∀ reg, Safe (prog reg)) :
    Safe (wRegWrite1Native prog r kf) := by
  simp only [wRegWrite1Native]
  split <;> simp [Safe, h]


theorem write2_safe {width : Nat} [NeZero width]
    (prog : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (h : ∀ reg, Safe (prog reg)) :
    Safe (wRegWrite2Native prog r kf) := by
  simp only [wRegWrite2Native]
  split <;> simp [Safe, h]


theorem live_safe {width : Nat} [NeZero width]
    (live : Spt Unit × Spt Unit) (bs : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) :
    Safe (wLiveNative live bs kf).1 := by
  simp only [wLiveNative]
  split <;> simp [Safe]


theorem stackMove_safe {width : Nat} [NeZero width]
    (n start offset i : Nat) (p : HolProg width) :
    Safe (stackMoveNative n start offset i p) = Safe p := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [stackMoveNative, Safe, ih]


theorem copyRetAux_safe {width : Nat} [NeZero width] (k f n : Nat) :
    Safe (copyRetAuxNative k f n : HolProg width) := by
  induction n with
  | zero => simp [copyRetAuxNative, Safe]
  | succ n ih => simp [copyRetAuxNative, listSeq, Safe, ih]



theorem copyRet_safe {width : Nat} [NeZero width] {β γ : Type}
    (perf b : Bool) (kf : Nat × Nat × γ) (vs : List β) (kont : HolProg width) :
    Safe (copyRetNative perf b kf vs kont) ↔ Safe kont := by
  simp only [copyRetNative]
  split
  · rfl
  · simp only [Safe, copyRetAux_safe]
    simp only [seqStackFreeNative]
    split <;> simp [Safe]


theorem inst_safe {width : Nat} [NeZero width]
    (instruction : HolInst width) (frame : Nat × Nat × Nat) :
    Safe (wInstNative instruction frame) := by
  have write1 (g : Nat → HolInst width) (r : Nat) :
      Safe (wRegWrite1Native (fun reg => .inst (g reg)) r frame) :=
    write1_safe _ r frame (fun _ => by trivial)
  have write21 (g : Nat → Nat → HolInst width) (r1 r2 : Nat) :
      Safe (wRegWrite2Native
        (fun reg2 => wRegWrite1Native (fun reg1 => .inst (g reg1 reg2)) r1 frame)
        r2 frame) :=
    write2_safe _ r2 frame (fun reg2 => write1 (fun reg1 => g reg1 reg2) r1)
  cases instruction with
  | arith a =>
    cases a <;> try (rename_i op d s ri; cases ri)
    all_goals simp [wInstNative, loads_safe, write1, Safe]
  | mem op d addr =>
    cases addr
    cases op <;> simp [wInstNative, loads_safe,
      write1, Safe]
  | skip => trivial
  | const n c => simp [wInstNative, write1]


theorem dest_safe {width : Nat} [NeZero width]
    (dest : Option Nat) (args : List Nat) (frame : Nat × Nat × Nat) :
    Safe (callDestNative (width := width) dest args frame).1 := by
  cases dest with
  | some d => trivial
  | none =>
    simp only [callDestNative]
    split <;> simp [loads_safe, Safe]


theorem share_safe {width : Nat} [NeZero width]
    (op : HolMemop) (v : Nat) (addr : HolAddr width) (frame : Nat × Nat × Nat) :
    Safe (wShareInstNative op v addr frame) := by
  cases addr
  cases op <;> simp only [wShareInstNative, loads_safe]
  all_goals first
    | exact write1_safe _ _ _ (fun _ => by trivial)
    | trivial


end InitECandidate.Solver.Wave8Stage.StackBitmapNativeHelpers
