import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Oracle151
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BackendDecomposition
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.StackCompileComposition
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.BitmapPrepend
import InitECandidate.Solver.Wave8Stage.CertifiedKernelPasses

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

noncomputable def transform (col : Option (Spt Nat)) (p : WordLangProgHOL (BitVec 64)) : WordLangProgHOL (BitVec 64) :=
  WordRemove.removeMustTerminate
    (WordAlloc.applyColour (WordAlloc.totalColour (col.getD .ln)) p)

theorem transform_seq (col : Option (Spt Nat)) (p q : WordLangProgHOL (BitVec 64)) :
    transform col (.seq p q) = .seq (transform col p) (transform col q) := rfl

def seqList : List (WordLangProgHOL (BitVec 64)) → WordLangProgHOL (BitVec 64) → WordLangProgHOL (BitVec 64)
  | [], tail => tail
  | p :: ps, tail => .seq p (seqList ps tail)

def seqHolList : List (HolProg 64) → HolProg 64 → HolProg 64
  | [], tail => tail
  | p :: ps, tail => .seq p (seqHolList ps tail)

theorem transform_seqList (col : Option (Spt Nat)) :
    (ps : List (WordLangProgHOL (BitVec 64))) → (tail : WordLangProgHOL (BitVec 64)) →
    transform col (seqList ps tail) = seqList (ps.map (transform col)) (transform col tail)
  | [], _ => rfl
  | p :: ps, tail => by
    simp only [seqList, List.map_cons, transform_seq, transform_seqList col ps tail]

def maxListProg : List (WordLangProgHOL (BitVec 64)) → Nat
  | [] => 0
  | p :: ps => max (maxVarHOL p) (maxListProg ps)

theorem maxVarHOL_seqList : (ps : List (WordLangProgHOL (BitVec 64))) → (tail : WordLangProgHOL (BitVec 64)) →
    maxVarHOL (seqList ps tail) = max (maxListProg ps) (maxVarHOL tail)
  | [], tail => by simp [seqList, maxListProg]
  | p :: ps, tail => by
    simp only [seqList, maxListProg, maxVarHOL, maxVarHOL_seqList ps tail, Nat.max_assoc]

def compList (conf : AsmConfigExact 64) (perf : Bool) (kf : Nat × Nat × Nat) :
    List (WordLangProgHOL (BitVec 64)) → AppList (BitVec 64) × Nat → List (HolProg 64) × (AppList (BitVec 64) × Nat)
  | [], st => ([], st)
  | p :: ps, st =>
      let r1 := WordToStack.Native.compNative conf perf p st kf
      let r2 := compList conf perf kf ps r1.2
      (r1.1 :: r2.1, r2.2)

theorem compNative_seqList (conf : AsmConfigExact 64) (perf : Bool) (kf : Nat × Nat × Nat) :
    (ps : List (WordLangProgHOL (BitVec 64))) → (tail : WordLangProgHOL (BitVec 64)) →
    (st : AppList (BitVec 64) × Nat) →
    WordToStack.Native.compNative conf perf (seqList ps tail) st kf =
      let r1 := compList conf perf kf ps st
      let r2 := WordToStack.Native.compNative conf perf tail r1.2 kf
      (seqHolList r1.1 r2.1, r2.2)
  | [], tail, st => rfl
  | p :: ps, tail, st => by
    simp only [seqList, compList, WordToStack.Native.compNative,
      compNative_seqList conf perf kf ps tail, seqHolList]

theorem step_seqList (col : Option (Spt Nat)) (conf : AsmConfigExact 64) (perf : Bool) (kf : Nat × Nat × Nat)
    (st : AppList (BitVec 64) × Nat)
    (ps progs : List (WordLangProgHOL (BitVec 64)))
    (cur tail : WordLangProgHOL (BitVec 64))
    (mB mT : Nat) (hols : List (HolProg 64)) (bodyT : HolProg 64) (stOut : AppList (BitVec 64) × Nat)
    (hdef : cur = seqList ps tail)
    (hprogs : ps.map (transform col) = progs)
    (hmB : maxListProg progs = mB)
    (hmT : maxVarHOL (transform col tail) = mT)
    (hcB : compList conf perf kf progs st = (hols, st))
    (hcT : WordToStack.Native.compNative conf perf (transform col tail) st kf = (bodyT, stOut)) :
    maxVarHOL (transform col cur) = max mB mT ∧
    WordToStack.Native.compNative conf perf (transform col cur) st kf = (seqHolList hols bodyT, stOut) := by
  rw [hdef, transform_seqList, hprogs]
  refine ⟨?_, ?_⟩
  · rw [maxVarHOL_seqList, hmB, hmT]
  · rw [compNative_seqList, hcB]; dsimp only; rw [hcT]

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151
