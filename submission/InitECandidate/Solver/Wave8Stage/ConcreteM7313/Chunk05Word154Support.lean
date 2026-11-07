import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Oracle154
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151Support
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151Allocation

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open BackendDecomposition Chunk05Stack151

def seqTreeList : List RegAlloc.ClashTree → RegAlloc.ClashTree → RegAlloc.ClashTree
  | [], tail => tail
  | t :: ts, tail => .seq t (seqTreeList ts tail)

theorem clash_seqList : (ps : List (WordLangProgHOL (BitVec 64))) → (tail : WordLangProgHOL (BitVec 64)) →
    WordAlloc.getClashTree (seqList ps tail) [] =
      seqTreeList (ps.map (fun p => WordAlloc.getClashTree p [])) (WordAlloc.getClashTree tail [])
  | [], _ => rfl
  | p :: ps, tail => by
    simp only [seqList, List.map_cons, seqTreeList, WordAlloc.getClashTree, clash_seqList ps tail]

def checkTreeList (f : Nat → Nat) : List RegAlloc.ClashTree → Option (Spt Unit × Spt Unit) →
    Option (Spt Unit × Spt Unit)
  | [], st => st
  | t :: ts, st =>
      match checkTreeList f ts st with
      | none => none
      | some (out, col) => RegAlloc.checkClashTree f t out col

theorem checkClashTree_seqTreeList (f : Nat → Nat) :
    (ts : List RegAlloc.ClashTree) → (tail : RegAlloc.ClashTree) →
    (live col : Spt Unit) →
    RegAlloc.checkClashTree f (seqTreeList ts tail) live col =
      checkTreeList f ts (RegAlloc.checkClashTree f tail live col)
  | [], tail, live, col => rfl
  | t :: ts, tail, live, col => by
    simp only [seqTreeList, RegAlloc.checkClashTree, checkClashTree_seqTreeList f ts tail live col, checkTreeList]
    rfl

theorem applyColour_seqList (f : Nat → Nat) :
    (ps : List (WordLangProgHOL (BitVec 64))) → (tail : WordLangProgHOL (BitVec 64)) →
    WordAlloc.applyColour f (seqList ps tail) =
      seqList (ps.map (WordAlloc.applyColour f)) (WordAlloc.applyColour f tail)
  | [], _ => rfl
  | p :: ps, tail => by
    simp only [seqList, List.map_cons, WordAlloc.applyColour, applyColour_seqList f ps tail]

theorem everyStackVar_seqList (pred : Nat → Bool) :
    (ps : List (WordLangProgHOL (BitVec 64))) → (tail : WordLangProgHOL (BitVec 64)) →
    everyStackVarHOL pred (seqList ps tail) =
      (ps.all (everyStackVarHOL pred) && everyStackVarHOL pred tail)
  | [], tail => by simp [seqList]
  | p :: ps, tail => by
    simp only [seqList, List.all_cons, everyStackVarHOL, everyStackVar_seqList pred ps tail, Bool.and_assoc]

theorem getForced_append : (c : AsmConfigExact 64) → (p : WordLangProgHOL (BitVec 64)) →
    (acc1 acc2 : List (Nat × Nat)) →
    WordAlloc.getForced c p (acc1 ++ acc2) = WordAlloc.getForced c p acc1 ++ acc2
  | c, .inst i, acc1, acc2 => by
    cases i with
    | arith a =>
      cases a <;> simp only [WordAlloc.getForced] <;> repeat (first | split | simp [List.append_assoc])
    | _ => simp [WordAlloc.getForced]
  | c, .mustTerminate s1, acc1, acc2 => by
    rw [WordAlloc.getForced, WordAlloc.getForced, getForced_append c s1 acc1 acc2]
  | c, .seq s1 s2, acc1, acc2 => by
    rw [WordAlloc.getForced, WordAlloc.getForced, getForced_append c s2 acc1 acc2, getForced_append c s1 _ acc2]
  | c, .ite _ _ _ e2 e3, acc1, acc2 => by
    rw [WordAlloc.getForced, WordAlloc.getForced, getForced_append c e3 acc1 acc2, getForced_append c e2 _ acc2]
  | c, .call ret _ _ h, acc1, acc2 => by
    cases ret with
    | none => simp [WordAlloc.getForced]
    | some r =>
      rcases r with ⟨_, _, retHandler, _, _⟩
      cases h with
      | none =>
        simp only [WordAlloc.getForced]
        exact getForced_append c retHandler acc1 acc2
      | some hh =>
        rcases hh with ⟨_, prog, _, _⟩
        simp only [WordAlloc.getForced]
        rw [getForced_append c retHandler acc1 acc2, getForced_append c prog _ acc2]
  | c, .loop _ body _, acc1, acc2 => by
    rw [WordAlloc.getForced, WordAlloc.getForced, getForced_append c body acc1 acc2]
  | _, .skip, _, _ => by simp [WordAlloc.getForced]
  | _, .move _ _, _, _ => by simp [WordAlloc.getForced]
  | _, .assign _ _, _, _ => by simp [WordAlloc.getForced]
  | _, .get _ _, _, _ => by simp [WordAlloc.getForced]
  | _, .set _ _, _, _ => by simp [WordAlloc.getForced]
  | _, .store _ _, _, _ => by simp [WordAlloc.getForced]
  | _, .alloc _ _, _, _ => by simp [WordAlloc.getForced]
  | _, .storeConsts _ _ _ _ _, _, _ => by simp [WordAlloc.getForced]
  | _, .raise _, _, _ => by simp [WordAlloc.getForced]
  | _, .return _ _, _, _ => by simp [WordAlloc.getForced]
  | _, .tick, _, _ => by simp [WordAlloc.getForced]
  | _, .locValue _ _, _, _ => by simp [WordAlloc.getForced]
  | _, .install _ _ _ _ _, _, _ => by simp [WordAlloc.getForced]
  | _, .codeBufferWrite _ _, _, _ => by simp [WordAlloc.getForced]
  | _, .dataBufferWrite _ _, _, _ => by simp [WordAlloc.getForced]
  | _, .ffi _ _ _ _ _ _, _, _ => by simp [WordAlloc.getForced]
  | _, .shareInst _ _ _, _, _ => by simp [WordAlloc.getForced]
  | _, .opCurrHeap _ _ _, _, _ => by simp [WordAlloc.getForced]
  | _, .break _, _, _ => by simp [WordAlloc.getForced]
  | _, .continue _, _, _ => by simp [WordAlloc.getForced]

theorem forced_seqList (c : AsmConfigExact 64) (pred : Nat × Nat → Bool) :
    (ps : List (WordLangProgHOL (BitVec 64))) → (tail : WordLangProgHOL (BitVec 64)) →
    (WordAlloc.getForced c (seqList ps tail) []).all pred =
      (ps.all (fun p => (WordAlloc.getForced c p []).all pred) &&
        (WordAlloc.getForced c tail []).all pred)
  | [], tail => by simp [seqList]
  | p :: ps, tail => by
    simp only [seqList, List.all_cons]
    rw [WordAlloc.getForced]
    have h := getForced_append c p [] (WordAlloc.getForced c (seqList ps tail) [])
    rw [List.nil_append] at h
    rw [h, List.all_append, forced_seqList c pred ps tail, Bool.and_assoc]

abbrev stackPred : Nat → Bool := fun x => decide (2 * registers ≤ x)
abbrev forcedPred (col : Spt Nat) : Nat × Nat → Bool :=
  fun (x, y) => WordAlloc.totalColour col x != WordAlloc.totalColour col y

theorem step_word154 (ps colPs progs : List (WordLangProgHOL (BitVec 64)))
    (ts : List RegAlloc.ClashTree)
    (cur tail : WordLangProgHOL (BitVec 64))
    (treeTail : RegAlloc.ClashTree)
    (chkIn chkOut : Option (Spt Unit × Spt Unit))
    (mB mT : Nat) (hols : List (HolProg 64)) (bodyT : HolProg 64)
    (st stOut : AppList (BitVec 64) × Nat)
    (hdef : cur = seqList ps tail)
    (htrees : ps.map (fun p => WordAlloc.getClashTree p []) = ts)
    (htreeT : WordAlloc.getClashTree tail [] = treeTail)
    (hchkT : RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) treeTail .ln .ln = chkIn)
    (hchkB : checkTreeList (WordAlloc.totalColour (oracle154.getD .ln)) ts chkIn = chkOut)
    (hcolPs : ps.map (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln))) = colPs)
    (hsB : colPs.all (everyStackVarHOL stackPred) = true)
    (hsT : everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) tail) = true)
    (hfB : ps.all (fun p => (WordAlloc.getForced riscvConfig p []).all (forcedPred (oracle154.getD .ln))) = true)
    (hfT : (WordAlloc.getForced riscvConfig tail []).all (forcedPred (oracle154.getD .ln)) = true)
    (hprogs : ps.map (transform oracle154) = progs)
    (hmB : maxListProg progs = mB)
    (hmT : maxVarHOL (transform oracle154 tail) = mT)
    (hcB : compList riscvConfig false (22, 13, 12) progs st = (hols, st))
    (hcT : WordToStack.Native.compNative riscvConfig false (transform oracle154 tail) st (22, 13, 12) = (bodyT, stOut)) :
    WordAlloc.getClashTree cur [] = seqTreeList ts treeTail ∧
    RegAlloc.checkClashTree (WordAlloc.totalColour (oracle154.getD .ln)) (seqTreeList ts treeTail) .ln .ln = chkOut ∧
    everyStackVarHOL stackPred (WordAlloc.applyColour (WordAlloc.totalColour (oracle154.getD .ln)) cur) = true ∧
    (WordAlloc.getForced riscvConfig cur []).all (forcedPred (oracle154.getD .ln)) = true ∧
    maxVarHOL (transform oracle154 cur) = max mB mT ∧
    WordToStack.Native.compNative riscvConfig false (transform oracle154 cur) st (22, 13, 12) = (seqHolList hols bodyT, stOut) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hdef, clash_seqList, htrees, htreeT]
  · rw [checkClashTree_seqTreeList, hchkT, hchkB]
  · rw [hdef, applyColour_seqList, everyStackVar_seqList, hcolPs, hsB, hsT]; rfl
  · rw [hdef, forced_seqList, hfB, hfT]; rfl
  · exact step_seqList oracle154 riscvConfig false (22, 13, 12) st ps progs cur tail mB mT hols bodyT stOut
      hdef hprogs hmB hmT hcB hcT

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Word154
