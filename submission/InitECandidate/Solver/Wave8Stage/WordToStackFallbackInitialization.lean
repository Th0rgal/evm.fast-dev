import InitECandidate.Solver.Wave8Stage.WordToStackCompileBudget
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GcFunOk

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace InitECandidate.Solver.Wave8Stage.WordToStackFallbackInitialization
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open WordToStackProofs.InitializationStateRel StackRemove.Proofs.InitMake

/-- The native Word initializer never observes its target's bitmap table. -/
theorem makeInit_withBitmaps {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k : Nat) (s : StackSemStateFiniteExact width C F)
    (bitmaps : List (BitVec width)) (code : Spt (Nat × WordLangProgHOL (BitVec width)))
    (oracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    WordToStack.Native.Initialization.makeInit ac k {s with bitmaps := bitmaps} code oracle =
      WordToStack.Native.Initialization.makeInit ac k s code oracle := rfl

/-- Replacing the fallback's short table by a valid full table restores the
complete native initialization contract. This uses the actual optional
initializer's failure branch and the actual StackAlloc initializer. -/
theorem fallback_initStateOk {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (dc : DataToWord.Config) (k : Nat) (cfg : C)
    (generateGc jump : Bool) (maxHeap dataSpace pointer : Nat)
    (bounds : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (lowerCode code : Spt (HolProg width)) (s : StackSemStateFiniteExact width C F)
    (dimension : goodDimindex width) (widthBound : 8 ≤ width) (registers : 4 < k)
    (bitmapBound : bitmaps.length + 1 < 2 ^ width)
    (bitmapPrefix : [(4 : BitVec width)] <+: bitmaps)
    (failed : makeInitOpt generateGc maxHeap bitmaps dataSpace (fun _ => (cfg, [], []))
      jump bounds pointer lowerCode s = none) :
    initStateOk ac k
      {StackAlloc.makeInit dc code (fun _ => (cfg, [], []))
        (makeInitAny generateGc maxHeap bitmaps dataSpace (fun _ => (cfg, [], []))
          jump bounds pointer lowerCode s) with bitmaps := bitmaps}
      (fun _ => ((bitmaps.length,cfg), [])) := by
  have stackBound : 1 < 2 ^ width := by omega
  simp only [makeInitAny,failed,StackAlloc.makeInit,initStateOk]
  refine ⟨registers,dimension,widthBound,True.intro,True.intro,True.intro,
    DataToWord.Proofs.Gc.gcFunOkWordGcFun,by simp,?_,bitmapBound,bitmapPrefix,
    stackBound,rfl,?_,?_,?_,?_⟩
  · simp [FUPDATE_HOL]
  · simp [StackRemove.storeList,StackSemRegisterTransfers.storeOfSyntax,FUPDATE_LIST_HOL_cons,FUPDATE_HOL]
  · simpa using bitmapBound
  · funext index
    simp [WordToStack.Native.compileWordToStackNative,appListAppend,appendAux]
  · intro index
    simp

#print axioms makeInit_withBitmaps
#print axioms fallback_initStateOk
end InitECandidate.Solver.Wave8Stage.WordToStackFallbackInitialization
