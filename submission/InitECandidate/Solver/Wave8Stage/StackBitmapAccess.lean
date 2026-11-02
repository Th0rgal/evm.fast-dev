import InitECandidate.Solver.Wave8Stage.StackBitmapPrefix
import Flapjack.Compiler.Backend.Semantics.StackSem.SizeBitmapCases

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace InitECandidate.Solver.Wave8Stage.StackBitmapAccess
open Flapjack Flapjack.StackSemStoreConsts Flapjack.StackSemStateOps
open Flapjack.StackSemSizeBitmapCases

/-- A successful constant store is unchanged by appending bitmap entries. -/
theorem storeConstSem_append {width : Nat} [NeZero width] {C F : Type}
    (t1 t2 : Nat) (s post : StackSemStateFiniteExact width C F)
    (extra : List (BitVec width))
    (run : storeConstSem (resultWidth := width) t1 t2 s = (none,post)) :
    storeConstSem (resultWidth := width) t1 t2 {s with bitmaps := s.bitmaps ++ extra} =
      (none,{post with bitmaps := post.bitmaps ++ extra}) := by
  unfold storeConstSem at run ⊢
  split at run
  · cases run
  · rename_i distinct
    rw [if_neg distinct]
    simp only [getVar] at run ⊢
    split at run
    · rename_i i a off h1 h2 h3
      cases copied : copyWordsExact i.toNat a off s.bitmaps (fun x => s.mdomain x = true) s.memory with
      | none => simp [copied] at run
      | some result =>
        rcases result with ⟨nextAddress,nextMemory⟩
        have same := StackBitmapPrefix.copyWords_append i.toNat a off s.bitmaps extra
          (fun x => s.mdomain x = true) s.memory _ copied
        simp only [same]
        simp only [copied,Prod.mk.injEq] at run
        obtain ⟨_,rfl⟩ := run
        cases s.useAlloc <;> simp [unsetVarZero,setVar]
    · cases run

/-- A successful indexed bitmap load observes the same prefix entry. -/
theorem bitmapLoad_append {width : Nat} [NeZero width] {C F : Type}
    (r v : Nat) (s post : StackSemStateFiniteExact width C F)
    (extra : List (BitVec width))
    (run : bitmapLoad r v s = (none,post)) :
    bitmapLoad r v {s with bitmaps := s.bitmaps ++ extra} =
      (none,{post with bitmaps := post.bitmaps ++ extra}) := by
  unfold bitmapLoad at run ⊢
  split at run
  · cases run
  · rename_i enabled
    rw [if_neg enabled]
    simp only [getVar] at run ⊢
    split at run
    · rename_i word lookup
      split at run
      · cases run
      · rename_i valid
        have small : word.toNat < s.bitmaps.length := by omega
        have large : ¬ (s.bitmaps ++ extra).length ≤ word.toNat := by
          simp only [List.length_append]; omega
        rw [dif_neg large,List.getElem_append_left small]
        simp only [Prod.mk.injEq] at run
        obtain ⟨_,rfl⟩ := run
        rfl
    · cases run

end InitECandidate.Solver.Wave8Stage.StackBitmapAccess
