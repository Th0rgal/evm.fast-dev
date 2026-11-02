import InitECandidate.Solver.Wave8Stage.StackBitmapPrefix
import Flapjack.Compiler.Backend.StackProps.InstructionConstants
import Flapjack.Compiler.Backend.StackProps.SharedMemoryClock

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace InitECandidate.Solver.Wave8Stage.StackBitmapPrimitives
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemExpressions
open Flapjack.StackSemInst Flapjack.StackSemIntegerInstructions Flapjack.StackSemShMem
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

theorem wordExp_withBitmaps {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F)
    (y : WordLangExpHOL (BitVec width)) (bitmaps : List (BitVec width)) :
    wordExp { s with bitmaps := bitmaps } y = wordExp s y := by
  refine WordLangExpHOL.rec
    (motive_1 := fun e : WordLangExpHOL (BitVec width) =>
      wordExp { s with bitmaps := bitmaps } e = wordExp s e)
    (motive_2 := fun es : List (WordLangExpHOL (BitVec width)) =>
      ∀ e ∈ es, wordExp { s with bitmaps := bitmaps } e = wordExp s e)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ y
  · intro value; simp only [wordExp]
  · intro register; simp only [wordExp]
  · intro name; simp only [wordExp]
  · intro address ih
    simp only [wordExp, ih, memLoad]
  · intro operator arguments ih
    simp only [wordExp]
    have hmap : arguments.attach.map (fun e => wordExp { s with bitmaps := bitmaps } e.val) =
        arguments.attach.map (fun e => wordExp s e.val) := by
      apply List.map_congr_left
      intro e _
      exact ih e.val e.property
    rw [hmap]
  · intro operator left right ihLeft ihRight
    simp only [wordExp, ihLeft, ihRight]
  · intro e h; cases h
  · intro head tail ihHead ihTail e he
    rcases List.mem_cons.mp he with rfl | ht
    · exact ihHead
    · exact ihTail e ht

theorem assign_withBitmaps {width : Nat} [NeZero width] {C F : Type}
    (x : Nat) (y : WordLangExpHOL (BitVec width))
    (s : StackSemStateFiniteExact width C F) (bitmaps : List (BitVec width)) :
    assign x y { s with bitmaps := bitmaps } =
      (assign x y s).map (fun s => { s with bitmaps := bitmaps }) := by
  simp only [assign, wordExp_withBitmaps]
  cases wordExp s y <;> simp [setVar]

theorem inst_withBitmaps {width : Nat} [NeZero width] {C : Type} {F : Type}
    (i : HolInst width) (s : StackSemStateFiniteExact width C F) (bitmaps : List (BitVec width)) :
    instHOL i { s with bitmaps := bitmaps } =
      (instHOL i s).map (fun s => { s with bitmaps := bitmaps }) := by
  cases i <;> simp only [instHOL, instInteger, Option.join_some,
    assign_withBitmaps, wordExp_withBitmaps, getVar, StackSemStateOps.getVars,
    memLoad, memStore, setVar]
  all_goals repeat' (split <;> try simp_all)
  all_goals try simp_all

theorem shMemLoad_withBitmaps {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (a : BitVec width) (s : StackSemStateFiniteExact width C F)
    (bitmaps : List (BitVec width)) :
    shMemLoad r a { s with bitmaps := bitmaps } =
      Prod.map id (fun s => { s with bitmaps := bitmaps }) (shMemLoad r a s) := by
  simp only [shMemLoad]
  repeat' first | split | simp_all

theorem shMemStore_withBitmaps {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (a : BitVec width) (s : StackSemStateFiniteExact width C F)
    (bitmaps : List (BitVec width)) :
    shMemStore r a { s with bitmaps := bitmaps } =
      Prod.map id (fun s => { s with bitmaps := bitmaps }) (shMemStore r a s) := by
  simp only [shMemStore,getVar]
  repeat' first | split | simp_all

theorem shMemLoad32_withBitmaps {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (a : BitVec width) (s : StackSemStateFiniteExact width C F)
    (bitmaps : List (BitVec width)) :
    shMemLoad32 r a { s with bitmaps := bitmaps } =
      Prod.map id (fun s => { s with bitmaps := bitmaps }) (shMemLoad32 r a s) := by
  simp only [shMemLoad32]
  repeat' first | split | simp_all

theorem shMemStore32_withBitmaps {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (a : BitVec width) (s : StackSemStateFiniteExact width C F)
    (bitmaps : List (BitVec width)) :
    shMemStore32 r a { s with bitmaps := bitmaps } =
      Prod.map id (fun s => { s with bitmaps := bitmaps }) (shMemStore32 r a s) := by
  simp only [shMemStore32,getVar]
  repeat' first | split | simp_all

theorem shMemLoad16_withBitmaps {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (a : BitVec width) (s : StackSemStateFiniteExact width C F)
    (bitmaps : List (BitVec width)) :
    shMemLoad16 r a { s with bitmaps := bitmaps } =
      Prod.map id (fun s => { s with bitmaps := bitmaps }) (shMemLoad16 r a s) := by
  simp only [shMemLoad16]
  repeat' first | split | simp_all

theorem shMemStore16_withBitmaps {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (a : BitVec width) (s : StackSemStateFiniteExact width C F)
    (bitmaps : List (BitVec width)) :
    shMemStore16 r a { s with bitmaps := bitmaps } =
      Prod.map id (fun s => { s with bitmaps := bitmaps }) (shMemStore16 r a s) := by
  simp only [shMemStore16,getVar]
  repeat' first | split | simp_all

theorem shMemLoadByte_withBitmaps {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (a : BitVec width) (s : StackSemStateFiniteExact width C F)
    (bitmaps : List (BitVec width)) :
    shMemLoadByte r a { s with bitmaps := bitmaps } =
      Prod.map id (fun s => { s with bitmaps := bitmaps }) (shMemLoadByte r a s) := by
  simp only [shMemLoadByte]
  repeat' first | split | simp_all

theorem shMemStoreByte_withBitmaps {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (a : BitVec width) (s : StackSemStateFiniteExact width C F)
    (bitmaps : List (BitVec width)) :
    shMemStoreByte r a { s with bitmaps := bitmaps } =
      Prod.map id (fun s => { s with bitmaps := bitmaps }) (shMemStoreByte r a s) := by
  simp only [shMemStoreByte,getVar]
  repeat' first | split | simp_all

theorem shMemOp_withBitmaps {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (r : Nat) (a : BitVec width)
    (s : StackSemStateFiniteExact width C F) (bitmaps : List (BitVec width)) :
    shMemOp op r a { s with bitmaps := bitmaps } =
      Prod.map id (fun s => { s with bitmaps := bitmaps }) (shMemOp op r a s) := by
  cases op <;> simp only [shMemOp, shMemLoad_withBitmaps, shMemStore_withBitmaps,
    shMemLoadByte_withBitmaps, shMemStoreByte_withBitmaps, shMemLoad16_withBitmaps,
    shMemStore16_withBitmaps, shMemLoad32_withBitmaps, shMemStore32_withBitmaps]

#print axioms wordExp_withBitmaps
#print axioms inst_withBitmaps
#print axioms shMemOp_withBitmaps
end InitECandidate.Solver.Wave8Stage.StackBitmapPrimitives
