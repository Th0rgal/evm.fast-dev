import InitECandidate.Solver.SelfContainedStageBounds

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.InitCodeLayout
open Classical Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.Proofs
open InitCodeThm InitCodeCorrect

/-- A concrete word-list region may be framed by the rest of an arbitrary
memory domain. Extra domain entries need not describe bitmaps or code. -/
theorem framed_wordListExists {width : Nat} [NeZero width] {β : Type}
    (good : goodDimindex width) (memory : BitVec width → β)
    (domain : BitVec width → Prop) (base : BitVec width) (count : Nat)
    (bound : (width / 8) * count < 2 ^ width)
    (included : ∀ a, addresses base count a → domain a) :
    ∃ frame, SetSep.star frame (Misc.wordListExists base count)
      (SetSep.fun2Set (memory, domain)) := by
  let outside := SetSep.fun2Set (memory, fun a => domain a ∧ ¬ addresses base count a)
  refine ⟨(fun h => h = outside), outside,
    SetSep.fun2Set (memory, addresses base count), ?_, rfl,
    WordListMemory.wordListExistsAddresses memory count base ⟨bound,good⟩⟩
  constructor
  · funext entry
    rcases entry with ⟨a,v⟩
    apply propext
    simp only [outside,SetSep.fun2SetThm]
    constructor
    · rintro (⟨eq,ha,_⟩ | ⟨eq,ha⟩)
      · exact ⟨eq,ha⟩
      · exact ⟨eq,included a ha⟩
    · rintro ⟨eq,ha⟩
      by_cases inside : addresses base count a
      · exact .inr ⟨eq,inside⟩
      · exact .inl ⟨eq,ha,inside⟩
  · rintro ⟨a,v⟩ ⟨left,right⟩
    exact ((SetSep.fun2SetThm _ _ _ _).mp left).2.2
      ((SetSep.fun2SetThm _ _ _ _).mp right).2

/-- Initialization layout and heap preservation depend on the heap region and
entry 1 alone. In particular this theorem imposes no register bound, compiler
relation, bitmap-domain or oracle contract on the rest of the code. -/
theorem run_layout {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap pointer : Nat)
    (s : StackSemStateFiniteExact width C F)
    (p2 p3 p4 bp : BitVec width)
    (good : goodDimindex width) (k8 : 8 ≤ pointer)
    (read2 : s.regs.lookup 2 = some (.word p2))
    (read3 : s.regs.lookup 3 = some (.word p3))
    (read4 : s.regs.lookup 4 = some (.word p4))
    (mem0 : s.memory p2 = .word bp)
    (entry : sptDomain s.code 1)
    (maxOk : maxStackAlloc ≤ maxHeap)
    (le : p2.toNat ≤ p4.toNat)
    (big : (1024 * bytesInWord width).toNat ≤ (p4-p2).toNat)
    (al2 : holByteAligned p2 = true) (al4 : holByteAligned p4 = true)
    (P0 : ((BitVec width × WordLocW width) → Prop) → Prop)
    (heap : SetSep.star P0
      (Misc.wordListExists p2 ((p4-p2).toNat / (bytesInWord width).toNat))
      (SetSep.fun2Set (s.memory,fun a => s.mdomain a = true))) :
    let reg3 := roundedThird p2 (shrunkThird p2 (adjustedThird p3 (middleWord p2 p4)
      (p2 + marginWord width) (p4 - marginWord width)) (maxHeapWord width maxHeap))
    ∃ (t : StackSemStateFiniteExact width C F) (heapLength stackLength : Nat),
      StackSemEvaluate.evaluate (initCode generateGc maxHeap pointer,s) = (none,t) ∧
      t = {s with memory := t.memory,regs := t.regs} ∧
      reg3.toNat = p2.toNat + heapLength * (width/8) ∧
      p4.toNat = reg3.toNat + stackLength * (width/8) ∧
      heapLength % 2 = 0 ∧ heapLength ≤ maxHeap ∧ maxStackAlloc ≤ stackLength ∧
      t.regs.lookup 5 = some (.word ((reg3-p2) >>> (1 : Nat))) ∧
      t.regs.lookup (pointer+2) = some (.word p2) ∧
      t.regs.lookup pointer = some (.word (p4-bytesInWord width)) ∧
      t.regs.lookup (pointer+1) =
        some (.word (reg3 + bytesInWord width * BitVec.ofNat width storeList.length)) ∧
      (∀ a, addresses p2 heapLength a → s.memory a = t.memory a) := by
  intro reg3
  have a2 := (byteAligned_iff good p2).mp al2
  have a4 := (byteAligned_iff good p4).mp al4
  have bnat : (bytesInWord width).toNat = width / 8 := by
    rcases good with h | h <;> subst h <;> rfl
  have diff : (p4 - p2).toNat = p4.toNat - p2.toNat := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact le)]
  have big' : 1024 * (width / 8) ≤ p4.toNat - p2.toNat := by
    rw [← diff]
    have : (1024 * bytesInWord width).toNat = 1024 * (width / 8) := by
      rcases good with h | h <;> subst h <;> rfl
    omega
  have bpos : 0 < width / 8 := by rcases good with h | h <;> subst h <;> decide
  obtain ⟨adjLe, shrLe, heapLength, stackLength, regEqN, endEqN, even, heapLe, heapLow,
    stackLow⟩ := initLayout good maxHeap maxOk p2 p3 p4 le big' a2 a4
  have regEq := addMulOfNat good p2 reg3 heapLength regEqN
  have endEq := addMulOfNat good reg3 p4 stackLength endEqN
  have count : (p4 - p2).toNat / (bytesInWord width).toNat = heapLength + stackLength := by
    rw [diff, bnat, endEqN, regEqN]
    rw [show p2.toNat + heapLength * (width / 8) + stackLength * (width / 8) - p2.toNat =
      (heapLength + stackLength) * (width / 8) by rw [Nat.add_mul]; omega]
    exact Nat.mul_div_cancel _ bpos
  rw [count] at heap
  have long : storeList.length + 1 ≤ stackLength := by
    have : storeList.length = 48 := rfl
    simp only [maxStackAlloc] at stackLow; omega
  obtain ⟨heapValues, storeValues, restValues, last, hlen, slen, rlen, split⟩ :=
    initHeapSplit _ p2 reg3 p4 heapLength stackLength _ _ regEq endEq long heap
  set H := Misc.wordList p2 heapValues with hH
  set S := Misc.wordList reg3 storeValues with hS
  set R := Misc.wordList (reg3 + bytesInWord width * BitVec.ofNat width storeList.length)
    restValues with hR
  set D : BitVec width → Prop := fun a => s.mdomain a = true with hD
  -- header reads and domain
  have headerSplit : SetSep.star (SetSep.star (SetSep.star (SetSep.star P0 S) R)
      (SetSep.one (p4 - bytesInWord width, last))) H (SetSep.fun2Set (s.memory, D)) := by
    rw [show SetSep.star (SetSep.star (SetSep.star (SetSep.star P0 S) R)
      (SetSep.one (p4 - bytesInWord width, last))) H =
      SetSep.star (SetSep.star (SetSep.star (SetSep.star P0 H) S) R)
        (SetSep.one (p4 - bytesInWord width, last)) by ac_rfl]
    exact split
  have heapBig : 5 ≤ heapLength := by
    have : storeList.length = 48 := rfl
    simp only [maxStackAlloc] at heapLow; omega
  have domain5 : ∀ i, i < 5 →
      s.mdomain (p2 + BitVec.ofNat width i * bytesInWord width) = true := by
    intro i hi
    have := (framedListRead _ p2 heapValues s.memory D headerSplit i (by omega)).2
    rw [BitVec.mul_comm] at this
    exact this
  -- the final stack word
  have lastDomain : s.mdomain (p4 - bytesInWord width) = true := by
    obtain ⟨part, single, sub⟩ := starRightMember _ _ _ split
    have member := sub (p4 - bytesInWord width, last) (by rw [single])
    exact ((SetSep.fun2SetThm _ _ _ _).mp member).2
  have written := StoreListCodeThm.writeWord (.word 0) last (p4 - bytesInWord width)
    (SetSep.star (SetSep.star (SetSep.star P0 H) S) R) s.memory D
    (by rw [SetSep.starComm]; exact split)
  have storeHeap : SetSep.star S (SetSep.star (SetSep.star (SetSep.star P0 H) R)
      (SetSep.one (p4 - bytesInWord width, .word 0)))
      (SetSep.fun2Set ((fun key => if key = p4 - bytesInWord width then .word 0
        else s.memory key), D)) := by
    rw [show SetSep.star S (SetSep.star (SetSep.star (SetSep.star P0 H) R)
      (SetSep.one (p4 - bytesInWord width, .word 0))) =
      SetSep.star (SetSep.star (SetSep.star (SetSep.star P0 H) S) R)
        (SetSep.one (p4 - bytesInWord width, .word 0)) by ac_rfl]
    exact written
  obtain ⟨t, run, shape, t0, t1, t2, t3, t4, t5, t6, t7, tk, tk1, tk2, tOther, tHeap⟩ :=
    runInitCode generateGc maxHeap pointer s p2 p3 p4 bp _ _ _ _ good k8 read2 read3 read4
      domain5 mem0 rfl rfl rfl rfl lastDomain entry storeValues _ slen storeHeap
  refine ⟨t,heapLength,stackLength,run,shape,regEqN,endEqN,even,heapLe,
    stackLow,t5,tk2,tk,tk1,?_⟩
  have tHeapLast : SetSep.star (SetSep.star (SetSep.star
      (SetSep.star
        (Misc.wordList reg3 ((storeList.reverse.map (storeInit generateGc pointer)).map
          (MemVal.memVal t.regs))) P0) R)
      (SetSep.one (p4 - bytesInWord width,.word 0))) H
      (SetSep.fun2Set (t.memory,D)) := by
    rw [show SetSep.star (SetSep.star (SetSep.star
      (SetSep.star
        (Misc.wordList reg3 ((storeList.reverse.map (storeInit generateGc pointer)).map
          (MemVal.memVal t.regs))) P0) R)
      (SetSep.one (p4 - bytesInWord width,.word 0))) H =
      SetSep.star
        (Misc.wordList reg3 ((storeList.reverse.map (storeInit generateGc pointer)).map
          (MemVal.memVal t.regs)))
        (SetSep.star (SetSep.star (SetSep.star P0 H) R)
          (SetSep.one (p4 - bytesInWord width,.word 0))) by ac_rfl]
    exact tHeap
  intro a member
  obtain ⟨i,hi,rfl⟩ := (mem_addresses heapLength p2 a).mp member
  rw [BitVec.mul_comm]
  rw [(framedListRead _ p2 heapValues s.memory D headerSplit i (by omega)).1,
    (framedListRead _ p2 heapValues t.memory D tHeapLast i (by omega)).1]

/-- The reduced source heap/store fields follow from the computed pointer
layout, without the whole-program StackRemove simulation relation. -/
theorem reduced_layout {width : Nat} [NeZero width] {C F : Type}
    (generateGc jump : Bool) (bounds : BitVec width × BitVec width)
    (pointer : Nat) (code : Spt (HolProg width)) (bitmaps : List (BitVec width))
    (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (t : StackSemStateFiniteExact width C F)
    (p2 reg3 p4 : BitVec width) (heapLength stackLength : Nat)
    (good : goodDimindex width)
    (regEqN : reg3.toNat = p2.toNat + heapLength * (width/8))
    (endEqN : p4.toNat = reg3.toNat + stackLength * (width/8))
    (even : heapLength % 2 = 0) (long : 49 ≤ stackLength)
    (t5 : t.regs.lookup 5 = some (.word ((reg3-p2) >>> (1 : Nat))))
    (tk2 : t.regs.lookup (pointer+2) = some (.word p2))
    (tk : t.regs.lookup pointer = some (.word (p4-bytesInWord width)))
    (tk1 : t.regs.lookup (pointer+1) =
      some (.word (reg3 + bytesInWord width * BitVec.ofNat width storeList.length))) :
    let reduced := InitReduce.initReduce generateGc jump bounds pointer code bitmaps
      dataSpace oracle t
    reduced.store.lookup .currHeap = some (.word p2) ∧
    reduced.store.lookup .heapLength =
      some (.word (BitVec.ofNat width (heapLength/2) * bytesInWord width)) ∧
    reduced.mdomain = (fun a => decide (addresses p2 heapLength a)) ∧
    reduced.memory = t.memory ∧ reduced.ffi = t.ffi ∧ reduced.be = t.be ∧
    reduced.shMdomain = t.shMdomain := by
  intro reduced
  have space := (spaceCounts good p2 reg3 p4 heapLength stackLength regEqN endEqN long).1
  have half := halfHeapWord good p2 reg3 heapLength regEqN even
  have size : storeList.length = 48 := rfl
  refine ⟨?_,?_,?_,rfl,rfl,rfl,rfl⟩
  · simp [reduced,InitReduce.initReduce,HolFiniteMapExact.lookup_updateListEq,
      storeList,storeInit,FUPDATE_LIST_HOL,FUPDATE_HOL,
      StackSemRegisterTransfers.storeOfSyntax,holFapply_of_lookup tk2]
  · simp [reduced,InitReduce.initReduce,HolFiniteMapExact.lookup_updateListEq,
      storeList,storeInit,FUPDATE_LIST_HOL,FUPDATE_HOL,
      StackSemRegisterTransfers.storeOfSyntax,holFapply_of_lookup t5,half,BitVec.mul_comm]
  · simp only [reduced,InitReduce.initReduce]
    erw [holFapply_of_lookup tk2,holFapply_of_lookup tk1]
    simp only [wordSemTheWord,size,space]

#print axioms reduced_layout

#print axioms framed_wordListExists
#print axioms run_layout
end InitECandidate.Solver.Wave8Stage.InitCodeLayout
