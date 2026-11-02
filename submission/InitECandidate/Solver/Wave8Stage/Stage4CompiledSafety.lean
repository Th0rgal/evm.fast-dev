import InitECandidate.Solver.Wave8Stage.Stage4StubDeletion
import InitECandidate.Solver.Wave8Stage.Static.StackToLabAndLabToTargetNoLocValue6

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace InitECandidate.Solver.Wave8Stage.RuntimeLabels
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackRemove
open InitECandidate.Solver.Wave8Stage.Static.StackToLabAndLabToTargetNoLocValue6
variable {width : Nat} [NeZero width]

/-- StackAlloc removes allocation primitives and preserves the stronger
syntactic exclusion of section 6, including freshly created return labels. -/
theorem programSafe_allocComp : ∀ (n m : Nat) (p : HolProg width),
    n ≠ storeConstsStubLocation → JC p = true →
    ProgramSafe storeConstsStubLocation (StackAlloc.comp n m p).1
  | n, m, .seq a b, hn, h => by
    simp only [JC, Bool.and_eq_true] at h
    rw [StackAlloc.comp]
    simp only [ProgramSafe]
    exact ⟨programSafe_allocComp n m a hn h.1, programSafe_allocComp n _ b hn h.2⟩
  | n, m, .ite c r ri a b, hn, h => by
    simp only [JC, Bool.and_eq_true] at h
    rw [StackAlloc.comp]
    simp only [ProgramSafe]
    exact ⟨programSafe_allocComp n m a hn h.1, programSafe_allocComp n _ b hn h.2⟩
  | n, m, .loop a, hn, h => by
    rw [StackAlloc.comp]
    simp only [ProgramSafe]
    exact programSafe_allocComp n m a hn h
  | n, m, .call none d e, hn, h => by
    rw [StackAlloc.comp]
    cases e with
    | none => cases d <;> simp_all [JC, sH, sRet, sHd, labOk, tgtOk6, ProgramSafe]
    | some e =>
      obtain ⟨q, h1, h2⟩ := e
      cases d <;> simp_all [JC, sH, sRet, sHd, labOk, tgtOk6, ProgramSafe]
  | n, m, .call (some (p1, lr, l1, l2)) d none, hn, h => by
    simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true, Bool.and_true] at h
    have hi := programSafe_allocComp n m p1 hn h.2
    rw [StackAlloc.comp]
    cases d <;> simp_all [ProgramSafe, tgtOk6]
  | n, m, .call (some (p1, lr, l1, l2)) d (some (p2, k1, k2)), hn, h => by
    simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true] at h
    have hi := programSafe_allocComp n m p1 hn h.1.2
    have hj := programSafe_allocComp n (StackAlloc.comp n m p1).2 p2 hn h.2
    rw [StackAlloc.comp]
    cases d <;> simp_all [ProgramSafe, tgtOk6]
  | n, m, .alloc _, hn, h => by
    rw [StackAlloc.comp]
    simp [ProgramSafe, LeafAllowed, gcStubLocation, storeConstsStubLocation,
      wordNumStubs, stackNumStubs] at hn ⊢
    exact hn
  | n, m, .storeConsts .., hn, h => by simp [JC] at h
  | n, m, .skip, hn, h | n, m, .inst .., hn, h | n, m, .get .., hn, h
  | n, m, .set .., hn, h | n, m, .opCurrHeap .., hn, h | n, m, .jumpLower .., hn, h
  | n, m, .raise .., hn, h | n, m, .ret .., hn, h | n, m, .break .., hn, h
  | n, m, .continue .., hn, h | n, m, .ffi .., hn, h | n, m, .tick, hn, h
  | n, m, .locValue .., hn, h | n, m, .install .., hn, h | n, m, .shMemOp .., hn, h
  | n, m, .codeBufferWrite .., hn, h | n, m, .dataBufferWrite .., hn, h
  | n, m, .rawCall .., hn, h | n, m, .stackAlloc .., hn, h | n, m, .stackFree .., hn, h
  | n, m, .stackStore .., hn, h | n, m, .stackStoreAny .., hn, h
  | n, m, .stackLoad .., hn, h | n, m, .stackLoadAny .., hn, h
  | n, m, .stackGetSize .., hn, h | n, m, .stackSetSize .., hn, h
  | n, m, .bitmapLoad .., hn, h | n, m, .halt .., hn, h => by
    simp_all [StackAlloc.comp, ProgramSafe, LeafAllowed, JC]
termination_by _ _ p => sizeOf p
decreasing_by all_goals (simp_wf <;> omega)

theorem programSafe_gcStub (conf : DataToWord.Config) :
    ∀ e ∈ StackAlloc.stubs (width := width) conf, ProgramSafe storeConstsStubLocation e.2 := by
  intro e he
  simp only [StackAlloc.stubs, List.mem_cons, List.not_mem_nil, or_false] at he
  subst he
  cases h : conf.gcKind with
  | generational sizes =>
    rcases sizes with _ | ⟨g, gs⟩ <;>
      simp [ProgramSafe, LeafAllowed, StackAlloc.memcpyCode, StackAlloc.clearTopInst, StackAlloc.wordGcMoveCode, StackAlloc.wordGcMoveListCode, StackAlloc.wordGcMoveLoopCode, StackAlloc.wordGcMoveBitmapCode, StackAlloc.wordGcMoveBitmapsCode, StackAlloc.wordGcMoveRootsBitmapsCode, StackAlloc.wordGenGcMoveCode, StackAlloc.wordGenGcPartialMoveCode, StackAlloc.wordGenGcMoveBitmapCode, StackAlloc.wordGenGcPartialMoveBitmapCode, StackAlloc.wordGenGcMoveBitmapsCode, StackAlloc.wordGenGcPartialMoveBitmapsCode, StackAlloc.wordGenGcMoveRootsBitmapsCode, StackAlloc.wordGenGcPartialMoveRootsBitmapsCode, StackAlloc.wordGenGcMoveListCode, StackAlloc.wordGenGcPartialMoveListCode, StackAlloc.wordGenGcMoveDataCode, StackAlloc.wordGenGcPartialMoveRefListCode, StackAlloc.wordGenGcPartialMoveDataCode, StackAlloc.wordGenGcMoveRefsCode, StackAlloc.wordGenGcMoveLoopCode, StackAlloc.wordGcPartialOrFull, StackAlloc.setNewTrigger, StackAlloc.wordGcCode,
      add1Inst, addBytesInWordInst, addInst, andInst, constInst, div2Inst, haltInst, leftShiftInst, listSeqHOL, loadInst, moveHOL, orInst, rightShiftInst, storeInst, sub1Inst, subInst, whileHOL, xorInst, h]
  | _ => simp [ProgramSafe, LeafAllowed, StackAlloc.memcpyCode, StackAlloc.clearTopInst, StackAlloc.wordGcMoveCode, StackAlloc.wordGcMoveListCode, StackAlloc.wordGcMoveLoopCode, StackAlloc.wordGcMoveBitmapCode, StackAlloc.wordGcMoveBitmapsCode, StackAlloc.wordGcMoveRootsBitmapsCode, StackAlloc.wordGenGcMoveCode, StackAlloc.wordGenGcPartialMoveCode, StackAlloc.wordGenGcMoveBitmapCode, StackAlloc.wordGenGcPartialMoveBitmapCode, StackAlloc.wordGenGcMoveBitmapsCode, StackAlloc.wordGenGcPartialMoveBitmapsCode, StackAlloc.wordGenGcMoveRootsBitmapsCode, StackAlloc.wordGenGcPartialMoveRootsBitmapsCode, StackAlloc.wordGenGcMoveListCode, StackAlloc.wordGenGcPartialMoveListCode, StackAlloc.wordGenGcMoveDataCode, StackAlloc.wordGenGcPartialMoveRefListCode, StackAlloc.wordGenGcPartialMoveDataCode, StackAlloc.wordGenGcMoveRefsCode, StackAlloc.wordGenGcMoveLoopCode, StackAlloc.wordGcPartialOrFull, StackAlloc.setNewTrigger, StackAlloc.wordGcCode,
      add1Inst, addBytesInWordInst, addInst, andInst, constInst, div2Inst, haltInst, leftShiftInst, listSeqHOL, loadInst, moveHOL, orInst, rightShiftInst, storeInst, sub1Inst, subInst, whileHOL, xorInst, h]


/-- Every non-store-constants section of the actual compiled table is safe. -/
theorem compiled_codeSafe {C F : Type} (dc : DataToWord.Config)
    (conf : AsmConfigExact width) (perf : Bool)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : ∀ x ∈ programs,
      Static.WordPassesPreserveNoStoreConsts.NoSt x.2.2 = true ∧ NSL x.2.2 = true)
    (s : StackSemStateFiniteExact width C F)
    (he : s.code = sptFromAList
      (StackAlloc.compile dc (StackRawCall.compile (compileNative conf perf programs).2.2.2))) :
    CodeSafe storeConstsStubLocation s := by
  intro n p hn hp
  rw [he, sptLookup_sptFromAList] at hp
  have hm := sptAListLookup_mem _ _ _ hp
  simp only [StackAlloc.compile, List.mem_append] at hm
  rcases hm with hm | hm
  · exact programSafe_gcStub dc (n, p) hm
  · obtain ⟨e, he, heq⟩ := List.mem_map.mp hm
    rcases e with ⟨name, body⟩
    simp only [StackAlloc.progComp, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [StackRawCall.compile] at he
    obtain ⟨q, hq, hqeq⟩ := List.mem_map.mp he
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hqeq
    apply programSafe_allocComp _ _ _ hn
    apply c_rawCallCompTop
    rcases c_compileNative conf perf programs h q hq with hbad | hclean
    · exact False.elim (hn hbad)
    · exact hclean

/-- Compiler syntax discharges the full table's code-safety premise for
arbitrary Pancake source declarations. -/
theorem pancake_compiled_codeSafe {C F : Type} (dc : DataToWord.Config)
    (conf : AsmConfigExact width) (perf : Bool) (wc : WordToWord.Config)
    (arch : AsmArchitecture) (source : List (Pancake.PanLang.DeclHOL width))
    (s : StackSemStateFiniteExact width C F)
    (he : s.code = sptFromAList
      (StackAlloc.compile dc (StackRawCall.compile
        (compileNative conf perf (WordToWord.compile wc conf
          (panToWordCompileProgHOL arch source)).2).2.2.2))) :
    CodeSafe storeConstsStubLocation s := by
  apply compiled_codeSafe dc conf perf _ _ s he
  intro x hx
  exact ⟨Static.PanToStackNoStoreConsts.panToWordToWord_NoSt arch source wc conf x hx,
    panToWordToWord_NSL arch source wc conf x hx⟩

/-- The actual compiler table can lose the store-constants stub without
changing an entry result. Only runtime safety and oracle emptiness remain. -/
theorem pancake_entry_without_stub {C F : Type} (dc : DataToWord.Config)
    (conf : AsmConfigExact width) (perf : Bool) (wc : WordToWord.Config)
    (arch : AsmArchitecture) (source : List (Pancake.PanLang.DeclHOL width))
    (s : StackSemStateFiniteExact width C F) (start : Nat)
    (he : s.code = sptFromAList
      (StackAlloc.compile dc (StackRawCall.compile
        (compileNative conf perf (WordToWord.compile wc conf
          (panToWordCompileProgHOL arch source)).2).2.2.2)))
    (hs : StateSafe storeConstsStubLocation s) (hn : start ≠ storeConstsStubLocation)
    (ho : ∀ i, (s.compileOracle i).2.1 = []) :
    let entries := StackAlloc.compile dc (StackRawCall.compile
      (compileNative conf perf (WordToWord.compile wc conf
        (panToWordCompileProgHOL arch source)).2).2.2.2)
    (StackSemEvaluate.evaluate
      (.call none (.inl start) none,
        { s with code := sptFromAList (withoutSection storeConstsStubLocation entries) })).1 =
      (StackSemEvaluate.evaluate (.call none (.inl start) none, s)).1 := by
  apply compiled_evaluate_without_stub dc conf perf _ _ s he
  · simp [ProgramSafe, hn]
  · exact hs
  · exact pancake_compiled_codeSafe dc conf perf wc arch source s he
  · exact ho



end InitECandidate.Solver.Wave8Stage.RuntimeLabels
