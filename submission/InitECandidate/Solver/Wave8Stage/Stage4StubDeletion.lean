import InitECandidate.Solver.Wave8Stage.Stage4CodeTransport

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace InitECandidate.Solver.Wave8Stage.RuntimeLabels
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemEvaluate Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native
variable {width : Nat} [NeZero width]

/-- The installed store-constants stub retains its literal body through the
RawCall and StackAlloc passes. This uses the real compiler wrapper and stubs. -/
theorem rawCall_alloc_storeConstsStub_lookup (dc : DataToWord.Config)
    (raiseBody : HolProg width) (registers : Nat) (bodies : List (Nat × HolProg width)) :
    sptLookup storeConstsStubLocation (sptFromAList
      (StackAlloc.compile dc (StackRawCall.compile
        ((raiseStubLocation, raiseBody) ::
          (storeConstsStubLocation, storeConstsStubNative registers) :: bodies)))) =
      some (storeConstsStubNative registers) := by
  simp [StackAlloc.compile, StackAlloc.stubs, StackRawCall.compile,
    List.map, sptLookup_sptFromAList, sptAListLookup, StackAlloc.progComp,
    gcStubLocation, raiseStubLocation, storeConstsStubLocation, wordNumStubs, stackNumStubs,
    storeConstsStubNative, StackRawCall.compTop, StackRawCall.comp, StackAlloc.comp]

/-- Specialization to the actual WordToStack output, including its stubs. -/
theorem compiled_storeConstsStub_lookup (dc : DataToWord.Config)
    (conf : AsmConfigExact width) (perf : Bool)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    sptLookup storeConstsStubLocation (sptFromAList
      (StackAlloc.compile dc (StackRawCall.compile (compileNative conf perf programs).2.2.2))) =
      some (storeConstsStubNative (conf.regCount - (5 + conf.avoidRegs.length))) := by
  cases perf <;> simp only [compileNative, Bool.false_eq_true, ↓reduceIte]
  all_goals exact rawCall_alloc_storeConstsStub_lookup dc _ _ _

theorem storeConstsStub_no_internal_labels (registers n k : Nat) :
    ¬StackSem.getLabelsExact (storeConstsStubNative (width := width) registers) (n, k) := by
  simp [storeConstsStubNative, StackSem.getLabelsExact]

/-- Removing stub 6 from the real compiled table preserves all other lookups
and all valid labels outside section 6. -/
theorem compiled_without_stub_agreement (dc : DataToWord.Config)
    (conf : AsmConfigExact width) (perf : Bool)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    let entries := StackAlloc.compile dc (StackRawCall.compile (compileNative conf perf programs).2.2.2)
    CodeAgreement storeConstsStubLocation (sptFromAList entries)
      (sptFromAList (withoutSection storeConstsStubLocation entries)) := by
  apply withoutSection_agreement
  intro p hp n k hl
  rw [compiled_storeConstsStub_lookup] at hp
  cases hp
  exact False.elim (storeConstsStub_no_internal_labels _ _ _ hl)

/-- Exact whole-run deletion theorem for an excluded section. Runtime and
program safety remain explicit premises until the concrete initializer and
compiled user sections are connected. -/
theorem evaluate_withoutSection {C F : Type} {bad : Nat}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (entries : List (Nat × HolProg width)) (he : s.code = sptFromAList entries)
    (hp : ProgramSafe bad p) (hs : StateSafe bad s) (hc : CodeSafe bad s)
    (ho : ∀ i, (s.compileOracle i).2.1 = [])
    (hl : ∀ q, sptLookup bad (sptFromAList entries) = some q →
      ∀ n k, StackSem.getLabelsExact q (n, k) → n = bad) :
    evaluate (p, { s with code := sptFromAList (withoutSection bad entries) }) =
      replaceResultCode (sptFromAList (withoutSection bad entries)) (evaluate (p, s)) := by
  apply evaluate_withCode p s hp hs hc ho
  rw [he]
  exact withoutSection_agreement bad entries hl

/-- Specialization with the actual unfiltered StackAlloc table. The label
agreement needed for deletion is discharged from the compiler equations. -/
theorem compiled_evaluate_without_stub {C F : Type}
    (dc : DataToWord.Config) (conf : AsmConfigExact width) (perf : Bool)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (he : s.code = sptFromAList
      (StackAlloc.compile dc (StackRawCall.compile (compileNative conf perf programs).2.2.2)))
    (hp : ProgramSafe storeConstsStubLocation p)
    (hs : StateSafe storeConstsStubLocation s) (hc : CodeSafe storeConstsStubLocation s)
    (ho : ∀ i, (s.compileOracle i).2.1 = []) :
    let entries := StackAlloc.compile dc (StackRawCall.compile (compileNative conf perf programs).2.2.2)
    (evaluate (p, { s with code := sptFromAList (withoutSection storeConstsStubLocation entries) })).1 =
      (evaluate (p, s)).1 := by
  have hag := compiled_without_stub_agreement dc conf perf programs
  dsimp only at hag
  rw [← he] at hag
  have heq := congrArg Prod.fst (evaluate_withCode p s hp hs hc ho _ hag)
  exact heq

#print axioms compiled_storeConstsStub_lookup
#print axioms compiled_without_stub_agreement
#print axioms compiled_evaluate_without_stub
end InitECandidate.Solver.Wave8Stage.RuntimeLabels
