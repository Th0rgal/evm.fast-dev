import InitECandidate.Solver.Wave8Stage.Stage4AllocFields
import InitECandidate.Solver.Wave8Stage.Stage4CodeExtension
import InitECandidate.Solver.Wave8Stage.Stage4AllocIdentity

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8Stage.AllocClock
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.Wave8Stage.RuntimeLabels
variable {width : Nat} [NeZero width]

/-- StackAlloc extends an allocation-free table without changing existing
lookups, provided the GC section name is not already used. -/
theorem alloc_code_extension (dc : DataToWord.Config) (code : List (Nat × HolProg width))
    (hid : ∀ e ∈ code, StackAlloc.progComp e = e)
    (hn : ∀ e ∈ code, e.1 ≠ gcStubLocation) :
    CodeExtension (sptFromAList code) (sptFromAList (StackAlloc.compile dc code)) := by
  have hmap : code.map StackAlloc.progComp = code := by
    conv_rhs => rw [← List.map_id code]
    exact List.map_congr_left hid
  intro n p hp
  rw [sptLookup_sptFromAList] at hp ⊢
  have hm := sptAListLookup_mem _ _ _ hp
  have hne := hn (n, p) hm
  simp only [StackAlloc.compile, hmap, StackAlloc.stubs, List.cons_append, List.nil_append,
    sptAListLookup, hne, ↓reduceIte]
  exact hp

/-- The allocation-removal boundary consumes no extra clock when the table
is unchanged by progComp and its source run cannot reach store-constants.
The collector, allocation flag and installation callbacks are transported
semantically, rather than inferred from the code identity. -/
theorem makeInit_entry_result {C F : Type}
    (dc : DataToWord.Config) (code : List (Nat × HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (s : StackSemStateFiniteExact width C F) (start k : Nat)
    (hid : ∀ e ∈ code, StackAlloc.progComp e = e)
    (hn : ∀ e ∈ code, e.1 ≠ gcStubLocation)
    (hs : StateSafe storeConstsStubLocation s)
    (hc : CodeSafe storeConstsStubLocation s)
    (hcode : s.code = sptFromAList (StackAlloc.compile dc code))
    (hstack : s.useStack = true)
    (ho : ∀ i, (s.compileOracle i).2.1 = [])
    (ho' : ∀ i, (oracle i).2.1 = [])
    (hstart : start ≠ storeConstsStubLocation)
    (hne : (StackSemEvaluate.evaluate (.call none (.inl start) none,
      { StackAlloc.makeInit dc (sptFromAList code) oracle s with clock := k })).1 ≠ some .error) :
    (StackSemEvaluate.evaluate (.call none (.inl start) none, { s with clock := k })).1 =
    (StackSemEvaluate.evaluate (.call none (.inl start) none,
      { StackAlloc.makeInit dc (sptFromAList code) oracle s with clock := k })).1 := by
  let raw : StackSemStateFiniteExact width C F := { s with code := sptFromAList code, clock := k }
  let source := { StackAlloc.makeInit dc (sptFromAList code) oracle s with clock := k }
  have ext : CodeExtension raw.code s.code := by
    rw [hcode]
    exact alloc_code_extension dc code hid hn
  have hr : StateSafe storeConstsStubLocation raw := ⟨hs.regs, hs.store, hs.stack, hs.memory⟩
  have hcr : CodeSafe storeConstsStubLocation raw := fun n p hn hp => hc n p hn (ext n p hp)
  have hp : ProgramSafe storeConstsStubLocation (.call none (.inl start) none : HolProg width) := by
    simp [ProgramSafe, hstart]
  have heq : AllocFields.override raw source = source := by
    simp only [AllocFields.override, raw, source, StackAlloc.makeInit, hstack]
  have fields := congrArg Prod.fst (AllocFields.evaluate_withAllocFields
    (.call none (.inl start) none) raw hp hr hcr ho source ho')
  change (StackSemEvaluate.evaluate (.call none (.inl start) none, AllocFields.override raw source)).1 =
    (StackSemEvaluate.evaluate (.call none (.inl start) none, raw)).1 at fields
  rw [heq] at fields
  have hnraw : (StackSemEvaluate.evaluate (.call none (.inl start) none, raw)).1 ≠ some .error := by
    rw [← fields]
    exact hne
  have added := congrArg Prod.fst (evaluate_extendCode (.call none (.inl start) none)
    raw hp hr hcr ho s.code ext hnraw)
  have hstate : { raw with code := s.code } = { s with clock := k } := rfl
  rw [hstate] at added
  exact added.trans fields.symm

end InitECandidate.Solver.Wave8Stage.AllocClock
