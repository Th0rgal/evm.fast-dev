import InitECandidate.Solver.Wave8Stage.Static.PanToStackAllocIdentityAndUnconditionalNoGcCall
import InitECandidate.Solver.Wave8Stage.Stage4CompiledSafety

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8Stage.AllocIdentity
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.Wave8Stage.Static
open PanToStackRawCallNoAllocAndStackAllocStructural
open PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc
open PanToStackAllocIdentityAndUnconditionalNoGcCall
open StackToLabAndLabToTargetNoLocValue6
variable {width : Nat} [NeZero width]

private theorem rawCall_progComp_id (info : Spt Nat) (n : Nat) (p : HolProg width)
    (ha : StackNoAlloc (StackRawCall.compTop info p) = true)
    (hs : JC p = true) (ht : NoTailHandler p = true) :
    StackAlloc.progComp (n, StackRawCall.compTop info p) = (n, StackRawCall.compTop info p) := by
  simp only [StackAlloc.progComp]
  rw [stackAllocComp_id _ _ _ ha (of_clean (c_rawCallCompTop info p hs)).1
    (th_rawCallCompTop info p ht)]

/-- StackAlloc is the identity on all RawCall sections, including the actual
untagged store-constants stub. This does not claim that the added GC stub is
unreachable or that changing the allocation flag preserves evaluation. -/
theorem rawCall_alloc_progComp_id (conf : AsmConfigExact width) (perf : Bool)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (hn : ∀ x ∈ programs, WordPassesPreserveNoStoreConsts.NoSt x.2.2 = true ∧ NSL x.2.2 = true)
    (ha : ∀ y ∈ StackRawCall.compile (compileNative conf perf programs).2.2.2,
      StackNoAlloc y.2 = true) :
    ∀ y ∈ StackRawCall.compile (compileNative conf perf programs).2.2.2,
      StackAlloc.progComp y = y := by
  intro y hy
  have hay := ha y hy
  simp only [StackRawCall.compile] at hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  unfold compileNative at hx
  dsimp only at hx
  rcases List.mem_cons.mp hx with rfl | hx
  · apply rawCall_progComp_id _ _ _ hay
    · cases perf <;> rfl
    · cases perf <;> rfl
  rcases List.mem_cons.mp hx with rfl | hx
  · simp [storeConstsStubNative, StackRawCall.compTop, StackRawCall.comp,
      StackAlloc.progComp, StackAlloc.comp]
  · apply rawCall_progComp_id _ _ _ hay
    · exact n_compileWordToStack conf perf _ programs _ hn x hx
    · exact h_compileWordToStack conf perf _ programs _ (fun e he => (hn e he).1) x hx

/-- Exact list equation for the real Pancake StackAlloc pass. It only prepends
its GC stub; every existing RawCall section is left literally unchanged. -/
theorem pancake_alloc_compile_eq (dc : DataToWord.Config) (conf : AsmConfigExact width)
    (perf : Bool) (wc : WordToWord.Config) (arch : AsmArchitecture)
    (source : List (Pancake.PanLang.DeclHOL width)) :
    let code := StackRawCall.compile (compileNative conf perf
      (WordToWord.compile wc conf (panToWordCompileProgHOL arch source)).2).2.2.2
    StackAlloc.compile dc code = StackAlloc.stubs dc ++ code := by
  intro code
  unfold StackAlloc.compile
  congr 1
  conv_rhs => rw [← List.map_id code]
  apply List.map_congr_left
  exact rawCall_alloc_progComp_id conf perf _
    (fun e he => ⟨PanToStackNoStoreConsts.panToWordToWord_NoSt arch source wc conf e he,
      panToWordToWord_NSL arch source wc conf e he⟩)
    (panToStackRawCall_noAlloc_unconditional arch source wc conf perf)

end InitECandidate.Solver.Wave8Stage.AllocIdentity
