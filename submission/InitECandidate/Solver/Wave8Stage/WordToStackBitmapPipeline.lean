import InitECandidate.Solver.Wave8Stage.StackBitmapNativeCompiler
import InitECandidate.Solver.Wave8Stage.WordToStackFallbackInitialization
import InitECandidate.Solver.Wave8Stage.WordCostPipelineCertificate

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace InitECandidate.Solver.Wave8Stage.WordToStackBitmapPipeline
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Pancake.PanLang
open StackBitmapNativeCompiler StackBitmapRefinement

private theorem zip_left {α β : Type} (a : α) (b : β) (as : List α) (bs : List β)
    (h : (a,b) ∈ as.zip bs) : a ∈ as := by
  induction as generalizing bs with
  | nil => simp at h
  | cons first rest ih =>
    cases bs with
    | nil => simp at h
    | cons next tail =>
      simp only [List.zip_cons_cons,List.mem_cons,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩ | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih tail h)

/-- Pan-to-Word does not create allocation or installation in any function,
including shadowed associations. -/
theorem pan_sourceSafe {width : Nat} [NeZero width] (isa : AsmArchitecture)
    (panCode : List (DeclHOL width)) :
    ∀ entry ∈ panToWordCompileProgHOL isa panCode, SourceSafe entry.2.2 := by
  intro entry member
  rcases entry with ⟨name,arity,body⟩
  constructor
  · rw [noInstallSubprogsHOL_eq_notCreated]
    apply LoopToWord.loop_to_word_compile_not_created_MEM name arity body _ _ member
    intro x hx
    cases x <;> simp_all
  · rw [noAllocSubprogsHOL_eq_notCreated]
    apply LoopToWord.loop_to_word_compile_not_created_MEM name arity body _ _ member
    intro x hx
    cases x <;> simp_all

/-- Every complete Word-to-Word output function retains both source-fragment
properties, uniformly over allocation oracles and cleanup. -/
theorem compile_sourceSafe {width : Nat} [NeZero width]
    (wc : WordToWord.Config) (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (guard : ∀ entry ∈ programs, SourceSafe entry.2.2) :
    ∀ entry ∈ (WordToWord.compile wc ac programs).2, SourceSafe entry.2.2 := by
  intro entry member
  change entry ∈ (programs.zip (WordToWord.nextNOracle programs.length wc.colOracle).1).map
    (WordToWord.fullCompileSingle ac.twoRegArith
      (ac.regCount - (5+ac.avoidRegs.length)) wc.regAlg ac) at member
  obtain ⟨⟨original,colour⟩,zipped,rfl⟩ := List.mem_map.mp member
  have before := guard original (zip_left original colour _ _ zipped)
  rcases original with ⟨name,arity,program⟩
  constructor
  · rw [noInstallSubprogsHOL_eq_notCreated,WordToWord.fullCompileSingle_eq]
    apply WordToWord.notCreated_removeMustTerminate
    apply WordConvs.compile_single_not_created_subprogs
    simpa only [noInstallSubprogsHOL_eq_notCreated] using before.1
  · rw [noAllocSubprogsHOL_eq_notCreated,WordToWord.fullCompileSingle_eq]
    apply WordToWord.notCreated_removeMustTerminate
    apply WordConvs.compile_single_not_created_subprogs
    simpa only [noAllocSubprogsHOL_eq_notCreated] using before.2

/-- The actual Pan-to-Word, Word-to-Word and native Word-to-Stack chain
produces code in the bitmap-refinement fragment. -/
theorem pipeline_codeSafe {width : Nat} [NeZero width]
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (panCode : List (DeclHOL width))
    (col : List (Option (Spt Nat)))
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (stackCode : List (Nat × HolProg width))
    (wtw : WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode) = (col,wordCode))
    (wts : WordToStack.Native.compileNative ac false wordCode = (bitmaps,wconf,fs,stackCode)) :
    CodeSafe (sptFromAList stackCode) := by
  have guard := compile_sourceSafe wc ac _ (pan_sourceSafe ac.isa panCode)
  rw [wtw] at guard
  have result := compile_codeSafe ac wordCode guard
  rwa [wts] at result

#print axioms pan_sourceSafe
#print axioms compile_sourceSafe
#print axioms pipeline_codeSafe
end InitECandidate.Solver.Wave8Stage.WordToStackBitmapPipeline
