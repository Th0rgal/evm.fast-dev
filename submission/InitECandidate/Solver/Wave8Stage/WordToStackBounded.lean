import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Raise

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
A quantitative strengthening of Flapjack's complete constructor simulation.
The proof of the Raise constructor is adapted from the pinned Flapjack
CompCorrect/Raise.lean, retaining every premise and the full result relation.
Only the additional bound on its actual clock witness is new.
-/

namespace InitECandidate.Solver.Wave8Stage.WordToStackBounded
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.Raise

def SimulationB {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (program : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) (bound : Nat) : Prop :=
  ∀ (k f frame : Nat)
    (sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat),
    (WordSemStateFiniteExact.evaluate program source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k program = true ∧ flatExpConventions program = true ∧
      compNative ac false program (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL program < 2 * frame + 2 * k) →
    ∃ (extraClock : Nat), extraClock ≤ bound ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens

theorem compCorrectRaise {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (name : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    SimulationB ac (.raise name) source 1 := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  have compiledEq := congrArg Prod.fst compilation
  simp only [compNative] at compiledEq
  subst compiled
  have nameEq : name = 2 := by
    simp only [postAllocConventionsHOL, Bool.and_eq_true] at conventions
    simpa [callArgConventionHOL] using conventions.2.2
  subst name
  obtain ⟨value,l1,l2,valueEq,jump,resultEq⟩ :=
    sourceRaiseSuccess 2 source sourcePost result execution notError
  obtain ⟨size,nonGc,gc,oldHandler,rest,sourceBound,suffix,postEq⟩ :=
    sourceHandlerFrame source sourcePost l1 l2 jump
  obtain ⟨offset,saved,postRelation,handler,offsetWidth,space,location,savedWord⟩ :=
    fullRaisePostRelation ac k f frame source target lens size nonGc gc oldHandler l1 l2 rest
      related sourceBound suffix
  have parts : target.useStack = true ∧ target.useStore = true ∧ 4 < k ∧
      sptLookup raiseStubLocation target.code = some (@raiseStubNative width _ false k) := by
    simp only [stateRel] at related
    tauto
  have placed : target.regs.lookup 1 = some value := by
    have placement : ∀ n v, sptLookup n source.locals = some v →
        n % 2 = 0 ∧ if n / 2 < k then target.regs.lookup (n / 2) = some v
        else ((target.stack.drop target.stackSpace).take f)[f - 1 - (n / 2 - k)]? =
          some v ∧ n / 2 < k + frame := by
      simp only [stateRel,Nat.add_zero] at related
      repeat' (rcases related with ⟨_,related⟩)
      exact related
    have observed := placement 2 value valueEq
    simpa [show 1 < k by omega] using observed.2
  refine ⟨1, Nat.le_refl 1, unwindTarget target k offset l1 l2 saved,some (.exception (.loc l1 l2)),?_,?_⟩
  · exact evaluateRaiseCall target k offset l1 l2 saved parts.2.2.2 parts.1 parts.2.1
      handler offsetWidth space location savedWord
  · rw [resultEq]
    simp only [compCorrectResult,Option.map,compileResult,ne_eq,not_true_eq_false,if_false]
    refine ⟨nonGc,gc,?_,?_,?_⟩
    · simpa only [postEq,pushLocals,clearedSource,lastNDrop2] using postRelation
    · simp only [postEq]
    · have distinct : 1 ≠ k := by omega
      simpa [unwindTarget,HolFiniteMapExact.lookup_updateEq,FUPDATE_HOL,distinct] using placed

#print axioms compCorrectRaise

end InitECandidate.Solver.Wave8Stage.WordToStackBounded
